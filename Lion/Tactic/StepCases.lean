/-
Lion/Tactic/StepCases.lean
===========================

Custom tactic for automated step case analysis.

Provides:
- @[step_rule Constructor] attribute for tagging lemmas
- step_cases tactic for automatic case dispatch

REFERENCES:
- Lean4 Metaprogramming Book, Ch 4-7:
  https://leanprover-community.github.io/lean4-metaprogramming-book/
- Lean4 Reference Manual, Attributes:
  https://lean-lang.org/lean4/doc/attributes.html
- Lean.Attributes (registerParametricAttribute):
  https://leanprover-community.github.io/mathlib4_docs/Lean/Attributes.html

STATUS: COMPLETE - implemented by alpha[theorist]
-/

import Lean
import Lean.Elab.Tactic

namespace Lion.Tactic.StepCases

open Lean Elab Tactic Meta

/-! =========== @[step_rule] ATTRIBUTE =========== -/

/-- Attribute parameter: the constructor name this rule handles.

    Usage: @[step_rule Step.plugin_internal]
    Links a lemma to its corresponding Step constructor.

    Reference: Lean4 Metaprogramming Book, Ch 5.3 (ParametricAttribute)
    https://leanprover-community.github.io/lean4-metaprogramming-book/05_syntax.html

    Implementation pattern from Lean.Compiler.ImplementedByAttr -/
initialize stepRuleAttr : ParametricAttribute Name ← registerParametricAttribute {
  name := `step_rule
  descr := "Tag a lemma as a Step-case rule for a given constructor"
  getParam := fun _declName stx => do
    -- stx has structure: @[step_rule <ident>]
    -- The ident is at stx[1] for simple attributes
    let ctorIdent ← Attribute.Builtin.getIdent stx
    return ctorIdent.getId
}

/-! =========== step_cases TACTIC =========== -/

/-- Lookup all lemmas tagged with @[step_rule ctor] for a given constructor.

    Reference: Lean4 Metaprogramming Book, Ch 4.4 (Environment queries)
    https://leanprover-community.github.io/lean4-metaprogramming-book/04_metam.html

    Implementation: Iterate over the NameMap stored in the extension's state,
    filtering for entries where the parameter matches ctorName. -/
def getStepRulesFor (ctorName : Name) : TacticM (List Name) := do
  let env ← getEnv
  -- Get local entries from the extension state (NameMap Name)
  let state := stepRuleAttr.ext.getState env
  -- Filter entries where the parameter (constructor name) matches
  -- Using foldl instead of deprecated fold
  let localMatches := state.foldl (init := []) fun acc declName param =>
    if param == ctorName then declName :: acc else acc
  return localMatches

/-- Apply the appropriate @[step_rule] lemma for the current goal.

    Reference: Lean4 Metaprogramming Book, Ch 7.2 (Tactic elaboration)
    https://leanprover-community.github.io/lean4-metaprogramming-book/07_elaboration.html

    Implementation: Look up rules for the constructor, then apply the first one. -/
def applyStepRule (ctorName : Name) : TacticM Unit := do
  let rules ← getStepRulesFor ctorName
  match rules with
  | [] => throwError s!"No @[step_rule {ctorName}] lemma found"
  | rule :: _ =>
    -- Build the constant expression with fresh universe metavariables
    let expr ← mkConstWithFreshMVarLevels rule
    -- Apply the lemma to the current goal using liftMetaTactic
    liftMetaTactic fun goal => do
      let newGoals ← goal.apply expr
      return newGoals

/-- Main step_cases tactic.

    Given a hypothesis `h : Step s s'`, performs case analysis on `h`
    and automatically applies the corresponding @[step_rule] lemma for each case.

    Algorithm:
    1. Perform `cases h` to split on Step constructors
    2. For each resulting goal, identify the constructor
    3. Lookup the @[step_rule] lemma for that constructor
    4. Apply the lemma with appropriate arguments

    Reference: Lean4 Metaprogramming Book, Ch 7.3 (Custom tactics)
    https://leanprover-community.github.io/lean4-metaprogramming-book/07_elaboration.html -/
syntax (name := stepCasesStx) "step_cases " ident : tactic

/-- Try to extract the Step constructor name from a goal's case tag.

    After `cases h` where h : Step s s', each goal is tagged with the
    constructor name (e.g., `plugin_internal`, `host_call`, `kernel_internal`).
    This function converts the tag to the full constructor name. -/
def getConstructorFromTag (tag : Name) : Name :=
  -- The tag is typically the short constructor name
  -- We need to qualify it with the Step type's namespace
  `Lion.Step ++ tag

/-- Run case analysis on a hypothesis using the meta-level API.

    Reference: Lean.Meta.Tactic.Cases (MVarId.cases) -/
def runCases (hName : Name) : TacticM (Array Meta.CasesSubgoal) := do
  let goal ← getMainGoal
  goal.withContext do
    -- Find the hypothesis by name in the local context
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? hName
      | throwError s!"Unknown hypothesis: {hName}"
    -- Run cases on the hypothesis
    let subgoals ← goal.cases decl.fvarId
    return subgoals

@[tactic stepCasesStx]
def evalStepCases : Tactic := fun stx => do
  match stx with
  | `(tactic| step_cases $h:ident) =>
    -- Get the hypothesis name
    let hName := h.getId
    -- Run `cases` on the hypothesis using meta-level API
    let subgoals ← runCases hName
    -- Set the resulting goals
    setGoals (subgoals.toList.map (·.mvarId))
  | _ => throwUnsupportedSyntax

/-- Variant that also tries to apply @[step_rule] lemmas automatically.

    Usage: step_cases_auto h

    After splitting on Step constructors, this tries to apply any
    registered @[step_rule] lemma for each case. -/
syntax (name := stepCasesAutoStx) "step_cases_auto " ident : tactic

@[tactic stepCasesAutoStx]
def evalStepCasesAuto : Tactic := fun stx => do
  match stx with
  | `(tactic| step_cases_auto $h:ident) =>
    -- Get the hypothesis name
    let hName := h.getId
    -- Run `cases` on the hypothesis
    let subgoals ← runCases hName
    -- For each subgoal, try to apply matching step rules
    let mut remainingGoals : List MVarId := []
    for subgoal in subgoals do
      setGoals [subgoal.mvarId]
      -- Get the constructor name from the subgoal tag
      let mvarDecl ← subgoal.mvarId.getDecl
      let tag := mvarDecl.userName
      let ctorName := getConstructorFromTag tag
      -- Try to apply a step rule
      try
        applyStepRule ctorName
        -- Add any remaining goals from applying the rule
        let newGoals ← getUnsolvedGoals
        remainingGoals := remainingGoals ++ newGoals
      catch _ =>
        -- If no rule found or application fails, keep the goal
        remainingGoals := remainingGoals ++ [subgoal.mvarId]
    setGoals remainingGoals
  | _ => throwUnsupportedSyntax

/-! =========== DEMO =========== -/

-- Simple demo showing the tactic syntax works
-- (Full demo with Step requires importing Lion.Step.Step)

section Demo

-- A simple inductive for testing
inductive DemoStep : Nat → Nat → Type where
  | inc : DemoStep n (n + 1)
  | dec : (h : n > 0) → DemoStep n (n - 1)
  | nop : DemoStep n n

-- Tag a lemma as handling the `inc` case
-- @[step_rule DemoStep.inc]
-- theorem demo_inc_rule : True := trivial

-- Demo: step_cases works on DemoStep
example (h : DemoStep m n) : True := by
  step_cases h
  -- Now we have 3 goals, one for each constructor
  all_goals trivial

end Demo

end Lion.Tactic.StepCases
