# 1.2 Mathematical Preliminaries

## 1.2.1 Categories and Functors

**Definition 1.1** (Category): A category $\mathbf{C}$ consists of:

1. A class of objects $\mathrm{Obj}(\mathbf{C})$
2. For each pair of objects $A, B \in \mathrm{Obj}(\mathbf{C})$, a set of
   morphisms $\mathrm{Hom}_{\mathbf{C}}(A,B)$
3. A composition operation
   $\circ: \mathrm{Hom}_{\mathbf{C}}(B,C) \times \mathrm{Hom}_{\mathbf{C}}(A,B) \to \mathrm{Hom}_{\mathbf{C}}(A,C)$
4. For each object $A$, an identity morphism
   $\mathrm{id}_A \in \mathrm{Hom}_{\mathbf{C}}(A,A)$

satisfying the category axioms:

$$\begin{align}
(h \circ g) \circ f &= h \circ (g \circ f) \quad \text{(associativity)} \\
\mathrm{id}_B \circ f &= f \quad \text{for all } f \in \mathrm{Hom}_{\mathbf{C}}(A,B) \\
f \circ \mathrm{id}_A &= f \quad \text{for all } f \in \mathrm{Hom}_{\mathbf{C}}(A,B)
\end{align}$$

**Example 1.1**: The category $\mathbf{Set}$ has sets as objects and functions
as morphisms.

**Definition 1.2** (Functor): A functor $F: \mathbf{C} \to \mathbf{D}$ between
categories consists of:

1. An object function $F: \mathrm{Obj}(\mathbf{C}) \to \mathrm{Obj}(\mathbf{D})$
2. A morphism function
   $F: \mathrm{Hom}_{\mathbf{C}}(A,B) \to \mathrm{Hom}_{\mathbf{D}}(F(A),F(B))$

satisfying the functoriality conditions:

$$\begin{align}
F(g \circ f) &= F(g) \circ F(f) \quad \text{(composition preservation)} \\
F(\mathrm{id}_A) &= \mathrm{id}_{F(A)} \quad \text{(identity preservation)}
\end{align}$$

for all composable morphisms $f, g$ and all objects $A$.

**Example 1.2**: The forgetful functor $U: \mathbf{Grp} \to \mathbf{Set}$ maps
groups to their underlying sets and group homomorphisms to their underlying
functions.

## 1.2.2 Natural Transformations

**Definition 1.3** (Natural Transformation): Given functors
$F, G: \mathbf{C} \to \mathbf{D}$, a natural transformation
$\alpha: F \Rightarrow G$ consists of:

1. For each object $A \in \mathrm{Obj}(\mathbf{C})$, a morphism
   $\alpha_A: F(A) \to G(A)$ in $\mathbf{D}$

satisfying the naturality condition:

$$\alpha_B \circ F(f) = G(f) \circ \alpha_A$$

for every morphism $f: A \to B$ in $\mathbf{C}$.

**Example 1.3**: The double dual embedding
$\eta: \mathrm{Id}_{\mathbf{Vect}_k} \Rightarrow (-)**$ from finite-dimensional
vector spaces to their double duals.

## 1.2.3 Monoidal Categories

**Definition 1.4** (Monoidal Category): A monoidal category consists of:

- A category $\mathbf{C}$
- A tensor product bifunctor
  $\otimes: \mathbf{C} \times \mathbf{C} \to \mathbf{C}$
- A unit object $I$
- Natural isomorphisms for associativity, left unit, and right unit
- Coherence conditions (pentagon and triangle identities)

**Example 1.4**: The category of vector spaces with tensor product.

**Definition 1.5** (Symmetric Monoidal Category): A monoidal category with a
braiding natural isomorphism $\gamma_{A,B}: A \otimes B \to B \otimes A$
satisfying coherence conditions.

## 1.2.4 Limits and Colimits

**Definition 1.6** (Limit): Given a diagram $D: J \to \mathbf{C}$, a limit is an
object $L$ with morphisms $\pi_j: L \to D(j)$ such that for any other cone with
apex $X$, there exists a unique morphism $u: X \to L$ making all triangles
commute.

**Definition 1.7** (Colimit): The dual notion to limits, representing "gluing"
constructions.

## 1.2.5 Adjunctions

**Definition 1.8** (Adjunction): Functors $F: \mathbf{C} \to \mathbf{D}$ and
$G: \mathbf{D} \to \mathbf{C}$ are adjoint ($F \dashv G$) if there exists a
natural isomorphism:

$$\mathrm{Hom}_{\mathbf{D}}(F(A), B) \cong \mathrm{Hom}_{\mathbf{C}}(A, G(B))$$

**Example 1.5**: Free-forgetful adjunction between groups and sets.
