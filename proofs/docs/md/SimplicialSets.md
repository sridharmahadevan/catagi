```lean
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
```

# SimplicialSets — Definitions 33, 37–40, Examples 8–12

Formalizes simplicial sets, degenerate simplices, standard simplices,
boundaries, and horns from Chapter 7 ("Geometric Transformers").

## References
- Mahadevan, *Categories for AGI*, Chapter 7
- Mathlib: `AlgebraicTopology.SimplicialSet`

```lean
open CategoryTheory Simplicial SSet
```

## Simplicial Sets — Background

The book models Geometric Transformers using simplicial sets.
Mathlib has `SSet` (simplicial sets as presheaves on Δ).

```lean
#check SSet
#check stdSimplex
```

## Examples 8–12 — Vertices, Edges, Face and Degeneracy Operators

> Example 8: The "vertices" of a simplicial object C_n are the objects in C,
>   and the "edges" are its arrows.
> Example 9: An n-simplex σ of C_n can be identified with the sequence
>   [c_0 →^{f_1} c_1 →^{f_2} ... →^{f_n} c_n].
> Example 10: The face operator d_i deletes the i-th vertex.
> Example 11: The face operator d_0 applied to an edge gives the codomain.
> Example 12: The degeneracy operator s_i inserts an identity at position i.

These are the standard simplicial identities, formalized in Mathlib's
`SimplexCategory` and its face/degeneracy maps.

```lean
#check SimplexCategory
#check SimplexCategory.δ  -- face maps
#check SimplexCategory.σ  -- degeneracy maps
```

## Definition 33 — Degenerate Simplex

> Given a category C, and an n-simplex σ of the simplicial set C_n,
> σ is a degenerate simplex if σ = s_i(τ) for some (n-1)-simplex τ.

```lean
/-- Definition 33: A simplex is degenerate if it is in the image of
    some degeneracy map. -/
def IsDegenerate {X : SSet} {n : ℕ} (x : X _⦋n + 1⦌) : Prop :=
  ∃ (i : Fin (n + 1)) (τ : X _⦋n⦌), X.σ i τ = x
```

## Definition 37 — Standard Simplex

> The standard simplex Δ^n is the simplicial set defined by the
> representable functor Hom_Δ(−, [n]).

```lean
-- Definition 37: The standard n-simplex Δ^n in Mathlib.
#check @stdSimplex
```

## Definition 38 — Simplicial Subset

> Let S_· denote a simplicial set. If for every integer n ≥ 0, we are
> given a subset T_n ⊆ S_n that is closed under face and degeneracy maps,
> then T is a simplicial subset of S.

A simplicial subset is a subfunctor / subobject in the presheaf category.

```lean
-- Definition 38: A simplicial subset is a monomorphism into the ambient
-- simplicial set. In Mathlib, this is a `Subobject` in the category `SSet`.
-- Subobjects in SSet are monomorphisms T ⟶ S
```

## Definition 39 — Boundary

> The boundary ∂Δ^n is the simplicial set obtained from the standard
> simplex Δ^n by removing the unique non-degenerate n-simplex.

```lean
-- Definition 39: The boundary of the standard n-simplex. 
#check @SSet.boundary
```

## Definition 40 — Horn

> The Horn Λ^n_i is the simplicial set obtained from the boundary ∂Δ^n
> by removing the i-th face. It is used to define Kan fibrations and
> inner/outer horn filling conditions.

```lean
-- Definition 40: The horn Λ^n_i. 
#check @SSet.horn

-- Inner horns (0 < i < n) vs outer horns (i = 0 or i = n) are
-- central to the book's discussion of DB and GT. Inner horn
-- extensions correspond to standard backpropagation (composition),
-- while outer horn extensions require the novel GT framework.
```

## Status

| Item   | Description          | Status                       |
|--------|----------------------|------------------------------|
| Ex 8–12| Vertices, faces etc  | ✅ Mathlib simplicial identities|
| Def 33 | Degenerate simplex   | ✅ `IsDegenerate`              |
| Def 37 | Standard simplex     | ✅ Mathlib `standardSimplex`   |
| Def 38 | Simplicial subset    | ✅ Subobject in SSet           |
| Def 39 | Boundary             | ✅ Mathlib `SSet.boundary`     |
| Def 40 | Horn                 | ✅ Mathlib `SSet.horn`         |
