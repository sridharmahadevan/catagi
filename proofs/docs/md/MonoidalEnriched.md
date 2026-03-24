```lean
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Enriched.Basic
```

# MonoidalEnriched — Definitions 23–25 from *Categories for AGI*

Monoidal categories, symmetric monoidal categories, and V-enriched categories.

## References
- Mahadevan, *Categories for AGI*, Chapter 5 ("Categorical Deep Learning")
- Mathlib: `CategoryTheory.Monoidal`, `CategoryTheory.Enriched`

```lean
open CategoryTheory
```

## Definition 23 — Monoidal Category

> A monoidal category is a category C together with a functor ⊗ : C × C → C,
> a unit object e, and natural isomorphisms (associator α, left unitor λ,
> right unitor ρ) satisfying the triangle and pentagon coherence axioms.

```lean
#check @MonoidalCategory
```

## Definition 24 — Symmetric Monoidal Category

> A symmetric monoidal category is a monoidal category (C, ⊗, e, α, λ, ρ)
> together with a natural isomorphism (braiding) σ_{a,b} : a ⊗ b ≅ b ⊗ a
> satisfying σ_{b,a} ∘ σ_{a,b} = id.

```lean
#check @SymmetricCategory
```

## Definition 25 — V-Enriched Category

> A V-enriched category consists of a regular category C, such that for each
> pair of objects x and y in C, the hom-object C(x, y) is an object in V
> (a monoidal category), with composition and identity morphisms in V
> satisfying associativity and unit laws.

```lean
#check @EnrichedCategory
```

## Status

| Def | Description             | Status                           |
|-----|-------------------------|----------------------------------|
| 23  | Monoidal category       | ✅ Mathlib `MonoidalCategory`     |
| 24  | Symmetric monoidal      | ✅ Mathlib `SymmetricCategory`    |
| 25  | V-enriched category     | ✅ Mathlib `EnrichedCategory`     |
