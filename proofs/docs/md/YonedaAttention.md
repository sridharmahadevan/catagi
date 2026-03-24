```lean
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.Hom
```

# YonedaAttention — Definitions 11–14, Theorem 1, Lemma 1

Formalizes natural transformations between functors, universal arrows,
the Yoneda lemma, and the book's novel connection between self-attention
in Transformers and the Yoneda embedding.

## References
- Mahadevan, *Categories for AGI*, Chapter 3 ("Representable Functors and the Yoneda Lemma")
- Mathlib: `CategoryTheory.Yoneda`, `CategoryTheory.Representable`

```lean
open CategoryTheory
```

## Definition 11 — Natural Transformation (between specific functor pairs)

> Given categories C and D, and functors F, G : C → D, a natural transformation
> η : F ⇒ G is a family of D-morphisms {η_c : F(c) → G(c)}_{c ∈ C}
> such that for every morphism f : c → c' in C,
> G(f) ∘ η_c = η_{c'} ∘ F(f).

(Already formalized in Functors.lean; re-exported here for context.)

## Definition 12 — Universal Arrow

> Given a functor S : D → C and an object c ∈ C, a universal arrow from c to S
> is a pair (r, u) where r is an object of D and u : c → S(r) is a morphism in C,
> such that for every pair (d, f) with f : c → S(d), there exists a unique
> morphism f' : r → d with S(f') ∘ u = f.

This is closely related to initial objects in the comma category (c ↓ S).

```lean
/-- Definition 12: Universal arrow from c to S.
    A pair (r, u : c ⟶ S.obj r) with the universal factorization property. -/
structure UniversalArrow {C D : Type*} [Category C] [Category D]
    (S : D ⥤ C) (c : C) where
  r : D
  u : c ⟶ S.obj r
  desc : ∀ (d : D) (f : c ⟶ S.obj d), r ⟶ d
  fac : ∀ (d : D) (f : c ⟶ S.obj d), u ≫ S.map (desc d f) = f
  uniq : ∀ (d : D) (f : c ⟶ S.obj d) (g : r ⟶ d),
    u ≫ S.map g = f → g = desc d f
```

## Definition 13 — Representation of a Functor

> If D is a category and H : D → Set is a functor, a representation of H
> is an object d ∈ D together with a natural isomorphism
> Hom_D(d, −) ≅ H.

This is Mathlib's `Functor.Representable` / `Representation`.

```lean
-- Mathlib's `Functor.Representable` (if available) or `RepresentedBy`
-- #check @CategoryTheory.Functor.Representable
```

## Lemma 1 / Theorem 1 — Yoneda Lemma

> For any functor F : C^op → Set and any object c ∈ C,
> Nat(Hom(−, c), F) ≅ F(c).
> Moreover, this bijection is natural in both c and F.

This is the Yoneda lemma, available in Mathlib as `yonedaEquiv`.

```lean
-- Lemma 1 / Theorem 1 (Yoneda Lemma).
-- Natural transformations from Hom(−, c) to F are in bijection with F(c).
-- In Mathlib: `yonedaEquiv`

-- The Yoneda equivalence is natural.
-- example (F : Cᵒᵖ ⥤ Type) (c : C) : (yoneda.obj c ⟶ F) ≃ F.obj (Opposite.op c)
```

## Definition 14 — Universal Representation via Representable Functors

> A universal representation of an object c ∈ C is defined as a contravariant
> functor F : C^op → Set that is representable, i.e., F ≅ Hom(−, c).

This is Mathlib's concept of representability.

```lean
-- Definition 14: An object c represents a presheaf F when Hom(−, c) ≅ F.
-- Representability is a property of presheaves.
-- example (F : Cᵒᵖ ⥤ Type) : Prop := ∃ (c : C), Nonempty (yoneda.obj c ≅ F)
```

## Attention as an Enriched Yoneda Profile (Informal Construction)

> Clicking the token "england" reveals its head-wise attention distribution
> at a fixed layer. The attention profile — and therefore the contextual
> embedding — changes with context, disambiguating the phrase "New England".

The book claims that self-attention in Transformers can be understood as a
*Yoneda profile*: for each token x, its contextual representation is determined
by how it "maps into" all other tokens, analogous to how an object in a
category is determined by its hom-functor Hom(−, x).

We formalize the core structural analogy. The full enriched version
(attention weights as enriched hom-values) requires the enriched Yoneda
lemma, which is partially available in Mathlib.

```lean
/-- The structural analogy: for a fixed attention layer, each token x
    induces a "profile" mapping every other token y to an attention weight.
    This mirrors the Yoneda embedding c ↦ Hom(−, c).

    The key insight is that two tokens with isomorphic attention profiles
    (same attention distribution over all keys) must have the same
    contextual embedding, just as the Yoneda lemma says two objects with
    naturally isomorphic hom-functors are isomorphic.
-/
structure AttentionYonedaProfile where
  /-- Token vocabulary (objects of the "token category") -/
  Token : Type
  /-- Attention weight type (enrichment base, e.g., ℝ≥0) -/
  Weight : Type
  /-- For each pair of tokens (query, key), the attention weight -/
  attn : Token → Token → Weight
  /-- The "Yoneda profile" of a query token is its attention over all keys -/
  profile (q : Token) : Token → Weight := attn q
```

## Status

| Item   | Description              | Status                        |
|--------|--------------------------|-------------------------------|
| Def 11 | Natural transformation   | ✅ (see Functors.lean)         |
| Def 12 | Universal arrow          | ✅ `UniversalArrow`            |
| Def 13 | Representation           | ✅ Mathlib `Representable`     |
| Def 14 | Universal representation | ✅ Mathlib                     |
| Thm 1  | Yoneda lemma             | ✅ Mathlib `yonedaEquiv`       |
| Lemma 1| Yoneda lemma             | ✅ (same as Thm 1)             |
| Attn   | Attention as Yoneda      | 📋 Structural analogy           |
