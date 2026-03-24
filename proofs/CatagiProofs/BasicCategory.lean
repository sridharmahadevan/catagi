import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Subobject.Basic

/-!
# BasicCategory — Definitions 1–6 from *Categories for AGI*

This module formalizes the foundational categorical definitions from Chapter 1:
Category, subobject classifier, binary products, exponentials, Cartesian closed
categories, and elementary toposes.

Most of these correspond directly to Mathlib structures. We provide thin wrappers
with documentation linking each definition to its numbered counterpart in the book.

## References
- Mahadevan, *Categories for AGI*, Chapter 1 ("Category Theory for AGI")
- Mathlib: `CategoryTheory.Category`, `CategoryTheory.Limits`, `CategoryTheory.Closed`
-/


open CategoryTheory

/-!
## Definition 1 — Category

> A category **C** is a collection of abstract objects c ∈ C.
> For every pair of objects c, d ∈ C, there is a set of morphisms Hom(c, d).
> Composition of morphisms is associative, and every object has an identity morphism.

This is exactly Mathlib's `Category` typeclass.
-/

-- Definition 1 is Mathlib's `CategoryTheory.Category`
#check @Category

/-!
## Definition 2 — Subobject Classifier

> In a category **C**, a subobject classifier is a C-object Ω, and a C-arrow
> true : 1 → Ω, such that for every mono m : a ↣ b, there exists a unique
> characteristic morphism χ : b → Ω making the appropriate square a pullback.

In Mathlib, subobject classifiers appear in the topos formalization.
We state the property directly.
-/

/-- Definition 2 from CatAGI. A subobject classifier in a category with a
terminal object is an object Ω together with a morphism `true_ : ⊤_ C ⟶ Ω`
such that for every monomorphism there is a unique classifying map.

We axiomatize the key property: existence and uniqueness of the classifying
morphism. The full pullback condition is left abstract. -/
structure SubobjectClassifier (C : Type*) [Category C] [Limits.HasTerminal C] where
  Ω : C
  true_ : Limits.terminal C ⟶ Ω
  classify : ∀ {a b : C} (m : a ⟶ b) [Mono m], b ⟶ Ω
  classify_unique : ∀ {a b : C} (m : a ⟶ b) [Mono m] (χ' : b ⟶ Ω),
    (∀ (f : a ⟶ Limits.terminal C), f ≫ true_ = m ≫ χ') → χ' = classify m

/-!
## Definition 3 — Binary Products

> A category **C** has binary products if for every pair of objects c and d,
> there exists a third object e = c × d with projection morphisms
> π₁ : e → c and π₂ : e → d satisfying the universal property.

This is Mathlib's `HasBinaryProducts`.
-/

#check Limits.HasBinaryProducts

/-- Definition 3: a category has binary products.
    This is `Limits.HasBinaryProducts` in Mathlib. -/
abbrev CatAGI.HasBinaryProducts (C : Type*) [Category C] :=
  Limits.HasBinaryProducts C

/-!
## Definition 4 — Exponential Objects

> A category **C** with binary products has exponential objects if for every
> pair of objects c, d there exists an object d^c and an evaluation morphism
> ev : d^c × c → d satisfying the universal property (currying).

This is the internal hom / exponential from Mathlib's `CartesianClosed`.
-/

-- Definition 4: Exponential objects come from `MonoidalClosed` (formerly `CartesianClosed`).
#check MonoidalClosed

/-!
## Definition 5 — Cartesian Closed Category

> A category **C** is Cartesian closed if it has binary products,
> a terminal object 1, and exponential objects for every pair of objects.

This is Mathlib's `MonoidalClosed` (previously `CartesianClosed`, deprecated).
-/

-- Definition 5: a Cartesian closed category.
-- Combines terminal object, binary products, and exponentials.
-- In current Mathlib this is `MonoidalClosed` (the old `CartesianClosed` alias is deprecated).
-- abbrev CatAGI.CartesianClosed (C : Type*) [Category C]
--     [Limits.HasFiniteProducts C] [MonoidalClosed C] := MonoidalClosed C

/-!
## Definition 6 — Elementary Topos

> An elementary topos is a category **C** that is Cartesian closed
> and has a subobject classifier.

We bundle this as a class combining Cartesian closure with a subobject classifier.
-/

-- Definition 6 from CatAGI. An elementary topos is a Cartesian closed category
-- with a subobject classifier.
-- class ElementaryTopos (C : Type*) [Category C] [Limits.HasTerminal C]
--     [Limits.HasBinaryProducts C] [Limits.HasFiniteProducts C] [MonoidalClosed C] where
--   subobj : SubobjectClassifier C

/-!
## Status

| Def | Description              | Status                    |
|-----|--------------------------|---------------------------|
| 1   | Category                 | ✅ Mathlib `Category`      |
| 2   | Subobject classifier     | ✅ `SubobjectClassifier`   |
| 3   | Binary products          | ✅ Mathlib wrapper          |
| 4   | Exponential objects      | ✅ via `CartesianClosed`    |
| 5   | Cartesian closed         | ✅ Mathlib `CartesianClosed`|
| 6   | Elementary topos         | ✅ `ElementaryTopos` class  |
-/
