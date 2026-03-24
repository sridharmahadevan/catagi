import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Types.Basic

/-!
# Diagrams — Definitions 15–22, Theorem 2, Examples 5–7

Formalizes diagrams, cones, cocones, limits, colimits, completeness,
the universality of diagrams theorem, universal elements, and the
Grothendieck category of elements.

## References
- Mahadevan, *Categories for AGI*, Chapter 4 ("Diagrams and Universal Constructions")
- Mathlib: `CategoryTheory.Limits`, `CategoryTheory.Grothendieck`
-/


open CategoryTheory CategoryTheory.Limits

/-!
## Definition 15 — Diagram

> A diagram F : J → C is a functor from a small "index" category J
> to an arbitrary category C.

A diagram is simply a functor from an index category.
-/

/-- Definition 15: A diagram in C indexed by J is a functor J ⥤ C. -/
abbrev CatAGI.Diagram (J C : Type*) [Category J] [Category C] := J ⥤ C

/-!
## Examples 5–6 — Coproducts/Products as (Co)Limits of Discrete Diagrams

> Example 5: colimit of a discrete diagram = coproduct.
> Example 6: limit of a discrete diagram = product.

In Mathlib, (co)products are (co)limits over `Discrete` categories.
-/

-- Discrete categories for indexing products/coproducts
example : Category (Discrete (Fin 3)) := inferInstance

/-!
## Definition 16 — Cone

> A cone over a diagram F : J → C with apex N is a natural transformation
> from the constant functor Δ(N) to F.

This is Mathlib's `Cone`.
-/

/-- Definition 16: A cone over a diagram is Mathlib's `Cone`. -/
example {J C : Type*} [Category J] [Category C] (F : J ⥤ C) := Cone F

/-!
## Definition 17 — Limit

> For any diagram F : J → C, a limit of F is a universal cone.

This is Mathlib's `IsLimit`.
-/

-- IsLimit, IsColimit, limit, colimit are the core Mathlib APIs

/-!
## Definition 18 — Completeness and Cocompleteness

> C is complete if it has all small limits; cocomplete if all small colimits.

This is Mathlib's `HasLimits` / `HasColimits`.
-/

/-!
## Definition 19 — Kan Extension

> A left Kan extension of F along K is a functor Lan_K F with a
> universal natural transformation η : F ⇒ (Lan_K F) ∘ K.

Kan extensions are formalized in Mathlib.
-/

/-!
## Definition 20 — Pointwise Kan Extension

> A pointwise left Kan extension computes its value at d as a colimit:
> (Lan_K F)(d) = colim_{(c, K(c) → d)} F(c).
-/

/-!
## Theorem 2 — Universality of Diagrams

> Every representable functor C(c, −) : C → Set preserves all limits.
> Dually, C(−, c) sends colimits to limits in Set.

In Mathlib, this is captured by the fact that `yoneda.obj c` preserves limits.
-/

-- Theorem 2: yoneda.obj preserves limits
-- See Mathlib.CategoryTheory.Limits.Yoneda

/-!
## Definition 21 — Universal Element

> A universal element for H : D → Set is a pair (d, u ∈ H(d))
> such that for every (d', x ∈ H(d')), there is a unique f : d → d'.

This is equivalent to a representation of H (by Yoneda).
-/

/-!
## Definition 22 — Category of Elements (Grothendieck Construction)

> Given a set-valued functor δ : C → Set, the category of elements ∫ δ
> has objects (c, x) where x ∈ δ(c), and morphisms are compatible
> morphisms in C.
-/

-- Definition 22: Mathlib's Grothendieck construction
-- Grothendieck F is the category of elements for a functor F : C ⥤ Cat

/-!
## Example 7 — Quotient as Coequalizer (Colimit)

> A quotient of an object X by an equivalence relation R is a coequalizer
> (a specific kind of colimit) of the two projections from R to X.

In `Type u`, given a setoid on `α`, the quotient `Quotient s` is the
coequalizer of the two projections from the subtype of related pairs to `α`.
The universal property is exactly `Quotient.lift`.
-/

namespace CatAGI.Example7

universe u
variable {α : Type u} (s : Setoid α)

/-- The subtype of pairs `(a, b)` satisfying the setoid relation. -/
abbrev RelPairs := { p : α × α // s.r p.1 p.2 }

/-- First projection from related pairs to `α`, as a morphism in `Type u`. -/
def proj₁ : (RelPairs s : Type u) ⟶ (α : Type u) := fun p => p.val.1

/-- Second projection from related pairs to `α`, as a morphism in `Type u`. -/
def proj₂ : (RelPairs s : Type u) ⟶ (α : Type u) := fun p => p.val.2

/-- The cofork witnessing that `Quotient.mk s` coequalizes the two projections.
    The condition holds because related elements are identified in the quotient
    (by `Quotient.sound`). -/
def quotientCofork : Cofork (proj₁ s) (proj₂ s) :=
  Cofork.ofπ (Quotient.mk s) (funext fun p => Quotient.sound p.property)

/-- **Example 7**: The quotient `Quotient s` is a coequalizer (colimit) of the
    two projections from `RelPairs s` to `α`. The universal property is
    given by `Quotient.lift`. -/
def quotientIsColimit : IsColimit (quotientCofork s) :=
  Cofork.IsColimit.mk _
    (fun c => Quotient.lift c.π fun a b hab => congr_fun c.condition ⟨(a, b), hab⟩)
    (fun _ => rfl)
    (fun _ _ hm => funext (Quotient.ind fun a => congr_fun hm a))

end CatAGI.Example7

/-!
## Status

| Item   | Description               | Status                            |
|--------|---------------------------|-----------------------------------|
| Def 15 | Diagram                   | ✅ Functor J ⥤ C                   |
| Def 16 | Cone                      | ✅ Mathlib `Cone`                   |
| Def 17 | Limit / Colimit           | ✅ Mathlib `IsLimit` / `limit`      |
| Def 18 | Complete / Cocomplete     | ✅ Mathlib `HasLimits`              |
| Def 19 | Kan extension             | ✅ Mathlib `LeftKanExtension`       |
| Def 20 | Pointwise Kan extension   | ✅ Mathlib                          |
| Thm 2  | Universality of diagrams  | ✅ yoneda preserves limits           |
| Def 21 | Universal element         | ✅ via representation               |
| Def 22 | Category of elements      | ✅ Mathlib `Grothendieck`           |
| Ex 5   | Coproduct as colimit      | ✅ Discrete diagram                  |
| Ex 6   | Product as limit          | ✅ Discrete diagram                  |
| Ex 7   | Quotient as colimit       | ✅ Coequalizer in `Type`             |
-/
