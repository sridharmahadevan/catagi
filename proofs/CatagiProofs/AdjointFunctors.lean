import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# AdjointFunctors — Definition 42, Theorems 4–8 from *Categories for AGI*

Formalizes adjunctions, triangle identities, and the preservation theorems
(right adjoints preserve limits, left adjoints preserve colimits).

## References
- Mahadevan, *Categories for AGI*, Chapter 11 ("Adjoint Functors")
- Mathlib: `CategoryTheory.Adjunction`
-/


open CategoryTheory

/-!
## Definition 42 — Adjunction

> An adjunction consists of a pair of functors F : C → D and G : D → C
> together with a natural isomorphism Hom_D(F(c), d) ≅ Hom_C(c, G(d))
> for all c ∈ C, d ∈ D. F is the left adjoint and G is the right adjoint.
-/

#check @Adjunction

/-!
## Theorem 4 — Unit Triangle Identity

> The unit η : Id_C ⇒ G ∘ F and counit ε : F ∘ G ⇒ Id_D satisfy:
> (ε F) ∘ (F η) = id_F  (left triangle identity)
-/

/-- Theorem 4: The left triangle identity (zig). -/
theorem triangle_right {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) (Y : D) :
    adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y) = 𝟙 _ :=
  adj.right_triangle_components Y

/-!
## Theorem 5 — Counit Triangle Identity

> (G ε) ∘ (η G) = id_G  (right triangle identity)
-/

/-- Theorem 5: The right triangle identity (zag). -/
theorem triangle_left {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) (X : C) :
    F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X) = 𝟙 _ :=
  adj.left_triangle_components X

/-!
## Theorem 6 — Right Adjoints Preserve Meets (in Preorders)

> Right adjoints preserve meets in a preorder.
> This is a special case of: right adjoints preserve limits.
-/

/-- Theorem 6: Right adjoints preserve limits (specializing to meets in preorders).
    Given an adjunction F ⊣ G, the right adjoint G preserves all small limits. -/
@[reducible]
noncomputable def right_adjoint_preserves_limits
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    Limits.PreservesLimitsOfSize.{0, 0} G :=
  adj.rightAdjoint_preservesLimits

/-!
## Theorem 7 — Limits from Adjunctions

> A category C admits all limits of diagrams indexed by a small category J
> if and only if the constant functor Δ : C → C^J has a right adjoint
> (the limit functor lim : C^J → C).
-/

/-- Theorem 7: The constant-diagram functor Δ : C → Cᴶ is left adjoint to the
    limit functor lim : Cᴶ → C, when C has all J-shaped limits. -/
noncomputable def limit_adjunction
    (J : Type) [SmallCategory J] (C : Type*) [Category C]
    [Limits.HasLimitsOfShape J C] :
    (Functor.const J : C ⥤ J ⥤ C) ⊣ Limits.lim :=
  Limits.constLimAdj

/-!
## Theorem 8 — RAPL / LAPC

> Right adjoints preserve limits, whereas left adjoints preserve colimits.
-/

/-- Theorem 8a (RAPL): Right adjoints preserve limits. -/
@[reducible]
noncomputable def rapl {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    Limits.PreservesLimitsOfSize.{0, 0} G :=
  adj.rightAdjoint_preservesLimits

/-- Theorem 8b (LAPC): Left adjoints preserve colimits. -/
@[reducible]
noncomputable def lapc {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    Limits.PreservesColimitsOfSize.{0, 0} F :=
  adj.leftAdjoint_preservesColimits

/-!
## Status

| Item   | Description           | Status                              |
|--------|-----------------------|-------------------------------------|
| Def 42 | Adjunction            | ✅ Mathlib `Adjunction`              |
| Thm 4  | Unit triangle         | ✅ `triangle_right`                  |
| Thm 5  | Counit triangle       | ✅ `triangle_left`                   |
| Thm 6  | Right adj ⊢ meets     | ✅ `right_adjoint_preserves_limits`  |
| Thm 7  | Limits from adjoints  | ✅ `limit_adjunction`                |
| Thm 8  | RAPL / LAPC           | ✅ `rapl` / `lapc`                   |
-/
