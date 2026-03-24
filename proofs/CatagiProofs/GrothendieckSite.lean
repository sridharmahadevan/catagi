import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Types.Basic

/-!
# GrothendieckSite — Definitions 46–49

Formalizes sieves, Grothendieck topologies, sites, and the subobject
classifier on presheaf toposes.

## References
- Mahadevan, *Categories for AGI*, Chapter 13 ("Topos Causal Models")
- Mathlib: `CategoryTheory.Sites`
-/


open CategoryTheory

universe u v

/-!
## Definition 46 — Sieve

> A sieve for any object x in a (small) category C is a subobject of
> its Yoneda embedding ᵏ(x) = C(−, x), i.e., a collection of morphisms
> into x closed under precomposition.
-/

#check @Sieve

/-!
## Definition 47 — Grothendieck Topology

> A Grothendieck topology on a category C is a function J which assigns
> to each object x of C a collection of sieves on x (called covering sieves)
> satisfying: maximal sieve covers, stability under pullback, and transitivity.
-/

#check @GrothendieckTopology

/-!
## Definition 48 — Site

> A site is defined as a pair (C, J) consisting of a small category C
> and a Grothendieck topology J on C.
-/

/-- Definition 48: A site is a category equipped with a Grothendieck topology.
    In Mathlib this is the data of a category `cat` together with a
    `GrothendieckTopology` on it. -/
structure Site where
  /-- The underlying category of the site. -/
  cat : Type u
  [instCat : Category.{v} cat]
  /-- The Grothendieck topology on `cat`. -/
  topology : GrothendieckTopology cat

attribute [instance] Site.instCat

/-!
## Definition 49 — Subobject Classifier on Presheaf Topos

> The subobject classifier Ω is defined on any topos Sets^{C^op} as
> the presheaf that assigns to each object c the set of sieves on c.

We construct Ω as an explicit functor `Cᵒᵖ ⥤ Type*`.
On objects it sends `c` to `Sieve c`; on morphisms it acts by
`Sieve.pullback`.  The functor laws follow from
`Sieve.pullback_id` and `Sieve.pullback_comp` (both in Mathlib).
-/

/-- Definition 49: The subobject classifier Ω on a presheaf topos `Cᵒᵖ ⥤ Type`
    sends each object `c` to `Sieve c` and acts on morphisms by sieve pullback.

    Given `f : X ⟶ Y` in `Cᵒᵖ` (i.e. `f.unop : Y.unop ⟶ X.unop` in `C`),
    `Ω.map f` pulls a sieve on `X.unop` back along `f.unop` to a sieve
    on `Y.unop`. -/
def subobjectClassifierPresheaf (C : Type u) [Category.{v} C] :
    Cᵒᵖ ⥤ Type (max v u) where
  obj X := Sieve X.unop
  map f := Sieve.pullback f.unop
  map_id X := by
    funext S
    simp
  map_comp f g := by
    funext S
    simp
    exact Sieve.pullback_comp S

/-! ### Key properties -/

/-- The subobject classifier sends each object to the type of sieves on it. -/
theorem subobjectClassifierPresheaf_obj (C : Type u) [Category.{v} C]
    (X : Cᵒᵖ) :
    (subobjectClassifierPresheaf C).obj X = Sieve X.unop :=
  rfl

/-- The subobject classifier acts on morphisms by sieve pullback. -/
theorem subobjectClassifierPresheaf_map (C : Type u) [Category.{v} C]
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (subobjectClassifierPresheaf C).map f = Sieve.pullback f.unop :=
  rfl

/-- Sieves on any object form a complete lattice (Mathlib). -/
example (C : Type u) [Category.{v} C] (X : C) :
    CompleteLattice (Sieve X) :=
  Sieve.instCompleteLattice

/-- The maximal sieve ⊤ acts as the "true" morphism `1 → Ω` of the
    subobject classifier: in each fiber, ⊤ is the greatest element. -/
theorem subobjectClassifierPresheaf_top_greatest
    (C : Type u) [Category.{v} C] (X : C) (S : Sieve X) :
    S ≤ ⊤ :=
  le_top

/-- The minimal sieve ⊥ is the least element in each fiber. -/
theorem subobjectClassifierPresheaf_bot_least
    (C : Type u) [Category.{v} C] (X : C) (S : Sieve X) :
    ⊥ ≤ S :=
  bot_le

/-- Pullback preserves the ordering on sieves. -/
theorem subobjectClassifierPresheaf_map_mono (C : Type u) [Category.{v} C]
    {X Y : C} (f : Y ⟶ X) {S T : Sieve X} (h : S ≤ T) :
    Sieve.pullback f S ≤ Sieve.pullback f T :=
  Sieve.pullback_monotone f h

/-!
## Status

| Def | Description              | Status                                 |
|-----|--------------------------|----------------------------------------|
| 46  | Sieve                    | ✅ Mathlib `Sieve`                      |
| 47  | Grothendieck topology    | ✅ Mathlib `GrothendieckTopology`        |
| 48  | Site                     | ✅ `Site` structure                      |
| 49  | Subobject classifier     | ✅ `subobjectClassifierPresheaf` functor |
-/
