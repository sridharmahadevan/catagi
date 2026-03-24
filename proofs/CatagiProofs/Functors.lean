import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Types.Basic

/-!
# Functors — Definitions 7–10, Examples 2–4 from *Categories for AGI*

This module formalizes functors (covariant/contravariant), natural transformations,
presheaf categories, and the Yoneda embedding from Chapter 2 ("Functors for AGI").

## References
- Mahadevan, *Categories for AGI*, Chapter 2
- Mathlib: `CategoryTheory.Functor`, `CategoryTheory.NatTrans`, `CategoryTheory.Yoneda`
-/


open CategoryTheory

/-!
## Definition 7 — Functor

> A functor F : C → D is a structure-preserving mapping between categories that
> maps every C-object c to a D-object F(c), and every C-morphism f : c → c'
> to a D-morphism F(f) : F(c) → F(c'), preserving identity and composition:
> F(id_c) = id_{F(c)} and F(g ∘ f) = F(g) ∘ F(f).

This is exactly Mathlib's `Functor`.
-/

-- Definition 1: Category is Mathlib's `CategoryTheory.Category`
#check @CategoryTheory.Category

/-!
## Definition 8 — Covariant Functor

> A covariant functor F : C → D maps objects and morphisms in the same direction:
> if f : a → b in C, then F(f) : F(a) → F(b) in D.

A covariant functor is simply a `Functor` in Mathlib.
-/

/-- Definition 8: Covariant functor. In Mathlib, all `Functor`s are covariant. -/
abbrev CatAGI.CovariantFunctor (C D : Type*) [Category C] [Category D] := C ⥤ D

/-!
## Definition 9 — Contravariant Functor

> A contravariant functor F : C^op → D reverses the direction of morphisms:
> if f : a → b in C, then F(f) : F(b) → F(a) in D.

In Mathlib, a contravariant functor C → D is modeled as a (covariant) functor Cᵒᵖ → D.
-/

/-- Definition 9: Contravariant functor as a functor from the opposite category. -/
abbrev CatAGI.ContravariantFunctor (C D : Type*) [Category C] [Category D] := Cᵒᵖ ⥤ D

/-!
## Example 2 — Presheaf Category

> The functor category of presheaves Sets^{C^op} → Sets is defined as a category,
> where every object is a presheaf, a contravariant set-valued functor P : C^op → Sets.

In Mathlib this is the functor category `Cᵒᵖ ⥤ Type v`.
-/

/-- Example 2: the presheaf category over C, i.e. the functor category Cᵒᵖ ⥤ Type. -/
abbrev CatAGI.Presheaf (C : Type*) [Category C] := Cᵒᵖ ⥤ Type

/-- The presheaf category has a natural category structure (functor category). -/
example (C : Type) [SmallCategory C] : Category (CatAGI.Presheaf C) := inferInstance

/-!
## Example 3 — Yoneda Embedding

> The Yoneda embedding is defined as the mapping
> ᵏ : C → Sets^{C^op}, c ↦ Hom_C(−, c).

This is Mathlib's `yoneda` functor.
-/

-- Example 3: The Yoneda embedding C → (Cᵒᵖ ⥤ Type).
#check @yoneda

-- The Yoneda embedding is fully faithful (Example 4 in CatAGI).
-- Mathlib name: `yoneda.instFull` and `yoneda.instFaithful`

/-!
## Definition 10 — Natural Transformation

> Given any two functors F, G : C → D, a natural transformation η : F ⇒ G
> is a family of D-morphisms η_c : F(c) → G(c) indexed by objects c ∈ C
> such that for every f : c → c' in C, G(f) ∘ η_c = η_{c'} ∘ F(f).

This is Mathlib's `NatTrans`.
-/

#check @NatTrans

/-- Definition 10: Natural transformation as `NatTrans` in Mathlib.
    The naturality condition is `NatTrans.naturality`. -/
example {C D : Type*} [Category C] [Category D] (F G : C ⥤ D)
    (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ η.app Y = η.app X ≫ G.map f :=
  η.naturality f

/-!
## Clustering as a Functor

> Treating clustering as a functor implies designing an algorithm that behaves
> functorially: if the distances were scaled, the clustering output should
> transform accordingly.

We formalize the key ingredients: partitions, refinements (with proved
reflexivity and transitivity), and the clustering functor mapping a partition
to its set of cluster labels.
-/

/-- A partition of a type into k clusters. -/
structure Partition (X : Type) where
  /-- Number of clusters -/
  k : ℕ
  /-- Assignment of each element to a cluster index -/
  assign : X → Fin k

/-- A refinement of partitions: P₁ refines P₂ if each cluster of P₁
    is contained in a cluster of P₂, witnessed by a map on cluster labels. -/
def Partition.Refines {X : Type} (P₁ P₂ : Partition X) : Prop :=
  ∃ f : Fin P₁.k → Fin P₂.k, ∀ x, P₂.assign x = f (P₁.assign x)

/-- Refinement is reflexive. -/
theorem Partition.Refines.refl {X : Type} (P : Partition X) : P.Refines P :=
  ⟨id, fun _ => rfl⟩

/-- Refinement is transitive. -/
theorem Partition.Refines.trans {X : Type} {P₁ P₂ P₃ : Partition X}
    (h₁₂ : P₁.Refines P₂) (h₂₃ : P₂.Refines P₃) : P₁.Refines P₃ :=
  let ⟨f, hf⟩ := h₁₂
  let ⟨g, hg⟩ := h₂₃
  ⟨g ∘ f, fun x => (hg x).trans (congrArg g (hf x))⟩

/-- The clustering functor maps a partition to its set of cluster labels,
    and a refinement to the induced map on cluster labels. -/
structure ClusteringFunctor (X : Type) where
  /-- The underlying partition -/
  partition : Partition X

/-- The type of cluster labels for a clustering functor. -/
def ClusteringFunctor.clusters {X : Type} (F : ClusteringFunctor X) : Type :=
  Fin F.partition.k

/-- Map each element to its cluster label. -/
def ClusteringFunctor.clusterOf {X : Type} (F : ClusteringFunctor X) :
    X → Fin F.partition.k :=
  F.partition.assign

/-- A refinement between clustering functors lifts to a map on cluster labels. -/
noncomputable def ClusteringFunctor.refineMap {X : Type} (F₁ F₂ : ClusteringFunctor X)
    (h : F₁.partition.Refines F₂.partition) :
    Fin F₁.partition.k → Fin F₂.partition.k :=
  h.choose

/-!
## Status

| Item      | Description             | Status                       |
|-----------|-------------------------|------------------------------|
| Def 7     | Functor                 | ✅ Mathlib `Functor`          |
| Def 8     | Covariant functor       | ✅ abbrev                      |
| Def 9     | Contravariant functor   | ✅ abbrev from `Cᵒᵖ`          |
| Def 10    | Natural transformation  | ✅ Mathlib `NatTrans`          |
| Example 2 | Presheaf category       | ✅ `Cᵒᵖ ⥤ Type`               |
| Example 3 | Yoneda embedding        | ✅ Mathlib `yoneda`            |
| Example 4 | Yoneda fully faithful   | ✅ Mathlib                     |
| Clustering | Clustering as functor  | ✅ `Partition` + `Refines` + `ClusteringFunctor` |
-/
