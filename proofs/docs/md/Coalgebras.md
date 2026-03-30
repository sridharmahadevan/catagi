```lean
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
```

# Coalgebras — Definitions 60–62

Formalizes labeled transition systems, coalgebras, and the probability
distribution functor for modeling consciousness.

## References
- Mahadevan, *Categories for AGI*, Chapter 25 ("Consciousness")

```lean
open CategoryTheory
```

## Definition 60 — Labeled Transition System (LTS)

> A labeled transition system (S, →_S, A) is defined by a set S of states,
> a transition relation →_S ⊆ S × A × S, and a set A of action labels.

```lean
/-- Definition 60: Labeled Transition System. -/
structure LTS where
  /-- State space -/
  S : Type
  /-- Action labels -/
  A : Type
  /-- Transition relation: s --a--> s' -/
  trans : S → A → S → Prop
```

## Definition 61 — Coalgebra for a Functor

> Let F : C → C be an endofunctor. An F-coalgebra is a pair (X, α)
> where X is an object and α : X → F(X) is a morphism.

```lean
/-- Definition 61: F-coalgebra for an endofunctor F. -/
structure Coalgebra {C : Type*} [Category C] (F : C ⥤ C) where
  carrier : C
  struct : carrier ⟶ F.obj carrier

/-- Morphism of F-coalgebras. -/
structure CoalgebraMor {C : Type*} [Category C] {F : C ⥤ C}
    (A B : Coalgebra F) where
  hom : A.carrier ⟶ B.carrier
  comm : hom ≫ B.struct = A.struct ≫ F.map hom

/-- Extensionality for coalgebra morphisms: determined by their carrier morphism. -/
@[ext]
theorem CoalgebraMor.ext {C : Type*} [Category C] {F : C ⥤ C} {A B : Coalgebra F}
    {f g : CoalgebraMor A B} (h : f.hom = g.hom) : f = g := by
  rcases f with ⟨_, _⟩; rcases g with ⟨_, _⟩; subst h; rfl

/-- The category of F-coalgebras for an endofunctor F : C ⥤ C.
    Objects are F-coalgebras and morphisms commute with the structure maps. -/
instance coalgebraCategory {C : Type*} [Category C] (F : C ⥤ C) :
    Category (Coalgebra F) where
  Hom := CoalgebraMor
  id A := ⟨𝟙 A.carrier, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Category.assoc, g.comm, ← Category.assoc, f.comm, Category.assoc, ← F.map_comp]⟩
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp [Category.assoc]
```

## Definition 62 — Probability Distribution Functor

> The probability distribution functor D is defined as
> D : Meas → Meas mapping a measurable space X to the space
> D(X) of probability measures on X.

```lean
/-- Definition 62: The probability distribution functor.
    Maps a measurable space to its space of probability measures,
    and a measurable function to its pushforward on measures. -/
structure ProbDistFunctor where
  /-- On objects: X ↦ Prob(X) -/
  onObj : Type → Type
  /-- On morphisms: measurable f ↦ pushforward f_* -/
  onMor : ∀ {X Y : Type}, (X → Y) → onObj X → onObj Y
  /-- Functoriality: identity maps are preserved. -/
  onMor_id : ∀ {X : Type}, onMor (id : X → X) = id
  /-- Functoriality: composition is preserved. -/
  onMor_comp : ∀ {X Y Z : Type} (f : X → Y) (g : Y → Z),
    onMor (g ∘ f) = onMor g ∘ onMor f
```

## Stochastic Coalgebras

> A stochastic coalgebra is a D-coalgebra, i.e., a pair (X, α : X → D(X)).
> This models a probabilistic transition system where from each state
> there is a probability distribution over next states.

```lean
/-- A stochastic coalgebra (X, α : X → D(X)) models probabilistic dynamics.
    Used in the consciousness framework to model state transitions
    of conscious/unconscious processes. -/
structure StochasticCoalgebra (D : ProbDistFunctor) where
  /-- State space -/
  X : Type
  /-- Transition kernel: each state maps to a distribution over next states -/
  α : X → D.onObj X

/-- A morphism of stochastic coalgebras: a measurable map between state spaces
    that commutes with the transition kernels. -/
structure StochasticCoalgebraMor (D : ProbDistFunctor) (A B : StochasticCoalgebra D) where
  /-- Map on state spaces -/
  hom : A.X → B.X
  /-- Commutativity: D(hom) ∘ α_A = α_B ∘ hom -/
  comm : D.onMor hom ∘ A.α = B.α ∘ hom
```

## Status

| Def | Description            | Status                    |
|-----|------------------------|---------------------------|
| 60  | LTS                    | ✅ `LTS`                   |
| 61  | Coalgebra              | ✅ `Coalgebra`             |
| —   | Coalgebra category     | ✅ `coalgebraCategory`     |
| 62  | Prob distribution func | ✅ `ProbDistFunctor`       |
| —   | Stochastic coalgebra   | ✅ `StochasticCoalgebra`   |
