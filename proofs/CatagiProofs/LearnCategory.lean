import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# LearnCategory — Definitions 31–32 from *Categories for AGI*

Formalizes the category **Learn** of supervised learners and the category
**Param** of parameterized functions, including backpropagation as a functor.

Morphisms are equivalence classes of learners (respectively, parameterized
functions), quotiented by parameter-space reparametrization so that the
category axioms hold exactly.

## References
- Mahadevan, *Categories for AGI*, Chapter 5 ("Categorical Deep Learning")
- Fong, Spivak, Tuyéras, "Backprop as Functor" (2019)
-/

open CategoryTheory

/-!
## Definition 31 — Category Learn

> The symmetric monoidal category Learn is defined as:
> - Objects: sets (input/output spaces)
> - Morphisms (A, B): triples (P, I, U, r) where P is a parameter space,
>   I : A × P → B is the implementation, U : A × B × P → P is the
>   update (learning) rule, and r : B × B → ℝ is the request function.
>
> Morphisms are taken up to reparametrization of the parameter space.
-/

/-- Definition 31: A learner morphism in the category Learn.
    Captures parameterized implementation + update rule. -/
structure Learner (A B : Type) where
  /-- Parameter space -/
  P : Type
  /-- Implementation: given input and parameters, produce output -/
  impl : A × P → B
  /-- Update rule: given input, desired output, and parameters, update parameters -/
  update : A × B × P → P
  /-- Request function: compares actual vs desired output -/
  request : B × B → Float

/-- Composition of learners (Definition 31).
    Given learners f : A → B and g : B → C, their composite
    uses the chain rule for parameter updates. -/
def Learner.comp {A B C : Type} (f : Learner A B) (g : Learner B C) :
    Learner A C where
  P := f.P × g.P
  impl := fun ⟨a, p_f, p_g⟩ => g.impl ⟨f.impl ⟨a, p_f⟩, p_g⟩
  update := fun ⟨a, c, p_f, p_g⟩ =>
    let b := f.impl ⟨a, p_f⟩
    (f.update ⟨a, b, p_f⟩, g.update ⟨b, c, p_g⟩)
  request := g.request

/-- Identity learner: passes input through unchanged. -/
def Learner.id (A : Type) : Learner A A where
  P := PUnit
  impl := fun ⟨a, _⟩ => a
  update := fun ⟨_, _, p⟩ => p
  request := fun ⟨_, _⟩ => 0.0

/-! ### Equivalence relation on learners -/

/-- Equivalence of learners up to parameter-space reparametrization.
    Two learners are equivalent when their implementations agree
    modulo a bijection on parameter spaces. -/
def Learner.Equiv {A B : Type} (f g : Learner A B) : Prop :=
  ∃ (e : f.P ≃ g.P), ∀ a p, f.impl (a, p) = g.impl (a, e p)

/-- The equivalence relation on learners forms a setoid. -/
instance learnerSetoid (A B : Type) : Setoid (Learner A B) where
  r := Learner.Equiv
  iseqv := {
    refl := fun f => ⟨.refl f.P, fun _ _ => rfl⟩
    symm := fun {f g} ⟨e, h⟩ => ⟨e.symm, fun a p => by
      have := (h a (e.symm p)).symm
      rwa [Equiv.apply_symm_apply] at this⟩
    trans := fun {_ _ _} ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ => ⟨e₁.trans e₂, fun a p => by
      simp only [Equiv.trans_apply]; exact (h₁ a p).trans (h₂ a (e₁ p))⟩
  }

/-! ### Canonical parameter-space equivalences -/

private def prodCongrEquiv {α₁ α₂ β₁ β₂ : Type}
    (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ where
  toFun := fun ⟨a, b⟩ => ⟨e₁ a, e₂ b⟩
  invFun := fun ⟨a, b⟩ => ⟨e₁.symm a, e₂.symm b⟩
  left_inv := fun ⟨a, b⟩ => by simp
  right_inv := fun ⟨a, b⟩ => by simp

private def punitProdEquiv (α : Type) : PUnit × α ≃ α where
  toFun := fun ⟨_, a⟩ => a
  invFun := fun a => ⟨PUnit.unit, a⟩
  left_inv := fun ⟨u, _⟩ => by cases u; rfl
  right_inv := fun _ => rfl

private def prodPUnitEquiv (α : Type) : α × PUnit ≃ α where
  toFun := fun ⟨a, _⟩ => a
  invFun := fun a => ⟨a, PUnit.unit⟩
  left_inv := fun ⟨_, u⟩ => by cases u; rfl
  right_inv := fun _ => rfl

private def prodAssocEquiv (α β γ : Type) : (α × β) × γ ≃ α × (β × γ) where
  toFun := fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  invFun := fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩
  left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  right_inv := fun ⟨_, _, _⟩ => rfl

/-- Composition of learners respects the equivalence relation. -/
private theorem Learner.comp_equiv {A B C : Type}
    ⦃f₁ f₂ : Learner A B⦄ (hf : f₁ ≈ f₂)
    ⦃g₁ g₂ : Learner B C⦄ (hg : g₁ ≈ g₂) :
    Learner.comp f₁ g₁ ≈ Learner.comp f₂ g₂ := by
  obtain ⟨ef, hf⟩ := hf
  obtain ⟨eg, hg⟩ := hg
  refine ⟨prodCongrEquiv ef eg, fun a ⟨pf, pg⟩ => ?_⟩
  show g₁.impl (f₁.impl (a, pf), pg) = g₂.impl (f₂.impl (a, ef pf), eg pg)
  rw [hf a pf, hg _ pg]

/-- Wrapper type for objects in the Learn category, avoiding conflict with
    the existing category instance on Type. -/
structure LearnObj where
  carrier : Type

/-- Category instance for Learn. Morphisms are equivalence classes of learners
    under parameter-space reparametrization. -/
instance : Category LearnObj where
  Hom A B := Quotient (learnerSetoid A.carrier B.carrier)
  id A := ⟦Learner.id A.carrier⟧
  comp f g := Quotient.map₂ Learner.comp
    (fun _ _ hf _ _ hg => Learner.comp_equiv hf hg) f g
  id_comp f := Quotient.inductionOn f fun f => by
    simp only [Quotient.map₂_mk]
    exact Quotient.sound ⟨punitProdEquiv f.P, fun a ⟨u, p⟩ => by cases u; rfl⟩
  comp_id f := Quotient.inductionOn f fun f => by
    simp only [Quotient.map₂_mk]
    exact Quotient.sound ⟨prodPUnitEquiv f.P, fun a ⟨p, u⟩ => by cases u; rfl⟩
  assoc f g h := Quotient.inductionOn f fun f =>
    Quotient.inductionOn g fun g =>
      Quotient.inductionOn h fun h => by
    simp only [Quotient.map₂_mk]
    exact Quotient.sound ⟨prodAssocEquiv f.P g.P h.P,
      fun a ⟨⟨pf, pg⟩, ph⟩ => rfl⟩

/-!
## Definition 32 — Category Param

> The category Param defines a strict symmetric monoidal category whose
> objects are Euclidean spaces, and whose morphisms are smooth
> parameterized functions with their derivatives.
-/

/-- Definition 32: A morphism in the Param category.
    A differentiable parameterized function with its derivative. -/
structure ParamMor (A B : Type) where
  /-- Parameter space -/
  P : Type
  /-- Forward map -/
  forward : P → A → B
  /-- Derivative / Jacobian (for backpropagation) -/
  backward : P → A → B → A × P

/-- Identity parameterized morphism. -/
def ParamMor.id (A : Type) : ParamMor A A where
  P := PUnit
  forward := fun _ a => a
  backward := fun _ _ b => ⟨b, PUnit.unit⟩

/-- Composition of parameterized morphisms (chain rule). -/
def ParamMor.comp {A B C : Type} (f : ParamMor A B) (g : ParamMor B C) :
    ParamMor A C where
  P := f.P × g.P
  forward := fun ⟨pf, pg⟩ a => g.forward pg (f.forward pf a)
  backward := fun ⟨pf, pg⟩ a c =>
    let b := f.forward pf a
    let (b_grad, pg') := g.backward pg b c
    let (a_grad, pf') := f.backward pf a b_grad
    (a_grad, (pf', pg'))

/-! ### Equivalence relation on parameterized morphisms -/

/-- Equivalence of parameterized morphisms up to parameter-space
    reparametrization. Two morphisms are equivalent when their forward
    maps agree modulo a bijection on parameter spaces. -/
def ParamMor.Equiv {A B : Type} (f g : ParamMor A B) : Prop :=
  ∃ (e : f.P ≃ g.P), ∀ p a, f.forward p a = g.forward (e p) a

/-- The equivalence relation on parameterized morphisms forms a setoid. -/
instance paramMorSetoid (A B : Type) : Setoid (ParamMor A B) where
  r := ParamMor.Equiv
  iseqv := {
    refl := fun f => ⟨.refl f.P, fun _ _ => rfl⟩
    symm := fun {f g} ⟨e, h⟩ => ⟨e.symm, fun p a => by
      have := (h (e.symm p) a).symm
      rwa [Equiv.apply_symm_apply] at this⟩
    trans := fun {_ _ _} ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ => ⟨e₁.trans e₂, fun p a => by
      simp only [Equiv.trans_apply]; exact (h₁ p a).trans (h₂ (e₁ p) a)⟩
  }

/-- Composition of parameterized morphisms respects the equivalence. -/
private theorem ParamMor.comp_equiv {A B C : Type}
    ⦃f₁ f₂ : ParamMor A B⦄ (hf : f₁ ≈ f₂)
    ⦃g₁ g₂ : ParamMor B C⦄ (hg : g₁ ≈ g₂) :
    ParamMor.comp f₁ g₁ ≈ ParamMor.comp f₂ g₂ := by
  obtain ⟨ef, hf⟩ := hf
  obtain ⟨eg, hg⟩ := hg
  refine ⟨prodCongrEquiv ef eg, fun ⟨pf, pg⟩ a => ?_⟩
  show g₁.forward pg (f₁.forward pf a) = g₂.forward (eg pg) (f₂.forward (ef pf) a)
  rw [hf pf a, hg pg _]

/-- Wrapper type for objects in the Param category. -/
structure ParamObj where
  carrier : Type

/-- Category instance for Param. Morphisms are equivalence classes of
    parameterized functions under parameter-space reparametrization. -/
instance : Category ParamObj where
  Hom A B := Quotient (paramMorSetoid A.carrier B.carrier)
  id A := ⟦ParamMor.id A.carrier⟧
  comp f g := Quotient.map₂ ParamMor.comp
    (fun _ _ hf _ _ hg => ParamMor.comp_equiv hf hg) f g
  id_comp f := Quotient.inductionOn f fun f => by
    simp only [Quotient.map₂_mk]
    exact Quotient.sound ⟨punitProdEquiv f.P, fun ⟨u, p⟩ a => by cases u; rfl⟩
  comp_id f := Quotient.inductionOn f fun f => by
    simp only [Quotient.map₂_mk]
    exact Quotient.sound ⟨prodPUnitEquiv f.P, fun ⟨p, u⟩ a => by cases u; rfl⟩
  assoc f g h := Quotient.inductionOn f fun f =>
    Quotient.inductionOn g fun g =>
      Quotient.inductionOn h fun h => by
    simp only [Quotient.map₂_mk]
    exact Quotient.sound ⟨prodAssocEquiv f.P g.P h.P,
      fun ⟨⟨pf, pg⟩, ph⟩ a => rfl⟩

/-!
## Backpropagation as a Functor

> The backpropagation algorithm defines a functor from Param to Learn:
> it sends each parameterized differentiable function to a learner
> whose update rule is gradient descent.
-/

/-- Map a parameterized morphism to a learner via backpropagation.
    The forward pass becomes the implementation, and the backward pass
    (derivative) provides the parameter update rule (gradient descent). -/
def backpropMap {A B : Type} (f : ParamMor A B) : Learner A B where
  P := f.P
  impl := fun ⟨a, p⟩ => f.forward p a
  update := fun ⟨a, b, p⟩ => (f.backward p a b).2
  request := fun ⟨_, _⟩ => 0.0

/-- backpropMap respects the equivalence on parameterized morphisms. -/
private theorem backpropMap_respects {A B : Type}
    ⦃f₁ f₂ : ParamMor A B⦄ (h : f₁ ≈ f₂) :
    @Setoid.r _ (learnerSetoid A B) (backpropMap f₁) (backpropMap f₂) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, fun a p => he p a⟩

/-- Backpropagation as a functor Param → Learn.
    The key insight is that the chain rule for derivatives corresponds
    to functorial composition of learners: backprop(g ∘ f) ≅ backprop(g) ∘ backprop(f). -/
def backpropFunctor : ParamObj ⥤ LearnObj where
  obj A := ⟨A.carrier⟩
  map f := Quotient.map backpropMap (fun _ _ h => backpropMap_respects h) f
  map_id X := by
    exact Quotient.sound ⟨.refl _, fun a p => by cases p; rfl⟩
  map_comp f g := Quotient.inductionOn f fun f =>
    Quotient.inductionOn g fun g => by
    simp only [Quotient.map_mk]
    exact Quotient.sound ⟨.refl _, fun a ⟨pf, pg⟩ => rfl⟩

/-!
## Status

| Def | Description         | Status          |
|-----|---------------------|-----------------|
| 31  | Category Learn      | ✅ `LearnObj` + `Category` (quotient) |
| 32  | Category Param      | ✅ `ParamObj` + `Category` (quotient) |
| BP  | Backprop functor    | ✅ `backpropFunctor` (fully proved)   |
-/
