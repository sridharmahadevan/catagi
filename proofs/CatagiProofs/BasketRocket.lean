import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic

/-!
# BasketRocket — Operational plan extraction and financially grounded reranking

This module formalizes the recent workflow-geometry chapters centered on
`BASKET`, `PLAN-KET`, and `ROCKET`.

The goal is not to mechanize the full data pipeline, but to capture the main
assertions in a Lean-friendly form:

- operational plans are finite partially ordered collections of action instances;
- displayed action chains are linearizations of those partial orders;
- `ROCKET` selects reward-maximizing plans from a local neighborhood;
- the reranker can be viewed as a normalization functor into value-complete plans.

## References
- Mahadevan, *Categories for AGI*, chapter
  "Building Agentic Systems using Kan Extension Transformers"
- Earlier CatAGI chapters on Kan extensions and Transformer categories
-/


open CategoryTheory

universe u

/-- An operational plan is a finite collection of action instances equipped with
    a partial order representing precedence constraints. -/
structure OperationalPlan (α : Type u) where
  /-- Action instances appearing in the plan. -/
  Event : Type u
  /-- Plans in the BASKET/ROCKET chapter are finite. -/
  instFintypeEvent : Fintype Event
  /-- Precedence is a partial order on action instances. -/
  instPartialOrderEvent : PartialOrder Event
  /-- Labels assign normalized action names to plan events. -/
  label : Event → α

attribute [instance] OperationalPlan.instFintypeEvent
attribute [instance] OperationalPlan.instPartialOrderEvent

/-- A displayed action chain is a linearization of the underlying partial order:
    precedence-respecting, but generally not identical to the whole plan. -/
structure Linearization {α : Type*} (P : OperationalPlan α) where
  order : P.Event → ℕ
  monotone_order : Monotone order

/-- An event is maximal if no strictly later event succeeds it in the plan. -/
def IsMaximalEvent {α : Type*} (P : OperationalPlan α) (e : P.Event) : Prop :=
  ∀ ⦃e' : P.Event⦄, e ≤ e' → e' = e

/-- A plan is value-complete when it reaches a designated terminal economic
    action such as `realize_revenue`. -/
def ValueComplete {α : Type*} (P : OperationalPlan α) (target : α) : Prop :=
  ∃ e : P.Event, P.label e = target ∧ IsMaximalEvent P e

/-- A convenient constructor for value-complete plans. -/
theorem valueComplete_of_labelled_terminal {α : Type*} {P : OperationalPlan α}
    {target : α} {e : P.Event} (hlabel : P.label e = target)
    (hmax : IsMaximalEvent P e) : ValueComplete P target :=
  ⟨e, hlabel, hmax⟩

/-- Morphisms of operational plans preserve both precedence and action labels. -/
structure PlanHom {α : Type*} (P Q : OperationalPlan α) where
  toFun : P.Event → Q.Event
  monotone_toFun : Monotone toFun
  label_preserving : ∀ e, Q.label (toFun e) = P.label e

@[ext]
theorem PlanHom.ext {α : Type*} {P Q : OperationalPlan α} {f g : PlanHom P Q}
    (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Operational plans form a category with precedence/label-preserving maps. -/
instance {α : Type*} : Category (OperationalPlan α) where
  Hom P Q := PlanHom P Q
  id P :=
    { toFun := id
      monotone_toFun := fun _ _ h => h
      label_preserving := by
        intro e
        rfl }
  comp f g :=
    { toFun := g.toFun ∘ f.toFun
      monotone_toFun := fun _ _ h => g.monotone_toFun (f.monotone_toFun h)
      label_preserving := by
        intro e
        simp [Function.comp, f.label_preserving, g.label_preserving] }
  id_comp f := by
    ext e
    rfl
  comp_id f := by
    ext e
    rfl
  assoc f g h := by
    ext e
    rfl

/-!
## BASKET and PLAN-KET

The chapter interprets workflow completion via Kan extensions. The left Kan
extension API is already available in Mathlib and is reused throughout this
repository.
-/

#check @Functor.LeftExtension

/-- `BASKET` extracts local operational plans from text. -/
structure BasketExtractor (Text : Type*) (α : Type*) where
  extract : Text → OperationalPlan α

/-- `PLAN-KET` embeds extracted plans into a latent plan manifold. -/
structure PlanEmbedding (α : Type*) (β : Type*) where
  encode : OperationalPlan α → β

/-!
## ROCKET
-/

/-- `ROCKET` selects a reward-maximizing plan from a finite local neighborhood. -/
structure RocketSelection (Plan : Type*) (Context : Type*) [DecidableEq Plan] where
  neighborhood : Finset Plan
  base : Plan
  base_mem : base ∈ neighborhood
  context : Context
  reward : Plan → Context → ℝ
  chosen : Plan
  chosen_mem : chosen ∈ neighborhood
  optimal : ∀ p ∈ neighborhood, reward p context ≤ reward chosen context

theorem RocketSelection.chosen_is_optimal {Plan : Type*} {Context : Type*}
    [DecidableEq Plan] (R : RocketSelection Plan Context)
    {p : Plan} (hp : p ∈ R.neighborhood) :
    R.reward p R.context ≤ R.reward R.chosen R.context :=
  R.optimal p hp

/-- `ROCKET` can be viewed as a normalization operator into value-complete
    plans. This is a Lean-friendly weakening of the chapter's normalization
    functor language. -/
structure RocketNormalization (α : Type*) where
  target : α
  normalize : OperationalPlan α → OperationalPlan α
  value_complete : ∀ P : OperationalPlan α, ValueComplete (normalize P) target

theorem RocketNormalization.normalized_plan_value_complete {α : Type*}
    (R : RocketNormalization α) (P : OperationalPlan α) :
    ValueComplete (R.normalize P) R.target :=
  R.value_complete P

/-!
## Status

| Item | Description | Status |
|------|-------------|--------|
| Def  | Operational plan as finite poset | ✅ `OperationalPlan` |
| Def  | Displayed chain as linearization | ✅ `Linearization` |
| Def  | Value-complete plan | ✅ `ValueComplete` |
| Def  | BASKET extraction | ✅ `BasketExtractor` |
| Def  | PLAN-KET latent embedding | ✅ `PlanEmbedding` |
| Def  | ROCKET reranking | ✅ `RocketSelection` |
| Thm  | ROCKET winner is reward-optimal in its neighborhood | ✅ `RocketSelection.chosen_is_optimal` |
| Def  | ROCKET as normalization operator | ✅ `RocketNormalization` |
-/
