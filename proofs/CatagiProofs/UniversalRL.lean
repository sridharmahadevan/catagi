import CatagiProofs.Coalgebras
import CatagiProofs.UniversalDecision
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-!
# UniversalRL — Coalgebraic reinforcement learning

This module formalizes the later-book chapter on Universal Reinforcement
Learning (URL). The focus is on compact, buildable Lean abstractions for the
main mathematical assertions:

- Markov chains and MDPs as structured stochastic systems;
- Bellman operators for deterministic stationary policies;
- asynchronous box-style invariants for distributed updates;
- diagrammatic URL architectures;
- final-coalgebra witnesses;
- reuse of the UDM/information-field layer for asynchronous information flow.

## References
- Mahadevan, *Categories for AGI*, Chapter
  "Universal Reinforcement Learning"
-/


open CategoryTheory
open scoped BigOperators

universe u v w

/-- A finite-state Markov chain with row-stochastic transition kernel. -/
structure MarkovChain where
  State : Type u
  [instFintypeState : Fintype State]
  transition : State → State → ℝ
  transition_nonneg : ∀ s s', 0 ≤ transition s s'
  transition_row_sum : ∀ s, (∑ s' : State, transition s s') = 1

attribute [instance] MarkovChain.instFintypeState

/-- A finite Markov decision process. -/
structure MDP where
  State : Type u
  Action : Type v
  [instFintypeState : Fintype State]
  transition : State → Action → State → ℝ
  reward : State → Action → ℝ
  gamma : ℝ
  gamma_nonneg : 0 ≤ gamma
  gamma_lt_one : gamma < 1
  transition_nonneg : ∀ s a s', 0 ≤ transition s a s'
  transition_row_sum : ∀ s a, (∑ s' : State, transition s a s') = 1

attribute [instance] MDP.instFintypeState

/-- Deterministic stationary policy on an MDP. -/
structure DeterministicPolicy (M : MDP) where
  act : M.State → M.Action

/-- Bellman operator for a deterministic stationary policy. -/
def BellmanOperator (M : MDP) (π : DeterministicPolicy M) (V : M.State → ℝ) :
    M.State → ℝ :=
  fun s =>
    M.reward s (π.act s) +
      M.gamma * ∑ s' : M.State, M.transition s (π.act s) s' * V s'

/-- A fixed point of the Bellman operator satisfies the pointwise Bellman
    equation. -/
theorem bellman_fixed_point_equation (M : MDP) (π : DeterministicPolicy M)
    (V : M.State → ℝ) (hfix : BellmanOperator M π V = V) (s : M.State) :
    V s = M.reward s (π.act s) +
      M.gamma * ∑ s' : M.State, M.transition s (π.act s) s' * V s' := by
  have hs := congrArg (fun f => f s) hfix
  simp [BellmanOperator] at hs
  symm
  exact hs

/-- A box-style invariant set for asynchronous distributed updates. -/
def ComponentBox (ι : Type u) (α : ι → Type v) := ∀ i, Set (α i)

/-- Membership of a state in a product box. -/
def InComponentBox {ι : Type u} {α : ι → Type v} (B : ComponentBox ι α)
    (x : ∀ i, α i) : Prop :=
  ∀ i, x i ∈ B i

/-- Update one component while leaving the others unchanged. -/
def updateComponent {ι : Type u} {α : ι → Type v} [DecidableEq ι]
    (x : ∀ i, α i) (i : ι) (xi : α i) : ∀ j, α j :=
  fun j => if h : j = i then h ▸ xi else x j

/-- If the replacement value stays inside the corresponding component box, then
    the updated state remains inside the whole box. -/
theorem updateComponent_preserves_box {ι : Type u} {α : ι → Type v} [DecidableEq ι]
    (B : ComponentBox ι α) (x : ∀ i, α i) (hx : InComponentBox B x)
    (i : ι) (xi : α i) (hxi : xi ∈ B i) :
    InComponentBox B (updateComponent x i xi) := by
  intro j
  by_cases h : j = i
  · subst h
    simp [updateComponent, hxi]
  · simp [updateComponent, h, hx j]

/-- A diagrammatic architecture for URL: a functor from a finite index category
    into some ambient category of models. -/
structure URLArchitecture (J : Type u) (C : Type v) [Category J] [Category C] where
  diagram : J ⥤ C

/-- If the ambient category has all `J`-shaped limits, the URL architecture has
    a canonical diagram limit. -/
noncomputable def URLArchitecture.limit {J : Type u} {C : Type v}
    [Category J] [Category C] [Limits.HasLimitsOfShape J C]
    (A : URLArchitecture J C) : C :=
  Limits.limit A.diagram

/-- A witness that an `F`-coalgebra is final. -/
structure FinalCoalgebraWitness {C : Type u} [Category C] (F : C ⥤ C) where
  carrier : Coalgebra F
  desc : ∀ A : Coalgebra F, CoalgebraMor A carrier
  uniq : ∀ (A : Coalgebra F) (f : CoalgebraMor A carrier), f = desc A

/-- The universal arrow into a final coalgebra witness is unique. -/
theorem FinalCoalgebraWitness.hom_ext {C : Type u} [Category C] {F : C ⥤ C}
    (W : FinalCoalgebraWitness F) (A : Coalgebra F)
    (f g : CoalgebraMor A W.carrier) : f = g := by
  rw [W.uniq A f, W.uniq A g]

/-- URL reuses the UDM layer for asynchronous information fields. -/
abbrev URLInformationField := InformationField

/-- The empty event is observable in every URL information field. -/
theorem URLInformationField.empty_mem (F : URLInformationField) :
    (∅ : Set F.Ω) ∈ F.events :=
  InformationField.empty_mem F

/-!
## Status

| Item | Description | Status |
|------|-------------|--------|
| Def  | Markov chain | ✅ `MarkovChain` |
| Def  | MDP | ✅ `MDP` |
| Def  | Deterministic stationary policy | ✅ `DeterministicPolicy` |
| Def  | Bellman operator | ✅ `BellmanOperator` |
| Thm  | Fixed point gives Bellman equation | ✅ `bellman_fixed_point_equation` |
| Def  | Asynchronous component box | ✅ `ComponentBox` / `InComponentBox` |
| Thm  | One-component update preserves box invariants | ✅ `updateComponent_preserves_box` |
| Def  | URL architecture as a diagram | ✅ `URLArchitecture` |
| Def  | Final coalgebra witness | ✅ `FinalCoalgebraWitness` |
| Thm  | Final coalgebra arrows are unique | ✅ `FinalCoalgebraWitness.hom_ext` |
| Def  | URL information field | ✅ `URLInformationField` |
-/
