import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# PredictiveStateTopos — Predictive state representations in a topos

This module formalizes the newer chapter on predictive state representations,
local predictive sections, and sheaf-style gluing.

The emphasis is on a buildable Lean approximation of the chapter's central
assertions:

- predictive state is determined by probabilities of future tests;
- local test families can separate hidden states;
- overlap mismatches define a predictive obstruction;
- in the single-context case the obstruction vanishes automatically.

## References
- Mahadevan, *Categories for AGI*, chapter
  "Predictive State Representations in a Topos"
-/


open CategoryTheory
open scoped BigOperators

universe u v w

/-- A predictive-state presheaf over a context category. We keep the codomain
    as `Type` to match the lightweight style used elsewhere in this repository. -/
abbrev PredictiveStatePresheaf (C : Type u) [Category C] := Cᵒᵖ ⥤ Type v

/-- A predictive-state model assigns to each test and hidden state its
    predictive probability. -/
structure PredictiveStateModel (Test : Type u) (State : Type v) where
  prob : Test → State → ℝ

/-- The predictive profile of a hidden state is the function assigning each
    test its predictive probability. -/
def predictiveProfile {Test : Type u} {State : Type v}
    (M : PredictiveStateModel Test State) (x : State) : Test → ℝ :=
  fun τ => M.prob τ x

/-- Local test families separate hidden states when distinct reachable states
    induce different predictive profiles. -/
def SeparatesStates {Test : Type u} {State : Type v}
    (M : PredictiveStateModel Test State) : Prop :=
  ∀ x y : State, x ≠ y → ∃ τ : Test, M.prob τ x ≠ M.prob τ y

/-- Separation implies injectivity of the predictive profile map. This is the
    local reconstruction content of the PSR chapter. -/
theorem predictiveProfile_injective {Test : Type u} {State : Type v}
    {M : PredictiveStateModel Test State} (hsep : SeparatesStates M) :
    Function.Injective (predictiveProfile M) := by
  intro x y hxy
  by_contra hne
  rcases hsep x y hne with ⟨τ, hτ⟩
  exact hτ (congrArg (fun f => f τ) hxy)

/-- A finite family of core tests that is sufficient to distinguish hidden
    states. This packages the chapter's "finite predictive rank/core tests"
    idea in a Lean-friendly form. -/
structure FiniteCoreTests {Test : Type u} {State : Type v} [DecidableEq Test]
    (M : PredictiveStateModel Test State) where
  core : Finset Test
  separates_on_core :
    ∀ {x y : State},
      (∀ τ : Test, τ ∈ core → M.prob τ x = M.prob τ y) → x = y

/-- A simplified sheaf-style cover of predictive sections over contexts.
    The codomain `V` is a common additive space on which overlap mismatches are
    compared. -/
structure PredictiveCover (ι : Type u) (V : Type v) [AddCommGroup V] where
  restrict : ι → ι → V → V

/-- Overlap mismatch between two local predictive sections. -/
def overlapMismatch {ι : Type u} {V : Type v} [AddCommGroup V]
    (cover : PredictiveCover ι V) (s : ι → V) (i j : ι) : V :=
  cover.restrict i j (s i) - cover.restrict j i (s j)

/-- A global predictive section is an element whose restrictions agree with all
    local sections on overlaps. -/
def HasGlobalSection {ι : Type u} {V : Type v} [AddCommGroup V]
    (cover : PredictiveCover ι V) (s : ι → V) : Prop :=
  ∃ g : V, ∀ i j : ι, cover.restrict i j (s i) = g

/-- Global agreement forces every pairwise overlap mismatch to vanish. -/
theorem overlapMismatch_eq_zero_of_globalSection {ι : Type u} {V : Type v}
    [AddCommGroup V] (cover : PredictiveCover ι V) (s : ι → V)
    (hglobal : HasGlobalSection cover s) (i j : ι) :
    overlapMismatch cover s i j = 0 := by
  rcases hglobal with ⟨g, hg⟩
  dsimp [overlapMismatch]
  rw [hg i j, hg j i, sub_self]

/-- A predictive obstruction class is a cocycle of overlap mismatches. -/
structure PredictiveObstructionClass {ι : Type u} {V : Type v}
    [AddCommGroup V] (δ : ι → ι → V) where
  cocycle : ∀ i j k : ι, δ i j + δ j k + δ k i = 0

/-- A norm-based predictive obstruction index. This is a computable proxy for
    the size of the mismatch cocycle. -/
def obstructionIndex {ι : Type u} {V : Type v} [Fintype ι] [NormedAddCommGroup V]
    (cover : PredictiveCover ι V) (s : ι → V) : ℝ :=
  ∑ i, ∑ j, ‖overlapMismatch cover s i j‖

theorem obstructionIndex_nonneg {ι : Type u} {V : Type v} [Fintype ι]
    [NormedAddCommGroup V] (cover : PredictiveCover ι V) (s : ι → V) :
    0 ≤ obstructionIndex cover s := by
  unfold obstructionIndex
  refine Finset.sum_nonneg ?_
  intro i hi
  refine Finset.sum_nonneg ?_
  intro j hj
  exact norm_nonneg _

/-- In the classical single-context PSR setting there are no nontrivial
    overlaps, so the predictive obstruction is automatically zero. -/
theorem classical_psr_special_case {ι : Type u} {V : Type v} [Unique ι]
    [AddCommGroup V] (cover : PredictiveCover ι V) (s : ι → V) (i j : ι) :
    overlapMismatch cover s i j = 0 := by
  have hij : i = j := Subsingleton.elim _ _
  subst hij
  dsimp [overlapMismatch]
  rw [sub_self]

/-!
## Status

| Item | Description | Status |
|------|-------------|--------|
| Def  | Predictive-state presheaf | ✅ `PredictiveStatePresheaf` |
| Def  | Predictive state model | ✅ `PredictiveStateModel` |
| Thm  | Local reconstruction via separating tests | ✅ `predictiveProfile_injective` |
| Def  | Finite core tests | ✅ `FiniteCoreTests` |
| Def  | Predictive cover / local sections | ✅ `PredictiveCover` |
| Def  | Predictive obstruction / overlap mismatch | ✅ `overlapMismatch` / `PredictiveObstructionClass` |
| Def  | Predictive obstruction index | ✅ `obstructionIndex` |
| Thm  | Global section implies zero pairwise obstruction | ✅ `overlapMismatch_eq_zero_of_globalSection` |
| Thm  | Classical PSR is the single-context special case | ✅ `classical_psr_special_case` |
-/
