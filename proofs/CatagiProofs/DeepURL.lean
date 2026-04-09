import CatagiProofs.UniversalRL
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# DeepURL — Deep Universal RL with structural constraints

This module formalizes the later chapter on Deep URL with Geometric
Transformers and Diagrammatic Backpropagation.

The emphasis is on stable Lean abstractions for the chapter's main claims:

- latent dynamics as approximate coalgebra morphisms;
- graph/diagrammatic structural losses;
- total loss decomposition;
- structural hypothesis restriction of the GT+DB family.

## References
- Mahadevan, *Categories for AGI*, Chapter
  "Deep URL with Geometric Transformers"
-/


open scoped BigOperators

universe u v

/-- A finite transition graph used to declare structural relations in Deep URL. -/
structure TransitionGraph where
  State : Type u
  [instFintypeState : Fintype State]
  [instDecidableEqState : DecidableEq State]
  edge : State → State → Prop
  [instDecidableRelEdge : DecidableRel edge]

attribute [instance] TransitionGraph.instFintypeState
attribute [instance] TransitionGraph.instDecidableEqState
attribute [instance] TransitionGraph.instDecidableRelEdge

/-- Deep URL model: an encoder together with latent dynamics. -/
structure DeepURLModel (X : Type u) (Z : Type v) where
  encoder : X → Z
  latentDynamics : Z → Z

/-- Pointwise residual for approximate coalgebra commutation in the simplified
    endomorphic setting `γ : X → X`. -/
def coalgebraResidual {X : Type u} {Z : Type v} [Sub Z]
    (γ : X → X) (M : DeepURLModel X Z) (x : X) : Z :=
  M.latentDynamics (M.encoder x) - M.encoder (γ x)

/-- Exact commutation gives zero residual. -/
theorem coalgebraResidual_eq_zero_of_exact {X : Type u} {Z : Type v}
    [AddGroup Z] (γ : X → X) (M : DeepURLModel X Z)
    (hcomm : ∀ x, M.latentDynamics (M.encoder x) = M.encoder (γ x)) (x : X) :
    coalgebraResidual γ M x = 0 := by
  simp [coalgebraResidual, hcomm x]

/-- Graph-structured loss used by GT/DB-style objectives. We use the sum of
    pairwise norms over declared edges. -/
def structuralLoss (G : TransitionGraph) {V : Type v} [NormedAddCommGroup V]
    (h : G.State → V) : ℝ :=
  ∑ i : G.State, ∑ j : G.State, if G.edge i j then ‖h i - h j‖ else 0

/-- Structural loss is always nonnegative. -/
theorem structuralLoss_nonneg (G : TransitionGraph) {V : Type v}
    [NormedAddCommGroup V] (h : G.State → V) :
    0 ≤ structuralLoss G h := by
  unfold structuralLoss
  refine Finset.sum_nonneg ?_
  intro i hi
  refine Finset.sum_nonneg ?_
  intro j hj
  split_ifs with hedge
  · exact norm_nonneg _
  · exact le_rfl

/-- Total Deep URL objective with task, graph, and diagrammatic terms. -/
def totalLoss (taskLoss graphLoss diagramLoss wgraph wdiag : ℝ) : ℝ :=
  taskLoss + wgraph * graphLoss + wdiag * diagramLoss

/-- Nonnegative coefficients and component losses imply a nonnegative total
    objective. -/
theorem totalLoss_nonneg {taskLoss graphLoss diagramLoss wgraph wdiag : ℝ}
    (htask : 0 ≤ taskLoss) (hgraph : 0 ≤ graphLoss) (hdiag : 0 ≤ diagramLoss)
    (hwgraph : 0 ≤ wgraph) (hwdiag : 0 ≤ wdiag) :
    0 ≤ totalLoss taskLoss graphLoss diagramLoss wgraph wdiag := by
  dsimp [totalLoss]
  nlinarith

/-- Base hypothesis class of candidate Deep URL models. -/
abbrev HypothesisClass (X : Type u) (Z : Type v) := Set (DeepURLModel X Z)

/-- Constrained class obtained by imposing diagrammatic constraints. -/
def constrainedHypothesisClass {X : Type u} {Z : Type v}
    (H : HypothesisClass X Z) (C : DeepURLModel X Z → Prop) : HypothesisClass X Z :=
  {h | h ∈ H ∧ C h}

/-- The constrained class is always a subset of the unconstrained class. -/
theorem constrainedHypothesisClass_subset {X : Type u} {Z : Type v}
    (H : HypothesisClass X Z) (C : DeepURLModel X Z → Prop) :
    constrainedHypothesisClass H C ⊆ H := by
  intro h hh
  exact hh.1

/-- If the constraints rule out at least one model from `H`, then the
    GT+DB-style constrained class is a strict subset of the GT class. -/
theorem hypothesis_restriction {X : Type u} {Z : Type v}
    (H : HypothesisClass X Z) (C : DeepURLModel X Z → Prop)
    (hnonvacuous : ∃ h, h ∈ H ∧ ¬ C h) :
    constrainedHypothesisClass H C ⊂ H := by
  constructor
  · exact constrainedHypothesisClass_subset H C
  · intro hSubset
    rcases hnonvacuous with ⟨h, hhH, hhnot⟩
    have hhconstrained : h ∈ constrainedHypothesisClass H C := hSubset hhH
    exact hhnot hhconstrained.2

/-!
## Status

| Item | Description | Status |
|------|-------------|--------|
| Def  | Transition graph | ✅ `TransitionGraph` |
| Def  | Deep URL model | ✅ `DeepURLModel` |
| Def  | Coalgebra-morphism residual | ✅ `coalgebraResidual` |
| Thm  | Exact commutation implies zero residual | ✅ `coalgebraResidual_eq_zero_of_exact` |
| Def  | Structural loss | ✅ `structuralLoss` |
| Thm  | Structural loss is nonnegative | ✅ `structuralLoss_nonneg` |
| Def  | Total loss decomposition | ✅ `totalLoss` |
| Thm  | Nonnegative components imply nonnegative total loss | ✅ `totalLoss_nonneg` |
| Def  | Constrained hypothesis class | ✅ `constrainedHypothesisClass` |
| Thm  | Structural hypothesis restriction | ✅ `hypothesis_restriction` |
-/
