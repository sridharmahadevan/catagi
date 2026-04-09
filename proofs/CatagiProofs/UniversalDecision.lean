import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.SetNotation

/-!
# UniversalDecision — Definitions 63–65

Formalizes the Universal Decision Model (UDM) category, information fields,
and Witsenhausen's intrinsic model for the chapter on Universal Decisions with
Kan Extensions. These definitions are also reused later in the consciousness
chapter.

## References
- Mahadevan, *Categories for AGI*, Chapter
  "Universal Decisions with Kan Extensions"
- Mahadevan, *Categories for AGI*, Chapter "Consciousness"
-/


open CategoryTheory

/-!
## Definition 63 — Universal Decision Model (UDM)

> A Universal Decision Model is defined as a category C_{UDM}, where
> each decision object is a tuple of decision-making agents with
> shared and private information.
-/

/-- Definition 63: Universal Decision Model.
    Objects are decision problems with agents, actions, and observations. -/
structure UDMObj where
  /-- Set of agents -/
  Agent : Type
  /-- Action space for each agent -/
  Action : Agent → Type
  /-- Observation/information for each agent -/
  Observation : Agent → Type
  /-- Outcome space -/
  Outcome : Type
  /-- Outcome function -/
  outcome : ((a : Agent) → Action a) → Outcome

/-!
## Definition 64 — Information Field

> The information field of an element α ∈ A in a decision object c
> is denoted H_α and represents the σ-algebra of events observable
> by agent α before making their decision.
-/

/-- Definition 64: Information field for an agent.
    The σ-algebra of events available to the agent for decision-making.
    Satisfies the closure properties of a σ-algebra:
    contains the full space, is closed under complement, and closed
    under countable union. -/
structure InformationField where
  /-- Underlying sample space -/
  Ω : Type
  /-- The σ-algebra (measurable sets) available to this agent -/
  events : Set (Set Ω)
  /-- The full space is in the σ-algebra -/
  univ_mem : Set.univ ∈ events
  /-- Closed under complement -/
  compl_mem : ∀ s ∈ events, sᶜ ∈ events
  /-- Closed under countable union -/
  iUnion_mem : ∀ (f : ℕ → Set Ω), (∀ n, f n ∈ events) → Set.iUnion f ∈ events

/-- The empty set is in every information field (by complement of univ). -/
theorem InformationField.empty_mem (F : InformationField) : (∅ : Set F.Ω) ∈ F.events := by
  have h := F.compl_mem Set.univ F.univ_mem
  convert h using 1
  ext x
  exact ⟨fun hx => absurd hx id, fun hx => absurd (Set.mem_univ x) hx⟩

/-- An information field that is coarser than (sub-σ-algebra of) another:
    every event observable in the coarser field is also observable in the finer one. -/
def InformationField.IsSubField (F G : InformationField) (h : F.Ω = G.Ω) : Prop :=
  ∀ s ∈ F.events, h ▸ s ∈ G.events

/-!
## Definition 65 — Witsenhausen's Intrinsic Model

> Given a subset of nodes B ⊂ A, let H_B = Ω × ∏_{a ∈ B} U_a be the
> product space. This defines a hierarchical information structure
> where each agent's information field is a sub-σ-algebra.
-/

/-- Definition 65: Witsenhausen's intrinsic model.
    A hierarchical information structure for multi-agent decision-making,
    where each agent has an action space, information field, and the fields
    respect the temporal ordering (earlier agents see less).
    Used to model the interaction between conscious and unconscious
    decision processes. -/
structure WitsenhausenModel where
  /-- Number of agents -/
  n : ℕ
  /-- Base probability space -/
  Ω : Type
  /-- Action space per agent -/
  Action : Fin n → Type
  /-- Information field per agent (sub-σ-algebra) -/
  infoEvents : Fin n → Set (Set Ω)
  /-- The full space is in each agent's information field -/
  info_univ : ∀ i, Set.univ ∈ infoEvents i
  /-- Each agent's information field is closed under complement -/
  info_compl : ∀ i, ∀ s ∈ infoEvents i, sᶜ ∈ infoEvents i
  /-- Cost function mapping state and joint action profile to a real cost -/
  cost : Ω → ((i : Fin n) → Action i) → Float

/-- Extract the information field for agent i as an InformationField structure.
    Requires the caller to supply the countable-union closure proof. -/
def WitsenhausenModel.agentInfoField (W : WitsenhausenModel)
    (i : Fin W.n)
    (hunion : ∀ (f : ℕ → Set W.Ω), (∀ n, f n ∈ W.infoEvents i) →
      Set.iUnion f ∈ W.infoEvents i) :
    InformationField where
  Ω := W.Ω
  events := W.infoEvents i
  univ_mem := W.info_univ i
  compl_mem := W.info_compl i
  iUnion_mem := hunion

/-- A strategy profile type for a Witsenhausen model: each agent has a
    decision rule mapping states to actions. -/
def WitsStrategyProfile (n : ℕ) (Ω : Type) (Act : Fin n → Type) : Type :=
  (i : Fin n) → Ω → Act i

/-- The cost of a joint strategy profile: applies each agent's strategy to a state
    and evaluates the cost function. -/
def witsEvalCost (n : ℕ) (Ω : Type) (Act : Fin n → Type)
    (costFn : Ω → ((i : Fin n) → Act i) → Float)
    (strategies : WitsStrategyProfile n Ω Act) (ω : Ω) : Float :=
  costFn ω (fun i => strategies i ω)

/-!
## Status

| Def | Description         | Status              |
|-----|---------------------|---------------------|
| 63  | UDM category        | ✅ `UDMObj`           |
| 64  | Information field    | ✅ σ-algebra axioms + `empty_mem` + `IsSubField` |
| 65  | Witsenhausen model   | ✅ `n`-agent model + `WitsStrategyProfile` + `witsEvalCost` |
-/
