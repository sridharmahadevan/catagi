import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# DynamicCompositionality — Definition 41

Formalizes dynamic compositionality, commutator energy,
and the Čech-style obstruction proxy.

## References
- Mahadevan, *Categories for AGI*, Chapter 8 ("Dynamic Compositionality")
-/


/-!
## Definition 41 — Dynamic Compositionality

> Dynamic compositionality is the property that the order in which
> sub-operators (e.g., attention, feed-forward) are applied matters
> for the learned representation, and this order sensitivity can be
> measured by the commutator energy.

## Commutator Energy

> Given two operators F, G acting on a representation space,
> the commutator energy is E_comm = ‖F ∘ G − G ∘ F‖².
> This measures how much the result depends on application order.
-/

/-- Commutator energy of two endomorphisms on a normed space.
    E_comm(F, G, x) = ‖F(G(x)) − G(F(x))‖² -/
noncomputable def commutatorEnergy {V : Type*} [NormedAddCommGroup V]
    (F G : V → V) (x : V) : ℝ :=
  ‖F (G x) - G (F x)‖ ^ 2

/-- Commutator energy is non-negative (it is a squared norm). -/
theorem commutatorEnergy_nonneg {V : Type*} [NormedAddCommGroup V]
    (F G : V → V) (x : V) : 0 ≤ commutatorEnergy F G x :=
  sq_nonneg _

/-- Commutator energy is symmetric in F and G: swapping the operators
    does not change the energy, since ‖a − b‖ = ‖b − a‖. -/
theorem commutatorEnergy_symm {V : Type*} [NormedAddCommGroup V]
    (F G : V → V) (x : V) : commutatorEnergy F G x = commutatorEnergy G F x := by
  simp only [commutatorEnergy, norm_sub_rev]

/-- Commuting operators have zero commutator energy. -/
theorem commutatorEnergy_comm_zero {V : Type*} [NormedAddCommGroup V]
    (F G : V → V) (x : V) (h : F (G x) = G (F x)) : commutatorEnergy F G x = 0 := by
  simp [commutatorEnergy, h]

/-- Zero commutator energy implies the operators commute at that point. -/
theorem commutatorEnergy_zero_comm {V : Type*} [NormedAddCommGroup V]
    (F G : V → V) (x : V) (h : commutatorEnergy F G x = 0) : F (G x) = G (F x) := by
  simp only [commutatorEnergy] at h
  have h1 : ‖F (G x) - G (F x)‖ = 0 := by
    nlinarith [norm_nonneg (F (G x) - G (F x))]
  rwa [norm_eq_zero, sub_eq_zero] at h1

/-- Expected commutator energy over a distribution.
    E[E_comm] = E_x[‖F(G(x)) − G(F(x))‖²] -/
noncomputable def expectedCommutatorEnergy {V : Type*} [NormedAddCommGroup V]
    [MeasurableSpace V] (F G : V → V) (μ : MeasureTheory.Measure V) : ℝ :=
  ∫ x, commutatorEnergy F G x ∂μ

/-!
## Čech-Style Obstruction Proxy

> The Čech obstruction proxy measures the failure of a diagram of
> sub-operators to commute, by comparing different composition paths.
> High obstruction = high order sensitivity = poor dynamic compositionality.
-/

/-- Čech obstruction proxy for a triangle of operators.
    Measures ‖h − g ∘ f‖ for a triangle f : A → B, g : B → C, h : A → C. -/
noncomputable def cechObstruction {V : Type*} [NormedAddCommGroup V]
    (f g h : V → V) (x : V) : ℝ :=
  ‖h x - g (f x)‖ ^ 2

/-- The Čech obstruction is non-negative (it is a squared norm). -/
theorem cechObstruction_nonneg {V : Type*} [NormedAddCommGroup V]
    (f g h : V → V) (x : V) : 0 ≤ cechObstruction f g h x :=
  sq_nonneg _

/-- The Čech obstruction is zero if and only if the triangle commutes. -/
theorem cechObstruction_zero_iff {V : Type*} [NormedAddCommGroup V]
    (f g h : V → V) (x : V) : cechObstruction f g h x = 0 ↔ h x = g (f x) := by
  simp only [cechObstruction]
  constructor
  · intro heq
    have h1 : ‖h x - g (f x)‖ = 0 := by
      nlinarith [norm_nonneg (h x - g (f x))]
    rwa [norm_eq_zero, sub_eq_zero] at h1
  · intro heq
    simp [heq]

/-- Commutator energy is a special case of the Čech obstruction where the
    triangle is `f = F`, `g = G`, `h = F ∘ G`. -/
theorem commutatorEnergy_eq_cechObstruction {V : Type*} [NormedAddCommGroup V]
    (F G : V → V) (x : V) :
    commutatorEnergy F G x = cechObstruction F G (F ∘ G) x := by
  rfl

/-!
## Definition 41 — `DynamicallyCompositional`

A system of operators is *dynamically compositional* when the commutator
energy between every pair of its component operators is bounded by a
given tolerance `ε ≥ 0`.  When `ε = 0` the operators pairwise commute.
-/

/-- A family of operators indexed by `ι` is dynamically compositional
    with tolerance `ε` when every pair has commutator energy at most `ε`
    at every point. -/
def DynamicallyCompositional {V : Type*} [NormedAddCommGroup V]
    {ι : Type*} (ops : ι → V → V) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∀ (i j : ι) (x : V), commutatorEnergy (ops i) (ops j) x ≤ ε

/-- If operators are dynamically compositional with tolerance 0,
    then every pair of operators commutes at every point. -/
theorem DynamicallyCompositional.comm_of_zero {V : Type*} [NormedAddCommGroup V]
    {ι : Type*} {ops : ι → V → V}
    (h : DynamicallyCompositional ops 0) (i j : ι) (x : V) :
    (ops i) ((ops j) x) = (ops j) ((ops i) x) := by
  have hle := h.2 i j x
  have hnn := commutatorEnergy_nonneg (ops i) (ops j) x
  exact commutatorEnergy_zero_comm _ _ _ (le_antisymm hle hnn)

/-!
## Status

| Item   | Description                     | Status                                |
|--------|---------------------------------|---------------------------------------|
| Def 41 | `DynamicallyCompositional`      | ✅ Formalized                          |
| —      | Commutator energy               | ✅ `commutatorEnergy`                  |
| —      | Non-negativity                  | ✅ `commutatorEnergy_nonneg`           |
| —      | Symmetry in F, G               | ✅ `commutatorEnergy_symm`             |
| —      | Commuting ⇒ zero               | ✅ `commutatorEnergy_comm_zero`        |
| —      | Zero ⇒ commuting               | ✅ `commutatorEnergy_zero_comm`        |
| —      | Expected E_comm                 | ✅ `expectedCommutatorEnergy`          |
| —      | Čech obstruction proxy          | ✅ `cechObstruction`                   |
| —      | Čech non-negativity             | ✅ `cechObstruction_nonneg`            |
| —      | Čech zero iff commutes          | ✅ `cechObstruction_zero_iff`          |
| —      | E_comm as Čech obstruction      | ✅ `commutatorEnergy_eq_cechObstruction` |
| —      | Zero tolerance ⇒ commuting     | ✅ `DynamicallyCompositional.comm_of_zero` |
-/
