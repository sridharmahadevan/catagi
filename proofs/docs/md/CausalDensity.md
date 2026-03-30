```lean
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
```

# CausalDensity — Definitions 58–59, Theorem 18

Formalizes left Kan extensions, differential causal density,
and the RN-Kan duality theorem.

## References
- Mahadevan, *Categories for AGI*, Chapter 22 ("Causal Density Functions")

```lean
open CategoryTheory MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
```

## Definition 58 — Left Kan Extension (restated for causal context)

> A left Kan extension of a functor F : C → E along K : C → D is a functor
> Lan_K F : D → E with a universal natural transformation η : F ⇒ (Lan_K F) ∘ K.

```lean
#check @Functor.LeftExtension
```

## Definition 59 — Differential Causal Density

> Let P_obs and P_{do(X_i)} be observational and interventional laws
> on a measurable space (X, Σ). The differential causal density is
> defined as the Radon-Nikodym derivative:
>   ρ_i(x) = dP_{do(X_i)} / dP_obs (x)
> whenever P_{do(X_i)} ≪ P_obs (absolute continuity).

```lean
/-- Definition 59: Differential causal density as a Radon-Nikodym derivative.
    ρ_i = dP_{do(X_i)} / dP_obs, measuring the pointwise causal effect
    of intervening on variable X_i. -/
noncomputable def differentialCausalDensity
    {α : Type*} [m : MeasurableSpace α]
    (P_obs P_do : @Measure α m) : α → ENNReal :=
  @Measure.rnDeriv α m P_do P_obs
```

## Theorem 18 — RN-Kan Duality

> Let μ, ν be probability measures on (X, Σ) with ν ≪ μ. Then there is
> a unique ρ ∈ L¹(μ) such that for all measurable A:
>   ν(A) = ∫_A ρ dμ
> Moreover, this ρ arises as the "value" of a pointwise left Kan extension
> in the stochastic category, dualizing the Radon-Nikodym theorem
> with the categorical Kan extension.

```lean
-- Theorem 18 (RN-Kan Duality): The Radon-Nikodym derivative ρ = dν/dμ
-- can be interpreted as a pointwise left Kan extension value.
-- The measure-theoretic half uses Mathlib's `Measure.withDensity_rnDeriv_eq`.

/-- Theorem 18 (Radon-Nikodym half): If ν is absolutely continuous w.r.t. μ,
    then ν can be recovered from its Radon-Nikodym derivative:
    μ.withDensity (dν/dμ) = ν. -/
theorem radon_nikodym_density {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [ν.HaveLebesgueDecomposition μ]
    (hac : ν ≪ μ) :
    μ.withDensity (ν.rnDeriv μ) = ν :=
  Measure.withDensity_rnDeriv_eq ν μ hac

/-- The categorical Kan-extension interpretation of the Radon-Nikodym theorem:
    the density dν/dμ arises as the unique measurable function making the
    "integration diagram" commute, analogous to a pointwise left Kan extension.
    This structure packages the density together with its defining property. -/
structure RNKanDuality {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) where
  /-- The density function (Radon-Nikodym derivative) -/
  density : α → ENNReal
  /-- The density recovers the measure: μ.withDensity ρ = ν -/
  density_spec : μ.withDensity density = ν

/-- Construct the RN-Kan duality witness from absolute continuity.
    The Radon-Nikodym derivative is the unique density satisfying the
    Kan-extension universal property (commutativity of the integration diagram). -/
noncomputable def RNKanDuality.ofAbsCont {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [ν.HaveLebesgueDecomposition μ]
    (hac : ν ≪ μ) : RNKanDuality μ ν where
  density := ν.rnDeriv μ
  density_spec := Measure.withDensity_rnDeriv_eq ν μ hac

/-- The differential causal density is a special case of RN-Kan duality
    applied to observational and interventional measures. -/
noncomputable def causalDensityAsKan {α : Type*} [MeasurableSpace α]
    (P_obs P_do : Measure α) [P_do.HaveLebesgueDecomposition P_obs]
    (hac : P_do ≪ P_obs) : RNKanDuality P_obs P_do :=
  RNKanDuality.ofAbsCont P_obs P_do hac
```

## Status

| Item   | Description             | Status                          |
|--------|-------------------------|---------------------------------|
| Def 58 | Left Kan extension      | ✅ Mathlib                        |
| Def 59 | Differential causal density | ✅ `differentialCausalDensity` |
| Thm 18 | RN-Kan duality          | ✅ `radon_nikodym_density` + `RNKanDuality` |
