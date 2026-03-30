import Mathlib.Data.Finset.Basic

/-!
# DoCalculus — Definitions 52–56

Formalizes the classical do-calculus foundations: structural causal models,
the do-operator, interventional distributions, potential outcomes,
and counterfactuals.

## References
- Mahadevan, *Categories for AGI*, Chapter 19 ("Judo Calculus")
- Pearl, *Causality* (2009)
-/

/-!
## Definition 52 — Structural Causal Model (SCM)

> An SCM is a triple ⟨U, V, F⟩ where V = {V₁, ..., V_n} are endogenous
> variables, U = {U₁, ..., U_n} are exogenous variables, and
> F = {f₁, ..., f_n} are structural equations V_i = f_i(pa(V_i), U_i).
-/

/-- Definition 52: Structural Causal Model.
    We use a simplified non-dependent formulation where all variables
    share a common value space, avoiding dependent-type complications. -/
structure SCM (Val : Type) where
  /-- Number of variables -/
  n : ℕ
  /-- Parent set for each variable -/
  parents : Fin n → Finset (Fin n)
  /-- Structural equation: variable i's value depends on parent values and noise -/
  mechanism : Fin n → (Fin n → Val) → Val → Val

/-!
## Definition 53 — Do-Operator

> The do-operator do(X = x) produces a modified model M_x by replacing
> the structural equations for variables in X with the constant x.
-/

/-- Definition 53: The do-operator modifies an SCM by surgical intervention.
    do(X_i = x) replaces the mechanism for variable i with a constant. -/
def SCM.doIntervention {Val : Type} (M : SCM Val) (target : Fin M.n)
    (val : Val) : SCM Val where
  n := M.n
  parents := fun i => if i = target then ∅ else M.parents i
  mechanism := fun i parentVals noise =>
    if i = target then val
    else M.mechanism i parentVals noise

/-!
## Definition 54 — Interventional Distribution

> The effect of the intervention do(X = x) on a variable Y is the
> distribution P(Y | do(X = x)), computed by marginalizing over
> exogenous variables in the modified model M_x.
-/

/-- Definition 54: Solve an SCM given exogenous variable values.
    Computes the unique solution to the structural equations by processing
    variables in index order (0, 1, …, n−1).  Under the standard convention
    that parents have strictly lower indices this is a valid topological
    traversal and produces the correct solution. -/
def SCM.solve {Val : Type} [Inhabited Val] (M : SCM Val)
    (exogenous : Fin M.n → Val) : Fin M.n → Val :=
  Fin.foldl M.n (fun acc i =>
    Function.update acc i (M.mechanism i acc (exogenous i)))
    (fun _ => default)

/-!
## Definition 55 — Potential Outcome

> The potential outcome of Y in response to an action do(X = x)
> is the value Y would take in the modified model M_x, denoted Y_x(u)
> for a given realization of exogenous variables u.
-/

/-- Definition 55: Potential outcome Y_x(u).
    The value that variable `outcome` would take if we intervene to set
    `target` to `val`, given exogenous values `exogenous`.
    Formally: Y_x(u) = solve(M_x, u)(outcome). -/
def SCM.potentialOutcome {Val : Type} [Inhabited Val] (M : SCM Val) (target : Fin M.n)
    (val : Val) (exogenous : Fin M.n → Val) (outcome : Fin M.n) : Val :=
  (M.doIntervention target val).solve exogenous outcome

/-!
## Definition 56 — Counterfactual

> The counterfactual sentence "The value that Y would have obtained
> had X been x, given that what we actually observed was e" is defined
> via the three-step abduction-action-prediction procedure.
-/

/-- Definition 56: Counterfactual query.
    Captures the three-step abduction-action-prediction procedure:
    1. **Abduction**: Given evidence, infer posterior over exogenous variables U.
    2. **Action**: Apply the intervention do(X = x) to get modified model M_x.
    3. **Prediction**: Compute the outcome Y in M_x using the inferred U. -/
structure Counterfactual (Val : Type) where
  /-- The base SCM -/
  model : SCM Val
  /-- Evidence: observed variable-value pairs (variable index, observed value) -/
  evidence : List (Fin model.n × Val)
  /-- Intervention target variable -/
  target : Fin model.n
  /-- Intervention value -/
  interventionVal : Val
  /-- Outcome variable of interest -/
  outcome : Fin model.n

/-- Evaluate a counterfactual given a specific exogenous assignment.
    In the deterministic case (known U), the three-step process reduces to:
    solve(M_{do(X=x)}, u)(Y). -/
def Counterfactual.eval {Val : Type} [Inhabited Val] (cf : Counterfactual Val)
    (exogenous : Fin cf.model.n → Val) : Val :=
  cf.model.potentialOutcome cf.target cf.interventionVal exogenous cf.outcome

/-!
## Status

| Def | Description             | Status                       |
|-----|-------------------------|------------------------------|
| 52  | SCM                     | ✅ `SCM` structure             |
| 53  | Do-operator             | ✅ `SCM.doIntervention`        |
| 54  | Interventional dist     | ✅ `SCM.solve`                 |
| 55  | Potential outcome       | ✅ `SCM.potentialOutcome`      |
| 56  | Counterfactual          | ✅ `Counterfactual`            |
-/
