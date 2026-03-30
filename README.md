# Categories for AGI — Lean 4 Formalization

Formal verification in [Lean 4](https://lean-lang.org/) + [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) of the categorical and mathematical claims from:

> **Sridhar Mahadevan**, *Categories for AI: An Introduction to Category Theory with Applications to Artificial General Intelligence*, UMass CMPSCI 692CT.

## Overview

This project formalizes covered definitions, theorems, lemmas, and examples
from the book as machine-checked Lean 4 artifacts. The current coverage includes
the original core chapters together with newer extensions for:

- **Chapter 21: Predictive State Representations in a Topos** — together with the BASKET/ROCKET workflow sections, covering local predictive sections, obstruction-style gluing, and operational reranking
- **Chapter 23 / Chapter 24: Universal RL / Deep URL** — coalgebraic RL abstractions, Bellman operators, structural losses, and hypothesis restriction
- **Chapter 20: TCM-DB (Mapping Documents into Topos Causal Model Databases)** — currently represented through the existing `ToposCausal`, `GrothendieckSite`, and `CausalFunctors` formalizations rather than a separate Lean chapter module
- the previously covered foundations: categories, functors, adjunctions, Kan extensions, toposes, causal models, coalgebras, transformers, and consciousness

**Zero `sorry`** — every proof obligation is discharged.

## Project Structure

```
proofs/
├── lakefile.lean              # Lean 4 project config (Mathlib dependency)
├── lean-toolchain             # leanprover/lean4:v4.29.0-rc6
├── CatagiProofs.lean          # Root import (all 25 modules)
├── CatagiProofs/
│   ├── BasicCategory.lean     # Defs 1-5: Categories, morphisms, isomorphisms
│   ├── Functors.lean          # Defs 6-10: Functors, natural transformations, Yoneda
│   ├── AdjointFunctors.lean   # Defs 11-14, Thms 3-8: Adjunctions, RAPL/LAPC
│   ├── Diagrams.lean          # Defs 15-22, Thm 2, Exs 5-7: Limits, Kan extensions
│   ├── MonoidalEnriched.lean  # Defs 23-27: Monoidal and enriched categories
│   ├── YonedaAttention.lean   # Attention as enriched Yoneda (structural analogy)
│   ├── SimplicialSets.lean    # Defs 31-33: Simplicial sets, horns, boundaries
│   ├── LiftingProblems.lean   # Defs 34-36, Exs 13-14: Lifting, weak factorization
│   ├── GrothendieckSite.lean  # Defs 46-49: Sieves, topologies, subobject classifier
│   ├── ToposCausal.lean       # Defs 37-40, Thms 9-11: Topos causal models
│   ├── CausalFunctors.lean    # Defs 42-50, Thms 12-16: Causal functors, Kan
│   ├── CausalDensity.lean     # Thm 18: Radon-Nikodym / Kan duality
│   ├── DoCalculus.lean        # Defs 51-56: SCM, do-calculus, counterfactuals
│   ├── JudoCalculus.lean      # Thm 17: j-do calculus, Grothendieck closure
│   ├── BasketRocket.lean      # BASKET/ROCKET: operational plans, reranking, normalization
│   ├── PredictiveStateTopos.lean # PSR in a topos: local tests, gluing, obstruction
│   ├── Coalgebras.lean        # Defs 57-58: F-coalgebras, bisimulation
│   ├── LearnCategory.lean     # Defs 59-61: Learn/Param categories (quotient types)
│   ├── TransformerCategory.lean # Defs 28-30: Transformer & LLM categories
│   ├── DynamicCompositionality.lean # Def 41: Commutator energy, Čech obstruction
│   ├── CommutatorBounds.lean  # Lemmas 1-4: Commutator bounds
│   ├── ToposConsciousness.lean # Thm 19, Def 62: Topos consciousness, Mitchell-Bénabou
│   ├── UniversalDecision.lean # Defs 63-65: Universal decision models, Witsenhausen
│   ├── UniversalRL.lean       # URL: MDPs, Bellman operators, final coalgebra witnesses
│   └── DeepURL.lean           # Deep URL: structural losses, residuals, hypothesis restriction
└── docs/
    ├── CatagiProofs.md        # Combined Markdown documentation
    ├── CatagiProofs.html      # HTML with table of contents
    ├── CatagiProofs.pdf       # PDF via LuaLaTeX
	    └── md/                    # Individual module docs
```

## Building

### Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean version manager)

### Build

```bash
cd proofs
lake exe cache get    # Download pre-built Mathlib (recommended, ~10 min first time)
lake build            # Build all 25 modules
```

### Verify zero sorry

```bash
grep -rn 'sorry' proofs/CatagiProofs/ --include='*.lean' | grep -v '\-\-' | grep -v '/\-'
# Should return nothing
```

## Documentation

Pre-built docs are in `proofs/docs/`:

| Format | File | Size |
|--------|------|------|
| Markdown | [`CatagiProofs.md`](proofs/docs/CatagiProofs.md) | 124 KB |
| HTML | [`CatagiProofs.html`](proofs/docs/CatagiProofs.html) | 168 KB |
| PDF | [`CatagiProofs.pdf`](proofs/docs/CatagiProofs.pdf) | 260 KB |

To regenerate:

```bash
cd proofs
lake exe mdgen CatagiProofs docs/md    # Generate per-module markdown
# Then use pandoc for HTML/PDF
```

## Key Technical Decisions

- **LearnCategory**: Uses quotient types with `Equiv.punitProd`/`Equiv.prodPUnit`/`Equiv.prodAssoc` to handle the `Unit × P ≅ P` isomorphism needed for category axioms
- **ToposCausal**: TCM/SCM category instances with `HasFiniteLimits` proved via terminal + pullbacks
- **CausalFunctors**: Kan extensions via `yoneda.lan`, Heyting implication on sieves
- **Subobject classifier**: Explicit `Cᵒᵖ ⥤ Type` functor via `Sieve` + `Sieve.pullback`
- **DynamicCompositionality**: Proved properties (nonneg, symmetry, zero ↔ commutativity)
- **BasketRocket**: Finite-poset operational plans, reward-maximizing reranking, normalization operators
- **PredictiveStateTopos**: Predictive profiles, separating test families, overlap obstructions, single-context PSR reduction
- **UniversalRL**: Markov chains, MDPs, Bellman fixed points, asynchronous box invariants, final coalgebra witnesses
- **DeepURL**: GT/DB-style structural loss, total loss decomposition, structural hypothesis restriction

## TCM-DB Status

The new book **Chapter 20** on **Mapping Documents into Topos Causal Model Databases
(TCM-DB)** does not yet have a dedicated Lean module. Its current formal
footprint is distributed across:

- `ToposCausal.lean` for TCM objects and finite-limit structure
- `GrothendieckSite.lean` for sieves, Grothendieck topologies, and subobject-classifier semantics
- `CausalFunctors.lean` for causal functors, Kan extensions, and internal Heyting-style logic

The recent FunctorFlow/cSQL case studies therefore remain expository examples
in the manuscript, while their topos-theoretic categorical core is already
reflected in the existing Lean formalization.

## License

[MIT](LICENSE)
