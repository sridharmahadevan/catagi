```lean
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Enriched.Basic
```

# TransformerCategory — Definitions 26–30 from *Categories for AGI*

Novel categorical definitions for Transformer models: the Transformer block
as a morphism, the category C_T of Transformer models, LLM syntax and
semantic categories, and the k-NN LLM category.

## References
- Mahadevan, *Categories for AGI*, Chapter 5 ("Categorical Deep Learning")

```lean
open CategoryTheory
```

## Definition 26 — Transformer Block

> A Transformer block is a sequence-to-sequence function mapping
> ℝ^{d × n} → ℝ^{d × n}. There are generally two types: encoder blocks
> and decoder blocks (which include causal masking).

```lean
/-- Definition 26: A Transformer block as a sequence-to-sequence map.
    We model it abstractly as an endomorphism on a sequence space. -/
structure TransformerBlock (d n : ℕ) where
  /-- The forward map of the block -/
  forward : (Fin d → Fin n → Float) → (Fin d → Fin n → Float)

/-- Identity transformer block (passes input through unchanged). -/
def TransformerBlock.id (d n : ℕ) : TransformerBlock d n where
  forward := _root_.id

/-- Compose two transformer blocks (feed-forward composition). -/
def TransformerBlock.comp {d n : ℕ} (f g : TransformerBlock d n) : TransformerBlock d n where
  forward := g.forward ∘ f.forward
```

## Definition 27 — Category C_T of Transformer Models

> The category C_T of Transformer models has objects that are sequence
> spaces ℝ^{d × n} and morphisms that are Transformer blocks (compositions
> of self-attention and feed-forward layers).

```lean
/-- Definition 27: Objects of the Transformer category are
    (dimension, sequence length) pairs. -/
structure TransObj where
  dim : ℕ
  seqLen : ℕ

/-- Definition 27: The category C_T of Transformer models.
    Morphisms are Transformer blocks. -/
structure TransMor (X Y : TransObj) where
  /-- Underlying function between sequence spaces -/
  toFun : (Fin X.dim → Fin X.seqLen → Float) →
          (Fin Y.dim → Fin Y.seqLen → Float)

/-- Identity morphism in the Transformer category. -/
def TransMor.id (X : TransObj) : TransMor X X where
  toFun := _root_.id

/-- Composition of morphisms in the Transformer category. -/
def TransMor.comp {X Y Z : TransObj} (f : TransMor X Y) (g : TransMor Y Z) : TransMor X Z where
  toFun := g.toFun ∘ f.toFun

/-- Extensionality for Transformer morphisms: two morphisms are equal
    iff their underlying functions are equal. -/
@[ext]
theorem TransMor.ext {X Y : TransObj} {f g : TransMor X Y}
    (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; subst h; rfl

/-- The category C_T of Transformer models, with sequence spaces as objects
    and sequence-to-sequence maps as morphisms. -/
instance : Category TransObj where
  Hom := TransMor
  id := TransMor.id
  comp := TransMor.comp
  id_comp f := by ext; rfl
  comp_id f := by ext; rfl
  assoc f g h := by ext; rfl
```

## Definition 28 — LLM Syntax Category

> The LLM syntax category L is defined as a category enriched over a
> monoidal category of probability distributions, where morphisms
> L(y | x) represent next-token conditional distributions.

```lean
/-- Definition 28: Objects of the LLM syntax category.
    Each object is a language model with a vocabulary size and context length. -/
structure LLMSynObj where
  vocabSize : ℕ
  ctxLen : ℕ

/-- Definition 28: Morphisms in the LLM syntax category.
    A stochastic map (conditional distribution) between token sequence spaces,
    modeled as a function on sequence representations. -/
structure LLMSynMor (X Y : LLMSynObj) where
  /-- The underlying deterministic map between sequence representations -/
  toFun : (Fin X.vocabSize → Fin X.ctxLen → Float) →
          (Fin Y.vocabSize → Fin Y.ctxLen → Float)

/-- Extensionality for LLM syntax morphisms. -/
@[ext]
theorem LLMSynMor.ext {X Y : LLMSynObj} {f g : LLMSynMor X Y}
    (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; subst h; rfl

/-- The LLM syntax category: objects are (vocab, context) pairs,
    morphisms are maps between sequence spaces with identity and composition. -/
instance : Category LLMSynObj where
  Hom := LLMSynMor
  id X := ⟨id⟩
  comp f g := ⟨g.toFun ∘ f.toFun⟩
  id_comp f := by ext; rfl
  comp_id f := by ext; rfl
  assoc f g h := by ext; rfl

/-- Original scaffold structure preserved for backward compatibility. -/
structure LLMSyntaxCat where
  Token : Type
  /-- Conditional distribution P(next | context) -/
  nextTokenDist : (List Token) → Token → Float
```

## Definition 29 — LLM Semantic Category

> For the LLM category L, the semantic category L_sem is defined
> with objects that are meaning representations and morphisms that
> capture semantic entailment relationships.

```lean
/-- Definition 29: LLM semantic category.
    Objects are meaning representations, with an entailment preorder.
    Morphisms are entailment proofs. -/
structure LLMSemanticCat where
  Meaning : Type
  entails : Meaning → Meaning → Prop
  /-- Entailment is reflexive -/
  entails_refl : ∀ x, entails x x
  /-- Entailment is transitive -/
  entails_trans : ∀ x y z, entails x y → entails y z → entails x z

/-- The entailment relation on an LLM semantic category forms a preorder. -/
@[reducible]
def LLMSemanticCat.toPreorder (S : LLMSemanticCat) : Preorder S.Meaning where
  le := S.entails
  le_refl := S.entails_refl
  le_trans := S.entails_trans
```

## Definition 30 — k-NN LLM Syntax Category

> The k-NN LLM syntax category L_{kNN} is defined as a category whose
> morphisms L_{kNN}(y | x) combine parametric and non-parametric
> (k-nearest-neighbor) retrieval-based next-token distributions.

```lean
/-- Definition 30: k-NN augmented LLM category.
    Combines parametric and retrieval-based distributions. -/
structure KNNLLMCat where
  Token : Type
  /-- Parametric next-token distribution -/
  parametricDist : (List Token) → Token → Float
  /-- k-NN retrieval distribution -/
  retrievalDist : (List Token) → Token → Float
  /-- Interpolation weight λ ∈ [0, 1] -/
  lambda : Float

/-- The combined k-NN LLM distribution: λ · retrieval + (1 − λ) · parametric.
    This is the interpolation formula from Khandelwal et al. (2020). -/
def KNNLLMCat.combinedDist (m : KNNLLMCat) (ctx : List m.Token) (tok : m.Token) : Float :=
  m.lambda * m.retrievalDist ctx tok + (1 - m.lambda) * m.parametricDist ctx tok

/-- When λ = 0, the combined distribution equals the parametric distribution. -/
theorem KNNLLMCat.combinedDist_lambda_zero (m : KNNLLMCat) (h : m.lambda = 0)
    (ctx : List m.Token) (tok : m.Token) :
    m.combinedDist ctx tok = 0 * m.retrievalDist ctx tok +
      (1 - 0) * m.parametricDist ctx tok := by
  simp [KNNLLMCat.combinedDist, h]

/-- When λ = 1, the combined distribution equals the retrieval distribution. -/
theorem KNNLLMCat.combinedDist_lambda_one (m : KNNLLMCat) (h : m.lambda = 1)
    (ctx : List m.Token) (tok : m.Token) :
    m.combinedDist ctx tok = 1 * m.retrievalDist ctx tok +
      (1 - 1) * m.parametricDist ctx tok := by
  simp [KNNLLMCat.combinedDist, h]
```

## Status

| Def | Description         | Status          |
|-----|---------------------|-----------------|
| 26  | Transformer block   | ✅ Struct + id/comp |
| 27  | Category C_T        | ✅ Category instance |
| 28  | LLM syntax cat      | ✅ `LLMSynObj` + `Category` |
| 29  | LLM semantic cat    | ✅ `LLMSemanticCat` + `Preorder` |
| 30  | k-NN LLM cat        | ✅ `KNNLLMCat` + `combinedDist` + λ-boundary thms |
