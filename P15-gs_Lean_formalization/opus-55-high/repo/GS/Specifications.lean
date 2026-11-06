module

public import GS.ThreeFactor
public import GS.OriginalLocalModel
public import GS.M4Necessary

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Theorem specifications -- definitions alone are not proofs

The Goal definitions specify propositions; definitions alone do not prove them.
The final two theorems link the m=4 proofs to their specifications. Extensions,
Continuation, and NonmanifoldClosure prove the other original specifications.
The public interface is `GSResults`; the scope is described in docs/RESULTS.md.
The suffix `Goal` labels a specification, not an assertion that it is proved.
-/

noncomputable section
open Matrix
namespace GS.Specifications

/-- Original m=2 equality, for actual matrices and actual permutations. -/
def TwoFactorOrthogonalizationGoal : Prop :=
  ∀ (n : ℕ) (s₁ s₂ : BlockSpec n) (σ : Equiv.Perm (Fin n)) (A : Mat n),
    InA2 s₁.size s₂.size (permMatrix σ) A ∧ Orthogonal A ↔
      InA2Orth s₁.size s₂.size (permMatrix σ) A

/-- The main arbitrary-permutation m=3 specification. -/
def ThreeFactorOrthogonalizationGoal : Prop :=
  ∀ (n : ℕ) (s₁ s₂ s₃ : BlockSpec n)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : Mat n),
    InA3 s₁.size s₂.size s₃.size (permMatrix σ₁) (permMatrix σ₂) A ∧ Orthogonal A ↔
      InA3Orth s₁.size s₂.size s₃.size (permMatrix σ₁) (permMatrix σ₂) A

/-- Structured QR existence, including all required support properties. -/
def StructuredQRGoal : Prop :=
  ∀ (n : ℕ) (s : BlockSpec n) (B : Mat n) (σ : Equiv.Perm (Fin n)),
    BlockDiagonal s.size B → IsUnit B.det →
      ∃ U R : Mat n, BlockDiagonal s.size U ∧ Orthogonal U ∧ Upper R ∧
        B * permMatrix σ = U * permMatrix σ * R

/-- The right-sided RQ counterpart. -/
def StructuredRQGoal : Prop :=
  ∀ (n : ℕ) (s : BlockSpec n) (B : Mat n) (σ : Equiv.Perm (Fin n)),
    BlockDiagonal s.size B → IsUnit B.det →
      ∃ U R : Mat n, BlockDiagonal s.size U ∧ Orthogonal U ∧ Upper R ∧
        permMatrix σ * B = R * permMatrix σ * U

/-- The two existence goals suffice for the full arbitrary-permutation m=3
statement. They remain explicit hypotheses; neither is assumed as an axiom. -/
theorem threeFactorOrthogonalization_of_structured
    (hqr : StructuredQRGoal) (hrq : StructuredRQGoal) :
    ThreeFactorOrthogonalizationGoal := by
  intro n s₁ s₂ s₃ σ₁ σ₂ A
  constructor
  · rintro ⟨⟨B₁, B₂, B₃, hb₁, hb₂, hb₃, he⟩, hA⟩
    have hdetA : A.det ≠ 0 := by
      intro hz
      have hgram := congrArg Matrix.det hA.1
      simp [Matrix.det_mul, Matrix.det_transpose, hz] at hgram
    have hprod : B₃.det * (permMatrix σ₂).det * B₂.det *
        (permMatrix σ₁).det * B₁.det ≠ 0 := by
      simpa only [he, product3, Matrix.det_mul] using hdetA
    have hdet₁ : IsUnit B₁.det := isUnit_iff_ne_zero.mpr (by
      intro hz
      exact hprod (by simp [hz]))
    have hdet₃ : IsUnit B₃.det := isUnit_iff_ne_zero.mpr (by
      intro hz
      exact hprod (by simp [hz]))
    obtain ⟨U₃, R₃, hu₃, ho₃, ht₃, eq₃⟩ := hqr n s₃ B₃ σ₂ hb₃ hdet₃
    obtain ⟨U₁, R₁, hu₁, ho₁, ht₁, eq₁⟩ := hrq n s₁ B₁ σ₁ hb₁ hdet₁
    exact threeFactor_from_structured_QR_RQ B₁ B₂ B₃
      (permMatrix σ₁) (permMatrix σ₂) A U₁ U₃ R₁ R₃ hb₂ hu₁ hu₃ ho₁ ho₃
      (perm_orthogonal σ₁) (perm_orthogonal σ₂) hA he eq₃ eq₁ ht₁ ht₃
  · exact inA3Orth_implies_inA3_and_orthogonal (perm_orthogonal σ₁)
      (perm_orthogonal σ₂)

/-- The cone product obstruction after the local model. It is proved in
`GS.NonmanifoldTopology.coneProductNonManifold` using a topological argument;
the optional sphere-homology computation is not needed. -/
def ConeProductNonManifoldGoal : Prop :=
  ∀ (d e : ℕ), 3 ≤ d →
    ¬ EuclideanAtSubset
      ({p : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ | Matrix.rank p.2 ≤ 1})
      (0,0)

end GS.Specifications
