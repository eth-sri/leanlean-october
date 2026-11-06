
import GS.MatrixFactor.StructuredQR
import GS.MatrixGeometry.Base



/-!
# Full two- and three-factor unitary factorization

These equivalences are unconditional: complex structured QR and RQ supply the
supported unitary outer factors. The middle factor is then unitary and block
triangular, hence block diagonal. Permutation connectors are arbitrary, and
the statements allow all natural block sizes without extra divisibility
assumptions.
-/

open Matrix GS.MatrixBase

namespace GS.MatrixFactor
variable {𝕜 : Type} [RCLike 𝕜]

variable (b b₁ b₂ b₃ : ℕ)

variable (B₂ P B₁ A B₃ P₂ P₁ : KMat 𝕜 n)

def product2  : KMat 𝕜 n := B₂ * P * B₁

def CBlockDiagonal   : Prop :=
  CSupported (fun i : Fin n => i.val / b) A

def product3 (B₂ P₁ B₁ : KMat 𝕜 n) : KMat 𝕜 n :=
  B₃ * P₂ * B₂ * P₁ * B₁

def CInA2   : Prop :=
  ∃ B₁ B₂, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    A = product2 B₂ P B₁

def CInA2Unitary   : Prop :=
  ∃ B₁ B₂, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    Unitary B₁ ∧ Unitary B₂ ∧ A = product2 B₂ P B₁

def CInA3  (P₂ A : KMat 𝕜 n) : Prop :=
  ∃ B₁ B₂ B₃, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ A = product3 B₃ P₂ B₂ P₁ B₁

def CInA3Unitary  (P₂ A : KMat 𝕜 n) : Prop :=
  ∃ B₁ B₂ B₃, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ Unitary B₁ ∧ Unitary B₂ ∧ Unitary B₃ ∧
    A = product3 B₃ P₂ B₂ P₁ B₁

/-- A unitary product with unitary outer factors has a unitary middle. -/
theorem middle_unitary_of_factorization {Q L M R : KMat 𝕜 n}
    (hQ : Unitary Q) (hL : Unitary L) (hR : Unitary R)
    (he : Q = L * M * R) : Unitary M := by
  have hm : M = Lᴴ * Q * Rᴴ := by
    rw [he]
    simp only [← Matrix.mul_assoc, hL.1, Matrix.one_mul]
    rw [Matrix.mul_assoc, hR.2, Matrix.mul_one]
  rw [hm]
  exact (hL.conjTranspose.mul hQ).mul hR.conjTranspose

/-- Every unitary three-factor product has supported unitary factors. -/
theorem threeFactorUnitarization 
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : KMat 𝕜 n) :
    CInA3 b₁ b₂ b₃ (cPermMatrix (𝕜 := 𝕜) σ₁) (cPermMatrix (𝕜 := 𝕜) σ₂) A ∧ Unitary A ↔
      CInA3Unitary b₁ b₂ b₃ (cPermMatrix (𝕜 := 𝕜) σ₁) (cPermMatrix (𝕜 := 𝕜) σ₂) A := by
  constructor
  · rintro ⟨⟨B₁,B₂,B₃,hb₁,hb₂,hb₃,he⟩,hA⟩
    let P₁ := cPermMatrix (𝕜 := 𝕜) σ₁
    let P₂ := cPermMatrix (𝕜 := 𝕜) σ₂
    have hd := unitary_det_ne_zero hA
    simp only [he, product3, Matrix.det_mul, mul_ne_zero_iff] at hd
    obtain ⟨U₃,R₃,hu₃,ho₃,ht₃,eq₃⟩ :=
      structuredQR _ B₃ σ₂ hb₃ hd.1.1.1.1
    obtain ⟨U₁,R₁,hu₁,ho₁,ht₁,eq₁⟩ :=
      structuredRQ _ B₁ σ₁ hb₁ hd.2
    let U₂ := R₃ * B₂ * R₁
    have hm : A = U₃ * P₂ * U₂ * P₁ * U₁ := by grind [product3]
    have ho₂ := middle_unitary_of_factorization hA
      (ho₃.mul (cPerm_unitary σ₂)) ((cPerm_unitary σ₁).mul ho₁)
      (by simpa only [Matrix.mul_assoc] using hm)
    exact ⟨U₁,U₂,U₃,hu₁,unitary_blockTriangular_supported ho₂
      (((cUpper_blockTriangular ht₃).mul (cSupported_blockTriangular hb₂)).mul
        (cUpper_blockTriangular ht₁)),hu₃,ho₁,ho₂,ho₃,hm⟩
  · rintro ⟨B₁,B₂,B₃,hb₁,hb₂,hb₃,hu₁,hu₂,hu₃,rfl⟩
    exact ⟨⟨B₁,B₂,B₃,hb₁,hb₂,hb₃,rfl⟩,
      (((hu₃.mul (cPerm_unitary σ₂)).mul hu₂).mul (cPerm_unitary σ₁)).mul hu₁⟩

/-- Two factors require only the left structured QR step. -/
theorem twoFactorUnitarization  (σ : Equiv.Perm (Fin n)) (A : KMat 𝕜 n) :
    CInA2 b₁ b₂ (cPermMatrix (𝕜 := 𝕜) σ) A ∧ Unitary A ↔
      CInA2Unitary b₁ b₂ (cPermMatrix (𝕜 := 𝕜) σ) A := by
  constructor
  · rintro ⟨⟨B₁,B₂,hb₁,hb₂,he⟩,hA⟩
    let P := cPermMatrix (𝕜 := 𝕜) σ
    have hd := unitary_det_ne_zero hA
    simp only [he, product2, Matrix.det_mul, mul_ne_zero_iff] at hd
    obtain ⟨U,R,hu,ho,ht,heq⟩ := structuredQR _ B₂ σ hb₂
      hd.1.1
    have hm : A = U * P * (R * B₁) := by
      rw [he]
      change (B₂ * P) * B₁ = _
      rw [heq, Matrix.mul_assoc]
    have hV := middle_unitary_of_factorization hA (ho.mul (cPerm_unitary σ))
      Unitary.one (by simpa only [Matrix.mul_one] using hm)
    exact ⟨R * B₁,U,unitary_blockTriangular_supported hV
      ((cUpper_blockTriangular ht).mul (cSupported_blockTriangular hb₁)),hu,hV,ho,hm⟩
  · rintro ⟨B₁,B₂,hb₁,hb₂,ho₁,ho₂,he⟩
    refine ⟨⟨B₁,B₂,hb₁,hb₂,he⟩,?_⟩
    rw [he]
    exact (ho₂.mul (cPerm_unitary σ)).mul ho₁

end GS.MatrixFactor
