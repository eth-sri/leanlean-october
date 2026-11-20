module

public import GS.Shared.QR

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix InnerProductSpace
open scoped BigOperators

namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

def BlockDiagonal (b : ℕ) (A : M 𝕜 n) : Prop :=
  CSupported (fun i : Fin n => i.val / b) A

def product3 (B₃ P₂ B₂ P₁ B₁ : M 𝕜 n) : M 𝕜 n :=
  B₃ * P₂ * B₂ * P₁ * B₁

def InA2 (b₁ b₂ : ℕ) (P A : M 𝕜 n) : Prop :=
  ∃ B₁ B₂, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧
    A = product2 B₂ P B₁

def InA2Unitary (b₁ b₂ : ℕ) (P A : M 𝕜 n) : Prop :=
  ∃ B₁ B₂, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧
    Unitary B₁ ∧ Unitary B₂ ∧ A = product2 B₂ P B₁

def InA3 (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : M 𝕜 n) : Prop :=
  ∃ B₁ B₂ B₃, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧
    BlockDiagonal b₃ B₃ ∧ A = product3 B₃ P₂ B₂ P₁ B₁

def InA3Unitary (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : M 𝕜 n) : Prop :=
  ∃ B₁ B₂ B₃, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧
    BlockDiagonal b₃ B₃ ∧ Unitary B₁ ∧ Unitary B₂ ∧ Unitary B₃ ∧
    A = product3 B₃ P₂ B₂ P₁ B₁

theorem inA3Unitary_implies_inA3_and_unitary {b₁ b₂ b₃ : ℕ} {P₁ P₂ A : M 𝕜 n}
    (hP₁ : Unitary P₁) (hP₂ : Unitary P₂)
    (h : InA3Unitary b₁ b₂ b₃ P₁ P₂ A) :
    InA3 b₁ b₂ b₃ P₁ P₂ A ∧ Unitary A := by
  rcases h with ⟨B₁,B₂,B₃,hb₁,hb₂,hb₃,hu₁,hu₂,hu₃,rfl⟩
  exact ⟨⟨B₁,B₂,B₃,hb₁,hb₂,hb₃,rfl⟩,
    (((hu₃.mul hP₂).mul hu₂).mul hP₁).mul hu₁⟩

private theorem middle_unitary {X A K B : M 𝕜 n}
    (hX : Unitary X) (hA : Unitary A) (hB : Unitary B) (he : X = A * K * B) : Unitary K := by
  have h : Aᴴ * X * Bᴴ = K := by
    rw [he]
    simp only [← Matrix.mul_assoc, hA.1, Matrix.one_mul,
      Matrix.mul_assoc K B, hB.2, Matrix.mul_one]
  exact h ▸ (hA.conjTranspose.mul hX).mul hB.conjTranspose

/-- Every unitary three-factor product has supported unitary factors. -/
theorem threeFactor (b₁ b₂ b₃ : ℕ)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : M 𝕜 n) :
    InA3 b₁ b₂ b₃ (permMatrix (𝕜 := 𝕜) σ₁) (permMatrix (𝕜 := 𝕜) σ₂) A ∧ Unitary A ↔
      InA3Unitary b₁ b₂ b₃ (permMatrix (𝕜 := 𝕜) σ₁) (permMatrix (𝕜 := 𝕜) σ₂) A := by
  let P₁ : M 𝕜 n := permMatrix σ₁
  let P₂ : M 𝕜 n := permMatrix σ₂
  have p₁ : Unitary P₁ := perm_unitary σ₁
  have p₂ : Unitary P₂ := perm_unitary σ₂
  refine ⟨?_, inA3Unitary_implies_inA3_and_unitary p₁ p₂⟩
  rintro ⟨⟨B₁,B₂,B₃,hb₁,hb₂,hb₃,hA⟩,hU⟩
  have hu : IsUnit (B₃ * P₂ * B₂ * P₁ * B₁) := by simpa only [hA, product3] using hU.isUnit
  simp only [IsUnit.mul_iff] at hu
  obtain ⟨U₃,R₃,hu₃,ho₃,ht₃,h₃⟩ := structuredQR _ B₃ σ₂ hb₃ hu.1.1.1.1
  obtain ⟨U₁,R₁,hu₁,ho₁,ht₁,h₁⟩ := structuredRQ _ B₁ σ₁ hb₁ hu.2
  have he : A = product3 U₃ P₂ (R₃ * B₂ * R₁) P₁ U₁ := calc
    A = (B₃ * P₂) * B₂ * (P₁ * B₁) := by grind [product3]
    _ = _ := by grind [product3]
  have ho₂ : Unitary (R₃ * B₂ * R₁) := middle_unitary hU (ho₃.mul p₂) (p₁.mul ho₁)
    (by simpa only [product3, Matrix.mul_assoc] using he)
  have hb := ((upper_blockTriangular ht₃).mul (supported_blockTriangular hb₂)).mul
    (upper_blockTriangular ht₁)
  exact ⟨U₁,_,U₃,hu₁,unitary_blockTriangular_supported ho₂ hb,hu₃,ho₁,ho₂,ho₃,he⟩

/-- Insert an identity between two copies of the right support pattern. -/
theorem twoFactor (b₁ b₂ : ℕ) (σ : Equiv.Perm (Fin n)) (A : M 𝕜 n) :
    InA2 b₁ b₂ (permMatrix (𝕜 := 𝕜) σ) A ∧ Unitary A ↔
      InA2Unitary b₁ b₂ (permMatrix (𝕜 := 𝕜) σ) A := by
  constructor
  · rintro ⟨⟨R,L,hR,hL,hA⟩,hU⟩
    obtain ⟨B,C,D,hB,hC,hD,uB,uC,uD,h⟩ := (threeFactor b₁ b₁ b₂ (.refl _) σ A).mp
      ⟨⟨R,1,L,hR,CSupported.one,hL,by simpa [product3, product2] using hA⟩,hU⟩
    exact ⟨C*B,D,CSupported.mul hC hB,hD,uC.mul uB,uD,
      by simpa [product2, product3, Matrix.mul_assoc] using h⟩
  · rintro ⟨R,L,hR,hL,uR,uL,rfl⟩
    exact ⟨⟨R,L,hR,hL,rfl⟩,(uL.mul (perm_unitary σ)).mul uR⟩

end GS.Shared
