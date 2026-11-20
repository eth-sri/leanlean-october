module
public import GS.Isometric.Products
@[expose] public section

/-! Common matrix families over the real and complex scalars. All block
constraints are expressed in the original matrix entries. -/
noncomputable section
open Matrix
namespace GS.Isometric
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
def Support {ι κ : Type*} (label : ι → κ) (A : Matrix ι ι 𝕜) : Prop :=
  ∀ i j, label i ≠ label j → A i j = 0
abbrev DiagonalBlocks (b : ℕ) (A : Square 𝕜 n) := Support (fun i => i.val / b) A

/-- Labels tie full complex blocks within one layer, never across layers. -/
def Tied (b : ℕ) (τ : ℕ → ℕ) (A : Square 𝕜 n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

/-- Express membership and the tangent generators in terms of the original entry constraints. -/
def BlockFactor (b : ℕ) (τ : ℕ → ℕ) (A : Square 𝕜 n) := DiagonalBlocks b A ∧ IsU A ∧ Tied b τ A

def BlockDirections (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (X Z : Square 𝕜 n) :=
  ∃ C Ω, (DiagonalBlocks b₂ C ∧ Skew C ∧ Tied b₂ τ₂ C) ∧
    (DiagonalBlocks b₁ Ω ∧ Skew Ω ∧ Tied b₁ τ₁ Ω) ∧ Z = C * X + X * Ω

def Shared₂ (r l : ℕ) (τ υ : ℕ → ℕ) (P X : Square 𝕜 n) :=
  ∃ L R, BlockFactor l υ L ∧ BlockFactor r τ R ∧ X = product₂ L P R

def In₂ (r l : ℕ) (P X : Square 𝕜 n) :=
  ∃ R L, DiagonalBlocks r R ∧ DiagonalBlocks l L ∧ X = L*P*R

def In₂U (r l : ℕ) (P X : Square 𝕜 n) :=
  ∃ R L, DiagonalBlocks r R ∧ DiagonalBlocks l L ∧ IsU R ∧ IsU L ∧ X = L*P*R

def In₃ (r m l : ℕ) (P Q X : Square 𝕜 n) := ∃ R M L,
  DiagonalBlocks r R ∧ DiagonalBlocks m M ∧ DiagonalBlocks l L ∧ X = L*Q*M*P*R

def In₃U (r m l : ℕ) (P Q X : Square 𝕜 n) := ∃ R M L,
  DiagonalBlocks r R ∧ DiagonalBlocks m M ∧ DiagonalBlocks l L ∧ IsU R ∧ IsU M ∧ IsU L ∧ X = L*Q*M*P*R

def chain4 (L P W Q Y S R : Square 𝕜 n) := L*P*W*Q*Y*S*R

def In₄ (a b c d : ℕ) (P Q S X : Square 𝕜 n) := ∃ R Y W L,
  DiagonalBlocks a R ∧ DiagonalBlocks b Y ∧ DiagonalBlocks c W ∧ DiagonalBlocks d L ∧ X = chain4 L S W Q Y P R

def In₄U (a b c d : ℕ) (P Q S X : Square 𝕜 n) := ∃ R Y W L,
  DiagonalBlocks a R ∧ DiagonalBlocks b Y ∧ DiagonalBlocks c W ∧ DiagonalBlocks d L ∧
  IsU R ∧ IsU Y ∧ IsU W ∧ IsU L ∧ X = chain4 L S W Q Y P R
end GS.Isometric
