module
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Group.Commute.Units
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

open scoped NNReal
namespace SevenEighths.CenteredMoment
noncomputable section

variable {M R : Type*} [CommMonoid M] [CommRing R]

structure MaskedCharacter (M R : Type*) [CommMonoid M] [CommRing R] where
  residue : M →* R
  character : MulChar R ℂ
  keep : M → Prop
  keep_mul : ∀ a b, keep (a * b) ↔ keep a ∧ keep b

def MaskedCharacter.value (d : MaskedCharacter M R) (a : M) : ℂ :=
  @ite ℂ (d.keep a) (Classical.propDecidable _) (d.character (d.residue a)) 0

@[simp] theorem MaskedCharacter.value_mul (d : MaskedCharacter M R) (a b : M) :
    d.value (a * b) = d.value a * d.value b := by
  classical
  simp only [MaskedCharacter.value, d.keep_mul, map_mul]
  split_ifs <;> simp_all

def normTwist (N : M →* ℝ≥0) (t : ℝ) (a : M) : ℂ :=
  ((N a : ℝ) : ℂ) ^ (Complex.I * t)

def coefficient (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ) (a : M) : ℂ :=
  d.value a * normTwist N t a

def volumeTerm (c I : ℂ) (t X : ℝ) : ℂ :=
  c * (X : ℂ) ^ (1 + Complex.I * t) * I

theorem volume_products_eq (c I₁ I₂ : ℂ) (t X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂)
    (hscale : X₁ * X₂ = Y₁ * Y₂) :
    volumeTerm c I₁ t X₁ * volumeTerm c I₂ t X₂ =
      volumeTerm c I₁ t Y₁ * volumeTerm c I₂ t Y₂ := by
  have hpow : (X₁ : ℂ) ^ (1 + Complex.I * t) *
      (X₂ : ℂ) ^ (1 + Complex.I * t) =
      (Y₁ : ℂ) ^ (1 + Complex.I * t) * (Y₂ : ℂ) ^ (1 + Complex.I * t) := by
    rw [← Complex.mul_cpow_ofReal_nonneg hX₁ hX₂,
      ← Complex.mul_cpow_ofReal_nonneg hY₁ hY₂, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, hscale]
  unfold volumeTerm
  grind

section
variable (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
include A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂
theorem centered_error_identity
    (hmain : a₁ * a₂ = b₁ * b₂) :
    A₁ * A₂ - B₁ * B₂ =
      (A₁ - a₁) * A₂ + a₁ * (A₂ - a₂) -
        (B₁ - b₁) * B₂ - b₁ * (B₂ - b₂) := by
  linear_combination hmain

theorem norm_centered_le
    (hmain : a₁ * a₂ = b₁ * b₂) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤
      ‖A₁ - a₁‖ * ‖A₂‖ + ‖a₁‖ * ‖A₂ - a₂‖ +
        ‖B₁ - b₁‖ * ‖B₂‖ + ‖b₁‖ * ‖B₂ - b₂‖ := by
  rw [centered_error_identity A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ hmain]
  calc
    _ ≤ ‖(A₁ - a₁) * A₂ + a₁ * (A₂ - a₂) - (B₁ - b₁) * B₂‖ +
        ‖b₁ * (B₂ - b₂)‖ := norm_sub_le _ _
    _ ≤ (‖(A₁ - a₁) * A₂ + a₁ * (A₂ - a₂)‖ +
        ‖(B₁ - b₁) * B₂‖) + ‖b₁ * (B₂ - b₂)‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ((‖(A₁ - a₁) * A₂‖ + ‖a₁ * (A₂ - a₂)‖) +
        ‖(B₁ - b₁) * B₂‖) + ‖b₁ * (B₂ - b₂)‖ :=
      add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ = _ := by simp_all

theorem norm_centered_le_of_approx
    (X₁ X₂ Y₁ Y₂ C E : ℝ)
    (hmain : a₁ * a₂ = b₁ * b₂)
    (hE : 0 ≤ E)
    (hA₁ : ‖A₁ - a₁‖ ≤ E) (hA₂ : ‖A₂ - a₂‖ ≤ E)
    (hB₁ : ‖B₁ - b₁‖ ≤ E) (hB₂ : ‖B₂ - b₂‖ ≤ E)
    (hvA₂ : ‖A₂‖ ≤ C * X₂) (hva₁ : ‖a₁‖ ≤ C * X₁)
    (hvB₂ : ‖B₂‖ ≤ C * Y₂) (hvb₁ : ‖b₁‖ ≤ C * Y₁) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ E * C * (X₁ + X₂ + Y₁ + Y₂) := by
  have h₁ := mul_le_mul hA₁ hvA₂ (norm_nonneg A₂) hE
  have h₂ := mul_le_mul hA₂ hva₁ (norm_nonneg a₁) hE
  have h₃ := mul_le_mul hB₁ hvB₂ (norm_nonneg B₂) hE
  have h₄ := mul_le_mul hB₂ hvb₁ (norm_nonneg b₁) hE
  have h := norm_centered_le A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ hmain
  nlinarith
end

theorem scale_le_product_div {X Y T L : ℝ}
    (hX : 0 ≤ X) (hL : 0 < L) (hY : L ≤ Y) (hprod : X * Y = T) :
    X ≤ T / L := by
  apply (le_div_iff₀ hL).mpr
  rw [← hprod]
  exact mul_le_mul_of_nonneg_left hY hX

theorem sum_scales_le {X₁ X₂ Y₁ Y₂ T L : ℝ}
    (hL : 0 < L) (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    X₁ + X₂ + Y₁ + Y₂ ≤ 4 * (T / L) := by
  pm_8140 a hX₁ hX₂ hprodX b
  pm_8140 c hY₁ hY₂ hprodY d
  linarith

theorem centered_saving_of_approx
    (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ T L C E : ℝ)
    (hmain : a₁ * a₂ = b₁ * b₂)
    (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hA₁ : ‖A₁ - a₁‖ ≤ E) (hA₂ : ‖A₂ - a₂‖ ≤ E)
    (hB₁ : ‖B₁ - b₁‖ ≤ E) (hB₂ : ‖B₂ - b₂‖ ≤ E)
    (hvA₂ : ‖A₂‖ ≤ C * X₂) (hva₁ : ‖a₁‖ ≤ C * X₁)
    (hvB₂ : ‖B₂‖ ≤ C * Y₂) (hvb₁ : ‖b₁‖ ≤ C * Y₁)
    (hL : 0 < L) (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ 4 * E * C * (T / L) := by
  have h := norm_centered_le_of_approx A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂
    X₁ X₂ Y₁ Y₂ C E hmain hE hA₁ hA₂ hB₁ hB₂ hvA₂ hva₁ hvB₂ hvb₁
  have hs := sum_scales_le hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY
  calc
    _ ≤ E * C * (X₁ + X₂ + Y₁ + Y₂) := h
    _ ≤ E * C * (4 * (T / L)) := mul_le_mul_of_nonneg_left hs (mul_nonneg hE hC)
    _ = _ := by ring

theorem normalized_centered_saving (D : ℂ) (T L C E : ℝ)
    (hT : 0 < T) (hbound : ‖D‖ ≤ 4 * E * C * (T / L)) :
    ‖(Real.sqrt T : ℂ)⁻¹ * D‖ ≤ 4 * E * C * (Real.sqrt T / L) := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le]
  calc
    _ ≤ (Real.sqrt T)⁻¹ * (4 * E * C * (T / L)) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hs.le)
    _ = 4 * E * C * ((T / Real.sqrt T) / L) := by ring
    _ = _ := by grind

end
end SevenEighths.CenteredMoment

end OAI
