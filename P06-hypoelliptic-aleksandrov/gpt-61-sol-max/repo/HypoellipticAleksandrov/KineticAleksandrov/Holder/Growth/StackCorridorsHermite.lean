module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Hermite
import Mathlib.Tactic

/-! # Uniform Hermite bounds for forward-stack endpoints -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

variable (m : ℕ)

/-- The source acceleration coefficient depends only on the stack height. -/
def stackAcceleration  : ℝ := 384*((m : ℝ)+2)+32

/-- A generous common native-coordinate bound for every stack path. -/
def stackPathBound  : ℝ := 64*((m : ℝ)+2)

/-- Uniform Euclidean acceleration bound for the source stack Hermite path. -/
theorem stack_hermite_acceleration {d : ℕ} {r T : ℝ} (hr : 0 < r)
    (m : ℕ) (hTlo : r^2/8 ≤ T) (x0 v0 x1 v1 : PDE.Vec d)
    (hx : PDE.vecEuclideanNorm (x1-x0-T • v0) ≤ ((m : ℝ)+2)*r^3)
    (hv : PDE.vecEuclideanNorm (v1-v0) ≤ r) :
    6*PDE.vecEuclideanNorm (x1-x0-T • v0)/T^2+
      4*PDE.vecEuclideanNorm (v1-v0)/T ≤ stackAcceleration m/r := by




  have heq : 6*(((m : ℝ)+2)*r^3)/(r^2/8)^2+4*r/(r^2/8) = stackAcceleration m/r := by
    unfold stackAcceleration
    field_simp
    ring
  rw [← heq]
  exact add_le_add (by
      apply div_le_div₀ (by positivity) (by nlinarith only [hx]) (by positivity) (by nlinarith)) (by
      apply div_le_div₀ (by positivity) (by nlinarith only [hv]) (by positivity) hTlo)

/-- Elementary absolute-value bounds for the four Hermite coefficients. -/
theorem hermite_unit_coefficients {z : ℝ} (hz : z ∈ Icc 0 1) :
    |3*z^2-2*z^3| ≤ 1 ∧ |z^3-z^2| ≤ 1 ∧
      |6*z-6*z^2| ≤ 6 ∧ |3*z^2-2*z| ≤ 5 := by
  have hz2 : z^2 ≤ z := by nlinarith only [hz.1, hz.2]
  have hz3 : z^3 ≤ z^2 := by nlinarith only [hz.1, hz.2, sq_nonneg z]
  have hc  := pow_nonneg hz.1 3


  refine ⟨abs_le.mpr ⟨by linarith, (by
      have h := mul_nonneg (sq_nonneg (1-z)) (by linarith only [hz.1] : 0 ≤ 1+2*z)
      nlinarith)⟩,
    abs_le.mpr ⟨by nlinarith, by nlinarith⟩,
    abs_le.mpr ⟨by nlinarith, by nlinarith⟩,
    abs_le.mpr ⟨by nlinarith, by nlinarith⟩⟩

/-- Source-relative position and velocity bounds for the unextended Hermite path. -/
theorem stack_hermite_bounds {d : ℕ} {r T : ℝ} (hr : 0 < r) (m : ℕ)
    (hTlo : r^2/8 ≤ T) (hThi : T ≤ ((m : ℝ)+1)*r^2)
    (x0 v0 x1 v1 : PDE.Vec d)
    (hx : PDE.vecEuclideanNorm (x1-x0-T • v0) ≤ ((m : ℝ)+2)*r^3)
    (hv : PDE.vecEuclideanNorm (v1-v0) ≤ r) {s : ℝ} (hs : s ∈ Icc 0 T) :
    PDE.vecEuclideanNorm (hermitePosition T x0 v0 x1 v1 s-x0-s • v0) ≤
      stackPathBound m*r^3 ∧
    PDE.vecEuclideanNorm (hermiteVelocity T x0 v0 x1 v1 s-v0) ≤ stackPathBound m*r := by
  let sharedTerm_9f3ff01e6b := (((3 * (s / T) ^ 2 - 2 * (s / T) ^ 3) • (x1 - x0 - T • v0)))
  let sharedTerm_25a312a129 := (((T * ((s / T) ^ 3 - (s / T) ^ 2)) • (v1 - v0)))
  let sharedTerm_fb8c5db7aa := ((((6 * (s / T) - 6 * (s / T) ^ 2) / T) • (x1 - x0 - T • v0)))
  have hT : 0 < T := (by positivity : 0 < r^2/8).trans_le hTlo

  obtain ⟨hc₁, hc₂, hc₃, hc₄⟩ := hermite_unit_coefficients (⟨div_nonneg hs.1 hT.le, (div_le_one hT).mpr hs.2⟩)
  have hn : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  constructor
  · rw [hermitePosition_eq hT.ne']
    have heq : x0+s • v0+sharedTerm_9f3ff01e6b+
        sharedTerm_25a312a129-x0-s • v0 =
        sharedTerm_9f3ff01e6b+
          sharedTerm_25a312a129 := by abel
    rw [heq]
    have hsum := PDE.vecEuclideanNorm_add_le
      sharedTerm_9f3ff01e6b
      sharedTerm_25a312a129
    rw [PDE.vecEuclideanNorm_smul, PDE.vecEuclideanNorm_smul,
      abs_mul, abs_of_pos hT] at hsum
    have h₁ := mul_le_mul hc₁ hx (PDE.vecEuclideanNorm_nonneg _) (by norm_num)



    unfold stackPathBound
    nlinarith only [hsum, h₁, (mul_le_mul_of_nonneg_left (mul_le_mul hc₂ hv (PDE.vecEuclideanNorm_nonneg _) (by norm_num)) hT.le), (mul_le_mul_of_nonneg_right hThi hr.le), hn, pow_pos hr 3]
  · change PDE.vecEuclideanNorm
      (v0+sharedTerm_fb8c5db7aa+
        (3*(s/T)^2-2*(s/T)) • (v1-v0)-v0) ≤ stackPathBound m*r
    rw [add_assoc, add_sub_cancel_left]
    have hsum := PDE.vecEuclideanNorm_add_le
      sharedTerm_fb8c5db7aa
      ((3*(s/T)^2-2*(s/T)) • (v1-v0))
    rw [PDE.vecEuclideanNorm_smul, PDE.vecEuclideanNorm_smul, abs_div,
      abs_of_pos hT] at hsum
    have h₁ : (|6*(s/T)-6*(s/T)^2|/T)*PDE.vecEuclideanNorm (x1-x0-T • v0) ≤
        (6/(r^2/8))*(((m : ℝ)+2)*r^3) := by
      apply mul_le_mul
      · exact div_le_div₀ (by norm_num) hc₃ (by positivity) hTlo
      · exact hx
      · exact PDE.vecEuclideanNorm_nonneg _
      · positivity

    have heq : (6/(r^2/8))*(((m : ℝ)+2)*r^3) = 48*((m : ℝ)+2)*r := by
      field_simp
      ring
    rw [heq] at h₁
    unfold stackPathBound
    nlinarith only [hsum, h₁, (mul_le_mul hc₄ hv (PDE.vecEuclideanNorm_nonneg _) (by norm_num)), hn, hr]

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
