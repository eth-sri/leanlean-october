module
public import RationalFiniteHeight
import WeylPort.Analytic.RealLaplace

@[expose] public section

noncomputable section
open Finset
namespace Montgomery.RationalMoment

def momentTransferCost (k H : ℕ) (T : ℝ) : ℝ :=
  (2 + (k : ℝ)^2) *
    (T+1+4*Real.exp (k : ℝ)*(H : ℝ)^(2*k)*
      (1+Real.log ⌊2*(k : ℝ)*Real.exp (k : ℝ)*(H : ℝ)^(2*k)⌋₊))

section
variable {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη : 0 < η)
include k hk η hη
/-- The logarithmic finite-height cost is uniformly a small power of H.
The constant is chosen before H and T. -/
theorem moment_transfer_cost_subpower :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 1 ≤ H → ∀ T : ℝ, 0 ≤ T →
      momentTransferCost k H T ≤ C * (T + (H : ℝ)^(2*k)) * (H : ℝ)^η := by
  pm_77 hkR k hk
  pm_389 hkpos k
  let J := 1 + Real.log (2*(k : ℝ)) + (k : ℝ)
  let D := J + 2*(k : ℝ)/η
  have hlogk : 0 ≤ Real.log (2*(k : ℝ)) := Real.log_nonneg (by linarith)
  pm_64 hJ J
  pm_4497
  refine ⟨(2+(k : ℝ)^2)*(1+4*Real.exp (k : ℝ)*D), by positivity, ?_⟩
  intro H hH T hT
  pm_77 hHR H hH
  pm_389 hHpos H
  let P := (H : ℝ)^(2*k)
  let Z := (H : ℝ)^η
  have hP : 1 ≤ P := one_le_pow₀ hHR
  have hZ : 1 ≤ Z := Real.one_le_rpow hHR hη.le
  have he : 1 ≤ Real.exp (k : ℝ) := Real.one_le_exp_iff.mpr hkpos.le
  let X := 2*(k : ℝ)*Real.exp (k : ℝ)*P
  have hX1 : 1 ≤ X := by
    have hke : 1 ≤ 2*(k : ℝ)*Real.exp (k : ℝ) := by
      nlinarith [mul_nonneg (show 0 ≤ 2*(k : ℝ)-1 by linarith) (sub_nonneg.mpr he)]
    dsimp only [X]
    pm_385 mul_nonneg sub_nonneg.mpr hke hP
  have hfloor : (1 : ℝ) ≤ ⌊X⌋₊ := by
    have hn : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by grind)
    exact_mod_cast hn
  have hlogX : Real.log ⌊X⌋₊ ≤ Real.log X :=
    Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have hlogeq : Real.log X = Real.log (2*(k : ℝ)) + (k : ℝ) +
      (2*(k : ℝ))*Real.log (H : ℝ) := by
    dsimp [X, P]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow]
    push_cast
    ring
  have hlog : 1 + Real.log ⌊X⌋₊ ≤ D * Z := by
    have hh := Real.log_le_rpow_div hHpos.le hη
    have hJZ := mul_le_mul_of_nonneg_left hZ hJ.le
    have hηterm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*(k : ℝ) by positivity)
    dsimp only [D]
    rw [hlogeq] at hlogX
    dsimp only [J, Z] at *
    simp only [div_eq_mul_inv] at hηterm ⊢
    nlinarith
  have hbase : T+1 ≤ (T+P)*Z := by
    nlinarith [mul_nonneg (show 0 ≤ T+P by linarith) (sub_nonneg.mpr hZ)]
  have hlarge : 4*Real.exp (k : ℝ)*P*(1+Real.log ⌊X⌋₊) ≤
      (4*Real.exp (k : ℝ)*D)*((T+P)*Z) := by
    have h1 := mul_le_mul_of_nonneg_left hlog
      (show 0 ≤ 4*Real.exp (k : ℝ)*P by positivity)
    have h2 := mul_le_mul_of_nonneg_left (show P ≤ T+P by linarith)
      (show 0 ≤ 4*Real.exp (k : ℝ)*D*Z by positivity)
    nlinarith
  have hh : T+1+4*Real.exp (k : ℝ)*P*(1+Real.log ⌊X⌋₊) ≤
      (1+4*Real.exp (k : ℝ)*D)*((T+P)*Z) := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2+(k : ℝ)^2 by positivity)
  change (2+(k : ℝ)^2)*(T+1+4*Real.exp (k : ℝ)*P*(1+Real.log ⌊X⌋₊)) ≤ _
  dsimp only [P, Z] at hh'
  nlinarith

/-- Coefficient-energy transfer with the exact asymptotic shape needed in the
research argument. The arithmetic small-power estimate for the coefficient
energy is not assumed or proved by this theorem. -/
theorem rational_moment_transfer_subpower :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℕ), 1 ≤ H → ∀ (T t₀ : ℝ), 0 ≤ T →
      ∀ (A : Finset ℚ) (c : ℚ → ℂ),
      (∀ r ∈ A, 0 < r ∧ r.den ≤ H ∧ |Real.log (r : ℝ)| ≤ 1) →
      ∀ (W : Finset ℝ), (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ t ∈ W, ‖∑ r ∈ A, c r * phase r t‖ ^ (2*k)) ≤
        C * (T+(H : ℝ)^(2*k)) * (H : ℝ)^η * rationalCoefficientEnergy A k c := by
  pm_98 C hC hcost moment_transfer_cost_subpower hk hη
  refine ⟨C, hC, ?_⟩
  intro H hH T t₀ hT A c hA W hW hsep
  have hh := rational_finite_height_moment A c k H hH (by norm_num : (0 : ℝ) ≤ 1)
    hT hA W hW hsep
  have he : ((H : ℝ)^k)^2 = (H : ℝ)^(2*k) := by rw [← pow_mul]; congr 1; omega
  dsimp only at hh
  simp only [mul_one, he, one_div, inv_inv, div_inv_eq_mul] at hh
  rw [show 2*(k : ℝ)*(Real.exp (k : ℝ)*(H : ℝ)^(2*k)) =
      2*(k : ℝ)*Real.exp (k : ℝ)*(H : ℝ)^(2*k) by ring] at hh
  have hb : (∑ t ∈ W, ‖∑ r ∈ A, c r * phase r t‖ ^ (2*k)) ≤
      momentTransferCost k H T * rationalCoefficientEnergy A k c := by
    unfold momentTransferCost
    convert hh using 1
    ring
  exact hb.trans (mul_le_mul_of_nonneg_right (hcost H hH T hT)
    (sum_nonneg (fun _ _ => sq_nonneg _)))
end

end Montgomery.RationalMoment
