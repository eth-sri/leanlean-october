module

public import NearlyMinimax.LowSmoothnessPrior
public import NearlyMinimax.RealDensity

@[expose] public section

/-! Raw-density normalization for the manuscript's high-smoothness prior.
The mass-concentration guard is a scalar event; density normalization and
original density bounds are consequences proved here. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

section
variable {d : ℕ} (C : ModelConstants d)

theorem high_raw_mass_lower (M cm m : ℝ)
    (hM : 2 ≤ M) (hcmU : cm ≤ 1 / C.densityUpper)
    (hm : |m - 1| ≤ cm / M) : 1 / 2 ≤ m := by
  have hU : 0 < C.densityUpper := lt_trans (by norm_num) C.one_lt_densityUpper
  have hcm1 : cm ≤ 1 := by
    apply hcmU.trans
    exact (div_le_one hU).mpr C.one_lt_densityUpper.le
  have hhalf : cm / M ≤ 1 / 2 := by
    gcongr
  grind

theorem high_normalized_density_interval
    (M cm m p : ℝ) (hM : 2 ≤ M) (hcm : 0 ≤ cm)
    (hcmU : cm ≤ 1 / C.densityUpper) (hm : |m - 1| ≤ cm / M)
    (hp : C.densityLower + 1 / M ≤ p ∧ p ≤ C.densityUpper - 1 / M) :
    C.densityLower ≤ p / m ∧ p / m ≤ C.densityUpper := by
  have hU : 0 < C.densityUpper := lt_trans (by norm_num) C.one_lt_densityUpper
  have hM0 : 0 < M := by linarith
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) (high_raw_mass_lower C M cm m hM hcmU hm)
  have hcmprod : C.densityUpper * cm ≤ 1 := by
    have h := (le_div_iff₀ hU).mp hcmU
    nlinarith
  have hLcm : C.densityLower * cm ≤ 1 := by
    have hLU :=
      C.densityLower_lt_one.le.trans C.one_lt_densityUpper.le
    exact (mul_le_mul_of_nonneg_right hLU hcm).trans hcmprod
  have hmass := abs_le.mp hm
  have hmulU : C.densityUpper * (cm / M) ≤ 1 / M := by
    have h := div_le_div_of_nonneg_right hcmprod hM0.le
    grind
  have hmulL : C.densityLower * (cm / M) ≤ 1 / M := by
    have h := div_le_div_of_nonneg_right hLcm hM0.le
    grind
  constructor
  · apply (le_div_iff₀ hm0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmass.2 C.densityLower_pos.le]
  · apply (div_le_iff₀ hm0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmass.1 hU.le]

end

def highRawDensityMass {d : ℕ} (p : Covariate d → ℝ) : ℝ :=
  ∫ x, p x ∂cubeVolume d

def highNormalizedDensity {d : ℕ} (p : Covariate d → ℝ) (x : Covariate d) : ℝ :=
  p x / highRawDensityMass p

section
variable {d : ℕ}

theorem highNormalizedDensity_measurable (p : Covariate d → ℝ)
    (hp : Measurable p) : Measurable (highNormalizedDensity p) := hp.div_const _

theorem highRawDensity_integrable (C : ModelConstants d) (M : ℝ)
    (hM : 0 < M) (p : Covariate d → ℝ) (hp : Measurable p)
    (hb : ∀ᵐ x ∂cubeVolume d,
      C.densityLower + 1 / M ≤ p x ∧ p x ≤ C.densityUpper - 1 / M) :
    Integrable p (cubeVolume d) := by
  let _ := cubeVolume_isProbability d
  exact integrable_of_ae_mem_nonneg_Icc hp (add_nonneg C.densityLower_pos.le (one_div_nonneg.mpr hM.le))
    (hb.mono fun _ hx => ⟨hx.1, hx.2.trans (by linarith [one_div_pos.mpr hM])⟩ :
      ∀ᵐ x ∂cubeVolume d, p x ∈ Icc (C.densityLower + 1 / M) C.densityUpper)

theorem highNormalizedDensity_normalized (p : Covariate d → ℝ)
    (hp : Integrable p (cubeVolume d)) (hp0 : 0 ≤ᵐ[cubeVolume d] p)
    (hm : 0 < highRawDensityMass p) :
    (∫⁻ x, ENNReal.ofReal (highNormalizedDensity p x) ∂cubeVolume d) = 1 := realDensity_normalized hp hp0 hm

theorem highNormalizedDensity_bounds (C : ModelConstants d) (M cm : ℝ)
    (hM : 2 ≤ M) (hcm : 0 ≤ cm) (hcmU : cm ≤ 1 / C.densityUpper)
    (p : Covariate d → ℝ)
    (hb : ∀ᵐ x ∂cubeVolume d,
      C.densityLower + 1 / M ≤ p x ∧ p x ≤ C.densityUpper - 1 / M)
    (hm : |highRawDensityMass p - 1| ≤ cm / M) :
    ∀ᵐ x ∂cubeVolume d,
      C.densityLower ≤ highNormalizedDensity p x ∧
        highNormalizedDensity p x ≤ C.densityUpper := by
  filter_upwards [hb] with x hx
  apply high_normalized_density_interval <;> assumption

end

/-- Actual ternary regression model with a normalized, nonuniform design. -/
def normalizedDensityTernaryParameter {d : ℕ} (p F : Covariate d → ℝ)
    (a V : ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) : RegressionParameter d where
  density := highNormalizedDensity p
  regression := F
  variance := V
  errors := ternaryErrorKernel a V F hF
  errors_markov := ternaryErrorKernel_markov a V F hF ha hp

section
variable {d : ℕ} (U : Set (Covariate d))
    (F : Covariate d → ℝ) (ℓ : ℕ) (α B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
include hB hL

/-- Pointwise mixed-derivative and Euclidean modulus bounds imply the
original sum-over-distinct-multi-indices norm on any extension domain. -/
theorem holderNorm_of_global_mixed_bounds_of_count
    (N : ℕ) (hN : (Finset.univ.filter (fun γ : Fin d → Fin (ℓ + 1) => (∑ i, (γ i).val) ≤ ℓ)).card ≤ N)
    (hsup : ∀ γ : Fin d → Fin (ℓ + 1), (∑ i, (γ i).val) ≤ ℓ →
      ∀ x, |multiPartial F (fun i => (γ i).val) x| ≤ B)
    (hmod : ∀ γ : Fin d → Fin (ℓ + 1), (∑ i, (γ i).val) = ℓ → ∀ x y,
      |multiPartial F (fun i => (γ i).val) x - multiPartial F (fun i => (γ i).val) y| ≤
        L * euclideanNorm (x - y) ^ α) :
    holderNorm U F ℓ α ≤ ENNReal.ofReal ((N : ℝ) * B + L) := by
  have hs (γ : Fin d → Fin (ℓ + 1)) (hγ : (∑ i, (γ i).val) ≤ ℓ) :
      derivativeSup U (multiPartial F (fun i => (γ i).val)) ≤ ENNReal.ofReal B := by
    solve_by_elim [iSup_le, ENNReal.ofReal_le_ofReal]
  have hh (γ : Fin d → Fin (ℓ + 1)) (hγ : (∑ i, (γ i).val) = ℓ) :
      holderSeminorm U (multiPartial F (fun i => (γ i).val)) α ≤ ENNReal.ofReal L := by
    apply iSup_le
    intro x
    apply iSup_le
    intro y
    by_cases hxy : (x : Covariate d) = y
    · simp [hxy]
    · simp only [ite_eq_right_iff.mpr (fun h => False.elim (hxy h))]
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ (Real.rpow_pos_of_pos
        (euclideanNorm_pos_of_ne_zero (x.val - y.val) (sub_ne_zero.mpr hxy)) α)).mpr
      exact hmod γ hγ x y
  rw [holderNorm, ENNReal.ofReal_add (by positivity) hL, ← Finset.sum_filter]
  apply add_le_add _ (iSup_le fun γ => ?_)
  · calc
      _ ≤ ∑ _γ ∈ Finset.univ.filter (fun γ : Fin d → Fin (ℓ + 1) => (∑ i, (γ i).val) ≤ ℓ),
          ENNReal.ofReal B := Finset.sum_le_sum fun γ hγ => hs γ (Finset.mem_filter.mp hγ).2
      _ ≤ _ := by
        rw [Finset.sum_const, ← ENNReal.ofReal_nsmul, nsmul_eq_mul]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by exact_mod_cast hN) hB)
  · split_ifs with h
    · exact hh γ h
    · positivity

end

end NearlyMinimax
