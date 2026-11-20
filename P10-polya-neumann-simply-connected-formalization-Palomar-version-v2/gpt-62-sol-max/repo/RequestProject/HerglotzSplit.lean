module

public import RequestProject.HerglotzGreen

/-!
# Boundary integrals of Herglotz coefficients

Consequences of the complex Green formula for the Herglotz coefficients `F_m` on a bounded
Lipschitz domain with positively oriented boundary parametrization `γ` (`c = -ik/2`,
`∂F_m = c F_{m+1}`, `∂̄F_m = c F_{m-1}`):

* `∫₀^{2π} conj(γ') F₋₁(γ) = -k ∫_Ω F₀` and `∫₀^{2π} γ' F₁(γ) = k ∫_Ω F₀`;
* the total conormal flux `∫₀^{2π} g_a = -k² ∫_Ω u_a`;
* `∫₀^{2π} conj(F₀(γ)) conj(γ') F₋₁(γ) = k ∫_Ω (|F₋₁|² − |F₀|²)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ} {γ : ℝ → ℂ} {a : ℝ → ℂ}

/-- `∂̄ conj(F) = conj α` when `DF(z) w = α w + β conj(w)`. -/
lemma dbar_conj_of_hasFDerivAt {F : ℂ → ℂ} {L : ℂ →L[ℝ] ℂ} {z α β : ℂ}
    (hF : HasFDerivAt F L z) (hL : ∀ w, L w = α * w + β * conj w) :
    dbar (fun x => conj (F x)) z = conj α := by
  have hcF :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z hF
  refine dbar_eq_of_hasFDerivAt (α := conj β) hcF fun w => ?_
  simp  [hL, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, map_add, map_mul, Complex.conj_conj]
  ring

/-- Herglotz coefficients are bounded Lipschitz functions. -/
lemma herglotzCoeff_bounded_lipschitz {a : ℝ → ℂ} (ha : IntervalIntegrable a volume 0 (2 * π))
    (k : ℝ) (m : ℤ) :
    (∃ K : NNReal, LipschitzWith K (herglotzCoeff k a m)) ∧
      ∀ z, ‖herglotzCoeff k a m z‖ ≤ (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖ :=
  ⟨lipschitzWith_herglotzCoeff ha k m, fun z => norm_herglotzCoeff_le k m z⟩

lemma integrableOn_herglotzCoeff (hb : Bornology.IsBounded Ω) {a : ℝ → ℂ}
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) (m : ℤ) :
    IntegrableOn (herglotzCoeff k a m) Ω :=
  Measure.integrableOn_of_bounded (M := (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖)
    hb.measure_lt_top.ne (continuous_herglotzCoeff ha k m).aestronglyMeasurable
    (Eventually.of_forall fun z => norm_herglotzCoeff_le k m z)

section

variable (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ) (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
include hb hL hγ ha k

/-- `∫₀^{2π} γ' F₁(γ) = k ∫_Ω F₀`. -/
lemma integral_herglotzCoeff_one_mul_deriv  :
    ∫ θ in (0 : ℝ)..(2 * π), herglotzCoeff k a 1 (γ θ) * deriv γ θ =
      (k : ℂ) * ∫ z in Ω, herglotzCoeff k a 0 z := by
  obtain ⟨⟨K, hK⟩, hB⟩ := herglotzCoeff_bounded_lipschitz ha k 1
  rw [integral_boundary_eq_dbar_of_bounded hb hL hγ hK hB]
  have hd : ∀ z, dbar (herglotzCoeff k a 1) z =
      -(Complex.I * k / 2) * herglotzCoeff k a 0 z := fun z => by
    obtain ⟨h1, h1L⟩ := herglotzCoeff_hasFDerivAt' ha k 1 z
    rw [dbar_eq_of_hasFDerivAt h1 h1L]
    norm_num
  simp_rw [hd]
  rw [integral_const_mul]
  ring_nf
  simp

/-- `∫₀^{2π} conj(γ') F₋₁(γ) = -k ∫_Ω F₀`. -/
lemma integral_conj_deriv_mul_herglotzCoeff_neg_one  :
    ∫ θ in (0 : ℝ)..(2 * π), conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ) =
      -(k : ℂ) * ∫ z in Ω, herglotzCoeff k a 0 z := by
  obtain ⟨⟨K, hK⟩, hB⟩ := herglotzCoeff_bounded_lipschitz ha k (-1)
  have hK' : LipschitzWith (1 * K) (fun z => conj (herglotzCoeff k a (-1) z)) :=
    Complex.isometry_conj.lipschitz.comp hK
  have hB' : ∀ z, ‖conj (herglotzCoeff k a (-1) z)‖ ≤
      (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖ := fun z => by simp_all
  have hg := integral_boundary_eq_dbar_of_bounded hb hL hγ hK' hB'
  have hd : ∀ z, dbar (fun x => conj (herglotzCoeff k a (-1) x)) z =
      conj (-(Complex.I * k / 2) * herglotzCoeff k a 0 z) := fun z => by
    obtain ⟨h1, h1L⟩ := herglotzCoeff_hasFDerivAt' ha k (-1) z
    rw [dbar_conj_of_hasFDerivAt h1 h1L]
    norm_num
  simp_rw [hd] at hg
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have e : ∫ θ in (0 : ℝ)..(2 * π), conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ) =
      conj (∫ θ in (0 : ℝ)..(2 * π), conj (herglotzCoeff k a (-1) (γ θ)) * deriv γ θ) := by
    rw [intervalIntegral.integral_of_le h2π, intervalIntegral.integral_of_le h2π,
      ← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [e, hg, integral_conj, map_mul, Complex.conj_conj, integral_const_mul]
  simp only [map_mul, map_ofNat, Complex.conj_I]
  ring_nf
  simp

/-- **Total conormal flux.** `∫₀^{2π} g_a = -k² ∫_Ω u_a`. -/
theorem integral_herglotzConormal  :
    ∫ θ in (0 : ℝ)..(2 * π), herglotzConormal k a γ θ =
      -((k : ℂ) ^ 2) * ∫ z in Ω, herglotzCoeff k a 0 z := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hi1 : IntervalIntegrable (fun θ => conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ))
      volume 0 (2 * π) := by
    have h := intervalIntegrable_comp_mul_deriv hKγ
      (Complex.continuous_conj.comp (continuous_herglotzCoeff ha k (-1)))
    rw [intervalIntegrable_iff] at h ⊢
    refine h.norm.mono' ?_ (Eventually.of_forall fun θ => by simp [mul_comm])
    refine (Complex.continuous_conj.comp_aestronglyMeasurable h.aestronglyMeasurable).congr ?_
    simp [mul_comm]
  have hi2 := intervalIntegrable_comp_mul_deriv hKγ (continuous_herglotzCoeff ha k 1)
  have hpt : ∀ θ, herglotzConormal k a γ θ = (k / 2 : ℂ) *
      (conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ) -
        herglotzCoeff k a 1 (γ θ) * deriv γ θ) := fun θ => by
    rw [herglotzConormal_eq ha]; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hi1 hi2,
    integral_conj_deriv_mul_herglotzCoeff_neg_one hb hL hγ ha,
    integral_herglotzCoeff_one_mul_deriv hb hL hγ ha]
  ring

/-- `∫₀^{2π} conj(F₀(γ)) conj(γ') F₋₁(γ) = k ∫_Ω (|F₋₁|² − |F₀|²)`. -/
theorem integral_conj_wave_mul_herglotzQ'  :
    ∫ θ in (0 : ℝ)..(2 * π), conj (herglotzCoeff k a 0 (γ θ)) *
        (conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ)) =
      ((k * ∫ z in Ω, (‖herglotzCoeff k a (-1) z‖ ^ 2 - ‖herglotzCoeff k a 0 z‖ ^ 2) : ℝ) :
        ℂ) := by
  have h := congrArg conj (integral_herglotzAdjacentBoundary hb hL hγ ha k (-1))
  rw [← intervalIntegral.intervalIntegral_conj] at h
  norm_num [herglotzAdjacentBoundary, map_mul] at h
  rw [Complex.ofReal_mul]
  refine Eq.trans (intervalIntegral.integral_congr fun θ _ => ?_) h
  ring

end

end PolyaNeumann

end
