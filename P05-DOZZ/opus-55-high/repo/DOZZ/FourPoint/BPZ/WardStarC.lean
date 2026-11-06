/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardStarB

/-! # The cutoff Ward identity

Both sides of the cutoff Ward identity have been rooted at the integration point: the left side
becomes `∫ ∂_v(φ k̃) Ψ` and the right side `∫ φ k̃ E[J^{-q-1} S]` for the rooted moment
`Ψ = E[J^{-q}]`. Since `Ψ` has the line derivative `E[-q J^{-q-1} S]` on the support of `φ`, an
integration by parts closes the identity

  `E[Î^{-q} ∫ ∂_v(φ k̃) |x|₊⁴ e^{γ² q h_r} dM_r] = q E[Î^{-q-1} ∫ φ k₁ Ŷ_v dM_r]`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ q r δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}
variable {P : Measure Ω} {X : Ω → Distr} {M : Ω → Measure ℂ} {Xc : Ω → ℂ → ℝ → ℝ}

/-- A continuous compactly supported function times a measurable function bounded on its
support is integrable. -/
theorem bpz_integrable_mul_of_bdd_on_tsupport {f g : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : AEStronglyMeasurable g volume) {K : ℝ}
    (hK : ∀ x ∈ tsupport f, |g x| ≤ K) : Integrable (fun x => f x * g x) := by
  refine ((hf.integrable_of_hasCompactSupport hfc).norm.const_mul K).mono'
    (hf.aestronglyMeasurable.mul hg) (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Real.norm_eq_abs (g x)]
  by_cases hx : x ∈ tsupport f
  · rw [mul_comm K]
    bound
  · simp [image_eq_zero_of_notMem_tsupport hx]
section
variable (hd : BPZWardData γ q r δ ρ kt k₂ φ D) (hp : BPZWardProb P X γ M Xc ρ k₂ D) (v : ℂ)
include hd hp

/-- The rooted moment and its line derivative are bounded on the support of the test
function. -/
theorem bpzWard_Psi_bounds :
    ∃ K : ℝ, ∀ x ∈ tsupport φ,
      |∫ ω, bpzRootedMixedReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x
          (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) ∂P| ≤ K ∧
      |∫ ω, -q * bpzRootedMixedReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x
          (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - 1) *
        bpzRootedMixedDerivApply γ r ρ (bpzWardCutWeight γ q r kt) k₂ x v
          (regularizedGMC P Xc γ r ω) (M ω) ∂P| ≤ K := by
  set k₁ := bpzWardCutWeight γ q r kt with hk₁def
  have hk₁0 := bpzWardCutWeight_nonneg hd
  have hq0 := le_trans zero_le_one hd.q_ge
  obtain ⟨R, hR⟩ := hd.φ_compact.isCompact.isBounded.exists_norm_le
  obtain ⟨c, hc, hlow⟩ := bpzWard_J_lower hd k₁ hk₁0 R
  set G : Ω → ℝ := fun ω => (c * (M ω D).toReal) ^ (-q) with hG
  have hmD :=
    ((Measure.measurable_coe hd.D_meas).comp hp.hMm).ennreal_toReal
  have hGi := bpzWard_integrable_rpow_neg hp hd.D_meas
    (hmD.const_mul c).aestronglyMeasurable hc (Eventually.of_forall fun ω => le_rfl) hq0
  set L := γ ^ 2 * Real.exp r * ‖v‖ with hL
  have hL0 : 0 ≤ L := by positivity
  have hG0 : 0 ≤ ∫ ω, G ω ∂P :=
    integral_nonneg fun ω => Real.rpow_nonneg (mul_nonneg hc.le ENNReal.toReal_nonneg) _
  refine ⟨(1 + q * L) * ∫ ω, G ω ∂P, fun x hx => ?_⟩
  have hpath : ∀ᵐ ω ∂P,
      bpzRootedMixedReal γ r ρ k₁ k₂ x (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) ≤ G ω ∧
      |-q * bpzRootedMixedReal γ r ρ k₁ k₂ x (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - 1) *
        bpzRootedMixedDerivApply γ r ρ k₁ k₂ x v (regularizedGMC P Xc γ r ω) (M ω)| ≤
        q * L * G ω := by
    filter_upwards [bpzWard_cut_integrable hd hp, hp.k₂_int,
      bpzWard_far_mass_pos hp hd.D_meas] with ω h1 h2 hpos
    have hlim := integrable_bpz_lim_part (γ := γ) hd.ρ_meas hd.k₂_meas hd.ρ_le_one hd.k₂_nonneg
      h2 hd.δ_pos hd.δ_r (hd.sep x hx) (Metric.mem_ball_self hd.δ_pos)
    set J := bpzRootedMixedReal γ r ρ k₁ k₂ x _ (M ω) with hJdef
    have hJ := hlow (regularizedGMC P Xc γ r ω) (M ω) x (hR x hx) hlim
    have hcpos := mul_pos hc hpos
    have hJpos : 0 < J := lt_of_lt_of_le hcpos hJ
    have hJq : J ^ (-q) ≤ G ω := Real.rpow_le_rpow_of_nonpos hcpos hJ (by linarith)
    have hS := abs_bpzRootedMixedDerivApply_le hd.ρ_nonneg hd.ρ_le_one hk₁0 hd.k₂_nonneg (integrable_bpz_cut_part hd.ρ_meas (measurable_bpzWardCutWeight hd) hd.ρ_nonneg hk₁0 h1 x)
      hlim v
    refine ⟨hJq, ?_⟩
    have hJq1 : 0 ≤ J ^ (-q - 1) := Real.rpow_nonneg hJpos.le _
    calc |-q * J ^ (-q - 1) * bpzRootedMixedDerivApply γ r ρ k₁ k₂ x v
          (regularizedGMC P Xc γ r ω) (M ω)|
        = q * J ^ (-q - 1) * |bpzRootedMixedDerivApply γ r ρ k₁ k₂ x v
            (regularizedGMC P Xc γ r ω) (M ω)| := by
          rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hq0, abs_of_nonneg hJq1]
      _ ≤ q * J ^ (-q - 1) * (L * J) :=
          by bound
      _ = q * L * J ^ (-q - 1 + 1) := by rw [Real.rpow_add_one hJpos.ne']; ring
      _ = q * L * J ^ (-q) := by simp
      _ ≤ q * L * G ω := by bound
  constructor
  · rw [abs_of_nonneg (integral_nonneg fun ω => Real.rpow_nonneg
      (bpzRootedMixedReal_nonneg hd.ρ_nonneg hd.ρ_le_one hk₁0 hd.k₂_nonneg x ..) _)]
    calc ∫ ω, bpzRootedMixedReal γ r ρ k₁ k₂ x _ (M ω) ^ (-q) ∂P
        ≤ ∫ ω, G ω ∂P := integral_mono_of_nonneg (Eventually.of_forall fun ω =>
          Real.rpow_nonneg (bpzRootedMixedReal_nonneg hd.ρ_nonneg hd.ρ_le_one hk₁0
            hd.k₂_nonneg x ..) _) hGi (hpath.mono fun ω h => h.1)
      _ ≤ (1 + q * L) * ∫ ω, G ω ∂P :=
          le_mul_of_one_le_left hG0 (by nlinarith)
  · calc |∫ ω, -q * bpzRootedMixedReal γ r ρ k₁ k₂ x _ (M ω) ^
          (-q - 1) * bpzRootedMixedDerivApply γ r ρ k₁ k₂ x v _ (M ω)
          ∂P| ≤ ∫ ω, q * L * G ω ∂P := by
          exact norm_integral_le_of_norm_le (hGi.const_mul _)
            (hpath.mono fun ω h => by rw [Real.norm_eq_abs]; exact h.2)
      _ = q * L * ∫ ω, G ω ∂P := integral_const_mul ..
      _ ≤ (1 + q * L) * ∫ ω, G ω ∂P := mul_le_mul_of_nonneg_right (by linarith) hG0

/-- Integration by parts against the rooted moment. -/
theorem bpzWard_ibp :
    ∫ x, fderiv ℝ (fun x => φ x * kt x) x v *
        ∫ ω, bpzRootedMixedReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x
          (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) ∂P =
      q * ∫ x, φ x * kt x *
        ∫ ω, bpzRootedMixedReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x
            (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - 1) *
          bpzRootedMixedDerivApply γ r ρ (bpzWardCutWeight γ q r kt) k₂ x v
            (regularizedGMC P Xc γ r ω) (M ω) ∂P := by
  have : IsProbabilityMeasure P := hp.hX.1
  set k₁ := bpzWardCutWeight γ q r kt with hk₁def
  have hk₁m : Measurable k₁ := measurable_bpzWardCutWeight hd
  set f : ℂ → ℝ := fun x => φ x * kt x with hf
  set Ψ : ℂ → ℝ := fun x => ∫ ω, bpzRootedMixedReal γ r ρ k₁ k₂ x
    (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) ∂P with hΨ
  set E : ℂ → ℝ := fun x => ∫ ω, bpzRootedMixedReal γ r ρ k₁ k₂ x
    (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - 1) *
      bpzRootedMixedDerivApply γ r ρ k₁ k₂ x v (regularizedGMC P Xc γ r ω) (M ω) ∂P with hE
  set Ψ' : ℂ → ℝ := fun x => ∫ ω, -q * bpzRootedMixedReal γ r ρ k₁ k₂ x
    (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - 1) *
      bpzRootedMixedDerivApply γ r ρ k₁ k₂ x v (regularizedGMC P Xc γ r ω) (M ω) ∂P with hΨ'
  have hΨ'E : ∀ x, Ψ' x = -q * E x := by
    intro x
    simp only [hΨ', hE]
    rw [← integral_const_mul]
    ring
  have hJm := measurable_bpzWard_J (γ := γ) (r := r) P X hp.hX M hp.hMm hp.hM.1 Xc hp.hXc
    hd.ρ_meas hk₁m hd.k₂_meas
  have hSm := measurable_bpzWard_S (γ := γ) (r := r) P X hp.hX M hp.hMm hp.hM.1 Xc hp.hXc
    hd.ρ_meas hk₁m hd.k₂_meas v
  have hΨm : AEStronglyMeasurable Ψ volume :=
    ((hJm.pow_const (-q)).stronglyMeasurable.integral_prod_left' (μ := P)).aestronglyMeasurable
  have hΨ'm : AEStronglyMeasurable Ψ' volume :=
    (((measurable_const.mul (hJm.pow_const _)).mul hSm).stronglyMeasurable.integral_prod_left'
      (μ := P)).aestronglyMeasurable
  obtain ⟨K, hK⟩ := bpzWard_Psi_bounds hd hp v
  have hfc : Continuous f := hd.f_C1.continuous
  have hfcs : HasCompactSupport f := hd.φ_compact.mul_right
  have hf'c : Continuous fun x => fderiv ℝ f x v :=
    (hd.f_C1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hf'cs : HasCompactSupport fun x => fderiv ℝ f x v :=
    (hfcs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) (by simp)
  have htsf : tsupport f ⊆ tsupport φ := tsupport_mul_subset_left
  have htsf' : tsupport (fun x => fderiv ℝ f x v) ⊆ tsupport φ :=
    ((tsupport_comp_subset (g := fun L : ℂ →L[ℝ] ℝ => L v) (by simp) _).trans
      (tsupport_fderiv_subset ℝ)).trans htsf
  have hf'g : Integrable (fun x => ContinuousLinearMap.mul ℝ ℝ (fderiv ℝ f x v) (Ψ x)) := by
    exact bpz_integrable_mul_of_bdd_on_tsupport hf'c hf'cs hΨm fun x hx => (hK x (htsf' hx)).1
  have hfg' : Integrable (fun x => ContinuousLinearMap.mul ℝ ℝ (f x) (Ψ' x)) := by
    exact bpz_integrable_mul_of_bdd_on_tsupport hfc hfcs hΨ'm fun x hx => (hK x (htsf hx)).2
  have hfg : Integrable (fun x => ContinuousLinearMap.mul ℝ ℝ (f x) (Ψ x)) := by
    exact bpz_integrable_mul_of_bdd_on_tsupport hfc hfcs hΨm fun x hx => (hK x (htsf hx)).1
  have hfd : ∀ x ∈ tsupport Ψ, HasLineDerivAt ℝ f (fderiv ℝ f x v) x v := fun x _ =>
    ((hd.f_C1.differentiable one_ne_zero) x).hasFDerivAt.hasLineDerivAt v
  have hgd : ∀ x ∈ tsupport f, HasLineDerivAt ℝ Ψ (Ψ' x) x v := fun x hx =>
    bpzWard_hasLineDerivAt_Psi hd hp (htsf hx) v
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable hf'g hfg' hfg
    hfd hgd
  simp only [ContinuousLinearMap.mul_apply'] at key
  have hfE : ∀ x, f x * Ψ' x = -q * (f x * E x) := fun x => by rw [hΨ'E]; ring
  simp_rw [hfE] at key
  rw [integral_const_mul] at key
  change ∫ x, fderiv ℝ f x v * Ψ x = q * ∫ x, f x * E x
  linarith

/-- **The cutoff Ward identity.** For the mixed mass `Î` (the cutoff chaos with the pinned
weight `k₁` on `{ρ > 0}` and the limit chaos with the weight `k₂` elsewhere),
`E[Î^{-q} ∫ ∂_v(φ k̃) |x|₊⁴ e^{γ² q h_r} dM_r] = q E[Î^{-q-1} ∫ φ k₁ Ŷ_v dM_r]`. -/
theorem bpzWard_cutoff_identity :
    ∫ ω, bpzMixedReal ρ (bpzWardCutWeight γ q r kt) k₂ (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) *
        ∫ x, bpzWardLeftWeight γ q r kt φ v x ∂regularizedGMC P Xc γ r ω ∂P =
      q * ∫ ω, bpzMixedReal ρ (bpzWardCutWeight γ q r kt) k₂ (regularizedGMC P Xc γ r ω) (M ω) ^
        (-q - 1) * ∫ x, φ x * bpzWardCutWeight γ q r kt x * bpzMixedDerivReal γ r ρ
          (bpzWardCutWeight γ q r kt) k₂ x v (regularizedGMC P Xc γ r ω) (M ω)
          ∂regularizedGMC P Xc γ r ω ∂P := by
  rw [bpzWard_left_deroot hd hp v, bpzWard_right_deroot hd hp v]
  exact bpzWard_ibp hd hp v

end

end DOZZ.Proofs
