/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.MomentMeas
public import DOZZ.FourPoint.BPZ.WardDefs

/-! # The complex combination of the four real Ward left sides -/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ χ α₁ α₂ α₃ : ℝ}

private def wclComb (a b c d : ℝ) : ℂ :=
  ((a : ℂ) + Complex.I * (b : ℂ) - Complex.I * (c : ℂ) + (d : ℂ)) / 2

section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
include μ

private lemma wcl_integral_comb {a b c d : α → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) (hc : Integrable c μ) (hd : Integrable d μ) :
    wclComb (∫ t, a t ∂μ) (∫ t, b t ∂μ) (∫ t, c t ∂μ) (∫ t, d t ∂μ) =
      ∫ t, wclComb (a t) (b t) (c t) (d t) ∂μ := by
  unfold wclComb
  have h1 : Integrable (fun t => (a t : ℂ)) μ := ha.ofReal
  have h2 : Integrable (fun t => Complex.I * (b t : ℂ)) μ := hb.ofReal.const_mul _
  have h3 : Integrable (fun t => Complex.I * (c t : ℂ)) μ := hc.ofReal.const_mul _
  have h4 : Integrable (fun t => (d t : ℂ)) μ := hd.ofReal
  have h12 : Integrable (fun t => (a t : ℂ) + Complex.I * (b t : ℂ)) μ := h1.add h2
  have h123 : Integrable (fun t => (a t : ℂ) + Complex.I * (b t : ℂ) - Complex.I * (c t : ℂ)) μ := h12.sub h3
  rw [integral_div, integral_add h123 h4, integral_sub h12 h3, integral_add h1 h2]
  simp [integral_const_mul, integral_complex_ofReal]

private lemma wcl_integral_three {f g h : α → ℂ}
    (c₀ c₁ c₂ : ℂ) (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    ∫ t, (c₀ * f t + c₁ * g t + c₂ * h t) ∂μ =
      c₀ * ∫ t, f t ∂μ + c₁ * ∫ t, g t ∂μ + c₂ * ∫ t, h t ∂μ := by
  have h01 : Integrable (fun t => c₀ * f t + c₁ * g t) μ := (hf.const_mul c₀).add (hg.const_mul c₁)
  rw [integral_add h01 (hh.const_mul c₂), integral_add (hf.const_mul c₀) (hg.const_mul c₁),
    integral_const_mul, integral_const_mul, integral_const_mul]


end
private lemma wcl_elem_bounds {k : ℝ} (hk : 0 ≤ k) (x z : ℂ) :
    k ≤ (1 + ‖x - z‖ ^ (-2 : ℝ)) * k ∧
    ‖(k : ℂ) / (z - x)‖ ≤ (1 + ‖x - z‖ ^ (-2 : ℝ)) * k ∧
    ‖(k : ℂ) / (z - x) ^ 2‖ ≤ (1 + ‖x - z‖ ^ (-2 : ℝ)) * k := by
  have hnn := bpz_rpow_neg_two_nonneg (norm_nonneg (x - z))
  refine ⟨le_mul_of_one_le_left hk (by linarith), ?_, ?_⟩
  · rcases eq_or_ne x z with rfl | hxz
    · rw [sub_self, div_zero, norm_zero]; positivity
    · have ht : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hk, norm_sub_rev z x,
        bpz_rpow_neg_two ht.le, div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_right ?_ hk
      rw [← inv_pow]; linarith [sq_nonneg (‖x - z‖⁻¹ - 1 / 2)]
  · rcases eq_or_ne x z with rfl | hxz
    · rw [sub_self, zero_pow two_ne_zero, div_zero, norm_zero]; positivity
    · have ht : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hk, norm_sub_rev z x,
        bpz_rpow_neg_two ht.le, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right (by linarith [inv_nonneg.mpr (sq_nonneg ‖x - z‖)]) hk

/-- **The combination of the four real Ward left sides.** For the test functions `Re g`, `Im g`
in the directions `1`, `i`, the combination `(L_{Re,1} + i L_{Im,1} - i L_{Re,i} + L_{Im,i}) / 2`
of the left sides `bpzWardLHS` is the explicit combination of the moments `J`, `E₁`, `D₁`. -/
theorem bpz_wardLHS_combination (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) :
    ((bpzWardLHS P M γ χ α₁ α₂ α₃ s z Complex.reCLM 1 : ℂ) +
        Complex.I * (bpzWardLHS P M γ χ α₁ α₂ α₃ s z Complex.imCLM 1 : ℂ) -
        Complex.I * (bpzWardLHS P M γ χ α₁ α₂ α₃ s z Complex.reCLM Complex.I : ℂ) +
        (bpzWardLHS P M γ χ α₁ α₂ α₃ s z Complex.imCLM Complex.I : ℂ)) / 2 =
      ((-1 - γ * χ / 2 + γ * (α₁ + α₂) / 2 : ℝ) : ℂ) * (bpzMomJ P M γ χ α₁ α₂ α₃ s z : ℂ) +
        (((γ * χ / 2 : ℝ) : ℂ) * (2 * z - 1) - ((γ * α₁ / 2 : ℝ) : ℂ) * (z - 1) -
          ((γ * α₂ / 2 : ℝ) : ℂ) * z) * bpzMomE1 P M γ χ α₁ α₂ α₃ s z +
        ((1 - γ * χ / 2 : ℝ) : ℂ) * (z * (z - 1)) * bpzMomD1 P M γ χ α₁ α₂ α₃ s z := by
  let k := bpzSoftWeight γ χ α₁ α₂ α₃ 0 z
  let g (x : ℂ) := (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x
  let F (ℓ : ℂ →L[ℝ] ℝ) (v x : ℂ) : ℝ :=
    fderiv ℝ (fun x => ℓ (bpzG z x) * bpzTildeWeight γ χ α₁ α₂ z x) x v *
      normPlus x ^ (γ * (α₁ + α₂ + α₃ - χ))
  let c₀ : ℂ := ((-1 - γ * χ / 2 + γ * (α₁ + α₂) / 2 : ℝ) : ℂ)
  let c₁ : ℂ := ((γ * χ / 2 : ℝ) : ℂ) * (2 * z - 1) - ((γ * α₁ / 2 : ℝ) : ℂ) * (z - 1) -
    ((γ * α₂ / 2 : ℝ) : ℂ) * z
  let c₂ : ℂ := ((1 - γ * χ / 2 : ℝ) : ℂ) * (z * (z - 1))
  have hFm (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) : Measurable (F ℓ v) :=
    (measurable_fderiv_apply_const ℝ _ v).mul (bpz_measurable_normPlus.pow_const _)
  have hFb (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ bpzRegular z, |F ℓ v x| ≤ A * g x := by
    obtain ⟨A, hA0, hA⟩ := bpz_g_fderiv_bound (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) hz0 hz1 ℓ v
    refine ⟨A, hA0, fun x hx => ?_⟩
    have hn : 0 ≤ normPlus x ^ (γ * (α₁ + α₂ + α₃ - χ)) := Real.rpow_nonneg (bpz_normPlus_pos x).le _
    dsimp [F, g, k]
    rw [abs_mul, abs_of_nonneg hn, bpzSoftWeight_zero_eq]
    exact (mul_le_mul_of_nonneg_right (hA x hx) hn).trans_eq (by ring)
  have hq1 : 1 ≤ s + 1 := by linarith
  have hgood : ∀ᵐ ω ∂P, Integrable g (M ω) ∧ 0 < ∫ x, k x ∂M ω ∧ ∀ᵐ x ∂M ω, x ∈ bpzRegular z := by
    filter_upwards [bpz_singular_integrable_ae P X hX hγ hγ2 M hM hχ hα₁ hα₂ hα₃ hq1 hz0 hz1,
      bpz_ae_regular P X hX hγ hγ2 M hM z] with ω hω hreg
    have hI := bpzSoftI_eq_toReal (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) 0 (M ω) z
    rw [bpzSoftI_eq_integral] at hI
    exact ⟨hω.1, hI ▸ ENNReal.toReal_pos hω.2.1.ne' hω.2.2.ne, hreg⟩
  have hdom : Integrable (fun ω => (∫ x, k x ∂M ω) ^ (-(s + 1)) * ∫ x, g x ∂M ω) P :=
    bpz_singular_dom_integrable P X hX hγ hγ2 M hM hMm hχ hα₁ hα₂ hα₃ hq1 hz0 hz1
  have hdom' : Integrable (fun ω => (∫ x, k x ∂M ω) ^ (-s - 1) * ∫ x, g x ∂M ω) P := by
    rwa [show -s - 1 = -(s + 1) by ring]
  have hIm : Measurable fun ω => ∫ x, k x ∂M ω :=
    (measurable_integral_measure (measurable_bpzSoftWeight 0 z)).comp hMm
  have houtF (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
      Integrable (fun ω => (∫ x, k x ∂M ω) ^ (-(s + 1)) * ∫ x, F ℓ v x ∂M ω) P := by
    obtain ⟨A, -, hA⟩ := hFb ℓ v
    refine (hdom.const_mul A).mono'
      ((hIm.pow_const _).mul ((measurable_integral_measure (hFm ℓ v)).comp hMm)).aestronglyMeasurable ?_
    filter_upwards [hgood] with ω hω
    have h0 := Real.rpow_nonneg hω.2.1.le (-(s + 1))
    have hint : ‖∫ x, F ℓ v x ∂M ω‖ ≤ A * ∫ x, g x ∂M ω := by
      rw [← integral_const_mul]
      exact norm_integral_le_of_norm_le (hω.1.const_mul A)
        (hω.2.2.mono fun x hx => by rw [Real.norm_eq_abs]; exact hA x hx)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, ← Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hint h0).trans_eq (by ring)
  have houtC {f : ℂ → ℂ} (hf : Measurable f) (hfg : ∀ x, ‖f x‖ ≤ g x) :
      Integrable (fun ω => (((∫ x, k x ∂M ω) ^ (-s - 1) : ℝ) : ℂ) * ∫ x, f x ∂M ω) P := by
    refine hdom'.mono' ((Complex.measurable_ofReal.comp (hIm.pow_const _)).aestronglyMeasurable.mul
      ((bpz_stronglyMeasurable_integral_measure hf.stronglyMeasurable).comp_measurable hMm).aestronglyMeasurable) ?_
    filter_upwards [hgood] with ω hω
    have h0 := Real.rpow_nonneg hω.2.1.le (-s - 1)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hω.1 (Eventually.of_forall hfg)) h0
  have hJr : Integrable (fun ω => (∫ x, k x ∂M ω) ^ (-s)) P := by
    refine hdom'.mono' (hIm.pow_const (-s)).aestronglyMeasurable ?_
    filter_upwards [hgood] with ω hω
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hω.2.1.le (-s))]
    refine (bpzRpow_pred_mul hω.2.1 (-s)).symm.trans_le (mul_le_mul_of_nonneg_left
      (integral_mono (hω.1.mono' (measurable_bpzSoftWeight 0 z).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (bpzSoftWeight_nonneg 0 z x)]
          exact (wcl_elem_bounds (bpzSoftWeight_nonneg 0 z x) x z).1))
        hω.1 fun x => (wcl_elem_bounds (bpzSoftWeight_nonneg 0 z x) x z).1)
      (Real.rpow_nonneg hω.2.1.le _))
  have hJ : Integrable (fun ω => (((∫ x, k x ∂M ω) ^ (-s) : ℝ) : ℂ)) P := hJr.ofReal
  have hkm : Measurable fun x => ((k x : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_bpzSoftWeight 0 z)
  have hE := houtC (f := fun x => ((k x : ℝ) : ℂ) / (z - x)) (hkm.div (measurable_const.sub measurable_id))
    fun x => (wcl_elem_bounds (bpzSoftWeight_nonneg 0 z x) x z).2.1
  have hD := houtC (f := fun x => ((k x : ℝ) : ℂ) / (z - x) ^ 2)
    (hkm.div ((measurable_const.sub measurable_id).pow_const 2))
    fun x => (wcl_elem_bounds (bpzSoftWeight_nonneg 0 z x) x z).2.2
  change wclComb (bpzWardLHS P M γ χ α₁ α₂ α₃ s z Complex.reCLM 1)
      (bpzWardLHS P M γ χ α₁ α₂ α₃ s z Complex.imCLM 1)
      (bpzWardLHS P M γ χ α₁ α₂ α₃ s z Complex.reCLM Complex.I)
      (bpzWardLHS P M γ χ α₁ α₂ α₃ s z Complex.imCLM Complex.I) =
    c₀ * (bpzMomJ P M γ χ α₁ α₂ α₃ s z : ℂ) + c₁ * bpzMomE1 P M γ χ α₁ α₂ α₃ s z +
      c₂ * bpzMomD1 P M γ χ α₁ α₂ α₃ s z
  have hLHS (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) : bpzWardLHS P M γ χ α₁ α₂ α₃ s z ℓ v =
      ∫ ω, (∫ x, k x ∂M ω) ^ (-(s + 1)) * ∫ x, F ℓ v x ∂M ω ∂P := rfl
  dsimp only [bpzMomJ, bpzMomE1, bpzMomD1]
  rw [hLHS, hLHS, hLHS, hLHS, wcl_integral_comb (houtF _ _) (houtF _ _) (houtF _ _) (houtF _ _),
    ← integral_complex_ofReal, ← wcl_integral_three c₀ c₁ c₂ hJ hE hD]
  refine integral_congr_ae (hgood.mono fun ω ⟨hg, hpos, hreg⟩ => ?_)
  have hcomb_mul (r a b c d : ℝ) : wclComb (r * a) (r * b) (r * c) (r * d) = (r : ℂ) * wclComb a b c d := by
    unfold wclComb; push_cast; ring
  have hintF (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) : Integrable (F ℓ v) (M ω) := by
    obtain ⟨A, -, hA⟩ := hFb ℓ v
    exact (hg.const_mul A).mono' (hFm ℓ v).aestronglyMeasurable
      (hreg.mono fun x hx => by rw [Real.norm_eq_abs]; exact hA x hx)
  have hk_int : Integrable (fun x => ((k x : ℝ) : ℂ)) (M ω) :=
    (hg.mono' (measurable_bpzSoftWeight 0 z).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (bpzSoftWeight_nonneg 0 z x)]
      exact (wcl_elem_bounds (bpzSoftWeight_nonneg 0 z x) x z).1)).ofReal
  have he1_int : Integrable (fun x => ((k x : ℝ) : ℂ) / (z - x)) (M ω) :=
    hg.mono' (hkm.div (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun x => (wcl_elem_bounds (bpzSoftWeight_nonneg 0 z x) x z).2.1)
  have hd1_int : Integrable (fun x => ((k x : ℝ) : ℂ) / (z - x) ^ 2) (M ω) :=
    hg.mono' (hkm.div ((measurable_const.sub measurable_id).pow_const 2)).aestronglyMeasurable
      (Eventually.of_forall fun x => (wcl_elem_bounds (bpzSoftWeight_nonneg 0 z x) x z).2.2)
  have hinner : wclComb (∫ x, F Complex.reCLM 1 x ∂M ω) (∫ x, F Complex.imCLM 1 x ∂M ω)
        (∫ x, F Complex.reCLM Complex.I x ∂M ω) (∫ x, F Complex.imCLM Complex.I x ∂M ω) =
      c₀ * ((∫ x, k x ∂M ω : ℝ) : ℂ) + c₁ * ∫ x, ((k x : ℝ) : ℂ) / (z - x) ∂M ω +
        c₂ * ∫ x, ((k x : ℝ) : ℂ) / (z - x) ^ 2 ∂M ω := by
    rw [wcl_integral_comb (hintF _ _) (hintF _ _) (hintF _ _) (hintF _ _),
      ← integral_complex_ofReal, ← wcl_integral_three c₀ c₁ c₂ hk_int he1_int hd1_int]
    refine integral_congr_ae (hreg.mono fun x hx => ?_)
    have hW := bpz_wirtinger_g_tildeWeight (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) hx
    rw [bpz_g_coefficients hx] at hW
    dsimp [wclComb, F, k, c₀, c₁, c₂]
    simp only [show bpzG = bpzGfun from rfl]
    rw [bpzSoftWeight_zero_eq]
    generalize normPlus x ^ (γ * (α₁ + α₂ + α₃ - χ)) = r
    push_cast at hW ⊢
    linear_combination (r : ℂ) * hW
  dsimp only
  rw [hcomb_mul, hinner, show -(s + 1) = -s - 1 by ring]
  have hIc : (((∫ x, k x ∂M ω) ^ (-s - 1) : ℝ) : ℂ) * ((∫ x, k x ∂M ω : ℝ) : ℂ) =
      (((∫ x, k x ∂M ω) ^ (-s) : ℝ) : ℂ) := mod_cast bpzRpow_pred_mul hpos (-s)
  linear_combination c₀ * hIc

end DOZZ.Proofs
