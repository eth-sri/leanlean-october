module

public import RequestProject.CircleAnalysisNotation

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import RequestProject.Reparam
public import RequestProject.CurveContinuity
public import RequestProject.PlanarNotation

/-!
# Rescaled-arclength parametrizations of Lipschitz Jordan curves

A Lipschitz, `2π`-periodic curve `γ` which is injective on `[0, 2π)` can be reparametrized by
rescaled arclength: there is a curve `γ̃` with the same image of `[0, 2π]`, again Lipschitz,
`2π`-periodic and injective on `[0, 2π)`, with `‖γ̃'‖` equal to a positive constant almost
everywhere, with the same signed-area integral `∫₀^{2π} Im(conj γ · γ')`, and with
`γ = γ̃ ∘ τ` for a monotone Lipschitz `τ` fixing `0` and `2π` (`exists_constSpeed_reparam`).
Reversing the direction changes the sign of this integral
(`exists_reverse_param`).

These are the analytic steps that turn a Lipschitz Jordan parametrization of the boundary into
a positively oriented rescaled-arclength parametrization (Definition 10.1 of the paper).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- The signed-area integrand `Im(conj γ · γ')`. -/
def signedAreaDensity (γ : ℝ → ℂ) (θ : ℝ) : ℝ := (conj (γ θ) * deriv γ θ).im

lemma norm_deriv_le_of_lipschitzWith {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (x : ℝ) : ‖deriv γ x‖ ≤ K :=
  norm_deriv_le_of_lipschitz hK

lemma locallyIntegrable_of_bounded {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ → F} {M : ℝ} (hf : AEStronglyMeasurable f volume) (hB : ∀ x, ‖f x‖ ≤ M) :
    LocallyIntegrable f volume := by
  refine locallyIntegrable_iff.mpr fun k hk => ?_
  exact Measure.integrableOn_of_bounded (M := M) hk.measure_lt_top.ne
    hf (Eventually.of_forall hB)

/-- The primitive of a bounded locally integrable function is Lipschitz. -/
lemma lipschitzWith_primitive {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {M : NNReal} (hf : AEStronglyMeasurable f volume) (hB : ∀ x, ‖f x‖ ≤ M)
    (a : ℝ) : LipschitzWith M (fun x => ∫ t in a..x, f t) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_of_bounded hf hB _ _) (intervalIntegrable_of_bounded hf hB _ _),
    Real.dist_eq]
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => hB t

/-- Fundamental theorem of calculus for Lipschitz curves. -/
theorem integral_deriv_of_lipschitz {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (a b : ℝ) : ∫ x in a..b, deriv γ x = γ b - γ a := by
  
  
  have hg  := hK.sub (lipschitzWith_primitive (measurable_deriv γ).aestronglyMeasurable
    (norm_deriv_le_of_lipschitzWith hK) a)
  have g_ac  :=
    (hg.lipschitzOnWith (s := uIcc a b)).absolutelyContinuousOnInterval
  have g_ae : ∀ᵐ x, x ∈ uIcc a b →
      HasDerivAt (fun x => γ x - ∫ t in a..x, deriv γ t) 0 x := by
    filter_upwards [hK.ae_differentiableAt ,
      LocallyIntegrable.ae_hasDerivAt_integral (locallyIntegrable_of_bounded (measurable_deriv γ).aestronglyMeasurable
        (norm_deriv_le_of_lipschitzWith hK))] with x hx₁ hx₂ _
    have := hx₁.hasDerivAt.sub (hx₂ a)
    rw [sub_self] at this
    exact this
  obtain ⟨C, hC⟩ := g_ac.const_of_ae_hasDerivAt_zero g_ae
  have h1 := hC a (by simp)
  have h2 := hC b (by simp)
  simp at h1 h2
  rw [← h1] at h2
  linear_combination -h2

/-- The arclength function `ℓ(θ) = ∫₀^θ ‖γ'‖`. -/
def arcLen (γ : ℝ → ℂ) (θ : ℝ) : ℝ := ∫ t in (0 : ℝ)..θ, ‖deriv γ t‖

section ArcLen

variable {γ : ℝ → ℂ} {K : NNReal}

lemma aestronglyMeasurable_norm_deriv (γ : ℝ → ℂ) :
    AEStronglyMeasurable (fun t => ‖deriv γ t‖) volume :=
  (by fun_prop)

section

variable (hK : LipschitzWith K γ) (a : ℝ) (hper : Function.Periodic γ anglePeriod) (b : ℝ)
include hK

lemma norm_norm_deriv_le (t : ℝ) : ‖‖deriv γ t‖‖ ≤ K := by
  rw [norm_norm]; exact norm_deriv_le_of_lipschitzWith hK t

lemma intervalIntegrable_norm_deriv :
    IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b :=
  intervalIntegrable_of_bounded (aestronglyMeasurable_norm_deriv γ) (norm_norm_deriv_le hK) a b

lemma arcLen_sub :
    arcLen γ b - arcLen γ a = ∫ t in a..b, ‖deriv γ t‖ :=
  intervalIntegral.integral_interval_sub_left (intervalIntegrable_norm_deriv hK _ _)
    (intervalIntegrable_norm_deriv hK _ _)

lemma arcLen_lipschitz : LipschitzWith K (arcLen γ) :=
  lipschitzWith_primitive (aestronglyMeasurable_norm_deriv γ) (norm_norm_deriv_le hK) 0

lemma arcLen_monotone : Monotone (arcLen γ) := by
  intro a b hab
  have := arcLen_sub hK a b
  have h0 : 0 ≤ ∫ t in a..b, ‖deriv γ t‖ :=
    intervalIntegral.integral_nonneg hab fun t _ => norm_nonneg _
  linarith

lemma norm_sub_le_arcLen {a b : ℝ} (hab : a ≤ b) :
    ‖γ b - γ a‖ ≤ arcLen γ b - arcLen γ a := by
  rw [arcLen_sub hK, ← integral_deriv_of_lipschitz hK]
  exact intervalIntegral.norm_integral_le_integral_norm hab

include hper in
lemma arcLen_add_period
    (θ : ℝ) : arcLen γ (θ + anglePeriod) = arcLen γ θ + arcLen γ anglePeriod := by
  have hd : Function.Periodic (fun t => ‖deriv γ t‖) anglePeriod := fun t => by
    have  := funext hper
    simp only
    rw [← deriv_comp_add_const, this]
  have h1 := arcLen_sub hK θ (θ + anglePeriod)
  have h2  :=
    hd.intervalIntegral_add_eq θ 0
  rw [zero_add] at h2
  unfold arcLen at h1 ⊢
  linarith

include hper in
lemma arcLen_strictMono
    (hinj : InjOn γ angleIco) : StrictMono (arcLen γ) := by
  refine (arcLen_monotone hK).strictMono_of_injective fun a b hab => ?_
  by_contra hne
  wlog hlt : a < b generalizing a b
  · exact (by grind)
  have hconst : ∀ x ∈ Icc a b, γ x = γ a := by
    intro x hx
    
    have h2 := arcLen_monotone hK hx.2
    have h3 := norm_sub_le_arcLen hK hx.1
    have : ‖γ x - γ a‖ ≤ 0 := by linarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hp : 0 < anglePeriod := by positivity
  set x0 := toIcoMod hp 0 a with hx0
  have hx0mem : x0 ∈ angleIco := by
    have := toIcoMod_mem_Ico hp 0 a
    simpa using this
  have hshift : ∀ t, γ (x0 + t) = γ (a + t) := by
    intro t
    rw [hx0, toIcoMod, sub_add_eq_add_sub, hper.sub_zsmul_eq]
  set δ := min (b - a) (anglePeriod - x0) / 2 with hδ
  have hδpos : 0 < δ := by
    have : 0 < b - a := by linarith
    have : 0 < anglePeriod - x0 := by linarith [hx0mem.2]
    positivity
  have hδ1 : δ < b - a := by
    have := min_le_left (b - a) (anglePeriod - x0); linarith
  have hδ2 : δ < anglePeriod - x0 := by
    have := min_le_right (b - a) (anglePeriod - x0); linarith
  
  have heq : γ (x0 + δ) = γ x0 := by
    rw [hshift δ, ← add_zero x0, hshift 0, add_zero,
      hconst (a + δ) ⟨by linarith, by linarith⟩]
  have := hinj (⟨by linarith [hx0mem.1], by linarith⟩) hx0mem heq
  linarith

lemma ae_hasDerivAt_arcLen :
    ∀ᵐ θ, HasDerivAt (arcLen γ) ‖deriv γ θ‖ θ := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral
    (locallyIntegrable_of_bounded (aestronglyMeasurable_norm_deriv γ)
      (norm_norm_deriv_le hK))] with θ hθ
  exact hθ 0

end

end ArcLen

/-- Lipschitz maps of `ℝ` send null sets to null sets. -/
lemma volume_image_eq_zero_of_lipschitz {f : ℝ → ℝ} {Kf : NNReal} (hf : LipschitzWith Kf f)
    {B : Set ℝ} (hB : volume B = 0) : volume (f '' B) = 0 := by
  have h := hf.hausdorffMeasure_image_le (d := 1) zero_le_one B
  rw [hausdorffMeasure_real, hB, mul_zero] at h
  exact le_antisymm h zero_le

/-- A function of `ℝ` sends the set where its derivative vanishes to a null set. -/
lemma volume_image_eq_zero_of_hasDerivAt_zero {f : ℝ → ℝ} {A : Set ℝ}
    (hA : ∀ x ∈ A, HasDerivAt f 0 x) : volume (f '' A) = 0 := by
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
    (f' := fun _ => 0) (fun x hx => ?_) (fun x _ => by simp)
  have := (hA x hx).hasFDerivAt.hasFDerivWithinAt (s := A)
  simpa using this

/-- A periodic function bounded on one period is bounded. -/
lemma abs_le_of_periodic {g : ℝ → ℝ} (hg : Function.Periodic g anglePeriod) {M : ℝ}
    (hb : ∀ x ∈ angleIco, |g x| ≤ M) (x : ℝ) : |g x| ≤ M := by
  have hp : 0 < anglePeriod := by positivity
  have hmem := toIcoMod_mem_Ico hp 0 x
  rw [zero_add] at hmem
  have : g (toIcoMod hp 0 x) = g x := by rw [toIcoMod, hg.sub_zsmul_eq]
  rw [← this]
  exact hb _ hmem

/-- Change of variables `t = e θ` for an order isomorphism `e` of `ℝ` that is Lipschitz and fixes
`0` and `2π`. -/
lemma integral_comp_orderIso {e : ℝ ≃o ℝ} {Ke : NNReal} (he : LipschitzWith Ke e)
    (h0 : e 0 = 0) (h2 : e anglePeriod = anglePeriod) (F : ℝ → ℝ) :
    ∫ₚ t, F t = ∫ₚ θ, deriv e θ * F (e θ) := by
  have hp : 0 ≤ anglePeriod := by positivity
  set D := {θ : ℝ | DifferentiableAt ℝ e θ} with hD
  have hDm  := measurableSet_of_differentiableAt ℝ e
  have hDc : volume Dᶜ = 0 := by
    have := he.ae_differentiableAt (μ := volume)
    exact this
  set S := angleInterior ∩ D with hS
  have hSm : MeasurableSet S := measurableSet_Ioo.inter hDm
  have hcv := integral_image_eq_integral_abs_deriv_smul hSm
    (fun x hx => (hx.2.hasDerivAt).hasDerivWithinAt) e.injective.injOn F
  have hmaps : ∀ x ∈ angleInterior, e x ∈ angleInterior := fun x hx =>
    ⟨h0 ▸ e.strictMono hx.1, h2 ▸ e.strictMono hx.2⟩
  have himg : e '' S =ᵐ[volume] angleInterior := by
    refine ae_eq_set.mpr ⟨?_, ?_⟩
    · have : e '' S \ angleInterior = ∅ := by
        rw [diff_eq_empty]
        rintro _ ⟨x, hx, rfl⟩
        exact hmaps x hx.1
      rw [this, measure_empty]
    · refine measure_mono_null ?_ (volume_image_eq_zero_of_lipschitz he hDc)
      intro t ⟨ht, htS⟩
      refine ⟨e.symm t, ?_, e.apply_symm_apply t⟩
      intro hd
      apply htS
      refine ⟨e.symm t, ⟨⟨?_, ?_⟩, hd⟩, e.apply_symm_apply t⟩
      · rw [← e.symm_apply_apply 0, h0]; exact e.symm.strictMono ht.1
      · rw [← e.symm_apply_apply anglePeriod, h2]; exact e.symm.strictMono ht.2
  have hSae : S =ᵐ[volume] angleInterior := by
    refine ae_eq_set.mpr ⟨?_, ?_⟩
    · rw [diff_eq_empty.mpr inter_subset_left, measure_empty]
    · refine measure_mono_null ?_ hDc
      simp [*]
  rw [intervalIntegral.integral_of_le hp, intervalIntegral.integral_of_le hp,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
    ← setIntegral_congr_set himg, hcv, setIntegral_congr_set hSae]
  refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
  simp only [smul_eq_mul]
  rw [abs_of_nonneg e.monotone.deriv_nonneg]

/-- Rescaled-arclength reparametrization of a Lipschitz closed curve that is injective on
`[0, 2π)`; the original curve is recovered as `γ = γ' ∘ τ` with `τ` the (monotone, Lipschitz)
rescaled arclength. -/
theorem exists_constSpeed_reparam {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ anglePeriod) (hinj : InjOn γ angleIco) :
    ∃ γ' : ℝ → ℂ, (∃ K', LipschitzWith K' γ') ∧ Function.Periodic γ' anglePeriod ∧
      InjOn γ' angleIco ∧ γ' '' angleInterval = γ '' angleInterval ∧
      (∃ c : ℝ, 0 < c ∧ ∀ᵐ θ, ‖deriv γ' θ‖ = c) ∧
      ∫ₚ θ, signedAreaDensity γ' θ =
        ∫ₚ θ, signedAreaDensity γ θ ∧
      ∃ τ : ℝ → ℝ, Monotone τ ∧ (∃ Kτ, LipschitzWith Kτ τ) ∧ τ 0 = 0 ∧ τ anglePeriod = anglePeriod ∧
        γ' ∘ τ = γ := by
  have hp : 0 < anglePeriod := by positivity
  have hsm := arcLen_strictMono hK hper hinj
  have hℓ0 : arcLen γ 0 = 0 := by simp [arcLen]
  set L := arcLen γ anglePeriod with hL
  have hLpos : 0 < L := by have := hsm hp; rwa [hℓ0] at this
  set a : ℝ := anglePeriod / L with ha
  have hapos : 0 < a := by positivity
  set s : ℝ → ℝ := fun θ => a * arcLen γ θ with hs
  have hs_mono : StrictMono s := fun x y h => mul_lt_mul_of_pos_left (hsm h) hapos
  have hs_lip : LipschitzWith (a.toNNReal * K) s := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := (arcLen_lipschitz hK).dist_le_mul x y
    rw [Real.dist_eq] at h ⊢
    simp only [hs]
    rw [← mul_sub, abs_mul, abs_of_pos hapos, NNReal.coe_mul, Real.coe_toNNReal _ hapos.le,
      mul_assoc]
    nlinarith
  have hs_add : ∀ θ, s (θ + anglePeriod) = s θ + anglePeriod := by
    intro θ
    simp [hs]
    rw [arcLen_add_period hK hper, mul_add, ← hL, ha]
    field_simp
  have hs0 : s 0 = 0 := by simp [*]
  have hs2 : s anglePeriod = anglePeriod := by grind
  have hs_bound : ∀ θ, |s θ - θ| ≤ anglePeriod := by
    refine abs_le_of_periodic  (fun θ => ?_) (fun x hx => ?_)
    · simp [hs_add]
    · have h1  := hs_mono.monotone hx.1
      have h2  := hs_mono.monotone hx.2.le
      rw [hs0] at h1; rw [hs2] at h2
      rw [abs_le]; grind
  have hsurj : Function.Surjective s := by
    refine hs_lip.continuous.surjective ?_ ?_
    · refine tendsto_atTop_mono (fun θ => ?_) (tendsto_atTop_add_const_right _ (-anglePeriod)
        tendsto_id)
      have := hs_bound θ; rw [abs_le] at this; simp only [id]; linarith
    · refine tendsto_atBot_mono (fun θ => ?_) (tendsto_atBot_add_const_right _ anglePeriod
        tendsto_id)
      have := hs_bound θ; rw [abs_le] at this; simp; linarith
  set e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective s hs_mono hsurj with he
  have hes : ∀ θ, e θ = s θ := fun θ => rfl
  have hσs : ∀ θ, e.symm (s θ) = θ := e.symm_apply_apply
  have hsσ : ∀ t, s (e.symm t) = t := e.apply_symm_apply
  have hσ_add : ∀ t, e.symm (t + anglePeriod) = e.symm t + anglePeriod := fun t => by
    apply hs_mono.injective; rw [hsσ, hs_add, hsσ]
  have hσ0 : e.symm 0 = 0 := by have := hσs 0; rwa [hs0] at this
  have hσ2 : e.symm anglePeriod = anglePeriod := by have := hσs anglePeriod; rwa [hs2] at this
  set γ' : ℝ → ℂ := fun t => γ (e.symm t) with hγ'
  have key : ∀ y x, y ≤ x → ‖γ' x - γ' y‖ ≤ L / anglePeriod * (x - y) := by
    intro y x hyx
    have h := norm_sub_le_arcLen hK (e.symm.monotone hyx)
    have h1 := hsσ x
    have h2 := hsσ y
    simp [hs] at h1 h2
    have e1 : arcLen γ (e.symm x) = x / a :=
      eq_div_of_mul_eq hapos.ne' (by rw [mul_comm]; exact h1)
    have e2 : arcLen γ (e.symm y) = y / a :=
      eq_div_of_mul_eq hapos.ne' (by rw [mul_comm]; exact h2)
    rw [e1, e2] at h
    calc _ ≤ _ := h
      _ = _ := by rw [ha]; field_simp
  have hγ'lip : LipschitzWith (L / anglePeriod).toNNReal γ' := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    rcases le_total y x with hyx | hxy
    · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]; exact key y x hyx
    · rw [abs_of_nonpos (sub_nonpos.mpr hxy), norm_sub_rev, neg_sub]; exact key x y hxy
  have hcomp : γ' ∘ s = γ := funext fun θ => by simp [hγ', hσs]
  have hchain := ae_deriv_comp hγ'lip hs_mono.monotone hs_lip
  rw [hcomp] at hchain
  
  refine ⟨γ', ⟨_, hγ'lip⟩, fun t => ?_, fun x hx y hy hxy => ?_, ?_,
    ⟨L / anglePeriod, by positivity, ?_⟩, ?_, s, hs_mono.monotone, ⟨_, hs_lip⟩, hs0, hs2, hcomp⟩
  · simp [hγ']; rw [hσ_add, hper]
  · have hmem : ∀ z ∈ angleIco, e.symm z ∈ angleIco := fun z hz =>
      ⟨hσ0 ▸ e.symm.monotone hz.1, hσ2 ▸ e.symm.strictMono hz.2⟩
    exact e.symm.injective (hinj (hmem x hx) (hmem y hy) hxy)
  · rw [show γ' = γ ∘ e.symm from rfl, image_comp, OrderIso.image_Icc, hσ0, hσ2]
  · rw [ae_iff]
    set B := {θ | ¬ (deriv γ θ = ((deriv s θ : ℝ) : ℂ) * deriv γ' (s θ) ∧
      HasDerivAt s (a * ‖deriv γ θ‖) θ)} with hB
    have hB0  := ae_iff.mp (hchain.and ((ae_hasDerivAt_arcLen hK).mono fun θ h => h.const_mul a))
    set A := {θ | HasDerivAt s 0 θ} with hA
    refine measure_mono_null (t := s '' A ∪ s '' B) ?_
      (measure_union_null (volume_image_eq_zero_of_hasDerivAt_zero fun x hx => hx)
        (volume_image_eq_zero_of_lipschitz hs_lip hB0))
    intro t ht
    by_cases hθB : e.symm t ∈ B
    · exact Or.inr ⟨e.symm t, hθB, hsσ t⟩
    · refine Or.inl ⟨e.symm t, ?_, hsσ t⟩
      obtain ⟨h1, h2⟩ := not_not.mp hθB
      by_cases hz : deriv γ (e.symm t) = 0
      · show HasDerivAt s 0 (e.symm t)
        rw [hz, norm_zero, mul_zero] at h2; exact h2
      · exfalso
        apply ht
        rw [h2.deriv, hsσ] at h1
        have h3 := congrArg norm h1
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h3
        
        have : a * ‖deriv γ' t‖ = 1 := by
          have := h3.symm
          field_simp at this
          nlinarith
        rw [ha] at this
        field_simp at this
        field_simp
        linarith
  · 
    rw [(integral_comp_orderIso (e := e) hs_lip hs0 hs2 (signedAreaDensity γ'))]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hchain] with θ hθ _
    simp only [hes, signedAreaDensity]
    have : γ' (s θ) = γ θ := congrFun hcomp θ
    rw [this, hθ, mul_left_comm, Complex.im_ofReal_mul]
    rfl

lemma deriv_periodic {γ : ℝ → ℂ} (hper : Function.Periodic γ anglePeriod) :
    Function.Periodic (deriv γ) anglePeriod := fun t => by
  have  := funext hper
  rw [← deriv_comp_add_const, this]

lemma signedAreaDensity_periodic {γ : ℝ → ℂ} (hper : Function.Periodic γ anglePeriod) :
    Function.Periodic (signedAreaDensity γ) anglePeriod := fun t => by
  simp [signedAreaDensity, hper t, deriv_periodic hper t]

lemma integral_signedAreaDensity_shift {γ : ℝ → ℂ} (hper : Function.Periodic γ anglePeriod)
    (a : ℝ) : ∫ θ in a..a + anglePeriod, signedAreaDensity γ θ =
      ∫ₚ θ, signedAreaDensity γ θ := by
  grind [(signedAreaDensity_periodic hper).intervalIntegral_add_eq a 0]

/-- Reversing the direction of a closed curve preserves the other properties of a
rescaled-arclength parametrization and changes the sign of the signed-area integral. -/
theorem exists_reverse_param {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ anglePeriod) (hinj : InjOn γ angleIco) {c : ℝ}
    (hc : ∀ᵐ θ, ‖deriv γ θ‖ = c) :
    ∃ γ' : ℝ → ℂ, LipschitzWith K γ' ∧ Function.Periodic γ' anglePeriod ∧
      InjOn γ' angleIco ∧ γ' '' angleInterval = γ '' angleInterval ∧
      (∀ᵐ θ, ‖deriv γ' θ‖ = c) ∧
      ∫ₚ θ, signedAreaDensity γ' θ =
        -∫ₚ θ, signedAreaDensity γ θ := by
  
  have hrev : ∀ x, γ (-x) = γ (anglePeriod - x) := fun x => by
    rw [← hper (-x)]; ring_nf
  refine ⟨fun θ => γ (-θ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have := hK.dist_le_mul (-x) (-y)
    rwa [dist_neg_neg] at this
  · intro θ
    simp only
    rw [neg_add, ← sub_eq_add_neg, hper.sub_eq]
  · intro x hx y hy hxy
    simp only at hxy
    have key : ∀ z ∈ angleIco, γ (-z) = γ (if z = 0 then 0 else anglePeriod - z) ∧
        (if z = 0 then 0 else anglePeriod - z) ∈ angleIco := by
      grind
    obtain ⟨hx1, hx2⟩ := key x hx
    obtain ⟨hy1, hy2⟩ := key y hy
    grind [hinj hx2 hy2 (by rw [← hx1, ← hy1, hxy])]
  · ext z
    simp
    constructor
    · grind
    · rintro ⟨φ, ⟨h1, h2⟩, rfl⟩
      refine ⟨anglePeriod - φ, (by grind), ?_⟩
      rw [hrev]; ring_nf
  · have h2  :=
      (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae hc
    filter_upwards [h2] with θ hθ
    rw [deriv_comp_neg, norm_neg, hθ]
  · have hd : ∀ θ, signedAreaDensity (fun θ => γ (-θ)) θ = -signedAreaDensity γ (-θ) := by
      simp [signedAreaDensity, deriv_comp_neg, mul_neg, Complex.neg_im]
    simp_rw [hd]
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg
      (signedAreaDensity γ), neg_zero]
    have := integral_signedAreaDensity_shift hper (-anglePeriod)
    rw [neg_add_cancel] at this
    rw [this]

end PolyaNeumann
