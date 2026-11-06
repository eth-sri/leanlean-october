module
public import NearlyMinimax.HighMarkedMeasurable
public import NearlyMinimax.HighMassTilt
@[expose] public section
noncomputable section
open Set MeasureTheory Function ProbabilityTheory
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {d k : ℕ}
def highAffineChart (d k : ℕ) (z : Fin d → ℤ) (x : Covariate d) : Covariate d :=
  fun r => k * x r - z r
def highPatchWrapLift  (j : HighWindowLabels d k) (b : Fin d → Bool) : Fin d → ℤ :=
  fun r => if b r then (j r).val+k else (j r).val
theorem finite_pi_measure_mono {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] (μ ν : (i : I) → Measure (E i))
    (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν := by
  have ho : (OuterMeasure.pi (fun i => (μ i).toOuterMeasure)) ≤
      OuterMeasure.pi (fun i => (ν i).toOuterMeasure) := by
    apply OuterMeasure.le_pi.mpr
    intro S hS
    exact (OuterMeasure.pi_pi_le _ S).trans (Finset.prod_le_prod (fun i _ => h i (S i)))
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.pi_def, toMeasure_apply _ _ hS, Measure.pi_def, toMeasure_apply _ _ hS]
  exact ho S
def highPatchProductChart  (d k ) (j : HighWindowLabels d k)
    (x : I → Covariate d) : I → Covariate d := fun i => highLocalCoordinates d k j (x i)
theorem highPatchProductChart_measurable  (d k j) :
    Measurable (highPatchProductChart (I := I) d k j) :=
  measurable_pi_iff.mpr (fun i => (highLocalCoordinates_measurable d k j).comp (measurable_pi_apply i))
theorem highPatchProductChart_map_le  [Fintype I]  [NeZero k]
    (hk : 4 ≤ k) (j ) :
    Measure.map (highPatchProductChart (I := I) d k j)
      (Measure.pi (fun _ => (cubeVolume d).restrict (highTorusPatch d k j))) ≤
    ENNReal.ofReal (((2/k)^d)^(Fintype.card I)) •
      Measure.pi (fun _ => volume.restrict (spatialPatchBox d)) := by
  have h_highLocalCoordinates_eq_affine_on_patch {x : Covariate d} (hx : x ∈ highTorusPatch d k j) (z : Fin d → ℤ) (hz : ∀ r, (z r : ZMod k)=j r) (hc : ∀ r, |(k : ℝ)*x r-z r| < 1) : highLocalCoordinates d k j x = highAffineChart d k z x := by
    funext r
    simp only [highLocalCoordinates, highLocalCoordinate, highRawChartCoordinate, highChartLift_eq_of_close k hk (j r) (x r) (z r) (hz r) (hc r),
      if_pos (hc r).le, highAffineChart]
  letI := cubeVolume_isProbability d
  letI := (volume.restrict (spatialPatchBox d)).smul_finite
    (c := ENNReal.ofReal ((2/↑k)^d)) ENNReal.ofReal_ne_top
  change Measure.map (fun x : I → Covariate d => fun i => highLocalCoordinates d k j (x i)) _ ≤ _
  rw [Measure.pi_map_pi (fun _ => (highLocalCoordinates_measurable d k j).aemeasurable)]
  have h_highLocalCoordinates_patch_map_le : Measure.map (highLocalCoordinates d k j)
      ((cubeVolume d).restrict (highTorusPatch d k j)) ≤
      ENNReal.ofReal ((2 / k)^d) • volume.restrict (spatialPatchBox d) := by
    have hbox : MeasurableSet (spatialPatchBox d) := measurableSet_Icc
    apply Measure.le_iff.mpr
    intro S hS
    have hcover : (highLocalCoordinates d k j ⁻¹' S ∩ highTorusPatch d k j) ∩ unitCube d ⊆
        ⋃ b : Fin d → Bool, highAffineChart d k (highPatchWrapLift j b) ⁻¹' (S ∩ spatialPatchBox d) := by
      intro x hx
      obtain ⟨z, hz, hc⟩ := hx.1.2
      have hzcase (r : Fin d) : ∃ b : Bool,
          z r = if b then ((j r).val : ℤ)+↑k else ((j r).val : ℤ) := by
        have h_highPatch_lift_cube_cases (j : ZMod k) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (z : ℤ) (hz : (z : ZMod k) = j) (hclose : |(k : ℝ)*x-z| < 1) : z = (j.val : ℤ) ∨ z = (j.val : ℤ)+(k : ℤ) := by
          have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
          have : (j.val : ℤ) < k := by exact_mod_cast ZMod.val_lt j
          obtain ⟨q, hq⟩ := (ZMod.intCast_eq_iff k z j).mp hz
          have : 0 ≤ z ∧ z ≤ (k : ℤ) := by
            have := abs_lt.mp hclose
            have hzL : (-1 : ℝ) < z := by nlinarith [mul_nonneg hkR.le hx.1]
            have hzU : (z : ℝ) < k+1 := by nlinarith [mul_le_mul_of_nonneg_left hx.2 hkR.le]
            have : (-1 : ℤ) < z := by exact_mod_cast hzL
            have : z < ↑k+1 := by exact_mod_cast hzU
            omega
          have hqcases : q = 0 ∨ q = 1 := by
            have hj0 : (0 : ℤ) ≤ j.val := Int.natCast_nonneg _
            have : ↑0 < k := by exact_mod_cast (by omega : 0 < k)
            have : 0 ≤ q := by
              by_contra h
              have : q ≤ -1 := by omega
              nlinarith
            have : q ≤ 1 := by
              by_contra h
              have : 2 ≤ q := by omega
              nlinarith
            omega
          rcases hqcases with hq0 | hq1
          · exact Or.inl (by simpa [hq0] using hq)
          · exact Or.inr (by simpa [hq1] using hq)
        rcases (h_highPatch_lift_cube_cases (j r) (x r) (hx.2 r) (z r) (hz r) (hc r))with h | h
        · exact ⟨false, h⟩
        · exact ⟨true, h⟩
      choose b hb using hzcase
      have hzb : z = highPatchWrapLift j b := by funext r; exact hb r
      have he := h_highLocalCoordinates_eq_affine_on_patch hx.1.2 z hz hc
      apply Set.mem_iUnion.mpr
      refine ⟨b, ?_⟩
      change highAffineChart d k (highPatchWrapLift j b) x ∈ S ∩ spatialPatchBox d
      rw [← hzb, ← he]
      have h_highLocalCoordinates_patch_mem_box : highLocalCoordinates d k j x ∈ spatialPatchBox d := by
        obtain ⟨z, hz, hc⟩ := hx.1.2
        rw [h_highLocalCoordinates_eq_affine_on_patch ⟨z,hz,hc⟩ z hz hc]
        constructor <;> intro r
        · exact (abs_lt.mp (hc r)).1.le
        · exact (abs_lt.mp (hc r)).2.le
      exact ⟨hx.1.1, h_highLocalCoordinates_patch_mem_box⟩
    rw [Measure.map_apply (highLocalCoordinates_measurable d k j) hS,
      Measure.restrict_apply ((highLocalCoordinates_measurable d k j) hS),
      cubeVolume, Measure.restrict_apply (((highLocalCoordinates_measurable d k j) hS).inter
        (highTorusPatch_measurableSet d k j)), Measure.smul_apply,
      Measure.restrict_apply hS, smul_eq_mul]
    calc
      _ ≤ volume (⋃ b : Fin d → Bool,
          highAffineChart d k (highPatchWrapLift j b) ⁻¹' (S ∩ spatialPatchBox d)) := measure_mono hcover
      _ ≤ ∑' b : Fin d → Bool,
          volume (highAffineChart d k (highPatchWrapLift j b) ⁻¹' (S ∩ spatialPatchBox d)) :=
        measure_iUnion_le _
      _ = ∑ b : Fin d → Bool,
          ENNReal.ofReal ((k^d)⁻¹) * volume (S ∩ spatialPatchBox d) := by
        rw [tsum_fintype]
        apply Finset.sum_congr rfl
        intro b _
        have h_highAffineChart_map_volume (hk : 0 < k) (z) : Measure.map (highAffineChart d k z) volume =
            ENNReal.ofReal (k^d)⁻¹ • (volume : Measure (Covariate d)) := by
          let f : Covariate d →ₗ[ℝ] Covariate d := (k : ℝ) • LinearMap.id
          have hdet : LinearMap.det f = (k : ℝ)^d := by
            simp [f, LinearMap.det_smul, LinearMap.det_id]
          have hf := Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := f)
            (by rw [hdet]; positivity)
          have heq : highAffineChart d k z = (fun x : Covariate d => (fun r => -(z r : ℝ)) + x) ∘ f := by
            funext x r
            simp [highAffineChart, f]
            ring
          rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop), hf, hdet,
            Measure.map_smul _ (by fun_prop), map_add_left_eq_self]
          congr 1
          rw [abs_of_nonneg (by positivity)]
        have h_highAffineChart_measurable (z) : Measurable (highAffineChart d k z) := by unfold highAffineChart; fun_prop
        rw [← Measure.map_apply (h_highAffineChart_measurable _) (hS.inter hbox),
          h_highAffineChart_map_volume (by omega) _, Measure.smul_apply, smul_eq_mul]
      _ = ENNReal.ofReal ((2 / k)^d) * volume (S ∩ spatialPatchBox d) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [← mul_assoc]
        congr 1
        have ht : (2 : ℝ≥0∞)^d = ENNReal.ofReal (2^d) := by
          rw [ENNReal.ofReal_pow] <;> norm_num
        rw [ht, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [div_pow]
        ring
  calc
    _ ≤ Measure.pi (fun _ => ENNReal.ofReal ((2/k)^d) •
      volume.restrict (spatialPatchBox d)) :=
      finite_pi_measure_mono _ _ (fun _ => h_highLocalCoordinates_patch_map_le)
    _ = _ := by
      rw [spatialPi_const_smul, ← ENNReal.ofReal_pow (by positivity)]
theorem high_raw_square_patch_integrable_bound {d k r : ℕ} [NeZero k]
    (hk : 4 ≤ k) (j R)
    (hR : ∀ y, Measurable (fun x => R x y))
    (H )
    (hH : Integrable H (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))))
    (hH0 : ∀ u, 0 ≤ H u)
    (hdom : ∀ x, (∀ i, x i ∈ highTorusPatch d k j) →
      selectedRawSquareEnergy R x ≤ H (highPatchProductChart d k j x)) :
    Integrable (selectedRawSquareEnergy R)
      (Measure.pi (fun _ => (cubeVolume d).restrict (highTorusPatch d k j))) ∧
    (∫ x, selectedRawSquareEnergy R x
      ∂Measure.pi (fun _ => (cubeVolume d).restrict (highTorusPatch d k j))) ≤
      ((2 / k) ^ d) ^ r *
        ∫ u, H u ∂Measure.pi (fun _ => volume.restrict (spatialPatchBox d)) := by
  let _ := cubeVolume_isProbability d
  have hrawMeas : Measurable (selectedRawSquareEnergy R) :=
    Finset.measurable_sum _ (fun y _ => (hR y).pow_const 2)
  have hraw0 (x : Fin r → Covariate d) : 0 ≤ selectedRawSquareEnergy R x :=
    Finset.sum_nonneg (fun y _ => sq_nonneg _)
  have heval := ((hH.smul_measure ENNReal.ofReal_ne_top).mono_measure (highPatchProductChart_map_le hk j)).comp_measurable (highPatchProductChart_measurable d k j)
  have hmem : ∀ᵐ x ∂Measure.pi (fun _ : Fin r => (cubeVolume d).restrict (highTorusPatch d k j)),
      ∀ i, x i ∈ highTorusPatch d k j :=
    ae_all_iff.mpr (fun i => Measure.tendsto_eval_ae_ae.eventually
      (ae_restrict_mem (highTorusPatch_measurableSet d k j)))
  have hrawI : Integrable (selectedRawSquareEnergy R)
      (Measure.pi (fun _ => (cubeVolume d).restrict (highTorusPatch d k j))) := by
    apply heval.mono' hrawMeas.aestronglyMeasurable
    filter_upwards [hmem] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hraw0 x)]
    exact hdom x hx
  refine ⟨hrawI, ?_⟩
  calc
    _ ≤ ∫ x, H (highPatchProductChart d k j x)
        ∂Measure.pi (fun _ => (cubeVolume d).restrict (highTorusPatch d k j)) :=
      integral_mono_ae hrawI heval (hmem.mono (fun x hx => hdom x hx))
    _ ≤ _ := by
      have h_highPatchProductChart_integral_le {I} [Fintype I] (H : (I → Covariate d) → ℝ) (hH : Integrable H (Measure.pi (fun _ : I => volume.restrict (spatialPatchBox d)))) (hH0 : ∀ x, 0 ≤ H x) : (∫ x, H (highPatchProductChart d k j x)
            ∂Measure.pi (fun _ : I => (cubeVolume d).restrict (highTorusPatch d k j))) ≤
          ((2/↑k)^d)^(Fintype.card I) *
            ∫ u, H u ∂Measure.pi (fun _ : I => volume.restrict (spatialPatchBox d)) := by
        have hs := hH.smul_measure (c := ENNReal.ofReal (((2/↑k)^d)^(Fintype.card I)))
          ENNReal.ofReal_ne_top
        rw [← integral_map (highPatchProductChart_measurable d k j).aemeasurable (hs.mono_measure (highPatchProductChart_map_le hk j)).aestronglyMeasurable]
        calc
          _ ≤ ∫ x, H x ∂ENNReal.ofReal (((2/↑k)^d)^(Fintype.card I)) •
              Measure.pi (fun _ : I => volume.restrict (spatialPatchBox d)) :=
            integral_mono_measure (highPatchProductChart_map_le hk j)
              (Filter.Eventually.of_forall hH0) hs
          _ = _ := by rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
      simpa only [Fintype.card_fin] using (h_highPatchProductChart_integral_le H hH hH0)
theorem high_marked_original_design_spatial_series 
    [Fintype ι] [DecidableEq ι] [MeasurableSpace E]  [NeZero k]
    (hk : 4 ≤ k) (j : HighWindowLabels d k) (n : ℕ)
    (π : Measure E) [SFinite π] (activation : E → ℝ) (hAct : Measurable activation)
    (a V η : ℝ) (ha : a ≠ 0) (pMinus pPlus cMass : ℝ)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass)
    (p ) (hpMeas : Measurable p)
    (hraw : ∀ x, pMinus ≤ p x ∧ p x ≤ pPlus)
    (pReset ) (hpReset : Measurable (Function.uncurry pReset))
    (cReset ) (hcReset : ∀ γ, Measurable (fun e => cReset e γ))
    (g w ) (hg : Measurable g) (hw : Measurable w)
    (φ : Covariate d → ι → ℝ) (hφ : ∀ γ, Measurable (fun x => φ x γ)) (c : ι → ℝ)
    (hq : ∀ x y, cMass ≤ highMarkedResponseMass a V η g w φ c x y)
    (hwo : ∀ x, x ∉ highTorusPatch d k j → w x = 0)
    (hro : ∀ e x, x ∉ highTorusPatch d k j → pReset e x = p x)
    (H : (r : ℕ) → (Fin r → Covariate d) → ℝ)
    (hH : ∀ r, Integrable (H r) (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))))
    (hH0 : ∀ r u, 0 ≤ H r u)
    (hdom : ∀ r x, (∀ i, x i ∈ highTorusPatch d k j) →
      selectedRawSquareEnergy (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) x ≤
        H r (highPatchProductChart d k j x)) :
    Integrable (highMarkedSampleConditionalEnergy n π activation a V η p pReset cReset g w φ c)
      (Measure.pi (fun _ => highNormalizedDesignLaw p)) ∧
    (∫ x, highMarkedSampleConditionalEnergy n π activation a V η p pReset cReset g w φ c x
      ∂Measure.pi (fun _ => highNormalizedDesignLaw p)) ≤
      ∑ r ∈ Finset.range (n + 1),
        (↑n * highFixedScoreDenominator pMinus cMass * (2 / ↑k) ^ d) ^ r /
          ↑r.factorial * ∫ u, H r u
            ∂Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d)) := by
  let _ := cubeVolume_isProbability d
  have hprob := high_normalized_design_probability p hpMeas pMinus pPlus hpMinus
    (Filter.Eventually.of_forall hraw)
  have hR (r : ℕ) (y : Fin r → Fin 3) : Measurable (fun x =>
      highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c x y) :=
    highMarkedSampleNumerator_measurable r π activation hAct a V η p hpMeas pReset hpReset
      cReset hcReset g w hg hw φ hφ c y
  have hRaw (r : ℕ) := high_raw_square_patch_integrable_bound hk j
    (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c)
    (hR r) (H r) (hH r) (hH0 r) (hdom r)
  have hs := high_marked_design_raw_factorial_series (cubeVolume d) n
    (highTorusPatch d k j) (highTorusPatch_measurableSet d k j)
    (highRawDensityMass p) pMinus cMass hpMinus hcMass ((highRawDensityMass_mem_Icc p hpMeas pMinus pPlus hpMinus (Filter.Eventually.of_forall hraw)).1) π activation a V η ha p hpMeas
    pReset cReset g w φ c
    (highMarkedResponseMass_measurable a V η g w hg hw φ hφ c)
    hprob (fun x => (hraw x).1) hq hwo hro hR (fun r => (hRaw r).1)
  refine ⟨hs.1, hs.2.trans ?_⟩
  apply Finset.sum_le_sum
  intro r hr
  have hco : 0 ≤ (↑n * highFixedScoreDenominator pMinus cMass) ^ r / ↑r.factorial := by
    apply div_nonneg
    · exact pow_nonneg (mul_nonneg (Nat.cast_nonneg n)
        (high_fixed_score_denominator_pos hpMinus hcMass).le) r
    · exact Nat.cast_nonneg _
  calc
    _ ≤ ((↑n * highFixedScoreDenominator pMinus cMass) ^ r / ↑r.factorial) *
        (((2 / ↑k) ^ d) ^ r * ∫ u, H r u
          ∂Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))) :=
      mul_le_mul_of_nonneg_left (hRaw r).2 hco
    _ = _ := by rw [mul_pow]; ring
theorem raw_joint_fisher_integrable_bound 
    [MeasurableSpace Ω] [MeasurableSpace Z]
    (ν : Measure Ω) [IsFiniteMeasure ν] (μ : Measure Z) [SFinite μ]
    (c ) (hc : ∀ ω, 0 < c ω) (hci : Integrable c ν)
    (L D ) (hL : Measurable (Function.uncurry L))
    (hD : Measurable (Function.uncurry D)) (hpos : ∀ ω z, 0 < L ω z)
    (B ) (hB : 0 ≤ B)
    (hscore : ∀ ω, Integrable (fun z => (D ω z / L ω z) ^ 2)
      (μ.withDensity (fun z => ENNReal.ofReal (L ω z / c ω))))
    (hbound : ∀ ω, (∫ z, (D ω z / L ω z) ^ 2
      ∂μ.withDensity (fun z => ENNReal.ofReal (L ω z / c ω))) ≤ B) :
    Integrable (fun z : Ω × Z => D z.1 z.2 ^ 2 / L z.1 z.2) (ν.prod μ) ∧
    (∫ z : Ω × Z, D z.1 z.2 ^ 2 / L z.1 z.2 ∂ν.prod μ) ≤ (∫ ω, c ω ∂ν) * B := by
  have h_normalized_likelihood_score_square_transfer (c) (hc : 0 < c) (L : Z → ℝ) (D : Z → ℝ) (hL : Measurable L) (hpos : ∀ z, 0 < L z) : (Integrable (fun z => (D z / L z) ^ 2)
        (μ.withDensity (fun z => ENNReal.ofReal (L z / c))) ↔
          Integrable (fun z => D z ^ 2 / L z) μ) ∧
      (∫ z, (D z / L z) ^ 2 ∂μ.withDensity (fun z => ENNReal.ofReal (L z / c))) =
        c⁻¹ * ∫ z, D z ^ 2 / L z ∂μ := by
    have hf : Measurable (fun z => ENNReal.ofReal (L z / c)) :=
      ENNReal.measurable_ofReal.comp (hL.div_const c)
    have he (z : Z) : (ENNReal.ofReal (L z / c)).toReal * (D z / L z) ^ 2 =
        c⁻¹ * (D z ^ 2 / L z) := by
      rw [ENNReal.toReal_ofReal (div_nonneg (hpos z).le hc.le)]
      field_simp [(hpos z).ne', hc.ne']
    constructor
    · rw [integrable_withDensity_iff_integrable_smul' hf
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      simp only [smul_eq_mul, he]
      exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (inv_ne_zero hc.ne')) _
    · have hi := integral_withDensity_eq_integral_toReal_smul (μ := μ) hf
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (fun z => (D z / L z) ^ 2)
      change (∫ z, (D z / L z) ^ 2 ∂μ.withDensity (fun z => ENNReal.ofReal (L z / c))) =
        ∫ z, (ENNReal.ofReal (L z / c)).toReal * (D z / L z) ^ 2 ∂μ at hi
      rw [hi]
      simp_rw [he]
      exact integral_const_mul _ _
  let W : Ω × Z → ℝ := fun z => D z.1 z.2 ^ 2 / L z.1 z.2
  have hW  := (hD.pow_const 2).div hL
  have hWi (ω : Ω) : Integrable (fun z => W (ω, z)) μ :=
    (h_normalized_likelihood_score_square_transfer (c ω) (hc ω) (L ω) (D ω)
      hL.of_uncurry_left (hpos ω)).1.mp (hscore ω)
  have hWn (ω : Ω) (z : Z) : 0 ≤ W (ω, z) := div_nonneg (sq_nonneg _) (hpos ω z).le
  have he (ω : Ω) : (∫ z, W (ω, z) ∂μ) = c ω *
      (∫ z, (D ω z / L ω z) ^ 2 ∂μ.withDensity (fun z => ENNReal.ofReal (L ω z / c ω))) := by
    have hs := (h_normalized_likelihood_score_square_transfer (c ω) (hc ω) (L ω) (D ω)
      hL.of_uncurry_left (hpos ω)).2
    rw [hs, ← mul_assoc, mul_inv_cancel₀ (hc ω).ne', one_mul]
  have hnorm (ω : Ω) : (∫ z, ‖W (ω, z)‖ ∂μ) ≤ c ω * B := by
    have heNorm : (fun z => ‖W (ω, z)‖) = (fun z => W (ω, z)) := by
      funext z
      rw [Real.norm_eq_abs, abs_of_nonneg (hWn ω z)]
    rw [heNorm, he]
    exact mul_le_mul_of_nonneg_left (hbound ω) (hc ω).le
  have hWI : Integrable W (ν.prod μ) :=
    (integrable_prod_iff hW.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hWi, (by apply (hci.mul_const B).mono' (hW.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable); apply Filter.Eventually.of_forall; intro ω; rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]; exact hnorm ω)⟩
  refine ⟨hWI, ?_⟩
  rw [integral_prod _ hWI]
  calc
    _ ≤ ∫ ω, c ω * B ∂ν := by
      apply integral_mono_ae hWI.integral_prod_left (hci.mul_const B)
      apply Filter.Eventually.of_forall
      intro ω
      change (∫ z, W (ω, z) ∂μ) ≤ c ω * B
      rw [he]
      exact mul_le_mul_of_nonneg_left (hbound ω) (hc ω).le
    _ = _ := integral_mul_const _ _
theorem high_raw_joint_fisher_integrable_bound  [MeasurableSpace Ω]
     (ν : Measure Ω) [IsProbabilityMeasure ν] (n a V p F)
    (hp : Measurable (Function.uncurry p)) (hF aRaw bRaw) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (D )
    (hD : Measurable (Function.uncurry D)) (B ) (hB : 0 ≤ B)
    (hscore : ∀ ω, Integrable (fun z => (D ω z / highRawSampleLikelihood n a V (p ω) (F ω) z) ^ 2)
      (highSampleIndexKernel n a V p F hp hF ω))
    (hbound : ∀ ω, (∫ z, (D ω z / highRawSampleLikelihood n a V (p ω) (F ω) z) ^ 2
      ∂highSampleIndexKernel n a V p F hp hF ω) ≤ B) :
    Integrable (fun z => D z.1 z.2 ^ 2 / highRawSampleLikelihood n a V (p z.1) (F z.1) z.2)
      (ν.prod (highSampleReference d n)) ∧
    (∫ z, D z.1 z.2 ^ 2 / highRawSampleLikelihood n a V (p z.1) (F z.1) z.2
      ∂ν.prod (highSampleReference d n)) ≤
      massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n * B := by
  let c : Ω → ℝ := fun ω => highRawDensityMass (p ω) ^ n
  have hmBound (ω : Ω) : aRaw ≤ highRawDensityMass (p ω) ∧ highRawDensityMass (p ω) ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
      (Filter.Eventually.of_forall (hraw ω))
  have hm (ω : Ω) : 0 < highRawDensityMass (p ω) := haRaw.trans_le (hmBound ω).1
  have hc  := fun ω => pow_pos (hm ω) n
  have he (ω : Ω) : highSampleIndexKernel n a V p F hp hF ω =
      (highSampleReference d n).withDensity (fun z =>
        ENNReal.ofReal (highRawSampleLikelihood n a V (p ω) (F ω) z / c ω)) := by
    rw [highSampleIndexKernel_apply]
    congr 1
    funext z
    congr 1
    apply (eq_div_iff (hc ω).ne').mpr
    simpa only [c, mul_comm] using
      highSampleLikelihood_mass_cancellation n a V (p ω) (F ω) (hm ω).ne' z
  exact raw_joint_fisher_integrable_bound ν (highSampleReference d n) c hc (by apply (integrable_const (bRaw ^ n)).mono' ((highRawDensityMass_joint_measurable p hp).pow_const n).aestronglyMeasurable; apply Filter.Eventually.of_forall; intro ω; rw [Real.norm_eq_abs, abs_of_nonneg (hc ω).le]; exact pow_le_pow_left₀ (hm ω).le (hmBound ω).2 n)
    (fun ω => highRawSampleLikelihood n a V (p ω) (F ω)) D
    (highRawSampleLikelihood_joint_measurable n a V p F hp hF) hD
    (fun ω z => Finset.prod_pos (fun i _ => mul_pos
      (haRaw.trans_le (hraw ω (z.1 i)).1) (hq ω _ _))) B hB
    (fun ω => by rw [← he ω]; exact hscore ω)
    (fun ω => by rw [← he ω]; exact hbound ω)
def finiteResponseSquareEnergy  [MeasurableSpace α] (n )
    (a V : ℝ) (F : α → ℝ) (S : ((Fin n → α) × (Fin n → Fin 3)) → ℝ)
    (x : Fin n → α) : ℝ :=
  ∑ y : Fin n → Fin 3, (∏ i, ternaryMass a (F (x i)) V (y i)) * (S (x, y)) ^ 2
theorem response_sample_square_integrable_integral  [MeasurableSpace α]
    (n ) (μ : Measure (Fin n → α)) [SFinite μ] (a V ) (ha : a ≠ 0)
    (F hF) (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (S ) (hS : Measurable S)
    (hE : Integrable (finiteResponseSquareEnergy n a V F S) μ) :
    Integrable (fun z => S z ^ 2) (μ.compProd (responseSampleIndexKernel n a V F hF)) ∧
    (∫ z, S z ^ 2 ∂μ.compProd (responseSampleIndexKernel n a V F hF)) =
      ∫ x, finiteResponseSquareEnergy n a V F S x ∂μ := by
  let _ := responseSampleIndexKernel_markov n a V F hF ha hq
  have he (x : Fin n → α) : (∫ y, ‖S (x, y) ^ 2‖ ∂responseSampleIndexKernel n a V F hF x) =
      finiteResponseSquareEnergy n a V F S x := by
    simp_rw [Real.norm_eq_abs, abs_sq]
    exact responseSampleIndexKernel_integral n a V F hF x (fun i y => hq (x i) y) _
  have hi : Integrable (fun z => S z ^ 2) (μ.compProd (responseSampleIndexKernel n a V F hF)) := by
    apply (Measure.integrable_compProd_iff (hS.pow_const 2).aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall (fun _ => Integrable.of_finite)
    · simpa only [he] using hE
  refine ⟨hi, ?_⟩
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x =>
    responseSampleIndexKernel_integral n a V F hF x (fun i y => hq (x i) y) _)
section
variable {E : Type*} [MeasurableSpace E]
def highFrameFullMarkedScore (d k D n ) [NeZero k]
    (π : HighWindowLabels d k → Measure E) (activation : HighWindowLabels d k → E → ℝ)
    (a V η : ℝ) (p : Covariate d → ℝ)
    (pReset : HighWindowLabels d k → E → Covariate d → ℝ)
    (cReset : HighWindowLabels d k → E → HighFrameIndex d D → ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  ∑ j, highFrameMarkedScore d k D n π activation a V η (p ∘ z.1)
    (fun j e => pReset j e ∘ z.1) cReset c z.1 j z.2
theorem high_frame_complete_design_spatial_series (d k D n ) [NeZero k] (hk : 4 ≤ k)
    (π ) [∀ j, SFinite (π j)]
    (activation : HighWindowLabels d k → E → ℝ)
    (hAct : ∀ j, Measurable (activation j)) (hActI : ∀ j, Integrable (activation j) (π j))
    (a V η pMinus pPlus cMass : ℝ) (ha : a ≠ 0) (hpMinus : 0 < pMinus)
    (hpPlus : 0 ≤ pPlus) (hcMass : 0 < cMass)
    (p ) (hp : Measurable p)
    (hraw : ∀ x, pMinus ≤ p x ∧ p x ≤ pPlus)
    (pReset )
    (hReset : ∀ j, Measurable (Function.uncurry (pReset j)))
    (hBound : ∀ j e x, |pReset j e x| ≤ pPlus)
    (hOutside : ∀ j e x, x ∉ highTorusPatch d k j → pReset j e x = p x)
    (cReset )
    (hcReset : ∀ j γ, Measurable (fun e => cReset j e γ))
    (c )
    (hq : ∀ x y, cMass ≤ ternaryMass a (highFrameField d k η (fun l => highFramePolynomial (c l)) x) V y)
    (hqReset : ∀ j e x y, 0 ≤ highMarkedResponseMass a V η
      (highLocalFieldWithout d k D η c j) (highPeriodicTensor d k j)
      (fun x => highLocalFrameFeature k j x) (cReset j e) x y)
    (hDensity : ∀ j (x : Fin n → Covariate d),
      (∫ e, activation j e * ∏ i, pReset j e (x i) ∂π j) = 0)
    (H : HighWindowLabels d k → (r : ℕ) → (Fin r → Covariate d) → ℝ)
    (hH : ∀ j r, Integrable (H j r) (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))))
    (hH0 : ∀ j r u, 0 ≤ H j r u)
    (hdom : ∀ j r x, (∀ i, x i ∈ highTorusPatch d k j) →
      selectedRawSquareEnergy (highMarkedSampleNumerator r (π j) (activation j) a V η p (pReset j)
        (cReset j) (highLocalFieldWithout d k D η c j) (highPeriodicTensor d k j)
          (fun x => highLocalFrameFeature k j x) (c j)) x ≤ H j r (highPatchProductChart d k j x)) :
    let F := highFrameField d k η (fun l => highFramePolynomial (c l))
    let hF : Measurable F := (highFrameField_contDiff d k η _).continuous.measurable
    let S := highFrameFullMarkedScore d k D n π activation a V η p pReset cReset c
    Integrable (fun z => S z ^ 2) ((Measure.pi (fun _ => highNormalizedDesignLaw p)).compProd
      (responseSampleIndexKernel n a V F hF)) ∧
    (∫ z, S z ^ 2 ∂(Measure.pi (fun _ => highNormalizedDesignLaw p)).compProd
      (responseSampleIndexKernel n a V F hF)) ≤
      (3 ^ d : ℕ) * ∑ j : HighWindowLabels d k, ∑ r ∈ Finset.range (n + 1),
        (↑n * highFixedScoreDenominator pMinus cMass * (2 / ↑k) ^ d) ^ r /
          ↑r.factorial * ∫ u, H j r u
            ∂Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d)) := by
  have h_highLocalFieldWithout_continuous (j) : Continuous (highLocalFieldWithout d k D η c j) := by
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro l _
    exact (highPeriodizedChart_contDiff d k l _
      (highFrameProfile_contDiff (highFramePolynomial (c l)))
      (highFrameProfile_zero_of_window_zero (highFramePolynomial (c l)))).continuous
  let F := highFrameField d k η (fun l => highFramePolynomial (c l))
  have hF : Measurable F := (highFrameField_contDiff d k η _).continuous.measurable
  let S := highFrameFullMarkedScore d k D n π activation a V η p pReset cReset c
  let μ := Measure.pi (fun _ : Fin n => highNormalizedDesignLaw p)
  let _ := high_normalized_design_probability p hp pMinus pPlus hpMinus (Filter.Eventually.of_forall hraw)
  let Eglobal := finiteResponseSquareEnergy n a V F S
  let Elocal (j : HighWindowLabels d k) := highMarkedSampleConditionalEnergy n (π j) (activation j)
    a V η p (pReset j) (cReset j) (highLocalFieldWithout d k D η c j)
      (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x) (c j)
  have hqLocal (j : HighWindowLabels d k) (x : Covariate d) (y : Fin 3) :
      cMass ≤ highMarkedResponseMass a V η (highLocalFieldWithout d k D η c j)
        (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x) (c j) x y := by
    unfold highMarkedResponseMass
    rw [← highFrameField_local_decomposition d k D hk η c j x]
    exact hq x y
  have hlocal (j : HighWindowLabels d k) := high_marked_original_design_spatial_series hk j n
    (π j) (activation j) (hAct j) a V η ha pMinus pPlus cMass hpMinus hcMass p hp hraw
    (pReset j) (hReset j) (cReset j) (hcReset j)
    (highLocalFieldWithout d k D η c j) (highPeriodicTensor d k j)
    (h_highLocalFieldWithout_continuous j).measurable
    (highPeriodicTensor_contDiff d k j).continuous.measurable
    (fun x => highLocalFrameFeature k j x) (highLocalFrameFeature_measurable k j) (c j)
    (hqLocal j) (fun x hx => by
      by_contra h
      exact hx (highPeriodicTensor_supported_patch d k j h))
    (hOutside j) (H j) (hH j) (hH0 j) (hdom j)
  have h_highFrameFullMarkedScore_measurable : Measurable (highFrameFullMarkedScore d k D n π activation a V η p pReset cReset c) := by
    apply measurable_from_prod_countable_left
    intro y
    apply Finset.measurable_sum
    intro j hj
    let g := highLocalFieldWithout d k D η c j
    let w := highPeriodicTensor d k j
    let φ : Covariate d → HighFrameIndex d D → ℝ := fun x => highLocalFrameFeature k j x
    have hg : Measurable g := (h_highLocalFieldWithout_continuous j).measurable
    have hw : Measurable w := (highPeriodicTensor_contDiff d k j).continuous.measurable
    have hφ : ∀ γ, Measurable (fun x => φ x γ) := highLocalFrameFeature_measurable k j
    have hR := highMarkedSampleNumerator_measurable n (π j) (activation j) (hAct j)
      a V η p hp (pReset j) (hReset j) (cReset j) (hcReset j) g w hg hw φ hφ (c j) y
    have hq : Measurable (fun x : Fin n → Covariate d =>
        ∏ i, highMarkedResponseMass a V η g w φ (c j) (x i) (y i)) :=
      Finset.measurable_prod _ (fun i _ =>
        (highMarkedResponseMass_measurable a V η g w hg hw φ hφ (c j) (y i)).comp (measurable_pi_apply i))
    have hL : Measurable (fun x : Fin n → Covariate d => selectedRawLikelihood p
        (highMarkedResponseMass a V η g w φ (c j)) x y) :=
      (Finset.measurable_prod _ (fun i _ => hp.comp (measurable_pi_apply i))).mul hq
    exact hR.div hL
  have hSm : Measurable S := h_highFrameFullMarkedScore_measurable
  have hEm : Measurable Eglobal := by
    apply Finset.measurable_sum
    intro y hy
    exact (Finset.measurable_prod _ (fun i _ =>
      ternaryMass_measurable_comp a V _ (hF.comp (measurable_pi_apply i)) (y i))).mul
        ((hSm.comp (measurable_id.prodMk measurable_const)).pow_const 2)
  have hEn (x : Fin n → Covariate d) : 0 ≤ Eglobal x :=
    Finset.sum_nonneg (fun y _ => mul_nonneg
      (Finset.prod_nonneg (fun i _ => hcMass.le.trans (hq (x i) (y i)))) (sq_nonneg _))
  have hpoint (x : Fin n → Covariate d) : Eglobal x ≤ (3 ^ d : ℕ) * ∑ j, Elocal j x := by
    have h_highFrameMarkedScore_energy_bound (p : Fin n → ℝ) (pReset : HighWindowLabels d k → E → Fin n → ℝ) (hReset : ∀ j i, Measurable (fun e => pReset j e i)) (hBound : ∀ j e i, |pReset j e i| ≤ pPlus) (hpd : ∀ i, p i ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (highFrameField d k η (fun l => highFramePolynomial (c l)) (x i)) V b) (hpReset : ∀ j e i b, 0 ≤ ternaryMass a (coefficientRegression η (fun i => highLocalFieldWithout d k D η c j (x i)) (fun i => highPeriodicTensor d k j (x i)) (fun i => highLocalFrameFeature k j (x i)) (cReset j e) i) V b) (hDensity : ∀ j, (∫ e, activation j e * ∏ i, pReset j e i ∂π j) = 0) : (∫ y, (∑ j, highFrameMarkedScore d k D n π activation a V η p pReset cReset c x j y)^2
        ∂Measure.pi (fun i => ternaryIndexMeasure a
          (highFrameField d k η (fun l => highFramePolynomial (c l)) (x i)) V
          ha (fun b => (hp i b).le))) ≤
        (3^d : ℕ) * ∑ j, ∫ y,
          (highFrameMarkedScore d k D n π activation a V η p pReset cReset c x j y)^2
          ∂Measure.pi (fun i => ternaryIndexMeasure a
            (highFrameField d k η (fun l => highFramePolynomial (c l)) (x i)) V
            ha (fun b => (hp i b).le)) := by
      apply finite_overlap_variance_bound _
        (highFrameMarkedScore d k D n π activation a V η p pReset cReset c x)
        (fun j l => l ∈ highNeighborLabels d k j) (3^d)
      · intro j l
        exact ⟨highNeighborLabels_symmetric d k j l, highNeighborLabels_symmetric d k l j⟩
      · intro j
        convert highNeighborLabels_card_le d k j using 1
        congr 1
        ext l
        simp
      · intro j l hjl
        have h_highFrameMarkedScore_orthogonal := highMarkedLocalScores_orthogonal π activation a V η ha p pReset cReset
            (fun j i => highLocalFieldWithout d k D η c j (x i))
            (fun j i => highPeriodicTensor d k j (x i))
            (fun j i => highLocalFrameFeature k j (x i)) c
            (fun i => highFrameField d k η (fun l => highFramePolynomial (c l)) (x i))
            (fun j => highFrameField_coefficientRegression d k D n hk η c j x)
            (fun j => highPatchSampleIndices d k n j x)
            (fun j i hi => highPeriodicTensor_sample_zero_outside_patch d k n j x i hi)
            hpd hp (fun j y => highMarkedResponseAction_integrable (π j) (activation j) (hActI j)
              a V η ha pPlus hpPlus (pReset j) (hReset j) (hBound j) (cReset j) (hcReset j)
              _ _ _ (hpReset j) y) hDensity j l
            (highPatchSampleIndices_disjoint d k n x j l hjl)
        exact h_highFrameMarkedScore_orthogonal
    have he := h_highFrameMarkedScore_energy_bound (p ∘ x) (fun j e => pReset j e ∘ x) (fun j i => (hReset j).comp (measurable_id.prodMk measurable_const)) (fun j e i => hBound j e (x i)) (fun i => (hpMinus.trans_le (hraw (x i)).1).ne') (fun i y => hcMass.trans_le (hq (x i) y)) (fun j e i y => hqReset j e (x i) y) (fun j => hDensity j x)
    rw [ternary_index_product_integral] at he
    have hloc (j : HighWindowLabels d k) :
        (∫ y, highFrameMarkedScore d k D n π activation a V η (p ∘ x)
          (fun j e => pReset j e ∘ x) cReset c x j y ^ 2
          ∂Measure.pi (fun i => ternaryIndexMeasure a (F (x i)) V ha
            (fun y => (hcMass.trans_le (hq (x i) y)).le))) = Elocal j x := by
      have hreg := highFrameField_coefficientRegression d k D n hk η c j x
      change coefficientRegression η (highLocalFieldWithout d k D η c j ∘ x)
        (highPeriodicTensor d k j ∘ x) ((fun x => highLocalFrameFeature k j x) ∘ x) (c j) =
          (fun i => F (x i)) at hreg
      have hs := high_marked_sample_energy_integral n (π j) (activation j) a V η ha p (pReset j)
        (cReset j) (highLocalFieldWithout d k D η c j) (highPeriodicTensor d k j)
          (fun x => highLocalFrameFeature k j x) (c j) x
            (fun x y => hcMass.trans_le (hqLocal j x y))
      rw [ternary_index_product_integral] at hs
      rw [hreg] at hs
      rw [ternary_index_product_integral]
      exact hs
    dsimp only [F] at hloc
    simp_rw [hloc] at he
    exact he
  have hu : Integrable (fun x => (3 ^ d : ℕ) * ∑ j, Elocal j x) μ :=
    (integrable_finsetSum _ (fun j _ => (hlocal j).1)).const_mul _
  have hEI : Integrable Eglobal μ := by
    apply hu.mono' hEm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hEn x)]
      exact hpoint x)
  have hs := response_sample_square_integrable_integral n μ a V ha F hF
    (fun x y => hcMass.le.trans (hq x y)) S hSm hEI
  refine ⟨hs.1, ?_⟩
  rw [hs.2]
  calc
    _ ≤ ∫ x, (3 ^ d : ℕ) * ∑ j, Elocal j x ∂μ := integral_mono hEI hu hpoint
    _ = (3 ^ d : ℕ) * ∑ j, ∫ x, Elocal j x ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => (hlocal j).1)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => (hlocal j).2)) (Nat.cast_nonneg _)
end
end NearlyMinimax
