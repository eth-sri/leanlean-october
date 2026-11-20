module

public import NearlyMinimax.MarginalLikelihood


@[expose] public section

/-! The exact marginal data density of the actual high mass-tilted experiment. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

def highMarginalRawLikelihood {d : ℕ} (ν : Measure Ω) (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (z : TernarySample d n) : ℝ :=
  ∫ ω, highRawSampleLikelihood n a V (p ω) (F ω) z ∂ν

section
variable {d : ℕ} (ν : Measure Ω)

theorem highMarginalRawLikelihood_measurable [SFinite ν]
    (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (highMarginalRawLikelihood ν n a V p F) :=
  (highRawSampleLikelihood_joint_measurable n a V p F hp hF).stronglyMeasurable.integral_prod_left'.measurable

theorem highMarginalRawLikelihood_pos [IsProbabilityMeasure ν]
    (n : ℕ) (a V P : ℝ) (hP : 0 ≤ P) (ha : a ≠ 0)
    (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpp : ∀ ω x, 0 < p ω x) (hpb : ∀ ω x, |p ω x| ≤ P)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (z : TernarySample d n) :
    0 < highMarginalRawLikelihood ν n a V p F z := by
  apply integral_likelihood_pos ν _
    (highRawSampleLikelihood_joint_measurable n a V p F hp hF).of_uncurry_right (P^n)
  · exact fun ω => highRawSampleLikelihood_pos n a V p F hpp hq ω z
  · exact fun ω => (le_abs_self _).trans
      (highRawSampleLikelihood_abs_le n a V P _ _ (hpb ω) ha
        (fun x y => (hq ω x y).le) z)

/-- The genuine mixture sample density, with the actual constant G_n. -/
theorem highMassTilt_index_marginal_density [IsProbabilityMeasure ν]
    (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw) (ha : a ≠ 0)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) :
    (highSampleIndexKernel n a V p F hp hF) ∘ₘ
        (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n) =
      (highSampleReference d n).withDensity (fun z => ENNReal.ofReal
        (highMarginalRawLikelihood ν n a V p F z /
          massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)) := by
  let m : Ω → ℝ := fun ω => highRawDensityMass (p ω)
  have hm : Measurable m := highRawDensityMass_joint_measurable p hp
  have hb (ω : Ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
    highRawDensityMass_joint_mem_Icc hp haRaw hraw ω
  have hG := massPowerNormalizer_pos ν m hm n aRaw bRaw haRaw hb
  let _ := massPowerTilt_isProbability ν m hm n aRaw bRaw haRaw hb
  have hpabs (ω : Ω) (x : Covariate d) : |p ω x| ≤ |bRaw| := highRawDensity_abs_bound haRaw.le hraw ω x
  let L : Ω × TernarySample d n → ℝ := fun z =>
    highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 / massPowerNormalizer ν m n
  have hL : Measurable L := (highRawSampleLikelihood_joint_measurable n a V p F hp hF).div_const _
  have hLb (z) : 0 ≤ L z ∧ L z ≤ |bRaw|^n / massPowerNormalizer ν m n := by
    have hl0 : 0 ≤ highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 :=
      Finset.prod_nonneg (fun i _ => mul_nonneg (haRaw.le.trans (hraw z.1 _).1) (hq z.1 _ _))
    have hlb := highRawSampleLikelihood_abs_le n a V |bRaw| _ _ (hpabs z.1) ha (hq z.1) z.2
    exact ⟨div_nonneg hl0 hG.le, div_le_div_of_nonneg_right ((le_abs_self _).trans hlb) hG.le⟩
  rw [← Measure.snd_compProd, Measure.snd,
    massPowerTilt_highSample_compProd ν n a V p F hp hF aRaw bRaw haRaw hraw]
  rw [map_snd_prod_withDensity_ofReal ν (highSampleReference d n) L hL
    (|bRaw|^n / massPowerNormalizer ν m n) hLb]
  congr 1
  funext z
  simp only [L, integral_div, highMarginalRawLikelihood, m]

end

section
variable {d : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw) (ha : a ≠ 0)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)

local notation "likelihood" => highMarginalRawLikelihood ν n a V p F
local notation "normalizer" => massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n

include aRaw bRaw haRaw ha hraw hq in
theorem highDataLaw_eq_density_map : highDataLaw ν n a V p F hp hF =
    ((highSampleReference d n).withDensity (fun z => ENNReal.ofReal (likelihood z / normalizer))).map
      (encodeDesignResponse a) := by
  rw [highDataLaw_eq_map, highMassTilt_index_marginal_density ν n a V p F hp hF aRaw bRaw haRaw ha hraw hq]

include aRaw bRaw haRaw ha hraw hq in
theorem highDataLaw_integral_marginal (H : ObservedSample d n → ℝ) (hH : Measurable H) :
    (∫ z, H z ∂highDataLaw ν n a V p F hp hF) =
      (∫ z, likelihood z * H (encodeDesignResponse a z) ∂highSampleReference d n) / normalizer := by
  have hl (z) : 0 ≤ likelihood z := integral_nonneg (fun ω =>
    Finset.prod_nonneg (fun i _ => mul_nonneg (haRaw.le.trans (hraw ω _).1) (hq ω _ _)))
  have hZ := massPowerNormalizer_pos ν _ (highRawDensityMass_joint_measurable p hp) n aRaw bRaw
    haRaw (highRawDensityMass_joint_mem_Icc hp haRaw hraw)
  rw [highDataLaw_eq_density_map ν n a V p F hp hF aRaw bRaw haRaw ha hraw hq,
    integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) hH.stronglyMeasurable,
    integral_realDensity_div (highMarginalRawLikelihood_measurable ν n a V p F hp hF) hl hZ.le]

end

end NearlyMinimax
