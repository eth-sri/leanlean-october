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

variable {d : ℕ} (ν : Measure Ω)

def highMarginalRawLikelihood {n : ℕ} (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (z : IndexedSample d n) : ℝ :=
  ∫ ω, highRawSampleLikelihood a V (p ω) (F ω) z ∂ν

theorem highMarginalRawLikelihood_measurable [SFinite ν]
    (n : ℕ) (a V : ℝ) {p F : Ω → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (highMarginalRawLikelihood ν (n := n) a V p F) :=
  (highRawSampleLikelihood_joint_measurable n a V hp hF).stronglyMeasurable.integral_prod_left'.measurable

theorem highMarginalRawLikelihood_pos [IsProbabilityMeasure ν]
    {n : ℕ} {a V P : ℝ} (hP : 0 ≤ P) (ha : a ≠ 0)
    {p F : Ω → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpp : ∀ ω x, 0 < p ω x) (hpb : ∀ ω x, |p ω x| ≤ P)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (z : IndexedSample d n) :
    0 < highMarginalRawLikelihood ν a V p F z := by
  apply integral_likelihood_pos ν _
    (highRawSampleLikelihood_joint_measurable n a V hp hF).of_uncurry_right (P^n)
  · solve_by_elim [highRawSampleLikelihood_pos]
  · exact fun ω => (le_abs_self _).trans
      (highRawSampleLikelihood_abs_le hP (hpb ω) ha
        (fun x y => (hq ω x y).le) z)

/-- The genuine mixture sample density, with the actual constant G_n. -/
theorem highMassTilt_index_marginal_density [IsProbabilityMeasure ν]
    (n : ℕ) {a V : ℝ} {p F : Ω → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    {aRaw bRaw : ℝ} (haRaw : 0 < aRaw) (ha : a ≠ 0)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) :
    (highSampleIndexKernel n a V hp hF) ∘ₘ
        (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n) =
      (highSampleReference d n).withDensity (fun z => ENNReal.ofReal
        (highMarginalRawLikelihood ν a V p F z /
          massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)) := by
  let m  := fun ω => highRawDensityMass (p ω)
  have hm  := highRawDensityMass_joint_measurable hp
  have hb ω  :=
    highRawDensityMass_mem_Icc hp.of_uncurry_left haRaw
      (Eventually.of_forall (hraw ω))
  have hG := massPowerNormalizer_pos ν hm n haRaw hb
  let _ := massPowerTilt_isProbability ν hm n haRaw hb
  have hpabs ω x : |p ω x| ≤ |bRaw| := by
    grind
  let L : Ω × (IndexedSample d n) → ℝ := fun z =>
    highRawSampleLikelihood a V (p z.1) (F z.1) z.2 / massPowerNormalizer ν m n
  have hL : Measurable L := (highRawSampleLikelihood_joint_measurable n a V hp hF).div_const _
  have hLb (z) : 0 ≤ L z ∧ L z ≤ |bRaw|^n / massPowerNormalizer ν m n := by
    have hl0 : 0 ≤ highRawSampleLikelihood a V (p z.1) (F z.1) z.2 :=
      Finset.prod_nonneg (fun i _ => mul_nonneg (haRaw.le.trans (hraw z.1 _).1) (hq z.1 _ _))
    have hlb := highRawSampleLikelihood_abs_le (abs_nonneg _) (hpabs z.1) ha (hq z.1) z.2
    exact ⟨div_nonneg hl0 hG.le, div_le_div_of_nonneg_right ((le_abs_self _).trans hlb) hG.le⟩
  rw [← Measure.snd_compProd, Measure.snd,
    massPowerTilt_highSample_compProd ν n a V hp hF haRaw hraw, map_snd_prod_withDensity_ofReal ν (highSampleReference d n) hL (by positivity) hLb]
  simp only [L, integral_div, highMarginalRawLikelihood, m]

end NearlyMinimax
