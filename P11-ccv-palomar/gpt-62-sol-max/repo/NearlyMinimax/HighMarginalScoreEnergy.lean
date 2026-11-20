module

public import NearlyMinimax.HighMarginalScore
public import NearlyMinimax.PosteriorScoreEnergy
public import NearlyMinimax.HighRawScoreEnergy


@[expose] public section

/-! Actual observed-data Fisher energy is bounded by genuine latent
append/heat likelihood Fisher energy. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem highMarginalRealScore_memLp_energy {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η aRaw bRaw : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (B : ℝ) (hE : HighRawFisherBudget ν n a V p F
      (highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F) B) :
    let P := highDataLaw ν n a V p F hp hF
    MemLp (highMarginalRealScore dependent hsymm ν π activation n a V η p F) 2 P ∧
      (∫ z, (highMarginalRealScore dependent hsymm ν π activation n a V η p F z)^2 ∂P) ≤ B := by
  unfold HighRawFisherBudget at hE
  let μ := highSampleReference d n
  let L : HistoryMarked dependent E × TernarySample d n → ℝ := fun z =>
    highRawSampleLikelihood n a V (p z.1) (F z.1) z.2
  let D : HistoryMarked dependent E × TernarySample d n → ℝ := fun z =>
    highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2
  let m := fun ω => highRawDensityMass (p ω)
  let G := massPowerNormalizer ν m n
  have hm := highRawDensityMass_joint_measurable p hp
  have hb (ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
    highRawDensityMass_joint_mem_Icc hp haRaw hraw ω
  have hG := massPowerNormalizer_pos ν m hm n aRaw bRaw haRaw hb
  have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ |bRaw| := highRawDensity_abs_bound haRaw.le hraw ω x
  have hLp (z) : 0 < L z := highRawSampleLikelihood_pos n a V p F
    (fun ω x => haRaw.trans_le (hraw ω x).1) hq z.1 z.2
  have hLb (z) : L z ≤ |bRaw|^n := (le_abs_self _).trans
    (highRawSampleLikelihood_abs_le n a V |bRaw| _ _ (hpb z.1) ha.ne'
      (fun x y => (hq z.1 x y).le) z.2)
  have hDb (z) : |D z| ≤ (Fintype.card J : ℝ) * (Ba * |bRaw|^n) +
      η^2 * (|bRaw|^n * ((n : ℝ)/a^2)) :=
    highHistoryLikelihoodDerivative_abs_le π dependent hsymm activation Ba hBa habound
      n a V η |bRaw| (abs_nonneg _) ha p F hpb (fun ω x y => (hq ω x y).le) z.1 z.2
  have he := posteriorMeanScore_memLp_energy ν μ L D
    (highRawSampleLikelihood_joint_measurable n a V p F hp hF)
    (highHistoryLikelihoodDerivative_measurable dependent hsymm π activation ham n a V η p F hp hF)
    hLp (|bRaw|^n) _ G hG hLb hDb hE.1
  have hR := highMarginalRealScore_measurable dependent hsymm ν π activation ham n a V η p F hp hF
  dsimp only
  rw [highDataLaw_eq_density_map ν n a V p F hp hF aRaw bRaw haRaw ha.ne' hraw
    (fun ω x y => (hq ω x y).le)]
  constructor
  · rw [memLp_map_measure_iff hR.aestronglyMeasurable (encodeDesignResponse_measurable a).aemeasurable]
    simp only [Function.comp_def, highMarginalRealScore_encode _ _ _ _ _ ha]
    change MemLp (posteriorMeanScore ν L D) 2
      (μ.withDensity fun z => ENNReal.ofReal ((∫ ω, L (ω, z) ∂ν) / G))
    exact he.1
  · rw [integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) (hR.pow_const 2).stronglyMeasurable]
    simp only [highMarginalRealScore_encode _ _ _ _ _ ha]
    exact he.2.trans hE.2

end NearlyMinimax
