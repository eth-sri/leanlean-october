module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.IsPottsInfiniteVolumeLimit
public import PottsDiscontinuity.Frozen.Defs.IsTranslationErgodic
public import PottsDiscontinuity.Frozen.Defs.DiagonalSite
public import PottsDiscontinuity.Frozen.Defs.PottsCriticalBeta
public import PottsDiscontinuity.RCMProof.Item3
public import PottsDiscontinuity.TorusCrossing.Final
public import PottsDiscontinuity.Infra.Lambda
public import PottsDiscontinuity.PottsThm.ColoringPushforward
public import PottsDiscontinuity.Potts.FreePottsLimit
public import PottsDiscontinuity.Potts.WiredPottsLimit
public import PottsDiscontinuity.PottsThm.CriticalParameters
public import PottsDiscontinuity.Duality.Discontinuity
public import PottsDiscontinuity.PottsThm.MixtureSeparation
public import PottsDiscontinuity.PottsThm.PottsColoringErgodicity
public import PottsDiscontinuity.Potts.FreeSpinFormula

/-!
# Theorem statement `potts_theorem_1_1` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

open FK Potts PottsThm Duality RCInfinite

/-- **Theorem 1.1** (arXiv:1611.09877v2, p. 2). -/
theorem potts_theorem_1_1 (q : ℕ) (hq : 4 < q) :
    ∃ μ : Fin (q + 1) → Measure (ℤ × ℤ → Set.Icc 1 q),
      (∀ i, IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) i (μ i)) ∧
      ((∀ i j, i ≠ j → μ i ≠ μ j) ∧ (∀ i, IsTranslationErgodic (μ i)) ∧
        μ 0 ≠ (q : ℝ≥0∞)⁻¹ • ∑ i : Fin q, μ i.succ) ∧
      (∀ i : Fin q, (1 : ℝ) / q < (μ i.succ).real {σ | ((σ (0, 0) : ℕ)) = (i.succ : ℕ)}) ∧
      (∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
              (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((μ 0).real {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / q))
            atTop (𝓝 (lam + 2 * S)) ∧
          0 < lam + 2 * S) := by
  classical
  have hq2 : 2 ≤ q := by omega
  have hqR : (4 : ℝ) < q := by exact_mod_cast hq
  let β := pottsCriticalBeta q
  have hβ : 0 < β := pottsCriticalBeta_pos q hq
  let θ := fkParameters q hq2 β hβ
  let Q : Set.Ici (1 : ℝ) := ⟨q, Set.mem_Ici.2 (by linarith)⟩
  have hθ : θ = FK.criticalParameters Q := fkParameters_pottsCriticalBeta q hq2 hβ
  obtain ⟨φ₀, hφ₀, _⟩ := FK.freeBoxLimit_existsUnique θ
  have hw₀ := hφ₀.atOrigin
  obtain ⟨φ₁, hw₁⟩ := FK.wiredBoxProbabilityMeasure_exists_limit θ
  have hRC₀ := FK.isRCInfiniteVolumeLimit_of_freeBox_tendsto θ φ₀ hw₀
  have hRC₁ := FK.isRCInfiniteVolumeLimit_of_wiredBox_tendsto θ φ₁ hw₁
  have hc₀ : IsRCInfiniteVolumeLimit (FK.criticalParameters Q).toP (FK.criticalParameters Q).toQ
      0 φ₀.toMeasure := by simpa only [hθ] using hRC₀
  have hr := RCMProof.rcItem3ForEveryFreeLimit_proved TorusCrossing.h319_proved _ hqR φ₀.toMeasure hc₀
  obtain ⟨hL, hcosh⟩ := arcosh_pos_of_gt4 (q : ℝ) hqR
  obtain ⟨S, hS, hrate⟩ := hr _ hL hcosh
  have hDisc := critical_discontinuity_of_pos_diagonal_rate Q _ _ hc₀ (by simpa only [hθ] using hRC₁) _
    (RCMProof.altTanhLimit_pos hL hS) hrate
  have hNo : φ₀.toMeasure existsInfiniteCluster = 0 := by
    apply nonpos_iff_eq_zero.mp
    rw [← not_lt]
    exact (not_lt_of_ge hDisc.1.le) ∘ (infiniteCluster_pos_iff_origin_pos θ 0 _ hRC₀).mp
  let seed : Set.Icc 1 q := ⟨1, le_rfl, by omega⟩
  let pin (i : Fin q) := boundaryColor q i.succ (by simp)
  let μP : Fin (q+1) → ProbabilityMeasure (SpinSpace q) :=
    Fin.cases (coloringProbability φ₀ seed) (fun i => coloringProbability φ₁ (pin i))
  let μ (i : Fin (q+1)) := (μP i).toMeasure
  let (i : Fin (q+1)) : IsProbabilityMeasure (μ i) := (μP i).prop
  have hLim₀ : IsPottsInfiniteVolumeLimit q β 0 (μ 0) := by
    refine potts_limit_of_cylinder_limits q hq2 β hβ 0 (μP 0) fun A ξ => ?_
    simpa only [← (freeColoringMap_isFreeESC φ₀ seed hNo).2 A ξ] using!
      free_potts_cylinder_tendsto q hq2 β hβ φ₀ hw₀ A ξ
  have hLim₁ (i : Fin q) : IsPottsInfiniteVolumeLimit q β i.succ (μ i.succ) := by
    refine potts_limit_of_cylinder_limits q hq2 β hβ i.succ (μP i.succ) fun A ξ => ?_
    simpa only [← (wiredColoringMap_isWiredESC φ₁ i.succ (by simp)).2 A ξ] using!
      wired_potts_cylinder_tendsto q hq2 β hβ i.succ (by simp) φ₁ hw₁ A ξ
  let : Nonempty (Set.Icc 1 q) := ⟨seed⟩
  have hm₀ : IsTranslationMixing (μ 0) := clusterColoring_map_mixing_of_RCmixing θ 0 _ hRC₀ seed
  have hm₁ (i : Fin q) : IsTranslationMixing (μ i.succ) := clusterColoring_map_mixing_of_RCmixing θ 1 _ hRC₁ (pin i)
  let A (i : Fin q) : Set (SpinSpace q) := {σ | σ (0,0) = pin i}
  have hA (i : Fin q) : MeasurableSet (A i) := (measurable_pi_apply _) (measurableSet_singleton _)
  have hzero : φ₀.toMeasure.real (infiniteAt (0,0)) = 0 := by
    rw [← Duality.infiniteClusterAt_eq_infiniteAt, Measure.real_def]
    change (φ₀.toMeasure (infiniteClusterAt 0)).toReal = 0
    simp [hDisc.1]
  have hpos : 0 < φ₁.toMeasure.real (infiniteAt (0,0)) := by
    rw [← Duality.infiniteClusterAt_eq_infiniteAt]
    exact ENNReal.toReal_pos hDisc.2.1.ne' (measure_ne_top _ _)
  have hfree (i : Fin q) : (μ 0).real (A i) = 1 / (q : ℝ) := by
    change (coloringMeasure φ₀ seed).real (A i) = _
    simp [A, coloringMeasure_site, hzero]
  have hon (i : Fin q) : 1 / (q : ℝ) < (μ i.succ).real (A i) := by
    change _ < (coloringMeasure φ₁ (pin i)).real (A i)
    simp only [A, coloringMeasure_site, eq_self, ite_true]
    have hqpos : (1 : ℝ) < q := by linarith
    have hh := mul_pos (sub_pos.mpr ((div_lt_one (by positivity : (0 : ℝ) < q)).mpr hqpos)) hpos
    linarith
  have hoff (i j : Fin q) (hij : i ≠ j) : (μ i.succ).real (A j) ≤ 1 / (q : ℝ) := by
    have hpin : pin i ≠ pin j := fun h => hij (Fin.succ_inj.mp (Fin.ext (congrArg Subtype.val h)))
    change (coloringMeasure φ₁ (pin i)).real (A j) ≤ _
    simp only [A, coloringMeasure_site, ite_eq_right hpin]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 1 / (q : ℝ))
      (measureReal_nonneg (μ := φ₁.toMeasure) (s := infiniteAt (0,0)))]
  have hdistinct (i j : Fin (q+1)) (hij : i ≠ j) (he : μ i = μ j) : False := by
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact hij rfl
      | succ j => exact (not_lt_of_ge (le_of_eq (he ▸ hfree j))) (hon j)
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (not_lt_of_ge (le_of_eq (he.symm ▸ hfree i))) (hon i)
      | succ j => exact (not_lt_of_ge (he ▸ hoff i j (fun h => hij (congrArg Fin.succ h)))) (hon j)
  have hne (he : μ 0 = (q : ℝ≥0∞)⁻¹ • ∑ i : Fin q, μ i.succ) : False := by
    let j : Fin q := ⟨0, by omega⟩
    have : ∀ i : Fin q, IsProbabilityMeasure (μ i.succ) := fun i => inferInstance
    exact (hon j).ne ((mixing_average_real_eq (by omega) (μ 0) (fun i => μ i.succ)
      hm₀ hm₁ he (hA j) j).trans (hfree j)).symm
  refine ⟨μ, Fin.cases hLim₀ hLim₁, ⟨hdistinct, Fin.cases hm₀.ergodic (fun i => (hm₁ i).ergodic), hne⟩, ?_, ?_⟩
  · intro i
    simpa only [A, Subtype.ext_iff, pin, boundaryColor] using hon i
  · intro lam hlam hc
    obtain ⟨T, hT, ht⟩ := hr lam hlam hc
    refine ⟨T, hT, ?_, RCMProof.altTanhLimit_pos hlam hT⟩
    let c := 1 - 1 / (q : ℝ)
    have hc : 0 < c := sub_pos.mpr ((div_lt_one (by positivity : (0 : ℝ) < q)).2 (by linarith))
    have hconn (n : ℕ) : 0 < φ₀.toMeasure.real
        {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)} := by
      change 0 < φ₀.toMeasure.real (Duality.connectionEvent 0 (diagonalSite n))
      rw [← TorusExploration.corrLength_connectionEvent_eq]
      exact CorrLength.isRCInfiniteVolumeLimit_connection_positive θ _ hRC₀ _ _
    have hsmall := tendsto_const_div_atTop_nhds_zero_nat (-Real.log c)
    have hcorr := free_spin_correlation q hq2 β hβ φ₀ hw₀ (μP 0) hLim₀
    simpa only [zero_add] using (hsmall.add ht).congr (fun n => by
      rw [hcorr, add_sub_cancel_left, Real.log_mul hc.ne' (hconn n).ne']
      ring)

end PottsDiscontinuity
