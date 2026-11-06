module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.PottsThm.DiscontinuityConsequences
public import PottsDiscontinuity.PottsThm.FreeCorrelationLimit
public import PottsDiscontinuity.PottsThm.WiredCorrelation
public import PottsDiscontinuity.PottsThm.WiredInfiniteAssociation

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.RCInfinite

private theorem criticalFreeBoxLimit (q : ℕ) (hq : 4 < q)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 0 φ.toMeasure) :
    Tendsto (fun n => boxProbabilityMeasure
      (fkParameters q (by omega) (pottsCriticalBeta q) (pottsCriticalBeta_pos q hq))
      (0, 0) n) atTop (𝓝 φ) := by
  have ht := boxMeasure_tendsto (criticalFKParameters q hq) 0 φ.toMeasure hφ
  rw [show (⟨φ.toMeasure, hφ.1⟩ : ProbabilityMeasure LatticeConfiguration) = φ by ext; rfl] at ht
  simpa [boxMeasure_free, criticalFKParameters, fkParameters] using ht

private theorem criticalWiredBoxLimit (q : ℕ) (hq : 4 < q)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 1 φ.toMeasure) :
    Tendsto (fun n => wiredBoxProbabilityMeasure
      (fkParameters q (by omega) (pottsCriticalBeta q) (pottsCriticalBeta_pos q hq))
      (0, 0) n) atTop (𝓝 φ) := by
  have ht := boxMeasure_tendsto (criticalFKParameters q hq) 1 φ.toMeasure hφ
  rw [show (⟨φ.toMeasure, hφ.1⟩ : ProbabilityMeasure LatticeConfiguration) = φ by ext; rfl] at ht
  simpa [boxMeasure_wired, criticalFKParameters, fkParameters] using ht

private theorem criticalInfiniteAt_translate (q : ℕ) (hq : 4 < q)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 1 φ.toMeasure)
    (x : LatticeVertex) :
    φ.toMeasure.real (infiniteAt x) = φ.toMeasure.real (infiniteAt (0, 0)) := by
  have htrans := limit_translate_real (criticalFKParameters q hq) 1 φ.toMeasure hφ
    x (measurableSet_infiniteAt x)
  rwa [show (edgeTranslate x) ⁻¹' infiniteAt x = infiniteAt (0, 0) by
    simpa [latticeTranslate] using infiniteAt_preimage x (0, 0), eq_comm] at htrans

theorem critical_potts_free_measure_ne_wired_average (q : ℕ) (hq : 4 < q)
    (μ : Fin (q + 1) → ProbabilityMeasure (SpinSpace q))
    (φ₀ : ProbabilityMeasure LatticeConfiguration)
    (φp : Fin q → ProbabilityMeasure LatticeConfiguration)
    (hRC₀ : IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 0 φ₀.toMeasure)
    (hμ₀ : IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) 0 (μ 0).toMeasure)
    (hRCp : ∀ i : Fin q, IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 1 (φp i).toMeasure)
    (hμp : ∀ i : Fin q, IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) i.succ
      (μ i.succ).toMeasure)
    (L : ℝ) (hL : 0 < L)
    (hrate : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
      (φ₀.toMeasure.real
        {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
      atTop (𝓝 L)) :
    (μ 0).toMeasure ≠ (q : ℝ≥0∞)⁻¹ • ∑ i : Fin q, (μ i.succ).toMeasure := by
  have hq2 : 2 ≤ q := by omega
  let j0 : Fin q := ⟨0, by omega⟩
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hqRpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hβ : 0 < pottsCriticalBeta q := pottsCriticalBeta_pos q hq
  have hφ₀weak := criticalFreeBoxLimit q hq φ₀ hRC₀
  have hφpweak (i : Fin q) := criticalWiredBoxLimit q hq (φp i) (hRCp i)
  have hdisc := rc_discontinuity_of_positive_rate q hq φ₀ (φp j0)
    hRC₀ (hRCp j0) L hL hrate
  have hθ : 0 < (φp j0).toMeasure.real (infiniteAt (0, 0)) :=
    ENNReal.toReal_pos (show 0 < (φp j0).toMeasure (infiniteAt (0, 0)) from hdisc.2).ne'
      (measure_ne_top _ _)
  let c : ℝ := 1 - 1 / (q : ℝ)
  have hc : 0 < c := sub_pos.mpr ((div_lt_one hqRpos).2 hqR)
  have hjoint (n : ℕ) :
      (φp j0).toMeasure.real (infiniteAt (0, 0)) ^ 2 ≤
        (φp j0).toMeasure.real (infiniteAt (0, 0) ∩ infiniteAt (diagonalSite n)) := by
    have hfkg := wired_infinite_at_positive_association
      (criticalFKParameters q hq) (φp j0) (hφpweak j0) (0, 0) (diagonalSite n)
    rw [criticalInfiniteAt_translate q hq (φp j0) (hRCp j0) (diagonalSite n)] at hfkg
    nlinarith [hfkg]
  have hcorrLower (i : Fin q) (n : ℕ) :
      1 / (q : ℝ) + c * (φp i).toMeasure.real
        (infiniteAt (0, 0) ∩ infiniteAt (diagonalSite n)) ≤
      (μ i.succ).toMeasure.real {σ | σ (0, 0) = σ (diagonalSite n)} := by
    simpa [c, ProbabilityMeasure.measureReal_eq_coe_coeFn] using
      wired_spin_correlation_lower_bound q hq2 (pottsCriticalBeta q) hβ
        i.succ (by simp) (φp i) (hφpweak i) (μ i.succ) (hμp i) (0, 0) (diagonalSite n)
  have hsumGap (n : ℕ) :
      (q : ℝ) * (1 / (q : ℝ)) + c * ((φp j0).toMeasure.real (infiniteAt (0, 0)) ^ 2) ≤
        ∑ i : Fin q, (μ i.succ).toMeasure.real {σ | σ (0, 0) = σ (diagonalSite n)} := by
    let d : Fin q → ℝ := fun i => (μ i.succ).toMeasure.real
      {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / (q : ℝ)
    have hd (i : Fin q) : 0 ≤ d i := by
      dsimp [d]
      linarith [hcorrLower i n, mul_nonneg hc.le (measureReal_nonneg (μ := (φp i).toMeasure)
        (s := infiniteAt (0, 0) ∩ infiniteAt (diagonalSite n)))]
    have hdsum : c * ((φp j0).toMeasure.real (infiniteAt (0, 0)) ^ 2) ≤ ∑ i : Fin q, d i :=
      le_trans (by dsimp [d]; linarith [hcorrLower j0 n, mul_le_mul_of_nonneg_left (hjoint n) hc.le])
        (Finset.single_le_sum (fun i _ => hd i) (Finset.mem_univ j0))
    have hdecomp : (∑ i : Fin q, (μ i.succ).toMeasure.real
        {σ | σ (0, 0) = σ (diagonalSite n)}) = ∑ i : Fin q, (1 / (q : ℝ) + d i) :=
      Finset.sum_congr rfl fun i _ => by dsimp [d]; ring
    rw [hdecomp, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
    linarith
  have hfreeLim := free_spin_correlation_tendsto_uniform q hq φ₀ hRC₀ (μ 0) hμ₀
    hφ₀weak L hL hrate
  intro heq
  have hbound (n : ℕ) :
      1 / (q : ℝ) + (c * ((φp j0).toMeasure.real (infiniteAt (0, 0)) ^ 2)) / q ≤
        (μ 0).toMeasure.real {σ | σ (0, 0) = σ (diagonalSite n)} := by
    have h := congrArg (fun ν : Measure (SpinSpace q) => ν.real
      {σ | σ (0, 0) = σ (diagonalSite n)}) heq
    rw [measureReal_ennreal_smul_apply, show (∑ i : Fin q, (μ i.succ).toMeasure).real
        {σ | σ (0, 0) = σ (diagonalSite n)} = ∑ i : Fin q, (μ i.succ).toMeasure.real
        {σ | σ (0, 0) = σ (diagonalSite n)} by simp [Measure.real_def, ENNReal.toReal_sum]] at h
    have hcorEq : (μ 0).toMeasure.real {σ | σ (0, 0) = σ (diagonalSite n)} =
        (1 / (q : ℝ)) * ∑ i : Fin q, (μ i.succ).toMeasure.real
          {σ | σ (0, 0) = σ (diagonalSite n)} := by simpa using h
    rw [hcorEq]
    calc 1 / (q : ℝ) + (c * ((φp j0).toMeasure.real (infiniteAt (0, 0)) ^ 2)) / q
      _ = (1 / (q : ℝ)) * ((q : ℝ) * (1 / (q : ℝ)) +
          c * ((φp j0).toMeasure.real (infiniteAt (0, 0)) ^ 2)) := by field_simp [hqRpos.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsumGap n) (one_div_pos.mpr hqRpos).le
  have hlimLower := le_of_tendsto_of_tendsto' tendsto_const_nhds hfreeLim hbound
  linarith [div_pos (mul_pos hc (sq_pos_of_pos hθ)) hqRpos]

end PottsDiscontinuity.PottsThm
