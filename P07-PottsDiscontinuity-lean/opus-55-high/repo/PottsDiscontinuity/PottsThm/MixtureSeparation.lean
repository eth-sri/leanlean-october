module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.PottsThm.DiscontinuityConsequences
public import PottsDiscontinuity.PottsThm.FreeCorrelationLimit
public import PottsDiscontinuity.PottsThm.WiredCorrelation
public import PottsDiscontinuity.PottsThm.WiredInfiniteAssociation

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.RCInfinite

section
variable (q : ℕ) (hq : 4 < q)
theorem criticalFreeBoxLimit (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 0 φ.toMeasure) :
    Tendsto (fun n => boxProbabilityMeasure
      (fkParameters q (by omega) (pottsCriticalBeta q) (pottsCriticalBeta_pos q hq))
      (0, 0) n) atTop (𝓝 φ) := by
  have ht := boxMeasure_tendsto (criticalFKParameters q hq) 0 φ.toMeasure hφ
  tauto

theorem criticalWiredBoxLimit (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 1 φ.toMeasure) :
    Tendsto (fun n => wiredBoxProbabilityMeasure
      (fkParameters q (by omega) (pottsCriticalBeta q) (pottsCriticalBeta_pos q hq))
      (0, 0) n) atTop (𝓝 φ) := by
  have ht := boxMeasure_tendsto (criticalFKParameters q hq) 1 φ.toMeasure hφ
  tauto

theorem criticalInfiniteAt_translate (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 1 φ.toMeasure)
    (x : LatticeVertex) :
    φ.toMeasure.real (infiniteAt x) = φ.toMeasure.real (infiniteAt (0, 0)) := by
  have htrans := limit_translate_real (criticalFKParameters q hq) 1 φ.toMeasure hφ
    x (measurableSet_infiniteAt x)
  have hpre : (edgeTranslate x) ⁻¹' infiniteAt x = infiniteAt (0, 0) := by
    simpa [latticeTranslate] using infiniteAt_preimage x (0, 0)
  simp_all

/-- At criticality, the wired average has a uniform two point excess over the
free limit. The gap comes from any one pinned component with positive
percolation probability and wired FKG. -/
theorem critical_potts_free_measure_ne_wired_average (μ : Fin (q + 1) → ProbabilityMeasure (SpinSpace q))
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
  intro heq
  let j0 : Fin q := ⟨0, by omega⟩
  have hφ (i) := criticalWiredBoxLimit q hq (φp i) (hRCp i)
  have hθ := ENNReal.toReal_pos
    (rc_discontinuity_of_positive_rate q hq φ₀ (φp j0) hRC₀ (hRCp j0) L hL hrate).2.ne' (measure_ne_top _ _)
  have hq' : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hc : 0 < 1 - 1 / (q : ℝ) := by rw [sub_pos, div_lt_one] <;> linarith
  have hlim := free_spin_correlation_tendsto_uniform q hq φ₀ hRC₀ (μ 0) hμ₀
    (criticalFreeBoxLimit q hq φ₀ hRC₀) L hL hrate
  have hpos : 0 < (1 - 1 / (q : ℝ)) * (φp j0).toMeasure.real (infiniteAt (0, 0)) ^ 2 / q := by positivity
  refine absurd (ge_of_tendsto hlim (.of_forall fun n => ?_)) (not_le.2 (lt_add_of_pos_right _ hpos))
  have h := congrArg (·.real {σ : SpinSpace q | σ (0, 0) = σ (diagonalSite n)}) heq
  simp [Measure.real_def, ENNReal.toReal_sum] at h
  have hj := wired_infinite_at_positive_association _ (φp j0) (hφ j0) (0, 0) (diagonalSite n)
  rw [criticalInfiniteAt_translate q hq (φp j0) (hRCp j0) (diagonalSite n)] at hj
  have hs (i : Fin q) := wired_spin_correlation_lower_bound q (by omega) (pottsCriticalBeta q)
    (pottsCriticalBeta_pos q hq) i.succ (Nat.le_add_left 1 _) (φp i) (hφ i) (μ i.succ) (hμp i) (0, 0) (diagonalSite n)
  have hS := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hs i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hS
  have := Finset.single_le_sum (f := fun i => (φp i).toMeasure.real (infiniteAt (0, 0) ∩ infiniteAt (diagonalSite n)))
    (fun i _ => measureReal_nonneg) (Finset.mem_univ j0)
  simp only [Measure.real_def, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at *
  rw [h, ← add_div, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [mul_one_div_cancel (by positivity)] at hS
  linarith [mul_le_mul_of_nonneg_left (hj.trans this) hc.le, sq (φp j0 |>.toMeasure (infiniteAt (0, 0))).toReal]

end

end PottsDiscontinuity.PottsThm
