module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitsStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassSupport
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # The initial atom and zero later bins of the canonical visit count -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

variable (nu : Measure Point) (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)

/-- Later enlarged entrances have no mass at the lower observation endpoint. -/
theorem timeBinCount_later_initial_slice_zero
     (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (n : ℕ) :
    enlargedVisitEntrance hH hLE hlam hLam A c J s T P (n + 1) {p | p.time = s} = 0 := by
  have hS : MeasurableSet {p : Point | p.time = s} :=
    (isClosed_eq continuous_time continuous_const).measurableSet
  change (_ : Measure Point).restrict _
    _ = 0
  rw [Measure.restrict_apply hS]
  have he : {p : Point | p.time = s} ∩ visitBoundary s T (visitEntranceInterval c) J =
      ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact (ne_of_lt hp.2.1) hp.1.symm
  simp_all

/-- Starting in the closed entrance interval contributes exactly one atom at its own time. -/
theorem timeBinCount_initial_slice
     (c : Clock) (J : Interval) (T : ℝ) (P : Point)
    (hv : P.velocity 0 ∈ closure c.entrance) :
    visitsFromZero hH hLE hlam hLam A c J T P {p | p.time = P.time} = 1 := by
  have hS : MeasurableSet {p : Point | p.time = P.time} :=
    (isClosed_eq continuous_time continuous_const).measurableSet
  let gm := enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P
  change Measure.sum gm _ = 1
  rw [Measure.sum_apply _ hS]
  have hz : ∀ n : ℕ, n ≠ 0 → gm n {p | p.time = P.time} = 0 := by
    intro n hn
    cases n with
    | zero => omega
    | succ n =>
      exact timeBinCount_later_initial_slice_zero
        hH hLE hlam hLam A c J P.time _ P n
  rw [tsum_eq_single 0 hz]
  have he : gm 0 = Measure.dirac P := ite_eq_left hv
  simp_all

/-- A later bin entirely beyond the observation horizon contains no starts. -/
theorem timeBinCount_mass_eq_zero_of_horizon_le
     (c : Clock) (J : Interval) (T : ℝ) (P : Point)
    (hT : 0 < T) (j : ℕ) (hj : j ≠ 0) (hTJ : T ≤ (j : ℝ) * c.r ^ 2) :
    enlargedTimeVisitMass (visitsFromZero hH hLE hlam hLam A c J T P) c P.time j = 0 := by
  have hs := enlargedVisitStarts_ae_support hH hLE hlam hLam A c J P.time (P.time + T)
    P le_rfl (by simp_all)
  have hz : visitsFromZero hH hLE hlam hLam A c J T P
      {p | p.time ∈ enlargedTimeBin c.r P.time j ∧
        p.velocity 0 ∈ closure c.entrance} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hs] with p hp
    intro hcell
    have ht := hcell.1
    rw [enlargedTimeBin] at ht
    grind
  exact congrArg ENNReal.toReal hz

/-- Later bins are bounded by the literal slab truncated at the supported horizon. -/
theorem timeBinCount_mass_le_truncated_slab  [IsFiniteMeasure nu]
    (c : Clock) (s T : ℝ) (j : ℕ) (hj : j ≠ 0)
    (hnu : ∀ᵐ p ∂nu, p.time < s + T) :
    enlargedTimeVisitMass nu c s j ≤
      (nu {p | p.time ∈ Ioc (s + (j : ℝ) * c.r ^ 2)
        (s + min (((j : ℝ) + 1) * c.r ^ 2) T)}).toReal := by
  apply ENNReal.toReal_mono (measure_ne_top nu _)
  apply measure_mono_ae
  filter_upwards [hnu] with p hp
  intro hcell
  have ht := hcell.1
  rw [enlargedTimeBin] at ht
  grind

/-- Bin zero charges its initial atom and its positive-time slab separately. -/
theorem timeBinCount_initial_mass_le_atom_add_slab
     [IsFiniteMeasure nu] (c : Clock) (s T : ℝ)
    (hnu : ∀ᵐ p ∂nu, p.time < s + T) :
    enlargedTimeVisitMass nu c s 0 ≤ (nu {p | p.time = s}).toReal +
      (nu {p | p.time ∈ Ioc s (s + min (c.r ^ 2) T)}).toReal := by
  let A : Set Point := {p | p.time = s}
  let B : Set Point := {p | p.time ∈ Ioc s (s + min (c.r ^ 2) T)}
  have hm : nu {p | p.time ∈ enlargedTimeBin c.r s 0 ∧
      p.velocity 0 ∈ closure c.entrance} ≤ nu A + nu B := by
    apply (measure_mono_ae ?_).trans (measure_union_le A B)
    filter_upwards [hnu] with p hp
    intro hcell
    have ht := hcell.1
    rcases eq_or_lt_of_le ht.1 with he | hlt
    · grind
    · right
      refine ⟨hlt, ?_⟩
      rw [add_min]
      exact le_min ht.2 hp.le
  have hr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top nu A, measure_ne_top nu B⟩) hm
  rw [ENNReal.toReal_add (measure_ne_top nu A) (measure_ne_top nu B)] at hr
  exact hr

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
