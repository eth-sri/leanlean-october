module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassGreenCapacity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassIntegratedGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassArithmetic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassSummation

/-! # Finiteness and uniform mass bounds for the actual entrance counting measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T) (P : Point)
    (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier)

include hT hP in
/-- The actual finite entrance count satisfies the quadratic source estimate. -/
theorem visitCount_partial_quadratic_bound (N : ℕ) :
    5 / 16 * c.r ^ 2 *
      ((∑ n ∈ Finset.range N, visitEntrancePiece hlam hLam A c J s T P n) univ).toReal ≤
        9 / 16 * c.r ^ 2 + 6 * Lam / lam * ((J.hi - J.lo) / 2) * c.r := by
  have h := visitQuadratic_partial_mass_bound hlam hLam A c J s T P hP N
  have he := visitRetainedExit_partial_real_mass_le_one hlam hLam A c J s T hT P hP N
  have hg := visitActiveGreen_partial_capacity hlam hLam A c J s T hT P hP N
  dsimp only at h he hg
  have hh := h.trans (add_le_add
    (mul_le_mul_of_nonneg_left he (by positivity))
    (mul_le_mul_of_nonneg_left hg (by linarith)))
  rw [visit_partial_real_mass _ N univ MeasurableSet.univ]
  convert hh using 1 <;> ring

/-- One ellipticity constant bounds the genuine full visit count in every bounded outer strip. -/
theorem exists_visitCount_mass_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀
        (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (_hT : s < T)
        (P : Point) (_hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier),
        Measure.sum (visitEntrancePiece hlam hLam A c J s T P) univ ≤
          ENNReal.ofReal (C * (1 + ((J.hi - J.lo) / 2) / c.r)) := by
  obtain ⟨C, hC, hc⟩ := exists_visit_mass_arithmetic_constant hlam hLam
  refine ⟨C, hC, ?_⟩
  intro A c J s T hT P hP
  apply visit_sum_mass_le_of_partial_mass_le
  intro N
  have hw := sub_pos.mpr J.ordered
  have hr := c.positive
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ univ) (by positivity)).mpr
  exact hc ((J.hi - J.lo) / 2) c.r _ (by linarith [J.ordered]) c.positive
    (visitCount_partial_quadratic_bound hlam hLam A c J s T hT P hP N)

include hT hP in
/-- The actual full entrance count is finite, without assuming its finiteness in the proof. -/
theorem visitCount_isFiniteMeasure :
    IsFiniteMeasure (Measure.sum (visitEntrancePiece hlam hLam A c J s T P)) := by
  obtain ⟨C, _, hc⟩ := exists_visitCount_mass_constant hlam hLam
  exact ⟨(hc A c J s T hT P hP).trans_lt ENNReal.ofReal_lt_top⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
