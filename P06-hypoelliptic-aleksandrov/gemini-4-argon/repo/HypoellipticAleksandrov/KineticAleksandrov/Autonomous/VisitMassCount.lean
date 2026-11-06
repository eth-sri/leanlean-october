module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassGreenCapacity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassIntegratedGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassArithmetic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassSummation
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Capacity
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationWaiting
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassOuterBounds
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCoefficientIntegral
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassExitIntegrals
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassOutgoing
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassQuadratic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSupport

/-! # Finiteness and uniform mass bounds for the actual entrance counting measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

/- The actual finite entrance count satisfies the quadratic source estimate. -/
theorem exists_visitCount_mass_constant {lam Lam }
    (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
        (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (_hT : s < T)
        (P : Point) (_hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier),
        Measure.sum (visitEntrancePiece hH hLE hlam hLam A c J s T P) univ ≤
          ENNReal.ofReal (C * (1 + ((J.hi - J.lo) / 2) / c.r)) := by
  obtain ⟨C, hC, hc⟩ : ∃ C : ℝ, 0 < C ∧ ∀ (R r M : ℝ), 0 < R → 0 < r →
      (5 / 16 * r ^ 2 * M ≤ 9 / 16 * r ^ 2 + 6 * Lam / lam * R * r) →
      M ≤ C * (1 + R / r) := by
    let K := 96 * Lam / (5 * lam)
    have hK : 0 < K := div_pos (mul_pos (by norm_num) (hlam.trans_le hLam)) (by positivity)
    refine ⟨9 / 5 + K, by linarith, ?_⟩
    intro R r M hR hr h
    have hb : M ≤ 9 / 5 + 96 * Lam / (5 * lam) * (R / r) := by
        have hp : 0 < 5 / 16 * r ^ 2 := by positivity
        have he : (5 / 16 * r ^ 2) * (9 / 5 + 96 * Lam / (5 * lam) * (R / r)) =
            9 / 16 * r ^ 2 + 6 * Lam / lam * R * r := by
          field_simp
          ring
        rw [← he] at h
        nlinarith only [h, hp]

      /- A uniform constant depending only on ellipticity controls the resulting count bound. -/
    change M ≤ 9 / 5 + K * (R / r) at hb
    have hp := div_pos hR hr
    nlinarith only [hb, hp, hK]
  refine ⟨C, hC, ?_⟩
  intro hH hLE A c J s T hT P hP
  apply visit_sum_mass_le_of_partial_mass_le
  intro N
  have hw : 0 < J.hi - J.lo := sub_pos.mpr J.ordered
  have hr := c.positive
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ univ) (by positivity)).mpr
  have _h_inl_14 : 5 / 16 * c.r ^ 2 * ((∑ n ∈ Finset.range N, visitEntrancePiece hH hLE hlam hLam A c J s T P n) univ).toReal ≤ 9 / 16 * c.r ^ 2 + 6 * Lam / lam * ((J.hi - J.lo) / 2) * c.r := by
    have h :
        let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P
            let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
            let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
            let B := visitBoundary s T (visitActiveInterval c) J
            5 * c.r ^ 2 / 16 * (∑ n ∈ Finset.range N, (mu n univ).toReal) ≤
              9 * c.r ^ 2 / 16 *
                (∑ n ∈ Finset.range N, (((E ∘ₘ mu n).restrict Bᶜ) univ).toReal) +
              2 * Lam * (∑ n ∈ Finset.range N, ((G ∘ₘ mu n) univ).toReal) := by
      have h := Finset.sum_le_sum (s := Finset.range N)
        (fun n _ => visitQuadratic_entrance_mass_bound hH hLE hlam hLam A c J s T P hP n)
      dsimp only at h ⊢
      simpa only [Finset.mul_sum, Finset.sum_add_distrib] using h
    have he := visitRetainedExit_partial_real_mass_le_one hH hLE hlam hLam A c J s T hT P hP N
    have hg : ∑ n ∈ Finset.range N,
        ((visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ
          visitEntrancePiece hH hLE hlam hLam A c J s T P n) univ).toReal ≤
            (J.hi - J.lo) / lam * (3 * c.r / 2) := by
      let gm := fun n => visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ
        visitEntrancePiece hH hLE hlam hLam A c J s T P n
      let U : Set Point := {p | p.velocity 0 ∈ c.active}
      have hU : MeasurableSet U :=
        isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
      have heq : ∀ n, gm n univ = gm n U := by
        intro n
        have hr := Measure.restrict_eq_self_of_ae_mem
          (visitActiveGreenMixture_ae_active hH hLE hlam hLam A c J s T
            (visitEntrancePiece hH hLE hlam hLam A c J s T P n))
        have hh := congrArg (fun m : Measure Point => m univ) hr
        change (gm n).restrict U univ = gm n univ at hh
        rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at hh
        exact hh.symm
      have hm := visitActiveGreen_partial_le hH hLE hlam hLam A c J s T hT P hP N U
      rw [visitOuterGreen_eq_strip hH hLE hlam hLam A J s T P hP] at hm
      have hc := strip_capacity hH hLE hlam hLam A J T
        ⟨P, WithTop.coe_lt_coe.mpr hP.2.1, hP.2.2⟩ (visitActiveInterval c)
      have hw : (visitActiveInterval c).hi - (visitActiveInterval c).lo = 3 * c.r / 2 := by
        dsimp only [visitActiveInterval]
        ring
      rw [hw] at hc
      have hnon : 0 ≤ (J.hi - J.lo) / lam * (3 * c.r / 2) := by
        exact mul_nonneg (div_nonneg (sub_pos.mpr J.ordered).le hlam.le)
          (div_nonneg (mul_nonneg (by norm_num) c.positive.le) (by norm_num))
      have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hm.trans hc)
      rw [ENNReal.toReal_ofReal hnon, visit_partial_real_mass _ N U hU] at hb
      convert hb using 1
      exact Finset.sum_congr rfl (fun n _ => congrArg ENNReal.toReal (heq n))
    dsimp only at h he hg
    have hh := h.trans (add_le_add
      (mul_le_mul_of_nonneg_left he (by positivity))
      (mul_le_mul_of_nonneg_left hg (by linarith)))
    rw [visit_partial_real_mass _ N univ MeasurableSet.univ]
    convert hh using 1 <;> ring
  exact hc ((J.hi - J.lo) / 2) c.r _ (by linarith [J.ordered]) c.positive
    _h_inl_14

/- The actual full entrance count is finite, without assuming its finiteness in the proof. -/
theorem visitCount_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) :
    IsFiniteMeasure (Measure.sum (visitEntrancePiece hH hLE hlam hLam A c J s T P)) := by
  obtain ⟨C, _, hc⟩ := exists_visitCount_mass_constant hlam hLam
  exact ⟨(hc hH hLE A c J s T hT P hP).trans_lt ENNReal.ofReal_lt_top⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
