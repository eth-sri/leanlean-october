module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassOuterBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationWaiting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Capacity

/-! # The capacity bound for the actual sum of active visit occupations -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (J : Interval) (s T : ℝ)

/-- Actual active Green mixtures are supported in the open active velocity interval. -/
theorem visitActiveGreenMixture_ae_active
    (mu : Measure Point) :
    ∀ᵐ q ∂(visitUnionGreenKernel hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu),
      q.velocity 0 ∈ c.active := by
  classical
  apply Measure.ae_comp_of_ae_ae
    (isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable)
  apply Filter.Eventually.of_forall
  intro p
  change ∀ᵐ q ∂(if hp : p ∈ visitPoleSet (visitActiveUnion c J) s T then
    finiteUnionGreen hlam hLam A (visitActiveUnion c J) T
      (visitPoleInclusion _ s T ⟨p, hp⟩) else 0), q.velocity 0 ∈ c.active
  split
  · rename_i hp
    exact (visitUnionGreen_ae_velocity hlam hLam A (visitActiveUnion c J) T
      (visitPoleInclusion _ s T ⟨p, hp⟩)).mono fun q hq =>
        ((visitActiveUnion_carrier c J).le hq).1
  · simp

/-- The partial sum of actual active Green masses has the source's velocity capacity bound. -/
theorem visitActiveGreen_partial_capacity (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    ∑ n ∈ Finset.range N,
      ((visitUnionGreenKernel hlam hLam A (visitActiveUnion c J) s T ∘ₘ
        visitEntrancePiece hlam hLam A c J s T P n) univ).toReal ≤
          (J.hi - J.lo) / lam * (3 * c.r / 2) := by
  let gm := fun n => visitUnionGreenKernel hlam hLam A (visitActiveUnion c J) s T ∘ₘ
    visitEntrancePiece hlam hLam A c J s T P n
  let U : Set Point := {p | p.velocity 0 ∈ c.active}
  have heq : ∀ n, gm n univ = gm n U := by
    intro n
    have hh := congrArg (fun m : Measure Point => m univ) (Measure.restrict_eq_self_of_ae_mem (visitActiveGreenMixture_ae_active hlam hLam A c J s T (visitEntrancePiece hlam hLam A c J s T P n)))
    change (gm n).restrict U univ = gm n univ at hh
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at hh
    exact hh.symm
  have hm := visitActiveGreen_partial_le hlam hLam A c J s T hT P hP N U
  rw [visitOuterGreen_eq_strip hlam hLam A J s T P hP] at hm
  have hc := strip_capacity hlam hLam A J T
    ⟨P, WithTop.coe_lt_coe.mpr hP.2.1, hP.2.2⟩ (visitActiveInterval c)
  have hw : (visitActiveInterval c).hi - (visitActiveInterval c).lo = 3 * c.r / 2 := by
    dsimp only [visitActiveInterval]
    ring
  rw [hw] at hc
  have hnon : 0 ≤ (J.hi - J.lo) / lam * (3 * c.r / 2) := mul_nonneg (div_nonneg (sub_pos.mpr J.ordered).le hlam.le)
      (div_nonneg (mul_nonneg (by norm_num) c.positive.le) (by norm_num))
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hm.trans hc)
  rw [ENNReal.toReal_ofReal hnon, visit_partial_real_mass _ N U (isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable)] at hb
  convert hb using 1
  exact Finset.sum_congr rfl (fun n _ => congrArg ENNReal.toReal (heq n))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
