module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AssemblyTheoremAutonomous
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AssemblyLocalisedAutonomous
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AssemblyAutonomousHolder
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnTime
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinCount
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionTerminalDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimedCoreDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartSlabBound
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCanonical
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinCountSlab
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinCountSupport
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassSupport
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VelocityReturn
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VelocityReturnAction
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlab
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinCountDecay
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationFiniteBounds
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionOccupation
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCapacity
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabArithmetic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabFullSpace
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabHorizon
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabIntegrated
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabOccupation
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabTerminal
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreen
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreenSupport
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitsStatement
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassSummation
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellCount
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellCountBounds
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartArithmetic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartDomination
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartFullSpace
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellsSlab
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartIntegrated
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartLower
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartPointBounds

/-! # Autonomous estimates relative to the Hörmander and Lieberman theorems

Composition discharges all four autonomous steps and preserves the statements' types.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov MeasureTheory Set Autonomous Holder
open scoped ENNReal

namespace Autonomous
open HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open ProbabilityTheory
open scoped Classical

/- The enlarged terminal measures satisfy the exact frontier domination statement. -/
theorem terminalDominationStatement_holds : TerminalDominationStatement := by
  intro hH hLE lam Lam hlam hLam A c J T P _hbar hT hJ _hvel N b hb hBT
  exact enlarged_active_terminal_le_fullspace hH hLE hlam hLam A c J
    P.time (P.time + T) P le_rfl (lt_add_of_pos_right P.time hT) hJ N b hb hBT

/- The exact time-bin count follows from exponent-six admissibility and return. -/
theorem timeBinCountStatement_holds : TimeBinCountStatement := by
  intro hH hLE lam Lam hlam hLam
  have hReturn := (return_time hH hLE lam Lam hlam hLam
      (smoothAutonomousP6_holds hH hLE lam Lam hlam hLam))
  obtain ⟨C, hC, hDecay⟩ : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (P : Point),
      |c.vbar| = 2 * c.r → P.velocity 0 ∈ closure c.entrance →
      ∀ (j : ℕ) (t : ℝ), (j : ℝ) * c.r ^ 2 ≤ t →
      S hH hLE hlam hLam A t (activeVelocityDatum c) (P.position 0, P.velocity 0) ≤
        C * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ) := by
      obtain ⟨C, hC, h⟩ : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (z : Z) (t : ℝ),
          |c.vbar| = 2 * c.r → |z.2| ≤ 3 * c.r → 0 ≤ t →
          S hH hLE hlam hLam A t (activeVelocityDatum c) z ≤
            C * (1 + t / c.r ^ 2) ^ (-(1 : ℝ) / 2) := by
        obtain ⟨C, hC, h⟩ := velocity_band_return_of_return_time hH hLE hlam hLam hReturn
        refine ⟨C, hC, ?_⟩
        intro A c z t hc hz ht
        rw [activeVelocityDatum_action_eq hH hLE hlam hLam A c t ht z]
        have hsub : {w : Z | w.2 ∈ c.active} ⊆ {w | |w.2| ≤ 3 * c.r} := by
          intro w hw
          have hh := (c.active_abs_bounds hw).2
          rw [hc] at hh
          change |w.2| ≤ 3 * c.r
          linarith only [hh]
        have hmass := (measure_mono (subset_univ {w : Z | |w.2| ≤ 3 * c.r})).trans
          (kernelXV_mass_le_one (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t) z)
        apply (ENNReal.toReal_mono (hmass.trans_lt ENNReal.one_lt_top).ne
          (measure_mono hsub)).trans
        simpa only [Real.coe_toNNReal t ht] using h A c.r z (Real.toNNReal t) c.positive hz
      refine ⟨C, hC, ?_⟩
      intro A c P hbar hv j t ht
      have hb := (c.active_abs_bounds (enlarged_closedEntrance_subset_active c hv)).2
      rw [hbar] at hb
      have hp : |P.velocity 0| ≤ 3 * c.r := by linarith only [hb, c.positive]
      have ht0 := (mul_nonneg (Nat.cast_nonneg j) (sq_nonneg c.r)).trans ht
      have _h_xinl_1 : 1 + (j : ℝ) ≤ 1 + t / c.r ^ 2 := by
        have h := (le_div_iff₀ (sq_pos_of_pos c.positive)).mpr ht
        linarith only [h]
      have _h_xinl_1 : (1 + t / c.r ^ 2) ^ (-1 / 2 : ℝ) ≤ (1 + (j : ℝ)) ^ (-1 / 2 : ℝ) := by
          exact (
        Real.rpow_le_rpow_of_nonpos (by positivity) _h_xinl_1
            (by norm_num)
        )
      exact (h A c (P.position 0, P.velocity 0) t hbar hp ht0).trans
        (mul_le_mul_of_nonneg_left _h_xinl_1 hC.le)

    /- A uniform probability bound on a bin gives radius-squared times that bound in occupation. -/
  let D := 2 * entranceSlabConstant Lam * C
  have hD : 0 < D := by
    dsimp only [D]
    exact mul_pos (mul_pos (by norm_num) (entranceSlabConstant_pos hlam hLam)) hC
  refine ⟨1 + D, by positivity, ?_⟩
  intro A c J T P hbar hJ hT hvel j
  let nu := visitsFromZero hH hLE hlam hLam A c J T P
  have : IsFiniteMeasure nu := enlargedVisitStarts_isFiniteMeasure
    hH hLE hlam hLam A c J (1 + T) T P (by linarith) hT
      (by nlinarith [sq_nonneg T]) hbar hJ hvel
  have hnu : ∀ᵐ p ∂nu, p.time < P.time + T :=
    (enlargedVisitStarts_ae_support hH hLE hlam hLam A c J P.time (P.time + T)
      P le_rfl (by linarith)).mono fun _ hp => hp.2.1
  have hslab (a b : ℝ) (hja : (j : ℝ) * c.r ^ 2 ≤ a) (hab : a ≤ b)
      (hbT : b ≤ T) (hlen : b - a ≤ c.r ^ 2) :
      (nu {p | p.time ∈ Ioc (P.time + a) (P.time + b)}).toReal ≤
        D * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ) := by
    let d := C * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ)
    let f := fun t => S hH hLE hlam hLam A t (activeVelocityDatum c)
      (P.position 0, P.velocity 0)
    have hd : 0 ≤ d := by dsimp only [d]; positivity
    have ha : 0 ≤ a := (by positivity : 0 ≤ (j : ℝ) * c.r ^ 2).trans hja
    have hp : f b ≤ d := hDecay A c P hbar hvel j b (hja.trans hab)
    have _h_xinl_0 : IntegrableOn (fun t => S hH hLE hlam hLam A t (activeVelocityDatum c) (P.position 0, P.velocity 0)) (Ioc a b) := by
      let z := (P.position 0, P.velocity 0)
      let E := fullSpaceEvolution hH hLE hlam hLam A
      let B : Set Z := {w | w.2 ∈ c.active}
      have hm : Measurable (fun t : ℝ => kernelXV E (Real.toNNReal t) z B) :=
        (physicalElapsedKernel E z).measurable_coe (isOpen_Ioo.measurableSet.preimage measurable_snd)
      have hi : IntegrableOn (fun t => (kernelXV E (Real.toNNReal t) z B).toReal)
          (Ioc a b) := by
        apply Integrable.mono' (integrable_const (1 : ℝ)) hm.ennreal_toReal.aestronglyMeasurable
        exact Filter.Eventually.of_forall fun t => by
          rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
          simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
            ((measure_mono (subset_univ B)).trans (kernelXV_mass_le_one E (Real.toNNReal t) z))
      apply hi.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (activeVelocityDatum_action_eq hH hLE hlam hLam A c t (ha.trans ht.1.le) z).symm
    have hg : (∫ t in Ioc a b, f t) ≤ c.r ^ 2 * d :=
      timeBinCount_integral_le hab hlen hd
        _h_xinl_0
        (fun t ht => hDecay A c P hbar hvel j t (hja.trans ht.1.le))
    have hn : c.r ^ (-2 : ℤ) * c.r ^ 2 = 1 := by
      norm_num only [zpow_neg, zpow_ofNat]
      exact inv_mul_cancel₀ (ne_of_gt (sq_pos_of_pos c.positive))
    have hb : entranceSlabConstant Lam *
        (f b + c.r ^ (-2 : ℤ) * ∫ t in Ioc a b, f t) ≤
          (2 * entranceSlabConstant Lam * C) * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ) := by
      calc
        _ ≤ entranceSlabConstant Lam * (d + c.r ^ (-2 : ℤ) * (c.r ^ 2 * d)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add hp (mul_le_mul_of_nonneg_left hg (by positivity)))
            (entranceSlabConstant_pos hlam hLam).le
        _ = _ := by rw [← mul_assoc, hn]; dsimp only [d]; ring
    have hv : P.velocity 0 ∈ J.carrier := hJ
      (subset_closure (enlarged_closedEntrance_subset_active c hvel))
    have hm : visitsFromZero hH hLE hlam hLam A c J T P
      {p | p.time ∈ Ioc (P.time + a) (P.time + b)} ≤
      ENNReal.ofReal (entranceSlabConstant Lam *
        (S hH hLE hlam hLam A b (activeVelocityDatum c) (P.position 0, P.velocity 0) +
          c.r ^ (-2 : ℤ) * ∫ t in Ioc a b,
            S hH hLE hlam hLam A t (activeVelocityDatum c) (P.position 0, P.velocity 0))) := by
      let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P
      let D : Set Point := {p | p.time ∈ Ioc (P.time + a) (P.time + b)}
      let mu := fun n => (gamma n).restrict D
      let f := fun t => S hH hLE hlam hLam A t (activeVelocityDatum c)
        (P.position 0, P.velocity 0)
      have hp : 0 ≤ f b := by
        dsimp only [f]
        rw [activeVelocityDatum_action_eq hH hLE hlam hLam A c b (ha.trans hab)]
        exact ENNReal.toReal_nonneg
      have hg : 0 ≤ ∫ t in Ioc a b, f t := by
        rw [← entranceSlab_fullSpaceOccupation_active_real hH hLE hlam hLam A c P T a b ha hbT]
        exact ENNReal.toReal_nonneg
      have hbound (N : ℕ) : (∑ n ∈ Finset.range N, mu n) univ ≤
          ENNReal.ofReal (entranceSlabConstant Lam *
            (f b + c.r ^ (-2 : ℤ) * ∫ t in Ioc a b, f t)) := by
        have hq := entranceSlabQuadratic_partial_mass_bound hH hLE hlam hLam A c J
          P.time (P.time + T) P le_rfl (by linarith) hJ (P.time + a) (P.time + b) N
        have ht : (∑ n ∈ Finset.range N,
          (((enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n).restrict
            {p | p.time ∈ Ioc (P.time + a) (P.time + b)}).bind
              (enlargedActiveTerminalFamily hH hLE hlam hLam A c J (P.time + b))
                {q | q.velocity 0 ∈ c.active}).toReal) ≤
          S hH hLE hlam hLam A b (activeVelocityDatum c) (P.position 0, P.velocity 0) := by
          have hb := (ha.trans hab)
          let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P
          let F := enlargedActiveTerminalFamily hH hLE hlam hLam A c J (P.time + b)
          let D : Set Point := {p | p.time ∈ Ioc (P.time + a) (P.time + b)}
          let B : Set Point := {q | q.velocity 0 ∈ c.active}
          let tm := fun n => ((gamma n).restrict D).bind F
          have hB : MeasurableSet B := isOpen_Ioo.measurableSet.preimage
            ((continuous_apply 0).comp continuous_velocity).measurable
          have hm : (∑ n ∈ Finset.range N, tm n) ≤
              enlargedFullSpaceTerminal hH hLE hlam hLam A P (P.time + b) := by
            calc
              _ ≤ ∑ n ∈ Finset.range N, (gamma n).bind F :=
                Finset.sum_le_sum fun n _ => entranceSlabTerminal_restrict_bind_le
                  hH hLE hlam hLam A c J (P.time + b) (gamma n) D
              _ ≤ _ := enlarged_active_terminal_le_fullspace hH hLE hlam hLam A c J
                P.time (P.time + T) P le_rfl (by linarith) hJ N (P.time + b)
                  (by linarith) (by linarith)
          have hr := ENNReal.toReal_mono
            (measure_ne_top (enlargedFullSpaceTerminal hH hLE hlam hLam A P (P.time + b)) B)
            (hm B)
          rw [visit_partial_real_mass tm N B hB] at hr
          have he : enlargedFullSpaceTerminal hH hLE hlam hLam A P (P.time + b)
              {q | q.velocity 0 ∈ c.active} =
              kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal b)
                (P.position 0, P.velocity 0) {z | z.2 ∈ c.active} := by
              have hB : MeasurableSet {q : Point | q.velocity 0 ∈ c.active} :=
                isOpen_Ioo.measurableSet.preimage
                  ((continuous_apply 0).comp continuous_velocity).measurable
              have he := Measure.map_apply
                (μ := kernelXV (fullSpaceEvolution hH hLE hlam hLam A)
                  (Real.toNNReal (P.time + b - P.time)) (P.position 0, P.velocity 0))
                (enlargedTerminalPoint_measurable (P.time + b)) hB
              have ht : P.time + b - P.time = b := by ring
              rw [ht] at he
              unfold enlargedFullSpaceTerminal
              rw [ht]
              exact he

            /- Physical time-slab occupation is exactly the elapsed active-band kernel integral. -/
          rw [he] at hr
          exact hr.trans_eq (activeVelocityDatum_action_eq hH hLE hlam hLam A c b hb
            (P.position 0, P.velocity 0)).symm
        have ho : (∑ n ∈ Finset.range N,
          ((enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) (P.time + b) ∘ₘ
            (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n).restrict
              {p | p.time ∈ Ioc (P.time + a) (P.time + b)}) univ).toReal) ≤
          ∫ t in Ioc a b,
            S hH hLE hlam hLam A t (activeVelocityDatum c) (P.position 0, P.velocity 0) := by
          let gm := fun n => enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J)
            (P.time + b) ∘ₘ
              (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n).restrict
                {p | p.time ∈ Ioc (P.time + a) (P.time + b)}
          have : ∀ n, IsFiniteMeasure (gm n) := fun n =>
            entranceSlabGreen_isFiniteMeasure hH hLE hlam hLam A c J (P.time + a) (P.time + b) _
              ((ae_restrict_mem (measurableSet_Ioc.preimage continuous_time.measurable)).mono
                fun _ hp => hp.1.le)
          have hm : (∑ n ∈ Finset.range N,
          enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) (P.time + b) ∘ₘ
            (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n).restrict
              {p | p.time ∈ Ioc (P.time + a) (P.time + b)}) ≤
          (enlargedFullSpaceOccupation hH hLE hlam hLam A P T).restrict
            {q | q.time ∈ Ioc (P.time + a) (P.time + b) ∧ q.velocity 0 ∈ c.active} := by
            let S : Set Point :=
              {q | q.time ∈ Ioc (P.time + a) (P.time + b) ∧ q.velocity 0 ∈ c.active}
            let gm := enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P
            have he : ∀ N : ℕ, (∑ n ∈ Finset.range N, (gm n).restrict S) =
                (∑ n ∈ Finset.range N, gm n).restrict S := by
              intro N
              induction N with
              | zero => simp only [Finset.range_zero, Finset.sum_empty, Measure.restrict_zero]
              | succ N ih => rw [Finset.sum_range_succ, Finset.sum_range_succ,
                  Measure.restrict_add, ih]
            have hle := Finset.sum_le_sum (s := Finset.range N) (fun n _ =>
              entranceSlab_greenMixture_le_restrict hH hLE hlam hLam A c J
                (P.time + a) (P.time + b) (P.time + T) (by linarith only [hbT]) hJ
                (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n))
            exact hle.trans ((he N).le.trans (Measure.restrict_mono (subset_refl S)
              (enlarged_active_occupation_le_fullspace hH hLE hlam hLam A c J T hT P hv N)))
          have hr := ENNReal.toReal_mono (measure_ne_top _ univ) (hm univ)
          rw [Measure.restrict_apply MeasurableSet.univ, univ_inter,
            entranceSlab_fullSpaceOccupation_active_real hH hLE hlam hLam A c P T a b ha hbT] at hr
          rw [visit_partial_real_mass gm N univ MeasurableSet.univ] at hr
          exact hr
        have hL := (hlam.trans_le hLam).le
        have hq' :=
          hq.trans (add_le_add (mul_le_mul_of_nonneg_left ht (by positivity))
            (mul_le_mul_of_nonneg_left ho (by positivity)))
        have hr := entranceSlab_mass_arithmetic c.positive hL hp hg hq'
        rw [← visit_partial_real_mass mu N univ MeasurableSet.univ] at hr
        exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ univ) (by
          exact mul_nonneg (entranceSlabConstant_pos hlam hLam).le
            (add_nonneg hp (mul_nonneg (by positivity) hg)))).mpr hr
      have hm := visit_sum_mass_le_of_partial_mass_le mu _ hbound
      have hD : MeasurableSet D := measurableSet_Ioc.preimage continuous_time.measurable
      have he : Measure.sum mu = (Measure.sum gamma).restrict D :=
        (Measure.restrict_sum gamma hD).symm
      rw [he, Measure.restrict_apply MeasurableSet.univ, univ_inter] at hm
      exact hm
    have hm' := hm.trans (ENNReal.ofReal_le_ofReal hb)
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm'
    have hCs := entranceSlabConstant_pos hlam hLam
    rw [ENNReal.toReal_ofReal (by positivity)] at hr
    exact hr
  by_cases hj : j = 0
  · subst j
    have hb := lt_min (sq_pos_of_pos c.positive) hT
    have hs := hslab 0 (min (c.r ^ 2) T) (by simp) hb.le (min_le_right _ _)
      (by linarith [min_le_left (c.r ^ 2) T])
    have hm : enlargedTimeVisitMass nu c P.time 0 ≤ (nu {p | p.time = P.time}).toReal +
      (nu {p | p.time ∈ Ioc P.time (P.time + min (c.r ^ 2) T)}).toReal := by
      let s := P.time
      let A : Set Point := {p | p.time = s}
      let B : Set Point := {p | p.time ∈ Ioc s (s + min (c.r ^ 2) T)}
      have hm : nu {p | p.time ∈ enlargedTimeBin c.r s 0 ∧
          p.velocity 0 ∈ closure c.entrance} ≤ nu A + nu B := by
        apply (measure_mono_ae ?_).trans (measure_union_le A B)
        filter_upwards [hnu] with p hp
        intro hcell
        have ht := hcell.1
        rw [enlargedTimeBin, ite_eq_left rfl] at ht
        rcases eq_or_lt_of_le ht.1 with he | hlt
        · exact Or.inl he.symm
        · right
          refine ⟨hlt, ?_⟩
          rw [add_min]
          exact le_min ht.2 hp.le
      have hr := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨measure_ne_top nu A, measure_ne_top nu B⟩) hm
      rw [ENNReal.toReal_add (measure_ne_top nu A) (measure_ne_top nu B)] at hr
      exact hr
    have he : visitsFromZero hH hLE hlam hLam A c J T P {p | p.time = P.time} = 1 := by
        have hS : MeasurableSet {p : Point | p.time = P.time} :=
          (isClosed_eq continuous_time continuous_const).measurableSet
        let gm := enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P
        change Measure.sum gm {p | p.time = P.time} = 1
        rw [Measure.sum_apply _ hS]
        have hz : ∀ n : ℕ, n ≠ 0 → gm n {p | p.time = P.time} = 0 := by
          intro n hn
          cases n with
          | zero => exact (hn rfl).elim
          | succ n =>
            let s := P.time
            let T := (P.time + T)
            have hS : MeasurableSet {p : Point | p.time = s} :=
              (isClosed_eq continuous_time continuous_const).measurableSet
            change (_ : Measure Point).restrict (visitBoundary s T (visitEntranceInterval c) J)
              {p | p.time = s} = 0
            rw [Measure.restrict_apply hS]
            have he : {p : Point | p.time = s} ∩ visitBoundary s T (visitEntranceInterval c) J =
                ∅ := by
              apply eq_empty_iff_forall_notMem.mpr
              intro p hp
              exact (ne_of_lt hp.2.1) hp.1.symm
            rw [he, measure_empty]
        rw [tsum_eq_single 0 hz]
        have he : gm 0 = Measure.dirac P := by
          change visitInitial P (visitEntranceInterval c)
            (visitBoundary P.time (P.time + T) (visitEntranceInterval c) J)
            (enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) (P.time + T)) = _
          unfold visitInitial
          exact ite_eq_left hvel
        rw [he, Measure.dirac_apply_of_mem (show P ∈ {p : Point | p.time = P.time} from rfl)]

      /- A later bin entirely beyond the observation horizon contains no starts. -/
    have hs' : (nu {p | p.time ∈ Ioc P.time (P.time + min (c.r ^ 2) T)}).toReal ≤ D := by
      simpa only [Nat.cast_zero, zero_add, add_zero, Real.one_rpow, mul_one] using hs
    have he' : (nu {p | p.time = P.time}).toReal = 1 := by
      exact congrArg ENNReal.toReal he
    simpa only [Nat.cast_zero, add_zero, Real.one_rpow, mul_one] using
      hm.trans (by rw [he']; linarith only [hs'])
  · by_cases hlate : T ≤ (j : ℝ) * c.r ^ 2
    · have _h_xinl_0 : enlargedTimeVisitMass (visitsFromZero hH hLE hlam hLam A c J T P) c P.time j = 0 := by
        have hTJ := hlate
        have hs := enlargedVisitStarts_ae_support hH hLE hlam hLam A c J P.time (P.time + T)
          P le_rfl (by linarith only [hT])
        have hz : visitsFromZero hH hLE hlam hLam A c J T P
            {p | p.time ∈ enlargedTimeBin c.r P.time j ∧
              p.velocity 0 ∈ closure c.entrance} = 0 := by
          apply measure_eq_zero_iff_ae_notMem.mpr
          filter_upwards [hs] with p hp
          intro hcell
          have ht := hcell.1
          rw [enlargedTimeBin, ite_eq_right hj] at ht
          have hlate : P.time + T < p.time := lt_of_le_of_lt
            (by linarith only [hTJ]) ht.1
          exact (not_lt_of_ge hlate.le) hp.2.1
        exact congrArg ENNReal.toReal hz
      rw [_h_xinl_0]
      positivity
    · have haT : (j : ℝ) * c.r ^ 2 < T := lt_of_not_ge hlate
      let a := (j : ℝ) * c.r ^ 2
      let b := min (((j : ℝ) + 1) * c.r ^ 2) T
      have hab : a ≤ b := le_min (by
        dsimp only [a]
        nlinarith [sq_pos_of_pos c.positive]) haT.le
      have hs := hslab a b le_rfl hab (min_le_right _ _)
        (by dsimp only [a, b]; nlinarith [min_le_left (((j : ℝ) + 1) * c.r ^ 2) T])
      have hm : enlargedTimeVisitMass nu c P.time j ≤
      (nu {p | p.time ∈ Ioc (P.time + (j : ℝ) * c.r ^ 2)
        (P.time + min (((j : ℝ) + 1) * c.r ^ 2) T)}).toReal := by
        let s := P.time
        apply ENNReal.toReal_mono (measure_ne_top nu _)
        apply measure_mono_ae
        filter_upwards [hnu] with p hp
        intro hcell
        have ht := hcell.1
        rw [enlargedTimeBin, ite_eq_right hj] at ht
        exact ⟨ht.1, by
          rw [add_min]
          exact le_min ht.2 hp.le⟩
      exact (hm.trans hs).trans (mul_le_mul_of_nonneg_right (by linarith)
        (by positivity))

/- All autonomous frontier steps hold relative to the source theorem. -/
theorem autonomousRemainingFrontier_holds : AutonomousRemainingFrontier := by
  have _h_xinl_1 : ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam), ∃ A0 Cs : ℝ, 0 < A0 ∧ 0 < Cs ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point), |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T → P.velocity 0 ∈ closure c.entrance → ∀ (a b : ℝ) (k : ℤ), 0 ≤ a → a < b → b - a ≤ c.r ^ 2 → b ≤ T → enlargedPositionSlabMass (visitsFromZero hH hLE hlam hLam A c J T P) c P.time 0 a b k ≤ Cs * ((kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal b) (P.position 0, P.velocity 0) (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3))).toReal + c.r ^ (-2 : ℤ) * ∫ t in Ioc a b, (kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t) (P.position 0, P.velocity 0) (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3))).toReal) := by
    intro hH hLE lam Lam hlam hLam
    obtain ⟨C, hC, hbound⟩ :
        ∃ C : ℝ, 0 < C ∧
            ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
              (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s x a b : ℝ) (k : ℤ)
              (mu : Measure Point) [IsFiniteMeasure mu],
              |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → a ≤ b →
              (∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.entrance) →
              let Y := x + ((k : ℝ) + 1 / 2) * c.r ^ 3
              5 * c.r ^ 2 / 16 * enlargedPositionSlabMass mu c s x a b k ≤
                9 * c.r ^ 2 / 16 *
                  ((positionStartTerminalKernel hH hLE hlam hLam A c J (s + b) ∘ₘ mu)
                    (positionStartBox c Y)).toReal +
                C * ((coreAllTimeGreenKernel hH hLE hlam hLam A c ∘ₘ mu)
                  ({q : Point | s + a < q.time ∧ q.time ≤ s + b} ∩ positionStartBox c Y)).toReal := by
      obtain ⟨C, hC, hbound⟩ := positionStartQuadratic_operator_bound hlam hLam
      refine ⟨C, hC, ?_⟩
      intro hH hLE A c J s x a b k mu _ hc hJ hab hmu
      dsimp only
      let Y := x + ((k : ℝ) + 1 / 2) * c.r ^ 3
      let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
        visitQuadratic c (q.velocity 0)
      let g := fun q : Point => forwardScalarOperator A.a f q
      let S := {q : Point | s + a < q.time ∧ q.time ≤ s + b}
      let W := positionStartBox c Y
      let B := positionStartTerminalKernel hH hLE hlam hLam A c J (s + b) ∘ₘ mu
      let D := positionStartTerminalKernel hH hLE hlam hLam A c J (s + a) ∘ₘ mu
      let G := coreAllTimeGreenKernel hH hLE hlam hLam A c ∘ₘ mu
      have hS : MeasurableSet S :=
        (isOpen_lt continuous_const continuous_time).measurableSet.inter
          (isClosed_le continuous_time continuous_const).measurableSet
      have hW : MeasurableSet W := measurableSet_positionStartBox c Y
      have hactive := hmu.mono fun _ hp => enlarged_closedEntrance_subset_active c hp
      have hfB := positionStartQuadratic_integrable c Y B
        (positionStartTerminalMixture_ae_closedActive hH hLE hlam hLam A c J (s + b) mu)
      have hgG : Integrable g G := positionStartQuadratic_operator_integrable
        hlam hLam A c Y hc G (positionStartAllTimeMixture_ae_active hH hLE hlam hLam A c mu)
      have hterm : (∫ q, f q ∂B) ≤ 9 * c.r ^ 2 / 16 * (B W).toReal := by
        have hh : (∫ q, f q ∂B) ≤ ∫ q, W.indicator (fun _ => 9 * c.r ^ 2 / 16) q ∂B := by
          apply integral_mono_ae hfB ((integrable_const _).indicator hW)
          filter_upwards [positionStartTerminalMixture_ae_closedActive
            hH hLE hlam hLam A c J (s + b) mu] with q hq
          have h := (positionStartQuadratic_box_bound c Y q hc hq).2
          change f q ≤ W.indicator (fun _ => 9 * c.r ^ 2 / 16) q
          by_cases hw : q ∈ W
          · rw [indicator_of_mem hw]
            simpa only [indicator_of_mem
              (show (q.position 0, q.velocity 0) ∈ box 4 c.r Y from hw), mul_one] using h
          · rw [indicator_of_notMem hw]
            simpa only [indicator_of_notMem
              (show (q.position 0, q.velocity 0) ∉ box 4 c.r Y from hw), mul_zero] using h
        rw [integral_indicator hW, integral_const] at hh
        simpa only [smul_eq_mul, Measure.real,
          Measure.restrict_apply MeasurableSet.univ, univ_inter, mul_comm] using hh
      have hop : -(∫ q in S, g q ∂G) ≤ C * (G (S ∩ W)).toReal := by
        have hh : (∫ q in S, -g q ∂G) ≤ ∫ q in S, W.indicator (fun _ => C) q ∂G := by
          apply integral_mono_ae hgG.neg.restrict (((integrable_const C).indicator hW).restrict)
          have ha : ∀ᵐ q ∂G.restrict S, q.velocity 0 ∈ c.active :=
            (positionStartAllTimeMixture_ae_active hH hLE hlam hLam A c mu).filter_mono
              (ae_mono Measure.restrict_le_self)
          filter_upwards [ha] with q hq
          change -g q ≤ W.indicator (fun _ => C) q
          have hb := (neg_le_abs (g q)).trans (hbound A c Y q hc hq)
          by_cases hw : q ∈ W
          · rw [indicator_of_mem hw]
            simpa only [indicator_of_mem
              (show (q.position 0, q.velocity 0) ∈ box 4 c.r Y from hw), mul_one] using hb
          · rw [indicator_of_notMem hw]
            simpa only [indicator_of_notMem
              (show (q.position 0, q.velocity 0) ∉ box 4 c.r Y from hw), mul_zero] using hb
        rw [integral_neg, integral_indicator hW, integral_const] at hh
        simpa only [smul_eq_mul, Measure.real,
          Measure.restrict_apply MeasurableSet.univ, univ_inter,
          Measure.restrict_apply hW, inter_comm, mul_comm] using hh
      have hi := positionStartQuadratic_integrated_slab_identity
        hH hLE hlam hLam A c J Y (s + a) (s + b) hc hJ mu hactive (by linarith only [hab])
      have hlo : 5 * c.r ^ 2 / 16 * enlargedPositionSlabMass mu c s x a b k ≤
          ∫ p in {q : Point | s + a < q.time ∧ q.time ≤ s + b},
            positionStartCutoff (x + ((k : ℝ) + 1 / 2) * c.r ^ 3) c.r c.positive
              (p.position 0) * visitQuadratic c (p.velocity 0) ∂mu := by
        let Y := x + ((k : ℝ) + 1 / 2) * c.r ^ 3
        let f := fun p : Point => positionStartCutoff Y c.r c.positive (p.position 0) *
          visitQuadratic c (p.velocity 0)
        let S := {q : Point | s + a < q.time ∧ q.time ≤ s + b}
        let B := {p : Point | s + a < p.time ∧ p.time ≤ s + b ∧
          p.position 0 ∈ enlargedPositionCell c.r x k ∧
            p.velocity 0 ∈ closure c.entrance}
        have hS : MeasurableSet S :=
          (isOpen_lt continuous_const continuous_time).measurableSet.inter
            (isClosed_le continuous_time continuous_const).measurableSet
        have hB : MeasurableSet B :=
          (isOpen_lt continuous_const continuous_time).measurableSet.inter
            ((isClosed_le continuous_time continuous_const).measurableSet.inter
              (((measurableSet_enlargedPositionCell c.r x k).preimage
                ((continuous_apply 0).comp continuous_position).measurable).inter
                  (isClosed_closure.measurableSet.preimage
                    ((continuous_apply 0).comp continuous_velocity).measurable)))
        have hf : Integrable f mu := positionStartQuadratic_integrable c Y mu
          (hmu.mono fun _ hp => subset_closure (enlarged_closedEntrance_subset_active c hp))
        have hm : (∫ p, B.indicator (fun _ => 5 * c.r ^ 2 / 16) p ∂mu) ≤
            ∫ p, S.indicator f p ∂mu := by
          apply integral_mono_ae ((integrable_const _).indicator hB) (hf.indicator hS)
          filter_upwards [hmu] with p hv
          by_cases hp : p ∈ B
          · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ S from ⟨hp.1, hp.2.1⟩)]
            exact positionStartQuadratic_start_lower c x k p hp.2.2.1 hp.2.2.2
          · rw [indicator_of_notMem hp]
            by_cases hs : p ∈ S
            · rw [indicator_of_mem hs]
              exact mul_nonneg ((positionStartCutoff_properties Y c.r c.positive).2 _).1
                (visitQuadratic_nonneg c
                  (subset_closure (enlarged_closedEntrance_subset_active c hv)))
            · rw [indicator_of_notMem hs]
        rw [integral_indicator hB, integral_const, integral_indicator hS] at hm
        change 5 * c.r ^ 2 / 16 * (mu B).toReal ≤ ∫ p in S, f p ∂mu
        simpa only [smul_eq_mul, mul_comm, Measure.real,
          Measure.restrict_apply MeasurableSet.univ, univ_inter] using hm
      have hn : 0 ≤ ∫ q, positionStartCutoff Y c.r c.positive (q.position 0) *
          visitQuadratic c (q.velocity 0)
          ∂(positionStartTerminalKernel hH hLE hlam hLam A c J (s + a) ∘ₘ mu) := by
        let b := (s + a)
        apply integral_nonneg_of_ae
        exact (positionStartTerminalMixture_ae_closedActive hH hLE hlam hLam A c J b mu).mono
          fun q hq => mul_nonneg ((positionStartCutoff_properties Y c.r c.positive).2 _).1
            (visitQuadratic_nonneg c hq)
      change (∫ q in S, f q ∂mu) = (∫ q, f q ∂B) - (∫ q, f q ∂D) -
        ∫ q in S, g q ∂G at hi
      change 5 * c.r ^ 2 / 16 * enlargedPositionSlabMass mu c s x a b k ≤
        (∫ q in S, f q ∂mu) at hlo
      change 0 ≤ ∫ q, f q ∂D at hn
      change 5 * c.r ^ 2 / 16 * enlargedPositionSlabMass mu c s x a b k ≤
        9 * c.r ^ 2 / 16 * (B W).toReal + C * (G (S ∩ W)).toReal
      linarith only [hlo, hi, hn, hterm, hop]
    refine ⟨4, 9 / 5 + 16 * C / 5, by norm_num, by positivity, ?_⟩
    intro A c J T P hc hJ hT hv a b k ha hab _hlen hb
    let mu := visitsFromZero hH hLE hlam hLam A c J T P
    have : IsFiniteMeasure mu :=
      visitsFromZero_isFiniteMeasure hH hLE hlam hLam A c J T P hc hJ hT hv
    let Y := ((k : ℝ) + 1 / 2) * c.r ^ 3
    let S := {q : Point | P.time + a < q.time ∧ q.time ≤ P.time + b}
    let W := positionStartBox c Y
    let B := positionStartTerminalKernel hH hLE hlam hLam A c J (P.time + b) ∘ₘ mu
    let G := coreAllTimeGreenKernel hH hLE hlam hLam A c ∘ₘ mu
    let E := fullSpaceEvolution hH hLE hlam hLam A
    let F := (kernelXV E (Real.toNNReal b) (P.position 0, P.velocity 0) (box 4 c.r Y)).toReal
    let I := ∫ t in Ioc a b,
      (kernelXV E (Real.toNNReal t) (P.position 0, P.velocity 0) (box 4 c.r Y)).toReal
    have hI : 0 ≤ I := setIntegral_nonneg measurableSet_Ioc fun _ _ => ENNReal.toReal_nonneg
    have hs := enlargedVisitStarts_ae_support hH hLE hlam hLam A c J P.time (P.time + T)
      P le_rfl (by linarith only [hT])
    have hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.entrance := hs.mono fun _ hp => hp.2.2
    have hB : B ≤ enlargedFullSpaceTerminal hH hLE hlam hLam A P (P.time + b) := by
      change (Measure.sum
        (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P)).bind
          (positionStartTerminalKernel hH hLE hlam hLam A c J (P.time + b)) ≤ _
      rw [Measure.bind_sum _ _ (Kernel.aemeasurable _)]
      apply positionStart_sum_le_of_partial_le
      intro N
      exact terminalDominationStatement_holds hH hLE lam Lam hlam hLam A c J T P hc hT hJ hv N (P.time + b)
        (by linarith only [ha, hab]) (by linarith only [hb])
    have hBF : (B W).toReal ≤ F := by
      have _h_xinl_1 : enlargedFullSpaceTerminal hH hLE hlam hLam A P (P.time + b) (positionStartBox c Y) = kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal b) (P.position 0, P.velocity 0) (box 4 c.r Y) := by
        unfold enlargedFullSpaceTerminal
        rw [Measure.map_apply (enlargedTerminalPoint_measurable _)
          (measurableSet_positionStartBox c Y), add_sub_cancel_left]
        rfl
      have hm := (hB W).trans_eq
        _h_xinl_1
      exact ENNReal.toReal_mono
        ((measure_mono (subset_univ _)).trans_lt
          ((kernelXV_mass_le_one E (Real.toNNReal b) (P.position 0, P.velocity 0)).trans_lt
            ENNReal.one_lt_top)).ne hm
    have hW := measurableSet_positionStartBox c Y
    have he := positionStartGreenMixture_slab_eq_finite hH hLE hlam hLam A c J
      (P.time + a) (P.time + b) (P.time + T) hJ mu
        (hs.mono fun _ hp => ⟨enlarged_closedEntrance_subset_active c hp.2.2, hp.2.1⟩)
          (by linarith only [hb])
    have hGE : G (S ∩ W) ≤ ENNReal.ofReal I := by
      have hh := congrArg (fun rho : Measure Point => rho W) he
      rw [Measure.restrict_apply hW, Measure.restrict_apply hW, inter_comm W] at hh
      change G (S ∩ W) = _ at hh
      rw [hh]
      apply (positionStart_all_occupation_le_fullspace hH hLE hlam hLam A c J T P hT
        (hJ (subset_closure (enlarged_closedEntrance_subset_active c hv))) (S ∩ W)).trans_eq
      have _h_xinl_0 : enlargedFullSpaceOccupation hH hLE hlam hLam A P T
        ({q : Point | P.time + a < q.time ∧ q.time ≤ P.time + b} ∩ positionStartBox c Y) =
        ∫⁻ t in Ioc a b, kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
          (P.position 0, P.velocity 0) (box 4 c.r Y) := by
          let S := {q : Point | P.time + a < q.time ∧ q.time ≤ P.time + b}
          let W := positionStartBox c Y
          have hS : MeasurableSet S :=
            (isOpen_lt continuous_const continuous_time).measurableSet.inter
              (isClosed_le continuous_time continuous_const).measurableSet
          have hW := measurableSet_positionStartBox c Y
          let F : Point → ℝ≥0∞ := (S ∩ W).indicator 1
          have hF : Measurable F := measurable_one.indicator (hS.inter hW)
          rw [← lintegral_indicator_one (hS.inter hW)]
          change (∫⁻ p, F p ∂enlargedFullSpaceOccupation hH hLE hlam hLam A P T) = _
          rw [enlargedFullSpaceOccupation_lintegral hH hLE hlam hLam A P T F hF]
          have he (t : ℝ) : (∫⁻ z, F (enlargedTerminalPoint (P.time + t) z)
              ∂kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
                (P.position 0, P.velocity 0)) =
              (Ioc a b).indicator (fun u => kernelXV (fullSpaceEvolution hH hLE hlam hLam A)
                (Real.toNNReal u) (P.position 0, P.velocity 0) (box 4 c.r Y)) t := by
            by_cases ht : t ∈ Ioc a b
            · rw [indicator_of_mem ht, ← lintegral_indicator_one (box_measurable 4 c.r Y)]
              apply lintegral_congr
              intro z
              have heq : enlargedTerminalPoint (P.time + t) z ∈ S ∩ W ↔ z ∈ box 4 c.r Y := by
                change ((P.time + a < P.time + t ∧ P.time + t ≤ P.time + b) ∧
                  z ∈ box 4 c.r Y) ↔ z ∈ box 4 c.r Y
                have hs : P.time + a < P.time + t ∧ P.time + t ≤ P.time + b := by
                  constructor <;> linarith only [ht.1, ht.2]
                exact and_iff_right hs
              simp only [F, Set.indicator, heq, Pi.one_apply]
            · rw [indicator_of_notMem ht]
              have hz : (fun z : Z => F (enlargedTerminalPoint (P.time + t) z)) =
                  fun _ => (0 : ℝ≥0∞) := by
                funext z
                have hn : enlargedTerminalPoint (P.time + t) z ∉ S ∩ W := by
                  intro hz
                  apply ht
                  have hs : P.time + a < P.time + t ∧ P.time + t ≤ P.time + b := hz.1
                  constructor <;> linarith only [hs.1, hs.2]
                exact indicator_of_notMem hn _
              rw [hz, lintegral_zero]
          simp_rw [he]
          rw [lintegral_indicator measurableSet_Ioc,
            Measure.restrict_restrict measurableSet_Ioc]
          have hs : Ioc a b ∩ Ioc 0 T = Ioc a b :=
            inter_eq_left.mpr (fun _ ht => ⟨ha.trans_lt ht.1, ht.2.trans hb⟩)
          rw [hs]


      exact _h_xinl_0.trans
          (positionStartBox_slab_ofReal_integral E (P.position 0, P.velocity 0) c.r Y a b).symm
    have hGI := ENNReal.toReal_mono ENNReal.ofReal_ne_top hGE
    rw [ENNReal.toReal_ofReal hI] at hGI
    have hn := hbound hH hLE A c J P.time 0 a b k mu hc hJ hab.le hmu
    simp only [zero_add] at hn
    have hfinal := hn.trans (add_le_add
      (mul_le_mul_of_nonneg_left hBF (by positivity))
      (mul_le_mul_of_nonneg_left hGI hC.le))
    exact positionStart_slab_arithmetic c.r C _ F I c.positive hC.le
      ENNReal.toReal_nonneg hI hfinal
  exact ⟨timeBinCountStatement_holds,
    _h_xinl_1,
    terminalDominationStatement_holds, coreDominationStatement_holds⟩

end Autonomous

end HypoellipticAleksandrov.KineticAleksandrov
