module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalKernel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalHalfMass
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Elapsed
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Probability.Kernel.Composition.Comp
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenBorel
import Mathlib.MeasureTheory.Measure.Prod
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.MixtureDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripTimeMarginal
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FarVelocityDensityDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.RestartTailStatement

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov SectionTwo ProbabilityTheory
open scoped ENNReal


/-- A geometric bound at half-mass times gives the source exponential estimate at every time. -/
theorem stripSurvivingMass_exp_of_half_mass {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (D : ℝ) (hD : 0 < D)
    (hhalf : ∀ s z, stripSurvivingMass H E s (s + D)
      (le_add_of_nonneg_right hD.le) z ≤ 1 / 2)
    (s t : ℝ) (ht : 0 ≤ t)
    (z : EvolutionState (intervalDomain H) (fun _ => 0) s) :
    stripSurvivingMass H E s (s + t) (le_add_of_nonneg_right ht) z ≤
      2 * Real.exp (-Real.log 2 * t / D)  := by
  have stripSurvivingMass_geometric_of_half_mass (n : ℕ) :
      stripSurvivingMass H E s (s + n * D)
      (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hD.le)) z ≤
        (1 / 2 : ℝ) ^ n := by
    induction n with
    | zero =>
      simpa using
        (stripSurvivingMass_bounds A H E hE s s le_rfl z).2
    | succ n ih =>
      have hst : s ≤ s + n * D :=
        le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hD.le)
      have htu : s + n * D ≤ s + (n + 1 : ℕ) * D := by
        rw [Nat.cast_add, Nat.cast_one, add_mul]
        linarith
      have ht : s + (n + 1 : ℕ) * D = (s + n * D) + D := by
        push_cast
        ring
      have hh : ∀ w, E.1 (s + n * D) (s + (n + 1 : ℕ) * D) htu 1 w ≤ 1 / 2 := by
        intro w
        have hs := hhalf (s + n * D) w
        change E.1 (s + n * D) ((s + n * D) + D) _ 1 w ≤ 1 / 2 at hs
        have heq : E.1 (s + n * D) (s + (n + 1 : ℕ) * D) htu 1 w =
            E.1 (s + n * D) ((s + n * D) + D) (le_add_of_nonneg_right hD.le) 1 w := by
          exact congrArg (fun u =>
            E.1 (s + n * D) u.1 u.2 1 w)
            (show (⟨s + (n + 1 : ℕ) * D, htu⟩ : {u : ℝ // s + n * D ≤ u}) =
              ⟨(s + n * D) + D, le_add_of_nonneg_right hD.le⟩ from Subtype.ext ht)
        rw [heq]
        exact hs
      have hm := stripSurvivingMass_le_mul_of_later_bound A H E hE s
        (s + n * D) (s + (n + 1 : ℕ) * D) (1 / 2) hst htu hh z
      exact hm.trans (by simpa only [pow_succ, mul_comm] using
        mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1 / 2))
  let n := Nat.floor (t / D)
  have hn' := Nat.lt_floor_add_one (t / D)
  have htime : s + n * D ≤ s + t := by
    exact add_le_add_right ((le_div_iff₀ hD).mp (Nat.floor_le (div_nonneg ht hD.le))) s
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : (1 / 2 : ℝ) ^ n = Real.exp (-Real.log 2 * n) := by
    rw [mul_comm (-Real.log 2) (n : ℝ), Real.exp_nat_mul,
      Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp
  have hx : -Real.log 2 * (n : ℝ) ≤ Real.log 2 + (-Real.log 2 * t / D) := by
    have hh := mul_le_mul_of_nonneg_left hn'.le hlog.le
    have heq : Real.log 2 * (t / D) = Real.log 2 * t / D := by ring
    rw [heq] at hh
    rw [mul_add, mul_one] at hh
    rw [neg_mul, neg_mul, neg_div]
    linarith only [hh]
  calc
    _ ≤ (1 / 2 : ℝ) ^ n := (stripSurvivingMass_antitone A H E hE s (s + n * D) (s + t) (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hD.le)) htime z).trans (stripSurvivingMass_geometric_of_half_mass n)
    _ = Real.exp (-Real.log 2 * n) := he
    _ ≤ Real.exp (Real.log 2 + (-Real.log 2 * t / D)) := Real.exp_le_exp.mpr hx
    _ = 2 * Real.exp (-Real.log 2 * t / D) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]


/-- The literal remaining killed mass from an interior active pole at nonnegative elapsed time. -/
def activeSurvivingMass
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t) : ℝ :=
  stripSurvivingMass c.activeInterval (stripEvolution hH hLE hlam hLam A c.activeInterval)
    e.time (e.time + t) (le_add_of_nonneg_right ht)
    (stripPoleState c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩)



/-- Put a native terminal state on its physical absolute-time slice. -/
def activeRestartPoint (H : Interval) (s : ℝ)
    (w : EvolutionState (intervalDomain H) (fun _ => 0) s) : Point :=
  ⟨s, w.1.2, w.1.1⟩

/-- Restoring physical coordinates on a fixed time slice is measurable. -/
theorem measurable_activeRestartPoint (H : Interval) (s : ℝ) :
    Measurable (activeRestartPoint H s) := by
  exact (KineticPoint.measurable_equivProd_symm 1).comp
    (measurable_const.prodMk
      ((measurable_snd.comp measurable_subtype_coe).prodMk
        (measurable_fst.comp measurable_subtype_coe)))

/-- The surviving terminal measure, restored to the source's physical spacetime coordinates. -/
def activeRestartMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t) : Measure Point :=
  ((stripEvolution hH hLE hlam hLam A c.activeInterval).2.fiberKernel
    (intervalDomain_measurable c.activeInterval) e.time (e.time + t)
    (le_add_of_nonneg_right ht)
    (stripPoleState c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩)).map
      (activeRestartPoint c.activeInterval (e.time + t))

/-- The mass of the remaining terminal measure is exactly the surviving killed mass. -/
theorem activeRestartMeasure_mass
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t) :
    activeRestartMeasure hH hLE hlam hLam A c e he t ht univ =
      ENNReal.ofReal (activeSurvivingMass hH hLE hlam hLam A c e he t ht) := by
  let E := stripEvolution hH hLE hlam hLam A c.activeInterval
  let z := stripPoleState c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩
  change (Measure.map (activeRestartPoint c.activeInterval (e.time + t))
    (E.2.fiberKernel (intervalDomain_measurable c.activeInterval)
      e.time (e.time + t) (le_add_of_nonneg_right ht) z)) univ =
    ENNReal.ofReal (stripSurvivingMass c.activeInterval E
      e.time (e.time + t) (le_add_of_nonneg_right ht) z)
  rw [Measure.map_apply (measurable_activeRestartPoint _ _) MeasurableSet.univ,
    preimage_univ, (stripSurvivingMass_eq_kernel_mass A c.activeInterval E (stripEvolution_spec hH hLE hlam hLam A c.activeInterval) e.time (e.time + t) (le_add_of_nonneg_right ht) z)]
  exact (ENNReal.ofReal_toReal
    ((E.2.fiberKernel_mass_le_one (intervalDomain_measurable c.activeInterval)
      e.time (e.time + t) (le_add_of_nonneg_right ht) z).trans_lt
        ENNReal.one_lt_top).ne).symm



/-- Shift a positive elapsed time by a nonnegative restart delay. -/
def tailElapsedShift (t : ℝ) (ht : 0 ≤ t) (tau : ElapsedTime ⊤) : ElapsedTime ⊤ :=
  ⟨t + tau.1, add_pos_of_nonneg_of_pos ht tau.2.1, ENNReal.ofReal_lt_top⟩




/-- Restore a native state as a valid infinite-horizon pole. -/
def tailRestartPole (H : Interval) (r : ℝ)
    (a : EvolutionState (intervalDomain H) (fun _ => 0) r) : StripPole H ⊤ :=
  ⟨activeRestartPoint H r a, WithTop.coe_lt_top _, by
    have ha := PDE.mem_translateSet_iff_sub_mem.mp a.2.1
    simpa only [activeRestartPoint, sub_zero, intervalDomain,
      PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate, Interval.carrier] using ha⟩


/-- Native terminal states recover their unchanged coordinates as physical poles. -/
theorem tailRestartPole_state (H : Interval) (r : ℝ)
    (a : EvolutionState (intervalDomain H) (fun _ => 0) r) :
    stripPoleState H ⊤ (tailRestartPole H r a) = a := by
  apply Subtype.ext
  rfl

/-- The restarted master query is jointly measurable in elapsed time and state. -/
def tailRestartQuery (H : Interval) (r : ℝ)
    (q : ElapsedTime ⊤ × EvolutionState (intervalDomain H) (fun _ => 0) r) :
    EvolutionQuery (intervalDomain H) (fun _ => 0) :=
  ⟨(r, r + q.1.1, q.2.1), le_add_of_nonneg_right q.1.2.1.le, q.2.2⟩






/-- Including the restart-time endpoint does not change the Green restart identity. -/
theorem active_tail_restart_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t) :
    (stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he)).restrict
      {p | e.time + t ≤ p.time} =
        enlargedActiveGreen hH hLE hlam hLam A c
          (activeRestartMeasure hH hLE hlam hLam A c e he t ht)    := by
  have measurable_tailElapsedShift : Measurable (tailElapsedShift t ht) :=
    (measurable_const.add measurable_subtype_coe).subtype_mk
  have active_green_time_slice_null (s : ℝ) :
      stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he)
      {p | p.time = s} = 0 := by
    have hh := stripGreen_timeMarginal hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c e he) {s} (measurableSet_singleton s)
    simpa using hh
  have active_tail_restart_identity_strict :
      (stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he)).restrict
      {p | e.time + t < p.time} =
        enlargedActiveGreen hH hLE hlam hLam A c
          (activeRestartMeasure hH hLE hlam hLam A c e he t ht) := by
    have tailRestart_green_identity (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E) (e : StripPole H ⊤) :
        (stripGreenOfKernel H E.2 ⊤ e).restrict {p | e.1.time + t < p.time} =
        (E.2.fiberKernel (intervalDomain_measurable H) e.1.time (e.1.time + t)
          (le_add_of_nonneg_right ht) (stripPoleState H ⊤ e)).bind
            (fun a => stripGreenOfKernel H E.2 ⊤ (tailRestartPole H (e.1.time + t) a)) := by
      have tailGreen_integrand_measurable (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (s : ℝ) (z : EvolutionState (intervalDomain H) (fun _ => 0) s) (F : Point → ℝ≥0∞) (hF : Measurable F) :
          Measurable (fun tau : ElapsedTime ⊤ => ∫⁻ w,
          F (elapsedPhysicalPoint s (tau, w)) ∂K.master (elapsedQuery s z tau)) := by
        let k := elapsedKernel K s ⊤
        have : IsFiniteKernel k := by dsimp [k, elapsedKernel]; infer_instance
        have hm : Measurable (fun q :
            (EvolutionState (intervalDomain H) (fun _ => 0) s × ElapsedTime ⊤) ×
              EvolutionAmbientState 1 => F (elapsedPhysicalPoint s (q.1.2, q.2))) :=
          hF.comp ((measurable_elapsedPhysicalPoint s ⊤).comp
            (measurable_fst.snd.prodMk measurable_snd))
        exact (hm.lintegral_kernel_prod_right' (κ := k)).comp
          (measurable_const.prodMk measurable_id)
      have tailRestart_action_swap (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (r : ℝ) (nu : Measure (EvolutionState (intervalDomain H) (fun _ => 0) r)) [IsFiniteMeasure nu] (F : Point → ℝ≥0∞) (hF : Measurable F) :
          (∫⁻ tau, ∫⁻ a, ∫⁻ w, F ⟨r + tau.1, w.2, w.1⟩
          ∂K.master (tailRestartQuery H r (tau, a)) ∂nu ∂elapsedVolume ⊤) =
          ∫⁻ a, ∫⁻ p, F p ∂stripGreenOfKernel H K ⊤ (tailRestartPole H r a) ∂nu := by
        have measurable_tailRestartQuery :
            Measurable (tailRestartQuery H r) := by
          apply Measurable.subtype_mk
          exact measurable_const.prodMk
            ((measurable_const.add (measurable_subtype_coe.comp measurable_fst)).prodMk
              (measurable_subtype_coe.comp measurable_snd))
        let k := K.master.comap (tailRestartQuery H r) (measurable_tailRestartQuery)
        have : IsFiniteKernel k := by dsimp [k]; infer_instance
        have hm : Measurable (fun q :
            (ElapsedTime ⊤ × EvolutionState (intervalDomain H) (fun _ => 0) r) ×
              EvolutionAmbientState 1 => F ⟨r + q.1.1.1, q.2.2, q.2.1⟩) :=
          hF.comp ((KineticPoint.measurable_equivProd_symm 1).comp
            ((measurable_const.add
              (measurable_subtype_coe.comp measurable_fst.fst)).prodMk
              (measurable_snd.snd.prodMk measurable_snd.fst)))
        have hi := hm.lintegral_kernel_prod_right' (κ := k)
        rw [lintegral_lintegral_swap hi.aemeasurable]
        apply lintegral_congr
        intro a
        rw [stripGreenOfKernel_spec H K ⊤ (tailRestartPole H r a) F hF,
          tailRestartPole_state]
        rfl
      have measurable_tailRestartPole (r : ℝ) : Measurable (tailRestartPole H r) :=
        (measurable_activeRestartPoint H r).subtype_mk
      have tailRestart_master_lintegral (s : ℝ) (r : ℝ) (u : ℝ) (hsr : s ≤ r) (hru : r ≤ u) (z : EvolutionState (intervalDomain H) (fun _ => 0) s) (F : Point → ℝ≥0∞) (hF : Measurable F) :
          (∫⁻ w, F ⟨u, w.2, w.1⟩ ∂E.2.master ⟨(s, u, z.1), hsr.trans hru, z.2⟩) =
          ∫⁻ a, ∫⁻ w, F ⟨u, w.2, w.1⟩
            ∂E.2.master ⟨(r, u, a.1), hru, a.2⟩
            ∂E.2.fiberKernel (intervalDomain_measurable H) s r hsr z := by
        have hG : Measurable (fun w : EvolutionAmbientState 1 => F ⟨u, w.2, w.1⟩) :=
          hF.comp ((KineticPoint.measurable_equivProd_symm 1).comp
            (measurable_const.prodMk (measurable_snd.prodMk measurable_fst)))
        change (∫⁻ w, F ⟨u, w.2, w.1⟩ ∂E.2.master
          (evolutionQueryOfState (intervalDomain H) (fun _ => 0) s u (hsr.trans hru) z)) = _
        rw [← (E.2.map_fiberKernel_eq_master (intervalDomain_measurable H) s u (hsr.trans hru) z), lintegral_map hG measurable_subtype_coe,
          hE.2.2.2 s r u hsr hru]
        refine (Kernel.lintegral_comp _ _ z
          (g := fun a : EvolutionState (intervalDomain H) (fun _ => 0) u =>
            F ⟨u, a.1.2, a.1.1⟩)
          (hG.comp measurable_subtype_coe)).trans ?_
        apply lintegral_congr
        intro a
        have hm := E.2.map_fiberKernel_eq_master (intervalDomain_measurable H) r u hru a
        change _ = (∫⁻ w, F ⟨u, w.2, w.1⟩ ∂E.2.master
          (evolutionQueryOfState (intervalDomain H) (fun _ => 0) r u hru a))
        rw [← hm, lintegral_map hG measurable_subtype_coe]
      have tailElapsedShift_map :
          (elapsedVolume ⊤).map (tailElapsedShift t ht) =
          (elapsedVolume ⊤).restrict {tau | t < tau.1} := by
        ext B hB
        have hm : MeasurableSet {tau : ElapsedTime ⊤ | t < tau.1} :=
          measurable_subtype_coe measurableSet_Ioi
        rw [Measure.map_apply (measurable_tailElapsedShift) hB,
          elapsedVolume_apply _ _ ((measurable_tailElapsedShift) hB),
          Measure.restrict_apply hB, elapsedVolume_apply _ _ (hB.inter hm)]
        have he : (Subtype.val : ElapsedTime ⊤ → ℝ) '' (B ∩ {tau | t < tau.1}) =
            (fun x => t + x) ''
              ((Subtype.val : ElapsedTime ⊤ → ℝ) '' ((tailElapsedShift t ht) ⁻¹' B)) := by
          ext x
          constructor
          · rintro ⟨tau, ⟨hBtau, httau⟩, rfl⟩
            let a : ElapsedTime ⊤ := ⟨tau.1 - t, sub_pos.mpr httau, ENNReal.ofReal_lt_top⟩
            have ha : tailElapsedShift t ht a = tau := Subtype.ext (by
              dsimp [a, tailElapsedShift]
              ring)
            have hb : a ∈ (tailElapsedShift t ht) ⁻¹' B := by
              change tailElapsedShift t ht a ∈ B
              rw [ha]
              exact hBtau
            exact ⟨a.1, ⟨a, hb, rfl⟩, by dsimp [a]; ring⟩
          · rintro ⟨x, ⟨tau, hBtau, rfl⟩, rfl⟩
            exact ⟨tailElapsedShift t ht tau, ⟨hBtau, by
              change t < t + tau.1; linarith [tau.2.1]⟩, rfl⟩
        rw [he]
        have hi : (fun x => t + x) ''
            ((Subtype.val : ElapsedTime ⊤ → ℝ) '' ((tailElapsedShift t ht) ⁻¹' B)) =
            (fun x => -t + x) ⁻¹'
              ((Subtype.val : ElapsedTime ⊤ → ℝ) '' ((tailElapsedShift t ht) ⁻¹' B)) := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            change -t + (t + y) ∈
              ((Subtype.val : ElapsedTime ⊤ → ℝ) '' ((tailElapsedShift t ht) ⁻¹' B))
            simpa using hy
          · intro hx
            exact ⟨-t + x, hx, by ring⟩
        rw [hi, measure_preimage_add volume (-t)]
      let r := e.1.time + t
      let z := stripPoleState H ⊤ e
      let nu := E.2.fiberKernel (intervalDomain_measurable H) e.1.time r
        (le_add_of_nonneg_right ht) z
      have : IsFiniteMeasure nu :=
        ⟨(E.2.fiberKernel_mass_le_one (intervalDomain_measurable H)
          e.1.time r (le_add_of_nonneg_right ht) z).trans_lt ENNReal.one_lt_top⟩
      have hk :=
        (Measure.measurable_measure.mpr (fun B hB =>
          stripGreenOfKernel_infinite_measurable_apply H E.2 B hB)).comp
            (measurable_tailRestartPole r)
      apply Measure.ext_of_lintegral
      intro F hF
      have hL : MeasurableSet {p : Point | e.1.time + t < p.time} :=
        continuous_time.measurable measurableSet_Ioi
      rw [← lintegral_indicator hL,
        stripGreenOfKernel_spec H E.2 ⊤ e _ (hF.indicator hL)]
      have heq : (fun tau => ∫⁻ w,
          {p : Point | e.1.time + t < p.time}.indicator F
            (elapsedPhysicalPoint e.1.time (tau, w))
            ∂E.2.master (elapsedQuery e.1.time z tau)) =
          {tau : ElapsedTime ⊤ | t < tau.1}.indicator
            (fun tau => ∫⁻ w, F (elapsedPhysicalPoint e.1.time (tau, w))
              ∂E.2.master (elapsedQuery e.1.time z tau)) := by
        funext tau
        by_cases hh : t < tau.1
        · have hh' : e.1.time + t < e.1.time + tau.1 := by linarith
          simp [Set.indicator, elapsedPhysicalPoint, hh, hh']
        · have hh' : ¬e.1.time + t < e.1.time + tau.1 := by simpa using hh
          simp [Set.indicator, elapsedPhysicalPoint, hh, hh', lintegral_zero]
      change (∫⁻ tau, (fun tau => ∫⁻ w,
        {p : Point | e.1.time + t < p.time}.indicator F
          (elapsedPhysicalPoint e.1.time (tau, w))
          ∂E.2.master (elapsedQuery e.1.time z tau)) tau ∂elapsedVolume ⊤) = _
      rw [heq, lintegral_indicator (show MeasurableSet {tau : ElapsedTime ⊤ | t < tau.1}
          from measurable_subtype_coe measurableSet_Ioi),
        ← tailElapsedShift_map, lintegral_map (tailGreen_integrand_measurable E.2 e.1.time z F hF) (measurable_tailElapsedShift)]
      have hc : (∫⁻ tau : ElapsedTime ⊤, ∫⁻ w,
          F (elapsedPhysicalPoint e.1.time (tailElapsedShift t ht tau, w))
          ∂E.2.master (elapsedQuery e.1.time z (tailElapsedShift t ht tau))
          ∂elapsedVolume ⊤) =
          ∫⁻ tau : ElapsedTime ⊤, ∫⁻ a, ∫⁻ w, F ⟨r + tau.1, w.2, w.1⟩
            ∂E.2.master (tailRestartQuery H r (tau, a)) ∂nu ∂elapsedVolume ⊤ := by
        apply lintegral_congr
        intro tau
        have hh := tailRestart_master_lintegral e.1.time r (r + tau.1)
          (le_add_of_nonneg_right ht) (le_add_of_nonneg_right tau.2.1.le) z F hF
        have htau : e.1.time + (t + tau.1) = r + tau.1 := by dsimp [r]; ring
        simpa only [elapsedPhysicalPoint, tailElapsedShift, elapsedQuery, htau,
          tailRestartQuery, nu] using hh
      rw [hc, tailRestart_action_swap E.2 r nu F hF]
      exact (Measure.lintegral_bind hk.aemeasurable hF.aemeasurable).symm
    classical
    let H := c.activeInterval
    let E := stripEvolution hH hLE hlam hLam A H
    let ep := densityClockPole c e he
    let nu := E.2.fiberKernel (intervalDomain_measurable H) e.time (e.time + t)
      (le_add_of_nonneg_right ht) (stripPoleState H ⊤ ep)
    let K := enlargedActiveGreenKernel hH hLE hlam hLam A c
    have hh := tailRestart_green_identity H E
      (stripEvolution_spec hH hLE hlam hLam A H) ep
    change (stripGreenOfKernel H E.2 ⊤ ep).restrict {p | e.time + t < p.time} =
      nu.bind (fun a => stripGreenOfKernel H E.2 ⊤
        (tailRestartPole H (e.time + t) a)) at hh
    change (stripGreenOfKernel H E.2 ⊤ ep).restrict {p | e.time + t < p.time} =
      (nu.map (activeRestartPoint H (e.time + t))).bind K
    rw [nested_bind_map nu _ (measurable_activeRestartPoint H (e.time + t)) K K.measurable]
    refine hh.trans ?_
    congr 1
    funext a
    change _ = (if hv : (activeRestartPoint H (e.time + t) a).velocity 0 ∈ c.active then
      stripGreen hH hLE hlam hLam A H ⊤
        (densityClockPole c (activeRestartPoint H (e.time + t) a) hv) else 0)
    split
    · rfl
    · rename_i hn
      exact (hn ((tailRestartPole H (e.time + t) a).2.2)).elim
  rw [← active_tail_restart_identity_strict]
  apply Measure.restrict_congr_set
  have hn : ∀ᵐ p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c e he), p.time ≠ e.time + t := by
    rw [ae_iff]
    simpa using
      active_green_time_slice_null (e.time + t)
  filter_upwards [hn] with p hp
  exact propext (le_iff_lt_or_eq.trans (or_iff_left hp.symm))


/-- Equal nonnegative density measures have equal real densities almost everywhere. -/
theorem mixture_density_unique {X : Type*} [MeasurableSpace X] (m : Measure X)
    [SigmaFinite m] (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (he : m.withDensity (fun x => ENNReal.ofReal (f x)) =
      m.withDensity (fun x => ENNReal.ofReal (g x))) : f =ᵐ[m] g := by
  filter_upwards [((withDensity_eq_iff_of_sigmaFinite hf.ennreal_ofReal.aemeasurable hg.ennreal_ofReal.aemeasurable).mp he)] with x hx
  simpa only [ENNReal.toReal_ofReal (hf0 x), ENNReal.toReal_ofReal (hg0 x)] using (congrArg ENNReal.toReal hx)

/-- A restarted density bounds the restriction of the original density, independently of choices. -/
theorem mixture_density_restrict_bound {X : Type*} [MeasurableSpace X] (m : Measure X)
    [SigmaFinite m] (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (L : Set X)
    (hL : MeasurableSet L) (p : ℝ≥0∞) (hgp : MemLp g p m)
    (he : (m.withDensity (fun x => ENNReal.ofReal (f x))).restrict L =
      m.withDensity (fun x => ENNReal.ofReal (g x))) :
    MemLp f p (m.restrict L) ∧ eLpNorm f p (m.restrict L) ≤ eLpNorm g p m := by
  have hh := congrArg (fun mu => mu.restrict L) he
  rw [Measure.restrict_restrict hL, inter_self,
    restrict_withDensity hL, restrict_withDensity hL] at hh
  have ha := mixture_density_unique (m.restrict L) f g hf hg hf0 hg0 hh
  exact ⟨(eLpNorm_congr_ae ha).trans_lt (hgp.restrict L),
    (eLpNorm_congr_ae ha).le.trans (eLpNorm_restrict_le g p m L)⟩

/-- The actual surviving terminal measure is finite. -/
theorem activeRestartMeasure_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t) :
    IsFiniteMeasure (activeRestartMeasure hH hLE hlam hLam A c e he t ht) := by
  constructor
  rw [activeRestartMeasure_mass hH hLE hlam hLam A c e he t ht]
  exact ENNReal.ofReal_lt_top


/-- The literal restarted-tail statement follows from the genuine restart and density proofs. -/
theorem restartTailStatement_holds :
    RestartTailStatement  := by
  intro hH hLE lam Lam hlam hLam q hq
  have active_density_tail (hq : 1 < q) (hq2 : q < 3 / 2) :
      ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active),
      ∃ G : Point → ℝ, enlargedIsDensityOn
        (stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he))
        (densityClockStrip c e) G ∧ ∀ t : ℝ, 0 ≤ t →
        MemLp G (ENNReal.ofReal q)
          (volume.restrict {p | e.time + t ≤ p.time ∧ p.velocity 0 ∈ c.active}) ∧
        (eLpNorm G (ENNReal.ofReal q)
          (volume.restrict {p | e.time + t ≤ p.time ∧ p.velocity 0 ∈ c.active})).toReal ≤
          C * Real.exp (-c₀ * t / c.r ^ 2) * c.r ^ (6 / q - 4) := by
    have activeRestartMeasure_mass_exp :
        ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
        (e : Point) (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t),
        activeRestartMeasure hH hLE hlam hLam A c e he t ht univ ≤
          ENNReal.ofReal (C * Real.exp (-c₀ * t / c.r ^ 2)) := by
      have active_survival_exp :
          ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
          (e : Point) (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t),
          activeSurvivingMass hH hLE hlam hLam A c e he t ht ≤
            C * Real.exp (-c₀ * t / c.r ^ 2) := by
        have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
        refine ⟨2, 16 * lam * Real.log 2 / 9, by norm_num, by positivity, ?_⟩
        intro A c e he t ht
        have hb := stripSurvivingMass_exp_of_half_mass A c.activeInterval (stripEvolution hH hLE hlam hLam A c.activeInterval) (stripEvolution_spec hH hLE hlam hLam A c.activeInterval)
          (activeHalfMassTime lam c) (activeHalfMassTime_pos hlam c)
          (active_survival_half_mass hH hLE hlam hLam A c) e.time t ht
          (stripPoleState c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩)
        have heq : -Real.log 2 * t / activeHalfMassTime lam c =
            -(16 * lam * Real.log 2 / 9) * t / c.r ^ 2 := by
          unfold activeHalfMassTime
          field_simp [hlam.ne', c.positive.ne']
        rw [heq] at hb
        exact hb
      obtain ⟨C, c₀, hC, hc₀, hb⟩ := active_survival_exp
      refine ⟨C, c₀, hC, hc₀, ?_⟩
      intro A c e he t ht
      rw [activeRestartMeasure_mass]
      exact ENNReal.ofReal_le_ofReal (hb A c e he t ht)
    obtain ⟨C1, hC1, hm⟩ := enlargedActiveGreen_density hH hLE hlam hLam q hq hq2
    obtain ⟨C2, c₀, hC2, hc₀, hs⟩ :=
      activeRestartMeasure_mass_exp
    obtain ⟨_, _, hp⟩ := one_sign_pole_density hH hLE hlam hLam q hq hq2
    refine ⟨C1 * C2, c₀, mul_pos hC1 hC2, hc₀, ?_⟩
    intro A c e he
    obtain ⟨G, hGm, hG0, hGd, _, hGa⟩ := hp A c e he
    change stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he) =
      volume.withDensity (fun p => ENNReal.ofReal (G p)) at hGd
    have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
    refine ⟨G, ⟨hGm, hG0, ?_⟩, ?_⟩
    · have hr := Measure.restrict_eq_self_of_ae_mem hGa
      have hS : MeasurableSet (densityClockStrip c e) :=
        (continuous_time.measurable measurableSet_Ioi).inter
          (isOpen_Ioo.measurableSet.preimage
            ((continuous_apply 0).comp continuous_velocity).measurable)
      change (stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        (densityClockPole c e he)).restrict (densityClockStrip c e) = _ at hr
      exact hr.symm.trans ((congrArg (fun mu =>
        mu.restrict (densityClockStrip c e)) hGd).trans
          (restrict_withDensity hS (fun p => ENNReal.ofReal (G p))))
    · intro t ht
      let nu := activeRestartMeasure hH hLE hlam hLam A c e he t ht
      have : IsFiniteMeasure nu :=
        activeRestartMeasure_isFiniteMeasure hH hLE hlam hLam A c e he t ht
      obtain ⟨g, hgm, hg0, hgd, hgp, hgb⟩ := hm A c nu
      have hed := (congrArg (fun mu =>
        mu.restrict {p | e.time + t ≤ p.time}) hGd).symm.trans ((active_tail_restart_identity hH hLE hlam hLam A c e he t ht).trans hgd)
      have hL : MeasurableSet {p : Point | e.time + t ≤ p.time} :=
        continuous_time.measurable measurableSet_Ici
      obtain ⟨hGp, hGn⟩ := mixture_density_restrict_bound volume G g hGm hgm hG0 hg0
        _ hL (ENNReal.ofReal q) hgp hed
      have hsub : ({p : Point | e.time + t ≤ p.time ∧ p.velocity 0 ∈ c.active}) ⊆ {p : Point | e.time + t ≤ p.time} := fun _ h => h.1
      refine ⟨(hGp.mono_measure (Measure.restrict_mono hsub le_rfl)), ?_⟩
      have hreal := (ENNReal.toReal_mono hgp.ne_top ((eLpNorm_mono_measure G (Measure.restrict_mono hsub le_rfl)).trans hGn)).trans hgb
      have hmass : (nu univ).toReal ≤ C2 * Real.exp (-c₀ * t / c.r ^ 2) :=
        (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hs A c e he t ht)).trans_eq
          (ENNReal.toReal_ofReal (mul_nonneg hC2.le (Real.exp_pos _).le))
      exact hreal.trans (by simpa only [mul_assoc, mul_comm, mul_left_comm] using (mul_le_mul_of_nonneg_left hmass (mul_nonneg hC1.le (Real.rpow_nonneg c.positive.le (6 / q - 4)))))
  exact active_density_tail hq.1 hq.2

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

