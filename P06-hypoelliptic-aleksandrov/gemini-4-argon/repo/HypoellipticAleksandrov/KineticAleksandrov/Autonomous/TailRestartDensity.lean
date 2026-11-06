module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestart
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FarVelocityDensityDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.RestartTailStatement
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Survival
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.MixtureDensityTests
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.MixtureDensityTransport
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalHalfMass
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalIteration
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.MixtureDensity
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenBorel
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripTimeMarginal
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartAction
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartGreen
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartKernel
import Mathlib.MeasureTheory.Measure.Prod
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Elapsed
import Mathlib.MeasureTheory.Group.Measure

/-! # Quantitative density tails from the genuine terminal restart -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal
open SectionTwo
open ProbabilityTheory

/- Equal nonnegative density measures have equal real densities almost everywhere. -/
theorem mixture_density_restrict_bound {X : Type*} [MeasurableSpace X] (m : Measure X)
    [SigmaFinite m] (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (L )
    (hL : MeasurableSet L) (p : ℝ≥0∞) (hgp : MemLp g p m)
    (he : (m.withDensity (fun x => ENNReal.ofReal (f x))).restrict L =
      m.withDensity (fun x => ENNReal.ofReal (g x))) :
    MemLp f p (m.restrict L) ∧ eLpNorm f p (m.restrict L) ≤ eLpNorm g p m := by
  have hh := congrArg (fun mu : Measure X => mu.restrict L) he
  rw [Measure.restrict_restrict hL, inter_self,
    restrict_withDensity hL, restrict_withDensity hL] at hh
  have ha : f =ᵐ[(m.restrict L)] g := by
    let m := (m.restrict L)
    have he := hh
    have hh := (withDensity_eq_iff_of_sigmaFinite
      hf.ennreal_ofReal.aemeasurable hg.ennreal_ofReal.aemeasurable).mp he
    filter_upwards [hh] with x hx
    have ht := congrArg ENNReal.toReal hx
    simpa only [ENNReal.toReal_ofReal (hf0 x), ENNReal.toReal_ofReal (hg0 x)] using ht
  exact ⟨(eLpNorm_congr_ae ha).trans_lt (hgp.restrict L),
    (eLpNorm_congr_ae ha).le.trans (eLpNorm_restrict_le g p m L)⟩

/- The actual surviving terminal measure is finite. -/
theorem active_density_tail
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q) (hq2 : q < (3 : ℝ) / 2) :
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
  obtain ⟨C1, hC1, hm⟩ : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (nu : Measure Point) [IsFiniteMeasure nu],
      ∃ g : Point → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
        enlargedActiveGreen hH hLE hlam hLam A c nu =
          volume.withDensity (fun x => ENNReal.ofReal (g x)) ∧
        MemLp g (ENNReal.ofReal q) volume ∧
        (eLpNorm g (ENNReal.ofReal q) volume).toReal ≤
          C * c.r ^ (6 / q - 4) * (nu Set.univ).toReal := by
    have hpq : q.HolderConjugate (q / (q - 1)) :=
      (Real.holderConjugate_iff_eq_conjExponent hq).2 rfl
    obtain ⟨C, hC, ht⟩ :=
      mixture_density_conjugate_tests hH hLE hlam hLam q _ hpq hq2
    refine ⟨C, hC, ?_⟩
    intro A c nu _
    let mu := enlargedActiveGreen hH hLE hlam hLam A c nu
    have : IsFiniteMeasure mu := enlargedActiveGreen_isFiniteMeasure hH hLE hlam hLam A c nu
    apply mixture_point_density_of_tests mu q
      (C * c.r ^ (6 / q - 4) * (nu Set.univ).toReal) hq
      (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg c.positive.le _))
        ENNReal.toReal_nonneg)
    intro f hfp hfn
    simpa only [mul_assoc, mul_comm, mul_left_comm] using ht A c nu f hfp hfn
  obtain ⟨C2, c₀, hC2, hc₀, hs⟩ : ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (e : Point) (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t),
      activeRestartMeasure hH hLE hlam hLam A c e he t ht univ ≤
        ENNReal.ofReal (C * Real.exp (-c₀ * t / c.r ^ 2)) := by
    obtain ⟨C, c₀, hC, hc₀, hb⟩ : ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (e : Point) (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t),
      activeSurvivingMass hH hLE hlam hLam A c e he t ht ≤
        C * Real.exp (-c₀ * t / c.r ^ 2) := by
      have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      refine ⟨2, 16 * lam * Real.log 2 / 9, by norm_num, by positivity, ?_⟩
      intro A c e he t ht
      let E := stripEvolution hH hLE hlam hLam A c.activeInterval
      have hE := stripEvolution_spec hH hLE hlam hLam A c.activeInterval
      have hb := stripSurvivingMass_exp_of_half_mass A c.activeInterval E hE
        (activeHalfMassTime lam c) (activeHalfMassTime_pos hlam c)
        (active_survival_half_mass hH hLE hlam hLam A c) e.time t ht
        (stripPoleState c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩)
      have heq : -Real.log 2 * t / activeHalfMassTime lam c =
          -(16 * lam * Real.log 2 / 9) * t / c.r ^ 2 := by
        unfold activeHalfMassTime
        field_simp [hlam.ne', c.positive.ne']
      rw [heq] at hb
      exact hb
    refine ⟨C, c₀, hC, hc₀, ?_⟩
    intro A c e he t ht
    rw [activeRestartMeasure_mass]
    exact ENNReal.ofReal_le_ofReal (hb A c e he t ht)
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
    exact hr.symm.trans ((congrArg (fun mu : Measure Point =>
      mu.restrict (densityClockStrip c e)) hGd).trans
        (restrict_withDensity hS (fun p => ENNReal.ofReal (G p))))
  · intro t ht
    let nu := activeRestartMeasure hH hLE hlam hLam A c e he t ht
    have : IsFiniteMeasure nu := by
        constructor
        rw [activeRestartMeasure_mass hH hLE hlam hLam A c e he t ht]
        exact ENNReal.ofReal_lt_top

      /- One fixed one-pole density has the uniform exponential Lq tail at every delay. -/
    obtain ⟨g, hgm, hg0, hgd, hgp, hgb⟩ := hm A c nu
    have heq : (stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he)).restrict
      {p | e.time + t ≤ p.time} =
        enlargedActiveGreen hH hLE hlam hLam A c
          (activeRestartMeasure hH hLE hlam hLam A c e he t ht) := by
      have _h_xinl_0 : (stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he)).restrict {p | e.time + t < p.time} = enlargedActiveGreen hH hLE hlam hLam A c (activeRestartMeasure hH hLE hlam hLam A c e he t ht) := by
        classical
        let H := c.activeInterval
        let E := stripEvolution hH hLE hlam hLam A H
        let ep := densityClockPole c e he
        let nu := E.2.fiberKernel (intervalDomain_measurable H) e.time (e.time + t)
          (le_add_of_nonneg_right ht) (stripPoleState H ⊤ ep)
        let K := enlargedActiveGreenKernel hH hLE hlam hLam A c
        have hh : (stripGreenOfKernel H E.2 ⊤ ep).restrict {p | ep.1.time + t < p.time} =
            (E.2.fiberKernel (intervalDomain_measurable H) ep.1.time (ep.1.time + t)
              (le_add_of_nonneg_right ht) (stripPoleState H ⊤ ep)).bind
                (fun a => stripGreenOfKernel H E.2 ⊤ (tailRestartPole H (ep.1.time + t) a)) := by
          have hE := (stripEvolution_spec hH hLE hlam hLam A H)
          let r := ep.1.time + t
          let z := stripPoleState H ⊤ ep
          let nu := E.2.fiberKernel (intervalDomain_measurable H) ep.1.time r
            (le_add_of_nonneg_right ht) z
          have : IsFiniteMeasure nu :=
            ⟨(E.2.fiberKernel_mass_le_one (intervalDomain_measurable H)
              ep.1.time r (le_add_of_nonneg_right ht) z).trans_lt ENNReal.one_lt_top⟩
          have _h_xinl_0 : Measurable (tailRestartPole H r) := by
              exact (
            (measurable_activeRestartPoint H r).subtype_mk
            )
          have hk : Measurable (fun a =>
              stripGreenOfKernel H E.2 ⊤ (tailRestartPole H r a)) :=
            (Measure.measurable_measure.mpr (fun B hB =>
              stripGreenOfKernel_infinite_measurable_apply H E.2 B hB)).comp
                _h_xinl_0
          apply Measure.ext_of_lintegral
          intro F hF
          have hL : MeasurableSet {p : Point | ep.1.time + t < p.time} :=
            continuous_time.measurable measurableSet_Ioi
          rw [← lintegral_indicator hL,
            stripGreenOfKernel_spec H E.2 ⊤ ep _ (hF.indicator hL)]
          have hi : Measurable (fun tau : ElapsedTime ⊤ => ∫⁻ w,
            F (elapsedPhysicalPoint ep.1.time (tau, w)) ∂E.2.master (elapsedQuery ep.1.time z tau)) := by
            let K := E.2
            let s := ep.1.time
            let k := elapsedKernel K s ⊤
            have : IsFiniteKernel k := by dsimp [k, elapsedKernel]; infer_instance
            have hm : Measurable (fun q :
                (EvolutionState (intervalDomain H) (fun _ => 0) s × ElapsedTime ⊤) ×
                  EvolutionAmbientState 1 => F (elapsedPhysicalPoint s (q.1.2, q.2))) :=
              hF.comp ((measurable_elapsedPhysicalPoint s ⊤).comp
                (measurable_fst.snd.prodMk measurable_snd))
            exact (hm.lintegral_kernel_prod_right' (κ := k)).comp
              (measurable_const.prodMk measurable_id)
          have heq : (fun tau : ElapsedTime ⊤ => ∫⁻ w,
              {p : Point | ep.1.time + t < p.time}.indicator F
                (elapsedPhysicalPoint ep.1.time (tau, w))
                ∂E.2.master (elapsedQuery ep.1.time z tau)) =
              {tau : ElapsedTime ⊤ | t < tau.1}.indicator
                (fun tau => ∫⁻ w, F (elapsedPhysicalPoint ep.1.time (tau, w))
                  ∂E.2.master (elapsedQuery ep.1.time z tau)) := by
            funext tau
            by_cases hh : t < tau.1
            · have hh' : ep.1.time + t < ep.1.time + tau.1 := by linarith
              simp only [Set.indicator, Set.mem_ofPred_eq, elapsedPhysicalPoint, hh, hh', ite_true]
            · have hh' : ¬ep.1.time + t < ep.1.time + tau.1 := by simpa using hh
              simp only [Set.indicator, Set.mem_ofPred_eq, elapsedPhysicalPoint,
                hh, hh', ite_false, lintegral_zero]
          change (∫⁻ tau, (fun tau : ElapsedTime ⊤ => ∫⁻ w,
            {p : Point | ep.1.time + t < p.time}.indicator F
              (elapsedPhysicalPoint ep.1.time (tau, w))
              ∂E.2.master (elapsedQuery ep.1.time z tau)) tau ∂elapsedVolume ⊤) = _
          have _h_xinl_0 : (elapsedVolume ⊤).map (tailElapsedShift t ht) = (elapsedVolume ⊤).restrict {tau | t < tau.1} := by
            ext B hB
            have hm : MeasurableSet {tau : ElapsedTime ⊤ | t < tau.1} :=
              measurable_subtype_coe measurableSet_Ioi
            rw [Measure.map_apply (measurable_tailElapsedShift t ht) hB,
              elapsedVolume_apply _ _ ((measurable_tailElapsedShift t ht) hB),
              Measure.restrict_apply hB, elapsedVolume_apply _ _ (hB.inter hm)]
            have he : (Subtype.val : ElapsedTime ⊤ → ℝ) '' (B ∩ {tau | t < tau.1}) =
                (fun x : ℝ => t + x) ''
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
            have hi : (fun x : ℝ => t + x) ''
                ((Subtype.val : ElapsedTime ⊤ → ℝ) '' ((tailElapsedShift t ht) ⁻¹' B)) =
                (fun x : ℝ => -t + x) ⁻¹'
                  ((Subtype.val : ElapsedTime ⊤ → ℝ) '' ((tailElapsedShift t ht) ⁻¹' B)) := by
              ext x
              constructor
              · rintro ⟨y, hy, rfl⟩
                change -t + (t + y) ∈
                  ((Subtype.val : ElapsedTime ⊤ → ℝ) '' ((tailElapsedShift t ht) ⁻¹' B))
                simpa only [neg_add_cancel_left] using hy
              · intro hx
                exact ⟨-t + x, hx, by ring⟩
            rw [hi, measure_preimage_add volume (-t)]
          rw [heq, lintegral_indicator (show MeasurableSet {tau : ElapsedTime ⊤ | t < tau.1}
              from measurable_subtype_coe measurableSet_Ioi),
            ← _h_xinl_0, lintegral_map hi (measurable_tailElapsedShift t ht)]
          have hc : (∫⁻ tau : ElapsedTime ⊤, ∫⁻ w,
              F (elapsedPhysicalPoint ep.1.time (tailElapsedShift t ht tau, w))
              ∂E.2.master (elapsedQuery ep.1.time z (tailElapsedShift t ht tau))
              ∂elapsedVolume ⊤) =
              ∫⁻ tau : ElapsedTime ⊤, ∫⁻ a, ∫⁻ w, F ⟨r + tau.1, w.2, w.1⟩
                ∂E.2.master (tailRestartQuery H r (tau, a)) ∂nu ∂elapsedVolume ⊤ := by
            apply lintegral_congr
            intro tau
            have hh := tailRestart_master_lintegral A H E hE ep.1.time r (r + tau.1)
              (le_add_of_nonneg_right ht) (le_add_of_nonneg_right tau.2.1.le) z F hF
            have htau : ep.1.time + (t + tau.1) = r + tau.1 := by dsimp [r]; ring
            simpa only [elapsedPhysicalPoint, tailElapsedShift, elapsedQuery, htau,
              tailRestartQuery, nu] using hh
          have _h_xinl_0 : (∫⁻ tau, ∫⁻ a, ∫⁻ w, F ⟨r + tau.1, w.2, w.1⟩
            ∂E.2.master (tailRestartQuery H r (tau, a)) ∂nu ∂elapsedVolume ⊤) =
            ∫⁻ a, ∫⁻ p, F p ∂stripGreenOfKernel H E.2 ⊤ (tailRestartPole H r a) ∂nu := by
            let K := E.2
            have _h_xinl_0 : Measurable (tailRestartQuery H r) := by
              apply Measurable.subtype_mk
              exact measurable_const.prodMk
                ((measurable_const.add (measurable_subtype_coe.comp measurable_fst)).prodMk
                  (measurable_subtype_coe.comp measurable_snd))
            let k := K.master.comap (tailRestartQuery H r) _h_xinl_0
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
            have _h_xinl_0 (H : Interval) (r : ℝ) (a) : stripPoleState H ⊤ (tailRestartPole H r a) = a := by
              apply Subtype.ext
              rfl
            rw [stripGreenOfKernel_spec H K ⊤ (tailRestartPole H r a) F hF,
              _h_xinl_0]
            rfl
          rw [hc, _h_xinl_0]
          exact (Measure.lintegral_bind hk.aemeasurable hF.aemeasurable).symm
        change (stripGreenOfKernel H E.2 ⊤ ep).restrict {p | e.time + t < p.time} =
          nu.bind (fun a => stripGreenOfKernel H E.2 ⊤
            (tailRestartPole H (e.time + t) a)) at hh
        change (stripGreenOfKernel H E.2 ⊤ ep).restrict {p | e.time + t < p.time} =
          (nu.map (activeRestartPoint H (e.time + t))).bind K
        rw [nested_bind_map nu _ (measurable_activeRestartPoint H (e.time + t)) K K.measurable]
        refine hh.trans ?_
        congr 1
        funext a
        have ha :=
          (tailRestartPole H (e.time + t) a).2.2
        change _ = (if hv : (activeRestartPoint H (e.time + t) a).velocity 0 ∈ c.active then
          stripGreen hH hLE hlam hLam A H ⊤
            (densityClockPole c (activeRestartPoint H (e.time + t) a) hv) else 0)
        split
        · rfl
        · rename_i hn
          exact (hn ha).elim
      rw [← _h_xinl_0]
      apply Measure.restrict_congr_set
      have hn : ∀ᵐ p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
          (densityClockPole c e he), p.time ≠ e.time + t := by
        rw [ae_iff]
        have _h_xinl_0 : stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he) {p | p.time = (e.time + t)} = 0 := by
          let s := (e.time + t)
          simpa only [mem_singleton_iff, Real.volume_singleton, nonpos_iff_eq_zero] using (stripGreen_timeMarginal hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he) {s} (measurableSet_singleton s))
        simpa only [not_not] using _h_xinl_0
      filter_upwards [hn] with p hp
      exact propext (le_iff_lt_or_eq.trans (or_iff_left hp.symm))
    have hed := (congrArg (fun mu : Measure Point =>
      mu.restrict {p | e.time + t ≤ p.time}) hGd).symm.trans (heq.trans hgd)
    have hL : MeasurableSet {p : Point | e.time + t ≤ p.time} :=
      continuous_time.measurable measurableSet_Ici
    obtain ⟨hGp, hGn⟩ := mixture_density_restrict_bound volume G g hGm hgm hG0 hg0
      _ hL (ENNReal.ofReal q) hgp hed
    let S := {p : Point | e.time + t ≤ p.time ∧ p.velocity 0 ∈ c.active}
    have hsub : S ⊆ {p : Point | e.time + t ≤ p.time} := fun _ h => h.1
    have hpn := hGp.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hnn := (eLpNorm_mono_measure G (Measure.restrict_mono hsub le_rfl)).trans hGn
    refine ⟨hpn, ?_⟩
    have hreal := (ENNReal.toReal_mono hgp.ne_top hnn).trans hgb
    have hmass : (nu univ).toReal ≤ C2 * Real.exp (-c₀ * t / c.r ^ 2) :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hs A c e he t ht)).trans_eq
        (ENNReal.toReal_ofReal (mul_nonneg hC2.le (Real.exp_pos _).le))
    have hb := mul_le_mul_of_nonneg_left hmass
      (mul_nonneg hC1.le (Real.rpow_nonneg c.positive.le (6 / q - 4)))
    exact hreal.trans (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hb)

/- The literal restarted-tail statement follows from the genuine restart and density proofs. -/
theorem restartTailStatement_holds :
    RestartTailStatement := by
  intro hH hLE lam Lam hlam hLam q hq
  exact active_density_tail hH hLE hlam hLam q hq.1 hq.2

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
