module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ActiveTerminalDominationStep
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ActiveTerminalDominationKernel
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionStoppedExit
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionFuture
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionHorizonSplit
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassTerminal
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionHorizonLimit
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionHorizonOrder
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionPotential
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtension
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRepresentation
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonConsistency
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripMeasureExt
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripTimeMarginal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Stopped potential inequalities including observation-time entrance atoms -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution
open scoped Classical
open ProbabilityTheory
open Filter
open scoped Topology

/- An active piece spends its potential on its terminal value and strictly earlier exits. -/
theorem enlarged_active_stopped_step
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b T : ℝ) (hBT : b ≤ T)
    (hJ : closure c.active ⊆ J.carrier) (u : Point → ℝ)
    (hphi : IsKineticC112On u {p | p.time < b})
    (hc : ContinuousOn u {p | p.time ≤ b}) (M ) (hM : 0 ≤ M)
    (hbound : ∀ p, p.time ≤ b → |u p| ≤ M)
    (hop : ∀ p, p.time < b → forwardScalarOperator A.a u p = 0)
    (hn : ∀ p, p.time ≤ b → 0 ≤ u p)
    (p : Point) (hv : p.velocity 0 ∈ c.active)
    (B ) (hB : MeasurableSet B) (hsub : B ⊆ {q | q.time < b}) :
    (∫ q, enlargedStoppedPotential b u q
      ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) +
    (∫ q, enlargedStoppedPotential b u q
      ∂(enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T p).restrict B) ≤
        enlargedStoppedPotential b u p := by
  by_cases hb : p.time < b
  · rw [show enlargedStoppedPotential b u p = u p from ite_eq_left hb.le]
    let V := enlargedStoppedPotential b u
    let ep := densityClockPole c p hv
    let E := stripExit hH hLE hlam hLam A c.activeInterval b
      (stripPoleFinite c.activeInterval ep b hb)
    have he : enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b p = E := by
      rw [enlarged_activeUnion_eq c J hJ]
      have hp' : p ∈ enlargedVisitPoleSet c.activeInterval.toFiniteUnion b :=
        ⟨hb, by rw [Interval.toFiniteUnion_carrier]; exact ep.2.2⟩
      change (if ht : p ∈ enlargedVisitPoleSet c.activeInterval.toFiniteUnion b then
        finiteUnionExit hH hLE hlam hLam A _ b (enlargedVisitPole _ _ ⟨p, ht⟩) else 0) = E
      rw [dite_eq_left hp']
      rfl
    have hs : ∀ᵐ q ∂E, q.time ≤ b :=
      (stripExitOfRealization_ae_closed_future hH hlam hLam A c.activeInterval
        (stripEvolution hH hLE hlam hLam A c.activeInterval)
        (stripEvolution_spec hH hLE hlam hLam A c.activeInterval) b
        (stripPoleFinite c.activeInterval ep b hb)).mono fun _ hq => hq.2.1
    have hiE := enlargedStoppedPotential_integrable b u hc M hM hbound E
    have hnn : 0 ≤ᵐ[E] V := hs.mono fun q hq => by
      change 0 ≤ (if q.time ≤ b then u q else 0)
      rw [ite_eq_left hq]
      exact hn q hq
    have hd : enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p +
      (enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T p).restrict B ≤
        enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b p := by
      let H := c.activeInterval.toFiniteUnion
      have hp : p ∈ enlargedVisitPoleSet H b :=
        ⟨hb, by
          rw [show H.carrier = c.activeInterval.carrier from Interval.toFiniteUnion_carrier _]
          exact (densityClockPole c p hv).2.2⟩
      have hpT : p ∈ enlargedVisitPoleSet H T := ⟨hb.trans_le hBT, hp.2⟩
      let ep : StripPole c.activeInterval ⊤ := ⟨p, WithTop.coe_lt_top _, (densityClockPole c p hv).2.2⟩
      unfold enlargedActiveTerminalFamily
      rw [enlarged_activeUnion_eq c J hJ]
      rw [ite_eq_right (fun h => (ne_of_lt hb) h.1)]
      change (if h : p ∈ enlargedVisitPoleSet H b then
        finiteUnionExit hH hLE hlam hLam A H b (enlargedVisitPole H b ⟨p, h⟩)
          else 0).restrict {q | q.time = b} +
        (if h : p ∈ enlargedVisitPoleSet H T then
          finiteUnionExit hH hLE hlam hLam A H T (enlargedVisitPole H T ⟨p, h⟩)
            else 0).restrict B ≤
          (if h : p ∈ enlargedVisitPoleSet H b then
            finiteUnionExit hH hLE hlam hLam A H b (enlargedVisitPole H b ⟨p, h⟩) else 0)
      rw [dite_eq_left hp, dite_eq_left hpT]
      exact enlarged_stripExit_cap_and_early_le hH hLE hlam hLam A c.activeInterval ep b T
        hb hBT B hB hsub
    rw [he] at hd
    have hm := integral_mono_measure hd hnn hiE
    have hi1 := enlargedStoppedPotential_integrable b u hc M hM hbound
      (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p)
    have hi2 := enlargedStoppedPotential_integrable b u hc M hM hbound
      ((enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T p).restrict B)
    rw [integral_add_measure hi1 hi2] at hm
    have heq : V =ᵐ[E] u := hs.mono fun _ hq => ite_eq_left hq
    rw [integral_congr_ae heq, enlarged_stripExit_potential_identity hH hLE hlam hLam A
      c.activeInterval ep b hb u hphi hc M hM hbound hop] at hm
    exact hm
  · have hz : (∫ q, enlargedStoppedPotential b u q
        ∂(enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T p).restrict B) =
        0 := by
      apply integral_eq_zero_of_ae
      apply (ae_restrict_of_ae
        (enlargedVisitExitKernel_ae_time_gt hH hLE hlam hLam A (visitActiveUnion c J) T p)).mono
      intro q hq
      exact ite_eq_right (not_le_of_gt ((le_of_not_gt hb).trans_lt hq))
    rw [hz, add_zero]
    by_cases he : p.time = b
    · have hvJ : p.velocity 0 ∈ (visitActiveUnion c J).carrier := by
        rw [visitActiveUnion_carrier]
        exact ⟨hv, hJ (subset_closure hv)⟩
      have hterm : enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p =
          Measure.dirac p := by
        unfold enlargedActiveTerminalFamily
        exact ite_eq_left ⟨he, hvJ⟩
      rw [hterm, integral_dirac]
    · have hp : p ∉ enlargedVisitPoleSet (visitActiveUnion c J) b :=
        fun hp => hb hp.1
      have hterm : enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p = 0 := by
        unfold enlargedActiveTerminalFamily
        rw [ite_eq_right (fun h => he h.1)]
        change (if ht : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then
          finiteUnionExit hH hLE hlam hLam A _ b (enlargedVisitPole _ _ ⟨p, ht⟩)
            else 0).restrict {q | q.time = b} = 0
        rw [dite_eq_right hp, Measure.restrict_zero]
      rw [hterm, integral_zero_measure]
      rw [show enlargedStoppedPotential b u p = 0 from
        ite_eq_right (fun h => he (le_antisymm h (le_of_not_gt hb)))]

/- A waiting piece returns only the potential carried by poles strictly before observation. -/
theorem enlarged_waiting_stopped_step
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (b T : ℝ) (hBT : b ≤ T)
    (u : Point → ℝ) (hphi : IsKineticC112On u {p | p.time < b})
    (hc : ContinuousOn u {p | p.time ≤ b}) (M ) (hM : 0 ≤ M)
    (hbound : ∀ p, p.time ≤ b → |u p| ≤ M)
    (hop : ∀ p, p.time < b → forwardScalarOperator A.a u p = 0)
    (hn : ∀ p, p.time ≤ b → 0 ≤ u p)
    (p : Point) (B ) (_hB : MeasurableSet B) :
    (∫ q, enlargedStoppedPotential b u q
      ∂(enlargedVisitExitKernel hH hLE hlam hLam A H T p).restrict B) ≤
        {q : Point | q.time < b}.indicator (enlargedStoppedPotential b u) p := by
  by_cases hp : p.time < b
  · rw [show {q : Point | q.time < b}.indicator (enlargedStoppedPotential b u) p =
      enlargedStoppedPotential b u p from
      Set.indicator_of_mem (show p ∈ {q : Point | q.time < b} from hp) _]
    have hi := enlargedStoppedPotential_integrable b u hc M hM hbound
      (enlargedVisitExitKernel hH hLE hlam hLam A H T p)
    have hnV : 0 ≤ᵐ[enlargedVisitExitKernel hH hLE hlam hLam A H T p]
        enlargedStoppedPotential b u := Filter.Eventually.of_forall fun q => by
      unfold enlargedStoppedPotential
      split
      · exact hn q ‹q.time ≤ b›
      · exact le_rfl
    have _h_xinl_1 : (∫ q, enlargedStoppedPotential b u q ∂enlargedVisitExitKernel hH hLE hlam hLam A H T p) ≤ enlargedStoppedPotential b u p := by
      by_cases hp : p ∈ enlargedVisitPoleSet H T
      · by_cases hb : p.time < b
        · let e := enlargedVisitPole H T ⟨p, hp⟩
          let I := H.component (finiteUnionPoleIndex H T e)
          let ep : StripPole I ⊤ := ⟨p, WithTop.coe_lt_top _,
            (finiteUnionComponentPole H T e).2.2⟩
          have hi : (∫ p, enlargedStoppedPotential b u p
          ∂stripExit hH hLE hlam hLam A I T (stripPoleFinite I ep T (hb.trans_le hBT))) ≤
          u ep.1 := by
            let S : Set Point := {p | p.time ≤ b}
            have hS : MeasurableSet S := (isClosed_le continuous_time continuous_const).measurableSet
            let E := stripExit hH hLE hlam hLam A I b (stripPoleFinite I ep b hb)
            have hs : ∀ᵐ p ∂E, p ∈ S :=
              (stripExitOfRealization_ae_closed_future hH hlam hLam A I
                (stripEvolution hH hLE hlam hLam A I)
                (stripEvolution_spec hH hLE hlam hLam A I) b (stripPoleFinite I ep b hb)).mono
                  fun _ hp => hp.2.1
            have hint := enlargedStoppedPotential_integrable b u hc M hM hbound E
            have heq : enlargedStoppedPotential b u =ᵐ[E] u := hs.mono fun p hp => ite_eq_left hp
            have hu : Integrable u E := hint.congr heq
            have hdom : (stripExit hH hLE hlam hLam A I T
                (stripPoleFinite I ep T (hb.trans_le hBT))).restrict S ≤ E := by
              rcases eq_or_lt_of_le hBT with rfl | hlt
              · exact Measure.restrict_le_self
              ·
                let t := fun n : ℕ => b + 1 / ((n : ℝ) + 1)
                have hbt (n : ℕ) : b < t n := by dsimp [t]; exact lt_add_of_pos_right b (by positivity)
                have ht (n : ℕ) : ep.1.time < t n := hb.trans (hbt n)
                have hlim : Tendsto t atTop (𝓝 b) := by
                  simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add b
                have hsmall := hlim.eventually (gt_mem_nhds hlt)
                let S : Set Point := {p | p.time ≤ b}
                have hS : MeasurableSet S := (isClosed_le continuous_time continuous_const).measurableSet
                apply enlarged_physical_measure_le
                intro f hn
                have hconv :
                    let t := fun n : ℕ => b + 1 / ((n : ℝ) + 1)
                        let ht := fun n : ℕ => hb.trans (show b < t n by
                          dsimp [t]
                          exact lt_add_of_pos_right b (by positivity))
                        Tendsto (fun n => ∫ p, exitProbePhysical f p
                          ∂stripExit hH hLE hlam hLam A I (t n) (stripPoleFinite I ep (t n) (ht n)))
                          atTop (𝓝 (∫ p, exitProbePhysical f p
                            ∂stripExit hH hLE hlam hLam A I b (stripPoleFinite I ep b hb))) := by
                  dsimp only
                  let t := fun n : ℕ => b + 1 / ((n : ℝ) + 1)
                  have ht (n : ℕ) : ep.1.time < t n := hb.trans (by
                      dsimp [t]
                      exact lt_add_of_pos_right b (by positivity))
                  have htlim : Tendsto t atTop (𝓝 b) := by
                    simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add b
                  let G := stripGreen hH hLE hlam hLam A I ⊤ ep
                  let g := forwardScalarOperator A.a (exitProbePhysical f)
                  have hg : Integrable g G :=
                    stripGreen_integrable hH hLE hlam hLam A I ⊤ ep (exitProbeOperatorDatum A f)
                  let D := fun n : ℕ => {p : Point | p.time < t n}
                  have hanti : Antitone D := by
                    intro n m hnm p hp
                    have hn : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
                    have hdiv : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
                      exact one_div_le_one_div_of_le (by positivity) (by linarith)
                    change p.time < b + 1 / ((m : ℝ) + 1) at hp
                    change p.time < b + 1 / ((n : ℝ) + 1)
                    linarith
                  have hD : (⋂ n, D n) = {p : Point | p.time ≤ b} := by
                    ext p
                    constructor
                    · intro hp
                      exact ge_of_tendsto htlim
                        (Filter.Eventually.of_forall fun n => (show p.time < t n from mem_iInter.mp hp n).le)
                    · intro hp
                      apply mem_iInter.mpr
                      intro n
                      change p.time < b + 1 / ((n : ℝ) + 1)
                      exact hp.trans_lt (lt_add_of_pos_right b (by positivity))
                  have hi := tendsto_setIntegral_of_antitone
                    (fun n => (isOpen_lt continuous_time continuous_const).measurableSet) hanti
                      (⟨0, hg.integrableOn⟩ : ∃ n, IntegrableOn g (D n) G)
                  rw [hD] at hi
                  have hae : {p : Point | p.time ≤ b} =ᵐ[G] {p | p.time < b} := by
                    have hz := enlarged_stripGreen_time_slice_zero hH hLE hlam hLam A I ep b
                    have hn : ∀ᵐ p ∂G, p.time ≠ b := by
                      rw [ae_iff]
                      simpa only [not_not] using hz
                    filter_upwards [hn] with p hp
                    exact propext (lt_iff_le_and_ne.trans (and_iff_left hp)).symm
                  rw [Measure.restrict_congr_set hae] at hi
                  have hp (B : ℝ) (hB : ep.1.time < B) :
                      (∫ p, exitProbePhysical f p
                        ∂stripExit hH hLE hlam hLam A I B (stripPoleFinite I ep B hB)) =
                        exitProbePhysical f ep.1 + ∫ p in {p : Point | p.time < B}, g p ∂G := by
                    have h := stripExitOfRealization_probe_integral hH hlam hLam A I
                      (stripEvolution hH hLE hlam hLam A I)
                      (stripEvolution_spec hH hLE hlam hLam A I) B (stripPoleFinite I ep B hB) f
                    change _ = exitProbePhysical f ep.1 + ∫ p, g p
                      ∂stripGreen hH hLE hlam hLam A I B (stripPoleFinite I ep B hB) at h
                    rw [stripGreen_finite_restrict_infinite] at h
                    exact h
                  have hf := hi.const_add (exitProbePhysical f ep.1)
                  rw [← hp b hb] at hf
                  exact hf.congr (fun n => (hp (t n) (ht n)).symm)
                apply ge_of_tendsto hconv
                filter_upwards [hsmall] with n hnT
                let R := (b + t n) / 2
                have hR : b < R := by dsimp [R]; linarith [hbt n]
                have hRt : R ≤ t n := by dsimp [R]; linarith [hbt n]
                have hRT := hRt.trans hnT.le
                have he := stripExit_horizon_consistency hH hLE hlam hLam A I ep T (t n)
                  (hb.trans hlt) (ht n) R hRT hRt
                have he' := congrArg (fun rho : Measure Point => rho.restrict S) he
                have hs : S ⊆ {p : Point | p.time < R} := fun p hp => hp.trans_lt hR
                simp only [Measure.restrict_restrict hS, inter_eq_left.mpr hs] at he'
                rw [he']
                exact integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall hn)
                  (nestedProbe_integrable A f _)
            have hnn := hs.mono fun p hp => hn p hp
            have hm := integral_mono_measure hdom hnn hu
            have hsub : reconstructionStrip I (ep.1.time - 1) b ⊆ {p | p.time < b} :=
              fun _ hp => hp.2.1
            have hr : IsKineticC112On u (reconstructionStrip I (ep.1.time - 1) b) := by
              rcases hphi with ⟨hc0, ht, hx, hv, htc, hxc, hvc, hvvc⟩
              exact ⟨hc0.mono hsub, fun p hp => ht p (hsub hp), fun p hp => hx p (hsub hp),
                fun p hp => hv p (hsub hp), htc.mono hsub, hxc.mono hsub, hvc.mono hsub,
                hvvc.mono hsub⟩
            have hi := strip_identity_C112 hH hLE hlam hLam A I (ep.1.time - 1) b
              (by linarith) (stripPoleFinite I ep b hb) (by change ep.1.time - 1 < ep.1.time; linarith)
              u hr
                (hc.mono fun p hp => by
                  rcases hp with hp | hp
                  · exact hp.2.1.le
                  · rcases hp with hp | hp
                    · exact hp.1.le
                    · exact hp.2.1.le)
                ⟨M, fun p hp => ⟨hbound p hp.2.1.le, by rw [hop p hp.2.1, abs_zero]; exact hM⟩⟩
            have hz : (∫ p, forwardScalarOperator A.a u p
                ∂stripGreen hH hLE hlam hLam A I b (stripPoleFinite I ep b hb)) = 0 := by
              apply integral_eq_zero_of_ae
              exact (stripGreenOfKernel_ae_mem_stripPast I _ b (stripPoleFinite I ep b hb)).mono
                fun p hp => hop p hp.1
            rw [hz, sub_zero] at hi
            rw [← hi] at hm
            change (∫ p, S.indicator u p ∂_) ≤ u ep.1
            rw [integral_indicator hS]
            exact hm
          change (∫ q, enlargedStoppedPotential b u q ∂
            (if ht : p ∈ enlargedVisitPoleSet H T then _ else 0)) ≤ _
          rw [dite_eq_left hp]
          change (∫ q, enlargedStoppedPotential b u q ∂stripExit hH hLE hlam hLam A I T _) ≤ _
          rw [show enlargedStoppedPotential b u p = u p from ite_eq_left hb.le]
          exact hi
        · have _h_inl_15 : (∫ q, enlargedStoppedPotential b u q
          ∂enlargedVisitExitKernel hH hLE hlam hLam A H T p) = 0 := by
            have hp := (le_of_not_gt hb)
            apply integral_eq_zero_of_ae
            exact (enlargedVisitExitKernel_ae_time_gt hH hLE hlam hLam A H T p).mono
              fun q hq => ite_eq_right (not_le_of_gt (hp.trans_lt hq))
          rw [_h_inl_15]
          unfold enlargedStoppedPotential
          split
          · exact hn p ‹p.time ≤ b›
          · exact le_rfl
      · change (∫ q, enlargedStoppedPotential b u q ∂
          (if ht : p ∈ enlargedVisitPoleSet H T then _ else 0)) ≤ _
        rw [dite_eq_right hp, integral_zero_measure]
        unfold enlargedStoppedPotential
        split
        · exact hn p ‹p.time ≤ b›
        · exact le_rfl
    exact (integral_mono_measure Measure.restrict_le_self hnV hi).trans
      _h_xinl_1
  · rw [show {q : Point | q.time < b}.indicator (enlargedStoppedPotential b u) p =
      0 from Set.indicator_of_notMem (show p ∉ {q : Point | q.time < b} from hp) _]
    apply le_of_eq
    apply integral_eq_zero_of_ae
    exact (ae_restrict_of_ae
      (enlargedVisitExitKernel_ae_time_gt hH hLE hlam hLam A H T p)).mono
        fun q hq => ite_eq_right (not_le_of_gt ((le_of_not_gt hp).trans_lt hq))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
