module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionHorizonLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRepresentation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassTerminal
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionFuture
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtension
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyBoundedData
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripCoordinates
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionFullSpace
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCapacity

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter SectionTwo TheoremA Evolution ProbabilityTheory Parabolic
open scoped Topology Classical

/-- Nonnegative compact smooth physical probes determine order of finite measures. -/
theorem enlarged_physical_measure_le {mu nu : Measure Point}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (h : ∀ f : exitProbeSubmodule, (∀ p, 0 ≤ exitProbePhysical f p) →
      (∫ p, exitProbePhysical f p ∂mu) ≤ ∫ p, exitProbePhysical f p ∂nu) : mu ≤ nu := by
  let e := reconstructionPhysicalHomeomorph
  have hm : mu.map e.symm ≤ nu.map e.symm := by
    apply measure_le_of_smooth_integral_le isOpen_univ (by simp)
    intro f hf hc _ hn
    let F : exitProbeSubmodule := ⟨f, hf, hc⟩
    have hi (rho : Measure Point) : (∫ x, f x ∂rho.map e.symm) =
        ∫ p, exitProbePhysical F p ∂rho :=
      integral_map e.symm.measurable.aemeasurable hf.continuous.measurable.aestronglyMeasurable
    rw [hi mu, hi nu]
    exact h F (fun p => hn _)
  have hb (rho : Measure Point) : (rho.map e.symm).map e = rho := by
    rw [Measure.map_map e.measurable e.symm.measurable]
    have he : e ∘ e.symm = (id : Point → Point) := funext e.apply_symm_apply
    rw [he, Measure.map_id]
  have hmap := Measure.map_mono hm e.measurable
  rwa [hb mu, hb nu] at hmap

/-- Later-horizon exits up to a closed intermediate time are dominated by its stopped exit.
This retains possible endpoint mass rather than assuming temporal atomlessness. -/
theorem enlarged_stripExit_early_closed_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (b T : ℝ) (hb : e.1.time < b) (hBT : b < T) :
    (stripExit hH hLE hlam hLam A H T
      (stripPoleFinite H e T (hb.trans hBT))).restrict {p | p.time ≤ b} ≤
        stripExit hH hLE hlam hLam A H b (stripPoleFinite H e b hb) := by
  let t := fun n : ℕ => b + 1 / ((n : ℝ) + 1)
  have hbt (n : ℕ) : b < t n := by dsimp [t]; exact lt_add_of_pos_right b (by positivity)
  have ht (n : ℕ) : e.1.time < t n := hb.trans (hbt n)
  have hlim : Tendsto t atTop (𝓝 b) := by
    simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add b
  let S : Set Point := {p | p.time ≤ b}
  have hS : MeasurableSet S := (isClosed_le continuous_time continuous_const).measurableSet
  apply enlarged_physical_measure_le
  intro f hn
  apply ge_of_tendsto (enlarged_exit_probe_right_limit hH hLE hlam hLam A H e b hb f)
  filter_upwards [(hlim.eventually (gt_mem_nhds hBT))] with n hnT
  let R := (b + t n) / 2
  have hR : b < R := by dsimp [R]; linarith [hbt n]
  have hRt : R ≤ t n := by dsimp [R]; linarith [hbt n]
  have he := stripExit_horizon_consistency hH hLE hlam hLam A H e T (t n)
    (hb.trans hBT) (ht n) R (hRt.trans hnT.le) hRt
  have he' := congrArg (fun rho => rho.restrict S) he
  have hs : S ⊆ {p : Point | p.time < R} := fun p hp => hp.trans_lt hR
  simp only [Measure.restrict_restrict hS, inter_eq_left.mpr hs] at he'
  rw [he']
  exact integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall hn)
    (nestedProbe_integrable A f _)


/-- Every actual terminal family has mass at most one, including zero-duration poles. -/
theorem enlarged_terminal_family_mass_le_one
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) (p : Point) :
    enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p univ ≤ 1 := by
  unfold enlargedActiveTerminalFamily
  split
  · simp
  · apply (Measure.restrict_le_self univ).trans
    change (if hp : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then
      finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) b
        (enlargedVisitPole _ _ ⟨p, hp⟩) else 0) univ ≤ 1
    split
    · simp
    · exact zero_le

/-- Every actual terminal fiber is finite. -/
instance enlarged_terminal_family_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) (p : Point) :
    IsFiniteMeasure (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) :=
  ⟨(enlarged_terminal_family_mass_le_one hH hLE hlam hLam A c J b p).trans_lt
    ENNReal.one_lt_top⟩



/-- The actual terminal family is measurable even on its zero-duration face. -/
theorem enlarged_terminal_family_measurable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    Measurable (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b) := by
  let E := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b
  have hS : MeasurableSet {q : Point | q.time = b} :=
    (isClosed_eq continuous_time continuous_const).measurableSet
  have hm : Measurable (fun p => (E p).restrict {q | q.time = b}) :=
    Measure.measurable_of_measurable_coe _ fun B hB => by
      simp_rw [Measure.restrict_apply hB]
      exact E.measurable_coe (hB.inter hS)
  exact Measure.measurable_dirac.ite
    (hS.inter ((visitActiveUnion c J).isOpen_carrier.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)) hm

/-- Kernel packaging of the already defined actual terminal family. -/
def enlargedTerminalFamilyKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) : Kernel Point Point :=
  ⟨enlargedActiveTerminalFamily hH hLE hlam hLam A c J b,
    enlarged_terminal_family_measurable hH hLE hlam hLam A c J b⟩

/-- The actual terminal kernel is uniformly finite with bound one. -/
instance enlargedTerminalFamilyKernel_isFiniteKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    IsFiniteKernel (enlargedTerminalFamilyKernel hH hLE hlam hLam A c J b) :=
  ⟨1, ENNReal.one_lt_top,
    enlarged_terminal_family_mass_le_one hH hLE hlam hLam A c J b⟩


/-- Keep a homogeneous potential up to the observation time and set it to zero afterwards. -/
def enlargedStoppedPotential (b : ℝ) (u : Point → ℝ) (p : Point) : ℝ :=
  if p.time ≤ b then u p else 0










/-- Integrating two actual kernel actions preserves their pointwise sum inequality. -/
theorem enlarged_integral_kernel_pair_le
    (K L : Kernel Point Point) (mu : Measure Point) [IsFiniteMeasure mu]
    (f g : Point → ℝ) (hK : Integrable f (K ∘ₘ mu)) (hL : Integrable f (L ∘ₘ mu))
    (hg : Integrable g mu)
    (hstep : ∀ᵐ p ∂mu, (∫ q, f q ∂K p) + (∫ q, f q ∂L p) ≤ g p) :
    (∫ q, f q ∂K ∘ₘ mu) + (∫ q, f q ∂L ∘ₘ mu) ≤ ∫ p, g p ∂mu := by
  have hiK : Integrable (fun p => ∫ q, f q ∂K p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hK
    simpa using hK.integral_comp
  have hiL : Integrable (fun p => ∫ q, f q ∂L p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hL
    simpa using hL.integral_comp
  rw [nested_integral_bind mu K K.measurable f hK,
    nested_integral_bind mu L L.measurable f hL, ← integral_add hiK hiL]
  exact integral_mono_ae (hiK.add hiL) hg hstep

/-- Integrating one actual kernel action preserves a pointwise bound. -/
theorem enlarged_integral_kernel_le
    (K : Kernel Point Point) (mu : Measure Point) [IsFiniteMeasure mu]
    (f g : Point → ℝ) (hK : Integrable f (K ∘ₘ mu)) (hg : Integrable g mu)
    (hstep : ∀ᵐ p ∂mu, (∫ q, f q ∂K p) ≤ g p) :
    (∫ q, f q ∂K ∘ₘ mu) ≤ ∫ p, g p ∂mu := by
  have hiK : Integrable (fun p => ∫ q, f q ∂K p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hK
    simpa using hK.integral_comp
  rw [nested_integral_bind mu K K.measurable f hK]
  exact integral_mono_ae hiK hg hstep

/-- Finite nonnegative terminal spends telescope through successive active and waiting values. -/
theorem enlarged_terminal_values_telescope (U R D : ℕ → ℝ)
    (hU : ∀ n, 0 ≤ U n) (ha : ∀ n, D n + R n ≤ U n)
    (hw : ∀ n, U (n + 1) ≤ R n) (N : ℕ) :
    (∑ n ∈ Finset.range N, D n) ≤ U 0 := by
  have hh : ∀ N, (∑ n ∈ Finset.range N, D n) + U N ≤ U 0 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith [ha N, hw N]
  linarith [hh N, hU N]



/-- Every finite sum of actual enlarged terminal pieces is finite. -/
instance enlargedActiveTerminal_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (N : ℕ) (b : ℝ) :
    IsFiniteMeasure (enlargedActiveTerminal hH hLE hlam hLam A c J s T P N b) := by
  change IsFiniteMeasure (∑ n ∈ Finset.range N,
    enlargedTerminalFamilyKernel hH hLE hlam hLam A c J b ∘ₘ
      enlargedVisitEntrance hH hLE hlam hLam A c J s T P n)
  infer_instance



/-- At every observation time in the source window, the genuine finite terminal sum is
bounded by the FULL-SPACE terminal measure. Initial-time entrance atoms are retained. -/
theorem enlarged_active_terminal_le_fullspace
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T)
    (hJ : closure c.active ⊆ J.carrier) (N : ℕ) (b : ℝ)
    (hb : P.time ≤ b) (hBT : b ≤ T) :
    enlargedActiveTerminal hH hLE hlam hLam A c J s T P N b ≤
      enlargedFullSpaceTerminal hH hLE hlam hLam A P b        := by
  have enlargedStoppedPotential_integrable (u : Point → ℝ) (hc : ContinuousOn u {p | p.time ≤ b}) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ p, p.time ≤ b → |u p| ≤ M) (mu : Measure Point) [IsFiniteMeasure mu] :
      Integrable (enlargedStoppedPotential b u) mu := by
    have enlargedStoppedPotential_measurable : Measurable (enlargedStoppedPotential b u) :=
      hc.measurable_piecewise continuousOn_const
          (isClosed_le continuous_time continuous_const).measurableSet
    apply Integrable.mono' (integrable_const M)
      (enlargedStoppedPotential_measurable).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro p
    rw [Real.norm_eq_abs]
    unfold enlargedStoppedPotential
    split
    · exact hb p ‹p.time ≤ b›
    · simpa using hM
  have enlarged_waiting_stopped_step (H : FiniteIntervalUnion) (u : Point → ℝ) (hphi : IsKineticC112On u {p | p.time < b}) (hc : ContinuousOn u {p | p.time ≤ b}) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ p, p.time ≤ b → |u p| ≤ M) (hop : ∀ p, p.time < b → forwardScalarOperator A.a u p = 0) (hn : ∀ p, p.time ≤ b → 0 ≤ u p) (p : Point) (B : Set Point) (_hB : MeasurableSet B) :
      (∫ q, enlargedStoppedPotential b u q
      ∂(enlargedVisitExitKernel hH hLE hlam hLam A H T p).restrict B) ≤
        {q : Point | q.time < b}.indicator (enlargedStoppedPotential b u) p := by
    have enlarged_exit_stopped_integral_le :
        (∫ q, enlargedStoppedPotential b u q
        ∂enlargedVisitExitKernel hH hLE hlam hLam A H T p) ≤
          enlargedStoppedPotential b u p := by
      have enlarged_exit_stopped_integral_zero (hp : b ≤ p.time) :
          (∫ q, enlargedStoppedPotential b u q
          ∂enlargedVisitExitKernel hH hLE hlam hLam A H T p) = 0 := by
        apply integral_eq_zero_of_ae
        exact (enlargedVisitExitKernel_ae_time_gt hH hLE hlam hLam A H T p).mono
          fun q hq => ite_eq_right (not_le_of_gt (hp.trans_lt hq))
      have enlarged_stripExit_stopped_potential_le (H : Interval) (e : StripPole H ⊤) (hb : e.1.time < b) :
          (∫ p, enlargedStoppedPotential b u p
          ∂stripExit hH hLE hlam hLam A H T (stripPoleFinite H e T (hb.trans_le hBT))) ≤
          u e.1 := by
        let S : Set Point := {p | p.time ≤ b}
        have hS : MeasurableSet S := (isClosed_le continuous_time continuous_const).measurableSet
        let E := stripExit hH hLE hlam hLam A H b (stripPoleFinite H e b hb)
        have hs :=
          (stripExitOfRealization_ae_closed_future hH hlam hLam A H
            (stripEvolution hH hLE hlam hLam A H)
            (stripEvolution_spec hH hLE hlam hLam A H) b (stripPoleFinite H e b hb)).mono
              fun _ hp => hp.2.1
        have hint := enlargedStoppedPotential_integrable u hc M hM hbound E
        have heq : enlargedStoppedPotential b u =ᵐ[E] u := hs.mono fun p hp => ite_eq_left hp
        have hdom : (stripExit hH hLE hlam hLam A H T
            (stripPoleFinite H e T (hb.trans_le hBT))).restrict S ≤ E := by
          rcases eq_or_lt_of_le hBT with rfl | hlt
          · exact Measure.restrict_le_self
          · exact enlarged_stripExit_early_closed_le hH hLE hlam hLam A H e b T hb hlt
        have hnn := hs.mono fun p hp => hn p hp
        have hm := integral_mono_measure hdom hnn (hint.congr heq)
        have hsub : reconstructionStrip H (e.1.time - 1) b ⊆ {p | p.time < b} :=
          fun _ hp => hp.2.1
        have hr : IsKineticC112On u (reconstructionStrip H (e.1.time - 1) b) := by
          rcases hphi with ⟨hc0, ht, hx, hv, htc, hxc, hvc, hvvc⟩
          exact ⟨hc0.mono hsub, fun p hp => ht p (hsub hp), fun p hp => hx p (hsub hp),
            fun p hp => hv p (hsub hp), htc.mono hsub, hxc.mono hsub, hvc.mono hsub,
            hvvc.mono hsub⟩
        have hi := strip_identity_C112 hH hLE hlam hLam A H (e.1.time - 1) b
          (by linarith) (stripPoleFinite H e b hb) (by change e.1.time - 1 < e.1.time; linarith)
          u hr
            (hc.mono fun p hp => by
              rcases hp with hp | hp
              · exact hp.2.1.le
              · rcases hp with hp | hp
                · exact hp.1.le
                · exact hp.2.1.le)
            ⟨M, fun p hp => ⟨hbound p hp.2.1.le, by rw [hop p hp.2.1, abs_zero]; exact hM⟩⟩
        have hz : (∫ p, forwardScalarOperator A.a u p
            ∂stripGreen hH hLE hlam hLam A H b (stripPoleFinite H e b hb)) = 0 := by
          apply integral_eq_zero_of_ae
          exact (stripGreenOfKernel_ae_mem_stripPast H _ b (stripPoleFinite H e b hb)).mono
            fun p hp => hop p hp.1
        rw [hz, sub_zero] at hi
        rw [← hi] at hm
        change (∫ p, S.indicator u p ∂_) ≤ u e.1
        rw [integral_indicator hS]
        exact hm
      by_cases hp : p ∈ enlargedVisitPoleSet H T
      · by_cases hb : p.time < b
        · let e := enlargedVisitPole H T ⟨p, hp⟩
          let I := H.component (finiteUnionPoleIndex H T e)
          let ep : StripPole I ⊤ := ⟨p, WithTop.coe_lt_top _,
            (finiteUnionComponentPole H T e).2.2⟩
          have hi := enlarged_stripExit_stopped_potential_le I ep
            hb
          change (∫ q, enlargedStoppedPotential b u q ∂
            (if ht : p ∈ enlargedVisitPoleSet H T then _ else 0)) ≤ _
          rw [dite_eq_left hp]
          change (∫ q, enlargedStoppedPotential b u q ∂stripExit hH hLE hlam hLam A I T _) ≤ _
          rw [show enlargedStoppedPotential b u p = u p from ite_eq_left hb.le]
          exact hi
        · rw [enlarged_exit_stopped_integral_zero (le_of_not_gt hb)]
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
    by_cases hp : p.time < b
    · rw [show {q : Point | q.time < b}.indicator (enlargedStoppedPotential b u) p =
        enlargedStoppedPotential b u p from
        Set.indicator_of_mem (show p ∈ {q : Point | q.time < b} from hp) _]
      have hi := enlargedStoppedPotential_integrable u hc M hM hbound
        (enlargedVisitExitKernel hH hLE hlam hLam A H T p)
      have hnV : 0 ≤ᵐ[enlargedVisitExitKernel hH hLE hlam hLam A H T p]
          enlargedStoppedPotential b u := Filter.Eventually.of_forall fun q => by
        unfold enlargedStoppedPotential
        split
        · exact hn q ‹q.time ≤ b›
        · exact le_rfl
      exact (integral_mono_measure Measure.restrict_le_self hnV hi).trans
        (enlarged_exit_stopped_integral_le)
    · rw [show {q : Point | q.time < b}.indicator (enlargedStoppedPotential b u) p =
        0 from Set.indicator_of_notMem (show p ∉ {q : Point | q.time < b} from hp) _]
      apply le_of_eq
      apply integral_eq_zero_of_ae
      exact (ae_restrict_of_ae
        (enlargedVisitExitKernel_ae_time_gt hH hLE hlam hLam A H T p)).mono
          fun q hq => ite_eq_right (not_le_of_gt ((le_of_not_gt hp).trans_lt hq))
  have enlarged_active_stopped_step (u : Point → ℝ) (hphi : IsKineticC112On u {p | p.time < b}) (hc : ContinuousOn u {p | p.time ≤ b}) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ p, p.time ≤ b → |u p| ≤ M) (hop : ∀ p, p.time < b → forwardScalarOperator A.a u p = 0) (hn : ∀ p, p.time ≤ b → 0 ≤ u p) (p : Point) (hv : p.velocity 0 ∈ c.active) (B : Set Point) (hB : MeasurableSet B) (hsub : B ⊆ {q | q.time < b}) :
      (∫ q, enlargedStoppedPotential b u q
      ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) +
    (∫ q, enlargedStoppedPotential b u q
      ∂(enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T p).restrict B) ≤
        enlargedStoppedPotential b u p := by
    have enlarged_terminal_and_early_exit_le (hb : p.time < b) :
        enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p +
        (enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T p).restrict B ≤
          enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b p := by
      have enlarged_stripExit_cap_and_early_le (H : Interval) (e : StripPole H ⊤) (b : ℝ) (T : ℝ) (hb : e.1.time < b) (hBT : b ≤ T) (B : Set Point) (hB : MeasurableSet B) (hsub : B ⊆ {p | p.time < b}) :
          (stripExit hH hLE hlam hLam A H b (stripPoleFinite H e b hb)).restrict
          {p | p.time = b} +
        (stripExit hH hLE hlam hLam A H T
          (stripPoleFinite H e T (hb.trans_le hBT))).restrict B ≤
            stripExit hH hLE hlam hLam A H b (stripPoleFinite H e b hb) := by
        let E := stripExit hH hLE hlam hLam A H b (stripPoleFinite H e b hb)
        have hpre : MeasurableSet {p : Point | p.time < b} :=
          (isOpen_lt continuous_time continuous_const).measurableSet
        have he := stripExit_horizon_consistency hH hLE hlam hLam A H e
          T b (hb.trans_le hBT) hb b hBT le_rfl
        have heB := congrArg (fun rho => rho.restrict B) he
        simp only [Measure.restrict_restrict hB, inter_eq_left.mpr hsub] at heB
        rw [heB]
        have hd : Disjoint {p : Point | p.time = b} {p | p.time < b} := by
          apply Set.disjoint_left.mpr
          intro p hp ht
          exact (ne_of_lt ht) hp
        calc
          _ ≤ E.restrict {p | p.time = b} + E.restrict {p | p.time < b} :=
            add_le_add le_rfl (Measure.restrict_mono_set E hsub)
          _ = E.restrict ({p | p.time = b} ∪ {p | p.time < b}) :=
            (Measure.restrict_union hd hpre).symm
          _ ≤ E := Measure.restrict_le_self
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
      exact enlarged_stripExit_cap_and_early_le c.activeInterval ep b T
        hb hBT B hB hsub
    have enlarged_active_stopped_step_earlier (hb : p.time < b) :
        (∫ q, enlargedStoppedPotential b u q
        ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) +
      (∫ q, enlargedStoppedPotential b u q
        ∂(enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T p).restrict B) ≤
          u p := by
      have enlarged_stripExit_potential_identity (H : Interval) (e : StripPole H ⊤) (b : ℝ) (hb : e.1.time < b) (u : Point → ℝ) (hphi : IsKineticC112On u {p | p.time < b}) (hc : ContinuousOn u {p | p.time ≤ b}) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ p, p.time ≤ b → |u p| ≤ M) (hop : ∀ p, p.time < b → forwardScalarOperator A.a u p = 0) :
          (∫ p, u p ∂stripExit hH hLE hlam hLam A H b (stripPoleFinite H e b hb)) = u e.1 := by
        have hsub : reconstructionStrip H (e.1.time - 1) b ⊆ {p | p.time < b} :=
          fun _ hp => hp.2.1
        have hr : IsKineticC112On u (reconstructionStrip H (e.1.time - 1) b) := by
          rcases hphi with ⟨hc0, ht, hx, hv, htc, hxc, hvc, hvvc⟩
          exact ⟨hc0.mono hsub, fun p hp => ht p (hsub hp), fun p hp => hx p (hsub hp),
            fun p hp => hv p (hsub hp), htc.mono hsub, hxc.mono hsub, hvc.mono hsub,
            hvvc.mono hsub⟩
        have hi := strip_identity_C112 hH hLE hlam hLam A H (e.1.time - 1) b
          (by linarith) (stripPoleFinite H e b hb) (by change e.1.time - 1 < e.1.time; linarith)
          u hr
            (hc.mono fun p hp => by
              rcases hp with hp | hp
              · exact hp.2.1.le
              · rcases hp with hp | hp
                · exact hp.1.le
                · exact hp.2.1.le)
            ⟨M, fun p hp => ⟨hbound p hp.2.1.le, by rw [hop p hp.2.1, abs_zero]; exact hM⟩⟩
        have hz : (∫ p, forwardScalarOperator A.a u p
            ∂stripGreen hH hLE hlam hLam A H b (stripPoleFinite H e b hb)) = 0 := by
          apply integral_eq_zero_of_ae
          exact (stripGreenOfKernel_ae_mem_stripPast H _ b (stripPoleFinite H e b hb)).mono
            fun p hp => hop p hp.1
        rw [hz, sub_zero] at hi
        exact hi.symm
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
      have hnn : 0 ≤ᵐ[E] V := hs.mono fun q hq => by
        change 0 ≤ (if q.time ≤ b then u q else 0)
        rw [ite_eq_left hq]
        exact hn q hq
      have hd := enlarged_terminal_and_early_exit_le hb
      rw [he] at hd
      have hm := integral_mono_measure hd hnn (enlargedStoppedPotential_integrable u hc M hM hbound E)
      rw [integral_add_measure (enlargedStoppedPotential_integrable u hc M hM hbound (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p)) (enlargedStoppedPotential_integrable u hc M hM hbound ((enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T p).restrict B))] at hm
      have heq : V =ᵐ[E] u := hs.mono fun _ hq => ite_eq_left hq
      rw [integral_congr_ae heq, enlarged_stripExit_potential_identity
        c.activeInterval ep b hb u hphi hc M hM hbound hop] at hm
      exact hm
    by_cases hb : p.time < b
    · rw [show enlargedStoppedPotential b u p = u p from ite_eq_left hb.le]
      exact enlarged_active_stopped_step_earlier hb
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
  have enlarged_exists_fullspace_potential (F : BoundedBorel (EvolutionAmbientState 1)) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hF0 : ∀ z, 0 ≤ F z) :
      ∃ u : Point → ℝ, IsKineticC112On u {p | p.time < b} ∧
      ContinuousOn u {p | p.time ≤ b} ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ p, p.time ≤ b → |u p| ≤ M) ∧
      (∀ p, p.time < b → forwardScalarOperator A.a u p = 0) ∧
      (∀ p, p.time ≤ b → 0 ≤ u p) ∧
      (∀ p, p.time = b → u p = F (p.velocity, p.position)) ∧
      (∀ p (hp : p.time ≤ b), u p = ∫ z, F z ∂
        (fullSpaceEvolution hH hLE hlam hLam A).2.master
          (wholeSpaceQuery p.time b hp p.velocity p.position)) := by
    obtain ⟨v, hv, hr⟩ := fullspace_bounded_smooth_solution hH hlam hLam A
      (fullSpaceEvolution hH hLE hlam hLam A)
      (fullSpaceEvolution_spec hH hLE hlam hLam A) b F hF
    have hwhole (t : ℝ) : movingDomain autonomousWholeDomain (fun _ => 0) t = univ :=
      movingDomain_wholeSpace 1 t
    let u := v ∘ sectionTwoPoint
    have hm (p : Point) (hp : p.time ≤ b) : sectionTwoPoint p ∈
        evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) b := by
      refine ⟨hp, ?_⟩
      rw [hwhole, closure_univ]
      trivial
    have hc : ContinuousOn u {p | p.time ≤ b} := hv.2.1.comp
      (continuous_sectionTwoPoint 1).continuousOn (fun p hp => hm p hp)
    have hs : IsKineticC112On u {p | p.time < b} := by
      apply nested_raw_isKineticC112On (isOpen_lt continuous_time continuous_const)
      let g : ℝ × (PDE.Vec 1 × PDE.Vec 1) → ℝ × (PDE.Vec 1 × PDE.Vec 1) :=
        fun q => (q.1, q.2.2, q.2.1)
      have hg : ContDiff ℝ (⊤ : ℕ∞) g := by unfold g; fun_prop
      have hmaps : MapsTo g ((KineticPoint.equivProd 1) '' {p : Point | p.time < b})
          (evolutionPastInteriorRaw autonomousWholeDomain (fun _ => 0) b) := by
        rintro q ⟨p, hp, rfl⟩
        refine ⟨hp, ?_⟩
        rw [hwhole]
        trivial
      exact hv.2.2.1.comp hg.contDiffOn hmaps
    have hrep (p : Point) (hp : p.time ≤ b) : u p = ∫ z, F z ∂
        (fullSpaceEvolution hH hLE hlam hLam A).2.master
          (wholeSpaceQuery p.time b hp p.velocity p.position) :=
      hr (wholeSpaceQuery p.time b hp p.velocity p.position) rfl
    refine ⟨u, hs, hc, ?_, ?_, ?_, ?_, hrep⟩
    · obtain ⟨M, hM, hb⟩ := hv.1
      exact ⟨M, hM, fun p hp => hb _ (hm p hp)⟩
    · intro p hp
      have hmem : sectionTwoPoint p ∈ evolutionPastOpenCylinder
          autonomousWholeDomain (fun _ => 0) b := by
        refine ⟨hp, ?_⟩
        rw [hwhole]
        trivial
      have ho := hv.2.2.2.1 (sectionTwoPoint p) hmem
      have he : v = u ∘ sectionTwoPoint := by
        funext q
        exact congrArg v (sectionTwoPoint_involutive q).symm
      rw [he, reconstruction_scalar_operator_swap, sectionTwoPoint_involutive p] at ho
      exact ho
    · intro p hp
      rw [hrep p hp]
      exact integral_nonneg hF0
    · intro p hp
      exact hv.2.2.2.2.1 (sectionTwoPoint p) ⟨hp, by
        rw [hwhole, closure_univ]
        trivial⟩
  have enlargedActiveTerminal_ae_time :
      ∀ᵐ q ∂enlargedActiveTerminal hH hLE hlam hLam A c J s T P N b, q.time = b := by
    have enlarged_terminal_family_ae_time (p : Point) :
        ∀ᵐ q ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p, q.time = b := by
      unfold enlargedActiveTerminalFamily
      split
      · rename_i hp
        exact (ae_dirac_iff (isClosed_eq continuous_time continuous_const).measurableSet).mpr hp.1
      · exact ae_restrict_mem (isClosed_eq continuous_time continuous_const).measurableSet
    apply ae_finsetSum_measure_iff.mpr
    intro n _
    change ∀ᵐ q ∂(enlargedTerminalFamilyKernel hH hLE hlam hLam A c J b ∘ₘ
      enlargedVisitEntrance hH hLE hlam hLam A c J s T P n), q.time = b
    apply Measure.ae_comp_of_ae_ae (isClosed_eq continuous_time continuous_const).measurableSet
    exact Filter.Eventually.of_forall fun p =>
      enlarged_terminal_family_ae_time p
  have enlarged_terminal_stopped_potential_le (u : Point → ℝ) (hphi : IsKineticC112On u {p | p.time < b}) (hc : ContinuousOn u {p | p.time ≤ b}) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ p, p.time ≤ b → |u p| ≤ M) (hop : ∀ p, p.time < b → forwardScalarOperator A.a u p = 0) (hn : ∀ p, p.time ≤ b → 0 ≤ u p) :
      (∫ q, enlargedStoppedPotential b u q
      ∂enlargedActiveTerminal hH hLE hlam hLam A c J s T P N b) ≤
        enlargedStoppedPotential b u P := by
    let V := enlargedStoppedPotential b u
    let D : Set Point := {q | q.time < b}
    have hD : MeasurableSet D := (isOpen_lt continuous_time continuous_const).measurableSet
    let Sin := visitBoundary s T (visitEntranceInterval c) J
    let Sout := visitBoundary s T (visitActiveInterval c) J
    have hi : MeasurableSet Sin := measurableSet_visitBoundary s T _ J
    have ho : MeasurableSet Sout := measurableSet_visitBoundary s T _ J
    let EA := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T
    let EW := enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) T
    let KA := EA.restrict (ho.inter hD)
    let KW := EW.restrict hi
    let KT := enlargedTerminalFamilyKernel hH hLE hlam hLam A c J b
    let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P
    let beta := enlargedVisitOutgoing hH hLE hlam hLam A c J s T P
    let U := fun n => ∫ p, V p ∂gamma n
    let R := fun n => ∫ p, V p ∂(beta n).restrict D
    let W := fun n => ∫ p, V p ∂KT ∘ₘ gamma n
    have hint (mu : Measure Point) [IsFiniteMeasure mu] : Integrable V mu :=
      enlargedStoppedPotential_integrable u hc M hM hbound mu
    have hnV (p : Point) : 0 ≤ V p := by
      dsimp [V, enlargedStoppedPotential]
      split
      · exact hn p ‹p.time ≤ b›
      · exact le_rfl
    have hka (n : ℕ) : KA ∘ₘ gamma n = (beta n).restrict D := by
      change (gamma n).bind (fun p => (EA p).restrict (Sout ∩ D)) = _
      rw [← nested_bind_restrict (gamma n) EA EA.measurable _ (ho.inter hD)]
      change (EA ∘ₘ gamma n).restrict (Sout ∩ D) =
        ((EA ∘ₘ gamma n).restrict Sout).restrict D
      rw [Measure.restrict_restrict hD, inter_comm]
    have hkw (n : ℕ) : KW ∘ₘ beta n = gamma (n + 1) := by
      change (beta n).bind (fun p => (EW p).restrict Sin) = _
      rw [← nested_bind_restrict (beta n) EW EW.measurable Sin hi]
      rfl
    have ha (n : ℕ) : W n + R n ≤ U n := by
      have hp : ∀ᵐ p ∂gamma n, p.velocity 0 ∈ c.active :=
        (enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n).mono
          fun _ hp => enlarged_closedEntrance_subset_active c hp.2.2
      have hh := enlarged_integral_kernel_pair_le KT KA (gamma n) V V
        (hint _) (hint _) (hint _) (hp.mono fun p hp =>
          enlarged_active_stopped_step u hphi hc M hM
            hbound hop hn p hp (Sout ∩ D) (ho.inter hD) inter_subset_right)
      rw [hka n] at hh
      exact hh
    have hw (n : ℕ) : U (n + 1) ≤ R n := by
      have hh := enlarged_integral_kernel_le KW (beta n) V (D.indicator V)
        (hint _) ((hint _).indicator hD) (Filter.Eventually.of_forall fun p =>
          enlarged_waiting_stopped_step (visitWaitingUnion c J)
            u hphi hc M hM hbound hop hn p Sin hi)
      rw [hkw n, integral_indicator hD] at hh
      exact hh
    have hinit : U 0 ≤ V P := by
      change (∫ p, V p ∂visitInitial P (visitEntranceInterval c) Sin EW) ≤ V P
      unfold visitInitial
      split
      · rw [integral_dirac]
      · have hh := enlarged_waiting_stopped_step (visitWaitingUnion c J) u hphi hc M hM hbound hop hn P Sin hi
        apply hh.trans
        by_cases hp : P ∈ D
        · rw [Set.indicator_of_mem hp]
        · rw [Set.indicator_of_notMem hp]
          exact hnV P
    change (∫ p, V p ∂∑ n ∈ Finset.range N, KT ∘ₘ gamma n) ≤ V P
    rw [integral_finsetSum_measure (fun n _ => hint (KT ∘ₘ gamma n))]
    exact (enlarged_terminal_values_telescope U R W (fun n => integral_nonneg hnV) ha hw N).trans hinit
  have enlargedFullSpace_native_terminal_integral (F : Point → ℝ) (hF : Measurable F) :
      (∫ w, F ⟨b, w.2, w.1⟩
      ∂(fullSpaceEvolution hH hLE hlam hLam A).2.master
        (wholeSpaceQuery P.time b hb P.velocity P.position)) =
      ∫ z, F (enlargedTerminalPoint b z)
        ∂kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal (b - P.time))
          (P.position 0, P.velocity 0) := by
    let E := fullSpaceEvolution hH hLE hlam hLam A
    let q := wholeSpaceQuery P.time b hb P.velocity P.position
    have hq : autonomousQueryShift (-P.time) q =
        wholeQuery (Real.toNNReal (b - P.time)) (P.position 0, P.velocity 0) := by
      apply Subtype.ext
      dsimp [autonomousQueryShift, q, wholeQuery, wholeSpaceQuery]
      rw [max_eq_left (sub_nonneg.mpr hb)]
      have hx : (fun _ => P.position 0) = P.position := by
        funext i
        exact congrArg P.position (Subsingleton.elim 0 i)
      have hv : (fun _ => P.velocity 0) = P.velocity := by
        funext i
        exact congrArg P.velocity (Subsingleton.elim 0 i)
      rw [hx, hv]
      congr 1
      ring
    have hk := fullspace_kernel_timeShift A E
      (fullSpaceEvolution_spec hH hLE hlam hLam A) (-P.time) q
    rw [hq] at hk
    change (∫ w, F ⟨b, w.2, w.1⟩ ∂E.2.master q) =
      ∫ z, F (enlargedTerminalPoint b z)
        ∂(E.2.master (wholeQuery (Real.toNNReal (b - P.time))
          (P.position 0, P.velocity 0))).map nativeToXV
    change _ = ∫ z, (F ∘ enlargedTerminalPoint b) z ∂_
    rw [(integral_map nativeToXV_measurable.aemeasurable (hF.comp (enlargedTerminalPoint_measurable b)).aestronglyMeasurable (μ := E.2.master (wholeQuery (Real.toNNReal (b - P.time)) (P.position 0, P.velocity 0)))), hk]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro w
    change F ⟨b, w.2, w.1⟩ = F (enlargedTerminalPoint b (nativeToXV w))
    congr 1
    apply KineticPoint.ext
    · rfl
    · funext i
      exact congrArg w.2 (Subsingleton.elim i 0)
    · funext i
      exact congrArg w.1 (Subsingleton.elim i 0)
  let mu := enlargedActiveTerminal hH hLE hlam hLam A c J s T P N b
  let nu := enlargedFullSpaceTerminal hH hLE hlam hLam A P b
  have : IsFiniteMeasure nu := ⟨(enlargedFullSpaceTerminal_mass_le_one
    hH hLE hlam hLam A P b).trans_lt ENNReal.one_lt_top⟩
  apply enlarged_physical_measure_le
  intro f hf0
  let G : EvolutionAmbientState 1 → ℝ :=
    fun z => f.1 ((evolutionProdCLE 1).symm (b, z.1, z.2))
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := f.2.1.comp
    ((evolutionProdCLE 1).symm.contDiff.comp
      (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)))
  obtain ⟨C, hC⟩ := f.2.2.exists_bound_of_continuous f.2.1.continuous
  let F : BoundedBorel (EvolutionAmbientState 1) :=
    ⟨G, hG.continuous.measurable, max C 0, le_max_right _ _, fun z => by
      have hx : |G z| ≤ C := by
        simpa only [Real.norm_eq_abs] using (hC ((evolutionProdCLE 1).symm (b, z.1, z.2)))
      exact hx.trans (le_max_left _ _)⟩
  have hF0 : ∀ z, 0 ≤ F z := fun z => hf0 ⟨b, z.2, z.1⟩
  obtain ⟨u, hphi, hc, ⟨M, hM, hbound⟩, hop, hn, ht, hr⟩ :=
    enlarged_exists_fullspace_potential F hG hF0
  have hp : enlargedStoppedPotential b u =ᵐ[mu] exitProbePhysical f := by
    filter_upwards [enlargedActiveTerminal_ae_time]
      with p hp
    rw [show enlargedStoppedPotential b u p = u p from ite_eq_left hp.le, ht p hp]
    change f.1 ((evolutionProdCLE 1).symm (b, p.velocity, p.position)) =
      f.1 ((evolutionProdCLE 1).symm (p.time, p.velocity, p.position))
    rw [hp]
  have hh := enlarged_terminal_stopped_potential_le u hphi hc M hM hbound hop hn
  change (∫ p, enlargedStoppedPotential b u p ∂mu) ≤ enlargedStoppedPotential b u P at hh
  rw [integral_congr_ae hp, show enlargedStoppedPotential b u P = u P from ite_eq_left hb,
    hr P hb] at hh
  have he : (∫ z, F z ∂(fullSpaceEvolution hH hLE hlam hLam A).2.master
      (wholeSpaceQuery P.time b hb P.velocity P.position)) =
      ∫ p, exitProbePhysical f p ∂nu := by
    have hi := enlargedFullSpace_native_terminal_integral
      (exitProbePhysical f) (exitProbePhysical_continuous_compact f).1.measurable
    change (∫ z, F z ∂(fullSpaceEvolution hH hLE hlam hLam A).2.master
      (wholeSpaceQuery P.time b hb P.velocity P.position)) = _ at hi
    unfold nu enlargedFullSpaceTerminal
    rw [integral_map (enlargedTerminalPoint_measurable b).aemeasurable
      (exitProbePhysical_continuous_compact f).1.measurable.aestronglyMeasurable]
    exact hi
  rw [he] at hh
  exact hh

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

