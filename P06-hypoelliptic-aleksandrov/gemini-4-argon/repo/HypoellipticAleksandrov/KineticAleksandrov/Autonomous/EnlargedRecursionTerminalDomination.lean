module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ActiveTerminalDominationPotential
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ActiveTerminalDominationSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ActiveTerminalDominationFullSpace
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCapacity
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ActiveTerminalDominationKernel
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ActiveTerminalDominationIntegration
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionSupport
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassSupport

/-! # Full-space domination of the actual enlarged terminal visits -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory Parabolic
open SectionTwo TheoremA Evolution
open scoped Classical

/- At every observation time in the source window, the genuine finite terminal sum is
bounded by the FULL-SPACE terminal measure. Initial-time entrance atoms are retained. -/
theorem enlarged_active_terminal_le_fullspace
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T)
    (hJ : closure c.active ⊆ J.carrier) (N : ℕ) (b )
    (hb : P.time ≤ b) (hBT : b ≤ T) :
    enlargedActiveTerminal hH hLE hlam hLam A c J s T P N b ≤
      enlargedFullSpaceTerminal hH hLE hlam hLam A P b := by
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
    enlarged_exists_fullspace_potential hH hLE hlam hLam A b F hG hF0
  have hp : enlargedStoppedPotential b u =ᵐ[mu] exitProbePhysical f := by
    have _h_xinl_1 : ∀ᵐ q ∂enlargedActiveTerminal hH hLE hlam hLam A c J s T P N b, q.time = b := by
      apply ae_finsetSum_measure_iff.mpr
      intro n _
      change ∀ᵐ q ∂(enlargedTerminalFamilyKernel hH hLE hlam hLam A c J b ∘ₘ
        enlargedVisitEntrance hH hLE hlam hLam A c J s T P n), q.time = b
      apply Measure.ae_comp_of_ae_ae (isClosed_eq continuous_time continuous_const).measurableSet
      exact Filter.Eventually.of_forall fun p =>
        enlarged_terminal_family_ae_time hH hLE hlam hLam A c J b p
    filter_upwards [_h_xinl_1]
      with p hp
    rw [show enlargedStoppedPotential b u p = u p from ite_eq_left hp.le, ht p hp]
    change f.1 ((evolutionProdCLE 1).symm (b, p.velocity, p.position)) =
      f.1 ((evolutionProdCLE 1).symm (p.time, p.velocity, p.position))
    rw [hp]
  have hh : (∫ q, enlargedStoppedPotential b u q
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
      enlargedStoppedPotential_integrable b u hc M hM hbound mu
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
          enlarged_active_stopped_step hH hLE hlam hLam A c J b T hBT hJ u hphi hc M hM
            hbound hop hn p hp (Sout ∩ D) (ho.inter hD) inter_subset_right)
      rw [hka n] at hh
      exact hh
    have hw (n : ℕ) : U (n + 1) ≤ R n := by
      have hh := enlarged_integral_kernel_le KW (beta n) V (D.indicator V)
        (hint _) ((hint _).indicator hD) (Filter.Eventually.of_forall fun p =>
          enlarged_waiting_stopped_step hH hLE hlam hLam A (visitWaitingUnion c J) b T hBT
            u hphi hc M hM hbound hop hn p Sin hi)
      rw [hkw n, integral_indicator hD] at hh
      exact hh
    have hinit : U 0 ≤ V P := by
      change (∫ p, V p ∂visitInitial P (visitEntranceInterval c) Sin EW) ≤ V P
      unfold visitInitial
      split
      · rw [integral_dirac]
      · have hh := enlarged_waiting_stopped_step hH hLE hlam hLam A (visitWaitingUnion c J)
          b T hBT u hphi hc M hM hbound hop hn P Sin hi
        apply hh.trans
        by_cases hp : P ∈ D
        · rw [Set.indicator_of_mem hp]
        · rw [Set.indicator_of_notMem hp]
          exact hnV P
    have hsum := (enlarged_terminal_values_telescope U R W
      (fun n => integral_nonneg hnV) ha hw N).trans hinit
    change (∫ p, V p ∂∑ n ∈ Finset.range N, KT ∘ₘ gamma n) ≤ V P
    rw [integral_finsetSum_measure (fun n _ => hint (KT ∘ₘ gamma n))]
    exact hsum
  change (∫ p, enlargedStoppedPotential b u p ∂mu) ≤ enlargedStoppedPotential b u P at hh
  rw [integral_congr_ae hp, show enlargedStoppedPotential b u P = u P from ite_eq_left hb,
    hr P hb] at hh
  have he : (∫ z, F z ∂(fullSpaceEvolution hH hLE hlam hLam A).2.master
      (wholeSpaceQuery P.time b hb P.velocity P.position)) =
      ∫ p, exitProbePhysical f p ∂nu := by
    have hi := enlargedFullSpace_native_terminal_integral hH hLE hlam hLam A P b hb
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
