module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FullSpaceIdentification
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Autonomy
import Mathlib.Tactic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory HypoellipticAleksandrov.KineticAleksandrov.SectionTwo ProbabilityTheory
open scoped ENNReal

/-- Every stationary velocity interval is contained in the full velocity domain. -/
theorem strip_subset_fullspace (H : Interval) (t : ℝ) :
    movingDomain (intervalDomain H) (fun _ => 0) t ⊆
      movingDomain autonomousWholeDomain (fun _ => 0) t := by
  change _ ⊆ movingDomain (wholeSpace 1) (fun _ => 0) t
  rw [movingDomain_wholeSpace]
  exact subset_univ _


/-- Every supplied strip realization is measure dominated by the supplied full-space one. -/
theorem strip_kernel_le_fullspace
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (H : Interval) (G : StripEvolution H) (hG : IsStripEvolution A H G) :
    MovingFiberKernel.IsZeroExtensionDominatedBy G.2 E.2 (strip_subset_fullspace H)  := by
  have fullspace_domainMonotone :
      IsDomainMonotoneEvolution autonomousWholeDomain (fun _ => 0)
      (evolutionCoefficient A.a) (identityDrift 1) E.2 := by
    obtain ⟨S, K, hc, -, -, -, -, hi, -, -, -, -, he, hcomp, -, hmono, -⟩ :=
      exists_terminalEvolution_of_classical hLE hH 1 (by omega) lam Lam 1 1
        hlam hLam one_pos le_rfl autonomousWholeDomain (fun _ => 0)
        (evolutionCoefficient A.a) (identityDrift 1) autonomousWholeDomain_admissible
        (zeroCurve_piecewiseC1 1) (evolutionCoefficient_smooth A)
        (evolutionCoefficient_symmetric A.a) (evolutionCoefficient_bounds A)
        (identityDrift_smooth 1) (identityDrift_bounds 1).1 (identityDrift_bounds 1).2
    simpa only [(fullSpaceEvolution_unique A E (S, K) hE ⟨hc, hi, he, hcomp⟩)] using hmono
  exact domainMonotone_of_realizes (evolutionCoefficient A.a) (identityDrift 1) E.2
    (fullspace_domainMonotone)
    (intervalDomain H) (fun _ => 0) (intervalDomain_admissible H)
    (zeroCurve_piecewiseC1 1) (strip_subset_fullspace H) G.1 G.2 hG


/-- Reinserting physical time is a measurable coordinate map. -/
theorem enlargedTerminalPoint_measurable (b : ℝ) : Measurable (enlargedTerminalPoint b) := by
  unfold enlargedTerminalPoint
  exact (KineticPoint.measurable_equivProd_symm 1).comp
    (measurable_const.prodMk ((measurable_pi_iff.mpr (fun _ => measurable_fst)).prodMk
      (measurable_pi_iff.mpr (fun _ => measurable_snd))))

/-- The full-space occupation has the literal iterated physical kernel action. -/
theorem enlargedFullSpaceOccupation_lintegral
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (P : Point) (T : ℝ)
    (F : Point → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂enlargedFullSpaceOccupation hH hLE hlam hLam A P T) =
      ∫⁻ t in Ioc 0 T, ∫⁻ z, F (enlargedTerminalPoint (P.time + t) z)
        ∂kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
          (P.position 0, P.velocity 0) := by
  have hm : Measurable (fun tz : ℝ × Z => enlargedTerminalPoint (P.time + tz.1) tz.2) := by
    unfold enlargedTerminalPoint
    exact (KineticPoint.measurable_equivProd_symm 1).comp
      ((measurable_const.add measurable_fst).prodMk
        ((measurable_pi_iff.mpr (fun _ => measurable_fst.comp measurable_snd)).prodMk
          (measurable_pi_iff.mpr (fun _ => measurable_snd.comp measurable_snd))))
  unfold enlargedFullSpaceOccupation
  rw [lintegral_map hF hm]
  exact Measure.lintegral_compProd (hF.comp hm)

/-- Full-space occupation can equally be integrated over the literal elapsed-time subtype. -/
theorem enlargedFullSpaceOccupation_elapsed_lintegral
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (P : Point) (T : ℝ) (hT : 0 < T)
    (F : Point → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂enlargedFullSpaceOccupation hH hLE hlam hLam A P T) =
      ∫⁻ t : ElapsedTime (ENNReal.ofReal T),
        ∫⁻ z, F (enlargedTerminalPoint (P.time + t.1) z)
          ∂kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t.1)
            (P.position 0, P.velocity 0) ∂elapsedVolume (ENNReal.ofReal T) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let f := fun t => ∫⁻ z, F (enlargedTerminalPoint (P.time + t) z)
    ∂kernelXV E (Real.toNNReal t) (P.position 0, P.velocity 0)
  have hm : Measurable (fun tz : ℝ × Z => F (enlargedTerminalPoint (P.time + tz.1) tz.2)) := by
    apply hF.comp
    unfold enlargedTerminalPoint
    exact (KineticPoint.measurable_equivProd_symm 1).comp
      ((measurable_const.add measurable_fst).prodMk
        ((measurable_pi_iff.mpr (fun _ => measurable_fst.comp measurable_snd)).prodMk
          (measurable_pi_iff.mpr (fun _ => measurable_snd.comp measurable_snd))))
  have hf : Measurable f := hm.lintegral_kernel_prod_right'
    (κ := physicalElapsedKernel E (P.position 0, P.velocity 0))
  have he : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < ENNReal.ofReal T} = Ioo 0 T := by
    ext t
    simp [ENNReal.ofReal_lt_ofReal_iff hT]
  have hmap : (elapsedVolume (ENNReal.ofReal T)).map Subtype.val = volume.restrict (Ioo 0 T) := by
    exact (map_comap_subtype_coe (measurableSet_elapsedTime (ENNReal.ofReal T)) volume).trans
      (congrArg (fun B => volume.restrict B) he)
  rw [enlargedFullSpaceOccupation_lintegral hH hLE hlam hLam A P T F hF]
  rw [← lintegral_map hf measurable_subtype_coe, hmap]
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume)).symm]

/-- Time autonomy identifies an absolute native query with the scalar elapsed kernel. -/
theorem enlargedFullSpace_native_elapsed_lintegral
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (P : Point) (t : ℝ) (ht : 0 ≤ t)
    (F : Point → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F ⟨P.time + t, w.2, w.1⟩
      ∂(fullSpaceEvolution hH hLE hlam hLam A).2.master
        (wholeSpaceQuery P.time (P.time + t) (by linarith) P.velocity P.position)) =
      ∫⁻ z, F (enlargedTerminalPoint (P.time + t) z)
        ∂kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
          (P.position 0, P.velocity 0) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let q := wholeSpaceQuery P.time (P.time + t) (by linarith) P.velocity P.position
  have hq : autonomousQueryShift (-P.time) q =
      wholeQuery (Real.toNNReal t) (P.position 0, P.velocity 0) := by
    apply Subtype.ext
    dsimp [autonomousQueryShift, q, wholeQuery, wholeSpaceQuery]
    rw [max_eq_left ht]
    have hx : (fun _ => P.position 0) = P.position := by
      funext i
      exact congrArg P.position (Subsingleton.elim 0 i)
    have hv : (fun _ => P.velocity 0) = P.velocity := by
      funext i
      exact congrArg P.velocity (Subsingleton.elim 0 i)
    rw [hx, hv]
    congr 1 <;> ring
  have hk := fullspace_kernel_timeShift A E
    (fullSpaceEvolution_spec hH hLE hlam hLam A) (-P.time) q
  rw [hq] at hk
  change (∫⁻ w, F ⟨P.time + t, w.2, w.1⟩ ∂E.2.master q) =
    ∫⁻ z, F (enlargedTerminalPoint (P.time + t) z)
      ∂(E.2.master (wholeQuery (Real.toNNReal t) (P.position 0, P.velocity 0))).map nativeToXV
  change _ = ∫⁻ z, (F ∘ enlargedTerminalPoint (P.time + t)) z ∂_
  rw [(lintegral_map (hF.comp (enlargedTerminalPoint_measurable (P.time + t))) nativeToXV_measurable (μ := E.2.master (wholeQuery (Real.toNNReal t) (P.position 0, P.velocity 0)))), hk]
  apply lintegral_congr
  intro w
  congr 1
  apply KineticPoint.ext
  · rfl
  · funext i
    exact congrArg w.2 (Subsingleton.elim i 0)
  · funext i
    exact congrArg w.1 (Subsingleton.elim i 0)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

