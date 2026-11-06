module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FullSpaceIdentificationDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Autonomy
import Mathlib.Tactic

/-! # Full-space occupation action in the enlarged recursion's physical coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov
open scoped ENNReal
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/- Reinserting physical time is a measurable coordinate map. -/
theorem enlargedTerminalPoint_measurable (b : ℝ) : Measurable (enlargedTerminalPoint b) := by
  unfold enlargedTerminalPoint
  exact (KineticPoint.measurable_equivProd_symm 1).comp
    (measurable_const.prodMk ((measurable_pi_iff.mpr (fun _ => measurable_fst)).prodMk
      (measurable_pi_iff.mpr (fun _ => measurable_snd))))

/- The full-space occupation has the literal iterated physical kernel action. -/
theorem enlargedFullSpaceOccupation_lintegral
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
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

/- Full-space occupation can equally be integrated over the literal elapsed-time subtype. -/
theorem enlargedFullSpace_native_elapsed_lintegral
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
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
    have hx : (fun _ : Fin 1 => P.position 0) = P.position := by
      funext i
      exact congrArg P.position (Subsingleton.elim 0 i)
    have hv : (fun _ : Fin 1 => P.velocity 0) = P.velocity := by
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
  have hm := lintegral_map
    (hF.comp (enlargedTerminalPoint_measurable (P.time + t))) nativeToXV_measurable
      (μ := E.2.master (wholeQuery (Real.toNNReal t) (P.position 0, P.velocity 0)))
  change _ = ∫⁻ z, (F ∘ enlargedTerminalPoint (P.time + t)) z ∂_
  rw [hm, hk]
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
