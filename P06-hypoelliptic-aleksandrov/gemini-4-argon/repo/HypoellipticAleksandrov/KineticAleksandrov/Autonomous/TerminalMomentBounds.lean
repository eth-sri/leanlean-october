module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsActual
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsRegularity
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsTruncation
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FourthMomentsPolynomials
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel

/-! # Source terminal second moments of the canonical full-space kernel -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory
open scoped ENNReal
open HypoellipticAleksandrov.Parabolic Set Filter HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology

/- The exact deterministic second-moment conditions, with constants 2 and 4/3. -/
theorem terminal_second_moments
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) :
    let E := fullSpaceEvolution hH hLE hlam hLam A
    (∫⁻ w, ENNReal.ofReal ((w.2-z.2)^2) ∂kernelXV E T z) ≤
      ENNReal.ofReal (2*Lam*(T : ℝ)) ∧
    (∫⁻ w, ENNReal.ofReal ((w.1-z.1)^2) ∂kernelXV E T z) ≤
      ENNReal.ofReal (2*z.2^2*(T : ℝ)^2+4/3*Lam*(T : ℝ)^3) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  have hE := fullSpaceEvolution_spec hH hLE hlam hLam A
  refine ⟨kernelXV_velocity_2_moment hlam A E hE z T, ?_⟩
  have _h_xinl_0 : (∫⁻ w, ENNReal.ofReal ((w.1-z.1)^2) ∂kernelXV E T z) ≤
      ENNReal.ofReal (z.2^2*(T : ℝ)^2+(2/3 : ℝ)*Lam*(T : ℝ)^3) := by
    have hLam := (hlam.le.trans (A.bounds 0 0).1).trans (A.bounds 0 0).2
    let W := positionSecondBarrier Lam z.1 T ∘ terminalPhysicalPoint
    let g := fun x : EvolutionAmbientState 1 => (x.2 0-z.1)^2
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := by dsimp only [g]; fun_prop
    have hw : ContDiff ℝ (⊤ : ℕ∞) (rawLift (positionSecondBarrier Lam z.1 T ∘ terminalPhysicalPoint)) := by
      let X0 := z.1
      change ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (PDE.Vec 1 × PDE.Vec 1) =>
        (q.2.2 0-X0+(T-q.1)*q.2.1 0)^2+(2/3:ℝ)*Lam*(T-q.1)^3)
      fun_prop
    have h := terminal_polynomial_lintegral_le hlam A E hE g hg
      (fun x => sq_nonneg _) W (terminal_raw_continuous W hw)
      (terminal_raw_regular W hw) T
      (fun p hp => positionSecondBarrier_nonneg hLam z.1 T (terminalPhysicalPoint p) hp)
      (fun p hp => by
        rw [terminalPhysicalPoint_operator]
        exact positionSecondBarrier_operator_nonpos A.a Lam z.1 T (terminalPhysicalPoint p)
          (A.bounds _ _).2)
      (fun p hp => by
        dsimp only [g, W, Function.comp_apply, terminalPhysicalPoint]
        rw [← hp]
        exact (positionSecondBarrier_terminal Lam z.1 (terminalPhysicalPoint p)).symm)
      (wholeQuery T z) rfl
    rw [kernelXV, lintegral_map (by fun_prop) nativeToXV_measurable]
    simpa only [g, W, wholeQuery, wholeSpaceQuery, terminalPhysicalPoint,
      Function.comp_apply, nativeToXV, positionSecondBarrier_start] using h
  apply _h_xinl_0.trans
  apply ENNReal.ofReal_le_ofReal
  have hL := hlam.le.trans hLam
  have hT := T.property
  have hh : 0 ≤ z.2^2*(T : ℝ)^2+(2/3 : ℝ)*Lam*(T : ℝ)^3 := by positivity
  linarith only [hh]

/- Both actual real second moments are integrable, rather than merely total integrals. -/
theorem terminal_second_moments_integrable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) :
    let E := fullSpaceEvolution hH hLE hlam hLam A
    Integrable (fun w : Z => (w.2-z.2)^2) (kernelXV E T z) ∧
      Integrable (fun w : Z => (w.1-z.1)^2) (kernelXV E T z) := by
  have h := terminal_second_moments hH hLE hlam hLam A z T
  constructor
  · apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (Filter.Eventually.of_forall (fun w : Z => sq_nonneg (w.2-z.2)))).mp
    exact ne_of_lt (h.1.trans_lt ENNReal.ofReal_lt_top)
  · apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (Filter.Eventually.of_forall (fun w : Z => sq_nonneg (w.1-z.1)))).mp
    exact ne_of_lt (h.2.trans_lt ENNReal.ofReal_lt_top)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
