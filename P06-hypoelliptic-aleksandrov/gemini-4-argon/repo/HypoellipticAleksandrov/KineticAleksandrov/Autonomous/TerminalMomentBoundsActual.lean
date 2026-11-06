module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsTruncation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsRegularity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FourthMomentsPolynomials
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel

/-! # Actual terminal moments of every realizing autonomous full-space kernel

Compact polynomial tests, epsilon-Lyapunov comparison and Fatou establish the
unbounded terminal moments without a diffusion realization or coefficient derivatives.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory Filter
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal Topology

/- The actual velocity terminal moment, with the polynomial's sharp start value. -/
theorem kernelXV_velocity_2_moment {lam Lam } (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (z : Z) (T : NNReal) :
    (∫⁻ w, ENNReal.ofReal ((w.2-z.2)^2) ∂kernelXV E T z) ≤
      ENNReal.ofReal (2*Lam*(T : ℝ)) := by
  have hLam := (hlam.le.trans (A.bounds 0 0).1).trans (A.bounds 0 0).2
  let W := velocitySecondBarrier Lam z.2 T ∘ terminalPhysicalPoint
  let g := fun x : EvolutionAmbientState 1 => (x.1 0-z.2)^2
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by dsimp only [g]; fun_prop
  have hw : ContDiff ℝ (⊤ : ℕ∞) (rawLift (velocitySecondBarrier Lam z.2 T ∘ terminalPhysicalPoint)) := by
    let v0 := z.2
    change ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (PDE.Vec 1 × PDE.Vec 1) =>
      (q.2.1 0-v0)^2+2*Lam*(T-q.1))
    fun_prop
  have h := terminal_polynomial_lintegral_le hlam A E hE g hg
    (fun x => sq_nonneg _) W (terminal_raw_continuous W hw)
    (terminal_raw_regular W hw) T
    (fun p hp => velocitySecondBarrier_nonneg hLam z.2 T (terminalPhysicalPoint p) hp)
    (fun p hp => by
      rw [terminalPhysicalPoint_operator]
      exact velocitySecondBarrier_operator_nonpos A.a Lam z.2 T (terminalPhysicalPoint p)
        (A.bounds _ _).2)
    (fun p hp => by
      dsimp only [g, W, Function.comp_apply, terminalPhysicalPoint]
      rw [← hp]
      exact (velocitySecondBarrier_terminal Lam z.2 (terminalPhysicalPoint p)).symm)
    (wholeQuery T z) rfl
  rw [kernelXV, lintegral_map (by fun_prop) nativeToXV_measurable]
  simpa only [g, W, wholeQuery, wholeSpaceQuery, terminalPhysicalPoint,
    Function.comp_apply, nativeToXV, velocitySecondBarrier_start] using h

/- The actual position terminal moment, with the polynomial's sharp start value. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
