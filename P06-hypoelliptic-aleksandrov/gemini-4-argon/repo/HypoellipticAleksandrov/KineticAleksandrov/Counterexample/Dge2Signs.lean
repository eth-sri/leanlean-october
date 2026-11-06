module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Cutoff
public import Mathlib.Topology.Order.Compact
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import PDEFoundation.Ambient.EuclideanNorm

/-!
# Seed sign control in dimensions at least two

The orthogonal direction is constructed in native coordinates, so the positive
Hessian direction requires exactly the source's dimension-at-least-two assumption.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open scoped BigOperators

/- A native vector in dimension at least two has a nonzero perpendicular direction. -/
theorem exists_native_perpendicular (d ) (hd : 2 ≤ d) (z : PDE.Vec d) :
    ∃ w : PDE.Vec d, w ≠ 0 ∧ PDE.vecDot z w = 0 := by
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  by_cases hz : z i = 0
  · refine ⟨Pi.single i 1, ?_, ?_⟩
    · intro h
      have hh := congrFun h i
      simp at hh
    · simp [PDE.vecDot, Pi.single_apply, hz]
  · let w : PDE.Vec d := z i • Pi.single j 1 - z j • Pi.single i 1
    refine ⟨w, ?_, ?_⟩
    · intro h
      have hh := congrFun h j
      have hji : j ≠ i := Ne.symm hij
      simp [w, hji] at hh
      exact hz hh
    · simp [w, PDE.vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
        Pi.single_apply]
      ring


/- The seed has a strictly positive Hessian direction at every point. -/
theorem seed_positive_direction (d ) (hd : 2 ≤ d) (alpha C₀ sigma : ℝ)
    (ha : 0 < alpha) (hsigma : 0 < sigma) (y e : PDE.Vec d) :
    ∃ w : PDE.Vec d,
      0 < fderiv ℝ (fun z => fderiv ℝ (fun a => seed alpha C₀ sigma a e) z w) y w := by
  obtain ⟨w, hw, hperp⟩ := exists_native_perpendicular d hd (y - e)
  refine ⟨w, ?_⟩
  have _h_xinl_0 : fderiv ℝ (fun z => fderiv ℝ (fun a => seed alpha C₀ sigma a e) z w) y w =
      seedTangentialEigenvalue alpha sigma y e * PDE.vecDot w w := by
    let u := w
    rw [seed_hessian alpha C₀ sigma hsigma]
    simp [seedHessianForm, seedTangentialEigenvalue, hperp]
  rw [_h_xinl_0]
  have hn : 0 < PDE.vecNormSq w :=
    (PDE.vecNormSq_nonneg w).lt_of_ne' (PDE.vecNormSq_eq_zero_iff.not.mpr hw)
  have _h_xinl_0 : 0 < seedTangentialEigenvalue alpha sigma y e := by
      exact (
    mul_pos ha (Real.rpow_pos_of_pos (seedBase_pos sigma hsigma y e) _)

    /- The radial seed eigenvalue is negative precisely past the source threshold. -/
    )
  exact mul_pos _h_xinl_0 hn

/- Past the source threshold the seed has a strictly negative Hessian direction. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
