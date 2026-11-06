module

import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus

/-!
# Linearity of the viscous transported operator

The operator `L_ε` is linear on functions that are slice regular at the point
in the sense of `IsSliceRegularAt`.  These identities are used to apply the
maximum argument to differences of a solution and a barrier.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov.Parabolic Filter
open scoped MatrixOrder Topology

variable {n : ℕ}

/-- Additivity of the classical gradient. -/
theorem classicalGradient_add  {g h : PDE.ScalarField n} {x : PDE.Vec n}
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) :
    PDE.classicalGradient (fun y => g y + h y) x =
      PDE.classicalGradient g x + PDE.classicalGradient h x := by
  ext i
  simp only [PDE.classicalGradient_apply, Pi.add_apply]
  rw [fderiv_fun_add hg hh]
  rfl

/-- Homogeneity of the classical gradient. -/
theorem classicalGradient_const_mul  {g : PDE.ScalarField n} {x : PDE.Vec n} (c : ℝ)
    (hg : DifferentiableAt ℝ g x) :
    PDE.classicalGradient (fun y => c * g y) x = c • PDE.classicalGradient g x := by
  ext i
  simp only [PDE.classicalGradient_apply, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_const_mul hg]
  rfl

/-- Additivity of `sliceHessian` for `C²` functions. -/
theorem sliceHessian_add  {g h : PDE.ScalarField n} {x : PDE.Vec n}
    (hg : ContDiffAt ℝ 2 g x) (hh : ContDiffAt ℝ 2 h x) :
    sliceHessian (fun y => g y + h y) x = sliceHessian g x + sliceHessian h x := by



  ext i j
  rw [sliceHessian_apply_eq_sndFDeriv (hg.add hh), Matrix.add_apply,
    sliceHessian_apply_eq_sndFDeriv hg, sliceHessian_apply_eq_sndFDeriv hh]
  have hev : fderiv ℝ (fun y => g y + h y) =ᶠ[𝓝 x]
      fun y => fderiv ℝ g y + fderiv ℝ h y := by
    filter_upwards [hg.eventually (by norm_num), hh.eventually (by norm_num)] with y hgy hhy
    exact fderiv_add (hgy.differentiableAt (by norm_num)) (hhy.differentiableAt (by norm_num))
  rw [hev.fderiv_eq, fderiv_fun_add ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)) ((hh.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]
  rfl

/-- Homogeneity of `sliceHessian` for `C²` functions. -/
theorem sliceHessian_const_mul  {g : PDE.ScalarField n} {x : PDE.Vec n} (c : ℝ)
    (hg : ContDiffAt ℝ 2 g x) :
    sliceHessian (fun y => c * g y) x = c • sliceHessian g x := by


  ext i j
  rw [sliceHessian_apply_eq_sndFDeriv (contDiffAt_const.mul hg), Matrix.smul_apply,
    sliceHessian_apply_eq_sndFDeriv hg]
  have hev : fderiv ℝ (fun y => c * g y) =ᶠ[𝓝 x] fun y => c • fderiv ℝ g y := by
    filter_upwards [hg.eventually (by norm_num)] with y hgy
    exact fderiv_const_mul (hgy.differentiableAt (by norm_num)) c
  rw [hev.fderiv_eq, fderiv_fun_const_smul ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]
  simp

/-- Slice regularity is preserved by sums. -/
theorem IsSliceRegularAt.add  {u v : HypoellipticAleksandrov.KineticScalarField n} {p : KineticPoint n}
    (hu : IsSliceRegularAt u p) (hv : IsSliceRegularAt v p) :
    IsSliceRegularAt (fun q => u q + v q) p :=
  ⟨hu.time.add hv.time, hu.position.add hv.position, hu.velocity.add hv.velocity⟩

/-- Slice regularity is preserved by constant multiples. -/
theorem IsSliceRegularAt.const_mul  {u : HypoellipticAleksandrov.KineticScalarField n} {p : KineticPoint n}
    (c : ℝ) (hu : IsSliceRegularAt u p) :
    IsSliceRegularAt (fun q => c * u q) p :=
  ⟨hu.time.const_mul c, contDiffAt_const.mul hu.position, contDiffAt_const.mul hu.velocity⟩

/-- Slice regularity is preserved by differences. -/
theorem IsSliceRegularAt.sub  {u v : HypoellipticAleksandrov.KineticScalarField n} {p : KineticPoint n}
    (hu : IsSliceRegularAt u p) (hv : IsSliceRegularAt v p) :
    IsSliceRegularAt (fun q => u q - v q) p :=
  ⟨hu.time.sub hv.time, hu.position.sub hv.position, hu.velocity.sub hv.velocity⟩

/-- Slice regularity is preserved by negation. -/
theorem IsSliceRegularAt.neg  {u : HypoellipticAleksandrov.KineticScalarField n} {p : KineticPoint n}
    (hu : IsSliceRegularAt u p) : IsSliceRegularAt (fun q => -u q) p :=
  ⟨hu.time.neg, hu.position.neg, hu.velocity.neg⟩

/-- Constants are slice regular. -/
theorem IsSliceRegularAt.const  (c : ℝ) (p : KineticPoint n) :
    IsSliceRegularAt (fun _ => c) p :=
  ⟨differentiableAt_const c, contDiffAt_const, contDiffAt_const⟩

variable {B : FullKineticCoefficient n} {b : PDE.VectorField n} {ε : ℝ}

/-- Additivity of `L_ε` at a slice-regular point. -/
theorem viscousTransportedOperator_add   {u v : HypoellipticAleksandrov.KineticScalarField n} {p : KineticPoint n}
    (hu : IsSliceRegularAt u p) (hv : IsSliceRegularAt v p) :
    viscousTransportedOperator B b ε (fun q => u q + v q) p =
      viscousTransportedOperator B b ε u p + viscousTransportedOperator B b ε v p := by
  let sharedTerm_97968d7f73 := ((fun q => u q + v q))
  have ht : kineticTimeDerivative sharedTerm_97968d7f73 p =
      kineticTimeDerivative u p + kineticTimeDerivative v p := by
    unfold kineticTimeDerivative
    exact deriv_fun_add hu.time hv.time
  have hpos : diffusedHessian sharedTerm_97968d7f73 p =
      diffusedHessian u p + diffusedHessian v p := by
    simp only [diffusedHessian_eq_sliceHessian]
    exact sliceHessian_add hu.position hv.position
  have hvel : kineticVelocityGradient sharedTerm_97968d7f73 p =
      kineticVelocityGradient u p + kineticVelocityGradient v p :=
    classicalGradient_add (hu.velocity.differentiableAt (by norm_num))
      (hv.velocity.differentiableAt (by norm_num))
  have hhess : kineticVelocityHessian sharedTerm_97968d7f73 p =
      kineticVelocityHessian u p + kineticVelocityHessian v p := by
    simp only [kineticVelocityHessian_eq_sliceHessian]
    exact sliceHessian_add hu.velocity hv.velocity
  rw [viscousTransportedOperator_apply, viscousTransportedOperator_apply,
    viscousTransportedOperator_apply, transportedForwardOperator_apply,
    transportedForwardOperator_apply, transportedForwardOperator_apply, ht, hpos, hvel, hhess]
  simp only [matrixContraction_add_right, PDE.vecDot, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, Matrix.add_apply]
  ring

/-- Homogeneity of `L_ε` at a slice-regular point. -/
theorem viscousTransportedOperator_const_mul   {u : HypoellipticAleksandrov.KineticScalarField n} {p : KineticPoint n}
    (c : ℝ) (hu : IsSliceRegularAt u p) :
    viscousTransportedOperator B b ε (fun q => c * u q) p =
      c * viscousTransportedOperator B b ε u p := by
  let sharedTerm_24e3731746 := ((fun q => c * u q))
  have ht : kineticTimeDerivative sharedTerm_24e3731746 p = c * kineticTimeDerivative u p := by
    unfold kineticTimeDerivative
    exact deriv_const_mul c hu.time
  have hpos : diffusedHessian sharedTerm_24e3731746 p = c • diffusedHessian u p := by
    simp only [diffusedHessian_eq_sliceHessian]
    exact sliceHessian_const_mul c hu.position
  have hvel : kineticVelocityGradient sharedTerm_24e3731746 p = c • kineticVelocityGradient u p :=
    classicalGradient_const_mul c (hu.velocity.differentiableAt (by norm_num))
  have hhess : kineticVelocityHessian sharedTerm_24e3731746 p = c • kineticVelocityHessian u p := by
    simp only [kineticVelocityHessian_eq_sliceHessian]
    exact sliceHessian_const_mul c hu.velocity
  rw [viscousTransportedOperator_apply, viscousTransportedOperator_apply,
    transportedForwardOperator_apply, transportedForwardOperator_apply, ht, hpos, hvel, hhess]
  simp only [matrixContraction_smul_right, PDE.vecDot, Pi.smul_apply, smul_eq_mul,
    Matrix.smul_apply]
  have hs : ∑ i, b p.position i * (c * kineticVelocityGradient u p i) =
      c * ∑ i, b p.position i * kineticVelocityGradient u p i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hs2 : ∑ i, c * kineticVelocityHessian u p i i =
      c * ∑ i, kineticVelocityHessian u p i i := (Finset.mul_sum _ _ _).symm
  rw [hs, hs2]
  ring

end HypoellipticAleksandrov.KineticAleksandrov
