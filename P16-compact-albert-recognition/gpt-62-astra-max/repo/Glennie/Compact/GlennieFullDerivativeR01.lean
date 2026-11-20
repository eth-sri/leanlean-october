/- Actual full native differential of Phi and its forward generation consequence.
All exposition and Lean code are AI-generated under Robert MacGregor's direction.
No novelty is asserted.
-/
module

public import Glennie.Compact.GlennieDerivativeGenerationR01
public import Glennie.Covariance
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

@[expose] public section
namespace Glennie.Compact.GlennieFullDerivativeR01

open Glennie
open Glennie.Compact.GlennieScalarPotentialR01
open Glennie.Compact.GlennieDerivativeR01
open Glennie.Compact.GlennieDerivativeGenerationR01

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-- The ordinary native product space, with its existing product topology. -/
abbrev NativeTriple := Albert × (Albert × Albert)

/-- The literal native scalar on three independently variable Albert inputs. -/
def phiTriple (p : NativeTriple) : ℝ := phi p.1 p.2.1 p.2.2

theorem phi_cyclic (x y z : Albert) : phi y z x = phi x y z := by
  grind [phi, phi_swap_first_two, phi_swap_first_third]

private theorem differentiable_phiTriple : Differentiable ℝ phiTriple := by
  unfold phiTriple phi U
  simp only [← jordanContinuous_apply,← pairingContinuous_apply]
  fun_prop

private theorem leftD {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X × Y → ℝ} {D : X × Y →L[ℝ] ℝ} {x : X} {y : Y}
    (d : HasFDerivAt f D (x,y)) : HasFDerivAt (fun a => f (a,y)) (D.comp (ContinuousLinearMap.inl ℝ X Y)) x :=
  d.comp x (hasFDerivAt_prodMk_left x y)
private theorem rightD {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X × Y → ℝ} {D : X × Y →L[ℝ] ℝ} {x : X} {y : Y}
    (d : HasFDerivAt f D (x,y)) : HasFDerivAt (fun b => f (x,b)) (D.comp (ContinuousLinearMap.inr ℝ X Y)) y :=
  d.comp y (hasFDerivAt_prodMk_right x y)

section StableFullDerivative
set_option backward.isDefEq.respectTransparency false
attribute [local instance 20000] Glennie.nativeRealSMulComm Glennie.nativeRealContinuousAdd Glennie.nativeRealContinuousSMul
/-- Three continuous linear trace pairings, with the actual cyclic G8 values. -/
def fullDerivative (x y z : Albert) : NativeTriple →L[ℝ] ℝ :=
  (nativeInnerContinuous (glennieVector y z x)).coprod
    ((nativeInnerContinuous (glennieVector z x y)).coprod
      (nativeInnerContinuous (glennieVector x y z)))
end StableFullDerivative

/-- Identify the actual joint derivative by its three coordinate restrictions.
Joint differentiability above supplies existence; it is not inferred from
separate partial derivatives alone. -/
theorem hasFDerivAt_phiTriple (x y z : Albert) :
    HasFDerivAt phiTriple (fullDerivative x y z) (x, y, z) := by
  let D := fderiv ℝ phiTriple (x,y,z)
  have hd : HasFDerivAt phiTriple D (x,y,z) := (differentiable_phiTriple _).hasFDerivAt
  have dx := leftD hd; have dq := rightD hd
  simp only [phiTriple] at dx dq
  have dy := leftD dq; have dz := rightD dq
  rw [funext fun w => (phi_cyclic w y z).symm] at dx
  rw [funext fun w => phi_cyclic z x w] at dy
  have e1 := dx.unique (hasFDerivAt_phi_third y z x)
  have e2 := dy.unique (hasFDerivAt_phi_third z x y)
  have e3 := dz.unique (hasFDerivAt_phi_third x y z)
  apply hd.congr_fderiv
  conv_lhs => rw [← ContinuousLinearMap.coprod_comp_inl_inr D,e1,
    ← ContinuousLinearMap.coprod_comp_inl_inr (D.comp (ContinuousLinearMap.inr ℝ Albert (Albert × Albert))),e2,e3]
  rfl

/-- A nonzero actual full differential forces full unital Jordan generation.
The three membership permutations use the proper-submodule theorem. -/
theorem eq_top_of_fderiv_phiTriple_ne_zero
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hd : fderiv ℝ phiTriple (x, y, z) ≠ 0) : K = ⊤ := by
  by_contra hK
  apply hd
  have van := glennieVector_eq_zero_of_ne_top K h1 hJ hK
  rw [(hasFDerivAt_phiTriple x y z).fderiv]; apply ContinuousLinearMap.ext; rintro ⟨a,b,c⟩
  simp [fullDerivative,pairingContinuous_apply,van y z x hy hz hx,van z x y hz hx hy,van x y z hx hy hz]

end
end Glennie.Compact.GlennieFullDerivativeR01
