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

theorem hasFDerivAt_phi_first (x y z : Albert) :
    HasFDerivAt (fun w : Albert => phi w y z)
      (nativeInnerContinuous (glennieVector y z x)) x :=
  (hasFDerivAt_phi_third y z x).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => (phi_cyclic w y z).symm)

theorem hasFDerivAt_phi_second (x y z : Albert) :
    HasFDerivAt (fun w : Albert => phi x w z)
      (nativeInnerContinuous (glennieVector z x y)) y :=
  (hasFDerivAt_phi_third z x y).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => phi_cyclic z x w)

@[fun_prop] theorem differentiable_jordan_triple {f g : NativeTriple → Albert}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun p => jordan (f p) (g p)) := by
  simpa only [Function.comp_def, jordanContinuous_apply] using
    jordanContinuous.isBoundedBilinearMap.differentiable.comp (hf.prodMk hg)

@[fun_prop] theorem differentiable_U_triple {f g : NativeTriple → Albert}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun p => U (f p) (g p)) := by
  unfold U
  fun_prop

/-- Joint differentiability, independently of the partial formulas. -/
theorem differentiable_phiTriple : Differentiable ℝ phiTriple := by
  unfold phiTriple phi
  simp only [← pairingContinuous_apply]
  fun_prop

section StableFullDerivative
set_option backward.isDefEq.respectTransparency false
attribute [local instance 20000] Glennie.nativeRealSMulComm Glennie.nativeRealContinuousAdd Glennie.nativeRealContinuousSMul
/-- Three continuous linear trace pairings, with the actual cyclic G8 values. -/
def fullDerivative (x y z : Albert) : NativeTriple →L[ℝ] ℝ :=
  (nativeInnerContinuous (glennieVector y z x)).coprod
    ((nativeInnerContinuous (glennieVector z x y)).coprod
      (nativeInnerContinuous (glennieVector x y z)))
end StableFullDerivative

/-- A differentiable map on a product is determined to first order by its
coordinate restrictions. -/
private theorem derivative_prod {A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {f : A × B → C} {x : A} {y : B} (hd : DifferentiableAt ℝ f (x,y))
    {u : A →L[ℝ] C} {v : B →L[ℝ] C}
    (hu : HasFDerivAt (fun a => f (a,y)) u x)
    (hv : HasFDerivAt (fun b => f (x,b)) v y) : HasFDerivAt f (u.coprod v) (x,y) := by
  have h₁ := (hd.hasFDerivAt.comp (g := f) x (hasFDerivAt_prodMk_left x y)).unique hu
  have h₂ := (hd.hasFDerivAt.comp (g := f) y (hasFDerivAt_prodMk_right x y)).unique hv
  exact hd.hasFDerivAt.congr_fderiv (by rw [← h₁, ← h₂, ContinuousLinearMap.coprod_comp_inl_inr])

private theorem derivative_triple {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : W → W → W → ℝ) (x y z : W)
    (hd : DifferentiableAt ℝ (fun p : W × W × W => f p.1 p.2.1 p.2.2) (x,y,z))
    {L M N : W →L[ℝ] ℝ} (hL : HasFDerivAt (fun a => f a y z) L x)
    (hM : HasFDerivAt (fun b => f x b z) M y) (hN : HasFDerivAt (f x y) N z) :
    HasFDerivAt (fun p : W × W × W => f p.1 p.2.1 p.2.2) (L.coprod (M.coprod N)) (x,y,z) := by
  have h := hd.comp (y,z) (hasFDerivAt_prodMk_right (𝕜 := ℝ) x (y,z)).differentiableAt
  exact derivative_prod (f := fun p : W × W × W => f p.1 p.2.1 p.2.2) hd hL
    (derivative_prod (f := fun p : W × W => f x p.1 p.2) h hM hN)

/-- Identify the actual joint derivative by its three coordinate restrictions. -/
theorem hasFDerivAt_phiTriple (x y z : Albert) :
    HasFDerivAt phiTriple (fullDerivative x y z) (x, y, z) :=
  derivative_triple phi x y z (differentiable_phiTriple (x,y,z))
    (hasFDerivAt_phi_first x y z) (hasFDerivAt_phi_second x y z) (hasFDerivAt_phi_third x y z)

/-- A nonzero actual full differential forces full unital Jordan generation.
The three membership permutations use the proper-submodule theorem. -/
theorem eq_top_of_fderiv_phiTriple_ne_zero
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : JordanClosed K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hd : fderiv ℝ phiTriple (x, y, z) ≠ 0) : K = ⊤ := by
  by_contra hK
  apply hd
  apply ContinuousLinearMap.ext
  rintro ⟨a,b,c⟩
  simp [(hasFDerivAt_phiTriple x y z).fderiv, fullDerivative,
    glennieVector_eq_zero_of_ne_top K h1 hJ hK, hx, hy, hz, ContinuousLinearMap.coprod_apply]

end
end Glennie.Compact.GlennieFullDerivativeR01
