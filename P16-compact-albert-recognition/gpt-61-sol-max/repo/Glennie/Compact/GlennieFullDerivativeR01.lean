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
set_option backward.isDefEq.respectTransparency false
abbrev NativeTriple := Albert × (Albert × Albert)

/-- The literal native scalar on three independently variable Albert inputs. -/
def phiTriple (p : NativeTriple) : ℝ := phi p.1 p.2.1 p.2.2

theorem phi_cyclic (x y z : Albert) : phi y z x = phi x y z := by
  rw [phi_swap_first_two z y x, phi_swap_first_third x y z, neg_neg]

theorem hasFDerivAt_phi_first (x y z : Albert) :
    HasFDerivAt (fun w : Albert => phi w y z)
      (nativeInnerContinuous (glennieVector y z x)) x := by
  convert hasFDerivAt_phi_third y z x using 1
  ext w
  exact (phi_cyclic w y z).symm

theorem hasFDerivAt_phi_second (x y z : Albert) :
    HasFDerivAt (fun w : Albert => phi x w z)
      (nativeInnerContinuous (glennieVector z x y)) y := by
  convert hasFDerivAt_phi_third z x y using 1
  ext w
  exact phi_cyclic z x w

/-! Joint differentiability is proved independently of the partial formulas. -/

@[fun_prop] theorem differentiable_jordan_triple {f g : NativeTriple → Albert}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun p => jordan (f p) (g p)) := by
  simpa only [Function.comp_def, jordanContinuous_apply_apply] using
    jordanContinuous.isBoundedBilinearMap.differentiable.comp (hf.prodMk hg)

@[fun_prop] theorem differentiable_U_triple {f g : NativeTriple → Albert}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun p => U (f p) (g p)) := by
  unfold U
  fun_prop

/-- Genuine joint differentiability of the original polynomial on all triples. -/
theorem differentiable_phiTriple : Differentiable ℝ phiTriple := by
  change Differentiable ℝ (fun p : NativeTriple =>
    nativeInnerContinuous (U p.1 (U p.2.1 p.2.2) - U p.2.1 (U p.1 p.2.2))
      (U p.2.2 (jordan p.1 p.2.1)))
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

theorem fullDerivative_apply (x y z a b c : Albert) :
    fullDerivative x y z (a, b, c) =
      inner a (glennieVector y z x) + inner b (glennieVector z x y) +
        inner c (glennieVector x y z) := by
  simp only [fullDerivative, ContinuousLinearMap.coprod_apply, pairingContinuous_apply,
    inner_comm (glennieVector y z x) a, inner_comm (glennieVector z x y) b,
    inner_comm (glennieVector x y z) c, add_assoc]

private theorem derivative_of_partials
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E × F → G} {x : E} {y : F} {A : E →L[ℝ] G} {B : F →L[ℝ] G}
    (hf : DifferentiableAt ℝ f (x, y))
    (hA : HasFDerivAt (fun t => f (t, y)) A x)
    (hB : HasFDerivAt (fun t => f (x, t)) B y) :
    HasFDerivAt f (A.coprod B) (x, y) := by
  apply hf.hasFDerivAt.congr_fderiv
  rw [← ContinuousLinearMap.coprod_comp_inl_inr (fderiv ℝ f (x, y))]
  congr 1
  · exact (hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)).unique hA
  · exact (hf.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)).unique hB

/-- The joint derivative is determined by its coordinate restrictions. -/
theorem hasFDerivAt_phiTriple (x y z : Albert) :
    HasFDerivAt phiTriple (fullDerivative x y z) (x, y, z) := by
  have hd : DifferentiableAt ℝ (fun q : Albert × Albert => phiTriple (x, q)) (y, z) :=
    (differentiable_phiTriple (x, y, z)).comp (y, z)
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) x (y, z)).differentiableAt
  exact derivative_of_partials (differentiable_phiTriple (x, y, z))
    (hasFDerivAt_phi_first x y z)
    (derivative_of_partials hd (hasFDerivAt_phi_second x y z) (hasFDerivAt_phi_third x y z))

theorem fderiv_phiTriple (x y z : Albert) :
    fderiv ℝ phiTriple (x, y, z) = fullDerivative x y z :=
  (hasFDerivAt_phiTriple x y z).fderiv

/-- The full differential on an arbitrary native direction (a,b,c). -/
theorem fderiv_phiTriple_apply (x y z a b c : Albert) :
    fderiv ℝ phiTriple (x, y, z) (a, b, c) =
      inner a (glennieVector y z x) + inner b (glennieVector z x y) +
        inner c (glennieVector x y z) := by
  rw [fderiv_phiTriple, fullDerivative_apply]

/-- Full ambient criticality is equivalent to vanishing of all three cyclic
native G8 values. The forward proof tests the three coordinate directions. -/
theorem fderiv_phiTriple_eq_zero_iff (x y z : Albert) :
    fderiv ℝ phiTriple (x, y, z) = 0 ↔
      glennieVector y z x = 0 ∧ glennieVector z x y = 0 ∧
        glennieVector x y z = 0 := by
  constructor
  · intro hd
    have h := fderiv_phiTriple_apply x y z
      (glennieVector y z x) (glennieVector z x y) (glennieVector x y z)
    rw [hd, zero_apply] at h
    have h1 := inner_self_nonneg (glennieVector y z x)
    have h2 := inner_self_nonneg (glennieVector z x y)
    have h3 := inner_self_nonneg (glennieVector x y z)
    exact ⟨(inner_self_eq_zero _).mp (by linarith),
      (inner_self_eq_zero _).mp (by linarith), (inner_self_eq_zero _).mp (by linarith)⟩
  · rintro ⟨h1, h2, h3⟩
    apply ContinuousLinearMap.ext
    rintro ⟨a, b, c⟩
    simp only [fderiv_phiTriple_apply, h1, h2, h3, inner_zero_right, add_zero, zero_apply]

/-- A nonzero actual full differential forces full unital Jordan generation.
The three membership permutations use the proper-submodule theorem. -/
theorem eq_top_of_fderiv_phiTriple_ne_zero
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hd : fderiv ℝ phiTriple (x, y, z) ≠ 0) : K = ⊤ := by
  by_contra hK
  apply hd
  apply (fderiv_phiTriple_eq_zero_iff x y z).mpr
  exact ⟨glennieVector_eq_zero_of_ne_top K h1 hJ hK y z x hy hz hx,
    glennieVector_eq_zero_of_ne_top K h1 hJ hK z x y hz hx hy,
    glennieVector_eq_zero_of_ne_top K h1 hJ hK x y z hx hy hz⟩

end
end Glennie.Compact.GlennieFullDerivativeR01
