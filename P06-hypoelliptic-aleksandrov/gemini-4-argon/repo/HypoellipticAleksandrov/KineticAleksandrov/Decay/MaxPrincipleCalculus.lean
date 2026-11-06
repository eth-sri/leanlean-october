module

import HypoellipticAleksandrov.Parabolic.ScalarClassical
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith

public import HypoellipticAleksandrov.KineticAleksandrov.Operator

/-!
# Pointwise calculus for the transported moving-domain maximum principle

Scalar Hessian calculations are applied to the diffused slice. No mixed or
second time derivatives are required.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open Filter Set Matrix
open scoped MatrixOrder Topology

private theorem hasDerivAt_affine_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x q : E) (s : ℝ) :
    HasDerivAt (fun r : ℝ => x + r • q) q s := by
  simpa only [one_smul] using
    ((hasDerivAt_id' (𝕜 := ℝ) s).smul_const q).const_add x

private theorem deriv_deriv_nonpos_of_isLocalMax
    {f : ℝ → ℝ} {a c : ℝ}
    (hmax : IsLocalMax f a)
    (hsecond : HasDerivAt (deriv f) c a)
    (hcont : ContinuousAt f a) :
    c ≤ 0 := by
  by_contra hc
  have hcpos : 0 < c := lt_of_not_ge hc
  have hmin : IsLocalMin f a :=
    isLocalMin_of_deriv_deriv_pos
      (by simpa only [hsecond.deriv] using hcpos)
      hmax.deriv_eq_zero hcont
  have heq : f =ᶠ[𝓝 a] fun _ => f a := by
    filter_upwards [hmax, hmin] with y hymax hymin
    exact le_antisymm hymax hymin
  have hderivEq : deriv f =ᶠ[𝓝 a] fun _ => 0 := by
    filter_upwards [heq.deriv] with y hy
    rw [hy]
    exact deriv_const y (f a)
  have : c = 0 := by
    calc
      c = deriv (deriv f) a := hsecond.deriv.symm
      _ = deriv (fun _ => 0) a := hderivEq.deriv_eq
      _ = 0 := deriv_const _ _
  exact hcpos.ne' this

private theorem hasDerivAt_fderiv_restrict_affine_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hsecond : HasFDerivAt (fderiv ℝ g) H x) :
    HasDerivAt
      (fun r : ℝ => fderiv ℝ g (x + r • q) q)
      (H q q) 0 := by
  have hline : HasDerivAt (fun r : ℝ => x + r • q) q 0 :=
    hasDerivAt_affine_line x q 0
  have hsecond' : HasFDerivAt (fderiv ℝ g) H (x + (0 : ℝ) • q) := by
    simpa only [zero_smul, add_zero] using hsecond
  have hgrad : HasDerivAt (fun r : ℝ => fderiv ℝ g (x + r • q)) (H q) 0 :=
    hsecond'.comp_hasDerivAt 0 hline
  simpa only [zero_smul, add_zero, map_zero] using
    hgrad.clm_apply (hasDerivAt_const (x := 0) (c := q))

private theorem fderiv_fderiv_apply_nonpos_of_isLocalMax_affineLine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    (hg : ContDiffAt ℝ 2 g x)
    (hmax : IsLocalMax (fun r : ℝ => g (x + r • q)) 0) :
    fderiv ℝ (fderiv ℝ g) x q q ≤ 0 := by
  have hlineCont : ContinuousAt (fun r : ℝ => x + r • q) 0 :=
    (hasDerivAt_affine_line x q 0).continuousAt
  have hgAtLineZero : ContinuousAt g (x + (0 : ℝ) • q) := by
    simpa only [zero_smul, add_zero] using hg.continuousAt
  have hcompCont :=
    hgAtLineZero.comp' (f := fun r : ℝ => x + r • q) hlineCont
  have _h_inl_18 : HasDerivAt (deriv (fun r : ℝ => g (x + r • q))) (fderiv ℝ (fderiv ℝ g) x q q) 0 := by
    have hgGradDiffAt : DifferentiableAt ℝ (fderiv ℝ g) x :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hEvalLine : HasDerivAt
        (fun r : ℝ => fderiv ℝ g (x + r • q) q)
        (fderiv ℝ (fderiv ℝ g) x q q) 0 :=
      hasDerivAt_fderiv_restrict_affine_line hgGradDiffAt.hasFDerivAt
    have hgEventually : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 g y :=
      hg.eventually (by norm_num)
    have hgEventuallyAtLineZero :
        ∀ᶠ y in 𝓝 (x + (0 : ℝ) • q), ContDiffAt ℝ 2 g y := by
      simpa only [zero_smul, add_zero] using hgEventually
    apply hEvalLine.congr_of_eventuallyEq
    filter_upwards [
      (hasDerivAt_affine_line x q 0).continuousAt hgEventuallyAtLineZero] with r hr
    change ContDiffAt ℝ 2 g (x + r • q) at hr
    exact (hr.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
      r (hasDerivAt_affine_line x q r) |>.deriv
  exact deriv_deriv_nonpos_of_isLocalMax hmax
    _h_inl_18 hcompCont

private theorem scalarSpatialHessian_apply_eq_sndFDeriv {n : ℕ}
    {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)
    (i j : Fin n) :
    scalarSpatialHessian u z i j =
      fderiv ℝ (fderiv ℝ (fun y : PDE.Vec n => u (z.1, y))) z.2
        (PDE.basisVec i) (PDE.basisVec j) := by
  let g : PDE.Vec n → ℝ := fun y => u (z.1, y)
  have hsecond :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hdiff : ∀ j : Fin n,
      DifferentiableAt ℝ (fun y : PDE.Vec n => fderiv ℝ g y (PDE.basisVec j)) z.2 := by
    intro j
    exact (hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) z.2)).differentiableAt
  change (fderiv ℝ (fun y : PDE.Vec n => fun j =>
      fderiv ℝ g y (PDE.basisVec j)) z.2 (PDE.basisVec i)) j = _
  rw [fderiv_pi hdiff]
  have hjapply := congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L (PDE.basisVec i)) ((hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) z.2)).fderiv)
  simpa [ContinuousLinearMap.flip_apply] using hjapply

private theorem scalarSpatialHessian_isSymm_of_contDiffAt {n : ℕ}
    {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2) :
    (scalarSpatialHessian u z).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  rw [scalarSpatialHessian_apply_eq_sndFDeriv hu,
    scalarSpatialHessian_apply_eq_sndFDeriv hu]
  exact
    (hu.isSymmSndFDerivAt (by norm_num)).eq (PDE.basisVec j) (PDE.basisVec i)

private theorem neg_scalarSpatialHessian_posSemidef_of_spatial_localMax
    {n : ℕ} {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)
    (hmax : IsLocalMax (fun y : PDE.Vec n => u (z.1, y)) z.2) :
    (-scalarSpatialHessian u z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    change -scalarSpatialHessian u z j i = -scalarSpatialHessian u z i j
    exact congrArg Neg.neg ((scalarSpatialHessian_isSymm_of_contDiffAt hu).apply i j)
  · intro q
    rw [neg_mulVec, dotProduct_neg]
    have hlineMax : IsLocalMax
        (fun r : ℝ => u (z.1, z.2 + r • q)) 0 := by
      have hmaxAtLineZero : IsLocalMax (fun y : PDE.Vec n => u (z.1, y))
          (z.2 + (0 : ℝ) • q) := by
        simpa only [zero_smul, add_zero] using hmax
      simpa only [Function.comp_def, id_eq] using hmaxAtLineZero.comp_continuous
        (g := fun r : ℝ => z.2 + r • q)
        (hasDerivAt_affine_line z.2 q 0).continuousAt
    change -dotProduct q
      ((scalarSpatialHessian u z).mulVec q) ≥ 0
    have _h_inl_21 : dotProduct q ((scalarSpatialHessian u z).mulVec q) =
      fderiv ℝ (fderiv ℝ (fun y : PDE.Vec n => u (z.1, y))) z.2 q q := by
      let g : PDE.Vec n → ℝ := fun y => u (z.1, y)
      let H := fderiv ℝ (fderiv ℝ g) z.2
      change (∑ i : Fin n, q i * ∑ j : Fin n,
          scalarSpatialHessian u z i j * q j) = H q q
      simp_rw [scalarSpatialHessian_apply_eq_sndFDeriv hu]
      change (∑ i : Fin n, q i * ∑ j : Fin n,
          H (PDE.basisVec i) (PDE.basisVec j) * q j) = H q q
      calc
        (∑ i : Fin n, q i * ∑ j : Fin n,
            H (PDE.basisVec i) (PDE.basisVec j) * q j) =
            ∑ i : Fin n, q i * H (PDE.basisVec i)
              (∑ j : Fin n, q j • PDE.basisVec j) := by
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          rw [map_sum]
          simp only [map_smul, smul_eq_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = ∑ i : Fin n, q i * H (PDE.basisVec i) q := by
          rw [PDE.sum_smul_basisVec]
        _ = H (∑ i : Fin n, q i • PDE.basisVec i) q := by
          rw [map_sum, _root_.sum_apply]
          simp only [map_smul, _root_.smul_apply, smul_eq_mul]
        _ = H q q := by rw [PDE.sum_smul_basisVec]
    rw [_h_inl_21]
    exact neg_nonneg.mpr
      (fderiv_fderiv_apply_nonpos_of_isLocalMax_affineLine hu hlineMax)

private theorem trace_mul_nonneg_of_posSemidef {n : ℕ} {A H : PDE.Mat n}
    (hA : A.PosSemidef) (hH : H.PosSemidef) :
    0 ≤ (A * H).trace := by
  classical
  let S : PDE.Mat n := CFC.sqrt H
  have hS : S.PosSemidef := by
    dsimp [S]
    exact CFC.sqrt_nonneg H |>.posSemidef
  have hconj := hA.mul_mul_conjTranspose_same S
  calc
    0 ≤ (S * A * Sᴴ).trace := hconj.trace_nonneg
    _ = (S * A * S).trace := by rw [hS.isHermitian.eq]
    _ = (A * S * S).trace := (Matrix.trace_mul_cycle A S S).symm
    _ = (A * (S * S)).trace := by rw [Matrix.mul_assoc]
    _ = (A * H).trace := by rw [show S * S = H by
      dsimp [S]
      exact CFC.sqrt_mul_sqrt_self H hH.nonneg]

private theorem matrixContraction_nonpos_of_psd_neg {n } {A H : PDE.Mat n}
    (hA : A.PosSemidef) (hH : (-H).PosSemidef) (hHsymm : H.IsSymm) :
    matrixContraction A H ≤ 0 := by
  have htrace := trace_mul_nonneg_of_posSemidef hA hH
  rw [matrixContraction_eq_trace_mul_of_isSymm A H hHsymm]
  calc
    (A * H).trace = -((A * (-H)).trace) := by simp
    _ ≤ 0 := neg_nonpos.mpr htrace

/- A positive semidefinite diffusion contracts the Hessian at a diffused
slice maximum to a nonpositive scalar. -/
theorem diffused_contraction_nonpos_of_localMax {d u} {p : KineticPoint d} {A : PDE.Mat d}
    (hu : ContDiffAt ℝ 2 (fun y => u ⟨p.time, y, p.velocity⟩) p.position)
    (hmax : IsLocalMax (fun y => u ⟨p.time, y, p.velocity⟩) p.position)
    (hA : A.PosSemidef) :
    matrixContraction A (diffusedHessian u p) ≤ 0 := by
  let f : TimeVelocity d → ℝ := fun z => u ⟨z.1, z.2, p.velocity⟩
  have heq : scalarSpatialHessian f (p.time, p.position) = diffusedHessian u p := rfl
  rw [← heq]
  exact matrixContraction_nonpos_of_psd_neg hA
    (neg_scalarSpatialHessian_posSemidef_of_spatial_localMax hu hmax)
    (scalarSpatialHessian_isSymm_of_contDiffAt hu)

/- A differentiable transported slice has zero gradient at a local maximum. -/
end HypoellipticAleksandrov.KineticAleksandrov.Decay
