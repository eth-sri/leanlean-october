module

import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
import HypoellipticAleksandrov.Parabolic.MinimumPrinciple
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.Derivatives
import Lean.Elab.Tactic.SolveByElim
import all HypoellipticAleksandrov.Parabolic.Derivatives

open private HypoellipticAleksandrov.Parabolic.hasDerivAt_fderiv_restrict_affine_line from HypoellipticAleksandrov.Parabolic.Derivatives
open private HypoellipticAleksandrov.Parabolic.deriv_deriv_nonpos_of_isLocalMax from HypoellipticAleksandrov.Parabolic.Derivatives
open private HypoellipticAleksandrov.Parabolic.hasDerivAt_affine_line from HypoellipticAleksandrov.Parabolic.Derivatives
section
open private HypoellipticAleksandrov.Parabolic.hasDerivAt_deriv_restrict_affine_line_local from HypoellipticAleksandrov.Parabolic.Derivatives
private alias _semanticProof_95918f25b56b := HypoellipticAleksandrov.Parabolic.hasDerivAt_deriv_restrict_affine_line_local
end


/-!
# Pointwise maximum calculus for the viscous transported operator

For `0 ≤ ε` the viscous transported operator is
`L_ε = ∂σ + B : D_y² + b(y) · ∇_z + ε Δ_z`.  This module proves the pointwise
sign of `L_ε w` at a point where `w` is `C²` and is maximal among all nearby
points of no earlier time.  This is the pointwise step of the usual maximum
argument used for Proposition 2.1.  No derivative of any
moving boundary curve is involved.

## Main definitions

* `viscousTransportedOperator`: the operator `L_ε`.
* `sliceHessian`: the Hessian matrix of a scalar function on `PDE.Vec n`, in the
  project's gradient convention.

## Main results

* `viscousTransportedOperator_nonpos_of_future_localMax`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set Matrix
open scoped MatrixOrder Topology

variable {n : ℕ}

variable (B : FullKineticCoefficient n) (b : PDE.VectorField n)

variable (ε : ℝ) (u : HypoellipticAleksandrov.KineticScalarField n) (p : KineticPoint n)

/-- The viscous transported operator `L_ε u = ∂σ u + B : D_y² u + b(y) · ∇_z u + ε Δ_z u`
at a kinetic point `(σ, y, z)`; `ε = 0` is `transportedForwardOperator`. -/
def viscousTransportedOperator    : ℝ :=
  transportedForwardOperator B b u p +
    ε * ∑ i, kineticVelocityHessian u p i i

/-- Unfolding of `viscousTransportedOperator`. -/
theorem viscousTransportedOperator_apply    :
    viscousTransportedOperator B b ε u p =
      transportedForwardOperator B b u p +
        ε * ∑ i, kineticVelocityHessian u p i i :=
  rfl

/-- At `ε = 0` the viscous operator is the transported forward operator. -/
@[simp] theorem viscousTransportedOperator_zero

    (u : HypoellipticAleksandrov.KineticScalarField n) (p : KineticPoint n) :
    viscousTransportedOperator B b 0 u p = transportedForwardOperator B b u p := by
  simp [viscousTransportedOperator]

/-- The ambient raw-coordinate form `(σ, (y, z)) ↦ u ⟨σ, y, z⟩` of a function on
kinetic points. -/
def rawLift  (u : HypoellipticAleksandrov.KineticScalarField n) :
    ℝ × (PDE.Vec n × PDE.Vec n) → ℝ :=
  fun q => u ⟨q.1, q.2.1, q.2.2⟩

/-- The Hessian matrix of a scalar function of a native vector, indexed as
`D_i (D_j g)`. -/
def sliceHessian  (g : PDE.ScalarField n) (x : PDE.Vec n) : PDE.Mat n :=
  fun i j =>
    (fderiv ℝ ((PDE.classicalGradient g)) x
      (PDE.basisVec i)) j

variable (u : HypoellipticAleksandrov.KineticScalarField n) (p : KineticPoint n)

/-- `diffusedHessian` is the Hessian of the diffused slice. -/
theorem diffusedHessian_eq_sliceHessian   :
    diffusedHessian u p =
      sliceHessian (fun y => u ⟨p.time, y, p.velocity⟩) p.position :=
  rfl

/-- `kineticVelocityHessian` is the Hessian of the transported slice. -/
theorem kineticVelocityHessian_eq_sliceHessian   :
    kineticVelocityHessian u p =
      sliceHessian (fun z => u ⟨p.time, p.position, z⟩) p.velocity :=
  rfl






variable {E : Type*}




private theorem hasDerivAt_deriv_restrict_affine_line_of_contDiffAt
     [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    (hg : ContDiffAt ℝ 2 g x) :
    HasDerivAt (deriv (fun r : ℝ => g (x + r • q)))
      (fderiv ℝ (fderiv ℝ g) x q q) 0 := (_semanticProof_95918f25b56b hg)

private theorem fderiv_fderiv_apply_nonpos_of_isLocalMax_affineLine
     [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    (hg : ContDiffAt ℝ 2 g x)
    (hmax : IsLocalMax (fun r : ℝ => g (x + r • q)) 0) :
    fderiv ℝ (fderiv ℝ g) x q q ≤ 0 := (deriv_deriv_nonpos_of_isLocalMax hmax (hasDerivAt_deriv_restrict_affine_line_of_contDiffAt hg)
  (ContinuousAt.comp'
    (Eq.mpr (id (congrArg (ContinuousAt g) (Eq.trans (congrArg (HAdd.hAdd x) (zero_smul ℝ q)) (add_zero x))))
      (ContDiffAt.continuousAt hg))
    (HasDerivAt.continuousAt (hasDerivAt_affine_line x q 0))))

variable {n : ℕ} {g : PDE.ScalarField n} {x : PDE.Vec n}

section
variable (hg : ContDiffAt ℝ 2 g x)

include hg
/-- Entries of `sliceHessian` are second Fréchet derivatives. -/
theorem sliceHessian_apply_eq_sndFDeriv   (i j : Fin n) :
    sliceHessian g x i j =
      fderiv ℝ (fderiv ℝ g) x (PDE.basisVec i) (PDE.basisVec j) := by
  have hsecond : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt

  change (fderiv ℝ (fun y  => fun j =>
      fderiv ℝ g y (PDE.basisVec j)) x (PDE.basisVec i)) j = _
  rw [fderiv_pi (by
      intro j
      exact (hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) x)).differentiableAt)]


  simpa [ContinuousLinearMap.flip_apply] using (congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L (PDE.basisVec i)) ((hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) x)).fderiv))

/-- The quadratic form of `sliceHessian` is the second Fréchet derivative. -/
theorem sliceHessian_quadratic_eq
    (q : PDE.Vec n) :
    dotProduct q ((sliceHessian g x).mulVec q) =
      fderiv ℝ (fderiv ℝ g) x q q := by
  let H := fderiv ℝ (fderiv ℝ g) x
  change (∑ i : Fin n, q i * ∑ j : Fin n, sliceHessian g x i j * q j) = H q q
  simp_rw [sliceHessian_apply_eq_sndFDeriv hg]
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

/-- `sliceHessian` of a `C²` function is symmetric. -/
theorem sliceHessian_isSymm   :
    (sliceHessian g x).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  rw [sliceHessian_apply_eq_sndFDeriv hg, sliceHessian_apply_eq_sndFDeriv hg]
  exact (hg.isSymmSndFDerivAt (by norm_num)).eq (PDE.basisVec j) (PDE.basisVec i)

/-- The negative Hessian is positive semidefinite at a local maximum. -/
theorem neg_sliceHessian_posSemidef_of_localMax
    (hmax : IsLocalMax g x) :
    (-sliceHessian g x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · simp_all [sliceHessian, sliceHessian_isSymm]
  · intro q
    rw [neg_mulVec, dotProduct_neg]

    change -dotProduct q ((sliceHessian g x).mulVec q) ≥ 0
    rw [sliceHessian_quadratic_eq hg q]
    exact neg_nonneg.mpr
      (fderiv_fderiv_apply_nonpos_of_isLocalMax_affineLine hg (by
          have hmaxAtLineZero : IsLocalMax g (x + (0 : ℝ) • q) := by
            simpa only [zero_smul, add_zero] using hmax
          simpa only [Function.comp_def] using
            hmaxAtLineZero.comp_continuous (g := fun r : ℝ => x + r • q)
              (_root_.HypoellipticAleksandrov.Parabolic.hasDerivAt_affine_line x q 0).continuousAt))
end


/-- A positive semidefinite coefficient contracts the Hessian at a local maximum
to a nonpositive number. -/
theorem matrixContraction_sliceHessian_nonpos_of_localMax  {A : PDE.Mat n}
    (hg : ContDiffAt ℝ 2 g x) (hmax : IsLocalMax g x) (hA : A.PosSemidef) :
    matrixContraction A (sliceHessian g x) ≤ 0 := by


  rw [matrixContraction_eq_trace_mul_of_isSymm A _ (sliceHessian_isSymm hg)]
  calc
    (A * sliceHessian g x).trace = -((A * (-sliceHessian g x)).trace) := by simp
    _ ≤ 0 := neg_nonpos.mpr (trace_mul_nonneg_of_posSemidef hA (neg_sliceHessian_posSemidef_of_localMax hg hmax))

/-- The Laplacian (trace of the Hessian) is nonpositive at a local maximum. -/
theorem sum_diag_sliceHessian_nonpos_of_localMax
    (hg : ContDiffAt ℝ 2 g x) (hmax : IsLocalMax g x) :
    ∑ i, sliceHessian g x i i ≤ 0 := by
  have h := matrixContraction_sliceHessian_nonpos_of_localMax hg hmax
    (Matrix.PosSemidef.one  )
  have hc : matrixContraction (1 : PDE.Mat n) (sliceHessian g x) =
      ∑ i, sliceHessian g x i i := by
    simp [matrixContraction, Matrix.one_apply]
  rw [hc] at h
  exact h

/-- The gradient of a differentiable function vanishes at a local maximum. -/
theorem classicalGradient_eq_zero_of_localMax
    (hg : DifferentiableAt ℝ g x) (hmax : IsLocalMax g x) :
    PDE.classicalGradient g x = 0 := by
  ext i
  change fderiv ℝ g x (PDE.basisVec i) = 0
  rw [hmax.hasFDerivAt_eq_zero hg.hasFDerivAt]
  rfl

/-- One-sided time calculus: if `f` is differentiable at `t₀` and `f t ≤ f t₀` for
all `t ≥ t₀` near `t₀`, then `deriv f t₀ ≤ 0`. -/
theorem deriv_nonpos_of_future_localMax {f : ℝ → ℝ} {t₀ : ℝ}
    (hf : DifferentiableAt ℝ f t₀) (hmax : ∀ᶠ t in 𝓝 t₀, t₀ ≤ t → f t ≤ f t₀) :
    deriv f t₀ ≤ 0 := by


  have h := (show IsLocalMaxOn f (Ici t₀) t₀ by
      show ∀ᶠ t in 𝓝[Ici t₀] t₀, f t ≤ f t₀
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hmax] with t ht hti
      exact ht hti).hasFDerivWithinAt_nonpos hf.hasDerivAt.hasFDerivAt.hasFDerivWithinAt (by
      apply mem_posTangentConeAt_of_segment_subset
      intro t ht
      exact (segment_subset_Icc (𝕜 := ℝ) (by linarith : t₀ ≤ t₀ + 1) ht).1)
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul] using h

/-- Anisotropic pointwise regularity used by the maximum argument: differentiable in
time, `C²` in the diffused coordinate and `C²` in the transported coordinate.  No
joint or mixed regularity, and in particular no second time derivative, is required. -/
structure IsSliceRegularAt {n : ℕ} (w : HypoellipticAleksandrov.KineticScalarField n) (p : KineticPoint n) : Prop where
  /-- Differentiability of the time slice. -/
  time : DifferentiableAt ℝ (fun t => w ⟨t, p.position, p.velocity⟩) p.time
  /-- `C²` regularity of the diffused-coordinate slice. -/
  position : ContDiffAt ℝ 2 (fun y => w ⟨p.time, y, p.velocity⟩) p.position
  /-- `C²` regularity of the transported-coordinate slice. -/
  velocity : ContDiffAt ℝ 2 (fun z => w ⟨p.time, p.position, z⟩) p.velocity

variable {n : ℕ}

variable {w : HypoellipticAleksandrov.KineticScalarField n} {p : KineticPoint n}

/-- Joint `C²` regularity in raw coordinates gives slice regularity. -/
theorem IsSliceRegularAt.of_contDiffAt
    (hw : ContDiffAt ℝ 2 (rawLift w) (p.time, p.position, p.velocity)) :
    IsSliceRegularAt w p := by



  refine ⟨?_, ?_, ?_⟩
  ·
    exact (ContDiffAt.comp
      p.time hw ((contDiffAt_id.prodMk (contDiffAt_const.prodMk contDiffAt_const)))).differentiableAt (by norm_num)
  ·
    exact ContDiffAt.comp (g := rawLift w) (f := (((fun y : PDE.Vec n => (p.time, y, p.velocity)))))
      p.position hw ((contDiffAt_const.prodMk (contDiffAt_id.prodMk contDiffAt_const)))
  ·
    exact ContDiffAt.comp (g := rawLift w) (f := (((fun z : PDE.Vec n => (p.time, p.position, z)))))
      p.velocity hw ((contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id)))

/-- Local maximum along a continuous curve through `p`. -/
theorem eventually_future_curve
    (hmax : ∀ᶠ q in 𝓝 p, p.time ≤ q.time → w q ≤ w p)
    {α : Type} [TopologicalSpace α] {a : α} {c : α → KineticPoint n}
    (hc : Continuous c) (hca : c a = p) :
    ∀ᶠ x in 𝓝 a, p.time ≤ (c x).time → w (c x) ≤ w p := by

  exact (show Tendsto c (𝓝 a) (𝓝 p) by
      rw [← hca]
      exact hc.continuousAt.tendsto).eventually hmax

/-- Pointwise sign of the viscous transported operator at a maximum over all nearby
points of no earlier time.  The point needs only the anisotropic slice regularity
and a positive semidefinite coefficient matrix. -/
theorem viscousTransportedOperator_nonpos_of_future_localMax
    {B : FullKineticCoefficient n} {b : PDE.VectorField n} {ε : ℝ}
    {w : HypoellipticAleksandrov.KineticScalarField n} {p : KineticPoint n}
    (hε : 0 ≤ ε)
    (hw : IsSliceRegularAt w p)
    (hmax : ∀ᶠ q in 𝓝 p, p.time ≤ q.time → w q ≤ w p)
    (hB : (B p.time p.position p.velocity).PosSemidef) :
    viscousTransportedOperator B b ε w p ≤ 0 := by

  have hzmax : IsLocalMax (fun z => w ⟨p.time, p.position, z⟩) p.velocity := by
    have := eventually_future_curve hmax

      (KineticPoint.continuous_mk continuous_const continuous_const continuous_id) rfl
    filter_upwards [this] with z hz
    exact hz le_rfl
  have htmax : ∀ᶠ t in 𝓝 p.time, p.time ≤ t → w ⟨t, p.position, p.velocity⟩ ≤ w p :=
    eventually_future_curve hmax

      (KineticPoint.continuous_mk continuous_id continuous_const continuous_const) rfl
  have htime : kineticTimeDerivative w p ≤ 0 :=
    deriv_nonpos_of_future_localMax (hw.time)
      htmax
  have hdiff : matrixContraction (B p.time p.position p.velocity) (diffusedHessian w p) ≤ 0 := by
    rw [diffusedHessian_eq_sliceHessian]
    exact matrixContraction_sliceHessian_nonpos_of_localMax
      hw.position (by
          have := eventually_future_curve hmax

            (KineticPoint.continuous_mk continuous_const continuous_id continuous_const) rfl
          filter_upwards [this] with y hy
          exact hy le_rfl) hB
  have hgrad : kineticVelocityGradient w p = 0 := by
    have h := classicalGradient_eq_zero_of_localMax
      (hw.velocity.differentiableAt (by norm_num)) hzmax
    exact h

  rw [viscousTransportedOperator_apply, transportedForwardOperator_apply, hgrad]
  simp only [PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
    fullKineticCoefficientAt_apply]
  have := mul_nonneg hε (neg_nonneg.mpr (show ∑ i, kineticVelocityHessian w p i i ≤ 0 by
      rw [kineticVelocityHessian_eq_sliceHessian]
      exact sum_diag_sliceHessian_nonpos_of_localMax hw.velocity hzmax))
  linarith

end HypoellipticAleksandrov.KineticAleksandrov
