module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import PDEFoundation.Sobolev.ClassicalGradient
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Algebra.Module.Determinant

/-!
# Time--velocity derivatives

This module supplies velocity-only coordinate derivatives of scalar functions
on the product carrier `TimeVelocity d`, together with the coordinate bridge
for determinants of continuous linear endomorphisms of that carrier.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Matrix
open scoped BigOperators Topology

/-- Differentiate a field of linear maps evaluated at a fixed vector. -/
theorem fderiv_eval_const_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {c : E → E →L[ℝ] F} {x : E}
    (hc : DifferentiableAt ℝ c x) (w v : E) :
    fderiv ℝ (fun y => c y w) x v = fderiv ℝ c x v w := by
  rw [(hc.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv]
  simp

private theorem deriv_deriv_nonpos_of_isLocalMax
    {f : ℝ → ℝ} {a : ℝ} (hmax : IsLocalMax f a) (hcont : ContinuousAt f a) :
    deriv (deriv f) a ≤ 0 := by
  by_contra! h
  have hmin := isLocalMin_of_deriv_deriv_pos h hmax.deriv_eq_zero hcont
  have heq : f =ᶠ[𝓝 a] fun _ => f a := by
    filter_upwards [hmax, hmin] with y h₁ h₂ using le_antisymm h₁ h₂
  simpa [heq.deriv.deriv_eq] using h

/-- The second derivative chain rule for a map with constant first derivative. -/
theorem fderiv_fderiv_comp_constDeriv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → ℝ} {φ : F → E} {x : F} {L : F →L[ℝ] E}
    (hg : ContDiffAt ℝ 2 g (φ x)) (hφ : ∀ y, HasFDerivAt φ L y) (v w : F) :
    fderiv ℝ (fderiv ℝ (g ∘ φ)) x v w = fderiv ℝ (fderiv ℝ g) (φ x) (L v) (L w) := by
  let R := (ContinuousLinearMap.compL ℝ F E ℝ).flip L
  have hd := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : fderiv ℝ (g ∘ φ) =ᶠ[𝓝 x] R ∘ fderiv ℝ g ∘ φ := by
    filter_upwards [(hφ x).continuousAt (hg.eventually (by norm_num))] with y hy
    change ContDiffAt ℝ 2 g (φ y) at hy
    exact ((hy.differentiableAt (by norm_num)).hasFDerivAt.comp y (hφ y)).fderiv
  rw [heq.fderiv_eq, (R.hasFDerivAt.comp x (hd.hasFDerivAt.comp x (hφ x))).fderiv]
  rfl

/-- Second derivatives are linear under subtraction of two locally `C²` functions. -/
theorem fderiv_fderiv_fun_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => f y - g y)) x =
      fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x := by
  have heq : fderiv ℝ (fun z => f z - g z) =ᶠ[𝓝 x] fun y => fderiv ℝ f y - fderiv ℝ g y := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y h₁ h₂
    exact fderiv_fun_sub (h₁.differentiableAt (by norm_num)) (h₂.differentiableAt (by norm_num))
  rw [heq.fderiv_eq, fderiv_fun_sub
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]

/-- At a local maximum of a locally `C²` function the second derivative is nonpositive. -/
theorem fderiv_fderiv_apply_nonpos_of_isLocalMax_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E} (hg : ContDiffAt ℝ 2 g x) (hmax : IsLocalMax g x) :
    fderiv ℝ (fderiv ℝ g) x q q ≤ 0 := by
  let φ : ℝ → E := fun r => x + r • q
  let L := (ContinuousLinearMap.id ℝ ℝ).smulRight q
  have hφ : ∀ y, HasFDerivAt φ L y := fun y =>
    ((hasFDerivAt_id y).smul_const q).const_add x
  have hzero : φ 0 = x := by simp [φ]
  have hmax' : IsLocalMax g (φ 0) := by simpa [hzero] using hmax
  have hcont : ContinuousAt g (φ 0) := by simpa [hzero] using hg.continuousAt
  have h₂ := fderiv_fderiv_comp_constDeriv (x := 0) (g := g)
    (by simpa [hzero] using hg) hφ 1 1
  have hφc : ContDiffAt ℝ 2 φ 0 := by dsimp [φ]; fun_prop
  have hd := (((show ContDiffAt ℝ 2 g (φ 0) from by simpa [hzero] using hg).comp 0 hφc).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : deriv (deriv (g ∘ φ)) 0 = fderiv ℝ (fderiv ℝ (g ∘ φ)) 0 1 1 := by
    change fderiv ℝ (fun t => fderiv ℝ (g ∘ φ) t 1) 0 1 = _
    exact fderiv_eval_const_apply hd _ _
  have hn := deriv_deriv_nonpos_of_isLocalMax
    (hmax'.comp_continuous (hφ 0).continuousAt) (hcont.comp (hφ 0).continuousAt)
  rw [heq, h₂] at hn
  simpa [L, hzero] using hn

section
variable {d : ℕ} (u : TimeVelocity d → ℝ) (z : TimeVelocity d)
include d u z

/-- The derivative of `u` in the unit time direction at `z`. -/
def timeDerivative : ℝ :=
  fderiv ℝ u z (1, 0)

/-- The velocity gradient of `u` at `z`, evaluated in the standard velocity directions. -/
def velocityGradient : PDE.Vec d :=
  fun i ↦ fderiv ℝ u z (0, Pi.single i 1)

/-- The velocity Hessian of `u` at `z`, with both derivatives in velocity directions. -/
def velocityHessian : PDE.Mat d :=
  fun i j ↦
    fderiv ℝ (fderiv ℝ u) z (0, Pi.single i 1) (0, Pi.single j 1)

end

section
variable {d : ℕ}

theorem timeDerivative_continuous {f : TimeVelocity d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (timeDerivative f) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

theorem timeDerivative_compact {f : TimeVelocity d → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (timeDerivative f) :=
  hf.fderiv_apply ℝ (1, 0)

theorem timeDerivative_tsupport (f : TimeVelocity d → ℝ) :
    tsupport (timeDerivative f) ⊆ tsupport f := tsupport_fderiv_apply_subset ℝ (1, 0)

theorem velocityGradient_contDiff {f : TimeVelocity d → ℝ} {i : Fin d}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (fun z => velocityGradient f z i) :=
  (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

end

section
variable {d : ℕ}

section
variable {f : TimeVelocity d → ℝ} {i : Fin d}

theorem velocityGradient_continuous
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (fun z => velocityGradient f z i) :=
  (velocityGradient_contDiff hf).continuous

theorem velocityGradient_compact
    (hf : HasCompactSupport f) : HasCompactSupport (fun z => velocityGradient f z i) :=
  hf.fderiv_apply ℝ (0, Pi.single i 1)

end

theorem velocityGradient_tsupport {i : Fin d} (f : TimeVelocity d → ℝ) :
    tsupport (fun z => velocityGradient f z i) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset ℝ (0, Pi.single i 1)

section
variable {f : TimeVelocity d → ℝ} {i j : Fin d}

theorem velocityHessian_continuous
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (fun z => velocityHessian f z i j) :=
  (((contDiff_infty_iff_fderiv.mp hf).2.continuous_fderiv (by simp)).clm_apply
    continuous_const).clm_apply continuous_const

theorem velocityHessian_compact
    (hf : HasCompactSupport f) : HasCompactSupport (fun z => velocityHessian f z i j) :=
  (hf.fderiv ℝ |>.fderiv ℝ).comp_left
    (g := fun L : TimeVelocity d →L[ℝ] TimeVelocity d →L[ℝ] ℝ =>
      L (0, Pi.single i 1) (0, Pi.single j 1)) rfl

end

section
variable {u : TimeVelocity d → ℝ} (hu : ContDiff ℝ 2 u)
include hu

/-- A globally `C²` scalar function has a `C¹` velocity gradient. -/
theorem contDiff_velocityGradient : ContDiff ℝ 1 (velocityGradient u) := by
  rw [contDiff_pi]
  intro i
  exact (hu.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)

/-- The velocity Hessian of a globally `C²` scalar function is symmetric. -/
theorem velocityHessian_isSymm (z : TimeVelocity d) : (velocityHessian u z).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  simpa [velocityHessian] using
    (hu.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq
      ((0 : ℝ), Pi.single j 1) ((0 : ℝ), Pi.single i 1)

end

/-- The coordinate matrix of a pulled-back bilinear form evaluates to the same quadratic form. -/
theorem coordinateQuadraticForm_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E →L[ℝ] E →L[ℝ] ℝ) (L : PDE.Vec d →L[ℝ] E) (q : PDE.Vec d) :
    dotProduct q (Matrix.mulVec (fun i j => H (L (PDE.basisVec i)) (L (PDE.basisVec j))) q) =
      H (L q) (L q) := by
  change (∑ i, q i * ∑ j, H (L (PDE.basisVec i)) (L (PDE.basisVec j)) * q j) = _
  calc
    _ = ∑ i, q i * H (L (PDE.basisVec i)) (L q) := by
      refine Finset.sum_congr rfl fun i _ => congrArg (q i * ·) ?_
      conv_rhs => rw [← PDE.sum_smul_basisVec q]
      simp only [map_sum, map_smul, smul_eq_mul]
      simp_rw [mul_comm (q _) (H _ _)]
    _ = _ := by
      conv_rhs => arg 1; rw [← PDE.sum_smul_basisVec q]
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]

end

/-- The coordinate velocity Hessian represents the second Fréchet derivative on pure
velocity directions. -/
theorem velocityHessian_quadratic_eq
    {d : ℕ} {u : TimeVelocity d → ℝ} (z : TimeVelocity d) (q : PDE.Vec d) :
    dotProduct q ((velocityHessian u z).mulVec q) =
      fderiv ℝ (fderiv ℝ u) z (0, q) (0, q) := coordinateQuadraticForm_eq _ (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d)) q

section
variable {d : ℕ} {u : TimeVelocity d → ℝ} {z : TimeVelocity d}

/-- The ordinary derivative along a time slice is the joint time derivative. -/
theorem time_slice_hasDerivAt (hu : DifferentiableAt ℝ u z) :
    HasDerivAt (fun t : ℝ => u (t, z.2)) (timeDerivative u z) z.1 := by
  simpa only [timeDerivative, Function.comp_def] using
    hu.hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id' (𝕜 := ℝ) z.1).prodMk (hasDerivAt_const z.1 z.2))

/-- A local maximum against the time past has nonnegative time derivative. -/
theorem timeDerivative_nonneg_of_localMaxOn_past {c : ℝ} (hu : DifferentiableAt ℝ u z)
    (hm : IsLocalMaxOn (fun t : ℝ => u (t, z.2) - c) (Set.Iic z.1) z.1) :
    0 ≤ timeDerivative u z := by
  have hseg : segment ℝ z.1 (z.1 - 1) ⊆ Set.Iic z.1 := by
    rw [segment_symm]
    exact (segment_subset_Icc (sub_le_self _ zero_le_one)).trans fun _ h => h.2
  have hneg : (-1 : ℝ) ∈ posTangentConeAt (Set.Iic z.1) z.1 := by
    simpa using sub_mem_posTangentConeAt_of_segment_subset hseg
  have h := hm.hasFDerivWithinAt_nonpos ((time_slice_hasDerivAt hu).sub_const c).hasDerivWithinAt hneg
  simpa using h

private def velocitySlope (p : PDE.Vec d) : PDE.Vec d →L[ℝ] ℝ :=
  ∑ i, p i • ContinuousLinearMap.proj i

private theorem velocitySlope_apply (p q : PDE.Vec d) : velocitySlope p q = PDE.vecDot p q := by
  simp [velocitySlope, PDE.vecDot, smul_eq_mul]

variable {h : ℝ} {p v₀ : PDE.Vec d}

private theorem hasFDerivAt_velocityAffine (v : PDE.Vec d) :
    HasFDerivAt (fun w => h + PDE.vecDot p (w - v₀)) (velocitySlope p) v := by
  simpa only [velocitySlope_apply, Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
    (((velocitySlope p).hasFDerivAt.comp v ((hasFDerivAt_id v).sub_const v₀)).const_add h)

/-- At a local maximum against an affine velocity function, the velocity slopes agree. -/
theorem velocityGradient_eq_of_spatial_localMax_affineContact
    (hu : DifferentiableAt ℝ u z)
    (hm : IsLocalMax (fun v : PDE.Vec d => u (z.1, v) - (h + PDE.vecDot p (v - v₀))) z.2) :
    velocityGradient u z = p := by
  have hd := hu.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
  have hz := sub_eq_zero.mp (hm.hasFDerivAt_eq_zero (hd.sub (hasFDerivAt_velocityAffine z.2)))
  ext i
  have hi := DFunLike.congr_fun hz (Pi.single i 1)
  rw [velocitySlope_apply] at hi
  change fderiv ℝ u z (0, Pi.single i 1) = p ⬝ᵥ Pi.single i 1 at hi
  simpa only [velocityGradient, dotProduct_single_one] using hi

/-- The Hessian at a local spatial maximum against an affine function is negative semidefinite. -/
theorem neg_velocityHessian_posSemidef_of_spatial_localMax_affineContact_of_contDiffAt
    (hu : ContDiffAt ℝ 2 u z)
    (hcontact : IsLocalMax (fun v : PDE.Vec d => u (z.1, v) - (h + PDE.vecDot p (v - v₀))) z.2) :
    (-velocityHessian u z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · refine Matrix.IsHermitian.neg (Matrix.IsHermitian.ext fun i j => ?_)
    simp only [star_trivial, velocityHessian]
    exact hu.isSymmSndFDerivAt (by norm_num) _ _
  · intro q
    let g : PDE.Vec d → ℝ := fun v => u (z.1, v)
    let ell : PDE.Vec d → ℝ := fun v => h + PDE.vecDot p (v - v₀)
    have hell (v : PDE.Vec d) : HasFDerivAt ell (velocitySlope p) v := hasFDerivAt_velocityAffine v
    have hec : ContDiffAt ℝ 2 ell z.2 := by dsimp [ell, PDE.vecDot]; fun_prop
    have hg : ContDiffAt ℝ 2 g z.2 := hu.comp z.2 (contDiffAt_const.prodMk contDiffAt_id)
    have hn := fderiv_fderiv_apply_nonpos_of_isLocalMax_of_contDiffAt (q := q) (hg.sub hec) hcontact
    rw [fderiv_fderiv_fun_sub hg hec, show fderiv ℝ ell = fun _ => velocitySlope p from funext fun v => (hell v).fderiv,
      fderiv_const_apply, sub_zero] at hn
    change fderiv ℝ (fderiv ℝ (u ∘ fun v : PDE.Vec d => (z.1, v))) z.2 q q ≤ 0 at hn
    rw [fderiv_fderiv_comp_constDeriv hu (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1)] at hn
    change fderiv ℝ (fderiv ℝ u) z (0, q) (0, q) ≤ 0 at hn
    simpa only [star_trivial, Matrix.neg_mulVec, dotProduct_neg, velocityHessian_quadratic_eq] using
      neg_nonneg.mpr hn

end

/-- A continuous linear equivalence from time--velocity points to `Fin (d + 1)` coordinates. -/
noncomputable def timeVelocityCoordinates (d : ℕ) :
    TimeVelocity d ≃L[ℝ] (Fin (d + 1) → ℝ) :=
  (((ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ (PDE.Vec d))).symm.trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 1) (Fin d)
      (fun _ ↦ ℝ)).symm).trans
    ((ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (1 + d) ↦ ℝ)
        finSumFinEquiv).trans
      (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (d + 1) ↦ ℝ)
        (finAddFlip (m := 1) (n := d))))

section
variable {d : ℕ} (L : TimeVelocity d →L[ℝ] TimeVelocity d)
include L

/-- Conjugates a time--velocity endomorphism into the standard finite-function coordinates. -/
def coordinateConjugate :
    (Fin (d + 1) → ℝ) →L[ℝ] (Fin (d + 1) → ℝ) :=
  (timeVelocityCoordinates d).toContinuousLinearMap.comp
    (L.comp (timeVelocityCoordinates d).symm.toContinuousLinearMap)

/-- The standard Pi-basis matrix of a coordinate-conjugated time--velocity endomorphism. -/
def coordinateMatrix :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  LinearMap.toMatrix' (coordinateConjugate L).toLinearMap

/-- Coordinate conjugation preserves the determinant of a time--velocity endomorphism. -/
theorem det_coordinateConjugate :
    (coordinateConjugate L).det = L.det := LinearMap.det_conj L.toLinearMap (timeVelocityCoordinates d).toLinearEquiv

/-- The coordinate matrix has the determinant of its time--velocity endomorphism. -/
theorem det_coordinateMatrix :
    (coordinateMatrix L).det = L.det := by
  calc
    (coordinateMatrix L).det = (coordinateConjugate L).det := by
      simp [coordinateMatrix]
    _ = L.det := det_coordinateConjugate L

end

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open Filter Matrix
open scoped BigOperators Topology

section
variable {d : ℕ} {g : PDE.Vec d → ℝ} {x : PDE.Vec d} (hg : ContDiffAt ℝ 2 g x)
include hg

/-- The derivative of a native coordinate gradient gives the entries of the second derivative. -/
theorem classicalGradient_fderiv_apply (i j : Fin d) :
    fderiv ℝ (PDE.classicalGradient g) x (PDE.basisVec i) j =
      fderiv ℝ (fderiv ℝ g) x (PDE.basisVec i) (PDE.basisVec j) := by
  have hd := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold PDE.classicalGradient
  rw [fderiv_pi (fun j => (hd.clm_apply (differentiableAt_const (PDE.basisVec j))))]
  exact fderiv_eval_const_apply hd _ _

/-- The negative coordinate Hessian at a local maximum is positive semidefinite. -/
theorem neg_classicalGradient_fderiv_posSemidef (hmax : IsLocalMax g x) :
    Matrix.PosSemidef (-(fun i j : Fin d => fderiv ℝ (PDE.classicalGradient g) x (PDE.basisVec i) j)) := by
  simp_rw [classicalGradient_fderiv_apply hg]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · refine Matrix.IsHermitian.neg (Matrix.IsHermitian.ext fun i j => ?_)
    simpa only [star_trivial] using hg.isSymmSndFDerivAt (by norm_num) (PDE.basisVec j) (PDE.basisVec i)
  · intro q
    let H : PDE.Mat d := fun i j => fderiv ℝ (fderiv ℝ g) x (PDE.basisVec i) (PDE.basisVec j)
    change 0 ≤ dotProduct (star q) ((-H).mulVec q)
    rw [star_trivial, Matrix.neg_mulVec, dotProduct_neg]
    change 0 ≤ -dotProduct q (Matrix.mulVec
      (fun i j => fderiv ℝ (fderiv ℝ g) x ((ContinuousLinearMap.id ℝ _) (PDE.basisVec i))
        ((ContinuousLinearMap.id ℝ _) (PDE.basisVec j))) q)
    rw [coordinateQuadraticForm_eq]
    exact neg_nonneg.mpr (fderiv_fderiv_apply_nonpos_of_isLocalMax_of_contDiffAt hg hmax)

end

end HypoellipticAleksandrov.Parabolic
