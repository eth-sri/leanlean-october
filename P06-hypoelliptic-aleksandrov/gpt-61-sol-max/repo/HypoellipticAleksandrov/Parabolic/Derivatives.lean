module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Algebra.Module.Determinant
import Batteries.Tactic.Alias



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

private theorem deriv_deriv_nonpos_of_isLocalMax
    {f : ℝ → ℝ} {a c : ℝ}
    (hmax : IsLocalMax f a)
    (hsecond : HasDerivAt (deriv f) c a)
    (hcont : ContinuousAt f a) :
    c ≤ 0 := by
  by_contra hc
  have hcpos : 0 < c := lt_of_not_ge hc
  have hmin  :=
    isLocalMin_of_deriv_deriv_pos
      (by simpa only [hsecond.deriv] using hcpos)
      hmax.deriv_eq_zero hcont


  have : c = 0 := by
    calc
      c = deriv (deriv f) a := hsecond.deriv.symm
      _ = deriv (fun _ => 0) a := (show deriv f =ᶠ[𝓝 a] fun _ => 0 by
          filter_upwards [(show f =ᶠ[𝓝 a] fun _ => f a by
              filter_upwards [hmax, hmin] with y hymax hymin
              exact le_antisymm hymax hymin).deriv] with y hy
          rw [hy]
          exact deriv_const y (f a)).deriv_eq
      _ = 0 := deriv_const _ _
  exact hcpos.ne' this

variable {E : Type*}

private theorem hasDerivAt_affine_line
     [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x q : E) (s : ℝ) :
    HasDerivAt (fun r : ℝ => x + r • q) q s := by
  simpa only [one_smul] using
    ((hasDerivAt_id'  s).smul_const q).const_add x

private theorem deriv_restrict_affine_line
     [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : Differentiable ℝ g) (x q : E) (s : ℝ) :
    deriv (fun r : ℝ => g (x + r • q)) s =
      fderiv ℝ g (x + s • q) q := (hg (x + s • q)).hasFDerivAt.comp_hasDerivAt
    s (hasDerivAt_affine_line x q s) |>.deriv

private theorem hasDerivAt_fderiv_restrict_affine_line
     [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hsecond : HasFDerivAt (fderiv ℝ g) H x) :
    HasDerivAt
      (fun r : ℝ => fderiv ℝ g (x + r • q) q)
      (H q q) 0 := by


  have hgrad : HasDerivAt (fun r : ℝ => fderiv ℝ g (x + r • q)) (H q) 0 := by
    exact (show HasFDerivAt (fderiv ℝ g) H (x + (0 : ℝ) • q) by
        simpa only [zero_smul, add_zero] using hsecond).comp_hasDerivAt 0 (hasDerivAt_affine_line x q 0)
  simpa only [zero_smul, add_zero, map_zero] using
    hgrad.clm_apply (hasDerivAt_const (x := 0) (c := q))

private theorem hasDerivAt_deriv_restrict_affine_line
     [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : ContDiff ℝ 2 g) (x q : E) :
    HasDerivAt (deriv (fun r : ℝ => g (x + r • q)))
      (fderiv ℝ (fderiv ℝ g) x q q) 0 := by



  apply (hasDerivAt_fderiv_restrict_affine_line (((hg.fderiv_right (m := 1) (by norm_num)).differentiable_one) x).hasFDerivAt).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (deriv_restrict_affine_line (hg.differentiable (by norm_num)) x q)

/-- At a local maximum of a globally `C²` scalar function, every diagonal value of its
second Fréchet derivative is nonpositive. -/
theorem fderiv_fderiv_apply_nonpos_of_isLocalMax
     [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    (hg : ContDiff ℝ 2 g) (hmax : IsLocalMax g x) :
    fderiv ℝ (fderiv ℝ g) x q q ≤ 0 := by
  let line : ℝ → E := fun r => x + r • q


  have hlineCont : ContinuousAt line 0 :=
    (hasDerivAt_affine_line x q 0).continuousAt


  have hfcont : ContinuousAt (fun r => g (line r)) 0 := by

    exact (show ContinuousAt g (line 0) by
        simpa only [line, zero_smul, add_zero] using ((hg.differentiable (by norm_num)) x).continuousAt).comp' hlineCont

  exact deriv_deriv_nonpos_of_isLocalMax ((show IsLocalMax g (line 0) by
      simpa only [line, zero_smul, add_zero] using hmax).comp_continuous hlineCont) (hasDerivAt_deriv_restrict_affine_line hg x q) hfcont

variable {d : ℕ}

variable (u : TimeVelocity d → ℝ) (z : TimeVelocity d)

/-- The derivative of `u` in the unit time direction at `z`. -/
def timeDerivative   : ℝ :=
  fderiv ℝ u z (1, 0)

/-- The velocity gradient of `u` at `z`, evaluated in the standard velocity directions. -/
def velocityGradient   : PDE.Vec d :=
  fun i ↦ fderiv ℝ u z (0, Pi.single i 1)

/-- The velocity Hessian of `u` at `z`, with both derivatives in velocity directions. -/
def velocityHessian   : PDE.Mat d :=
  fun i j ↦
    fderiv ℝ (fderiv ℝ u) z (0, Pi.single i 1) (0, Pi.single j 1)

section
variable {u : TimeVelocity d → ℝ} (hu : ContDiff ℝ 2 u)

include hu
/-- A globally `C²` scalar function has a `C¹` velocity gradient. -/
theorem contDiff_velocityGradient   : ContDiff ℝ 1 (velocityGradient u) := by
  rw [contDiff_pi]
  intro i
  change ContDiff ℝ 1 (fun z  ↦ fderiv ℝ u z (0, Pi.single i 1))
  exact (hu.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)

/-- A globally `C²` scalar function has a differentiable velocity gradient. -/
theorem differentiable_velocityGradient   : Differentiable ℝ (velocityGradient u) :=
  (contDiff_velocityGradient hu).differentiable (by norm_num)

/-- The velocity Hessian of a globally `C²` scalar function is symmetric. -/
theorem velocityHessian_isSymm   (z : TimeVelocity d) : (velocityHessian u z).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  simpa [velocityHessian] using
    (hu.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq
      ((0 ), Pi.single j 1) ((0 ), Pi.single i 1)
end


variable (q : PDE.Vec d)

private theorem sum_smul_single_one   :
    (∑ i : Fin d, q i • ((Pi.single i (1 )) : PDE.Vec d)) = q := by
  ext j
  simp [Pi.single_apply]

private theorem sum_velocity_directions   :
    (∑ i : Fin d, q i •
      ((0, (Pi.single i (1 ) )) : TimeVelocity d)) = (0, q) := by
  apply Prod.ext
  · simp only [Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero]
  · simp only [Prod.snd_sum, Prod.smul_snd, sum_smul_single_one]

variable {u : TimeVelocity d → ℝ}

/-- The coordinate velocity Hessian represents the second Fréchet derivative on pure
velocity directions. -/
theorem velocityHessian_quadratic_eq
      (z : TimeVelocity d) (q : PDE.Vec d) :
    dotProduct q ((velocityHessian u z).mulVec q) =
      fderiv ℝ (fderiv ℝ u) z (0, q) (0, q) := by
  let H := fderiv ℝ (fderiv ℝ u) z
  change (∑ i : Fin d, q i * ∑ j : Fin d,
      H (0, Pi.single i 1) (0, Pi.single j 1) * q j) = H (0, q) (0, q)
  calc
    (∑ i : Fin d, q i * ∑ j : Fin d,
        H (0, Pi.single i 1) (0, Pi.single j 1) * q j) =
        ∑ i : Fin d, q i * H (0, Pi.single i 1)
          (∑ j : Fin d, q j •
            ((0, (Pi.single j (1 ) )) : TimeVelocity d)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      congr 1
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = ∑ i : Fin d, q i * H (0, Pi.single i 1) (0, q) := by
      rw [sum_velocity_directions]
    _ = H (∑ i : Fin d, q i •
        ((0, (Pi.single i (1 ) )) : TimeVelocity d)) (0, q) := by
      rw [map_sum, _root_.sum_apply]
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
    _ = H (0, q) (0, q) := by rw [sum_velocity_directions]

private theorem velocityHessian_isHermitian
      {z : TimeVelocity d}
    (hu : ContDiff ℝ 2 u) :
    (velocityHessian u z).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial, velocityHessian]
  exact hu.contDiffAt.isSymmSndFDerivAt (by norm_num)
    (0, Pi.single j 1) (0, Pi.single i 1)

private theorem fderiv_fderiv_spatial_restrict
      (hu : ContDiff ℝ 2 u)
    (z : TimeVelocity d) (q : PDE.Vec d) :
    fderiv ℝ (fderiv ℝ (fun v  => u (z.1, v))) z.2 q q =
      fderiv ℝ (fderiv ℝ u) z (0, q) (0, q) := by
  have huSpatial : ContDiff ℝ 2 (fun v  => u (z.1, v)) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  have hSpatialLine :=
    (hasDerivAt_deriv_restrict_affine_line huSpatial z.2 q).deriv
  have hJointLine :=
    (hasDerivAt_deriv_restrict_affine_line hu z (0, q)).deriv
  have hlines :
      (fun r : ℝ => u (z.1, z.2 + r • q)) =
        fun r : ℝ => u (z + r • ((0, q) : TimeVelocity d)) := by
    funext r
    congr 1
    apply Prod.ext <;> simp
  rw [hlines] at hSpatialLine
  exact hSpatialLine.symm.trans hJointLine

variable (h : ℝ)

private theorem affine_contact_contDiff
      (p z : PDE.Vec d) :
    ContDiff ℝ 2 (fun v  => h + PDE.vecDot p (v - z)) := by
  unfold PDE.vecDot
  fun_prop

private theorem affine_contact_second_fderiv_zero
      (p z q : PDE.Vec d) :
    fderiv ℝ (fderiv ℝ (fun v  => h + PDE.vecDot p (v - z))) z q q = 0 := by
  let affine  := fun v => h + PDE.vecDot p (v - z)

  have hsecond := (hasDerivAt_deriv_restrict_affine_line (affine_contact_contDiff h p z) z q).deriv
  have hlineEq : (fun r : ℝ => affine (z + r • q)) =
      fun r => h + r * PDE.vecDot p q := by
    funext r
    simp only [affine, PDE.vecDot, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, add_sub_cancel_left, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hderivEq : deriv (fun r  => h + r * PDE.vecDot p q) =
      fun _ => PDE.vecDot p q := by
    funext r
    exact (by
      simpa only [one_mul] using
        ((hasDerivAt_id'  r).mul_const (PDE.vecDot p q)).const_add h :
          HasDerivAt (fun s  => h + s * PDE.vecDot p q) (PDE.vecDot p q) r).deriv
  rw [hlineEq, hderivEq] at hsecond
  exact hsecond.symm.trans (deriv_const 0 _)

private theorem fderiv_fderiv_fun_sub_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x q : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y - g y)) x q q =
      fderiv ℝ (fderiv ℝ f) x q q - fderiv ℝ (fderiv ℝ g) x q q := by


  have hgradEq : fderiv ℝ (fun y => f y - g y) =
      fun y => fderiv ℝ f y - fderiv ℝ g y := by
    funext y
    exact fderiv_fun_sub ((hf.differentiable (by norm_num)) y) ((hg.differentiable (by norm_num)) y)
  rw [hgradEq]


  rw [fderiv_fun_sub (((hf.fderiv_right (m := 1) (by norm_num)).differentiable_one) x) (((hg.fderiv_right (m := 1) (by norm_num)).differentiable_one) x)]
  rfl

/-- At a spatial local maximum against an affine velocity contact function, the negative
velocity Hessian is positive semidefinite. -/
theorem neg_velocityHessian_posSemidef_of_spatial_localMax_affineContact
    {d : ℕ} {u : TimeVelocity d → ℝ} {z : TimeVelocity d}
    {h : ℝ} {p : PDE.Vec d}
    (hu : ContDiff ℝ 2 u)
    (hcontact : IsLocalMax
      (fun v  => u (z.1, v) -
        (h + PDE.vecDot p (v - z.2))) z.2) :
    (-velocityHessian u z).PosSemidef := by
  let sharedTerm_1c9b33078c := ((fun v : PDE.Vec d => u (z.1, v)))
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (velocityHessian_isHermitian hu).neg
  · intro q
    let g  := fun v =>
      u (z.1, v) - (h + PDE.vecDot p (v - z.2))
    have huSpatial : ContDiff ℝ 2 sharedTerm_1c9b33078c := by
      exact hu.comp (contDiff_const.prodMk contDiff_id)

    have hgNonpos : fderiv ℝ (fderiv ℝ g) z.2 q q ≤ 0 :=
      fderiv_fderiv_apply_nonpos_of_isLocalMax (huSpatial.sub (affine_contact_contDiff h p z.2)) hcontact


    have hsub : fderiv ℝ (fderiv ℝ g) z.2 q q =
        fderiv ℝ (fderiv ℝ sharedTerm_1c9b33078c) z.2 q q -
          fderiv ℝ (fderiv ℝ
            (fun v  => h + PDE.vecDot p (v - z.2))) z.2 q q := by
      exact fderiv_fderiv_fun_sub_apply huSpatial
        (affine_contact_contDiff h p z.2) z.2 q

    simpa only [star_trivial, Matrix.neg_mulVec, dotProduct_neg,
      velocityHessian_quadratic_eq] using neg_nonneg.mpr (by
          rw [hsub, (affine_contact_second_fderiv_zero h p z.2 q), sub_zero, (fderiv_fderiv_spatial_restrict hu z q)] at hgNonpos
          exact hgNonpos)

/-- A continuous linear equivalence from time--velocity points to `Fin (d + 1)` coordinates. -/
def timeVelocityCoordinates (d : ℕ) :
    TimeVelocity d ≃L[ℝ] (Fin (d + 1) → ℝ) :=
  (((ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ (PDE.Vec d))).symm.trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 1) (Fin d)
      (fun _ ↦ ℝ)).symm).trans
    ((ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (1 + d) ↦ ℝ)
        finSumFinEquiv).trans
      (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (d + 1) ↦ ℝ)
        (finAddFlip (m := 1) (n := d))))

variable {d : ℕ} (L : TimeVelocity d →L[ℝ] TimeVelocity d)

/-- Conjugates a time--velocity endomorphism into the standard finite-function coordinates. -/
def coordinateConjugate  :
    (Fin (d + 1) → ℝ) →L[ℝ] (Fin (d + 1) → ℝ) :=
  (timeVelocityCoordinates d).toContinuousLinearMap.comp
    (L.comp (timeVelocityCoordinates d).symm.toContinuousLinearMap)

/-- The standard Pi-basis matrix of a coordinate-conjugated time--velocity endomorphism. -/
def coordinateMatrix   :=
  LinearMap.toMatrix' (coordinateConjugate L).toLinearMap

/-- Coordinate conjugation preserves the determinant of a time--velocity endomorphism. -/
theorem det_coordinateConjugate  :
    (coordinateConjugate L).det = L.det := LinearMap.det_conj L.toLinearMap _

/-- The coordinate matrix has the determinant of its time--velocity endomorphism. -/
theorem det_coordinateMatrix  :
    (coordinateMatrix L).det = L.det := by
  simp_all [coordinateMatrix, coordinateConjugate, det_coordinateConjugate]

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open Filter Matrix
open scoped BigOperators Topology

private alias deriv_deriv_nonpos_of_isLocalMax_local := _root_.HypoellipticAleksandrov.Parabolic.deriv_deriv_nonpos_of_isLocalMax


variable {E : Type*}




private theorem hasDerivAt_deriv_restrict_affine_line_local
     [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E} (hg : ContDiffAt ℝ 2 g x) :
    HasDerivAt (deriv (fun r : ℝ => g (x + r • q)))
      (fderiv ℝ (fderiv ℝ g) x q q) 0 := by

  have hGrad : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hEvalLine : HasDerivAt
      (fun r : ℝ => fderiv ℝ g (x + r • q) q)
      (fderiv ℝ (fderiv ℝ g) x q q) 0 := by
    exact _root_.HypoellipticAleksandrov.Parabolic.hasDerivAt_fderiv_restrict_affine_line hGrad
  apply hEvalLine.congr_of_eventuallyEq
  have hTendsto' : Filter.Tendsto (fun r : ℝ => x + r • q) (𝓝 0)
      (𝓝 (x + (0 : ℝ) • q)) := (show HasDerivAt (fun r : ℝ => x + r • q) q 0 by
          simpa only [one_smul] using
            ((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const q).const_add x).continuousAt

  have hEvent : ∀ᶠ r : ℝ in 𝓝 0, ContDiffAt ℝ 2 g (x + r • q) :=
    (show Filter.Tendsto (fun r : ℝ => x + r • q) (𝓝 0) (𝓝 x) by
        simpa only [zero_smul, add_zero] using hTendsto').eventually (hg.eventually (by norm_num))
  filter_upwards [hEvent] with r hgr
  exact ((hgr.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt r
    (by simpa only [one_smul] using
      ((hasDerivAt_id'  r).smul_const q).const_add x)).deriv

private theorem fderiv_fderiv_apply_nonpos_of_isLocalMax_local
     [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    (hg : ContDiffAt ℝ 2 g x) (hmax : IsLocalMax g x) :
    fderiv ℝ (fderiv ℝ g) x q q ≤ 0 := by
  let line : ℝ → E := fun r => x + r • q


  have hlineCont : ContinuousAt line 0 := (show HasDerivAt line q 0 by
      simpa only [line, one_smul] using
        ((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const q).const_add x).continuousAt




  exact _root_.HypoellipticAleksandrov.Parabolic.deriv_deriv_nonpos_of_isLocalMax ((show IsLocalMax g (line 0) by
      simpa only [line, zero_smul, add_zero] using hmax).comp_continuous hlineCont) (hasDerivAt_deriv_restrict_affine_line_local hg) (by

          exact (show ContinuousAt g (line 0) by
              simpa only [line, zero_smul, add_zero] using hg.continuousAt).comp' hlineCont)

private theorem fderiv_fderiv_spatial_restrict_local
    {d : ℕ} {u : TimeVelocity d → ℝ} {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z) (q : PDE.Vec d) :
    fderiv ℝ (fderiv ℝ (fun v  => u (z.1, v))) z.2 q q =
      fderiv ℝ (fderiv ℝ u) z (0, q) (0, q) := by

  have hSpatialLine :=
    (hasDerivAt_deriv_restrict_affine_line_local (q := q) (by
        simpa only [Function.comp_def, id_eq] using
          hu.comp z.2 (contDiffAt_const.prodMk contDiffAt_id))).deriv

  have hlines :
      (fun r : ℝ => u (z.1, z.2 + r • q)) =
        fun r : ℝ => u (z + r • ((0, q) : TimeVelocity d)) := by
    funext r
    congr 1
    apply Prod.ext <;> simp
  rw [hlines] at hSpatialLine
  exact hSpatialLine.symm.trans ((hasDerivAt_deriv_restrict_affine_line_local hu (q := (0, q))).deriv)

private theorem fderiv_fderiv_fun_sub_apply_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x q : E} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => f y - g y)) x q q =
      fderiv ℝ (fderiv ℝ f) x q q - fderiv ℝ (fderiv ℝ g) x q q := by









  have hderiv  :=
    (((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.sub ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt).congr_of_eventuallyEq (by
        filter_upwards [((hf.eventually (by norm_num)).mono fun _ hy => hy.differentiableAt (by norm_num)), ((hg.eventually (by norm_num)).mono fun _ hy => hy.differentiableAt (by norm_num))] with y hfy hgy
        exact fderiv_fun_sub hfy hgy)
  rw [hderiv.fderiv]
  rfl

variable {d : ℕ}

variable (h : ℝ)

private theorem affine_contact_contDiffAt_local
      (p z : PDE.Vec d) :
    ContDiffAt ℝ 2 (fun v  => h + PDE.vecDot p (v - z)) z := by
  unfold PDE.vecDot
  fun_prop




variable {u : TimeVelocity d → ℝ} {z : TimeVelocity d}

private theorem velocityHessian_isHermitian_local

    (hu : ContDiffAt ℝ 2 u z) :
    (velocityHessian u z).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial, velocityHessian]
  exact hu.isSymmSndFDerivAt (by norm_num)
    (0, Pi.single j 1) (0, Pi.single i 1)

/-- At a spatial local maximum against an affine velocity contact function, the negative
velocity Hessian is positive semidefinite under a local `C²` hypothesis at the contact point. -/
theorem neg_velocityHessian_posSemidef_of_spatial_localMax_affineContact_of_contDiffAt

    {h : ℝ} {p : PDE.Vec d}
    (hu : ContDiffAt ℝ 2 u z)
    (hcontact : IsLocalMax
      (fun v  => u (z.1, v) -
        (h + PDE.vecDot p (v - z.2))) z.2) :
    (-velocityHessian u z).PosSemidef := (PosSemidef.of_dotProduct_mulVec_nonneg (IsHermitian.neg (velocityHessian_isHermitian_local hu)) fun q =>
  Eq.mpr
    (id
      (congrArg (LE.le 0)
        (Eq.trans
          (Eq.trans (congr (congrArg dotProduct (star_trivial q)) (neg_mulVec q (velocityHessian u z)))
            (dotProduct_neg q (velocityHessian u z *ᵥ q)))
          (congrArg Neg.neg (velocityHessian_quadratic_eq z q)))))
    (neg_nonneg.mpr
      (Eq.mp (congrArg (fun _a => _a ≤ 0) (fderiv_fderiv_spatial_restrict_local hu q))
        (Eq.mp (congrArg (fun _a => _a ≤ 0) (sub_zero (((fderiv ℝ (fderiv ℝ fun v => u (z.1, v)) z.2) q) q)))
          (Eq.mp
            (congrArg (fun _a => ((fderiv ℝ (fderiv ℝ fun v => u (z.1, v)) z.2) q) q - _a ≤ 0)
              (affine_contact_second_fderiv_zero h p z.2 q))
            (Eq.mp
              (congrArg (fun _a => _a ≤ 0)
                (fderiv_fderiv_fun_sub_apply_local
                  (ContDiffAt.comp z.2 hu (ContDiffAt.prodMk contDiffAt_const contDiffAt_id))
                  (affine_contact_contDiffAt_local h p z.2)))
              (fderiv_fderiv_apply_nonpos_of_isLocalMax_local
                (ContDiffAt.sub (ContDiffAt.comp z.2 hu (ContDiffAt.prodMk contDiffAt_const contDiffAt_id))
                  (affine_contact_contDiffAt_local h p z.2))
                hcontact)))))))

end HypoellipticAleksandrov.Parabolic
