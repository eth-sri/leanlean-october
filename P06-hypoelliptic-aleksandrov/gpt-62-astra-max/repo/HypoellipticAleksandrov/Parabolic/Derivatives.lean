module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.DerivativeTest
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

private theorem deriv_deriv_nonpos_of_isLocalMax
    {f : ℝ → ℝ} {a c : ℝ}
    (hmax : IsLocalMax f a)
    (hsecond : HasDerivAt (deriv f) c a)
    (hcont : ContinuousAt f a) :
    c ≤ 0 := by
  by_contra hc
  have hcpos := lt_of_not_ge hc
  have hmin :=
    isLocalMin_of_deriv_deriv_pos
      (by simpa [hsecond.deriv] using hcpos)
      hmax.deriv_eq_zero hcont
  have heq : f =ᶠ[𝓝 a] fun _ => f a := by
    filter_upwards [hmax, hmin] with y hymax hymin
    exact le_antisymm hymax hymin
  have hderivEq : deriv f =ᶠ[𝓝 a] fun _ => 0 := by
    filter_upwards [heq.deriv] with y hy
    rw [hy]
    apply deriv_const
  have : c = 0 := by
    calc
      c = deriv (deriv f) a := hsecond.deriv.symm
      _ = deriv (fun _ => 0) a := hderivEq.deriv_eq
      _ = 0 := deriv_const _ _
  exact hcpos.ne' this

section
variable {d : ℕ} {E : Type*} {u : TimeVelocity d → ℝ} (h : ℝ) (hu : ContDiff ℝ 2 u)
    (z : TimeVelocity d) (q : PDE.Vec d)

private theorem hasDerivAt_affine_line [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x q : E) (s : ℝ) :
    HasDerivAt (fun r : ℝ => x + r • q) q s := by
  simpa using
    ((hasDerivAt_id' (𝕜 := ℝ) s).smul_const q).const_add x

private theorem deriv_restrict_affine_line [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : Differentiable ℝ g) (x q : E) (s : ℝ) :
    deriv (fun r : ℝ => g (x + r • q)) s =
      fderiv ℝ g (x + s • q) q := (hg (x + s • q)).hasFDerivAt.comp_hasDerivAt
    s (hasDerivAt_affine_line x q s) |>.deriv

private theorem hasDerivAt_fderiv_restrict_affine_line [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hsecond : HasFDerivAt (fderiv ℝ g) H x) :
    HasDerivAt
      (fun r : ℝ => fderiv ℝ g (x + r • q) q)
      (H q q) 0 := by
  have hsecond' : HasFDerivAt (fderiv ℝ g) H (x + (0 : ℝ) • q) := by
    simpa using hsecond
  have hgrad : HasDerivAt (fun r : ℝ => fderiv ℝ g (x + r • q)) (H q) 0 := by
    exact hsecond'.comp_hasDerivAt 0 (hasDerivAt_affine_line x q 0)
  simpa using
    hgrad.clm_apply (hasDerivAt_const (x := 0) (c := q))

private theorem hasDerivAt_deriv_restrict_affine_line [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : ContDiff ℝ 2 g) (x q : E) :
    HasDerivAt (deriv (fun r : ℝ => g (x + r • q)))
      (fderiv ℝ (fderiv ℝ g) x q q) 0 := by
  have hgDerivDiff : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable_one
  apply (hasDerivAt_fderiv_restrict_affine_line (hgDerivDiff x).hasFDerivAt).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun r =>
    deriv_restrict_affine_line (hg.differentiable (by norm_num)) x q r

/-- At a local maximum of a globally `C²` scalar function, every diagonal value of its
second Fréchet derivative is nonpositive. -/
theorem fderiv_fderiv_apply_nonpos_of_isLocalMax [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    (hg : ContDiff ℝ 2 g) (hmax : IsLocalMax g x) :
    fderiv ℝ (fderiv ℝ g) x q q ≤ 0 := by
  let line : ℝ → E := fun r => x + r • q
  let f := fun r => g (line r)
  have hlineCont : ContinuousAt line 0 :=
    (hasDerivAt_affine_line x q 0).continuousAt
  have hmax' : IsLocalMax g (line 0) := by
    simpa [line] using hmax
  have hfmax : IsLocalMax f 0 := hmax'.comp_continuous hlineCont
  have hfcont : ContinuousAt f 0 := by
    have hgcont : ContinuousAt g (line 0) := by
      simpa only [line, zero_smul, add_zero] using ((hg.differentiable (by norm_num)) x).continuousAt
    exact hgcont.comp' hlineCont
  apply_rules [deriv_deriv_nonpos_of_isLocalMax, hasDerivAt_deriv_restrict_affine_line]

/-- The derivative of `u` in the unit time direction at `z`. -/
def timeDerivative (u : TimeVelocity d → ℝ) (z : TimeVelocity d) : ℝ :=
  fderiv ℝ u z (1, 0)

/-- The velocity gradient of `u` at `z`, evaluated in the standard velocity directions. -/
def velocityGradient (u : TimeVelocity d → ℝ) (z : TimeVelocity d) : PDE.Vec d :=
  fun i ↦ fderiv ℝ u z (0, Pi.single i 1)

/-- The velocity Hessian of `u` at `z`, with both derivatives in velocity directions. -/
def velocityHessian (u : TimeVelocity d → ℝ) (z : TimeVelocity d) : PDE.Mat d :=
  fun i j ↦
    fderiv ℝ (fderiv ℝ u) z (0, Pi.single i 1) (0, Pi.single j 1)

include hu in
/-- A globally `C²` scalar function has a `C¹` velocity gradient. -/
theorem contDiff_velocityGradient : ContDiff ℝ 1 (velocityGradient u) := by
  rw [contDiff_pi]
  intro i
  change ContDiff ℝ 1 (fun z : TimeVelocity d ↦ fderiv ℝ u z (0, Pi.single i 1))
  fun_prop

include hu in
/-- A globally `C²` scalar function has a differentiable velocity gradient. -/
theorem differentiable_velocityGradient : Differentiable ℝ (velocityGradient u) :=
  (contDiff_velocityGradient hu).differentiable (by norm_num)

include hu in
/-- The velocity Hessian of a globally `C²` scalar function is symmetric. -/
theorem velocityHessian_isSymm : (velocityHessian u z).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  exact (hu.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq
      ((0 : ℝ), Pi.single j 1) ((0 : ℝ), Pi.single i 1)

private theorem sum_smul_single_one :
    (∑ i : Fin d, q i • ((Pi.single i (1 : ℝ)) : PDE.Vec d)) = q := by
  ext j
  simp [Pi.single_apply]

private theorem sum_velocity_directions :
    (∑ i : Fin d, q i •
      ((0, (Pi.single i (1 : ℝ) : PDE.Vec d)) : TimeVelocity d)) = (0, q) := by
  apply Prod.ext
  · simp only [Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero]
  · simp only [Prod.snd_sum, Prod.smul_snd, sum_smul_single_one]

/-- The coordinate velocity Hessian represents the second Fréchet derivative on pure
velocity directions. -/
theorem velocityHessian_quadratic_eq :
    dotProduct q ((velocityHessian u z).mulVec q) =
      fderiv ℝ (fderiv ℝ u) z (0, q) (0, q) := by
  let H := fderiv ℝ (fderiv ℝ u) z
  calc
    (∑ i : Fin d, q i * ∑ j : Fin d,
        H (0, Pi.single i 1) (0, Pi.single j 1) * q j) =
        ∑ i : Fin d, q i * H (0, Pi.single i 1)
          (∑ j : Fin d, q j •
            ((0, (Pi.single j (1 : ℝ) : PDE.Vec d)))) := by
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
        ((0, (Pi.single i (1 : ℝ) : PDE.Vec d)))) (0, q) := by
      rw [map_sum, _root_.sum_apply]
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
    _ = H (0, q) (0, q) := by rw [sum_velocity_directions]

private theorem velocityHessian_isHermitian {z : TimeVelocity d}
    (hu : ContDiff ℝ 2 u) :
    (velocityHessian u z).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  exact hu.contDiffAt.isSymmSndFDerivAt (by norm_num)
    (0, Pi.single j 1) (0, Pi.single i 1)

include hu in
private theorem fderiv_fderiv_spatial_restrict :
    fderiv ℝ (fderiv ℝ (fun v : PDE.Vec d => u (z.1, v))) z.2 q q =
      fderiv ℝ (fderiv ℝ u) z (0, q) (0, q) := by
  have huSpatial : ContDiff ℝ 2 (fun v : PDE.Vec d => u (z.1, v)) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  have hSpatialLine :=
    (hasDerivAt_deriv_restrict_affine_line huSpatial z.2 q).deriv
  have hlines :
      (fun r : ℝ => u (z.1, z.2 + r • q)) =
        fun r : ℝ => u (z + r • ((0, q))) := by
    funext r
    congr 1
    apply Prod.ext <;> simp
  rw [hlines] at hSpatialLine
  exact hSpatialLine.symm.trans ((hasDerivAt_deriv_restrict_affine_line hu z (0, q)).deriv)

private theorem affine_contact_contDiff (p z : PDE.Vec d) :
    ContDiff ℝ 2 (fun v : PDE.Vec d => h + PDE.vecDot p (v - z)) := by
  unfold PDE.vecDot
  fun_prop

private theorem affine_contact_second_fderiv_zero (p z q : PDE.Vec d) :
    fderiv ℝ (fderiv ℝ (fun v : PDE.Vec d => h + PDE.vecDot p (v - z))) z q q = 0 := by
  let affine := fun v => h + PDE.vecDot p (v - z)
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
  have hderivEq : deriv (fun r : ℝ => h + r * PDE.vecDot p q) =
      fun _ => PDE.vecDot p q := by
    simp
  rw [hlineEq, hderivEq] at hsecond
  exact hsecond.symm.trans (deriv_const 0 (PDE.vecDot p q))

private theorem fderiv_fderiv_fun_sub_apply [NormedAddCommGroup E] [NormedSpace ℝ E]
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
theorem neg_velocityHessian_posSemidef_of_spatial_localMax_affineContact {z : TimeVelocity d}
    {h : ℝ} {p : PDE.Vec d}
    (hu : ContDiff ℝ 2 u)
    (hcontact : IsLocalMax
      (fun v : PDE.Vec d => u (z.1, v) -
        (h + PDE.vecDot p (v - z.2))) z.2) :
    (-velocityHessian u z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (velocityHessian_isHermitian hu).neg
  · intro q
    let g := fun v =>
      u (z.1, v) - (h + PDE.vecDot p (v - z.2))
    have huSpatial : ContDiff ℝ 2 (fun v : PDE.Vec d => u (z.1, v)) := by
      fun_prop
    have hgNonpos : fderiv ℝ (fderiv ℝ g) z.2 q q ≤ 0 :=
      fderiv_fderiv_apply_nonpos_of_isLocalMax (huSpatial.sub (affine_contact_contDiff h p z.2)) hcontact
    have hHnonpos : fderiv ℝ (fderiv ℝ u) z (0, q) (0, q) ≤ 0 := by
      rw [(fderiv_fderiv_fun_sub_apply huSpatial (affine_contact_contDiff h p z.2) z.2 q), (affine_contact_second_fderiv_zero h p z.2 q), sub_zero, (fderiv_fderiv_spatial_restrict hu z q)] at hgNonpos
      exact hgNonpos
    simpa only [star_trivial, Matrix.neg_mulVec, dotProduct_neg,
      velocityHessian_quadratic_eq] using neg_nonneg.mpr hHnonpos

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

/-- Conjugates a time--velocity endomorphism into the standard finite-function coordinates. -/
def coordinateConjugate :
    (Fin (d + 1) → ℝ) →L[ℝ] (Fin (d + 1) → ℝ) :=
  (timeVelocityCoordinates d).toContinuousLinearMap.comp
    (L.comp (timeVelocityCoordinates d).symm.toContinuousLinearMap)

include L in
/-- The standard Pi-basis matrix of a coordinate-conjugated time--velocity endomorphism. -/
def coordinateMatrix :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  LinearMap.toMatrix' (coordinateConjugate L).toLinearMap

/-- Coordinate conjugation preserves the determinant of a time--velocity endomorphism. -/
theorem det_coordinateConjugate :
    (coordinateConjugate L).det = L.det := by
  apply LinearMap.det_conj

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

private theorem deriv_deriv_nonpos_of_isLocalMax_local
    {f : ℝ → ℝ} {a c : ℝ}
    (hmax : IsLocalMax f a)
    (hsecond : HasDerivAt (deriv f) c a)
    (hcont : ContinuousAt f a) :
    c ≤ 0 := by
  by_contra hc
  have hcpos := lt_of_not_ge hc
  have hmin :=
    isLocalMin_of_deriv_deriv_pos
      (by simpa [hsecond.deriv] using hcpos)
      hmax.deriv_eq_zero hcont
  have heq : f =ᶠ[𝓝 a] fun _ => f a := by
    filter_upwards [hmax, hmin] with y hymax hymin
    exact le_antisymm hymax hymin
  have hderivEq : deriv f =ᶠ[𝓝 a] fun _ => 0 := by
    filter_upwards [heq.deriv] with y hy
    rw [hy]
    apply deriv_const
  have : c = 0 := by
    calc
      c = deriv (deriv f) a := hsecond.deriv.symm
      _ = deriv (fun _ => 0) a := hderivEq.deriv_eq
      _ = 0 := deriv_const _ _
  exact hcpos.ne' this

variable {d : ℕ} {E : Type*} {u : TimeVelocity d → ℝ} {z : TimeVelocity d} {h : ℝ} {p : PDE.Vec d}
    (hu : ContDiffAt ℝ 2 u z)

private theorem hasDerivAt_fderiv_restrict_affine_line_at [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hsecond : HasFDerivAt (fderiv ℝ g) H x) :
    HasDerivAt
      (fun r : ℝ => fderiv ℝ g (x + r • q) q)
      (H q q) 0 := by
  have hline : HasDerivAt (fun r : ℝ => x + r • q) q 0 := by
    simpa using
      ((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const q).const_add x
  have hsecond' : HasFDerivAt (fderiv ℝ g) H (x + (0 : ℝ) • q) := by
    simpa using hsecond
  have hgrad : HasDerivAt (fun r : ℝ => fderiv ℝ g (x + r • q)) (H q) 0 :=
    hsecond'.comp_hasDerivAt 0 hline
  simpa using
    hgrad.clm_apply (hasDerivAt_const (x := 0) (c := q))

private theorem hasDerivAt_deriv_restrict_affine_line_local [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E} (hg : ContDiffAt ℝ 2 g x) :
    HasDerivAt (deriv (fun r : ℝ => g (x + r • q)))
      (fderiv ℝ (fderiv ℝ g) x q q) 0 := by
  have hline : HasDerivAt (fun r : ℝ => x + r • q) q 0 := by
    simpa using
      ((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const q).const_add x
  have hGrad : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
  apply (hasDerivAt_fderiv_restrict_affine_line_at hGrad).congr_of_eventuallyEq
  have hTendsto' : Filter.Tendsto (fun r : ℝ => x + r • q) (𝓝 0)
      (𝓝 (x + (0 : ℝ) • q)) := hline.continuousAt
  have hTendsto : Filter.Tendsto (fun r : ℝ => x + r • q) (𝓝 0) (𝓝 x) := by
    simpa using hTendsto'
  filter_upwards [(hTendsto.eventually (hg.eventually (by norm_num)))] with r hgr
  exact ((hgr.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt r
    (by simpa using
      ((hasDerivAt_id' (𝕜 := ℝ) r).smul_const q).const_add x)).deriv

private theorem fderiv_fderiv_apply_nonpos_of_isLocalMax_local [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    (hg : ContDiffAt ℝ 2 g x) (hmax : IsLocalMax g x) :
    fderiv ℝ (fderiv ℝ g) x q q ≤ 0 := by
  let line : ℝ → E := fun r => x + r • q
  let f := fun r => g (line r)
  have hlineDeriv : HasDerivAt line q 0 := by
    simpa [line] using
      ((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const q).const_add x
  have hlineCont : ContinuousAt line 0 := hlineDeriv.continuousAt
  have hmax' : IsLocalMax g (line 0) := by
    simpa [line] using hmax
  have hfcont : ContinuousAt f 0 := by
    have hgcont : ContinuousAt g (line 0) := by
      simpa [line] using hg.continuousAt
    exact hgcont.comp' hlineCont
  have hfsecond : HasDerivAt (deriv f)
      (fderiv ℝ (fderiv ℝ g) x q q) 0 := by
    exact hasDerivAt_deriv_restrict_affine_line_local hg
  exact deriv_deriv_nonpos_of_isLocalMax_local (hmax'.comp_continuous hlineCont) hfsecond hfcont

include hu in
private theorem fderiv_fderiv_spatial_restrict_local (q : PDE.Vec d) :
    fderiv ℝ (fderiv ℝ (fun v : PDE.Vec d => u (z.1, v))) z.2 q q =
      fderiv ℝ (fderiv ℝ u) z (0, q) (0, q) := by
  have huSpatial : ContDiffAt ℝ 2 (fun v : PDE.Vec d => u (z.1, v)) z.2 := by
    fun_prop
  have hSpatialLine :=
    (hasDerivAt_deriv_restrict_affine_line_local (q := q) huSpatial).deriv
  have hlines :
      (fun r : ℝ => u (z.1, z.2 + r • q)) =
        fun r : ℝ => u (z + r • ((0, q))) := by
    funext r
    congr 1
    apply Prod.ext <;> simp
  rw [hlines] at hSpatialLine
  exact hSpatialLine.symm.trans ((hasDerivAt_deriv_restrict_affine_line_local hu (q := (0, q))).deriv)

private theorem fderiv_fderiv_fun_sub_apply_local [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x q : E} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => f y - g y)) x q q =
      fderiv ℝ (fderiv ℝ f) x q q - fderiv ℝ (fderiv ℝ g) x q q := by
  have hgradEq : (fun y => fderiv ℝ (fun z => f z - g z) y) =ᶠ[𝓝 x]
      fun y => fderiv ℝ f y - fderiv ℝ g y := by
    filter_upwards [((hf.eventually (by norm_num)).mono fun _ hy => hy.differentiableAt (by norm_num)), ((hg.eventually (by norm_num)).mono fun _ hy => hy.differentiableAt (by norm_num))] with y hfy hgy
    exact fderiv_fun_sub hfy hgy
  have hsub : HasFDerivAt (fun y => fderiv ℝ f y - fderiv ℝ g y)
      (fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.sub ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  rw [(hsub.congr_of_eventuallyEq hgradEq).fderiv]
  rfl

private theorem affine_contact_contDiffAt_local (h : ℝ) (p z : PDE.Vec d) :
    ContDiffAt ℝ 2 (fun v : PDE.Vec d => h + PDE.vecDot p (v - z)) z := by
  unfold PDE.vecDot
  fun_prop

private theorem affine_contact_second_fderiv_zero_local (h : ℝ) (p z q : PDE.Vec d) :
    fderiv ℝ (fderiv ℝ (fun v : PDE.Vec d => h + PDE.vecDot p (v - z))) z q q = 0 := by
  let affine := fun v => h + PDE.vecDot p (v - z)
  have hsecond :=
    (hasDerivAt_deriv_restrict_affine_line_local (q := q) (affine_contact_contDiffAt_local h p z)).deriv
  have hlineEq : (fun r : ℝ => affine (z + r • q)) =
      fun r => h + r * PDE.vecDot p q := by
    funext r
    simp only [affine, PDE.vecDot, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, add_sub_cancel_left, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hderivEq : deriv (fun r : ℝ => h + r * PDE.vecDot p q) =
      fun _ => PDE.vecDot p q := by
    simp
  rw [hlineEq, hderivEq] at hsecond
  exact hsecond.symm.trans (deriv_const 0 (PDE.vecDot p q))

include hu in
private theorem velocityHessian_isHermitian_local :
    (velocityHessian u z).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  exact hu.isSymmSndFDerivAt (by norm_num)
    (0, Pi.single j 1) (0, Pi.single i 1)

include hu in
/-- At a spatial local maximum against an affine velocity contact function, the negative
velocity Hessian is positive semidefinite under a local `C²` hypothesis at the contact point. -/
theorem neg_velocityHessian_posSemidef_of_spatial_localMax_affineContact_of_contDiffAt
    (hcontact : IsLocalMax
      (fun v : PDE.Vec d => u (z.1, v) -
        (h + PDE.vecDot p (v - z.2))) z.2) :
    (-velocityHessian u z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (velocityHessian_isHermitian_local hu).neg
  · intro q
    let g := fun v =>
      u (z.1, v) - (h + PDE.vecDot p (v - z.2))
    have huSpatial : ContDiffAt ℝ 2 (fun v : PDE.Vec d => u (z.1, v)) z.2 := by
      fun_prop
    have hgNonpos : fderiv ℝ (fderiv ℝ g) z.2 q q ≤ 0 :=
      fderiv_fderiv_apply_nonpos_of_isLocalMax_local (huSpatial.sub (affine_contact_contDiffAt_local h p z.2)) hcontact
    have hHnonpos : fderiv ℝ (fderiv ℝ u) z (0, q) (0, q) ≤ 0 := by
      rw [(fderiv_fderiv_fun_sub_apply_local huSpatial (affine_contact_contDiffAt_local h p z.2)), (affine_contact_second_fderiv_zero_local h p z.2 q), sub_zero, (fderiv_fderiv_spatial_restrict_local hu q)] at hgNonpos
      exact hgNonpos
    simpa only [star_trivial, Matrix.neg_mulVec, dotProduct_neg,
      velocityHessian_quadratic_eq] using neg_nonneg.mpr hHnonpos

end HypoellipticAleksandrov.Parabolic
