module

public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import HypoellipticAleksandrov.Parabolic.HarnackGeometry
public import HypoellipticAleksandrov.Parabolic.LocalClassical
import Aesop
import Mathlib.Tactic.Bound
public import PDEFoundation.Calculus.RegularityOrder




/-!
# Parabolic affine scaling

This file records the exact translation and parabolic-dilation identities for
the forward time--velocity operator.  The affine map itself is defined in
`HarnackGeometry`; this module supplies its differential and the induced local
classical pullback API.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Set
open scoped MatrixOrder Topology

variable {d : ℕ}

variable (r : ℝ)

/-- The derivative of parabolic affine scaling. -/
def parabolicLinear   :
    TimeVelocity d →L[ℝ] TimeVelocity d :=
  ((r ^ 2) • ContinuousLinearMap.fst ℝ ℝ (PDE.Vec d)).prod
    (r • ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))

/-- Evaluation of the linear part of parabolic affine scaling. -/
@[simp] theorem parabolicLinear_apply   (z : TimeVelocity d) :
    parabolicLinear r z = (r ^ 2 * z.1, r • z.2) :=
  rfl

variable (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ)

/-- The affine parabolic map has its constant linear part as Fréchet derivative. -/
theorem hasFDerivAt_parabolicAffine
    (z : TimeVelocity d) :
    HasFDerivAt (parabolicAffine t₀ v₀ r) (parabolicLinear r) z := by
  change HasFDerivAt (fun z : TimeVelocity d ↦
    (t₀ + r ^ 2 * z.1, v₀ + r • z.2)) (parabolicLinear r) z
  convert ((hasFDerivAt_const t₀ z).add
    ((hasFDerivAt_const (r ^ 2) z).mul hasFDerivAt_fst)).prodMk
      ((hasFDerivAt_const v₀ z).add
        ((hasFDerivAt_const r z).smul
          (hasFDerivAt_snd (𝕜 := ℝ) (p := z)))) using 1
  ext <;> simp [parabolicLinear]

/-- Parabolic affine scaling is globally smooth. -/
theorem contDiff_parabolicAffine   :
    ContDiff ℝ 2 (parabolicAffine t₀ v₀ r) := by
  change ContDiff ℝ 2 (fun z : TimeVelocity d ↦
    (t₀ + r ^ 2 * z.1, v₀ + r • z.2))
  fun_prop

/-- Parabolic affine scaling is smooth at every order. -/
theorem contDiff_infty_parabolicAffine   : ContDiff ℝ (⊤ ) (parabolicAffine t₀ v₀ r) := by
  change ContDiff ℝ (⊤ ) (fun z : TimeVelocity d ↦
    (t₀ + r ^ 2 * z.1, v₀ + r • z.2))
  fun_prop

/-- Pulls a scalar function back by parabolic affine scaling. -/
def pullbackScalar  (q : TimeVelocity d → ℝ)
    (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ) : TimeVelocity d → ℝ :=
  q ∘ parabolicAffine t₀ v₀ r

/-- Pulls a coefficient field back by parabolic affine scaling. -/
def pullbackCoefficient  (B : CoefficientField d)
    (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ) : CoefficientField d :=
  fun t v ↦ B (t₀ + r ^ 2 * t) (v₀ + r • v)

/-- Evaluation of a scalar pullback. -/
@[simp] theorem pullbackScalar_apply  (q : TimeVelocity d → ℝ)
    (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ) (z : TimeVelocity d) :
    pullbackScalar q t₀ v₀ r z = q (parabolicAffine t₀ v₀ r z) :=
  rfl

/-- Evaluation of a coefficient pullback. -/
@[simp] theorem coefficientAt_pullbackCoefficient  (B : CoefficientField d)
    (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ) (z : TimeVelocity d) :
    coefficientAt (pullbackCoefficient B t₀ v₀ r) z =
      coefficientAt B (parabolicAffine t₀ v₀ r z) :=
  rfl

/-- Local coefficient continuity is preserved by parabolic affine pullback. -/
theorem IsContinuousCoefficientOn.pullback  {B : CoefficientField d}
    {U V : HypoellipticAleksandrov.Parabolic.Region d} {t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hB : IsContinuousCoefficientOn B U)
    (hmap : MapsTo (parabolicAffine t₀ v₀ r) V U) :
    IsContinuousCoefficientOn (pullbackCoefficient B t₀ v₀ r) V := hB.comp (contDiff_parabolicAffine t₀ v₀ r).continuous.continuousOn hmap

variable {q : TimeVelocity d → ℝ} {U V : HypoellipticAleksandrov.Parabolic.Region d} {t₀ r : ℝ} {v₀ : PDE.Vec d}

/-- Local `C²` regularity is preserved by parabolic affine pullback. -/
theorem ContDiffOn.pullbackScalar
    (hq : ContDiffOn ℝ 2 q U) (hmap : MapsTo (parabolicAffine t₀ v₀ r) V U) :
    ContDiffOn ℝ 2 (pullbackScalar q t₀ v₀ r) V := hq.comp (contDiff_parabolicAffine t₀ v₀ r).contDiffOn hmap

/-- Local nonnegativity is preserved by parabolic affine pullback. -/
theorem IsNonnegativeOn.pullbackScalar
    (hq : IsNonnegativeOn q U) (hmap : MapsTo (parabolicAffine t₀ v₀ r) V U) :
    IsNonnegativeOn (pullbackScalar q t₀ v₀ r) V :=
  fun z hz => by
    bound

variable {B : CoefficientField d} {U V : HypoellipticAleksandrov.Parabolic.Region d}

/-- Local lower ellipticity is preserved by parabolic affine pullback. -/
theorem HasLowerEllipticityOn.pullback   {lam t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hB : HasLowerEllipticityOn lam B U)
    (hmap : MapsTo (parabolicAffine t₀ v₀ r) V U) :
    HasLowerEllipticityOn lam (pullbackCoefficient B t₀ v₀ r) V :=
  fun z hz => by
    aesop

/-- Local upper ellipticity is preserved by parabolic affine pullback. -/
theorem HasUpperEllipticityOn.pullback   {Lam t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hB : HasUpperEllipticityOn Lam B U)
    (hmap : MapsTo (parabolicAffine t₀ v₀ r) V U) :
    HasUpperEllipticityOn Lam (pullbackCoefficient B t₀ v₀ r) V :=
  fun z hz => by
    aesop

section
variable {q : TimeVelocity d → ℝ} {z : TimeVelocity d} {t₀ r : ℝ} {v₀ : PDE.Vec d} (hq : ContDiffAt ℝ 2 q (parabolicAffine t₀ v₀ r z))

include hq
private theorem fderiv_pullbackScalar_eventually   :
    fderiv ℝ (pullbackScalar q t₀ v₀ r) =ᶠ[𝓝 z]
      fun y ↦ (fderiv ℝ q (parabolicAffine t₀ v₀ r y)).comp
        (parabolicLinear  r) := by

  have hlocal := hq.eventually (by
      norm_cast)
  filter_upwards [(hasFDerivAt_parabolicAffine t₀ v₀ r z).continuousAt.tendsto.eventually
    hlocal] with y hy
  change fderiv ℝ (q ∘ parabolicAffine t₀ v₀ r) y = _
  rw [fderiv_comp y (hy.differentiableAt (by norm_num))
    (hasFDerivAt_parabolicAffine t₀ v₀ r y).differentiableAt,
    (hasFDerivAt_parabolicAffine t₀ v₀ r y).fderiv]

/-- The velocity Hessian of a scalar pullback has the exact parabolic scale. -/
theorem velocityHessian_pullbackScalar   :
    velocityHessian (pullbackScalar q t₀ v₀ r) z =
      r ^ 2 • velocityHessian q (parabolicAffine t₀ v₀ r z) := by
  let a := parabolicAffine t₀ v₀ r
  let L := parabolicLinear (d := d) r
  let c  := fun y ↦ fderiv ℝ q (a y)
  have hc : HasFDerivAt c ((fderiv ℝ (fderiv ℝ q) (a z)).comp L) z := by
    exact ((hq.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp z (hasFDerivAt_parabolicAffine t₀ v₀ r z)




  ext i j
  unfold velocityHessian
  rw [((hc.clm_comp (hasFDerivAt_const L z)).congr_of_eventuallyEq (fderiv_pullbackScalar_eventually hq)).fderiv]
  simp [a, L, c, parabolicLinear, parabolicAffine, ContinuousLinearMap.compL]
  let H := fderiv ℝ (fderiv ℝ q) (t₀ + r ^ 2 * z.1, v₀ + r • z.2)
  change H ((0 ), r • (Pi.single i (1 ) : PDE.Vec d))
      ((0 ), r • (Pi.single j (1 ) : PDE.Vec d)) =
    r ^ 2 * H ((0 ), (Pi.single i (1 ) ))
      ((0 ), (Pi.single j (1 ) ))
  have hi : ((0 : ℝ), r • (Pi.single i (1 ) : PDE.Vec d)) =
      r • ((0 : ℝ), (Pi.single i (1 ) : PDE.Vec d)) := by
    ext <;> simp
  have hj : ((0 : ℝ), r • (Pi.single j (1 ) : PDE.Vec d)) =
      r • ((0 : ℝ), (Pi.single j (1 ) : PDE.Vec d)) := by
    ext <;> simp
  rw [hi, H.map_smul]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hj, (H ((0 ), (Pi.single i (1 ) ))).map_smul]
  simp only [smul_eq_mul]
  ring

/-- The time derivative of a scalar pullback has the exact parabolic scale. -/
theorem timeDerivative_pullbackScalar   :
    timeDerivative (pullbackScalar q t₀ v₀ r) z =
      r ^ 2 * timeDerivative q (parabolicAffine t₀ v₀ r z) := by
  let sharedTerm_06b2dc29f2 := ((fderiv ℝ q (parabolicAffine t₀ v₀ r z)))
  unfold timeDerivative
  rw [show fderiv ℝ (pullbackScalar q t₀ v₀ r) z =
      sharedTerm_06b2dc29f2.comp (parabolicLinear  r) from (hq.differentiableAt (by norm_num)).hasFDerivAt.comp z
      (hasFDerivAt_parabolicAffine t₀ v₀ r z) |>.fderiv]
  simp only [ContinuousLinearMap.comp_apply, parabolicLinear_apply]
  simpa [smul_eq_mul] using
    sharedTerm_06b2dc29f2.map_smul (r ^ 2)
      ((1 ), (0 ))
end


variable {B : CoefficientField d}

section
variable {q : TimeVelocity d → ℝ} {z : TimeVelocity d} {t₀ r : ℝ} {v₀ : PDE.Vec d} (hq : ContDiffAt ℝ 2 q (parabolicAffine t₀ v₀ r z))

include hq
/-- Matrix contraction with a pullback Hessian has the exact parabolic scale. -/
theorem matrixContraction_pullbackScalar
     :
    matrixContraction (coefficientAt (pullbackCoefficient B t₀ v₀ r) z)
      (velocityHessian (pullbackScalar q t₀ v₀ r) z) =
      r ^ 2 * matrixContraction (coefficientAt B (parabolicAffine t₀ v₀ r z))
        (velocityHessian q (parabolicAffine t₀ v₀ r z)) := by
  simp_all [coefficientAt_pullbackCoefficient, velocityHessian_pullbackScalar]

/-- The forward parabolic operator is covariant under every parabolic affine map. -/
theorem parabolicOperator_pullbackScalar
     :
    parabolicOperator (pullbackCoefficient B t₀ v₀ r) (pullbackScalar q t₀ v₀ r) z =
      r ^ 2 * parabolicOperator B q (parabolicAffine t₀ v₀ r z) := by
  rw [parabolicOperator_apply, parabolicOperator_apply,
    timeDerivative_pullbackScalar hq, matrixContraction_pullbackScalar hq]
  ring
end


/-- A local supersolution pulls back with its source multiplied by the square scale. -/
theorem IsParabolicSupersolutionOn.pullback
    {f q : TimeVelocity d → ℝ} {U V : HypoellipticAleksandrov.Parabolic.Region d} {t₀ r : ℝ}
    {v₀ : PDE.Vec d} (hU : IsOpen U) (hq : ContDiffOn ℝ 2 q U)
    (h : IsParabolicSupersolutionOn B f q U)
    (hmap : MapsTo (parabolicAffine t₀ v₀ r) V U) :
    IsParabolicSupersolutionOn (pullbackCoefficient B t₀ v₀ r)
      (fun z ↦ r ^ 2 * f (parabolicAffine t₀ v₀ r z))
      (pullbackScalar q t₀ v₀ r) V := by
  intro z hz
  rw [parabolicOperator_pullbackScalar
    (contDiffAt_of_contDiffOn_of_isOpen hU hq (hmap hz))]
  exact mul_le_mul_of_nonneg_left (h _ (hmap hz)) (sq_nonneg r)

variable (A : CoefficientField d)

variable (T : ℝ)

/-- A coefficient field expressed in the absolute-time age variable. -/
def ageCoefficient    : CoefficientField d :=
  fun theta v ↦ A (T - theta) v

/-- Evaluation of the absolute-time age coefficient. -/
@[simp] theorem coefficientAt_ageCoefficient
     (z : TimeVelocity d) :
    coefficientAt (ageCoefficient A T) z = A (T - z.1) z.2 :=
  rfl





end HypoellipticAleksandrov.Parabolic
