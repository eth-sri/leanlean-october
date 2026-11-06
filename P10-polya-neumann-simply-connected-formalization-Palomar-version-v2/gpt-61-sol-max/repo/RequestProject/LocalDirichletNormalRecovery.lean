module

public import RequestProject.PlanarTypes

public import RequestProject.LocalDirichletFlattenedEquation
public import RequestProject.RiemannMappingEnergy
public import RequestProject.LpBoundedMultiplier
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
Recovery of the actual normal second derivative in a smooth graph chart.
The matrix is `[[1,-f′],[-f′,1+f′²]]`. The existing physical equation has
`div(A∇u) = -G`, hence the recovered numerator is
`-G + f′′ Dy u + 2 f′ Dxy u - Dxx u`. Tangential second derivatives may be
supplied as genuine L² data; no normal second derivative or recovery identity
is assumed. Interior smoothness and localized compact-test integration by
parts turn the recovered L² derivative into the actual weak derivative.
This module is part of the verified dependency chain.
-/

@[expose] public section
noncomputable section
namespace PolyaNeumann

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff

section
variable {a b : PlaneMap} {z } (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) (v : ℂ)
include a b z ha hb v

theorem dirichlet_normal_dirD_add :
    dirD (fun w => a w + b w) v z = dirD a v z + dirD b v z := by
  change fderiv ℝ (fun w => a w + b w) z v = _
  rw [fderiv_fun_add ha hb]
  rfl

theorem dirichlet_normal_dirD_sub :
    dirD (fun w => a w - b w) v z = dirD a v z - dirD b v z := by
  change fderiv ℝ (fun w => a w - b w) z v = _
  rw [fderiv_fun_sub ha hb]
  rfl

theorem dirichlet_normal_dirD_mul :
    dirD (fun w => a w * b w) v z = dirD a v z * b z + a z * dirD b v z := by
  change fderiv ℝ (fun w => a w * b w) z v = _
  rw [fderiv_fun_mul ha hb]
  change a z * dirD b v z + b z * dirD a v z = _
  ring

end


/-- The actual graph curvature coefficient in complex scalar form. -/
def dirichletGraphCurvature f (z : ℂ)  :=
  ((deriv (deriv f) z.re : ℝ) : ℂ)

theorem dirD_dirichletGraphSlope_one 
    (hf : RealSmooth f) z :
    dirD (dirichletGraphSlope f) 1 z = dirichletGraphCurvature f z := by
  have hd := ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)) z.re
  have hs := Complex.ofRealCLM.hasFDerivAt.comp z
    (hd.hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt)
  change fderiv ℝ (Complex.ofRealCLM ∘ (deriv f ∘ Complex.re)) z 1 = _
  rw [hs.fderiv]
  aesop

section
variable {U : PlanarSet} (hU : IsOpen U) {f : RealMap} (hf : RealSmooth f)

include U hU f hf in
theorem dirichletFlattenedDivergence_normal_expansion 
    (hu : RealSmoothOn u U)  (hz : z ∈ U) :
    dirichletFlattenedDivergence f u z =
      dirD (dirD u 1) 1 z - dirichletGraphCurvature f z * dirD u Complex.I z -
        2 * dirichletGraphSlope f z * dirD (dirD u 1) Complex.I z +
        (1 + dirichletGraphSlope f z ^ 2) * dirD (dirD u Complex.I) Complex.I z := by
  let d := dirichletGraphSlope f
  let x := dirD u 1
  let y := dirD u Complex.I
  have hd  :=
    (dirichletGraphSlope_contDiff hf).differentiable (by simp) z
  have hx  :=
    ((dirichlet_contDiffOn_dirD hU hu 1).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds hz)
  have hy  :=
    ((dirichlet_contDiffOn_dirD hU hu Complex.I).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds hz)
  have hdx  := dirD_dirichletGraphSlope_one hf z
  have hdy  := dirD_dirichletGraphSlope_I hf z
  have haI : dirD (fun w => (1 : ℂ) + d w ^ 2) Complex.I z = 0 := by
    have heq : (fun w => (1 : ℂ) + d w ^ 2) = fun w => 1 + d w * d w := by
      funext w
      rw [pow_two]
    rw [heq, dirichlet_normal_dirD_add (a := fun _ => 1)
      (b := fun w => d w * d w) (differentiableAt_const 1) (hd.mul hd),
      dirichlet_normal_dirD_mul (a := d) (b := d) hd hd, hdy]
    simp [dirD]
  have hflux₀ : dirD (dirichletFlattenedFlux f u 0) 1 z =
      dirD x 1 z - (dirichletGraphCurvature f z * y z + d z * dirD y 1 z) := by
    change dirD (fun w => x w - d w * y w) 1 z = _
    rw [dirichlet_normal_dirD_sub (a := x) (b := fun w => d w * y w)
      hx (hd.mul hy), dirichlet_normal_dirD_mul (a := d) (b := y) hd hy, hdx]
  have hflux₁ : dirD (dirichletFlattenedFlux f u 1) Complex.I z =
      -d z * dirD x Complex.I z + (1 + d z ^ 2) * dirD y Complex.I z := by
    have heq : dirichletFlattenedFlux f u 1 =
        fun w => (1 + d w ^ 2) * y w - d w * x w := by
      funext w
      change -d w * x w + (1 + d w ^ 2) * y w = _
      ring
    rw [heq, dirichlet_normal_dirD_sub
      (a := fun w => (1 + d w ^ 2) * y w) (b := fun w => d w * x w)
      (((differentiableAt_const 1).add (hd.pow 2)).mul hy) (hd.mul hx),
      dirichlet_normal_dirD_mul (a := fun w => 1 + d w ^ 2) (b := y)
        ((differentiableAt_const 1).add (hd.pow 2)) hy,
      dirichlet_normal_dirD_mul (a := d) (b := x) hd hx, haI, hdy]
    ring
  grind only [dirichletFlattenedDivergence, dirD, dirichletGraphCurvature, dirichletGraphSlope, dirichlet_dirD_comm]

/-- The reciprocal actual normal coefficient, with a genuine global bound. -/
def dirichletNormalCoefficientInverse f (z : ℂ)  :=
  Complex.ofReal ((1 + (deriv f z.re) ^ 2 : ℝ)⁻¹)

theorem dirichletNormalCoefficientInverse_mul f z :
    dirichletNormalCoefficientInverse f z * (1 + dirichletGraphSlope f z ^ 2) = 1 := by
  have hpos : (1 + (deriv f z.re) ^ 2 : ℝ) ≠ 0 := by positivity
  have heq : (1 + dirichletGraphSlope f z ^ 2 : ℂ) =
      ((1 + (deriv f z.re) ^ 2 : ℝ) : ℂ) := by
    simp [dirichletGraphSlope]
  rw [heq, dirichletNormalCoefficientInverse, ← Complex.ofReal_mul,
    inv_mul_cancel₀ hpos, Complex.ofReal_one]

include U hU f hf in
theorem dirichlet_normal_derivative_recovery {u G : PlaneMap}
    (hu : RealSmoothOn u U)
    (hstrong : ∀ z ∈ U, dirichletFlattenedDivergence f u z = -G z)
     (hz : z ∈ U) :
    dirD (dirD u Complex.I) Complex.I z = dirichletNormalCoefficientInverse f z *
      (-G z + dirichletGraphCurvature f z * dirD u Complex.I z +
        2 * dirichletGraphSlope f z * dirD (dirD u 1) Complex.I z -
        dirD (dirD u 1) 1 z) := by
  grind only [dirichletFlattenedDivergence_normal_expansion, dirichletGraphCurvature, dirD, dirichletGraphSlope, dirichletNormalCoefficientInverse_mul]

end



end PolyaNeumann
end
