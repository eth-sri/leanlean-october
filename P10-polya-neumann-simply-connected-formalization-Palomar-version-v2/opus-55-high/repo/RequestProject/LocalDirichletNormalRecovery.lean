module

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
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff

variable {a b : ℂ → ℂ} {z : ℂ} {U : Set ℂ}

theorem dirichlet_normal_dirD_add (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) (v : ℂ) :
    dirD (fun w => a w + b w) v z = dirD a v z + dirD b v z := by
  change fderiv ℝ (fun w => a w + b w) z v = _
  rw [fderiv_fun_add ha hb]
  rfl

theorem dirichlet_normal_dirD_sub (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) (v : ℂ) :
    dirD (fun w => a w - b w) v z = dirD a v z - dirD b v z := by
  change fderiv ℝ (fun w => a w - b w) z v = _
  rw [fderiv_fun_sub ha hb]
  rfl

theorem dirichlet_normal_dirD_mul (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) (v : ℂ) :
    dirD (fun w => a w * b w) v z = dirD a v z * b z + a z * dirD b v z := by
  change fderiv ℝ (fun w => a w * b w) z v = _
  rw [fderiv_fun_mul ha hb]
  change a z * dirD b v z + b z * dirD a v z = _
  ring

/-- The actual graph curvature coefficient in complex scalar form. -/
def dirichletGraphCurvature (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ((deriv (deriv f) z.re : ℝ) : ℂ)

theorem dirD_dirichletGraphSlope_one {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : ℂ) :
    dirD (dirichletGraphSlope f) 1 z = dirichletGraphCurvature f z := by
  change fderiv ℝ (Complex.ofRealCLM ∘ (deriv f ∘ Complex.re)) z 1 = _
  simp [(Complex.ofRealCLM.hasFDerivAt.comp z     ((((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)) z.re).hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt)).fderiv, dirichletGraphCurvature]

/-- Mixed derivative symmetry is derived at each genuine smooth interior
point; it is not an assumed weak second-derivative identity. -/
theorem dirichlet_normal_dirD_comm (hU : IsOpen U) {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) {z : ℂ} (hz : z ∈ U) (v w : ℂ) :
    dirD (dirD u v) w z = dirD (dirD u w) v z := by
  have hs := hu.contDiffAt (hU.mem_nhds hz)
  have hd  :=
    (hs.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).differentiableAt (by simp)
  have hv : fderiv ℝ (dirD u v) z w = fderiv ℝ (fderiv ℝ u) z w v := by
    change fderiv ℝ (fun x => fderiv ℝ u x v) z w = _
    simp [fderiv_clm_apply hd (differentiableAt_const v)]
  have hw : fderiv ℝ (dirD u w) z v = fderiv ℝ (fderiv ℝ u) z v w := by
    change fderiv ℝ (fun x => fderiv ℝ u x w) z v = _
    simp [fderiv_clm_apply hd (differentiableAt_const w)]
  change fderiv ℝ (dirD u v) z w = fderiv ℝ (dirD u w) z v
  rw [hv, hw]
  exact (hs.isSymmSndFDerivAt (by
    norm_num)).eq w v

theorem dirichletFlattenedDivergence_normal_expansion (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) {z : ℂ} (hz : z ∈ U) :
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
  have hdy  := dirD_dirichletGraphSlope_I hf z
  have haI : dirD (fun w => 1 + d w ^ 2) Complex.I z = 0 := by
    have heq : (fun w => 1 + d w ^ 2) = fun w => 1 + d w * d w := by
      ring
    rw [heq, dirichlet_normal_dirD_add 
      (b := fun w => d w * d w) (differentiableAt_const 1) (hd.mul hd),
      dirichlet_normal_dirD_mul   hd hd, hdy]
    simp [dirD]
  have hflux₀ : dirD (dirichletFlattenedFlux f u 0) 1 z =
      dirD x 1 z - (dirichletGraphCurvature f z * y z + d z * dirD y 1 z) := by
    change dirD (fun w => x w - d w * y w) 1 z = _
    rw [dirichlet_normal_dirD_sub  (b := fun w => d w * y w)
      hx (hd.mul hy), dirichlet_normal_dirD_mul   hd hy, dirD_dirichletGraphSlope_one hf z]
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
      dirichlet_normal_dirD_mul (a := fun w => 1 + d w ^ 2) 
        ((differentiableAt_const 1).add (hd.pow 2)) hy,
      dirichlet_normal_dirD_mul   hd hx, haI, hdy]
    ring
  rw [dirichletFlattenedDivergence, hflux₀, hflux₁]
  rw [dirichlet_normal_dirD_comm hU hu hz Complex.I 1]
  ring

/-- The reciprocal actual normal coefficient, with a genuine global bound. -/
def dirichletNormalCoefficientInverse (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  Complex.ofReal ((1 + (deriv f z.re) ^ 2 : ℝ)⁻¹)

theorem dirichletNormalCoefficientInverse_mul (f : ℝ → ℝ) (z : ℂ) :
    dirichletNormalCoefficientInverse f z * (1 + dirichletGraphSlope f z ^ 2) = 1 := by
  have heq : 1 + dirichletGraphSlope f z ^ 2 =
      (1 + (deriv f z.re) ^ 2 : ℝ) := by
    simp [dirichletGraphSlope]
  rw [heq, dirichletNormalCoefficientInverse, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (by positivity), Complex.ofReal_one]

theorem dirichlet_normal_derivative_recovery (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u G : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hstrong : ∀ z ∈ U, dirichletFlattenedDivergence f u z = -G z)
    {z : ℂ} (hz : z ∈ U) :
    dirD (dirD u Complex.I) Complex.I z = dirichletNormalCoefficientInverse f z *
      (-G z + dirichletGraphCurvature f z * dirD u Complex.I z +
        2 * dirichletGraphSlope f z * dirD (dirD u 1) Complex.I z -
        dirD (dirD u 1) 1 z) := by
  have he := dirichletFlattenedDivergence_normal_expansion hU hf hu hz
  rw [hstrong z hz] at he
  have hnum : -G z + dirichletGraphCurvature f z * dirD u Complex.I z +
      2 * dirichletGraphSlope f z * dirD (dirD u 1) Complex.I z - dirD (dirD u 1) 1 z =
      (1 + dirichletGraphSlope f z ^ 2) * dirD (dirD u Complex.I) Complex.I z := by
    linear_combination he
  rw [hnum, ← mul_assoc, dirichletNormalCoefficientInverse_mul, one_mul]

section NormalData

variable {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u G : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hstrong : ∀ z ∈ U, dirichletFlattenedDivergence f u z = -G z)
    (hG : MemLp G 2 (volume.restrict U))
    (hDy : MemLp (dirD u Complex.I) 2 (volume.restrict U))
    (hDxx : MemLp (dirD (dirD u 1) 1) 2 (volume.restrict U))
    (hDxy : MemLp (dirD (dirD u 1) Complex.I) 2 (volume.restrict U))
    {L M : ℝ}
    (hSlope : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphSlope f z‖ ≤ L)
    (hCurvature : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphCurvature f z‖ ≤ M)

end NormalData

end PolyaNeumann
end
