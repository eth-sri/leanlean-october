import GS.MatrixGeometry.Base

import GS.MatrixGeometry.FactorCharts
import GS.MatrixGeometry.Directions



set_option backward.isDefEq.respectTransparency false
/-!
# The actual shared orbit differential and its stabilizer kernel

Differentiate the concrete Cayley factor parametrization, retaining the -2
and +2 coefficients of the existing Cayley convention.  Its range is exactly
the point-based shared direction space.  At the identity, its entire kernel
integrates to the actual shared stabilizer; conversely every stabilizer element
in this Cayley chart comes from that kernel.

These are coordinate differentials of an actual smooth factor map.  No atlas
or manifold tangent space on its orbit image is introduced in this module.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.MatrixBase
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  {right left : Pattern 𝕜 n}
variable (g : Factors right left)


variable (P Y : KMat 𝕜 n)

variable (v : PairGenerator right left)

/-- Total reconstruction in the genuine shared product group. -/
def factorLift  :
    Factors right left := (reconstruct g.1 v.1, reconstruct g.2 v.2)

@[simp] theorem factorLift_zero : factorLift g 0 = g := Prod.ext (reconstruct_zero g.1) (reconstruct_zero g.2)

theorem continuous_factorLift : Continuous (factorLift g) :=
  by fun_prop [factorLift]

/-- Matrix formula on the whole shared coordinate model. -/
def orbitParam   :
    KMat 𝕜 n := factorLift g v • P

@[simp] theorem orbitParam_zero  :
    orbitParam g P 0 = g • P := by simp_all [factorLift_zero,orbitParam]

theorem orbitParam_smooth  :
    ContDiff ℝ ⊤ (orbitParam g P) := smooth_matrix_product
    (smooth_matrix_product ((reconstruct_matrix_smooth g.1).comp contDiff_fst) contDiff_const)
    ((matrixConjTransposeCLM  ).contDiff.comp
      ((reconstruct_matrix_smooth g.2).comp contDiff_snd))

/-- Reuse the checked ambient Cayley derivative without changing its proof. -/
theorem reconstruct_line_hasDerivAt_zero {s : Pattern 𝕜 n} (Q : Factor s)
    (v : Generator s) :
    HasDerivAt (fun t : ℝ => Factor.matrix (reconstruct Q (t • v)))
      ((-2 : ℝ) • (Factor.matrix Q * v.val)) 0 :=
  GS.MatrixBase.chartInv_line_hasDerivAt_zero (Factor.matrix Q) v.val v.property.2.1

/-- True Frechet derivative at the centre, not a definition of a differential. -/
theorem orbitParam_fderiv_zero 
     :
    fderiv ℝ (orbitParam g P) 0 v =
      GS.MatrixBase.tangentParam (Factor.matrix g.1) P (Factor.matrix g.2)ᴴ
        ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) := by
  have hdL := reconstruct_line_hasDerivAt_zero g.1 v.1
  have hdR := (matrixConjTransposeCLM  ).hasFDerivAt.comp_hasDerivAt 0
    (reconstruct_line_hasDerivAt_zero g.2 v.2)
  have ht : ((-2 : ℝ) • (Factor.matrix g.2 * v.2.val))ᴴ =
      (2 : ℝ) • (v.2.val * (Factor.matrix g.2)ᴴ) := by
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_mul, v.2.property.2.1,
      Matrix.neg_mul, smul_neg, ← neg_smul]
    norm_num
  change HasDerivAt (fun t => _ᴴ) _ᴴ 0 at hdR
  rw [ht] at hdR
  have hactual := hasDerivAt_matrix_mul
    (hasDerivAt_matrix_mul hdL (hasDerivAt_const 0 P)) hdR
  have hi := ((orbitParam_smooth g P).differentiable (by simp) 0).hasFDerivAt
  have hcomputed := hi.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).smul_const v) (by simp)
  have ha : HasDerivAt (fun t : ℝ => orbitParam g P (t • v))
      (GS.MatrixBase.tangentParam (Factor.matrix g.1) P (Factor.matrix g.2)ᴴ
        ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val)) 0 := by simp_all [GS.MatrixBase.tangentParam,factorLift,orbitParam,reconstruct_zero,action_apply,zero_smul,Prod.smul_fst,Prod.smul_snd,Matrix.mul_assoc,]
  simpa only [one_smul] using hcomputed.unique ha

/-- The actual coordinate differential has the full tied generator range. -/
theorem orbitParam_fderiv_zero_range  :
    (∃ v : PairGenerator right left, fderiv ℝ (orbitParam g P) 0 v = Y) ↔
      Y ∈ pointDirections right left (g • P) := by
  change (∃ v : PairGenerator right left, fderiv ℝ (orbitParam g P) 0 v = Y) ↔
    Y ∈ pointDirections right left (GS.MatrixBase.product2 (Factor.matrix g.1) P (Factor.matrix g.2)ᴴ)
  rw [← sharedDirection_iff_pointDirections P (Factor.matrix g.1)
    (Factor.matrix g.2)ᴴ Y (Factor.matrix_shared g.1)
    (shared_factor_conjTranspose (Factor.matrix_shared g.2))]
  constructor
  · rintro ⟨v, rfl⟩
    rw [orbitParam_fderiv_zero]
    let C := (-2 : ℝ) • v.1
    let Ω := (2 : ℝ) • v.2
    exact ⟨C.val, C.property, Ω.val, Ω.property, rfl⟩
  · rintro ⟨C, hC, Ω, hΩ, hY⟩
    let c : Generator left := ⟨C, hC⟩
    let w : Generator right := ⟨Ω, hΩ⟩
    refine ⟨((-1 / 2 : ℝ) • c, (1 / 2 : ℝ) • w), ?_⟩
    rw [orbitParam_fderiv_zero, hY]
    change GS.MatrixBase.tangentParam (Factor.matrix g.1) P (Factor.matrix g.2)ᴴ
      ((-2 : ℝ) • ((-1 / 2 : ℝ) • C)) ((2 : ℝ) • ((1 / 2 : ℝ) • Ω)) = _
    norm_num [smul_smul, GS.MatrixBase.tangentParam]

theorem orbitParam_intertwine_of_kernel
    (h : fderiv ℝ (orbitParam (1 : Factors right left) P) 0 v = 0) :
    v.1.val * P = P * v.2.val := by
  rw [orbitParam_fderiv_zero] at h
  change GS.MatrixBase.tangentParam (1 : KMat 𝕜 n) P (1 : KMat 𝕜 n)ᴴ
    ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) = 0 at h
  simp only [GS.MatrixBase.tangentParam, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul] at h
  linear_combination (norm := module) (-1/2 : ℝ) • h

end GS.MatrixGeometry
