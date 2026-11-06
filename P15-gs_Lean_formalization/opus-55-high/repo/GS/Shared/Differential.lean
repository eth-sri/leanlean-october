module

public import GS.Shared.FactorCharts
public import GS.Shared.Directions

@[expose] public section

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
open Matrix
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {right left : Pattern 𝕜 n}

section
variable (g : Factors right left)
/-- Total reconstruction in the genuine shared product group. -/
def factorLift (v : PairGenerator right left) :
    Factors right left := (reconstruct g.1 v.1, reconstruct g.2 v.2)

@[simp] theorem factorLift_zero : factorLift g 0 = g :=
  Prod.ext (reconstruct_zero g.1) (reconstruct_zero g.2)

theorem continuous_factorLift : Continuous (factorLift g) :=
  ((continuous_reconstruct g.1).comp continuous_fst).prodMk
    ((continuous_reconstruct g.2).comp continuous_snd)

end

section
variable (g : Factors right left) (P : 𝕄)
/-- Matrix formula on the whole shared coordinate model. -/
def orbitParam (v : PairGenerator right left) :
    𝕄 := factorLift g v • P

@[simp] theorem orbitParam_zero :
    orbitParam g P 0 = g • P := by simp only [orbitParam, factorLift_zero]

theorem orbitParam_smooth :
    ContDiff ℝ ⊤ (orbitParam g P) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  exact smooth_mul_at
    (smooth_mul_at ((reconstruct_matrix_smooth g.1).contDiffAt.comp v contDiffAt_fst)
      contDiffAt_const)
    (smooth_conjTranspose_at ((reconstruct_matrix_smooth g.2).contDiffAt.comp v contDiffAt_snd))

end

/-- Reuse the checked ambient Cayley derivative without changing its proof. -/
theorem reconstruct_line_hasDerivAt_zero {s : Pattern 𝕜 n} (Q : Factor s)
    (v : Generator s) :
    HasDerivAt (fun t : ℝ => Factor.matrix (reconstruct Q (t • v)))
      ((-2 : ℝ) • (Factor.matrix Q * v.val)) 0 :=
  (hasDerivAt_matrix_mul (hasDerivAt_const 0 (Factor.matrix Q))
    (cayley_line_derivative v.val v.property.2.1)).congr_deriv (by simp)

section
variable (g : Factors right left)
/-- True Frechet derivative at the centre, not a definition of a differential. -/
theorem orbitParam_fderiv_zero (v : PairGenerator right left) :
    fderiv ℝ (orbitParam g P) 0 v =
      tangentParam (Factor.matrix g.1) P (Factor.matrix g.2)ᴴ
        ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) := by
  have hdL := reconstruct_line_hasDerivAt_zero g.1 v.1
  have hdR := hasDerivAt_matrix_conjTranspose (reconstruct_line_hasDerivAt_zero g.2 v.2)
  have ht : ((-2 : ℝ) • (Factor.matrix g.2 * v.2.val))ᴴ =
      (2 : ℝ) • (v.2.val * (Factor.matrix g.2)ᴴ) := by
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_mul, v.2.property.2.1,
      Matrix.neg_mul, smul_neg, ← neg_smul]
    norm_num
  rw [ht] at hdR
  have hactual := hasDerivAt_product2 P hdL hdR
  have hi := ((orbitParam_smooth g P).differentiable (by simp) 0).hasFDerivAt
  have hcomputed := hi.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).smul_const v) (by simp)
  have ha : HasDerivAt (fun t : ℝ => orbitParam g P (t • v))
      (tangentParam (Factor.matrix g.1) P (Factor.matrix g.2)ᴴ
        ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val)) 0 := by
    simpa only [orbitParam, factorLift, action_apply, zero_smul,
      reconstruct_zero, tangentParam, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc, Prod.smul_fst, Prod.smul_snd] using hactual
  simpa only [one_smul] using hcomputed.unique ha

/-- The actual coordinate differential has the full tied generator range. -/
theorem orbitParam_fderiv_zero_range (P Y : 𝕄) :
    (∃ v : PairGenerator right left, fderiv ℝ (orbitParam g P) 0 v = Y) ↔
      Y ∈ pointDirections right left (g • P) := by
  change (∃ v : PairGenerator right left, fderiv ℝ (orbitParam g P) 0 v = Y) ↔
    Y ∈ pointDirections right left (Factor.matrix g.1 * P * (Factor.matrix g.2)ᴴ)
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
    change tangentParam (Factor.matrix g.1) P (Factor.matrix g.2)ᴴ
      ((-2 : ℝ) • ((-1 / 2 : ℝ) • C)) ((2 : ℝ) • ((1 / 2 : ℝ) • Ω)) = _
    norm_num [smul_smul, tangentParam]

end

section
variable (P : 𝕄) (v : PairGenerator right left)
theorem orbitParam_kernel_iff_intertwine :
    fderiv ℝ (orbitParam (1 : Factors right left) P) 0 v = 0 ↔
      v.1.val * P = P * v.2.val := by
  rw [orbitParam_fderiv_zero]
  change tangentParam (1 : 𝕄) P (1 : 𝕄)ᴴ
    ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) = 0 ↔ _
  simp only [tangentParam, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul]
  constructor
  · intro h
    have hz : (-2 : ℝ) • (v.1.val * P - P * v.2.val) = 0 := by
      simpa only [smul_sub, sub_eq_add_neg, smul_add, smul_neg,
        neg_smul, neg_add_rev, neg_neg] using h
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  simp_all

/-- Both implications hold for the entire Cayley parameter domain.  Thus the
continuous shared stabilizer is handled by its true linear kernel in this chart. -/
theorem factorLift_stabilizes_iff_kernel :
    factorLift (1 : Factors right left) v • P = P ↔
      fderiv ℝ (orbitParam (1 : Factors right left) P) 0 v = 0 := by
  rw [orbitParam_kernel_iff_intertwine]
  have hA := admissible_of_isSkew v.1.property.2.1
  have hB := admissible_of_isSkew v.2.property.2.1
  have ho := cayley_unitary v.2.property.2.1 hB
  simp only [factorLift, action_apply, reconstruct_matrix, Prod.fst_one, Prod.snd_one, Factor.matrix_one,
    Matrix.one_mul]
  constructor
  · intro h
    have he := congrArg (fun Y : 𝕄 => Y * cayley v.2.val) h
    have hi : cayley v.1.val * P = P * cayley v.2.val := by
      simpa only [Matrix.mul_assoc, ho.1, Matrix.mul_one] using he
    have hc := cayley_intertwine (admissible_cayley hA) (admissible_cayley hB) hi
    simpa only [cayley_involutive hA, cayley_involutive hB] using hc
  · intro h
    rw [cayley_intertwine hA hB h,
      Matrix.mul_assoc, ho.2, Matrix.mul_one]

end

end GS.Shared
