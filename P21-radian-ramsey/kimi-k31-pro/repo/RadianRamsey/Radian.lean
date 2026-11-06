module

public import RadianRamsey.RadianAlgebra
public import RadianRamsey.AlgebraicRamsey
public import OAI.Combinatorics.EuclideanRamsey.NineLinearObstruction
public import OAI.Combinatorics.EuclideanRamsey.IndependentTensor

@[expose] public section

/-!
# Theorem D: the radian 9-gon is non-Ramsey when `tan (θ/2)` is transcendental

Theorem D of the spherical-ramsey note (`note/spherical-ramsey.tex`,
doi:10.5281/zenodo.23396387). The nine points `(cos kθ, sin kθ)`, `k = 0, …, 8`.

This mirrors OpenAI's `EuclideanRamseyNine` (openai/math @ fd4aeeb2, Apache-2.0, included under
`OAI/` with header-only changes for the module system, and imported): `NineLinearObstruction.not_ramsey_of_det_ne_zero` (necessity direction
through `ramsey_fieldCriterion`), `IndependentTensor.tensorEmbedding_injective`
(`ℚ(t) ⊗ ℚ(t) ↪ ℚ(T, U)`), and `CircleConsequence.circle_five_affineSpan`. The local
`Algebra ℚ` instances and the proof of `coefficientEquiv_tau` follow `NineField.lean`.
The determinant is in `RadianRamsey.RadianAlgebra`. OAI's definitions (`Ramsey`, `FieldCriterion`,
`augmented`, `coordinateField`) are used directly.
-/

namespace OAI
noncomputable section
open scoped TensorProduct
namespace EuclideanRamsey
namespace Radian

/-- The nine points at angles `0, θ, 2θ, …, 8θ` on the unit circle. -/
def radianConfig (θ : ℝ) (k : Fin 9) : Space 2 :=
  WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]

@[simp] theorem radianConfig_zero (θ : ℝ) (k : Fin 9) :
    radianConfig θ k 0 = Real.cos ((k : ℕ) * θ) := by simp [radianConfig]

@[simp] theorem radianConfig_one (θ : ℝ) (k : Fin 9) :
    radianConfig θ k 1 = Real.sin ((k : ℕ) * θ) := by simp [radianConfig]

theorem radianConfig_on_circle (θ : ℝ) (k : Fin 9) : dist (radianConfig θ k) 0 = 1 := by
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, sq_abs]

/-! ## Half-angle trigonometry -/

section Trig

theorem half_angle {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) :
    (1 + Real.tan (θ / 2) ^ 2) * Real.cos θ = 1 - Real.tan (θ / 2) ^ 2 ∧
      (1 + Real.tan (θ / 2) ^ 2) * Real.sin θ = 2 * Real.tan (θ / 2) := by
  obtain ⟨x, rfl⟩ : ∃ x, θ = 2 * x := ⟨θ / 2, by ring⟩
  have hx : 2 * x / 2 = x := by ring
  rw [hx] at hc ⊢
  have h1 := Real.sin_sq_add_cos_sq x
  rw [Real.cos_two_mul', Real.sin_two_mul, Real.tan_eq_sin_div_cos]
  constructor
  · field_simp
    linear_combination (Real.cos x ^ 2 - Real.sin x ^ 2) * h1
  · field_simp
    linear_combination Real.sin x * h1

theorem trig_rot {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) (n : ℕ) :
    (1 + Real.tan (θ / 2) ^ 2) ^ n * Real.cos (n * θ) = (rot (Real.tan (θ / 2)) n).1 ∧
      (1 + Real.tan (θ / 2) ^ 2) ^ n * Real.sin (n * θ) = (rot (Real.tan (θ / 2)) n).2 := by
  obtain ⟨h1, h2⟩ := half_angle hc
  set t := Real.tan (θ / 2)
  induction n with
  | zero => simp [rot]
  | succ n ih =>
    obtain ⟨i1, i2⟩ := ih
    have hca : Real.cos (((n + 1 : ℕ) : ℝ) * θ) =
        Real.cos (n * θ) * Real.cos θ - Real.sin (n * θ) * Real.sin θ := by
      rw [Nat.cast_succ, add_mul, one_mul, Real.cos_add]
    have hsa : Real.sin (((n + 1 : ℕ) : ℝ) * θ) =
        Real.sin (n * θ) * Real.cos θ + Real.cos (n * θ) * Real.sin θ := by
      rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add]
    rw [hca, hsa]
    simp only [rot]
    constructor
    · linear_combination ((1 + t ^ 2) * Real.cos θ) * i1 + (rot t n).1 * h1 -
        ((1 + t ^ 2) * Real.sin θ) * i2 - (rot t n).2 * h2
    · linear_combination ((1 + t ^ 2) * Real.cos θ) * i2 + (rot t n).2 * h1 +
        ((1 + t ^ 2) * Real.sin θ) * i1 + (rot t n).1 * h2

theorem one_add_tan_sq_ne (θ : ℝ) : 1 + Real.tan (θ / 2) ^ 2 ≠ 0 := by positivity

theorem cos_eq {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) (n : ℕ) :
    Real.cos (n * θ) = (rot (Real.tan (θ / 2)) n).1 / (1 + Real.tan (θ / 2) ^ 2) ^ n := by
  rw [eq_div_iff (pow_ne_zero n (one_add_tan_sq_ne θ)), mul_comm]
  exact (trig_rot hc n).1

theorem sin_eq {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) (n : ℕ) :
    Real.sin (n * θ) = (rot (Real.tan (θ / 2)) n).2 / (1 + Real.tan (θ / 2) ^ 2) ^ n := by
  rw [eq_div_iff (pow_ne_zero n (one_add_tan_sq_ne θ)), mul_comm]
  exact (trig_rot hc n).2

theorem tan_recover {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) :
    Real.tan (θ / 2) = Real.sin θ / (1 + Real.cos θ) := by
  obtain ⟨h1, h2⟩ := half_angle hc
  have hne : 1 + Real.cos θ ≠ 0 := by
    intro h
    have : (1 + Real.tan (θ / 2) ^ 2) * (1 + Real.cos θ) = 2 := by linear_combination h1
    rw [h, mul_zero] at this
    norm_num at this
  rw [eq_div_iff hne]
  apply mul_left_cancel₀ (one_add_tan_sq_ne θ)
  linear_combination Real.tan (θ / 2) * h1 - h2

theorem cos_half_ne {θ : ℝ} (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    Real.cos (θ / 2) ≠ 0 := by
  intro h
  apply ht
  rw [Real.tan_eq_sin_div_cos, h, div_zero]
  exact isAlgebraic_zero

end Trig

/-! ## The coordinate field is `ℚ(tan (θ/2))` -/

section CoordField

variable (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2)))
include ht

theorem tan_mem : Real.tan (θ / 2) ∈ coordinateField (radianConfig θ) := by
  rw [tan_recover (cos_half_ne ht)]
  let F := coordinateField (radianConfig θ)
  have hc (j : Fin 2) : radianConfig θ 1 j ∈ F :=
    IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self ((1 : Fin 9), j))
  simpa only [radianConfig_zero, radianConfig_one, Fin.val_one, Nat.cast_one, one_mul] using
    F.div_mem (hc 1) (F.add_mem F.one_mem (hc 0))

/-- The parameter `t = tan (θ/2)` as an element of the coordinate field. -/
def tau : Coeff (radianConfig θ) := ⟨Real.tan (θ / 2), tan_mem θ ht⟩

theorem coordinate_eq (k : Fin 9) :
    coordinate (radianConfig θ) k 0 = (rot (tau θ ht) k).1 / (1 + tau θ ht ^ 2) ^ (k : ℕ) ∧
      coordinate (radianConfig θ) k 1 = (rot (tau θ ht) k).2 / (1 + tau θ ht ^ 2) ^ (k : ℕ) := by
  have hm := map_rot (algebraMap (Coeff (radianConfig θ)) ℝ) (tau θ ht) k
  have hτ : algebraMap (Coeff (radianConfig θ)) ℝ (tau θ ht) = Real.tan (θ / 2) := rfl
  rw [hτ] at hm
  constructor
  · apply (algebraMap (Coeff (radianConfig θ)) ℝ).injective
    rw [map_div₀, map_pow, map_add, map_one, map_pow, hm.1, hτ]
    change radianConfig θ k 0 = _
    rw [radianConfig_zero, cos_eq (cos_half_ne ht)]
  · apply (algebraMap (Coeff (radianConfig θ)) ℝ).injective
    rw [map_div₀, map_pow, map_add, map_one, map_pow, hm.2, hτ]
    change radianConfig θ k 1 = _
    rw [radianConfig_one, sin_eq (cos_half_ne ht)]

theorem coordinateField_eq :
    coordinateField (radianConfig θ) =
      IntermediateField.adjoin ℚ (Set.range (fun _ : Unit => Real.tan (θ / 2))) := by
  let E : IntermediateField ℚ ℝ :=
    IntermediateField.adjoin ℚ (Set.range (fun _ : Unit => Real.tan (θ / 2)))
  let σ : E := ⟨Real.tan (θ / 2), IntermediateField.subset_adjoin ℚ _ ⟨(), rfl⟩⟩
  have hm (k : ℕ) := map_rot (algebraMap E ℝ) σ k
  have hσ : algebraMap E ℝ σ = Real.tan (θ / 2) := rfl
  rw [hσ] at hm
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨⟨k, j⟩, rfl⟩
    fin_cases j
    · have hx : radianConfig θ k 0 =
          algebraMap E ℝ ((rot σ k).1 / (1 + σ ^ 2) ^ (k : ℕ)) := by
        rw [map_div₀, map_pow, map_add, map_one, map_pow, (hm k).1, hσ, radianConfig_zero,
          cos_eq (cos_half_ne ht)]
      change radianConfig θ k 0 ∈ E
      rw [hx]
      exact Subtype.property ((rot σ k).1 / (1 + σ ^ 2) ^ (k : ℕ))
    · have hx : radianConfig θ k 1 =
          algebraMap E ℝ ((rot σ k).2 / (1 + σ ^ 2) ^ (k : ℕ)) := by
        rw [map_div₀, map_pow, map_add, map_one, map_pow, (hm k).2, hσ, radianConfig_one,
          sin_eq (cos_half_ne ht)]
      change radianConfig θ k 1 ∈ E
      rw [hx]
      exact Subtype.property ((rot σ k).2 / (1 + σ ^ 2) ^ (k : ℕ))
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨_, rfl⟩
    exact tan_mem θ ht

/-! ## Embedding `B = F ⊗ F` into `ℚ(T, U)` (as in OAI `NineField`) -/

local instance ratAlgebra : Algebra ℚ (IndependentTensor.Rat Unit) :=
  OreLocalization.instAlgebra (R₀ := ℚ) (R := IndependentTensor.Poly Unit)
    (S := nonZeroDivisors (IndependentTensor.Poly Unit))

local instance jointAlgebra : Algebra ℚ (IndependentTensor.JointField Unit) :=
  OreLocalization.instAlgebra (R₀ := ℚ) (R := IndependentTensor.JointPoly Unit)
    (S := nonZeroDivisors (IndependentTensor.JointPoly Unit))

theorem tan_indep : AlgebraicIndependent ℚ (fun _ : Unit => Real.tan (θ / 2)) :=
  algebraicIndependent_unique_type_iff.mpr ht

def coefficientEquiv : Coeff (radianConfig θ) ≃ₐ[ℚ] IndependentTensor.Rat Unit :=
  (IntermediateField.equivOfEq (coordinateField_eq θ ht)).trans
    (tan_indep θ ht).aevalEquivField.symm

theorem coefficientEquiv_tau :
    coefficientEquiv θ ht (tau θ ht) =
      algebraMap (IndependentTensor.Poly Unit) (IndependentTensor.Rat Unit)
        (MvPolynomial.X ()) := by
  apply (tan_indep θ ht).aevalEquivField.injective
  change (tan_indep θ ht).aevalEquivField
      ((tan_indep θ ht).aevalEquivField.symm
        ((IntermediateField.equivOfEq (coordinateField_eq θ ht)) (tau θ ht))) = _
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  change Real.tan (θ / 2) =
    ((tan_indep θ ht).aevalEquivField
      (algebraMap (IndependentTensor.Poly Unit) (IndependentTensor.Rat Unit)
        (MvPolynomial.X ())) : ℝ)
  rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
  simp

def leftCoeff : Coeff (radianConfig θ) →ₐ[ℚ] IndependentTensor.JointField Unit :=
  (IndependentTensor.leftMap Unit).comp (coefficientEquiv θ ht).toAlgHom

def rightCoeff : Coeff (radianConfig θ) →ₐ[ℚ] IndependentTensor.JointField Unit :=
  (IndependentTensor.rightMap Unit).comp (coefficientEquiv θ ht).toAlgHom

/-- The polynomial inclusion `ℚ[T, U] → ℚ(T, U)`. -/
abbrev incl : Poly →+* IndependentTensor.JointField Unit :=
  algebraMap (IndependentTensor.JointPoly Unit) (IndependentTensor.JointField Unit)

theorem leftCoeff_tau : leftCoeff θ ht (tau θ ht) = incl T := by
  simp [leftCoeff, coefficientEquiv_tau, T]

theorem rightCoeff_tau : rightCoeff θ ht (tau θ ht) = incl U := by
  simp [rightCoeff, coefficientEquiv_tau, U]

/-- Any algebra map sending `τ` to `z` sends the augmented coordinates to `rv z`. -/
theorem map_augmented {K : Type*} [Field K] [Algebra ℚ K]
    (g : Coeff (radianConfig θ) →ₐ[ℚ] K) (z : K) (hz : g (tau θ ht) = z) (k : Fin 9)
    (m : Fin 3) : g (augmented (radianConfig θ) k (finSuccEquiv 2 m)) = rv z k m := by
  have hm : g (rot (tau θ ht) k).1 = (rot z k).1 ∧ g (rot (tau θ ht) k).2 = (rot z k).2 := by
    rw [← hz]
    exact map_rot (g : Coeff (radianConfig θ) →+* K) (tau θ ht) k
  obtain ⟨hx, hy⟩ := coordinate_eq θ ht k
  fin_cases m
  · simp [augmented, rv]
  · change g (coordinate (radianConfig θ) k 0) = _
    rw [hx, map_div₀, map_pow, map_add, map_one, map_pow, hm.1, hz]
    simp [rv]
  · change g (coordinate (radianConfig θ) k 1) = _
    rw [hy, map_div₀, map_pow, map_add, map_one, map_pow, hm.2, hz]
    simp [rv]

/-- The tensor square of the coordinate field embeds in `ℚ(T, U)`. -/
def tensorMap : TensorRing (radianConfig θ) →ₐ[ℚ] IndependentTensor.JointField Unit :=
  (IndependentTensor.tensorEmbedding Unit).comp
    (Algebra.TensorProduct.congr (coefficientEquiv θ ht) (coefficientEquiv θ ht)).toAlgHom

theorem tensorMap_injective : Function.Injective (tensorMap θ ht) :=
  (IndependentTensor.tensorEmbedding_injective Unit).comp
    (Algebra.TensorProduct.congr (coefficientEquiv θ ht) (coefficientEquiv θ ht)).injective

@[simp] theorem tensorMap_tmul (x y : Coeff (radianConfig θ)) :
    tensorMap θ ht (x ⊗ₜ[ℚ] y) = leftCoeff θ ht x * rightCoeff θ ht y := by
  simp [tensorMap, leftCoeff, rightCoeff]

/-- Rows and columns: `Option (Fin 2) × Option (Fin 2) ≃ Fin 3 × Fin 3 ≃ Fin 9`. -/
def e : NineLinearObstruction.Column 2 ≃ Fin 9 :=
  (Equiv.prodCongr (finSuccEquiv 2).symm (finSuccEquiv 2).symm).trans
    (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin (3 * 3))

theorem reindex_evaluationMatrix :
    Matrix.reindex e e
        (NineLinearObstruction.evaluationMatrix (radianConfig θ) (tensorMap θ ht) e) =
      G (incl T) (incl U) := by
  ext k j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    NineLinearObstruction.evaluationMatrix, Equiv.apply_symm_apply, tensorMap_tmul, map_one,
    mul_one, one_mul, G]
  obtain ⟨h1, h2⟩ : (e.symm j).1 = finSuccEquiv 2 (col j).1 ∧
      (e.symm j).2 = finSuccEquiv 2 (col j).2 := ⟨rfl, rfl⟩
  rw [h1, h2, map_augmented θ ht _ _ (leftCoeff_tau θ ht),
    map_augmented θ ht _ _ (rightCoeff_tau θ ht)]

theorem evaluationMatrix_det_ne_zero :
    (NineLinearObstruction.evaluationMatrix (radianConfig θ) (tensorMap θ ht) e).det ≠ 0 := by
  rw [← Matrix.det_reindex_self e, reindex_evaluationMatrix]
  exact det_G_ne_zero incl
    (IsFractionRing.injective (IndependentTensor.JointPoly Unit)
      (IndependentTensor.JointField Unit))

/-- Distinctness is a consequence: two equal points give two equal rows. -/
theorem radianConfig_injective : Function.Injective (radianConfig θ) := by
  intro i j hij
  by_contra hne
  apply evaluationMatrix_det_ne_zero θ ht
  apply Matrix.det_zero_of_row_eq (e.symm.injective.ne hne)
  funext q
  have haug : augmented (radianConfig θ) i = augmented (radianConfig θ) j := by
    funext α
    cases α with
    | none => rfl
    | some m => exact Subtype.ext (congrArg (fun p : Space 2 => p m) hij)
  simp only [NineLinearObstruction.evaluationMatrix, Equiv.apply_symm_apply, haug]

theorem radianConfig_affineSpan : affineSpan ℝ (Set.range (radianConfig θ)) = ⊤ := by
  classical
  let A := affineSpan ℝ (Set.range (radianConfig θ))
  have hp (i : Fin 9) : radianConfig θ i ∈ A := mem_affineSpan ℝ (Set.mem_range_self i)
  let u := radianConfig θ 1 - radianConfig θ 0
  let v := radianConfig θ 2 - radianConfig θ 0
  let D : ℝ := u 0 * v 1 - v 0 * u 1
  have hid : D = 2 * Real.sin θ * (1 - Real.cos θ) := by
    simp [D, u, v, radianConfig_zero, radianConfig_one, Real.cos_two_mul, Real.sin_two_mul] <;> ring
  have h10 : radianConfig θ 1 ≠ radianConfig θ 0 := by
    intro h
    have hi := radianConfig_injective θ ht h
    norm_num at hi
  have h20 : radianConfig θ 2 ≠ radianConfig θ 0 := by
    intro h
    have hi := radianConfig_injective θ ht h
    norm_num at hi
  have hs : Real.sin θ ≠ 0 := by
    intro hs
    have hc : Real.cos θ ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq θ]
    apply h20
    ext j
    fin_cases j <;> simp [radianConfig, Real.cos_two_mul, Real.sin_two_mul, hs, hc] <;> norm_num
  have hc : Real.cos θ ≠ 1 := by
    intro hc
    have hs : Real.sin θ = 0 := by nlinarith [Real.sin_sq_add_cos_sq θ]
    exact h10 (by ext j; fin_cases j <;> simp [radianConfig, hc, hs])
  have hD : D ≠ 0 := by
    rw [hid]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hs) (sub_ne_zero.mpr (Ne.symm hc))
  have hu : u ∈ A.direction := by
    simpa [u, vsub_eq_sub] using AffineSubspace.vsub_mem_direction (hp 1) (hp 0)
  have hv : v ∈ A.direction := by
    simpa [v, vsub_eq_sub] using AffineSubspace.vsub_mem_direction (hp 2) (hp 0)
  apply top_unique
  intro x hx
  let w := x - radianConfig θ 0
  let α : ℝ := (w 0 * v 1 - v 0 * w 1) / D
  let β : ℝ := (u 0 * w 1 - w 0 * u 1) / D
  have hcomb : α • u + β • v = w := by
    ext j
    fin_cases j <;> simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
      dsimp [α, β] <;> field_simp [hD] <;> dsimp [D] <;> ring
  have hm : α • u + β • v ∈ A.direction :=
    A.direction.add_mem (A.direction.smul_mem α hu) (A.direction.smul_mem β hv)
  have he := AffineSubspace.vadd_mem_of_mem_direction hm (hp 0)
  simpa [hcomb, w, vadd_eq_add] using he

/-- **Theorem D, ⇒.** If `tan (θ/2)` is transcendental, the nine points at angles
`0, θ, …, 8θ` are distinct, lie on the unit circle, and are not Euclidean Ramsey. -/
theorem radian_configuration :
    Function.Injective (radianConfig θ) ∧ (∀ k, dist (radianConfig θ k) 0 = 1) ∧
      ¬ Ramsey (radianConfig θ) :=
  ⟨radianConfig_injective θ ht, radianConfig_on_circle θ, fun hR =>
    NineLinearObstruction.not_fieldCriterion_of_det_ne_zero (radianConfig θ) (by decide)
      (tensorMap θ ht) (tensorMap_injective θ ht) e (evaluationMatrix_det_ne_zero θ ht)
      (realCriterion_fieldCriterion _
        (ramsey_realCriterion _ (by decide) (radianConfig_affineSpan θ ht) hR))⟩

end CoordField

/-! ## Main theorems -/

theorem radian_not_ramsey (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    ¬ Ramsey (radianConfig θ) :=
  (radian_configuration θ ht).2.2

/-! ## The converse (`ramsey_of_algebraic`) and the iff -/

theorem algebraic_of_tan {θ : ℝ} (h : IsAlgebraic ℚ (Real.tan (θ / 2))) :
    IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ) := by
  let A := algebraicClosure ℚ ℝ
  by_cases hc : Real.cos (θ / 2) = 0
  · have h2 : θ = 2 * (θ / 2) := by ring
    rw [h2, Real.cos_two_mul, Real.sin_two_mul, hc]
    refine ⟨?_, by simpa using isAlgebraic_zero⟩
    rw [← mem_algebraicClosure_iff]
    norm_num
  · have hA : Real.tan (θ / 2) ∈ A := mem_algebraicClosure_iff.mpr h
    obtain ⟨h1, h2⟩ := half_angle hc
    have hd : 1 + Real.tan (θ / 2) ^ 2 ∈ A := A.add_mem A.one_mem (A.pow_mem hA 2)
    have hcos : Real.cos θ = (1 - Real.tan (θ / 2) ^ 2) / (1 + Real.tan (θ / 2) ^ 2) := by
      rw [eq_div_iff (one_add_tan_sq_ne θ), mul_comm, h1]
    have hsin : Real.sin θ = (2 * Real.tan (θ / 2)) / (1 + Real.tan (θ / 2) ^ 2) := by
      rw [eq_div_iff (one_add_tan_sq_ne θ), mul_comm, h2]
    rw [← mem_algebraicClosure_iff, ← mem_algebraicClosure_iff, hcos, hsin]
    exact ⟨A.div_mem (A.sub_mem A.one_mem (A.pow_mem hA 2)) hd,
      A.div_mem (A.mul_mem (A.natCast_mem 2) hA) hd⟩

theorem algebraic_multiples {θ : ℝ} (hc : IsAlgebraic ℚ (Real.cos θ))
    (hs : IsAlgebraic ℚ (Real.sin θ)) (n : ℕ) :
    IsAlgebraic ℚ (Real.cos (n * θ)) ∧ IsAlgebraic ℚ (Real.sin (n * θ)) := by
  let A := algebraicClosure ℚ ℝ
  simp only [← mem_algebraicClosure_iff] at hc hs ⊢
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Real.cos_add, Real.sin_add]
    exact ⟨A.sub_mem (A.mul_mem ih.1 hc) (A.mul_mem ih.2 hs),
      A.add_mem (A.mul_mem ih.2 hc) (A.mul_mem ih.1 hs)⟩

/-- **Theorem D.** For distinct radian points: Ramsey iff `cos θ` and `sin θ` are algebraic
(that is, iff `e^{iθ}` is algebraic). -/
theorem radian_ramsey_iff (θ : ℝ) (hinj : Function.Injective (radianConfig θ)) :
    Ramsey (radianConfig θ) ↔ IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ) := by
  constructor
  · intro hR
    by_contra hna
    exact radian_not_ramsey θ (fun htan => hna (algebraic_of_tan htan)) hR
  · rintro ⟨hc, hs⟩
    refine fieldCriterion_ramsey _ (by norm_num) (by norm_num) hinj
      (fieldCriterion_of_algebraic _ ?_ ⟨0, 1, radianConfig_on_circle θ⟩)
    intro k j
    fin_cases j
    · simpa using (algebraic_multiples hc hs k).1
    · simpa using (algebraic_multiples hc hs k).2

/-- The same, phrased with the half-angle tangent (Mathlib's junk value `tan (π/2) = 0` is
algebraic, and at `θ ≡ π` the points are `±1` with algebraic coordinates, so no case split
is needed in the statement). -/
theorem radian_ramsey_iff_tan (θ : ℝ) (hinj : Function.Injective (radianConfig θ)) :
    Ramsey (radianConfig θ) ↔ IsAlgebraic ℚ (Real.tan (θ / 2)) := by
  constructor
  · intro hR
    by_contra hna
    exact radian_not_ramsey θ hna hR
  · intro h
    exact (radian_ramsey_iff θ hinj).2 (algebraic_of_tan h)

end Radian
end EuclideanRamsey
end
end OAI
