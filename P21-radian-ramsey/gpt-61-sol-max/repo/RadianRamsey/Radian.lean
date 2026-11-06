module

public import RadianRamsey.RadianAlgebra
public import RadianRamsey.AlgebraicRamsey
public import OAI.Combinatorics.EuclideanRamsey.TensorDescent
public import OAI.Combinatorics.EuclideanRamsey.IndependentTensor

@[expose] public section

/-!
# Theorem D: the radian 9-gon is non-Ramsey when `tan (θ/2)` is transcendental

Theorem D of the spherical-ramsey note (`note/spherical-ramsey.tex`,
doi:10.5281/zenodo.23396387). The nine points `(cos kθ, sin kθ)`, `k = 0, …, 8`.

This mirrors OpenAI's `EuclideanRamseyNine` (openai/math @ fd4aeeb2, Apache-2.0, included under
`OAI/` with header-only changes for the module system, and imported): `NineLinearObstruction.not_ramsey_of_det_ne_zero` (necessity direction
through `ramsey_fieldCriterion`), `IndependentTensor.tensorEmbedding_injective`
(`ℚ(t) ⊗ ℚ(t) ↪ ℚ(T, U)`). The local
`Algebra ℚ` instances and the proof of `coefficientEquiv_tau` follow `NineField.lean`.
The determinant is in `RadianRamsey.RadianAlgebra`. OAI's definitions (`Ramsey`, `FieldCriterion`,
`augmented`, `coordinateField`) are used directly.
-/

namespace OAI.EuclideanRamsey
noncomputable section

namespace Radian

theorem map_rv {K L : Type*} [Field K] [Field L] (f : K →+* L) (z : K) (n : ℕ) :
    (fun m => f (rv z n m)) = rv (f z) n := by
  ext m
  fin_cases m <;> simp [rv,map_rot f z n]

/-- The nine points at angles `0, θ, 2θ, …, 8θ` on the unit circle. -/
@[simp] def radianConfig (θ : ℝ) (k : Fin 9) : Space 2 :=
  WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]

theorem radianConfig_on_circle (θ : ℝ) (k : Fin 9) : dist (radianConfig θ k) 0 = 1 := by
  rw [EuclideanSpace.dist_eq]
  simp

/-! ## Half-angle trigonometry -/


theorem half_angle {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) :
    (1 + Real.tan (θ / 2) ^ 2) * Real.cos θ = 1 - Real.tan (θ / 2) ^ 2 ∧
      (1 + Real.tan (θ / 2) ^ 2) * Real.sin θ = 2 * Real.tan (θ / 2) := by
  obtain ⟨x, rfl⟩ : ∃ x, θ = 2 * x := ⟨θ / 2, by ring⟩
  have hx : 2 * x / 2 = x := by ring
  rw [hx] at hc ⊢
  rw [Real.cos_two_mul', Real.sin_two_mul, Real.tan_eq_sin_div_cos]
  constructor <;> field_simp <;> rw [Real.sin_sq] <;> ring


theorem trig_rot {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) (n : ℕ) :
    (1 + Real.tan (θ / 2) ^ 2) ^ n * Real.cos (n * θ) = (rot (Real.tan (θ / 2)) n).1 ∧
      (1 + Real.tan (θ / 2) ^ 2) ^ n * Real.sin (n * θ) = (rot (Real.tan (θ / 2)) n).2 := by
  obtain ⟨h1, h2⟩ := half_angle hc
  generalize Real.tan (θ / 2) = t at *
  induction n with
  | zero => simp [rot]
  | succ n ih =>
    simp only [Nat.cast_succ, add_mul, one_mul, Real.cos_add, Real.sin_add, rot]
    grind


theorem one_add_tan_sq_ne (θ : ℝ) : 1 + Real.tan (θ / 2) ^ 2 ≠ 0 := by positivity

theorem real_coordinates {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) (k : Fin 9) (m : Fin 3) :
    realAugmented (radianConfig θ) k (finSuccEquiv 2 m) = rv (Real.tan (θ/2)) k m := by
  cases m using Fin.cases with
  | zero => rfl
  | succ m =>
    rw [finSuccEquiv_succ]
    fin_cases m <;> simp [realAugmented,rv,(trig_rot hc k).1.symm,(trig_rot hc k).2.symm,
      pow_ne_zero _ (one_add_tan_sq_ne θ)]

theorem tan_recover {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) :
    Real.tan (θ / 2) = Real.sin θ / (1 + Real.cos θ) := by
  grind [half_angle, one_add_tan_sq_ne]

theorem cos_half_ne {θ : ℝ} (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    Real.cos (θ / 2) ≠ 0 := by
  contrapose! ht
  simp [Real.tan_eq_sin_div_cos, ht, Transcendental, isAlgebraic_zero]


/-! ## The coordinate field is `ℚ(tan (θ/2))` -/

section CoordField

variable (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2)))
include ht

theorem tan_mem : Real.tan (θ / 2) ∈ coordinateField (radianConfig θ) := by
  rw [tan_recover (cos_half_ne ht)]
  let F := coordinateField (radianConfig θ)
  have hc j : radianConfig θ 1 j ∈ F :=
    IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self ((1 : Fin 9), j))
  aesop

/-- The parameter `t = tan (θ/2)` as an element of the coordinate field. -/
def tau : Coeff (radianConfig θ) := ⟨Real.tan (θ / 2), tan_mem θ ht⟩

theorem coordinateField_eq :
    coordinateField (radianConfig θ) =
      IntermediateField.adjoin ℚ (Set.range (fun _ : Unit => Real.tan (θ / 2))) := by
  let E := IntermediateField.adjoin ℚ (Set.range (fun _ : Unit => Real.tan (θ / 2)))
  have htE : Real.tan (θ / 2) ∈ E := IntermediateField.subset_adjoin ℚ _ ⟨(), rfl⟩
  let t : E := ⟨Real.tan (θ / 2),htE⟩
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨⟨k, j⟩, rfl⟩
    change radianConfig θ k j ∈ E
    change realAugmented (radianConfig θ) k (some j) ∈ E
    rw [← finSuccEquiv_succ j,real_coordinates (cos_half_ne ht)]
    exact (congrFun (map_rv E.val.toRingHom t k) j.succ) ▸ (rv t k j.succ).prop
  simp_all [tan_mem]

/-! ## Embedding `B = F ⊗ F` into `ℚ(T, U)` (as in OAI `NineField`) -/

attribute [local instance 2000] OreLocalization.instAlgebra

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
  simp only [coefficientEquiv, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
  ext <;> simp_all [tau]

def leftCoeff : Coeff (radianConfig θ) →ₐ[ℚ] IndependentTensor.JointField Unit :=
  (IndependentTensor.leftMap Unit).comp (coefficientEquiv θ ht).toAlgHom

def rightCoeff : Coeff (radianConfig θ) →ₐ[ℚ] IndependentTensor.JointField Unit :=
  (IndependentTensor.rightMap Unit).comp (coefficientEquiv θ ht).toAlgHom

/-- The polynomial inclusion `ℚ[T, U] → ℚ(T, U)`. -/
abbrev incl : Poly →+* IndependentTensor.JointField Unit :=
  algebraMap (IndependentTensor.JointPoly Unit) (IndependentTensor.JointField Unit)

/-- Any algebra map sending `τ` to `z` sends the augmented coordinates to `rv z`. -/
theorem map_augmented {K : Type*} [Field K] [Algebra ℚ K]
    (g : Coeff (radianConfig θ) →ₐ[ℚ] K) (z : K) (hz : g (tau θ ht) = z) (k : Fin 9)
    (m : Fin 3) : g (augmented (radianConfig θ) k (finSuccEquiv 2 m)) = rv z k m := by
  trans g (rv (tau θ ht) k m)
  · congr 1
    apply Subtype.ext
    have h := (real_coordinates (cos_half_ne ht) k m).trans
      (congrFun (map_rv (algebraMap (Coeff (radianConfig θ)) ℝ) (tau θ ht) k) m).symm
    convert h using 1 <;> cases finSuccEquiv 2 m <;> rfl
  · simpa [hz] using congrFun (map_rv g.toRingHom (tau θ ht) k) m

/-- The tensor square of the coordinate field embeds in `ℚ(T, U)`. -/
def tensorMap : TensorRing (radianConfig θ) →ₐ[ℚ] IndependentTensor.JointField Unit :=
  (IndependentTensor.tensorEmbedding Unit).comp
    (Algebra.TensorProduct.congr (coefficientEquiv θ ht) (coefficientEquiv θ ht)).toAlgHom

/-- Rows and columns: `Option (Fin 2) × Option (Fin 2) ≃ Fin 3 × Fin 3 ≃ Fin 9`. -/
abbrev Column := Option (Fin 2) × Option (Fin 2)

def e : Column ≃ Fin 9 :=
  (Equiv.prodCongr (finSuccEquiv 2).symm (finSuccEquiv 2).symm).trans
    (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin (3 * 3))

def evaluationMatrix : Matrix Column Column (IndependentTensor.JointField Unit) := fun i q =>
  tensorMap θ ht (augmented (radianConfig θ) (e i) q.1 ⊗ₜ[ℚ]
    augmented (radianConfig θ) (e i) q.2)

theorem evaluationMatrix_det_ne_zero :
    (evaluationMatrix θ ht).det ≠ 0 := by
  rw [← Matrix.det_reindex_self e]
  convert det_G_ne_zero incl
    (IsFractionRing.injective (IndependentTensor.JointPoly Unit)
      (IndependentTensor.JointField Unit)) using 2
  ext k j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, evaluationMatrix, Equiv.apply_symm_apply]
  change leftCoeff θ ht (augmented (radianConfig θ) k (finSuccEquiv 2 (col j).1)) *
    rightCoeff θ ht (augmented (radianConfig θ) k (finSuccEquiv 2 (col j).2)) =
      rv (incl T) k (col j).1 * rv (incl U) k (col j).2
  congr 1 <;> apply map_augmented θ ht <;> simp [leftCoeff,rightCoeff,coefficientEquiv_tau,T,U]

/-- Distinctness is a consequence: two equal points give two equal rows. -/
theorem radianConfig_injective : Function.Injective (radianConfig θ) := by
  intro i j hij
  by_contra hne
  apply evaluationMatrix_det_ne_zero θ ht
  apply Matrix.det_zero_of_row_eq (e.symm.injective.ne hne)
  funext q
  have haug : augmented (radianConfig θ) i = augmented (radianConfig θ) j := by
    ext α
    cases α <;> simp_all [augmented, coordinate]
  simp_all [evaluationMatrix]

theorem radianConfig_affineSpan : affineSpan ℝ (Set.range (radianConfig θ)) = ⊤ := by
  let f : Fin 3 ↪ Fin 9 := Fin.castLEEmb (by decide)
  have hc : EuclideanGeometry.Cospherical (Set.range (radianConfig θ)) :=
    ⟨0, 1, by rintro _ ⟨i, rfl⟩; exact radianConfig_on_circle θ i⟩
  have hi := hc.affineIndependent (Set.range_comp_subset_range f _)
    ((radianConfig_injective θ ht).comp f.injective)
  have hs := hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Space])
  exact top_unique (hs ▸ affineSpan_mono ℝ (Set.range_comp_subset_range f _))

/-- The main theorem inside the section, where the local `Algebra ℚ` instance on `ℚ(T, U)`
matches the one `tensorMap` was built with. -/
theorem radian_configuration :
    Function.Injective (radianConfig θ) ∧ (∀ k, dist (radianConfig θ k) 0 = 1) ∧
      ¬ Ramsey (radianConfig θ)  := by
  refine ⟨radianConfig_injective θ ht,radianConfig_on_circle θ,?_⟩
  intro hR
  let a := radianConfig θ
  let f := tensorMap θ ht
  classical
  let F := coordinateField a
  let b := Module.Free.chooseBasis F ℝ
  let δ := tensorCoordinates F b
  have haug i α :
      ((augmented a i α : F) : ℝ) = realAugmented a i α := by
    cases α <;> rfl
  obtain ⟨P,hP,hspatial⟩ := ramsey_realCriterion a (by decide)
    (radianConfig_affineSpan θ ht) hR
  have hv (k) : (evaluationMatrix θ ht).mulVec (fun q => f (δ (P q.1 q.2) k)) = 0 := by
    ext i
    have h := congrArg (fun t => f (δ t k)) (hP (e i))
    change f (δ (∑ α,∑ β,(realAugmented a (e i) α ⊗ₜ[ℚ] (1:ℝ))*P α β*
      ((1:ℝ) ⊗ₜ[ℚ] realAugmented a (e i) β)) k) = f (δ 0 k) at h
    simp only [map_sum, ← haug, δ, tensorCoordinates_sandwich, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul, map_mul, map_zero, Finsupp.zero_apply] at h
    change (∑ q : Column, evaluationMatrix θ ht i q * f (δ (P q.1 q.2) k)) = 0
    rw [Fintype.sum_prod_type]
    convert h using 1
    congr! 2 with α _ β
  have hzVec k := Matrix.eq_zero_of_mulVec_eq_zero
    (evaluationMatrix_det_ne_zero θ ht) (hv k)
  have hz α β : P α β = 0 := by
    apply δ.injective
    ext k
    apply ((IndependentTensor.tensorEmbedding_injective Unit).comp
      (Algebra.TensorProduct.congr (coefficientEquiv θ ht) (coefficientEquiv θ ht)).injective)
    have h := congrFun (hzVec k) (α,β)
    simpa [f,tensorMap] using h
  let j : Fin 2 := 0
  have h := congrFun (congrFun hspatial j) j
  change Algebra.TensorProduct.lmul' ℚ (P (some j) (some j)) = 1 at h
  simp [hz] at h

end CoordField

/-! ## Main theorems -/

theorem radian_not_ramsey (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    ¬ Ramsey (radianConfig θ) :=
  (radian_configuration θ ht).2.2

/-! ## The converse (`ramsey_of_algebraic`) and the iff -/

theorem algebraic_of_tan {θ : ℝ} (h : IsAlgebraic ℚ (Real.tan (θ / 2))) :
    IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ) := by
  have hs : IsAlgebraic ℚ (Real.sin θ) := by
    rw [Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq,div_eq_mul_inv]
    exact ((isAlgebraic_natCast 2).mul h).mul (isAlgebraic_one.add (h.pow 2)).inv
  refine ⟨IsAlgebraic.of_pow (by decide : 0 < 2) ?_, hs⟩
  rw [Real.cos_sq']
  exact isAlgebraic_one.sub (hs.pow 2)

theorem algebraic_multiples {θ : ℝ} (hc : IsAlgebraic ℚ (Real.cos θ))
    (hs : IsAlgebraic ℚ (Real.sin θ)) (n : ℕ) :
    IsAlgebraic ℚ (Real.cos (n * θ)) ∧ IsAlgebraic ℚ (Real.sin (n * θ)) := by
  induction n with
  | zero => simp; exact ⟨isAlgebraic_one, isAlgebraic_zero⟩
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Real.cos_add, Real.sin_add]
    exact ⟨(ih.1.mul hc).sub (ih.2.mul hs), (ih.2.mul hc).add (ih.1.mul hs)⟩

/-- **Theorem D.** For distinct radian points: Ramsey iff `cos θ` and `sin θ` are algebraic
(that is, iff `e^{iθ}` is algebraic). -/
theorem radian_ramsey_iff (θ : ℝ) (hinj : Function.Injective (radianConfig θ)) :
    Ramsey (radianConfig θ) ↔ IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ) := by
  constructor
  · intro hR
    by_contra hna
    exact radian_not_ramsey θ (fun htan => hna (algebraic_of_tan htan)) hR
  · rintro ⟨hc, hs⟩
    refine ramsey_of_algebraic (radianConfig θ) (by norm_num) (by norm_num) hinj ?_
      (radianConfig_on_circle θ)
    simp_all [algebraic_multiples]

/-- The same, phrased with the half-angle tangent (Mathlib's junk value `tan (π/2) = 0` is
algebraic, and at `θ ≡ π` the points are `±1` with algebraic coordinates, so no case split
is needed in the statement). -/
theorem radian_ramsey_iff_tan (θ : ℝ) (hinj : Function.Injective (radianConfig θ)) :
    Ramsey (radianConfig θ) ↔ IsAlgebraic ℚ (Real.tan (θ / 2)) :=
  ⟨not_imp_not.mp (radian_not_ramsey θ),
    fun h => (radian_ramsey_iff θ hinj).2 (algebraic_of_tan h)⟩

end Radian
end

end OAI.EuclideanRamsey
