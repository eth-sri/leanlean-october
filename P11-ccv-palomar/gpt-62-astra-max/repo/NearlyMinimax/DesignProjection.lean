module

public import NearlyMinimax.Projection


@[expose] public section

open Matrix MeasureTheory
open scoped BigOperators

noncomputable section
namespace NearlyMinimax

section
variable {ι κ : Type*}

/-- Matrices use their finite product Borel structure. -/
instance designMatrixMeasurableSpace : MeasurableSpace (Matrix ι κ ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → κ → ℝ))

instance designMatrixMeasurableAdd : MeasurableAdd₂ (Matrix ι κ ℝ) :=
  inferInstanceAs (MeasurableAdd₂ (ι → κ → ℝ))

instance designMatrixMeasurableSub : MeasurableSub₂ (Matrix ι κ ℝ) :=
  inferInstanceAs (MeasurableSub₂ (ι → κ → ℝ))

end

section
variable {ι κ : Type*} [Fintype ι] {P : Matrix ι ι ℝ}

instance designMatrixBorelSpace [Fintype κ] :
    BorelSpace (Matrix ι κ ℝ) := inferInstanceAs (BorelSpace (ι → κ → ℝ))

/-- An exact Gram–Schmidt projection update.  Real inversion returns
zero at a zero residual, so this also handles dependent columns. -/
def designProjectionUpdate
    (P : Matrix ι ι ℝ) (v : ι → ℝ) : Matrix ι ι ℝ :=
  let r := v - P *ᵥ v
  P + (projectionEnergy r)⁻¹ • vecMulVec r r

/-- A rank-safe Gram–Schmidt projection onto a list of design columns. -/
def designListProjection : List (ι → ℝ) → Matrix ι ι ℝ
  | [] => 0
  | v :: vs => designProjectionUpdate (designListProjection vs) v

/-- The new residual is in the kernel of the old projection. -/
theorem design_update_residual_killed (hidem : P * P = P) (v : ι → ℝ) :
    P *ᵥ (v - P *ᵥ v) = 0 := by
  rw [mulVec_sub, mulVec_mulVec, hidem, sub_self]

/-- Every Gram–Schmidt update preserves symmetry. -/
theorem design_update_symmetric (hsym : Pᵀ = P) (v : ι → ℝ) :
    (designProjectionUpdate P v)ᵀ = designProjectionUpdate P v := by
  simp_all [designProjectionUpdate]

end

/-- The inverse coefficient is correct even when the residual vanishes. -/
theorem design_inverse_energy_identity (e : ℝ) : e⁻¹ * (e⁻¹ * e) = e⁻¹ := by
  grind

section
variable {ι : Type*} [Fintype ι] {P : Matrix ι ι ℝ} (hsym : Pᵀ = P) (hidem : P * P = P) (v q : ι → ℝ)
include hsym hidem

/-- Every Gram–Schmidt update preserves idempotence, including a zero
or linearly dependent design column. -/
theorem design_update_idempotent :
    designProjectionUpdate P v * designProjectionUpdate P v = designProjectionUpdate P v := by
  let r := v - P *ᵥ v
  have hr  := design_update_residual_killed hidem v
  have hPr : P * vecMulVec r r = 0 := by rw [mul_vecMulVec, hr, zero_vecMulVec]
  have hrP : vecMulVec r r * P = 0 := by
    rw [vecMulVec_mul, ← mulVec_transpose, hsym, hr, vecMulVec_zero]
  have hrr : vecMulVec r r * vecMulVec r r = projectionEnergy r • vecMulVec r r := by
    rw [vecMulVec_mul_vecMulVec]
    simp [projectionEnergy]
  change (P + (projectionEnergy r)⁻¹ • vecMulVec r r) *
    (P + (projectionEnergy r)⁻¹ • vecMulVec r r) = P + _
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hidem,
    Matrix.mul_smul, hPr, smul_zero, add_zero, Matrix.smul_mul, hrP, smul_zero,
    Matrix.smul_mul, Matrix.mul_smul, hrr, smul_smul, smul_smul, zero_add, mul_assoc, design_inverse_energy_identity]

/-- Updating leaves every previously fitted vector fixed. -/
theorem design_update_preserves_fixed (hq : P *ᵥ q = q) : designProjectionUpdate P v *ᵥ q = q := by
  let r := v - P *ᵥ v
  have hd : r ⬝ᵥ q = 0 := by
    calc
      _ = r ⬝ᵥ (P *ᵥ q) := by rw [hq]
      _ = _ := by rw [dotProduct_mulVec, ← mulVec_transpose, hsym]
      _ = 0 := by rw [(design_update_residual_killed hidem v), zero_dotProduct]
  change (P + (projectionEnergy r)⁻¹ • vecMulVec r r) *ᵥ q = q
  rw [add_mulVec, hq, smul_mulVec, vecMulVec_mulVec, hd, MulOpposite.op_zero,
    zero_smul, smul_zero, add_zero]

/-- The updated projection fixes the newly supplied column as well. -/
theorem design_update_fixes_new :
    designProjectionUpdate P v *ᵥ v = v := by
  let r := v - P *ᵥ v
  have horth : r ⬝ᵥ (P *ᵥ v) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, (design_update_residual_killed hidem v), zero_dotProduct]
  have hv : v = P *ᵥ v + r := by dsimp [r]; abel
  have hd : r ⬝ᵥ v = projectionEnergy r := by
    conv_lhs => rw [hv]
    rw [dotProduct_add, horth, zero_add]
    rfl
  change (P + (projectionEnergy r)⁻¹ • vecMulVec r r) *ᵥ v = v
  rw [add_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, hd, smul_smul]
  by_cases he : projectionEnergy r = 0
  · simpa [(dotProduct_self_eq_zero.mp he)] using hv.symm
  · rw [inv_mul_cancel₀ he, one_smul]
    exact hv.symm

end

/-- Updating uses only vectors in the existing range and the newly
supplied column, so it preserves membership in their span. -/
theorem design_update_range {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) {v : ι → ℝ} {K : Submodule ℝ (ι → ℝ)}
    (hP : ∀ x, P *ᵥ x ∈ K) (hv : v ∈ K) :
    ∀ x, designProjectionUpdate P v *ᵥ x ∈ K := by
  intro x
  unfold designProjectionUpdate
  rw [add_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  exact K.add_mem (hP x) (K.smul_mem _ (K.smul_mem _ (K.sub_mem hv (hP v))))

/-- Span of the supplied design vectors. -/
def designListSpan {ι : Type*} [Fintype ι] (vs : List (ι → ℝ)) : Submodule ℝ (ι → ℝ) :=
  Submodule.span ℝ {v | v ∈ vs}

/-- The recursively constructed matrix is the genuine orthogonal
projection onto the design span, including dependent or zero columns. -/
theorem design_list_projection_spec {ι : Type*} [Fintype ι]
    (vs : List (ι → ℝ)) :
    (designListProjection vs)ᵀ = designListProjection vs ∧
    designListProjection vs * designListProjection vs = designListProjection vs ∧
    (∀ v ∈ vs, designListProjection vs *ᵥ v = v) ∧
    (∀ x, designListProjection vs *ᵥ x ∈ designListSpan vs) := by
  induction vs with
  | nil =>
    simp [designListProjection]
  | cons v vs ih =>
    obtain ⟨hsym, hidem, hfix, hrange⟩ := ih
    have hspan : designListSpan vs ≤ designListSpan (v :: vs) := by
      apply Submodule.span_mono
      exact fun w => List.mem_cons_of_mem v
    refine ⟨design_update_symmetric hsym v, design_update_idempotent hsym hidem v, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with heq | hq
      · subst q
        exact design_update_fixes_new hsym hidem v
      · exact design_update_preserves_fixed hsym hidem v q (hfix q hq)
    · exact design_update_range _ (fun x => hspan (hrange x)) (Submodule.subset_span List.mem_cons_self)

/-- A canonical exact empirical projection constructed by rank-safe
Gram–Schmidt on the design columns. -/
def empiricalDesignProjection {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix ι κ ℝ) : Matrix ι ι ℝ :=
  designListProjection (Finset.univ.toList.map B.col)

/-- The vector span used by the construction is precisely the design
matrix's column range. -/
theorem empirical_design_span {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix ι κ ℝ) :
    designListSpan (Finset.univ.toList.map B.col) = LinearMap.range B.mulVecLin := by
  rw [Matrix.range_mulVecLin]
  unfold designListSpan
  congr 1
  ext v
  simp

section
variable {ι κ : Type*} [Fintype ι]

/-- The measurable construction has all the algebraic projection
properties, and its range is exactly the design column range. -/
theorem empirical_design_projection_spec [Fintype κ]
    [DecidableEq κ] (B : Matrix ι κ ℝ) :
    (empiricalDesignProjection B)ᵀ = empiricalDesignProjection B ∧
    empiricalDesignProjection B * empiricalDesignProjection B = empiricalDesignProjection B ∧
    LinearMap.range (empiricalDesignProjection B).mulVecLin = LinearMap.range B.mulVecLin := by
  obtain ⟨hsym, hidem, hfix, hrange⟩ :=
    design_list_projection_spec (Finset.univ.toList.map B.col)
  refine ⟨hsym, hidem, le_antisymm ?_ ?_⟩
  · intro v hv
    rcases hv with ⟨x, rfl⟩
    rw [← empirical_design_span B]
    exact hrange x
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro v ⟨j, rfl⟩
    exact ⟨B.col j, hfix _ (List.mem_map.mpr ⟨j, by simp, rfl⟩)⟩

/-- The exact residual retains at least sample size minus design-column
count degrees of freedom even if the design matrix is rank deficient. -/
theorem empirical_design_residual_degrees [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (B : Matrix ι κ ℝ) :
    (Fintype.card ι) - Fintype.card κ ≤ (1 - empiricalDesignProjection B).trace := by
  have hs := empirical_design_projection_spec B
  exact projection_degrees_of_freedom_bound hs.2.1 hs.2.2.le

end

variable {X ι κ : Type*} [MeasurableSpace X] [Fintype ι] (vs : List κ) {P : X → Matrix ι ι ℝ}
    {v : X → ι → ℝ}

/-- Euclidean squared length is a measurable statistic. -/
theorem design_measurable_energy (hv : Measurable v) : Measurable (fun x => projectionEnergy (v x)) := by
  apply Finset.measurable_sum
  intro i hi
  fun_prop

/-- Rank-safe Gram–Schmidt is Borel at a vanishing residual: its scalar
inverse is the measurable real inverse, including its value zero at zero. -/
theorem design_update_measurable
    (P : X → Matrix ι ι ℝ) (v : X → ι → ℝ) (hP : Measurable P) (hv : Measurable v) :
    Measurable (fun x => designProjectionUpdate (P x) (v x)) := by
  exact hP.add ((design_measurable_energy (hv.sub (by fun_prop))).inv.smul (by
    fun_prop))

/-- A finite sequence of measurable design columns produces a
measurable orthogonal projection without any constant-rank restriction. -/
theorem design_list_projection_measurable (v : κ → X → ι → ℝ)
    (hv : ∀ j, Measurable (v j)) :
    Measurable (fun x => designListProjection (vs.map (fun j => v j x))) := by
  induction vs with
  | nil => exact measurable_const
  | cons j vs ih =>
    solve_by_elim [design_update_measurable]

/-- The actual empirical column-space projection is Borel even where
the design matrix changes rank. -/
theorem empirical_design_projection_measurable [Fintype κ] [DecidableEq κ]
    {B : X → Matrix ι κ ℝ} (hB : Measurable B) :
    Measurable (fun x => empiricalDesignProjection (B x)) := by
  apply design_list_projection_measurable Finset.univ.toList
    (fun j x => (B x).col j)
  intro j
  apply measurable_pi_iff.mpr
  intro i
  measurability

/-- The corresponding real-valued residual estimator is Borel as a
function of both the design and response data, at every design rank. -/
theorem empirical_residual_estimator_measurable [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : X → Matrix ι κ ℝ) (Y : X → ι → ℝ) (hB : Measurable B) (hY : Measurable Y) :
    Measurable (fun x => projectionEstimator (1 - empiricalDesignProjection (B x)) (Y x)) := by
  let A  := fun x => 1 - empiricalDesignProjection (B x)
  have hA : Measurable A := measurable_const.sub (empirical_design_projection_measurable hB)
  have hnum : Measurable (fun x => projectionQuadratic (A x) (Y x)) := by
    apply Finset.measurable_sum
    intro i hi
    fun_prop
  have htrace : Measurable (fun x => (A x).trace) := by
    fun_prop
  exact hnum.div htrace

end NearlyMinimax
