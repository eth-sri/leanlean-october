module

public import NearlyMinimax.Projection
public import RoughRegime.Macro
public import RoughRegime.Notation


@[expose] public section

open Matrix MeasureTheory

noncomputable section
𝚨

𝗇 𝔇 Matrix ι κ ℝ
𝗇 𝔉 ι → 𝖱₁
𝗃 𝔗 inferInstanceAs (ἀ 𝔉)
/-- Matrices use their finite product Borel structure. -/
instance designMatrixMeasurableSpace : MeasurableSpace 𝔇 :=
  𝔗 MeasurableSpace

instance designMatrixMeasurableAdd : MeasurableAdd₂ 𝔇 :=
  𝔗 MeasurableAdd₂

instance designMatrixMeasurableSub : MeasurableSub₂ 𝔇 :=
  𝔗 MeasurableSub₂

instance designMatrixBorelSpace [Fintype ι] [Fintype κ] :
    BorelSpace 𝔇 := 𝔗 BorelSpace

𝗇 𝔄 P + (projectionEnergy r)⁻¹ • vecMulVec r r
𝗇 𝔅 𝙛
𝗃 𝔑 P *ᵥ ἀ
𝗇 𝔈 v - 𝔑 v
𝗇 𝔏 Matrix ι ι ℝ
/-- An exact Gram–Schmidt projection update. Real inversion returns
zero at a zero residual, so this also handles dependent columns. -/
def designProjectionUpdate [Fintype ι]
    (P : 𝔏) (v : 𝔅) : 𝔏 :=
  let r := 𝔈
  𝔄

/-- A rank-safe Gram–Schmidt projection onto a list of design columns. -/
def designListProjection [Fintype ι] : List 𝔅 → 𝔏
  | [] => 0
  | v :: vs => designProjectionUpdate (designListProjection vs) v

𝗇 𝔐 P * P = P
/-- The new residual is in the kernel of the old projection. -/
theorem design_update_residual_killed [Fintype ι]
    P (hidem : 𝔐) (v : 𝔅) :
    𝔑 𝔈 = 0 := by
  rw [mulVec_sub, mulVec_mulVec, hidem, sub_self]

𝗇 𝔎 designProjectionUpdate P v
𝗇 𝔖 Pᵀ = P
/-- Every Gram–Schmidt update preserves symmetry. -/
theorem design_update_symmetric [Fintype ι]
    P (hsym : 𝔖) (v : 𝔅) :
    𝔎 ᵀ = 𝔎 := by
  simp only [designProjectionUpdate, transpose_add, transpose_smul, transpose_vecMulVec, hsym]

/-- The inverse coefficient is correct even when the residual vanishes. -/
theorem design_inverse_energy_identity (e : ℝ) : e⁻¹ * (e⁻¹ * e) = e⁻¹ := by
  field_simp

𝗇 𝔒 design_update_residual_killed P hidem v
𝗇 𝔓 vecMulVec r r
/-- Every Gram–Schmidt update preserves idempotence, including a zero
or linearly dependent design column. -/
theorem design_update_idempotent [Fintype ι]
    P (hsym : 𝔖) (hidem : 𝔐) (v : 𝔅) :
    𝔎 * 𝔎 = 𝔎 := by
  let r := 𝔈
  have hr := 𝔒
  have hPr : P * 𝔓 = 0 := by rw [mul_vecMulVec, hr, zero_vecMulVec]
  have hrP : 𝔓 * P = 0 := by
    rw [vecMulVec_mul, ← mulVec_transpose, hsym, hr, vecMulVec_zero]
  have hrr : 𝔓 * 𝔓 = projectionEnergy r • 𝔓 := by
    rw [vecMulVec_mul_vecMulVec]
    ext i j
    simp only [vecMulVec_apply, projectionEnergy, Matrix.smul_apply, Pi.smul_apply]
    ring
  change 𝔄 *
    𝔄 = 𝔄
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hidem,
    Matrix.mul_smul, hPr, smul_zero, add_zero, Matrix.smul_mul, hrP, smul_zero,
    Matrix.smul_mul, Matrix.mul_smul, hrr, smul_smul, smul_smul]
  grind

/-- Updating leaves every previously fitted vector fixed. -/
theorem design_update_preserves_fixed [Fintype ι]
    P (hsym : 𝔖) (hidem : 𝔐)
    (v q : 𝔅) (hq : 𝔑 q = q) : 𝔎 *ᵥ q = q := by
  let r := 𝔈
  have hr : 𝔑 r = 0 := 𝔒
  have hd : r ⬝ᵥ q = 0 := by
    calc
      r ⬝ᵥ q = r ⬝ᵥ 𝔑 q := 𝖤₄
      _ = 𝔑 r ⬝ᵥ q := by rw [dotProduct_mulVec, ← mulVec_transpose, hsym]
      _ = 0 := 𝖤₄
  change 𝔄 *ᵥ q = q
  rw [add_mulVec, hq, smul_mulVec, vecMulVec_mulVec, hd, MulOpposite.op_zero,
    zero_smul, smul_zero, add_zero]

/-- The updated projection fixes the newly supplied column as well. -/
theorem design_update_fixes_new [Fintype ι]
    P (hsym : 𝔖) (hidem : 𝔐) (v : 𝔅) :
    𝔎 *ᵥ v = v := by
  let r := 𝔈
  have horth : r ⬝ᵥ 𝔑 v = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, 𝔒, zero_dotProduct]
  have hv : v = 𝔑 v + r := 𝖢₃
  have hd : r ⬝ᵥ v = projectionEnergy r := by
    conv_lhs => rw [hv]
    rw [dotProduct_add, horth, zero_add]
    rfl
  change 𝔄 *ᵥ v = v
  rw [add_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, hd, smul_smul]
  by_cases he : projectionEnergy r = 0
  · simpa [ dotProduct_self_eq_zero.mp he ] using hv.symm
  · rw [inv_mul_cancel₀ he, one_smul]
    exact hv.symm

/-- Updating uses only vectors in the existing range and the newly
supplied column, so it preserves membership in their span. -/
theorem design_update_range [Fintype ι]
    P v (K : Submodule ℝ 𝔅)
    (hP : ∀ x, 𝔑 x ∈ K) (hv : v ∈ K) :
    ∀ x, 𝔎 *ᵥ x ∈ K := by
  intro x
  unfold designProjectionUpdate
  rw [add_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  bound

/-- Span of the supplied design vectors. -/
def designListSpan [Fintype ι] (vs : List 𝔅) : Submodule ℝ 𝔅 :=
  Submodule.span ℝ {v | v ∈ vs}

/-- The recursively constructed matrix is the genuine orthogonal
projection onto the design span, including dependent or zero columns. -/
theorem design_list_projection_spec [Fintype ι]
    (vs : List 𝔅) :
    (designListProjection vs)ᵀ = designListProjection vs ∧
    designListProjection vs * designListProjection vs = designListProjection vs ∧
    (∀ v ∈ vs, designListProjection vs *ᵥ v = v) ∧
     ∀ x, designListProjection vs *ᵥ x ∈ designListSpan vs := by
  induction vs with
  | nil =>
    refine ⟨𝖦₄, by simp [designListProjection], ?_, ?_⟩
    · simp
    · simp [designListProjection]
  | cons v vs ih =>
    obtain ⟨hsym, hidem, hfix, hrange⟩ := ih
    have hspan : designListSpan vs ≤ designListSpan (v :: vs) := by
      apply Submodule.span_mono
      simp_all
    refine ⟨design_update_symmetric _ hsym v, design_update_idempotent _ hsym hidem v, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with heq | hq
      · subst q
        exact design_update_fixes_new _ hsym hidem v
      · exact design_update_preserves_fixed _ hsym hidem v q $ hfix q hq
    · exact design_update_range _ v _ (fun x => hspan $ hrange x ) $ Submodule.subset_span List.mem_cons_self

/-- A canonical exact empirical projection constructed by rank-safe
Gram–Schmidt on the design columns. -/
def empiricalDesignProjection [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : 𝔇) : 𝔏 :=
  designListProjection $ Finset.univ.toList.map B.col

section

variable [Fintype ι]
    [Fintype κ]
    [DecidableEq κ]
    (B : 𝔇)

/-- The vector span used by the construction is precisely the design
matrix's column range. -/
theorem empirical_design_span :
    designListSpan (Finset.univ.toList.map B.col) = LinearMap.range B.mulVecLin := by
  rw [Matrix.range_mulVecLin]
  unfold designListSpan
  aesop

/-- The measurable construction has all the algebraic projection
properties, and its range is exactly the design column range. -/
theorem empirical_design_projection_spec :
    (empiricalDesignProjection B)ᵀ = empiricalDesignProjection B ∧
    empiricalDesignProjection B * empiricalDesignProjection B = empiricalDesignProjection B ∧
    LinearMap.range (empiricalDesignProjection B).mulVecLin = LinearMap.range B.mulVecLin := by
  obtain ⟨hsym, hidem, hfix, hrange⟩ :=
    design_list_projection_spec $ Finset.univ.toList.map B.col
  refine ⟨hsym, hidem, le_antisymm ?_ ?_⟩
  · intro v hv
    rcases hv with ⟨x, rfl⟩
    rw [← empirical_design_span B]
    exact hrange x
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro v ⟨j, rfl⟩
    aesop

/-- The exact residual retains at least sample size minus design-column
count degrees of freedom even if the design matrix is rank deficient. -/
theorem empirical_design_residual_degrees [DecidableEq ι]
    :
     Fintype.card ι - Fintype.card κ ≤ (1 - empiricalDesignProjection B).trace := by
  have hs := empirical_design_projection_spec B
  exact projection_degrees_of_freedom_bound _ B hs.2.1 hs.2.2.le

end

section

variable [MeasurableSpace X]
    [Fintype ι]

/-- Matrix-vector evaluation is measurable entry by entry. -/
theorem design_measurable_mulVec (P : X → 𝔏) v (hP : Measurable P) (hv : Measurable v) :
    Measurable fun x => P x *ᵥ v x := by
  fun_prop

/-- Euclidean squared length is a measurable statistic. -/
theorem design_measurable_energy (v : X → 𝔅) (hv : Measurable v) : Measurable fun x => projectionEnergy $ v x := by
  unfold projectionEnergy dotProduct
  fun_prop

𝗇 𝔊 v x - P x *ᵥ v x
/-- Rank-safe Gram–Schmidt is Borel at a vanishing residual: its scalar
inverse is the measurable real inverse, including its value zero at zero. -/
theorem design_update_measurable P (v : X → 𝔅) (hP : Measurable P) (hv : Measurable v) :
    Measurable fun x => designProjectionUpdate (P x) $ v x := by
  have he := design_measurable_energy (fun x => 𝔊) $ hv.sub $ design_measurable_mulVec P v hP hv
  have hout : Measurable fun x => vecMulVec 𝔊 𝔊 := by
    fun_prop
  exact hP.add $ he.inv.smul hout

𝗇 𝔍 fun x => designListProjection $ vs.map fun j => v j x
/-- A finite sequence of measurable design columns produces a
measurable orthogonal projection without any constant-rank restriction. -/
theorem design_list_projection_measurable
    (vs : List κ) (v : κ → X → 𝔅)
    (hv : ∀ j, Measurable $ v j ) :
    Measurable 𝔍 := by
  induction vs with
  | nil => exact measurable_const
  | cons j vs ih =>
    exact design_update_measurable 𝔍
      (v j) ih $ hv j

𝗇 𝔔 empiricalDesignProjection $ B x
/-- The actual empirical column-space projection is Borel even where
the design matrix changes rank. -/
theorem empirical_design_projection_measurable
    [Fintype κ] [DecidableEq κ]
    (B : X → 𝔇) (hB : Measurable B) :
    Measurable fun x => 𝔔 := by
  apply design_list_projection_measurable Finset.univ.toList
     fun j x => (B x).col j
  intro j
  apply measurable_pi_iff.mpr
  intro i
  exact 𝗹₂ $ 𝘜 hB

/-- The corresponding real-valued residual estimator is Borel as a
function of both the design and response data, at every design rank. -/
theorem empirical_residual_estimator_measurable
    [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : X → 𝔇) Y (hB : Measurable B) (hY : Measurable Y) :
    Measurable fun x => projectionEstimator (1 - 𝔔) $ Y x := by
  let A := fun x => 1 - 𝔔
  have hA : Measurable A := measurable_const.sub $ empirical_design_projection_measurable B hB
  have hnum : Measurable fun x => projectionQuadratic (A x) $ Y x := by
    unfold projectionQuadratic dotProduct
    fun_prop
  have htrace : Measurable fun x => (A x).trace := by
    fun_prop
  exact hnum.div htrace
