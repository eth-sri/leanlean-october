module
public import NearlyMinimax.ModelRegularity
@[expose] public section
noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
instance designMatrixMeasurableSpace {ι κ : Type*} : MeasurableSpace (Matrix ι κ ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → κ → ℝ))
instance designMatrixBorelSpace {ι κ : Type*} [Fintype ι] [Fintype κ] :
    BorelSpace (Matrix ι κ ℝ) := inferInstanceAs (BorelSpace (ι → κ → ℝ))
def designProjectionUpdate  [Fintype ι]
    (P : Matrix ι ι ℝ) (v : ι → ℝ) : Matrix ι ι ℝ :=
  let r := v - P *ᵥ v
  P + (projectionEnergy r)⁻¹ • vecMulVec r r
def designListProjection {ι : Type*} [Fintype ι] : List (ι → ℝ) → Matrix ι ι ℝ
  | [] => 0
  | v :: vs => designProjectionUpdate (designListProjection vs) v
theorem design_update_residual_killed  [Fintype ι]
    (P : Matrix ι ι ℝ) (hidem : P * P = P) (v : ι → ℝ) :
    P *ᵥ (v - P *ᵥ v) = 0 := by
  rw [mulVec_sub, mulVec_mulVec, hidem, sub_self]
theorem design_inverse_energy_identity (e : ℝ) : e⁻¹ * (e⁻¹ * e) = e⁻¹ := by
  by_cases he : e = 0
  · simp [he]
  · field_simp
theorem design_update_preserves_fixed  [Fintype ι]
    (P : Matrix ι ι ℝ) (hsym : Pᵀ = P) (hidem : P * P = P)
    (v q ) (hq : P *ᵥ q = q) : designProjectionUpdate P v *ᵥ q = q := by
  let r := v - P *ᵥ v
  have hd : r ⬝ᵥ q = 0 := by
    calc
      r ⬝ᵥ q = r ⬝ᵥ (P *ᵥ q) := by rw [hq]
      _ = (P *ᵥ r) ⬝ᵥ q := by rw [dotProduct_mulVec, ← mulVec_transpose, hsym]
      _ = 0 := by rw [design_update_residual_killed P hidem v, zero_dotProduct]
  change (P + (projectionEnergy r)⁻¹ • vecMulVec r r) *ᵥ q = q
  rw [add_mulVec, hq, smul_mulVec, vecMulVec_mulVec, hd, MulOpposite.op_zero,
    zero_smul, smul_zero, add_zero]
theorem design_update_range  [Fintype ι]
    (P v) (K : Submodule ℝ (ι → ℝ))
    (hP : ∀ x, P *ᵥ x ∈ K) (hv : v ∈ K) :
    ∀ x, designProjectionUpdate P v *ᵥ x ∈ K := by
  intro x
  unfold designProjectionUpdate
  rw [add_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  exact K.add_mem (hP x) (K.smul_mem _ (K.smul_mem _ (K.sub_mem hv (hP v))))
def designListSpan  [Fintype ι] (vs : List (ι → ℝ)) : Submodule ℝ (ι → ℝ) :=
  Submodule.span ℝ {v | v ∈ vs}
theorem design_list_projection_spec  [Fintype ι]
    (vs : List (ι → ℝ)) :
    (designListProjection vs)ᵀ = designListProjection vs ∧
    designListProjection vs * designListProjection vs = designListProjection vs ∧
    (∀ v ∈ vs, designListProjection vs *ᵥ v = v) ∧
    (∀ x, designListProjection vs *ᵥ x ∈ designListSpan vs) := by
  induction vs with
  | nil =>
    refine ⟨by simp [designListProjection], by simp [designListProjection], ?_, ?_⟩
    · intro v hv
      simp at hv
    · intro x
      simp [designListProjection]
  | cons v vs ih =>
    obtain ⟨hsym, hidem, hfix, hrange⟩ := ih
    have hspan : designListSpan vs ≤ designListSpan (v :: vs) := by
      apply Submodule.span_mono
      intro w hw
      exact List.mem_cons_of_mem v hw
    have hvspan : v ∈ designListSpan (v :: vs) :=
      Submodule.subset_span (List.mem_cons_self)
    have h_design_update_symmetric (P : Matrix ι ι ℝ) (hsym : Pᵀ = P) : (designProjectionUpdate P v)ᵀ = designProjectionUpdate P v := by
      simp only [designProjectionUpdate, transpose_add, transpose_smul, transpose_vecMulVec, hsym]
    have h_design_update_idempotent (P : Matrix ι ι ℝ) (hsym : Pᵀ = P) (hidem : P * P = P) : designProjectionUpdate P v * designProjectionUpdate P v = designProjectionUpdate P v := by
      let r := v - P *ᵥ v
      have hr : P *ᵥ r = 0 := design_update_residual_killed P hidem v
      have hPr : P * vecMulVec r r = 0 := by rw [mul_vecMulVec, hr, zero_vecMulVec]
      have hrP : vecMulVec r r * P = 0 := by
        rw [vecMulVec_mul, ← mulVec_transpose, hsym, hr, vecMulVec_zero]
      have hrr : vecMulVec r r * vecMulVec r r = projectionEnergy r • vecMulVec r r := by
        rw [vecMulVec_mul_vecMulVec]
        ext i j
        simp only [vecMulVec_apply, projectionEnergy, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
        ring
      change (P + (projectionEnergy r)⁻¹ • vecMulVec r r) *
        (P + (projectionEnergy r)⁻¹ • vecMulVec r r) = P + (projectionEnergy r)⁻¹ • vecMulVec r r
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hidem,
        Matrix.mul_smul, hPr, smul_zero, add_zero, Matrix.smul_mul, hrP, smul_zero,
        Matrix.smul_mul, Matrix.mul_smul, hrr, smul_smul, smul_smul, zero_add, mul_assoc, design_inverse_energy_identity]
    refine ⟨(h_design_update_symmetric _ hsym), (h_design_update_idempotent _ hsym hidem), ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with heq | hq
      · subst q
        have h_design_update_fixes_new (P : Matrix ι ι ℝ) (hsym : Pᵀ = P) (hidem : P * P = P) : designProjectionUpdate P v *ᵥ v = v := by
          let r := v - P *ᵥ v
          have horth : r ⬝ᵥ (P *ᵥ v) = 0 := by
            rw [dotProduct_mulVec, ← mulVec_transpose, hsym, design_update_residual_killed P hidem v, zero_dotProduct]
          have hv : v = P *ᵥ v + r := by dsimp [r]; abel
          have hd : r ⬝ᵥ v = projectionEnergy r := by
            conv_lhs => rw [hv]
            rw [dotProduct_add, horth, zero_add]
            rfl
          change (P + (projectionEnergy r)⁻¹ • vecMulVec r r) *ᵥ v = v
          rw [add_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, hd, smul_smul]
          by_cases he : projectionEnergy r = 0
          · have hrzero  := dotProduct_self_eq_zero.mp he
            rw [hrzero, smul_zero]
            simpa [hrzero] using hv.symm
          · rw [inv_mul_cancel₀ he, one_smul]
            exact hv.symm
        exact (h_design_update_fixes_new _ hsym hidem)
      · exact design_update_preserves_fixed _ hsym hidem v q (hfix q hq)
    · exact design_update_range _ v _ (fun x => hspan (hrange x)) hvspan
def empiricalDesignProjection  [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix ι κ ℝ) : Matrix ι ι ℝ :=
  designListProjection (Finset.univ.toList.map B.col)
theorem empirical_design_projection_spec {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (B : Matrix ι κ ℝ) :
    (empiricalDesignProjection B)ᵀ = empiricalDesignProjection B ∧
    empiricalDesignProjection B * empiricalDesignProjection B = empiricalDesignProjection B ∧
    LinearMap.range (empiricalDesignProjection B).mulVecLin = LinearMap.range B.mulVecLin := by
  obtain ⟨hsym, hidem, hfix, hrange⟩ :=
    design_list_projection_spec (Finset.univ.toList.map B.col)
  refine ⟨hsym, hidem, le_antisymm ?_ ?_⟩
  · intro v hv
    rcases hv with ⟨x, rfl⟩
    have h_empirical_design_span : designListSpan (Finset.univ.toList.map B.col) = LinearMap.range B.mulVecLin := by
      rw [Matrix.range_mulVecLin]
      unfold designListSpan
      congr 1
      ext v
      simp only [Set.mem_setOf_eq, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
        Set.mem_range]
    rw [← h_empirical_design_span]
    exact hrange x
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro v ⟨j, rfl⟩
    exact ⟨B.col j, hfix (B.col j) (List.mem_map.mpr ⟨j, by simp, rfl⟩)⟩
theorem empirical_design_residual_degrees  [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (B : Matrix ι κ ℝ) :
    (Fintype.card ι : ℝ) - Fintype.card κ ≤ (1 - empiricalDesignProjection B).trace := by
  have hs := empirical_design_projection_spec B
  have h_projection_degrees_of_freedom_bound (P : Matrix ι ι ℝ) (hidem : P * P = P) (hrange : LinearMap.range P.mulVecLin ≤ LinearMap.range B.mulVecLin) : (Fintype.card ι ) - Fintype.card κ ≤ (1 - P).trace := by
    have : (P.rank : ℝ) ≤ Fintype.card κ := by exact_mod_cast ((Submodule.finrank_mono hrange).trans B.rank_le_card_width)
    have h_projection_trace_eq_rank : P.trace = P.rank := by
      have hi : IsIdempotentElem P.mulVecLin := by
        change P.mulVecLin ∘ₗ P.mulVecLin = P.mulVecLin
        rw [← mulVecLin_mul, hidem]
      have hp := (LinearMap.isProj_range_iff_isIdempotentElem P.mulVecLin).mpr hi
      have ht := hp.trace
      rw [← Matrix.toLin'_apply', Matrix.trace_toLin'_eq] at ht
      exact ht
    rw [trace_sub, trace_one, h_projection_trace_eq_rank]
    linarith
  exact h_projection_degrees_of_freedom_bound _ hs.2.1 hs.2.2.le
theorem empirical_design_fixes_evaluation  [Fintype ι]
    [Fintype κ] [DecidableEq κ] (B : Matrix ι κ ℝ) (a : κ → ℝ) :
    empiricalDesignProjection B *ᵥ (B *ᵥ a) = B *ᵥ a := by
  have hs := empirical_design_projection_spec B
  have hq : B *ᵥ a ∈ LinearMap.range (empiricalDesignProjection B).mulVecLin := by
    rw [hs.2.2]
    exact ⟨a, rfl⟩
  rcases hq with ⟨v, hv⟩
  change empiricalDesignProjection B *ᵥ v = B *ᵥ a at hv
  rw [← hv, mulVec_mulVec, hs.2.1]
end NearlyMinimax
