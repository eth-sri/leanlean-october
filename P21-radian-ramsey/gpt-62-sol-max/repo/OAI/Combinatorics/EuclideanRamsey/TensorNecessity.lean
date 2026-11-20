/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/TensorNecessity.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Adapted to the Lean module system and simplified for this proof.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.Model

@[expose] public section

namespace OAI.EuclideanRamsey

noncomputable section

open scoped TensorProduct RealInnerProductSpace nonZeroDivisors
open Finset Matrix

private lemma congruent_affine {s d D : ℕ} {a : Fin s → Space d} {b : Fin s → Space D}
    (h : Congruent a b) (i₀ : Fin s) (x : Fin D) :
    ∃ w : AffineRow d, ∀ i, evalRow a i w = b i x := by
  let A : Matrix (Fin s) (Fin d) ℝ := of fun i => ⇑(a i - a i₀)
  let B : Matrix (Fin s) (Fin D) ℝ := of fun i => ⇑(b i - b i₀)
  have hG : A * A.transpose = B * B.transpose := by
    ext i j
    change ⇑(a i - a i₀) ⬝ᵥ ⇑(a j - a i₀) = ⇑(b i - b i₀) ⬝ᵥ ⇑(b j - b i₀)
    have hg : ⟪a j-a i₀,a i-a i₀⟫ = ⟪b j-b i₀,b i-b i₀⟫ := by
      simp only [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
        sub_sub_sub_cancel_right,← dist_eq_norm,h i i₀,h j i₀,h j i]
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial] using hg
  have hGB : A.toEuclideanLin.range = B.toEuclideanLin.range := by
    simpa [Matrix.toLpLin_mul,Matrix.toEuclideanLin_conjTranspose_eq_adjoint,LinearMap.range_self_comp_adjoint,
      ← Matrix.conjTranspose_eq_transpose_of_trivial] using
      congrArg (fun M : Matrix (Fin s) (Fin s) ℝ => M.toEuclideanLin.range) hG
  obtain ⟨u,hu⟩ := (hGB.ge (LinearMap.mem_range_self B.toEuclideanLin (EuclideanSpace.single x 1)))
  refine ⟨Option.elim' (b i₀ x - ∑ j, a i₀ j*u j) u,fun i => ?_⟩
  have he := congrArg (fun v : Space s => v i) hu
  simp [toLpLin_apply,mulVec,dotProduct,A,B,sub_mul,Finset.sum_sub_distrib] at he
  simp [evalRow]
  linarith

abbrev ComplexTensor := ℂ ⊗[ℚ] ℂ

abbrev complexSqRow {s : ℕ} {ι : Type*} (e : Fin s ≃ ι × ι) (u : ι → ℂ) : Fin s → ComplexTensor :=
  fun j => u (e j).1 ⊗ₜ[ℚ] u (e j).2

private lemma dot_complexSqRow {s : ℕ} {ι : Type*} [Fintype ι]
    (e : Fin s ≃ ι × ι) (u w : ι → ℂ) :
    complexSqRow e u ⬝ᵥ complexSqRow e w = (u ⬝ᵥ w) ⊗ₜ[ℚ] (u ⬝ᵥ w) := by
  let f (p : ι × ι) := (u p.1*w p.1) ⊗ₜ[ℚ] (u p.2*w p.2)
  simp only [dotProduct,complexSqRow,Algebra.TensorProduct.tmul_mul_tmul]
  rw [e.sum_comp f,Fintype.sum_prod_type,TensorProduct.sum_tmul]
  simp only [f,TensorProduct.tmul_sum]

/-- A finite colouring obstruction stated in terms of a coordinatewise statistic. -/
private lemma obstruction {s d : ℕ} (a : Fin s → Space d) (i₀ : Fin s) (f : Fin s → ℝ → ℝ)
    (h₀ : ∀ x, ∑ i, f i x = 0)
    (h₁ : ∀ {D : ℕ} {b : Fin s → Space D}, Congruent a b → ∑ i, ∑ j, f i (b i j) = -1) : ¬ Ramsey a := by
  classical
  intro h
  let C := AddCircle (2:ℝ)
  let : Fact (0 < (2:ℝ)) := ⟨by norm_num⟩
  let ε := (1:ℝ)/(2*s)
  have hs := Nat.zero_lt_of_lt i₀.isLt
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨T,_,hT,hcov⟩ := (isCompact_univ : IsCompact (Set.univ : Set (Fin s → C))).finite_cover_balls hε
  let := hT.fintype
  choose c hc using (fun v : Fin s → C => show ∃ t : T, dist v t.val < ε by simpa using hcov (Set.mem_univ v))
  let e := Fintype.equivFin T
  obtain ⟨D,_,hD⟩ := h (Fintype.card T+2) (by omega)
  let H (z : Space D) (i : Fin s) := ∑ j, f i (z j)
  let Q : ℝ →+ C := QuotientAddGroup.mk' _
  let F (z : Space D) : Fin s → C := fun i => Q (H z i)
  obtain ⟨b,hb,k,hk⟩ := hD (fun z => (e (c (F z))).castLE (by omega))
  have he (i : Fin s) : c (F (b i)) = c (F (b i₀)) := e.injective
    (Fin.castLE_injective _ ((hk i).trans (hk i₀).symm))
  have hd (i : Fin s) : ‖F (b i) i-F (b i₀) i‖ < 2*ε := by
    rw [← dist_eq_norm]
    refine (dist_le_pi_dist _ _ _).trans_lt ((dist_triangle_right _ _ (c (F (b i))).val).trans_lt ?_)
    rw [he i]
    exact (add_lt_add (he i ▸ hc _) (hc _)).trans_eq (two_mul ε).symm
  have hH : ∑ i, H (b i₀) i = 0 := by rw [Finset.sum_comm]; simp [h₀]
  have hsum : ∑ i, (F (b i) i-F (b i₀) i) = ((-1:ℝ) : C) := by
    simp only [F,← map_sub,← map_sum,Finset.sum_sub_distrib,hH,show ∑ i, H (b i) i = -1 from h₁ hb,sub_zero]
    rfl
  have hlt := (norm_sum_le _ _).trans_lt (sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨i₀⟩) fun i _ => hd i)
  rw [hsum,(AddCircle.norm_coe_eq_abs_iff 2 (by norm_num)).mpr (by norm_num)] at hlt
  simp [nsmul_eq_mul,ε] at hlt
  grind

lemma nonramsey_of_complex_matrix {s d : ℕ} (a : Fin s → Space d) {ι : Type*} [Fintype ι]
    (e : Fin s ≃ ι × ι) (r : Fin s → ι → ℂ) (q : Fin s → ℂ) (hq : ∀ i, q i ≠ 0)
    {i₀ i₁ : Fin s} (ha : a i₀ ≠ a i₁)
    (h : (Matrix.of fun i => complexSqRow e (r i)).det ∈ ComplexTensor⁰)
    (hspan : ∀ w : AffineRow d, ∃ v, ∀ i, r i ⬝ᵥ v = q i * (evalRow a i w : ℝ)) : ¬ Ramsey a := by
  classical
  let M := Matrix.of fun i => complexSqRow e (r i)
  let T := M.mulVecLin.restrictScalars ℚ
  have hT : T.ker = ⊥ := LinearMap.ker_eq_bot.mpr (Matrix.mulVec_injective_of_det_mem_nonZeroDivisors h)
  let δ := (q i₀)⁻¹ • r i₀ - (q i₁)⁻¹ • r i₁
  let l : (Fin s → ComplexTensor) →ₗ[ℚ] ℝ := (Complex.reLm.restrictScalars ℚ).comp
    ((Algebra.TensorProduct.lmul' ℚ).toLinearMap.comp
      ((dotProductBilin ℚ ℚ (complexSqRow e δ)).comp T.leftInverse))
  have hL (w : AffineRow d) : l (fun i =>
      ((q i * (evalRow a i w : ℝ)) ⊗ₜ[ℚ] (q i * (evalRow a i w : ℝ)))) =
      (evalRow a i₀ w - evalRow a i₁ w)^2 := by
    obtain ⟨v,hv⟩ := hspan w
    have h' : T (complexSqRow e v) = fun i => (r i ⬝ᵥ v) ⊗ₜ[ℚ] (r i ⬝ᵥ v) :=
      funext fun i => dot_complexSqRow e (r i) v
    simp_rw [← hv,← h']
    change (Algebra.TensorProduct.lmul' ℚ (complexSqRow e δ ⬝ᵥ (T.leftInverse (T (complexSqRow e v))))).re = _
    rw [T.leftInverse_apply_of_inj hT,dot_complexSqRow,Algebra.TensorProduct.lmul'_apply_tmul]
    simp only [δ,sub_dotProduct,smul_dotProduct,hv,smul_eq_mul,← mul_assoc,inv_mul_cancel₀ (hq _),
      one_mul,← Complex.ofReal_sub,← Complex.ofReal_mul,Complex.ofReal_re,pow_two]
  let c := dist (a i₀) (a i₁)^2
  let f (i : Fin s) (x : ℝ) := l (Pi.single i ((q i * x) ⊗ₜ[ℚ] (q i * x)))/(-c)
  have hf (w : AffineRow d) : (∑ i, f i (evalRow a i w)) =
      (evalRow a i₀ w-evalRow a i₁ w)^2/(-c) := by
    simp only [f,← Finset.sum_div,← map_sum,Finset.univ_sum_single,hL]
  apply obstruction a i₀ f
  · intro y
    simpa [evalRow] using hf (Pi.single none y)
  · intro D b hb
    choose w hw using fun x => congruent_affine hb i₀ x
    rw [Finset.sum_comm]
    have he (x : Fin D) : (∑ i, f i (b i x)) = (b i₀ x-b i₁ x)^2/(-c) := by
      simpa only [hw x] using hf (w x)
    simp only [he, ← Finset.sum_div]
    have hsum : (∑ x, (b i₀ x-b i₁ x)^2) = c := by
      dsimp [c]
      rw [← hb i₀ i₁,EuclideanSpace.dist_sq_eq]
      simp [Real.dist_eq]
    aesop
end
end OAI.EuclideanRamsey
