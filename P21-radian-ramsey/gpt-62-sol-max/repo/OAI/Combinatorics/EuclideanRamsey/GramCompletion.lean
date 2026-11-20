/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/{GramCompletion,SignedRows}.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Adapted to the Lean module system and simplified for this proof.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.FiniteSmoothing

@[expose] public section

namespace OAI.EuclideanRamsey

noncomputable section

open scoped TensorProduct MatrixOrder Discrete
open Matrix Finset

private lemma integerize_nonnegative {α : Type*} (f : Bool → α →₀ ℚ)
    (hf : ∀ i x, 0 ≤ f i x) : ∃ (M : ℕ) (n : Bool → α →₀ ℕ),
      0 < M ∧ ∀ i, (n i).mapRange (Nat.cast : ℕ → ℚ) (by simp) = (M:ℚ) • f i := by
  classical
  let S := (f false).support ∪ (f true).support
  let A : Matrix Bool ↥S ℚ := fun i x => f i x
  let M := A.den
  let n (i : Bool) := (f i).mapRange (fun q => ⌊(M:ℚ)*q⌋.toNat) (by simp)
  have hM := Nat.pos_of_ne_zero A.den_ne_zero
  refine ⟨M,n,hM,fun i => ?_⟩
  ext x
  simp only [n,Finsupp.mapRange_apply,Finsupp.smul_apply,smul_eq_mul]
  by_cases hx : x ∈ (f i).support
  · have hxS : x ∈ S := by cases i <;> simp [S,hx]
    have hA : (A.num i ⟨x,hxS⟩:ℚ) = (M:ℚ)*f i x := by
      simpa [A,mul_comm] using (div_eq_iff (Nat.cast_ne_zero.mpr hM.ne')).mp (A.num_div_den i ⟨x,hxS⟩)
    have hn : 0 ≤ A.num i ⟨x,hxS⟩ := by exact_mod_cast hA.ge.trans' (mul_nonneg (Nat.cast_nonneg _) (hf i x))
    rw [← hA,Int.floor_intCast,← Int.cast_natCast,Int.toNat_of_nonneg hn]
  · simp [Finsupp.notMem_support_iff.mp hx]

/-- An axis-aligned certificate with a common signed coefficient family. -/
def DiagonalCertificate {s d : ℕ} (a : Fin s → Space d) (η : ℝ) : Prop :=
  ∃ (k : Type) (_ : Fintype k) (b : k → ℝ) (c : k → ℚ),
    (∀ i, (∑ r : Fin d, ∑ j, c j • ((a i r * b j) ⊗ₜ[ℚ] (a i r * b j))) =
      ∑ j, c j • (b j ⊗ₜ[ℚ] b j)) ∧
    (∑ j, (c j:ℝ)*b j^2) = 1 ∧ (d:ℝ) * (∑ j, max (-(c j:ℝ)) 0 * b j^2) < η

open scoped BigOperators
open Discrete in
theorem diagonal_two_scale {s d : ℕ} (a : Fin s → Space d)
    (hs : 1 ≤ s) (η : ℝ) (h : DiagonalCertificate a η) :
    ∃ (σ : Type) (_ : Fintype σ) (M : ℝ) (_ : 0 < M) (f g : Fin s → EuclideanSpace ℝ σ),
      (∀ i j,‖f i-f j‖^2=M*(1+η)*‖a i-a j‖^2) ∧
      (∀ i j,‖g i-g j‖^2=M*η*‖a i-a j‖^2) ∧
      ∀ i,∃ σ : Equiv.Perm σ,∀ x,g i (σ x)=f i x := by
  classical
  obtain ⟨k,hk,b₀,c₀,he,hcov,hneg⟩ := h
  let := hk
  let κ := Option (Fin d) × k
  let c (j : κ) : ℚ := j.1.elim' (-c₀ j.2) (fun _ => c₀ j.2)
  let U₀ : Projection κ d := latticeLift fun j => j.1.elim' 0 (fun i => EuclideanSpace.single i (b₀ j.2))
  let v := latticeLift (fun j : κ => j.1.elim' (b₀ j.2) (fun _ => (0:ℝ)))
  let φ (i : Fin s) : Lattice κ →+ ℝ := v + ((dotProductBilin ℝ ℝ (a i)).comp
    (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap).toAddMonoidHom.comp U₀
  have hφ (i : Fin s) (j : κ) : φ i (axis j) = j.1.elim' 1 (a i) * b₀ j.2 := by
    rcases j with ⟨j,l⟩; cases j <;> simp [φ,v,U₀,dotProduct,Pi.single_apply,mul_ite]
  obtain ⟨ν,hcos,hν⟩ := finite_lattice_identity φ c (fun i => by
    simpa [κ,hφ,c,Fintype.sum_prod_type,Fintype.sum_option,neg_smul,sum_neg_distrib,sub_eq_add_neg,add_comm] using sub_eq_zero.mpr (he i))
  obtain ⟨b,hbm,hneg⟩ := smooth_stencil U₀ ν c hν (by
    simpa [κ,U₀,c,Fintype.sum_prod_type,Fintype.sum_option,nsmul_eq_mul] using hneg)
  let μ := ν*b
  let f (i : Bool) := (cond i μ⁻ μ⁺).coeff
  have hf (i : Bool) (γ : Lattice κ) : 0 ≤ f i γ := by
    cases i; exact posPart_nonneg μ γ; exact negPart_nonneg μ γ
  have hcoeff : f false - f true = μ.coeff := by
    exact congrArg AddMonoidAlgebra.coeff (posPart_sub_negPart μ)

  have hmom (α β : Fin d) : quadratic (gradientCoord U₀ α) (gradientCoord U₀ β) μ =
      (if α=β then 1 else 0) := by
    have hq := Ideal.mul_mem_right b _ hν
    rw [sub_mul] at hq
    have hm := quadratic_of_cube (gradientCoord U₀ α) (gradientCoord U₀ β) hq
    rw [map_sub,sub_eq_zero] at hm
    rw [hm]
    simp [quadratic_mul,stencil,hbm,Rat.smul_def]
    by_cases h : α=β <;>
      simp_all [κ,c,gradientCoord,U₀,Fintype.sum_prod_type,Fintype.sum_option,mul_ite,ite_mul,← pow_two]

  obtain ⟨M,n,hM,hn⟩ := integerize_nonnegative f hf
  let T (i : Bool) := (n i).toMultiset
  let ev (i : Fin s) (γ : Lattice κ) := v γ+∑ α,a i α*U₀ γ α
  have hmap (i : Fin s) : (T false).map (ev i) = (T true).map (ev i) := by
    simp only [T,Finsupp.toMultiset_map]
    congr 1
    apply Finsupp.mapRange_injective (Nat.cast : ℕ → ℚ) (by simp) Nat.cast_injective
    simp only [← Finsupp.mapDomain_mapRange (ev i) _ (Nat.cast : ℕ → ℚ) _ (fun x y => Nat.cast_add x y),
      hn,Finsupp.mapDomain_smul]
    congr 1
    rw [← sub_eq_zero,← Finsupp.mapDomain_sub,hcoeff]
    exact congrArg AddMonoidAlgebra.coeff (Ideal.mul_mem_right b _ (hcos i) : rowMap (φ i) μ = 0)
  let e (i : Fin s) := ((T false).mapEquiv (ev i)).trans
    ((Multiset.cast (hmap i)).trans ((T true).mapEquiv (ev i)).symm)
  let τ := T false
  let e₀ := e ⟨0,hs⟩
  let E : ∀ i : Bool, τ ≃ T i := Bool.rec (Equiv.refl _) e₀
  let W (i : Bool) : Matrix (Fin d) τ ℝ := fun j x => U₀ (E i x) j
  let U := W false
  let V := W true
  have hgram (i : Bool) (j l : Fin d) : (W i * (W i).transpose) j l =
      M * quadratic (gradientCoord U₀ j) (gradientCoord U₀ l) (cond i μ⁻ μ⁺) := by
    let w (x : Lattice κ) := U₀ x j * U₀ x l
    change (∑ x : τ, w (E i x)) = _
    rw [(E i).sum_comp (fun x : T i => w x)]
    change ((univ : Finset (T i)).val.map (fun x : T i => w x)).sum =
      M * Finsupp.linearCombination ℚ w (f i)
    rw [← Rat.cast_natCast,← Rat.smul_def,← map_smul,← hn,Multiset.map_univ,Finsupp.toMultiset_map,
      Finsupp.sum_toMultiset,Finsupp.sum_mapDomain_index,Finsupp.linearCombination_apply,Finsupp.sum_mapRange_index] <;>
      simp [Rat.smul_def,nsmul_eq_mul,add_smul]
  have hdiff : U*U.transpose-V*V.transpose=(M:ℝ) • 1 := by
    ext j l
    simp only [U,V,Matrix.sub_apply,hgram,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Bool.cond_false,Bool.cond_true]
    rw [← mul_sub,← map_sub,posPart_sub_negPart,hmom]
  have htrace : (V*V.transpose).trace < M*η := by
    simp only [V,Matrix.trace,Matrix.diag,hgram,Bool.cond_true,← Finset.mul_sum,sum_quadratic]
    exact mul_lt_mul_of_pos_left hneg (Nat.cast_pos.mpr hM)

  let vp : τ → ℝ := fun x => v x
  let vn : τ → ℝ := fun x => v (e₀ x)

  have hPSD : ((M*η) • (1 : Matrix (Fin d) (Fin d) ℝ)-V*V.transpose).PosSemidef := by
    have hA : (V*V.transpose).PosSemidef := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose V
    apply Matrix.le_iff.mp
    rw [← Algebra.algebraMap_eq_smul_one]
    apply le_algebraMap_of_spectrum_le (ha := hA.1)
    rw [hA.1.spectrum_real_eq_range_eigenvalues, hA.1.trace_eq_sum_eigenvalues] at *
    rintro _ ⟨i,rfl⟩
    exact (single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (mem_univ i)).trans htrace.le
  obtain ⟨R,hR⟩ := CStarAlgebra.nonneg_iff_eq_mul_star_self.mp hPSD.nonneg
  replace hR : R*R.transpose = (M*η:ℝ) • 1 - V*V.transpose := by
    simpa [Matrix.star_eq_conjTranspose,conjTranspose_eq_transpose_of_trivial] using hR.symm
  let F (w : τ → ℝ) (A : Matrix (Fin d) τ ℝ) (i : Fin s) : EuclideanSpace ℝ (τ ⊕ Fin d) :=
    WithLp.toLp 2 (Sum.elim w 0) + (A.fromCols R).transpose.toEuclideanLin (a i)
  have hdist (w : τ → ℝ) (A : Matrix (Fin d) τ ℝ) (q : ℝ)
      (hG : A*A.transpose+R*R.transpose=q • 1) (i j : Fin s) :
      ‖F w A i - F w A j‖^2 = q*‖a i-a j‖^2 := by
    dsimp only [F]
    rw [add_sub_add_left_eq_sub, ← map_sub, ← real_inner_self_eq_norm_sq, ← LinearMap.adjoint_inner_right,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul,
      Matrix.transpose_fromCols,Matrix.fromCols_mul_fromRows,hG,map_smul, Matrix.toLpLin_one,
      LinearMap.smul_apply, LinearMap.id_apply,real_inner_smul_right, real_inner_self_eq_norm_sq]
  refine ⟨_,inferInstance,M,Nat.cast_pos.mpr hM,F vp U,F vn V,?_,?_,?_⟩
  · apply hdist
    rw [hR,mul_add,mul_one,add_smul,← hdiff]; abel
  · apply hdist
    rw [hR]; abel
  · intro i
    refine ⟨Equiv.sumCongr ((e i).trans e₀.symm) (Equiv.refl _),?_⟩
    rintro (y|y)
    · have he : ev i (e i y) = ev i y := by
        rw [← Multiset.mapEquiv_apply (T true) (ev i),← Multiset.mapEquiv_apply (T false) (ev i)]
        simp [e]
      simpa [F,vp,vn,U,V,W,E,e₀,ev,Matrix.fromCols,Matrix.toLpLin_apply,Matrix.mulVec,dotProduct,mul_comm] using he
    · rfl

end
end OAI.EuclideanRamsey
