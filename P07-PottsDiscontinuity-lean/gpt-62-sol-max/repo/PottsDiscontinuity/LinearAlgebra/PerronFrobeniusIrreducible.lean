module

public import Mathlib
public import PottsDiscontinuity.LinearAlgebra.SymmetricSpectral

/-! The positive Perron eigenvector and simplicity of the Perron root for real symmetric
irreducible nonnegative matrices. -/

@[expose] public section

open Matrix

namespace PottsDiscontinuity.PerronFrobenius

variable {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ}

theorem dotProduct_self_nonneg' (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem abs_dotProduct_self (v : ι → ℝ) : (fun i => |v i|) ⬝ᵥ (fun i => |v i|) = v ⬝ᵥ v :=
  Finset.sum_congr rfl fun i _ => abs_mul_abs_self (v i)

/-- For a nonnegative matrix, `|vᵀ A v| ≤ |v|ᵀ A |v|`. -/
theorem abs_dotProduct_mulVec_le (hnn : ∀ i j, 0 ≤ A i j) (v : ι → ℝ) :
    |v ⬝ᵥ (A *ᵥ v)| ≤ (fun i => |v i|) ⬝ᵥ (A *ᵥ fun i => |v i|) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  simp [abs_of_nonneg (hnn i j)]

variable [DecidableEq ι] [Nonempty ι]

/-- If `A v = μ v` with `|μ| ≥ ρ` (`ρ` the largest eigenvalue) then `|v|` is an eigenvector of `A`
for `ρ`. -/
theorem abs_mulVec_eq (hA : A.IsHermitian) (hnn : ∀ i j, 0 ≤ A i j) {μ : ℝ} {v : ι → ℝ}
    (hv : A *ᵥ v = μ • v) (hμ : pfRoot A ≤ |μ|) :
    A *ᵥ (fun i => |v i|) = pfRoot A • (fun i => |v i|) := by
  apply mulVec_eq_pfRoot_smul_of_dotProduct_mulVec_eq hA
  have hvv := dotProduct_self_nonneg' v
  have h1 : |v ⬝ᵥ (A *ᵥ v)| = |μ| * (v ⬝ᵥ v) := by
    simp_all
  have h2 := abs_dotProduct_mulVec_le hnn v
  have h3 := dotProduct_mulVec_le_pfRoot hA (fun i => |v i|)
  rw [abs_dotProduct_self] at h3 ⊢
  apply le_antisymm h3
  nlinarith

/-- All eigenvalues of a symmetric nonnegative matrix are bounded in absolute value by the
largest one. -/
theorem abs_eigenvalues_le_pfRoot (hA : A.IsHermitian) (hnn : ∀ i j, 0 ≤ A i j) (i : ι) :
    |hA.eigenvalues i| ≤ pfRoot A := by
  have hb := mulVec_eigvec hA i
  have hbb : eigvec hA i ⬝ᵥ eigvec hA i = 1 := by simpa using eigvec_dot hA i i
  have h1 : |eigvec hA i ⬝ᵥ (A *ᵥ eigvec hA i)| = |hA.eigenvalues i| := by
    simp_all
  have h2 := abs_dotProduct_mulVec_le hnn (eigvec hA i)
  have h3 := dotProduct_mulVec_le_pfRoot hA (fun j => |eigvec hA i j|)
  rw [abs_dotProduct_self, hbb] at h3
  linarith

/-- A nonnegative symmetric matrix with a positive entry has positive largest eigenvalue. -/
theorem pfRoot_pos (hA : A.IsHermitian) (hnn : ∀ i j, 0 ≤ A i j) (hne : ∃ i j, 0 < A i j) :
    0 < pfRoot A := by
  obtain ⟨i, j, hij⟩ := hne
  have h := dotProduct_mulVec_le_pfRoot hA (fun _ : ι => (1 : ℝ))
  have hs : 0 < (fun _ : ι => (1 : ℝ)) ⬝ᵥ (A *ᵥ fun _ : ι => (1 : ℝ)) := by
    simp only [dotProduct, mulVec, one_mul, mul_one]
    refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)
      ⟨i, Finset.mem_univ i, Finset.sum_pos' (fun j _ => hnn i j) ⟨j, Finset.mem_univ j, hij⟩⟩
  have hcard : (0 : ℝ) < (fun _ : ι => (1 : ℝ)) ⬝ᵥ (fun _ : ι => (1 : ℝ)) := by
    simp [dotProduct, Fintype.card_pos]
  nlinarith

omit [Nonempty ι] in
theorem pow_mulVec_eq_of_mulVec_eq {c : ℝ} {w : ι → ℝ} (h : A *ᵥ w = c • w) (M : ℕ) :
    (A ^ M) *ᵥ w = c ^ M • w := by
  induction M with
  | zero => simp
  | succ M ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, h, smul_smul, ← pow_succ]

omit [Nonempty ι] in
theorem rootMultiplicity_charpoly_eq_card (hA : A.IsHermitian) (a : ℝ) :
    A.charpoly.rootMultiplicity a =
      (Finset.univ.filter fun i => hA.eigenvalues i = a).card := by
  rw [← Polynomial.count_roots, hA.roots_charpoly_eq_eigenvalues]
  simp only [Function.comp_def, Multiset.count_map, RCLike.ofReal_real_eq_id, id_eq]
  rw [Finset.card_def, Finset.filter_val]
  simp [eq_comm]

/-! ### Irreducible matrices -/

section Irreducible

variable (hnn : ∀ i j, 0 ≤ A i j) (hirr : ∀ i j, ∃ k > 0, 0 < (A ^ k) i j)

include hnn hirr in
theorem exists_pos_entry_of_irreducible : ∃ i j, 0 < A i j := by
  by_contra h
  push Not at h
  obtain ⟨k, hk, hpos⟩ := hirr (Classical.arbitrary ι) (Classical.arbitrary ι)
  have hA0 : A = 0 := by
    ext i j
    exact le_antisymm (h i j) (hnn i j)
  rw [hA0, zero_pow hk.ne'] at hpos
  simp at hpos

omit [Nonempty ι] in
include hnn hirr in
/-- A nonnegative eigenvector (for a positive eigenvalue) of an irreducible matrix is strictly
positive. -/
theorem pos_of_nonneg_eigenvector {ρ : ℝ} (hρ : 0 < ρ) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hwne : w ≠ 0) (hw : A *ᵥ w = ρ • w) : ∀ i, 0 < w i := by
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hwne (funext hcon)
  have hjpos : 0 < w j := lt_of_le_of_ne (hw0 j) (Ne.symm hj)
  intro i
  obtain ⟨k, hk, hkpos⟩ := hirr i j
  have h1 := congrFun (pow_mulVec_eq_of_mulVec_eq hw k) i
  have h2 : (A ^ k) i j * w j ≤ ((A ^ k) *ᵥ w) i := by
    exact Finset.single_le_sum (f := fun l => (A ^ k) i l * w l)
      (fun l _ => mul_nonneg (pow_apply_nonneg hnn k i l) (hw0 l)) (Finset.mem_univ j)
  have h3 : 0 < ρ ^ k * w i := by
    have : 0 < (A ^ k) i j * w j := mul_pos hkpos hjpos
    have h4 := lt_of_lt_of_le this h2
    rw [h1] at h4
    simpa using h4
  by_contra hcon
  push Not at hcon
  nlinarith [pow_pos hρ k]

variable (hA : A.IsHermitian)

include hA hnn hirr in
theorem pfRoot_pos_of_irreducible : 0 < pfRoot A :=
  pfRoot_pos hA hnn (exists_pos_entry_of_irreducible hnn hirr)

private theorem eigvec_ne_zero (i : ι) : eigvec hA i ≠ 0 := by
  intro h
  simpa [h] using eigvec_dot hA i i

include hA hnn hirr in
private theorem abs_eigenvector_pos {w : ι → ℝ}
    (hw : A *ᵥ w = pfRoot A • w) (hne : w ≠ 0) : ∀ i, 0 < |w i| := by
  have hρ := pfRoot_pos_of_irreducible hnn hirr hA
  refine pos_of_nonneg_eigenvector hnn hirr hρ (fun _ => abs_nonneg _) ?_
    (abs_mulVec_eq hA hnn hw (le_abs_self _))
  intro h
  exact hne (funext fun i => abs_eq_zero.mp (congrFun h i))

include hA hnn hirr in
/-- The absolute value of a nonzero Perron eigenvector is strictly positive. -/
theorem exists_pos_eigenvector :
    ∃ v : ι → ℝ, (∀ i, 0 < v i) ∧ A *ᵥ v = pfRoot A • v := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_pfRoot hA
  have hw : A *ᵥ eigvec hA i = pfRoot A • eigvec hA i := by rw [mulVec_eigvec, hi]
  exact ⟨_, abs_eigenvector_pos hnn hirr hA hw (eigvec_ne_zero hA i),
    abs_mulVec_eq hA hnn hw (le_abs_self _)⟩

include hA hnn hirr in
private theorem eigenspace_pfRoot_eq {u w : ι → ℝ} (hu : u ≠ 0)
    (hv : A *ᵥ u = pfRoot A • u) (hw : A *ᵥ w = pfRoot A • w) : ∃ c : ℝ, w = c • u := by
  let i : ι := Classical.arbitrary ι
  let t := w i / u i
  have hi := abs_pos.mp (abs_eigenvector_pos hnn hirr hA hv hu i)
  have hz : A *ᵥ (w - t • u) = pfRoot A • (w - t • u) := by
    rw [mulVec_sub, mulVec_smul, hw, hv, smul_sub, smul_comm]
  refine ⟨t, ?_⟩
  by_contra h
  have := abs_eigenvector_pos hnn hirr hA hz (sub_ne_zero.mpr h) i
  simp [t, hi] at this

include hA hnn hirr in
private theorem existsUnique_eigenvalues_eq_pfRoot : ∃! i, hA.eigenvalues i = pfRoot A := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_pfRoot hA
  refine ⟨i, hi, fun j hj => ?_⟩
  by_contra hne
  have hbi : A *ᵥ eigvec hA i = pfRoot A • eigvec hA i := by rw [mulVec_eigvec, hi]
  have hbj : A *ᵥ eigvec hA j = pfRoot A • eigvec hA j := by rw [mulVec_eigvec, hj]
  obtain ⟨c, hc⟩ := eigenspace_pfRoot_eq hnn hirr hA (eigvec_ne_zero hA j) hbj hbi
  have hii := eigvec_dot hA i i
  have hjj := eigvec_dot hA j j
  have hij := eigvec_dot hA i j
  simp_all

include hA hnn hirr in
/-- The characteristic polynomial has `pfRoot A` as a simple root. -/
theorem rootMultiplicity_charpoly_pfRoot :
    A.charpoly.rootMultiplicity (pfRoot A) = 1 := by
  rw [rootMultiplicity_charpoly_eq_card hA, Finset.card_eq_one]
  obtain ⟨i, hi, huniq⟩ := existsUnique_eigenvalues_eq_pfRoot hnn hirr hA
  exact ⟨i, by grind [Finset.mem_filter]⟩

end Irreducible
end PottsDiscontinuity.PerronFrobenius
