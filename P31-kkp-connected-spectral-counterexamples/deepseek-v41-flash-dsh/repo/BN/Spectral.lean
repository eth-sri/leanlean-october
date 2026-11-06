module
public import Mathlib
@[expose] public section

open Matrix Finset
open scoped InnerProductSpace Matrix

namespace BN

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The adjacency eigenvalues of a finite simple graph, indexed with algebraic
multiplicity by its vertex type. -/
noncomputable def adjacencyEigenvalues
    (G : SimpleGraph V) [DecidableRel G.Adj] : V → ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues

/-- The adjacency eigenvalues in nonincreasing order. The value at `i` is the
paper's `λ_{i+1}(G)`. -/
noncomputable def adjacencyEigenvalues₀
    (G : SimpleGraph V) [DecidableRel G.Adj] : Fin (Fintype.card V) → ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀

/-- The largest adjacency eigenvalue `λ₁(G)`. -/
noncomputable def lambda1
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] : ℝ :=
  adjacencyEigenvalues₀ G ⟨0, Fintype.card_pos⟩

/-- The second-largest adjacency eigenvalue `λ₂(G)`. -/
noncomputable def lambda2
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V] : ℝ :=
  adjacencyEigenvalues₀ G ⟨1, Fintype.one_lt_card⟩
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ}

lemma mul_diagonal_mul_transpose_apply (U : Matrix n n ℝ) (d : n → ℝ) (a b : n) :
    (U * diagonal d * Uᵀ) a b = ∑ k, d k * U a k * U b k := by
  calc (U * diagonal d * Uᵀ) a b
      = ∑ k, (U * diagonal d) a k * Uᵀ k b := by rw [mul_apply]
    _ = ∑ k, (U a k * d k) * U b k := by simp [mul_diagonal, transpose_apply]
    _ = ∑ k, d k * U a k * U b k := Finset.sum_congr rfl fun _ _ => by ring

lemma mul_diagonal_mul_transpose_eq_sum_smul_vecMulVec (U : Matrix n n ℝ) (d : n → ℝ) :
    U * diagonal d * Uᵀ = ∑ k, d k • vecMulVec (U.col k) (U.col k) := by
  ext a b
  rw [mul_diagonal_mul_transpose_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [smul_eq_mul, vecMulVec_apply, col_apply, mul_assoc]

lemma isHermitian_eq_sum_smul_vecMulVec {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    A = ∑ k, hA.eigenvalues k • vecMulVec ((hA.eigenvectorUnitary : Matrix n n ℝ).col k)
        ((hA.eigenvectorUnitary : Matrix n n ℝ).col k) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp]
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  exact mul_diagonal_mul_transpose_eq_sum_smul_vecMulVec _ _

lemma vecMulVec_mulVec_real (u v x : n → ℝ) :
    vecMulVec u v *ᵥ x = (v ⬝ᵥ x) • u := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

lemma isHermitian_quadratic (hB : A.IsHermitian) (x : n → ℝ) :
    x ⬝ᵥ A *ᵥ x = ∑ k, hB.eigenvalues k * ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ x) ^ 2 := by
  have hx : A = ∑ k, hB.eigenvalues k •
        vecMulVec (hB.eigenvectorBasis k : n → ℝ) (hB.eigenvectorBasis k : n → ℝ) := by
    simpa [IsHermitian.eigenvectorUnitary_col_eq] using isHermitian_eq_sum_smul_vecMulVec hB
  conv_lhs => rw [hx]
  rw [sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mulVec, dotProduct_smul, vecMulVec_mulVec_real, dotProduct_smul]
  rw [dotProduct_comm x]
  ring

lemma eigenvectorBasis_dotProduct_self (hB : A.IsHermitian) (i : n) :
    (hB.eigenvectorBasis i : n → ℝ) ⬝ᵥ (hB.eigenvectorBasis i : n → ℝ) = 1 := by
  have hn : ‖hB.eigenvectorBasis i‖ = 1 := hB.eigenvectorBasis.orthonormal.1 i
  have hsq := EuclideanSpace.real_norm_sq_eq (hB.eigenvectorBasis i)
  simp [dotProduct, pow_two] at hsq ⊢
  simpa [hn] using hsq.symm

lemma parseval_eigenvectorBasis (hB : A.IsHermitian) (x : n → ℝ) :
    ∑ k, ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ x) ^ 2 = x ⬝ᵥ x := by
  have h := OrthonormalBasis.sum_sq_inner_right (hB.eigenvectorBasis) (WithLp.toLp 2 x)
  have hinter (k : n) :
      ⟪hB.eigenvectorBasis k, WithLp.toLp 2 x⟫_ℝ =
        (hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ x := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct_comm]
  simp only [hinter] at h
  have hnorm : ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, pow_two]
  exact h.trans hnorm

lemma eigenvalues_le_top [Nonempty n] (hB : A.IsHermitian) (i : n) :
    hB.eigenvalues i ≤ hB.eigenvalues₀ ⟨0, Fintype.card_pos⟩ := by
  have : hB.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i) ≤
      hB.eigenvalues₀ ⟨0, Fintype.card_pos⟩ := hB.eigenvalues₀_antitone (Fin.zero_le _)
  simpa [IsHermitian.eigenvalues] using this

lemma rayleigh_le [Nonempty n] (hB : A.IsHermitian) (x : n → ℝ) :
    x ⬝ᵥ A *ᵥ x ≤ hB.eigenvalues₀ ⟨0, Fintype.card_pos⟩ * (x ⬝ᵥ x) := by
  rw [isHermitian_quadratic hB, ← parseval_eigenvectorBasis hB x, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_right (eigenvalues_le_top hB k) (sq_nonneg _)

lemma bessel_two {u v x : n → ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0) :
    (u ⬝ᵥ x) ^ 2 + (v ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ x := by
  set a := u ⬝ᵥ x
  set b := v ⬝ᵥ x
  set w := a • u + b • v
  set y := x - w
  have hy : 0 ≤ y ⬝ᵥ y := by
    simp only [dotProduct]
    exact sum_nonneg fun _ _ ↦ mul_self_nonneg _
  have hxu : x ⬝ᵥ u = a := by rw [dotProduct_comm]
  have hxv : x ⬝ᵥ v = b := by rw [dotProduct_comm]
  have hxw : x ⬝ᵥ w = a ^ 2 + b ^ 2 := by
    simp [w, dotProduct_add, dotProduct_smul, hxu, hxv, pow_two]
  have hvu : v ⬝ᵥ u = 0 := by rw [dotProduct_comm, huv]
  have hww : w ⬝ᵥ w = a ^ 2 + b ^ 2 := by
    simp [w, dotProduct_add, dotProduct_smul, smul_dotProduct, hu, hv, huv, hvu]
    ring
  have hexpand : y ⬝ᵥ y = x ⬝ᵥ x - 2 * (x ⬝ᵥ w) + w ⬝ᵥ w := by
    simp [y, dotProduct_sub, dotProduct_comm w x]
    ring
  linarith

lemma sum_antitone_le_two {m : ℕ} (hm : 2 ≤ m) (L q : Fin m → ℝ) (hL : Antitone L)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (hsum : ∑ i, q i = 2) :
    ∑ i, L i * q i ≤ L ⟨0, by omega⟩ + L ⟨1, by omega⟩ := by
  set a : Fin m := ⟨0, by omega⟩ with ha
  set b : Fin m := ⟨1, by omega⟩ with hb
  have hkey : ∀ i : Fin m, L i * q i ≤ L b * q i + (if i = a then (L a - L b) * q i else 0) := by
    intro i
    by_cases hi : i = a
    · subst hi
      simp only [ite_true]
      linarith
    · have h1i : b ≤ i := by
        rw [Fin.le_iff_val_le_val, hb]
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero fun h => hi (Fin.ext (by simpa [ha] using h)))
      simp only [if_neg hi, add_zero]
      exact mul_le_mul_of_nonneg_right (hL h1i) (hq0 i)
  calc ∑ i, L i * q i
      ≤ ∑ i, (L b * q i + (if i = a then (L a - L b) * q i else 0)) :=
        Finset.sum_le_sum fun i _ => hkey i
    _ = L b * ∑ i, q i + (L a - L b) * q a := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_ite_eq']
        simp
    _ = L b * 2 + (L a - L b) * q a := by rw [hsum]
    _ ≤ L a + L b := by
        have hba : L b ≤ L a := hL (by simp [a, b, Fin.le_iff_val_le_val])
        nlinarith [hq1 a, hba]

lemma sum_pair_le [Nontrivial n] (hB : A.IsHermitian) {u v : n → ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0) :
    u ⬝ᵥ A *ᵥ u + v ⬝ᵥ A *ᵥ v ≤
      hB.eigenvalues₀ ⟨0, Fintype.card_pos⟩ + hB.eigenvalues₀ ⟨1, Fintype.one_lt_card⟩ := by
  rw [isHermitian_quadratic hB, isHermitian_quadratic hB, ← Finset.sum_add_distrib]
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) with he
  set q : Fin (Fintype.card n) → ℝ :=
    fun i => ((hB.eigenvectorBasis (e i) : n → ℝ) ⬝ᵥ u) ^ 2 +
      ((hB.eigenvectorBasis (e i) : n → ℝ) ⬝ᵥ v) ^ 2 with hq
  have hreindex : ∑ k : n, (hB.eigenvalues k *
      ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ u) ^ 2 +
      hB.eigenvalues k * ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ v) ^ 2) =
      ∑ i, hB.eigenvalues₀ i * q i := by
    rw [← Fintype.sum_equiv e]
    intro i
    simp only [hq, he, IsHermitian.eigenvalues, Equiv.symm_apply_apply]
    ring
  rw [hreindex]
  have hq0 : ∀ i, 0 ≤ q i := fun i => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hq1 : ∀ i, q i ≤ 1 := by
    intro i
    have h1 : (hB.eigenvectorBasis (e i) : n → ℝ) ⬝ᵥ (hB.eigenvectorBasis (e i) : n → ℝ) = 1 :=
      eigenvectorBasis_dotProduct_self hB _
    have h2 := bessel_two hu hv huv (x := (hB.eigenvectorBasis (e i) : n → ℝ))
    simpa [q, dotProduct_comm, h1] using h2
  have hsumq : ∑ i, q i = 2 := by
    simp only [hq, Finset.sum_add_distrib]
    rw [Fintype.sum_equiv e (fun i => ((hB.eigenvectorBasis (e i) : n → ℝ) ⬝ᵥ u) ^ 2)
      (fun k => ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ u) ^ 2) (fun i => rfl), 
      Fintype.sum_equiv e (fun i => ((hB.eigenvectorBasis (e i) : n → ℝ) ⬝ᵥ v) ^ 2)
      (fun k => ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ v) ^ 2) (fun i => rfl),
      parseval_eigenvectorBasis hB u, parseval_eigenvectorBasis hB v, hu, hv]
    norm_num
  exact sum_antitone_le_two (Nat.succ_le_of_lt Fintype.one_lt_card) _ _ hB.eigenvalues₀_antitone hq0 hq1 hsumq

/-- Two-by-two algebraic core: if `a, b ≥ 0`, `c ^ 2 ≤ a * b`, `a ≤ L1`, `a + b ≤ L1 + L2` and
`c ^ 2 ≤ (L1 - a) * (L1 - b)`, then `a² + b² + 2c² ≤ L1² + L2²`. -/
lemma sq_add_sq_add_two_mul_sq_le {a b c L1 L2 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpsd : c ^ 2 ≤ a * b) (hL : a ≤ L1) (htr : a + b ≤ L1 + L2)
    (hdet : c ^ 2 ≤ (L1 - a) * (L1 - b)) :
    a ^ 2 + b ^ 2 + 2 * c ^ 2 ≤ L1 ^ 2 + L2 ^ 2 := by
  have h1 : 0 ≤ L1 - a := by linarith
  by_cases hb2 : b ≤ L1
  · have h2 : 0 ≤ L1 - b := by linarith
    by_cases h : a + b ≤ L1
    · nlinarith [mul_nonneg ha hb]
    · rw [not_le] at h
      have h3 : 0 ≤ a + b - L1 := by linarith
      have h4 : a + b - L1 ≤ L2 := by linarith
      nlinarith [mul_nonneg h1 h2, mul_nonneg h3 h3, mul_nonneg h3 (le_trans h3 h4)]
  · rw [not_le] at hb2
    have hnb : L1 - b < 0 := by linarith
    rcases lt_or_eq_of_le hL with hlt | heq
    · have hneg : (L1 - a) * (L1 - b) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) hnb
      nlinarith
    · have hc0 : c = 0 := by nlinarith
      have hL2b : b ≤ L2 := by linarith
      have hL2 : 0 ≤ L2 := le_trans hb hL2b
      nlinarith [mul_nonneg hb (by linarith : (0:ℝ) ≤ L2 - b), mul_nonneg hL2 hL2]

end BN
