module

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Price.Basic
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Comparison

@[expose] public noncomputable section

/-! Polynomial leading-coefficient degeneration over a commutative ring. -/

namespace OAI.MatrixMultiplication.AuxiliarySeparation
open Polynomial Foundation TensorResource
open scoped Topology Polynomial

namespace Price
variable {K : Type*} [CommRing K] (χ : Price K)
variable {U V W X Y Z : Type} [Fintype U] [Fintype V] [Fintype W]
variable [Fintype X] [Fintype Y] [Fintype Z]

private theorem coeff_pair (p q : K[X]) (h : ℕ) : (p*q).coeff h =
    ∑ i : Fin (h+1), p.coeff i * q.coeff (h-i) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Fin.sum_univ_eq_sum_range (fun i => p.coeff i * q.coeff (h-i))]

/-- Split the requested degree between all three legs. The triangular set of
copies depends only on the coefficient index, not on the local map degrees. -/
private theorem value_coeff (T : Tensor K U V W) (A : X → U → K[X]) (B : Y → V → K[X])
    (D : Z → W → K[X]) (h : ℕ) :
    χ.value (fun x y z => (Tensor.restrict A B D (fun u v w => C (T u v w)) x y z).coeff h) ≤
      (h+1:ℝ)^6 * χ.value T := by
  classical
  let I := (i : Fin (h+1)) × Fin (i.val+1)
  let _ : DecidableEq I := Classical.decEq I
  have triple (p q r : K[X]) : (p*q*r).coeff h = ∑ i : I,
      p.coeff i.2 * q.coeff (i.1-i.2) * r.coeff (h-i.1) := by
    simp [I, coeff_pair, Fintype.sum_sigma, Finset.sum_mul]
  let S := Tensor.directSum fun _ : I => T
  have hh := χ.value_restrict S (fun x (i,u) => (A x u).coeff i.2)
    (fun y (i,v) => (B y v).coeff (i.1-i.2)) (fun z (i,w) => (D z w).coeff (h-i.1))
  apply le_trans
  · convert hh using 2
    funext
    simp only [Tensor.restrict, finsetSum_coeff, coeff_mul_C]
    simp only [triple, Finset.sum_mul]
    simp [S, Tensor.directSum, Fintype.sum_prod_type, ite_and]
    tensor_sums
  · rw [χ.copies _ (fun _ => rfl)]
    apply mul_le_mul_of_nonneg_right _ (χ.nonneg T)
    have hi : Fintype.card I ≤ (h+1)^2 := by
      simpa [I, Fintype.card_sigma, sq] using Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin (h+1)) _ => (show i.val+1 ≤ h+1 from i.isLt))
    apply (χ.scalar_le_cube (d := (h+1)^2) (by positivity) (χ.raw.monotone' (((scalars (K := K)).monotone' hi).trans (diag_le _)))).trans
    push_cast; apply le_of_eq; ring

/-- The top coefficient in a fixed degree multiplies across words, provided
all entries have degree at most that bound (including the zero entries). -/
theorem value_top (T : Tensor K U V W) (H : Tensor K X Y Z) (A : X → U → K[X])
    (B : Y → V → K[X]) (D : Z → W → K[X]) (k : ℕ)
    (e : ∀ x y z, let p := Tensor.restrict A B D (fun u v w => C (T u v w)) x y z
                  p.natDegree ≤ k ∧ p.coeff k = H x y z) : χ.value H ≤ χ.value T := by
  apply polynomial_overhead (χ.nonneg _) ((C (k:ℝ)*Polynomial.X+1)^6)
  intro n
  let liftMap {I J : Type} (f : I → J → K[X]) (x : Fin n → I) (y : Fin n → J) := ∏ i, f (x i) (y i)
  have he (x y z) : (Tensor.restrict (liftMap A) (liftMap B) (liftMap D) (fun u v w => C (Tensor.power T n u v w)) x y z).coeff (n*k) = Tensor.power H n x y z := by
    have h := coeff_prod_of_natDegree_le Finset.univ _ k fun i _ => (e (x i) (y i) (z i)).1
    simp_rw [(e _ _ _).2] at h
    simpa [Tensor.restrict, liftMap, Tensor.power, Tensor.word, Fintype.prod_sum, Finset.prod_mul_distrib] using h
  simpa [he, mul_comm (n:ℝ)] using χ.value_coeff (Tensor.power T n) (liftMap A) (liftMap B) (liftMap D) (n*k)

/-- Compare the input weight sum to the output weight. Translating all
output exponents by a common bound makes the substitution polynomial. -/
theorem value_weighted (T : Tensor K U V W) (H : Tensor K X Y Z)
    (f : X → U) (g : Y → V) (l : Z → W) (a : X → ℕ) (b : Y → ℕ) (c : Z → ℕ)
    (h : ∀ x y z, (T (f x) (g y) (l z) ≠ 0 → c z ≤ a x + b y) ∧
      H x y z = if a x + b y = c z then T (f x) (g y) (l z) else 0) : χ.value H ≤ χ.value T := by
  classical
  let top {I : Type} [Fintype I] (f : I → ℕ) := Finset.univ.sup f
  have bound {I : Type} [Fintype I] (f : I → ℕ) (i) : f i ≤ top f := Finset.le_sup (Finset.mem_univ i)
  let diag {I J : Type} (u : I → J) (w : I → ℕ) (i : I) (j : J) : K[X] := if j = u i then Polynomial.X ^ w i else 0
  apply χ.value_top T H (diag f fun x => top a-a x) (diag g fun y => top b-b y) (diag l c) (top a+top b)
  intro x y z
  obtain ⟨hw,he⟩ := h x y z
  simp [Tensor.restrict, diag, ite_mul, mul_ite, ← pow_add, coeff_X_pow]
  by_cases hz : T (f x) (g y) (l z) = 0
  · simp_all
  have := bound a x; have := bound b y; specialize hw hz
  refine ⟨(natDegree_C_mul_le ..).trans ((natDegree_X_pow_le _).trans (by omega)), ?_⟩
  grind

end Price
end OAI.MatrixMultiplication.AuxiliarySeparation
