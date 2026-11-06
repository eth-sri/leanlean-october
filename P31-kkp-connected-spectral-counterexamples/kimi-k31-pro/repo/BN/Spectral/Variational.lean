/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

module
public import Mathlib.Analysis.Matrix.Spectrum
public import BN.Basic.Inner
public import Mathlib.Analysis.InnerProductSpace.PiL2
@[expose] public section

/-!
# Variational comparison for rank-at-most-two PSD matrices

The two-dimensional variational bound on a pair of orthonormal Rayleigh
quotients, the rank-two spectral writing of a PSD matrix, and
`lem:variational` of `docs/sol.tex`.
-/

namespace BN

open Matrix Finset
open scoped InnerProductSpace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {B : Matrix n n ℝ}

noncomputable section

noncomputable def lambdaMax (hB : B.IsHermitian) [Nonempty n] : ℝ :=
  hB.eigenvalues₀ ⟨0, Fintype.card_pos⟩

noncomputable def lambdaSecond (hB : B.IsHermitian) [Nontrivial n] : ℝ :=
  hB.eigenvalues₀ ⟨1, Fintype.one_lt_card⟩

/-! ### Coordinate form of the eigenbasis -/

lemma eigenvectorBasis_dotProduct_self (hB : B.IsHermitian) (i : n) :
    (hB.eigenvectorBasis i : n → ℝ) ⬝ᵥ (hB.eigenvectorBasis i : n → ℝ) = 1 := by
  have hn : ‖hB.eigenvectorBasis i‖ = 1 := hB.eigenvectorBasis.orthonormal.1 i
  have hsq := EuclideanSpace.real_norm_sq_eq (hB.eigenvectorBasis i)
  simp [dotProduct, pow_two] at hsq ⊢
  simpa [hn] using hsq.symm

lemma eigenvectorBasis_dotProduct (hB : B.IsHermitian) {i j : n} (hij : i ≠ j) :
    (hB.eigenvectorBasis i : n → ℝ) ⬝ᵥ (hB.eigenvectorBasis j : n → ℝ) = 0 := by
  have h0 : ⟪hB.eigenvectorBasis i, hB.eigenvectorBasis j⟫_ℝ = 0 :=
    hB.eigenvectorBasis.orthonormal.inner_eq_zero hij
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h0
  simpa [dotProduct_comm] using h0

lemma parseval_eigenvectorBasis (hB : B.IsHermitian) (x : n → ℝ) :
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

lemma vecMulVec_mulVec_real (u v x : n → ℝ) :
    vecMulVec u v *ᵥ x = (v ⬝ᵥ x) • u := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

lemma isHermitian_quadratic (hB : B.IsHermitian) (x : n → ℝ) :
    x ⬝ᵥ B *ᵥ x =
      ∑ k, hB.eigenvalues k *
        ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ x) ^ 2 := by
  have hx :
      B = ∑ k, hB.eigenvalues k •
        vecMulVec (hB.eigenvectorBasis k : n → ℝ)
          (hB.eigenvectorBasis k : n → ℝ) := by
    simpa [IsHermitian.eigenvectorUnitary_col_eq] using
      isHermitian_eq_sum_smul_vecMulVec hB
  conv_lhs => rw [hx]
  rw [sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [smul_mulVec, dotProduct_smul, vecMulVec_mulVec_real, dotProduct_smul]
  rw [dotProduct_comm x]
  ring

lemma rayleigh_le_lambdaMax [Nonempty n] (hB : B.IsHermitian) {u : n → ℝ}
    (hu : u ⬝ᵥ u = 1) :
    u ⬝ᵥ B *ᵥ u ≤ lambdaMax hB := by
  rw [isHermitian_quadratic hB]
  calc
    _ ≤ ∑ k, lambdaMax hB * ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ u) ^ 2 :=
      Finset.sum_le_sum fun k _ ↦
        mul_le_mul_of_nonneg_right (hB.eigenvalues₀_antitone (Fin.zero_le _)) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, parseval_eigenvectorBasis, hu, mul_one]

/-! ### CG02: rank-two writing -/

lemma exists_finTwo_writing {X : Matrix (Fin 2) (Fin 2) ℝ} (hX : X.PosSemidef) :
    ∃ (u v : Fin 2 → ℝ) (α β : ℝ),
      0 ≤ β ∧ β ≤ α ∧ u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ u ⬝ᵥ v = 0 ∧
        X = α • vecMulVec u u + β • vecMulVec v v := by
  let hA := hX.isHermitian
  let u : Fin 2 → ℝ := hA.eigenvectorBasis 0
  let v : Fin 2 → ℝ := hA.eigenvectorBasis 1
  let α := hA.eigenvalues 0
  let β := hA.eigenvalues 1
  have hu : u ⬝ᵥ u = 1 := eigenvectorBasis_dotProduct_self hA 0
  have hv : v ⬝ᵥ v = 1 := eigenvectorBasis_dotProduct_self hA 1
  have huv : u ⬝ᵥ v = 0 := eigenvectorBasis_dotProduct hA (by decide)
  have hx : X = α • vecMulVec u u + β • vecMulVec v v := by
    simpa [u, v, α, β, Fin.sum_univ_two, IsHermitian.eigenvectorUnitary_col_eq] using
      isHermitian_eq_sum_smul_vecMulVec hA
  have hα : 0 ≤ α := hX.eigenvalues_nonneg 0
  have hβ : 0 ≤ β := hX.eigenvalues_nonneg 1
  rcases le_total β α with hβα | hαβ
  · exact ⟨u, v, α, β, hβ, hβα, hu, hv, huv, hx⟩
  · refine ⟨v, u, β, α, hα, hαβ, hv, hu, ?_, ?_⟩
    · rwa [dotProduct_comm]
    · rw [hx, add_comm]

/-! ### CG01: two-dimensional variational comparison -/

lemma bessel_two {u v x : n → ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0) :
    (u ⬝ᵥ x) ^ 2 + (v ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ x := by
  let a := u ⬝ᵥ x
  let b := v ⬝ᵥ x
  have hy : 0 ≤ (x - a • u - b • v) ⬝ᵥ (x - a • u - b • v) := by
    simp only [dotProduct]
    exact sum_nonneg fun _ _ => mul_self_nonneg _
  simp [a, b, dotProduct_sub, dotProduct_smul, hu, hv, huv, dotProduct_comm] at hy
  nlinarith

lemma sum_antitone_le_two_largest {m : ℕ} (hm : 2 ≤ m)
    (lam q : Fin m → ℝ) (hlam : Antitone lam)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (hsum : ∑ i, q i = 2) :
    ∑ i, lam i * q i ≤ lam ⟨0, by omega⟩ + lam ⟨1, by omega⟩ := by
  set a : Fin m := ⟨0, by omega⟩
  set b : Fin m := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b]
  have hdecomp := (sum_add_sum_compl ({a, b} : Finset (Fin m)) (fun i ↦ lam i * q i)).symm
  rw [hdecomp, sum_pair hab]
  have hlamb (i : Fin m) (hi : i ∈ ({a, b} : Finset (Fin m))ᶜ) : lam i ≤ lam b := by
    have hib : i ≠ a ∧ i ≠ b := by
      simpa [mem_compl, mem_insert, mem_singleton] using hi
    have : b ≤ i := Fin.le_iff_val_le_val.mpr (by
      change 1 ≤ i.val
      have : i.val ≠ 0 ∧ i.val ≠ 1 :=
        ⟨fun h ↦ hib.1 (Fin.ext h), fun h ↦ hib.2 (Fin.ext h)⟩
      omega)
    exact hlam this
  have hrest : ∑ i ∈ ({a, b} : Finset (Fin m))ᶜ, q i = 2 - q a - q b := by
    have := (sum_add_sum_compl ({a, b} : Finset (Fin m)) q).symm
    simp only [sum_pair hab] at this
    linarith
  have hlamab : lam b ≤ lam a :=
    hlam (show a ≤ b from Fin.le_iff_val_le_val.mpr (by simp [a, b]))
  calc
    lam a * q a + lam b * q b + ∑ i ∈ ({a, b} : Finset (Fin m))ᶜ, lam i * q i ≤
        lam a * q a + lam b * q b + lam b * ∑ i ∈ ({a, b} : Finset (Fin m))ᶜ, q i := by
      apply add_le_add_right
      rw [mul_sum]
      exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hlamb i hi) (hq0 i)
    _ = 2 * lam b + (lam a - lam b) * q a := by rw [hrest]; ring
    _ ≤ lam a + lam b := by
      have := mul_le_mul_of_nonneg_left (hq1 a) (sub_nonneg.mpr hlamab)
      linarith

lemma orthonormal_pair_le_lambdaMax_add_lambdaSecond [Nontrivial n]
    (hB : B.IsHermitian) {u v : n → ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0) :
    u ⬝ᵥ B *ᵥ u + v ⬝ᵥ B *ᵥ v ≤ lambdaMax hB + lambdaSecond hB := by
  rw [isHermitian_quadratic hB, isHermitian_quadratic hB, ← sum_add_distrib]
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  let q : Fin (Fintype.card n) → ℝ := fun i =>
    ((hB.eigenvectorBasis (e i) : n → ℝ) ⬝ᵥ u) ^ 2 +
      ((hB.eigenvectorBasis (e i) : n → ℝ) ⬝ᵥ v) ^ 2
  have hreindex :
      (∑ k, (hB.eigenvalues k * ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ u) ^ 2 +
        hB.eigenvalues k * ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ v) ^ 2)) =
      ∑ i, hB.eigenvalues₀ i * q i := by
    rw [← e.sum_comp (fun k => hB.eigenvalues k *
      ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ u) ^ 2 +
        hB.eigenvalues k * ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ v) ^ 2)]
    simp [q, IsHermitian.eigenvalues, e, mul_add]
  have hsumq : ∑ i, q i = 2 := by
    simp only [q]
    rw [e.sum_comp (fun k => ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ u) ^ 2 +
      ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ v) ^ 2)]
    simp [sum_add_distrib, parseval_eigenvectorBasis, hu, hv]
    norm_num
  have hq0 (i : Fin (Fintype.card n)) : 0 ≤ q i :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hq1 (i : Fin (Fintype.card n)) : q i ≤ 1 := by
    have := bessel_two hu hv huv (x := (hB.eigenvectorBasis (e i) : n → ℝ))
    simpa [q, eigenvectorBasis_dotProduct_self hB, dotProduct_comm] using this
  rw [hreindex]
  have htwo : 2 ≤ Fintype.card n := Nat.succ_le_of_lt Fintype.one_lt_card
  have hbound := sum_antitone_le_two_largest htwo hB.eigenvalues₀ q
    hB.eigenvalues₀_antitone hq0 hq1 hsumq
  simpa [lambdaMax, lambdaSecond] using hbound

/-! ### Inner products against rank-one terms -/

lemma inner_vecMulVec (C : Matrix n n ℝ) (u : n → ℝ) :
    inner C (vecMulVec u u) = u ⬝ᵥ C *ᵥ u := by
  simp [inner_eq_sum, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum,
    mul_left_comm]

lemma inner_vecMulVec_vecMulVec (u v : n → ℝ) :
    inner (vecMulVec u u) (vecMulVec v v) = (u ⬝ᵥ v) ^ 2 := by
  rw [inner_vecMulVec, vecMulVec_mulVec_real, dotProduct_smul, smul_eq_mul,
    mul_comm, dotProduct_comm, pow_two]

lemma inner_self_rankTwo {u v : n → ℝ} (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (huv : u ⬝ᵥ v = 0) (α β : ℝ) :
    inner (α • vecMulVec u u + β • vecMulVec v v)
        (α • vecMulVec u u + β • vecMulVec v v) =
      α ^ 2 + β ^ 2 := by
  have hvu : v ⬝ᵥ u = 0 := by rw [dotProduct_comm, huv]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  simp [inner_vecMulVec_vecMulVec, hu, hv, huv, hvu]
  ring

end

end BN
