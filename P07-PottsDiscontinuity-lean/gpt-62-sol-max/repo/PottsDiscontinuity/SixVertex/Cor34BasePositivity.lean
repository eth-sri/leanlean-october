module

public import PottsDiscontinuity.Bethe.DiscreteBase
public import PottsDiscontinuity.BetheAnsatz.GapGeometry
public import PottsDiscontinuity.SixVertex.Cor34BetheWave
public import PottsDiscontinuity.SixVertex.InfinitySupport
public import PottsDiscontinuity.SixVertex.Rotate

/-! The base Bethe wave is a centered Vandermonde in the compressed particle positions.
Its phase is independent of the configuration and its real weight is positive on the
support of the infinite-anisotropy transfer matrix. -/

@[expose] public section

open Finset Complex Matrix

namespace PottsDiscontinuity.SixVertex

open BetheAnsatz

private theorem baseWave_det {N n : ℕ} (x : Fin n → ℤ) :
    cor34_normalizedCoordinate 0 (Bethe.discreteBaseSolution N n) x =
      (of (fun i j : Fin n => z (Bethe.discreteBaseSolution N n i) ^
        (x j + (n - 1 - j.val : ℕ)))).det := by
  classical
  rw [Matrix.det_apply']
  apply sum_congr rfl
  intro σ _
  rw [cor34_normalizedAmplitude_zero, mul_assoc, planeWave, ← prod_mul_distrib]
  congr 1
  apply prod_congr rfl
  intro j _
  simp only [prod_const, Fin.card_Ioi, Matrix.of_apply, zpow_add₀ (z_ne_zero _), zpow_natCast]
  simp [z, ← Complex.exp_int_mul, mul_comm, mul_left_comm]

private theorem exp_diff (u v : ℝ) :
    z (2 * v) - z (2 * u) = (z u * z v) * (2 * I * (Real.sin (v - u) : ℂ)) := by
  have hs : 2 * I * (Real.sin (v - u) : ℂ) =
      Complex.exp (I * ((v - u : ℝ) : ℂ)) - Complex.exp (-(I * ((v - u : ℝ) : ℂ))) := by
    rw [Complex.ofReal_sin, Complex.sin]
    simp only [mul_comm _ I]
    ring_nf
    simp
  rw [hs, mul_sub]
  simp only [z, ← Complex.exp_add, ofReal_mul, ofReal_ofNat, ofReal_sub]
  ring

private theorem centered_vandermonde {n : ℕ} (u : Fin n → ℝ) :
    (of fun i j : Fin n => z ((2 * j.val + 1 - n) * u i)).det =
      (2 * I) ^ cor34_pairCount n *
        (↑(∏ i : Fin n, ∏ j ∈ Ioi i, Real.sin (u j - u i)) : ℂ) := by
  classical
  have hm : (of fun i j : Fin n => z ((2 * j.val + 1 - n) * u i)) =
      of (fun i j => (z (u i) ^ (n - 1))⁻¹ * vandermonde (fun i => z (2 * u i)) i j) := by
    ext i j
    simp only [of_apply, vandermonde_apply, z, ← Complex.exp_nat_mul, ← Complex.exp_neg,
      ← Complex.exp_add]
    congr 1
    have hn : 1 ≤ n := by have := i.isLt; omega
    push_cast [Nat.cast_sub hn]
    ring
  rw [hm, det_mul_column, det_vandermonde]
  simp_rw [exp_diff]
  simp_rw [prod_mul_distrib, prod_const, prod_pow_eq_pow_sum, ← Complex.ofReal_prod]
  have hp : (∏ i : Fin n, ∏ j ∈ Ioi i, z (u i) * z (u j)) =
      ∏ i : Fin n, z (u i) ^ (n - 1) := by
    rw [prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun _ i => z (u i))]
    simp [card_compl]
  simp_rw [prod_mul_distrib, prod_const] at hp
  rw [hp, ← mul_pow (2 : ℂ) I, prod_inv_distrib, ← mul_assoc, inv_mul_cancel₀, one_mul]
  · rfl
  · exact prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (z_ne_zero _)

private noncomputable def compressedPosition {N n : ℕ} (x : State N n) (j : Fin n) : ℤ :=
  positions x j - (j.val : ℤ)

private theorem compressed_gaps {N n : ℕ} (x : State N n) {a b : Fin n} (hab : a < b) :
    let d := compressedPosition x b - compressedPosition x a
    (0 ≤ d ∧ d ≤ (N - n : ℕ)) ∧
      (NoConsecutiveUp x.1 → 0 < d ∧ d < (N - n : ℕ)) := by
  have hn : 0 < n := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let s := compressedPosition x
  let f : Fin (m + 1) := 0
  let l := Fin.last m
  have hpositions (j : Fin (m + 1)) : 0 ≤ positions x j ∧ positions x j < N := by
    have := (x.1.orderEmbOfFin x.2 j).isLt
    dsimp [positions]; omega
  have step (j : Fin m) : positions x j.castSucc < positions x j.succ :=
    positions_strictMono x (by simp)
  have hm : Monotone s := Fin.monotone_iff_le_succ.mpr fun j => by
    have := step j
    dsimp [s, compressedPosition]
    try simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_succ]
    omega
  have hfa := hm (Fin.zero_le a)
  have hbl := hm (Fin.le_last b)
  have hab' := hm hab.le
  have hl := (hpositions l).2
  have hf := (hpositions f).1
  have hnN : m + 1 ≤ N := by simpa [x.2] using Finset.card_le_univ x.1
  change (0 ≤ s b - s a ∧ s b - s a ≤ (N - (m + 1) : ℕ)) ∧ _
  have span : s b - s a ≤ positions x l - positions x f - m := by
    change s f ≤ s a at hfa
    change s b ≤ s l at hbl
    simp only [s, compressedPosition, f, l, Fin.val_zero, Nat.cast_zero, sub_zero, Fin.val_last] at hfa hbl
    change s b - s a ≤ positions x (Fin.last m) - positions x 0 - m
    dsimp [s, compressedPosition]
    omega
  refine ⟨⟨by omega, by omega⟩, fun hx => ?_⟩
  have hs : StrictMono s := Fin.strictMono_iff_lt_succ.mpr fun j => by
    have hv := step j
    let u := x.1.orderEmbOfFin x.2 j.castSucc
    let v := x.1.orderEmbOfFin x.2 j.succ
    have hne : positions x j.succ ≠ positions x j.castSucc + 1 := by
      intro he
      change (v.val : ℤ) = u.val + 1 at he
      have hnxt : nxt u = v := Fin.ext (by rw [nxt_val_mod, Nat.mod_eq_of_lt (by omega)]; omega)
      exact hx u (Finset.orderEmbOfFin_mem _ _ _) (hnxt ▸ Finset.orderEmbOfFin_mem _ _ _)
    dsimp [s, compressedPosition]
    try simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_succ]
    omega
  refine ⟨sub_pos.mpr (hs hab), ?_⟩
  have hnoseam : ¬ (positions x f = 0 ∧ positions x l = (N : ℤ) - 1) := by
    rintro ⟨hf0, hlN⟩
    let u := x.1.orderEmbOfFin x.2 l
    let v := x.1.orderEmbOfFin x.2 f
    change (u.val : ℤ) = N - 1 at hlN
    change (v.val : ℤ) = 0 at hf0
    have hnxt : nxt u = v := by
      apply Fin.ext
      rw [nxt_val_mod, show u.val + 1 = N by omega, Nat.mod_self]
      omega
    exact hx u (Finset.orderEmbOfFin_mem _ _ _) (hnxt ▸ Finset.orderEmbOfFin_mem _ _ _)
  change s b - s a < (N - (m + 1) : ℕ)
  omega

/-- The base wave has a common phase, with positive weight on all independent states. -/
theorem cor34_base_phase {N n : ℕ} (hnN : n < N) (x : State N n) :
    let W := (((2 * I : ℂ) ^ cor34_pairCount n)⁻¹) *
      cor34_normalizedCoordinate 0 (Bethe.discreteBaseSolution N n) (positions x)
    0 ≤ W.re ∧ (NoConsecutiveUp x.1 → 0 < W.re) := by
  classical
  let u : Fin n → ℝ := fun i => Real.pi * (positions x i + (n - 1 - i.val : ℕ)) / (N - n : ℕ)
  dsimp only
  rw [baseWave_det, ← det_transpose]
  have he : (of (fun i j : Fin n => z (Bethe.discreteBaseSolution N n i) ^
      (positions x j + (n - 1 - j.val : ℕ))))ᵀ =
      of (fun i j : Fin n => z ((2 * j.val + 1 - n) * u i)) := by
    ext i j
    simp only [transpose_apply, of_apply, u, z, ← Complex.exp_int_mul,
      Bethe.discreteBaseSolution, Bethe.discreteBetheIndex]
    congr 1
    push_cast
    ring
  rw [he, centered_vandermonde, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ (mul_ne_zero (by norm_num) I_ne_zero)), one_mul, ofReal_re]
  have hm : 0 < ((N - n : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hnN
  have hu (i j : Fin n) (hij : i < j) :
      let v : ℝ := ((compressedPosition x j - compressedPosition x i : ℤ) : ℝ)
      u j - u i = Real.pi * v / (N - n : ℕ) := by
    dsimp [u, compressedPosition]
    push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (show i.val ≤ n - 1 by omega),
      Nat.cast_sub (show j.val ≤ n - 1 by omega)]
    ring
  have bounds (i j : Fin n) (hij : j ∈ Ioi i) := compressed_gaps x (mem_Ioi.mp hij)
  constructor
  · refine prod_nonneg fun i _ => prod_nonneg fun j hj => ?_
    rw [hu i j (mem_Ioi.mp hj)]
    obtain ⟨⟨ha, hb⟩, _⟩ := bounds i j hj
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact div_nonneg (mul_nonneg Real.pi_pos.le (by exact_mod_cast ha)) hm.le
    · rw [div_le_iff₀ hm]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hb) Real.pi_pos.le
  · intro h
    refine prod_pos fun i _ => prod_pos fun j hj => ?_
    rw [hu i j (mem_Ioi.mp hj)]
    obtain ⟨ha, hb⟩ := (bounds i j hj).2 h
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact div_pos (mul_pos Real.pi_pos (by exact_mod_cast ha)) hm
    · rw [div_lt_iff₀ hm]
      exact mul_lt_mul_of_pos_left (by exact_mod_cast hb) Real.pi_pos

end PottsDiscontinuity.SixVertex
