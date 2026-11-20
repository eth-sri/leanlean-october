module

public import ImprovedExponents.AllEdges.Task
public import ImprovedExponents.AllEdges.MinPlus.Transpose
public import ThreeSumApsp.Spec.Sec3.Theorem21b.NegativeTriangle

@[expose] public section

/-!
# Recovering the (min,+)-product one bit at a time

Shift both input matrices by the magnitude bound to make their entries nonnegative. When a bit
is appended to each prefix, every candidate sum changes from `s` to one of `2s, 2s+1, 2s+2`.
Consequently, from the old minimum `d`, two equality queries suffice to determine the new
minimum: test for `2d` and `2d+1`, and take `2d+2` if neither is attained. All entries are queried
simultaneously using all-edges Exact Triangle, with the second input matrix transposed.
-/

namespace ImprovedExponents.AllEdges.MinPlus

open Light ThreeSumApsp ThreeSumApsp.Spec

/-- Number of binary digits used for the nonnegative shifted inputs. -/
def levels (U : ℕ) : ℕ := Nat.log 2 (3 * U) + 1

theorem lt_power (U : ℕ) : 3 * U < 2 ^ levels U := Nat.lt_pow_succ_log_self (by decide) _

theorem power_le {U : ℕ} (hU : 1 ≤ U) : 2 ^ levels U ≤ 6 * U := by
  have := Nat.pow_log_le_self 2 (show 3 * U ≠ 0 by omega)
  rw [levels, pow_succ]
  omega

variable {x : MatInst} {μ : ℕ → ℤ} {fr : ℕ}

abbrev width (x : MatInst) := x.n * x.n

abbrev shifted (x : MatInst) : List ℤ := affL 1 x.U x.A ++ transposeL x.n x.U x.B

abbrev left (x : MatInst) (ℓ : ℕ) := (affL 1 x.U x.A).map (prefQ ℓ)
abbrev right (x : MatInst) (ℓ : ℕ) := (affL 1 x.U x.B).map (prefQ ℓ)
abbrev rightT (x : MatInst) (ℓ : ℕ) := (transposeL x.n x.U x.B).map (prefQ ℓ)

abbrev best (x : MatInst) (ℓ : ℕ) := minPlusList x.n (left x ℓ) (right x ℓ)

abbrev minimum (x : MatInst) (ℓ q : ℕ) :=
  minPlusEntry x.n (left x ℓ) (right x ℓ) (q / x.n) (q % x.n)

abbrev sumAt (x : MatInst) (ℓ q k : ℕ) :=
  entry x.n (left x ℓ) (q / x.n) k + entry x.n (right x ℓ) k (q % x.n)

/-- The outer edge tests the candidate `2d+e`. -/
abbrev question (x : MatInst) (ℓ : ℕ) (e : ℤ) := affL (-2) (-e) (best x (ℓ + 1))

noncomputable abbrev flags (x : MatInst) (ℓ : ℕ) (e : ℤ) :=
  aeFlags x.n (question x ℓ e) (rightT x ℓ) (left x ℓ)

section facts

variable (h : x.Pre μ fr)

include h in
private theorem ix {q k : ℕ} (hq : q < width x) (hk : k < x.n) :
    q / x.n * x.n + k < width x ∧ k * x.n + q % x.n < width x := by
  have hn : 0 < x.n := h.n_pos
  exact ⟨Nat.mul_add_lt_mul ((Nat.div_lt_iff_lt_mul hn).2 hq) hk,
    Nat.mul_add_lt_mul hk (Nat.mod_lt _ hn)⟩

@[simp] theorem best_length (x : MatInst) (ℓ : ℕ) : (best x ℓ).length = width x :=
  length_minPlusList ..

theorem best_getD {ℓ q : ℕ} (hq : q < width x) : (best x ℓ).getD q 0 = minimum x ℓ q :=
  List.getD_map_range _ hq 0

include h in
theorem shifted_range : ∀ z ∈ shifted x, 0 ≤ z ∧ z ≤ 2 * (x.U : ℤ) := by
  intro z hz
  rcases List.mem_append.1 hz with ha | hb
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
    have := abs_le.1 (h.leA y hy)
    simp only [one_mul]
    omega
  · have := mem_transposeL_bounds h.leB h.lenB x.U z hb
    omega

private theorem pref_entry {L : List ℤ} {U : ℤ} {q : ℕ} (hq : q < L.length) (ℓ : ℕ) :
    ((affL 1 U L).map (prefQ ℓ)).getD q 0 = prefQ ℓ (L.getD q 0 + U) := by
  simp [affL, List.getD_eq_getElem?_getD, hq]

include h in
private theorem sum_eq {q k ℓ : ℕ} (hq : q < width x) (hk : k < x.n) :
    sumAt x ℓ q k = prefQ ℓ (entry x.n x.A (q / x.n) k + x.U) +
      prefQ ℓ (entry x.n x.B k (q % x.n) + x.U) := by
  simp only [sumAt, entry, left, right]
  rw [pref_entry (h.lenA ▸ (ix h hq hk).1), pref_entry (h.lenB ▸ (ix h hq hk).2)]

private theorem min_le {ℓ q k : ℕ} (hk : k < x.n) : minimum x ℓ q ≤ sumAt x ℓ q k :=
  minPlusEntry_le _ _ _ _ _ hk

include h in
private theorem min_attained (ℓ q : ℕ) : ∃ k < x.n, minimum x ℓ q = sumAt x ℓ q k :=
  exists_minPlusEntry_eq h.n_pos ..

private theorem shift_range {L : List ℤ} {U : ℕ} (hL : AbsLe L U) (i : ℕ) :
    0 ≤ L.getD i 0 + U ∧ L.getD i 0 + U ≤ 2 * (U : ℤ) := by
  have := abs_le.1 (hL.abs_getD_le (by positivity) i)
  omega

include h in
theorem best_bounds (ℓ : ℕ) : ∀ z ∈ best x ℓ, 0 ≤ z ∧ z ≤ 4 * (x.U : ℤ) := by
  intro z hz
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hz
  obtain ⟨k, hk, he⟩ := min_attained h ℓ q
  change 0 ≤ minimum x ℓ q ∧ minimum x ℓ q ≤ _
  rw [he, sum_eq h (List.mem_range.1 hq) hk]
  obtain ⟨ha, ha'⟩ := shift_range h.leA (q / x.n * x.n + k)
  obtain ⟨hb, hb'⟩ := shift_range h.leB (k * x.n + q % x.n)
  unfold entry
  exact ⟨add_nonneg (prefQ_nonneg ha _) (prefQ_nonneg hb _),
    by linarith [prefQ_le ha ℓ, prefQ_le hb ℓ]⟩

include h in
theorem best_top : best x (levels x.U) = List.replicate (width x) 0 := by
  apply List.ext_getElem <;> simp only [best_length, List.length_replicate]
  intro q hq _
  rw [← List.getD_eq_getElem _ 0, best_getD hq, List.getElem_replicate]
  obtain ⟨k, hk, he⟩ := min_attained h (levels x.U) q
  rw [he, sum_eq h hq hk]
  have hp : (3 : ℤ) * x.U < 2 ^ levels x.U := by exact_mod_cast lt_power x.U
  have ha := shift_range h.leA (q / x.n * x.n + k)
  have hb := shift_range h.leB (k * x.n + q % x.n)
  simp only [entry, prefQ_start (L := levels x.U) ha.1 (by omega),
    prefQ_start (L := levels x.U) hb.1 (by omega), add_zero]

include h in
theorem best_zero : affL 1 (-(2 * (x.U : ℤ))) (best x 0) = minPlusList x.n x.A x.B := by
  apply List.ext_getElem <;> simp only [length_affL, length_minPlusList]
  intro q hq hq'
  rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0]
  rw [affL, List.getD_map_of_lt _ (best_length .. ▸ hq) 0 0,
    one_mul, best_getD hq, minPlusList, List.getD_map_range _ hq]
  obtain ⟨k, hk, he⟩ := exists_minPlusEntry_eq h.n_pos x.A x.B (q / x.n) (q % x.n)
  obtain ⟨j, hj, he'⟩ := min_attained h 0 q
  have lo := minPlusEntry_le _ x.A x.B (q / x.n) (q % x.n) hj
  have hi := min_le (x := x) (ℓ := 0) (q := q) hk
  rw [sum_eq h hq hk] at hi
  rw [sum_eq h hq hj] at he'
  simp only [prefQ, pow_zero, Int.ediv_one] at hi he'
  omega

include h in
private theorem flag_getD {ℓ q : ℕ} (hq : q < width x) (e : ℤ) :
    (flags x ℓ e).getD q 0 = flag (∃ k < x.n, sumAt x ℓ q k = 2 * minimum x (ℓ + 1) q + e) := by
  rw [aeFlags_getD _ _ _ hq]
  have hab : (question x ℓ e).getD q 0 = -2 * minimum x (ℓ + 1) q - e := by
    rw [← best_getD hq]
    simp [affL, List.getD_eq_getElem?_getD, hq, sub_eq_add_neg]
  rw [hab]
  apply flag_congr
  refine exists_congr fun k => and_congr_right fun hk => ?_
  have hj : q % x.n < x.n := Nat.mod_lt _ h.n_pos
  have hb : (rightT x ℓ).getD (q % x.n * x.n + k) 0 =
      prefQ ℓ (entry x.n x.B k (q % x.n) + x.U) := by
    have hi := Nat.mul_add_lt_mul hj hk
    rw [rightT, List.getD_map_of_lt _ (show _ < (transposeL x.n x.U x.B).length by simpa using hi) 0 0,
      transposeL_getD _ _ hj hk]
  rw [hb, sum_eq h hq hk]
  have hA : q / x.n * x.n + k < x.A.length := by rw [h.lenA]; exact (ix h hq hk).1
  simp only [left, pref_entry hA, entry]
  omega

include h in
private theorem min_eq {ℓ q : ℕ} {d : ℤ} (hd : d ≤ minimum x ℓ q) :
    (∃ k < x.n, sumAt x ℓ q k = d) ↔ minimum x ℓ q = d := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (min_le hk).antisymm hd
  · intro he
    obtain ⟨k, hk, hm⟩ := min_attained h ℓ q
    exact ⟨k, hk, hm.symm.trans he⟩

include h in
theorem refine_min {q ℓ : ℕ} (hq : q < width x) (hℓ : ℓ + 1 ≤ levels x.U) :
    2 * (best x (ℓ + 1)).getD q 0 +
        (1 - (flags x ℓ 0).getD q 0) * (2 - (flags x ℓ 1).getD q 0) = (best x ℓ).getD q 0 := by
  simp only [best_getD hq, flag_getD h hq, add_zero]
  have step k (hk : k < x.n) : 2 * sumAt x (ℓ + 1) q k ≤ sumAt x ℓ q k ∧
      sumAt x ℓ q k ≤ 2 * sumAt x (ℓ + 1) q k + 2 := by
    rw [sum_eq h hq hk, sum_eq h hq hk, (pref_step hℓ _).1, (pref_step hℓ _).1]
    simp only [shiftQ]
    split_ifs <;> omega
  obtain ⟨j, hj, he⟩ := min_attained h ℓ q
  obtain ⟨k, hk, he'⟩ := min_attained h (ℓ + 1) q
  have lo : 2 * minimum x (ℓ + 1) q ≤ minimum x ℓ q := by
    rw [he]
    linarith [min_le (ℓ := ℓ + 1) (q := q) hj, (step j hj).1]
  have hi := (min_le (ℓ := ℓ) (q := q) hk).trans (step k hk).2
  rw [← he'] at hi
  rw [min_eq h lo, flag]
  split_ifs with h0
  · omega
  · rw [min_eq h (by omega), flag]
    split_ifs <;> omega

end facts
end ImprovedExponents.AllEdges.MinPlus
