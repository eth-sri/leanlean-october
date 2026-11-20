module

public import ImprovedExponents.AllEdges.Pairs.Bridge

/-! # Refining a min-plus product one bit at a time

At the next binary digit every pair sum is twice its old value plus 0, 1 or 2.
Doubling an exact lower bound thus misses the new minimum by at most two. An
all-edges equality query either witnesses the lower bound or lets us increment
it. Two queries suffice; there is no separate inequality oracle or bit search.
-/

@[expose] public section

namespace ImprovedExponents.AllEdges.Scale
open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec3

abbrev area (x : MatInst) := x.n * x.n
abbrev left (x : MatInst) := affL 1 x.U x.A
abbrev right (x : MatInst) := transposeL x.n x.U x.B
abbrev data (x : MatInst) := left x ++ right x

/-- Sum at one choice of the inner vertex, using the high bits only. -/
def cost (x : MatInst) (ℓ q k : ℕ) :=
  prefQ ℓ (x.A.getD (q / x.n * x.n + k) 0 + x.U) +
  prefQ ℓ (x.B.getD (k * x.n + q % x.n) 0 + x.U)

/-- `L` is a nonnegative lower bound at every cell and misses by at most `e`. -/
structure Lower (x : MatInst) (ℓ : ℕ) (L : List ℤ) (e : ℕ) : Prop where
  len : L.length = area x
  cell : ∀ q < area x, 0 ≤ L.getD q 0 ∧ (∀ k < x.n, L.getD q 0 ≤ cost x ℓ q k) ∧
    ∃ k < x.n, cost x ℓ q k ≤ L.getD q 0 + e

variable {x : MatInst} {μ : ℕ → ℤ} {fr ℓ q e : ℕ} {L : List ℤ}

private theorem shifted {Y : List ℤ} (h : AbsLe Y x.U) (i : ℕ) :
    0 ≤ Y.getD i 0 + x.U ∧ Y.getD i 0 + x.U ≤ 2 * x.U := by
  have := abs_le.mp (AbsLe.abs_getD_le (Nat.cast_nonneg _) h i); omega

theorem data_range (h : x.Pre μ fr) : ∀ z ∈ data x, 0 ≤ z ∧ z ≤ 2 * x.U := by
  intro z hz
  rcases List.mem_append.mp hz with hy|hy
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hy
    have := abs_le.mp (h.leA _ hv); simp; omega
  · have := mem_transposeL_bounds h.leB h.lenB x.U _ hy; omega

theorem Lower.bounded (h : x.Pre μ fr) (a : Lower x ℓ L e) : AbsLe L (4 * x.U) := by
  intro z hz
  obtain ⟨q,hq,rfl⟩ := List.getElem_of_mem hz
  have ⟨h0,lo,_⟩ := a.cell q (a.len ▸ hq)
  have H := lo 0 h.n_pos
  simp only [cost] at H
  have A := shifted h.leA (q / x.n * x.n + 0)
  have B := shifted h.leB (0 * x.n + q % x.n)
  have := prefQ_le A.1 ℓ; have := prefQ_le B.1 ℓ
  rw [List.getD_eq_getElem _ _ hq] at h0 H
  rw [abs_of_nonneg h0]; omega

theorem start (h : x.Pre μ fr) : Lower x (aeLevels x.U) (affL 0 0 x.A) 0 := by
  refine ⟨by simp [area,h.lenA], fun q hq => ?_⟩
  have hb : 2 * (x.U : ℤ) < 2 ^ aeLevels x.U := by
    exact_mod_cast (show 2*x.U < 2^aeLevels x.U by have := lt_two_pow_aeLevels x.U; omega)
  have z (k : ℕ) : cost x (aeLevels x.U) q k = 0 := by
    have A := shifted h.leA (q / x.n * x.n + k); have B := shifted h.leB (k * x.n + q % x.n)
    simp only [cost,prefQ_start A.1 (A.2.trans_lt hb),prefQ_start B.1 (B.2.trans_lt hb),add_zero]
  have hqA : q < x.A.length := h.lenA.symm ▸ hq
  rw [affL,List.getD_map_of_lt _ hqA 0 0]
  simpa [z] using (show ∃ k < x.n, True from ⟨0,h.n_pos,trivial⟩)


private theorem next_digit (ℓ : ℕ) (z : ℤ) :
    2 * prefQ (ℓ+1) z ≤ prefQ ℓ z ∧ prefQ ℓ z ≤ 2 * prefQ (ℓ+1) z + 1 := by
  have H := (pref_step (le_refl (ℓ+1)) z).1
  unfold shiftQ at H; split at H <;> omega

theorem double (h : Lower x (ℓ+1) L 0) : Lower x ℓ (affL 2 0 L) 2 := by
  refine ⟨by simp [h.len], fun q hq => ?_⟩
  rw [affL,List.getD_map_of_lt _ (h.len.symm ▸ hq) 0 0]
  obtain ⟨h0,lo,k,hk,hi⟩ := h.cell q hq
  have step (c : ℕ) : 2 * cost x (ℓ+1) q c ≤ cost x ℓ q c ∧
      cost x ℓ q c ≤ 2 * cost x (ℓ+1) q c + 2 := by
    unfold cost; have := next_digit ℓ (x.A.getD (q / x.n * x.n + c) 0 + x.U)
    have := next_digit ℓ (x.B.getD (c * x.n + q % x.n) 0 + x.U); omega
  exact by grind

noncomputable def answers (x : MatInst) (ℓ : ℕ) (L : List ℤ) :=
  aeFlags x.n (affL (-1) 0 L) ((right x).map (prefQ ℓ)) ((left x).map (prefQ ℓ))

@[simp] theorem answers_length : (answers x ℓ L).length = area x := by simp [answers,area]

theorem answers_bits : ∀ z ∈ answers x ℓ L, z = 0 ∨ z = 1 := by
  intro z hz; obtain ⟨i,-,rfl⟩ := List.mem_map.mp hz; unfold flag; split <;> simp

noncomputable def advance (x : MatInst) (ℓ : ℕ) (L : List ℤ) :=
  List.zipWith (fun l f => l + 1 * (1 - f)) L (answers x ℓ L)

private theorem answer_at (h : x.Pre μ fr) (hL : L.length = area x) (hq : q < area x) :
    (answers x ℓ L).getD q 0 = flag (∃ k < x.n, cost x ℓ q k = L.getD q 0) := by
  rw [answers,aeFlags_getD _ _ _ hq,affL,List.getD_map_of_lt _ (hL.symm ▸ hq) 0 0]
  apply flag_congr; apply exists_congr; intro k; apply and_congr_right; intro hk
  have hi : q / x.n < x.n := (Nat.div_lt_iff_lt_mul h.n_pos).mpr hq
  have hj := Nat.mod_lt q h.n_pos
  have bound {i : ℕ} (hi : i < x.n) := Nat.mul_add_lt_mul hi hk
  rw [List.getD_map_of_lt _ (by simp [bound hj]) 0 0, transposeL_getD _ _ hj hk,
    List.getD_map_of_lt _ (by simpa [left,h.lenA] using bound hi) 0 0]
  rw [left,affL,List.getD_map_of_lt _ (h.lenA.symm ▸ bound hi) 0 0]
  simp only [one_mul,neg_one_mul,add_zero,cost]
  omega

theorem probe (h : x.Pre μ fr) (a : Lower x ℓ L (e+1)) : Lower x ℓ (advance x ℓ L) e := by
  refine ⟨by simp [advance,a.len], fun q hq => ?_⟩
  obtain ⟨h0,lo,k,hk,hi⟩ := a.cell q hq
  have hl := a.len.symm ▸ hq; have hf := (answers_length (x:=x) (ℓ:=ℓ) (L:=L)).symm ▸ hq
  have hread : (advance x ℓ L).getD q 0 = L.getD q 0 + 1*(1 - (answers x ℓ L).getD q 0) := by
    rw [List.getD_eq_getElem _ _ (by simpa [advance,a.len] using hq : q < (advance x ℓ L).length),
      List.getD_eq_getElem L _ hl, List.getD_eq_getElem (answers x ℓ L) _ hf]
    apply List.getElem_zipWith
  simp only [hread,answer_at h a.len hq,flag,one_mul]
  split_ifs with yes
  · obtain ⟨j,hj,he⟩ := yes; exact by grind
  · exact by grind

theorem finish (h : x.Pre μ fr) (a : Lower x 0 L 0) : affL 1 (-(2*x.U)) L = minPlusList x.n x.A x.B := by
  apply List.ext_getElem; · simp [a.len,area,length_minPlusList]
  intro q hq _
  have hq' : q < area x := by simpa [a.len] using hq
  obtain ⟨_,lo,k,hk,hi⟩ := a.cell q hq'
  obtain ⟨j,hj,hmin⟩ := exists_minPlusEntry_eq h.n_pos x.A x.B (q/x.n) (q%x.n)
  have hle := minPlusEntry_le x.n x.A x.B (q/x.n) (q%x.n) hk
  have hlo := lo j hj
  simp only [cost,prefQ,pow_zero,Int.ediv_one,entry, Nat.cast_zero, add_zero] at hi hlo hmin hle
  rw [List.getD_eq_getElem L 0 (a.len.symm ▸ hq')] at hi hlo
  simp [affL,minPlusList]; omega

end ImprovedExponents.AllEdges.Scale
