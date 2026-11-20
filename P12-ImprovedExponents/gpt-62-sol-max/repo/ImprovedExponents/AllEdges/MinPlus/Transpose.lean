module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Lang.Lib.SquarePass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Lang.Frames
public import ThreeSumApsp.Spec.Sec3.Problems

@[expose] public section

/-! A matrix transpose that adds a fixed offset to every entry. -/

namespace ImprovedExponents.AllEdges

open Light ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Transpose
registers [Side, Src, Shift, Dst, Row, Col]

def cell : Stmt :=
  .store (v Dst +' (v Row *' v Side +' v Col)) (M (v Src +' (v Col *' v Side +' v Row)) +' v Shift)
end Transpose

open Transpose in
def transposeBody : Stmt := squarePass Row Col cell

/-- The transpose of the `n × n` matrix `Y` (entry `(k, j)` at `k n + j`) with `c` added: cell
`q = j n + k` holds `Y[k n + j] + c`. -/
def transposeL (n : ℕ) (c : ℤ) (Y : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q => Y.getD (q % n * n + q / n) 0 + c

@[simp] theorem length_transposeL (n : ℕ) (c : ℤ) (Y : List ℤ) :
    (transposeL n c Y).length = n * n := by
  simp [transposeL]

/-- The entry `(j, k)` of the transpose. -/
theorem transposeL_getD {n : ℕ} (c : ℤ) (Y : List ℤ) {j k : ℕ} (hj : j < n) (hk : k < n) :
    (transposeL n c Y).getD (j * n + k) 0 = Y.getD (k * n + j) 0 + c := by
  rw [transposeL, List.getD_map_range _ (Nat.mul_add_lt_mul hj hk),
    Nat.mul_add_div_of_lt hk, Nat.mul_add_mod_of_lt hk]

/-- The entries of the transpose of a matrix with entries in `[-U, U]`, with `c` added, lie in
`[c - U, c + U]`. -/
theorem mem_transposeL_bounds {n : ℕ} {Y : List ℤ} {U : ℤ} (hY : AbsLe Y U)
    (hlen : Y.length = n * n) (c : ℤ) : ∀ z ∈ transposeL n c Y, c - U ≤ z ∧ z ≤ c + U := by
  intro z hz
  simp only [transposeL, List.mem_map, List.mem_range] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  have hn : 0 < n := by lia
  have hidx : q % n * n + q / n < n * n := by
    have h1 := Nat.mod_lt q hn
    have h2 : q / n < n := by rwa [Nat.div_lt_iff_lt_mul hn]
    nlinarith
  have hmem : Y.getD (q % n * n + q / n) 0 ∈ Y := by
    simp_all
  have := abs_le.1 (hY _ hmem)
  omega

open Transpose in
/-- Transpose and shift, writing only the destination matrix. -/
theorem transpose_meets {p : ℕ} (hp : P[p]? = some transposeBody) {μ : ℕ → ℤ} {src dst n : ℕ}
    {c : ℤ} {Y : List ℤ} (hY : Seg μ src Y) (hlen : Y.length = n * n)
    (hsep : Apart src (n * n) dst (n * n))
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ src + n * n ≤ lim.space ∧ dst + n * n ≤ lim.space)
    (hfits : ∀ y ∈ Y, |y + c| ≤ lim.word) :
    Meets lim P p d [(n : ℤ), src, c, dst] μ (30 * (n * n) + 20 * n + 6) fun _ μ' =>
      Seg μ' dst (transposeL n c Y) ∧ SameOutside μ μ' dst (n * n) := by
  obtain ⟨hs, hsrc, hdst⟩ := hlim
  have hn : (n : ℤ) ≤ lim.word := le_trans (by nlinarith) hs
  let f q := (transposeL n c Y).getD q 0
  refine .of_body hp ?_
  unfold transposeBody
  refine (Ends.squarePass (r := Row) (c := Col) (dst := dst) (T := 30 * (n * n) + 20 * n + 6)
    f hn rfl ?_ (hT := by light_time [cell])).mono le_rfl ?_
  · intro i j hi hj
    have h₁ := Nat.mul_add_lt_mul hi hj
    have h₂ := Nat.mul_add_lt_mul hj hi
    have hread : wrote μ dst f (i * n + j) (src + (j * n + i)) = Y.getD (j * n + i) 0 :=
      (wrote_rest (by omega)).trans (hY.getD (hlen ▸ h₂) 0)
    have hm : Y.getD (j * n + i) 0 ∈ Y := by
      simp_all
    have hb := abs_le.1 (hfits _ hm)
    have hf := transposeL_getD c Y hi hj
    have haddr (b r s : ℕ) : ((b : ℤ) + ((r : ℤ) * n + s)).toNat = b + (r * n + s) := by
      rfl
    have hl : rectLoc (frame [n, src, c, dst]) Row Col i j = frame [n, src, c, dst, i, j] := by
      rw [rectLoc, update_frame_setLocal, update_frame_setLocal]
      rfl
    rw [hl, ← Nat.add_assoc, ← wrote_succ]
    change f (i * n + j) = _ at hf
    simp only [List.getD_eq_getElem?_getD] at hread hf hb
    light_block using h₁, h₂, cell, haddr, hread, hf
  · intro σ hσ
    rw [hσ]
    exact ⟨seg_wrote (length_transposeL n c Y) fun i hi => (List.getD_eq_getElem _ _ hi).symm,
      sameOutside_wrote le_rfl⟩

end ImprovedExponents.AllEdges
