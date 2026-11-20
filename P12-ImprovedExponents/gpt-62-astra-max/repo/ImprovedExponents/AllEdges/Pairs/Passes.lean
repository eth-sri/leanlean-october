module

public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Spec.Sec3.Problems

@[expose] public section

/-!
# Two loops over arrays for the reduction from all pairs to all-edges Exact Triangle

The host `pairsAE` (`ImprovedExponents.AllEdges.Pairs.Host`) asks a solver of all-edges Exact
Triangle `2b + 3` questions and takes, cell by cell, the disjunction of the answers; one of the
three matrices of a question is a transpose.  The two loops of this file do these two things.

* or(len, f, out) replaces out[i] by out[i] + f[i] − out[i] f[i] for i < len: the disjunction of
  two flags, in at most 31 len + 6 steps (`or_meets`; the pattern is upstream's `bump`).
* transpose(n, src, c, dst) writes src[i n + j] + c to dst[j n + i] for i, j < n, in at most
  30 n² + 20 n + 6 steps (`transpose_meets`): a loop over the columns j, whose body is a pass over
  the row j of the destination.
-/

namespace ImprovedExponents.AllEdges

open Light ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The disjunction of two arrays of flags -/

namespace OrPass

end OrPass

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/Passes.lean (bump_meets)

/-! ## The transpose -/

namespace Transpose

/-- The side n of the matrix. -/
abbrev Side : ℕ := 0
/-- The address of the source. -/
abbrev Src : ℕ := 1
/-- The summand c. -/
abbrev Shift : ℕ := 2
/-- The address of the destination. -/
abbrev Dst : ℕ := 3
/-- The column j of the source. -/
abbrev Col : ℕ := 4
/-- The address of the row j of the destination. -/
abbrev Row : ℕ := 5
/-- The row i of the source. -/
abbrev Idx : ℕ := 6

end Transpose

open Transpose in
/-- The row j of the destination: for i < n, dst[j n + i] := src[i n + j] + c. -/
def transposeRow : Stmt :=
  .set Row (v Dst +' v Col *' v Side) ;;
  pass Idx (v Side) (v Row) (M (v Src +' v Idx *' v Side +' v Col) +' v Shift)

open Transpose in
/-- transpose(n, src, c, dst): for j < n, the row j of the destination. -/
def transposeBody : Stmt := .for Col (v Side) transposeRow

/-- The transpose of the `n × n` matrix `Y` (entry `(k, j)` at `k n + j`) with `c` added: cell
`q = j n + k` holds `Y[k n + j] + c`. -/
def transposeL (n : ℕ) (c : ℤ) (Y : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q => Y.getD (q % n * n + q / n) 0 + c

@[simp] theorem length_transposeL (n : ℕ) (c : ℤ) (Y : List ℤ) :
    (transposeL n c Y).length = n * n := by
  simp [transposeL]

/-- The entry `(j, k)` of the transpose. -/
theorem transposeL_getD {n} (c : ℤ) (Y : List ℤ) {j k} (hj : j < n) (hk : k < n) :
    (transposeL n c Y).getD (j * n + k) 0 = Y.getD (k * n + j) 0 + c := by
  have hq : j * n + k < n * n := by nlinarith
  have hdiv : (j * n + k) / n = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hk]
    simp
  have hmod : (j * n + k) % n = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  simp [transposeL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq,
    Option.map_some, Option.getD_some, hdiv, hmod]

/-- The entries of the transpose of a matrix with entries in `[-U, U]`, with `c` added, lie in
`[c - U, c + U]`. -/
theorem mem_transposeL_bounds {n} {Y} {U} (hY : AbsLe Y U)
    (hlen : Y.length = n * n) (c : ℤ) : ∀ z ∈ transposeL n c Y, c - U ≤ z ∧ z ≤ c + U := by
  intro z hz
  simp only [transposeL, List.mem_map, List.mem_range] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  have hn : 0 < n := by grind
  have hidx : q % n * n + q / n < n * n := by
    have h1 := Nat.mod_lt q hn
    have h2 : q / n < n := by rwa [Nat.div_lt_iff_lt_mul hn]
    nlinarith
  have hmem : Y.getD (q % n * n + q / n) 0 ∈ Y := by
    grind
  have := abs_le.1 (hY _ hmem)
  omega

/-- The memory after the rows `0, …, j - 1` of the transpose have been written. -/
private def tMem (μ : ℕ → ℤ) (dst n : ℕ) (c : ℤ) (Y : List ℤ) (j : ℕ) : ℕ → ℤ :=
  wrote μ dst (fun q => (transposeL n c Y).getD q 0) (j * n)

/-- The row `j` written on top of the rows below it. -/
private theorem tMem_succ {μ} {dst n} {c} {Y} {j} (hj : j < n) :
    wrote (tMem μ dst n c Y j) (dst + j * n) (fun i => Y.getD (i * n + j) 0 + c) n =
      tMem μ dst n c Y (j + 1) := by
  funext a
  simp only [tMem, wrote, Nat.succ_mul]
  grind [transposeL_getD]

/-- **transpose** writes the transpose of the matrix at src, with c added to every entry, to the n²
cells from dst, and changes nothing else. -/
theorem transpose_meets {p} (hp : P[p]? = some transposeBody) {μ} {src dst n}
    {c} {Y} (hY : Seg μ src Y) (hlen : Y.length = n * n)
    (hsep : Apart src (n * n) dst (n * n))
    (hlim : lim.space ≤ lim.word ∧ src + n * n ≤ lim.space ∧ dst + n * n ≤ lim.space)
    (hfits : ∀ y ∈ Y, |y + c| ≤ lim.word) :
    Meets lim P p d [n, src, c, dst] μ (30 * (n * n) + 20 * n + 6) fun _ μ' =>
      Seg μ' dst (transposeL n c Y) ∧ SameOutside μ μ' dst (n * n) := by
  obtain ⟨hsp, hsrc, hdst⟩ := hlim
  have hn : n ≤ lim.word :=
    le_trans (by nlinarith) hsp
  refine .of_body hp ?_
  simp [transposeBody]
  refine Ends.forShape (fun j s μ' => ⟨frame [n, src, c, dst, j, s.1, s.2], μ'⟩)
    (fun j μ' => μ' = tMem μ dst n c Y j) n (30 * n + 11) (0, 0) (by simp [tMem, wrote_zero])
    ?round ?done
    (first := by
      rw [update_frame_setLocal]
      exact congrArg (State.mk · μ) (frame_append_zeros _ 2).symm)

  case round =>
    rintro j s μ' hj rfl
    have hjn : j * n + n ≤ n * n := by nlinarith
    light_set (dst + j * n : ℕ)
    refine Ends.pass (fun i => Y.getD (i * n + j) 0 + c) (fun i hi => ?_) ?_ hsp (by omega) rfl rfl

    · -- round i reads src[i n + j], which is never written
      have hin : i * n + j < n * n := by nlinarith
      have hread : wrote (tMem μ dst n c Y j) (dst + j * n) (fun i => Y.getD (i * n + j) 0 + c) i
          (src + (i * n + j)) = Y.getD (i * n + j) 0 := by
        rw [wrote_rest (by omega), tMem, wrote_rest (by omega), hY.getD (hlen ▸ hin)]
      have hmem : Y.getD (i * n + j) 0 ∈ Y := by
        grind
      have hfit := abs_le.1 (hfits _ hmem)
      have htoNat : (src + (i : ℤ) * n + j).toNat = src + (i * n + j) := by omega
      simp at hread hfit
      rw [update_frame_setLocal]
      simp [Expr.Safe, Op.eval, Expr.val, frame, setLocal, getElem?_pos, Option.getD_some, Limits.Addr, abs_le, htoNat, hread]
      grind
    · refine ⟨((dst + j * n : ℕ), n), tMem μ dst n c Y (j + 1), ?_, rfl⟩
      rw [update_frame_setLocal, tMem_succ hj]
      rfl
  case done =>
    rintro s μ' rfl
    refine ⟨fun i hi => ?_, show SameOutside μ (tMem μ dst n c Y n) dst (n * n) from
      sameOutside_wrote le_rfl⟩
    simp at hi
    change wrote μ dst (fun q => (transposeL n c Y).getD q 0) (n * n) (dst + i) = _
    rw [wrote_done hi, List.getD_eq_getElem _ _ (by grind)]

end ImprovedExponents.AllEdges
