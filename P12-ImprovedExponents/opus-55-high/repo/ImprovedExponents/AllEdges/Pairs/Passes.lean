
import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Lib.Pass
import ThreeSumApsp.Lang.Tactics
import ThreeSumApsp.Lang.Frames
import ThreeSumApsp.Spec.Sec3.Problems


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

/- The number of cells. -/
slots Len
/- The address of the flags that are read. -/
slots 1 Flags
/- The address of the flags that are changed. -/
slots 2 Dest
/- The counter. -/
slots 3 Index

end OrPass

open OrPass in
/-- or(len, f, out): for i < len, out[i] := out[i] + f[i] − out[i] · f[i]. -/
def orBody : Stmt :=
  pass Index (v Len) (v Dest)
    (M (v Dest +' v Index) +' M (v Flags +' v Index) -'
      M (v Dest +' v Index) *' M (v Flags +' v Index))

/-- The disjunction of two lists of flags, cell by cell. -/
def orL (L F : List ℤ) : List ℤ := List.zipWith (fun o f => o + f - o * f) L F

@[simp] theorem length_orL (L F : List ℤ) : (orL L F).length = min L.length F.length := by
  simp [orL]

variable {p : ℕ} {μ : ℕ → ℤ}

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/Passes.lean (bump_meets)
/-- **or** replaces the flags at out by their disjunction with the flags at f, and changes nothing
else.  All flags are 0 or 1. -/
theorem or_meets (hp : P[p]? = some orBody) {fl out len : ℕ} {F L : List ℤ}
    (hF : Seg μ fl F) (hL : Seg μ out L) (hlen : F.length = len ∧ L.length = len)
    (hsep : Apart fl len out len)
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ fl + len ≤ lim.space ∧ out + len ≤ lim.space)
    (hflag : ∀ f ∈ F, f = 0 ∨ f = 1) (hL01 : ∀ o ∈ L, o = 0 ∨ o = 1) (hw : 1 ≤ lim.word) :
    Meets lim P p d [(len : ℤ), fl, out] μ (31 * len + 6) fun _ μ' =>
      Seg μ' out (orL L F) ∧ SameOutside μ μ' out len := by
  obtain ⟨hsp, hfl, hout⟩ := hlim
  set f : ℕ → ℤ := fun i => L.getD i 0 + F.getD i 0 - L.getD i 0 * F.getD i 0 with hf
  have hfi : ∀ i (hF : i < F.length) (hL : i < L.length), f i = L[i] + F[i] - L[i] * F[i] :=
    by simp_all
  refine .of_body hp (Ends.pass f (fun j hj => ?_) ?_ hsp hout rfl rfl)
  · -- round j reads f[j], which is never written, and out[j], which it then overwrites
    have hreadF : wrote μ out f j (fl + j) = F[j] :=
      (wrote_rest).trans (by aesop)
    have hreadL : wrote μ out f j (out + j) = L[j] :=
      (wrote_rest).trans (by aesop)
    rcases hflag _ (List.getElem_mem (show j < F.length by omega)) with h | h <;>
    rcases hL01 _ (List.getElem_mem (show j < L.length by omega)) with h' | h'
    all_goals
      simp [Limits.Addr, abs_le, hreadF, hfi j (by omega) (by omega), h]; omega
  grind [seg_wrote, sameOutside_wrote, le_rfl, orL, List.length_zipWith]

/-! ## The transpose -/

namespace Transpose

/- The side n of the matrix. -/
slots Side
/- The address of the source. -/
slots 1 Src
/- The summand c. -/
slots 2 Shift
/- The address of the destination. -/
slots 3 Dst
/- The column j of the source. -/
slots 4 Col
/- The address of the row j of the destination. -/
slots 5 Row
/- The row i of the source. -/
slots 6 Idx

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

variable {n j : ℕ}

/-- The entry `(j, k)` of the transpose. -/
theorem transposeL_getD (c : ℤ) (Y : List ℤ) {k : ℕ} (hj : j < n) (hk : k < n) :
    (transposeL n c Y).getD (j * n + k) 0 = Y.getD (k * n + j) 0 + c := by
  have hq : j * n + k < n * n := by nlinarith
  have hdiv : (j * n + k) / n = j := by
    grind [Nat.add_comm, Nat.add_mul_div_right, Nat.div_eq_of_lt]
  grind [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt, transposeL, List.getElem?_range]

variable {Y : List ℤ}

/-- The entries of the transpose of a matrix with entries in `[-U, U]`, with `c` added, lie in
`[c - U, c + U]`. -/
theorem mem_transposeL_bounds {U : ℤ} (hY : AbsLe Y U)
    (hlen : Y.length = n * n) (c : ℤ) : ∀ z ∈ transposeL n c Y, c - U ≤ z ∧ z ≤ c + U := by
  intro z hz
  simp only [transposeL, List.mem_map, List.mem_range] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  have hn : 0 < n := by grind
  have hidx : q % n * n + q / n < n * n := by
    have h1 := q.mod_lt hn
    have h2 : q / n < n := by simp_all [Nat.div_lt_iff_lt_mul]
    nlinarith
  have hmem : Y.getD (q % n * n + q / n) 0 ∈ Y := by
    simp_all
  have := abs_le.1 (by aesop)
  omega

/-- The memory after the rows `0, …, j - 1` of the transpose have been written. -/
def tMem (μ : ℕ → ℤ) (dst n : ℕ) (c : ℤ) (Y : List ℤ) (j : ℕ) : ℕ → ℤ :=
  wrote μ dst (fun q => (transposeL n c Y).getD q 0) (j * n)

variable {dst : ℕ} {c : ℤ}

/-- The row `j` written on top of the rows below it. -/
theorem tMem_succ (hj : j < n) :
    wrote (tMem μ dst n c Y j) (dst + j * n) (fun i => Y.getD (i * n + j) 0 + c) n =
      tMem μ dst n c Y (j + 1) := by
  funext a
  simp only [tMem, wrote, Nat.succ_mul]
  grind [Nat.add_sub_cancel_left, transposeL_getD]

/-- **transpose** writes the transpose of the matrix at src, with c added to every entry, to the n²
cells from dst, and changes nothing else. -/
theorem transpose_meets (hp : P[p]? = some transposeBody) {src : ℕ}
    (hY : Seg μ src Y) (hlen : Y.length = n * n)
    (hsep : Apart src (n * n) dst (n * n))
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ src + n * n ≤ lim.space ∧ dst + n * n ≤ lim.space)
    (hfits : ∀ y ∈ Y, |y + c| ≤ lim.word) :
    Meets lim P p d [(n : ℤ), src, c, dst] μ (30 * (n * n) + 20 * n + 6) fun _ μ' =>
      Seg μ' dst (transposeL n c Y) ∧ SameOutside μ μ' dst (n * n) := by
  obtain ⟨hsp, hsrc, hdst⟩ := hlim
  have hn : n ≤ lim.word :=
    le_trans (by exact_mod_cast (Nat.le_mul_self n).trans (by omega : n * n ≤ lim.space)) hsp
  refine .of_body hp ?_
  refine Ends.forShape (fun j s μ' => ⟨frame [n, src, c, dst, j, s.1, s.2], μ'⟩)
    (fun j μ' => μ' = tMem μ dst n c Y j) n (30 * n + 11) (0, 0) (by simp [tMem, wrote_zero])
    ?_ ?_
    (first := by
      rw [update_frame_setLocal]
      exact congrArg (State.mk · μ) (frame_append_zeros _ 2).symm)
  ·
    rintro j s μ' hj rfl
    have hjn : j * n + n ≤ n * n := by nlinarith
    light_set (dst + j * n)
    refine Ends.pass (fun i => Y.getD (i * n + j) 0 + c) (fun i hi => ?_) ?_ hsp (by omega) rfl rfl
    · -- round i reads src[i n + j], which is never written
      have hin : i * n + j < n * n := by nlinarith
      have hread : wrote (tMem μ dst n c Y j) (dst + j * n) (fun i => Y.getD (i * n + j) 0 + c) i
          (src + (i * n + j)) = Y.getD (i * n + j) 0 := by
        rw [wrote_rest, tMem, wrote_rest, hY.getD (by omega)]
      have hmem : Y.getD (i * n + j) 0 ∈ Y := by
        simp_all
      have htoNat : (src + (i : ℤ) * n + j).toNat = src + i * n + j := by omega
      simp [Expr.Safe, Op.eval, Expr.val, frame, setLocal, Limits.Addr, htoNat]
      grind
    · refine ⟨(dst + j * n, n), tMem μ dst n c Y _, ?_, rfl⟩
      rw [update_frame_setLocal, tMem_succ hj]
      rfl
  ·
    rintro s μ' rfl
    refine ⟨fun i hi => ?_, show SameOutside μ (tMem μ dst n c Y n) dst _ from
      sameOutside_wrote le_rfl⟩
    simp [length_transposeL] at hi
    change wrote μ dst (fun q => (transposeL n c Y).getD q 0) _ _ = _
    grind [wrote_done, List.getD_eq_getElem]
