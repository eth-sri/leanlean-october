module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Lang.Frames
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


/-- or(len, f, out): for i < len, out[i] := out[i] + f[i] − out[i] · f[i]. -/
def orBody  :=
  pass 3 (v 0) (v 2)
    (M (v 2 +' v 3) +' M (v 1 +' v 3) -'
      M (v 2 +' v 3) *' M (v 1 +' v 3))

/-- The disjunction of two lists of flags, cell by cell. -/
def orL (L F : List ℤ) := List.zipWith (fun o f => o + f - o * f) L F

@[simp] theorem length_orL L F : (orL L F).length = min L.length F.length := by
  simp [orL]

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/Passes.lean (bump_meets)
/-- **or** replaces the flags at out by their disjunction with the flags at f, and changes nothing
else.  All flags are 0 or 1. -/
theorem or_meets {p} (hp : P[p]? = some orBody) {μ} {fl out len} {F L}
    (hF : Seg μ fl F) (hL : Seg μ out L) (hlen : F.length = len ∧ L.length = len)
    (hsep : Apart fl len out len)
    (hlim : lim.space ≤ lim.word ∧ fl + len ≤ lim.space ∧ out + len ≤ lim.space)
    (hflag : ∀ f ∈ F, f = 0 ∨ f = 1) (hL01 : ∀ o ∈ L, o = 0 ∨ o = 1) (hw : 1 ≤ lim.word) :
    Meets lim P p d [len, fl, out] μ (31 * len + 6) fun _ μ' =>
      Seg μ' out (orL L F) ∧ SameOutside μ μ' out len := by
  obtain ⟨lF, lL⟩ := hlen
  obtain ⟨hsp, hfl, hout⟩ := hlim
  set f : Light.Memory := fun i => L.getD i 0 + F.getD i 0 - L.getD i 0 * F.getD i 0 with hf

  refine .of_body hp (Ends.pass f (fun j hj => ?_) ?_ hsp hout rfl rfl)
  · -- round j reads f[j], which is never written, and out[j], which it then overwrites
    have  : wrote μ out f j (fl + j) = F[j] :=
      (wrote_rest (by omega)).trans (hF j (by omega))
    have  : wrote μ out f j (out + j) = L[j] :=
      (wrote_rest (by omega)).trans (hL j (by omega))
    rw [update_frame_setLocal]
    rcases hflag _ (List.getElem_mem (show j < F.length by omega)) with h | h <;>
    rcases hL01 _ (List.getElem_mem (show j < L.length by omega)) with h' | h'
    all_goals
      simp_all [Limits.Addr, abs_le] <;> omega
  · dsimp only
    refine ⟨seg_wrote (by simp [orL, lF, lL]) fun i hi => ?_, sameOutside_wrote le_rfl⟩
    grind [orL]

/-! ## The transpose -/


/-- The row j of the destination: for i < n, dst[j n + i] := src[i n + j] + c. -/
def transposeRow  :=
  .set 5 (v 3 +' v 4 *' v 0) ;;
  pass 6 (v 0) (v 5) (M (v 1 +' v 6 *' v 0 +' v 4) +' v 2)

/-- transpose(n, src, c, dst): for j < n, the row j of the destination. -/
def transposeBody : Stmt := .for 4 (v 0) transposeRow

/-- The transpose of the `n × n` matrix `Y` (entry `(k, j)` at `k n + j`) with `c` added: cell
`q = j n + k` holds `Y[k n + j] + c`. -/
def transposeL n c (Y : List ℤ) :=
  (List.range (n * n)).map fun q => Y.getD (q % n * n + q / n) 0 + c

@[simp] theorem length_transposeL n c Y :
    (transposeL n c Y).length = n * n := by
  simp [transposeL]

/-- The entry `(j, k)` of the transpose. -/
theorem transposeL_getD {n} c Y {j k} (hj : j < n) (hk : k < n) :
    (transposeL n c Y).getD (j * n + k) 0 = Y.getD (k * n + j) 0 + c := by



  simp only [transposeL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by nlinarith : j * n + k < n * n),
    Option.map_some, Option.getD_some, (by
      grind [Nat.add_mul_div_right, Nat.div_eq_of_lt]
     : (j * n + k) / n = j), (by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
     : (j * n + k) % n = k)]

/-- The entries of the transpose of a matrix with entries in `[-U, U]`, with `c` added, lie in
`[c - U, c + U]`. -/
theorem mem_transposeL_bounds {n} {Y} {U} (hY : AbsLe Y U)
    (hlen : Y.length = n * n) c : ∀ z ∈ transposeL n c Y, c - U ≤ z ∧ z ≤ c + U := by
  intro z hz
  simp only [transposeL, List.mem_map, List.mem_range] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  have hn : 0 < n := by grind
  have  : q % n * n + q / n < n * n := by
    have  := Nat.mod_lt q hn
    have  : q / n < n := by rwa [Nat.div_lt_iff_lt_mul hn]
    nlinarith

  have := abs_le.1 (hY _ (by
    simp_all
   : Y.getD (q % n * n + q / n) 0 ∈ Y))
  constructor <;> omega

/-- The memory after the rows `0, …, j - 1` of the transpose have been written. -/
private def tMem μ dst n c Y j :=
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
  have  : (n : ℤ) ≤ lim.word :=
    le_trans (by nlinarith) hsp
  refine .of_body hp ?_
  simp only [transposeBody]
  refine Ends.forShape (fun j (s : ℤ × ℤ) μ' => ⟨frame [n, src, c, dst, j, s.1, s.2], μ'⟩)
    (fun j μ' => μ' = tMem μ dst n c Y j) n (30 * n + 11) (0, 0) (by simp [tMem, wrote_zero])
    ?round ?done
    (first := by
      rw [update_frame_setLocal]
      exact congrArg (State.mk · μ) (frame_append_zeros _ 2).symm)
    (hT := by simp; nlinarith)
  case round =>
    rintro j s μ' hj rfl
    have  : j * n + n ≤ n * n := by nlinarith
    simp only [transposeRow]
    -- Row := Dst + Col * Side
    light_set (dst + j * n : ℕ)
    refine Ends.pass (fun i => Y.getD (i * n + j) 0 + c) (fun i hi => ?_) ?_ hsp (by omega) rfl rfl
      (hT := by simp; omega)
    · -- round i reads src[i n + j], which is never written
      have hin : i * n + j < n * n := by nlinarith
      have hread : wrote (tMem μ dst n c Y j) (dst + j * n) (fun i => Y.getD (i * n + j) 0 + c) i
          (src + (i * n + j)) = Y.getD (i * n + j) 0 := by
        rw [wrote_rest (by omega), tMem, wrote_rest (by omega), hY.getD (hlen ▸ hin)]

      have hfit := abs_le.1 (hfits _ (by
        grind
       : Y.getD (i * n + j) 0 ∈ Y))
      have  : ((src : ℤ) + (i : ℤ) * n + j).toNat = src + (i * n + j) := by omega
      simp only [List.getD_eq_getElem?_getD] at hread hfit
      simp_all [Limits.Addr, abs_le] <;> omega
    · refine ⟨((dst + j * n : ℕ), n), tMem μ dst n c Y (j + 1), ?_, rfl⟩
      rw [update_frame_setLocal, tMem_succ hj]
      rfl
  case done =>
    rintro s μ' rfl
    refine ⟨fun i hi => ?_, show SameOutside μ (tMem μ dst n c Y n) dst (n * n) from
      sameOutside_wrote le_rfl⟩
    simp only [length_transposeL] at hi
    change wrote μ dst (fun q => (transposeL n c Y).getD q 0) (n * n) (dst + i) = _
    rw [wrote_done hi, List.getD_eq_getElem _ _ (by simpa using hi)]

end ImprovedExponents.AllEdges
