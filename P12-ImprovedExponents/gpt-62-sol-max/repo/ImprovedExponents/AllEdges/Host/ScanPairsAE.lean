module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.WhileShape

public import ImprovedExponents.AllEdges.Host.Flags

@[expose] public section

/-!
# Reading the answers of one instance and scanning for witnesses, with flags

Footnote 10 of the paper: the proof of Theorem 17 "also solves the all-edges version of Exact
Triangle (scanning each pair only until its zero triangle is found)".

scanPairsAE(out, qa, qb, w, flg, ab, bc, ac, n, c0, len) is upstream's scanPairs with the flag `f`
replaced by the base address `flg` of the `n²` flags: for every query pair number `i < w` whose
answer `out[i]` is not 0, if the flag of the pair `(qa[i], qb[i])`, the cell `flg + qa[i] n +
qb[i]`, is 0, scan the piece `{c0, …, c0 + len - 1}` for a zero triangle through the pair and store
the result in the flag (`scanPairsAE_meets`).  The pure side is `aeStep` and `aeExecs` of
`Flags.lean`.
-/

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace ScanPairsAE

/-- The locals of `scanPairsAE`.  The arguments: the addresses of the answers and of the rows and
the columns of the query pairs, their number `w`, the address of the flags, the addresses of the
three arrays of weights, `n`, and the first vertex and the number of vertices of the piece.  Then
the counter, the address of the flag of the current pair, and the result of its scan. -/
registers [Out, Rows, Cols, Num, Flg, AdrAB, AdrBC, AdrAC, Size, First, Len, Cnt, Idx, Res]

end ScanPairsAE

open ScanPairsAE in
/-- One query pair: if out[i] ≠ 0 then idx := flg + qa[i] n + qb[i]; if M idx = 0 then
M idx := scan(ab, bc, ac, n, qa[i], qb[i], c0, len). -/
def scanPairsAEStep (pScan : ℕ) : Stmt :=
  .ite (M (v Out +' v Cnt) =' k 0) .skip
    (.set Idx (v Flg +' M (v Rows +' v Cnt) *' v Size +' M (v Cols +' v Cnt)) ;;
      .ite (M (v Idx) =' k 0)
        (.call pScan [v AdrAB, v AdrBC, v AdrAC, v Size, M (v Rows +' v Cnt),
          M (v Cols +' v Cnt), v First, v Len] Res ;;
          .store (v Idx) (v Res))
        .skip)

open ScanPairsAE in
/-- scanPairsAE(out, qa, qb, w, flg, ab, bc, ac, n, c0, len); the parameter is the procedure number
of `scan`. -/
def scanPairsAEBody (pScan : ℕ) : Stmt :=
  .set Cnt (k 0) ;;
  .while (v Cnt <' v Num) (scanPairsAEStep pScan ;; .set Cnt (v Cnt +' k 1))

/-- The time for reading w answers and the flags of the accepted pairs. -/
def tAnswersAE (w : ℕ) : ℕ := 68 * w + 6

/-- The time of one scan of a piece of len vertices, with its call and the store of its result. -/
def tScanCallAE (len : ℕ) : ℕ := tScan len + 30

/-- The time of scanPairsAE, given the number of scans. -/
def tScanPairsAE (w len execs : ℕ) : ℕ := tAnswersAE w + tScanCallAE len * execs

/-- The cell `a n + b` of the query pair number `i`, in the lists of its rows and columns. -/
def idxOf (n : ℕ) (QA QB : List ℕ) (i : ℕ) : ℕ := QA.getD i 0 * n + QB.getD i 0

section

variable {pScan : ℕ} {x : TriInst} {μ : ℕ → ℤ} {out qa qb w c0 len flg : ℕ}
  {OUT F : List ℤ} {QA QB : List ℕ}

/-- The flags fit and are disjoint from the inputs. -/
structure FlagsAt (lim : Limits) (μ : ℕ → ℤ) (x : TriInst) (flg : ℕ) (F : List ℤ) : Prop where
  len : F.length = x.n * x.n
  seg : Seg μ flg F
  below : flg + x.n * x.n ≤ lim.space
  apartAB : Apart flg (x.n * x.n) x.ab (x.n * x.n)
  apartBC : Apart flg (x.n * x.n) x.bc (x.n * x.n)
  apartAC : Apart flg (x.n * x.n) x.ac (x.n * x.n)

private abbrev scanPairLoc (x : TriInst) (out qa qb w flg c0 len i : ℕ) (idx res : ℤ) : List ℤ :=
  [out, qa, qb, w, flg, x.ab, x.bc, x.ac, x.n, c0, len, i, idx, res]

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/ScanPairs.lean
/-- The time of the rounds, added up. -/
theorem sum_scanPairsAE_rounds (acc hit : ℕ → Bool) (idx : ℕ → ℕ) (F : List ℤ) (len w : ℕ) :
    ∑ i ∈ Finset.range w, (4 + (64 + if aeExec acc hit idx F i then tScanCallAE len else 0))
      = 68 * w + tScanCallAE len * aeExecs acc hit idx F w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [Finset.sum_range_succ, ih, aeExecs]
    lia

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/ScanPairs.lean
/-- **scanPairsAE** treats the `w` query pairs of an instance: the flags become
`aeStep … F w`, no other cell changes, and the time depends on the number of scans that are made. -/
theorem scanPairsAE_meets {p : ℕ} (hP : P[p]? = some (scanPairsAEBody pScan))
    (hp : P[pScan]? = some scanBody)
    (C : Weights lim μ x) (A : Answers lim μ out qa qb w x.n OUT QA QB)
    (hA : Apart flg (x.n * x.n) out w) (hQA : Apart flg (x.n * x.n) qa w)
    (hQB : Apart flg (x.n * x.n) qb w) (G : FlagsAt lim μ x flg F)
    (hd : d < lim.depth) (hc : c0 + len ≤ x.n) :
    let acc := accOf OUT
    let hit := hitOf x.n x.AB x.BC x.AC QA QB c0 len
    let idx := idxOf x.n QA QB
    Meets lim P p d [out, qa, qb, w, flg, x.ab, x.bc, x.ac, x.n, c0, len] μ
      (tScanPairsAE w len (aeExecs acc hit idx F w)) fun _ ν =>
      Seg ν flg (aeStep acc hit idx F w) ∧ SameOutside μ ν flg (x.n * x.n) := by
  intro acc hit idx
  refine .of_body hP ?_
  have hw := C.hw
  light_facts A A.arrOUT A.arrQA A.arrQB G
  have hsum := sum_scanPairsAE_rounds acc hit idx F len w
  unfold tScanPairsAE tAnswersAE
  light_step
  refine Ends.whileShapeCosts (fun i (z : ℤ × ℤ) ν =>
      ⟨frame (scanPairLoc x out qa qb w flg c0 len i z.1 z.2), ν⟩)
    (fun i _ ν => Seg ν flg (aeStep acc hit idx F i) ∧ SameOutside μ ν flg (x.n * x.n)) w
    (fun i => 64 + if aeExec acc hit idx F i then tScanCallAE len else 0) (0, 0) μ
    ⟨G.seg, .refl⟩ ?_ (fun _ _ h => h) (first := (frame_append_zeros _ 2).symm ▸ rfl)
    (hT := by light_side)
  rintro i ⟨j, r⟩ μ' hi ⟨seg, rest⟩
  have C' := C.keep rest G.apartAB G.apartBC G.apartAC
  have A' : Answers lim μ' out qa qb w x.n OUT QA QB :=
    ⟨A.arrOUT.keep, A.arrQA.keep, A.arrQB.keep, A.w_lt⟩
  have hreadOUT := A'.arrOUT.read hi
  have hreadQA := A'.arrQA.read hi
  have hreadQB := A'.arrQB.read hi
  have ha := A'.arrQA.getD_lt hi
  have hb := A'.arrQB.getD_lt hi
  have hidx := Nat.mul_add_lt_mul ha hb
  have hq : idx i < (aeStep acc hit idx F i).length := by simpa [idx, idxOf, G.len] using hidx
  have hreadF := seg.getD hq 0
  dsimp only [acc, hit, idx] at *
  unfold aeExec
  rw [aeStep_succ]
  unfold aePair
  simp only [idxOf, accOf, hitOf, Bool.and_eq_true, decide_eq_true_eq] at hq hreadF ⊢
  set! answer := OUT.getD i 0 with ← eout
  set! a := QA.getD i 0 with ← eqa
  set! b := QB.getD i 0 with ← eqb
  set! cell := (aeStep (accOf OUT) (hitOf x.n x.AB x.BC x.AC QA QB c0 len) (idxOf x.n QA QB) F i).getD (a * x.n + b) 0 with ← eflg
  simp only [eout, eqa, eqb, eflg, decide_eq_true_eq] at ha hb hreadOUT hreadQA hreadQB hidx hq hreadF ⊢
  have haddr : ((flg : ℤ) + (a * (x.n : ℤ) + b)).toNat = flg + (a * x.n + b) := rfl
  -- The two tests implement the guard of aePair.
  unfold scanPairsAEStep
  light_if hz hz : answer = 0 using hreadOUT
  ·
    light_set (i + 1 : ℕ) using hz, tScanCallAE
    exact ⟨(j, r), _, rfl, by simpa [hz] using seg, rest⟩
  simp only [ne_eq, hz, not_false_eq_true, true_and]
  light_set (flg + (a * x.n + b) : ℕ) using hreadQA, hreadQB
  light_if hzero hzero : cell = 0 using haddr, hreadF
  ·
    light_call (scan_meets hp C' ha hb hc) using hreadQA, hreadQB, hzero, tScanCallAE with _ _ ⟨rfl, rfl⟩
    rw [flag_eq_bit]
    light_store (flg + (a * x.n + b) : ℕ) (bit (scanHit x.n x.AB x.BC x.AC a b c0 len)) using
      hzero, tScanCallAE
    light_set (i + 1 : ℕ) using hzero, tScanCallAE
    refine ⟨(_, _), _, rfl, ?_, rest.update ⟨by omega, by omega⟩ _⟩
    simpa [hzero] using seg.update_in hq (bit (scanHit x.n x.AB x.BC x.AC a b c0 len))
  ·
    light_set (i + 1 : ℕ) using hzero
    exact ⟨(_, r), _, rfl, by simpa [hzero] using seg, rest⟩

end

end Light.Sec3
