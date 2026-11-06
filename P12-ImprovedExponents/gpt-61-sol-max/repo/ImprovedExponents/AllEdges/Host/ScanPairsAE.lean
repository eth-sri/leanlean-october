module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Lang.Auto
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
the result in the flag (`scanPairsAE_spec`).  The pure side is `aeStep` and `aeExecs` of
`Flags.lean`.
-/

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}


/-- One query pair: if out[i] ≠ 0 then idx := flg + qa[i] n + qb[i]; if M idx = 0 then
M idx := scan(ab, bc, ac, n, qa[i], qb[i], c0, len). -/
def scanPairsAEStep (pScan : ℕ) : Stmt :=
  .ite (M (v 0 +' v 11) =' k 0) .skip
    (.set 12 (v 4 +' M (v 1 +' v 11) *' v 8 +' M (v 2 +' v 11)) ;;
      .ite (M (v 12) =' k 0)
        (.call pScan [v 5, v 6, v 7, v 8, M (v 1 +' v 11),
          M (v 2 +' v 11), v 9, v 10] 13 ;;
          .store (v 12) (v 13))
        .skip)

/-- scanPairsAE(out, qa, qb, w, flg, ab, bc, ac, n, c0, len); the parameter is the procedure number
of `scan`. -/
def scanPairsAEBody (pScan : ℕ)  :=
  .set 11 (k 0) ;;
  .while (v 11 <' v 3) (scanPairsAEStep pScan ;; .set 11 (v 11 +' k 1))

/-- The time for reading w answers and the flags of the accepted pairs. -/
def tAnswersAE w := 68 * w + 6

/-- The time of one scan of a piece of len vertices, with its call and the store of its result. -/
def tScanCallAE len := tScan len + 30

/-- The time of scanPairsAE, given the number of scans. -/
def tScanPairsAE w len execs := tAnswersAE w + tScanCallAE len * execs

/-- The cell `a n + b` of the query pair number `i`, in the lists of its rows and columns. -/
def idxOf n (QA QB : List ℕ) i := QA.getD i 0 * n + QB.getD i 0

section

variable {pScan : ℕ} {μ : Light.Memory} {out qa qb w ab bc ac n c0 len U flg : ℕ}
  {OUT AB BC AC F : List ℤ} {QA QB : List ℕ}

/-- What `scanPairsAE` assumes about the flags: `n²` cells at `flg`, within the memory and apart
from the three arrays of weights. -/
structure FlagsAt (lim : Limits) (μ : Light.Memory) (flg ab bc ac n : ℕ) (F : List ℤ) : Prop where
  len : F.length = n * n
  seg : Seg μ flg F
  below : flg + n * n ≤ lim.space
  apartAB : Apart flg (n * n) ab (n * n)
  apartBC : Apart flg (n * n) bc (n * n)
  apartAC : Apart flg (n * n) ac (n * n)

/-- The state of `scanPairsAE` when `i` query pairs have been treated and the counter is `j`. -/
def scanPairsAEState (μ : Light.Memory) (out qa qb w flg ab bc ac n c0 len : ℕ) (OUT AB BC AC F : List ℤ)
    (QA QB : List ℕ) (i j : ℕ) (idx res : ℤ) : State :=
  ⟨frame [out, qa, qb, w, flg, ab, bc, ac, n, c0, len, j, idx, res],
    wrote μ flg
      (fun q => (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i).getD q 0)
      (n * n)⟩

/-- The flags after `i` query pairs are a segment of `n²` cells at `flg`. -/
theorem seg_aeStep (G : FlagsAt lim μ flg ab bc ac n F) i :
    Seg (wrote μ flg
      (fun q => (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i).getD q 0)
      (n * n)) flg (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i) := by
  intro q hq
  rw [length_aeStep, G.len] at hq
  rw [wrote_done hq, List.getD_eq_getElem]

/-- The weights are not touched by the flags. -/
theorem weights_wrote (C : Weights lim μ ab bc ac n U AB BC AC)
    (G : FlagsAt lim μ flg ab bc ac n F) f :
    Weights lim (wrote μ flg f (n * n)) ab bc ac n U AB BC AC := by
  light_facts C C.arrAB C.arrBC C.arrAC G
  exact
    { C with
      arrAB := C.arrAB.keep fun b hb => wrote_rest (by omega)
      arrBC := C.arrBC.keep fun b hb => wrote_rest (by omega)
      arrAC := C.arrAC.keep fun b hb => wrote_rest (by omega) }

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/ScanPairs.lean
variable (hp : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (A : Answers lim μ out qa qb w n OUT QA QB)
    (hA : Apart flg (n * n) out w) (hQA : Apart flg (n * n) qa w) (hQB : Apart flg (n * n) qb w)
    (G : FlagsAt lim μ flg ab bc ac n F) (hd : d < lim.depth) (hc : c0 + len ≤ n)

include hp C A hA hQA hQB G hd hc in
/-- One query pair: a scan is made if the pair is accepted and its flag is 0. -/
theorem scanPairsAEStep_spec  {i}
    (hi : i < w) idx res :
    Ends lim P d (scanPairsAEStep pScan)
      (scanPairsAEState μ out qa qb w flg ab bc ac n c0 len OUT AB BC AC F QA QB i i idx res)
      (60 + if aeExec (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i then
        tScanCallAE len else 0)
      fun σ' => ∃ idx' res', σ' = scanPairsAEState μ out qa qb w flg ab bc ac n c0 len OUT AB BC AC
        F QA QB (i + 1) i idx' res' := by
  light_facts C C.arrAB C.arrBC C.arrAC
  light_facts A A.arrOUT A.arrQA A.arrQB
  light_facts G
  set μ₁ := wrote μ flg
    (fun q => (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i).getD q 0)
    (n * n) with hμ₁
  have hreadOUT : μ₁ (out + i) = OUT.getD i 0 := by
    rw [hμ₁, wrote_rest (by omega)]; exact A.arrOUT.read hi
  have hreadQA : μ₁ (qa + i) = QA.getD i 0 := by
    rw [hμ₁, wrote_rest (by omega)]; exact A.arrQA.read hi
  have hreadQB : μ₁ (qb + i) = QB.getD i 0 := by
    rw [hμ₁, wrote_rest (by omega)]; exact A.arrQB.read hi
  have ha := A.arrQA.getD_lt hi
  have hb := A.arrQB.getD_lt hi
  have hidx : idxOf n QA QB i < n * n := Nat.mul_add_lt_mul ha hb
  have hlenS : idxOf n QA QB i <
      (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i).length := by
    simp_all
  have hreadF : μ₁ (flg + idxOf n QA QB i) =
      (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i).getD
        (idxOf n QA QB i) 0 := by
    rw [hμ₁, wrote_done hidx]

  unfold scanPairsAEStep scanPairsAEState
  rw [← hμ₁, aeStep_succ, aePair, aeExec, accOf, hitOf]
  generalize hS : aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i = S
    at hreadF hμ₁ hlenS ⊢
  generalize hcell : S.getD (idxOf n QA QB i) 0 = cell at hreadF ⊢
  generalize OUT.getD i 0 = answer at hreadOUT ⊢
  unfold idxOf at hidx hreadF hlenS ⊢
  generalize QA.getD i 0 = a at hreadQA ha hidx hreadF hlenS ⊢
  generalize QB.getD i 0 = b at hreadQB hb hidx hreadF hlenS ⊢
  have haddr : ((flg : ℤ) + ((a : ℤ) * (n : ℤ) + (b : ℤ))).toNat = flg + (a * n + b) := by
    rfl
  -- if out[i] = 0
  by_cases hz : answer = 0
  · refine Ends.iteLast (fun _ => Ends.skip ⟨idx, res, ?_⟩)
      (fun h => absurd (by simp [hreadOUT, hz]) h) (by light_side)
    rw [hμ₁]
    simp [hz]
  refine Ends.iteLast (fun h => absurd h (by simp [hreadOUT, hz])) (fun _ => ?_) (by light_side)
  -- idx := flg + qa[i] n + qb[i]
  light_set (flg + (a * n + b) : ℕ) using hreadQA, hreadQB
  -- if M idx = 0
  by_cases hcell0 : cell = 0
  · refine Ends.iteLast (fun _ => ?_) fun h => absurd (by simp [haddr, hreadF, hcell0]) h
    -- res := scan(ab, bc, ac, n, qa[i], qb[i], c0, len); M idx := res
    light_call (scan_meets hp (weights_wrote C G fun q => (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len)
      (idxOf n QA QB) F i).getD q 0
    ) ha hb hc) using hreadQA, hreadQB, hz, hcell0, tScanCallAE with
      _ _ ⟨rfl, rfl⟩
    rw [flag_eq_bit]
    light_store (flg + (a * n + b)) (bit (scanHit n AB BC AC a b c0 len)) using hz, hcell0,
      tScanCallAE
    refine ⟨(flg + (a * n + b) : ℕ), bit (scanHit n AB BC AC a b c0 len), ?_⟩
    rw [ite_eq_left ⟨decide_eq_true hz, hcell0⟩]
    congr 1
    funext y
    by_cases hy : y = flg + (a * n + b)
    · subst hy
      rw [Function.update_self, wrote_done hidx, getD_set_self _ hlenS]
    · rw [Function.update_of_ne hy, hμ₁]
      by_cases hin : Inside flg (n * n) y
      · obtain ⟨q, rfl⟩ : ∃ q, y = flg + q := ⟨y - flg, by omega⟩
        rw [wrote_done (by omega), wrote_done (by omega), (by grind : ∀ (x : ℤ), (S.set (a * n + b) x).getD q 0 = S.getD q 0)]
      · grind [wrote_rest]
  · refine Ends.iteLast (fun h => absurd h (by simp [haddr, hreadF, hcell0])) fun _ =>
      Ends.skip ⟨(flg + (a * n + b) : ℕ), res, ?_⟩
    rw [hμ₁]
    simp [hcell0]

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/ScanPairs.lean
/-- The time of the rounds, added up. -/
theorem sum_scanPairsAE_rounds acc hit idx F len w :
    ∑ i ∈ Finset.range w, (4 + (64 + if aeExec acc hit idx F i then tScanCallAE len else 0))
      = 68 * w + tScanCallAE len * aeExecs acc hit idx F w := by
  induction w with
  | zero => simp [aeExecs]
  | succ w ih =>
    ram_safe [Finset.sum_range_succ, aeExecs_succ]

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/ScanPairs.lean
include hp C A hA hQA hQB G hd hc in
/-- **scanPairsAE** treats the `w` query pairs of an instance: the flags become
`aeStep … F w`, no other cell changes, and the time depends on the number of scans that are made. -/
theorem scanPairsAE_spec  :
    Ends lim P d (scanPairsAEBody pScan)
      ⟨frame [out, qa, qb, w, flg, ab, bc, ac, n, c0, len], μ⟩
      (tScanPairsAE w len (aeExecs (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB)
        F w)) fun σ' =>
      Seg σ'.mem flg (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F w) ∧
        SameOutside μ σ'.mem flg (n * n) := by
  light_facts C C.arrAB C.arrBC C.arrAC
  light_facts A A.arrOUT A.arrQA A.arrQB
  light_facts G
  have  := sum_scanPairsAE_rounds (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB)
    F len w
  unfold tScanPairsAE tAnswersAE
  -- i := 0
  light_set (0 : ℕ)
  -- while i < w
  refine (Ends.while (fun i σ => ∃ idx res, σ = scanPairsAEState μ out qa qb w flg ab bc ac n c0
    len OUT AB BC AC F QA QB i i idx res) w
    (fun i => 64 + if aeExec (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i then
      tScanCallAE len else 0) ?start ?round ?done).mono
    (by light_side) fun _ h => h
  case start =>

    refine ⟨0, 0, ?_⟩
    simp only [scanPairsAEState, aeStep_zero, ← (by
      funext y
      by_cases hin : Inside flg (n * n) y
      · obtain ⟨q, rfl⟩ : ∃ q, y = flg + q := ⟨y - flg, by omega⟩
        rw [wrote_done (by omega), G.seg.getD (by rw [G.len]; omega)]
      · rw [wrote_rest (by omega)]
     : μ = wrote μ flg (fun q => F.getD q 0) (n * n))]
    simpa using (frame_append_zeros [out, qa, qb, w, flg, ab, bc, ac, n, c0, len, 0] 2).symm
  case round =>
    rintro i _ hi ⟨idx, res, rfl⟩
    refine ⟨by simp, by simp [scanPairsAEState]; omega, ?_⟩
    -- the query pair number i; then i := i + 1
    refine Ends.next _ ((scanPairsAEStep_spec hp C A hA hQA hQB G hd hc hi idx res).mono le_rfl
      ?_) (by omega)
    rintro _ ⟨idx', res', rfl⟩
    light_block [scanPairsAEState]
  case done =>
    rintro _ ⟨idx, res, rfl⟩
    refine ⟨by simp, by simp [scanPairsAEState], seg_aeStep G w, ?_⟩
    simp only [scanPairsAEState]
    exact sameOutside_wrote le_rfl

end

end Light.Sec3
