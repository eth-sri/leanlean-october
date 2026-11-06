module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Arrays
public import ImprovedExponents.AllEdges.Task
public import ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.Scan
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.NeedPolynomial
public import ThreeSumApsp.Programs.Sec3.Theorem17.TimeBound.Terms
public import ThreeSumApsp.Lang.Lib.Copy
public import ImprovedExponents.Pipeline.HostBound

@[expose] public section

/-!
# The flags of the all-edges host, as pure data

Footnote 10 of the paper: the proof of Theorem 17 "also solves the all-edges version of Exact
Triangle (scanning each pair only until its zero triangle is found)".  The all-edges host keeps
`n²` flags, one per pair `(a, b)`: for an accepted query pair whose flag is still 0, it scans the
piece of its instance and stores the result in the flag; a pair whose flag is already 1 is skipped.

The first part is generic, over the acceptance `acc i`, the result `hit i` of the scan and the cell
`idx i` of the query pair number `i`: `aeStep acc hit idx F i` are the flags after the first `i`
query pairs have been treated, starting from `F`, and `aeExecs acc hit idx F w` is the number of
scans made.  A scan either fails or raises the number of flags that are not 0
(`aeExecs_add_ones_le`).

The second part follows the flags through the loop over the instances of upstream's host
(`HostData`): `flagsAt X t` are the flags when instance `t` begins.  After all instances they are
the flags of the task (`flagsAt_m`), and at most `Σ fails + n²` scans are made (`sum_execsAE_le`).
-/

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The flags through the query pairs of one instance -/

section Generic

variable (acc hit : ℕ → Bool) (idx : ℕ → ℕ)

/-- The query pair number `i`, treated with the flags `F`: if it is accepted and its flag is 0, the
result of its scan goes into its flag. -/
def aePair (F : List ℤ) (i : ℕ) : List ℤ :=
  if acc i = true ∧ F.getD (idx i) 0 = 0 then F.set (idx i) (bit (hit i)) else F

/-- The flags after the first `i` query pairs have been treated, starting from the flags `F`. -/
def aeStep (F : List ℤ) : ℕ → List ℤ
  | 0 => F
  | i + 1 => aePair acc hit idx (aeStep F i) i

/-- A scan is made for the query pair number `i`, if the flags were `F` at first: the pair is
accepted and its flag is still 0. -/
def aeExec (F : List ℤ) (i : ℕ) : Bool :=
  acc i && decide ((aeStep acc hit idx F i).getD (idx i) 0 = 0)

/-- The number of scans made for the first `w` query pairs, if the flags were `F` at first. -/
def aeExecs (F : List ℤ) (w : ℕ) : ℕ := ((List.range w).filter (aeExec acc hit idx F)).length

/-- The number of flags that are not 0. -/
def ones (F : List ℤ) : ℕ := F.countP fun x => decide (x ≠ 0)

variable {acc hit idx}

@[simp] theorem aeStep_zero (F : List ℤ) : aeStep acc hit idx F 0 = F := rfl

@[simp] theorem aeStep_succ (F : List ℤ) (i : ℕ) :
    aeStep acc hit idx F (i + 1) = aePair acc hit idx (aeStep acc hit idx F i) i := rfl

@[simp] theorem length_aePair (F : List ℤ) (i : ℕ) :
    (aePair acc hit idx F i).length = F.length := by
  unfold aePair
  split_ifs <;> simp

@[simp] theorem length_aeStep (F : List ℤ) (i : ℕ) :
    (aeStep acc hit idx F i).length = F.length := by
  induction i with
  | zero => rfl
  | succ i ih => rw [aeStep, length_aePair, ih]

/-- A cell of a list other than the one that is set. -/
theorem getD_set_ne (F : List ℤ) {j q : ℕ} (hne : j ≠ q) (x : ℤ) :
    (F.set j x).getD q 0 = F.getD q 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set, ite_eq_right hne]

/-- The cell of a list that is set. -/
theorem getD_set_self (F : List ℤ) {j : ℕ} (hj : j < F.length) (x : ℤ) :
    (F.set j x).getD j 0 = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, ite_eq_left rfl, ite_eq_left hj,
    Option.getD_some]

/-- The bit of a proposition is 0 if and only if the proposition fails. -/
theorem bit_decide_eq_zero (P : Prop) [Decidable P] : bit (decide P) = 0 ↔ ¬P := by
  by_cases h : P <;> simp [bit, h]

theorem aeExecs_succ (F : List ℤ) (w : ℕ) :
    aeExecs acc hit idx F (w + 1) =
      aeExecs acc hit idx F w + if aeExec acc hit idx F w then 1 else 0 := by
  simp only [aeExecs, List.range_succ, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  split_ifs <;> rfl

/-- The flag of the cell `q` after `i` query pairs: 1 if one of them is accepted, lies in the cell
and hits, else what it was, if the cell was 0 when the instance began. -/
theorem aeStep_getD {F : List ℤ} {q : ℕ} (hq : q < F.length) (i : ℕ) :
    (aeStep acc hit idx F i).getD q 0 =
      if F.getD q 0 = 0 then
        bit (decide (∃ j < i, idx j = q ∧ acc j = true ∧ hit j = true))
      else F.getD q 0 := by
  induction i with
  | zero => simp [aeStep, bit]
  | succ i ih =>
    have hex : (∃ j < i + 1, idx j = q ∧ acc j = true ∧ hit j = true) ↔
        (∃ j < i, idx j = q ∧ acc j = true ∧ hit j = true) ∨
          (idx i = q ∧ acc i = true ∧ hit i = true) := by
      constructor
      · rintro ⟨j, hj, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
        · exact Or.inl ⟨j, hlt, h⟩
        · exact Or.inr h
      · rintro (⟨j, hj, h⟩ | h)
        · exact ⟨j, by omega, h⟩
        · exact ⟨i, by omega, h⟩
    rw [aeStep_succ, aePair]
    by_cases hpq : idx i = q
    · -- the pair `i` lies in the cell `q`
      rw [hpq]
      have hlen : q < (aeStep acc hit idx F i).length := by rwa [length_aeStep]
      split_ifs with h0 hF hF
      · -- it is scanned: its flag was 0, so no earlier pair in the cell hit
        rw [ih, ite_eq_left hF, bit_decide_eq_zero] at h0
        rw [getD_set_self _ hlen]
        congr 1
        rw [Bool.eq_iff_iff, decide_eq_true_eq, hex]
        simp [h0.1, h0.2, hpq]
      · rw [ih, ite_eq_right hF] at h0
        exact absurd h0.2 hF
      · -- it is not scanned: not accepted, or an earlier pair in the cell hit
        rw [ih, ite_eq_left hF, bit_decide_eq_zero] at h0
        rw [ih, ite_eq_left hF]
        congr 1
        rw [decide_eq_decide, hex]
        constructor
        · exact Or.inl
        · rintro (h | ⟨-, hacc, -⟩)
          · exact h
          · by_contra hn
            exact h0 ⟨hacc, hn⟩
      · rw [ih, ite_eq_right hF]
    · -- the pair `i` lies in another cell
      have hex' : (∃ j < i + 1, idx j = q ∧ acc j = true ∧ hit j = true) ↔
          (∃ j < i, idx j = q ∧ acc j = true ∧ hit j = true) := by
        rw [hex]
        simp [hpq]
      have key : (aeStep acc hit idx F i).getD q 0 = if F.getD q 0 = 0 then
          bit (decide (∃ j < i + 1, idx j = q ∧ acc j = true ∧ hit j = true))
          else F.getD q 0 := by
        rw [ih]
        simp only [hex']
      by_cases h0 : acc i = true ∧ (aeStep acc hit idx F i).getD (idx i) 0 = 0
      · rw [ite_eq_left h0, getD_set_ne _ hpq]
        exact key
      · rw [ite_eq_right h0]
        exact key

/-- The number of flags that are not 0 is at most the number of flags. -/
theorem ones_le_length (F : List ℤ) : ones F ≤ F.length := List.countP_le_length

/-- Treating one query pair: a scan fails or raises the number of flags that are not 0. -/
theorem aeExec_add_ones_le (F : List ℤ) {i : ℕ} (hidx : idx i < F.length) :
    (if aeExec acc hit idx F i then 1 else 0) + ones (aeStep acc hit idx F i) ≤
      (if acc i && !hit i then 1 else 0) + ones (aeStep acc hit idx F (i + 1)) := by
  have hidx' : idx i < (aeStep acc hit idx F i).length := by rwa [length_aeStep]
  rw [aeStep_succ, aePair]
  by_cases h0 : acc i = true ∧ (aeStep acc hit idx F i).getD (idx i) 0 = 0
  · -- a scan is made
    have hex : aeExec acc hit idx F i = true := by
      rw [aeExec, Bool.and_eq_true, decide_eq_true_eq]
      exact h0
    rw [ite_eq_left h0, ite_eq_left hex, ones, ones, List.countP_set hidx',
      ← List.getD_eq_getElem _ 0 hidx', h0.2]
    rcases hhit : hit i
    · -- it fails
      simp [h0.1, bit]
    · -- it hits: one more flag is 1
      rw [h0.1, bit, ite_eq_left rfl]
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, zero_add, ne_eq,
        one_ne_zero, not_false_eq_true, not_true_eq_false, decide_true, decide_false, ite_true,
        Nat.sub_zero]
      omega
  · -- no scan: the pair is not accepted or its flag is not 0
    have hex : aeExec acc hit idx F i = false := by
      rcases h : aeExec acc hit idx F i
      · rfl
      · rw [aeExec, Bool.and_eq_true, decide_eq_true_eq] at h
        exact absurd h h0
    rw [ite_eq_right h0]
    simp only [hex, Bool.false_eq_true, ite_false, zero_add]
    exact Nat.le_add_left _ _

/-- **Each scan fails or raises the number of flags that are 1**: through `w` query pairs whose
cells lie within the flags. -/
theorem aeExecs_add_ones_le (F : List ℤ) {w : ℕ} (hidx : ∀ i < w, idx i < F.length) :
    aeExecs acc hit idx F w + ones F ≤
      failsUpto acc hit w + ones (aeStep acc hit idx F w) := by
  induction w with
  | zero => simp [aeExecs, failsUpto]
  | succ w ih =>
    have := aeExec_add_ones_le (acc := acc) (hit := hit) F (hidx w (Nat.lt_succ_self w))
    rw [aeExecs_succ, failsUpto_succ]
    have ih := ih fun i hi => hidx i (by omega)
    omega

/-- The flags depend only on the first `w` query pairs. -/
theorem aeStep_congr {acc' hit' : ℕ → Bool} {idx' : ℕ → ℕ} (F : List ℤ) {w : ℕ}
    (h : ∀ i < w, acc i = acc' i ∧ hit i = hit' i ∧ idx i = idx' i) :
    aeStep acc hit idx F w = aeStep acc' hit' idx' F w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    obtain ⟨ha, hh, hi⟩ := h w (Nat.lt_succ_self w)
    rw [aeStep_succ, aeStep_succ, ih fun i hi => h i (by omega), aePair, aePair, ha, hh, hi]

/-- The number of scans depends only on the first `w` query pairs. -/
theorem aeExecs_congr {acc' hit' : ℕ → Bool} {idx' : ℕ → ℕ} (F : List ℤ) {w : ℕ}
    (h : ∀ i < w, acc i = acc' i ∧ hit i = hit' i ∧ idx i = idx' i) :
    aeExecs acc hit idx F w = aeExecs acc' hit' idx' F w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    obtain ⟨ha, hh, hi⟩ := h w (Nat.lt_succ_self w)
    rw [aeExecs_succ, aeExecs_succ, ih fun i hi => h i (by omega), aeExec, aeExec, ha, hi,
      aeStep_congr F fun i hi => h i (by omega)]

end Generic

/-! ## The flags through the instances of the host -/

namespace HostData

variable (X : HostData)

/-- The cell `a n + b` of the query pair number `i` of instance `t`. -/
def pairIdx (t i : ℕ) : ℕ := X.rowOf t i * X.n + X.colOf t i

/-- The flags after the first `i` query pairs of instance `t` have been treated, starting from the
flags `F`. -/
def flagsStep (t : ℕ) (F : List ℤ) (i : ℕ) : List ℤ := aeStep (X.acc t) (X.hit t) (X.pairIdx t) F i

/-- The number of scans made for the first `w` query pairs of instance `t`, if the flags were `F`
when the instance began. -/
def execsAEUpto (t : ℕ) (F : List ℤ) (w : ℕ) : ℕ := aeExecs (X.acc t) (X.hit t) (X.pairIdx t) F w

/-- The flags when instance `t` begins: all 0 at first. -/
def flagsAt : ℕ → List ℤ
  | 0 => List.replicate (X.n * X.n) 0
  | t + 1 => X.flagsStep t (flagsAt t) (X.w t)

/-- The number of scans made for instance `t`. -/
def execsAE (t : ℕ) : ℕ := X.execsAEUpto t (X.flagsAt t) (X.w t)

theorem flagsStep_def (t : ℕ) (F : List ℤ) (i : ℕ) :
    X.flagsStep t F i = aeStep (X.acc t) (X.hit t) (X.pairIdx t) F i := rfl

@[simp] theorem length_flagsStep (t : ℕ) (F : List ℤ) (i : ℕ) :
    (X.flagsStep t F i).length = F.length := length_aeStep _ _

@[simp] theorem length_flagsAt (t : ℕ) : (X.flagsAt t).length = X.n * X.n := by
  induction t with
  | zero => simp [flagsAt]
  | succ t ih => rw [flagsAt, length_flagsStep, ih]

/-- The flag of the cell `q < n²` when instance `T` begins: 1 if an accepted query pair of an
earlier instance lies in the cell and hits, 0 if not. -/
theorem flagsAt_getD {T q : ℕ} (hq : q < X.n * X.n) :
    (X.flagsAt T).getD q 0 =
      bit (decide (∃ t < T, ∃ i < X.w t, X.pairIdx t i = q ∧ X.acc t i = true ∧
        X.hit t i = true)) := by
  induction T with
  | zero => simp [flagsAt, List.getD_eq_getElem?_getD, hq, bit]
  | succ T ih =>
    have hex : (∃ t < T + 1, ∃ i < X.w t, X.pairIdx t i = q ∧ X.acc t i = true ∧
        X.hit t i = true) ↔
        (∃ t < T, ∃ i < X.w t, X.pairIdx t i = q ∧ X.acc t i = true ∧ X.hit t i = true) ∨
          (∃ i < X.w T, X.pairIdx T i = q ∧ X.acc T i = true ∧ X.hit T i = true) := by
      constructor
      · rintro ⟨t, ht, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with hlt | rfl
        · exact Or.inl ⟨t, hlt, h⟩
        · exact Or.inr h
      · rintro (⟨t, ht, h⟩ | h)
        · exact ⟨t, by omega, h⟩
        · exact ⟨T, by omega, h⟩
    rw [flagsAt, flagsStep_def, aeStep_getD (by rw [length_flagsAt]; exact hq), ih]
    simp only [bit, hex, decide_eq_true_eq]
    by_cases hprev : ∃ t < T, ∃ i < X.w t, X.pairIdx t i = q ∧ X.acc t i = true ∧ X.hit t i = true
    · simp [hprev]
    · simp [hprev]

/-- The cell of the query pair number `i` of instance `t`, in the lists of rows and columns that the
host writes. -/
theorem pairIdx_eq {t i : ℕ} (hi : i < X.w t) :
    X.pairIdx t i = (X.WI t).getD i 0 * X.n + (X.WJ t).getD i 0 := by
  rw [pairIdx, getD_WI hi, getD_WJ hi]

variable {X} in
/-- The cells of the query pairs of an instance lie within the `n²` flags. -/
theorem Valid.pairIdx_lt (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    X.pairIdx t i < X.n * X.n :=
  Nat.mul_add_lt_mul (hv.rowOf_lt ht hi) (hv.colOf_lt ht hi)

/-! ## Correctness -/

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/InstanceFacts.lean (found_m)
/-- **After all instances, the flags are those of all-edges Exact Triangle**: a pair with a zero
triangle is accepted and hit in the instance of the piece of its `c`, and every hit is a zero
triangle. -/
theorem flagsAt_m (hv : X.Valid) :
    X.flagsAt X.m = ImprovedExponents.AllEdges.aeFlags X.n X.AB X.BC X.AC := by
  apply List.ext_getElem (by simp)
  intro q hq _
  rw [← List.getD_eq_getElem _ 0 hq, ← List.getD_eq_getElem _ 0 (by simpa using hq)]
  rw [length_flagsAt] at hq
  have ha : q / X.n < X.n := Nat.div_lt_of_lt_mul' hq
  have hb : q % X.n < X.n := Nat.mod_lt_of_lt_mul hq
  have hdivmod : q / X.n * X.n + q % X.n = q := Nat.div_add_mod' q X.n
  rw [X.flagsAt_getD hq, ← hdivmod,
    ImprovedExponents.AllEdges.aeFlags_getD_eq_bit_scanHit _ _ _ ha hb, hdivmod]
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [scanHit, List.any_eq_true, List.mem_range, decide_eq_true_eq, Nat.add_zero, hdivmod]
  constructor
  · rintro ⟨t, ht, i, hi, hpq, -, hhit⟩
    obtain ⟨c, hc, hzero⟩ := (hit_iff hi).1 hhit
    have := hv.piece_le ht
    have hcol := hv.colOf_lt ht hi
    have hrow : X.rowOf t i = q / X.n := by
      rw [← hpq, pairIdx, Nat.mul_add_div_of_lt hcol]
    have hcol' : X.colOf t i = q % X.n := by
      rw [← hpq, pairIdx, Nat.mul_add_mod_of_lt hcol]
    refine ⟨X.c0 t + c, by omega, ?_⟩
    rw [sumAt, hrow, hcol', hdivmod] at hzero
    exact hzero
  · rintro ⟨c, hc, hzero⟩
    obtain ⟨t, ht, i, hi, hrow, hcol, c', hc', rfl⟩ := hv.exists_query ha hb hc
    refine ⟨t, ht, i, hi, ?_, ?_, ?_⟩
    · rw [pairIdx, hrow, hcol, hdivmod]
    · refine (acc_iff hv ht hi).2 ⟨c', hc', ?_⟩
      rw [sumAt, hrow, hcol, hdivmod, hzero]
      exact dvd_zero _
    · refine (hit_iff hi).2 ⟨c', hc', ?_⟩
      rw [sumAt, hrow, hcol, hdivmod]
      exact hzero

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/InstanceFacts.lean (sum_execs_le)
/-- **The number of scans of the all-edges host**: each one fails or raises the number of flags that
are 1, and there are `n²` flags. -/
theorem sum_execsAE_le (hv : X.Valid) :
    ∑ t ∈ Finset.range X.m, X.execsAE t ≤ ∑ t ∈ Finset.range X.m, X.fails t + X.n * X.n := by
  have key : ∀ T ≤ X.m, ∑ t ∈ Finset.range T, X.execsAE t + ones (X.flagsAt 0) ≤
      ∑ t ∈ Finset.range T, X.fails t + ones (X.flagsAt T) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      intro hT
      have : X.execsAE T + ones (X.flagsAt T) ≤ X.fails T + ones (X.flagsAt (T + 1)) :=
        aeExecs_add_ones_le (X.flagsAt T) fun i hi => by
          rw [length_flagsAt]
          exact hv.pairIdx_lt (by omega) hi
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have := ih (by omega)
      omega
  have hle := ones_le_length (X.flagsAt X.m)
  rw [length_flagsAt] at hle
  have := key X.m le_rfl
  omega

end HostData


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



variable {lim : Limits} {P : Program} {d : ℕ}

namespace ScanPairsAE

/-- The locals of `scanPairsAE`.  The arguments: the addresses of the answers and of the rows and
the columns of the query pairs, their number `w`, the address of the flags, the addresses of the
three arrays of weights, `n`, and the first vertex and the number of vertices of the piece.  Then
the counter, the address of the flag of the current pair, and the result of its scan. -/
abbrev Out : ℕ := 0
@[inherit_doc Out] abbrev Rows : ℕ := 1
@[inherit_doc Out] abbrev Cols : ℕ := 2
@[inherit_doc Out] abbrev Num : ℕ := 3
@[inherit_doc Out] abbrev Flg : ℕ := 4
@[inherit_doc Out] abbrev AdrAB : ℕ := 5
@[inherit_doc Out] abbrev AdrBC : ℕ := 6
@[inherit_doc Out] abbrev AdrAC : ℕ := 7
@[inherit_doc Out] abbrev Size : ℕ := 8
@[inherit_doc Out] abbrev First : ℕ := 9
@[inherit_doc Out] abbrev Len : ℕ := 10
@[inherit_doc Out] abbrev Cnt : ℕ := 11
@[inherit_doc Out] abbrev Idx : ℕ := 12
@[inherit_doc Out] abbrev Res : ℕ := 13

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

variable {pScan : ℕ} {μ : ℕ → ℤ} {out qa qb w ab bc ac n c0 len U flg : ℕ}
  {OUT AB BC AC F : List ℤ} {QA QB : List ℕ}

/-- What `scanPairsAE` assumes about the flags: `n²` cells at `flg`, within the memory and apart
from the three arrays of weights. -/
structure FlagsAt (lim : Limits) (μ : ℕ → ℤ) (flg ab bc ac n : ℕ) (F : List ℤ) : Prop where
  len : F.length = n * n
  seg : Seg μ flg F
  below : flg + n * n ≤ lim.space
  apartAB : Apart flg (n * n) ab (n * n)
  apartBC : Apart flg (n * n) bc (n * n)
  apartAC : Apart flg (n * n) ac (n * n)

/-- The state of `scanPairsAE` when `i` query pairs have been treated and the counter is `j`. -/
def scanPairsAEState (μ : ℕ → ℤ) (out qa qb w flg ab bc ac n c0 len : ℕ) (OUT AB BC AC F : List ℤ)
    (QA QB : List ℕ) (i j : ℕ) (idx res : ℤ) : State :=
  ⟨frame [out, qa, qb, w, flg, ab, bc, ac, n, c0, len, j, idx, res],
    wrote μ flg
      (fun q => (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i).getD q 0)
      (n * n)⟩

/-- The flags after `i` query pairs are a segment of `n²` cells at `flg`. -/
theorem seg_aeStep (G : FlagsAt lim μ flg ab bc ac n F) (i : ℕ) :
    Seg (wrote μ flg
      (fun q => (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i).getD q 0)
      (n * n)) flg (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i) := by
  intro q hq
  rw [length_aeStep, G.len] at hq
  rw [wrote_done hq, List.getD_eq_getElem]

/-- The weights are not touched by the flags. -/
theorem weights_wrote (C : Weights lim μ ab bc ac n U AB BC AC)
    (G : FlagsAt lim μ flg ab bc ac n F) (f : ℕ → ℤ) :
    Weights lim (wrote μ flg f (n * n)) ab bc ac n U AB BC AC := by
  light_facts C C.arrAB C.arrBC C.arrAC G
  exact
    { C with
      arrAB := C.arrAB.keep fun b hb => wrote_rest (by omega)
      arrBC := C.arrBC.keep fun b hb => wrote_rest (by omega)
      arrAC := C.arrAC.keep fun b hb => wrote_rest (by omega) }

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/ScanPairs.lean
/-- One query pair: a scan is made if the pair is accepted and its flag is 0. -/
theorem scanPairsAEStep_spec (hp : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (A : Answers lim μ out qa qb w n OUT QA QB)
    (hA : Apart flg (n * n) out w) (hQA : Apart flg (n * n) qa w) (hQB : Apart flg (n * n) qb w)
    (G : FlagsAt lim μ flg ab bc ac n F) (hd : d < lim.depth) (hc : c0 + len ≤ n) {i : ℕ}
    (hi : i < w) (idx res : ℤ) :
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
  have hreadQA : μ₁ (qa + i) = (QA.getD i 0 : ℕ) := by
    rw [hμ₁, wrote_rest (by omega)]; exact A.arrQA.read hi
  have hreadQB : μ₁ (qb + i) = (QB.getD i 0 : ℕ) := by
    rw [hμ₁, wrote_rest (by omega)]; exact A.arrQB.read hi
  have ha := A.arrQA.getD_lt hi
  have hb := A.arrQB.getD_lt hi
  have hidx : idxOf n QA QB i < n * n := Nat.mul_add_lt_mul ha hb
  have hlenS : idxOf n QA QB i <
      (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i).length := by
    rw [length_aeStep, G.len]; exact hidx
  have hreadF : μ₁ (flg + idxOf n QA QB i) =
      (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i).getD
        (idxOf n QA QB i) 0 := by
    rw [hμ₁, wrote_done hidx]
  have C₁ := weights_wrote C G (fun q => (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len)
    (idxOf n QA QB) F i).getD q 0)
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
    rw [show (flg : ℤ) + ((a : ℤ) * (n : ℤ) + (b : ℤ)) = ((flg + (a * n + b) : ℕ) : ℤ) by
      push_cast; ring, Int.toNat_natCast]
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
    light_call (scan_meets hp C₁ ha hb hc) using hreadQA, hreadQB, hz, hcell0, tScanCallAE with
      _ _ ⟨rfl, rfl⟩
    rw [flag_eq_bit]
    light_store (flg + (a * n + b) : ℕ) (bit (scanHit n AB BC AC a b c0 len)) using hz, hcell0,
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
        rw [wrote_done (by omega), wrote_done (by omega), getD_set_ne _ (by omega)]
      · have hout : Outside flg (n * n) y := by simp only [Inside, Outside] at hin ⊢; omega
        rw [wrote_rest hout, wrote_rest hout]
  · refine Ends.iteLast (fun h => absurd h (by simp [haddr, hreadF, hcell0])) fun _ =>
      Ends.skip ⟨(flg + (a * n + b) : ℕ), res, ?_⟩
    rw [hμ₁]
    simp [hcell0]

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/ScanPairs.lean
/-- The time of the rounds, added up. -/
theorem sum_scanPairsAE_rounds (acc hit : ℕ → Bool) (idx : ℕ → ℕ) (F : List ℤ) (len w : ℕ) :
    ∑ i ∈ Finset.range w, (4 + (64 + if aeExec acc hit idx F i then tScanCallAE len else 0))
      = 68 * w + tScanCallAE len * aeExecs acc hit idx F w := by
  induction w with
  | zero => simp [aeExecs]
  | succ w ih =>
    rw [Finset.sum_range_succ, ih, aeExecs_succ]
    split_ifs <;> ring

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/ScanPairs.lean
/-- **scanPairsAE** treats the `w` query pairs of an instance: the flags become
`aeStep … F w`, no other cell changes, and the time depends on the number of scans that are made. -/
theorem scanPairsAE_spec (hp : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (A : Answers lim μ out qa qb w n OUT QA QB)
    (hA : Apart flg (n * n) out w) (hQA : Apart flg (n * n) qa w) (hQB : Apart flg (n * n) qb w)
    (G : FlagsAt lim μ flg ab bc ac n F) (hd : d < lim.depth) (hc : c0 + len ≤ n) :
    Ends lim P d (scanPairsAEBody pScan)
      ⟨frame [out, qa, qb, w, flg, ab, bc, ac, n, c0, len], μ⟩
      (tScanPairsAE w len (aeExecs (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB)
        F w)) fun σ' =>
      Seg σ'.mem flg (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F w) ∧
        SameOutside μ σ'.mem flg (n * n) := by
  light_facts C C.arrAB C.arrBC C.arrAC
  light_facts A A.arrOUT A.arrQA A.arrQB
  light_facts G
  have := sum_scanPairsAE_rounds (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB)
    F len w
  unfold tScanPairsAE tAnswersAE
  -- i := 0
  light_set (0 : ℕ)
  -- while i < w
  refine (Ends.while (fun i σ => ∃ idx res, σ = scanPairsAEState μ out qa qb w flg ab bc ac n c0
    len OUT AB BC AC F QA QB i i idx res) w
    (fun i => 64 + if aeExec (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i then
      tScanCallAE len else 0) ?start ?round ?done).mono
    (by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega) fun _ h => h
  case start =>
    have hmem : μ = wrote μ flg (fun q => F.getD q 0) (n * n) := by
      funext y
      by_cases hin : Inside flg (n * n) y
      · obtain ⟨q, rfl⟩ : ∃ q, y = flg + q := ⟨y - flg, by omega⟩
        rw [wrote_done (by omega), G.seg.getD (by rw [G.len]; omega)]
      · rw [wrote_rest (by simp only [Inside, Outside] at hin ⊢; omega)]
    refine ⟨0, 0, ?_⟩
    simp only [scanPairsAEState, aeStep_zero, ← hmem]
    simpa using (frame_append_zeros [(out : ℤ), qa, qb, w, flg, ab, bc, ac, n, c0, len, 0] 2).symm
  case round =>
    rintro i _ hi ⟨idx, res, rfl⟩
    refine ⟨by simp, by simp [scanPairsAEState]; omega, ?_⟩
    -- the query pair number i; then i := i + 1
    refine Ends.next _ ((scanPairsAEStep_spec hp C A hA hQA hQB G hd hc hi idx res).mono le_rfl
      ?_) (by omega)
    rintro _ ⟨idx', res', rfl⟩
    unfold scanPairsAEState
    light_set (i + 1 : ℕ)
    exact ⟨idx', res', rfl⟩
  case done =>
    rintro _ ⟨idx, res, rfl⟩
    refine ⟨by simp, by simp [scanPairsAEState], seg_aeStep G w, ?_⟩
    simp only [scanPairsAEState]
    exact sameOutside_wrote le_rfl

end

end Light.Sec3

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

theorem hasZero_iff (n : ℕ) (AB BC AC : List ℤ) :
    hasZero n AB BC AC = true ↔ (triOf n AB BC AC).HasZeroTriangle := by
  unfold hasZero TriangleInstance.HasZeroTriangle TriangleInstance.IsZeroTriangle TriangleInstance.S
  simp only [List.any_eq_true, List.mem_range, scanHit, decide_eq_true_eq]
  exact ⟨fun ⟨a, ha, b, hb, c, hc, h⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, by simpa [triOf] using h⟩,
    fun ⟨a, b, c, h⟩ => ⟨a, a.2, b, b.2, c, c.2, by simpa [triOf] using h⟩⟩

def bruteNeed (_n U : ℕ) : Need := ⟨3 * U + 1, 0, 1⟩

theorem _root_.Light.TriInst.Pre.weights {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hok : (bruteNeed x.n x.U).Ok lim fr d) :
    Weights lim μ x.ab x.bc x.ac x.n x.U x.AB x.BC x.AC where
  hw := hok.space
  hU := by exact_mod_cast hok.word
  arrAB := ⟨hpre.lenAB, hpre.segAB, hpre.leAB, hpre.belowAB.trans hok.cells⟩
  arrBC := ⟨hpre.lenBC, hpre.segBC, hpre.leBC, hpre.belowBC.trans hok.cells⟩
  arrAC := ⟨hpre.lenAC, hpre.segAC, hpre.leAC, hpre.belowAC.trans hok.cells⟩

def bruteAEPair (pScan : ℕ) : Stmt :=
  .call pScan [v 2, v 3, v 4, v 0, v 6, v 7, k 0, v 0] 9 ;;
  .store (v 5 +' v 6 *' v 0 +' v 7) (v 9)

def bruteAEInner (pScan : ℕ) : Stmt := Stmt.for 7 (v 0) (bruteAEPair pScan)

def bruteAEBody (pScan : ℕ) : Stmt :=
  Stmt.for 6 (v 0) (bruteAEInner pScan) ;; .set 0 (v 5)

/-- The time of bruteAE. -/
def tBruteAE (n : ℕ) : ℕ := 110 * n ^ 3 + 100

/-- The flags of the pairs `(a', b')` before `(a, b)` in the order of the rows, written from `fr`:
the cells `fr + q` for `q < a n + b`. -/
noncomputable def bruteAEMem (μ : ℕ → ℤ) (fr n : ℕ) (AB BC AC : List ℤ) (q : ℕ) : ℕ → ℤ :=
  wrote μ fr (fun q => (aeFlags n AB BC AC).getD q 0) q

section

variable {pScan : ℕ} {μ : ℕ → ℤ} {ab bc ac n a U fr : ℕ} {AB BC AC : List ℤ}

/-- Writing the flag of `(a, b)` after those of the earlier pairs. -/
theorem bruteAEMem_succ (ha : a < n) {b : ℕ} (hb : b < n) :
    Function.update (bruteAEMem μ fr n AB BC AC (a * n + b)) (fr + (a * n + b))
      (bit (scanHit n AB BC AC a b 0 n)) = bruteAEMem μ fr n AB BC AC (a * n + b + 1) := by
  rw [bruteAEMem, bruteAEMem, ← wrote_succ, aeFlags_getD_eq_bit_scanHit _ _ _ ha hb]

/-- The flags are not where the weights are. -/
theorem weights_bruteAEMem (C : Weights lim μ ab bc ac n U AB BC AC) (hfr : ab + n * n ≤ fr)
    (hfr' : bc + n * n ≤ fr) (hfr'' : ac + n * n ≤ fr) (q : ℕ) :
    Weights lim (bruteAEMem μ fr n AB BC AC q) ab bc ac n U AB BC AC := by
  light_facts C C.arrAB C.arrBC C.arrAC
  exact
    { C with
      arrAB := C.arrAB.keep fun y hy => wrote_rest (by omega)
      arrBC := C.arrBC.keep fun y hy => wrote_rest (by omega)
      arrAC := C.arrAC.keep fun y hy => wrote_rest (by omega) }

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/BruteForce.lean
/-- One pair: its flag is written. -/
theorem bruteAEPair_spec {b : ℕ} {r : ℤ} (hP : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (hfr : ab + n * n ≤ fr) (hfr' : bc + n * n ≤ fr)
    (hfr'' : ac + n * n ≤ fr) (hlim : fr + n * n ≤ lim.space) (hd : d < lim.depth) (ha : a < n)
    (hb : b < n) :
    Ends lim P d (bruteAEPair pScan)
      ⟨frame [n, U, ab, bc, ac, fr, a, b, 0, r], bruteAEMem μ fr n AB BC AC (a * n + b)⟩
      (tScan n + 24) fun σ' => ∃ r', σ' = ⟨frame [n, U, ab, bc, ac, fr, a, b, 0, r'],
        bruteAEMem μ fr n AB BC AC (a * n + b + 1)⟩ := by
  light_facts C C.arrAB C.arrBC C.arrAC
  have C' := weights_bruteAEMem C hfr hfr' hfr'' (a * n + b)
  have : a * n + b < n * n := Nat.mul_add_lt_mul ha hb
  -- res := scan(ab, bc, ac, n, a, b, 0, n)
  light_call (scan_meets hP C' ha hb (c0 := 0) (Nat.zero_add n).le) with _ _ ⟨rfl, rfl⟩
  rw [flag_eq_bit]
  -- M (fr + a n + b) := res
  refine Ends.storeTo (fr + (a * n + b) : ℕ) (bit (scanHit n AB BC AC a b 0 n))
    ⟨bit (scanHit n AB BC AC a b 0 n), ?_⟩
  rw [bruteAEMem_succ ha hb]
  simp

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/BruteForce.lean
/-- The inner loop: all `b` for one `a`. -/
theorem bruteAEInner_spec {b₀ r₀ : ℤ} (hP : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (hfr : ab + n * n ≤ fr) (hfr' : bc + n * n ≤ fr)
    (hfr'' : ac + n * n ≤ fr) (hlim : fr + n * n ≤ lim.space) (hd : d < lim.depth)
    (hn : n ≤ lim.space) (ha : a < n) :
    Ends lim P d (bruteAEInner pScan)
      ⟨frame [n, U, ab, bc, ac, fr, a, b₀, 0, r₀], bruteAEMem μ fr n AB BC AC (a * n)⟩
      (n * (24 * n + 67) + 6) fun σ' => ∃ r, σ' = ⟨frame [n, U, ab, bc, ac, fr, a, n, 0, r],
        bruteAEMem μ fr n AB BC AC ((a + 1) * n)⟩ := by
  have hw := C.hw
  -- for b < n
  refine Ends.for (fun b σ => ∃ r, σ = ⟨frame [n, U, ab, bc, ac, fr, a, b, 0, r],
    bruteAEMem μ fr n AB BC AC (a * n + b)⟩) n (tScan n + 24)
    ?start ?round ?done ?bound (hT := by simp [tScan]; ring_nf; omega)
  case start => exact ⟨r₀, by simp [update_frame_setLocal]⟩
  case bound =>
    rintro b _ - - ⟨r, rfl⟩
    simp
  case round =>
    rintro b _ hb - ⟨r, rfl⟩
    refine (bruteAEPair_spec hP C hfr hfr' hfr'' hlim hd ha hb).mono le_rfl ?_
    rintro _ ⟨r', rfl⟩
    exact ⟨by simp, r', by simp [update_frame_setLocal, Nat.add_assoc]⟩
  case done =>
    rintro _ - ⟨r, rfl⟩
    exact ⟨r, by rw [Nat.add_mul, Nat.one_mul]⟩

end

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/BruteForce.lean
/-- The steps of the two loops of bruteAE are within its time. -/
theorem tBruteAE_ge (n : ℕ) : n * (1 + (n * (24 * n + 67) + 6) + 7) + 8 ≤ tBruteAE n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tBruteAE]
  · have hsq : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn (by omega)
    have hlin : n ≤ n ^ 3 := Nat.le_self_pow (by omega) n
    rw [show n * (1 + (n * (24 * n + 67) + 6) + 7) = 24 * n ^ 3 + 67 * n ^ 2 + 14 * n by ring,
      tBruteAE]
    omega

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/BruteForce.lean
/-- **The brute force for all-edges Exact Triangle.**  In any program that holds `scanBody` as its
procedure number `pScan`, `bruteAEBody pScan` ends within `tBruteAE n` steps, writes the `n²` flags
of the instance to the cells from `fr`, changes no other cell, and returns `fr`. -/
theorem bruteAE_spec {pScan : ℕ} (hP : P[pScan]? = some scanBody) (x : TriInst) (μ : ℕ → ℤ)
    (fr : ℕ) (hpre : x.Pre μ fr) (hok : (bruteNeed x.n x.U).Ok lim fr d)
    (hlim : fr + x.n * x.n ≤ lim.space) :
    Ends lim P d (bruteAEBody pScan) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩ (tBruteAE x.n)
      fun σ' => σ'.loc 0 = fr ∧ Seg σ'.mem fr (aeFlags x.n x.AB x.BC x.AC) ∧ Kept μ σ'.mem fr := by
  have C := hpre.weights hok
  have hw := C.hw
  have hd : d < lim.depth := hok.depth
  have hn : x.n ≤ lim.space :=
    (Nat.le_mul_of_pos_left _ hpre.n_pos).trans ((Nat.le_add_left _ _).trans C.arrAB.below)
  have := tBruteAE_ge x.n
  have hfr := hpre.belowAB
  have hfr' := hpre.belowBC
  have hfr'' := hpre.belowAC
  unfold bruteAEBody
  -- for a < n
  refine Ends.next _ (Ends.for (fun a σ => ∃ b r, σ = ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr, a, b,
    0, r], bruteAEMem μ fr x.n x.AB x.BC x.AC (a * x.n)⟩) x.n (x.n * (24 * x.n + 67) + 6)
    ?start ?round ?done ?bound (hT := le_rfl)) (by simp; omega)
  case start =>
    refine ⟨0, 0, ?_⟩
    simp only [bruteAEMem, Nat.zero_mul, wrote_zero]
    simpa [update_frame_setLocal] using
      (frame_append_zeros [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, fr, 0] 3).symm
  case bound =>
    rintro a _ - - ⟨b, r, rfl⟩
    simp
  case round =>
    rintro a _ ha - ⟨b, r, rfl⟩
    refine (bruteAEInner_spec hP C hfr hfr' hfr'' hlim hd hn ha).mono le_rfl ?_
    rintro _ ⟨r', rfl⟩
    exact ⟨by simp, x.n, r', by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ - ⟨b, r, rfl⟩
    -- return fr
    refine Ends.setTo fr ⟨by simp, ?_, ?_⟩ (by simp) (by simp; omega)
    · intro q hq
      rw [length_aeFlags] at hq
      change bruteAEMem μ fr x.n x.AB x.BC x.AC (x.n * x.n) (fr + q) = _
      rw [bruteAEMem, wrote_done hq, List.getD_eq_getElem]
    · intro y hy
      change bruteAEMem μ fr x.n x.AB x.BC x.AC (x.n * x.n) y = μ y
      exact wrote_rest (by simp only [Outside]; omega)

/-- The specification of `bruteAE`, for its callers: the flags stand at `fr`, nothing below `fr`
changes, and the result is `fr`. -/
theorem bruteAE_meets {p pScan : ℕ} (hB : P[p]? = some (bruteAEBody pScan))
    (hP : P[pScan]? = some scanBody) (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (bruteNeed x.n x.U).Ok lim fr d) (hlim : fr + x.n * x.n ≤ lim.space) :
    Meets lim P p d [x.n, x.U, x.ab, x.bc, x.ac, fr] μ (tBruteAE x.n) fun r μ' =>
      r = fr ∧ Seg μ' fr (aeFlags x.n x.AB x.BC x.AC) ∧ Kept μ μ' fr :=
  Meets.of_body hB (bruteAE_spec hP x μ fr hpre hok hlim)

end ImprovedExponents.AllEdges




namespace ImprovedExponents.HostMid

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

def midSize (D g : ℕ) : ℕ := pieceSizeNat D g * Nat.sqrt D

theorem pieceSizeNat_le_sqrt (D g : ℕ) : pieceSizeNat D g ≤ Nat.sqrt D := by
  unfold pieceSizeNat
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  · exact (ceilDiv_le_iff_le_smul hg).2 (by simpa using Nat.le_mul_of_pos_left _ hg)

theorem midSize_le (D g : ℕ) : midSize D g ≤ D :=
  (Nat.mul_le_mul_right _ (pieceSizeNat_le_sqrt D g)).trans (Nat.sqrt_le D)

theorem one_le_midSize {D g : ℕ} (hD : 16 ≤ D) (hg : 1 ≤ g) : 1 ≤ midSize D g := by
  have : 4 ≤ Nat.sqrt D := Nat.le_sqrt.2 (by omega)
  have hpiece : 1 ≤ pieceSizeNat D g := (Nat.lt_ceilDiv_iff hg).2 (by omega)
  exact Nat.mul_pos hpiece (by omega)

def midArgs (G : ℕ → ℕ) : List ℕ → List ℕ
  | [n, D, w] => [n, midSize D (G D), w]
  | ps => ps

theorem polyBound_midArgs_le (G : ℕ → ℕ) (s k : ℕ) (ps : List ℕ) :
    polyBound s k (midArgs G ps) ≤ polyBound s k ps := by
  unfold midArgs
  split
  · simp only [polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    gcongr
    exact midSize_le _ _
  · exact le_rfl

theorem polyNeedN_midArgs {need : List ℕ → Need} (G : ℕ → ℕ) (h : PolyNeedN need) :
    PolyNeedN fun ps => need (midArgs G ps) := by
  obtain ⟨s, k, hle⟩ := h
  exact ⟨s, k, fun ps => ⟨(hle _).1.trans (polyBound_midArgs_le G s k ps),
    (hle _).2.1.trans (polyBound_midArgs_le G s k ps),
    (hle _).2.2.trans (polyBound_midArgs_le G s k ps)⟩⟩

open Et17 in
def et17Sizes' (ν : Et17Nums) : Stmt :=
  .call ν.pChoose [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v ParD, v Free] ThePrime ;;
  .call ν.pCap [v Size, v ParD] Cap ;;
  .call ν.pCeil [v RootD, v ParG] PieceLen ;;
  .call ν.pCeil [v Size, v PieceLen] NumPieces ;;
  .call ν.pBitLen [v Bound] Bits ;;
  .set ParD (v PieceLen *' v RootD) ;;
  et17Addr

def hostNeedAt' (a b : ℕ) (need : List ℕ → Need) (n U D g : ℕ) : Need :=
  ⟨hostWord a b n U D g + (supNeed need n (midSize D g) (queryCapNat n D)).word,
    chooseCells n U D + hostLayout n U D + (supNeed need n (midSize D g) (queryCapNat n D)).cells
      + 2,
    2 * Nat.clog 2 n + 8 + (supNeed need n (midSize D g) (queryCapNat n D)).depth⟩

def hostNeed' (Dfun Gfun wD wG : ℕ → ℕ) (need : List ℕ → Need) (n U : ℕ) : Need :=
  hostNeedAt' (wD n) (wG (Dfun n)) need n U (Dfun n) (Gfun (Dfun n))

def hostData' (x : TriInst) (D g : ℕ) : HostData :=
  ⟨x.n, midSize D g, chosenPrime x.n D x.AB x.BC x.AC, pieceSizeNat D g, queryCapNat x.n D, x.AB,
    x.BC, x.AC⟩

def et17LocB' (x : TriInst) (fr D g : ℕ) : List ℤ :=
  Et17.locals x (hostData' x D g) fr g (Nat.sqrt D : ℕ) 0 0

theorem hostData'_p_le (x : TriInst) {D : ℕ} (g : ℕ) (hD : 16 ≤ D) :
    (hostData' x D g).p ≤ Nat.sqrt D :=
  chosenPrime_le_sqrt x.AB x.BC x.AC hD

theorem hostData'_m_le {x : TriInst} {D g : ℕ} (h : BigCase x.n D g) :
    (hostData' x D g).m ≤ 4 * x.n * g :=
  HostData.m_le (BC := x.BC) (AC := x.AC) h (chosenPrime_mem x.AB x.BC x.AC h.sixteen_le)

theorem hostData'_valid {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ} (hpre : x.Pre μ fr)
    (h : BigCase x.n D g) : (hostData' x D g).Valid := by
  have hD := h.sixteen_le
  have hDn := h.le_n
  have hg := h.one_le_g
  have hp := chosenPrime_mem (n := x.n) x.AB x.BC x.AC hD
  have : 4 ≤ Nat.sqrt D := Nat.le_sqrt.2 (by omega)
  exact
    { n_pos := le_trans (by norm_num) (hD.trans hDn)
      p_pos := (mem_primesInRange.mp hp).1.one_le
      q_pos := (Nat.lt_ceilDiv_iff hg).2 (by omega)
      cap_pos := by
        simp only [hostData']
        rw [queryCapNat, Nat.le_sqrt, Nat.le_div_iff_mul_le (by omega)]
        have : x.n ≤ x.n ^ 4 := Nat.le_self_pow (by norm_num) x.n
        omega
      qp_le := Nat.mul_le_mul_left _ (hostData'_p_le x g hD)
      lenAB := hpre.lenAB
      lenBC := hpre.lenBC
      lenAC := hpre.lenAC }

/-! ## The addresses -/

/-- The arrays of the variant fit into the cells that upstream's `hostLayout` counts. -/
theorem aFr_le' {x : TriInst} {D g : ℕ} (hD : 16 ≤ D) (fr : ℕ) :
    aFr (hostData' x D g) x.U fr ≤ fr + hostLayout x.n x.U D := by
  have : chosenPrime x.n D x.AB x.BC x.AC ≤ Nat.sqrt D := chosenPrime_le_sqrt x.AB x.BC x.AC hD
  have : x.n * midSize D g ≤ x.n * D := Nat.mul_le_mul_left _ (midSize_le D g)
  simp only [aFr, aOut, aY, aX, aCw, aCl, aCr, aQj, aQi, aCur, aCls, aRac, aRbc, aRab, hostData']
  unfold hostLayout
  omega

/-! ## The limits -/

/-- What hostLoop asks of the limits. -/
theorem hostLim_of_ok' {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {x : TriInst}
    {fr D g : ℕ} (hbig : BigCase x.n D g) (hok : (hostNeedAt' a b need x.n x.U D g).Ok lim fr d) :
    HostLim lim (d + 1) (hostData' x D g) x.U (hostAddr x (hostData' x D g) fr) need := by
  have hD : 16 ≤ D := hbig.sixteen_le
  have hok0 : (hostNeedAt a b (fun ps => need (midArgs (fun _ => g) ps)) x.n x.U D g).Ok lim fr d :=
    hok
  have : fr + (chooseCells x.n x.U D + hostLayout x.n x.U D
      + (supNeed need x.n (midSize D g) (queryCapNat x.n D)).cells + 2) ≤ lim.space := hok.cells
  have : d + (2 * Nat.clog 2 x.n + 8
      + (supNeed need x.n (midSize D g) (queryCapNat x.n D)).depth) ≤ lim.depth := hok.depth
  have hword : ((hostWord a b x.n x.U D g
      + (supNeed need x.n (midSize D g) (queryCapNat x.n D)).word : ℕ) : ℤ) ≤ lim.word := hok.word
  have := aFr_le' (x := x) (g := g) hD fr
  have := hostData'_p_le x g hD
  have hm := hostData'_m_le hbig
  have : 2 * Nat.sqrt D ≤ hostLayout x.n x.U D := by unfold hostLayout; omega
  exact
    { space := hok.space
      fr := by change aFr (hostData' x D g) x.U fr < lim.space; omega
      prime := by omega
      count := le_word_of_le_hostWord hok0 (hm.trans (by unfold hostWord; omega))
      step := le_word_of_le_hostWord hok0 (by
        change x.n + pieceSizeNat D g ≤ _
        unfold hostWord
        omega)
      weights := le_word_of_le_hostWord hok0
      depth := by omega
      solver := fun t ht => by
        have : (hostData' x D g).w t ≤ queryCapNat x.n D := (hostData' x D g).w_le_cap ht
        have hmem : (hostData' x D g).w t ∈ Finset.range (queryCapNat x.n D + 1) :=
          Finset.mem_range.2 (by omega)
        have hsword : (need [x.n, midSize D g, (hostData' x D g).w t]).word
            ≤ (supNeed need x.n (midSize D g) (queryCapNat x.n D)).word :=
          Finset.le_sup (f := fun v => (need [x.n, midSize D g, v]).word) hmem
        have : (need [x.n, midSize D g, (hostData' x D g).w t]).cells
            ≤ (supNeed need x.n (midSize D g) (queryCapNat x.n D)).cells :=
          Finset.le_sup (f := fun v => (need [x.n, midSize D g, v]).cells) hmem
        have : (need [x.n, midSize D g, (hostData' x D g).w t]).depth
            ≤ (supNeed need x.n (midSize D g) (queryCapNat x.n D)).depth :=
          Finset.le_sup (f := fun v => (need [x.n, midSize D g, v]).depth) hmem
        change (need [x.n, midSize D g, (hostData' x D g).w t]).Ok lim
          (aFr (hostData' x D g) x.U fr) (d + 1 + 1)
        exact ⟨le_trans (Nat.cast_le.2 (hsword.trans (Nat.le_add_left _ _))) hword, by omega,
          hok.space, by omega⟩ }

/-! ## The first part and the small case -/

variable {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ} {lim : Limits} {d : ℕ}

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/ParametersStage.lean
/-- **The first part of et17**, within the limits of the variant: the parameters, and whether n is
small.  No cell changes. -/
theorem et17Params_spec' (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG) (x : TriInst)
    (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeed' Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Params ν) ⟨frame (et17Loc0 x fr), μ⟩
      (tD x.n + tG (Dfun x.n) + (18 * Nat.sqrt (Dfun x.n) + 12) + 40)
      fun σ' => σ' = ⟨frame (et17LocA x fr (Dfun x.n) (Gfun (Dfun x.n))), μ⟩ := by
  have hn := hpre.n_pos
  have hDpos := C.D_pos x.n hn
  replace hok : (hostNeed Dfun Gfun wD wG (fun ps => need (midArgs Gfun ps)) x.n x.U).Ok lim fr d :=
    hok
  unfold hostNeed at hok
  have hdepth := hok.depth
  simp only [hostNeedAt] at hdepth
  generalize hD : Dfun x.n = D at *
  generalize hg : Gfun D = g at *
  -- The numbers that this part forms fit in a word.
  have hwD : ((wD x.n : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have hwG : ((wG D : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have hsqrt : ((3 * D + 4 : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have : ((16 : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  unfold et17Params et17Loc0 et17LocA
  -- D := Dfun(n); g := Gfun(D)
  light_call (C.dProc lim d x.n μ hn hok.space hwD (by omega)) with _ μ ⟨rfl, rfl⟩
  rw [hD]
  light_call (C.gProc lim d D μ hDpos hok.space hwG (by omega)) with _ μ ⟨rfl, rfl⟩
  rw [hg]
  -- s := sqrt(D)
  light_call (sqrt_meets (K := D) C.hSqrt μ hsqrt) with _ μ ⟨rfl, rfl⟩
  -- the four tests: D < 16, n < D, g < 1, s < g
  refine Ends.block ⟨by simp; omega, ?_⟩
  by_cases hD16 : D < 16 <;> by_cases hnD : x.n < D <;> by_cases hg0 : g = 0 <;>
    by_cases hsg : Nat.sqrt D < g <;> simp [update_frame_setLocal, SmallCase, hD16, hnD, hg0, hsg]

end ImprovedExponents.HostMid




/-!
# The loop over the instances of the all-edges host

Upstream's `hostLoop` (`Host/Loop.lean`) treats the instances of the reduction one after the other:
the two matrices, the solver, and the scans of the accepted pairs, while no zero triangle has been
found.  The all-edges variant `hostLoopAE` keeps `n²` flags, one per pair `(a, b)`, in the `n²`
cells below the free pointer `fr` that the solver gets: it fills them with 0 first, and for every
instance it calls `scanPairsAE` instead of `scanPairs`, which scans an accepted pair whose flag is
still 0 and stores the result in the flag.  The loop returns the address of the flags, and after
all instances the flags are those of all-edges Exact Triangle (`hostLoopAE_spec`).

The text has upstream's twenty arguments and locals; the local `Found` holds the address of the
flags.  The specifications of upstream's parts that do not involve the scans (`hostParams_spec`,
`writeX_meets`, `writeY_meets`, `solver_meets`, `hostNext_spec`) are used as they are.
-/

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec HostLocal

variable {lim : Limits} {d : ℕ}

/-! ## The text -/

/-- The four calls for one instance: the two matrices, the solver, the scans with the flags. -/
def hostCallsAE (pS pWriteX pWriteY pScanPairsAE : ℕ) : Stmt :=
  .call pWriteX [v MatX, v ResAC, v Size, v ParD, v ThePrime, v PieceStart, v Len, v Residue]
    Unused ;;
  .call pWriteY [v MatY, v ResBC, v Size, v ParD, v ThePrime, v PieceStart, v Len] Unused ;;
  .call pS [v Size, v ParD, v NumPairs, k 1, v MatX, v MatY, v Rows +' v Start, v Cols +' v Start,
    v AdrOut, v SolverFree] Unused ;;
  .call pScanPairsAE [v AdrOut, v Rows +' v Start, v Cols +' v Start, v NumPairs, v Found, v AdrAB,
    v AdrBC, v AdrAC, v Size, v PieceStart, v Len] Unused

/-- One round of hostLoopAE. -/
def hostRoundAE (pS pWriteX pWriteY pScanPairsAE : ℕ) : Stmt :=
  hostParams ;;
  hostCallsAE pS pWriteX pWriteY pScanPairsAE ;;
  hostNext

/-- hostLoopAE(n, D, p, q, chunkCount, m, ab, bc, ac, rac, rbc, qi, qj, cr, cl, cw, x, y, out, fr):
the flags are the `n²` cells below `fr`; they are returned. -/
def hostLoopAEBody (pS pWriteX pWriteY pScanPairsAE pFill : ℕ) : Stmt :=
  .set Inst (k 0) ;; .set ChunkNo (k 0) ;; .set PieceStart (k 0) ;;
  .set Found (v SolverFree -' (v Size *' v Size)) ;;
  .call pFill [v Found, v Size *' v Size, k 0] Unused ;;
  .while (v Inst <' v NumInst) (hostRoundAE pS pWriteX pWriteY pScanPairsAE) ;;
  .set 0 (v Found)

/-- The number of steps of hostLoopAE, if the solver takes Tn. -/
def tHostLoopAE (Tn : List ℕ → ℕ) (X : HostData) : ℕ :=
  (∑ t ∈ Finset.range X.m, (tWrites X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
    tScanPairsAE (X.w t) (X.len t) (X.execsAE t))) + fillTime (X.n * X.n) + 40

/-- The context of hostLoopAE: upstream's `HostCtx` (the solver, the two write routines, the scan),
and the all-edges scan of the pairs and the fill routine. -/
structure HostCtxAE (P₀ R : Program) (pS pWriteX pWriteY pScan pScanPairsAE pFill : ℕ)
    (Tn : List ℕ → ℕ) (need : List ℕ → Need) : Prop extends
    HostCtx P₀ R pS pWriteX pWriteY pScan Tn need where
  scanPairsAE : (P₀ ++ R)[pScanPairsAE]? = some (scanPairsAEBody pScan)
  fill : (P₀ ++ R)[pFill]? = some fillBody

/-! ## The calls -/

variable {P₀ R : Program} {pS pWriteX pWriteY pScan pScanPairsAE pFill : ℕ}
  {Tn : List ℕ → ℕ} {need : List ℕ → Need} {X : HostData} {U : ℕ} {A : HostAddr} {μ μ' : ℕ → ℤ}
  {t flg : ℕ}

/-- The time of the four calls. -/
def tCallsAE (Tn : List ℕ → ℕ) (X : HostData) (t : ℕ) : ℕ :=
  tWriteX X.n X.D (X.len t) + tWriteY X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
    tScanPairsAE (X.w t) (X.len t) (X.execsAE t) + 52

/-- The flags of the all-edges host lie in the `n²` cells below the solver's free pointer, above
the answers of every instance. -/
structure FlagsPlace (X : HostData) (A : HostAddr) (flg : ℕ) : Prop where
  fr : flg + X.n * X.n = A.fr
  x : A.x ≤ flg
  out : ∀ t < X.m, A.out + X.w t ≤ flg

/-- The call of scanPairsAE for instance t, once the solver has answered: the flags are updated,
and nothing else changes. -/
theorem HostCtxAE.scanPairsAE_meets
    (C : HostCtxAE P₀ R pS pWriteX pWriteY pScan pScanPairsAE pFill Tn need)
    (S : HostSetting lim d X U A need μ μ') (hF : FlagsPlace X A flg) (ht : t < X.m)
    (hans : Seg μ' A.out (X.ans t)) (hflags : Seg μ' flg (X.flagsAt t)) :
    Meets lim (P₀ ++ R) pScanPairsAE (d + 1)
      [(A.out : ℤ), (A.qi + X.lo t : ℕ), (A.qj + X.lo t : ℕ), X.w t, flg, A.ab, A.bc, A.ac, X.n,
        X.c0 t, X.len t] μ' (tScanPairsAE (X.w t) (X.len t) (X.execsAE t))
      fun _ μ₁ => Seg μ₁ flg (X.flagsAt (t + 1)) ∧ SameOutside μ' μ₁ flg (X.n * X.n) := by
  have := S.places ht
  have hout := hF.out t ht
  have := hF.fr
  have hcongr : ∀ i < X.w t, accOf (X.ans t) i = X.acc t i ∧
      hitOf X.n X.AB X.BC X.AC (X.WI t) (X.WJ t) (X.c0 t) (X.len t) i = X.hit t i ∧
      idxOf X.n (X.WI t) (X.WJ t) i = X.pairIdx t i :=
    fun i hi => ⟨rfl, rfl, (X.pairIdx_eq hi).symm⟩
  have hstep := aeStep_congr (X.flagsAt t) hcongr
  have hexecs := aeExecs_congr (X.flagsAt t) hcongr
  refine Meets.of_body C.scanPairsAE ((scanPairsAE_spec C.scan (S.weights ht) (S.answers ht hans)
    (Or.inr hout) (Or.inr (by omega)) (Or.inr (by omega))
    { len := X.length_flagsAt t, seg := hflags, below := by omega
      apartAB := Or.inr (by omega), apartBC := Or.inr (by omega), apartAC := Or.inr (by omega) }
    (by omega) (S.ok.valid.piece_le ht)).mono (le_of_eq ?_) ?_)
  · rw [hexecs]
    rfl
  · rintro σ' ⟨hseg, hsame⟩
    refine ⟨?_, hsame⟩
    rw [HostData.flagsAt, HostData.flagsStep_def, ← hstep]
    exact hseg

/-- **The four calls for instance t**: the flags of instance `t + 1` are in place. -/
theorem hostCallsAE_spec
    (C : HostCtxAE P₀ R pS pWriteX pWriteY pScan pScanPairsAE pFill Tn need)
    (S : HostSetting lim d X U A need μ μ') (hF : FlagsPlace X A flg) (ht : t < X.m)
    (hflags : Seg μ' flg (X.flagsAt t)) (ch : ℕ) (res : ℤ) :
    Ends lim (P₀ ++ R) d (hostCallsAE pS pWriteX pWriteY pScanPairsAE)
      (hostState X A t ch (X.c0 t) flg (X.len t) (X.rho t) (X.lo t) (X.w t) res μ')
      (tCallsAE Tn X t) fun σ => ∃ (res' : ℤ) (μ'' : ℕ → ℤ),
        σ = hostState X A t ch (X.c0 t) flg (X.len t) (X.rho t) (X.lo t) (X.w t) res' μ'' ∧
          HostSetting lim d X U A need μ μ'' ∧ Seg μ'' flg (X.flagsAt (t + 1)) := by
  have := S.places ht
  have := hF.out t ht
  have := hF.fr
  have hlen := X.length_flagsAt t
  unfold hostCallsAE tCallsAE
  -- res := writeX(x, rac, n, D, p, c0, len, rho)
  light_call (C.writeX_meets S ht) with r₁ μ₁ ⟨hX, hrest₁⟩
  have S₁ := S.next fun a ha => hrest₁ a (Or.inl ha)
  replace hflags : Seg μ₁ flg (X.flagsAt t) :=
    hflags.keep fun b hb => hrest₁ b (Or.inr (by rw [hlen] at hb; omega))
  -- res := writeY(y, rbc, n, D, p, c0, len)
  light_call (C.writeY_meets S₁ ht) with r₂ μ₂ ⟨hY, hrest₂⟩
  have S₂ := S₁.next fun a ha => hrest₂ a (Or.inl (by omega))
  replace hX : Seg μ₂ A.x (X.matX t) :=
    hX.keep (by light_keep [X.length_matX t])
  replace hflags : Seg μ₂ flg (X.flagsAt t) :=
    hflags.keep fun b hb => hrest₂ b (Or.inr (by rw [hlen] at hb; omega))
  -- res := solver(n, D, w, 1, x, y, qi + lo, qj + lo, out, fr)
  light_call (C.solver_meets S₂ ht hX hY) with r₃ μ₃ ⟨hans, hkept₃⟩
  have S₃ := S₂.next fun a ha => hkept₃ a (by omega)
  replace hflags : Seg μ₃ flg (X.flagsAt t) :=
    hflags.keep fun b hb => hkept₃ b (by rw [hlen] at hb; omega)
  -- res := scanPairsAE(out, qi + lo, qj + lo, w, flg, ab, bc, ac, n, c0, len)
  light_call (C.scanPairsAE_meets S₃ hF ht hans hflags) with r₄ μ₄ ⟨hflags', hsame⟩
  exact ⟨r₄, μ₄, rfl, S₃.next fun a ha => hsame a (Or.inl (by omega)), hflags'⟩

/-! ## The loop -/

/-- The invariant of the loop, before instance t: upstream's `HostInv` with the address of the
flags in the local `Found`, and the flags of instance `t` in place. -/
def HostInvAE (lim : Limits) (d : ℕ) (X : HostData) (U : ℕ) (A : HostAddr) (flg : ℕ)
    (need : List ℕ → Need) (μ : ℕ → ℤ) (t : ℕ) (σ : State) : Prop :=
  ∃ (len rho lo w res : ℤ) (μ' : ℕ → ℤ),
    σ = hostState X A t (t % X.chunkCount) (X.c0 t) flg len rho lo w res μ' ∧
    HostSetting lim d X U A need μ μ' ∧ Seg μ' flg (X.flagsAt t)

/-- **One round of the loop.** -/
theorem hostRoundAE_spec
    (C : HostCtxAE P₀ R pS pWriteX pWriteY pScan pScanPairsAE pFill Tn need)
    (hF : FlagsPlace X A flg) (ht : t < X.m) {σ : State}
    (hσ : HostInvAE lim d X U A flg need μ t σ) :
    Ends lim (P₀ ++ R) d (hostRoundAE pS pWriteX pWriteY pScanPairsAE) σ (tCallsAE Tn X t + 45)
      (HostInvAE lim d X U A flg need μ (t + 1)) := by
  obtain ⟨len, rho, lo, w, res, μ', rfl, S, hflags⟩ := hσ
  unfold hostRoundAE
  -- the parameters of the instance
  light_piece (hostParams_spec S ht _ len rho lo w res) with _ rfl
  -- the four calls
  light_piece (hostCallsAE_spec C S hF ht hflags _ res) with _ ⟨res', μ'', rfl, S', hflags'⟩
  -- the counters
  light_piece (hostNext_spec S' ht _ _ _ _ _ res') with _ rfl
  exact ⟨_, _, _, _, _, μ'', rfl, S', hflags'⟩

/-- **hostLoopAE** returns the address of the flags, which hold the flags of all-edges Exact
Triangle, and changes no cell below x. -/
theorem hostLoopAE_spec
    (C : HostCtxAE P₀ R pS pWriteX pWriteY pScan pScanPairsAE pFill Tn need)
    (hok : HostOk X U) (hmem : HostMem X A μ) (hlay : HostLay X A)
    (hlim : HostLim lim d X U A need) (hF : FlagsPlace X A flg) :
    Ends lim (P₀ ++ R) d (hostLoopAEBody pS pWriteX pWriteY pScanPairsAE pFill)
      ⟨frame (hostLoopArgs X A), μ⟩ (tHostLoopAE Tn X) fun σ' =>
      σ'.loc 0 = flg ∧ Seg σ'.mem flg (ImprovedExponents.AllEdges.aeFlags X.n X.AB X.BC X.AC) ∧
        Kept μ σ'.mem A.x := by
  have hw := hlim.space
  have := hlim.fr
  have hflg := hF.fr
  have hT : ∑ t ∈ Finset.range X.m, (4 + (tCallsAE Tn X t + 45))
      ≤ ∑ t ∈ Finset.range X.m, (tWrites X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
        tScanPairsAE (X.w t) (X.len t) (X.execsAE t)) :=
    Finset.sum_le_sum fun t _ => by simp [tCallsAE, tWrites]; omega
  have hflgZ : ((A.fr : ℕ) : ℤ) - (X.n : ℤ) * (X.n : ℤ) = (flg : ℕ) := by
    rw [← hflg]
    push_cast
    ring
  have := hF.x
  have := hlim.depth
  unfold hostLoopAEBody tHostLoopAE hostLoopArgs
  -- t := 0; ch := 0; c0 := 0; fnd := fr - n²
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set (flg : ℕ) using hflgZ
  -- fill(fnd, n², 0)
  light_call (fill_meets (lim := lim) (d := d + 1) (x := (0 : ℤ)) C.fill hw
    (by rw [hflg]; omega)) with r₀ μ₁ ⟨hzero, hsame⟩
  -- while t < m
  refine Ends.next _ (Ends.while (HostInvAE lim d X U A flg need μ) X.m
    (fun t => tCallsAE Tn X t + 45) ?start ?round ?done)
    (by simp only [Cond.cost, Expr.cost, List.map, List.sum_cons, List.sum_nil, Nat.reduceAdd]
        omega)
  case start =>
    refine ⟨0, 0, 0, 0, r₀, μ₁, ?_,
      ⟨hok, hmem, hlay, hlim, fun a ha => hsame a (Or.inl (by omega))⟩, hzero⟩
    rw [hostState]
    simp only [HostData.c0, Nat.zero_div, Nat.zero_mul, Nat.cast_zero, Nat.zero_mod, setLocal]
  case round =>
    intro t σ ht hσ
    obtain ⟨len, rho, lo, w, res, μ', rfl, -, -⟩ := id hσ
    exact ⟨⟨trivial, trivial⟩, by simpa using ht, hostRoundAE_spec C hF ht hσ⟩
  case done =>
    rintro _ ⟨len, rho, lo, w, res, μ', rfl, S, hflags⟩
    rw [X.flagsAt_m hok.valid] at hflags
    -- return fnd
    exact ⟨⟨trivial, trivial⟩, by simp, Ends.setTo (flg : ℕ) ⟨by simp, hflags, S.kept⟩
      (hT := by
        simp only [Cond.cost, Expr.cost, List.map, List.sum_cons, List.sum_nil, Nat.reduceAdd]
        omega)⟩

end Light.Sec3




/-!
# The all-edges host: the program, its time and its need

The all-edges variant of the host of Theorem 17 is the host of `ImprovedExponents.HostMid` (the
solver is charged at the inner dimension `midSize D g`) with the loop over the instances replaced
by `hostLoopAE`, the brute force by `bruteAE`, and the solver's free pointer moved up by `n²` cells
that hold the flags (`et17TablesAE`, `aeCoreBody`).  The top procedure `aeTopBody` copies the `n²`
flags to the place `out` of the task (`aeTask`).

This file holds the text, the time (`hostTimeAE`), the need (`hostNeedAE`), the specifications of
the parts (`et17TablesAE_spec`, `aeCore_spec`, `aeTop_spec`), the assembled program (`aeProcs`)
and the statement that it solves all-edges Exact Triangle (`ae17_solves`).
-/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec HostMid

/-! ## The text -/

open Et17 in
/-- The third part of the all-edges host: upstream's `et17Tables` with the all-edges loop, whose
free pointer is `n²` cells above the answers; the flags lie in between. -/
def et17TablesAE (ν : Et17Nums) (pLoopAE : ℕ) : Stmt :=
  .call ν.pDbl [v Free, v ThePrime, v Bits] Small ;;
  .call ν.pResidues [v AdrAB, v ResAB, v SizeSq, v Free, v Bits] Small ;;
  .call ν.pResidues [v AdrBC, v ResBC, v SizeSq, v Free, v Bits] Small ;;
  .call ν.pResidues [v AdrAC, v ResAC, v SizeSq, v Free, v Bits] Small ;;
  .call ν.pClasses [v ResAB, v Size, v ThePrime, v Cls, v Cur, v Rows, v Cols] Small ;;
  .call ν.pChunks [v Cls, v ThePrime, v Cap, v TabR, v TabL, v TabW] NumChunks ;;
  .set NumInst (v NumPieces *' v NumChunks) ;;
  .call pLoopAE [v Size, v ParD, v ThePrime, v PieceLen, v NumChunks, v NumInst, v AdrAB, v AdrBC,
    v AdrAC, v ResAC, v ResBC, v Rows, v Cols, v TabR, v TabL, v TabW, v MatX, v MatY, v AdrOut,
    v SolverFree +' v SizeSq] 0

open Et17 in
/-- aeCore(n, U, ab, bc, ac, fr): the parameters, then the brute force or the three parts of the
variant host; it returns the address of the `n²` flags, which lie at or above `fr`. -/
def aeCoreBody (ν : Et17Nums) (pBruteAE pLoopAE : ℕ) : Stmt :=
  et17Params ν ;;
  .ite (v Small =' k 1)
    (.call pBruteAE [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v Free] 0)
    (et17Sizes' ν ;; et17TablesAE ν pLoopAE)

/-- ae(n, U, ab, bc, ac, out, fr): the core, then the `n²` flags are copied to `out`. -/
def aeTopBody (pCore pCopy : ℕ) : Stmt :=
  .call pCore [v 0, v 1, v 2, v 3, v 4, v 6] 7 ;;
  .call pCopy [v 7, v 5, v 0 *' v 0] 7

/-! ## Time and need -/

/-- A bound on the time of the all-edges loop: as `hostLoopBound'`, with the all-edges scan of the
answers, at most `falsePositiveBound + n²` scans, and the filling of the flags. -/
noncomputable def hostLoopBoundAE (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  4 * n * g *
      (tWrites n D (pieceSizeNat D g) + supTime Tn n (midSize D g) (queryCapNat n D)
        + tAnswersAE (queryCapNat n D))
    + tScanCallAE (pieceSizeNat D g) * (falsePositiveBound n U D + n * n) + fillTime (n * n) + 40

/-- The time of the core after the tests, if n is not small. -/
noncomputable def hostMainAE (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  chooseTime n U D + tQueryCapNat n D + tCeilDiv (Nat.sqrt D) g + tCeilDiv n (pieceSizeNat D g)
    + tBitLen U + tDblTable (bitLen U) + 3 * tResidues (n * n) (bitLen U) + tClasses n (Nat.sqrt D)
    + tChunks (Nat.sqrt D) (4 * n * g) + hostLoopBoundAE Tn n U D g + 300

/-- A bound on the time of the core in the worst case. -/
noncomputable def hostCoreTime (Dfun Gfun tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  hostSetup tD tG n (Dfun n) +
    if SmallCase n (Dfun n) (Gfun (Dfun n)) then tBruteAE n + 20
    else hostMainAE Tn n U (Dfun n) (Gfun (Dfun n))

/-- **A bound on the time of the all-edges host in the worst case**, for the parameter functions
Dfun, Gfun with the times tD, tG, over a solver with the time Tn: the core and the copy. -/
noncomputable def hostTimeAE (Dfun Gfun tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  hostCoreTime Dfun Gfun tD tG Tn n U + copyTime (n * n) + 20

/-- The need of the core of the all-edges host for given parameters D and g: `hostNeedAt'` with
`n²` more cells for the flags. -/
def hostNeedCoreAt (a b : ℕ) (need : List ℕ → Need) (n U D g : ℕ) : Need :=
  ⟨(hostNeedAt' a b need n U D g).word, (hostNeedAt' a b need n U D g).cells + n * n,
    (hostNeedAt' a b need n U D g).depth⟩

/-- The need of the core of the all-edges host. -/
def hostNeedCore (Dfun Gfun wD wG : ℕ → ℕ) (need : List ℕ → Need) (n U : ℕ) : Need :=
  hostNeedCoreAt (wD n) (wG (Dfun n)) need n U (Dfun n) (Gfun (Dfun n))

/-- **The need of the all-edges host**, over a solver with the need `need`: that of the core, one
level of calls up. -/
def hostNeedAE (Dfun Gfun wD wG : ℕ → ℕ) (need : List ℕ → Need) (n U : ℕ) : Need :=
  ⟨(hostNeedCore Dfun Gfun wD wG need n U).word, (hostNeedCore Dfun Gfun wD wG need n U).cells,
    (hostNeedCore Dfun Gfun wD wG need n U).depth + 1⟩

/-- The need of the variant host is allowed for when that of the all-edges host is. -/
theorem hostNeedAt'_ok {lim : Limits} {d a b n U D g : ℕ} {need : List ℕ → Need} {fr : ℕ}
    (hok : (hostNeedCoreAt a b need n U D g).Ok lim fr d) :
    (hostNeedAt' a b need n U D g).Ok lim fr d :=
  hok.mono le_rfl (by simp only [hostNeedCoreAt]; omega) (by simp only [hostNeedCoreAt]; omega)

/-- The time of the third part in a run of the all-edges host. -/
def hostRunTimeAE (Tn : List ℕ → ℕ) (X : HostData) (U : ℕ) : ℕ :=
  tDblTable (bitLen U) + 3 * tResidues (X.n * X.n) (bitLen U) + tClasses X.n X.p
    + tChunks X.p X.chunkCount + tHostLoopAE Tn X + 80

/-! ## The context -/

/-- The context of the all-edges host: that of the variant host, and the new procedures. -/
structure AeCtx (P₀ R : Program) (ν : Et17Nums) (pScanPairsAE pFill pBruteAE pLoopAE : ℕ)
    (Tn : List ℕ → ℕ) (need : List ℕ → Need) (Dfun Gfun tD tG wD wG : ℕ → ℕ) : Prop where
  base : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG
  scanPairsAE : (P₀ ++ R)[pScanPairsAE]? = some (scanPairsAEBody ν.pScan)
  fill : (P₀ ++ R)[pFill]? = some fillBody
  bruteAE : (P₀ ++ R)[pBruteAE]? = some (bruteAEBody ν.pScan)
  loopAE : (P₀ ++ R)[pLoopAE]? =
    some (hostLoopAEBody ν.pS ν.pWriteX ν.pWriteY pScanPairsAE pFill)

variable {P₀ R : Program} {ν : Et17Nums} {pScanPairsAE pFill pBruteAE pLoopAE : ℕ}
  {Tn : List ℕ → ℕ} {need : List ℕ → Need} {Dfun Gfun tD tG wD wG : ℕ → ℕ} {lim : Limits} {d : ℕ}

/-- The context of the all-edges loop. -/
theorem AeCtx.loop (C : AeCtx P₀ R ν pScanPairsAE pFill pBruteAE pLoopAE Tn need Dfun Gfun tD tG
    wD wG) :
    HostCtxAE P₀ R ν.pS ν.pWriteX ν.pWriteY ν.pScan pScanPairsAE pFill Tn need :=
  { C.base.loop with scanPairsAE := C.scanPairsAE, fill := C.fill }

/-! ## The third part -/

/-- The addresses of the all-edges loop: upstream's, with the free pointer `n²` cells up. -/
def hostAddrAE (x : TriInst) (X : HostData) (fr : ℕ) : HostAddr :=
  { hostAddr x X fr with fr := aFr X x.U fr + X.n * X.n }

/-- What the all-edges loop asks of the limits. -/
theorem hostLimAE_of_ok {a b : ℕ} {x : TriInst} {fr D g : ℕ} (hbig : BigCase x.n D g)
    (hok : (hostNeedCoreAt a b need x.n x.U D g).Ok lim fr d) :
    HostLim lim (d + 1) (hostData' x D g) x.U (hostAddrAE x (hostData' x D g) fr) need := by
  have h := hostLim_of_ok' hbig (hostNeedAt'_ok hok)
  have hcells := hok.cells
  have hfr := aFr_le' (x := x) (g := g) hbig.sixteen_le fr
  simp only [hostNeedCoreAt, hostNeedAt'] at hcells
  exact
    { space := h.space
      fr := by change aFr (hostData' x D g) x.U fr + x.n * x.n < lim.space; omega
      prime := h.prime
      count := h.count
      step := h.step
      weights := h.weights
      depth := by have := hok.depth; simp only [hostNeedCoreAt, hostNeedAt'] at this; omega
      solver := fun t ht => by
        have hs := h.solver t ht
        have : (hostData' x D g).w t ≤ queryCapNat x.n D := (hostData' x D g).w_le_cap ht
        have :
            (need [(hostData' x D g).n, (hostData' x D g).D, (hostData' x D g).w t]).cells
              ≤ (supNeed need x.n (midSize D g) (queryCapNat x.n D)).cells :=
          Finset.le_sup (f := fun v => (need [x.n, midSize D g, v]).cells)
            (Finset.mem_range.2 (by omega))
        exact ⟨hs.word, by change aFr (hostData' x D g) x.U fr + x.n * x.n + _ ≤ _; omega,
          hs.space, hs.depth⟩ }

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Arrays.lean
open Et17 in
/-- **The third part of the all-edges host**: the result is the address of the flags, which hold
the flags of all-edges Exact Triangle; only cells from the free pointer on change. -/
theorem et17Sizes_spec' (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG)
    (x : TriInst) (μ : ℕ → ℤ) (fr D g a b : ℕ) (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt' a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Sizes' ν) ⟨frame (et17LocA x fr D g), μ⟩
      (chooseTime x.n x.U D + tQueryCapNat x.n D + tCeilDiv (Nat.sqrt D) g +
        tCeilDiv x.n (pieceSizeNat D g) + tBitLen x.U + 120)
      fun σ' => ∃ μ', σ' = ⟨frame (et17LocB' x fr D g), μ'⟩ ∧ Kept μ μ' fr := by
  have hok0 : (hostNeedAt a b (fun ps => need (midArgs (fun _ => g) ps)) x.n x.U D g).Ok lim fr d :=
    hok
  have hD16 : 16 ≤ D := hbig.sixteen_le
  have hg1 : 1 ≤ g := hbig.one_le_g
  have hsqrt : 4 ≤ Nat.sqrt D := Nat.le_sqrt.2 (by omega)
  have hdepth : d < lim.depth := by
    have := hok.depth
    simp only [hostNeedAt'] at this
    omega
  have htop : aFr (hostData' x D g) x.U fr ≤ lim.space := by
    have := aFr_le' (x := x) (g := g) hD16 fr
    have hcells := hok.cells
    simp only [hostNeedAt'] at hcells
    omega
  have hmid : ((midSize D g : ℕ) : ℤ) = ((Nat.sqrt D ⌈/⌉ g : ℕ) : ℤ) * (Nat.sqrt D : ℤ) := by
    unfold midSize pieceSizeNat
    push_cast
    rfl
  have : ((midSize D g : ℕ) : ℤ) ≤ lim.word :=
    le_word_of_le_hostWord hok0 ((midSize_le D g).trans (by unfold hostWord; omega))
  unfold et17Sizes' et17LocA
  rw [ite_eq_right (not_smallCase_iff.2 hbig)]
  light_call (choosePrime_meets C.hChoose C.ch (choosePre_of_ok hpre hok0)) with _ μ₁ ⟨rfl, hμ₁⟩
  light_call (queryCapNat_meets (n := x.n) (D := D) C.hCap (by omega) (le_word_of_le_hostWord hok0))
    with _ μ₁ ⟨rfl, rfl⟩
  light_call (ceilDiv_meets (a := Nat.sqrt D) (b := g) C.hCeil hg1 (le_word_of_le_hostWord hok0))
    with _ μ₁ ⟨rfl, rfl⟩
  light_call (ceilDiv_meets (a := x.n) (b := pieceSizeNat D g) C.hCeil
    ((Nat.lt_ceilDiv_iff hg1).2 (by omega)) (le_word_of_le_hostWord hok0)) using pieceSizeNat
    with _ μ₁ ⟨rfl, rfl⟩
  light_call (bitLen_meets (U := x.U) C.hBitLen (le_word_of_le_hostWord hok0)) with _ μ₁ ⟨rfl, rfl⟩
  light_set (midSize D g : ℕ) using hmid
  refine (et17Addr_spec x (hostData' x D g) hok.space htop).mono (by simp [et17Addr]; omega) ?_
  rintro _ rfl
  exact ⟨μ₁, rfl, fun c hc => hμ₁ c (Or.inl hc)⟩

open Et17 in
theorem et17TablesAE_spec
    (C : AeCtx P₀ R ν pScanPairsAE pFill pBruteAE pLoopAE Tn need Dfun Gfun tD tG wD wG)
    (x : TriInst) (μ : ℕ → ℤ) (fr D g a b : ℕ) (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedCoreAt a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17TablesAE ν pLoopAE) ⟨frame (et17LocB' x fr D g), μ⟩
      (hostRunTimeAE Tn (hostData' x D g) x.U)
      fun σ' => ∃ flg : ℕ, fr ≤ flg ∧ flg + x.n * x.n ≤ lim.space ∧ σ'.loc 0 = flg ∧
        Seg σ'.mem flg (aeFlags x.n x.AB x.BC x.AC) ∧ Kept μ σ'.mem fr := by
  have hok' := hostNeedAt'_ok hok
  have hD16 := hbig.sixteen_le
  have hok0 : (hostNeedAt a b (fun ps => need (midArgs (fun _ => g) ps)) x.n x.U D g).Ok lim fr d :=
    hok'
  have hr : Et17.Ready lim d x (hostData' x D g) μ fr := by
    have hcells := hok'.cells
    have hdepth := hok'.depth
    have htop := aFr_le' (x := x) (g := g) hD16 fr
    have hp : 2 ≤ (hostData' x D g).p := two_le_chosenPrime x.AB x.BC x.AC hD16
    have hps := Nat.mul_le_mul_right (2 ^ (bitLen x.U + 1)) (hostData'_p_le x g hD16)
    simp only [hostNeedAt'] at hcells hdepth
    exact
      { space := hok'.space, depth := by omega, prime := by omega
        word := le_word_of_le_hostWord hok0, top := by omega
        segAB := hpre.segAB, segBC := hpre.segBC, segAC := hpre.segAC
        lenAB := hpre.lenAB, lenBC := hpre.lenBC, lenAC := hpre.lenAC
        leAB := hpre.leAB, leBC := hpre.leBC, leAC := hpre.leAC
        belowAB := hpre.belowAB, belowBC := hpre.belowBC, belowAC := hpre.belowAC }
  have hlim := hostLimAE_of_ok hbig hok
  have hv := hostData'_valid hpre hbig
  have hdepth := hok.depth
  simp only [hostNeedCoreAt, hostNeedAt'] at hdepth
  unfold et17LocB'
  generalize hX : hostData' x D g = X at hr hlim hv ⊢
  have hn : X.n = x.n := by rw [← hX]; rfl
  have hfr : fr ≤ aX X x.U fr := by
    have := host_places X x.U fr
    omega
  unfold et17TablesAE hostRunTimeAE
  refine resid_then C.base.hDbl C.base.hResid C.base.hResidues hr (fun r₁ μ₁ hresid => ?_)
    (by omega)
  refine classes_then C.base.hClasses C.base.hChunks hr hv.cap_pos hresid.rab
    (fun r₂ μ₂ hclass => ?_) (by omega)
  have hcount := hlim.count
  have hm : (X.m : ℤ) = (X.h : ℤ) * X.chunkCount := by
    rw [HostData.m]
    push_cast
    rfl
  have hpos : (0 : ℤ) ≤ (X.h : ℤ) * X.chunkCount := by positivity
  light_set (X.m : ℕ) using hm
  have hlay := hostLay_of hr (hr.chunkCount_le hv.cap_pos)
  have hplaces := host_places X x.U fr
  have hx : aX X x.U fr ≤ aFr X x.U fr := by omega
  have hfrA : (hostAddr x X fr).fr = aFr X x.U fr := rfl
  have hfrS : aFr X x.U fr + X.n * X.n < lim.space := hlim.fr
  have hsw := hlim.space
  have hfrW : (aFr X x.U fr : ℤ) + (X.n : ℤ) * (X.n : ℤ) ≤ lim.word := by
    have : ((aFr X x.U fr + X.n * X.n : ℕ) : ℤ) ≤ lim.word := by
      exact_mod_cast (Nat.cast_lt.2 hfrS).le.trans hsw
    push_cast at this
    exact this
  have : (hostAddr x X fr).out = aOut X x.U fr := rfl
  have hF : FlagsPlace X (hostAddrAE x X fr) (aFr X x.U fr) := ⟨rfl, hx, hlay.ofr⟩
  have hofr : ∀ t < X.m, (hostAddrAE x X fr).out + X.w t ≤ (hostAddrAE x X fr).fr := fun t ht => by
    have := hlay.ofr t ht
    change (hostAddr x X fr).out + X.w t ≤ aFr X x.U fr + X.n * X.n
    omega
  have : HostLay X (hostAddrAE x X fr) := { hlay with ofr := hofr }
  have hargs : ((aFr X x.U fr + X.n * X.n : ℕ) : ℤ) =
      (aFr X x.U fr : ℤ) + ((X.n : ℤ) * (X.n : ℤ)) := by push_cast; rfl
  light_call (Meets.of_body (Q := fun r μ' => r = aFr X x.U fr ∧
      Seg μ' (aFr X x.U fr) (aeFlags X.n X.AB X.BC X.AC) ∧ Kept μ₂ μ' (hostAddrAE x X fr).x)
    C.loopAE (hostLoopAE_spec C.loop ⟨hv, hr.leAB, hr.leBC, hr.leAC⟩
      { hostMem_of hr hresid hclass with } this hlim hF)) using hostLoopArgs, hostAddrAE, hostAddr,
    hargs with r μ₃ ⟨rfl, hflags, hkept⟩
  refine ⟨aFr X x.U fr, by omega, by rw [← hn]; omega, rfl, ?_, fun c hc => ?_⟩
  · have hAB : X.AB = x.AB := by rw [← hX]; rfl
    have hBC : X.BC = x.BC := by rw [← hX]; rfl
    have hAC : X.AC = x.AC := by rw [← hX]; rfl
    rwa [hn, hAB, hBC, hAC] at hflags
  · have hcls : fr ≤ aCls X x.U fr := by omega
    exact (hkept c (lt_of_lt_of_le hc hfr)).trans ((hclass.same c (Or.inl (by omega))).trans
      (hresid.same c (Or.inl hc)))

theorem instanceAE_le (Tn : List ℕ → ℕ) (n D g execs : ℕ) {len q w cap : ℕ} (hlen : len ≤ q)
    (hw : w ≤ cap) :
    tWrites n (midSize D g) len + Tn [n, midSize D g, w] + tScanPairsAE w len execs
      ≤ tWrites n D q + supTime Tn n (midSize D g) cap + tAnswersAE cap
        + tScanCallAE q * execs := by
  have : tWrites n (midSize D g) len ≤ tWrites n D q := by
    have := midSize_le D g
    unfold tWrites tWriteX tWriteY
    gcongr
  have : Tn [n, midSize D g, w] ≤ supTime Tn n (midSize D g) cap :=
    Finset.le_sup (f := fun w => Tn [n, midSize D g, w]) (Finset.mem_range.2 (by omega))
  have : tAnswersAE w ≤ tAnswersAE cap := by
    unfold tAnswersAE
    gcongr
  have : tScanCallAE len * execs ≤ tScanCallAE q * execs := by
    unfold tScanCallAE tScan
    gcongr
  unfold tScanPairsAE
  omega

variable {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ}

theorem hostRunTimeAE_le (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) (Tn : List ℕ → ℕ) :
    hostRunTimeAE Tn (hostData' x D g) x.U
      ≤ tDblTable (bitLen x.U) + 3 * tResidues (x.n * x.n) (bitLen x.U)
        + tClasses x.n (Nat.sqrt D) + tChunks (Nat.sqrt D) (4 * x.n * g)
        + hostLoopBoundAE Tn x.n x.U D g + 80 := by
  set X := hostData' x D g
  have hv := hostData'_valid hpre hbig
  have hm := hostData'_m_le hbig
  have : X.p ≤ Nat.sqrt D := hostData'_p_le x g hbig.sixteen_le
  have : X.chunkCount ≤ 4 * x.n * g :=
    (Nat.le_mul_of_pos_left _ ((Nat.lt_ceilDiv_iff hv.q_pos).2 (by rw [zero_mul]; exact hv.n_pos))).trans hm
  have hexecs : ∑ t ∈ Finset.range X.m, X.execsAE t ≤ falsePositiveBound x.n x.U D + x.n * x.n :=
    (X.sum_execsAE_le hv).trans (Nat.add_le_add_right
      ((HostData.sum_fails_le hv).trans (F_le_falsePositiveBound hpre hbig)) _)
  have : tHostLoopAE Tn X ≤ hostLoopBoundAE Tn x.n x.U D g := by
    unfold tHostLoopAE hostLoopBoundAE
    refine Nat.add_le_add_right (Nat.add_le_add_right ?_ _) _
    calc ∑ t ∈ Finset.range X.m,
          (tWrites X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
            tScanPairsAE (X.w t) (X.len t) (X.execsAE t))
        ≤ ∑ t ∈ Finset.range X.m,
          (tWrites x.n D (pieceSizeNat D g) + supTime Tn x.n (midSize D g) (queryCapNat x.n D) +
            tAnswersAE (queryCapNat x.n D) + tScanCallAE (pieceSizeNat D g) * X.execsAE t) :=
          Finset.sum_le_sum fun t ht => instanceAE_le Tn x.n D g _ (Nat.min_le_left _ _)
            (X.w_le_cap (Finset.mem_range.1 ht))
      _ = X.m * (tWrites x.n D (pieceSizeNat D g) +
            supTime Tn x.n (midSize D g) (queryCapNat x.n D) + tAnswersAE (queryCapNat x.n D)) +
          tScanCallAE (pieceSizeNat D g) * ∑ t ∈ Finset.range X.m, X.execsAE t := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
            Finset.mul_sum]
      _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_right _ hm) (Nat.mul_le_mul_left _ hexecs)
  have hn : X.n = x.n := rfl
  unfold hostRunTimeAE
  rw [hn]
  unfold tClasses tChunks
  omega

end ImprovedExponents.AllEdges

namespace ImprovedExponents.ParamRoutines

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec3

noncomputable def paramDRat (a b n : ℕ) : ℕ := ⌊(n : ℝ) ^ ((a : ℝ) / b)⌋₊
noncomputable def paramGRat (c d D : ℕ) : ℕ := ⌈(D : ℝ) ^ ((c : ℝ) / d)⌉₊
noncomputable def paramGRatOf (a b c d n : ℕ) : ℕ := paramGRat c d (paramDRat a b n)

def paramDRatNat (a b n : ℕ) : ℕ := rootFloor b (n ^ a)
def paramGRatNat (c d D : ℕ) : ℕ := rootCeil d (D ^ c)

theorem rpow_natCast_div (n a b : ℕ) :
    (n : ℝ) ^ ((a : ℝ) / b) = ((n ^ a : ℕ) : ℝ) ^ ((b : ℝ)⁻¹) := by
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul n.cast_nonneg, div_eq_mul_inv]

theorem paramDRatNat_eq {b : ℕ} (hb : b ≠ 0) (a n : ℕ) : paramDRatNat a b n = paramDRat a b n := by
  rw [paramDRatNat, paramDRat, rpow_natCast_div, floor_rpow_inv hb]

theorem paramGRatNat_paramDRat {d : ℕ} (hd : d ≠ 0) (a b c : ℕ) {n : ℕ}
    (hD : 1 ≤ paramDRat a b n) :
    paramGRatNat c d (paramDRat a b n) = paramGRatOf a b c d n := by
  rw [paramGRatNat, paramGRatOf, paramGRat, rpow_natCast_div,
    ceil_rpow_inv hd (Nat.one_le_pow _ _ hD)]

theorem one_le_paramDRatNat {b : ℕ} (hb : b ≠ 0) (a : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ paramDRatNat a b n :=
  le_rootFloor hb (by simpa using Nat.one_le_pow a n hn)

theorem one_le_paramDRat {b : ℕ} (hb : b ≠ 0) (a : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ paramDRat a b n :=
  paramDRatNat_eq hb a n ▸ one_le_paramDRatNat hb a hn

theorem one_le_paramGRatNat (c d D : ℕ) : 1 ≤ paramGRatNat c d D := Nat.succ_le_succ (Nat.zero_le _)

theorem paramDRatNat_le (a b n : ℕ) : paramDRatNat a b n ≤ n ^ a := Nat.findGreatest_le _

theorem paramGRatNat_le (c d D : ℕ) : paramGRatNat c d D ≤ D ^ c + 1 :=
  Nat.succ_le_succ (Nat.findGreatest_le _)

theorem paramDRatNat_le_self {a b : ℕ} (hb : b ≠ 0) (h : a ≤ b) {n : ℕ} (hn : 1 ≤ n) :
    paramDRatNat a b n ≤ n :=
  (Nat.pow_le_pow_iff_left hb).1 ((rootFloor_pow_le hb _).trans (Nat.pow_le_pow_right hn h))

theorem paramGRatNat_le_self {c d : ℕ} (hd : d ≠ 0) (h : c ≤ d) {D : ℕ} (hD : 1 ≤ D) :
    paramGRatNat c d D ≤ D :=
  rootCeil_le hd (Nat.one_le_pow _ _ hD) (Nat.pow_le_pow_right hD h)

variable {lim : Limits} {P : Program} {d : ℕ}

def powThen (e : ℕ) (s : Stmt) : Stmt :=
  .set 1 (k 0) ;;
  .set 2 (k 1) ;;
  .while (v 1 <' k e) (
    .set 2 (v 2 *' v 0) ;;
    .set 1 (v 1 +' k 1)) ;;
  s

theorem powThen_ends {μ : ℕ → ℤ} {x e B T : ℕ} {s : Stmt} {Q : State → Prop}
    (hB : ∀ i ≤ e, x ^ i ≤ B) (hword : ((B + e + 1 : ℕ) : ℤ) ≤ lim.word) (hT : 12 * e + 8 ≤ T)
    (h : Ends lim P d s ⟨frame [x, e, (x ^ e : ℕ)], μ⟩ (T - (12 * e + 8)) Q) :
    Ends lim P d (powThen e s) ⟨frame [(x : ℤ)], μ⟩ T Q := by
  push_cast at hword
  have : (0 : ℤ) ≤ B := Int.natCast_nonneg _
  unfold powThen
  light_set (0 : ℕ)
  light_set (1 : ℕ)
  refine Ends.next (12 * e + 4) (Ends.whileBlock
    (fun i σ => σ = ⟨frame [x, i, (x ^ i : ℕ)], μ⟩) e (by simp) ?round ?done
    (by simp; omega)) (by simp; omega)
  case round =>
    rintro i _ hi rfl
    have hle : ((x ^ (i + 1) : ℕ) : ℤ) ≤ B := by exact_mod_cast hB (i + 1) hi
    have hmul : ((x ^ i : ℕ) : ℤ) * x = ((x ^ (i + 1) : ℕ) : ℤ) := by push_cast; ring
    have hmul0 : (0 : ℤ) ≤ ((x ^ (i + 1) : ℕ) : ℤ) := Int.natCast_nonneg _
    generalize ((x ^ (i + 1) : ℕ) : ℤ) = q' at hle hmul hmul0
    generalize ((x ^ i : ℕ) : ℤ) = q at hmul
    exact ⟨by light_side, by light_side, by light_side [hmul],
      by simp [update_frame_setLocal, hmul]⟩
  case done =>
    rintro _ rfl
    exact ⟨by light_side, by light_side, h.mono (by simp; omega) fun _ hQ => hQ⟩

def dRatBody (a b pRoot : ℕ) : Stmt :=
  powThen a (
    .call pRoot [k b, v 2 +' k 1] 1 ;;
    .set 0 (v 1 -' k 1))

def tDRat (a b n : ℕ) : ℕ := (paramDRatNat a b n + 1) * (16 * b + 27) + 12 * a + 18
def wDRat (a b n : ℕ) : ℕ := (n ^ a + 1) * (paramDRatNat a b n + 1) + a + b + 1

def gRatBody (c d pRoot : ℕ) : Stmt :=
  powThen c (.call pRoot [k d, v 2] 0)

def tGRat (c d D : ℕ) : ℕ := paramGRatNat c d D * (16 * d + 27) + 12 * c + 12
def wGRat (c d D : ℕ) : ℕ := D ^ c * paramGRatNat c d D + c + d + 1

theorem getElem?_behind (Q L R : Program) {i : ℕ} {body : Stmt} (h : L[i]? = some body) :
    (Q ++ L ++ R)[Q.length + i]? = some body := by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact getElem?_append_of_eq_some h R

def ratProcs (a b c d o : ℕ) : Program :=
  [powLtBody, rootCeilBody o, dRatBody a b (o + 1), gRatBody c d (o + 1)]

theorem paramProc_dRat {b : ℕ} (hb : b ≠ 0) (a c d : ℕ) (Q R : Program) :
    ParamProc (Q ++ ratProcs a b c d Q.length ++ R) (Q.length + 2) (paramDRatNat a b)
      (tDRat a b) (wDRat a b) := by
  intro lim dep n μ hn _ hword hd
  refine Meets.of_body (getElem?_behind Q _ R (i := 2) rfl) ?_
  have hR := getElem?_behind Q (ratProcs a b c d Q.length) R (i := 1) rfl
  have hP := getElem?_behind Q (ratProcs a b c d Q.length) R (i := 0) rfl
  have hroot : rootCeil b (n ^ a + 1) = paramDRatNat a b n + 1 := rootCeil_succ hb _
  have hpows : ∀ i ≤ a, n ^ i ≤ n ^ a + 1 := fun _ hi =>
    (Nat.pow_le_pow_right hn hi).trans (Nat.le_succ _)
  have hmul : n ^ a + 1 ≤ (n ^ a + 1) * (paramDRatNat a b n + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hmul' : paramDRatNat a b n + 1 ≤ (n ^ a + 1) * (paramDRatNat a b n + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  unfold wDRat at hword
  unfold dRatBody tDRat
  generalize hD : paramDRatNat a b n = D at hroot hmul hmul' hword
  generalize hN : n ^ a = N at hroot hmul hmul' hword hpows
  have hfits : (((N + 1) * (D + 1) + b + 1 : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast (by omega)) hword
  generalize hM : (N + 1) * (D + 1) = M at hmul hmul' hword hfits
  refine powThen_ends (B := N + 1) hpows (le_trans (by exact_mod_cast (by omega)) hword)
    (by omega) ?_
  rw [hN]
  have hN1 : ((N + 1 : ℕ) : ℤ) ≤ lim.word := le_trans (by exact_mod_cast (by omega)) hword
  have : ((b : ℕ) : ℤ) ≤ lim.word := le_trans (by exact_mod_cast (by omega)) hword
  push_cast at hN1
  refine Ends.callToThen (rootCeil_meets (e := b) (t := N + 1) hR hP hb (by omega)
    (by rw [hroot, hM]; exact hfits) (by omega)) ?_
    (hT := by simp [tRootCeil, hroot]; omega)
  rintro _ μ' ⟨rfl, hμ⟩
  rw [hroot, hμ]
  have hD1 : ((D + 1 : ℕ) : ℤ) ≤ lim.word := le_trans (by exact_mod_cast (by omega)) hword
  push_cast at hD1
  exact Ends.setTo D (by simp) (he := by light_side) (hT := by simp [tRootCeil, hroot]; omega)

theorem paramProc_gRat {d : ℕ} (hd : d ≠ 0) (a b c : ℕ) (Q R : Program) :
    ParamProc (Q ++ ratProcs a b c d Q.length ++ R) (Q.length + 3) (paramGRatNat c d)
      (tGRat c d) (wGRat c d) := by
  intro lim dep D μ hD _ hword hd'
  refine Meets.of_body (getElem?_behind Q _ R (i := 3) rfl) ?_
  have hR := getElem?_behind Q (ratProcs a b c d Q.length) R (i := 1) rfl
  have hP := getElem?_behind Q (ratProcs a b c d Q.length) R (i := 0) rfl
  have hpos : 1 ≤ paramGRatNat c d D := one_le_paramGRatNat c d D
  have hmul : D ^ c ≤ D ^ c * paramGRatNat c d D := Nat.le_mul_of_pos_right _ hpos
  have hN0 : 1 ≤ D ^ c := Nat.one_le_pow _ _ hD
  have hpows : ∀ i ≤ c, D ^ i ≤ D ^ c := fun i hi => Nat.pow_le_pow_right hD hi
  unfold wGRat at hword
  unfold gRatBody tGRat
  unfold paramGRatNat at hpos hmul hword ⊢
  generalize hN : D ^ c = N at hpos hmul hword hpows hN0
  have hfits : ((N * rootCeil d N + d + 1 : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast (by omega)) hword
  generalize hG : rootCeil d N = G at hpos hmul hword hfits
  generalize hM : N * G = M at hmul hword hfits
  refine powThen_ends (B := N) hpows (le_trans (by exact_mod_cast (by omega)) hword)
    (by omega) ?_
  rw [hN]
  have : ((N : ℕ) : ℤ) ≤ lim.word := le_trans (by exact_mod_cast (by omega)) hword
  have : ((d : ℕ) : ℤ) ≤ lim.word := le_trans (by exact_mod_cast (by omega)) hword
  exact Ends.callTo (rootCeil_meets (e := d) (t := N) hR hP hd hN0
    (by rw [hG, hM]; exact hfits) (by omega)) (fun r μ' h => by simpa [hG] using h)
    (hT := by simp [tRootCeil, hG]; omega)

theorem polyBounded_paramDRatNat (a b : ℕ) : PolyBounded fun n _ => paramDRatNat a b n :=
  (by growth_poly [] : PolyBounded fun n _ => n ^ a).of_le fun n _ => paramDRatNat_le a b n

theorem polyBounded_paramGRatNat (c d : ℕ) {D : ℕ → ℕ} (hD : PolyBounded fun n _ => D n) :
    PolyBounded fun n _ => paramGRatNat c d (D n) :=
  (by growth_poly [hD] : PolyBounded fun n _ => D n ^ c + 1).of_le fun n _ =>
    paramGRatNat_le c d (D n)

theorem polyBounded_wDRat (a b : ℕ) : PolyBounded fun n _ => wDRat a b n := by
  unfold wDRat
  growth_poly [polyBounded_paramDRatNat a b]

theorem polyBounded_wGRat (c d : ℕ) {D : ℕ → ℕ} (hD : PolyBounded fun n _ => D n) :
    PolyBounded fun n _ => wGRat c d (D n) := by
  unfold wGRat
  growth_poly [hD, polyBounded_paramGRatNat c d hD]

theorem steps_tDRat {a b : ℕ} (hb : b ≠ 0) (hab : a ≤ b) :
    StepsMon (fun θ => tDRat a b θ.n) 2 2 0 := by
  have hD : StepsMon (fun θ => paramDRatNat a b θ.n) 2 2 0 :=
    (steps_n.mono (by decide)).of_le fun _ hθ => paramDRatNat_le_self hb hab hθ.one_le_n_nat
  unfold tDRat
  growth [hD]

theorem steps_tGRat {c d : ℕ} (hd : d ≠ 0) (hcd : c ≤ d) :
    StepsMon (fun θ => tGRat c d θ.D) 2 2 0 := by
  have hG : StepsMon (fun θ => paramGRatNat c d θ.D) 2 2 0 :=
    (steps_D.mono (by decide)).of_le fun _ hθ => paramGRatNat_le_self hd hcd hθ.one_le_D_nat
  unfold tGRat
  growth [hG]

end ImprovedExponents.ParamRoutines




/-!
# The all-edges host solves all-edges Exact Triangle; the program, assembled

The specification of the core (`aeCore_spec`, as `ImprovedExponents.HostMid.et17_spec'`) and of the
top procedure (`aeTop_spec`), the list `aeProcs` of the procedures (the variant host's `et17Procs'`
with the all-edges procedures appended), and `ae17_solves`: with a solver of Lop-AE-SparseTri and
two parameter procedures, the program solves `aeTask` with the time `hostTimeAE` and the need
`hostNeedAE`, which stays polynomial (`hostNeedAE_poly`).
-/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec HostMid

variable {P₀ R : Program} {ν : Et17Nums} {pScanPairsAE pFill pBruteAE pLoopAE : ℕ}
  {Tn : List ℕ → ℕ} {need : List ℕ → Need} {Dfun Gfun tD tG wD wG : ℕ → ℕ} {lim : Limits} {d : ℕ}

/-! ## The core -/

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/ParametersStage.lean
open Et17 in
/-- **The small case**: the call of the all-edges brute force, which writes the flags at the free
pointer and returns it. -/
theorem aeSmall_spec
    (C : AeCtx P₀ R ν pScanPairsAE pFill pBruteAE pLoopAE Tn need Dfun Gfun tD tG wD wG)
    (x : TriInst) (μ : ℕ → ℤ) (fr D g a b : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeedCoreAt a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (.call pBruteAE [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v Free] 0)
      ⟨frame (et17LocA x fr D g), μ⟩ (tBruteAE x.n + 8)
      fun σ' => ∃ flg : ℕ, fr ≤ flg ∧ flg + x.n * x.n ≤ lim.space ∧ σ'.loc 0 = flg ∧
        Seg σ'.mem flg (aeFlags x.n x.AB x.BC x.AC) ∧ Kept μ σ'.mem fr := by
  have hok' := hostNeedAt'_ok hok
  have hbrute : (bruteNeed x.n x.U).Ok lim fr (d + 1) :=
    hok'.mono (by simp only [bruteNeed, hostNeedAt', hostWord]; omega)
      (by simp only [bruteNeed]; omega) (by simp only [bruteNeed, hostNeedAt']; omega)
  have hdepth := hok.depth
  have hcells := hok.cells
  simp only [hostNeedCoreAt, hostNeedAt'] at hdepth hcells
  refine Ends.callTo (bruteAE_meets C.bruteAE C.base.loop.scan x μ fr hpre hbrute (by omega)) ?_
    (by simp [et17LocA])
  rintro _ _ ⟨rfl, hseg, hkept⟩
  exact ⟨fr, le_rfl, by omega, by simp [et17LocA], hseg, hkept⟩

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Correct.lean
/-- **The core of the all-edges host**: within `hostCoreTime`, it returns the address of the flags
of all-edges Exact Triangle, which lie at or above the free pointer; no cell below the free
pointer changes. -/
theorem aeCore_spec
    (C : AeCtx P₀ R ν pScanPairsAE pFill pBruteAE pLoopAE Tn need Dfun Gfun tD tG wD wG)
    (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeedCore Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (aeCoreBody ν pBruteAE pLoopAE) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩
      (hostCoreTime Dfun Gfun tD tG Tn x.n x.U)
      fun σ' => ∃ flg : ℕ, fr ≤ flg ∧ flg + x.n * x.n ≤ lim.space ∧ σ'.loc 0 = flg ∧
        Seg σ'.mem flg (aeFlags x.n x.AB x.BC x.AC) ∧ Kept μ σ'.mem fr := by
  have : (hostNeed' Dfun Gfun wD wG need x.n x.U).Ok lim fr d := hostNeedAt'_ok hok
  have hparams := et17Params_spec' C.base x μ fr hpre this
  have : (1 : ℤ) ≤ lim.word := by
    have hword := hok.word
    simp only [hostNeedCore, hostNeedCoreAt, hostNeedAt', hostWord] at hword
    omega
  rw [← frame_append_zeros [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, fr] 29]
  unfold hostNeedCore at hok
  unfold aeCoreBody hostCoreTime hostSetup
  generalize Dfun x.n = D at *
  generalize Gfun D = g at *
  -- the parameters
  refine Ends.next _ (hparams.mono le_rfl ?_) (by omega)
  rintro _ rfl
  -- if n is small: the brute force
  by_cases hs : SmallCase x.n D g
  · rw [ite_eq_left hs]
    exact Ends.iteLast (fun _ => (aeSmall_spec C x μ fr D g _ _ hpre hok).mono
      (by simp; omega) fun _ h => h) (fun h => absurd (by simp [et17LocA, hs]) h) (by simp; omega)
  rw [ite_eq_right hs]
  refine Ends.iteLast (fun h => absurd h (by simp [et17LocA, hs])) (fun _ => ?_) (by simp; omega)
  -- otherwise: the sizes, then the tables and the loop over the instances
  have hbig := not_smallCase_iff.1 hs
  have := hostRunTimeAE_le hpre hbig Tn
  refine Ends.next _ ((et17Sizes_spec' C.base x μ fr D g _ _ hpre hbig (hostNeedAt'_ok hok)).mono
    le_rfl ?_) (by unfold hostMainAE; simp; omega)
  rintro _ ⟨μ', rfl, hk⟩
  refine (et17TablesAE_spec C x μ' fr D g _ _ (hpre.keep hk) hbig hok).mono
    (by unfold hostMainAE; simp; omega) ?_
  rintro σ'' ⟨flg, hfr, hsp, hres, hseg, hk'⟩
  exact ⟨flg, hfr, hsp, hres, hseg, fun a ha => (hk' a ha).trans (hk a ha)⟩

/-! ## The top procedure -/

/-- **The all-edges host decides all-edges Exact Triangle.**  In a program `P₀ ++ R` that
satisfies the context, with the core at `pCore` and `copy` at `pCopy`, on an instance with
`x.Pre μ fr` and within limits that allow for `hostNeedAE`, the top procedure ends within
`hostTimeAE` steps in a state that satisfies `aeTask.Post`. -/
theorem aeTop_spec {pCore pCopy : ℕ}
    (C : AeCtx P₀ R ν pScanPairsAE pFill pBruteAE pLoopAE Tn need Dfun Gfun tD tG wD wG)
    (hCore : (P₀ ++ R)[pCore]? = some (aeCoreBody ν pBruteAE pLoopAE))
    (hCopy : (P₀ ++ R)[pCopy]? = some copyBody)
    (x : AeInst) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeedAE Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (aeTopBody pCore pCopy)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr], μ⟩
      (hostTimeAE Dfun Gfun tD tG Tn x.n x.U) fun σ' => aeTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hdepth := hok.depth
  have hcells := hok.cells
  have hw := hok.space
  simp only [hostNeedAE, hostNeedCore, hostNeedCoreAt, hostNeedAt'] at hdepth hcells
  have hok₁ : (hostNeedCore Dfun Gfun wD wG need x.n x.U).Ok lim fr (d + 1) :=
    hok.mono le_rfl le_rfl (by simp only [hostNeedAE]; omega)
  have : 3 * (x.n * x.n) ≤ hostLayout x.n x.U (Dfun x.n) := by unfold hostLayout; omega
  have := hpre.belowOut
  unfold aeTopBody hostTimeAE
  -- flg := aeCore(n, U, ab, bc, ac, fr)
  have hcore : Ends lim (P₀ ++ R) (d + 1) (aeCoreBody ν pBruteAE pLoopAE)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩ (hostCoreTime Dfun Gfun tD tG Tn x.n x.U)
      fun σ' => ∃ flg : ℕ, fr ≤ flg ∧ flg + x.n * x.n ≤ lim.space ∧ σ'.loc 0 = flg ∧
        Seg σ'.mem flg (aeFlags x.n x.AB x.BC x.AC) ∧ Kept μ σ'.mem fr :=
    aeCore_spec C x.tri μ fr hpre.tri hok₁
  light_call (Meets.of_body (Q := fun r μ' => ∃ flg : ℕ, fr ≤ flg ∧ flg + x.n * x.n ≤ lim.space ∧
      r = flg ∧ Seg μ' flg (aeFlags x.n x.AB x.BC x.AC) ∧ Kept μ μ' fr) hCore hcore)
    with r μ₁ ⟨flg, hfr, hsp, rfl, hseg, hkept⟩
  -- flg := copy(flg, out, n * n)
  have hn : ((x.n * x.n : ℕ) : ℤ) = (x.n : ℤ) * (x.n : ℤ) := by push_cast; rfl
  have hsep : Apart flg (x.n * x.n) x.out (x.n * x.n) := Or.inr (by omega)
  refine Ends.callTo (copy_meets hCopy hw hsp (by omega) hsep)
    ?_ (by light_side [hn])
  rintro _ μ₂ ⟨hcopy, hsame⟩
  refine ⟨fun i hi => ?_, fun c hc => ?_⟩
  · rw [length_aeFlags] at hi
    change μ₂ (x.out + i) = _
    rw [hcopy i hi]
    exact hseg i (by rw [length_aeFlags]; exact hi)
  · exact (hsame c hc.2).trans (hkept c hc.1)

theorem exists_aeFlags_ne_zero_iff (n : ℕ) (AB BC AC : List ℤ) :
    (∃ q < n * n, (aeFlags n AB BC AC).getD q 0 ≠ 0) ↔ (triOf n AB BC AC).HasZeroTriangle := by
  rw [← hasZero_iff]
  simp only [hasZero, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨q, hq, hne⟩
    have hn : 0 < n := by rcases n with _ | n <;> simp_all
    have ha : q / n < n := Nat.div_lt_of_lt_mul' hq
    have hb : q % n < n := Nat.mod_lt q hn
    rw [show q = q / n * n + q % n from (Nat.div_add_mod' q n).symm,
      aeFlags_getD_eq_bit_scanHit _ _ _ ha hb] at hne
    exact ⟨q / n, ha, q % n, hb,
      by cases h : scanHit n AB BC AC (q / n) (q % n) 0 n <;> simp_all [bit]⟩
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨a * n + b, Nat.mul_add_lt_mul ha hb, ?_⟩
    rw [aeFlags_getD_eq_bit_scanHit _ _ _ ha hb, h]
    decide

def aeEtRound : Stmt :=
  .ite (M (v 6) =' k 0) .skip (.set 0 (k 1)) ;;
  .set 6 (v 6 +' k 1)

def aeEtBody (pCore : ℕ) : Stmt :=
  .call pCore [v 0, v 1, v 2, v 3, v 4, v 5] 6 ;;
  .set 7 (v 6 +' v 0 *' v 0) ;;
  .set 0 (k 0) ;;
  .while (v 6 <' v 7) aeEtRound

theorem aeEtRound_runs {μ : ℕ → ℤ} {u ab bc ac fr flg end_ q : ℕ} {P : Prop}
    {v : ℤ} (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word)
    (hread : μ (flg + q) = v) (hlt : flg + q < lim.space) :
    aeEtRound.Runs lim ⟨frame [flag P, u, ab, bc, ac, fr, (flg + q : ℕ), (end_ : ℕ)], μ⟩
      (· = ⟨frame [flag (P ∨ v ≠ 0), u, ab, bc, ac, fr, (flg + (q + 1) : ℕ), (end_ : ℕ)], μ⟩) := by
  classical
  by_cases hv : v = 0 <;> by_cases hP : P <;>
    exact ⟨by
      simp [aeEtRound, Limits.Addr, abs_le, update_frame_setLocal, hread, hv, hP, flag]; omega,
      by simp [aeEtRound, update_frame_setLocal, hread, hv, hP, flag, add_assoc]⟩

theorem aeEt_spec {P : Program} {pCore T : ℕ} {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hd : d < lim.depth) (h1 : (1 : ℤ) ≤ lim.word) (hw : (lim.space : ℤ) ≤ lim.word)
    (hCore : Meets lim P pCore (d + 1) [x.n, x.U, x.ab, x.bc, x.ac, fr] μ T
      fun r μ' => ∃ flg : ℕ, fr ≤ flg ∧ flg + x.n * x.n ≤ lim.space ∧
        r = flg ∧ Seg μ' flg (aeFlags x.n x.AB x.BC x.AC) ∧ Kept μ μ' fr) :
    Ends lim P d (aeEtBody pCore)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩
      (T + copyTime (x.n * x.n) + 20) fun σ' => etTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  rw [← frame_append_zeros [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, fr] 2]
  unfold aeEtBody
  light_call hCore with r μ₁ ⟨flg, hfr, hsp, rfl, hseg, hkept⟩
  have hlen : (aeFlags x.n x.AB x.BC x.AC).length = x.n * x.n := length_aeFlags ..
  have hiff := exists_aeFlags_ne_zero_iff x.n x.AB x.BC x.AC
  generalize aeFlags x.n x.AB x.BC x.AC = F at hseg hlen hiff
  have hn : (0 : ℤ) ≤ (x.n : ℤ) * (x.n : ℤ) := by positivity
  light_set (flg + x.n * x.n : ℕ)
  light_set (0 : ℕ)
  refine Ends.whileBlock (fun q σ => σ = ⟨frame [
      flag (∃ j < q, F.getD j 0 ≠ 0),
      x.U, x.ab, x.bc, x.ac, fr, (flg + q : ℕ), (flg + x.n * x.n : ℕ)], μ₁⟩)
    (x.n * x.n) ?start ?round ?done (by light_time [aeEtRound, copyTime])
  case start =>
    rw [flag_of_not (not_exists.2 fun _ ⟨h, _⟩ => Nat.not_lt_zero _ h), Nat.add_zero]
    rfl
  case round =>
    rintro q _ hq rfl
    have hread : μ₁ (flg + q) = F.getD q 0 := hseg.getD (by omega) 0
    have hex : (∃ j < q + 1, F.getD j 0 ≠ 0) ↔
        (∃ j < q, F.getD j 0 ≠ 0) ∨ F.getD q 0 ≠ 0 :=
      ⟨fun ⟨j, hj, h⟩ => (Nat.lt_succ_iff_lt_or_eq.1 hj).imp (⟨j, ·, h⟩) (by rintro rfl; exact h),
        fun h => h.elim (fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩) (⟨q, by omega, ·⟩)⟩
    refine ⟨by light_side, by simp; omega, ?_⟩
    rw [flag_congr hex]
    exact aeEtRound_runs hw h1 hread (by omega)
  case done =>
    rintro _ rfl
    refine ⟨by light_side, by simp, ?_, hkept⟩
    simp only [frame, List.getD_cons_zero]
    exact flag_congr hiff

/-! ## The program -/

def aeProcs (pS pD pG o : ℕ) : Program :=
  let ν := et17NumsAt pS pD pG o
  [sqrtBody,
    scanBody,
    .skip,
    primesBody ν.ch.pSqrt ν.ch.pSieve,
    bitLenBody,
    dblTableBody,
    residBody,
    residuesBody ν.pResid,
    spreadTableBody,
    szTableBody,
    buildZBody,
    countZeroBody,
    vlinBody,
    cconvBody,
    fillBody,
    phaseBody ν.ch.cp.str,
    strBody ν.ch.cp.str,
    countPrimeBody ν.ch.cp,
    choosePrimeBody ν.ch,
    queryCapNatBody,
    ceilDivBody,
    classesBody,
    chunksBody,
    writeXBody,
    writeYBody,
    .skip,
    .skip,
    .skip,
    sieveBody,
    scanPairsAEBody (o + 1),
    bruteAEBody (o + 1),
    hostLoopAEBody pS (o + 23) (o + 24) (o + 29) (o + 14),
    aeCoreBody ν (o + 30) (o + 31),
    aeTopBody (o + 32) (o + 34),
    copyBody,
    aeEtBody (o + 32)]

def iTop : ℕ := 33

variable {pS pD pG : ℕ}

theorem aeCtx_assembled (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) (R : Program) :
    AeCtx P₀ (aeProcs pS pD pG P₀.length ++ R) (et17NumsAt pS pD pG P₀.length)
      (P₀.length + 29) (P₀.length + 14) (P₀.length + 30) (P₀.length + 31) Tn need Dfun Gfun tD tG
      wD wG := by
  have L : ∀ {i : ℕ} {body : Stmt}, (aeProcs pS pD pG P₀.length)[i]? = some body →
      (P₀ ++ (aeProcs pS pD pG P₀.length ++ R))[P₀.length + i]? = some body :=
    fun h => getElem?_append_append R h
  exact
    { base :=
        { loop := ⟨hsol, L rfl, L rfl, L rfl⟩
          hSqrt := L (i := 0) rfl
          hChoose := L rfl
          ch := ⟨L rfl, L rfl, L rfl,
            ⟨L rfl, L rfl, L rfl, L rfl, L rfl,
              L rfl, L rfl,
              ⟨L rfl, L rfl, L rfl, L rfl, L rfl⟩⟩,
            ⟨L (i := 0) rfl, L rfl⟩⟩
          hCap := L rfl
          hCeil := L rfl
          hBitLen := L rfl
          hDbl := L rfl
          hResid := L rfl
          hResidues := L rfl
          hClasses := L rfl
          hChunks := L rfl
          dProc := hD _
          gProc := hG _
          D_pos := hpos }
      scanPairsAE := L (i := 29) rfl
      fill := L (i := 14) rfl
      bruteAE := L (i := 30) rfl
      loopAE := L (i := 31) rfl }

theorem ae17_solves (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) :
    Solves aeTask (P₀ ++ aeProcs pS pD pG P₀.length) (P₀.length + iTop)
      (hostTimeAE Dfun Gfun tD tG Tn) (hostNeedAE Dfun Gfun wD wG need) := by
  refine ⟨aeTopBody (P₀.length + 32) (P₀.length + 34), ?_, fun R lim d x μ fr hpre hok => ?_⟩
  · have htop := getElem?_append_append (P₀ := P₀) (B := aeProcs pS pD pG P₀.length) []
      (i := 33) rfl
    rwa [List.append_nil] at htop
  · rw [List.append_assoc]
    have C := aeCtx_assembled hsol hD hG hpos R
    exact aeTop_spec C (getElem?_append_append R (i := 32) rfl)
      (getElem?_append_append R (i := 34) rfl) x μ fr hpre hok

theorem etAE_solves (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) :
    Solves etTask (P₀ ++ aeProcs pS pD pG P₀.length) (P₀.length + 35)
      (hostTimeAE Dfun Gfun tD tG Tn) (hostNeedAE Dfun Gfun wD wG need) := by
  refine ⟨aeEtBody (P₀.length + 32), ?_, fun R lim d x μ fr hpre hok => ?_⟩
  · simpa using getElem?_append_append (P₀ := P₀) (B := aeProcs pS pD pG P₀.length) [] (i := 35) rfl
  · rw [List.append_assoc]
    change (hostNeedAE Dfun Gfun wD wG need x.n x.U).Ok lim fr d at hok
    have hword := hok.word
    have hdepth := hok.depth
    simp only [hostNeedAE, hostNeedCore, hostNeedCoreAt, hostNeedAt', hostWord] at hword hdepth
    have hok₁ : (hostNeedCore Dfun Gfun wD wG need x.n x.U).Ok lim fr (d + 1) :=
      hok.mono le_rfl le_rfl (by simp only [hostNeedAE]; omega)
    exact aeEt_spec (by omega) (by omega) hok.space
      (Meets.of_body (getElem?_append_append R (i := 32) rfl)
        (aeCore_spec (aeCtx_assembled hsol hD hG hpos R) x μ fr hpre hok₁))

/-! ## The need stays polynomial -/

theorem hostNeedAE_poly (hD : PolyBounded fun n _ => Dfun n)
    (hG : PolyBounded fun n _ => Gfun (Dfun n)) (hwD : PolyBounded fun n _ => wD n)
    (hwG : PolyBounded fun n _ => wG (Dfun n)) (h : PolyNeedN need) :
    PolyNeed (hostNeedAE Dfun Gfun wD wG need) := by
  obtain ⟨s, k, hle⟩ := hostNeed_poly hD hG hwD hwG (polyNeedN_midArgs Gfun h)
  refine ⟨1 + (s + 0), k + 2, fun n U => ?_⟩
  obtain ⟨hw, hc, hd⟩ := hle n U
  have hsq : n * n ≤ polyBound 0 2 [n, U] := by
    simp only [polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      pow_zero, one_mul]
    calc n * n ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n)
      _ ≤ ((n + 1) * (U + 1)) * ((n + 1) * (U + 1)) := Nat.mul_le_mul
          (Nat.le_mul_of_pos_right _ (Nat.succ_pos U)) (Nat.le_mul_of_pos_right _ (Nat.succ_pos U))
      _ = ((n + 1) * (U + 1)) ^ 2 := (sq _).symm
  have hone : 1 ≤ polyBound 0 2 [n, U] := one_le_polyBound 0 2 [n, U]
  have hmono := polyBound_mono (Nat.le_add_right s 0 |>.trans (Nat.le_add_left _ 1))
    (Nat.le_add_right k 2) [n, U]
  refine ⟨hw.trans hmono, ?_, ?_⟩
  · exact add_le_polyBound hc hsq
  · exact (Nat.add_le_add hd hone).trans (add_le_polyBound le_rfl le_rfl)






open ParamRoutines

noncomputable def bound17Mid (MM : ℕ → ℝ) (D g : ℕ → ℕ) (C : ℝ) (T : ℕ → ℕ → ℕ → ℝ) (n : ℕ)
    (κ : ℝ) : ℝ :=
  4 * (n : ℝ) * (g n : ℝ) *
      (T n (midSize (D n) (g n)) (queryCap n (D n)) + C * ((n : ℝ) ^ 2 / Real.sqrt (D n))) +
    C * (termScans n (g n) κ + termPrime MM n (D n) + termBuild n (D n) (g n))

def ObeysBound17Mid (MM : ℕ → ℝ) (D g : ℕ → ℕ) (time : (List ℕ → ℕ) → ℕ → ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (Tn : List ℕ → ℕ) (T : ℕ → ℕ → ℕ → ℝ),
    (∀ m d w w' : ℕ, 1 ≤ m → 1 ≤ d → w ≤ w' → (Tn [m, d, w] : ℝ) ≤ T m d w') →
    ∀ (n U : ℕ) (κ : ℝ), 16 ≤ D n → D n ≤ n → 1 ≤ g n → (g n : ℝ) ≤ Real.sqrt (D n) → 1 ≤ κ →
      (U : ℝ) ≤ (n : ℝ) ^ κ → (time Tn n U : ℝ) ≤ bound17Mid MM D g C T n κ

theorem supTime_zero (n D cap : ℕ) : supTime (fun _ => 0) n D cap = 0 := by
  simp [supTime]

theorem not_smallCase_of_hyp {n D g : ℕ} (h16 : 16 ≤ D) (hDn : D ≤ n) (hg1 : 1 ≤ g)
    (hg : (g : ℝ) ≤ Real.sqrt D) : ¬ SmallCase n D g := by
  have : g ≤ Nat.sqrt D := by
    rw [Nat.le_sqrt']
    exact_mod_cast (Real.le_sqrt g.cast_nonneg D.cast_nonneg).1 hg
  unfold SmallCase
  omega

noncomputable def hostRestAE (tD tG : ℕ → ℕ) (θ : CostParams) : ℕ :=
  hostSetup tD tG θ.n θ.D + hostMainAE (fun _ => 0) θ.n θ.U θ.D θ.g + copyTime (θ.n * θ.n) + 20

theorem hostTimeAE_eq {Dfun Gfun : ℕ → ℕ} (tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) {θ : CostParams}
    (hD : Dfun θ.n = θ.D) (hG : Gfun θ.D = θ.g) (hs : ¬ SmallCase θ.n θ.D θ.g) :
    hostTimeAE Dfun Gfun tD tG Tn θ.n θ.U
      = 4 * θ.n * θ.g * supTime Tn θ.n (midSize θ.D θ.g) (queryCapNat θ.n θ.D)
        + hostRestAE tD tG θ := by
  unfold hostTimeAE hostCoreTime hostRestAE
  rw [hD, hG]
  simp only [ite_eq_right hs]
  unfold hostMainAE hostLoopBoundAE
  rw [supTime_zero]
  ring

noncomputable def restBoundAE (θ : CostParams) : ℝ :=
  (θ.n : ℝ) * θ.g * ((θ.n : ℝ) ^ 2 / Real.sqrt θ.D) + budget θ

theorem stepsRestAE_of_budget {t : CostParams → ℕ} (h : Steps t budget) : Steps t restBoundAE :=
  h.mono_right fun θ _ => le_add_of_nonneg_left (by positivity)

theorem steps_tScanCallAE :
    Steps (fun θ => tScanCallAE (pieceSizeNat θ.D θ.g)) fun θ => Real.sqrt θ.D / θ.g := by
  have hone : ∀ θ : CostParams, θ.Hyp → 1 ≤ Real.sqrt θ.D / θ.g := fun _ hθ =>
    (one_le_div hθ.g_pos).2 hθ.hgD
  have hpiece : Steps (fun θ => pieceSizeNat θ.D θ.g) fun θ => Real.sqrt θ.D / θ.g := by
    refine Dominated.of_le_const_mul (C := 2) (by norm_num) fun θ hθ => ?_
    have hlt : (pieceSizeNat θ.D θ.g : ℝ) * θ.g < (Nat.sqrt θ.D : ℝ) + θ.g := by
      exact_mod_cast Nat.ceilDiv_mul_lt (a := Nat.sqrt θ.D) hθ.hg
    rw [← mul_div_assoc, le_div_iff₀ hθ.g_pos]
    linarith [hlt, Real.nat_sqrt_le_real_sqrt (a := θ.D), hθ.hgD]
  exact (hpiece.const_mul.add (.const hone)).add (.const hone)

theorem steps_falsePositiveBoundAE :
    Steps (fun θ => falsePositiveBound θ.n θ.U θ.D + θ.n * θ.n) fun θ =>
      θ.κ * (θ.n : ℝ) ^ 3 * Real.log θ.n / Real.sqrt θ.D := by
  have hconst : 0 ≤ Hashing.falsePositiveConst :=
    zero_le_one.trans Hashing.one_le_falsePositiveConst
  refine Steps.add (Dominated.of_le_const_mul hconst fun θ hθ => (Nat.floor_le ?_).trans ?_)
    (.of_le fun θ hθ => ?_)
  · have : 0 ≤ kappaOf θ.n θ.U := zero_le_one.trans (one_le_kappaOf θ.n θ.U)
    positivity
  · gcongr
    rcases Nat.eq_zero_or_pos θ.U with hU | hU
    · simp [kappaOf, hU, hθ.hκ]
    · exact kappaOf_le ((by norm_num : 2 ≤ 16).trans hθ.sixteen_le_n) hU hθ.hκ hθ.hUn
  · rw [le_div_iff₀ hθ.sqrt_pos]
    calc ((θ.n * θ.n : ℕ) : ℝ) * Real.sqrt θ.D
        ≤ (θ.n : ℝ) ^ 3 := by
          push_cast
          calc (θ.n : ℝ) * θ.n * Real.sqrt θ.D ≤ (θ.n : ℝ) * θ.n * θ.n :=
                mul_le_mul_of_nonneg_left hθ.sqrt_le_n (by positivity)
            _ = (θ.n : ℝ) ^ 3 := by ring
      _ = mon 3 0 0 θ := by simp [mon_eq]
      _ ≤ mon 3 0 1 θ := Scale.mon_le_mon (by decide) hθ
      _ = θ.κ * (θ.n : ℝ) ^ 3 * Real.log θ.n := by rw [mon_eq]; ring

theorem steps_scans :
    Steps (fun θ => tScanCallAE (pieceSizeNat θ.D θ.g) * (falsePositiveBound θ.n θ.U θ.D + θ.n * θ.n))
      budget := by
  refine (steps_tScanCallAE.mul steps_falsePositiveBoundAE).mono_right fun θ hθ =>
    le_trans (le_of_eq ?_) (termScans_le_budget θ)
  have : 0 < Real.sqrt θ.D := hθ.sqrt_pos
  have : (0 : ℝ) < θ.g := hθ.g_pos
  unfold termScans
  field_simp

theorem steps_instances : Steps (fun θ => 4 * θ.n * θ.g) fun θ => (θ.n : ℝ) * θ.g :=
  (Steps.const_mul (Dominated.refl _ _)).mul (Dominated.refl _ _)

theorem steps_tWrites :
    StepsMon (fun θ => tWrites θ.n θ.D (pieceSizeNat θ.D θ.g)) 1 2 0 := by
  unfold tWrites
  growth [steps_tWriteX, steps_tWriteY]

theorem steps_instances_mul_tWrites :
    Steps (fun θ => 4 * θ.n * θ.g * tWrites θ.n θ.D (pieceSizeNat θ.D θ.g)) budget :=
  (steps_instances.mul (steps_of_softO steps_tWrites)).mono_right fun θ hθ =>
    le_trans (le_of_eq (by
      simp only [termBuild, mon_eq, pow_zero, mul_one, pow_one, Real.sq_sqrt θ.D.cast_nonneg]
      ring)) (termBuild_le_budget hθ)

theorem steps_tAnswersAE :
    Steps (fun θ => tAnswersAE (queryCapNat θ.n θ.D)) fun θ => (θ.n : ℝ) ^ 2 / Real.sqrt θ.D := by
  refine Steps.add (Steps.const_mul (Dominated.of_le fun θ hθ => cast_queryCapNat_le hθ))
    (.const fun θ hθ => ?_)
  rw [one_le_div hθ.sqrt_pos]
  exact hθ.sqrt_le_n.trans (le_self_pow₀ hθ.one_le_n two_ne_zero)

theorem steps_fillAE : StepsMon (fun θ => fillTime (θ.n * θ.n)) 2 0 0 := by
  unfold fillTime
  growth [steps_n]

theorem steps_copyAE : StepsMon (fun θ => copyTime (θ.n * θ.n)) 2 0 0 := by
  unfold copyTime
  growth [steps_n]

theorem steps_hostSetup {tD tG : ℕ → ℕ} (hD : Steps (fun θ => tD θ.n) budget)
    (hG : Steps (fun θ => tG θ.D) budget) : Steps (fun θ => hostSetup tD tG θ.n θ.D) budget :=
  hD.add hG
  |>.add (by growth [steps_sqrt] : StepsMon _ 0 1 0).withinBuild
  |>.add (Scale.SoftO.const _).withinBuild

theorem steps_hostLoopBoundAE :
    Steps (fun θ => hostLoopBoundAE (fun _ => 0) θ.n θ.U θ.D θ.g) restBoundAE :=
  (stepsRestAE_of_budget steps_instances_mul_tWrites)
  |>.mul_add (stepsRestAE_of_budget ((Scale.SoftO.const 0).withinBuild.mono_left fun θ _ => by
    rw [supTime_zero, Nat.mul_zero]))
  |>.mul_add ((steps_instances.mul steps_tAnswersAE).mono_right fun _ hθ =>
    le_add_of_nonneg_right (budget_nonneg hθ))
  |>.add (stepsRestAE_of_budget steps_scans)
  |>.add (stepsRestAE_of_budget steps_fillAE.withinBuild)
  |>.add (stepsRestAE_of_budget (Scale.SoftO.const _).withinBuild)

theorem steps_hostRestAE {tD tG : ℕ → ℕ} (hD : Steps (fun θ => tD θ.n) budget)
    (hG : Steps (fun θ => tG θ.D) budget) : Steps (hostRestAE tD tG) restBoundAE :=
  (stepsRestAE_of_budget (steps_hostSetup hD hG)).add
    ((stepsRestAE_of_budget steps_chooseTime)
      |>.add (stepsRestAE_of_budget steps_tQueryCapNat.withinBuild)
      |>.add (stepsRestAE_of_budget steps_tCeilDiv_piece.withinBuild)
      |>.add (stepsRestAE_of_budget steps_tCeilDiv_num.withinBuild)
      |>.add (stepsRestAE_of_budget steps_tBitLen.withinScans)
      |>.add (stepsRestAE_of_budget steps_tDblTable.withinScans)
      |>.add (stepsRestAE_of_budget ((Scale.SoftO.const _).mul steps_tResidues).withinScans)
      |>.add (stepsRestAE_of_budget steps_tClasses.withinBuild)
      |>.add (stepsRestAE_of_budget steps_tChunks.withinBuild)
      |>.add steps_hostLoopBoundAE
      |>.add (stepsRestAE_of_budget (Scale.SoftO.const _).withinBuild))
  |>.add (stepsRestAE_of_budget steps_copyAE.withinBuild)
  |>.add (stepsRestAE_of_budget (Scale.SoftO.const _).withinBuild)

theorem cast_supTime_le {Tn : List ℕ → ℕ} {T : ℕ → ℕ → ℕ → ℝ}
    (hT : ∀ n D w w' : ℕ, 1 ≤ n → 1 ≤ D → w ≤ w' → (Tn [n, D, w] : ℝ) ≤ T n D w') {n D : ℕ}
    (hn : 1 ≤ n) (hD : 1 ≤ D) (cap : ℕ) : ((supTime Tn n D cap : ℕ) : ℝ) ≤ T n D cap := by
  obtain ⟨w, hw, hsup⟩ : ∃ w ∈ Finset.range (cap + 1),
      (Finset.range (cap + 1)).sup (fun w => Tn [n, D, w]) = Tn [n, D, w] :=
    Finset.exists_mem_eq_sup _ ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ _
  rw [supTime, hsup]
  exact hT n D w cap hn hD (Nat.lt_succ_iff.1 (Finset.mem_range.1 hw))

theorem obeysBound17Mid_hostTimeAE (D g : ℕ → ℕ) {Dfun Gfun tD tG : ℕ → ℕ}
    (hDf : ∀ n, Dfun n = D n) (hGf : ∀ n, 1 ≤ n → Gfun (D n) = g n)
    (hD : Steps (fun θ => tD θ.n) budget) (hG : Steps (fun θ => tG θ.D) budget) :
    ObeysBound17Mid strassen D g (hostTimeAE Dfun Gfun tD tG) := by
  obtain ⟨C, hC, hsteps⟩ := steps_hostRestAE hD hG
  refine ⟨C, hC, fun Tn T hT n U κ h16 hDn hg1 hg hκ hU => ?_⟩
  have hθ : CostParams.Hyp ⟨n, D n, g n, U, κ⟩ := ⟨h16, hDn, hg1, hg, hκ, hU⟩
  have hn1 : 1 ≤ n := hθ.one_le_n_nat
  have hD1 : 1 ≤ D n := hθ.one_le_D_nat
  have hmid : 1 ≤ midSize (D n) (g n) := one_le_midSize h16 hg1
  have hs : ¬ SmallCase n (D n) (g n) := not_smallCase_of_hyp h16 hDn hg1 hg
  have hsolver := cast_supTime_le hT hn1 hmid (queryCapNat n (D n))
  have hrest := hsteps ⟨n, D n, g n, U, κ⟩ hθ
  have hcalls : (4 * (n : ℝ) * g n) * (supTime Tn n (midSize (D n) (g n)) (queryCapNat n (D n)) : ℝ)
      ≤ (4 * (n : ℝ) * g n) * T n (midSize (D n) (g n)) (queryCapNat n (D n)) :=
    mul_le_mul_of_nonneg_left hsolver (by positivity)
  have hquery : 0 ≤ C * ((n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n))) := by positivity
  rw [hostTimeAE_eq (θ := ⟨n, D n, g n, U, κ⟩) tD tG Tn (hDf n) (hGf n hn1) hs]
  rw [queryCapNat_eq n hD1] at hcalls ⊢
  simp only [bound17Mid, restBoundAE, budget] at hrest ⊢
  push_cast
  linarith [hcalls, hrest, hquery]

def _root_.ImprovedExponents.MidHostRat (M : DetTimeModel) : Prop :=
  HostBound M strassen (paramDRat 27 469) (paramGRatOf 27 469 13 358)
    (fun n => pieceSizeNat (paramDRat 27 469 n) (paramGRatOf 27 469 13 358 n)
      * Nat.sqrt (paramDRat 27 469 n))

theorem midHost_of_host {M : DetTimeModel} {task : Task}
    (hM : M.lopDetect = lightModel.lopDetect) (het : M.exactTriangle = SolvedIn task)
    (host : ∀ (Q : Program) (pS : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need),
      SolvesN lopDetectTask Q pS Tn r →
      ∃ (R : Program) (p' : ℕ),
        Solves task (Q ++ R) p'
          (hostTimeAE (paramDRatNat 27 469) (paramGRatNat 13 358)
            (tDRat 27 469) (tGRat 13 358) Tn)
          (hostNeedAE (paramDRatNat 27 469) (paramGRatNat 13 358)
            (wDRat 27 469) (wGRat 13 358) r)) :
    MidHostRat M := by
  obtain ⟨C, hC, bound⟩ := obeysBound17Mid_hostTimeAE (paramDRat 27 469)
    (paramGRatOf 27 469 13 358) (paramDRatNat_eq (by omega) 27)
    (fun _ hn => paramGRatNat_paramDRat (by omega) 27 469 13 (one_le_paramDRat (by omega) 27 hn))
    (steps_tDRat (a := 27) (b := 469) (by omega) (by omega)).withinBuild
    (steps_tGRat (c := 13) (d := 358) (by omega) (by omega)).withinBuild
  refine ⟨C, hC, fun T hT => ?_⟩
  rw [hM] at hT
  obtain ⟨Q, pS, Tn, r, hpoly, hsolves, hle⟩ := hT
  obtain ⟨R, p', hs⟩ := host Q pS Tn r hsolves
  have hp := hostNeedAE_poly (polyBounded_paramDRatNat 27 469)
    (polyBounded_paramGRatNat 13 358 (polyBounded_paramDRatNat 27 469))
    (polyBounded_wDRat 27 469) (polyBounded_wGRat 13 358 (polyBounded_paramDRatNat 27 469)) hpoly
  refine ⟨timeUpTo _, het ▸ hs.solvedIn hp, fun n κ u h16 hDn hg1 hg hκ hu =>
    timeUpTo_le fun U hU =>
      bound Tn T hle n U κ h16 hDn hg1 hg hκ (hU.trans (max_le hu (by positivity)))⟩

theorem midHostRat_ae : MidHostRat lightModelAE :=
  midHost_of_host rfl rfl fun Q _ _ _ hs => by
    have h := ae17_solves (P₀ := Q ++ ratProcs 27 469 13 358 Q.length) (hs.append _)
      (paramProc_dRat (by omega) 27 13 358 Q) (paramProc_gRat (by omega) 27 469 13 Q)
      (fun _ => one_le_paramDRatNat (by omega) 27)
    rw [List.append_assoc] at h
    exact ⟨_, _, h⟩

theorem _root_.ImprovedExponents.midHostRat_light : MidHostRat lightModel :=
  midHost_of_host rfl rfl fun Q _ _ _ hs => by
    have h := etAE_solves (P₀ := Q ++ ratProcs 27 469 13 358 Q.length) (hs.append _)
      (paramProc_dRat (by omega) 27 13 358 Q) (paramProc_gRat (by omega) 27 469 13 Q)
      (fun _ => one_le_paramDRatNat (by omega) 27)
    rw [List.append_assoc] at h
    exact ⟨_, _, h⟩

theorem _root_.ImprovedExponents.claim_bruteForce' : Claim.BruteForce lightModel := by
  refine ⟨300, [aeEtBody 1, bruteAEBody 2, scanBody], 0,
    fun n _ => tBruteAE n + copyTime (n * n) + 20,
    fun n U => ⟨3 * U + 1, n * n, 2⟩, by poly_need [],
    ⟨aeEtBody 1, rfl, fun R lim d x μ fr hpre hok => ?_⟩, fun n U u hn _ _ => ?_⟩
  · change Need.Ok ⟨3 * x.U + 1, x.n * x.n, 2⟩ lim fr d at hok
    have h1 : (1 : ℤ) ≤ lim.word := by have := hok.word; simp at this; omega
    have hd : d < lim.depth := by have := hok.depth; simp at this; omega
    have hb : (bruteNeed x.n x.U).Ok lim fr (d + 1) :=
      hok.mono le_rfl (by simp [bruteNeed]) (by simp [bruteNeed])
    exact aeEt_spec hd h1 hok.space ((bruteAE_meets rfl rfl x μ fr hpre hb hok.cells).mono le_rfl
      fun _ _ ⟨hr, hs, hk⟩ => ⟨fr, le_rfl, hok.cells, hr, hs, hk⟩)
  · have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
    have : (n : ℝ) * n ≤ (n : ℝ) ^ 3 := by nlinarith
    have : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1
    have : 0 ≤ (n : ℝ) ^ 3 * logU u := mul_nonneg (by positivity) (logU_pos u).le
    simp only [tBruteAE, copyTime]
    push_cast
    linarith

end ImprovedExponents.AllEdges
