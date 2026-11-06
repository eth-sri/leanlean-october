module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.InstanceFacts
public import ImprovedExponents.AllEdges.Task

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

open ThreeSumApsp.Spec

/-! ## The flags through the query pairs of one instance -/

section

variable (acc hit : ℕ → Bool) (idx : ℕ → ℕ)

/-- The query pair number `i`, treated with the flags `F`: if it is accepted and its flag is 0, the
result of its scan goes into its flag. -/
def aePair (F : List ℤ) i :=
  if acc i = true ∧ F.getD (idx i) 0 = 0 then F.set (idx i) (bit (hit i)) else F

/-- The flags after the first `i` query pairs have been treated, starting from the flags `F`. -/
def aeStep F
  | 0 => F
  | i + 1 => aePair acc hit idx (aeStep F i) i

/-- A scan is made for the query pair number `i`, if the flags were `F` at first: the pair is
accepted and its flag is still 0. -/
def aeExec F i :=
  acc i && decide ((aeStep acc hit idx F i).getD (idx i) 0 = 0)

/-- The number of scans made for the first `w` query pairs, if the flags were `F` at first. -/
def aeExecs F w := ((List.range w).filter (aeExec acc hit idx F)).length

/-- The number of flags that are not 0. -/
def ones (F : List ℤ) := F.countP fun x => decide (x ≠ 0)

variable {acc hit idx}

@[simp] theorem aeStep_zero F : aeStep acc hit idx F 0 = F := rfl

@[simp] theorem aeStep_succ F i :
    aeStep acc hit idx F (i + 1) = aePair acc hit idx (aeStep acc hit idx F i) i := rfl

@[simp] theorem length_aePair F i :
    (aePair acc hit idx F i).length = F.length := by
  grind [aePair]

@[simp] theorem length_aeStep F i :
    (aeStep acc hit idx F i).length = F.length := by
  induction i <;> simp_all

/-- The cell of a list that is set. -/
theorem getD_set_self (F : List ℤ) {j} (hj : j < F.length) x :
    (F.set j x).getD j 0 = x := by
  simp_all

/-- The bit of a proposition is 0 if and only if the proposition fails. -/
theorem bit_decide_eq_zero P [Decidable P] : bit (decide P) = 0 ↔ ¬P := by
  by_cases h : P <;> simp [bit, h]

theorem aeExecs_succ F w :
    aeExecs acc hit idx F (w + 1) =
      aeExecs acc hit idx F w + if aeExec acc hit idx F w then 1 else 0 := by
  grind [aeExecs, List.range_succ]

/-- The flag of the cell `q` after `i` query pairs: 1 if one of them is accepted, lies in the cell
and hits, else what it was, if the cell was 0 when the instance began. -/
theorem aeStep_getD {F} {q} (hq : q < F.length) i :
    (aeStep acc hit idx F i).getD q 0 =
      if F.getD q 0 = 0 then
        bit (decide (∃ j < i, idx j = q ∧ acc j = true ∧ hit j = true))
      else F.getD q 0 := by
  induction i with
  | zero => simp [aeStep, bit]
  | succ i ih =>
    have hex : (∃ j < i + 1, idx j = q ∧ acc j = true ∧ hit j = true) ↔
        (∃ j < i, idx j = q ∧ acc j = true ∧ hit j = true) ∨
          idx i = q ∧ acc i = true ∧ hit i = true := by
      grind
    rw [aeStep_succ, aePair]
    by_cases hpq : idx i = q
    · -- the pair `i` lies in the cell `q`
      rw [hpq]

      split_ifs with h0 hF hF
      · -- it is scanned: its flag was 0, so no earlier pair in the cell hit
        rw [ih, ite_eq_left hF, bit_decide_eq_zero] at h0
        rw [getD_set_self _ (by rwa [length_aeStep])]
        simp_all
      · grind
      · -- it is not scanned: not accepted, or an earlier pair in the cell hit
        rw [ih, ite_eq_left hF, bit_decide_eq_zero] at h0
        rw [ih, ite_eq_left hF]
        congr 1
        rw [decide_eq_decide, hex]
        grind
      · rw [ih, ite_eq_right hF]
    · -- the pair `i` lies in another cell
      aesop

/-- The number of flags that are not 0 is at most the number of flags. -/
theorem ones_le_length F : ones F ≤ F.length := List.countP_le_length

/-- Treating one query pair: a scan fails or raises the number of flags that are not 0. -/
theorem aeExec_add_ones_le F {i} (hidx : idx i < F.length) :
    (if aeExec acc hit idx F i then 1 else 0) + ones (aeStep acc hit idx F i) ≤
      (if acc i && !hit i then 1 else 0) + ones (aeStep acc hit idx F (i + 1)) := by
  grind [length_aeStep, aeStep_succ, aePair, aeExec, ones, bit]

/-- **Each scan fails or raises the number of flags that are 1**: through `w` query pairs whose
cells lie within the flags. -/
theorem aeExecs_add_ones_le F {w} (hidx : ∀ i < w, idx i < F.length) :
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
theorem aeStep_congr {acc' hit'} {idx'} F {w}
    (h : ∀ i < w, acc i = acc' i ∧ hit i = hit' i ∧ idx i = idx' i) :
    aeStep acc hit idx F w = aeStep acc' hit' idx' F w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    obtain ⟨ha, hh, hi⟩ := h w (Nat.lt_succ_self w)
    rw [aeStep_succ, aeStep_succ, ih fun i hi => h i (by omega), aePair, aePair, ha, hh, hi]

/-- The number of scans depends only on the first `w` query pairs. -/
theorem aeExecs_congr {acc' hit'} {idx'} F {w}
    (h : ∀ i < w, acc i = acc' i ∧ hit i = hit' i ∧ idx i = idx' i) :
    aeExecs acc hit idx F w = aeExecs acc' hit' idx' F w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    obtain ⟨ha, hh, hi⟩ := h w (Nat.lt_succ_self w)
    rw [aeExecs_succ, aeExecs_succ, ih fun i hi => h i (by omega), aeExec, aeExec, ha, hi,
      aeStep_congr F fun i hi => h i (by omega)]

end

/-! ## The flags through the instances of the host -/

namespace HostData

variable (X : HostData)

/-- The cell `a n + b` of the query pair number `i` of instance `t`. -/
def pairIdx t i := X.rowOf t i * X.n + X.colOf t i

/-- The flags after the first `i` query pairs of instance `t` have been treated, starting from the
flags `F`. -/
def flagsStep t F i := aeStep (X.acc t) (X.hit t) (X.pairIdx t) F i

/-- The flags when instance `t` begins: all 0 at first. -/
def flagsAt
  | 0 => List.replicate (X.n * X.n) 0
  | t + 1 => X.flagsStep t (flagsAt t) (X.w t)

/-- The number of scans made for instance `t`. -/
def execsAE t := (aeExecs (X.acc t) (X.hit t) (X.pairIdx t) (X.flagsAt t) (X.w t) : ℕ)

theorem flagsStep_def t F i :
    X.flagsStep t F i = aeStep (X.acc t) (X.hit t) (X.pairIdx t) F i := rfl

@[simp] theorem length_flagsStep t F i :
    (X.flagsStep t F i).length = F.length := length_aeStep _ _

@[simp] theorem length_flagsAt t : (X.flagsAt t).length = X.n * X.n := by
  induction t with
  | zero => simp [flagsAt]
  | succ t ih => rw [flagsAt, length_flagsStep, ih]

/-- The flag of the cell `q < n²` when instance `T` begins: 1 if an accepted query pair of an
earlier instance lies in the cell and hits, 0 if not. -/
theorem flagsAt_getD {T q} (hq : q < X.n * X.n) :
    (X.flagsAt T).getD q 0 =
      bit (decide (∃ t < T, ∃ i < X.w t, X.pairIdx t i = q ∧ X.acc t i = true ∧
        X.hit t i = true)) := by
  induction T with
  | zero => simp [flagsAt, List.getD_eq_getElem?_getD, hq, bit]
  | succ T ih =>
    have hex : (∃ t < T + 1, ∃ i < X.w t, X.pairIdx t i = q ∧ X.acc t i = true ∧
        X.hit t i = true) ↔
        (∃ t < T, ∃ i < X.w t, X.pairIdx t i = q ∧ X.acc t i = true ∧ X.hit t i = true) ∨
          ∃ i < X.w T, X.pairIdx T i = q ∧ X.acc T i = true ∧ X.hit T i = true := by
      grind
    rw [flagsAt, flagsStep_def, aeStep_getD (by rw [length_flagsAt]; exact hq), ih]
    simp only [bit, hex, decide_eq_true_eq]
    by_cases hprev : ∃ t < T, ∃ i < X.w t, X.pairIdx t i = q ∧ X.acc t i = true ∧ X.hit t i = true
    · simp [hprev]
    · simp [hprev]

/-- The cell of the query pair number `i` of instance `t`, in the lists of rows and columns that the
host writes. -/
theorem pairIdx_eq {t i} (hi : i < X.w t) :
    X.pairIdx t i = (X.WI t).getD i 0 * X.n + (X.WJ t).getD i 0 := by
  rw [pairIdx, getD_WI hi, getD_WJ hi]

variable {X} in
/-- The cells of the query pairs of an instance lie within the `n²` flags. -/
theorem Valid.pairIdx_lt (hv : X.Valid) {t i } (ht : t < X.m) (hi : i < X.w t) :
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
  have ha := Nat.div_lt_of_lt_mul' hq
  have hb := Nat.mod_lt_of_lt_mul hq
  have hdivmod := Nat.div_add_mod' q X.n
  rw [X.flagsAt_getD hq, ← hdivmod,
    ImprovedExponents.AllEdges.aeFlags_getD_eq_bit_scanHit _ _ _ ha hb, hdivmod]
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [scanHit, List.any_eq_true, List.mem_range, decide_eq_true_eq, Nat.add_zero, hdivmod]
  constructor
  · rintro ⟨t, ht, i, hi, hpq, -, hhit⟩
    obtain ⟨c, hc, hzero⟩ := (hit_iff hi).1 hhit
    have  := hv.piece_le ht
    have hcol := hv.colOf_lt ht hi
    have hrow : X.rowOf t i = q / X.n := by
      rw [← hpq, pairIdx, Nat.mul_add_div_of_lt hcol]

    refine ⟨X.c0 t + c, by omega, ?_⟩
    rw [sumAt, hrow, (by
      simp_all [pairIdx] <;> omega
     : X.colOf t i = q % X.n), hdivmod] at hzero
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
      have  : X.execsAE T + ones (X.flagsAt T) ≤ X.fails T + ones (X.flagsAt (T + 1)) :=
        aeExecs_add_ones_le (X.flagsAt T) fun i hi => by
          rw [length_flagsAt]
          exact hv.pairIdx_lt (by omega) hi
      grind [Finset.sum_range_succ]
  have hle := ones_le_length (X.flagsAt X.m)
  rw [length_flagsAt] at hle
  have := key X.m le_rfl
  omega

end HostData

end Light.Sec3
