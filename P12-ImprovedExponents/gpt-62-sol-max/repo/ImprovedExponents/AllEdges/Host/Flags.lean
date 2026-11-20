module

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
def aeExecs (F : List ℤ) : ℕ → ℕ
  | 0 => 0
  | w + 1 => aeExecs F w + if aeExec acc hit idx F w then 1 else 0

/-- The number of flags that are not 0. -/
def ones (F : List ℤ) : ℕ := F.countP fun x => decide (x ≠ 0)

variable {acc hit idx}

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

/-- The flag of the cell `q` after `i` query pairs: 1 if one of them is accepted, lies in the cell
and hits, else what it was, if the cell was 0 when the instance began. -/
theorem aeStep_getD {F : List ℤ} {q : ℕ} (hq : q < F.length) (i : ℕ) :
    (aeStep acc hit idx F i).getD q 0 =
      if F.getD q 0 = 0 then
        bit (decide (∃ j < i, idx j = q ∧ acc j = true ∧ hit j = true))
      else F.getD q 0 := by
  induction i with
  | zero => aesop
  | succ i ih =>
    have hs : q < (aeStep acc hit idx F i).length := by simpa
    simp only [aeStep_succ, aePair, Nat.exists_lt_succ_right]
    by_cases hq : idx i = q
    · simp only [hq, true_and, apply_ite (fun l : List ℤ => l.getD q 0),
        List.getD_eq_getElem?_getD, List.getElem?_set_self hs, Option.getD_some]
      simp only [List.getD_eq_getElem?_getD] at ih
      rw [ih]
      by_cases h0 : F[q]?.getD 0 = 0
      · by_cases h : ∃ j < i, idx j = q ∧ acc j = true ∧ hit j = true <;>
          cases acc i <;> cases hit i <;> simp_all [bit]
      · simp [h0]
    · simp only [apply_ite (fun l : List ℤ => l.getD q 0), List.getD_eq_getElem?_getD,
        List.getElem?_set_ne hq, hq, false_and, or_false, ite_self]
      exact ih

/-- The number of flags that are not 0 is at most the number of flags. -/
theorem ones_le_length (F : List ℤ) : ones F ≤ F.length := List.countP_le_length

/-- Treating one query pair: a scan fails or raises the number of flags that are not 0. -/
theorem aeExec_add_ones_le (F : List ℤ) {i : ℕ} (hidx : idx i < F.length) :
    (if aeExec acc hit idx F i then 1 else 0) + ones (aeStep acc hit idx F i) ≤
      (if acc i && !hit i then 1 else 0) + ones (aeStep acc hit idx F (i + 1)) := by
  have hidx' : idx i < (aeStep acc hit idx F i).length := by simpa
  simp only [aeStep_succ, aePair, aeExec, Bool.and_eq_true, decide_eq_true_eq]
  split <;> rename_i h
  · rw [ones, ones, List.countP_set hidx', ← List.getD_eq_getElem _ 0 hidx', h.2, h.1]
    cases hit i <;> simp [bit] <;> omega
  · simp

/-- **Each scan fails or raises the number of flags that are 1**: through `w` query pairs whose
cells lie within the flags. -/
theorem aeExecs_add_ones_le (F : List ℤ) {w : ℕ} (hidx : ∀ i < w, idx i < F.length) :
    aeExecs acc hit idx F w + ones F ≤
      failsUpto acc hit w + ones (aeStep acc hit idx F w) := by
  induction w with
  | zero => rfl
  | succ w ih =>
    have := aeExec_add_ones_le (acc := acc) (hit := hit) F (hidx w (Nat.lt_succ_self w))
    rw [aeExecs, failsUpto_succ]
    grind

/-- The flags and scan count depend only on the first `w` query pairs. -/
theorem ae_congr {acc' hit' : ℕ → Bool} {idx' : ℕ → ℕ} (F : List ℤ) {w : ℕ}
    (h : ∀ i < w, acc i = acc' i ∧ hit i = hit' i ∧ idx i = idx' i) :
    aeStep acc hit idx F w = aeStep acc' hit' idx' F w ∧
      aeExecs acc hit idx F w = aeExecs acc' hit' idx' F w := by
  induction w with
  | zero => exact ⟨rfl, rfl⟩
  | succ w ih =>
    obtain ⟨ha, hh, hi⟩ := h w (by omega)
    obtain ⟨hs, hc⟩ := ih fun i hi => h i (by omega)
    exact ⟨by simp only [aeStep_succ, aePair, hs, ha, hh, hi],
      by rw [aeExecs, aeExecs, hc, aeExec, aeExec, ha, hi, hs]⟩

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
    rw [flagsAt, flagsStep, aeStep_getD (by simp_all), ih]
    simp only [Nat.exists_lt_succ_right]
    by_cases h : ∃ t < T, ∃ i < X.w t, X.pairIdx t i = q ∧ X.acc t i = true ∧ X.hit t i = true <;>
      simp [h, bit]

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
  rw [← List.getD_eq_getElem _ 0 hq, ← List.getD_eq_getElem _ 0 (by assumption)]
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
    have hpiece := hv.piece_le ht
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
      simp
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
      have hstep : X.execsAE T + ones (X.flagsAt T) ≤ X.fails T + ones (X.flagsAt (T + 1)) :=
        aeExecs_add_ones_le (X.flagsAt T) fun i hi => by
          rw [length_flagsAt]
          exact hv.pairIdx_lt (by omega) hi
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      omega
  have hle := ones_le_length (X.flagsAt X.m)
  rw [length_flagsAt] at hle
  grind

end HostData

end Light.Sec3
