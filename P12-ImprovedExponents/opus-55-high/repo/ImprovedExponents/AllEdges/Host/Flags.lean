
import ThreeSumApsp.Programs.Sec3.Theorem17.Host.InstanceFacts
import ImprovedExponents.AllEdges.Task


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
def aeExecs (F : List ℤ) (w : ℕ) : ℕ := ((List.range w).filter (aeExec acc hit idx F)).length

/-- The number of flags that are not 0. -/
def ones (F : List ℤ) : ℕ := F.countP fun x => decide (x ≠ 0)

variable {acc hit idx}

variable (F : List ℤ)

@[simp] theorem aeStep_zero : aeStep acc hit idx F 0 = F := rfl

@[simp] theorem aeStep_succ (i : ℕ) :
    aeStep acc hit idx F (i + 1) = aePair acc hit idx (aeStep acc hit idx F i) i := rfl

@[simp] theorem length_aePair (i : ℕ) :
    (aePair acc hit idx F i).length = F.length := by
  unfold aePair
  grind

@[simp] theorem length_aeStep (i : ℕ) :
    (aeStep acc hit idx F i).length = F.length := by
  induction i with
  | zero => rfl
  | succ i ih => simp_all

variable {j q : ℕ}

/-- A cell of a list other than the one that is set. -/
theorem getD_set_ne (hne : j ≠ q) (x : ℤ) :
    (F.set j x).getD q 0 = F.getD q 0 := by
  simp_all


/-- The bit of a proposition is 0 if and only if the proposition fails. -/
theorem bit_decide_eq_zero (P : Prop) [Decidable P] : bit (decide P) = 0 ↔ ¬P := by
  grind [bit]

theorem aeExecs_succ (w : ℕ) :
    aeExecs acc hit idx F (w + 1) =
      aeExecs acc hit idx F w + if aeExec acc hit idx F w then 1 else 0 := by
  grind [aeExecs, List.range_succ]

/-- The flag of the cell `q` after `i` query pairs: 1 if one of them is accepted, lies in the cell
and hits, else what it was, if the cell was 0 when the instance began. -/
theorem aeStep_getD {F : List ℤ} (hq : q < F.length) (i : ℕ) :
    (aeStep acc hit idx F i).getD q 0 =
      if F.getD q 0 = 0 then
        bit (decide (∃ j < i, idx j = q ∧ acc j = true ∧ hit j = true))
      else F.getD q 0 := by
  induction i with
  | zero => aesop
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
        simp_all
      · simp_all
      · -- it is not scanned: not accepted, or an earlier pair in the cell hit
        rw [ih, ite_eq_left hF, bit_decide_eq_zero] at h0
        rw [ih, ite_eq_left hF]
        congr 1
        simp_all
      simp_all
    aesop

/-- The number of flags that are not 0 is at most the number of flags. -/
theorem ones_le_length : ones F ≤ F.length := List.countP_le_length

/-- Treating one query pair: a scan fails or raises the number of flags that are not 0. -/
theorem aeExec_add_ones_le {i : ℕ} (hidx : idx i < F.length) :
    (if aeExec acc hit idx F i then 1 else 0) + ones (aeStep acc hit idx F i) ≤
      (if acc i && !hit i then 1 else 0) + ones (aeStep acc hit idx F (i + 1)) := by
  have hidx' : idx i < (aeStep acc hit idx F i).length := by simp_all
  rw [aeStep_succ, aePair]
  by_cases h0 : acc i = true ∧ (aeStep acc hit idx F i).getD (idx i) 0 = 0
  · -- a scan is made
    grind [ones, bit]
  · -- no scan: the pair is not accepted or its flag is not 0
    have hex : aeExec acc hit idx F i = false := by
      grind [aeExec]
    grind

variable {w : ℕ}

/-- **Each scan fails or raises the number of flags that are 1**: through `w` query pairs whose
cells lie within the flags. -/
theorem aeExecs_add_ones_le (hidx : ∀ i < w, idx i < F.length) :
    aeExecs acc hit idx F w + ones F ≤
      failsUpto acc hit w + ones (aeStep acc hit idx F w) := by
  induction w with
  | zero => rfl
  | succ w ih =>
    have := aeExec_add_ones_le (acc := acc) (hit := hit) F (by aesop)
    grind [aeExecs_succ, failsUpto_succ]

variable {hit' acc' : ℕ → Bool} {idx' : ℕ → ℕ}

/-- The flags depend only on the first `w` query pairs. -/
theorem aeStep_congr
    (h : ∀ i < w, acc i = acc' i ∧ hit i = hit' i ∧ idx i = idx' i) :
    aeStep acc hit idx F w = aeStep acc' hit' idx' F w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    obtain ⟨ha, hh, hi⟩ := h w (Nat.lt_succ_self w)
    rw [aeStep_succ, aeStep_succ, ih fun i hi => by grind, aePair, aePair, ha, hh, hi]

/-- The number of scans depends only on the first `w` query pairs. -/
theorem aeExecs_congr
    (h : ∀ i < w, acc i = acc' i ∧ hit i = hit' i ∧ idx i = idx' i) :
    aeExecs acc hit idx F w = aeExecs acc' hit' idx' F w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    obtain ⟨ha, hh, hi⟩ := h w (Nat.lt_succ_self w)
    rw [aeExecs_succ, aeExecs_succ, ih fun i hi => by grind, aeExec, aeExec, ha, hi,
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
  | succ t ih => simp_all [flagsAt]

/-- The flag of the cell `q < n²` when instance `T` begins: 1 if an accepted query pair of an
earlier instance lies in the cell and hits, 0 if not. -/
theorem flagsAt_getD {T q : ℕ} (hq : q < X.n * X.n) :
    (X.flagsAt T).getD q 0 =
      bit (decide (∃ t < T, ∃ i < X.w t, X.pairIdx t i = q ∧ X.acc t i = true ∧
        X.hit t i = true)) := by
  induction T with
  | zero => simp [flagsAt, bit]
  | succ T ih =>
    rw [flagsAt, flagsStep_def, aeStep_getD (by simp_all), ih]
    grind [bit]

variable {i t : ℕ}

/-- The cell of the query pair number `i` of instance `t`, in the lists of rows and columns that the
host writes. -/
theorem pairIdx_eq (hi : i < X.w t) :
    X.pairIdx t i = (X.WI t).getD i 0 * X.n + (X.WJ t).getD i 0 := by
  grind [pairIdx, getD_WI, getD_WJ]

variable {X} in
/-- The cells of the query pairs of an instance lie within the `n²` flags. -/
theorem Valid.pairIdx_lt (hv : X.Valid) (ht : t < X.m) (hi : i < X.w t) :
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
  rw [← List.getD_eq_getElem _, ← List.getD_eq_getElem _]
  rw [length_flagsAt] at hq
  have ha := Nat.div_lt_of_lt_mul' hq
  have hb := Nat.mod_lt_of_lt_mul hq
  have hdivmod := q.div_add_mod' X.n
  rw [X.flagsAt_getD hq, ← hdivmod,
    ImprovedExponents.AllEdges.aeFlags_getD_eq_bit_scanHit _ _ _ ha hb]
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [scanHit, List.any_eq_true, List.mem_range, decide_eq_true_eq, Nat.add_zero, hdivmod]
  constructor
  · rintro ⟨t, ht, i, hi, hpq, -, hhit⟩
    obtain ⟨c, hc, hzero⟩ := (hit_iff hi).1 hhit
    have hpiece := hv.piece_le ht
    have hcol := hv.colOf_lt ht hi
    grind [pairIdx, Nat.mul_add_div_of_lt, Nat.mul_add_mod_of_lt, sumAt]
  · rintro ⟨c, hc, hzero⟩
    obtain ⟨t, ht, i, hi, hrow, hcol, c', hc', rfl⟩ := hv.exists_query ha hb hc
    refine ⟨t, ht, i, hi, ?_, ?_, ?_⟩
    · grind [pairIdx]
    · refine (acc_iff hv ht hi).2 ⟨c', hc', ?_⟩
      simp_all [sumAt]
    · refine (hit_iff hi).2 ⟨c', hc', ?_⟩
      grind [sumAt]

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
      have hstep : X.execsAE T + ones _ ≤ X.fails T + ones (X.flagsAt (T + 1)) :=
        aeExecs_add_ones_le _ fun i hi => by
          rw [length_flagsAt]
          exact hv.pairIdx_lt (by omega) hi
      grind [Finset.sum_range_succ]
  grind [ones_le_length, length_flagsAt]
