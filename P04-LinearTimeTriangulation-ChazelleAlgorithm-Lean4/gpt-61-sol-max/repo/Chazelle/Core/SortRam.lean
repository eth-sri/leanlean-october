module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SortList
public import Chazelle.Core.SpecKernels
public import Chazelle.Programs.Tactics

/-!
# Sorting on the RAM, part 2: a verified bottom-up merge sort (WP-C)

`sortStmt cmp` sorts `K` naturals ("items") by a comparison procedure `cmp`, a statement with a
contract `CmpOK` (it reads two items in registers `sr 0`, `sr 1`, writes the bit `le a b` into
`sr 2`, may write the bands `Bc` and nothing else, and preserves an arbitrary invariant `J`).
Only natural registers of band `bSort` (`sr i = bandReg bSort i = 30000 + i`), the allocator and
fresh memory are written; values are added, subtracted and compared, never multiplied; every
stored natural is an item, an index `≤ 2K` or an address below `ALLOC + 2K`.

## Registers (band `bSort`)

| register | role |
|---|---|
| `sr 0`, `sr 1`, `sr 2` | comparator: the two items, the answer bit |
| `sr 3`, `sr 4` | input: base `S` and length `K` of the item array |
| `sr 5` | output: base of the sorted array (fresh, below the new allocator) |
| `sr 6`, `sr 17` | the constants `1`, `2` |
| `sr 7`, `sr 8` | source and destination arrays of the current pass |
| `sr 9`, `sr 10` … `sr 12` | run width `w`; `lo`, `mid`, `hi` of the current pair of runs |
| `sr 13` … `sr 15` | merge cursors `i`, `j`, `k` (copy loop: `i`) |
| `sr 16`, `sr 18` | scratch (address, word) |

## Algorithm and cost

Copy the items to a fresh array `A₀ = ALLOC` (raising `ALLOC` by `2` per item, so that it grows
by `2K` in total), then run passes with widths `w = 1, 2, 4, …` while `w < K`, each merging the
runs `[lo, lo + w)`, `[lo + w, lo + 2w)` of the source array into the destination array
(`A₀`, `A₀ + K` alternately).  Cost (`sortStmt_exec`):
`≤ (κ + 30) (K (⌈log₂ K⌉ + 1) + 1)` for a comparator of cost `≤ κ`.

## Main result

`sortStmt_exec`: from a word-bounded configuration with the items `L` at `S` below the allocator
and room for the cost, the sort ends with a list `L'` at the output base that is a permutation of
`L`, sorted for `le` (`List.Pairwise`), in a fresh area, respecting `Frame (insert bSort Bc)` and
the invariant `J`.
-/

namespace Chazelle.Core

namespace SortR

open Machine Machine.Stmt Programs SortL

@[expose] public section

/-! ## The program -/


/-- Load the items `src[i]`, `src[j]` into the comparator registers. -/
def cmpLoad : Stmt :=
  block [.addN 30016 30007 30013, .loadN 30000 30016, .addN 30016 30007 30014, .loadN 30001 30016]

/-- Move `src[i]` to `dst[k]`, `i := i + 1`. -/
def takeL : Stmt :=
  block [.addN 30016 30007 30013, .loadN 30018 30016, .addN 30016 30008 30015, .storeN 30016 30018,
    .addN 30013 30013 30006]

/-- Move `src[j]` to `dst[k]`, `j := j + 1`. -/
def takeR : Stmt :=
  block [.addN 30016 30007 30014, .loadN 30018 30016, .addN 30016 30008 30015, .storeN 30016 30018,
    .addN 30014 30014 30006]

section
variable (cmp : Stmt)
include cmp
/-- One output word of a merge. -/
def mergeStep : Stmt :=
  .ifLtN 30013 30011
    (.ifLtN 30014 30012 (.seq cmpLoad (.seq cmp (.ifLtN 30002 30006 takeR takeL))) takeL) takeR

/-- The merge loop body: one output word, `k := k + 1`. -/
def mergeBody : Stmt := .seq (mergeStep cmp) (.instr (.addN 30015 30015 30006))

/-- The merge of `src[lo, mid)` and `src[mid, hi)` into `dst[lo, hi)`. -/
def mergeLoop : Stmt := .whileLtN 30015 30012 (mergeBody cmp)


end

/-- `r := min (x + w) K`. -/
def clamp (r x : ℕ) : Stmt :=
  .seq (.instr (.addN r x 30009)) (.ifLtN 30004 r (.instr (.copyN r 30004)) .skip)

/-- The merge cursors `i := lo`, `j := mid`, `k := lo`. -/
def cursors : Stmt := block [.copyN 30013 30010, .copyN 30014 30011, .copyN 30015 30010]

/-- `mid := min (lo + w) K`, `hi := min (mid + w) K`, cursors, merge, `lo := hi`. -/
def pairBody (cmp : Stmt) : Stmt :=
  .seq (clamp 30011 30010) (.seq (clamp 30012 30011)
    (.seq cursors (.seq (mergeLoop cmp) (.instr (.copyN 30010 30012)))))

/-- One pass: all pairs of runs. -/
def pairLoop (cmp : Stmt) : Stmt := .whileLtN 30010 30004 (pairBody cmp)

/-- Swap the arrays and double the width. -/
def swapBlock : Stmt := block [.copyN 30018 30007, .copyN 30007 30008, .copyN 30008 30018,
  .addN 30009 30009 30009]

/-- A pass with its bookkeeping. -/
def passBody (cmp : Stmt) : Stmt := .seq (.instr (.constN 30010 0)) (.seq (pairLoop cmp) swapBlock)

/-- The passes, while `w < K`. -/
def passLoop (cmp : Stmt) : Stmt := .whileLtN 30009 30004 (passBody cmp)

/-- Copy one item to the fresh array and raise the allocator by `2`. -/
def copyBody : Stmt :=
  block [.addN 30016 30003 30013, .loadN 30018 30016, .addN 30016 30007 30013, .storeN 30016 30018,
    .addN 30013 30013 30006, .addN 9999 9999 30017]

/-- The copy loop. -/
def copyLoop : Stmt := .whileLtN 30013 30004 copyBody

/-- Constants, the two fresh arrays, `i := 0`. -/
def sortInit : Stmt := block [.constN 30006 1, .constN 30017 2, .copyN 30007 9999,
  .addN 30008 9999 30004, .constN 30013 0]

/-- **The sort.** -/
def sortStmt (cmp : Stmt) : Stmt :=
  .seq sortInit (.seq copyLoop (.seq (.instr (.constN 30009 1))
    (.seq (passLoop cmp) (.instr (.copyN 30005 30007)))))

/-- The cost bound of the sort for a comparator of cost `≤ κ`. -/
def sortCost (κ K : ℕ) : ℕ := (κ + 30) * (K * (Nat.clog 2 K + 1) + 1)

/-! ## The comparator contract -/

/-- **Contract of a comparison procedure**: from every word-bounded configuration satisfying the
invariant `J`, `cmp` runs in at most `κ` steps, keeps `J`, writes into `sr 2` the bit
`le (sr 0) (sr 1)`, and changes no natural register except `sr 0 … sr 2` and those of the bands
`Bc` (never `ALLOC`), no real register outside `Bc`, no memory and no output. -/
def CmpOK (P : Polygon) (W : ℕ) (cmp : Stmt) (Bc : Finset ℕ) (J : Config → Prop)
    (le : ℕ → ℕ → Bool) (κ : ℕ) : Prop :=
  ∀ c, WordsBounded W c → J c →
    ∃ c' k, Exec P W cmp c c' k ∧ k ≤ κ ∧ J c' ∧
      c'.nreg 30002 = (if le (c.nreg 30000) (c.nreg 30001) then 1 else 0) ∧
      (∀ r, r ≠ 30000 → r ≠ 30001 → r ≠ 30002 → (bandOf r ∉ Bc ∨ r = ALLOC) →
        c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ Bc → c'.rreg r = c.rreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output

/-- `J` is insensitive to the writes of the sort itself (registers of band `bSort`, the
allocator, memory from `A₀` on). -/
def JStable (J : Config → Prop) (A₀ : ℕ) : Prop :=
  ∀ c c', J c → (∀ r, bandOf r ≠ bSort → r ≠ ALLOC → c'.nreg r = c.nreg r) →
    c'.rreg = c.rreg → (∀ a, a < A₀ → c'.nmem a = c.nmem a) → c'.rmem = c.rmem →
      c'.output = c.output → J c'

/-! ## A loop rule that also bounds the growth of a quantity by the cost -/

/-- `whileLtN` with a potential `Φ` (upper cost bound) and a quantity `ψ` that each iteration
raises by at most its cost: the whole loop raises `ψ` by at most its cost. -/
theorem whileLtN_potential_lb {P : Polygon} {W a b : ℕ} {body : Stmt}
    (I : Config → Prop) (Φ ψ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c ∧ ψ c' ≤ ψ c + k)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ Φ c + 2 ∧ ψ c' ≤ ψ c + k := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨c₁, k₁, hb, hI₁, hΦ, hψ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hk₂, hψ'⟩ := ih (Φ c₁) (by omega) hI₁ rfl
      exact ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', by omega, by omega⟩
    · exact ⟨c, 2, .whileLtN_false ht (hI c hc), hc, ht, by omega, by omega⟩

/-! ## Sort-local steps -/

/-- A step of the sort itself: only band `bSort`, the allocator and memory from `A₀` on change. -/
def SL (A₀ : ℕ) (c c' : Config) : Prop :=
  (∀ r, bandOf r ≠ bSort → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
    (∀ a, a < A₀ → c'.nmem a = c.nmem a) ∧ c'.rmem = c.rmem ∧ c'.output = c.output

section
variable (Bc : Finset ℕ) (A₀ : ℕ)
include Bc A₀
/-- **The global frame of the sort** relative to its entry configuration `c₀`: registers outside
the bands `bSort`, `Bc` and the allocator, real registers outside `Bc`, memory below `A₀`, real
memory and output are those of `c₀`. -/
def Loc (c₀ c : Config) : Prop :=
  (∀ r, bandOf r ∉ Bc → bandOf r ≠ bSort → r ≠ ALLOC → c.nreg r = c₀.nreg r) ∧
    (∀ r, bandOf r ∉ Bc → c.rreg r = c₀.rreg r) ∧ (∀ a, a < A₀ → c.nmem a = c₀.nmem a) ∧
    c.rmem = c₀.rmem ∧ c.output = c₀.output

/-- The entry configuration is within the frame. -/
theorem Loc.refl (c : Config) : Loc Bc A₀ c c :=
  by core_grind


end

/-- A sort-local step keeps the global frame. -/
theorem Loc.sl {Bc : Finset ℕ} {A₀ : ℕ} {c₀ c c' : Config} (h : Loc Bc A₀ c₀ c)
    (h' : SL A₀ c c') : Loc Bc A₀ c₀ c' :=
  ⟨fun r h1 h2 h3 => (h'.1 r h2 h3).trans (h.1 r h1 h2 h3),
    fun r h1 => by ram_grind,
    fun a ha => (h'.2.2.1 a ha).trans (h.2.2.1 a ha), h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

/-- The band of a register of the sort band. -/
theorem bandOf_sort {r : ℕ} (h : bandOf r ≠ bSort) : r < 30000 ∨ 40000 ≤ r := by
  omega_nf

/-! ## The straight-line pieces -/

section pieces
variable {P : Polygon} {W : ℕ}

section
variable (c : Config) (hc : WordsBounded W c)
include hc
/-- `takeL`: `dst[k] := src[i]`, `i := i + 1` (scratch `sr 16`, `sr 18`). -/
theorem takeL_exec (h1 : c.nreg 30007 + c.nreg 30013 ≤ W)
    (h2 : c.nreg 30008 + c.nreg 30015 ≤ W) (h3 : c.nreg 30013 + c.nreg 30006 ≤ W) :
    ∃ c' k, Exec P W takeL c c' k ∧ k = 5 ∧
      c'.nmem = upd c.nmem (c.nreg 30008 + c.nreg 30015) (c.nmem (c.nreg 30007 + c.nreg 30013)) ∧
      c'.nreg 30013 = c.nreg 30013 + c.nreg 30006 ∧
      (∀ r, r ≠ 30013 → r ≠ 30016 → r ≠ 30018 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold takeL
  exec_block
  all_goals simp_all

/-- `takeR`: `dst[k] := src[j]`, `j := j + 1` (scratch `sr 16`, `sr 18`). -/
theorem takeR_exec (h1 : c.nreg 30007 + c.nreg 30014 ≤ W)
    (h2 : c.nreg 30008 + c.nreg 30015 ≤ W) (h3 : c.nreg 30014 + c.nreg 30006 ≤ W) :
    ∃ c' k, Exec P W takeR c c' k ∧ k = 5 ∧
      c'.nmem = upd c.nmem (c.nreg 30008 + c.nreg 30015) (c.nmem (c.nreg 30007 + c.nreg 30014)) ∧
      c'.nreg 30014 = c.nreg 30014 + c.nreg 30006 ∧
      (∀ r, r ≠ 30014 → r ≠ 30016 → r ≠ 30018 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold takeR
  exec_block
  all_goals simp_all

/-- `cmpLoad`: `sr 0 := src[i]`, `sr 1 := src[j]` (scratch `sr 16`). -/
theorem cmpLoad_exec (h1 : c.nreg 30007 + c.nreg 30013 ≤ W)
    (h2 : c.nreg 30007 + c.nreg 30014 ≤ W) :
    ∃ c' k, Exec P W cmpLoad c c' k ∧ k = 4 ∧
      c'.nreg 30000 = c.nmem (c.nreg 30007 + c.nreg 30013) ∧
      c'.nreg 30001 = c.nmem (c.nreg 30007 + c.nreg 30014) ∧
      (∀ r, r ≠ 30000 → r ≠ 30001 → r ≠ 30016 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cmpLoad
  exec_block
  all_goals simp_all


end

section
variable {c : Config} (hc : WordsBounded W c)
include hc
/-- `addN` with its effect spelled out. -/
theorem addN_char (r x y : ℕ) (h : c.nreg x + c.nreg y ≤ W) :
    ∃ c', Exec P W (.instr (.addN r x y)) c c' 1 ∧ c'.nreg = upd c.nreg r (c.nreg x + c.nreg y) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  ⟨_, Exec.addN hc r x y h, rfl, rfl, rfl, rfl, rfl⟩

/-- `copyN` with its effect spelled out. -/
theorem copyN_char (r x : ℕ) :
    ∃ c', Exec P W (.instr (.copyN r x)) c c' 1 ∧ c'.nreg = upd c.nreg r (c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  ⟨_, Exec.copyN hc r x, rfl, rfl, rfl, rfl, rfl⟩

/-- `constN` with its effect spelled out. -/
theorem constN_char (r v : ℕ) (h : v ≤ W) :
    ∃ c', Exec P W (.instr (.constN r v)) c c' 1 ∧ c'.nreg = upd c.nreg r v ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  ⟨_, Exec.constN hc r v h, rfl, rfl, rfl, rfl, rfl⟩

/-- `clamp r x`: `r := min (x + w) K`, cost `≤ 3`. -/
theorem clamp_exec (r x : ℕ) (hr : r ≠ 30004)
    (h : c.nreg x + c.nreg 30009 ≤ W) :
    ∃ c' k, Exec P W (clamp r x) c c' k ∧ k ≤ 3 ∧
      c'.nreg = upd c.nreg r (min (c.nreg x + c.nreg 30009) (c.nreg 30004)) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, e₁, n₁, m₁, rr₁, rm₁, o₁⟩ := addN_char (P := P) hc r x 30009 h
  have hK : c₁.nreg 30004 = c.nreg 30004 := by ram_simp
  have hR : c₁.nreg r = c.nreg x + c.nreg 30009 := by simp_all
  by_cases ht : c₁.nreg 30004 < c₁.nreg r
  · obtain ⟨c₂, e₂, n₂, m₂, rr₂, rm₂, o₂⟩ := copyN_char (P := P) e₁.wb_right r 30004
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true ht e₂), le_refl _, ?_, m₂.trans m₁, rr₂.trans rr₁,
      rm₂.trans rm₁, o₂.trans o₁⟩
    grind [Machine.upd_upd_same]
  · refine ⟨c₁, _, .seq e₁ (.ifLtN_false ht (.skip e₁.wb_right)), le_refl _, ?_, m₁, rr₁, rm₁,
      o₁⟩
    simp_all

/-- `cursors`: `i := lo`, `j := mid`, `k := lo`, cost `3`. -/
theorem cursors_exec :
    ∃ c' k, Exec P W cursors c c' k ∧ k = 3 ∧
      c'.nreg 30013 = c.nreg 30010 ∧ c'.nreg 30014 = c.nreg 30011 ∧
      c'.nreg 30015 = c.nreg 30010 ∧
      (∀ r, r ≠ 30013 → r ≠ 30014 → r ≠ 30015 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cursors
  exec_block
  simp_all

/-- `swapBlock`: exchange the arrays, double the width, cost `4`. -/
theorem swap_exec (h : c.nreg 30009 + c.nreg 30009 ≤ W) :
    ∃ c' k, Exec P W swapBlock c c' k ∧ k = 4 ∧
      c'.nreg 30007 = c.nreg 30008 ∧ c'.nreg 30008 = c.nreg 30007 ∧
      c'.nreg 30009 = c.nreg 30009 + c.nreg 30009 ∧
      (∀ r, r ≠ 30007 → r ≠ 30008 → r ≠ 30009 → r ≠ 30018 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold swapBlock
  exec_block
  all_goals simp_all


end

end pieces

/-! ## Segments -/

section
variable {m : ℕ → ℕ} {p n : ℕ}
/-- Dropping from a list read as a segment. -/
theorem drop_of_seg {l : List ℕ} (h : seg m p n = l) (d : ℕ) :
    l.drop d = seg m (p + d) (n - d) := by
  grind [seg_drop]

/-- A nonempty segment starts with its first word. -/
theorem seg_pos (h : 0 < n) : seg m p n = m p :: seg m (p + 1) (n - 1) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  grind [seg_succ]

/-- A segment of length `0` is empty. -/
theorem seg_eq_nil (h : n = 0) : seg m p n = [] := by
  subst h; rfl


end

/-- Rewriting the bounds of a segment. -/
theorem seg_arg {m : ℕ → ℕ} {p p' n n' : ℕ} (hp : p = p') (hn : n = n') :
    seg m p n = seg m p' n' := by
  simp_all

/-! ## The merge loop -/

section merge
variable {P : Polygon} {W : ℕ} {J : Config → Prop} {le : ℕ → ℕ → Bool} {Bc : Finset ℕ} {A₀ : ℕ}

/-- **The merge loop invariant** for the merge of `a = src[lo, mid)` and `b = src[mid, hi)` into
`dst[lo, hi)`, relative to the entry configuration `c₀` of the sort and the entry
configuration `cS` of the merge. -/
structure MergeInv (W : ℕ) (J : Config → Prop) (le : ℕ → ℕ → Bool) (Bc : Finset ℕ) (A₀ : ℕ)
    (c₀ cS : Config) (src dst lo mid hi : ℕ) (a b : List ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  hJ : J c
  loc : Loc Bc A₀ c₀ c
  one : c.nreg 30006 = 1
  rsrc : c.nreg 30007 = src
  rdst : c.nreg 30008 = dst
  rmid : c.nreg 30011 = mid
  rhi : c.nreg 30012 = hi
  keep : ∀ r, (30000 ≤ r ∧ r < 40000 ∨ r = ALLOC) → r ≠ 30000 → r ≠ 30001 → r ≠ 30002 →
    r ≠ 30013 → r ≠ 30014 → r ≠ 30015 → r ≠ 30016 → r ≠ 30018 → c.nreg r = cS.nreg r
  lo_i : lo ≤ c.nreg 30013
  i_mid : c.nreg 30013 ≤ mid
  mid_j : mid ≤ c.nreg 30014
  j_hi : c.nreg 30014 ≤ hi
  rk : c.nreg 30015 + mid = c.nreg 30013 + c.nreg 30014
  bsrc : src + hi ≤ W
  bdst : dst + hi + 1 ≤ W
  disj : src + hi ≤ dst + lo ∨ dst + hi ≤ src + lo
  dA : A₀ ≤ dst
  ma : seg c.nmem (src + lo) (mid - lo) = a
  mb : seg c.nmem (src + mid) (hi - mid) = b
  out : seg c.nmem (dst + lo) (c.nreg 30015 - lo) ++
    List.merge (a.drop (c.nreg 30013 - lo)) (b.drop (c.nreg 30014 - mid)) le = List.merge a b le
  mem : ∀ x, (x < dst + lo ∨ dst + hi ≤ x) → c.nmem x = cS.nmem x

variable {c₀ cS : Config} {src dst lo mid hi : ℕ} {a b : List ℕ}

/-- The invariant survives changes of the comparator registers, the scratch registers and the
bands `Bc` (the comparator's writes). -/
theorem MergeInv.congr {c c' : Config}
    (h : MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c) (hw : WordsBounded W c')
    (hJ : J c') (hloc : Loc Bc A₀ c₀ c') (hm : c'.nmem = c.nmem)
    (hr : ∀ r, (30000 ≤ r ∧ r < 40000 ∨ r = ALLOC) → r ≠ 30000 → r ≠ 30001 → r ≠ 30002 →
      r ≠ 30016 → r ≠ 30018 → c'.nreg r = c.nreg r) :
    MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c' := by
  ram_grind

/-- The memory after a store at `dst + k` (`lo ≤ k < hi`) reads the same on the source window
and outside `[dst + lo, dst + hi)`. -/
theorem store_facts {c : Config} (h : MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c) {k v : ℕ}
    (hk1 : lo ≤ k) (hk2 : k < hi) :
    seg (upd c.nmem (dst + k) v) (src + lo) (mid - lo) = a ∧
      seg (upd c.nmem (dst + k) v) (src + mid) (hi - mid) = b ∧
      (∀ x, (x < dst + lo ∨ dst + hi ≤ x) → upd c.nmem (dst + k) v x = cS.nmem x) := by
  have := h.lo_i; have := h.i_mid; have := h.mid_j; have := h.j_hi; have := h.disj
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [← h.ma]; apply seg_congr; ram_simp
  · rw [← h.mb]; apply seg_congr; ram_simp
  · rw [Machine.upd_other _ _ _ (by omega)]; ram_grind

section
variable (hJs : JStable J A₀) {c : Config} (h : MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c)
include hJs h
/-- **Taking the left head**: `takeL` then `k := k + 1` keeps the invariant, when the left run is
not exhausted and its head is `≤` the head of the right run (if any). -/
theorem stepL (hil : c.nreg 30013 < mid)
    (hle : c.nreg 30014 < hi →
      le (c.nmem (src + c.nreg 30013)) (c.nmem (src + c.nreg 30014)) = true) :
    ∃ c₃ c₄, Exec P W takeL c c₃ 5 ∧ Exec P W (.instr (.addN 30015 30015 30006)) c₃ c₄ 1 ∧
      MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c₄ ∧
      c₄.nreg 30015 = c.nreg 30015 + 1 := by
  have hj := h.j_hi
  have hk := h.rk
  have hmj := h.mid_j
  have hbs := h.bsrc
  have hbd := h.bdst
  have hli := h.lo_i
  have him := h.i_mid
  obtain ⟨c₃, k₃, e₃, rfl, hm₃, hi₃, hr₃, hrr₃, hrm₃, ho₃⟩ := takeL_exec (P := P) c h.wb
    (by ram_grind) (by ram_grind) (by ram_grind)
  have w₃ := e₃.wb_right
  have k₃ : c₃.nreg 30015 = c.nreg 30015 := hr₃ _ (by omega) (by omega) (by omega)
  have o₃ : c₃.nreg 30006 = 1 := (hr₃ _ (by omega) (by omega) (by omega)).trans h.one
  obtain ⟨c₄, e₄, n₄, m₄, rr₄, rm₄, o₄⟩ := addN_char (P := P) w₃ 30015 30015 30006
    (by omega)
  refine ⟨c₃, c₄, e₃, e₄, ?_, by simp_all⟩
  have w₄ : WordsBounded W c₄ := e₄.wb_right
  -- the new memory
  have hm₄ : c₄.nmem = upd c.nmem (dst + c.nreg 30015) (c.nmem (src + c.nreg 30013)) := by
    rw [m₄, hm₃, h.rsrc, h.rdst]
  have hlok : lo ≤ c.nreg 30015 := by omega
  have hkhi : c.nreg 30015 < hi := by omega
  obtain ⟨sa, sb, sm⟩ := store_facts h (v := c.nmem (src + c.nreg 30013)) hlok hkhi
  -- registers
  have r₄ : ∀ r, r ≠ 30013 → r ≠ 30015 → r ≠ 30016 → r ≠ 30018 → c₄.nreg r = c.nreg r := by
    ram_simp
  have i₄ : c₄.nreg 30013 = c.nreg 30013 + 1 := by
    simp_all
  have j₄ : c₄.nreg 30014 = c.nreg 30014 := r₄ _ (by omega) (by omega) (by omega) (by omega)
  have kk₄ : c₄.nreg 30015 = c.nreg 30015 + 1 := by
    simp_all
  -- the sort-local step
  have hsl : SL A₀ c c₄ := by
    refine ⟨fun r hb ha => ?_, rr₄.trans hrr₃, fun x hx => ?_, rm₄.trans hrm₃, o₄.trans ho₃⟩
    · have := bandOf_sort hb
      grind
    · rw [hm₄, Machine.upd_other _ _ _ (by have := h.dA; omega)]
  have hJ₄ : J c₄ := hJs c c₄ h.hJ hsl.1 hsl.2.1 hsl.2.2.1 hsl.2.2.2.1 hsl.2.2.2.2
  -- the list step
  have hA : a.drop (c.nreg 30013 - lo) =
      c.nmem (src + c.nreg 30013) :: a.drop (c.nreg 30013 + 1 - lo) := by
    rw [drop_of_seg h.ma, drop_of_seg h.ma, seg_pos (by omega)]
    grind
  have hout := h.out
  rw [hA] at hout
  have hstep := merge_step_left hout (fun y ys' hy => by
    have hjh : c.nreg 30014 < hi := by
      by_contra hc
      rw [drop_of_seg h.mb, seg_eq_nil (by omega)] at hy
      grind
    rw [drop_of_seg h.mb, seg_pos (by omega)] at hy
    grind)
  exact
  { wb := w₄, hJ := hJ₄, loc := h.loc.sl hsl,
    one := (r₄ _ (by omega) (by omega) (by omega) (by omega)).trans h.one,
    rsrc := (r₄ _ (by omega) (by omega) (by omega) (by omega)).trans h.rsrc,
    rdst := (r₄ _ (by omega) (by omega) (by omega) (by omega)).trans h.rdst,
    rmid := (r₄ _ (by omega) (by omega) (by omega) (by omega)).trans h.rmid,
    rhi := (r₄ _ (by omega) (by omega) (by omega) (by omega)).trans h.rhi,
    keep := fun r _ _ _ _ h13 _ h15 h16 h18 =>
      (r₄ r h13 h15 h16 h18).trans (h.keep r ‹_› ‹_› ‹_› ‹_› h13 ‹_› h15 h16 h18),
    lo_i := by omega, i_mid := by omega, mid_j := by omega,
    j_hi := by omega, rk := by omega, bsrc := h.bsrc,
    bdst := h.bdst, disj := h.disj, dA := h.dA, ma := by grind,
    mb := by grind,
    out := by
      rw [hm₄, i₄, j₄, kk₄, show c.nreg 30015 + 1 - lo = (c.nreg 30015 - lo) + 1 by omega,
        seg_upd_end (m := c.nmem) (c.nmem (src + c.nreg 30013)) _ (fun x => by
          grind [Machine.upd_apply])]
      exact hstep,
    mem := fun x hx => by rw [hm₄]; grind }

/-- **Taking the right head**: `takeR` then `k := k + 1` keeps the invariant, when the right run
is not exhausted and the head of the left run (if any) is not `≤` its head. -/
theorem stepR (hjl : c.nreg 30014 < hi)
    (hle : c.nreg 30013 < mid →
      le (c.nmem (src + c.nreg 30013)) (c.nmem (src + c.nreg 30014)) = false) :
    ∃ c₃ c₄, Exec P W takeR c c₃ 5 ∧ Exec P W (.instr (.addN 30015 30015 30006)) c₃ c₄ 1 ∧
      MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c₄ ∧
      c₄.nreg 30015 = c.nreg 30015 + 1 := by
  have hj := h.j_hi
  have hk := h.rk
  have hmj := h.mid_j
  have hbs := h.bsrc
  have hbd := h.bdst
  have hli := h.lo_i
  have him := h.i_mid
  obtain ⟨c₃, k₃, e₃, rfl, hm₃, hi₃, hr₃, hrr₃, hrm₃, ho₃⟩ := takeR_exec (P := P) c h.wb
    (by ram_grind) (by ram_grind) (by ram_grind)
  have w₃ := e₃.wb_right
  have k₃ : c₃.nreg 30015 = c.nreg 30015 := hr₃ _ (by omega) (by omega) (by omega)
  have o₃ : c₃.nreg 30006 = 1 := (hr₃ _ (by omega) (by omega) (by omega)).trans h.one
  obtain ⟨c₄, e₄, n₄, m₄, rr₄, rm₄, o₄⟩ := addN_char (P := P) w₃ 30015 30015 30006
    (by omega)
  refine ⟨c₃, c₄, e₃, e₄, ?_, by simp_all⟩
  have w₄ : WordsBounded W c₄ := e₄.wb_right
  -- the new memory
  have hm₄ : c₄.nmem = upd c.nmem (dst + c.nreg 30015) (c.nmem (src + c.nreg 30014)) := by
    rw [m₄, hm₃, h.rsrc, h.rdst]
  have hlok : lo ≤ c.nreg 30015 := by omega
  have hkhi : c.nreg 30015 < hi := by omega
  obtain ⟨sa, sb, sm⟩ := store_facts h (v := c.nmem (src + c.nreg 30014)) hlok hkhi
  -- registers
  have r₄ : ∀ r, r ≠ 30014 → r ≠ 30015 → r ≠ 30016 → r ≠ 30018 → c₄.nreg r = c.nreg r := by
    ram_simp
  have j₄ : c₄.nreg 30014 = c.nreg 30014 + 1 := by
    simp_all
  have i₄ : c₄.nreg 30013 = c.nreg 30013 := r₄ _ (by omega) (by omega) (by omega) (by omega)
  have kk₄ : c₄.nreg 30015 = c.nreg 30015 + 1 := by
    simp_all
  -- the sort-local step
  have hsl : SL A₀ c c₄ := by
    refine ⟨fun r hb ha => ?_, rr₄.trans hrr₃, fun x hx => ?_, rm₄.trans hrm₃, o₄.trans ho₃⟩
    · have := bandOf_sort hb
      grind
    · rw [hm₄, Machine.upd_other _ _ _ (by have := h.dA; omega)]
  have hJ₄ : J c₄ := hJs c c₄ h.hJ hsl.1 hsl.2.1 hsl.2.2.1 hsl.2.2.2.1 hsl.2.2.2.2
  -- the list step
  have hB : b.drop (c.nreg 30014 - mid) =
      c.nmem (src + c.nreg 30014) :: b.drop (c.nreg 30014 + 1 - mid) := by
    rw [drop_of_seg h.mb, drop_of_seg h.mb, seg_pos (by omega)]
    grind
  have hout := h.out
  rw [hB] at hout
  have hstep := merge_step_right hout (fun x xs' hx => by
    have hil : c.nreg 30013 < mid := by
      by_contra hc
      rw [drop_of_seg h.ma, seg_eq_nil (by omega)] at hx
      grind
    rw [drop_of_seg h.ma, seg_pos (by omega)] at hx
    grind)
  exact
  { wb := w₄, hJ := hJ₄, loc := h.loc.sl hsl,
    one := (r₄ _ (by omega) (by omega) (by omega) (by omega)).trans h.one,
    rsrc := (r₄ _ (by omega) (by omega) (by omega) (by omega)).trans h.rsrc,
    rdst := (r₄ _ (by omega) (by omega) (by omega) (by omega)).trans h.rdst,
    rmid := (r₄ _ (by omega) (by omega) (by omega) (by omega)).trans h.rmid,
    rhi := (r₄ _ (by omega) (by omega) (by omega) (by omega)).trans h.rhi,
    keep := fun r _ _ _ _ _ h14 h15 h16 h18 =>
      (r₄ r h14 h15 h16 h18).trans (h.keep r ‹_› ‹_› ‹_› ‹_› ‹_› h14 h15 h16 h18),
    lo_i := by omega, i_mid := by omega,
    mid_j := by omega, j_hi := by omega, rk := by omega, bsrc := h.bsrc,
    bdst := h.bdst, disj := h.disj, dA := h.dA, ma := by grind,
    mb := by grind,
    out := by
      rw [hm₄, i₄, j₄, kk₄, show c.nreg 30015 + 1 - lo = (c.nreg 30015 - lo) + 1 by omega,
        seg_upd_end (m := c.nmem) (c.nmem (src + c.nreg 30014)) _ (fun x => by
          grind [Machine.upd_apply])]
      exact hstep,
    mem := fun x hx => by rw [hm₄]; grind }


end

/-- The comparator keeps the global frame. -/
theorem Loc.cmp {c₀ c c' : Config} (h : Loc Bc A₀ c₀ c)
    (hr : ∀ r, r ≠ 30000 → r ≠ 30001 → r ≠ 30002 → (bandOf r ∉ Bc ∨ r = ALLOC) →
      c'.nreg r = c.nreg r)
    (hrr : ∀ r, bandOf r ∉ Bc → c'.rreg r = c.rreg r) (hm : c'.nmem = c.nmem)
    (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) : Loc Bc A₀ c₀ c' := by
  refine ⟨fun r h1 h2 h3 => ?_, fun r h1 => (hrr r h1).trans (h.2.1 r h1),
    fun a ha => by ram_grind, hrm.trans h.2.2.2.1, ho.trans h.2.2.2.2⟩
  have := bandOf_sort h2
  ram_grind

section
variable {cmp : Stmt} {κ : ℕ} (hcmp : CmpOK P W cmp Bc J le κ) (hJs : JStable J A₀) (hB : bSort ∉ Bc) {c : Config} (h : MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c)
include hcmp hJs hB h
/-- **One iteration of the merge loop** (cost `≤ κ + 14`). -/
theorem mergeBody_inv
    (hk : c.nreg 30015 < c.nreg 30012) :
    ∃ c' k, Exec P W (mergeBody cmp) c c' k ∧
      MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c' ∧ k ≤ κ + 14 ∧
      c'.nreg 30015 = c.nreg 30015 + 1 := by
  have hj := h.j_hi
  have hrk := h.rk
  have hmj := h.mid_j
  have hbs := h.bsrc
  
  have him := h.i_mid
  rw [h.rhi] at hk
  unfold mergeBody mergeStep
  by_cases hi1 : c.nreg 30013 < mid
  · have t1 : c.nreg 30013 < c.nreg 30011 := by ram_grind
    by_cases hj1 : c.nreg 30014 < hi
    · have t2 : c.nreg 30014 < c.nreg 30012 := by ram_grind
      -- load and compare
      obtain ⟨c₁, k₁, e₁, rfl, x₁, y₁, r₁, m₁, rr₁, rm₁, o₁⟩ := cmpLoad_exec (P := P) c h.wb
        (by ram_grind) (by ram_grind)
      have sl₁ : SL A₀ c c₁ := ⟨fun r hb _ => by
          have := bandOf_sort hb; grind, rr₁,
        fun x _ => by rw [m₁], rm₁, o₁⟩
      have I₁ := h.congr e₁.wb_right (hJs c c₁ h.hJ sl₁.1 sl₁.2.1 sl₁.2.2.1 sl₁.2.2.2.1
        sl₁.2.2.2.2) (h.loc.sl sl₁) m₁ (fun r _ h0 h1' _ h16 _ => r₁ r h0 h1' h16)
      obtain ⟨c₂, k₂, e₂, hk₂, hJ₂, bit₂, r₂, rr₂, m₂, rm₂, o₂⟩ := hcmp c₁ e₁.wb_right I₁.hJ
      have I₂ := I₁.congr e₂.wb_right hJ₂ (I₁.loc.cmp r₂ rr₂ m₂ rm₂ o₂) m₂
        (fun r hr h0 h1' h2' _ _ => r₂ r h0 h1' h2' (by
          grind [bandOf, bSort]))
      have i₂ : c₂.nreg 30013 = c.nreg 30013 := by
        rw [r₂ _ (by omega) (by omega) (by omega) (Or.inl (by
          intro hm; apply hB; rwa [show bandOf 30013 = bSort by decide] at hm)),
          r₁ _ (by omega) (by omega) (by omega)]
      have j₂ : c₂.nreg 30014 = c.nreg 30014 := by
        rw [r₂ _ (by omega) (by omega) (by omega) (Or.inl (by
          intro hm; apply hB; rwa [show bandOf 30014 = bSort by decide] at hm)),
          r₁ _ (by omega) (by omega) (by omega)]
      have k₂e : c₂.nreg 30015 = c.nreg 30015 := by
        rw [r₂ _ (by omega) (by omega) (by omega) (Or.inl (by
          intro hm; apply hB; rwa [show bandOf 30015 = bSort by decide] at hm)),
          r₁ _ (by omega) (by omega) (by omega)]
      
      rw [x₁, y₁, h.rsrc] at bit₂
      by_cases hle : le (c.nmem (src + c.nreg 30013)) (c.nmem (src + c.nreg 30014)) = true
      · rw [ite_eq_left hle] at bit₂
        obtain ⟨c₃, c₄, e₃, e₄, I₄, k₄⟩ := stepL (P := P) hJs I₂ (by omega)
          (fun _ => by grind)
        refine ⟨c₄, _, .seq (.ifLtN_true t1 (.ifLtN_true t2 (.seq e₁ (.seq e₂
          (.ifLtN_false (by rw [bit₂, I₂.one]; decide) e₃))))) e₄, I₄, by omega,
          by rw [k₄, k₂e]⟩
      · rw [ite_eq_right hle] at bit₂
        obtain ⟨c₃, c₄, e₃, e₄, I₄, k₄⟩ := stepR (P := P) hJs I₂ (by omega)
          (fun _ => by grind)
        refine ⟨c₄, _, .seq (.ifLtN_true t1 (.ifLtN_true t2 (.seq e₁ (.seq e₂
          (.ifLtN_true (by rw [bit₂, I₂.one]; decide) e₃))))) e₄, I₄, by omega,
          by rw [k₄, k₂e]⟩
    · have t2 : ¬ c.nreg 30014 < c.nreg 30012 := by ram_grind
      obtain ⟨c₃, c₄, e₃, e₄, I₄, k₄⟩ := stepL (P := P) hJs h hi1 (fun h' => absurd h' hj1)
      exact ⟨c₄, _, .seq (.ifLtN_true t1 (.ifLtN_false t2 e₃)) e₄, I₄, by omega, k₄⟩
  · have t1 : ¬ c.nreg 30013 < c.nreg 30011 := by ram_grind
    obtain ⟨c₃, c₄, e₃, e₄, I₄, k₄⟩ := stepR (P := P) hJs h (by omega) (fun h' => absurd h' hi1)
    exact ⟨c₄, _, .seq (.ifLtN_false t1 e₃) e₄, I₄, by omega, k₄⟩

/-- **The merge loop**: from the invariant, the loop ends with `dst[lo, hi) = merge a b`, in at
most `(κ + 16) (hi - k) + 2` steps. -/
theorem mergeLoop_inv :
    ∃ c' k, Exec P W (mergeLoop cmp) c c' k ∧
      MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c' ∧
      k ≤ (κ + 16) * (hi - c.nreg 30015) + 2 ∧
      seg c'.nmem (dst + lo) (hi - lo) = List.merge a b le := by
  obtain ⟨c', k, e, I', hex, hk⟩ := Exec.whileLtN_bounded
    (MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b) (fun d => hi - d.nreg 30015) (κ + 14)
    (fun _ h => h.wb) (fun d hd ht => by
      obtain ⟨d', k, e, I, hk, hk'⟩ := mergeBody_inv (P := P) hcmp hJs hB hd ht
      have := hd.rhi
      exact ⟨d', k, e, I, hk, by omega⟩) h
  refine ⟨c', k, e, I', hk, ?_⟩
  have := I'.out
  have hi' := I'.rhi
  have h1 := I'.i_mid
  have h2 := I'.j_hi
  have h3 := I'.rk
  have h4 := I'.lo_i
  have h5 := I'.mid_j
  rw [hi'] at hex
  rw [List.drop_of_length_le (by rw [← I'.ma]; simp; omega),
    List.drop_of_length_le (by rw [← I'.mb]; simp; omega), List.nil_merge, List.append_nil,
    show c'.nreg 30015 - lo = hi - lo by omega] at this
  exact this


end

end merge

/-! ## One pass -/

section pass
variable {P : Polygon} {W : ℕ} {J : Config → Prop} {le : ℕ → ℕ → Bool} {Bc : Finset ℕ} {A₀ : ℕ}

/-- **The invariant of the loop over the pairs of runs** of a pass with width `w` from the
source array `src` (holding `l`) to `dst`, relative to the entry configuration `c₀` of the sort
and `cP` of the pass: `dst[0, lo)` holds the pass of `l[0, lo)`. -/
structure PairInv (W : ℕ) (J : Config → Prop) (le : ℕ → ℕ → Bool) (Bc : Finset ℕ) (A₀ : ℕ)
    (c₀ cP : Config) (src dst w K : ℕ) (l : List ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  hJ : J c
  loc : Loc Bc A₀ c₀ c
  rK : c.nreg 30004 = K
  one : c.nreg 30006 = 1
  rsrc : c.nreg 30007 = src
  rdst : c.nreg 30008 = dst
  rw : c.nreg 30009 = w
  keep : ∀ r, (30000 ≤ r ∧ r < 40000 ∨ r = ALLOC) → r ≠ 30000 → r ≠ 30001 → r ≠ 30002 →
    (r < 30010 ∨ 30016 < r) → r ≠ 30018 → c.nreg r = cP.nreg r
  wpos : 0 < w
  wK : w < K
  lo_K : c.nreg 30010 ≤ K
  lo_t : c.nreg 30010 = K ∨ ∃ t, c.nreg 30010 = t * (2 * w)
  arr : (src = A₀ ∧ dst = A₀ + K) ∨ (src = A₀ + K ∧ dst = A₀)
  bW : A₀ + 2 * K + 1 ≤ W
  ml : seg c.nmem src K = l
  out : seg c.nmem dst (c.nreg 30010) = mpass le w (l.take (c.nreg 30010))
  mem : ∀ x, (x < dst ∨ dst + K ≤ x) → c.nmem x = cP.nmem x

variable {c₀ cP : Config} {src dst w K : ℕ} {l : List ℕ}

/-- The pass of a prefix made of whole double blocks, extended by one double block. -/
theorem mpass_take_step (hw : 0 < w) {lo mid hi t : ℕ} (hlo : lo = t * (2 * w))
    (hloK : lo < l.length) (hmid : mid = min (lo + w) l.length)
    (hhi : hi = min (mid + w) l.length) :
    mpass le w (l.take hi) = mpass le w (l.take lo) ++
      List.merge ((l.drop lo).take (mid - lo)) ((l.drop mid).take (hi - mid)) le := by
  have e1 : l.take hi = l.take lo ++ (l.drop lo).take (hi - lo) := by
    rw [← List.take_add]; grind
  have hlen : (l.take lo).length = t * (2 * w) := by
    grind
  have hb : hi - lo ≤ 2 * w := by omega
  have hlen2 : ((l.drop lo).take (hi - lo)).length ≤ 2 * w := by
    grind
  rw [e1, mpass_append hw t _ _ hlen, mpass_small hw _ hlen2]
  congr 2
  · rw [List.take_take]; grind
  · rw [List.drop_take, List.drop_drop]
    by_cases h : lo + w ≤ l.length
    · grind
    · rw [List.drop_of_length_le (l := l) (by omega), List.drop_of_length_le (l := l) (by omega)]
      simp

section
variable {cmp : Stmt} {κ : ℕ} (hcmp : CmpOK P W cmp Bc J le κ) (hJs : JStable J A₀) (hB : bSort ∉ Bc) {c : Config} (h : PairInv W J le Bc A₀ c₀ cP src dst w K l c)
include hcmp hJs hB h
/-- **One iteration of the pair loop**: merge one pair of runs. -/
theorem pairBody_inv (hlt : c.nreg 30010 < c.nreg 30004) :
    ∃ c' k, Exec P W (pairBody cmp) c c' k ∧ PairInv W J le Bc A₀ c₀ cP src dst w K l c' ∧
      (κ + 30) * (K - c'.nreg 30010) + k + 2 ≤ (κ + 30) * (K - c.nreg 30010) := by
  have hK := h.rK
  have hbW := h.bW
  have hwK := h.wK
  have hwp := h.wpos
  have harr := h.arr
  rw [hK] at hlt
  set lo := c.nreg 30010 with hlo
  set mid := min (lo + w) K with hmid
  set hi := min (mid + w) K with hhi
  -- mid, hi
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ := clamp_exec (P := P) h.wb 30011 30010
    (by omega) (by ram_grind)
  have n₁' : c₁.nreg = upd c.nreg 30011 mid := by rw [n₁, h.rw, hK]
  have b₁ : c₁.nreg 30011 + c₁.nreg 30009 ≤ W := by
    rw [n₁', Machine.upd_same, Machine.upd_other _ _ _ (by omega), h.rw]; omega
  obtain ⟨c₂, k₂, e₂, hk₂, n₂, m₂, rr₂, rm₂, o₂⟩ := clamp_exec (P := P) e₁.wb_right 30012 30011
    (by omega) b₁
  have n₂' : c₂.nreg = upd (upd c.nreg 30011 mid) 30012 hi := by
    rw [n₂, n₁']; simp only [Machine.upd_same]
    rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega), h.rw, hK]
  obtain ⟨c₃, k₃, e₃, rfl, i₃, j₃, kk₃, r₃, m₃, rr₃, rm₃, o₃⟩ := cursors_exec (P := P) e₂.wb_right
  have R₃ : ∀ r, r ≠ 30011 → r ≠ 30012 → r ≠ 30013 → r ≠ 30014 → r ≠ 30015 →
      c₃.nreg r = c.nreg r := by
    ram_simp
  have mid₃ : c₃.nreg 30011 = mid := by
    rw [r₃ _ (by omega) (by omega) (by omega), n₂', Machine.upd_other _ _ _ (by omega),
      Machine.upd_same]
  have hi₃ : c₃.nreg 30012 = hi := by
    rw [r₃ _ (by omega) (by omega) (by omega), n₂', Machine.upd_same]
  have lo₂ : c₂.nreg 30010 = lo := by
    grind
  have mid₂ : c₂.nreg 30011 = mid := by
    grind
  rw [lo₂] at i₃ kk₃
  rw [mid₂] at j₃
  have mm₃ : c₃.nmem = c.nmem := by grind
  have sl₃ : SL A₀ c c₃ := ⟨fun r hb _ => by
      have := bandOf_sort hb; grind,
    by grind, fun x _ => by rw [mm₃], by grind, by grind⟩
  have hJ₃ : J c₃ := hJs c c₃ h.hJ sl₃.1 sl₃.2.1 sl₃.2.2.1 sl₃.2.2.2.1 sl₃.2.2.2.2
  -- the merge invariant at entry
  have I₃ : MergeInv W J le Bc A₀ c₀ c₃ src dst lo mid hi (seg c₃.nmem (src + lo) (mid - lo))
      (seg c₃.nmem (src + mid) (hi - mid)) c₃ :=
    { wb := e₃.wb_right, hJ := hJ₃, loc := h.loc.sl sl₃,
      one := (R₃ _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.one,
      rsrc := (R₃ _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.rsrc,
      rdst := (R₃ _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.rdst,
      rmid := mid₃, rhi := hi₃, keep := fun _ _ _ _ _ _ _ _ _ _ => rfl,
      lo_i := by rw [i₃], i_mid := by omega, mid_j := by rw [j₃],
      j_hi := by omega, rk := by omega,
      bsrc := by omega, bdst := by omega, disj := by omega, dA := by omega, ma := rfl, mb := rfl,
      out := by rw [kk₃, i₃, j₃, Nat.sub_self, Nat.sub_self, seg_zero, List.drop_zero,
        List.drop_zero, List.nil_append],
      mem := fun _ _ => rfl }
  obtain ⟨c₄, k₄, e₄, I₄, hk₄, hseg₄⟩ := mergeLoop_inv (P := P) hcmp hJs hB I₃
  rw [kk₃] at hk₄
  obtain ⟨c₅, e₅, n₅, m₅, rr₅, rm₅, o₅⟩ := copyN_char (P := P) I₄.wb 30010 30012
  have hi₄ := I₄.rhi
  have lo₅ : c₅.nreg 30010 = hi := by rw [n₅, Machine.upd_same, hi₄]
  have R₅ : ∀ r, r ≠ 30010 → c₅.nreg r = c₄.nreg r := fun r hr => by
    ram_simp
  have sl₅ : SL A₀ c₄ c₅ := ⟨fun r hb _ => by
      ram_grind, rr₅, fun x _ => by rw [m₅], rm₅, o₅⟩
  -- registers of `c₅` outside the merge scratch
  have K₅ : ∀ r, (30000 ≤ r ∧ r < 40000 ∨ r = ALLOC) → r ≠ 30000 → r ≠ 30001 → r ≠ 30002 →
      (r < 30010 ∨ 30016 < r) → r ≠ 30018 → c₅.nreg r = c.nreg r := by
    intro r hr h0 h1 h2 h3 h4
    rw [R₅ r (by omega), I₄.keep r hr h0 h1 h2 (by omega) (by omega) (by omega) (by omega) h4,
      R₃ r (by omega) (by omega) (by omega) (by omega) (by omega)]
  -- memory of `c₄`
  have M₄ : ∀ x, (x < dst + lo ∨ dst + hi ≤ x) → c₄.nmem x = c.nmem x := fun x hx => by
    rw [I₄.mem x hx, mm₃]
  have hl : l.length = K := by rw [← h.ml, seg_length]
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ?_, ?_⟩
  · exact
    { wb := e₅.wb_right, hJ := hJs c₄ c₅ I₄.hJ sl₅.1 sl₅.2.1 sl₅.2.2.1 sl₅.2.2.2.1 sl₅.2.2.2.2,
      loc := I₄.loc.sl sl₅,
      rK := (K₅ _ (Or.inl (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hK,
      one := (K₅ _ (Or.inl (by omega)) (by omega) (by omega) (by omega) (by omega)
        (by omega)).trans h.one,
      rsrc := (K₅ _ (Or.inl (by omega)) (by omega) (by omega) (by omega) (by omega)
        (by omega)).trans h.rsrc,
      rdst := (K₅ _ (Or.inl (by omega)) (by omega) (by omega) (by omega) (by omega)
        (by omega)).trans h.rdst,
      rw := (K₅ _ (Or.inl (by omega)) (by omega) (by omega) (by omega) (by omega)
        (by omega)).trans h.rw,
      keep := fun r hr h0 h1 h2 h3 h4 => (K₅ r hr h0 h1 h2 h3 h4).trans
        (h.keep r hr h0 h1 h2 h3 h4),
      wpos := hwp, wK := hwK, lo_K := by omega,
      lo_t := by
        rw [lo₅]
        rcases h.lo_t with h' | ⟨t, ht⟩
        · omega
        · by_cases hc : lo + 2 * w ≤ K
          · right; exact ⟨t + 1, by rw [Nat.succ_mul]; omega⟩
          · left; omega,
      arr := harr, bW := hbW,
      ml := by
        rw [m₅, ← h.ml]; apply seg_congr; intro t ht
        exact M₄ _ (by omega),
      out := by
        rw [lo₅, m₅, show hi = lo + (hi - lo) by omega, seg_add, hseg₄]
        have t0 : ∃ t, lo = t * (2 * w) := by
          rcases h.lo_t with h' | ht
          all_goals omega
        obtain ⟨t, ht⟩ := t0
        rw [show lo + (hi - lo) = hi by omega,
          mpass_take_step hwp ht (by omega) (show mid = min (lo + w) l.length by rw [hl])
            (show hi = min (mid + w) l.length by rw [hl])]
        congr 1
        · rw [← h.out]; apply seg_congr; grind
        · rw [mm₃, ← h.ml, seg_drop, seg_take, seg_drop, seg_take]
          congr 1
          · apply seg_arg <;> omega
          · by_cases hc : mid < hi
            · apply seg_arg <;> omega
            · rw [seg_eq_nil (by omega), seg_eq_nil (by omega)],
      mem := fun x hx => by
        rw [m₅, M₄ x (by omega)]; exact h.mem x hx }
  · rw [lo₅]
    have e1 : K - lo = (K - hi) + (hi - lo) := by omega
    rw [e1, Nat.mul_add]
    have : 1 ≤ hi - lo := by omega
    grind

/-- **The pair loop**: one whole pass, `dst[0, K) = mpass w l`, cost `≤ (κ + 30) K + 2`. -/
theorem pairLoop_inv :
    ∃ c' k, Exec P W (pairLoop cmp) c c' k ∧ PairInv W J le Bc A₀ c₀ cP src dst w K l c' ∧
      k ≤ (κ + 30) * (K - c.nreg 30010) + 2 ∧ c'.nreg 30010 = K ∧
      seg c'.nmem dst K = mpass le w l := by
  obtain ⟨c', k, e, I', hex, hk⟩ := Exec.whileLtN_potential
    (PairInv W J le Bc A₀ c₀ cP src dst w K l) (fun d => (κ + 30) * (K - d.nreg 30010))
    (fun _ h => h.wb) (fun d hd ht => pairBody_inv (P := P) hcmp hJs hB hd ht) h
  have hK := I'.rK
  have hlo := I'.lo_K
  have hlK : c'.nreg 30010 = K := by omega
  refine ⟨c', k, e, I', hk, hlK, ?_⟩
  have := I'.out
  rw [hlK, List.take_of_length_le (by rw [← I'.ml, seg_length])] at this
  exact this


end

end pass

/-! ## The passes -/

section passes
variable {P : Polygon} {W : ℕ} {J : Config → Prop} {le : ℕ → ℕ → Bool} {Bc : Finset ℕ} {A₀ : ℕ}

/-- **The invariant of the pass loop** (width `w = 2 ^ p`), relative to the entry configuration
`c₀` of the sort and the configuration `cC` at the start of the passes: the source array holds a
permutation of `L` whose blocks of width `w` are sorted. -/
structure PassInv (W : ℕ) (J : Config → Prop) (le : ℕ → ℕ → Bool) (Bc : Finset ℕ) (A₀ : ℕ)
    (c₀ cC : Config) (K : ℕ) (L : List ℕ) (p : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  hJ : J c
  loc : Loc Bc A₀ c₀ c
  rK : c.nreg 30004 = K
  one : c.nreg 30006 = 1
  rw : c.nreg 30009 = 2 ^ p
  keep : ∀ r, (30000 ≤ r ∧ r < 40000 ∨ r = ALLOC) → r ≠ 30000 → r ≠ 30001 → r ≠ 30002 →
    (r < 30007 ∨ 30016 < r) → r ≠ 30018 → c.nreg r = cC.nreg r
  arr : (c.nreg 30007 = A₀ ∧ c.nreg 30008 = A₀ + K) ∨ (c.nreg 30007 = A₀ + K ∧ c.nreg 30008 = A₀)
  bW : A₀ + 2 * K + 1 ≤ W
  lst : ∃ l, seg c.nmem (c.nreg 30007) K = l ∧ l.Perm L ∧ ChunkSorted le (2 ^ p) l

variable {c₀ cC : Config} {K : ℕ} {L : List ℕ}

section
variable {cmp : Stmt} {κ : ℕ} (hcmp : CmpOK P W cmp Bc J le κ) (hJs : JStable J A₀) (hB : bSort ∉ Bc) (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a) {p : ℕ} {c : Config} (h : PassInv W J le Bc A₀ c₀ cC K L p c)
include hcmp hJs hB trans total h
/-- **One pass** (cost `≤ (κ + 30) K + 7`). -/
theorem passBody_inv
    (hlt : c.nreg 30009 < c.nreg 30004) :
    ∃ c' k, Exec P W (passBody cmp) c c' k ∧ PassInv W J le Bc A₀ c₀ cC K L (p + 1) c' ∧
      k ≤ (κ + 30) * K + 7 := by
  have hK := h.rK
  have hbW := h.bW
  have hw := h.rw
  rw [hK, hw] at hlt
  obtain ⟨l, hl, hperm, hsorted⟩ := h.lst
  have hpos : 0 < 2 ^ p := Nat.two_pow_pos p
  obtain ⟨c₁, e₁, n₁, m₁, rr₁, rm₁, o₁⟩ := constN_char (P := P) h.wb 30010 0 (by omega)
  have R₁ : ∀ r, r ≠ 30010 → c₁.nreg r = c.nreg r := fun r hr => by
    simp_all
  have sl₁ : SL A₀ c c₁ := ⟨fun r hb _ => by
      ram_grind, rr₁, fun x _ => by rw [m₁], rm₁, o₁⟩
  have I₁ : PairInv W J le Bc A₀ c₀ c₁ (c.nreg 30007) (c.nreg 30008) (2 ^ p) K l c₁ :=
    { wb := e₁.wb_right, hJ := hJs c c₁ h.hJ sl₁.1 sl₁.2.1 sl₁.2.2.1 sl₁.2.2.2.1 sl₁.2.2.2.2,
      loc := h.loc.sl sl₁, rK := (R₁ _ (by omega)).trans hK, one := (R₁ _ (by omega)).trans h.one,
      rsrc := R₁ _ (by omega), rdst := R₁ _ (by omega), rw := (R₁ _ (by omega)).trans hw,
      keep := fun _ _ _ _ _ _ _ => rfl, wpos := hpos, wK := hlt,
      lo_K := by simp_all,
      lo_t := Or.inr ⟨0, by simp_all⟩, arr := h.arr, bW := hbW,
      ml := by simp_all,
      out := by rw [n₁, Machine.upd_same, seg_zero, List.take_zero, mpass_nil],
      mem := fun _ _ => rfl }
  obtain ⟨c₂, k₂, e₂, I₂, hk₂, hlo₂, hseg₂⟩ := pairLoop_inv (P := P) hcmp hJs hB I₁
  have hw₂ := I₂.rw
  obtain ⟨c₃, k₃, e₃, rfl, s₃, d₃, w₃, r₃, m₃, rr₃, rm₃, o₃⟩ := swap_exec (P := P) I₂.wb
    (by omega)
  have sl₃ : SL A₀ c₂ c₃ := ⟨fun r hb _ => by
      have := bandOf_sort hb; grind, rr₃,
    fun x _ => by rw [m₃], rm₃, o₃⟩
  have K₃ : ∀ r, (30000 ≤ r ∧ r < 40000 ∨ r = ALLOC) → r ≠ 30000 → r ≠ 30001 → r ≠ 30002 →
      (r < 30007 ∨ 30016 < r) → r ≠ 30018 → c₃.nreg r = c.nreg r := by
    grind [Chazelle.Core.SortR.PairInv.keep]
  have lo₁ : c₁.nreg 30010 = 0 := by rw [n₁, Machine.upd_same]
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), ?_, by grind⟩
  have harr := h.arr
  have hs₂ := I₂.rsrc
  have hd₂ := I₂.rdst
  exact
  { wb := e₃.wb_right, hJ := hJs c₂ c₃ I₂.hJ sl₃.1 sl₃.2.1 sl₃.2.2.1 sl₃.2.2.2.1 sl₃.2.2.2.2,
    loc := I₂.loc.sl sl₃,
    rK := (K₃ _ (Or.inl (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hK,
    one := (K₃ _ (Or.inl (by omega)) (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans h.one,
    rw := by omega,
    keep := fun r hr h0 h1 h2 h3 h4 => (K₃ r hr h0 h1 h2 h3 h4).trans (h.keep r hr h0 h1 h2 h3 h4),
    arr := by grind,
    bW := hbW,
    lst := ⟨mpass le (2 ^ p) l, by grind, (mpass_perm _ _).trans hperm,
      by rw [pow_succ']; exact chunkSorted_mpass trans total hpos hsorted⟩ }

/-- **The passes**: from `w = 2 ^ p` until `w ≥ K`; at the end the source array is sorted.
Cost `≤ ((κ + 30) K + 9) (⌈log₂ K⌉ - p) + 2`. -/
theorem passLoop_inv :
    ∃ c' k, Exec P W (passLoop cmp) c c' k ∧ (∃ p', PassInv W J le Bc A₀ c₀ cC K L p' c') ∧
      k ≤ ((κ + 30) * K + 9) * (Nat.clog 2 K - p) + 2 ∧
      ∃ l, seg c'.nmem (c'.nreg 30007) K = l ∧ l.Perm L ∧ l.Pairwise fun a b => le a b := by
  obtain ⟨c', k, e, ⟨p', I'⟩, hex, hk⟩ := Exec.whileLtN_bounded
    (fun d => ∃ q, PassInv W J le Bc A₀ c₀ cC K L q d)
    (fun d => Nat.clog 2 K - Nat.log 2 (d.nreg 30009)) ((κ + 30) * K + 7)
    (fun _ ⟨_, h⟩ => h.wb) (fun d ⟨q, hd⟩ ht => by
      obtain ⟨d', k, e, I, hk⟩ := passBody_inv (P := P) hcmp hJs hB trans total hd ht
      refine ⟨d', k, e, ⟨q + 1, I⟩, hk, ?_⟩
      have h1 := hd.rw
      have h2 := I.rw
      have h3 := hd.rK
      rw [h1, h3] at ht
      have hq : q < Nat.clog 2 K := (Nat.lt_clog_iff_pow_lt (by norm_num)).2 ht
      rw [h1, h2, Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)]
      omega) ⟨p, h⟩
  refine ⟨c', k, e, ⟨p', I'⟩, by rw [h.rw, Nat.log_pow (by norm_num)] at hk; exact hk, ?_⟩
  obtain ⟨l, hl, hperm, hs⟩ := I'.lst
  have hw := I'.rw
  have hK := I'.rK
  rw [hw, hK] at hex
  refine ⟨l, hl, hperm, pairwise_of_chunkSorted hs ?_⟩
  aesop


end

end passes

/-! ## The copy loop -/

section copy
variable {P : Polygon} {W : ℕ}

section
variable {c : Config} (hc : WordsBounded W c)
include hc
/-- `copyBody`: `A₀[i] := S[i]`, `i := i + 1`, `ALLOC := ALLOC + 2`, cost `6`. -/
theorem copyBody_exec (h1 : c.nreg 30003 + c.nreg 30013 ≤ W)
    (h2 : c.nreg 30007 + c.nreg 30013 ≤ W) (h3 : c.nreg 30013 + c.nreg 30006 ≤ W)
    (h4 : c.nreg 9999 + c.nreg 30017 ≤ W) :
    ∃ c' k, Exec P W copyBody c c' k ∧ k = 6 ∧
      c'.nmem = upd c.nmem (c.nreg 30007 + c.nreg 30013) (c.nmem (c.nreg 30003 + c.nreg 30013)) ∧
      c'.nreg 30013 = c.nreg 30013 + c.nreg 30006 ∧ c'.nreg 9999 = c.nreg 9999 + c.nreg 30017 ∧
      (∀ r, r ≠ 30013 → r ≠ 30016 → r ≠ 30018 → r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold copyBody
  exec_block
  all_goals simp_all

/-- `sortInit`: the constants, the arrays `A₀ = ALLOC`, `A₀ + K`, `i := 0`; cost `5`. -/
theorem sortInit_exec (h1 : 2 ≤ W)
    (h2 : c.nreg 9999 + c.nreg 30004 ≤ W) :
    ∃ c' k, Exec P W sortInit c c' k ∧ k = 5 ∧
      c'.nreg 30006 = 1 ∧ c'.nreg 30017 = 2 ∧ c'.nreg 30007 = c.nreg 9999 ∧
      c'.nreg 30008 = c.nreg 9999 + c.nreg 30004 ∧ c'.nreg 30013 = 0 ∧
      (∀ r, r ≠ 30006 → r ≠ 30017 → r ≠ 30007 → r ≠ 30008 → r ≠ 30013 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sortInit
  exec_block
  · omega
  all_goals simp_all


end

variable {J : Config → Prop} {Bc : Finset ℕ} {A₀ : ℕ}

/-- **The copy loop invariant**, relative to the entry configuration `c₀` of the sort: the first
`i` items are copied to `A₀`, and the allocator is `A₀ + 2 i`. -/
structure CopyInv (W : ℕ) (J : Config → Prop) (Bc : Finset ℕ) (A₀ : ℕ) (c₀ : Config)
    (S K : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  hJ : J c
  loc : Loc Bc A₀ c₀ c
  rS : c.nreg 30003 = S
  rK : c.nreg 30004 = K
  one : c.nreg 30006 = 1
  two : c.nreg 30017 = 2
  rsrc : c.nreg 30007 = A₀
  rdst : c.nreg 30008 = A₀ + K
  iK : c.nreg 30013 ≤ K
  alloc : c.nreg ALLOC = A₀ + 2 * c.nreg 30013
  bS : S + K ≤ A₀
  bW : A₀ + 2 * K + 1 ≤ W
  cp : seg c.nmem A₀ (c.nreg 30013) = seg c₀.nmem S (c.nreg 30013)

variable {c₀ : Config} {S K : ℕ}

/-- **The copy loop**: cost `≤ 8 K + 2`, and the allocator grows by at most the cost. -/
theorem copyLoop_inv (hJs : JStable J A₀) {c : Config} (h : CopyInv W J Bc A₀ c₀ S K c) :
    ∃ c' k, Exec P W copyLoop c c' k ∧ CopyInv W J Bc A₀ c₀ S K c' ∧ c'.nreg 30013 = K ∧
      k ≤ 8 * (K - c.nreg 30013) + 2 ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  obtain ⟨c', k, e, I', hex, hk, hψ⟩ := whileLtN_potential_lb (P := P) (a := 30013) (b := 30004)
    (CopyInv W J Bc A₀ c₀ S K) (fun d => 8 * (K - d.nreg 30013)) (fun d => d.nreg ALLOC)
    (fun _ h => h.wb) (fun d hd ht => by
      have := hd.iK; have := hd.alloc; have := hd.bS; have := hd.bW
      have hK := hd.rK
      rw [hK] at ht
      obtain ⟨d', k, e, rfl, m', i', a', r', rr', rm', o'⟩ := copyBody_exec (P := P) hd.wb
        (by ram_grind) (by ram_grind) (by ram_grind)
        (by ram_grind)
      have sl : SL A₀ d d' := ⟨fun r hb ha => by
          have := bandOf_sort hb
          exact r' r (by omega) (by omega) (by omega) ha, rr',
        fun x hx => by rw [m', Machine.upd_other _ _ _ (by rw [hd.rsrc]; omega)], rm', o'⟩
      have hi' : d'.nreg 30013 = d.nreg 30013 + 1 := by rw [i', hd.one]
      refine ⟨d', 6, e, ?_, by omega, by
        show d'.nreg 9999 ≤ d.nreg 9999 + 6
        rw [a', hd.two]; omega⟩
      exact
      { wb := e.wb_right, hJ := hJs d d' hd.hJ sl.1 sl.2.1 sl.2.2.1 sl.2.2.2.1 sl.2.2.2.2,
        loc := hd.loc.sl sl,
        rS := (r' _ (by omega) (by omega) (by omega) (by omega)).trans hd.rS,
        rK := (r' _ (by omega) (by omega) (by omega) (by omega)).trans hd.rK,
        one := (r' _ (by omega) (by omega) (by omega) (by omega)).trans hd.one,
        two := (r' _ (by omega) (by omega) (by omega) (by omega)).trans hd.two,
        rsrc := (r' _ (by omega) (by omega) (by omega) (by omega)).trans hd.rsrc,
        rdst := (r' _ (by omega) (by omega) (by omega) (by omega)).trans hd.rdst,
        iK := by omega,
        alloc := by
          show d'.nreg 9999 = _
          rw [a', hi', hd.two, show (9999 : ℕ) = ALLOC from rfl, hd.alloc]; omega,
        bS := hd.bS, bW := hd.bW,
        cp := by
          rw [hi', m', hd.rsrc, hd.rS,
            seg_upd_end (m := d.nmem) (d.nmem (S + d.nreg 30013)) _ (fun x => by
              rw [Machine.upd_apply]), seg_snoc, hd.cp]
          congr 2
          exact (hd.loc.2.2.1 _ (by omega)) }) h
  have := I'.iK
  have hK := I'.rK
  rw [hK] at hex
  exact ⟨c', k, e, I', by omega, hk, hψ⟩

end copy

/-! ## The sort -/

/-- The cost bound dominates the cost of the phases. -/
theorem sortCost_ge (κ K : ℕ) :
    5 + (8 * K + 2) + 1 + (((κ + 30) * K + 9) * Nat.clog 2 K + 2) + 1 ≤ sortCost κ K := by
  unfold sortCost
  have hc : Nat.clog 2 K ≤ K := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  grind

/-- The cost bound leaves room for the two arrays. -/
theorem sortCost_room (κ K : ℕ) : 2 * K + 2 ≤ sortCost κ K := by
  unfold sortCost
  grind

/-- **The sort meets its specification** (at the level of executions).  From a word-bounded
configuration `c` satisfying `J`, with the items `L` stored at `S = sr 3` below the allocator,
`K = |L|` in `sr 4`, and room for `sortCost κ K` cells above the allocator, `sortStmt cmp` runs in
at most `sortCost κ K` steps and leaves in `sr 5` the base of a fresh array (between the old and
the new allocator) holding a permutation of `L` sorted for `le`; it keeps `J` and respects
`Frame (insert bSort Bc)`.  Hypotheses on the comparator: `CmpOK` with bands `Bc ∌ bSort`, `le`
transitive and total, and `J` insensitive to the sort's own writes (`JStable`). -/
theorem sortStmt_exec {P : Polygon} {W : ℕ} {cmp : Stmt} {Bc : Finset ℕ} {J : Config → Prop}
    {le : ℕ → ℕ → Bool} {κ : ℕ} (hcmp : CmpOK P W cmp Bc J le κ) (hB : bSort ∉ Bc)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    {c : Config} (hw : WordsBounded W c) (hJ : J c) (hJs : JStable J (c.nreg ALLOC))
    (L : List ℕ) (hL : seg c.nmem (c.nreg 30003) L.length = L) (hK : c.nreg 30004 = L.length)
    (hS : c.nreg 30003 + L.length ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + sortCost κ L.length ≤ W) :
    ∃ c' k, Exec P W (sortStmt cmp) c c' k ∧ k ≤ sortCost κ L.length ∧ J c' ∧
      Frame (insert bSort Bc) c c' k ∧
      c.nreg ALLOC ≤ c'.nreg 30005 ∧ c'.nreg 30005 + L.length ≤ c'.nreg ALLOC ∧
      ∃ L', seg c'.nmem (c'.nreg 30005) L.length = L' ∧ L'.Perm L ∧
        L'.Pairwise fun a b => le a b := by
  set A₀ := c.nreg ALLOC with hA₀
  set K := L.length with hKdef
  have hr := sortCost_room κ K
  have hA : c.nreg 9999 = A₀ := rfl
  -- initialisation
  obtain ⟨c₁, k₁, e₁, rfl, o₁, t₁, s₁, d₁, i₁, r₁, m₁, rr₁, rm₁, out₁⟩ := sortInit_exec (P := P) hw
    (by omega) (by omega)
  have sl₁ : SL A₀ c c₁ := ⟨fun r hb _ => by
      have := bandOf_sort hb; grind,
    rr₁, fun x _ => by rw [m₁], rm₁, out₁⟩
  have C₁ : CopyInv W J Bc A₀ c (c.nreg 30003) K c₁ :=
    { wb := e₁.wb_right, hJ := hJs c c₁ hJ sl₁.1 sl₁.2.1 sl₁.2.2.1 sl₁.2.2.2.1 sl₁.2.2.2.2,
      loc := (Loc.refl Bc A₀ c).sl sl₁,
      rS := r₁ _ (by omega) (by omega) (by omega) (by omega) (by omega),
      rK := (r₁ _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans hK,
      one := o₁, two := t₁, rsrc := s₁, rdst := by omega,
      iK := by omega,
      alloc := by ram_grind,
      bS := hS, bW := by omega, cp := by rw [i₁]; rfl }
  -- the copy
  obtain ⟨c₂, k₂, e₂, C₂, hi₂, hk₂, ha₂⟩ := copyLoop_inv (P := P) hJs C₁
  have hal₂ := C₂.alloc
  have hal₁ := C₁.alloc
  rw [hi₂] at hal₂
  rw [i₁] at hal₁ hk₂
  -- the width
  obtain ⟨c₃, e₃, n₃, m₃, rr₃, rm₃, out₃⟩ := constN_char (P := P) C₂.wb 30009 1 (by omega)
  have R₃ : ∀ r, r ≠ 30009 → c₃.nreg r = c₂.nreg r := fun r hr => by
    ram_simp
  have sl₃ : SL A₀ c₂ c₃ := ⟨fun r hb _ => by
      ram_grind, rr₃, fun x _ => by rw [m₃], rm₃, out₃⟩
  have P₃ : PassInv W J le Bc A₀ c c₃ K L 0 c₃ :=
    { wb := e₃.wb_right, hJ := hJs c₂ c₃ C₂.hJ sl₃.1 sl₃.2.1 sl₃.2.2.1 sl₃.2.2.2.1 sl₃.2.2.2.2,
      loc := C₂.loc.sl sl₃, rK := (R₃ _ (by omega)).trans C₂.rK,
      one := (R₃ _ (by omega)).trans C₂.one, rw := by rw [n₃, Machine.upd_same]; rfl,
      keep := fun _ _ _ _ _ _ _ => rfl,
      arr := Or.inl ⟨(R₃ _ (by omega)).trans C₂.rsrc, (R₃ _ (by omega)).trans C₂.rdst⟩,
      bW := C₂.bW,
      lst := ⟨L, by
          grind [Chazelle.Core.SortR.CopyInv.rsrc, Chazelle.Core.SortR.CopyInv.cp],
        List.Perm.refl L, by rw [pow_zero]; exact chunkSorted_one L⟩ }
  -- the passes
  obtain ⟨c₄, k₄, e₄, ⟨p₄, P₄⟩, hk₄, l, hl, hperm, hsorted⟩ :=
    passLoop_inv (P := P) hcmp hJs hB trans total P₃
  rw [Nat.sub_zero] at hk₄
  -- the output
  obtain ⟨c₅, e₅, n₅, m₅, rr₅, rm₅, out₅⟩ := copyN_char (P := P) P₄.wb 30005 30007
  have R₅ : ∀ r, r ≠ 30005 → c₅.nreg r = c₄.nreg r := fun r hr => by
    ram_simp
  have o₅ : c₅.nreg 30005 = c₄.nreg 30007 := by rw [n₅, Machine.upd_same]
  have sl₅ : SL A₀ c₄ c₅ := ⟨fun r hb _ => by
      ram_grind, rr₅, fun x _ => by rw [m₅], rm₅, out₅⟩
  have loc₅ := P₄.loc.sl sl₅
  have al₅ : c₅.nreg ALLOC = A₀ + 2 * K := by
    rw [R₅ _ (by decide), P₄.keep ALLOC (Or.inr rfl) (by decide) (by decide) (by decide)
      (by decide) (by decide), R₃ _ (by decide)]
    exact hal₂
  have harr := P₄.arr
  have hk0 := sortCost_ge κ K
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega,
    hJs c₄ c₅ P₄.hJ sl₅.1 sl₅.2.1 sl₅.2.2.1 sl₅.2.2.2.1 sl₅.2.2.2.2, ?_, by omega,
    by omega, l, by grind, hperm, hsorted⟩
  refine ⟨fun r hr ha => ?_, fun r hr => ?_, fun a ha => loc₅.2.2.1 a ha,
    fun a _ => by rw [loc₅.2.2.2.1], loc₅.2.2.2.2, by omega, ?_⟩
  · rw [Finset.mem_insert, not_or] at hr
    exact loc₅.1 r hr.2 hr.1 ha
  · rw [Finset.mem_insert, not_or] at hr
    exact loc₅.2.1 r hr.2
  omega

/-- **The sort as a `Meets` judgement** (bands `bSort` and the comparator's `Bc`).  The
comparator's invariant `Ctx P W c₀` may depend on the entry configuration `c₀` (for instance on the
memory below the allocator, which the sort never writes), and so may the order `le P c₀`.
Input: the items `seg c.nmem S K` (`S = rd c bSort 3`, `K = rd c bSort 4`) below the allocator.
Output (`rd c' bSort 5`): a fresh array, between the old and the new allocator, holding a sorted
permutation of the items.  Cost `sortCost κ K`. -/
theorem sort_meets {cmp : Stmt} {Bc : Finset ℕ} (hB : bSort ∉ Bc) (κ : ℕ)
    (Ctx : Polygon → ℕ → Config → Config → Prop) (le : Polygon → Config → ℕ → ℕ → Bool) :
    Meets (sortStmt cmp) (insert bSort Bc)
      (fun P W c => Ctx P W c c ∧ CmpOK P W cmp Bc (Ctx P W c) (le P c) κ ∧
        JStable (Ctx P W c) (c.nreg ALLOC) ∧
        (∀ a b d, le P c a b → le P c b d → le P c a d) ∧ (∀ a b, le P c a b || le P c b a) ∧
        rd c bSort 3 + rd c bSort 4 ≤ c.nreg ALLOC)
      (fun P c c' => c.nreg ALLOC ≤ rd c' bSort 5 ∧ rd c' bSort 5 + rd c bSort 4 ≤ c'.nreg ALLOC ∧
        (seg c'.nmem (rd c' bSort 5) (rd c bSort 4)).Perm (seg c.nmem (rd c bSort 3) (rd c bSort 4)) ∧
        (seg c'.nmem (rd c' bSort 5) (rd c bSort 4)).Pairwise fun a b => le P c a b)
      (fun _ c => sortCost κ (rd c bSort 4)) := by
  rintro P W c hw ⟨hJ, hcmp, hJs, htr, hto, hS⟩ hroom
  simp only at hroom ⊢
  have e3 : rd c bSort 3 = c.nreg 30003 := rfl
  have e4 : rd c bSort 4 = c.nreg 30004 := rfl
  have e5 : ∀ c' : Config, rd c' bSort 5 = c'.nreg 30005 := fun _ => rfl
  set L := seg c.nmem (c.nreg 30003) (c.nreg 30004) with hL
  have hlen : L.length = c.nreg 30004 := seg_length
  obtain ⟨c', k, e, hk, hJ', hfr, h1, h2, L', h3, h4, h5⟩ := sortStmt_exec (P := P) hcmp hB htr hto
    hw hJ hJs L (by rw [hlen]) hlen.symm (by omega)
    (by simp_all)
  grind

end

end SortR

end Chazelle.Core
