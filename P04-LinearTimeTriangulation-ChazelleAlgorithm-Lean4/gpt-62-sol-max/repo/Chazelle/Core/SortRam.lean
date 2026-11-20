module

meta import Chazelle.Programs.RamEval

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

/-- Move `src[i]` to `dst[k]` and advance the chosen source cursor. -/
def takeCursor (i : ℕ) : Stmt :=
  block [.addN 30016 30007 i, .loadN 30018 30016, .addN 30016 30008 30015, .storeN 30016 30018,
    .addN i i 30006]

abbrev takeL := takeCursor 30013
abbrev takeR := takeCursor 30014

/-- One output word of a merge. -/
def mergeStep (cmp : Stmt) : Stmt :=
  .ifLtN 30013 30011
    (.ifLtN 30014 30012 (.seq cmpLoad (.seq cmp (.ifLtN 30002 30006 takeR takeL))) takeL) takeR

/-- The merge loop body: one output word, `k := k + 1`. -/
def mergeBody (cmp : Stmt) : Stmt := .seq (mergeStep cmp) (.instr (.addN 30015 30015 30006))

/-- The merge of `src[lo, mid)` and `src[mid, hi)` into `dst[lo, hi)`. -/
def mergeLoop (cmp : Stmt) : Stmt := .whileLtN 30015 30012 (mergeBody cmp)

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
    c'.rreg = c.rreg → (MemEqBelow A₀ c'.nmem c.nmem) → c'.rmem = c.rmem →
      c'.output = c.output → J c'

/-! ## Sort-local steps -/

/-- A step of the sort itself: only band `bSort`, the allocator and memory from `A₀` on change. -/
def SL (A₀ : ℕ) (c c' : Config) : Prop :=
  (∀ r, bandOf r ≠ bSort → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
    (MemEqBelow A₀ c'.nmem c.nmem) ∧ c'.rmem = c.rmem ∧ c'.output = c.output

/-- **The global frame of the sort** relative to its entry configuration `c₀`: registers outside
the bands `bSort`, `Bc` and the allocator, real registers outside `Bc`, memory below `A₀`, real
memory and output are those of `c₀`. -/
def Loc (Bc : Finset ℕ) (A₀ : ℕ) (c₀ c : Config) : Prop :=
  (∀ r, bandOf r ∉ Bc → bandOf r ≠ bSort → r ≠ ALLOC → c.nreg r = c₀.nreg r) ∧
    (∀ r, bandOf r ∉ Bc → c.rreg r = c₀.rreg r) ∧ (MemEqBelow A₀ c.nmem c₀.nmem) ∧
    c.rmem = c₀.rmem ∧ c.output = c₀.output

/-- The entry configuration is within the frame. -/
theorem Loc.refl (Bc : Finset ℕ) (A₀ : ℕ) (c : Config) : Loc Bc A₀ c c :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- A sort-local step keeps the global frame. -/
theorem Loc.sl {Bc : Finset ℕ} {A₀ : ℕ} {c₀ c c' : Config} (h : Loc Bc A₀ c₀ c)
    (h' : SL A₀ c c') : Loc Bc A₀ c₀ c' :=
  ⟨fun r h1 h2 h3 => (h'.1 r h2 h3).trans (h.1 r h1 h2 h3),
    fun r h1 => by rw [h'.2.1]; exact h.2.1 r h1,
    fun a ha => (h'.2.2.1 a ha).trans (h.2.2.1 a ha), h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

/-- The band of a register of the sort band. -/
theorem bandOf_sort {r : ℕ} (h : bandOf r ≠ bSort) : r < 30000 ∨ 40000 ≤ r := by
  reg_omega

/-! ## The straight-line pieces -/

section pieces
variable {P : Polygon} {W : ℕ}

private theorem takeCursor_exec (c : Config) (hc : WordsBounded W c) {i : ℕ}
    (hi : i = 30013 ∨ i = 30014) (h1 : c.nreg 30007 + c.nreg i ≤ W)
    (h2 : c.nreg 30008 + c.nreg 30015 ≤ W) (h3 : c.nreg i + c.nreg 30006 ≤ W) :
    ∃ c' k, Exec P W (takeCursor i) c c' k ∧ k = 5 ∧
      c'.nmem = upd c.nmem (c.nreg 30008 + c.nreg 30015) (c.nmem (c.nreg 30007 + c.nreg i)) ∧
      c'.nreg i = c.nreg i + c.nreg 30006 ∧
      (∀ r, r ≠ i → r ≠ 30016 → r ≠ 30018 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  rcases hi with rfl | rfl <;> (unfold takeCursor; exec_block!; simp_all)

/-- `cmpLoad`: `sr 0 := src[i]`, `sr 1 := src[j]` (scratch `sr 16`). -/
theorem cmpLoad_exec (c : Config) (hc : WordsBounded W c) (h1 : c.nreg 30007 + c.nreg 30013 ≤ W)
    (h2 : c.nreg 30007 + c.nreg 30014 ≤ W) :
    ∃ c' k, Exec P W cmpLoad c c' k ∧ k = 4 ∧
      c'.nreg 30000 = c.nmem (c.nreg 30007 + c.nreg 30013) ∧
      c'.nreg 30001 = c.nmem (c.nreg 30007 + c.nreg 30014) ∧
      (∀ r, r ≠ 30000 → r ≠ 30001 → r ≠ 30016 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cmpLoad
  exec_block!
  simp_all

/-- `addN` with its effect spelled out. -/
theorem addN_char {c : Config} (hc : WordsBounded W c) (r x y : ℕ) (h : c.nreg x + c.nreg y ≤ W) :
    ∃ c', Exec P W (.instr (.addN r x y)) c c' 1 ∧ c'.nreg = upd c.nreg r (c.nreg x + c.nreg y) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  ⟨_, Exec.addN hc r x y h, rfl, rfl, rfl, rfl, rfl⟩

/-- `copyN` with its effect spelled out. -/
theorem copyN_char {c : Config} (hc : WordsBounded W c) (r x : ℕ) :
    ∃ c', Exec P W (.instr (.copyN r x)) c c' 1 ∧ c'.nreg = upd c.nreg r (c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  ⟨_, Exec.copyN hc r x, rfl, rfl, rfl, rfl, rfl⟩

/-- `constN` with its effect spelled out. -/
theorem constN_char {c : Config} (hc : WordsBounded W c) (r v : ℕ) (h : v ≤ W) :
    ∃ c', Exec P W (.instr (.constN r v)) c c' 1 ∧ c'.nreg = upd c.nreg r v ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  ⟨_, Exec.constN hc r v h, rfl, rfl, rfl, rfl, rfl⟩

/-- `clamp r x`: `r := min (x + w) K`, cost `≤ 3`. -/
theorem clamp_exec {c : Config} (hc : WordsBounded W c) (r x : ℕ) (hr : r ≠ 30004)
    (h : c.nreg x + c.nreg 30009 ≤ W) :
    ∃ c' k, Exec P W (clamp r x) c c' k ∧ k ≤ 3 ∧
      c'.nreg = upd c.nreg r (min (c.nreg x + c.nreg 30009) (c.nreg 30004)) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, e₁, n₁, m₁, rr₁, rm₁, o₁⟩ := addN_char (P := P) hc r x 30009 h
  have hK : c₁.nreg 30004 = c.nreg 30004 := by rw [n₁, Machine.upd_other _ _ _ (Ne.symm hr)]
  have hR : c₁.nreg r = c.nreg x + c.nreg 30009 := by simp_all
  by_cases ht : c₁.nreg 30004 < c₁.nreg r
  · obtain ⟨c₂, e₂, n₂, m₂, rr₂, rm₂, o₂⟩ := copyN_char (P := P) e₁.wb_right r 30004
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true ht e₂), le_refl _, ?_, m₂.trans m₁, rr₂.trans rr₁,
      rm₂.trans rm₁, o₂.trans o₁⟩
    rw [n₂, hK, n₁, Machine.upd_upd_same]
    congr 1
    rw [hK, hR] at ht
    omega
  · refine ⟨c₁, _, .seq e₁ (.ifLtN_false ht (.skip e₁.wb_right)), le_refl _, ?_, m₁, rr₁, rm₁,
      o₁⟩
    simp_all

/-- `cursors`: `i := lo`, `j := mid`, `k := lo`, cost `3`. -/
theorem cursors_exec {c : Config} (hc : WordsBounded W c) :
    ∃ c' k, Exec P W cursors c c' k ∧ k = 3 ∧
      c'.nreg 30013 = c.nreg 30010 ∧ c'.nreg 30014 = c.nreg 30011 ∧
      c'.nreg 30015 = c.nreg 30010 ∧
      (∀ r, r ≠ 30013 → r ≠ 30014 → r ≠ 30015 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  ram_exec

/-- `swapBlock`: exchange the arrays, double the width, cost `4`. -/
theorem swap_exec {c : Config} (hc : WordsBounded W c) (h : c.nreg 30009 + c.nreg 30009 ≤ W) :
    ∃ c' k, Exec P W swapBlock c c' k ∧ k = 4 ∧
      c'.nreg 30007 = c.nreg 30008 ∧ c'.nreg 30008 = c.nreg 30007 ∧
      c'.nreg 30009 = c.nreg 30009 + c.nreg 30009 ∧
      (∀ r, r ≠ 30007 → r ≠ 30008 → r ≠ 30009 → r ≠ 30018 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  ram_exec

end pieces

/-! ## Segments -/

/-- Dropping from a list read as a segment. -/
theorem drop_of_seg {m : ℕ → ℕ} {p n : ℕ} {l : List ℕ} (h : seg m p n = l) (d : ℕ) :
    l.drop d = seg m (p + d) (n - d) := by
  rw [← h, seg_drop]

/-- A nonempty segment starts with its first word. -/
theorem seg_pos {m : ℕ → ℕ} {p n : ℕ} (h : 0 < n) : seg m p n = m p :: seg m (p + 1) (n - 1) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [seg_succ]; rfl

/-- A segment of length `0` is empty. -/
theorem seg_eq_nil {m : ℕ → ℕ} {p n : ℕ} (h : n = 0) : seg m p n = [] := by
  subst h; rfl

/-- Rewriting the bounds of a segment. -/
theorem seg_arg {m : ℕ → ℕ} {p p' n n' : ℕ} (hp : p = p') (hn : n = n') :
    seg m p n = seg m p' n' := by
  subst hp hn; rfl

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
  have e := fun r (h1 : 30000 ≤ r ∧ r < 40000) (h2 : r ≠ 30000) (h3 : r ≠ 30001) (h4 : r ≠ 30002)
    (h5 : r ≠ 30016) (h6 : r ≠ 30018) => hr r (Or.inl h1) h2 h3 h4 h5 h6
  have e6 := (ram_app% (e 30006 ?_ ?_ ?_ ?_ ?_ ?_))
  have e7 := (ram_app% (e 30007 ?_ ?_ ?_ ?_ ?_ ?_))
  have e8 := (ram_app% (e 30008 ?_ ?_ ?_ ?_ ?_ ?_))
  have e11 := (ram_app% (e 30011 ?_ ?_ ?_ ?_ ?_ ?_))
  have e12 := (ram_app% (e 30012 ?_ ?_ ?_ ?_ ?_ ?_))
  have e13 := (ram_app% (e 30013 ?_ ?_ ?_ ?_ ?_ ?_))
  have e14 := (ram_app% (e 30014 ?_ ?_ ?_ ?_ ?_ ?_))
  have e15 := (ram_app% (e 30015 ?_ ?_ ?_ ?_ ?_ ?_))
  exact
  { wb := hw, hJ := hJ, loc := hloc, one := e6.trans h.one, rsrc := e7.trans h.rsrc,
    rdst := e8.trans h.rdst, rmid := e11.trans h.rmid, rhi := e12.trans h.rhi,
    keep := fun r hr1 h0 h1 h2 h13 h14 h15 h16 h18 =>
      (hr r hr1 h0 h1 h2 h16 h18).trans (h.keep r hr1 h0 h1 h2 h13 h14 h15 h16 h18),
    lo_i := e13 ▸ h.lo_i, i_mid := e13 ▸ h.i_mid, mid_j := e14 ▸ h.mid_j, j_hi := e14 ▸ h.j_hi,
    rk := by rw [e13, e14, e15]; exact h.rk, bsrc := h.bsrc, bdst := h.bdst, disj := h.disj,
    dA := h.dA, ma := hm ▸ h.ma, mb := hm ▸ h.mb, out := by rw [hm, e13, e14, e15]; exact h.out,
    mem := fun x hx => by rw [hm]; exact h.mem x hx }

/-- The memory after a store at `dst + k` (`lo ≤ k < hi`) reads the same on the source window
and outside `[dst + lo, dst + hi)`. -/
theorem store_facts {c : Config} (h : MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c) {k v : ℕ}
    (hk1 : lo ≤ k) (hk2 : k < hi) :
    seg (upd c.nmem (dst + k) v) (src + lo) (mid - lo) = a ∧
      seg (upd c.nmem (dst + k) v) (src + mid) (hi - mid) = b ∧
      (∀ x, (x < dst + lo ∨ dst + hi ≤ x) → upd c.nmem (dst + k) v x = cS.nmem x) := by
  have := h.lo_i; have := h.i_mid; have := h.mid_j; have := h.j_hi; have := h.disj
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [← h.ma]; apply seg_congr; intro t ht
    rw [Machine.upd_other _ _ _ (by have := h.disj; omega)]
  · rw [← h.mb]; apply seg_congr; intro t ht
    rw [Machine.upd_other _ _ _ (by have := h.disj; omega)]
  · ram_post

/-- The remaining items of a nonempty run start with the word at the cursor. -/
private theorem drop_step {m : ℕ → ℕ} {src lo hi i : ℕ} {a : List ℕ}
    (h : seg m (src + lo) (hi - lo) = a) (hlo : lo ≤ i) (hhi : i < hi) :
    a.drop (i - lo) = m (src + i) :: a.drop (i + 1 - lo) := by
  ram_rw [drop_of_seg h, drop_of_seg h, seg_pos]
  congr 1
  · congr 1; omega
  · apply seg_arg <;> omega

private theorem drop_head {m : ℕ → ℕ} {src lo hi i : ℕ} {a xs : List ℕ} {x : ℕ}
    (h : seg m (src + lo) (hi - lo) = a) (hlo : lo ≤ i) (hx : a.drop (i - lo) = x :: xs) :
    i < hi ∧ x = m (src + i) := by
  have hhi : i < hi := by
    by_contra hn
    ram_rw [drop_of_seg h, seg_eq_nil] at hx
    exact List.cons_ne_nil _ _ hx.symm
  exact ⟨hhi, (List.cons.inj ((drop_step h hlo hhi).symm.trans hx)).1.symm⟩

/-- Consume a head from either run, according to the stable merge comparison. -/
private theorem merge_advance (hJs : JStable J A₀) {c : Config}
    (h : MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c) (left : Bool)
    (hlt : if left then c.nreg 30013 < mid else c.nreg 30014 < hi)
    (hle : (if left then c.nreg 30014 < hi else c.nreg 30013 < mid) →
      le (c.nmem (src + c.nreg 30013)) (c.nmem (src + c.nreg 30014)) = left) :
    ∃ c₃ c₄, Exec P W (takeCursor (if left then 30013 else 30014)) c c₃ 5 ∧
      Exec P W (.instr (.addN 30015 30015 30006)) c₃ c₄ 1 ∧
      MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c₄ ∧
      c₄.nreg 30015 = c.nreg 30015 + 1 := by
  let r := if left then 30013 else 30014
  let i := c.nreg 30013 + (if left then 1 else 0)
  let j := c.nreg 30014 + (if left then 0 else 1)
  have hr : r = 30013 ∨ r = 30014 := by cases left <;> simp [r]
  have hj := h.j_hi
  have hk := h.rk
  have hmj := h.mid_j
  have hbs := h.bsrc
  have hbd := h.bdst
  have hli := h.lo_i
  have him := h.i_mid
  have hir : c.nreg r < hi := by cases left <;> simp [r] at hlt ⊢ <;> omega
  have hkhi : c.nreg 30015 < hi := by cases left <;> simp at hlt <;> omega
  obtain ⟨c₃, -, e₃, rfl, hm₃, hi₃, hr₃, rr₃, rm₃, o₃⟩ := takeCursor_exec (P := P) c h.wb hr
    (by rw [h.rsrc]; omega) (by rw [h.rdst]; omega) (by rw [h.one]; omega)
  have k₃ : c₃.nreg 30015 = c.nreg 30015 := (ram_app% (hr₃ _ ?_ ?_ ?_))
  have o3 : c₃.nreg 30006 = 1 := ram_app% ((hr₃ _ ?_ ?_ ?_).trans h.one)
  obtain ⟨c₄, e₄, n₄, m₄, rr₄, rm₄, o₄⟩ := addN_char (P := P) e₃.wb_right 30015 30015 30006
    (by rw [k₃, o3]; omega)
  let v := c.nmem (src + c.nreg r)
  have hm₄ : c₄.nmem = upd c.nmem (dst + c.nreg 30015) v := by rw [m₄, hm₃, h.rsrc, h.rdst]
  obtain ⟨sa, sb, sm⟩ := store_facts h (v := v) (k := c.nreg 30015) (by omega) hkhi
  have r₄ (a : ℕ) (h1 : a ≠ r) (h2 : a ≠ 30015) (h3 : a ≠ 30016) (h4 : a ≠ 30018) :
      c₄.nreg a = c.nreg a := by
    rw [n₄, Machine.upd_other _ _ _ h2]; exact hr₃ a h1 h3 h4
  have inc : c₄.nreg r = c.nreg r + 1 := by ram_rw [n₄, Machine.upd_other _ _, hi₃, h.one]
  have i₄ : c₄.nreg 30013 = i := by
    cases left
    · exact (ram_app% (r₄ _ ?_ ?_ ?_ ?_))
    · exact inc
  have j₄ : c₄.nreg 30014 = j := by
    cases left
    · exact inc
    · exact (ram_app% (r₄ _ ?_ ?_ ?_ ?_))
  have k₄ : c₄.nreg 30015 = c.nreg 30015 + 1 := by rw [n₄, Machine.upd_same, k₃, o3]
  have hsl : SL A₀ c c₄ := by
    refine ⟨fun x hb _ => ?_, rr₄.trans rr₃, fun x hx => ?_, rm₄.trans rm₃, o₄.trans o₃⟩
    · have := bandOf_sort hb
      refine r₄ x ?_ ?_ ?_ ?_ <;> omega
    · rw [hm₄, Machine.upd_other _ _ _ (by have := h.dA; omega)]
  have hout : (seg c.nmem (dst + lo) (c.nreg 30015 - lo) ++ [v]) ++
      List.merge (a.drop (i - lo)) (b.drop (j - mid)) le = List.merge a b le := by
    have e := h.out
    cases left
    · dsimp [r, i, j, v] at hlt hle ⊢
      rw [drop_step h.mb hmj hlt] at e
      apply merge_step_right e
      intro x xs hx
      obtain ⟨hc, rfl⟩ := drop_head h.ma hli hx
      simp [hle hc]
    · dsimp [r, i, j, v] at hlt hle ⊢
      rw [drop_step h.ma hli hlt] at e
      apply merge_step_left e
      intro y ys hy
      obtain ⟨hc, rfl⟩ := drop_head h.mb hmj hy
      exact hle hc
  refine ⟨c₃, c₄, e₃, e₄, ?_, k₄⟩
  exact
  { wb := e₄.wb_right, hJ := hJs c c₄ h.hJ hsl.1 hsl.2.1 hsl.2.2.1 hsl.2.2.2.1 hsl.2.2.2.2,
    loc := h.loc.sl hsl,
    one := (r₄ _ (by omega) (by decide) (by decide) (by decide)).trans h.one,
    rsrc := (r₄ _ (by omega) (by decide) (by decide) (by decide)).trans h.rsrc,
    rdst := (r₄ _ (by omega) (by decide) (by decide) (by decide)).trans h.rdst,
    rmid := (r₄ _ (by omega) (by decide) (by decide) (by decide)).trans h.rmid,
    rhi := (r₄ _ (by omega) (by decide) (by decide) (by decide)).trans h.rhi,
    keep := fun x hb h0 h1 h2 h13 h14 h15 h16 h18 =>
      (r₄ x (by omega) h15 h16 h18).trans (h.keep x hb h0 h1 h2 h13 h14 h15 h16 h18),
    lo_i := by rw [i₄]; cases left <;> simp [i] <;> omega,
    i_mid := by rw [i₄]; cases left <;> simp [i] at hlt ⊢ <;> omega,
    mid_j := by rw [j₄]; cases left <;> simp [j] <;> omega,
    j_hi := by rw [j₄]; cases left <;> simp [j] at hlt ⊢ <;> omega,
    rk := by rw [i₄, j₄, k₄]; cases left <;> simp [i, j] <;> omega,
    bsrc := h.bsrc, bdst := h.bdst, disj := h.disj, dA := h.dA, ma := hm₄.symm ▸ sa,
    mb := hm₄.symm ▸ sb,
    out := by
      rw [hm₄, i₄, j₄, k₄, show c.nreg 30015 + 1 - lo = (c.nreg 30015 - lo) + 1 by omega,
        seg_upd_end (m := c.nmem) v _ (fun x => by
          rw [Machine.upd_apply, show dst + lo + (c.nreg 30015 - lo) = dst + c.nreg 30015 by omega])]
      exact hout,
    mem := fun x hx => by rw [hm₄]; exact sm x hx }

/-- The comparator keeps the global frame. -/
theorem Loc.cmp {c₀ c c' : Config} (h : Loc Bc A₀ c₀ c)
    (hr : ∀ r, r ≠ 30000 → r ≠ 30001 → r ≠ 30002 → (bandOf r ∉ Bc ∨ r = ALLOC) →
      c'.nreg r = c.nreg r)
    (hrr : ∀ r, bandOf r ∉ Bc → c'.rreg r = c.rreg r) (hm : c'.nmem = c.nmem)
    (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) : Loc Bc A₀ c₀ c' := by
  refine ⟨fun r h1 h2 h3 => ?_, fun r h1 => (hrr r h1).trans (h.2.1 r h1),
    fun a ha => by rw [hm]; exact h.2.2.1 a ha, hrm.trans h.2.2.2.1, ho.trans h.2.2.2.2⟩
  have := bandOf_sort h2
  exact ((ram_app% (hr r ?_ ?_ ?_ (Or.inl h1)))).trans (h.1 r h1 h2 h3)

section

variable {cmp : Stmt} {κ : ℕ} (hcmp : CmpOK P W cmp Bc J le κ)
    (hJs : JStable J A₀) (hB : bSort ∉ Bc) {c : Config}
    (h : MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c)
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
  · have t1 : c.nreg 30013 < c.nreg 30011 := by rwa [h.rmid]
    by_cases hj1 : c.nreg 30014 < hi
    · have t2 : c.nreg 30014 < c.nreg 30012 := by rwa [h.rhi]
      -- load and compare
      obtain ⟨c₁, k₁, e₁, rfl, x₁, y₁, r₁, m₁, rr₁, rm₁, o₁⟩ := cmpLoad_exec (P := P) c h.wb
        (by rw [h.rsrc]; omega) (by rw [h.rsrc]; omega)
      have sl₁ : SL A₀ c c₁ := ⟨fun r hb _ => by
          have := bandOf_sort hb; exact (ram_app% (r₁ r ?_ ?_ ?_)), rr₁,
        fun x _ => by rw [m₁], rm₁, o₁⟩
      have I₁ := h.congr e₁.wb_right (hJs c c₁ h.hJ sl₁.1 sl₁.2.1 sl₁.2.2.1 sl₁.2.2.2.1
        sl₁.2.2.2.2) (h.loc.sl sl₁) m₁ (fun r _ h0 h1' _ h16 _ => r₁ r h0 h1' h16)
      obtain ⟨c₂, k₂, e₂, hk₂, hJ₂, bit₂, r₂, rr₂, m₂, rm₂, o₂⟩ := hcmp c₁ e₁.wb_right I₁.hJ
      have I₂ := I₁.congr e₂.wb_right hJ₂ (I₁.loc.cmp r₂ rr₂ m₂ rm₂ o₂) m₂
        (fun r hr h0 h1' h2' _ _ => r₂ r h0 h1' h2' (by
          rcases hr with hr | hr
          · left; intro hm; apply hB
            have : bandOf r = bSort := by unfold bandOf bSort; omega
            rwa [this] at hm
          · exact Or.inr hr))
      have i₂ : c₂.nreg 30013 = c.nreg 30013 := by
        ram_rw [r₂ _ (by omega) (by omega) (by omega) (Or.inl (by
          assumption)),
          r₁]
      have j₂ : c₂.nreg 30014 = c.nreg 30014 := by
        ram_rw [r₂ _ (by omega) (by omega) (by omega) (Or.inl (by
          assumption)),
          r₁]
      have k₂e : c₂.nreg 30015 = c.nreg 30015 := by
        ram_rw [r₂ _ (by omega) (by omega) (by omega) (Or.inl (by
          assumption)),
          r₁]
      have mm₂ := m₂.trans m₁
      rw [x₁, y₁, h.rsrc] at bit₂
      by_cases hle : le (c.nmem (src + c.nreg 30013)) (c.nmem (src + c.nreg 30014)) = true
      · rw [ite_eq_left hle] at bit₂
        obtain ⟨c₃, c₄, e₃, e₄, I₄, k₄⟩ := merge_advance (P := P) hJs I₂ true (by rwa [i₂])
          (fun _ => by rwa [mm₂, i₂, j₂])
        refine ⟨c₄, _, .seq (.ifLtN_true t1 (.ifLtN_true t2 (.seq e₁ (.seq e₂
          (.ifLtN_false (by simp [bit₂, I₂.one]) e₃))))) e₄, I₄, by omega,
          by rw [k₄, k₂e]⟩
      · rw [ite_eq_right hle] at bit₂
        obtain ⟨c₃, c₄, e₃, e₄, I₄, k₄⟩ := merge_advance (P := P) hJs I₂ false (by rwa [j₂])
          (fun _ => by rw [mm₂, i₂, j₂]; simpa using hle)
        refine ⟨c₄, _, (by ram_path [bit₂, I₂.one]), I₄, by omega,
          by rw [k₄, k₂e]⟩
    · have t2 : ¬ c.nreg 30014 < c.nreg 30012 := by rwa [h.rhi]
      obtain ⟨c₃, c₄, e₃, e₄, I₄, k₄⟩ := merge_advance (P := P) hJs h true hi1 (fun h' => absurd h' hj1)
      exact ⟨c₄, _, .seq (.ifLtN_true t1 (.ifLtN_false t2 e₃)) e₄, I₄, by omega, k₄⟩
  · have t1 : ¬ c.nreg 30013 < c.nreg 30011 := by rwa [h.rmid]
    obtain ⟨c₃, c₄, e₃, e₄, I₄, k₄⟩ := merge_advance (P := P) hJs h false (by change c.nreg 30014 < hi; omega) (fun h' => absurd h' hi1)
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
      exact ⟨d', k, e, I, hk, by rw [hk']; omega⟩) h
  refine ⟨c', k, e, I', hk, ?_⟩
  have := I'.out
  have hi' := I'.rhi
  have h1 := I'.i_mid
  have h2 := I'.j_hi
  have h3 := I'.rk
  have h4 := I'.lo_i
  have h5 := I'.mid_j
  rw [hi'] at hex
  rwa [List.drop_of_length_le (by rw [← I'.ma]; simp; omega),
    List.drop_of_length_le (by rw [← I'.mb]; simp; omega), List.nil_merge, List.append_nil,
    show c'.nreg 30015 - lo = hi - lo by omega] at this

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
    rw [← List.take_add]; congr 1; omega
  have hlen : (l.take lo).length = t * (2 * w) := by
    rw [List.length_take, ← hlo]; omega
  have hb : hi - lo ≤ 2 * w := by omega
  have hlen2 : ((l.drop lo).take (hi - lo)).length ≤ 2 * w := by
    rw [List.length_take]; exact (Nat.min_le_left _ _).trans hb
  rw [e1, mpass_append hw t _ _ hlen, mpass_small hw _ hlen2]
  congr 2
  · rw [List.take_take]; congr 1; omega
  · rw [List.drop_take, List.drop_drop]
    by_cases h : lo + w ≤ l.length
    · rw [show lo + w = mid by omega]; congr 1; omega
    · rw [List.drop_of_length_le (l := l) (by omega), List.drop_of_length_le (l := l) (by omega)]
      simp

section

variable {cmp : Stmt} {κ : ℕ} (hcmp : CmpOK P W cmp Bc J le κ)
    (hJs : JStable J A₀) (hB : bSort ∉ Bc) {c : Config}
    (h : PairInv W J le Bc A₀ c₀ cP src dst w K l c)
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
    (by omega) (by rw [h.rw]; omega)
  have n₁' : c₁.nreg = upd c.nreg 30011 mid := by rw [n₁, h.rw, hK]
  have b₁ : c₁.nreg 30011 + c₁.nreg 30009 ≤ W := by
    ram_simp [n₁', h.rw] <;> reg_omega
  obtain ⟨c₂, k₂, e₂, hk₂, n₂, m₂, rr₂, rm₂, o₂⟩ := clamp_exec (P := P) e₁.wb_right 30012 30011
    (by omega) b₁
  have n₂' : c₂.nreg = upd (upd c.nreg 30011 mid) 30012 hi := by
    ram_finish [n₂, n₁', h.rw, hK]
  obtain ⟨c₃, k₃, e₃, rfl, i₃, j₃, kk₃, r₃, m₃, rr₃, rm₃, o₃⟩ := cursors_exec (P := P) e₂.wb_right
  have R₃ : ∀ r, r ≠ 30011 → r ≠ 30012 → r ≠ 30013 → r ≠ 30014 → r ≠ 30015 →
      c₃.nreg r = c.nreg r := by
    ram_post
  have mid₃ : c₃.nreg 30011 = mid := by
    ram_finish [r₃, n₂']
  have hi₃ : c₃.nreg 30012 = hi := by
    ram_finish [r₃, n₂']
  have lo₂ : c₂.nreg 30010 = lo := by
    ram_post
  have mid₂ : c₂.nreg 30011 = mid := by
    ram_finish [n₂']
  rw [lo₂] at i₃ kk₃
  rw [mid₂] at j₃
  have mm₃ : c₃.nmem = c.nmem := by rw [m₃, m₂, m₁]
  have sl₃ : SL A₀ c c₃ := ⟨fun r hb _ => by
      have := bandOf_sort hb; exact (ram_app% (R₃ r ?_ ?_ ?_ ?_ ?_)),
    by rw [rr₃, rr₂, rr₁], fun x _ => by rw [mm₃], by rw [rm₃, rm₂, rm₁], by rw [o₃, o₂, o₁]⟩
  have hJ₃ := hJs c c₃ h.hJ sl₃.1 sl₃.2.1 sl₃.2.2.1 sl₃.2.2.2.1 sl₃.2.2.2.2
  -- the merge invariant at entry
  have I₃ : MergeInv W J le Bc A₀ c₀ c₃ src dst lo mid hi (seg c₃.nmem (src + lo) (mid - lo))
      (seg c₃.nmem (src + mid) (hi - mid)) c₃ :=
    { wb := e₃.wb_right, hJ := hJ₃, loc := h.loc.sl sl₃,
      one := (R₃ _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.one,
      rsrc := (R₃ _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.rsrc,
      rdst := (R₃ _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.rdst,
      rmid := mid₃, rhi := hi₃, keep := fun _ _ _ _ _ _ _ _ _ _ => rfl,
      lo_i := by rw [i₃], i_mid := by rw [i₃]; omega, mid_j := by rw [j₃],
      j_hi := by rw [j₃]; omega, rk := by omega,
      bsrc := by omega, bdst := by omega, disj := by omega, dA := by omega, ma := rfl, mb := rfl,
      out := by ram_finish [kk₃, i₃, j₃, Nat.sub_self, seg_zero, List.drop_zero, List.nil_append],
      mem := fun _ _ => rfl }
  obtain ⟨c₄, k₄, e₄, I₄, hk₄, hseg₄⟩ := mergeLoop_inv (P := P) hcmp hJs hB I₃
  rw [kk₃] at hk₄
  obtain ⟨c₅, e₅, n₅, m₅, rr₅, rm₅, o₅⟩ := copyN_char (P := P) I₄.wb 30010 30012
  have hi₄ := I₄.rhi
  have lo₅ : c₅.nreg 30010 = hi := by ram_finish
  have R₅ : ∀ r, r ≠ 30010 → c₅.nreg r = c₄.nreg r := fun r hr => by
    ram_finish
  have sl₅ : SL A₀ c₄ c₅ := ⟨fun r hb _ => by
      have := bandOf_sort hb; exact R₅ r (by omega), rr₅, fun x _ => by rw [m₅], rm₅, o₅⟩
  -- registers of `c₅` outside the merge scratch
  have K₅ : ∀ r, (30000 ≤ r ∧ r < 40000 ∨ r = ALLOC) → r ≠ 30000 → r ≠ 30001 → r ≠ 30002 →
      (r < 30010 ∨ 30016 < r) → r ≠ 30018 → c₅.nreg r = c.nreg r := by
    intro r hr h0 h1 h2 h3 h4
    ram_rw [R₅ r, (ram_app% (I₄.keep r hr h0 h1 h2 ?_ ?_ ?_ ?_ h4)),
      R₃ r]
  -- memory of `c₄`
  have M₄ : ∀ x, (x < dst + lo ∨ dst + hi ≤ x) → c₄.nmem x = c.nmem x := fun x hx => by
    rw [I₄.mem x hx, mm₃]
  have hl : l.length = K := by rw [← h.ml, seg_length]
  refine ⟨c₅, _, (by ram_path), ?_, ?_⟩
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
      wpos := hwp, wK := hwK, lo_K := by rw [lo₅]; omega,
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
          · omega
          · exact ht
        obtain ⟨t, ht⟩ := t0
        rw [show lo + (hi - lo) = hi by omega,
          mpass_take_step hwp ht (by omega) (show mid = min (lo + w) l.length by rw [hl])
            (show hi = min (mid + w) l.length by rw [hl])]
        congr 1
        · rw [← h.out]; apply seg_congr; intro t' ht'
          exact M₄ _ (by omega)
        · rw [mm₃, ← h.ml, seg_drop, seg_take, seg_drop, seg_take]
          congr 1
          · apply seg_arg <;> omega
          · by_cases hc : mid < hi
            · apply seg_arg <;> omega
            · ram_rw [seg_eq_nil, seg_eq_nil],
      mem := fun x hx => by
        ram_rw [m₅, M₄ x]; exact h.mem x hx }
  · rw [lo₅]
    have e1 : K - lo = (K - hi) + (hi - lo) := by omega
    rw [e1, Nat.mul_add]
    have : 1 ≤ hi - lo := by omega
    
    
    nlinarith

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
  rwa [hlK, List.take_of_length_le (by rw [← I'.ml, seg_length])] at this

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

variable {cmp : Stmt} {κ : ℕ} (hcmp : CmpOK P W cmp Bc J le κ)
    (hJs : JStable J A₀) (hB : bSort ∉ Bc)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    {p : ℕ} {c : Config} (h : PassInv W J le Bc A₀ c₀ cC K L p c)
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
  have hpos := Nat.two_pow_pos p
  obtain ⟨c₁, e₁, n₁, m₁, rr₁, rm₁, o₁⟩ := constN_char (P := P) h.wb 30010 0 (by omega)
  have R₁ : ∀ r, r ≠ 30010 → c₁.nreg r = c.nreg r := fun r hr => by
    simp_all
  have sl₁ : SL A₀ c c₁ := ⟨fun r hb _ => by
      have := bandOf_sort hb; exact R₁ r (by omega), rr₁, fun x _ => by rw [m₁], rm₁, o₁⟩
  have I₁ : PairInv W J le Bc A₀ c₀ c₁ (c.nreg 30007) (c.nreg 30008) (2 ^ p) K l c₁ :=
    { wb := e₁.wb_right, hJ := hJs c c₁ h.hJ sl₁.1 sl₁.2.1 sl₁.2.2.1 sl₁.2.2.2.1 sl₁.2.2.2.2,
      loc := h.loc.sl sl₁, rK := (R₁ _ (by omega)).trans hK, one := (R₁ _ (by omega)).trans h.one,
      rsrc := R₁ _ (by omega), rdst := R₁ _ (by omega), rw := (R₁ _ (by omega)).trans hw,
      keep := fun _ _ _ _ _ _ _ => rfl, wpos := hpos, wK := hlt,
      lo_K := by simp_all,
      lo_t := Or.inr ⟨0, by simp_all⟩, arr := h.arr, bW := hbW,
      ml := by rwa [m₁],
      out := by ram_simp [n₁, seg_zero, List.take_zero, mpass_nil],
      mem := fun _ _ => rfl }
  obtain ⟨c₂, k₂, e₂, I₂, hk₂, hlo₂, hseg₂⟩ := pairLoop_inv (P := P) hcmp hJs hB I₁
  have hw₂ := I₂.rw
  obtain ⟨c₃, k₃, e₃, rfl, s₃, d₃, w₃, r₃, m₃, rr₃, rm₃, o₃⟩ := swap_exec (P := P) I₂.wb
    (by rw [hw₂]; omega)
  have sl₃ : SL A₀ c₂ c₃ := ⟨fun r hb _ => by
      have := bandOf_sort hb; exact (ram_app% (r₃ r ?_ ?_ ?_ ?_)), rr₃,
    fun x _ => by rw [m₃], rm₃, o₃⟩
  have K₃ : ∀ r, (30000 ≤ r ∧ r < 40000 ∨ r = ALLOC) → r ≠ 30000 → r ≠ 30001 → r ≠ 30002 →
      (r < 30007 ∨ 30016 < r) → r ≠ 30018 → c₃.nreg r = c.nreg r := by
    ram_post [r₃, I₂.keep, R₁]
  have lo₁ : c₁.nreg 30010 = 0 := by rw [n₁, Machine.upd_same]
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), ?_, by rw [lo₁, Nat.sub_zero] at hk₂; omega⟩
  have harr := h.arr
  have hs₂ := I₂.rsrc
  have hd₂ := I₂.rdst
  exact
  { wb := e₃.wb_right, hJ := hJs c₂ c₃ I₂.hJ sl₃.1 sl₃.2.1 sl₃.2.2.1 sl₃.2.2.2.1 sl₃.2.2.2.2,
    loc := I₂.loc.sl sl₃,
    rK := (K₃ _ (Or.inl (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hK,
    one := (K₃ _ (Or.inl (by omega)) (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans h.one,
    rw := by rw [w₃, hw₂, pow_succ]; omega,
    keep := fun r hr h0 h1 h2 h3 h4 => (K₃ r hr h0 h1 h2 h3 h4).trans (h.keep r hr h0 h1 h2 h3 h4),
    arr := by rw [s₃, d₃, hs₂, hd₂]; omega,
    bW := hbW,
    lst := ⟨mpass le (2 ^ p) l, by rwa [m₃, s₃, hd₂], (mpass_perm _ _).trans hperm,
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
      have hq := (Nat.lt_clog_iff_pow_lt (by norm_num)).2 ht
      ram_rw [h1, h2, Nat.log_pow, Nat.log_pow]
      omega) ⟨p, h⟩
  refine ⟨c', k, e, ⟨p', I'⟩, by ram_rw assumption [h.rw, Nat.log_pow] at hk, ?_⟩
  obtain ⟨l, hl, hperm, hs⟩ := I'.lst
  have hw := I'.rw
  have hK := I'.rK
  rw [hw, hK] at hex
  refine ⟨l, hl, hperm, pairwise_of_chunkSorted hs ?_⟩
  rw [← hl, seg_length]; omega

end

end passes

/-! ## The copy loop -/

section copy
variable {P : Polygon} {W : ℕ}

/-- `copyBody`: `A₀[i] := S[i]`, `i := i + 1`, `ALLOC := ALLOC + 2`, cost `6`. -/
theorem copyBody_exec {c : Config} (hc : WordsBounded W c) (h1 : c.nreg 30003 + c.nreg 30013 ≤ W)
    (h2 : c.nreg 30007 + c.nreg 30013 ≤ W) (h3 : c.nreg 30013 + c.nreg 30006 ≤ W)
    (h4 : c.nreg 9999 + c.nreg 30017 ≤ W) :
    ∃ c' k, Exec P W copyBody c c' k ∧ k = 6 ∧
      c'.nmem = upd c.nmem (c.nreg 30007 + c.nreg 30013) (c.nmem (c.nreg 30003 + c.nreg 30013)) ∧
      c'.nreg 30013 = c.nreg 30013 + c.nreg 30006 ∧ c'.nreg 9999 = c.nreg 9999 + c.nreg 30017 ∧
      (∀ r, r ≠ 30013 → r ≠ 30016 → r ≠ 30018 → r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold copyBody
  exec_block!
  simp_all

/-- `sortInit`: the constants, the arrays `A₀ = ALLOC`, `A₀ + K`, `i := 0`; cost `5`. -/
theorem sortInit_exec {c : Config} (hc : WordsBounded W c) (h1 : 2 ≤ W)
    (h2 : c.nreg 9999 + c.nreg 30004 ≤ W) :
    ∃ c' k, Exec P W sortInit c c' k ∧ k = 5 ∧
      c'.nreg 30006 = 1 ∧ c'.nreg 30017 = 2 ∧ c'.nreg 30007 = c.nreg 9999 ∧
      c'.nreg 30008 = c.nreg 9999 + c.nreg 30004 ∧ c'.nreg 30013 = 0 ∧
      (∀ r, r ≠ 30006 → r ≠ 30017 → r ≠ 30007 → r ≠ 30008 → r ≠ 30013 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sortInit
  exec_block!
  simp_all

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
  obtain ⟨c', k, e, I', hex, hk, hψ⟩ := Exec.whileLtN_growth (P := P) (a := 30013) (b := 30004)
    (CopyInv W J Bc A₀ c₀ S K) (fun d => 8 * (K - d.nreg 30013)) (fun d => d.nreg ALLOC)
    (fun _ h => h.wb) (fun d hd ht => by
      have := hd.iK; have := hd.alloc; have := hd.bS; have := hd.bW
      have hK := hd.rK
      rw [hK] at ht
      obtain ⟨d', k, e, rfl, m', i', a', r', rr', rm', o'⟩ := copyBody_exec (P := P) hd.wb
        (by rw [hd.rS]; omega) (by rw [hd.rsrc]; omega) (by rw [hd.one]; omega)
        (by rw [show (9999 : ℕ) = ALLOC from rfl, hd.alloc, hd.two]; omega)
      have sl : SL A₀ d d' := ⟨fun r hb ha => by
          have := bandOf_sort hb
          exact (ram_app% (r' r ?_ ?_ ?_ ha)), rr',
        fun x hx => by frame_finish, rm', o'⟩
      have hi' : d'.nreg 30013 = d.nreg 30013 + 1 := by rw [i', hd.one]
      refine ⟨d', 6, e, ?_, by rw [hi']; omega, by
        ram_finish [a', hd.two]⟩
      exact
      { wb := e.wb_right, hJ := hJs d d' hd.hJ sl.1 sl.2.1 sl.2.2.1 sl.2.2.2.1 sl.2.2.2.2,
        loc := hd.loc.sl sl,
        rS := (r' _ (by omega) (by omega) (by omega) (by omega)).trans hd.rS,
        rK := (r' _ (by omega) (by omega) (by omega) (by omega)).trans hd.rK,
        one := (r' _ (by omega) (by omega) (by omega) (by omega)).trans hd.one,
        two := (r' _ (by omega) (by omega) (by omega) (by omega)).trans hd.two,
        rsrc := (r' _ (by omega) (by omega) (by omega) (by omega)).trans hd.rsrc,
        rdst := (r' _ (by omega) (by omega) (by omega) (by omega)).trans hd.rdst,
        iK := by rw [hi']; omega,
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
  have h1 : 30 * K ≤ (κ + 30) * K := Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- The cost bound leaves room for the two arrays. -/
theorem sortCost_room (κ K : ℕ) : 2 * K + 2 ≤ sortCost κ K := by
  unfold sortCost
  have h1 : K ≤ K * (Nat.clog 2 K + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have h2 : 30 * (K + 1) ≤ (κ + 30) * (K * (Nat.clog 2 K + 1) + 1) :=
    ram_app% (Nat.mul_le_mul ?_ ?_)
  omega

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
    (by omega) (by rw [hA, hK]; omega)
  have sl₁ : SL A₀ c c₁ := ⟨fun r hb _ => by
      have := bandOf_sort hb; frame_finish,
    rr₁, fun x _ => by rw [m₁], rm₁, out₁⟩
  have C₁ : CopyInv W J Bc A₀ c (c.nreg 30003) K c₁ :=
    { wb := e₁.wb_right, hJ := hJs c c₁ hJ sl₁.1 sl₁.2.1 sl₁.2.2.1 sl₁.2.2.2.1 sl₁.2.2.2.2,
      loc := (Loc.refl Bc A₀ c).sl sl₁,
      rS := (ram_app% (r₁ _ ?_ ?_ ?_ ?_ ?_)),
      rK := (r₁ _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans hK,
      one := o₁, two := t₁, rsrc := s₁, rdst := by rw [d₁, hK, hA],
      iK := by rw [i₁]; omega,
      alloc := by ram_finish,
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
    ram_simp [n₃]
  have sl₃ : SL A₀ c₂ c₃ := ⟨fun r hb _ => by
      have := bandOf_sort hb; exact R₃ r (by omega), rr₃, fun x _ => by rw [m₃], rm₃, out₃⟩
  have P₃ : PassInv W J le Bc A₀ c c₃ K L 0 c₃ :=
    { wb := e₃.wb_right, hJ := hJs c₂ c₃ C₂.hJ sl₃.1 sl₃.2.1 sl₃.2.2.1 sl₃.2.2.2.1 sl₃.2.2.2.2,
      loc := C₂.loc.sl sl₃, rK := (R₃ _ (by omega)).trans C₂.rK,
      one := (R₃ _ (by omega)).trans C₂.one, rw := by ram_finish,
      keep := fun _ _ _ _ _ _ _ => rfl,
      arr := Or.inl ⟨(R₃ _ (by omega)).trans C₂.rsrc, (R₃ _ (by omega)).trans C₂.rdst⟩,
      bW := C₂.bW,
      lst := ⟨L, by
          ram_rw [R₃, C₂.rsrc, m₃]
          have := C₂.cp
          rw [hi₂] at this
          rwa [this],
        List.Perm.refl L, by rw [pow_zero]; exact chunkSorted_one L⟩ }
  -- the passes
  obtain ⟨c₄, k₄, e₄, ⟨p₄, P₄⟩, hk₄, l, hl, hperm, hsorted⟩ :=
    passLoop_inv (P := P) hcmp hJs hB trans total P₃
  rw [Nat.sub_zero] at hk₄
  -- the output
  obtain ⟨c₅, e₅, n₅, m₅, rr₅, rm₅, out₅⟩ := copyN_char (P := P) P₄.wb 30005 30007
  have R₅ : ∀ r, r ≠ 30005 → c₅.nreg r = c₄.nreg r := fun r hr => by
    ram_simp [n₅]
  have o₅ : c₅.nreg 30005 = c₄.nreg 30007 := by rw [n₅, Machine.upd_same]
  have sl₅ : SL A₀ c₄ c₅ := ⟨fun r hb _ => by
      have := bandOf_sort hb; exact R₅ r (by omega), rr₅, fun x _ => by rw [m₅], rm₅, out₅⟩
  have loc₅ := P₄.loc.sl sl₅
  have al₅ : c₅.nreg ALLOC = A₀ + 2 * K := by
    ram_rw assumption [R₅, (ram_app% (P₄.keep ALLOC (Or.inr rfl) ?_ ?_ ?_
      ?_ ?_)), R₃]
  have harr := P₄.arr
  have hk0 := sortCost_ge κ K
  refine ⟨c₅, _, (by ram_path), by omega,
    hJs c₄ c₅ P₄.hJ sl₅.1 sl₅.2.1 sl₅.2.2.1 sl₅.2.2.2.1 sl₅.2.2.2.2, ?_, by rw [o₅]; omega,
    by rw [o₅, al₅]; omega, l, by rwa [o₅, m₅], hperm, hsorted⟩
  refine ⟨fun r hr ha => ?_, fun r hr => ?_, fun a ha => loc₅.2.2.1 a ha,
    fun a _ => by rw [loc₅.2.2.2.1], loc₅.2.2.2.2, by rw [al₅]; omega, ?_⟩
  · rw [Finset.mem_insert, not_or] at hr
    exact loc₅.1 r hr.2 hr.1 ha
  · rw [Finset.mem_insert, not_or] at hr
    exact loc₅.2.1 r hr.2
  · rw [al₅]
    
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
    hw hJ hJs L (by rw [hlen]) hlen.symm (by simp_all)
    (by simp_all)
  refine ⟨c', k, e, by rwa [e4, ← hlen], ⟨by rwa [e5],
    by rwa [e5, e4, ← hlen], ?_, ?_⟩, hfr⟩
  · rwa [e5, e4, e3, ← hlen, h3, hlen]
  · rwa [e5, e4, ← hlen, h3]

end

end SortR

end Chazelle.Core
