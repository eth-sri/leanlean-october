module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Mountain.RamStack

/-!
# The monotone-mountain stack walk on a sub-polygon given by an index table, part 1

This file is the *relocatable* version of `Chazelle.Mountain.mountainStmt` (`RamStack.lean`,
`RamTheorem.lean`): it triangulates a monotone mountain `Q = subPoly P l` whose vertices are
given, in natural memory, by an *index table* `nmem (base + i) = l[i]` (`i < m = l.length`),
and emits the triangles in **original** indices `(l[b], l[c], l[k])`.  The stack of positions
`0 … m - 1` lives in natural memory at a second region `nmem (sbase + t)`, `t < m`.

## Register and memory layout

Inputs (never written):
* `nreg 60 = base` (the index table), `nreg 61 = sbase` (the stack), `nreg 62 = m`.

Written (all in `63 … 74`):
* `nreg 63 = top` (stack height), `nreg 64 = k` (current position), `nreg 65 = 1`,
  `nreg 66 = c` (top entry), `nreg 67 = b` (second entry), `nreg 68 = 2`, `nreg 69` the flag
  of the pop loop, `nreg 70 = 0`, `nreg 71` scratch (addresses), `nreg 72 = l[c]`,
  `nreg 73 = l[b]`, `nreg 74 = l[k]`.
* real registers `61 … 72`: `rreg 61, 62` the coordinates of `vtx l[b]`, `rreg 63, 64` of
  `vtx l[c]`, `rreg 65, 66` of `vtx l[k]`; `rreg 67` the determinant (`rreg 68, 69` scratch);
  `rreg 70 = σ`, `rreg 71 = σ * det`, `rreg 72 = 0`.
* natural memory: only the stack region `sbase … sbase + m - 1`.

The layout hypothesis `SLayout W base sbase m`: the table and the stack regions are disjoint
(`base + m ≤ sbase ∨ sbase + m ≤ base`) and every address fits in a word
(`base + m ≤ W`, `sbase + m ≤ W`).

## The program

```
init:  1; 2; 0; nmem sbase := 0; nmem (sbase+1) := 1; top := 2; k := 2       -- subInitBlock
       read v_{l[m-1]}, v_{l[0]}, v_{l[1]}; D₀ := det; σ := if 0 < D₀ then 1 else -1
while k < m:                                                                  -- subOuterLoop
  flag := 1
  while 0 < flag:                                                             -- subInnerLoop
    if top < 2 then flag := 0
    else c := nmem (sbase+top-1); b := nmem (sbase+top-2);
         l[c], l[b], l[k] from the table; read their coordinates; D := det; t := σ * D
         if 0 < t then (emit (l[b], l[c], l[k]); top := top - 1) else flag := 0
  nmem (sbase + top) := k; top := top + 1; k := k + 1                         -- subPushStmt
```

## Relation to the abstract algorithm

`stackS c = stk (fun i => c.nmem (c.nreg 61 + i)) (c.nreg 63)` is the stack of positions
(top first).  The pop loop mirrors `popLoop (subPoly P l) σ k`, and every emitted triangle
`(b, c, k)` (positions) is emitted as `relabelList l (b, c, k)`.

## Main results

* `subTestStmt_exec`: the corner test, cost `≤ 25`.
* `subInnerLoop_exec`: the pop loop at position `k` from the stack `s` emits
  `(popLoop (subPoly P l) σ k s).1.map (relabelList l)`, leaves the stack
  `(popLoop (subPoly P l) σ k s).2.1`, and costs `≤ 32 * ((popLoop …).1.length + 1) + 2`.
-/

namespace Chazelle.Mountain

open Machine Machine.Stmt Programs
open Chazelle.EarClip (detInto detInto_exec subPoly relabelList vtx_subPoly_getD n_subPoly)

@[expose] public section

/-! ### The stack and the frame -/

/-- The stack of positions held by a configuration: `nmem (sbase + top - 1), …, nmem sbase`
(top first), with `sbase = nreg 61` and `top = nreg 63`. -/
def stackS (c : Config) : List ℕ := stk (fun i => c.nmem (c.nreg 61 + i)) (c.nreg 63)

/-- The stack only depends on `nreg 61`, `nreg 63` and the natural memory. -/
theorem stackS_congr {c c' : Config} (h61 : c'.nreg 61 = c.nreg 61)
    (h63 : c'.nreg 63 = c.nreg 63) (hnm : c'.nmem = c.nmem) : stackS c' = stackS c := by
  unfold stackS; Ξ h61, h63, hnm

/-- **Push into a shifted region**: writing `v` at address `s + t` and taking `t + 1` entries
of the region starting at `s` pushes `v`. -/
theorem stk_shift_push (g : ℕ → ℕ) (s t v : ℕ) :
    stk (fun i => upd g (s + t) v (s + i)) (t + 1) = v :: stk (fun i => g (s + i)) t := by
  have e : (fun i => upd g (s + t) v (s + i)) = upd (fun i => g (s + i)) t v := by
    funext i
    by_cases h : i = t
    · subst h; Ξ Machine.upd_same, Machine.upd_same
    · Ξ Machine.upd_other _ _ _ (⋄), Machine.upd_other _ _ _ h
  Ξ e, stk_push

/-- The layout hypothesis: the index table `base … base + m - 1` and the stack region
`sbase … sbase + m - 1` are disjoint, and every address of either region is `≤ W`. -/
def SLayout (W base sbase m : ℕ) : Prop :=
  (base + m ≤ sbase ∨ sbase + m ≤ base) ∧ base + m ≤ W ∧ sbase + m ≤ W

/-- The index table: `nmem (base + i) = l[i]` for `i < l.length`. -/
def STab (l : List ℕ) (base : ℕ) (c : Config) : Prop :=
  ∀ i, i < l.length → c.nmem (base + i) = l.getD i 0

/-- The constants of the fragment: `nreg 60 = base`, `nreg 61 = sbase`, `nreg 62 = m`,
`nreg 65 = 1`, `nreg 68 = 2`, `nreg 70 = 0`, `rreg 70 = σ`, `rreg 72 = 0`. -/
def SConsts (base sbase m : ℕ) (σ : ℝ) (c : Config) : Prop :=
  c.nreg 60 = base ∧ c.nreg 61 = sbase ∧ c.nreg 62 = m ∧ c.nreg 65 = 1 ∧ c.nreg 68 = 2 ∧
    c.nreg 70 = 0 ∧ c.rreg 70 = σ ∧ c.rreg 72 = 0

/-- **The frame of the fragment**: `c` agrees with `c₀` on every natural register outside
`63 … 74`, every real register outside `61 … 72`, every natural memory cell outside the stack
region `nreg 61 … nreg 61 + nreg 62 - 1` (of `c₀`), and the whole real memory. -/
def SFrame (c₀ c : Config) : Prop :=
  (∀ r, (r < 63 ∨ 74 < r) → c.nreg r = c₀.nreg r) ∧
  (∀ r, (r < 61 ∨ 72 < r) → c.rreg r = c₀.rreg r) ∧
  (∀ a, (a < c₀.nreg 61 ∨ c₀.nreg 61 + c₀.nreg 62 ≤ a) → c.nmem a = c₀.nmem a) ∧
  c.rmem = c₀.rmem

/-- The frame is reflexive. -/
theorem sFrame_refl (c : Config) : SFrame c c :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

/-- The frame is transitive. -/
theorem sFrame_trans {c₀ c₁ c₂ : Config} (h₁ : SFrame c₀ c₁) (h₂ : SFrame c₁ c₂) :
    SFrame c₀ c₂ := by
  obtain ⟨n₁, r₁, m₁, q₁⟩ := h₁
  obtain ⟨n₂, r₂, m₂, q₂⟩ := h₂
  have e61 : c₁.nreg 61 = c₀.nreg 61 := n₁ 61 (by omega)
  have e62 : c₁.nreg 62 = c₀.nreg 62 := n₁ 62 (by omega)
  refine ⟨fun r hr => by rw [n₂ r hr, n₁ r hr], fun r hr => by rw [r₂ r hr, r₁ r hr],
    fun a ha => ?_, by rw [q₂, q₁]⟩
  rw [m₂ a (by rw [e61, e62]; exact ha), m₁ a ha]

/-- A step that changes nothing but the natural registers `63 … 74`, the real registers
`61 … 72` and the output keeps the frame. -/
theorem sFrame_of_regs {c c' : Config} (hn : ∀ r, (r < 63 ∨ 74 < r) → c'.nreg r = c.nreg r)
    (hr : ∀ r, (r < 61 ∨ 72 < r) → c'.rreg r = c.rreg r) (hnm : c'.nmem = c.nmem)
    (hrm : c'.rmem = c.rmem) : SFrame c c' :=
  ⟨hn, hr, fun a _ => by rw [hnm], hrm⟩

/-! ### The program -/

/-- The corner test, reading: the positions `c := nmem (sbase + top - 1)`,
`b := nmem (sbase + top - 2)`, the original indices `l[c]`, `l[b]`, `l[k]` from the table, then
the coordinates of `vtx l[b]`, `vtx l[c]`, `vtx l[k]` into `rreg 61 … rreg 66`.
Exactly `17` instructions. -/
def subReadStmt : Stmt :=
  block [.addN 71 61 63, .subN 71 71 65, .loadN 66 71, .subN 71 71 65, .loadN 67 71,
    .addN 72 60 66, .loadN 72 72, .addN 73 60 67, .loadN 73 73, .addN 74 60 64, .loadN 74 74,
    .readX 61 73, .readY 62 73, .readX 63 72, .readY 64 72, .readX 65 74, .readY 66 74]

/-- The corner test: `subReadStmt`, `rreg 67 := det (vtx l[b]) (vtx l[c]) (vtx l[k])`,
`rreg 71 := rreg 70 * rreg 67`.  Exactly `25` instructions. -/
def subTestStmt : Stmt :=
  .seq subReadStmt (.seq (detInto 67 68 69 61 62 63 64 65 66) (.instr (.mulR 71 70 67)))

/-- A pop: `emit (l[b], l[c], l[k]); top := top - 1`. -/
def subPopStmt : Stmt := block [.emit 73 72 74, .subN 63 63 65]

/-- The body of the pop loop: `if top < 2 then flag := 0 else (test; if 0 < σ * D then pop
else flag := 0)`. -/
def subInnerBody : Stmt :=
  .ifLtN 63 68 (.instr (.constN 69 0))
    (.seq subTestStmt (.ifLtR 72 71 subPopStmt (.instr (.constN 69 0))))

/-- **The pop loop**: `while 0 < flag do subInnerBody`. -/
def subInnerLoop : Stmt := .whileLtN 70 69 subInnerBody

/-- The push: `nmem (sbase + top) := k; top := top + 1; k := k + 1`.  Exactly `4`
instructions. -/
def subPushStmt : Stmt := block [.addN 71 61 63, .storeN 71 64, .addN 63 63 65, .addN 64 64 65]

/-- The body of the walk: `flag := 1; subInnerLoop; subPushStmt`. -/
def subOuterBody : Stmt := .seq (.instr (.constN 69 1)) (.seq subInnerLoop subPushStmt)

/-- **The walk**: `while k < m do subOuterBody`. -/
def subOuterLoop : Stmt := .whileLtN 64 62 subOuterBody

/-- The initialisation: the constants `1, 2, 0`, the stack `[1, 0]` (`nmem sbase := 0`,
`nmem (sbase + 1) := 1`, `top := 2`), `k := 2`, the original indices `l[m-1], l[0], l[1]`
(into `nreg 72, 73, 74`) and their coordinates into `rreg 61 … rreg 66`, `rreg 72 := 0`.
Exactly `21` instructions. -/
def subInitBlock : Stmt :=
  block [.constN 65 1, .constN 68 2, .constN 70 0, .storeN 61 70, .addN 71 61 65, .storeN 71 65,
    .copyN 63 68, .copyN 64 68, .addN 72 60 62, .subN 72 72 65, .loadN 72 72, .loadN 73 60,
    .addN 74 60 65, .loadN 74 74, .readX 61 72, .readY 62 72, .readX 63 73, .readY 64 73,
    .readX 65 74, .readY 66 74, .constR 72 0]

/-- The sign: `rreg 67 := D₀ = det v_{l[m-1]} v_{l[0]} v_{l[1]};
rreg 70 := if 0 < D₀ then 1 else -1`. -/
def subSignStmt : Stmt :=
  .seq (detInto 67 68 69 61 62 63 64 65 66)
    (.ifLtR 72 67 (.instr (.constR 70 1)) (.instr (.constR 70 (-1))))

/-- **The monotone-mountain triangulator for a sub-polygon given by an index table.** -/
def mountainSubStmt : Stmt := .seq subInitBlock (.seq subSignStmt subOuterLoop)

/-! ### The corner test -/

section specs
variable {P : Polygon} {W : ℕ}

set_option linter.unusedSimpArgs false in
/-- **Spec lemma for `subTestStmt`.**  With `nreg 65 = 1` and the four addresses in range:
cost `≤ 25`; `nreg 72 = l[c]`, `nreg 73 = l[b]`, `nreg 74 = l[k]` read through the table at
`nreg 60` from the positions `c = nmem (sbase + top - 1)`, `b = nmem (sbase + top - 1 - 1)`;
`rreg 71 = rreg 70 * det (vtx l[b]) (vtx l[c]) (vtx l[k])`; natural registers other than
`66, 67, 71, 72, 73, 74`, real registers outside `61 … 69` other than `71`, both memories and
the output are unchanged. -/
theorem subTestStmt_exec (c : Config) (hc : WordsBounded W c) (h65 : c.nreg 65 = 1)
    (hs : c.nreg 61 + c.nreg 63 ≤ W)
    (hcb : c.nreg 60 + c.nmem (c.nreg 61 + c.nreg 63 - 1) ≤ W)
    (hbb : c.nreg 60 + c.nmem (c.nreg 61 + c.nreg 63 - 1 - 1) ≤ W)
    (hkb : c.nreg 60 + c.nreg 64 ≤ W) :
    ∃ c' k, Exec P W subTestStmt c c' k ∧ k ≤ 25 ∧
      c'.nreg 72 = c.nmem (c.nreg 60 + c.nmem (c.nreg 61 + c.nreg 63 - 1)) ∧
      c'.nreg 73 = c.nmem (c.nreg 60 + c.nmem (c.nreg 61 + c.nreg 63 - 1 - 1)) ∧
      c'.nreg 74 = c.nmem (c.nreg 60 + c.nreg 64) ∧
      c'.rreg 71 = c.rreg 70 *
        det (P.vtx (c.nmem (c.nreg 60 + c.nmem (c.nreg 61 + c.nreg 63 - 1 - 1))))
          (P.vtx (c.nmem (c.nreg 60 + c.nmem (c.nreg 61 + c.nreg 63 - 1))))
          (P.vtx (c.nmem (c.nreg 60 + c.nreg 64))) ∧
      (∀ r, r ≠ 66 → r ≠ 67 → r ≠ 71 → r ≠ 72 → r ≠ 73 → r ≠ 74 → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 61 ∨ 69 < r) → r ≠ 71 → c'.rreg r = c.rreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold subTestStmt subReadStmt
  refine spec_seq ?_
  exec_block
  · exact hs
  · config_simp; rw [h65]; exact hcb
  · config_simp; rw [h65]; exact hbb
  · config_simp; exact hkb
  refine spec_seq (spec_use (detInto_exec (P := P) 67 68 69 61 62 63 64 65 66 (⌖)
    (⌖) (⌖)
    (fun r hr => by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) _ ‹_›) ?_)
  rintro c₁ k₁ hk₁ hw₁ ⟨hdet, hfr, hn, hnm, hrm, hout⟩
  refine spec_instr (Exec.mulR hw₁ 71 70 67) fun hw₂ => ?_
  config_simp at hdet
  have e70 : c₁.rreg 70 = c.rreg 70 := by
    rw [hfr 70 (⌖) (⌖) (⌖)]; config_simp
  refine ⟨⋄, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · config_simp; rw [hn]; config_simp; Ξ h65
  · config_simp; rw [hn]; config_simp; Ξ h65
  · config_simp; rw [hn]; config_simp
  · config_simp; Ξ hdet, e70, h65
  · intro r h66 h67 h71 h72 h73 h74
    config_simp; rw [hn]; Θ h66, h67, h71, h72, h73, h74
  · intro r hr h71
    config_simp
    Ξ Machine.upd_other _ _ _ h71, hfr r (⋄) (⋄) (⋄)
    simp [show r ≠ 61 by omega, show r ≠ 62 by omega, show r ≠ 63 by omega,
      show r ≠ 64 by omega, show r ≠ 65 by omega, show r ≠ 66 by omega]
  · config_simp; Ξ hnm
  · config_simp; Ξ hrm
  · config_simp; Ξ hout

end specs

/-! ### The pop loop -/

/-- The potential of the pop loop at position `k`: `0` once the flag is `0`, otherwise
`32 * (p + 1)` with `p` the number of pops still to come. -/
noncomputable def subInnerPot (P : Polygon) (l : List ℕ) (σ : ℝ) (k : ℕ) (c : Config) : ℕ :=
  if c.nreg 69 = 0 then 0 else 32 * ((popLoop (subPoly P l) σ k (stackS c)).1.length + 1)

/-- **The invariant of the pop loop** at position `k`, relative to the configuration `c₀` at
the start of the loop, with target output `oF` and target stack `sF`: the word bound, the
constants, the index table, the frame, `nreg 64 = k`, `top ≤ k`, stack entries `< m`, and
either the flag is `1`, the output followed by the (relabelled) triangles still to be emitted by
`popLoop (subPoly P l) σ k (stackS c)` is `oF`, and that call ends with the stack `sF`; or the
flag is `0`, the output is `oF` and the stack is `sF`. -/
def SInnerInv (P : Polygon) (W : ℕ) (l : List ℕ) (base sbase : ℕ) (σ : ℝ) (k : ℕ)
    (c₀ : Config) (oF : List Polygon.Triangle) (sF : List ℕ) (c : Config) : Prop :=
  WordsBounded W c ∧ SConsts base sbase l.length σ c ∧ STab l base c ∧ SFrame c₀ c ∧
    c.nreg 64 = k ∧ c.nreg 63 ≤ k ∧ (∀ x ∈ stackS c, x < l.length) ∧
    ((c.nreg 69 = 1 ∧
        c.output ++ (popLoop (subPoly P l) σ k (stackS c)).1.map (relabelList l) = oF ∧
        (popLoop (subPoly P l) σ k (stackS c)).2.1 = sF) ∨
      (c.nreg 69 = 0 ∧ c.output = oF ∧ stackS c = sF))

section inner
variable {P : Polygon} {W : ℕ} {l : List ℕ} {base sbase : ℕ}

/-- **A pop re-establishes the invariant** and decreases the potential by `32`.  `c` is the
configuration at the start of the iteration (flag `1`, `2 ≤ top`, a convex corner of
`subPoly P l`), `c'` the one after the pop, described by the equations `e…`. -/
theorem sInnerInv_pop {σ : ℝ} {k : ℕ} {c₀ : Config} {oF : List Polygon.Triangle}
    {sF : List ℕ} {c c' : Config} (hw' : WordsBounded W c')
    (hC' : SConsts base sbase l.length σ c') (hT' : STab l base c') (hF' : SFrame c₀ c')
    (h64 : c.nreg 64 = k) (htop : c.nreg 63 ≤ k) (hge : 2 ≤ c.nreg 63) (hf : c.nreg 69 = 1)
    (hlt : ∀ x ∈ stackS c, x < l.length)
    (hconv : 0 < σ * det ((subPoly P l).vtx (c.nmem (c.nreg 61 + (c.nreg 63 - 2))))
      ((subPoly P l).vtx (c.nmem (c.nreg 61 + (c.nreg 63 - 1)))) ((subPoly P l).vtx k))
    (hout : c.output ++ (popLoop (subPoly P l) σ k (stackS c)).1.map (relabelList l) = oF)
    (hst : (popLoop (subPoly P l) σ k (stackS c)).2.1 = sF)
    (e61 : c'.nreg 61 = c.nreg 61) (e63 : c'.nreg 63 = c.nreg 63 - 1)
    (e64 : c'.nreg 64 = c.nreg 64) (e69 : c'.nreg 69 = 1) (enm : c'.nmem = c.nmem)
    (eout : c'.output = c.output ++ [relabelList l (c.nmem (c.nreg 61 + (c.nreg 63 - 2)),
      c.nmem (c.nreg 61 + (c.nreg 63 - 1)), k)]) :
    SInnerInv P W l base sbase σ k c₀ oF sF c' ∧
      subInnerPot P l σ k c' + 32 ≤ subInnerPot P l σ k c := by
  have hs : stackS c = c.nmem (c.nreg 61 + (c.nreg 63 - 1)) ::
      c.nmem (c.nreg 61 + (c.nreg 63 - 2)) :: stk (fun i => c.nmem (c.nreg 61 + i))
        (c.nreg 63 - 2) := stk_two hge
  have hs' : stackS c' = c.nmem (c.nreg 61 + (c.nreg 63 - 2)) ::
      stk (fun i => c.nmem (c.nreg 61 + i)) (c.nreg 63 - 2) := by
    unfold stackS
    rw [e61, e63, enm, stk_pop (f := fun i => c.nmem (c.nreg 61 + i)) (t := c.nreg 63 - 1)
      (⋄), show c.nreg 63 - 1 - 1 = c.nreg 63 - 2 by omega]
  have hpl : popLoop (subPoly P l) σ k (stackS c) =
      ((c.nmem (c.nreg 61 + (c.nreg 63 - 2)), c.nmem (c.nreg 61 + (c.nreg 63 - 1)), k) ::
          (popLoop (subPoly P l) σ k (stackS c')).1,
        (popLoop (subPoly P l) σ k (stackS c')).2.1,
        (popLoop (subPoly P l) σ k (stackS c')).2.2 + 1) := by
    Ξ hs, hs', popLoop_cons_cons, ite_eq_left hconv
  refine ⟨⟨hw', hC', hT', hF', by rw [e64, h64], ⋄, ?_, Or.inl ⟨e69, ?_, ?_⟩⟩, ?_⟩
  · intro x hx
    rw [hs'] at hx
    exact hlt x (by rw [hs]; exact List.mem_cons_of_mem _ hx)
  · Ξ eout, List.append_assoc, List.singleton_append, ← hout, hpl, List.map_cons
  · Ξ ← hst, hpl
  · unfold subInnerPot
    rw [ite_eq_right (⋄), ite_eq_right (by omega), hpl, List.length_cons]
    omega

/-- **Stopping re-establishes the invariant** (flag `0`) when the pop loop emits nothing more
and keeps the stack. -/
theorem sInnerInv_stop {σ : ℝ} {k : ℕ} {c₀ : Config} {oF : List Polygon.Triangle}
    {sF : List ℕ} {c c' : Config} (hw' : WordsBounded W c')
    (hC' : SConsts base sbase l.length σ c') (hT' : STab l base c') (hF' : SFrame c₀ c')
    (h64 : c.nreg 64 = k) (htop : c.nreg 63 ≤ k) (hlt : ∀ x ∈ stackS c, x < l.length)
    (hpl : (popLoop (subPoly P l) σ k (stackS c)).1 = [])
    (hpl2 : (popLoop (subPoly P l) σ k (stackS c)).2.1 = stackS c)
    (hout : c.output ++ (popLoop (subPoly P l) σ k (stackS c)).1.map (relabelList l) = oF)
    (hst : (popLoop (subPoly P l) σ k (stackS c)).2.1 = sF)
    (e61 : c'.nreg 61 = c.nreg 61) (e63 : c'.nreg 63 = c.nreg 63)
    (e64 : c'.nreg 64 = c.nreg 64) (e69 : c'.nreg 69 = 0) (enm : c'.nmem = c.nmem)
    (eout : c'.output = c.output) :
    SInnerInv P W l base sbase σ k c₀ oF sF c' ∧ subInnerPot P l σ k c' = 0 := by
  have hs' : stackS c' = stackS c := stackS_congr e61 e63 enm
  refine ⟨⟨hw', hC', hT', hF', by rw [e64, h64], ⋄, by rw [hs']; exact hlt,
    Or.inr ⟨e69, ?_, ?_⟩⟩, ?_⟩
  · Ξ eout, ← hout, hpl, List.map_nil, List.append_nil
  · Ξ hs', ← hst, hpl2
  · unfold subInnerPot; rw [ite_eq_left e69]


/-- **One iteration of the pop loop** preserves `SInnerInv` and decreases the potential
`subInnerPot` by at least its cost plus `2`. -/
theorem subInnerBody_inv (hL : SLayout W base sbase l.length) {σ : ℝ} {k : ℕ}
    (hk : k < l.length) {c₀ : Config} {oF : List Polygon.Triangle} {sF : List ℕ}
    (c : Config) (hI : SInnerInv P W l base sbase σ k c₀ oF sF c)
    (ht : c.nreg 70 < c.nreg 69) :
    ∃ c' k', Exec P W subInnerBody c c' k' ∧ SInnerInv P W l base sbase σ k c₀ oF sF c' ∧
      subInnerPot P l σ k c' + k' + 2 ≤ subInnerPot P l σ k c := by
  obtain ⟨-, hWb, hWs⟩ := hL
  obtain ⟨hw, hC, hT, hF, h64, htop, hlt, hflag⟩ := hI
  obtain ⟨h60, h61, h62, h65, h68, h70, hr70, hr72⟩ := hC
  obtain ⟨hf, hout, hst⟩ : c.nreg 69 = 1 ∧
      c.output ++ (popLoop (subPoly P l) σ k (stackS c)).1.map (relabelList l) = oF ∧
      (popLoop (subPoly P l) σ k (stackS c)).2.1 = sF := by
    rcases hflag with h | h
    · exact h
    · omega
  have hpot : subInnerPot P l σ k c =
      32 * ((popLoop (subPoly P l) σ k (stackS c)).1.length + 1) := by
    unfold subInnerPot; rw [ite_eq_right (by omega)]
  unfold subInnerBody
  by_cases hlt2 : c.nreg 63 < 2
  · -- fewer than two entries: stop
    have hpl : popLoop (subPoly P l) σ k (stackS c) = ([], stackS c, 0) := by
      unfold stackS
      obtain h | h : c.nreg 63 = 0 ∨ c.nreg 63 = 1 := by omega
      · rw [h]; exact popLoop_nil _ σ k
      · rw [h]; exact popLoop_singleton _ σ k _
    refine spec_ifLtN_true (by rw [h68]; exact hlt2)
      (spec_instr (Exec.constN hw 69 0 (Nat.zero_le _)) fun hw' => ?_)
    obtain ⟨hI', hp'⟩ := sInnerInv_stop (P := P) (W := W) (c₀ := c₀) hw'
      ⟨by config_simp; exact h60, by config_simp; exact h61, by config_simp; exact h62,
        by config_simp; exact h65, by config_simp; exact h68, by config_simp; exact h70,
        by config_simp; exact hr70, by config_simp; exact hr72⟩
      hT (sFrame_trans hF (sFrame_of_regs
        (fun r hr => by config_simp; exact Machine.upd_other _ _ _ (by omega))
        (fun r _ => rfl) rfl rfl))
      h64 htop hlt (by rw [hpl]) (by rw [hpl]) hout hst (by config_simp) (by config_simp)
      (by config_simp) (by config_simp) rfl rfl
    refine ⟨hI', ?_⟩
    rw [hp', hpot, hpl]
    simp
  · have hge : 2 ≤ c.nreg 63 := by omega
    have hs : stackS c = c.nmem (c.nreg 61 + (c.nreg 63 - 1)) ::
        c.nmem (c.nreg 61 + (c.nreg 63 - 2)) :: stk (fun i => c.nmem (c.nreg 61 + i))
          (c.nreg 63 - 2) := stk_two hge
    have hcm : c.nmem (c.nreg 61 + (c.nreg 63 - 1)) < l.length :=
      hlt _ (by rw [hs]; exact List.mem_cons_self)
    have hbm : c.nmem (c.nreg 61 + (c.nreg 63 - 2)) < l.length :=
      hlt _ (by rw [hs]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have ea1 : c.nreg 61 + c.nreg 63 - 1 = c.nreg 61 + (c.nreg 63 - 1) := by omega
    have ea2 : c.nreg 61 + c.nreg 63 - 1 - 1 = c.nreg 61 + (c.nreg 63 - 2) := by omega
    refine spec_ifLtN_false (by rw [h68]; exact hlt2) ?_
    refine spec_seq (spec_use (subTestStmt_exec (P := P) c hw h65 (by rw [h61]; omega)
      (by rw [ea1, h60]; omega) (by rw [ea2, h60]; omega) (by rw [h60, h64]; omega)) ?_)
    rintro c₁ k₁ hk₁ hw₁ ⟨e72, e73, e74, e71, efr, erf, enm, erm, eout⟩
    rw [ea2, h60, hT _ hbm] at e73
    rw [ea1, h60, hT _ hcm] at e72
    rw [h60, h64, hT _ hk] at e74
    rw [ea2, ea1, h60, hT _ hbm, hT _ hcm, h64, hT _ hk] at e71
    have n60 : c₁.nreg 60 = c.nreg 60 :=
      efr 60 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have n61 : c₁.nreg 61 = c.nreg 61 :=
      efr 61 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have n62 : c₁.nreg 62 = c.nreg 62 :=
      efr 62 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have n63 : c₁.nreg 63 = c.nreg 63 :=
      efr 63 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have n64 : c₁.nreg 64 = c.nreg 64 :=
      efr 64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have n65 : c₁.nreg 65 = c.nreg 65 :=
      efr 65 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have n68 : c₁.nreg 68 = c.nreg 68 :=
      efr 68 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have n69 : c₁.nreg 69 = c.nreg 69 :=
      efr 69 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have n70 : c₁.nreg 70 = c.nreg 70 :=
      efr 70 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have r70 : c₁.rreg 70 = c.rreg 70 := erf 70 (by omega) (by decide)
    have r72 : c₁.rreg 72 = c.rreg 72 := erf 72 (by omega) (by decide)
    have hF₁ := sFrame_of_regs
      (fun r hr => efr r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
      (fun r hr => erf r (by omega) (by omega)) enm erm
    by_cases hconv : 0 < σ * det ((subPoly P l).vtx (c.nmem (c.nreg 61 + (c.nreg 63 - 2))))
        ((subPoly P l).vtx (c.nmem (c.nreg 61 + (c.nreg 63 - 1)))) ((subPoly P l).vtx k)
    · -- a convex corner: pop
      have hconv' := hconv
      rw [vtx_subPoly_getD P l hbm, vtx_subPoly_getD P l hcm, vtx_subPoly_getD P l hk]
        at hconv'
      refine spec_ifLtR_true (by rw [e71, r72, hr70, hr72]; exact hconv') ?_
      unfold subPopStmt
      exec_block
      obtain ⟨hI', hp'⟩ := sInnerInv_pop (P := P) (W := W) (c₀ := c₀) ‹WordsBounded _ _›
        ⟨by config_simp; rw [n60, h60], by config_simp; rw [n61, h61],
          by config_simp; rw [n62, h62], by config_simp; rw [n65, h65],
          by config_simp; rw [n68, h68], by config_simp; rw [n70, h70],
          by config_simp; rw [r70, hr70], by config_simp; rw [r72, hr72]⟩
        (fun i hi => by config_simp; rw [enm]; exact hT i hi)
        (sFrame_trans hF (sFrame_trans hF₁ (sFrame_of_regs
          (fun r hr => by config_simp; exact Machine.upd_other _ _ _ (by omega))
          (fun r _ => by config_simp) (by config_simp) (by config_simp))))
        h64 htop hge hf hlt hconv hout hst (by config_simp; rw [n61])
        (by config_simp; rw [n63, n65, h65]) (by config_simp; rw [n64])
        (by config_simp; rw [n69, hf]) (by config_simp; rw [enm])
        (by config_simp; rw [eout, e73, e72, e74]; rfl)
      exact ⟨hI', by omega⟩
    · -- not convex: stop
      have hconv' := hconv
      rw [vtx_subPoly_getD P l hbm, vtx_subPoly_getD P l hcm, vtx_subPoly_getD P l hk]
        at hconv'
      refine spec_ifLtR_false (by rw [e71, r72, hr70, hr72]; exact hconv')
        (spec_instr (Exec.constN hw₁ 69 0 (Nat.zero_le _)) fun hw' => ?_)
      have hpl : popLoop (subPoly P l) σ k (stackS c) = ([], stackS c, 1) := by
        rw [hs, popLoop_cons_cons, ite_eq_right hconv]
      obtain ⟨hI', hp'⟩ := sInnerInv_stop (P := P) (W := W) (c₀ := c₀) hw'
        ⟨by config_simp; rw [n60, h60], by config_simp; rw [n61, h61],
          by config_simp; rw [n62, h62], by config_simp; rw [n65, h65],
          by config_simp; rw [n68, h68], by config_simp; rw [n70, h70],
          by config_simp; rw [r70, hr70], by config_simp; rw [r72, hr72]⟩
        (fun i hi => by config_simp; rw [enm]; exact hT i hi)
        (sFrame_trans hF (sFrame_trans hF₁ (sFrame_of_regs
          (fun r hr => by config_simp; exact Machine.upd_other _ _ _ (by omega))
          (fun r _ => rfl) rfl rfl)))
        h64 htop hlt (by rw [hpl]) (by rw [hpl]) hout hst (by config_simp; rw [n61])
        (by config_simp; rw [n63]) (by config_simp; rw [n64]) (by config_simp)
        (by config_simp; rw [enm]) (by config_simp; rw [eout])
      refine ⟨hI', ?_⟩
      rw [hp', hpot, hpl]
      simp only [List.length_nil]
      omega

/-- **Spec lemma for the pop loop.**  From a configuration with the constants, the index table,
`nreg 64 = k < m`, `top ≤ k`, stack entries `< m` and flag `1`, the pop loop emits
`(popLoop (subPoly P l) σ k s).1.map (relabelList l)` (`s = stackS c`), leaves the stack
`(popLoop (subPoly P l) σ k s).2.1`, keeps the constants, the table, the frame, `nreg 64 = k`,
`top ≤ k` and the bound on the entries, and costs `≤ 32 * ((popLoop … s).1.length + 1) + 2`. -/
theorem subInnerLoop_exec (hL : SLayout W base sbase l.length) {σ : ℝ} {k : ℕ}
    (hk : k < l.length) (c : Config) (hw : WordsBounded W c)
    (hC : SConsts base sbase l.length σ c) (hT : STab l base c) (h64 : c.nreg 64 = k)
    (htop : c.nreg 63 ≤ k) (hlt : ∀ x ∈ stackS c, x < l.length) (hf : c.nreg 69 = 1) :
    ∃ c' k', Exec P W subInnerLoop c c' k' ∧
      k' ≤ 32 * ((popLoop (subPoly P l) σ k (stackS c)).1.length + 1) + 2 ∧
      SConsts base sbase l.length σ c' ∧ STab l base c' ∧ SFrame c c' ∧ c'.nreg 64 = k ∧
      c'.nreg 63 ≤ k ∧ (∀ x ∈ stackS c', x < l.length) ∧
      c'.output = c.output ++ (popLoop (subPoly P l) σ k (stackS c)).1.map (relabelList l) ∧
      stackS c' = (popLoop (subPoly P l) σ k (stackS c)).2.1 := by
  have hI : SInnerInv P W l base sbase σ k c
      (c.output ++ (popLoop (subPoly P l) σ k (stackS c)).1.map (relabelList l))
      (popLoop (subPoly P l) σ k (stackS c)).2.1 c :=
    ⟨hw, hC, hT, sFrame_refl c, h64, htop, hlt, Or.inl ⟨hf, rfl, rfl⟩⟩
  obtain ⟨c', k', ex, hI', hexit, hk'⟩ := Exec.whileLtN_potential
    (SInnerInv P W l base sbase σ k c
      (c.output ++ (popLoop (subPoly P l) σ k (stackS c)).1.map (relabelList l))
      (popLoop (subPoly P l) σ k (stackS c)).2.1)
    (subInnerPot P l σ k) (fun _ h => h.1) (fun d hd ht => subInnerBody_inv hL hk d hd ht) hI
  obtain ⟨-, hC', hT', hF', h64', htop', hlt', hflag'⟩ := hI'
  have hpot : subInnerPot P l σ k c =
      32 * ((popLoop (subPoly P l) σ k (stackS c)).1.length + 1) := by
    unfold subInnerPot; Ξ ite_eq_right (⋄)
  rcases hflag' with ⟨hf', -, -⟩ | ⟨-, hout', hst'⟩
  · exfalso; apply hexit; rw [hf', hC'.2.2.2.2.2.1]; omega
  · exact ⟨c', k', ex, by rw [← hpot]; exact hk', hC', hT', hF', h64', htop', hlt', hout', hst'⟩

end inner

end

end Chazelle.Mountain
