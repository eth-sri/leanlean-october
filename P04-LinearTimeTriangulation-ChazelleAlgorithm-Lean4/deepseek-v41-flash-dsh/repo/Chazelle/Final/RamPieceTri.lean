module

public import Chazelle.Golf

public import Chazelle.Final.PieceTri
public import Chazelle.Mountain.RamSubTheorem

/-!
# Triangulating one piece on the RAM

`pieceTriStmt` triangulates one piece of the subdivision, handed over as a **cyclic linked
list**, in time linear in its size `m`, by reorienting it into a monotone mountain listed in
increasing `ylexLT` order (`Chazelle.Final.PieceTri`) and running the verified relocatable
stack walk `Chazelle.Mountain.mountainSubStmt`.

## Input representation (fixed here; produced by the piece-splitting stage)

Natural registers (never written):
* `nreg 80 = NB`: base of the successor array, `nxt[x] = nmem (NB + x)`;
* `nreg 81 = VB`: base of the vertex array, `vtx[x] = nmem (VB + x)` (a vertex index of `P`);
* `nreg 82 = s`: a node of the piece;
* `nreg 83 = m`: the number of vertices of the piece;
* `nreg 84 = WB`: base of a work band of `4 m` cells `WB … WB + 4m - 1`.

The piece is the list `l` (`l.length = m`) with `l[i] = vtx[nxt^i s]` and `nxt^m s = s`
(`PieceInput`); the node cells `NB + nxt^i s`, `VB + nxt^i s` (`i < m`) lie outside the work
band, and every address used is `≤ W`.

## The program (`pieceTriStmt`)

```
walk:  node := s; p := WB
       while p < WB + 2m: nmem p := vtx[node]; node := nxt[node]; p := p + 1
       -- D[i] = nmem (WB + i) = l[i % m], i < 2m (the list, written twice)
min:   mp := WB; q := WB + 1
       while q < WB + m: if ylexLT (vtx D[q]) (vtx D[mp]) then mp := q;  q := q + 1
       -- i0 = mp - WB is a ylexLT-minimal position (IsMinPos)
dir:   if ylexLT (vtx D[i0 + 1]) (vtx D[i0 + m - 1])        -- DirFwd
       then a := mp, inc := 1, dec := 0 else a := mp + m, inc := 0, dec := 1
copy:  b := WB + 2m
       while b < WB + 3m: nmem b := nmem a; a := a + inc - dec; b := b + 1
       -- nmem (WB + 2m + j) = (reorient P l i0)[j], j < m
frag:  nreg 60 := WB + 2m; nreg 61 := WB + 3m; nreg 62 := m; mountainSubStmt
```

Registers written: natural `60 … 74` (the fragment uses `63 … 74`) and `85 … 94`; real
`61 … 72` (fragment) and `80 … 83`.  Memory written: only the work band.

## Costs

walk `≤ 16 m + 7`, min `≤ 16 m + 5`, dir `≤ 18`, copy `≤ 7 m + 5`, setup `4`, fragment
`≤ 73 m`: total `≤ 112 m + 39` (`pieceTri_exec`).

## Main results

* `pieceTri_exec`: on a piece that is a rotated (possibly reversed) monotone mountain, the
  program appends `T.map (relabelList l)` to the output for a weak triangulation `T` of
  `subPoly P l`, at cost `≤ 112 m + 39`, with the frame above.
* `pieceTri_exec_of_isPiece`: the same for an `IsPiece P l` of a simple polygon.
-/

namespace Chazelle.Final

open Machine Machine.Stmt Programs
open Chazelle.Mountain
open Chazelle.EarClip (subPoly relabelList n_subPoly)
open Chazelle.Existence (WeakTriangulates)

@[expose] public section

/-! ### The input -/

/-- The `i`-th node of the cyclic linked list with successor array at `NB` in memory `mem`,
starting from `s`. -/
def nodeSeq (mem : ℕ → ℕ) (NB s i : ℕ) : ℕ := (fun x => mem (NB + x))^[i] s

theorem nodeSeq_zero (mem : ℕ → ℕ) (NB s : ℕ) : nodeSeq mem NB s 0 = s := rfl

theorem nodeSeq_succ (mem : ℕ → ℕ) (NB s i : ℕ) :
    nodeSeq mem NB s (i + 1) = mem (NB + nodeSeq mem NB s i) :=
  Function.iterate_succ_apply' _ _ _

/-- A cyclic list of period `m` can be read modulo `m`. -/
theorem nodeSeq_mod {mem : ℕ → ℕ} {NB s m : ℕ} (h : nodeSeq mem NB s m = s) (i : ℕ) :
    nodeSeq mem NB s i = nodeSeq mem NB s (i % m) := by
  unfold nodeSeq at *
  conv_lhs => rw [← Nat.mod_add_div i m]
  Ξ Function.iterate_add_apply, Function.iterate_mul, Function.iterate_fixed h

/-- **The input of the piece triangulator** in the configuration `c`: the piece `l` is the
cyclic linked list at `nreg 80` (successors), `nreg 81` (vertex indices) from the node
`nreg 82`, of length `nreg 83 = l.length`; its node cells lie outside the work band
`[nreg 84, nreg 84 + 4 m)`, and all addresses used are `≤ W`. -/
structure PieceInput (W : ℕ) (l : List ℕ) (c : Config) : Prop where
  len : c.nreg 83 = l.length
  cyc : nodeSeq c.nmem (c.nreg 80) (c.nreg 82) l.length = c.nreg 82
  vtx : ∀ i, i < l.length →
    c.nmem (c.nreg 81 + nodeSeq c.nmem (c.nreg 80) (c.nreg 82) i) = l.getD i 0
  nxtW : ∀ i, i < l.length → c.nreg 80 + nodeSeq c.nmem (c.nreg 80) (c.nreg 82) i ≤ W
  vtxW : ∀ i, i < l.length → c.nreg 81 + nodeSeq c.nmem (c.nreg 80) (c.nreg 82) i ≤ W
  nxtOut : ∀ i, i < l.length →
    c.nreg 80 + nodeSeq c.nmem (c.nreg 80) (c.nreg 82) i < c.nreg 84 ∨
      c.nreg 84 + 4 * l.length ≤ c.nreg 80 + nodeSeq c.nmem (c.nreg 80) (c.nreg 82) i
  vtxOut : ∀ i, i < l.length →
    c.nreg 81 + nodeSeq c.nmem (c.nreg 80) (c.nreg 82) i < c.nreg 84 ∨
      c.nreg 84 + 4 * l.length ≤ c.nreg 81 + nodeSeq c.nmem (c.nreg 80) (c.nreg 82) i
  work : c.nreg 84 + 4 * l.length ≤ W

/-! ### The frame of the reorientation phases -/

/-- The frame of the phases before the fragment: natural registers outside `85 … 94`, real
registers outside `80 … 83`, natural memory outside the work band (of `c₀`), the real memory
and the output are unchanged. -/
def PFrame (c₀ c : Config) : Prop :=
  (∀ r, (r < 85 ∨ 94 < r) → c.nreg r = c₀.nreg r) ∧
  (∀ r, (r < 80 ∨ 83 < r) → c.rreg r = c₀.rreg r) ∧
  (∀ a, (a < c₀.nreg 84 ∨ c₀.nreg 84 + 4 * c₀.nreg 83 ≤ a) → c.nmem a = c₀.nmem a) ∧
  c.rmem = c₀.rmem ∧ c.output = c₀.output

theorem pFrame_trans {c₀ c₁ c₂ : Config} (h₁ : PFrame c₀ c₁) (h₂ : PFrame c₁ c₂) :
    PFrame c₀ c₂ := by
  obtain ⟨n₁, r₁, m₁, q₁, o₁⟩ := h₁
  obtain ⟨n₂, r₂, m₂, q₂, o₂⟩ := h₂
  have e83 : c₁.nreg 83 = c₀.nreg 83 := n₁ 83 (by omega)
  have e84 : c₁.nreg 84 = c₀.nreg 84 := n₁ 84 (by omega)
  refine ⟨fun r hr => by rw [n₂ r hr, n₁ r hr], fun r hr => by rw [r₂ r hr, r₁ r hr],
    fun a ha => ?_, by rw [q₂, q₁], by rw [o₂, o₁]⟩
  rw [m₂ a (by rw [e83, e84]; exact ha), m₁ a ha]

/-! ### The lexicographic test -/

/-- `if ylexLT (rreg a1, rreg a2) (rreg b1, rreg b2) then t else e`: compare heights, then
abscissae. -/
def ylexTest (a1 a2 b1 b2 : ℕ) (t e : Stmt) : Stmt :=
  .ifLtR a2 b2 t (.ifLtR b2 a2 e (.ifLtR a1 b1 t e))

section ylex
variable {P : Polygon} {W : ℕ}

/-- **Spec lemma for `ylexTest`**: if both branches satisfy `post` within cost `K`, the test
does within `K + 6`. -/
theorem ylexTest_exec {a1 a2 b1 b2 : ℕ} {t e : Stmt} {K : ℕ} {post : Config → Prop}
    (c : Config)
    (ht : ylexLT (c.rreg a1, c.rreg a2) (c.rreg b1, c.rreg b2) →
      ∃ c' k, Exec P W t c c' k ∧ k ≤ K ∧ post c')
    (he : ¬ ylexLT (c.rreg a1, c.rreg a2) (c.rreg b1, c.rreg b2) →
      ∃ c' k, Exec P W e c c' k ∧ k ≤ K ∧ post c') :
    ∃ c' k, Exec P W (ylexTest a1 a2 b1 b2 t e) c c' k ∧ k ≤ K + 6 ∧ post c' := by
  unfold ylexTest
  by_cases h1 : c.rreg a2 < c.rreg b2
  · obtain ⟨c', k, ex, hk, hp⟩ := ht (Or.inl h1)
    exact ⟨c', k + 1, .ifLtR_true h1 ex, ⋄, hp⟩
  · by_cases h2 : c.rreg b2 < c.rreg a2
    · obtain ⟨c', k, ex, hk, hp⟩ := he (fun h => by
        rcases h with h | ⟨h, -⟩ <;> dsimp only at h <;> linarith)
      exact ⟨c', k + 1 + 2, .ifLtR_false h1 (.ifLtR_true h2 ex), ⋄, hp⟩
    · have heq : c.rreg a2 = c.rreg b2 := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
      by_cases h3 : c.rreg a1 < c.rreg b1
      · obtain ⟨c', k, ex, hk, hp⟩ := ht (Or.inr ⟨heq, h3⟩)
        exact ⟨c', k + 1 + 2 + 2, .ifLtR_false h1 (.ifLtR_false h2 (.ifLtR_true h3 ex)),
          ⋄, hp⟩
      · obtain ⟨c', k, ex, hk, hp⟩ := he (fun h => by
          rcases h with h | ⟨-, h⟩ <;> dsimp only at h
          · exact h1 h
          · exact h3 h)
        exact ⟨c', k + 2 + 2 + 2, .ifLtR_false h1 (.ifLtR_false h2 (.ifLtR_false h3 ex)),
          ⋄, hp⟩

end ylex

/-! ### The program -/

/-- Initialisation: `nreg 88 := 1`, `node := s`, `p := WB`, `nreg 87 := WB + 2m`. -/
def ptInit : Stmt := block [.constN 88 1, .copyN 85 82, .copyN 86 84, .addN 87 84 83,
  .addN 87 87 83]

/-- One step of the walk: `nmem p := vtx[node]; node := nxt[node]; p := p + 1`. -/
def walkBody : Stmt := block [.addN 89 81 85, .loadN 89 89, .storeN 86 89, .addN 89 80 85,
  .loadN 85 89, .addN 86 86 88]

/-- The walk: `while p < WB + 2m do walkBody`. -/
def walkLoop : Stmt := .whileLtN 86 87 walkBody

/-- Initialisation of the minimum scan: `mp := WB; q := WB + 1; nreg 87 := WB + m`. -/
def minInit : Stmt := block [.copyN 90 84, .addN 86 84 88, .addN 87 84 83]

/-- Reading the two vertices `vtx D[q]` (into `rreg 80, 81`) and `vtx D[mp]`
(into `rreg 82, 83`). -/
def minRead : Stmt := block [.loadN 89 86, .loadN 91 90, .readX 80 89, .readY 81 89,
  .readX 82 91, .readY 83 91]

/-- `if ylexLT (vtx D[q]) (vtx D[mp]) then mp := q`. -/
def minUpdate : Stmt := ylexTest 80 81 82 83 (.instr (.copyN 90 86)) .skip

/-- One step of the minimum scan. -/
def minBody : Stmt := .seq minRead (.seq minUpdate (.instr (.addN 86 86 88)))

/-- The minimum scan: `while q < WB + m do minBody`. -/
def minLoop : Stmt := .whileLtN 86 87 minBody

/-- Reading the successor `vtx D[i0 + 1]` (into `rreg 80, 81`) and the predecessor
`vtx D[i0 + m - 1]` (into `rreg 82, 83`) of the minimum. -/
def dirRead : Stmt := block [.addN 89 90 88, .loadN 89 89, .addN 91 90 83, .subN 91 91 88,
  .loadN 91 91, .readX 80 89, .readY 81 89, .readX 82 91, .readY 83 91]

/-- Forward copy set-up: `a := mp; inc := 1; dec := 0`. -/
def fwdSetup : Stmt := block [.copyN 86 90, .constN 92 1, .constN 93 0]

/-- Backward copy set-up: `a := mp + m; inc := 0; dec := 1`. -/
def bwdSetup : Stmt := block [.addN 86 90 83, .constN 92 0, .constN 93 1]

/-- The direction choice. -/
def dirSel : Stmt := ylexTest 80 81 82 83 fwdSetup bwdSetup

/-- Initialisation of the copy: `b := WB + 2m; nreg 87 := WB + 3m`. -/
def copyInit : Stmt := block [.addN 94 84 83, .addN 94 94 83, .addN 87 94 83]

/-- One step of the copy: `nmem b := nmem a; a := a + inc - dec; b := b + 1`. -/
def copyBody : Stmt := block [.loadN 89 86, .storeN 94 89, .addN 86 86 92, .subN 86 86 93,
  .addN 94 94 88]

/-- The copy: `while b < WB + 3m do copyBody`. -/
def copyLoop : Stmt := .whileLtN 94 87 copyBody

/-- The inputs of the fragment: `base := WB + 2m`, `sbase := WB + 3m`, `m`. -/
def fragInit : Stmt := block [.addN 60 84 83, .addN 60 60 83, .addN 61 60 83, .copyN 62 83]

/-- **The piece triangulator.** -/
def pieceTriStmt : Stmt :=
  .seq (.seq ptInit walkLoop) (.seq (.seq minInit minLoop) (.seq (.seq dirRead dirSel)
    (.seq (.seq copyInit copyLoop) (.seq fragInit mountainSubStmt))))

/-! ### Phase 1: the walk -/

/-- The invariant of the walk, relative to the configuration `c₀` at the start of the phase:
`p = nreg 86`, `node = nreg 85 = nxt^(p - WB) s` (in the memory of `c₀`), and the cells
`WB + k`, `k < p - WB`, hold `l[k % m]`. -/
def WalkInv (W : ℕ) (l : List ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ PFrame c₀ c ∧ c.nreg 88 = 1 ∧
    c.nreg 87 = c₀.nreg 84 + 2 * l.length ∧ c₀.nreg 84 ≤ c.nreg 86 ∧
    c.nreg 86 ≤ c₀.nreg 84 + 2 * l.length ∧
    c.nreg 85 = nodeSeq c₀.nmem (c₀.nreg 80) (c₀.nreg 82) (c.nreg 86 - c₀.nreg 84) ∧
    ∀ k, k < c.nreg 86 - c₀.nreg 84 → c.nmem (c₀.nreg 84 + k) = l.getD (k % l.length) 0

section walk
variable {P : Polygon} {W : ℕ} {l : List ℕ}


/-- **One step of the walk** preserves `WalkInv`, costs `6` and advances `p`. -/
theorem walkBody_inv {c₀ : Config} (hin : PieceInput W l c₀) (c : Config)
    (hI : WalkInv W l c₀ c) (ht : c.nreg 86 < c.nreg 87) :
    ∃ c' k, Exec P W walkBody c c' k ∧ WalkInv W l c₀ c' ∧ k ≤ 6 ∧
      c₀.nreg 84 + 2 * l.length - c'.nreg 86 < c₀.nreg 84 + 2 * l.length - c.nreg 86 := by
  obtain ⟨hw, hF, h88, h87, hlo, hhi, h85, htab⟩ := hI
  have hF' := hF
  obtain ⟨hFn, hFr, hFm, hFrm, hFo⟩ := hF
  have e80 : c.nreg 80 = c₀.nreg 80 := hFn 80 (⋄)
  have e81 : c.nreg 81 = c₀.nreg 81 := hFn 81 (⋄)
  have e83 := hin.len
  Ξ' h87 at ht
  have hm0 : 0 < l.length := ⋄
  have him : (c.nreg 86 - c₀.nreg 84) % l.length < l.length := Nat.mod_lt _ hm0
  have hnode : c.nreg 85 =
      nodeSeq c₀.nmem (c₀.nreg 80) (c₀.nreg 82) ((c.nreg 86 - c₀.nreg 84) % l.length) := by
    Ξ h85, nodeSeq_mod hin.cyc
  have hvW := hin.vtxW _ him
  have hnW := hin.nxtW _ him
  have hvO := hin.vtxOut _ him
  have hnO := hin.nxtOut _ him
  have hW := hin.work
  Ξ' ← hnode at hvW hnW hvO hnO
  have hvmem : c.nmem (c.nreg 81 + c.nreg 85) = l.getD ((c.nreg 86 - c₀.nreg 84) % l.length) 0 := by
    Ξ e81, hFm _ (by rw [e83]; exact hvO), hnode
    exact hin.vtx _ him
  have hne : c.nreg 80 + c.nreg 85 ≠ c.nreg 86 := by rw [e80]; omega
  have hnmem : c.nmem (c.nreg 80 + c.nreg 85) = c₀.nmem (c₀.nreg 80 + c.nreg 85) := by
    Ξ e80, hFm _ (by rw [e83]; exact hnO)
  unfold walkBody
  exec_block
  · rw [e81]; exact hvW
  · config_simp; rw [e80]; exact hnW
  · config_simp; rw [h88]; omega
  · refine ⟨⟨‹_›, pFrame_trans hF' ⟨fun r hr => ?_, fun r _ => rfl, fun a ha => ?_, rfl, rfl⟩,
      by config_simp; exact h88, by config_simp; exact h87, by config_simp; omega,
      by config_simp; omega, ?_, ?_⟩, ⋄, by config_simp; omega⟩
    · have h1 : r ≠ 85 := ⋄
      have h2 : r ≠ 86 := ⋄
      have h3 : r ≠ 89 := ⋄
      Θ h1, h2, h3
    · config_simp
      Ξ Machine.upd_other _ _ _ (by rw [hFn 84 (⋄), hFn 83 (⋄)] at ha; omega)
    · config_simp
      rw [Machine.upd_other _ _ _ hne, hnmem, h88,
        show c.nreg 86 + 1 - c₀.nreg 84 = c.nreg 86 - c₀.nreg 84 + 1 by omega, nodeSeq_succ,
        h85]
    · intro k hk
      config_simp at hk
      Ξ' h88 at hk
      config_simp
      by_cases hk' : k = c.nreg 86 - c₀.nreg 84
      · Ξ show c₀.nreg 84 + k = c.nreg 86 by omega, Machine.upd_same, hvmem, hk'
      · Ξ Machine.upd_other _ _ _ (⋄)
        exact htab k (⋄)

/-- **Spec lemma for the walk phase** `ptInit; walkLoop`: cost `≤ 16 m + 7`; afterwards the
cells `WB + i`, `i < 2m`, hold `l[i % m]`, `nreg 88 = 1`, within the frame `PFrame`. -/
theorem walkPhase_exec (c : Config) (hc : WordsBounded W c) (hin : PieceInput W l c)
    (hm1 : 1 ≤ l.length) :
    ∃ c' k, Exec P W (.seq ptInit walkLoop) c c' k ∧ k ≤ 16 * l.length + 7 ∧ PFrame c c' ∧
      c'.nreg 88 = 1 ∧
      ∀ i, i < 2 * l.length → c'.nmem (c.nreg 84 + i) = l.getD (i % l.length) 0 := by
  have hW := hin.work
  have h83 := hin.len
  unfold ptInit
  refine spec_seq ?_
  exec_block
  · omega
  · config_simp; omega
  · config_simp; omega
  refine spec_imp (Exec.whileLtN_bounded (WalkInv W l c)
    (fun d => c.nreg 84 + 2 * l.length - d.nreg 86) 6 (fun _ h => h.1)
    (fun d hd ht => walkBody_inv (P := P) hin d hd ht) ?_) ?_
  · refine ⟨‹_›, ⟨fun r hr => ?_, fun r _ => rfl, fun a _ => rfl, rfl, rfl⟩,
      by config_simp, by config_simp; omega, by config_simp; exact le_rfl, by config_simp; omega,
      ?_, ?_⟩
    · have h1 : r ≠ 85 := ⋄
      have h2 : r ≠ 86 := ⋄
      have h3 : r ≠ 87 := ⋄
      have h4 : r ≠ 88 := ⋄
      Θ h1, h2, h3, h4
    · config_simp; rw [Nat.sub_self]; rfl
    · intro k hk; config_simp at hk; omega
  · rintro c' k ⟨⟨hw, hF, h88, h87, hlo, hhi, h85, htab⟩, hexit, hk⟩
    config_simp at hk
    Ξ' h87 at hexit
    refine ⟨⋄, hF, h88, fun i hi => htab i (⋄)⟩

end walk

/-! ### Phase 2: the minimum scan -/

section minimum
variable {P : Polygon} {W : ℕ} {l : List ℕ}

/-- **Spec lemma for the update of the minimum**: cost `≤ 7`; `mp := q` exactly when
`(rreg 80, rreg 81) <_ylex (rreg 82, rreg 83)`; nothing else changes. -/
theorem minUpdate_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W minUpdate c c' k ∧ k ≤ 7 ∧
      (ylexLT (c.rreg 80, c.rreg 81) (c.rreg 82, c.rreg 83) → c'.nreg 90 = c.nreg 86) ∧
      (¬ ylexLT (c.rreg 80, c.rreg 81) (c.rreg 82, c.rreg 83) → c'.nreg 90 = c.nreg 90) ∧
      (∀ r, r ≠ 90 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold minUpdate
  refine ylexTest_exec (K := 1) c (fun h => ?_) (fun h => ?_)
  · refine ⟨_, 1, Exec.copyN hc 90 86, le_rfl, fun _ => by config_simp,
      fun h' => absurd h h', fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩
  · exact ⟨c, 0, .skip hc, by omega, fun h' => absurd h' h, fun _ => rfl, fun _ _ => rfl, rfl,
      rfl, rfl, rfl⟩

/-- **Spec lemma for one step of the minimum scan**: cost `≤ 14`; `mp := q` exactly when
`vtx (nmem q) <_ylex vtx (nmem mp)`; `q := q + nreg 88`; natural registers other than
`86, 89, 90, 91`, real registers outside `80 … 83`, memories and output unchanged. -/
theorem minBody_exec (c : Config) (hc : WordsBounded W c) (hW : c.nreg 86 + c.nreg 88 ≤ W) :
    ∃ c' k, Exec P W minBody c c' k ∧ k ≤ 14 ∧
      (ylexLT (P.vtx (c.nmem (c.nreg 86))) (P.vtx (c.nmem (c.nreg 90))) →
        c'.nreg 90 = c.nreg 86) ∧
      (¬ ylexLT (P.vtx (c.nmem (c.nreg 86))) (P.vtx (c.nmem (c.nreg 90))) →
        c'.nreg 90 = c.nreg 90) ∧
      c'.nreg 86 = c.nreg 86 + c.nreg 88 ∧
      (∀ r, r ≠ 86 → r ≠ 89 → r ≠ 90 → r ≠ 91 → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 80 ∨ 83 < r) → c'.rreg r = c.rreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold minBody minRead
  refine spec_seq ?_
  exec_block
  refine spec_seq (spec_use (minUpdate_exec _ ‹_›) ?_)
  intro c₁ k₁ hk₁ hw₁ ⟨hlt, hnlt, hfr, hrr, hnm, hrm, hout⟩
  config_simp at hlt
  config_simp at hnlt
  config_simp at hfr
  config_simp at hrr
  config_simp at hnm
  config_simp at hrm
  config_simp at hout
  ϴ' Prod.mk.eta at hlt hnlt
  have hn86 : c₁.nreg 86 = c.nreg 86 := by rw [hfr 86 (⋄)]; config_simp
  have hn88 : c₁.nreg 88 = c.nreg 88 := by rw [hfr 88 (⋄)]; config_simp
  refine spec_instr (Exec.addN hw₁ 86 86 88 (by rw [hn86, hn88]; exact hW)) fun _ => ?_
  refine ⟨⋄, fun h => ?_, fun h => ?_, ?_, fun r h86 h89 h90 h91 => ?_, fun r hr => ?_,
    hnm, hrm, hout⟩
  · config_simp; exact hlt h
  · config_simp; exact hnlt h
  · config_simp; Ξ hn86, hn88
  · config_simp; rw [Machine.upd_other _ _ _ h86, hfr r h90]; Θ h89, h91
  · config_simp; Ξ hrr
    simp [show r ≠ 80 by omega, show r ≠ 81 by omega, show r ≠ 82 by omega,
      show r ≠ 83 by omega]

/-- The invariant of the minimum scan, relative to the configuration `c₀` at the start of the
phase: `q = nreg 86`, `mp = nreg 90 < q`, and position `mp - WB` is `ylexLT`-minimal among the
positions `< q - WB`. -/
def MinInv (P : Polygon) (W : ℕ) (l : List ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ PFrame c₀ c ∧ c.nmem = c₀.nmem ∧ c.nreg 88 = 1 ∧
    c.nreg 87 = c₀.nreg 84 + l.length ∧ c₀.nreg 84 < c.nreg 86 ∧
    c.nreg 86 ≤ c₀.nreg 84 + l.length ∧ c₀.nreg 84 ≤ c.nreg 90 ∧ c.nreg 90 < c.nreg 86 ∧
    ∀ j, j < c.nreg 86 - c₀.nreg 84 →
      ¬ ylexLT (ptAt P l j) (ptAt P l (c.nreg 90 - c₀.nreg 84))

/-- Reading the doubled table `D[i] = l[i % m]` at an address of the first copy. -/
theorem tab_read {c₀ c : Config} (htab : ∀ i, i < 2 * l.length →
      c₀.nmem (c₀.nreg 84 + i) = l.getD (i % l.length) 0)
    (hnm : c.nmem = c₀.nmem) {a : ℕ} (hlo : c₀.nreg 84 ≤ a) (hhi : a < c₀.nreg 84 + l.length) :
    P.vtx (c.nmem a) = ptAt P l (a - c₀.nreg 84) := by
  rw [hnm, show a = c₀.nreg 84 + (a - c₀.nreg 84) by omega, htab _ (⋄),
    Nat.mod_eq_of_lt (⋄), Nat.add_sub_cancel_left]
  rfl


/-- **One step of the minimum scan** preserves `MinInv`, costs `≤ 14` and advances `q`. -/
theorem minBody_inv {c₀ : Config} (hW : c₀.nreg 84 + 4 * l.length ≤ W)
    (htab : ∀ i, i < 2 * l.length → c₀.nmem (c₀.nreg 84 + i) = l.getD (i % l.length) 0)
    (c : Config) (hI : MinInv P W l c₀ c) (ht : c.nreg 86 < c.nreg 87) :
    ∃ c' k, Exec P W minBody c c' k ∧ MinInv P W l c₀ c' ∧ k ≤ 14 ∧
      c₀.nreg 84 + l.length - c'.nreg 86 < c₀.nreg 84 + l.length - c.nreg 86 := by
  obtain ⟨hw, hF, hnm, h88, h87, hlo, hhi, hmlo, hmhi, hmin⟩ := hI
  rw [h87] at ht
  obtain ⟨c', k, ex, hk, hlt, hnlt, h86', hfn, hfr, hnm', hrm', hout'⟩ :=
    minBody_exec (P := P) c hw (by rw [h88]; omega)
  have eq : P.vtx (c.nmem (c.nreg 86)) = ptAt P l (c.nreg 86 - c₀.nreg 84) :=
    tab_read htab hnm (by omega) (by omega)
  have em : P.vtx (c.nmem (c.nreg 90)) = ptAt P l (c.nreg 90 - c₀.nreg 84) :=
    tab_read htab hnm (by omega) (by omega)
  rw [eq, em] at hlt hnlt
  have hF' : PFrame c c' := ⟨fun r hr => hfn r (by omega) (by omega) (by omega) (by omega),
    fun r hr => hfr r hr, fun a _ => by rw [hnm'], hrm', hout'⟩
  refine ⟨c', k, ex, ⟨ex.wb_right, pFrame_trans hF hF', by rw [hnm', hnm], ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, hk, ?_⟩
  · rw [hfn 88 (by omega) (by omega) (by omega) (by omega), h88]
  · rw [hfn 87 (by omega) (by omega) (by omega) (by omega), h87]
  · rw [h86']; omega
  · rw [h86', h88]; omega
  · by_cases hl : ylexLT (ptAt P l (c.nreg 86 - c₀.nreg 84)) (ptAt P l (c.nreg 90 - c₀.nreg 84))
    · rw [hlt hl]; omega
    · rw [hnlt hl]; omega
  · by_cases hl : ylexLT (ptAt P l (c.nreg 86 - c₀.nreg 84)) (ptAt P l (c.nreg 90 - c₀.nreg 84))
    · rw [hlt hl, h86', h88]; omega
    · rw [hnlt hl, h86', h88]; omega
  · intro j hj
    rw [h86', h88] at hj
    by_cases hl : ylexLT (ptAt P l (c.nreg 86 - c₀.nreg 84)) (ptAt P l (c.nreg 90 - c₀.nreg 84))
    · rw [hlt hl]
      rcases Nat.lt_or_ge j (c.nreg 86 - c₀.nreg 84) with hj' | hj'
      · exact fun h' => hmin j hj' (ylexLT_trans h' hl)
      · rw [show j = c.nreg 86 - c₀.nreg 84 by omega]
        exact ylexLT_irrefl _
    · rw [hnlt hl]
      rcases Nat.lt_or_ge j (c.nreg 86 - c₀.nreg 84) with hj' | hj'
      · exact hmin j hj'
      · rw [show j = c.nreg 86 - c₀.nreg 84 by omega]
        exact hl
  · rw [h86', h88]; omega

/-- **Spec lemma for the minimum phase** `minInit; minLoop`: cost `≤ 16 m + 5`; afterwards
`mp = nreg 90 ≥ WB` and `mp - WB` is a minimum position of `l` (`IsMinPos`); the memory is
unchanged, `nreg 88 = 1`, within `PFrame`. -/
theorem minPhase_exec (c : Config) (hc : WordsBounded W c) (hm1 : 1 ≤ l.length)
    (h83 : c.nreg 83 = l.length) (hW : c.nreg 84 + 4 * l.length ≤ W) (h88 : c.nreg 88 = 1)
    (htab : ∀ i, i < 2 * l.length → c.nmem (c.nreg 84 + i) = l.getD (i % l.length) 0) :
    ∃ c' k, Exec P W (.seq minInit minLoop) c c' k ∧ k ≤ 16 * l.length + 5 ∧ PFrame c c' ∧
      c'.nmem = c.nmem ∧ c'.nreg 88 = 1 ∧ c.nreg 84 ≤ c'.nreg 90 ∧
      IsMinPos P l (c'.nreg 90 - c.nreg 84) := by
  unfold minInit
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h88]; omega
  · config_simp; omega
  refine spec_imp (Exec.whileLtN_bounded (MinInv P W l c)
    (fun d => c.nreg 84 + l.length - d.nreg 86) 14 (fun _ h => h.1)
    (fun d hd ht => minBody_inv (P := P) hW htab d hd ht) ?_) ?_
  · refine ⟨‹_›, ⟨fun r hr => ?_, fun r _ => rfl, fun a _ => rfl, rfl, rfl⟩, rfl,
      by config_simp; exact h88, by config_simp; rw [h83], by config_simp; omega,
      by config_simp; omega, by config_simp; exact le_rfl, by config_simp; omega, ?_⟩
    · have h1 : r ≠ 86 := ⋄
      have h2 : r ≠ 87 := ⋄
      have h3 : r ≠ 90 := ⋄
      Θ h1, h2, h3
    · intro j hj
      config_simp at hj
      config_simp
      Ξ' h88 at hj
      Ξ show j = 0 by omega, Nat.sub_self
      exact ylexLT_irrefl _
  · rintro c' k ⟨⟨hw, hF, hnm, h88', h87, hlo, hhi, hmlo, hmhi, hmin⟩, hexit, hk⟩
    config_simp at hk
    Ξ' h88 at hk
    Ξ' h87 at hexit
    refine ⟨⋄, hF, hnm, h88', hmlo, ⋄, fun j hj => hmin j (⋄)⟩

end minimum

/-! ### Phase 3: the direction -/

section direction
variable {P : Polygon} {W : ℕ} {l : List ℕ}

/-- **Spec lemma for the direction choice**: cost `≤ 9`; forward set-up
(`a := mp, inc := 1, dec := 0`) when `(rreg 80, rreg 81) <_ylex (rreg 82, rreg 83)`, backward
set-up (`a := mp + m, inc := 0, dec := 1`) otherwise; nothing else changes. -/
theorem dirSel_exec (c : Config) (hc : WordsBounded W c) (h1 : 1 ≤ W)
    (hW : c.nreg 90 + c.nreg 83 ≤ W) :
    ∃ c' k, Exec P W dirSel c c' k ∧ k ≤ 9 ∧
      (ylexLT (c.rreg 80, c.rreg 81) (c.rreg 82, c.rreg 83) →
        c'.nreg 86 = c.nreg 90 ∧ c'.nreg 92 = 1 ∧ c'.nreg 93 = 0) ∧
      (¬ ylexLT (c.rreg 80, c.rreg 81) (c.rreg 82, c.rreg 83) →
        c'.nreg 86 = c.nreg 90 + c.nreg 83 ∧ c'.nreg 92 = 0 ∧ c'.nreg 93 = 1) ∧
      (∀ r, r ≠ 86 → r ≠ 92 → r ≠ 93 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dirSel
  refine ylexTest_exec (K := 3) c (fun h => ?_) (fun h => ?_)
  · unfold fwdSetup
    exec_block
    · omega
    · omega
    · refine ⟨by omega, fun _ => ⟨by config_simp, by config_simp, by config_simp⟩,
        fun h' => absurd h h', fun r h86 h92 h93 => by simp [h86, h92, h93], rfl, rfl, rfl,
        rfl⟩
  · unfold bwdSetup
    exec_block
    · exact hW
    · omega
    · omega
    · refine ⟨by omega, fun h' => absurd h' h,
        fun _ => ⟨by config_simp, by config_simp, by config_simp⟩,
        fun r h86 h92 h93 => by simp [h86, h92, h93], rfl, rfl, rfl, rfl⟩


/-- **Spec lemma for the direction phase** `dirRead; dirSel`: with `mp = nreg 90`,
`i0 = mp - WB < m`: cost `≤ 18`; forward set-up iff `DirFwd P l i0`. -/
theorem dirPhase_exec (c : Config) (hc : WordsBounded W c) (hm1 : 1 ≤ l.length)
    (h83 : c.nreg 83 = l.length) (hW : c.nreg 84 + 4 * l.length ≤ W) (h88 : c.nreg 88 = 1)
    (htab : ∀ i, i < 2 * l.length → c.nmem (c.nreg 84 + i) = l.getD (i % l.length) 0)
    (hlo : c.nreg 84 ≤ c.nreg 90) (hi0 : c.nreg 90 - c.nreg 84 < l.length) :
    ∃ c' k, Exec P W (.seq dirRead dirSel) c c' k ∧ k ≤ 18 ∧ PFrame c c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 88 = 1 ∧ c'.nreg 90 = c.nreg 90 ∧
      (DirFwd P l (c.nreg 90 - c.nreg 84) →
        c'.nreg 86 = c.nreg 90 ∧ c'.nreg 92 = 1 ∧ c'.nreg 93 = 0) ∧
      (¬ DirFwd P l (c.nreg 90 - c.nreg 84) →
        c'.nreg 86 = c.nreg 90 + l.length ∧ c'.nreg 92 = 0 ∧ c'.nreg 93 = 1) := by
  have hq : ∀ a, c.nreg 84 ≤ a → a - c.nreg 84 < 2 * l.length →
      P.vtx (c.nmem a) = ptAt P l ((a - c.nreg 84) % l.length) := by
    intro a ha1 ha2
    rw [show a = c.nreg 84 + (a - c.nreg 84) by omega, htab _ ha2, Nat.add_sub_cancel_left]
    rfl
  have enx : P.vtx (c.nmem (c.nreg 90 + c.nreg 88)) =
      ptAt P l ((c.nreg 90 - c.nreg 84 + 1) % l.length) := by
    rw [hq _ (by omega) (by omega), h88, show c.nreg 90 + 1 - c.nreg 84 =
      c.nreg 90 - c.nreg 84 + 1 by omega]
  have epr : P.vtx (c.nmem (c.nreg 90 + c.nreg 83 - c.nreg 88)) =
      ptAt P l ((c.nreg 90 - c.nreg 84 + l.length - 1) % l.length) := by
    rw [hq _ (by omega) (by omega), h88, h83, show c.nreg 90 + l.length - 1 - c.nreg 84 =
      c.nreg 90 - c.nreg 84 + l.length - 1 by omega]
  unfold dirRead
  refine spec_seq ?_
  exec_block
  · rw [h88]; omega
  · config_simp; rw [h83]; omega
  refine spec_use (dirSel_exec _ ‹_› (by omega) (by config_simp; rw [h83]; omega)) ?_
  intro c' k hk hw' ⟨hf, hb, hfn, hrr, hnm, hrm, hout⟩
  config_simp at hf
  config_simp at hb
  config_simp at hfn
  config_simp at hrr
  config_simp at hnm
  config_simp at hrm
  config_simp at hout
  simp only [Prod.mk.eta] at hf hb
  rw [enx, epr] at hf hb
  rw [h83] at hb
  refine ⟨by omega, ⟨fun r hr => ?_, fun r hr => ?_, fun a _ => by rw [hnm], hrm, hout⟩, hnm,
    ?_, ?_, fun hd => hf hd, fun hd => hb hd⟩
  · rw [hfn r (by omega) (by omega) (by omega)]
    simp [show r ≠ 89 by omega, show r ≠ 91 by omega]
  · rw [hrr]
    simp [show r ≠ 80 by omega, show r ≠ 81 by omega, show r ≠ 82 by omega,
      show r ≠ 83 by omega]
  · rw [hfn 88 (by omega) (by omega) (by omega)]; config_simp; exact h88
  · rw [hfn 90 (by omega) (by omega) (by omega)]; config_simp

end direction

/-! ### Phase 4: the copy -/

/-- The invariant of the copy, relative to the configuration `c₀` at the start of the phase
(after the direction set-up), with `WB = nreg 84`, `mp = nreg 90`, `i0 = mp - WB`:
`b = nreg 94 ∈ [WB + 2m, WB + 3m]`, `j = b - (WB + 2m)` entries copied, the source pointer
`a = nreg 86` is `mp + j` (forward) or `mp + m - j` (backward), the doubled table is intact,
and `nmem (WB + 2m + j') = (reorient P l i0)[j']` for `j' < j`. -/
def CopyInv (P : Polygon) (W : ℕ) (l : List ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ PFrame c₀ c ∧ c.nreg 88 = 1 ∧
    c.nreg 87 = c₀.nreg 84 + 3 * l.length ∧ c₀.nreg 84 + 2 * l.length ≤ c.nreg 94 ∧
    c.nreg 94 ≤ c₀.nreg 84 + 3 * l.length ∧
    (DirFwd P l (c₀.nreg 90 - c₀.nreg 84) →
      c.nreg 86 = c₀.nreg 90 + (c.nreg 94 - (c₀.nreg 84 + 2 * l.length)) ∧
        c.nreg 92 = 1 ∧ c.nreg 93 = 0) ∧
    (¬ DirFwd P l (c₀.nreg 90 - c₀.nreg 84) →
      c.nreg 86 + (c.nreg 94 - (c₀.nreg 84 + 2 * l.length)) = c₀.nreg 90 + l.length ∧
        c.nreg 92 = 0 ∧ c.nreg 93 = 1) ∧
    (∀ i, i < 2 * l.length → c.nmem (c₀.nreg 84 + i) = c₀.nmem (c₀.nreg 84 + i)) ∧
    ∀ j, j < c.nreg 94 - (c₀.nreg 84 + 2 * l.length) →
      c.nmem (c₀.nreg 84 + 2 * l.length + j) = (reorient P l (c₀.nreg 90 - c₀.nreg 84)).getD j 0

section copy
variable {P : Polygon} {W : ℕ} {l : List ℕ}


/-- **One step of the copy** preserves `CopyInv`, costs `5` and advances `b`. -/
theorem copyBody_inv {c₀ : Config} (h83 : c₀.nreg 83 = l.length)
    (hW : c₀.nreg 84 + 4 * l.length ≤ W)
    (htab : ∀ i, i < 2 * l.length → c₀.nmem (c₀.nreg 84 + i) = l.getD (i % l.length) 0)
    (hlo : c₀.nreg 84 ≤ c₀.nreg 90) (hi0 : c₀.nreg 90 - c₀.nreg 84 < l.length)
    (c : Config) (hI : CopyInv P W l c₀ c) (ht : c.nreg 94 < c.nreg 87) :
    ∃ c' k, Exec P W copyBody c c' k ∧ CopyInv P W l c₀ c' ∧ k ≤ 5 ∧
      c₀.nreg 84 + 3 * l.length - c'.nreg 94 < c₀.nreg 84 + 3 * l.length - c.nreg 94 := by
  obtain ⟨hw, hF, h88, h87, hblo, hbhi, hfwd, hbwd, hD, hT⟩ := hI
  have hF' := hF
  obtain ⟨hFn, hFr, hFm, hFrm, hFo⟩ := hF
  have e83 : c.nreg 83 = c₀.nreg 83 := hFn 83 (⋄)
  have e84 : c.nreg 84 = c₀.nreg 84 := hFn 84 (⋄)
  Ξ' h87 at ht
  have hval : c.nmem (c.nreg 86) = (reorient P l (c₀.nreg 90 - c₀.nreg 84)).getD
      (c.nreg 94 - (c₀.nreg 84 + 2 * l.length)) 0 := by
    by_cases hd : DirFwd P l (c₀.nreg 90 - c₀.nreg 84)
    · obtain ⟨e86, -, -⟩ := hfwd hd
      rw [show c.nreg 86 = c₀.nreg 84 + (c₀.nreg 90 - c₀.nreg 84 +
          (c.nreg 94 - (c₀.nreg 84 + 2 * l.length))) by omega, hD _ (⋄),
        htab _ (⋄)]
      unfold reorient
      Ξ ite_eq_left hd, getD_fwdList _ _ (⋄)
    · obtain ⟨e86, -, -⟩ := hbwd hd
      rw [show c.nreg 86 = c₀.nreg 84 + (c₀.nreg 90 - c₀.nreg 84 + l.length -
          (c.nreg 94 - (c₀.nreg 84 + 2 * l.length))) by omega, hD _ (⋄),
        htab _ (⋄)]
      unfold reorient
      Ξ ite_eq_right hd, getD_bwdList _ _ (⋄)
  have hside : c.nreg 86 + c.nreg 92 ≤ W := by
    by_cases hd : DirFwd P l (c₀.nreg 90 - c₀.nreg 84)
    · obtain ⟨e86, e92, -⟩ := hfwd hd
      rw [e86, e92]; omega
    · obtain ⟨-, e92, -⟩ := hbwd hd
      rw [e92, Nat.add_zero]; exact hw.1 86
  unfold copyBody
  exec_block
  · exact hside
  · config_simp; rw [h88]; omega
  · refine ⟨⟨‹_›, pFrame_trans hF' ⟨fun r hr => ?_, fun r _ => rfl, fun a ha => ?_, rfl, rfl⟩,
      by config_simp; exact h88, by config_simp; exact h87, by config_simp; omega,
      by config_simp; omega, fun hd => ?_, fun hd => ?_, fun i hi => ?_, fun j hj => ?_⟩,
      ⋄, by config_simp; omega⟩
    · have h1 : r ≠ 86 := ⋄
      have h2 : r ≠ 89 := ⋄
      have h3 : r ≠ 94 := ⋄
      Θ h1, h2, h3
    · config_simp
      Ξ Machine.upd_other _ _ _ (by rw [e83, e84, h83] at ha; omega)
    · obtain ⟨e86, e92, e93⟩ := hfwd hd
      config_simp
      Ξ e86, e92, e93, h88
      omega
    · obtain ⟨e86, e92, e93⟩ := hbwd hd
      config_simp
      Ξ e92, e93, h88
      omega
    · config_simp
      Ξ Machine.upd_other _ _ _ (⋄)
      exact hD i hi
    · config_simp at hj
      Ξ' h88 at hj
      config_simp
      by_cases hj' : j = c.nreg 94 - (c₀.nreg 84 + 2 * l.length)
      · rw [show c₀.nreg 84 + 2 * l.length + j = c.nreg 94 by omega, Machine.upd_same, hval,
          hj']
      · Ξ Machine.upd_other _ _ _ (⋄)
        exact hT j (⋄)

/-- **Spec lemma for the copy phase** `copyInit; copyLoop`: after the direction set-up, the
cells `WB + 2m + j` (`j < m`) receive `(reorient P l i0)[j]`; cost `≤ 7 m + 5`; `PFrame`. -/
theorem copyPhase_exec (c : Config) (hc : WordsBounded W c) (h83 : c.nreg 83 = l.length)
    (hW : c.nreg 84 + 4 * l.length ≤ W) (h88 : c.nreg 88 = 1)
    (htab : ∀ i, i < 2 * l.length → c.nmem (c.nreg 84 + i) = l.getD (i % l.length) 0)
    (hlo : c.nreg 84 ≤ c.nreg 90) (hi0 : c.nreg 90 - c.nreg 84 < l.length)
    (hfwd : DirFwd P l (c.nreg 90 - c.nreg 84) →
      c.nreg 86 = c.nreg 90 ∧ c.nreg 92 = 1 ∧ c.nreg 93 = 0)
    (hbwd : ¬ DirFwd P l (c.nreg 90 - c.nreg 84) →
      c.nreg 86 = c.nreg 90 + l.length ∧ c.nreg 92 = 0 ∧ c.nreg 93 = 1) :
    ∃ c' k, Exec P W (.seq copyInit copyLoop) c c' k ∧ k ≤ 7 * l.length + 5 ∧ PFrame c c' ∧
      ∀ j, j < l.length → c'.nmem (c.nreg 84 + 2 * l.length + j) =
        (reorient P l (c.nreg 90 - c.nreg 84)).getD j 0 := by
  unfold copyInit
  refine spec_seq ?_
  exec_block
  · rw [h83]; omega
  · config_simp; rw [h83]; omega
  · config_simp; rw [h83]; omega
  refine spec_imp (Exec.whileLtN_bounded (CopyInv P W l c)
    (fun d => c.nreg 84 + 3 * l.length - d.nreg 94) 5 (fun _ h => h.1)
    (fun d hd ht => copyBody_inv (P := P) h83 hW htab hlo hi0 d hd ht) ?_) ?_
  · refine ⟨‹_›, ⟨fun r hr => ?_, fun r _ => rfl, fun a _ => rfl, rfl, rfl⟩,
      by config_simp; exact h88, by config_simp; rw [h83]; omega, by config_simp; rw [h83]; omega,
      by config_simp; rw [h83]; omega, fun hd => ?_, fun hd => ?_, fun i _ => rfl, ?_⟩
    · have h1 : r ≠ 87 := ⋄
      have h2 : r ≠ 94 := ⋄
      Θ h1, h2
    · obtain ⟨e86, e92, e93⟩ := hfwd hd
      config_simp
      Ξ e86, e92, e93, h83
      omega
    · obtain ⟨e86, e92, e93⟩ := hbwd hd
      config_simp
      Ξ e86, e92, e93, h83
      omega
    · intro j hj
      config_simp at hj
      Ξ' h83 at hj
      omega
  · rintro c' k ⟨⟨hw, hF, h88', h87, hblo, hbhi, -, -, -, hT⟩, hexit, hk⟩
    config_simp at hk
    Ξ' h83 at hk
    Ξ' h87 at hexit
    refine ⟨⋄, hF, fun j hj => hT j (⋄)⟩

end copy

/-! ### Phase 5: the stack walk, and the whole program -/

section main
variable {P : Polygon} {W : ℕ}

/-- **Spec lemma for the last phase** `fragInit; mountainSubStmt`: with the reoriented list `l'`
(a mountain) in the cells `WB + 2m + j`, the fragment appends `T.map (relabelList l')` for a
weak triangulation `T` of `subPoly P l'`, at cost `≤ 73 m + 4`, using the stack band
`[WB + 3m, WB + 4m)`. -/
theorem fragPhase_exec {l' : List ℕ} (c : Config) (hc : WordsBounded W c)
    (h83 : c.nreg 83 = l'.length) (hW : c.nreg 84 + 4 * l'.length ≤ W)
    (hM : IsMountain (subPoly P l'))
    (htab : ∀ j, j < l'.length → c.nmem (c.nreg 84 + 2 * l'.length + j) = l'.getD j 0) :
    ∃ c' k, Exec P W (.seq fragInit mountainSubStmt) c c' k ∧ k ≤ 73 * l'.length + 4 ∧
      (∃ T, WeakTriangulates (subPoly P l') T ∧ c'.output = c.output ++ T.map (relabelList l')) ∧
      (∀ r, (r < 60 ∨ 74 < r) → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 61 ∨ 72 < r) → c'.rreg r = c.rreg r) ∧
      (∀ a, (a < c.nreg 84 + 3 * l'.length ∨ c.nreg 84 + 4 * l'.length ≤ a) →
        c'.nmem a = c.nmem a) ∧
      c'.rmem = c.rmem := by
  unfold fragInit
  refine spec_seq ?_
  exec_block
  · rw [h83]; omega
  · config_simp; rw [h83]; omega
  · config_simp; rw [h83]; omega
  obtain ⟨c', k, T, ex, hk, hT, hout, hn, hr, hnm, hrm⟩ :=
    mountainSub_exec_weak (P := P) (W := W) hM _ ‹_›
      (fun i hi => by
        config_simp
        rw [h83, show c.nreg 84 + l'.length + l'.length + i = c.nreg 84 + 2 * l'.length + i by
          omega]
        exact htab i hi)
      (by config_simp; exact h83) (Or.inl (by config_simp; rw [h83]))
      (by config_simp; rw [h83]; omega) (by config_simp; rw [h83]; omega)
  refine ⟨c', k, ex, ⋄, ⟨T, hT, Ρ hout⟩, fun r hr' => ?_, fun r hr' => ?_,
    fun a ha => ?_, hrm⟩
  · Ξ hn r (⋄)
    Θ show r ≠ 60 by omega, show r ≠ 61 by omega, show r ≠ 62 by omega
  · Ξ hr r hr'
  · Ξ hnm a (by config_simp; rw [h83]; omega)


/-- **The piece triangulator.**  Let the piece `l` be given as a cyclic linked list
(`PieceInput W l c`, registers `80 … 84`), and let it be a rotated, possibly reversed,
monotone mountain (the conclusion of `Chazelle.Mountain.piece_isMountain`).  Then
`pieceTriStmt` runs with cost `≤ 112 m + 39` (`m = l.length`) and appends to the output
`T.map (relabelList l)` for a weak triangulation `T` of `subPoly P l` (triangles in original
vertex indices).  **Frame:** natural registers outside `60 … 74` and `85 … 94` (in particular
the inputs `80 … 84`), real registers outside `61 … 72` and `80 … 83`, the natural memory
outside the work band `[WB, WB + 4m)` (in particular the linked arrays) and the real memory
are unchanged. -/
theorem pieceTri_exec {l : List ℕ}
    (hmount : ∃ s, IsMountain ((subPoly P l).rotate s) ∨
      IsMountain ((subPoly P l.reverse).rotate s))
    (c : Config) (hc : WordsBounded W c) (hin : PieceInput W l c) :
    ∃ c' k, Exec P W pieceTriStmt c c' k ∧ k ≤ 112 * l.length + 39 ∧
      (∃ T, WeakTriangulates (subPoly P l) T ∧ c'.output = c.output ++ T.map (relabelList l)) ∧
      (∀ r, (r < 60 ∨ (74 < r ∧ r < 85) ∨ 94 < r) → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 61 ∨ (72 < r ∧ r < 80) ∨ 83 < r) → c'.rreg r = c.rreg r) ∧
      (∀ a, (a < c.nreg 84 ∨ c.nreg 84 + 4 * l.length ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rmem = c.rmem := by
  have h3 : 3 ≤ l.length := by
    obtain ⟨s, h | h⟩ := hmount
    · have := h.1.1
      rwa [Chazelle.Existence.n_rotate, n_subPoly] at this
    · have := h.1.1
      rwa [Chazelle.Existence.n_rotate, n_subPoly, List.length_reverse] at this
  have hW := hin.work
  have h83 := hin.len
  -- phase 1
  obtain ⟨c₁, k₁, ex₁, hk₁, hF₁, h88₁, htab₁⟩ := walkPhase_exec (P := P) c hc hin (⋄)
  have e83₁ : c₁.nreg 83 = l.length := Ρ hF₁.1 83 (⋄), h83
  have e84₁ : c₁.nreg 84 = c.nreg 84 := hF₁.1 84 (⋄)
  Ξ' ← e84₁ at htab₁
  -- phase 2
  obtain ⟨c₂, k₂, ex₂, hk₂, hF₂, hnm₂, h88₂, hlo₂, hmin₂⟩ := minPhase_exec (P := P) c₁
    ex₁.wb_right (⋄) e83₁ (by rw [e84₁]; exact hW) h88₁ htab₁
  have e83₂ : c₂.nreg 83 = l.length := Ρ hF₂.1 83 (⋄), e83₁
  have e84₂ : c₂.nreg 84 = c₁.nreg 84 := hF₂.1 84 (⋄)
  have htab₂ : ∀ i, i < 2 * l.length →
      c₂.nmem (c₂.nreg 84 + i) = l.getD (i % l.length) 0 := by
    rw [hnm₂, e84₂]; exact htab₁
  -- phase 3
  obtain ⟨c₃, k₃, ex₃, hk₃, hF₃, hnm₃, h88₃, h90₃, hf₃, hb₃⟩ := dirPhase_exec (P := P) c₂
    ex₂.wb_right (⋄) e83₂ (by rw [e84₂, e84₁]; exact hW) h88₂ htab₂
    (by rw [e84₂]; exact hlo₂) (by rw [e84₂]; exact hmin₂.1)
  have e83₃ : c₃.nreg 83 = l.length := Ρ hF₃.1 83 (⋄), e83₂
  have e84₃ : c₃.nreg 84 = c₁.nreg 84 := Ρ hF₃.1 84 (⋄), e84₂
  have htab₃ : ∀ i, i < 2 * l.length →
      c₃.nmem (c₃.nreg 84 + i) = l.getD (i % l.length) 0 := by
    rw [hnm₃, e84₃, ← e84₂]; exact htab₂
  Ξ' e84₂ at hf₃ hb₃
  -- phase 4
  obtain ⟨c₄, k₄, ex₄, hk₄, hF₄, htab₄⟩ := copyPhase_exec (P := P) c₃ ex₃.wb_right e83₃
    (by rw [e84₃, e84₁]; exact hW) h88₃ htab₃ (by rw [e84₃, h90₃]; exact hlo₂)
    (by rw [e84₃, h90₃]; exact hmin₂.1) (by rw [e84₃, h90₃]; exact hf₃)
    (by rw [e84₃, h90₃]; exact hb₃)
  Ξ' e84₃, h90₃ at htab₄
  have hF := pFrame_trans hF₁ (pFrame_trans hF₂ (pFrame_trans hF₃ hF₄))
  have e83₄ : c₄.nreg 83 = l.length := Ρ hF.1 83 (⋄), h83
  have e84₄ : c₄.nreg 84 = c.nreg 84 := hF.1 84 (⋄)
  -- phase 5
  have hlen := length_reorient P l (c₂.nreg 90 - c₁.nreg 84)
  have hM := isMountain_reorient hmount hmin₂
  obtain ⟨c₅, k₅, ex₅, hk₅, ⟨T, hT, hout⟩, hn₅, hr₅, hnm₅, hrm₅⟩ :=
    fragPhase_exec (P := P) (W := W) (l' := reorient P l (c₂.nreg 90 - c₁.nreg 84)) c₄
      ex₄.wb_right (Ρ e83₄, hlen) (by rw [e84₄, hlen]; exact hW) hM
      (fun j hj => by rw [e84₄, hlen, ← e84₁]; exact htab₄ j (by rw [hlen] at hj; exact hj))
  obtain ⟨T', hT', heq⟩ := goodTri_piece_of_mountain hmin₂ ⟨T, hT, rfl⟩
  Ξ' hlen at hk₅
  Ξ' e84₄, hlen at hnm₅
  refine ⟨c₅, _, Exec.seq ex₁ (Exec.seq ex₂ (Exec.seq ex₃ (Exec.seq ex₄ ex₅))), ⋄,
    ⟨T', hT', Ρ hout, heq, hF.2.2.2.2⟩, fun r hr => ?_, fun r hr => ?_, fun a ha => ?_,
    Ρ hrm₅, hF.2.2.2.1⟩
  · Ξ hn₅ r (⋄), hF.1 r (⋄)
  · Ξ hr₅ r (⋄), hF.2.1 r (⋄)
  · Ξ hnm₅ a (⋄), hF.2.2.1 a (by rw [h83]; exact ha)

end main

end

end Chazelle.Final
