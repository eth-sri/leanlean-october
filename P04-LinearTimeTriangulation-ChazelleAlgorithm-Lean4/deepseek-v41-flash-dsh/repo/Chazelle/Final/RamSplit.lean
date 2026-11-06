module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Final.LinkSplit
public import Chazelle.EarClip.RamDet
public import Chazelle.Programs.Tactics

/-!
# Splitting along the diagonal list on the RAM

`splitStmt` realises the linked-structure splitting of `Chazelle.Final.LinkSplit` on the real
RAM, in time linear in `n`.

## Layout

Inputs (natural registers, never written): `nreg 100 = B` (base of the work area),
`nreg 101 = DB` (the diagonal band: diagonal `j < ND` is `(nmem (DB + 2j), nmem (DB + 2j + 1))`),
`nreg 102 = ND`; real register `rreg 100 = σ` (the orientation `orient P`).

With `NN = n + 2 ND` (the final number of nodes) the work area holds the bands

| band | address of entry `i` | contents |
|------|----------------------|----------|
| `vtx` | `B + i` | vertex of node `i` |
| `nxt` | `B + NN + i` | successor of node `i` |
| `prv` | `B + 2 NN + i` | predecessor of node `i` |
| `sib` | `B + 3 NN + i` | next copy of the vertex of node `i`, encoded `+1` (`0` = none) |
| `head` | `B + 4 NN + v` | first copy of vertex `v < n`, encoded `+1` |

Registers written: natural `103 … 139`, real `101 … 117`.  The bases are left in
`nreg 105 = B`, `nreg 106 = B + NN`, `nreg 107 = B + 2 NN`, `nreg 108 = B + 3 NN`,
`nreg 109 = B + 4 NN`, and `nreg 115 = NN` (the number of nodes) at the end.

## The program

```
init:  n := P.n; 0; 1; 2; rreg 117 := 0; NN := n + 2 ND; bases
       for k < n: vtx[k] := k; nxt[k] := k + 1; prv[k] := k - 1; sib[k] := 0; head[k] := k + 1
       nxt[n-1] := 0; prv[0] := n - 1; cnt := n; k := 0
main:  while k < ND:
         a := D[k].1; b := D[k].2
         x := find(a, b); y := find(b, a)        -- scan the copies, wedge test (`nodeWedge`)
         px := prv[x]; ny := nxt[y]; ha := head[a]; hb := head[b]
         vtx[cnt] := a; vtx[cnt+1] := b
         nxt[y] := x; nxt[cnt+1] := ny; nxt[px] := cnt; nxt[cnt] := cnt+1
         prv[x] := y; prv[ny] := cnt+1; prv[cnt] := px; prv[cnt+1] := cnt
         sib[cnt] := ha; sib[cnt+1] := hb; head[a] := cnt+1; head[b] := cnt+2
         cnt := cnt + 2; k := k + 1
find(v, w): res := 0; e := head[v]
         while 0 < e: node := e - 1; if wedge(node, w) then res := node; e := sib[node]
```

## Relation to the abstract algorithm

`MemRel mem B NN n S`: the bands of `mem` hold the structure `S` (`Chain` describes the copy
lists).  The main loop simulates `runState P σ (initState n) D` step by step
(`mainLoop_exec`); its cost is bounded through `runCost`.  The initialisation builds
`initState n` (`initLoop_exec`, `memRel_init`), and `splitStmt_exec` is the specification of the
whole program: cost `≤ 62 * runCost + 63 ND + 16 n + 23`, the structure
`runState P σ (initState n) D` in the work area (`ScanHyp`), and the frame.
-/

namespace Chazelle.Final

open Machine Machine.Stmt Programs
open Chazelle.EarClip (detInto detInto_exec)

@[expose] public section

/-! ### The representation in memory -/

/-- `Chain mem SB e l`: following the encoded pointer `e` (`z + 1` for node `z`, `0` for the
end) through the sibling band at `SB` enumerates the list `l`. -/
def Chain (mem : ℕ → ℕ) (SB : ℕ) : ℕ → List ℕ → Prop
  | e, [] => e = 0
  | e, z :: l => e = z + 1 ∧ Chain mem SB (mem (SB + z)) l

/-- A chain only depends on the sibling entries of its members. -/
theorem chain_congr {mem mem' : ℕ → ℕ} {SB : ℕ} :
    ∀ {e : ℕ} {l : List ℕ}, (∀ z ∈ l, mem' (SB + z) = mem (SB + z)) →
      Chain mem SB e l → Chain mem' SB e l
  | _, [], _, h => h
  | _, z :: l, hs, ⟨h1, h2⟩ => ⟨h1, by
      Ξ hs z List.mem_cons_self
      exact chain_congr (fun z' hz' => hs z' (List.mem_cons_of_mem _ hz')) h2⟩

/-- A chain is determined by its start. -/
theorem chain_unique {mem : ℕ → ℕ} {SB : ℕ} :
    ∀ {e : ℕ} {l l' : List ℕ}, Chain mem SB e l → Chain mem SB e l' → l = l'
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, h, h' => by
      ϴ' Chain at h h'; omega
  | _, _ :: _, [], h, h' => by
      ϴ' Chain at h h'; omega
  | _, z :: l, z' :: l', ⟨h1, h2⟩, ⟨h1', h2'⟩ => by
      have hz : z = z' := ⋄
      subst hz
      Ξ chain_unique h2 h2'

/-- **The memory holds the structure**: the `vtx`, `nxt`, `prv` bands agree with `S` on the
nodes, and the copy lists of the vertices `< n` are chained through the `sib` band from the
`head` band. -/
structure MemRel (mem : ℕ → ℕ) (B NN n : ℕ) (S : LState) : Prop where
  vtx : ∀ z < S.cnt, mem (B + z) = S.vtx z
  nxt : ∀ z < S.cnt, mem (B + NN + z) = S.nxt z
  prv : ∀ z < S.cnt, mem (B + 2 * NN + z) = S.prv z
  cop : ∀ v < n, Chain mem (B + 3 * NN) (mem (B + 4 * NN + v)) (S.cop v)

/-! ### The wedge test -/

/-- Reading the corner of `node = nreg 124` and the target `w = nreg 125`: the coordinates of
`vtx (prv node)` into `rreg 101, 102`, of `vtx node` into `rreg 103, 104`, of
`vtx (nxt node)` into `rreg 105, 106`, of `w` into `rreg 107, 108`.  Exactly `18`
instructions. -/
def wedgeReadStmt : Stmt :=
  block [.addN 129 107 124, .loadN 130 129, .addN 129 105 130, .loadN 130 129,
    .readX 101 130, .readY 102 130,
    .addN 129 105 124, .loadN 130 129, .readX 103 130, .readY 104 130,
    .addN 129 106 124, .loadN 130 129, .addN 129 105 130, .loadN 130 129,
    .readX 105 130, .readY 106 130, .readX 107 125, .readY 108 125]

/-- The three determinants `D = rreg 109`, `L₁ = rreg 110`, `L₂ = rreg 111`, their products
with `σ = rreg 100` into `rreg 114, 115, 116`, and `flag := 0`. -/
def wedgeDetStmt : Stmt :=
  .seq (detInto 109 112 113 101 102 103 104 105 106)
    (.seq (detInto 110 112 113 101 102 103 104 107 108)
      (.seq (detInto 111 112 113 103 104 105 106 107 108)
        (block [.mulR 114 100 109, .mulR 115 100 110, .mulR 116 100 111, .constN 127 0])))

/-- `flag := 1`. -/
def setFlag : Stmt := .instr (.constN 127 1)

/-- The sign logic of `wedgeSign` (with `rreg 117 = 0`). -/
def wedgeLogic : Stmt :=
  .ifLtR 117 114 (.ifLtR 117 115 (.ifLtR 117 116 setFlag .skip) .skip)
    (.ifLtR 114 117 (.ifLtR 117 115 setFlag (.ifLtR 117 116 setFlag .skip))
      (.ifLtR 117 116 setFlag .skip))

/-- **The wedge test on the RAM**: `flag = nreg 127` becomes `1` iff the node `nreg 124` passes
the wedge test towards the vertex `nreg 125`. -/
def wedgeStmt : Stmt := .seq wedgeReadStmt (.seq wedgeDetStmt wedgeLogic)

section Wedge

variable {P : Polygon} {W : ℕ}

/-- Spec of the sign logic of the wedge test. -/
theorem wedgeLogic_exec (c : Config) (hc : WordsBounded W c) (h1 : 1 ≤ W)
    (h117 : c.rreg 117 = 0) (h127 : c.nreg 127 = 0) :
    ∃ c' k, Exec P W wedgeLogic c c' k ∧ k ≤ 8 ∧
      (wedgeSign 1 (c.rreg 114) (c.rreg 115) (c.rreg 116) → c'.nreg 127 = 1) ∧
      (¬ wedgeSign 1 (c.rreg 114) (c.rreg 115) (c.rreg 116) → c'.nreg 127 = 0) ∧
      (∀ r, r ≠ 127 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hset : ∀ K, ∃ c' k, Exec P W setFlag c c' k ∧ k + K ≤ K + 1 ∧ c'.nreg 127 = 1 ∧
      (∀ r, r ≠ 127 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := fun K =>
    ⟨_, 1, Exec.constN hc 127 1 h1, ⋄, ✓, fun r hr => by simp [hr], rfl, rfl, rfl,
      rfl⟩
  unfold wedgeLogic wedgeSign
  ϴ one_mul
  by_cases hD : c.rreg 117 < c.rreg 114
  · Ξ' h117 at hD
    refine spec_ifLtR_true (by rw [h117]; exact hD) ?_
    Ξ ite_eq_left hD
    by_cases hL1 : 0 < c.rreg 115
    · refine spec_ifLtR_true (by rw [h117]; exact hL1) ?_
      by_cases hL2 : 0 < c.rreg 116
      · refine spec_ifLtR_true (by rw [h117]; exact hL2) ?_
        obtain ⟨c', k, ex, hk, hf, hr⟩ := hset 2
        exact ⟨c', k, ex, ⋄, fun _ => hf, fun h => absurd ⟨hL1, hL2⟩ h, hr⟩
      · refine spec_ifLtR_false (by rw [h117]; exact hL2) (spec_skip hc ?_)
        exact ⟨⋄, fun h => absurd h.2 hL2, fun _ => h127, fun _ _ => rfl, rfl, rfl, rfl,
          rfl⟩
    · refine spec_ifLtR_false (by rw [h117]; exact hL1) (spec_skip hc ?_)
      exact ⟨⋄, fun h => absurd h.1 hL1, fun _ => h127, fun _ _ => rfl, rfl, rfl, rfl,
        rfl⟩
  · Ξ' h117 at hD
    refine spec_ifLtR_false (by rw [h117]; exact hD) ?_
    Ξ ite_eq_right hD
    by_cases hD' : c.rreg 114 < 0
    · refine spec_ifLtR_true (by rw [h117]; exact hD') ?_
      Ξ ite_eq_left hD'
      by_cases hL1 : 0 < c.rreg 115
      · refine spec_ifLtR_true (by rw [h117]; exact hL1) ?_
        obtain ⟨c', k, ex, hk, hf, hr⟩ := hset 2
        exact ⟨c', k, ex, ⋄, fun _ => hf, fun h => absurd (Or.inl hL1) h, hr⟩
      · refine spec_ifLtR_false (by rw [h117]; exact hL1) ?_
        by_cases hL2 : 0 < c.rreg 116
        · refine spec_ifLtR_true (by rw [h117]; exact hL2) ?_
          obtain ⟨c', k, ex, hk, hf, hr⟩ := hset 5
          exact ⟨c', k, ex, ⋄, fun _ => hf, fun h => absurd (Or.inr hL2) h, hr⟩
        · refine spec_ifLtR_false (by rw [h117]; exact hL2) (spec_skip hc ?_)
          refine ⟨⋄, fun h => ?_, fun _ => h127, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
          rcases h with h | h
          · exact absurd h hL1
          · exact absurd h hL2
    · refine spec_ifLtR_false (by rw [h117]; exact hD') ?_
      Ξ ite_eq_right hD'
      by_cases hL2 : 0 < c.rreg 116
      · refine spec_ifLtR_true (by rw [h117]; exact hL2) ?_
        obtain ⟨c', k, ex, hk, hf, hr⟩ := hset 4
        exact ⟨c', k, ex, ⋄, fun _ => hf, fun h => absurd hL2 h, hr⟩
      · refine spec_ifLtR_false (by rw [h117]; exact hL2) (spec_skip hc ?_)
        exact ⟨⋄, fun h => absurd h hL2, fun _ => h127, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

/-- The wedge test in terms of the three signed determinants. -/
theorem wedgeTest_iff_sign (σ : ℝ) (p a q x : Point) :
    wedgeTest σ p a q x ↔ wedgeSign 1 (σ * det p a q) (σ * det p a x) (σ * det a q x) := by
  unfold wedgeTest wedgeSign; ϴ one_mul

/-- **Spec of the wedge test.**  With the node `nreg 124`, the target vertex `nreg 125`, the
bases `nreg 105 = VB`, `nreg 106 = NB`, `nreg 107 = PB` and `rreg 117 = 0`: cost `≤ 55`; the
flag `nreg 127` is `1` iff the target passes the `σ = rreg 100` wedge test at the corner
`vtx[prv node] → vtx[node] → vtx[nxt node]`, else `0`; only `nreg 127, 129, 130` and
`rreg 101 … 116` change. -/
theorem wedgeStmt_exec (c : Config) (hc : WordsBounded W c) (h1 : 1 ≤ W)
    (h117 : c.rreg 117 = 0)
    (hA1 : c.nreg 107 + c.nreg 124 ≤ W)
    (hA2 : c.nreg 105 + c.nmem (c.nreg 107 + c.nreg 124) ≤ W)
    (hA3 : c.nreg 105 + c.nreg 124 ≤ W)
    (hA4 : c.nreg 106 + c.nreg 124 ≤ W)
    (hA5 : c.nreg 105 + c.nmem (c.nreg 106 + c.nreg 124) ≤ W) :
    ∃ c' k, Exec P W wedgeStmt c c' k ∧ k ≤ 55 ∧
      (wedgeTest (c.rreg 100) (P.vtx (c.nmem (c.nreg 105 + c.nmem (c.nreg 107 + c.nreg 124))))
          (P.vtx (c.nmem (c.nreg 105 + c.nreg 124)))
          (P.vtx (c.nmem (c.nreg 105 + c.nmem (c.nreg 106 + c.nreg 124))))
          (P.vtx (c.nreg 125)) → c'.nreg 127 = 1) ∧
      (¬ wedgeTest (c.rreg 100) (P.vtx (c.nmem (c.nreg 105 + c.nmem (c.nreg 107 + c.nreg 124))))
          (P.vtx (c.nmem (c.nreg 105 + c.nreg 124)))
          (P.vtx (c.nmem (c.nreg 105 + c.nmem (c.nreg 106 + c.nreg 124))))
          (P.vtx (c.nreg 125)) → c'.nreg 127 = 0) ∧
      (∀ r, r ≠ 127 → r ≠ 129 → r ≠ 130 → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 101 ∨ 116 < r) → c'.rreg r = c.rreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold wedgeStmt wedgeReadStmt wedgeDetStmt
  refine spec_seq ?_
  exec_block
  · exact hA1
  · config_simp; exact hA2
  · config_simp; exact hA3
  · config_simp; exact hA4
  · config_simp; exact hA5
  refine spec_seq (spec_seq (spec_use (detInto_exec (P := P) 109 112 113 101 102 103 104 105 106
    (⌖) (⌖) (⌖)
    (fun r hr => by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) _ ‹_›) ?_))
  rintro c₁ k₁ hk₁ hw₁ ⟨hD, hfr₁, hn₁, hnm₁, hrm₁, hout₁⟩
  refine spec_seq (spec_use (detInto_exec (P := P) 110 112 113 101 102 103 104 107 108
    (⌖) (⌖) (⌖)
    (fun r hr => by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) _ hw₁) ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨hL1, hfr₂, hn₂, hnm₂, hrm₂, hout₂⟩
  refine spec_seq (spec_use (detInto_exec (P := P) 111 112 113 103 104 105 106 107 108
    (⌖) (⌖) (⌖)
    (fun r hr => by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) _ hw₂) ?_)
  rintro c₃ k₃ hk₃ hw₃ ⟨hL2, hfr₃, hn₃, hnm₃, hrm₃, hout₃⟩
  exec_block
  · omega
  refine spec_use (wedgeLogic_exec _ ‹_› h1 ?_ ?_) ?_
  · config_simp
    rw [hfr₃ 117 (⌖) (⌖) (⌖), hfr₂ 117 (⌖) (⌖) (⌖),
      hfr₁ 117 (⌖) (⌖) (⌖)]
    config_simp; exact h117
  · config_simp
  rintro c₄ k₄ hk₄ hw₄ ⟨hy, hn, hnfr, hr₄, hnm₄, hrm₄, hout₄⟩
  config_simp at hy
  config_simp at hn
  -- the real registers after the three determinants
  have e : ∀ r, (r < 101 ∨ 108 < r) → r ≠ 109 → r ≠ 110 → r ≠ 111 → r ≠ 112 → r ≠ 113 →
      c₃.rreg r = c.rreg r := by
    intro r hr h9 h10 h11 h12 h13
    Ξ hfr₃ r h11 h12 h13, hfr₂ r h10 h12 h13, hfr₁ r h9 h12 h13
    config_simp
    simp [show r ≠ 101 by omega, show r ≠ 102 by omega, show r ≠ 103 by omega,
      show r ≠ 104 by omega, show r ≠ 105 by omega, show r ≠ 106 by omega, show r ≠ 107 by omega,
      show r ≠ 108 by omega]
  have e100 : c₃.rreg 100 = c.rreg 100 := e 100 (⋄) (⌖) (⌖) (⌖)
    (⌖) (⌖)
  have eD : c₃.rreg 109 = det (P.vtx (c.nmem (c.nreg 105 + c.nmem (c.nreg 107 + c.nreg 124))))
      (P.vtx (c.nmem (c.nreg 105 + c.nreg 124)))
      (P.vtx (c.nmem (c.nreg 105 + c.nmem (c.nreg 106 + c.nreg 124)))) := by
    rw [hfr₃ 109 (⌖) (⌖) (⌖), hfr₂ 109 (⌖) (⌖) (⌖),
      hD]
    config_simp
  have eL1 : c₃.rreg 110 = det (P.vtx (c.nmem (c.nreg 105 + c.nmem (c.nreg 107 + c.nreg 124))))
      (P.vtx (c.nmem (c.nreg 105 + c.nreg 124))) (P.vtx (c.nreg 125)) := by
    rw [hfr₃ 110 (⌖) (⌖) (⌖), hL1, hfr₁ 101 (⌖) (⌖)
      (⌖), hfr₁ 102 (⌖) (⌖) (⌖), hfr₁ 103 (⌖) (⌖)
      (⌖), hfr₁ 104 (⌖) (⌖) (⌖), hfr₁ 107 (⌖) (⌖)
      (⌖), hfr₁ 108 (⌖) (⌖) (⌖)]
    config_simp
  have eL2 : c₃.rreg 111 = det (P.vtx (c.nmem (c.nreg 105 + c.nreg 124)))
      (P.vtx (c.nmem (c.nreg 105 + c.nmem (c.nreg 106 + c.nreg 124)))) (P.vtx (c.nreg 125)) := by
    rw [hL2, hfr₂ 103 (⌖) (⌖) (⌖), hfr₂ 104 (⌖) (⌖)
      (⌖), hfr₂ 105 (⌖) (⌖) (⌖), hfr₂ 106 (⌖) (⌖)
      (⌖), hfr₂ 107 (⌖) (⌖) (⌖), hfr₂ 108 (⌖) (⌖)
      (⌖), hfr₁ 103 (⌖) (⌖) (⌖), hfr₁ 104 (⌖) (⌖)
      (⌖), hfr₁ 105 (⌖) (⌖) (⌖), hfr₁ 106 (⌖) (⌖)
      (⌖), hfr₁ 107 (⌖) (⌖) (⌖), hfr₁ 108 (⌖) (⌖)
      (⌖)]
    config_simp
  Ξ' eD, eL1, eL2, e100, ← wedgeTest_iff_sign at hy hn
  refine ⟨⋄, hy, hn, fun r h127 h129 h130 => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · Ξ hnfr r h127
    config_simp
    Ξ Machine.upd_other _ _ _ h127, hn₃, hn₂, hn₁
    config_simp
    Θ h129, h130
  · Ξ congrFun hr₄ r
    config_simp
    rw [Machine.upd_other _ _ _ (by omega : r ≠ 116), Machine.upd_other _ _ _ (by omega : r ≠ 115),
      Machine.upd_other _ _ _ (by omega : r ≠ 114)]
    exact e r (⋄) (⋄) (⋄) (⋄) (⋄) (⋄)
  · rw [hnm₄]; config_simp; Ξ hnm₃, hnm₂, hnm₁
  · rw [hrm₄]; config_simp; Ξ hrm₃, hrm₂, hrm₁
  · rw [hout₄]; config_simp; Ξ hout₃, hout₂, hout₁

end Wedge

/-! ### Finding the copy -/

/-- The body of the copy scan: `node := e - 1; wedge; if 0 < flag then res := node;
e := sib[node]`. -/
def findBody : Stmt :=
  .seq (.instr (.subN 124 123 113))
    (.seq wedgeStmt (.seq (.ifLtN 112 127 (.instr (.copyN 126 124)) .skip)
      (block [.addN 129 108 124, .loadN 123 129])))

/-- The copy scan: `while 0 < e do findBody`. -/
def findLoop : Stmt := .whileLtN 112 123 findBody

/-- **Find the copy** of the vertex `v = nreg 128` passing the wedge test towards the vertex
`w = nreg 125`: `res := 0; e := head[v]; findLoop`; the result is in `nreg 126`. -/
def findStmt : Stmt := .seq (block [.constN 126 0, .addN 129 109 128, .loadN 123 129]) findLoop

open Classical in
/-- The wedge predicate of the scan, as a Boolean. -/
noncomputable def wedgeP (P : Polygon) (σ : ℝ) (S : LState) (w : ℕ) : ℕ → Bool :=
  fun z => decide (nodeWedge P σ S z w)

open Classical in
/-- The Boolean wedge predicate. -/
theorem wedgeP_eq_true {P : Polygon} {σ : ℝ} {S : LState} {w z : ℕ} :
    wedgeP P σ S w z = true ↔ nodeWedge P σ S z w := by
  unfold wedgeP; exact decide_eq_true_iff

/-- The standing hypotheses of the scan on a configuration: the band bases, the constants, the
orientation, the memory relation, closure, and the address bound. -/
structure ScanHyp (P : Polygon) (W B NN n : ℕ) (σ : ℝ) (S : LState) (c : Config) : Prop where
  r105 : c.nreg 105 = B
  r106 : c.nreg 106 = B + NN
  r107 : c.nreg 107 = B + 2 * NN
  r108 : c.nreg 108 = B + 3 * NN
  r109 : c.nreg 109 = B + 4 * NN
  r112 : c.nreg 112 = 0
  r113 : c.nreg 113 = 1
  s100 : c.rreg 100 = σ
  s117 : c.rreg 117 = 0
  mem : MemRel c.nmem B NN n S
  closed : Closed S n
  cntNN : S.cnt ≤ NN
  addr : B + 4 * NN + n ≤ W

/-- The scan hypotheses only depend on the registers and memory they mention. -/
theorem ScanHyp.congr {P : Polygon} {W B NN n : ℕ} {σ : ℝ} {S : LState} {c c' : Config}
    (h : ScanHyp P W B NN n σ S c)
    (hn : ∀ r, r = 105 ∨ r = 106 ∨ r = 107 ∨ r = 108 ∨ r = 109 ∨ r = 112 ∨ r = 113 →
      c'.nreg r = c.nreg r)
    (hr : c'.rreg 100 = c.rreg 100 ∧ c'.rreg 117 = c.rreg 117) (hm : c'.nmem = c.nmem) :
    ScanHyp P W B NN n σ S c' where
  r105 := by rw [hn 105 (✓)]; exact h.r105
  r106 := by rw [hn 106 (✓)]; exact h.r106
  r107 := by rw [hn 107 (✓)]; exact h.r107
  r108 := by rw [hn 108 (✓)]; exact h.r108
  r109 := by rw [hn 109 (✓)]; exact h.r109
  r112 := by rw [hn 112 (✓)]; exact h.r112
  r113 := by rw [hn 113 (✓)]; exact h.r113
  s100 := by rw [hr.1]; exact h.s100
  s117 := by rw [hr.2]; exact h.s117
  mem := by rw [hm]; exact h.mem
  closed := h.closed
  cntNN := h.cntNN
  addr := h.addr

section Find

variable {P : Polygon} {W B NN n : ℕ} {σ : ℝ} {S : LState}

/-- The invariant of the scan for the vertex `v` towards `w`, relative to the entry
configuration `c₀`. -/
def FindInv (P : Polygon) (W B NN n : ℕ) (σ : ℝ) (S : LState) (v w : ℕ) (c₀ c : Config) :
    Prop :=
  WordsBounded W c ∧ ScanHyp P W B NN n σ S c ∧ c.nreg 125 = w ∧
    (∀ r, r ≠ 123 → r ≠ 124 → r ≠ 126 → r ≠ 127 → r ≠ 129 → r ≠ 130 → c.nreg r = c₀.nreg r) ∧
    (∀ r, (r < 101 ∨ 116 < r) → c.rreg r = c₀.rreg r) ∧
    c.nmem = c₀.nmem ∧ c.rmem = c₀.rmem ∧ c.output = c₀.output ∧
    ∃ done rest, S.cop v = done ++ rest ∧ Chain c.nmem (B + 3 * NN) (c.nreg 123) rest ∧
      c.nreg 126 = selectLast (wedgeP P σ S w) done 0

open Classical in
/-- The measure of the scan: the length of the remaining chain. -/
noncomputable def chainLen (mem : ℕ → ℕ) (SB e : ℕ) : ℕ :=
  if h : ∃ l, Chain mem SB e l then (Classical.choose h).length else 0

/-- The measure of a chain is its length. -/
theorem chainLen_eq {mem : ℕ → ℕ} {SB e : ℕ} {l : List ℕ} (h : Chain mem SB e l) :
    chainLen mem SB e = l.length := by
  have hex : ∃ l, Chain mem SB e l := ⟨l, h⟩
  unfold chainLen
  Ξ dite_eq_left hex, chain_unique (Classical.choose_spec hex) h

/-- One iteration of the scan. -/
theorem findBody_inv {v w : ℕ} {c₀ c : Config} (hI : FindInv P W B NN n σ S v w c₀ c)
    (ht : c.nreg 112 < c.nreg 123) :
    ∃ c' k, Exec P W findBody c c' k ∧ FindInv P W B NN n σ S v w c₀ c' ∧ k ≤ 60 ∧
      chainLen c₀.nmem (B + 3 * NN) (c'.nreg 123) < chainLen c₀.nmem (B + 3 * NN) (c.nreg 123) := by
  classical
  obtain ⟨hw, hH, h125, hfn, hfr, hnm, hrm, hout, done, rest, hsplit, hchain, hres⟩ := hI
  rw [hH.r112] at ht
  obtain ⟨z, rest', rfl⟩ : ∃ z rest', rest = z :: rest' := by
    cases rest with
    | nil => simp only [Chain] at hchain; omega
    | cons z rest' => exact ⟨z, rest', rfl⟩
  obtain ⟨he, hchain'⟩ := hchain
  have hzmem : z ∈ S.cop v := by rw [hsplit]; simp
  have hz : z < S.cnt := hH.closed.cop v z hzmem
  have hpz := hH.closed.prv z hz
  have hnz := hH.closed.nxt z hz
  have hcnt := hH.cntNN
  have haddr := hH.addr
  have hW1 : 1 ≤ W := by have := hw.1 113; rw [hH.r113] at this; exact this
  unfold findBody
  refine spec_seq (spec_instr (Exec.subN hw 124 123 113) fun hw₁ => ?_)
  have hH₁ := hH.congr (c' := { c with nreg := upd c.nreg 124 (c.nreg 123 - c.nreg 113) })
    (fun r hr => by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) ⟨rfl, rfl⟩ rfl
  have hnode : c.nreg 123 - c.nreg 113 = z := by rw [hH.r113, he]; omega
  refine spec_seq (spec_use (wedgeStmt_exec (P := P) _ hw₁ hW1 hH₁.s117 ?_ ?_ ?_ ?_ ?_) ?_)
  · config_simp; rw [hnode, hH.r107]; omega
  · config_simp; rw [hnode, hH.r107, hH.r105, hH.mem.prv z hz]; omega
  · config_simp; rw [hnode, hH.r105]; omega
  · config_simp; rw [hnode, hH.r106]; omega
  · config_simp; rw [hnode, hH.r106, hH.r105, hH.mem.nxt z hz]; omega
  rintro c₂ k₂ hk₂ hw₂ ⟨hyes, hno, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩
  config_simp at hyes
  config_simp at hno
  rw [hnode, hH.r105, hH.r106, hH.r107, hH.mem.prv z hz, hH.mem.nxt z hz,
    hH.mem.vtx _ hpz, hH.mem.vtx _ hnz, hH.mem.vtx z hz, hH.s100, h125] at hyes hno
  have h112₂ : c₂.nreg 112 = 0 := by
    rw [hfn₂ 112 (⌖) (by decide) (by decide)]; config_simp; exact hH.r112
  have h124₂ : c₂.nreg 124 = z := by
    rw [hfn₂ 124 (⌖) (by decide) (by decide)]; config_simp; exact hnode
  -- the conditional update of the result
  have hcond : ∃ c₃ k₃, Exec P W (.ifLtN 112 127 (.instr (.copyN 126 124)) .skip) c₂ c₃ k₃ ∧
      k₃ ≤ 2 ∧ c₃.nreg 126 = (if wedgeP P σ S w z then z else c.nreg 126) ∧
      (∀ r, r ≠ 126 → c₃.nreg r = c₂.nreg r) ∧ c₃.rreg = c₂.rreg ∧ c₃.nmem = c₂.nmem ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    by_cases hp : nodeWedge P σ S z w
    · have h127 := hyes hp
      refine spec_ifLtN_true (by rw [h112₂, h127]; omega)
        (spec_instr (Exec.copyN hw₂ 126 124) fun _ => ?_)
      refine ⟨⋄, ?_, fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩
      rw [ite_eq_left (wedgeP_eq_true.2 hp)]; config_simp; exact h124₂
    · have h127 := hno hp
      refine spec_ifLtN_false (by rw [h112₂, h127]; omega) (spec_skip hw₂ ?_)
      refine ⟨⋄, ?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
      rw [ite_eq_right (fun h => hp (wedgeP_eq_true.1 h)), hfn₂ 126 (⌖) (by decide) (by decide)]
      config_simp
  refine spec_seq (spec_use hcond ?_)
  rintro c₃ k₃ hk₃ hw₃ ⟨hres₃, hfn₃, hfr₃, hnm₃, hrm₃, hout₃⟩
  have h108₃ : c₃.nreg 108 = B + 3 * NN := by
    rw [hfn₃ 108 (⌖), hfn₂ 108 (by decide) (by decide) (by decide)]
    config_simp; exact hH.r108
  have h124₃ : c₃.nreg 124 = z := by rw [hfn₃ 124 (⌖)]; exact h124₂
  have hmem₃ : c₃.nmem = c.nmem := Ρ hnm₃, hnm₂
  exec_block
  · rw [h108₃, h124₃]; omega
  have e1 : chainLen c₀.nmem (B + 3 * NN) (c.nmem (B + 3 * NN + z)) = rest'.length :=
    chainLen_eq (by rw [← hnm]; exact hchain')
  have e2 : chainLen c₀.nmem (B + 3 * NN) (c.nreg 123) = rest'.length + 1 := by
    rw [chainLen_eq (l := z :: rest') (by rw [← hnm]; exact ⟨he, hchain'⟩)]; simp
  refine ⟨?_, ⋄, ?_⟩
  · refine ⟨‹_›, hH.congr (fun r hr => ?_) ⟨?_, ?_⟩ ?_, ?_, fun r h123 h124 h126 h127 h129 h130 => ?_,
      fun r hr => ?_, ?_, ?_, ?_, done ++ [z], rest', by rw [hsplit]; simp, ?_, ?_⟩
    · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · config_simp
        rw [hfn₃ _ (⌖), hfn₂ _ (by decide) (by decide) (by decide)]
        config_simp
    · config_simp; rw [hfr₃, hfr₂ 100 (⋄)]
    · config_simp; rw [hfr₃, hfr₂ 117 (⋄)]
    · config_simp; exact hmem₃
    · config_simp
      rw [hfn₃ 125 (⌖), hfn₂ 125 (by decide) (by decide) (by decide)]
      config_simp; exact h125
    · config_simp
      rw [Machine.upd_other _ _ _ h123, Machine.upd_other _ _ _ h129, hfn₃ r h126,
        hfn₂ r h127 h129 h130]
      config_simp
      Ξ Machine.upd_other _ _ _ h124
      exact hfn r h123 h124 h126 h127 h129 h130
    · config_simp; rw [hfr₃, hfr₂ r hr, hfr r hr]
    · config_simp; rw [hmem₃, hnm]
    · config_simp; rw [hrm₃, hrm₂, hrm]
    · config_simp; rw [hout₃, hout₂, hout]
    · config_simp
      Ξ hmem₃, h108₃, h124₃
      exact hchain'
    · config_simp
      Ξ hres₃, hres, selectLast_append, selectLast_cons, selectLast_nil
  · config_simp
    Ξ hmem₃, h108₃, h124₃, e1, e2
    omega

/-- **Spec of the copy scan.**  Under the scan hypotheses, with `nreg 128 = v < n` and
`nreg 125 = w`: cost `≤ 62 * (S.cop v).length + 5`, and `nreg 126 = findCopy P σ S v w`; only
`nreg 123, 124, 126, 127, 129, 130` and `rreg 101 … 116` change. -/
theorem findStmt_exec {v w : ℕ} (c : Config) (hc : WordsBounded W c)
    (hH : ScanHyp P W B NN n σ S c) (hv : c.nreg 128 = v) (hvn : v < n) (h125 : c.nreg 125 = w) :
    ∃ c' k, Exec P W findStmt c c' k ∧ k ≤ 62 * (S.cop v).length + 5 ∧
      c'.nreg 126 = findCopy P σ S v w ∧ ScanHyp P W B NN n σ S c' ∧
      (∀ r, r ≠ 123 → r ≠ 124 → r ≠ 126 → r ≠ 127 → r ≠ 129 → r ≠ 130 → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 101 ∨ 116 < r) → c'.rreg r = c.rreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have haddr := hH.addr
  unfold findStmt findLoop
  refine spec_seq ?_
  exec_block
  · omega
  · config_simp; rw [hH.r109, hv]; omega
  set c₁ : Config := { c with nreg := (upd (upd (upd c.nreg 126 0) 129
    (c.nreg 109 + c.nreg 128)) 123 (c.nmem (c.nreg 109 + c.nreg 128))) } with hc₁
  have hH₁ : ScanHyp P W B NN n σ S c₁ := hH.congr (fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [hc₁] <;> config_simp)
    ⟨rfl, rfl⟩ rfl
  have hchain₁ : Chain c₁.nmem (B + 3 * NN) (c₁.nreg 123) (S.cop v) := by
    simp only [hc₁]; config_simp; rw [hH.r109, hv]; exact hH.mem.cop v hvn
  have hI₀ : FindInv P W B NN n σ S v w c₁ c₁ := by
    refine ⟨‹_›, hH₁, by simp only [hc₁]; config_simp; exact h125, fun _ _ _ _ _ _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl, [], S.cop v, rfl, hchain₁, ?_⟩
    simp only [hc₁]; config_simp; rfl
  refine spec_imp (Exec.whileLtN_bounded (FindInv P W B NN n σ S v w c₁)
    (fun d => chainLen c₁.nmem (B + 3 * NN) (d.nreg 123)) 60 (fun _ h => h.1)
    (fun d hI ht => findBody_inv hI ht) hI₀) ?_
  rintro c' k ⟨⟨hw', hH', h125', hfn', hfr', hnm', hrm', hout', done, rest, hsplit, hchain, hres⟩,
    hexit, hk⟩
  have hrest : rest = [] := by
    Ξ' hH'.r112 at hexit
    cases rest with
    | nil => rfl
    | cons z l => exact absurd (by rw [hchain.1]; omega) hexit
  subst hrest
  Ξ' List.append_nil at hsplit
  have hμ : chainLen c₁.nmem (B + 3 * NN) (c₁.nreg 123) = (S.cop v).length :=
    chainLen_eq hchain₁
  refine ⟨by rw [hμ] at hk; omega, by rw [hres, ← hsplit]; rfl, hH', ?_, ?_, ?_, ?_, ?_⟩
  · intro r h123 h124 h126 h127 h129 h130
    Ξ hfn' r h123 h124 h126 h127 h129 h130
    ϴ hc₁
    Ξ Machine.upd_other _ _ _ h123, Machine.upd_other _ _ _ h129, Machine.upd_other _ _ _ h126
  · intro r hr; Ξ hfr' r hr
  · Ξ hnm'
  · Ξ hrm'
  · Ξ hout'

end Find

/-! ### The surgery in memory -/

/-- The memory after the surgery stores, in program order (`N = cnt`, `px = prv[x]`,
`ny = nxt[y]`, `ha = head[a]`, `hb = head[b]`). -/
def surgMem (mem : ℕ → ℕ) (B NN a b x y px ny N ha hb : ℕ) : ℕ → ℕ :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd mem
    (B + N) a) (B + (N + 1)) b)
    (B + NN + y) x) (B + NN + (N + 1)) ny) (B + NN + px) N) (B + NN + N) (N + 1))
    (B + 2 * NN + x) y) (B + 2 * NN + ny) (N + 1)) (B + 2 * NN + N) px) (B + 2 * NN + (N + 1)) N)
    (B + 3 * NN + N) ha) (B + 3 * NN + (N + 1)) hb)
    (B + 4 * NN + a) (N + 1)) (B + 4 * NN + b) (N + 1 + 1)

/-- The bands of the memory after the surgery stores. -/
theorem surgMem_bands (mem : ℕ → ℕ) {B NN a b x y px ny N ha hb : ℕ} (hN : N + 2 ≤ NN)
    (hab : a ≠ b) (hx : x < N) (hy : y < N) (hpx : px < N) (hny : ny < N) :
    (∀ z < N + 2, surgMem mem B NN a b x y px ny N ha hb (B + z) =
      upd (upd (fun t => mem (B + t)) N a) (N + 1) b z) ∧
    (∀ z < N + 2, surgMem mem B NN a b x y px ny N ha hb (B + NN + z) =
      upd (upd (upd (upd (fun t => mem (B + NN + t)) y x) (N + 1) ny) px N) N (N + 1) z) ∧
    (∀ z < N + 2, surgMem mem B NN a b x y px ny N ha hb (B + 2 * NN + z) =
      upd (upd (upd (upd (fun t => mem (B + 2 * NN + t)) x y) ny (N + 1)) N px) (N + 1) N z) ∧
    (∀ z < N, surgMem mem B NN a b x y px ny N ha hb (B + 3 * NN + z) = mem (B + 3 * NN + z)) ∧
    surgMem mem B NN a b x y px ny N ha hb (B + 3 * NN + N) = ha ∧
    surgMem mem B NN a b x y px ny N ha hb (B + 3 * NN + (N + 1)) = hb ∧
    surgMem mem B NN a b x y px ny N ha hb (B + 4 * NN + a) = N + 1 ∧
    surgMem mem B NN a b x y px ny N ha hb (B + 4 * NN + b) = N + 1 + 1 ∧
    (∀ v, v ≠ a → v ≠ b → surgMem mem B NN a b x y px ny N ha hb (B + 4 * NN + v) =
      mem (B + 4 * NN + v)) := by
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, ?_, ?_, ?_, ?_,
    fun v hva hvb => ?_⟩ <;>
  · unfold surgMem
    repeat' (first | omega | rfl | (rw [Machine.upd_apply]; split_ifs))

/-- The surgery stores stay in the work area. -/
theorem surgMem_frame (mem : ℕ → ℕ) {B NN n a b x y px ny N ha hb : ℕ} (hN : N + 2 ≤ NN)
    (hA : a < n) (hB : b < n) (hx : x < N) (hy : y < N) (hpx : px < N) (hny : ny < N) :
    ∀ t, (t < B ∨ B + 4 * NN + n ≤ t) → surgMem mem B NN a b x y px ny N ha hb t = mem t := by
  intro t ht
  unfold surgMem
  repeat' (first | omega | rfl | (rw [Machine.upd_apply]; split_ifs))

/-- **The memory relation passes through the surgery stores.** -/
theorem memRel_surgery {mem : ℕ → ℕ} {B NN n : ℕ} {S : LState} (hM : MemRel mem B NN n S)
    (hS : Closed S n) (hN : S.cnt + 2 ≤ NN) {a b x y : ℕ} (ha : a < n) (hb : b < n)
    (hab : a ≠ b) (hx : x < S.cnt) (hy : y < S.cnt) :
    MemRel (surgMem mem B NN a b x y (S.prv x) (S.nxt y) S.cnt (mem (B + 4 * NN + a))
      (mem (B + 4 * NN + b))) B NN n (surgery S a b x y) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := surgMem_bands mem (B := B) (ha := mem (B + 4 * NN + a))
    (hb := mem (B + 4 * NN + b)) hN hab hx hy (hS.prv x hx) (hS.nxt y hy)
  have hvtx := fun z hz => hM.vtx z hz
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, fun v hv => ?_⟩
  · have hz' : z < S.cnt + 2 := hz
    Ξ e1 z hz'
    show _ = upd (upd S.vtx S.cnt a) (S.cnt + 1) b z
    ϴ Machine.upd_apply
    split_ifs
    · rfl
    · rfl
    · exact hM.vtx z (⋄)
  · have hz' : z < S.cnt + 2 := hz
    Ξ e2 z hz'
    show _ = upd (upd (upd (upd S.nxt y x) (S.cnt + 1) (S.nxt y)) (S.prv x) S.cnt) S.cnt
      (S.cnt + 1) z
    ϴ Machine.upd_apply
    split_ifs
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hM.nxt z (⋄)
  · have hz' : z < S.cnt + 2 := hz
    Ξ e3 z hz'
    show _ = upd (upd (upd (upd S.prv x y) (S.nxt y) (S.cnt + 1)) S.cnt (S.prv x)) (S.cnt + 1)
      S.cnt z
    ϴ Machine.upd_apply
    split_ifs
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hM.prv z (⋄)
  · show Chain _ _ _ (upd (upd S.cop a (S.cnt :: S.cop a)) b ((S.cnt + 1) :: S.cop b) v)
    have hsib : ∀ w, ∀ z ∈ S.cop w, surgMem mem B NN a b x y (S.prv x) (S.nxt y) S.cnt
        (mem (B + 4 * NN + a)) (mem (B + 4 * NN + b)) (B + 3 * NN + z) = mem (B + 3 * NN + z) :=
      fun w z hz => e4 z (hS.cop w z hz)
    by_cases hvb : v = b
    · subst hvb
      Ξ Machine.upd_same, e8
      refine ⟨rfl, ?_⟩
      Ξ e6
      exact chain_congr (fun z hz => hsib v z hz) (hM.cop v hb)
    · Ξ Machine.upd_other _ _ _ hvb
      by_cases hva : v = a
      · subst hva
        Ξ Machine.upd_same, e7
        refine ⟨rfl, ?_⟩
        Ξ e5
        exact chain_congr (fun z hz => hsib v z hz) (hM.cop v ha)
      · Ξ Machine.upd_other _ _ _ hva, e9 v hva hvb
        exact chain_congr (fun z hz => hsib v z hz) (hM.cop v hv)

/-! ### One diagonal -/

/-- Load the diagonal `k = nreg 116`: `a := D[2k]`, `b := D[2k+1]` (into `nreg 117, 118`), and
set up the first scan (`v := a`, `w := b`).  Exactly `7` instructions. -/
def mainLoadStmt : Stmt :=
  block [.addN 129 101 116, .addN 129 129 116, .loadN 117 129, .addN 129 129 113, .loadN 118 129,
    .copyN 128 117, .copyN 125 118]

/-- `x := res` and set up the second scan (`v := b`, `w := a`).  Exactly `3` instructions. -/
def mainMidStmt : Stmt := block [.copyN 119 126, .copyN 128 118, .copyN 125 117]

/-- `y := res` and the surgery (see the module docstring), then `cnt := cnt + 2`,
`k := k + 1`.  Exactly `41` instructions. -/
def mainSurgStmt : Stmt :=
  block [.copyN 120 126,
    .addN 129 107 119, .loadN 121 129, .addN 129 106 120, .loadN 122 129,
    .addN 129 109 117, .loadN 130 129, .addN 129 109 118, .loadN 137 129,
    .addN 138 115 113, .addN 139 138 113,
    .addN 129 105 115, .storeN 129 117, .addN 129 105 138, .storeN 129 118,
    .addN 129 106 120, .storeN 129 119, .addN 129 106 138, .storeN 129 122,
    .addN 129 106 121, .storeN 129 115, .addN 129 106 115, .storeN 129 138,
    .addN 129 107 119, .storeN 129 120, .addN 129 107 122, .storeN 129 138,
    .addN 129 107 115, .storeN 129 121, .addN 129 107 138, .storeN 129 115,
    .addN 129 108 115, .storeN 129 130, .addN 129 108 138, .storeN 129 137,
    .addN 129 109 117, .storeN 129 138, .addN 129 109 118, .storeN 129 139,
    .copyN 115 139, .addN 116 116 113]

/-- **One diagonal**: load it, find the two copies, and split. -/
def mainBody : Stmt :=
  .seq mainLoadStmt (.seq findStmt (.seq mainMidStmt (.seq findStmt mainSurgStmt)))

/-- **The main loop**: `while k < ND do mainBody`. -/
def mainLoop : Stmt := .whileLtN 116 102 mainBody

section Main

variable {P : Polygon} {W B NN n : ℕ} {σ : ℝ} {S : LState}

/-- **Spec of the surgery block.** -/
theorem mainSurg_exec {a b x y : ℕ} (c : Config) (hc : WordsBounded W c)
    (hH : ScanHyp P W B NN n σ S c) (h115 : c.nreg 115 = S.cnt) (h117 : c.nreg 117 = a)
    (h118 : c.nreg 118 = b) (h119 : c.nreg 119 = x) (h126 : c.nreg 126 = y) (ha : a < n)
    (hb : b < n) (hx : x < S.cnt) (hy : y < S.cnt) (hcnt : S.cnt + 2 ≤ NN)
    (h116W : c.nreg 116 + 1 ≤ W) :
    ∃ c' k, Exec P W mainSurgStmt c c' k ∧ k ≤ 41 ∧
      c'.nmem = surgMem c.nmem B NN a b x y (S.prv x) (S.nxt y) S.cnt
        (c.nmem (B + 4 * NN + a)) (c.nmem (B + 4 * NN + b)) ∧
      c'.nreg 115 = S.cnt + 2 ∧ c'.nreg 116 = c.nreg 116 + 1 ∧
      (∀ r, (r < 115 ∨ 139 < r) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hpx := hH.closed.prv x hx
  have hny := hH.closed.nxt y hy
  have haddr := hH.addr
  have e1 := hH.mem.prv x hx
  have e2 := hH.mem.nxt y hy
  have h105 := hH.r105
  have h106 := hH.r106
  have h107 := hH.r107
  have h108 := hH.r108
  have h109 := hH.r109
  have h113 := hH.r113
  unfold mainSurgStmt
  exec_block
  all_goals first
    | (config_simp; simp only [h105, h106, h107, h108, h109, h113, h115, h117, h118, h119, h126,
        e1, e2]; omega)
    | skip
  refine ⟨⋄, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · config_simp
    ϴ h105, h106, h107, h108, h109, h113, h115, h117, h118, h119, h126, e1, e2
    rfl
  · config_simp; ϴ h113, h115
  · config_simp; ϴ h113
  · config_simp
    simp [show r ≠ 115 by omega, show r ≠ 116 by omega, show r ≠ 120 by omega, show r ≠ 121 by omega,
      show r ≠ 122 by omega, show r ≠ 129 by omega, show r ≠ 130 by omega, show r ≠ 137 by omega,
      show r ≠ 138 by omega, show r ≠ 139 by omega]

/-- **Spec of one diagonal.**  From a configuration holding the structure `S` (with `cnt` nodes
in `nreg 115`), the diagonal index `k = nreg 116` and the diagonal `d` in the diagonal band:
the body leaves the structure `step P σ S d`, `cnt + 2`, `k + 1`, at cost
`≤ 62 * ((S.cop d.1).length + (S.cop d.2).length) + 61`; it writes only the natural registers
`115 … 139`, the real registers `101 … 116` and the work area `B … B + 4 NN + n - 1`. -/
theorem mainBody_exec {d : ℕ × ℕ} {k DB : ℕ} (c : Config) (hc : WordsBounded W c)
    (hH : ScanHyp P W B NN n σ S c) (h101 : c.nreg 101 = DB) (h115 : c.nreg 115 = S.cnt)
    (h116 : c.nreg 116 = k) (hd1 : c.nmem (DB + k + k) = d.1)
    (hd2 : c.nmem (DB + k + k + 1) = d.2) (ha : d.1 < n) (hb : d.2 < n) (hab : d.1 ≠ d.2)
    (hcnt : S.cnt + 2 ≤ NN) (hDB : DB + k + k + 1 ≤ W) (hkW : k + 1 ≤ W) :
    ∃ c' k', Exec P W mainBody c c' k' ∧
      k' ≤ 62 * ((S.cop d.1).length + (S.cop d.2).length) + 61 ∧
      ScanHyp P W B NN n σ (step P σ S d) c' ∧ c'.nreg 115 = S.cnt + 2 ∧ c'.nreg 116 = k + 1 ∧
      (∀ r, (r < 115 ∨ 139 < r) → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 101 ∨ 116 < r) → c'.rreg r = c.rreg r) ∧
      (∀ t, (t < B ∨ B + 4 * NN + n ≤ t) → c'.nmem t = c.nmem t) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hS := hH.closed
  have hx := findCopy_lt (P := P) (σ := σ) hS d.1 d.2
  have hy := findCopy_lt (P := P) (σ := σ) hS d.2 d.1
  unfold mainBody mainLoadStmt
  refine spec_seq ?_
  exec_block
  · rw [h101, h116]; omega
  · config_simp; rw [h101, h116]; omega
  · config_simp; rw [h101, h116, hH.r113]; omega
  -- first scan
  refine spec_seq (spec_use (findStmt_exec (P := P) (v := d.1) (w := d.2) _ ‹_›
    (hH.congr (fun r hr => ?_) ⟨rfl, rfl⟩ rfl) ?_ ha ?_) ?_)
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> config_simp
  · config_simp; rw [h101, h116, hd1]
  · config_simp; rw [h101, h116, hH.r113, hd2]
  rintro c₂ k₂ hk₂ hw₂ ⟨hres₂, hH₂, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩
  config_simp at hfn₂
  config_simp at hfr₂
  config_simp at hnm₂
  config_simp at hrm₂
  config_simp at hout₂
  have h117₂ : c₂.nreg 117 = d.1 := by
    rw [hfn₂ 117 (⌖) (by decide) (by decide) (by decide) (by decide) (by decide)]
    config_simp; rw [h101, h116, hd1]
  have h118₂ : c₂.nreg 118 = d.2 := by
    rw [hfn₂ 118 (⌖) (by decide) (by decide) (by decide) (by decide) (by decide)]
    config_simp; rw [h101, h116, hH.r113, hd2]
  unfold mainMidStmt
  refine spec_seq ?_
  exec_block
  -- second scan
  refine spec_seq (spec_use (findStmt_exec (P := P) (v := d.2) (w := d.1) _ ‹_›
    (hH₂.congr (fun r hr => ?_) ⟨rfl, rfl⟩ rfl) ?_ hb ?_) ?_)
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> config_simp
  · config_simp; exact h118₂
  · config_simp; exact h117₂
  rintro c₄ k₄ hk₄ hw₄ ⟨hres₄, hH₄, hfn₄, hfr₄, hnm₄, hrm₄, hout₄⟩
  config_simp at hfn₄
  config_simp at hfr₄
  config_simp at hnm₄
  config_simp at hrm₄
  config_simp at hout₄
  have hreg₄ : ∀ r, r ≠ 117 → r ≠ 118 → r ≠ 119 → r ≠ 123 → r ≠ 124 → r ≠ 125 → r ≠ 126 →
      r ≠ 127 → r ≠ 128 → r ≠ 129 → r ≠ 130 → c₄.nreg r = c.nreg r := by
    intro r h117 h118 h119 h123 h124 h125 h126 h127 h128 h129 h130
    Ξ hfn₄ r h123 h124 h126 h127 h129 h130
    rw [Machine.upd_other _ _ _ h125, Machine.upd_other _ _ _ h128,
      Machine.upd_other _ _ _ h119, hfn₂ r h123 h124 h126 h127 h129 h130]
    Θ h117, h118, h125, h128, h129
  have hmem₄ : c₄.nmem = c.nmem := Ρ hnm₄, hnm₂
  have h115₄ : c₄.nreg 115 = S.cnt := by
    rw [hreg₄ 115 (⌖) (by decide) (by decide) (by decide) (by decide) (by decide)
      (⌖) (by decide) (by decide) (by decide) (by decide), h115]
  have h117₄ : c₄.nreg 117 = d.1 := by
    rw [hfn₄ 117 (⌖) (by decide) (by decide) (by decide) (by decide) (by decide)]
    config_simp; exact h117₂
  have h118₄ : c₄.nreg 118 = d.2 := by
    rw [hfn₄ 118 (⌖) (by decide) (by decide) (by decide) (by decide) (by decide)]
    config_simp; exact h118₂
  have h119₄ : c₄.nreg 119 = findCopy P σ S d.1 d.2 := by
    rw [hfn₄ 119 (⌖) (by decide) (by decide) (by decide) (by decide) (by decide)]
    config_simp; exact hres₂
  have h116₄ : c₄.nreg 116 = k := by
    rw [hreg₄ 116 (⌖) (by decide) (by decide) (by decide) (by decide) (by decide)
      (⌖) (by decide) (by decide) (by decide) (by decide), h116]
  refine spec_use (mainSurg_exec (a := d.1) (b := d.2) (x := findCopy P σ S d.1 d.2)
    (y := findCopy P σ S d.2 d.1) c₄ hw₄ hH₄ h115₄ h117₄ h118₄ h119₄ hres₄ ha hb hx hy hcnt
    (by rw [h116₄]; exact hkW)) ?_
  rintro c₅ k₅ hk₅ hw₅ ⟨hnm₅, h115₅, h116₅, hfn₅, hfr₅, hrm₅, hout₅⟩
  have hmemrel := memRel_surgery (hH₄.mem) hS hcnt ha hb hab hx hy
  rw [← hnm₅] at hmemrel
  have hreg₅ : ∀ r, (r < 115 ∨ 139 < r) → c₅.nreg r = c.nreg r := fun r hr => by
    rw [hfn₅ r hr, hreg₄ r (⋄) (by omega) (by omega) (by omega) (by omega) (by omega)
      (⋄) (by omega) (by omega) (by omega) (by omega)]
  have hrreg₅ : ∀ r, (r < 101 ∨ 116 < r) → c₅.rreg r = c.rreg r := fun r hr => by
    rw [hfr₅, hfr₄ r hr]; rw [hfr₂ r hr]
  refine ⟨⋄, ?_, by rw [h115₅], by rw [h116₅, h116₄], hreg₅, hrreg₅, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmemrel, hS.step ha hb, ?_, hH.addr⟩
    · rw [hreg₅ 105 (⋄)]; exact hH.r105
    · rw [hreg₅ 106 (⋄)]; exact hH.r106
    · rw [hreg₅ 107 (⋄)]; exact hH.r107
    · rw [hreg₅ 108 (⋄)]; exact hH.r108
    · rw [hreg₅ 109 (⋄)]; exact hH.r109
    · rw [hreg₅ 112 (⋄)]; exact hH.r112
    · rw [hreg₅ 113 (⋄)]; exact hH.r113
    · rw [hrreg₅ 100 (⋄)]; exact hH.s100
    · rw [hrreg₅ 117 (⋄)]; exact hH.s117
    · show S.cnt + 2 ≤ NN; exact hcnt
  · intro t ht
    Ξ hnm₅, hmem₄
    exact surgMem_frame c.nmem hcnt ha hb hx hy (hS.prv _ hx) (hS.nxt _ hy) t ht
  · rw [hrm₅, hrm₄]; rw [hrm₂]
  · rw [hout₅, hout₄]; rw [hout₂]

/-! ### The main loop -/

/-- The invariant of the main loop, relative to its entry configuration `c₀`: after `k = nreg 116`
diagonals the memory holds `runState P σ (initState n) (D.take k)`, `cnt = n + 2 k`, and the
frame. -/
def MainInv (P : Polygon) (W B NN n DB ND : ℕ) (σ : ℝ) (D : List (ℕ × ℕ)) (c₀ c : Config) :
    Prop :=
  WordsBounded W c ∧ c.nreg 116 ≤ ND ∧
    ScanHyp P W B NN n σ (runState P σ (initState n) (D.take (c.nreg 116))) c ∧
    c.nreg 115 = n + 2 * c.nreg 116 ∧ c.nreg 101 = DB ∧ c.nreg 102 = ND ∧
    (∀ r, (r < 115 ∨ 139 < r) → c.nreg r = c₀.nreg r) ∧
    (∀ r, (r < 101 ∨ 116 < r) → c.rreg r = c₀.rreg r) ∧
    (∀ t, (t < B ∨ B + 4 * NN + n ≤ t) → c.nmem t = c₀.nmem t) ∧
    c.rmem = c₀.rmem ∧ c.output = c₀.output

/-- The potential of the main loop: `62` per wedge test still to come (`runCost`) plus `63` per
diagonal still to come. -/
noncomputable def mainPot (P : Polygon) (n ND : ℕ) (σ : ℝ) (D : List (ℕ × ℕ)) (c : Config) : ℕ :=
  62 * runCost P σ (runState P σ (initState n) (D.take (c.nreg 116))) (D.drop (c.nreg 116)) +
    63 * (ND - c.nreg 116)

/-- The run on a prefix one longer is one more step. -/
theorem runState_take_succ (σ : ℝ) (S : LState) {D : List (ℕ × ℕ)} {k : ℕ} (hk : k < D.length) :
    runState P σ S (D.take (k + 1)) = step P σ (runState P σ S (D.take k)) D[k] := by
  Ξ List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, runState_append
  rfl

/-- **Spec of the main loop.** -/
theorem mainLoop_exec {DB ND : ℕ} {D : List (ℕ × ℕ)} (hlen : D.length = ND)
    (hNN : NN = n + 2 * ND) (hD : ∀ d ∈ D, d.1 < n ∧ d.2 < n ∧ d.1 ≠ d.2)
    (_hn : 0 < n) (c₀ : Config) (hI : MainInv P W B NN n DB ND σ D c₀ c₀)
    (hband : ∀ j < ND, c₀.nmem (DB + 2 * j) = (D.getD j (0, 0)).1 ∧
      c₀.nmem (DB + 2 * j + 1) = (D.getD j (0, 0)).2)
    (hDB : DB + 2 * ND ≤ B ∨ B + 4 * NN + n ≤ DB) (hDBW : DB + 2 * ND ≤ W) (hNW : ND + 1 ≤ W) :
    ∃ c' k, Exec P W mainLoop c₀ c' k ∧ MainInv P W B NN n DB ND σ D c₀ c' ∧
      c'.nreg 116 = ND ∧ k ≤ mainPot P n ND σ D c₀ + 2 := by
  have hbody : ∀ c, MainInv P W B NN n DB ND σ D c₀ c → c.nreg 116 < c.nreg 102 →
      ∃ c' k, Exec P W mainBody c c' k ∧ MainInv P W B NN n DB ND σ D c₀ c' ∧
        mainPot P n ND σ D c' + k + 2 ≤ mainPot P n ND σ D c := by
    intro c ⟨hw, hkND, hH, h115, h101, h102, hfn, hfr, hnm, hrm, hout⟩ ht
    Ξ' h102 at ht
    set k := c.nreg 116 with hk
    have hkD : k < D.length := ⋄
    set S := runState P σ (initState n) (D.take k) with hSdef
    have hcnt : S.cnt = n + 2 * k := by
      rw [hSdef, cnt_runState, List.length_take]; show n + 2 * min k D.length = _
      Ξ min_eq_left (⋄)
    obtain ⟨hd1n, hd2n, hdne⟩ := hD (D[k]) (List.getElem_mem hkD)
    have hb := hband k ht
    Ξ' List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkD, Option.getD_some at hb
    have hdk1 : c.nmem (DB + k + k) = (D[k]).1 := by
      rw [hnm _ (⋄), show DB + k + k = DB + 2 * k by omega]; exact hb.1
    have hdk2 : c.nmem (DB + k + k + 1) = (D[k]).2 := by
      rw [hnm _ (⋄), show DB + k + k + 1 = DB + 2 * k + 1 by omega]; exact hb.2
    obtain ⟨c', k', ex, hk', hH', h115', h116', hfn', hfr', hnm', hrm', hout'⟩ :=
      mainBody_exec (P := P) (d := D[k]) (k := k) (DB := DB) c hw hH h101 (Ρ h115, hcnt)
        rfl hdk1 hdk2 hd1n hd2n hdne (⋄) (⋄) (⋄)
    refine ⟨c', k', ex, ⟨ex.wb_right, ⋄, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [h116', runState_take_succ σ _ hkD]; exact hH'
    · rw [h115', h116', hcnt]; ring
    · rw [hfn' 101 (⋄)]; exact h101
    · rw [hfn' 102 (⋄)]; exact h102
    · intro r hr; Ξ hfn' r hr, hfn r hr
    · intro r hr; Ξ hfr' r hr, hfr r hr
    · intro t ht; Ξ hnm' t ht, hnm t ht
    · Ξ hrm', hrm
    · Ξ hout', hout
    · unfold mainPot
      rw [h116', ← hk, runState_take_succ σ _ hkD, ← hSdef, List.drop_eq_getElem_cons hkD,
        runCost_cons]
      have : ND - k = ND - (k + 1) + 1 := ⋄
      Ξ this
      nlinarith
  obtain ⟨c', k, ex, hI', hexit, hk⟩ := Exec.whileLtN_potential (MainInv P W B NN n DB ND σ D c₀)
    (mainPot P n ND σ D) (fun _ h => h.1) hbody hI
  refine ⟨c', k, ex, hI', ?_, hk⟩
  have := hI'.2.1
  Ξ' hI'.2.2.2.2.2.1 at hexit
  omega

end Main

/-! ### Initialisation -/

/-- `n := P.n`, the constants `0, 1, 2`, `rreg 117 := 0`, `NN := n + 2 ND`, the band bases,
`k := 0`.  Exactly `13` instructions. -/
def initBlock : Stmt :=
  block [.inputSize 103, .constN 112 0, .constN 113 1, .constN 114 2, .constR 117 0,
    .addN 104 103 102, .addN 104 104 102,
    .copyN 105 100, .addN 106 105 104, .addN 107 106 104, .addN 108 107 104, .addN 109 108 104,
    .constN 116 0]

/-- One vertex `k = nreg 116`: `vtx[k] := k; nxt[k] := k + 1; prv[k] := k - 1; sib[k] := 0;
head[k] := k + 1; k := k + 1`.  Exactly `14` instructions. -/
def initBody : Stmt :=
  block [.addN 129 105 116, .storeN 129 116,
    .addN 130 116 113, .addN 129 106 116, .storeN 129 130,
    .subN 130 116 113, .addN 129 107 116, .storeN 129 130,
    .addN 129 108 116, .storeN 129 112,
    .addN 130 116 113, .addN 129 109 116, .storeN 129 130,
    .addN 116 116 113]

/-- `while k < n do initBody`. -/
def initLoop : Stmt := .whileLtN 116 103 initBody

/-- `nxt[n-1] := 0; prv[0] := n - 1; cnt := n; k := 0`.  Exactly `6` instructions. -/
def initFix : Stmt :=
  block [.subN 130 103 113, .addN 129 106 130, .storeN 129 112, .storeN 107 130,
    .copyN 115 103, .constN 116 0]

/-- **The splitting program** (without the output pass): initialisation, then the main loop. -/
def splitStmt : Stmt := .seq initBlock (.seq initLoop (.seq initFix mainLoop))

section Init

variable {P : Polygon} {W : ℕ}

/-- Name the starting configuration of a spec goal. -/
theorem spec_name {s : Stmt} {c : Config} {Q : Config → ℕ → Prop}
    (h : ∀ c₀, c₀ = c → ∃ c' k, Exec P W s c₀ c' k ∧ Q c' k) :
    ∃ c' k, Exec P W s c c' k ∧ Q c' k := h c rfl

/-- The invariant of the initialisation loop. -/
def InitInv (P : Polygon) (W B NN : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 116 ≤ P.n ∧ c.nreg 103 = P.n ∧ c.nreg 105 = B ∧
    c.nreg 106 = B + NN ∧ c.nreg 107 = B + 2 * NN ∧ c.nreg 108 = B + 3 * NN ∧
    c.nreg 109 = B + 4 * NN ∧ c.nreg 112 = 0 ∧ c.nreg 113 = 1 ∧
    (∀ z < c.nreg 116, c.nmem (B + z) = z ∧ c.nmem (B + NN + z) = z + 1 ∧
      c.nmem (B + 2 * NN + z) = z - 1 ∧ c.nmem (B + 3 * NN + z) = 0 ∧
      c.nmem (B + 4 * NN + z) = z + 1) ∧
    (∀ r, r ≠ 116 → r ≠ 129 → r ≠ 130 → c.nreg r = c₀.nreg r) ∧ c.rreg = c₀.rreg ∧
    (∀ t, (t < B ∨ B + 4 * NN + P.n ≤ t) → c.nmem t = c₀.nmem t) ∧
    c.rmem = c₀.rmem ∧ c.output = c₀.output

/-- One iteration of the initialisation loop preserves `InitInv`. -/
theorem initBody_inv {B NN : ℕ} (hNN : P.n ≤ NN) (hW : B + 4 * NN + P.n ≤ W) {c₀ c : Config}
    (hI : InitInv P W B NN c₀ c) (ht : c.nreg 116 < c.nreg 103) :
    ∃ c' k, Exec P W initBody c c' k ∧ InitInv P W B NN c₀ c' ∧ k ≤ 14 ∧
      P.n - c'.nreg 116 < P.n - c.nreg 116 := by
  obtain ⟨hw, hk, h103, h105, h106, h107, h108, h109, h112, h113, hbands, hfn, hfr, hnm, hrm,
    hout⟩ := hI
  Ξ' h103 at ht
  set k := c.nreg 116 with hkdef
  unfold initBody
  exec_block
  all_goals first
    | (config_simp; simp only [h105, h106, h107, h108, h109, h112, h113]; omega)
    | skip
  refine ⟨⟨‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⋄, ?_⟩
  · config_simp; rw [h113]; omega
  · config_simp; exact h103
  · config_simp; exact h105
  · config_simp; exact h106
  · config_simp; exact h107
  · config_simp; exact h108
  · config_simp; exact h109
  · config_simp; exact h112
  · config_simp; exact h113
  · intro z hz
    config_simp at hz
    Ξ' h113 at hz
    config_simp
    ϴ h105, h106, h107, h108, h109, h112, h113
    have hb := hbands z
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · repeat' (first | omega | (rw [Machine.upd_apply]; split_ifs))
  · intro r h116 h129 h130
    config_simp
    ϴ Machine.upd_apply, h116, h129, h130, ite_false
    exact hfn r h116 h129 h130
  · config_simp; exact hfr
  · intro t ht
    config_simp
    ϴ h105, h106, h107, h108, h109, h112, h113
    repeat' (first | omega | (rw [Machine.upd_apply]; split_ifs))
    exact hnm t ht
  · config_simp; exact hrm
  · config_simp; exact hout
  · config_simp; rw [h113]; omega

/-- **Spec of the initialisation loop**: from `k = 0` it fills the five bands for the `n`
vertices, at cost `≤ 16 n + 2`. -/
theorem initLoop_exec {B NN : ℕ} (hNN : P.n ≤ NN) (hW : B + 4 * NN + P.n ≤ W) (c₀ : Config)
    (hI : InitInv P W B NN c₀ c₀) (h0 : c₀.nreg 116 = 0) :
    ∃ c' k, Exec P W initLoop c₀ c' k ∧ k ≤ 16 * P.n + 2 ∧ InitInv P W B NN c₀ c' ∧
      c'.nreg 116 = P.n := by
  obtain ⟨c', k, ex, hI', hexit, hk⟩ := Exec.whileLtN_bounded (InitInv P W B NN c₀)
    (fun d => P.n - d.nreg 116) 14 (fun _ h => h.1)
    (fun d hd ht => initBody_inv hNN hW hd ht) hI
  refine ⟨c', k, ex, ?_, hI', ?_⟩
  · Ξ' h0 at hk
    simpa [Nat.sub_zero, Nat.mul_comm] using hk
  · have := hI'.2.1
    Ξ' hI'.2.2.1 at hexit
    omega

/-- The memory relation for the initial structure: node `z < n` is vertex `z`, with successor
`(z + 1) % n` and predecessor `(z + n - 1) % n`, and the only copy of `v < n` is `v`. -/
theorem memRel_init {mem : ℕ → ℕ} {B NN n : ℕ} (_hn : 0 < n)
    (hv : ∀ z < n, mem (B + z) = z) (hx : ∀ z < n, mem (B + NN + z) = (z + 1) % n)
    (hp : ∀ z < n, mem (B + 2 * NN + z) = (z + n - 1) % n)
    (hs : ∀ z < n, mem (B + 3 * NN + z) = 0) (hh : ∀ z < n, mem (B + 4 * NN + z) = z + 1) :
    MemRel mem B NN n (initState n) := by
  refine ⟨fun z hz => hv z hz, fun z hz => hx z hz, fun z hz => hp z hz, fun v hv' => ?_⟩
  show Chain mem (B + 3 * NN) (mem (B + 4 * NN + v)) (if v < n then [v] else [])
  Ξ ite_eq_left hv', hh v hv'
  exact ⟨rfl, hs v hv'⟩

/-- **Spec of the splitting program.**  With the work-area base `B = nreg 100`, the diagonal
band `DB = nreg 101` holding the list `D` of `ND = nreg 102` pairs of distinct vertices `< n`,
the orientation `σ = rreg 100`, and `NN = n + 2 ND`: `splitStmt` leaves the linked structure
`runState P σ (initState n) D` in the work area (`ScanHyp`), with `nreg 115 = NN` nodes, at
cost `≤ 62 * runCost + 63 ND + 16 n + 23`.  It writes only the natural registers `103 … 139`, the
real registers `101 … 117` and the work area `[B, B + 4 NN + n)`. -/
theorem splitStmt_exec {B DB ND NN : ℕ} {σ : ℝ} {D : List (ℕ × ℕ)} (c : Config)
    (hc : WordsBounded W c) (h100 : c.nreg 100 = B) (h101 : c.nreg 101 = DB)
    (h102 : c.nreg 102 = ND) (hσ : c.rreg 100 = σ) (hlen : D.length = ND)
    (hNN : NN = P.n + 2 * ND) (hD : ∀ d ∈ D, d.1 < P.n ∧ d.2 < P.n ∧ d.1 ≠ d.2) (hn : 0 < P.n)
    (hband : ∀ j < ND, c.nmem (DB + 2 * j) = (D.getD j (0, 0)).1 ∧
      c.nmem (DB + 2 * j + 1) = (D.getD j (0, 0)).2)
    (hDB : DB + 2 * ND ≤ B ∨ B + 4 * NN + P.n ≤ DB) (hW : B + 4 * NN + P.n ≤ W)
    (hDBW : DB + 2 * ND ≤ W) :
    ∃ c' k, Exec P W splitStmt c c' k ∧
      k ≤ 62 * runCost P σ (initState P.n) D + 63 * ND + 16 * P.n + 23 ∧
      ScanHyp P W B NN P.n σ (runState P σ (initState P.n) D) c' ∧ c'.nreg 115 = NN ∧
      (∀ r, (r < 103 ∨ 139 < r) → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 101 ∨ 117 < r) → c'.rreg r = c.rreg r) ∧
      (∀ t, (t < B ∨ B + 4 * NN + P.n ≤ t) → c'.nmem t = c.nmem t) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hNNn : P.n ≤ NN := by omega
  unfold splitStmt initBlock
  refine spec_seq ?_
  exec_block
  · omega
  · omega
  · omega
  · omega
  · config_simp; rw [h102]; omega
  · config_simp; rw [h102]; omega
  · config_simp; rw [h100, h102]; omega
  · config_simp; rw [h100, h102]; omega
  · config_simp; rw [h100, h102]; omega
  · config_simp; rw [h100, h102]; omega
  · omega
  refine spec_name fun c₁ hc₁ => ?_
  -- the initialisation loop
  have hI₀ : InitInv P W B NN c₁ c₁ := by
    refine ⟨by rw [hc₁]; assumption, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ _ _ => rfl, rfl,
      fun _ _ => rfl,
      rfl, rfl⟩ <;> simp only [hc₁] <;> config_simp
    · omega
    · rw [h100]
    · rw [h100, h102, hNN]; ring
    · rw [h100, h102, hNN]; ring
    · rw [h100, h102, hNN]; ring
    · rw [h100, h102, hNN]; ring
    · intro z hz; omega
  refine spec_seq (spec_use (initLoop_exec hNNn hW c₁ hI₀ (by simp only [hc₁]; config_simp)) ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨⟨-, -, h103, h105, h106, h107, h108, h109, h112, h113, hbands, hfn, hfr,
    hnm, hrm, hout⟩, h116⟩
  -- the fix-up
  unfold initFix
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h106, h103, h113]; omega
  · omega
  refine spec_name fun c₃ hc₃ => ?_
  have e₁ : ∀ r, r ≠ 103 → r ≠ 104 → r ≠ 105 → r ≠ 106 → r ≠ 107 → r ≠ 108 → r ≠ 109 →
      r ≠ 112 → r ≠ 113 → r ≠ 114 → r ≠ 116 → c₁.nreg r = c.nreg r := by
    intro r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    simp only [hc₁]
    simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]
  have hmem₃ : c₃.nmem = upd (upd c₂.nmem (B + NN + (P.n - 1)) 0) (B + 2 * NN) (P.n - 1) := by
    simp only [hc₃]
    rw [h106, h103, h113, h112, h107]
  have hS₀ : ScanHyp P W B NN P.n σ (runState P σ (initState P.n) (D.take 0)) c₃ := by
    rw [List.take_zero, runState_nil]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, closed_init hn, hNNn, hW⟩ <;>
      simp only [hc₃] <;> config_simp
    · exact h105
    · exact h106
    · exact h107
    · exact h108
    · exact h109
    · exact h112
    · exact h113
    · rw [hfr]; simp only [hc₁]; config_simp; exact hσ
    · rw [hfr]; simp only [hc₁]; config_simp; simp
    · rw [h106, h103, h113, h112, h107]
      have hb := fun z (hz : z < P.n) => hbands z (by rw [h116]; exact hz)
      refine memRel_init hn (fun z hz => ?_) (fun z hz => ?_) (fun z hz => ?_) (fun z hz => ?_)
        (fun z hz => ?_) <;> simp only [Machine.upd_apply]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; exact (hb z hz).1
      · rw [ite_eq_right (by omega)]
        split_ifs with h
        · rw [show z = P.n - 1 by omega, show P.n - 1 + 1 = P.n by omega, Nat.mod_self]
        · rw [(hb z hz).2.1, Nat.mod_eq_of_lt (by omega)]
      · split_ifs with h h'
        · rw [show z = 0 by omega, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
        · omega
        · rw [(hb z hz).2.2.1, show z + P.n - 1 = (z - 1) + P.n by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; exact (hb z hz).2.2.2.1
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; exact (hb z hz).2.2.2.2
  have hMI : MainInv P W B NN P.n DB ND σ D c₃ c₃ := by
    refine ⟨by rw [hc₃]; assumption, ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl⟩
    · simp only [hc₃]; config_simp; omega
    · have e : c₃.nreg 116 = 0 := by simp only [hc₃]; config_simp
      rw [e]; exact hS₀
    · simp only [hc₃]; config_simp; exact h103
    · simp only [hc₃]; config_simp
      rw [hfn 101 (by decide) (by decide) (by decide), e₁ 101 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h101]
    · simp only [hc₃]; config_simp
      rw [hfn 102 (by decide) (by decide) (by decide), e₁ 102 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h102]
  have hband₃ : ∀ j < ND, c₃.nmem (DB + 2 * j) = (D.getD j (0, 0)).1 ∧
      c₃.nmem (DB + 2 * j + 1) = (D.getD j (0, 0)).2 := by
    intro j hj
    have hout : ∀ t, DB ≤ t → t < DB + 2 * ND → c₃.nmem t = c.nmem t := by
      intro t ht1 ht2
      rw [hmem₃, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        hnm t (by omega)]
      simp only [hc₁]
    rw [hout _ (by omega) (by omega), hout _ (by omega) (by omega)]
    exact hband j hj
  obtain ⟨c₄, k₄, ex₄, hMI₄, h116₄, hk₄⟩ := mainLoop_exec (P := P) hlen hNN hD hn c₃ hMI hband₃
    hDB hDBW (by omega)
  obtain ⟨hw₄, -, hS₄, h115₄, -, -, hfn₄, hfr₄, hnm₄, hrm₄, hout₄⟩ := hMI₄
  rw [h116₄, ← hlen, List.take_length] at hS₄
  refine ⟨c₄, k₄, ex₄, ?_, hS₄, by rw [h115₄, h116₄, hNN], ?_, ?_, ?_, ?_, ?_⟩
  · have : mainPot P P.n ND σ D c₃ = 62 * runCost P σ (initState P.n) D + 63 * ND := by
      unfold mainPot
      have e : c₃.nreg 116 = 0 := by simp only [hc₃]; config_simp
      rw [e, List.take_zero, List.drop_zero, runState_nil, Nat.sub_zero]
    omega
  · intro r hr
    rw [hfn₄ r (by omega)]
    simp only [hc₃]
    rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      hfn r (by omega) (by omega) (by omega)]
    exact e₁ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  · intro r hr
    rw [hfr₄ r (by omega)]
    simp only [hc₃]
    rw [hfr]; simp only [hc₁]
    rw [Machine.upd_other _ _ _ (by omega)]
  · intro t ht
    rw [hnm₄ t ht, hmem₃, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      hnm t ht]
    simp only [hc₁]
  · rw [hrm₄]; simp only [hc₃]; rw [hrm]; simp only [hc₁]
  · rw [hout₄]; simp only [hc₃]; rw [hout]; simp only [hc₁]

end Init

end

end Chazelle.Final
