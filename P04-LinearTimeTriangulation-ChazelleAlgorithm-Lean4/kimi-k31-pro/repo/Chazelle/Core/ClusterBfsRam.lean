module

public import Chazelle.Core.ClusterBfs
public import Chazelle.Programs.Tactics
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics
public import Chazelle.ChainTactics

/-!
# WP-I, part 3: breadth-first search on the RAM

`bfsStmt`: breadth-first search on a rotation system stored in memory (`ClusterMap.lean`), from
a source `s`, over the unblocked darts between unblocked vertices, writing the label `L`, the
level and the parent dart of every reached vertex and the queue of reached vertices.  The
invariants are those of `ClusterBfs.lean`; the arrays are clamped views (`view`) of memory.

## Registers (band `bCluster = 13`)

| register | role |
|---|---|
| `130001` | the constant `1` (set by the caller) |
| `130100 … 130105` | bases of `opp`, `rot`, `vert`, `first`, `db`, `vb` (read only) |
| `130106 … 130109` | bases of `lab`, `lev`, `par`, `q` (written) |
| `130110`, `130111`, `130112` | `nv` (the sentinel), the label `L`, the source `s` |
| `130120`, `130121` | queue head `h` and tail `t` |
| `130122`, `130123`, `130124` | the head vertex `u`, `first u`, the current dart `d` |
| `130125`, `130130` | the end-of-orbit flag, the dart counter `j` |
| `130126`, `130127`, `130128`, `130129` | scratch address, scratch word, `w`, `lev u + 1` |

## Cost

`bfs_exec`: at most `20 nv + 45 N + 30` steps (`nv` vertices, `N` darts).
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## Generic combinators for statements with a cost bound -/

section gen

variable {P : Polygon} {W : ℕ}

/-- Sequencing of two bounded executions. -/
theorem seqX {s t : Stmt} {c : Config} {K₁ K₂ : ℕ} {R₁ R₂ : Config → Prop}
    (h₁ : ∃ c₁ k₁, Exec P W s c c₁ k₁ ∧ k₁ ≤ K₁ ∧ R₁ c₁)
    (h₂ : ∀ c₁, R₁ c₁ → ∃ c₂ k₂, Exec P W t c₁ c₂ k₂ ∧ k₂ ≤ K₂ ∧ R₂ c₂) :
    ∃ c₂ k, Exec P W (.seq s t) c c₂ k ∧ k ≤ K₁ + K₂ ∧ R₂ c₂ := by
  obtain ⟨c₁, k₁, e₁, hk₁, r₁⟩ := h₁
  obtain ⟨c₂, k₂, e₂, hk₂, r₂⟩ := h₂ c₁ r₁
  exact ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, r₂⟩

/-- Weakening of the bound and of the postcondition. -/
theorem weakenX {s : Stmt} {c : Config} {K K' : ℕ} {R R' : Config → Prop}
    (h : ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ R c') (hK : K ≤ K') (hR : ∀ c', R c' → R' c') :
    ∃ c' k, Exec P W s c c' k ∧ k ≤ K' ∧ R' c' := by
  obtain ⟨c', k, e, hk, r⟩ := h
  exact ⟨c', k, e, by omega, hR c' r⟩

/-- `if x ≠ 1 then S`, with `nreg 130001 = 1`. -/
def ifNe1 (x : ℕ) (S : Stmt) : Stmt := .ifLtN x 130001 S (.ifLtN 130001 x S .skip)

/-- The test `x ≠ 1`. -/
theorem ifNe1_exec {S : Stmt} {c : Config} {K : ℕ} {R : Config → Prop} (hw : WordsBounded W c)
    (hone : c.nreg 130001 = 1) (x : ℕ)
    (hS : c.nreg x ≠ 1 → ∃ c' k, Exec P W S c c' k ∧ k ≤ K ∧ R c')
    (hskip : c.nreg x = 1 → R c) :
    ∃ c' k, Exec P W (ifNe1 x S) c c' k ∧ k ≤ K + 4 ∧ R c' := by
  unfold ifNe1
  by_cases h1 : c.nreg x < c.nreg 130001
  · obtain ⟨c', k, e, hk, r⟩ := hS (by omega)
    exact ⟨c', k + 1, .ifLtN_true h1 e, by omega, r⟩
  · by_cases h2 : c.nreg 130001 < c.nreg x
    · obtain ⟨c', k, e, hk, r⟩ := hS (by omega)
      exact ⟨c', k + 1 + 2, .ifLtN_false h1 (.ifLtN_true h2 e), by omega, r⟩
    · exact ⟨c, 0 + 2 + 2, .ifLtN_false h1 (.ifLtN_false h2 (.skip hw)), by omega,
        hskip (by omega)⟩

/-- `whileLtN` with a potential, keeping track of the final potential: the cost plus the final
potential is at most the initial potential plus `2`. -/
theorem whileLtN_pot {a b : ℕ} {body : Stmt} (I : Config → Prop) (Φ : Config → ℕ)
    (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k + Φ c' ≤ Φ c + 2 := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨c₁, k₁, hb, hI₁, hΦ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hk₂⟩ := ih (Φ c₁) (by omega) hI₁ rfl
      exact ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', by omega⟩
    · exact ⟨c, 2, .whileLtN_false ht (hI c hc), hc, ht, by omega⟩

/-- `ifNe1` when the flag is not `1`: the body runs, at most `3` extra steps. -/
theorem ifNe1_run {S : Stmt} {c c' : Config} {k : ℕ} (hone : c.nreg 130001 = 1) {x : ℕ}
    (hx : c.nreg x ≠ 1) (h : Exec P W S c c' k) :
    ∃ k', Exec P W (ifNe1 x S) c c' k' ∧ k' ≤ k + 3 := by
  unfold ifNe1
  by_cases h1 : c.nreg x < c.nreg 130001
  · exact ⟨k + 1, .ifLtN_true h1 h, by omega⟩
  · exact ⟨k + 1 + 2, .ifLtN_false h1 (.ifLtN_true (by omega) h), by omega⟩

/-- `ifNe1` when the flag is `1`: nothing happens, in `4` steps. -/
theorem ifNe1_skip {S : Stmt} {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {x : ℕ} (hx : c.nreg x = 1) : Exec P W (ifNe1 x S) c c 4 := by
  unfold ifNe1
  exact .ifLtN_false (by omega) (.ifLtN_false (by omega) (.skip hw))

/-- **A counted loop** `while i < n do body`, where the body advances the counter register `ri`
by one and keeps the bound register `rn`: an invariant `I j` indexed by the counter value, a
body cost `≤ B`; total cost `≤ (B + 2) (n - j₀) + 2`. -/
theorem forN {ri rn : ℕ} {body : Stmt} (I : ℕ → Config → Prop) (n B : ℕ)
    (hI : ∀ j c, I j c → WordsBounded W c ∧ c.nreg ri = j ∧ c.nreg rn = n)
    (hbody : ∀ j c, j < n → I j c → ∃ c' k, Exec P W body c c' k ∧ k ≤ B ∧ I (j + 1) c')
    {j₀ : ℕ} {c : Config} (hc : I j₀ c) (hj₀ : j₀ ≤ n) :
    ∃ c' k, Exec P W (.whileLtN ri rn body) c c' k ∧ k ≤ (B + 2) * (n - j₀) + 2 ∧ I n c' := by
  obtain ⟨c', k, e, ⟨j', hIj, hj'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := ri) (b := rn) (body := body) (fun c => ∃ j, I j c ∧ j ≤ n)
    (fun c => (B + 2) * (n - c.nreg ri)) (fun c ⟨j, h, _⟩ => (hI j c h).1)
    (fun c ⟨j, h, hjn⟩ htest => by
      obtain ⟨-, hri, hrn⟩ := hI j c h
      rw [hri, hrn] at htest
      obtain ⟨c', k, e, hk, h'⟩ := hbody j c htest h
      obtain ⟨-, hri', -⟩ := hI (j + 1) c' h'
      refine ⟨c', k, e, ⟨j + 1, h', by omega⟩, ?_⟩
      rw [hri, hri']
      have : (B + 2) * (n - j) = (B + 2) * (n - (j + 1)) + (B + 2) := by
        rw [← Nat.mul_succ]; congr 1; omega
      omega) ⟨j₀, hc, hj₀⟩
  obtain ⟨-, hri, hrn⟩ := hI j' c' hIj
  have hj'n : j' = n := by rwo [hri, hrn] at htest
  subst hj'n
  refine ⟨c', k, e, ?_, hIj⟩
  obtain ⟨-, hri0, -⟩ := hI j₀ c hc
  rw [hri0] at hk
  exact hk

end gen

/-! ## Layout -/

/-- Two address ranges `[b₁, b₁ + n₁)`, `[b₂, b₂ + n₂)` are disjoint. -/
def Disj (b₁ n₁ b₂ n₂ : ℕ) : Prop := b₁ + n₁ ≤ b₂ ∨ b₂ + n₂ ≤ b₁

/-- The memory layout of a search: bases of the read-only arrays and of the written arrays. -/
structure Lay where
  /-- base of `opp` -/
  bO : ℕ
  /-- base of `rot` -/
  bR : ℕ
  /-- base of `vert` -/
  bV : ℕ
  /-- base of `first` -/
  bF : ℕ
  /-- base of `db` -/
  bDB : ℕ
  /-- base of `vb` -/
  bVB : ℕ
  /-- base of `lab` -/
  bLab : ℕ
  /-- base of `lev` -/
  bLev : ℕ
  /-- base of `par` -/
  bPar : ℕ
  /-- base of `q` -/
  bQ : ℕ
  /-- vertices -/
  nv : ℕ
  /-- darts -/
  N : ℕ

namespace Lay

variable (Y : Lay)

/-- The rotation system read from memory. -/
def env (m : ℕ → ℕ) : Env :=
  ⟨view m Y.bO Y.N, view m Y.bR Y.N, view m Y.bV Y.N, view m Y.bF Y.nv, view m Y.bDB Y.N,
    view m Y.bVB Y.nv, Y.nv, Y.N⟩

/-- The addresses written by the search: the arrays `lab`, `lev`, `par`, `q`. -/
def Written (a : ℕ) : Prop :=
  (Y.bLab ≤ a ∧ a < Y.bLab + Y.nv) ∨ (Y.bLev ≤ a ∧ a < Y.bLev + Y.nv) ∨
    (Y.bPar ≤ a ∧ a < Y.bPar + Y.nv) ∨ (Y.bQ ≤ a ∧ a < Y.bQ + Y.nv)

/-- **A good layout** for the word bound `W`: the written arrays are pairwise disjoint and
disjoint from the read-only ones, and every address and count stays below `W`. -/
structure Good (W : ℕ) : Prop where
  d1 : ∀ b n, (b = Y.bO ∧ n = Y.N) ∨ (b = Y.bR ∧ n = Y.N) ∨ (b = Y.bV ∧ n = Y.N) ∨
      (b = Y.bF ∧ n = Y.nv) ∨ (b = Y.bDB ∧ n = Y.N) ∨ (b = Y.bVB ∧ n = Y.nv) →
    Disj b n Y.bLab Y.nv ∧ Disj b n Y.bLev Y.nv ∧ Disj b n Y.bPar Y.nv ∧ Disj b n Y.bQ Y.nv
  d2 : Disj Y.bLab Y.nv Y.bLev Y.nv ∧ Disj Y.bLab Y.nv Y.bPar Y.nv ∧
    Disj Y.bLab Y.nv Y.bQ Y.nv ∧ Disj Y.bLev Y.nv Y.bPar Y.nv ∧ Disj Y.bLev Y.nv Y.bQ Y.nv ∧
    Disj Y.bPar Y.nv Y.bQ Y.nv
  wO : Y.bO + Y.N ≤ W
  wR : Y.bR + Y.N ≤ W
  wV : Y.bV + Y.N ≤ W
  wF : Y.bF + Y.nv ≤ W
  wDB : Y.bDB + Y.N ≤ W
  wVB : Y.bVB + Y.nv ≤ W
  wLab : Y.bLab + Y.nv ≤ W
  wLev : Y.bLev + Y.nv ≤ W
  wPar : Y.bPar + Y.nv ≤ W
  wQ : Y.bQ + Y.nv ≤ W
  wn : Y.nv + 1 ≤ W
  wN : Y.N + 1 ≤ W

variable {Y}

/-- Memories agreeing outside the written arrays read the same rotation system. -/
@[simp] theorem env_nv (m : ℕ → ℕ) : (Y.env m).nv = Y.nv := rfl

@[simp] theorem env_N (m : ℕ → ℕ) : (Y.env m).N = Y.N := rfl

theorem env_congr {W : ℕ} (hY : Y.Good W) {m m' : ℕ → ℕ} (h : ∀ a, ¬ Y.Written a → m' a = m a) :
    Y.env m' = Y.env m := by
  have key : ∀ b n, (b = Y.bO ∧ n = Y.N) ∨ (b = Y.bR ∧ n = Y.N) ∨ (b = Y.bV ∧ n = Y.N) ∨
      (b = Y.bF ∧ n = Y.nv) ∨ (b = Y.bDB ∧ n = Y.N) ∨ (b = Y.bVB ∧ n = Y.nv) →
      view m' b n = view m b n := by
    intro b n hbn
    obtain ⟨h1, h2, h3, h4⟩ := hY.d1 b n hbn
    refine view_congr (fun i hi => h _ ?_)
    unfold Written Disj at *
    omega
  unfold env
  rw [key _ _ (Or.inl ⟨rfl, rfl⟩), key _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩)),
    key _ _ (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))),
    key _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))),
    key _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))),
    key _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))]

end Lay

/-! ## Views of the written arrays after a push -/

section views

variable {Y : Lay} {W : ℕ}

/-- The written arrays of a configuration's memory. -/
def labV (Y : Lay) (m : ℕ → ℕ) : ℕ → ℕ := view m Y.bLab Y.nv
/-- The level array. -/
def levV (Y : Lay) (m : ℕ → ℕ) : ℕ → ℕ := view m Y.bLev Y.nv
/-- The parent array. -/
def parV (Y : Lay) (m : ℕ → ℕ) : ℕ → ℕ := view m Y.bPar Y.nv
/-- The queue array. -/
def qV (Y : Lay) (m : ℕ → ℕ) : ℕ → ℕ := view m Y.bQ Y.nv

/-- The memory after a push. -/
def pushMem (Y : Lay) (m : ℕ → ℕ) (w t L lu e : ℕ) : ℕ → ℕ :=
  upd (upd (upd (upd m (Y.bLab + w) L) (Y.bLev + w) lu) (Y.bPar + w) e) (Y.bQ + t) w

theorem labV_push (hY : Y.Good W) (m : ℕ → ℕ) {w t : ℕ} (hw : w < Y.nv) (ht : t < Y.nv)
    (L lu e : ℕ) :
    labV Y (pushMem Y m w t L lu e) = Function.update (labV Y m) w L := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hY.d2
  unfold labV pushMem Disj at *
  rw [view_upd_out _ _ _ _ _ (by omega), view_upd_out _ _ _ _ _ (by omega),
    view_upd_out _ _ _ _ _ (by omega), view_upd_in _ _ _ _ _ hw]

theorem levV_push (hY : Y.Good W) (m : ℕ → ℕ) {w t : ℕ} (hw : w < Y.nv) (ht : t < Y.nv)
    (L lu e : ℕ) :
    levV Y (pushMem Y m w t L lu e) = Function.update (levV Y m) w lu := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hY.d2
  unfold levV pushMem Disj at *
  rw [view_upd_out _ _ _ _ _ (by omega), view_upd_out _ _ _ _ _ (by omega),
    view_upd_in _ _ _ _ _ hw, view_upd_out _ _ _ _ _ (by omega)]

theorem parV_push (hY : Y.Good W) (m : ℕ → ℕ) {w t : ℕ} (hw : w < Y.nv) (ht : t < Y.nv)
    (L lu e : ℕ) :
    parV Y (pushMem Y m w t L lu e) = Function.update (parV Y m) w e := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hY.d2
  unfold parV pushMem Disj at *
  rw [view_upd_out _ _ _ _ _ (by omega), view_upd_in _ _ _ _ _ hw,
    view_upd_out _ _ _ _ _ (by omega), view_upd_out _ _ _ _ _ (by omega)]

theorem qV_push (hY : Y.Good W) (m : ℕ → ℕ) {w t : ℕ} (hw : w < Y.nv) (ht : t < Y.nv)
    (L lu e : ℕ) :
    qV Y (pushMem Y m w t L lu e) = Function.update (qV Y m) t w := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hY.d2
  unfold qV pushMem Disj at *
  rw [view_upd_in _ _ _ _ _ ht, view_upd_out _ _ _ _ _ (by omega),
    view_upd_out _ _ _ _ _ (by omega), view_upd_out _ _ _ _ _ (by omega)]

/-- A push writes only the written arrays. -/
theorem pushMem_other (m : ℕ → ℕ) {w t : ℕ} (hw : w < Y.nv) (ht : t < Y.nv) (L lu e : ℕ)
    {a : ℕ} (ha : ¬ Y.Written a) : pushMem Y m w t L lu e a = m a := by
  unfold pushMem Lay.Written at *
  rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
    Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]

end views

/-! ## Registers and the frame of the search -/

/-- The registers holding the layout, the label, the source and the constant `1`. -/
structure Regs (Y : Lay) (s L : ℕ) (c : Config) : Prop where
  one : c.nreg 130001 = 1
  rO : c.nreg 130100 = Y.bO
  rR : c.nreg 130101 = Y.bR
  rV : c.nreg 130102 = Y.bV
  rF : c.nreg 130103 = Y.bF
  rDB : c.nreg 130104 = Y.bDB
  rVB : c.nreg 130105 = Y.bVB
  rLab : c.nreg 130106 = Y.bLab
  rLev : c.nreg 130107 = Y.bLev
  rPar : c.nreg 130108 = Y.bPar
  rQ : c.nreg 130109 = Y.bQ
  rn : c.nreg 130110 = Y.nv
  rL : c.nreg 130111 = L
  rs : c.nreg 130112 = s

/-- The scratch registers of the search. -/
def Scr (r : ℕ) : Prop := 130120 ≤ r ∧ r ≤ 130130

/-- **The frame of the search** relative to its entry configuration `c0`: only the scratch
registers and the written arrays change. -/
def Fr (Y : Lay) (c0 c : Config) : Prop :=
  (∀ r, ¬ Scr r → c.nreg r = c0.nreg r) ∧ c.rreg = c0.rreg ∧ c.rmem = c0.rmem ∧
    c.output = c0.output ∧ ∀ a, ¬ Y.Written a → c.nmem a = c0.nmem a

/-- Changing only scratch registers keeps the frame. -/
theorem Fr.nreg {Y : Lay} {c0 c : Config} (hf : Fr Y c0 c) {f : ℕ → ℕ}
    (hfr : ∀ r, ¬ Scr r → f r = c.nreg r) : Fr Y c0 { c with nreg := f } :=
  ⟨fun r hr => (hfr r hr).trans (hf.1 r hr), hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩

/-- The layout registers survive the frame. -/
theorem Regs.fr {Y : Lay} {s L : ℕ} {c0 c : Config} (h : Regs Y s L c0) (hf : Fr Y c0 c) :
    Regs Y s L c := by
  have k  := hf.1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rwa [k _ (by ufo Scr)])

/-! ## The program -/

/-- Push `w` (address `lab + w` in `130126`): label, level, parent dart, queue entry `t`,
`t := t + 1`. -/
def pushB : Stmt := block [.storeN 130126 130111, .addN 130126 130107 130128,
  .storeN 130126 130129, .addN 130126 130108 130128, .storeN 130126 130124,
  .addN 130126 130109 130121, .storeN 130126 130128, .addN 130121 130121 130001]

/-- Visit `w`: push it unless it is labelled (`lab w < nv`). -/
def visitB : Stmt := .seq (block [.addN 130126 130106 130128, .loadN 130127 130126])
  (.ifLtN 130127 130110 .skip pushB)

/-- An unblocked dart `d`: `w := vert (opp d)`, visit `w` unless it is blocked. -/
def allowB : Stmt := .seq (block [.addN 130126 130100 130124, .loadN 130127 130126,
  .addN 130126 130102 130127, .loadN 130128 130126, .addN 130126 130105 130128,
  .loadN 130127 130126]) (ifNe1 130127 visitB)

/-- The current dart `d`: handle it unless it is blocked. -/
def dartB : Stmt := .seq (block [.addN 130126 130104 130124, .loadN 130127 130126])
  (ifNe1 130127 allowB)

/-- Advance: `d := rot d`, `j := j + 1`. -/
def advB : Stmt := block [.addN 130126 130101 130124, .loadN 130124 130126,
  .addN 130130 130130 130001]

/-- End of the orbit: `done := 1` if `d = first u`. -/
def testB : Stmt :=
  .ifLtN 130124 130123 .skip (.ifLtN 130123 130124 .skip (block [.constN 130125 1]))

/-- One dart of the inner loop. -/
def innerBody : Stmt := .seq dartB (.seq advB testB)

/-- The inner loop: the rotation orbit of `first u`. -/
def innerLoop : Stmt := .whileLtN 130125 130001 innerBody

/-- The head entry: `u := q h`, `lu := lev u + 1`, `d0 := d := first u`, `done := 0`,
`j := 0`. -/
def headB : Stmt := block [.addN 130126 130109 130120, .loadN 130122 130126,
  .addN 130126 130107 130122, .loadN 130129 130126, .addN 130129 130129 130001,
  .addN 130126 130103 130122, .loadN 130123 130126, .copyN 130124 130123, .constN 130125 0,
  .constN 130130 0]

/-- One entry of the queue. -/
def outerBody : Stmt := .seq headB (.seq innerLoop (.instr (.addN 130120 130120 130001)))

/-- The outer loop, while `h < t`. -/
def outerLoop : Stmt := .whileLtN 130120 130121 outerBody

/-- Start: `q 0 := s`, `lab s := L`, `lev s := 0`, `h := 0`, `t := 1`. -/
def initB : Stmt := block [.copyN 130126 130109, .storeN 130126 130112,
  .addN 130126 130106 130112, .storeN 130126 130111, .addN 130126 130107 130112,
  .constN 130127 0, .storeN 130126 130127, .constN 130120 0, .constN 130121 1]

/-- **Breadth-first search.** -/
def bfsStmt : Stmt := .seq initB outerLoop

/-! ## The straight-line pieces -/

section pieces

variable {P : Polygon} {W : ℕ} {Y : Lay} {s L : ℕ}

theorem pushB_exec (hY : Y.Good W) {c : Config} (hw : WordsBounded W c) (hR : Regs Y s L c)
    {w t e lu : ℕ} (hA : c.nreg 130126 = Y.bLab + w) (hW : c.nreg 130128 = w)
    (hT : c.nreg 130121 = t) (hE : c.nreg 130124 = e) (hLU : c.nreg 130129 = lu)
    (hwn : w < Y.nv) (htn : t < Y.nv) :
    ∃ c' k, Exec P W pushB c c' k ∧ k = 8 ∧
      c'.nmem = pushMem Y c.nmem w t L lu e ∧ c'.nreg 130121 = t + 1 ∧
      (∀ r, r ≠ 130126 → r ≠ 130121 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hY.wLev; have := hY.wPar; have := hY.wQ; have := hY.wn
  unfold pushB
  exec_block
  · config_simp; rwo [hR.rLev, hW]
  · config_simp; rwo [hR.rPar, hW]
  · config_simp; rwo [hR.rQ, hT]
  · config_simp; rwo [hT, hR.one]
  · refine ⟨rfl, ?_, by config_simp; rw [hT, hR.one], fun r h1 h2 => ?_, rfl, rfl, rfl⟩
    · simp only [pushMem, hA, hR.rL, hR.rLev, hW, hLU, hR.rPar, hE, hR.rQ, hT]
    · simp [h1, h2]

end pieces

/-! ## The inner loop -/

/-- **The configuration invariant of the inner loop**: the abstract invariant `InvIn` on the views
of memory, the head vertex `u = q h`, `lu = lev u + 1`, `d0 = first u`, the current dart
`d = rot^[j] d0`, and the flag `done` (`0` while `j < per`, `1` when `j = per`). -/
structure II (Y : Lay) (W s L : ℕ) (lab0 : ℕ → ℕ) (c0 c : Config) : Prop where
  wb : WordsBounded W c
  fr : Fr Y c0 c
  inv : (Y.env c0.nmem).InvIn s L lab0 (labV Y c.nmem) (levV Y c.nmem) (parV Y c.nmem)
    (qV Y c.nmem) (c.nreg 130120) (c.nreg 130121) (c.nreg 130130)
  u : c.nreg 130122 = qV Y c.nmem (c.nreg 130120)
  lu : c.nreg 130129 = levV Y c.nmem (c.nreg 130122) + 1
  d0 : c.nreg 130123 = (Y.env c0.nmem).first (c.nreg 130122)
  d : c.nreg 130124 = (Y.env c0.nmem).rot^[c.nreg 130130] (c.nreg 130123)
  dn : (c.nreg 130125 = 0 ∧ c.nreg 130130 < per (Y.env c0.nmem).rot Y.N (c.nreg 130123)) ∨
    (c.nreg 130125 = 1 ∧ c.nreg 130130 = per (Y.env c0.nmem).rot Y.N (c.nreg 130123))

/-- The state after handling one dart (relative to the registers `R` and memory `m` at the start
of `dartB`, with head index `h`, dart counter `j` and head vertex `u`). -/
def DPost (Y : Lay) (W s L : ℕ) (lab0 : ℕ → ℕ) (c0 : Config) (h j u : ℕ) (R : ℕ → ℕ)
    (m : ℕ → ℕ) (c1 : Config) : Prop :=
  WordsBounded W c1 ∧ Fr Y c0 c1 ∧
    (Y.env c0.nmem).InvIn s L lab0 (labV Y c1.nmem) (levV Y c1.nmem) (parV Y c1.nmem)
      (qV Y c1.nmem) h (c1.nreg 130121) (j + 1) ∧
    (∀ r, r ≠ 130121 → r ≠ 130126 → r ≠ 130127 → r ≠ 130128 → c1.nreg r = R r) ∧
    (∀ i, i < R 130121 → qV Y c1.nmem i = qV Y m i) ∧ R 130121 ≤ c1.nreg 130121 ∧
    levV Y c1.nmem u = levV Y m u

section inner

variable {P : Polygon} {W : ℕ} {Y : Lay} {s L : ℕ} {lab0 : ℕ → ℕ} {c0 : Config}

/-- Reading a read-only array of the entry memory through the frame. -/
theorem Fr.read {c : Config} (hY : Y.Good W) (hf : Fr Y c0 c) {b n i : ℕ}
    (hb : (b = Y.bO ∧ n = Y.N) ∨ (b = Y.bR ∧ n = Y.N) ∨ (b = Y.bV ∧ n = Y.N) ∨
      (b = Y.bF ∧ n = Y.nv) ∨ (b = Y.bDB ∧ n = Y.N) ∨ (b = Y.bVB ∧ n = Y.nv)) (hi : i < n) :
    c.nmem (b + i) = view c0.nmem b n i := by
  rw [view_lt hi]
  refine hf.2.2.2.2 _ ?_
  obtain ⟨h1, h2, h3, h4⟩ := hY.d1 b n hb
  unfold Lay.Written Disj at *
  omega

/-- Visiting `w = head e` for an unblocked dart `e` to an unblocked vertex: skip it if labelled,
push it otherwise. -/
theorem visitB_exec (hY : Y.Good W) (hR0 : Regs Y s L c0) (hp : (Y.env c0.nmem).Pre s L lab0)
    {c c' : Config} (hI : II Y W s L lab0 c0 c) (hjp : c.nreg 130130 <
      per (Y.env c0.nmem).rot Y.N (c.nreg 130123))
    (hw' : WordsBounded W c') (hf' : Fr Y c0 c') (hm' : c'.nmem = c.nmem)
    (hr' : ∀ r, r ≠ 130126 → r ≠ 130127 → r ≠ 130128 → c'.nreg r = c.nreg r)
    (hdb : (Y.env c0.nmem).db (c.nreg 130124) ≠ 1)
    (hW' : c'.nreg 130128 = (Y.env c0.nmem).head (c.nreg 130124))
    (hvb : (Y.env c0.nmem).vb ((Y.env c0.nmem).head (c.nreg 130124)) ≠ 1) :
    ∃ c1 k, Exec P W visitB c' c1 k ∧ k ≤ 20 ∧
      DPost Y W s L lab0 c0 (c.nreg 130120) (c.nreg 130130) (c.nreg 130122) c.nreg c.nmem c1 := by
  have hR'  := hR0.fr hf'
  have hIn := hI.inv
  have hht := hIn.hlt
  have hun : c.nreg 130122 < Y.nv := by rw [hI.u]; exact hIn.inv.qlt _ hht
  have he : (Y.env c0.nmem).rot^[c.nreg 130130] ((Y.env c0.nmem).first
      (qV Y c.nmem (c.nreg 130120))) = c.nreg 130124 := by rw [← hI.u, ← hI.d0, ← hI.d]
  have hjp' : c.nreg 130130 < per (Y.env c0.nmem).rot (Y.env c0.nmem).N
      ((Y.env c0.nmem).first (qV Y c.nmem (c.nreg 130120))) := by
    rwx [← hI.u, ← hI.d0]
  have hfirst : (Y.env c0.nmem).first (c.nreg 130122) < Y.N := hp.ok.first_lt _ hun
  have heN : c.nreg 130124 < Y.N := by
    rw [hI.d, hI.d0]; exact hp.ok.injOn.iterate_lt _ hfirst
  have hve : (Y.env c0.nmem).vert (c.nreg 130124) = qV Y c.nmem (c.nreg 130120) := by
    rw [← he, hp.ok.vert_iterate _ (by rwx [← hI.u]), hp.ok.vert_first _
      (by rwx [← hI.u])]
  have hwn : (Y.env c0.nmem).head (c.nreg 130124) < Y.nv :=
    hp.ok.vert_lt _ (hp.ok.opp_lt _ heN)
  have hvis := hIn.visited_iff hp heN hdb hve hvb
  have := hY.wLab
  unfold visitB
  refine seqX (K₁ := 2) (K₂ := 18) (R₁ := fun c2 => WordsBounded W c2 ∧ c2.nmem = c.nmem ∧
      c2.nreg 130126 = Y.bLab + (Y.env c0.nmem).head (c.nreg 130124) ∧
      c2.nreg 130127 = labV Y c.nmem ((Y.env c0.nmem).head (c.nreg 130124)) ∧
      (∀ r, r ≠ 130126 → r ≠ 130127 → r ≠ 130128 → c2.nreg r = c.nreg r) ∧
      c2.nreg 130128 = (Y.env c0.nmem).head (c.nreg 130124) ∧ c2.rreg = c'.rreg ∧
      c2.rmem = c'.rmem ∧ c2.output = c'.output) ?_ ?_
  · exec_block
    · rwo [hR'.rLab, hW']
    · refine ⟨by omega, ‹_›, hm', by config_simp; rw [hR'.rLab, hW'], ?_, fun r h1 h2 h3 => ?_,
        by config_simp; exact hW', rfl, rfl, rfl⟩
      · config_simp; rw [hR'.rLab, hW', hm', labV, view_lt hwn]
      · config_simp; rw [Machine.upd_other _ _ _ h2, Machine.upd_other _ _ _ h1]
        exact hr' r h1 h2 h3
  · rintro c2 ⟨hw2, hm2, hA2, hX2, hr2, hW2, hrr2, hrm2, ho2⟩
    have hf2 : Fr Y c0 c2 := by
      refine ⟨fun r hr => ?_, hrr2.trans hf'.2.1, hrm2.trans hf'.2.2.1, ho2.trans hf'.2.2.2.1,
        fun a ha => by rw [hm2]; exact hI.fr.2.2.2.2 a ha⟩
      have h6 : r ≠ 130126 := fun h => hr (by ruo [h] Scr)
      have h7 : r ≠ 130127 := fun h => hr (by ruo [h] Scr)
      have h8 : r ≠ 130128 := fun h => hr (by ruo [h] Scr)
      rw [hr2 r h6 h7 h8]; exact hI.fr.1 r hr
    have hR2  := hR0.fr hf2
    by_cases hv : c2.nreg 130127 < c2.nreg 130110
    · -- already labelled: skip
      refine ⟨c2, 0 + 1, .ifLtN_true hv (.skip hw2), by omega, hw2, hf2, ?_,
        fun r h1 h6 h7 h8 => hr2 r h6 h7 h8, fun i _ => by rw [hm2],
        by rw [hr2 _ (by decide) (by decide) (by decide)], by rw [hm2]⟩
      rw [hm2, hr2 _ (by decide) (by decide) (by decide)]
      refine hIn.skip' hjp' he (Or.inr (Or.inr ?_))
      rw [hX2, hR2.rn] at hv
      exact hvis.mp hv
    · -- not labelled: push
      rw [hX2, hR2.rn] at hv
      have hnot : ∀ i, i < c.nreg 130121 →
          qV Y c.nmem i ≠ (Y.env c0.nmem).head (c.nreg 130124) := by
        intro i hi hqi
        exact hv (hvis.mpr ⟨i, hi, hqi⟩)
      have htn  := hIn.inv.t_lt_of_notMem hwn hnot
      obtain ⟨c1, k1, e1, hk1, hm1, hT1, hr1, hrr1, hrm1, ho1⟩ := pushB_exec (P := P) hY hw2 hR2
        hA2 hW2 (by rw [hr2 _ (by decide) (by decide) (by decide)])
        (by rw [hr2 _ (by decide) (by decide) (by decide)])
        (by rw [hr2 _ (by decide) (by decide) (by decide)]) hwn htn
      refine ⟨c1, k1 + 2, .ifLtN_false (by rwx [hX2, hR2.rn]) e1, by omega,
        e1.wb_right, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨fun r hr => ?_, hrr1.trans hf2.2.1, hrm1.trans hf2.2.2.1, ho1.trans hf2.2.2.2.1,
          fun a ha => ?_⟩
        · have h6 : r ≠ 130126 := fun h => hr (by ruo [h] Scr)
          have h1 : r ≠ 130121 := fun h => hr (by ruo [h] Scr)
          rw [hr1 r h6 h1]; exact hf2.1 r hr
        · rw [hm1, pushMem_other _ hwn htn _ _ _ ha]; exact hf2.2.2.2.2 a ha
      · rw [hm1, hT1, hm2, labV_push hY _ hwn htn, levV_push hY _ hwn htn, parV_push hY _ hwn htn,
          qV_push hY _ hwn htn]
        refine hIn.push' hp hjp' he rfl ?_ hdb hvb hnot
        rw [hI.lu, hI.u]
      · intro r h1 h6 h7 h8
        rw [hr1 r h6 h1, hr2 r h6 h7 h8]
      · intro i hi
        rw [hm1, hm2, qV_push hY _ hwn htn, Function.update_of_ne (by omega)]
      · rwo [hT1]
      · rw [hm1, hm2, levV_push hY _ hwn htn, Function.update_of_ne]
        intro heq
        exact hnot _ hht (by rw [← hI.u, heq])

/-- The frame of a configuration that differs from `c` only in the scratch registers `130126 …
130128`. -/
theorem fr_scratch {c c1 : Config} (hf : Fr Y c0 c) (hm : c1.nmem = c.nmem)
    (hr : ∀ r, r ≠ 130126 → r ≠ 130127 → r ≠ 130128 → c1.nreg r = c.nreg r)
    (hrr : c1.rreg = c.rreg) (hrm : c1.rmem = c.rmem) (ho : c1.output = c.output) :
    Fr Y c0 c1 := by
  refine ⟨fun r hr' => ?_, hrr.trans hf.2.1, hrm.trans hf.2.2.1, ho.trans hf.2.2.2.1,
    fun a ha => by rw [hm]; exact hf.2.2.2.2 a ha⟩
  have h6 : r ≠ 130126 := fun h => hr' (by ruo [h] Scr)
  have h7 : r ≠ 130127 := fun h => hr' (by ruo [h] Scr)
  have h8 : r ≠ 130128 := fun h => hr' (by ruo [h] Scr)
  rw [hr r h6 h7 h8]; exact hf.1 r hr'

/-- A skipped dart: nothing but scratch registers changed. -/
theorem dpost_skip (_hp : (Y.env c0.nmem).Pre s L lab0) {c c1 : Config}
    (hI : II Y W s L lab0 c0 c)
    (hjp : c.nreg 130130 < per (Y.env c0.nmem).rot Y.N (c.nreg 130123))
    (hw1 : WordsBounded W c1) (hf1 : Fr Y c0 c1) (hm : c1.nmem = c.nmem)
    (hr : ∀ r, r ≠ 130126 → r ≠ 130127 → r ≠ 130128 → c1.nreg r = c.nreg r)
    (hcase : (Y.env c0.nmem).db (c.nreg 130124) = 1 ∨
      (Y.env c0.nmem).vb ((Y.env c0.nmem).head (c.nreg 130124)) = 1) :
    DPost Y W s L lab0 c0 (c.nreg 130120) (c.nreg 130130) (c.nreg 130122) c.nreg c.nmem c1 := by
  have he : (Y.env c0.nmem).rot^[c.nreg 130130] ((Y.env c0.nmem).first
      (qV Y c.nmem (c.nreg 130120))) = c.nreg 130124 := by rw [← hI.u, ← hI.d0, ← hI.d]
  have hjp' : c.nreg 130130 < per (Y.env c0.nmem).rot (Y.env c0.nmem).N
      ((Y.env c0.nmem).first (qV Y c.nmem (c.nreg 130120))) := by
    rwx [← hI.u, ← hI.d0]
  refine ⟨hw1, hf1, ?_, fun r h1 h6 h7 h8 => hr r h6 h7 h8, fun i _ => by rw [hm],
    by rw [hr _ (by decide) (by decide) (by decide)], by rw [hm]⟩
  rw [hm, hr _ (by decide) (by decide) (by decide)]
  rcases hcase with h | h
  · exact hI.inv.skip' hjp' he (Or.inl h)
  · exact hI.inv.skip' hjp' he (Or.inr (Or.inl h))

/-- An unblocked dart: read its head and its flag, visit the head unless it is blocked. -/
theorem allowB_exec (hY : Y.Good W) (hR0 : Regs Y s L c0) (hp : (Y.env c0.nmem).Pre s L lab0)
    {c c' : Config} (hI : II Y W s L lab0 c0 c) (hjp : c.nreg 130130 <
      per (Y.env c0.nmem).rot Y.N (c.nreg 130123))
    (hw' : WordsBounded W c') (hf' : Fr Y c0 c') (hm' : c'.nmem = c.nmem)
    (hr' : ∀ r, r ≠ 130126 → r ≠ 130127 → r ≠ 130128 → c'.nreg r = c.nreg r)
    (hdb : (Y.env c0.nmem).db (c.nreg 130124) ≠ 1) :
    ∃ c1 k, Exec P W allowB c' c1 k ∧ k ≤ 30 ∧
      DPost Y W s L lab0 c0 (c.nreg 130120) (c.nreg 130130) (c.nreg 130122) c.nreg c.nmem c1 := by
  have hR' : Regs Y s L c' := hR0.fr hf'
  have hht := hI.inv.hlt
  have hun : c.nreg 130122 < Y.nv := by rw [hI.u]; exact hI.inv.inv.qlt _ hht
  have hfirst : (Y.env c0.nmem).first (c.nreg 130122) < Y.N := hp.ok.first_lt _ hun
  have heN : c.nreg 130124 < Y.N := by
    rw [hI.d, hI.d0]; exact hp.ok.injOn.iterate_lt _ hfirst
  have hoN : (Y.env c0.nmem).opp (c.nreg 130124) < Y.N := hp.ok.opp_lt _ heN
  have hwn : (Y.env c0.nmem).head (c.nreg 130124) < Y.nv := hp.ok.vert_lt _ hoN
  have hD : c'.nreg 130124 = c.nreg 130124 := hr' _ (by decide) (by decide) (by decide)
  have r1 : c'.nmem (Y.bO + c.nreg 130124) = (Y.env c0.nmem).opp (c.nreg 130124) :=
    Fr.read hY hf' (Or.inl ⟨rfl, rfl⟩) heN
  have r2 : c'.nmem (Y.bV + (Y.env c0.nmem).opp (c.nreg 130124)) =
      (Y.env c0.nmem).head (c.nreg 130124) :=
    Fr.read hY hf' (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hoN
  have r3 : c'.nmem (Y.bVB + (Y.env c0.nmem).head (c.nreg 130124)) =
      (Y.env c0.nmem).vb ((Y.env c0.nmem).head (c.nreg 130124)) :=
    Fr.read hY hf' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))) hwn
  have := hY.wO; have := hY.wV; have := hY.wVB
  unfold allowB
  refine seqX (K₁ := 6) (K₂ := 24) (R₁ := fun c2 => WordsBounded W c2 ∧ c2.nmem = c.nmem ∧
      c2.nreg 130127 = (Y.env c0.nmem).vb ((Y.env c0.nmem).head (c.nreg 130124)) ∧
      c2.nreg 130128 = (Y.env c0.nmem).head (c.nreg 130124) ∧
      (∀ r, r ≠ 130126 → r ≠ 130127 → r ≠ 130128 → c2.nreg r = c.nreg r) ∧
      c2.rreg = c'.rreg ∧ c2.rmem = c'.rmem ∧ c2.output = c'.output) ?_ ?_
  · exec_block
    · rwo [hR'.rO, hD]
    · config_simp; rwo [hR'.rV, hR'.rO, hD, r1]
    · config_simp; rwo [hR'.rVB, hR'.rV, hR'.rO, hD, r1, r2]
    · refine ⟨by omega, ‹_›, hm', ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
      · config_simp; rw [hR'.rVB, hR'.rV, hR'.rO, hD, r1, r2, r3]
      · config_simp; rw [hR'.rV, hR'.rO, hD, r1, r2]
      · config_simp
        simp only [Machine.upd_apply, h1, h2, h3, ite_false]
        exact hr' r h1 h2 h3
  · rintro c2 ⟨hw2, hm2, hX2, hW2, hr2, hrr2, hrm2, ho2⟩
    have hf2 : Fr Y c0 c2 := fr_scratch hI.fr hm2 hr2 (hrr2.trans (hf'.2.1.trans hI.fr.2.1.symm))
      (hrm2.trans (hf'.2.2.1.trans hI.fr.2.2.1.symm))
      (ho2.trans (hf'.2.2.2.1.trans hI.fr.2.2.2.1.symm))
    have hone2 : c2.nreg 130001 = 1 := (hR0.fr hf2).one
    refine weakenX (ifNe1_exec (K := 20) hw2 hone2 130127 (fun hne => ?_) (fun heq => ?_))
      (by omega) (fun _ => id)
    · rw [hX2] at hne
      exact visitB_exec hY hR0 hp hI hjp hw2 hf2 hm2 hr2 hdb hW2 hne
    · rw [hX2] at heq
      exact dpost_skip hp hI hjp hw2 hf2 hm2 hr2 (Or.inr heq)

/-- **One dart** of the inner loop (before the advance): cost `≤ 36`. -/
theorem dartB_exec (hY : Y.Good W) (hR0 : Regs Y s L c0) (hp : (Y.env c0.nmem).Pre s L lab0)
    {c : Config} (hI : II Y W s L lab0 c0 c) (hjp : c.nreg 130130 <
      per (Y.env c0.nmem).rot Y.N (c.nreg 130123)) :
    ∃ c1 k, Exec P W dartB c c1 k ∧ k ≤ 36 ∧
      DPost Y W s L lab0 c0 (c.nreg 130120) (c.nreg 130130) (c.nreg 130122) c.nreg c.nmem c1 := by
  have hR : Regs Y s L c := hR0.fr hI.fr
  have hht := hI.inv.hlt
  have hun : c.nreg 130122 < Y.nv := by rw [hI.u]; exact hI.inv.inv.qlt _ hht
  have hfirst : (Y.env c0.nmem).first (c.nreg 130122) < Y.N := hp.ok.first_lt _ hun
  have heN : c.nreg 130124 < Y.N := by
    rw [hI.d, hI.d0]; exact hp.ok.injOn.iterate_lt _ hfirst
  have r1 : c.nmem (Y.bDB + c.nreg 130124) = (Y.env c0.nmem).db (c.nreg 130124) :=
    Fr.read hY hI.fr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))) heN
  have := hY.wDB
  have hw := hI.wb
  unfold dartB
  refine seqX (K₁ := 2) (K₂ := 34) (R₁ := fun c2 => WordsBounded W c2 ∧ c2.nmem = c.nmem ∧
      c2.nreg 130127 = (Y.env c0.nmem).db (c.nreg 130124) ∧
      (∀ r, r ≠ 130126 → r ≠ 130127 → r ≠ 130128 → c2.nreg r = c.nreg r) ∧
      c2.rreg = c.rreg ∧ c2.rmem = c.rmem ∧ c2.output = c.output) ?_ ?_
  · exec_block
    · rwo [hR.rDB]
    · refine ⟨by omega, ‹_›, rfl, by config_simp; rw [hR.rDB, r1], fun r h1 h2 h3 => ?_, rfl,
        rfl, rfl⟩
      config_simp
      rw [Machine.upd_other _ _ _ h2, Machine.upd_other _ _ _ h1]
  · rintro c2 ⟨hw2, hm2, hX2, hr2, hrr2, hrm2, ho2⟩
    have hf2 : Fr Y c0 c2 := fr_scratch hI.fr hm2 hr2 hrr2 hrm2 ho2
    have hone2 : c2.nreg 130001 = 1 := (hR0.fr hf2).one
    refine weakenX (ifNe1_exec (K := 30) hw2 hone2 130127 (fun hne => ?_) (fun heq => ?_))
      (by omega) (fun _ => id)
    · rw [hX2] at hne
      exact allowB_exec hY hR0 hp hI hjp hw2 hf2 hm2 hr2 hne
    · rw [hX2] at heq
      exact dpost_skip hp hI hjp hw2 hf2 hm2 hr2 (Or.inl heq)

/-- **One iteration of the inner loop**: handle the current dart, advance, test the end of the
orbit.  Cost `≤ 48`. -/
theorem innerBody_exec (hY : Y.Good W) (hR0 : Regs Y s L c0) (hp : (Y.env c0.nmem).Pre s L lab0)
    {c : Config} (hI : II Y W s L lab0 c0 c) (hdn : c.nreg 130125 = 0) :
    ∃ c' k, Exec P W innerBody c c' k ∧ k ≤ 48 ∧ II Y W s L lab0 c0 c' ∧
      c'.nreg 130120 = c.nreg 130120 ∧ c'.nreg 130122 = c.nreg 130122 ∧
      c'.nreg 130123 = c.nreg 130123 ∧ c'.nreg 130129 = c.nreg 130129 ∧
      c'.nreg 130130 = c.nreg 130130 + 1 ∧
      (∀ i, i < c.nreg 130121 → qV Y c'.nmem i = qV Y c.nmem i) ∧
      c.nreg 130121 ≤ c'.nreg 130121 ∧
      (c'.nreg 130125 = 0 ∨ c'.nreg 130130 = per (Y.env c0.nmem).rot Y.N (c.nreg 130123)) := by
  have hjp : c.nreg 130130 < per (Y.env c0.nmem).rot Y.N (c.nreg 130123) := by
    rcases hI.dn with h | h
    · exact h.2
    · omega
  have hht := hI.inv.hlt
  have hun : c.nreg 130122 < Y.nv := by rw [hI.u]; exact hI.inv.inv.qlt _ hht
  have hfirst : (Y.env c0.nmem).first (c.nreg 130122) < Y.N := hp.ok.first_lt _ hun
  have hd0N : c.nreg 130123 < Y.N := by rwx [hI.d0]
  have heN : c.nreg 130124 < Y.N := by
    rw [hI.d, hI.d0]; exact hp.ok.injOn.iterate_lt _ hfirst
  have hperN : per (Y.env c0.nmem).rot Y.N (c.nreg 130123) ≤ Y.N := per_le hp.ok.injOn hd0N
  have := hY.wR; have := hY.wN
  unfold innerBody
  refine seqX (K₁ := 36) (K₂ := 12) (dartB_exec hY hR0 hp hI hjp) ?_
  rintro c1 ⟨hw1, hf1, hIn1, hr1, hq1, ht1, hl1⟩
  have hR1 : Regs Y s L c1 := hR0.fr hf1
  have hD1 : c1.nreg 130124 = c.nreg 130124 := hr1 _ (by decide) (by decide) (by decide)
    (by decide)
  have hJ1 : c1.nreg 130130 = c.nreg 130130 := hr1 _ (by decide) (by decide) (by decide)
    (by decide)
  have rd : c1.nmem (Y.bR + c.nreg 130124) = (Y.env c0.nmem).rot (c.nreg 130124) :=
    Fr.read hY hf1 (Or.inr (Or.inl ⟨rfl, rfl⟩)) heN
  have hrotN : (Y.env c0.nmem).rot (c.nreg 130124) < Y.N := hp.ok.rot_lt _ heN
  refine seqX (K₁ := 3) (K₂ := 9) (R₁ := fun c2 => WordsBounded W c2 ∧ c2.nmem = c1.nmem ∧
      c2.nreg 130124 = (Y.env c0.nmem).rot (c.nreg 130124) ∧
      c2.nreg 130130 = c.nreg 130130 + 1 ∧
      (∀ r, r ≠ 130124 → r ≠ 130126 → r ≠ 130130 → c2.nreg r = c1.nreg r) ∧
      c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output) ?_ ?_
  · unfold advB
    exec_block
    · rwo [hR1.rR, hD1]
    · config_simp; rwo [hJ1, hR1.one]
    · refine ⟨by omega, ‹_›, rfl, by config_simp; rw [hR1.rR, hD1, rd],
        by config_simp; rw [hJ1, hR1.one], fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
      simp only [Machine.upd_apply, h1, h2, h3, ite_false]
  · rintro c2 ⟨hw2, hm2, hD2, hJ2, hr2, hrr2, hrm2, ho2⟩
    have hd02 : c2.nreg 130123 = c.nreg 130123 := by
      rw [hr2 _ (by decide) (by decide) (by decide), hr1 _ (by decide) (by decide) (by decide)
        (by decide)]
    -- the facts common to both outcomes of the test
    have hiter : (Y.env c0.nmem).rot (c.nreg 130124) =
        (Y.env c0.nmem).rot^[c.nreg 130130 + 1] (c.nreg 130123) := by
      rw [hI.d, Function.iterate_succ_apply']
    have key : ∀ c3 : Config, WordsBounded W c3 → c3.nmem = c2.nmem → c3.rreg = c2.rreg →
        c3.rmem = c2.rmem → c3.output = c2.output →
        (∀ r, r ≠ 130125 → c3.nreg r = c2.nreg r) →
        ((c3.nreg 130125 = 0 ∧ c.nreg 130130 + 1 < per (Y.env c0.nmem).rot Y.N (c.nreg 130123)) ∨
          (c3.nreg 130125 = 1 ∧
            c.nreg 130130 + 1 = per (Y.env c0.nmem).rot Y.N (c.nreg 130123))) →
        II Y W s L lab0 c0 c3 ∧
        c3.nreg 130120 = c.nreg 130120 ∧ c3.nreg 130122 = c.nreg 130122 ∧
        c3.nreg 130123 = c.nreg 130123 ∧ c3.nreg 130129 = c.nreg 130129 ∧
        c3.nreg 130130 = c.nreg 130130 + 1 ∧
        (∀ i, i < c.nreg 130121 → qV Y c3.nmem i = qV Y c.nmem i) ∧
        c.nreg 130121 ≤ c3.nreg 130121 ∧
        (c3.nreg 130125 = 0 ∨ c3.nreg 130130 = per (Y.env c0.nmem).rot Y.N (c.nreg 130123)) := by
      intro c3 hw3 hm3 hrr3 hrm3 ho3 hr3 hdn3
      have g : ∀ r, r ≠ 130124 → r ≠ 130125 → r ≠ 130126 → r ≠ 130127 → r ≠ 130128 →
          r ≠ 130130 → r ≠ 130121 → c3.nreg r = c.nreg r := by
        intro r a1 a2 a3 a4 a5 a6 a7
        rw [hr3 r a2, hr2 r a1 a3 a6, hr1 r a7 a3 a4 a5]
      have e120 := g 130120 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)
      have e122 := g 130122 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)
      have e123 := g 130123 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)
      have e129 := g 130129 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)
      have e130 : c3.nreg 130130 = c.nreg 130130 + 1 := by rw [hr3 _ (by decide), hJ2]
      have e121 : c3.nreg 130121 = c1.nreg 130121 := by
        rw [hr3 _ (by decide), hr2 _ (by decide) (by decide) (by decide)]
      have hf3 : Fr Y c0 c3 := by
        refine ⟨fun r hr => ?_, hrr3.trans (hrr2.trans hf1.2.1), hrm3.trans (hrm2.trans hf1.2.2.1),
          ho3.trans (ho2.trans hf1.2.2.2.1), fun a ha => by rw [hm3, hm2]; exact hf1.2.2.2.2 a ha⟩
        have a1 : r ≠ 130124 := fun h => hr (by ruo [h] Scr)
        have a2 : r ≠ 130125 := fun h => hr (by ruo [h] Scr)
        have a3 : r ≠ 130126 := fun h => hr (by ruo [h] Scr)
        have a6 : r ≠ 130130 := fun h => hr (by ruo [h] Scr)
        rw [hr3 r a2, hr2 r a1 a3 a6]; exact hf1.1 r hr
      have hqh : qV Y c1.nmem (c.nreg 130120) = qV Y c.nmem (c.nreg 130120) := hq1 _ hht
      refine ⟨⟨hw3, hf3, ?_, ?_, ?_, ?_, ?_, ?_⟩, e120, e122, e123, e129, e130, ?_, ?_, ?_⟩
      · rwx [hm3, hm2, e120, e121, e130]
      · rw [e122, hm3, hm2, e120, hqh]; exact hI.u
      · rw [e129, e122, hm3, hm2, hl1]; exact hI.lu
      · rw [e123, e122]; exact hI.d0
      · rw [hr3 _ (by decide), hD2, e130, e123, hiter]
      · rw [e123]; rw [e130]
        rcases hdn3 with h | h
        · exact Or.inl h
        · exact Or.inr h
      · intro i hi; rw [hm3, hm2]; exact hq1 i hi
      · rwx [e121]
      · rcases hdn3 with h | h
        · exact Or.inl h.1
        · exact Or.inr (by rw [e130]; exact h.2)
    have hdn2 : c2.nreg 130125 = 0 := by
      rw [hr2 _ (by decide) (by decide) (by decide), hr1 _ (by decide) (by decide) (by decide)
        (by decide)]
      exact hdn
    unfold testB
    by_cases hlt : c2.nreg 130124 < c2.nreg 130123
    · refine ⟨c2, 0 + 1, .ifLtN_true hlt (.skip hw2), by omega, key c2 hw2 rfl rfl rfl rfl
        (fun _ _ => rfl) (Or.inl ⟨hdn2, ?_⟩)⟩
      rcases Nat.lt_or_ge (c.nreg 130130 + 1) (per (Y.env c0.nmem).rot Y.N (c.nreg 130123))
        with h | h
      · exact h
      · exfalso
        have heq : c.nreg 130130 + 1 = per (Y.env c0.nmem).rot Y.N (c.nreg 130123) := by omega
        rw [hD2, hd02, hiter, heq, iterate_per (N := Y.N) hp.ok.injOn hd0N] at hlt
        exact lt_irrefl _ hlt
    · by_cases hgt : c2.nreg 130123 < c2.nreg 130124
      · refine ⟨c2, 0 + 1 + 2, .ifLtN_false hlt (.ifLtN_true hgt (.skip hw2)), by omega,
          key c2 hw2 rfl rfl rfl rfl (fun _ _ => rfl) (Or.inl ⟨hdn2, ?_⟩)⟩
        rcases Nat.lt_or_ge (c.nreg 130130 + 1) (per (Y.env c0.nmem).rot Y.N (c.nreg 130123))
          with h | h
        · exact h
        · exfalso
          have heq : c.nreg 130130 + 1 = per (Y.env c0.nmem).rot Y.N (c.nreg 130123) := by omega
          rw [hD2, hd02, hiter, heq, iterate_per (N := Y.N) hp.ok.injOn hd0N] at hgt
          exact lt_irrefl _ hgt
      · have heqd : c2.nreg 130124 = c2.nreg 130123 := by omega
        have hper : c.nreg 130130 + 1 = per (Y.env c0.nmem).rot Y.N (c.nreg 130123) := by
          rw [hD2, hd02, hiter] at heqd
          by_contra hne
          exact iterate_ne_of_lt_per (N := Y.N) hp.ok.injOn hd0N (by omega) (by omega) heqd
        have e3 := Exec.constN (P := P) hw2 130125 1 (by omega)
        refine ⟨_, 1 + 2 + 2, .ifLtN_false hlt (.ifLtN_false hgt (Exec.block_cons e3
          (Exec.block_nil e3.wb_right))), by omega, key _ e3.wb_right rfl rfl rfl rfl
          (fun r hr => by simp [hr]) (Or.inr ⟨(by simp), hper⟩)⟩

/-- **The inner loop** over the rotation orbit of `first u`: cost `≤ 50 (deg u + 1) + 2`; at
the end the whole orbit is processed. -/
theorem innerLoop_exec (hY : Y.Good W) (hR0 : Regs Y s L c0)
    (hp : (Y.env c0.nmem).Pre s L lab0) {c : Config} (hI : II Y W s L lab0 c0 c)
    (hdn : c.nreg 130125 = 0) (hj : c.nreg 130130 = 0) :
    ∃ c' k, Exec P W innerLoop c c' k ∧
      k ≤ 50 * (per (Y.env c0.nmem).rot Y.N (c.nreg 130123) + 1) + 2 ∧
      II Y W s L lab0 c0 c' ∧ c'.nreg 130125 = 1 ∧
      c'.nreg 130130 = per (Y.env c0.nmem).rot Y.N (c.nreg 130123) ∧
      c'.nreg 130120 = c.nreg 130120 ∧ c'.nreg 130122 = c.nreg 130122 ∧
      c'.nreg 130123 = c.nreg 130123 ∧
      (∀ i, i < c.nreg 130121 → qV Y c'.nmem i = qV Y c.nmem i) ∧
      c.nreg 130121 ≤ c'.nreg 130121 := by
  set pr := per (Y.env c0.nmem).rot Y.N (c.nreg 130123) with hpr
  obtain ⟨c', k, e, ⟨hI', h120, h122, h123, hq', ht'⟩, htest, hk⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 130125) (b := 130001) (body := innerBody)
    (fun c' => II Y W s L lab0 c0 c' ∧ c'.nreg 130120 = c.nreg 130120 ∧
      c'.nreg 130122 = c.nreg 130122 ∧ c'.nreg 130123 = c.nreg 130123 ∧
      (∀ i, i < c.nreg 130121 → qV Y c'.nmem i = qV Y c.nmem i) ∧
      c.nreg 130121 ≤ c'.nreg 130121)
    (fun c' => 50 * (pr + 1 - c'.nreg 130130 - c'.nreg 130125)) (fun c' h => h.1.wb)
    (fun c1 ⟨hI1, g120, g122, g123, gq, gt⟩ htest => by
      have hone  := (hR0.fr hI1.fr).one
      have hdn1 : c1.nreg 130125 = 0 := by omega
      have hjp1 : c1.nreg 130130 < pr := by
        rcases hI1.dn with h | h
        · rw [hpr, ← g123]; exact h.2
        · omega
      obtain ⟨c2, k2, e2, hk2, hI2, f120, f122, f123, f129, f130, fq, ft, fdn⟩ :=
        innerBody_exec hY hR0 hp hI1 hdn1
      refine ⟨c2, k2, e2, ⟨hI2, f120.trans g120, f122.trans g122, f123.trans g123,
        fun i hi => (fq i (by omega)).trans (gq i hi), gt.trans ft⟩, ?_⟩
      rw [g123, ← hpr] at fdn
      have hd2 : c2.nreg 130125 = 0 ∨ c2.nreg 130125 = 1 := by
        rcases hI2.dn with h | h
        · exact Or.inl h.1
        · exact Or.inr h.1
      rcases fdn with h | h
      · have hlt : c2.nreg 130130 < pr := by
          rcases hI2.dn with h' | h'
          · rw [hpr, ← g123, ← f123]; exact h'.2
          · omega
        rw [h, hdn1, f130]
        have : pr + 1 - (c1.nreg 130130 + 1) - 0 + 1 = pr + 1 - c1.nreg 130130 - 0 := by omega
        rw [f130] at hlt
        omega
      · rw [h, hdn1]
        rcases hd2 with h' | h' <;> rw [h'] <;> rw [f130] at h <;> omega) ⟨hI, rfl, rfl, rfl,
      fun _ _ => rfl, le_rfl⟩
  have hone  := (hR0.fr hI'.fr).one
  have hdn' : c'.nreg 130125 = 1 ∧ c'.nreg 130130 = pr := by
    rcases hI'.dn with h | h
    · omega
    · rwx [hpr, ← h123]
  refine ⟨c', k, e, by rwo [hdn, hj] at hk, hI', hdn'.1, hdn'.2, h120, h122, h123, hq', ht'⟩

end inner

/-! ## The outer loop -/

/-- **The configuration invariant of the outer loop.** -/
structure OI (Y : Lay) (W s L : ℕ) (lab0 : ℕ → ℕ) (c0 c : Config) : Prop where
  wb : WordsBounded W c
  fr : Fr Y c0 c
  inv : (Y.env c0.nmem).Inv s L lab0 (labV Y c.nmem) (levV Y c.nmem) (parV Y c.nmem)
    (qV Y c.nmem) (c.nreg 130120) (c.nreg 130121)

section outer

variable {P : Polygon} {W : ℕ} {Y : Lay} {s L : ℕ} {lab0 : ℕ → ℕ} {c0 : Config}

/-- The head entry: load `u = q h`, `lev u + 1`, `first u`; start the inner loop. -/
theorem headB_exec (hY : Y.Good W) (hR0 : Regs Y s L c0) (hp : (Y.env c0.nmem).Pre s L lab0)
    {c : Config} (hI : OI Y W s L lab0 c0 c) (hht : c.nreg 130120 < c.nreg 130121) :
    ∃ c1 k, Exec P W headB c c1 k ∧ k = 10 ∧ II Y W s L lab0 c0 c1 ∧ c1.nreg 130125 = 0 ∧
      c1.nreg 130130 = 0 ∧ c1.nreg 130120 = c.nreg 130120 ∧ c1.nreg 130121 = c.nreg 130121 ∧
      c1.nmem = c.nmem ∧
      c1.nreg 130123 = (Y.env c0.nmem).first (qV Y c.nmem (c.nreg 130120)) := by
  have hR : Regs Y s L c := hR0.fr hI.fr
  have hw := hI.wb
  have htn : c.nreg 130121 ≤ Y.nv := hI.inv.tn
  have hun : qV Y c.nmem (c.nreg 130120) < Y.nv := hI.inv.qlt _ hht
  have hlev := hI.inv.lev_le _ hht
  have rq : c.nmem (Y.bQ + c.nreg 130120) = qV Y c.nmem (c.nreg 130120) := by
    rw [qV, view_lt (by omega)]
  have rl : c.nmem (Y.bLev + qV Y c.nmem (c.nreg 130120)) =
      levV Y c.nmem (qV Y c.nmem (c.nreg 130120)) := by rw [levV, view_lt hun]
  have rf : c.nmem (Y.bF + qV Y c.nmem (c.nreg 130120)) =
      (Y.env c0.nmem).first (qV Y c.nmem (c.nreg 130120)) :=
    Fr.read hY hI.fr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) hun
  have hfN : (Y.env c0.nmem).first (qV Y c.nmem (c.nreg 130120)) < Y.N := hp.ok.first_lt _ hun
  have := hY.wQ; have := hY.wLev; have := hY.wF; have := hY.wn
  unfold headB
  exec_block
  · sio only [hR.rQ]
  · config_simp; sio only [hR.rQ, hR.rLev, rq]
  · config_simp; sio only [hR.rQ, hR.rLev, rq, rl, hR.one]
  · config_simp; sio only [hR.rQ, hR.rF, rq]
  · omega
  · omega
  · refine ⟨rfl, ⟨‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by config_simp, by config_simp,
      by config_simp, by config_simp, rfl, by config_simp; simp only [hR.rQ, hR.rF, rq, rf]⟩
    · exact Fr.nreg hI.fr (fun r hr => by
        unfold Scr at hr; simp only [Machine.upd_apply]; splao)
    · config_simp; exact hI.inv.start hht
    · config_simp; simp only [hR.rQ, rq]
    · config_simp; simp only [hR.rQ, hR.rLev, rq, rl, hR.one]
    · config_simp; simp only [hR.rQ, hR.rF, rq, rf]
    · config_simp; sirfl only [hR.rQ, hR.rF, rq, rf]
    · config_simp; left
      simp only [hR.rQ, hR.rF, rq, rf]
      exact per_pos (N := Y.N) hp.ok.injOn hfN

/-- **One entry of the queue**: cost `≤ 50 deg u + 63`. -/
theorem outerBody_exec (hY : Y.Good W) (hR0 : Regs Y s L c0) (hp : (Y.env c0.nmem).Pre s L lab0)
    {c : Config} (hI : OI Y W s L lab0 c0 c) (hht : c.nreg 130120 < c.nreg 130121) :
    ∃ c' k, Exec P W outerBody c c' k ∧
      k ≤ 50 * (Y.env c0.nmem).deg (qV Y c.nmem (c.nreg 130120)) + 63 ∧
      OI Y W s L lab0 c0 c' ∧ c'.nreg 130120 = c.nreg 130120 + 1 ∧
      (∀ i, i < c.nreg 130121 → qV Y c'.nmem i = qV Y c.nmem i) := by
  obtain ⟨c1, k1, e1, hk1, hII1, hdn1, hj1, h120, h121, hm1, h123⟩ :=
    headB_exec (P := P) hY hR0 hp hI hht
  obtain ⟨c2, k2, e2, hk2, hII2, hdn2, hj2, g120, g122, g123, gq, gt⟩ :=
    innerLoop_exec (P := P) hY hR0 hp hII1 hdn1 hj1
  have hun : qV Y c.nmem (c.nreg 130120) < Y.nv := hI.inv.qlt _ hht
  have hper : per (Y.env c0.nmem).rot Y.N (c1.nreg 130123) =
      (Y.env c0.nmem).deg (qV Y c.nmem (c.nreg 130120)) := by
    rw [h123]; exact hp.ok.per_first hun
  -- the inner invariant at the end of the orbit
  have hfin : (Y.env c0.nmem).Inv s L lab0 (labV Y c2.nmem) (levV Y c2.nmem) (parV Y c2.nmem)
      (qV Y c2.nmem) (c2.nreg 130120 + 1) (c2.nreg 130121) := by
    refine hII2.inv.finish hp ?_
    rw [hj2, ← hII2.u, g122, hII1.d0]
    rfl
  have hone : c2.nreg 130001 = 1 := (hR0.fr hII2.fr).one
  have hw2 := hII2.wb
  have htn : c2.nreg 130121 ≤ Y.nv := hII2.inv.inv.tn
  have hht2 : c2.nreg 130120 < c2.nreg 130121 := hII2.inv.hlt
  have := hY.wn
  have e3 := Exec.addN (P := P) hw2 130120 130120 130001 (by rwo [hone])
  refine ⟨_, k1 + (k2 + 1), .seq e1 (.seq e2 e3), ?_, ⟨e3.wb_right, ?_, ?_⟩, ?_, ?_⟩
  · rwo [hper] at hk2
  · exact Fr.nreg hII2.fr (fun r hr => by
      unfold Scr at hr; simp only [Machine.upd_apply]; splao)
  · simp only [Machine.upd_same, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Machine.upd_other]
    rwx [hone]
  · simp only [Machine.upd_same]; rw [hone, g120, h120]
  · intro i hi
    rw [gq i (by rwx [h121]), hm1]

/-- **The outer loop**: from the invariant, the loop ends with `h = t`; the cost plus
`70 (nv - t) + 50 (N - Σ_{i<t} deg (q i))` at the end is at most the same quantity at the start
plus `2`. -/
theorem outerLoop_exec (hY : Y.Good W) (hR0 : Regs Y s L c0) (hp : (Y.env c0.nmem).Pre s L lab0)
    {c : Config} (hI : OI Y W s L lab0 c0 c) :
    ∃ c' k, Exec P W outerLoop c c' k ∧
      k + (70 * (Y.nv - c'.nreg 130120) + 50 * (Y.N - ∑ i ∈ Finset.range (c'.nreg 130120),
        (Y.env c0.nmem).deg (qV Y c'.nmem i))) ≤
      70 * (Y.nv - c.nreg 130120) + 50 * (Y.N - ∑ i ∈ Finset.range (c.nreg 130120),
        (Y.env c0.nmem).deg (qV Y c.nmem i)) + 2 ∧
      OI Y W s L lab0 c0 c' ∧ c'.nreg 130120 = c'.nreg 130121 := by
  obtain ⟨c', k, e, hI', htest, hk⟩ := whileLtN_pot (P := P) (W := W) (a := 130120)
    (b := 130121) (body := outerBody) (OI Y W s L lab0 c0)
    (fun c => 70 * (Y.nv - c.nreg 130120) + 50 * (Y.N - ∑ i ∈ Finset.range (c.nreg 130120),
      (Y.env c0.nmem).deg (qV Y c.nmem i))) (fun c h => h.wb)
    (fun c1 hI1 htest => by
      obtain ⟨c2, k2, e2, hk2, hI2, h120, hq⟩ := outerBody_exec (P := P) hY hR0 hp hI1 htest
      refine ⟨c2, k2, e2, hI2, ?_⟩
      have htn : c1.nreg 130121 ≤ Y.nv := hI1.inv.tn
      have hsum : ∑ i ∈ Finset.range (c2.nreg 130120), (Y.env c0.nmem).deg (qV Y c2.nmem i) =
          ∑ i ∈ Finset.range (c1.nreg 130120), (Y.env c0.nmem).deg (qV Y c1.nmem i) +
            (Y.env c0.nmem).deg (qV Y c1.nmem (c1.nreg 130120)) := by
        rw [h120, Finset.sum_range_succ, hq _ htest]
        congr 1
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [hq i (by rwo [Finset.mem_range] at hi)]
      have hle := hI2.inv.sum_deg_le hp.ok (n := c2.nreg 130120) hI2.inv.ht
      rw [hsum] at hle ⊢
      change _ ≤ Y.N at hle
      rw [h120]
      omega) hI
  refine ⟨c', k, e, hk, hI', ?_⟩
  have := hI'.inv.ht
  omega

end outer

/-! ## The whole search -/

section main

variable {P : Polygon} {W : ℕ} {Y : Lay} {s L : ℕ} {c0 : Config}

/-- **Breadth-first search on the RAM.**  From a configuration whose registers hold a good
layout, the label `L` and the source `s` (`Regs`), with the precondition `Pre` (a well-formed
rotation system, `s` unblocked, `L < nv`, the sentinel `nv` in `lab` at every vertex reachable
from `s`), `bfsStmt` runs in at most `70 t + 50 Σ_{i<t} deg (q i) + 11` steps (`t` the
number of reached vertices), changes only the scratch
registers and the arrays `lab`, `lev`, `par`, `q` (`Fr`), and ends with the invariant `Inv` at
`h = t`: the queue holds exactly the vertices reachable from `s` (`Env.Inv.reach_iff`), they are
labelled `L`, the other labels are unchanged, and the levels and parents form a breadth-first
tree (`Env.Inv.par`, `Env.Inv.lev_head_le`). -/
theorem bfs_exec (hY : Y.Good W) (hR0 : Regs Y s L c0)
    (hp : (Y.env c0.nmem).Pre s L (labV Y c0.nmem)) (hw : WordsBounded W c0) :
    ∃ c' k, Exec P W bfsStmt c0 c' k ∧
      k ≤ 70 * c'.nreg 130121 + 50 * ∑ i ∈ Finset.range (c'.nreg 130121),
        (Y.env c0.nmem).deg (qV Y c'.nmem i) + 11 ∧
      OI Y W s L (labV Y c0.nmem) c0 c' ∧ c'.nreg 130120 = c'.nreg 130121 := by
  have hsn : s < Y.nv := hp.s_lt
  have := hY.wLab; have := hY.wLev; have := hY.wQ; have := hY.wn
  have hne1 : Y.bQ ≠ Y.bLab + s := by
    have := hY.d2.2.2.1; ufo Disj at this
  have hne2 : Y.bQ ≠ Y.bLev + s := by
    have := hY.d2.2.2.2.2.1; ufo Disj at this
  have hne3 : Y.bLab + s ≠ Y.bLev + s := by
    have := hY.d2.1; ufo Disj at this
  unfold bfsStmt
  have hinit : ∃ c1 k1, Exec P W initB c0 c1 k1 ∧ k1 ≤ 9 ∧
      OI Y W s L (labV Y c0.nmem) c0 c1 ∧ c1.nreg 130120 = 0 := by
    unfold initB
    exec_block
    · config_simp; rwo [hR0.rLab, hR0.rs]
    · config_simp; rwo [hR0.rLev, hR0.rs]
    · omega
    · omega
    · omega
    · refine ⟨by omega, ⟨‹_›, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a ha => ?_⟩, ?_⟩, by config_simp⟩
      · unfold Scr at hr; simp only [Machine.upd_apply]; splao
      · simp only [Machine.upd_apply, hR0.rQ, hR0.rLab, hR0.rLev, hR0.rs]
        unfold Lay.Written at ha
        splao
      · simp only [Machine.upd_same, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
          Machine.upd_other, hR0.rQ, hR0.rLab, hR0.rLev, hR0.rs, hR0.rL]
        have hq : qV Y (upd (upd (upd c0.nmem Y.bQ s) (Y.bLab + s) L) (Y.bLev + s) 0) =
            Function.update (qV Y c0.nmem) 0 s := by
          unfold qV
          rw [view_upd_out _ _ _ _ _ (by have := hY.d2.2.2.2.2.1; ufo Disj at this),
            view_upd_out _ _ _ _ _ (by have := hY.d2.2.2.1; ufo Disj at this)]
          exact view_upd_in c0.nmem Y.bQ Y.nv 0 s (by omega)
        have hl : labV Y (upd (upd (upd c0.nmem Y.bQ s) (Y.bLab + s) L) (Y.bLev + s) 0) =
            Function.update (labV Y c0.nmem) s L := by
          unfold labV
          rw [view_upd_out _ _ _ _ _ (by have := hY.d2.1; ufo Disj at this),
            view_upd_in _ _ _ _ _ hsn,
            view_upd_out _ _ _ _ _ (by have := hY.d2.2.2.1; ufo Disj at this)]
        have hv : levV Y (upd (upd (upd c0.nmem Y.bQ s) (Y.bLab + s) L) (Y.bLev + s) 0) s = 0 := by
          unfold levV
          rw [view_lt hsn, Machine.upd_same]
        refine Env.Inv.init hp (by rw [hq, Function.update_self]) (fun v hv' => ?_) hv
        rw [hl]
        by_cases hvs : v = s
        · subst hvs; simp
        · rw [Function.update_of_ne hvs, ite_eq_right hvs]
  obtain ⟨c1, k1, e1, hk1, hI1, h0⟩ := hinit
  obtain ⟨c', k, e, hk, hI', ht⟩ := outerLoop_exec (P := P) hY hR0 hp hI1
  refine ⟨c', k1 + k, .seq e1 e, ?_, hI', ht⟩
  have hsum := hI'.inv.sum_deg_le hp.ok (n := c'.nreg 130121) le_rfl
  have htn : c'.nreg 130121 ≤ Y.nv := hI'.inv.tn
  change _ ≤ Y.N at hsum
  rw [h0, Finset.range_zero, Finset.sum_empty, ht] at hk
  omega

end main

end

end Chazelle.Core.Cluster
