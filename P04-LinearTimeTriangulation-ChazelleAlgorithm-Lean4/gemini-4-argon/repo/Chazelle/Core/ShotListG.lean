module

public import Chazelle.Core.ShotListMain

/-!
# The model-generic shot list, part 1: the operation contracts and the context

`ShotListG` generalises the sweep's wrapper `ShotList.shotList` (shoot a horizontal ray at a
list of arcs with at most three vertex holes, keep the first hit) from chain models to **any**
model with a descriptor (`ModelDescAt`), in particular the interior model of `Q` (finding E7-B).
The two places where the chain wrapper uses chain primitives become parameters:

* a **key comparison** `kc a b d e` (`KeyG`): the bit `50210` is the key order of the positions
  `(a, b)` and `(d, e)` (registers of the caller's block), for two positions inside walk edges
  (height codes positive); it replaces `offCmp` in the cutting block;
* an **abscissa comparison** `xc a b d e` (`XG`): the bit `50210` is the order of the
  abscissae of the points of two positions at one height; it replaces `absKey`/`absCmp` in the
  running minimum.

Both run under the caller's **environment** `E` (a predicate on configurations that survives
the wrapper's frames, `Stable`) and the wrapper's constants (`KCtx`), write only registers of the
oracle bands other than the allocator (`OpW`), and leave the memory unchanged (`FrameB`).  The
calling convention of the chain wrapper is kept: the constants `R + 30 = 0`, `R + 31 = 1`, the
address `R + 34` of the word after the model descriptor, so `offCmp` behind a block of copies is
a key comparison of a chain model.

This file: the contracts, the shooting context `ShotCtxG` (and its frame lemma) and the running
minimum `BestG` (the hit position only; no abscissa record).
-/

namespace Chazelle.Core

namespace ShotListG

open Machine Machine.Stmt Programs SignK SweepPrim ShotList
open Chazelle.Visibility (rayPt)

@[expose] public section

/-! ## The contracts of the operations -/

/-- A register of the caller's block `R … R + 299`. -/
def InB (R r : ℕ) : Prop := R ≤ r ∧ r < R + 300

/-- **The write set of an operation**: registers of the oracle bands other than the allocator. -/
def OpW (B : ℕ → Bool) : Prop := ∀ r, B r = true → bandOf r ∈ oracleBands ∧ r ≠ ALLOC

/-- **An environment stable under the wrapper's frames**: writes in the oracle bands and in the
registers `R + 9 … R + 299`, memory changes at or above the allocator, a larger allocator. -/
def Stable (Bo : Finset ℕ) (W R : ℕ) (E : Config → Prop) : Prop :=
  ∀ c c' k, E c → WordsBounded W c' →
    FrameR Bo (fun r => R + 9 ≤ r ∧ r < R + 300) c c' k → E c'

/-- **The facts an operation may use**: the environment, the machine, the model descriptor at
`R` and the wrapper's constants. -/
def KCtx (P : Polygon) (W : ℕ) (M : Model) (R : ℕ) (E : Config → Prop) (c : Config) : Prop :=
  E c ∧ GoodEnv P ∧ hostWords P.n ≤ W ∧ ModelDescAt c.nmem (c.nreg R) (Qof P) M ∧
    ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg R) ∧ c.nreg (R + 30) = 0 ∧
    c.nreg (R + 31) = 1 ∧ c.nreg (R + 34) = c.nreg R + 1

/-- **Contract of a key comparison** (at most `K` steps, writes `Bk`): for two positions inside
walk edges, the bit `50210` is the key order. -/
def KeyG (P : Polygon) (W : ℕ) (M : Model) (R : ℕ) (E : Config → Prop)
    (kc : ℕ → ℕ → ℕ → ℕ → Stmt) (Bk : ℕ → Bool) (K : ℕ) : Prop :=
  ∀ a b d e, InB R a → InB R b → InB R d → InB R e → ∀ c, WordsBounded W c →
    KCtx P W M R E c →
    ProperPos M (Qof P) P.n ⟨c.nreg a, c.nreg b⟩ → c.nreg a < M.W.n → 0 < c.nreg b →
    ProperPos M (Qof P) P.n ⟨c.nreg d, c.nreg e⟩ → c.nreg d < M.W.n → 0 < c.nreg e →
    c.nreg ALLOC + K ≤ W →
    ∃ c' k, Exec P W (kc a b d e) c c' k ∧ k ≤ K ∧
      BitIs c' 50210 (M.key (Qof P) ⟨c.nreg a, c.nreg b⟩ < M.key (Qof P) ⟨c.nreg d, c.nreg e⟩) ∧
      FrameB Bk c c'

/-- **Contract of an abscissa comparison** (at most `K` steps, writes `Bx`): for two positions
whose points lie at one admissible height (`Y`), the bit `50210` is the order of their
abscissae. -/
def XG (P : Polygon) (W : ℕ) (M : Model) (R : ℕ) (E : Config → Prop) (Y : ℝ → Prop)
    (xc : ℕ → ℕ → ℕ → ℕ → Stmt) (Bx : ℕ → Bool) (K : ℕ) : Prop :=
  ∀ a b d e, InB R a → InB R b → InB R d → InB R e → ∀ c, WordsBounded W c →
    KCtx P W M R E c →
    ProperPos M (Qof P) P.n ⟨c.nreg a, c.nreg b⟩ → c.nreg a < M.W.n →
    ProperPos M (Qof P) P.n ⟨c.nreg d, c.nreg e⟩ → c.nreg d < M.W.n →
    (M.pos (Qof P) ⟨c.nreg a, c.nreg b⟩).2 = (M.pos (Qof P) ⟨c.nreg d, c.nreg e⟩).2 →
    Y (M.pos (Qof P) ⟨c.nreg a, c.nreg b⟩).2 → c.nreg ALLOC + K ≤ W →
    ∃ c' k, Exec P W (xc a b d e) c c' k ∧ k ≤ K ∧
      BitIs c' 50210 ((M.pos (Qof P) ⟨c.nreg a, c.nreg b⟩).1 <
        (M.pos (Qof P) ⟨c.nreg d, c.nreg e⟩).1) ∧
      FrameB Bx c c'

/-! ## Descriptors survive memory changes above the allocator -/

/-- **A well-formed model descriptor** below `E` survives a change of the memory at or above `E`
(and a larger bound), for both kinds of models. -/
theorem modelDescG_keep {P : Polygon} {m m' : ℕ → ℕ} {D E E' : ℕ} {M : Model}
    (hwf : ModelDescWF P E m D) (hMD : ModelDescAt m D (Qof P) M)
    (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    ModelDescWF P E' m' D ∧ ModelDescAt m' D (Qof P) M := by
  rcases hMD with ⟨h0, H, C, hC, rfl⟩ | ⟨h1, hbit, rfl⟩
  · obtain ⟨w', h0', hC'⟩ := modelDesc_keep hwf h0 hC he hE
    exact ⟨w', Or.inl ⟨h0', H, C, hC', rfl⟩⟩
  · have hD := hwf.1
    have e0 : m' D = m D := he _ (by omega)
    have e1 : m' (D + 1) = m (D + 1) := he _ (by omega)
    refine ⟨⟨by omega, fun h => by rw [e0, h1] at h; exact absurd h (by norm_num)⟩,
      Or.inr ⟨by rw [e0, h1], by rwa [e1], rfl⟩⟩

/-! ## Host regularity of the descriptor (spec amendment G10) -/

/-- **The host of a chain descriptor at `D + 1` is regular** (the shooter's precondition since
amendment G10). -/
def HReg (P : Polygon) (m : ℕ → ℕ) (D : ℕ) : Prop :=
  m D = 0 → ∀ H C, ChainDescAt m (D + 1) (Qof P) H C → HostRegular (Qof P).n H

/-- Host regularity survives a change of the memory at or above the bound of a well-formed
descriptor. -/
theorem hreg_keep {P : Polygon} {m m' : ℕ → ℕ} {D E : ℕ} {M : Model}
    (hwf : ModelDescWF P E m D) (hMD : ModelDescAt m D (Qof P) M) (h : HReg P m D)
    (he : ∀ a, a < E → m' a = m a) : HReg P m' D := by
  intro h0 H C hC
  have hD := hwf.1
  have h0' : m D = 0 := by rwa [← he D (by omega)]
  rcases hMD with ⟨-, H₀, C₀, hC₀, -⟩ | ⟨h1, -, -⟩
  · obtain ⟨-, -, hEb, -⟩ := (hwf.2 h0').2 H₀ C₀ hC₀
    have hH : HostAt m' (m (D + 1)) H₀ := hostAt_agree hC₀.1 hEb he
    have e1 : m' (D + 1) = m (D + 1) := he _ (by omega)
    have : H = H₀ := NFLoc.hostAt_unique (by rw [← e1]; exact hC.1) hH
    subst this
    exact h h0' H C₀ hC₀
  · rw [h0'] at h1; exact absurd h1 (by norm_num)

/-! ## The shooting context -/

/-- **The shooting context** at `R` for the model `M`: the facts of the operations (`KCtx`), the
shooter's context `X` with room for the weight bound, the model admitted by `Ok`, the direction
bit. -/
def ShotCtxG (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop) (R : ℕ)
    (M : Model) (E : Config → Prop) (c : Config) : Prop :=
  KCtx P W M R E c ∧ X.holds P c.nmem (c.nreg (R + 8)) (c.nreg ALLOC) ∧
    c.nreg (R + 7) ≤ X.cap P c.nmem (c.nreg (R + 8)) ∧ Ok P M ∧
    BitIs c (R + 35) (c.nreg (R + 6) = 1) ∧ HReg P c.nmem (c.nreg R)

/-- **The shooting context survives** a frame of the oracle bands and the registers
`R + 9 … R + 299` that keeps the registers `R … R + 8` and `R + 30 … R + 35`. -/
theorem ShotCtxG.frame {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
    (hXl : X.CapLocal) {R : ℕ} {M : Model} {E : Config → Prop} {Bo : Finset ℕ}
    (hS : Stable Bo W R E)
    {c c' : Config} {Wr : ℕ → Prop} {k : ℕ} (h : ShotCtxG P W X Ok R M E c)
    (hw' : WordsBounded W c') (hf : FrameR Bo Wr c c' k)
    (hWr : ∀ r, Wr r → R + 9 ≤ r ∧ r < R + 300)
    (hr : ∀ i, (i ≤ 8 ∨ (30 ≤ i ∧ i ≤ 35)) → c'.nreg (R + i) = c.nreg (R + i)) :
    ShotCtxG P W X Ok R M E c' := by
  obtain ⟨⟨hE, hG, hHW, hMD, hmwf, h30, h31, h34⟩, hX, hcap, hOk, hσ, hreg⟩ := h
  have hf' := hf.mono le_rfl hWr le_rfl
  obtain ⟨-, -, hmem, -, -, hA, -⟩ := hf
  have he : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a := hmem
  have r0 : c'.nreg R = c.nreg R := by simpa using hr 0 (Or.inl (by omega))
  obtain ⟨mw', hMD'⟩ := modelDescG_keep hmwf hMD he hA
  refine ⟨⟨hS c c' k hE hw' hf', hG, hHW, by rwa [r0], by rwa [r0],
    by rw [hr 30 (Or.inr (by omega)), h30], by rw [hr 31 (Or.inr (by omega)), h31],
    by rw [hr 34 (Or.inr (by omega)), r0, h34]⟩, ?_, ?_, hOk,
    ⟨by rw [hr 35 (Or.inr (by omega))]; exact hσ.1,
      by rw [hr 35 (Or.inr (by omega)), hr 6 (Or.inl (by omega))]; exact hσ.2⟩,
    by rw [r0]; exact hreg_keep hmwf hMD hreg he⟩
  · rw [hr 8 (Or.inl (by omega))]
    exact X.mono P _ _ _ _ hA (X.local_ P _ _ _ _ (fun a ha => (he a ha).symm) hX)
  · rw [hr 8 (Or.inl (by omega)), hr 7 (Or.inl (by omega)), hXl P c.nmem c'.nmem _ _ he hX]
    exact hcap

/-- A register of the caller's block is outside a band set avoiding the block's band. -/
theorem band_RB {R : ℕ} (hR : RegsOK R) {Bo : Finset ℕ} (hRB : bandOf R ∉ Bo) {i : ℕ}
    (hi : i < 300) : bandOf (R + i) ∉ Bo := by
  rwa [band_block hR (by omega) (by omega)]

/-- A register of the caller's block is not written by an operation. -/
theorem opW_R {B : ℕ → Bool} (hB : OpW B) {R : ℕ} (hR : RegsOK R) {r : ℕ} (h1 : R ≤ r)
    (h2 : r < R + 300) : B r = false := by
  cases hb : B r
  · rfl
  · have := (hB r hb).1
    have h' := band_R hR (i := r - R) (by omega)
    rw [show R + (r - R) = r by omega] at h'
    exact absurd this h'

/-- The allocator is not written by an operation. -/
theorem opW_alloc {B : ℕ → Bool} (hB : OpW B) : B ALLOC = false := by
  cases hb : B ALLOC
  · rfl
  · exact absurd rfl (hB _ hb).2

/-! ## The running minimum -/

/-- **The running minimum** at `R` describes the first hit of the ray from `z` in direction `σ`
on `S` in the model `M` (the hit position in `R + 21`, `R + 22`). -/
def BestG (P : Polygon) (M : Model) (R : ℕ) (c : Config) (S : Set Point) (z : Point) (σ : ℝ) :
    Prop :=
  c.nreg (R + 20) ≤ 1 ∧
    (c.nreg (R + 20) = 1 → ∃ t, FirstHit S z σ t ∧
      ProperPos M (Qof P) P.n ⟨c.nreg (R + 21), c.nreg (R + 22)⟩ ∧
      c.nreg (R + 21) < M.W.n ∧
      M.pos (Qof P) ⟨c.nreg (R + 21), c.nreg (R + 22)⟩ = rayPt z σ t) ∧
    (c.nreg (R + 20) ≠ 1 → NoHit S z σ)

/-- The running minimum depends only on its registers. -/
theorem BestG.congr {P : Polygon} {M : Model} {R : ℕ} {c c' : Config} {S : Set Point} {z : Point}
    {σ : ℝ} (h : BestG P M R c S z σ) (e0 : c'.nreg (R + 20) = c.nreg (R + 20))
    (e1 : c'.nreg (R + 21) = c.nreg (R + 21)) (e2 : c'.nreg (R + 22) = c.nreg (R + 22)) :
    BestG P M R c' S z σ := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨by rwa [e0], fun hf => ?_, fun hf => h2 (by rwa [← e0])⟩
  obtain ⟨t, ht, hp, he, hpos⟩ := h1 (by rwa [← e0])
  exact ⟨t, ht, by rwa [e1, e2], by rwa [e1], by rwa [e1, e2]⟩

end

end ShotListG

end Chazelle.Core
