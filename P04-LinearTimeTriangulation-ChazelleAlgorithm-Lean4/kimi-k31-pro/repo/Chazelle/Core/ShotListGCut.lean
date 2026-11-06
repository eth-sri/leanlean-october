module

public import Chazelle.Core.ShotListG
public import Chazelle.Rwx
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics

/-!
# The model-generic shot list, part 2: the cutting block

`cutBG kc R ℓ` is the sweep's cutting block `ShotList.cutB` with the correction of the bit
`a < b` for two interior positions of one edge done by the key comparison `kc` (`offBG`)
instead of `offCmp`.  `cutBG_exec`: the pieces `levPieces` of the arc of level `ℓ` in the
registers of the next level, for any model `M` with a key comparison (`KeyG`).
-/

namespace Chazelle.Core

namespace ShotListG

open Machine Machine.Stmt Programs SignK SweepPrim ShotList
open Chazelle.Chain (sideInArc)

@[expose] public section

/-! ## Operations keep the context -/

/-- **A write set of the wrapper's blocks**: scratch registers of the caller's block (not the
inputs `R … R + 8`, not the constants `R + 30 … R + 35`) or registers of an operation. -/
def WrG (R : ℕ) (B : ℕ → Bool) : Prop :=
  ∀ r, B r = true → (R + 9 ≤ r ∧ r < R + 30) ∨ (R + 36 ≤ r ∧ r < R + 300) ∨
    (bandOf r ∈ oracleBands ∧ r ≠ ALLOC)

theorem WrG.alloc {R : ℕ} (hR : RegsOK R) {B : ℕ → Bool} (h : WrG R B) : B ALLOC = false := by
  cases hb : B ALLOC
  · rfl
  · have := h _ hb
    unfold RegsOK at hR; unfold ALLOC at this
    rcases this with h1 | h1 | h1
    · omega
    · omega
    · exact absurd rfl h1.2

theorem WrG.keep {R : ℕ} (hR : RegsOK R) {B : ℕ → Bool} (h : WrG R B) {i : ℕ}
    (hi : i < 9 ∨ (30 ≤ i ∧ i < 36)) : B (R + i) = false := by
  cases hb : B (R + i)
  · rfl
  · have := h _ hb
    rcases this with h1 | h1 | h1
    · omega
    · omega
    · exact absurd h1.1 (band_R hR (by omega))

theorem WrG.frameR {R : ℕ} (hR : RegsOK R) {B : ℕ → Bool} (h : WrG R B) {Bo : Finset ℕ}
    (hBo : oracleBands ⊆ Bo) {c c' : Config} (hf : FrameB B c c') (k : ℕ) :
    FrameR Bo (fun r => R + 9 ≤ r ∧ r < R + 300) c c' k :=
  FrameR.of_frameB hf (fun r hr => by
    rcases h r hr with h1 | h1 | h1
    · exact Or.inl ⟨h1.1, by omega⟩
    · exact Or.inl ⟨by omega, h1.2⟩
    · exact Or.inr (hBo h1.1)) (h.alloc hR) k

/-- **The operations' context survives** a register frame of the wrapper's blocks. -/
theorem KCtx.of_frameB {P : Polygon} {W : ℕ} {M : Model} {R : ℕ} (hR : RegsOK R)
    {E : Config → Prop} {Bo : Finset ℕ} (hBo : oracleBands ⊆ Bo) (hS : Stable Bo W R E) {c c' : Config} {B : ℕ → Bool}
    (h : KCtx P W M R E c) (hw' : WordsBounded W c') (hf : FrameB B c c') (hB : WrG R B) :
    KCtx P W M R E c' := by
  obtain ⟨hE, hG, hHW, hMD, hmwf, h30, h31, h34⟩ := h
  have k : ∀ i, (i < 9 ∨ (30 ≤ i ∧ i < 36)) → c'.nreg (R + i) = c.nreg (R + i) := fun i hi =>
    hf.1 _ (hB.keep hR hi)
  have r0 : c'.nreg R = c.nreg R := by simpa using k 0 (by omega)
  have hA : c'.nreg ALLOC = c.nreg ALLOC := hf.1 _ (hB.alloc hR)
  have hm  := hf.2.2.1
  exact ⟨hS c c' 0 hE hw' (hB.frameR hR hBo hf 0), hG, hHW, by rwx [hm, r0],
    by rwx [hm, r0, hA], by rw [k 30 (by omega), h30], by rw [k 31 (by omega), h31],
    by rw [k 34 (by omega), r0, h34]⟩

/-! ## The correction of `a < b` -/

/-- The correction of the bit `a < b` (`R + 100`) by the key comparison `kc`, when `a`, `b` are
interior positions of one edge. -/
def offBG (kc : ℕ → ℕ → ℕ → ℕ → Stmt) (R ℓ : ℕ) : Stmt :=
  .ifLtN (rL R ℓ) (rL R ℓ + 2) .skip (.ifLtN (rL R ℓ + 2) (rL R ℓ) .skip
    (.ifLtN (R + 30) (rL R ℓ + 1) (.ifLtN (R + 30) (rL R ℓ + 3)
      (.seq (kc (rL R ℓ) (rL R ℓ + 1) (rL R ℓ + 2) (rL R ℓ + 3))
        (.instr (.copyN (R + 100) 50210))) .skip) .skip))

/-- The registers written by `offBG`. -/
def BoffG (R : ℕ) (Bk : ℕ → Bool) (r : ℕ) : Bool := r == R + 100 || Bk r

/-- **The correction of `a < b`**: afterwards the bit `R + 100` is the key order of `a`, `b`. -/
theorem offBG_exec {P : Polygon} {W : ℕ} {M : Model} {R ℓ : ℕ} {E : Config → Prop}
    {kc : ℕ → ℕ → ℕ → ℕ → Stmt} {Bk : ℕ → Bool} {K : ℕ} (hk : KeyG P W M R E kc Bk K)
    (hℓ : ℓ ≤ 2) (c : Config) (hw : WordsBounded W c) (hctx : KCtx P W M R E c)
    (hroom : c.nreg ALLOC + K ≤ W)
    (ha : NormPos M (Qof P) P.n (posR c (rL R ℓ, rL R ℓ + 1)))
    (hb : NormPos M (Qof P) P.n (posR c (rL R ℓ + 2, rL R ℓ + 3)))
    (hae : c.nreg (rL R ℓ) < M.W.n) (hbe : c.nreg (rL R ℓ + 2) < M.W.n)
    (hbit : BitIs c (R + 100) (LexLt (c.nreg (rL R ℓ)) (ibv (c.nreg (rL R ℓ + 1)))
      (c.nreg (rL R ℓ + 2)) (ibv (c.nreg (rL R ℓ + 3))))) :
    ∃ c' k, Exec P W (offBG kc R ℓ) c c' k ∧ k ≤ K + 10 ∧
      BitIs c' (R + 100) (M.key (Qof P) (posR c (rL R ℓ, rL R ℓ + 1)) <
        M.key (Qof P) (posR c (rL R ℓ + 2, rL R ℓ + 3))) ∧
      FrameB (BoffG R Bk) c c' := by
  set L := rL R ℓ with hL
  have hz : c.nreg (R + 30) = 0 := hctx.2.2.2.2.2.1
  have hne_of : ¬ (c.nreg L = c.nreg (L + 2) ∧ 0 < c.nreg (L + 1) ∧ 0 < c.nreg (L + 3)) →
      BitIs c (R + 100) (M.key (Qof P) (posR c (L, L + 1)) <
        M.key (Qof P) (posR c (L + 2, L + 3))) := fun hne => by
    have := lexLt_iff_key ha hb hne
    simp only [posR] at this ⊢
    exact ⟨hbit.1, hbit.2.trans this⟩
  have fr0 : FrameB (BoffG R Bk) c c := FrameB.refl _ _
  unfold offBG
  by_cases h1 : c.nreg L < c.nreg (L + 2)
  · exact ⟨c, _, .ifLtN_true h1 (.skip hw), by omega, hne_of (by omega), fr0⟩
  by_cases h2 : c.nreg (L + 2) < c.nreg L
  · exact ⟨c, _, .ifLtN_false h1 (.ifLtN_true h2 (.skip hw)), by omega, hne_of (by omega), fr0⟩
  by_cases h3 : c.nreg (R + 30) < c.nreg (L + 1)
  swap
  · exact ⟨c, _, .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_false h3 (.skip hw))), by omega,
      hne_of (by omega), fr0⟩
  by_cases h4 : c.nreg (R + 30) < c.nreg (L + 3)
  swap
  · exact ⟨c, _, .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_true h3 (.ifLtN_false h4 (.skip hw)))),
      by omega, hne_of (by omega), fr0⟩
  -- two interior positions of one edge: the key comparison
  have iL : ∀ i, i < 4 → InB R (L + i) := fun i hi => by ruo [hL] InB rL
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, f₁⟩ := hk L (L + 1) (L + 2) (L + 3) (iL 0 (by omega))
    (iL 1 (by omega)) (iL 2 (by omega)) (iL 3 (by omega)) c hw hctx ha.1 hae
    (by omega) hb.1 hbe (by omega) hroom
  have e₂ := Exec.copyN (P := P) e₁.wb_right (R + 100) 50210
  have ex : Exec P W (offBG kc R ℓ) c _ _ :=
    .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_true h3 (.ifLtN_true h4 (.seq e₁ e₂))))
  refine ⟨_, _, ex, by omega, ⟨?_, ?_⟩, ?_⟩
  · simp only [upd_same]; exact b₁.1
  · simp only [upd_same]; exact b₁.2
  · have g1 : FrameB (BoffG R Bk) c c₁ := frameB_mono f₁ (fun r hr => by simp [BoffG, hr])
    have g2 : FrameB (BoffG R Bk) c₁ _ := frameB_mono (exec_frameB e₂
      (show wr (Bone (R + 100)) (.instr (.copyN (R + 100) 50210)) = true by
        simp [wr, wrOK, Bone])) (fun r hr => by
          simp only [Bone, beq_iff_eq] at hr; subst hr; simp [BoffG])
    exact g1.trans g2

/-! ## The cutting block -/

/-- **The cutting block of level `ℓ`** with the key comparison `kc`. -/
def cutBG (kc : ℕ → ℕ → ℕ → ℕ → Stmt) (R ℓ : ℕ) : Stmt :=
  .seq (kltSeq (R + 30) (cmpList R ℓ)) (.seq (offBG kc R ℓ) (.seq (formB R)
    (selB (rL R ℓ) (R + 10 + 2 * ℓ) (R + 11 + 2 * ℓ) (R + 30) (rL R ℓ + 10) (rL R ℓ + 4)
      (rL R ℓ + 8) (R + 30 + ℓ) (R + 9) (R + 120) (R + 140) (R + 160) (R + 180) (R + 200)
      (R + 220))))

/-- The registers written by `cutBG`. -/
def BcutG (R ℓ : ℕ) (Bk : ℕ → Bool) (r : ℕ) : Bool :=
  Bouts (cmpList R ℓ) r || BoffG R Bk r || Bform R r || decide (rL R ℓ + 4 ≤ r ∧ r < rL R ℓ + 14)

theorem bouts_range {R ℓ r : ℕ} (h : Bouts (cmpList R ℓ) r = true) : R + 100 ≤ r ∧ r < R + 108 := by
  simp only [Bouts, cmpOuts, cmpList, List.map_cons, List.map_nil, List.contains_eq_mem,
    List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq] at h
  omega

/-- The cutting block writes scratch registers and registers of the key comparison. -/
theorem wrG_cut {R ℓ : ℕ} (hℓ : ℓ ≤ 2) {Bk : ℕ → Bool} (hBk : OpW Bk) : WrG R (BcutG R ℓ Bk) :=
  fun r hr => by
    simp only [BcutG, BoffG, Bool.or_eq_true, beq_iff_eq] at hr
    rcases hr with ((h | h | h) | h) | h
    · have := bouts_range h; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inr (hBk r h))
    · simp only [Bform, decide_eq_true_eq] at h; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · simp only [decide_eq_true_eq] at h; unfold rL at h; exact Or.inr (Or.inl ⟨by omega, by omega⟩)

/-- **The cutting block of level `ℓ`**: the pieces `levPieces` in the registers of the next
level (`rL R ℓ + 10 …`, `rL R ℓ + 4 …`, their number in `rL R ℓ + 8`). -/
theorem cutBG_exec {P : Polygon} {W : ℕ} {M : Model} {R ℓ : ℕ} (hR : RegsOK R) (hℓ : ℓ ≤ 2)
    {E : Config → Prop} {Bo : Finset ℕ} (hBo : oracleBands ⊆ Bo) (hS : Stable Bo W R E)
    {kc : ℕ → ℕ → ℕ → ℕ → Stmt} {Bk : ℕ → Bool} {K : ℕ}
    (hk : KeyG P W M R E kc Bk K) (hBk : OpW Bk) (c : Config) (hw : WordsBounded W c)
    (hW : 2 ≤ W) (hctx : KCtx P W M R E c) (hroom : c.nreg ALLOC + K ≤ W)
    (ha : NormPos M (Qof P) P.n (posR c (rL R ℓ, rL R ℓ + 1)))
    (hb : NormPos M (Qof P) P.n (posR c (rL R ℓ + 2, rL R ℓ + 3)))
    (hae : c.nreg (rL R ℓ) < M.W.n) (hbe : c.nreg (rL R ℓ + 2) < M.W.n) :
    ∃ c' k, Exec P W (cutBG kc R ℓ) c c' k ∧ k ≤ K + 500 ∧
      PiecesAt c' (rL R ℓ + 10) (rL R ℓ + 4) (rL R ℓ + 8)
        (levPieces M (Qof P) (c.nreg (R + 30 + ℓ) < c.nreg (R + 9))
          (posR c (rL R ℓ, rL R ℓ + 1)) (posR c (rL R ℓ + 2, rL R ℓ + 3))
          (c.nreg (R + 10 + 2 * ℓ)) (c.nreg (R + 11 + 2 * ℓ))) ∧
      FrameB (BcutG R ℓ Bk) c c' := by
  set L := rL R ℓ with hL
  have hLd : L = R + 40 + 10 * ℓ := rfl
  set Q := Qof P
  set a := posR c (L, L + 1) with ha_def
  set b := posR c (L + 2, L + 3) with hb_def
  set x := c.nreg (R + 10 + 2 * ℓ)
  set y := c.nreg (R + 11 + 2 * ℓ)
  have hz : c.nreg (R + 30) = 0 := hctx.2.2.2.2.2.1
  have hX : NormPos M Q P.n ⟨x, 0⟩ := normPos_vtx M Q P.n x
  have hY : NormPos M Q P.n ⟨y, 0⟩ := normPos_vtx M Q P.n y
  -- the comparisons
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, f₁⟩ := kltSeq_exec (P := P) (by omega) (R + 30) (cmpList R ℓ) c hw
    hz (cmpList_ok hℓ)
  have in₁ : ∀ r, (r < R + 100 ∨ R + 108 ≤ r) → c₁.nreg r = c.nreg r := fun r hr =>
    f₁.1 r (by
      cases hb : Bouts (cmpList R ℓ) r
      · rfl
      · have := bouts_range hb; omega)
  have mem : ∀ t ∈ cmpList R ℓ, BitIs c₁ t.2.2.2.2 (LexLt (c.nreg t.1) (ibv (c.nreg t.2.1))
      (c.nreg t.2.2.1) (ibv (c.nreg t.2.2.2.1))) := b₁
  simp only [cmpList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at mem
  obtain ⟨bab, bax, bxa, bay, byb, bxb, bxy, byx⟩ := mem
  rw [hz] at bax bxa bay byb bxb bxy byx
  -- the key order
  have vtx : ∀ (u v : WPos), NormPos M Q P.n u → NormPos M Q P.n v → (u.hgt = 0 ∨ v.hgt = 0) →
      (LexLt u.edge (ibv u.hgt) v.edge (ibv v.hgt) ↔ M.key Q u < M.key Q v) :=
    fun u v hu hv h0 => lexLt_iff_key hu hv (by omega)
  have kax : BitIs c₁ (R + 101) (M.key Q a < M.key Q ⟨x, 0⟩) :=
    ⟨bax.1, bax.2.trans (vtx _ _ ha hX (Or.inr rfl))⟩
  have kxa : BitIs c₁ (R + 102) (M.key Q ⟨x, 0⟩ < M.key Q a) :=
    ⟨bxa.1, bxa.2.trans (vtx _ _ hX ha (Or.inl rfl))⟩
  have kay : BitIs c₁ (R + 103) (M.key Q a < M.key Q ⟨y, 0⟩) :=
    ⟨bay.1, bay.2.trans (vtx _ _ ha hY (Or.inr rfl))⟩
  have kyb : BitIs c₁ (R + 104) (M.key Q ⟨y, 0⟩ < M.key Q b) :=
    ⟨byb.1, byb.2.trans (vtx _ _ hY hb (Or.inl rfl))⟩
  have kxb : BitIs c₁ (R + 105) (M.key Q ⟨x, 0⟩ < M.key Q b) :=
    ⟨bxb.1, bxb.2.trans (vtx _ _ hX hb (Or.inl rfl))⟩
  have kxy : BitIs c₁ (R + 106) (M.key Q ⟨x, 0⟩ < M.key Q ⟨y, 0⟩) :=
    ⟨bxy.1, bxy.2.trans (vtx _ _ hX hY (Or.inl rfl))⟩
  have kyx : BitIs c₁ (R + 107) (M.key Q ⟨y, 0⟩ < M.key Q ⟨x, 0⟩) :=
    ⟨byx.1, byx.2.trans (vtx _ _ hY hX (Or.inl rfl))⟩
  -- the correction of `a < b`
  have gL0 : c₁.nreg L = c.nreg L := in₁ _ (by omega)
  have gL1 : c₁.nreg (L + 1) = c.nreg (L + 1) := in₁ _ (by omega)
  have gL2 : c₁.nreg (L + 2) = c.nreg (L + 2) := in₁ _ (by omega)
  have gL3 : c₁.nreg (L + 3) = c.nreg (L + 3) := in₁ _ (by omega)
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := in₁ _ (by unfold ALLOC; ufo RegsOK at hR)
  have pa : posR c₁ (L, L + 1) = a := by
    simp only [posR, ha_def, WPos.mk.injEq]; exact ⟨gL0, gL1⟩
  have pb : posR c₁ (L + 2, L + 3) = b := by
    simp only [posR, hb_def, WPos.mk.injEq]; exact ⟨gL2, gL3⟩
  have ctx₁ : KCtx P W M R E c₁ := KCtx.of_frameB hR hBo hS hctx e₁.wb_right f₁ (fun r hr => by
    have := bouts_range hr; exact Or.inr (Or.inl ⟨by omega, by omega⟩))
  obtain ⟨c₂, k₂, e₂, hk₂, kab, f₂⟩ := offBG_exec (P := P) hk hℓ c₁ e₁.wb_right ctx₁
    (by rwx [hA1]) (by rwx [pa]) (by rwx [pb])
    (by rwx [gL0]) (by rwx [gL2])
    (by rw [gL0, gL1, gL2, gL3]; exact bab)
  rw [pa, pb] at kab
  have o₂ : ∀ r, (R + 100 < r ∧ r < R + 300) → BoffG R Bk r = false := fun r hr => by
    simp only [BoffG, opW_R hBk hR (by omega) hr.2, Bool.or_false, beq_eq_false_iff_ne]
    omega
  have ks := fun {r : ℕ} {p : Prop} (h : BitIs c₁ r p) (hr : R + 100 < r ∧ r < R + 300) =>
    bitIs_keep h f₂ (o₂ r hr)
  -- the six tests
  obtain ⟨c₃, k₃, e₃, hk₃, t1, t2, t3, t4, t5, t6, f₃⟩ := formB_exec (P := P) R c₂ e₂.wb_right
    hW kab (ks kax (by omega)) (ks kxa (by omega)) (ks kay (by omega)) (ks kyb (by omega))
    (ks kxb (by omega)) (ks kxy (by omega)) (ks kyx (by omega))
  -- registers of `c` read by the selection
  have gR : ∀ i, i < 100 → c₃.nreg (R + i) = c.nreg (R + i) := fun i hi => by
    rw [f₃.1 (R + i) (by sio only [Bform, decide_eq_false_iff_not]),
      f₂.1 (R + i) (by
        simp only [BoffG, opW_R hBk hR (r := R + i) (by omega) (by omega), Bool.or_false,
          beq_eq_false_iff_ne]; omega), in₁ (R + i) (Or.inl (by omega))]
  have gR' : ∀ r, R ≤ r → r < R + 100 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    have := gR (r - R) (by omega)
    rwa [show R + (r - R) = r by omega] at this
  have z3 : c₃.nreg (R + 30) = 0 := by rw [gR 30 (by omega), hz]
  obtain ⟨c₄, k₄, e₄, hk₄, pc₄, r₄, m₄, rr₄, rm₄, o₄⟩ := selB_exec (P := P) c₃ e₃.wb_right hW
    (L := L) (hx := R + 10 + 2 * ℓ) (hy := R + 11 + 2 * ℓ) (z := R + 30) (N := L + 10)
    (S := L + 4) (Cn := L + 8) (hpA := R + 30 + ℓ) (hpB := R + 9) (c1 := R + 120)
    (c2 := R + 140) (c3 := R + 160) (c4 := R + 180) (c5 := R + 200) (c6 := R + 220)
    (by intro e o ho; cases e <;> simp only [End.regs] <;> omega) (by omega) (by omega)
    (by omega) z3 t1.1 t2.1 t3.1 t4.1 t5.1 t6.1
  have ex : Exec P W (cutBG kc R ℓ) c c₄ (k₁ + (k₂ + (k₃ + k₄))) := .seq e₁ (.seq e₂ (.seq e₃ e₄))
  refine ⟨c₄, _, ex, by sio only [cmpList, List.length_cons, List.length_nil] at hk₁,
    ?_, ?_⟩
  · -- the pieces
    have hsel : selPos c₃ L (R + 10 + 2 * ℓ) (R + 11 + 2 * ℓ) (R + 30) =
        fun tl => tl.map fun e => (End.val a b ⟨x, 0⟩ ⟨y, 0⟩ e.1, End.val a b ⟨x, 0⟩ ⟨y, 0⟩ e.2) := by
      funext tl
      unfold selPos
      congr 1
      funext e
      have ev : ∀ u : End, posR c₃ (End.regs L (R + 10 + 2 * ℓ) (R + 11 + 2 * ℓ) (R + 30) u) =
          End.val a b ⟨x, 0⟩ ⟨y, 0⟩ u := by
        intro u
        cases u <;> simp only [End.regs, End.val, posR, ha_def, hb_def, WPos.mk.injEq]
        · exact ⟨gR' _ (by omega) (by omega), gR' _ (by omega) (by omega)⟩
        · exact ⟨gR' _ (by omega) (by omega), gR' _ (by omega) (by omega)⟩
        · exact ⟨gR' _ (by omega) (by omega), z3⟩
        · exact ⟨gR' _ (by omega) (by omega), z3⟩
      rw [ev, ev]
    rw [hsel] at pc₄
    have hp3 : (c₃.nreg (R + 30 + ℓ) < c₃.nreg (R + 9)) ↔
        (c.nreg (R + 30 + ℓ) < c.nreg (R + 9)) := by
      rw [gR' _ (by omega) (by omega), gR' _ (by omega) (by omega)]
    unfold levPieces
    by_cases hp : c.nreg (R + 30 + ℓ) < c.nreg (R + 9)
    · have hd : decide (c₃.nreg (R + 30 + ℓ) < c₃.nreg (R + 9)) = true := by
        simp [hp3.2 hp]
      rw [hd] at pc₄
      rw [ite_yes _ _ hp]
      unfold cut1
      rw [cutK_eq_selT (M.key Q a) (M.key Q b) (M.key Q ⟨x, 0⟩) (M.key Q ⟨y, 0⟩) a b ⟨x, 0⟩
        ⟨y, 0⟩ (c1 := decide (c₃.nreg (R + 120) = 1)) (c2 := decide (c₃.nreg (R + 140) = 1))
        (c3 := decide (c₃.nreg (R + 160) = 1)) (c4 := decide (c₃.nreg (R + 180) = 1))
        (c5 := decide (c₃.nreg (R + 200) = 1)) (c6 := decide (c₃.nreg (R + 220) = 1))
        (by rw [decide_eq_true_iff]; exact t1.2) (by rw [decide_eq_true_iff]; exact t2.2)
        (by rw [decide_eq_true_iff]; exact t3.2) (by rw [decide_eq_true_iff]; exact t4.2)
        (by rw [decide_eq_true_iff]; exact t5.2) (by rw [decide_eq_true_iff]; exact t6.2)]
      exact pc₄
    · have hd : decide (c₃.nreg (R + 30 + ℓ) < c₃.nreg (R + 9)) = false := by
        simp only [decide_eq_false_iff_not]; exact fun h => hp (hp3.1 h)
      rw [hd] at pc₄
      rw [ite_no _ _ hp]
      exact pc₄
  · -- the frame
    have f₄ : FrameB (fun r => decide (L + 4 ≤ r ∧ r < L + 14)) c₃ c₄ :=
      ⟨fun r hr => r₄ r (by sio only [decide_eq_false_iff_not] at hr)
        (by sio only [decide_eq_false_iff_not] at hr)
        (by sio only [decide_eq_false_iff_not] at hr),
       fun r _ => by rw [rr₄], m₄, rm₄, o₄⟩
    have c1 : FrameB (BcutG R ℓ Bk) c c₁ := frameB_mono f₁ (fun r hr => by simp [BcutG, hr])
    have c2 : FrameB (BcutG R ℓ Bk) c₁ c₂ := frameB_mono f₂ (fun r hr => by simp [BcutG, hr])
    have c3 : FrameB (BcutG R ℓ Bk) c₂ c₃ := frameB_mono f₃ (fun r hr => by simp [BcutG, hr])
    have c4 : FrameB (BcutG R ℓ Bk) c₃ c₄ := frameB_mono f₄ (fun r hr => by
      simp only [decide_eq_true_eq] at hr; simp [BcutG, ← hL, hr])
    exact c1.trans (c2.trans (c3.trans c4))

end

end ShotListG

end Chazelle.Core
