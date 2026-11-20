module

meta import Chazelle.Programs.RamEval

public import Chazelle.Core.ShotListG

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

section

variable {R : ℕ} (hR : RegsOK R) {B : ℕ → Bool} (h : WrG R B)
include hR h

theorem WrG.alloc : B ALLOC = false := by
  cases hb : B ALLOC
  · rfl
  · have := h _ hb
    unfold RegsOK at hR; unfold ALLOC at this
    rcases this with h1 | h1 | h1
    · omega
    · omega
    · exact absurd rfl h1.2

theorem WrG.keep {i : ℕ}
    (hi : i < 9 ∨ (30 ≤ i ∧ i < 36)) : B (R + i) = false := by
  cases hb : B (R + i)
  · rfl
  · have := h _ hb
    rcases this with h1 | h1 | h1
    · omega
    · omega
    · exact absurd h1.1 (band_R hR (by omega))

theorem WrG.frameR {Bo : Finset ℕ}
    (hBo : oracleBands ⊆ Bo) {c c' : Config} (hf : FrameB B c c') (k : ℕ) :
    FrameR Bo (fun r => R + 9 ≤ r ∧ r < R + 300) c c' k :=
  FrameR.of_frameB hf (fun r hr => by
    rcases h r hr with h1 | h1 | h1
    · exact Or.inl ⟨h1.1, by omega⟩
    · exact Or.inl ⟨by omega, h1.2⟩
    · exact Or.inr (hBo h1.1)) (h.alloc hR) k

end

/-- **The operations' context survives** a register frame of the wrapper's blocks. -/
theorem KCtx.of_frameB {P : Polygon} {W : ℕ} {M : Model} {R : ℕ} (hR : RegsOK R)
    {E : Config → Prop} {Bo : Finset ℕ} (hBo : oracleBands ⊆ Bo) (hS : Stable Bo W R E) {c c' : Config} {B : ℕ → Bool}
    (h : KCtx P W M R E c) (hw' : WordsBounded W c') (hf : FrameB B c c') (hB : WrG R B) :
    KCtx P W M R E c' := by
  obtain ⟨hE, hG, hHW, hMD, hmwf, h30, h31, h34⟩ := h
  have k : ∀ i, (i < 9 ∨ (30 ≤ i ∧ i < 36)) → c'.nreg (R + i) = c.nreg (R + i) := fun i hi =>
    hf.1 _ (hB.keep hR hi)
  have r0 : c'.nreg R = c.nreg R := by simpa using k 0 (by omega)
  have hA := hf.1 _ (hB.alloc hR)
  have hm := hf.2.2.1
  exact ⟨hS c c' 0 hE hw' (hB.frameR hR hBo hf 0), hG, hHW, by rwa [hm, r0],
    by rwa [hm, r0, hA], by rw [k 30 (by omega), h30], by rw [k 31 (by omega), h31],
    by simp_all⟩

/-! ## The correction of `a < b` -/

/-- The correction of the bit `a < b` (`R + 100`) by the key comparison `kc`, when `a`, `b` are
interior positions of one edge. -/
def offBG (kc : ℕ → ℕ → ℕ → ℕ → Stmt) (R ℓ : ℕ) : Stmt :=
  offWith R ℓ (.seq (kc (rL R ℓ) (rL R ℓ + 1) (rL R ℓ + 2) (rL R ℓ + 3))
    (.instr (.copyN (R + 100) 50210)))

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
  refine offWith_exec (K := K + 2) c hw _ hctx.2.2.2.2.2.1 ha hb hbit ?_
  set L := rL R ℓ with hL
  intro _ h₃ h₄
  -- two interior positions of one edge: the key comparison
  have iL : ∀ i, i < 4 → InB R (L + i) := fun i hi => by rw [hL]; unfold InB rL; omega
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, f₁⟩ := hk L (L + 1) (L + 2) (L + 3) (iL 0 (by omega))
    (iL 1 (by omega)) (iL 2 (by omega)) (iL 3 (by omega)) c hw hctx ha.1 hae
    (by omega) hb.1 hbe (by omega) hroom
  have e₂ := Exec.copyN (P := P) e₁.wb_right (R + 100) 50210
  refine ⟨_, _, .seq e₁ e₂, by omega, ⟨?_, ?_⟩, ?_⟩
  · simp only [upd_same]; exact b₁.1
  · simp only [upd_same]; exact b₁.2
  · have g1 : FrameB (BoffG R Bk) c c₁ := (by ram_frame)
    have g2 : FrameB (BoffG R Bk) c₁ _ := frameB_mono (exec_frameB e₂
      (show wr (Bone (R + 100)) (.instr (.copyN (R + 100) 50210)) = true by
        simp [write_check, Bone])) (fun r hr => by
          simp only [Bone, beq_iff_eq] at hr; subst hr; simp [BoffG])
    exact g1.trans g2

/-! ## The cutting block -/

/-- **The cutting block of level `ℓ`** with the key comparison `kc`. -/
def cutBG (kc : ℕ → ℕ → ℕ → ℕ → Stmt) (R ℓ : ℕ) : Stmt :=
  cutWith R ℓ (offBG kc R ℓ)

/-- The registers written by `cutBG`. -/
def BcutG (R ℓ : ℕ) (Bk : ℕ → Bool) (r : ℕ) : Bool :=
  Bouts (cmpList R ℓ) r || BoffG R Bk r || Bform R r || decide (rL R ℓ + 4 ≤ r ∧ r < rL R ℓ + 14)

/-- The cutting block writes scratch registers and registers of the key comparison. -/
theorem wrG_cut {R ℓ : ℕ} (hℓ : ℓ ≤ 2) {Bk : ℕ → Bool} (hBk : OpW Bk) : WrG R (BcutG R ℓ Bk) :=
  fun r hr => by
    simp only [BcutG, BoffG, Bool.or_eq_true, beq_iff_eq] at hr
    rcases hr with ((h | h | h) | h) | h
    · have := bouts_range h; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · simp_all 
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
  have hz := hctx.2.2.2.2.2.1
  obtain ⟨d, k, ex, hk', hp, f⟩ := cutWith_exec (P := P) hℓ c hw hW hz ha hb hae hbe
    (s := offBG kc R ℓ) (B := BoffG R Bk) (K := K + 10)
    (fun r h1 h2 hn => by simp [BoffG, opW_R hBk hR h1 h2, hn]) (by
      intro d hd hf keep ha' hb' he₁ he₂ bit
      have ctx := KCtx.of_frameB hR hBo hS hctx hd hf (fun r hr => by
        have := bouts_range hr; exact Or.inr (Or.inl ⟨by omega, by omega⟩))
      exact offBG_exec hk hℓ d hd ctx
        (by rwa [keep _ (by unfold ALLOC; unfold RegsOK at hR; omega)]) ha' hb' he₁ he₂ bit)
  exact ⟨d, k, ex, by omega, hp, f⟩

end

end ShotListG

end Chazelle.Core
