module

public import Chazelle.Core.SweepIoAsm3
public import Chazelle.Core.SweepEvWinArcs
public import Chazelle.Core.MergeAsmDesc
public import Chazelle.Core.NFBuildSpec
public import Chazelle.Rwx
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

/-!
# The sweep RAM (WP-D), the assembly (piece I), part 4: `asmGoal`

**`asmGoal : AsmGoal`**: from stages 2/3 (`SweepEvSpec`), a side-0 initialisation (`InitSpec`)
and the query loop (`LoopSpec`), the sweep `SweepSpecH` with the program `asmProg`.

The run: `preS` (side saved in `sw 99`, `sw 7 := 0`), stage 0 (`initS_exec`, `St0`, hence `St0S`),
stages 2/3 (`SweepEv.Pre` from the precondition and `St0S`; `SweepEv.Post`), the initialisation
of the answers (`ansInit_exec`), which gives `AEnv` at its end (`asm_aenv` below), the side-0
initialisation (`InitSpec`, `Aux`), `sw 11 := ALLOC` (`ABase`), the loop (`LoopSpec`).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim Sweep

@[expose] public section

variable {P : Polygon} {W : ℕ}

/-- A chord list below a bound survives a change of the memory above it. -/
theorem chordList_keep {m m' : ℕ → ℕ} {A E : ℕ} {L : List (ℕ × ℕ × ℕ)} (h : ChordListAt m A L)
    (hb : A + 3 * L.length ≤ E) (he : ∀ a, a < E → m' a = m a) : ChordListAt m' A L := by
  intro i hi
  rw [he _ (by omega), he (A + 3 * i + 1) (by omega), he (A + 3 * i + 2) (by omega)]
  exact h i hi

theorem bands_sub {r : ℕ} (hr : bandOf r ∉ sweepBands ∪ oracleBands) :
    bandOf r ∉ ({bSweep, bLocate} : Finset ℕ) := by
  intro h
  apply hr
  simp [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h <;> rw [h] <;> decide

/-- **The environment of the answer phase after `ansInit`.** -/
theorem asm_aenv {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction} {H : Host}
    {N₁ N₂ : NF} {c c₃ c₄ : Config} (hXl : X.CapLocal) (hG : GoodEnv P)
    (hWh : hostWords P.n ≤ W) (hX : X.holds P c.nmem (c.nreg (sw 10)) (c.nreg ALLOC))
    (hcap : c.nreg (sw 5) ≤ X.cap P c.nmem (c.nreg (sw 10))) (hP : J.P.Simple)
    (hOk₁ : Ok P (chainModel J.left)) (hOk₂ : Ok P (chainModel J.right))
    (hNW₁ : NFWithin c.nmem (c.nreg (sw 3)) (c.nreg ALLOC) N₁)
    (hNW₂ : NFWithin c.nmem (c.nreg (sw 4)) (c.nreg ALLOC) N₂)
    (hNF₁ : IsNF (chainModel J.left) (Qof P) N₁) (hNF₂ : IsNF (chainModel J.right) (Qof P) N₂)
    (hdeg₁ : (chainModel J.left).DegLe (N₁.F (chainModel J.left) (Qof P)) (c.nreg (sw 6)))
    (hdeg₂ : (chainModel J.right).DegLe (N₂.F (chainModel J.right) (Qof P)) (c.nreg (sw 6)))
    (hsg₁ : (chainModel J.left).Semigranular (N₁.F (chainModel J.left) (Qof P)) (c.nreg (sw 5)))
    (hsg₂ : (chainModel J.right).Semigranular (N₂.F (chainModel J.right) (Qof P)) (c.nreg (sw 5)))
    (hWm : 2 * J.whole.m + 7 ≤ W)
    -- after stages 2/3
    (hst₃ : SweepEv.St0S P c₃ H J) (hout₃ : SweepEv.Out P J N₂ c₃)
    (hs₃ : rd c₃ bSweep 200 + 5 * rd c₃ bSweep 201 ≤ c₃.nreg ALLOC)
    (hl₃ : rd c₃ bSweep 300 + 7 * rd c₃ bSweep 301 ≤ c₃.nreg ALLOC)
    (ht₃ : rd c₃ bSweep 302 + 3 * (2 * N₂.nChords) ≤ c₃.nreg ALLOC)
    (hS : rd c₃ bSweep 201 ≤ 16 * (N₁.nChords + N₂.nChords + 1))
    (hLg : rd c₃ bSweep 301 ≤ 16 * (N₁.nChords + N₂.nChords + 1))
    (hr₃ : ∀ j, j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 10 → c₃.nreg (sw j) = c.nreg (sw j))
    (hm₃ : ∀ a, a < c.nreg ALLOC → c₃.nmem a = c.nmem a) (hA₃ : c.nreg ALLOC ≤ c₃.nreg ALLOC)
    -- after `ansInit`
    (hK : Consts c₄) (z30 : c₄.nreg (sw 30) = c₃.nreg ALLOC)
    (z31 : c₄.nreg (sw 31) = c₃.nreg ALLOC + 6) (z0 : c₄.nmem (c₃.nreg ALLOC) = 0)
    (zq : ∀ j, j < 5 → c₄.nmem (c₃.nreg ALLOC + 1 + j) = c₃.nmem (c₃.nreg (sw 20) + j))
    (z6 : c₄.nmem (c₃.nreg ALLOC + 6) = 0)
    (zl : ∀ j, j < 5 → c₄.nmem (c₃.nreg ALLOC + 6 + 1 + j) = c₃.nmem (c₃.nreg (sw 21) + j))
    (tb : c₄.nreg TBR = c₃.nreg ALLOC + 12) (ta : c₄.nreg ALLOC = c₄.nreg TBR + c₄.nreg TLR)
    (t64 : 64 * (N₁.nChords + N₂.nChords + 1) ≤ 2 ^ c₄.nreg TLR)
    (ttab : ∀ i, i < c₄.nreg TLR → c₄.nmem (c₄.nreg TBR + i) = 2 ^ i)
    (m₄ : ∀ a, a < c₃.nreg ALLOC → c₄.nmem a = c₃.nmem a)
    (r₄ : ∀ j, j < 700 → j ≠ 30 → j ≠ 31 → j ≠ 96 → j ≠ 97 → j ≠ 98 → j ≠ 600 → j ≠ 601 →
      (j < 610 ∨ 616 < j) → c₄.nreg (sw j) = c₃.nreg (sw j)) :
    AEnv P W X Ok J H N₁ N₂ (c.nreg ALLOC) c₄ := by
  set A₀ := c.nreg ALLOC with hA₀
  set A₃ := c₃.nreg ALLOC with hA₃d
  have hA₄ : A₃ + 12 ≤ c₄.nreg ALLOC := by omega
  have r : ∀ j, j < 30 → c₄.nreg (sw j) = c₃.nreg (sw j) := fun j hj =>
    r₄ j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (Or.inl (by omega))
  have rr : ∀ j, (j = 200 ∨ j = 201 ∨ j = 300 ∨ j = 301 ∨ j = 302) →
      c₄.nreg (sw j) = c₃.nreg (sw j) := fun j hj =>
    r₄ j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (Or.inl (by omega))
  have e3 : c₄.nreg (sw 3) = c.nreg (sw 3) := (r 3 (by omega)).trans (hr₃ 3 (by simp))
  have e4 : c₄.nreg (sw 4) = c.nreg (sw 4) := (r 4 (by omega)).trans (hr₃ 4 (by simp))
  have e5 : c₄.nreg (sw 5) = c.nreg (sw 5) := (r 5 (by omega)).trans (hr₃ 5 (by simp))
  have e6 : c₄.nreg (sw 6) = c.nreg (sw 6) := (r 6 (by omega)).trans (hr₃ 6 (by simp))
  have e10 : c₄.nreg (sw 10) = c.nreg (sw 10) := (r 10 (by omega)).trans (hr₃ 10 (by simp))
  have m : ∀ a, a < A₀ → c₄.nmem a = c.nmem a := fun a ha => (m₄ a (by omega)).trans (hm₃ a ha)
  obtain ⟨b3, -⟩ := Restore.nf_bounds hNW₁
  obtain ⟨b4, -⟩ := Restore.nf_bounds hNW₂
  have hK₁  := hNW₁.nfAt.1
  have hK₂  := hNW₂.nfAt.1
  -- the stage-0 state with the new model descriptors
  have hst₃' := hst₃
  obtain ⟨-, -, -, -, -, -, d20, w20, d21, w21, -⟩ := hst₃'
  have hn₂  := WalkEmbed.cm_n J.right
  obtain ⟨md30, mw30, -⟩ := modelDesc_of_copy (P := P) (A := A₃) (E' := c₄.nreg ALLOC) w20 d20
    le_rfl m₄ z0 zq (by omega)
  obtain ⟨md31, mw31, -⟩ := modelDesc_of_copy (P := P) (A := A₃ + 6) (E' := c₄.nreg ALLOC) w21 d21
    (by omega) m₄ z6 zl (by omega)
  have hst₄ : SweepEv.St0S P c₄ H J := by
    refine st0S_md hst₃ (fun j hj h11 h30 h31 => r₄ j (by omega) h30 h31 (by omega) (by omega)
      (by omega) (by omega) (by omega) (Or.inl (by omega))) m₄ (by omega) ?_ ?_ ?_ ?_
    · rw [z30]; exact md30
    · rw [z30]; exact mw30
    · rw [z31]; exact md31
    · rw [z31]; exact mw31
  have h20 := w20.1
  have h21 := w21.1
  have hnar₁ := SweepEv.arcsTask J.left (Qof P) N₁ hP hNF₁
  have hnar₂ := SweepEv.arcsTask J.right (Qof P) N₂ hP hNF₂
  refine
    { hG := hG
      hWh := hWh
      hX := ?_
      hcap := ?_
      hP := hP
      hOk₁ := hOk₁
      hOk₂ := hOk₂
      hN₁ := by rw [e3]; exact Robust.transport hNW₁ m
      hN₂ := by rw [e4]; exact Robust.transport hNW₂ m
      hNF₁ := hNF₁
      hNF₂ := hNF₂
      hdeg₁ := by rwx [e6]
      hdeg₂ := by rwx [e6]
      hsg₁ := by rwx [e5]
      hsg₂ := by rwx [e5]
      hst := hst₄
      hE := by omega
      hWm := hWm
      hK := hK
      htab := ttab
      hbig₁ := by omega
      hbig₂ := by omega
      hbigE := ?_
      hTB := by omega
      hTW := by omega
      hout := out_transport hout₃ rr m₄ hs₃ hl₃ ht₃
      hstops := ?_
      hlog := ?_
      htabw := ?_
      hK₁ := by rwx [e3, m _ (by omega)]
      hK₂ := by rwx [e4, m _ (by omega)]
      hmd₁ := fun j hj => by
        rw [z30, zq j hj, r 20 (by omega), m₄ _ (by omega)]
      hmd₂ := fun j hj => by
        rw [z31, zl j hj, r 21 (by omega), m₄ _ (by omega)] }
  · rw [e10]
    exact X.mono _ _ _ _ _ (by omega) (X.local_ _ _ _ _ _ (fun a ha => (m a ha).symm) hX)
  · rwx [e5, e10, hXl _ _ _ _ _ m hX]
  · show rd c₄ bSweep 201 + rd c₄ bSweep 301 + 2 * N₂.nChords < 2 ^ c₄.nreg TLR
    rw [show rd c₄ bSweep 201 = rd c₃ bSweep 201 from rr 201 (by simp),
      show rd c₄ bSweep 301 = rd c₃ bSweep 301 from rr 301 (by simp)]
    omega
  · show rd c₄ bSweep 200 + 5 * rd c₄ bSweep 201 ≤ c₄.nreg ALLOC
    rw [show rd c₄ bSweep 200 = rd c₃ bSweep 200 from rr 200 (by simp),
      show rd c₄ bSweep 201 = rd c₃ bSweep 201 from rr 201 (by simp)]
    omega
  · show rd c₄ bSweep 300 + 7 * rd c₄ bSweep 301 ≤ c₄.nreg ALLOC
    rw [show rd c₄ bSweep 300 = rd c₃ bSweep 300 from rr 300 (by simp),
      show rd c₄ bSweep 301 = rd c₃ bSweep 301 from rr 301 (by simp)]
    omega
  · show rd c₄ bSweep 302 + 3 * (2 * N₂.nChords) ≤ c₄.nreg ALLOC
    rw [show rd c₄ bSweep 302 = rd c₃ bSweep 302 from rr 302 (by simp)]
    omega

end

end SweepIo

end Chazelle.Core
