module

public import Chazelle.Core.DownPhaseOracleShE
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics

/-!
# WP-M (E7-B, RAM part 13): the set-up of the interior shooter

`frontI = saveS ; initI ; bitI ; originI`: the inputs of band `bShoot` saved in band `17`, the
constants, the host record `Host.whole n` at the entry allocator, the orientation bit, the
symbolic origin.  `frontI_exec`: the static environment `SEnv` holds for the query's `Stat`
(`statOf`), and the running best hit is empty.
-/


namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Visibility (rayPt)

@[expose] public section

/-- **The set-up of the interior shooter.** -/
def frontI : Stmt := .seq (saveS 140000) (.seq (.seq initI bitI) originI)

/-- The static data of a query of the interior shooter. -/
noncomputable def statOf (P : Polygon) (c : Config) (o : Origin) : Stat :=
  ⟨c.nreg ALLOC, c.nmem, c.nreg 140013, c.nreg 140009, c.nreg 140001, c.nreg 140002,
    c.nreg 140003, c.nreg 140004, c.nreg 140008, oSym (Qof P) o⟩

section exec

variable {P : Polygon} {W : ℕ} {O : OracleIface}

/-- **The set-up of the interior shooter.** -/
theorem frontI_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) (hX : (gradeCtx O).holds P c.nmem (c.nreg 140013) (c.nreg ALLOC))
    (hcap : c.nreg 140009 ≤ (gradeCtx O).cap P c.nmem (c.nreg 140013))
    (hwf : c.nreg 140000 + 6 ≤ c.nreg ALLOC)
    (hbit : c.nmem (c.nreg 140000 + 1) = 1 ↔ Mountain.LeftInside (Qof P)) {o : Origin}
    (ho : OriginIn c 140005 o) (hol : o.Lt P.n (interiorModel (Qof P)))
    (hroom : c.nreg ALLOC + 8 ≤ W) :
    ∃ c' k, Exec P W frontI c c' k ∧ k ≤ 52 ∧ SEnv P W O (statOf P c o) c' ∧
      c'.nreg 170070 = 0 ∧ c'.nreg ALLOC = c.nreg ALLOC + 8 ∧ Frame ioBands c c' k := by
  have hn3 : 3 ≤ P.n := Chazelle.Jordan.simple_three_le hG.1
  have hW := hHW
  unfold hostWords at hW
  -- save
  obtain ⟨c₁, e₁, a10, a13, ar, arr, am, arm, ao⟩ := saveS_exec (P := P) 140000 (by norm_num) c hw
  have w₁ := e₁.wb_right
  have aA : c₁.nreg ALLOC = c.nreg ALLOC := ar _ (by ufo ALLOC)
  have F₁ : Frame ioBands c c₁ 11 := frameIO_of_frameB
    (B := fun r => decide (170000 ≤ r ∧ r < 170014))
    (fun r hr => io_of_band (Or.inl (by sio at hr)))
    ⟨fun r hr => ar r (by simpa using hr), fun r _ => by rw [arr], am, arm, ao⟩ 11
  have hlow := ShootCut.grade_low hX
  have a0 : c₁.nreg 170000 = c.nreg 140000 := a10 0 (by norm_num)
  have a13' : c₁.nreg 170013 = c.nreg 140013 := a13
  -- the constants and the host record
  obtain ⟨c₂, k₂, e₂, hk₂, hk₂', b10, b11, b12, b18, b19, b16, b17, b14, b14', b15, bA, b70, bm0,
      bm1, bm2, bm3, bmlo, br, brr, brm, bo⟩ := initI_exec (P := P) c₁ w₁
    (by rw [a0]; have := hw.1 ALLOC; omega) (by rw [a13']; have := hlow.1; have := hw.1 ALLOC; omega)
    (by rwx [aA]) (by omega) (by omega)
  have w₂ := e₂.wb_right
  have F₂ : Frame ioBands c₁ c₂ k₂ := by
    refine ⟨fun r hr ha => br r ?_, fun r _ => by rw [brr], bmlo,
      fun a _ => by rw [brm], bo, by rwo [bA], by rwo [bA]⟩
    intro hb
    unfold BinitR at hb
    apply hr
    rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      (try (subst h; decide))
    exact absurd h ha
  -- the origin
  have hcopy : ∀ r, 170000 ≤ r → r < 170010 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    br r (by ufo BinitR)
  have ho₂ : OriginIn c₂ 170005 o := by
    have e5 : c₂.nreg 170005 = c.nreg 140005 := by rw [hcopy _ (by norm_num) (by norm_num)]; exact a10 5 (by norm_num)
    have e6 : c₂.nreg 170006 = c.nreg 140006 := by rw [hcopy _ (by norm_num) (by norm_num)]; exact a10 6 (by norm_num)
    have e7 : c₂.nreg 170007 = c.nreg 140007 := by rw [hcopy _ (by norm_num) (by norm_num)]; exact a10 7 (by norm_num)
    exact ShotList.originIn_copy ho e5 e6 e7
  obtain ⟨c₃, k₃, e₃, hk₃, s₃, r₃, m₃, rr₃, rm₃, o₃⟩ := originI_exec (P := P) c₂ w₂ hn3 b11 b10 b12
    b18 b19 (by rwx [b14, a0, am]) b14' ho₂ hol (by omega)
  have F₃ : Frame ioBands c₂ c₃ k₃ := frameIO_of_frameB
    (B := fun r => decide (r = 170020 ∨ r = 170021 ∨ r = 170022 ∨ r = 170092 ∨ r = 170095 ∨
      r = 170096))
    (fun r hr => io_of_band (Or.inl (by sio at hr)))
    ⟨fun r hr => r₃ r (by unfold BorgR; simpa using hr), fun r _ => by rw [rr₃], m₃, rm₃, o₃⟩ k₃
  have k3 : ∀ r, ¬ BorgR r → c₃.nreg r = c₂.nreg r := r₃
  have g : ∀ r, ¬ BorgR r → ¬ BinitR r → c₃.nreg r = c₁.nreg r := fun r h1 h2 => by
    rw [k3 r h1, br r h2]
  have gs : ∀ i, i < 10 → c₃.nreg (170000 + i) = c.nreg (140000 + i) := fun i hi => by
    rw [g _ (by ufo BorgR) (by ufo BinitR)]; exact a10 i hi
  have q : ∀ r, ¬ BorgR r → c₃.nreg r = c₂.nreg r := k3
  have ex : Exec P W frontI c c₃ (11 + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  have cA : c₃.nreg ALLOC = c.nreg ALLOC + 8 := by
    rw [q _ (by ufo BorgR ALLOC), bA, aA]
  refine ⟨c₃, _, ex, by omega, ⟨hG, hHW, gs 1 (by norm_num), gs 2 (by norm_num),
    gs 3 (by norm_num), gs 4 (by norm_num), gs 8 (by norm_num), gs 9 (by norm_num),
    by rwx [g _ (by ufo BorgR) (by ufo BinitR)],
    by rwx [q _ (by ufo BorgR)], by rwx [q _ (by ufo BorgR)],
    by rwx [q _ (by ufo BorgR)], by rwx [q _ (by ufo BorgR)],
    by rwx [q _ (by ufo BorgR)],
    by rwx [q _ (by ufo BorgR), b14, a0, am],
    by rwx [q _ (by ufo BorgR)],
    by rwr [q _ (by ufo BorgR), b15, aA],
    by rwr [q _ (by ufo BorgR), b16, a13', am],
    by rwr [q _ (by ufo BorgR), b17, a13', am], s₃,
    fun a ha => by rw [m₃, bmlo a (by rwx [aA]), am]; rfl,
    by rw [m₃]; show c₂.nmem (c.nreg ALLOC) = 1; rw [← aA]; exact bm0,
    by rw [m₃]; show c₂.nmem (c.nreg ALLOC + 1) = 0; rw [← aA]; exact bm1,
    by rw [m₃]; show c₂.nmem (c.nreg ALLOC + 2) = 0; rw [← aA]; exact bm2,
    by rw [m₃]; show c₂.nmem (c.nreg ALLOC + 3) = P.n - 1; rw [← aA]; exact bm3,
    by rw [cA]; show c.nreg ALLOC + 8 ≤ c.nreg ALLOC + 8; exact le_rfl, hX, hcap⟩,
    by rwx [q _ (by ufo BorgR)], cA,
    ((F₁.trans F₂).trans F₃).mono (by simp) (by omega)⟩

end exec

end

end IOrc

end Chazelle.Core
