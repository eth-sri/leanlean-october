module

public import Chazelle.Core.DownPhaseOracleShE

/-!
# WP-M (E7-B, RAM part 13): the set-up of the interior shooter

`frontI = saveS ; initI ; bitI ; originI`: the inputs of band `bShoot` saved in band `17`, the
constants, the host record `Host.whole n` at the entry allocator, the orientation bit, the
symbolic origin.  `frontI_exec`: the static environment `SEnv` holds for the query's `Stat`
(`statOf`), and the running best hit is empty.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Visibility (rayPt)

@[expose] public section

/-- Execute the common prefix of the interior oracles: save the query words, allocate
and initialize the host record, and set the orientation bit. -/
theorem front_init_exec {P : Polygon} {W : ℕ} {O : OracleIface} (b : ℕ)
    (hb : b + 13 < 170000) (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) (hX : (gradeCtx O).holds P c.nmem (c.nreg (b + 13)) (c.nreg ALLOC))
    (hcap : c.nreg (b + 9) ≤ (gradeCtx O).cap P c.nmem (c.nreg (b + 13)))
    (hwf : c.nreg b + 6 ≤ c.nreg ALLOC)
    (hbit : c.nmem (c.nreg b + 1) = 1 ↔ Mountain.LeftInside (Qof P))
    (hroom : c.nreg ALLOC + 8 ≤ W) (o : SymPt) :
    ∃ c₁ d k, Exec P W (saveS b) c c₁ 11 ∧ Exec P W (.seq initI bitI) c₁ d k ∧ k ≤ 27 ∧
      SEnvBase P W O ⟨c.nreg ALLOC, c.nmem, c.nreg (b + 13), c.nreg (b + 9), c.nreg (b + 1),
        c.nreg (b + 2), c.nreg (b + 3), c.nreg (b + 4), c.nreg (b + 8), o⟩ d ∧
      (∀ i, i < 10 → d.nreg (170000 + i) = c.nreg (b + i)) ∧
      d.nreg ALLOC = c.nreg ALLOC + 8 ∧ d.nreg 170070 = 0 ∧ Frame ioBands c d (11 + k) := by
  have hn3 := Chazelle.Jordan.simple_three_le hG.1
  have hW := hHW
  unfold hostWords at hW
  obtain ⟨c₁, e₁, a10, a13, ar, arr, am, arm, ao⟩ := saveS_exec (P := P) b hb c hw
  have aA : c₁.nreg ALLOC = c.nreg ALLOC := ar _ (by unfold ALLOC; omega)
  have F₁ : Frame ioBands c c₁ 11 := frameIO_of_frameB
    (B := fun r => decide (170000 ≤ r ∧ r < 170014))
    (fun r hr => io_of_band (Or.inl (by simp at hr; omega)))
    ⟨fun r hr => ar r (by simpa using hr), fun r _ => congrFun arr r,
      am, arm, ao⟩ 11
  have hlow := ShootCut.grade_low hX
  have a0 : c₁.nreg 170000 = c.nreg b := a10 0 (by decide)
  obtain ⟨d, k, e₂, hk0, hk, b10, b11, b12, b18, b19, b16, b17, b14, b14', b15, bA, b70, bm0,
      bm1, bm2, bm3, bmlo, br, brr, brm, bo⟩ := initI_exec (P := P) c₁ e₁.wb_right
    (by rw [a0]; have := hw.1 ALLOC; omega) (by rw [a13]; have := hlow.1; have := hw.1 ALLOC; omega)
    (by rwa [aA]) (by omega) (by omega)
  have F₂ : Frame ioBands c₁ d k := by
    refine ⟨fun r hr ha => br r ?_, fun r _ => congrFun brr r, bmlo,
      fun a _ => congrFun brm a, bo, by omega, by omega⟩
    intro h
    unfold BinitR at h
    rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst r <;>
      first | exact ha rfl | exact hr (by decide)
  have gs : ∀ i, i < 10 → d.nreg (170000 + i) = c.nreg (b + i) := fun i hi =>
    (br _ (by unfold BinitR; omega)).trans (a10 i hi)
  have g13 := (br 170013 (by unfold BinitR; decide)).trans a13
  rw [aA] at bA b15 bm0 bm1 bm2 bm3 bmlo
  rw [a13, am] at b16 b17
  rw [a0, am, hbit] at b14
  exact ⟨c₁, d, k, e₁, e₂, hk, ⟨hG, hHW, gs 1 (by decide), gs 2 (by decide), gs 3 (by decide),
    gs 4 (by decide), gs 8 (by decide), gs 9 (by decide), g13, b10, b11, b12, b18, b19, b14, b14',
    b15, b16, b17, fun a ha => (bmlo a ha).trans (congrFun am a), bm0, bm1, bm2, bm3,
    bA.ge, hX, hcap⟩, gs, bA, b70, by simpa only [Finset.union_self] using F₁.trans F₂⟩

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
    (ho : OriginIn c 140005 o) (hol : o.Lt P.n (inputModel P))
    (hroom : c.nreg ALLOC + 8 ≤ W) :
    ∃ c' k, Exec P W frontI c c' k ∧ k ≤ 52 ∧ SEnv P W O (statOf P c o) c' ∧
      c'.nreg 170070 = 0 ∧ c'.nreg ALLOC = c.nreg ALLOC + 8 ∧ Frame ioBands c c' k := by
  obtain ⟨c₁, c₂, k₂, e₁, e₂, hk₂, hE, saved, bA, b70, F₂⟩ := front_init_exec
    (P := P) 140000 (by decide) c hw hG hHW hX hcap hwf hbit hroom (oSym (Qof P) o)
  have ho₂ : OriginIn c₂ 170005 o :=
    ShotList.originIn_copy ho (saved 5 (by decide)) (saved 6 (by decide)) (saved 7 (by decide))
  have hn := Chazelle.Jordan.simple_three_le hG.1
  have hW : P.n + 3 ≤ W := by reg_omega
  obtain ⟨c₃, k₃, e₃, hk₃, s₃, r₃, m₃, rr₃, rm₃, o₃⟩ := originI_exec c₂ e₂.wb_right hn
    hE.r11 hE.r10 hE.r12 hE.r18 hE.r19 hE.lb hE.lb1 ho₂ hol hW
  have F₃ : Frame ioBands c₂ c₃ k₃ := frameIO_of_frameB
    (B := fun r => decide (r = 170020 ∨ r = 170021 ∨ r = 170022 ∨ r = 170092 ∨ r = 170095 ∨
      r = 170096))
    (fun r hr => io_of_band (Or.inl (by simp at hr; omega)))
    ⟨fun r hr => r₃ r (by unfold BorgR; simpa using hr), fun r _ => congrFun rr₃ r, m₃, rm₃, o₃⟩ k₃
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega,
    ⟨hE.keep (fun r h1 h2 => r₃ r (by unfold BorgR; omega)) (fun a _ => congrFun m₃ a) F₃.2.2.2.2.2.1,
      s₃⟩, (r₃ _ (by unfold BorgR; decide)).trans b70,
    (r₃ _ (by unfold BorgR; decide)).trans bA, ?_⟩
  simpa only [Finset.union_self, Nat.add_assoc] using F₂.trans F₃

end exec

end

end IOrc

end Chazelle.Core
