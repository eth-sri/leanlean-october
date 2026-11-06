module

public import Chazelle.Core.DownPhaseOracleShG

/-!
# WP-M (E7-B): the interior shooter

`shI sh`: on a chain descriptor (kind `0`) the chain shooter `sh` itself; on the descriptor of the
interior model (kind `1`) the set-up `frontI` and the query `queryI sh` (one or two sub-queries
through chains of `Q`, each one or two calls of `sh`).

**`interiorShooter_of`**: from a shooter for the chain models (`OkModel`, bands `oracleBands`,
cost `F`), `shI sh` is a shooter for `OkI` (chain models and the interior model of `Qof P`), with
bands `ioBands = insert bUp oracleBands` and cost `FI F γ = 4 F γ + 3000 (⌈log₂ γ⌉ + 1) + 20000`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Visibility (rayPt)

@[expose] public section

/-- **The models served by the interior oracles**: the chain models of `OkModel` and the interior
model of `Q`. -/
def OkI (P : Polygon) (M : Model) : Prop := OkModel P M ∨ M = interiorModel (Qof P)

/-- **The interior shooter.** -/
def shI (sh : Stmt) : Stmt :=
  .seq (block [.loadN 170099 140000, .constN 170098 1])
    (.ifLtN 170099 170098 sh (.seq frontI (queryI sh)))

/-- The cost of the interior shooter. -/
def FI (F : ℕ → ℕ) (γ : ℕ) : ℕ := 4 * F γ + 3000 * (Nat.clog 2 γ + 1) + 20000

theorem chainModel_ne_interior'' (C : Chain) (Q : Polygon) : chainModel C ≠ interiorModel Q := by
  intro h
  have := congrArg (fun M : Model => M.counted 0) h
  simp [chainModel, interiorModel] at this

/-- An `OkI` model with a chain descriptor is an `OkModel`. -/
theorem okModel_of_okI {P : Polygon} {m : ℕ → ℕ} {B : ℕ} {M : Model}
    (hMD : ModelDescAt m B (Qof P) M) (h0 : m B = 0) (hOk : OkI P M) : OkModel P M := by
  rcases hOk with h | h
  · exact h
  · rcases hMD with ⟨-, H, C, -, hM⟩ | ⟨h1, -, -⟩
    · exact absurd (hM.symm.trans h) (chainModel_ne_interior'' C _)
    · rw [h0] at h1; exact absurd h1 (by norm_num)

theorem room_q {A F' cl W : ℕ} (h : A + (4 * F' + 3000 * (cl + 1) + 20000) ≤ W) :
    A + 8 + (4 * F' + 3000 * (cl + 1) + 19000) ≤ W := by linarith

theorem cost_q {k₁ k₂ k₃ F' cl : ℕ} (h1 : k₁ = 2) (h2 : k₂ ≤ 52)
    (h3 : k₃ ≤ 4 * F' + 3000 * (cl + 1) + 19000) :
    k₁ + (k₂ + k₃ + 2) ≤ 4 * F' + 3000 * (cl + 1) + 20000 := by linarith

section exec

variable {P : Polygon} {W : ℕ} {O : OracleIface}

theorem load_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W (block [.loadN 170099 140000, .constN 170098 1]) c c' k ∧ k = 2 ∧
      c'.nreg 170099 = c.nmem (c.nreg 140000) ∧ c'.nreg 170098 = 1 ∧
      FrameB (fun r => decide (r = 170098 ∨ r = 170099)) c c' := by
  have hwr : wr (fun r => decide (r = 170098 ∨ r = 170099))
      (block [.loadN 170099 140000, .constN 170098 1]) = true := by decide
  suffices h : ∃ c' k, Exec P W (block [.loadN 170099 140000, .constN 170098 1]) c c' k ∧ k = 2 ∧
      c'.nreg 170099 = c.nmem (c.nreg 140000) ∧ c'.nreg 170098 = 1 by
    obtain ⟨c', k, e, h1, h2, h3⟩ := h
    exact ⟨c', k, e, h1, h2, h3, exec_frameB e hwr⟩
  exec_block
  · omega
  exact ⟨rfl, by config_simp, by config_simp⟩

theorem load_io {r : ℕ} (h : decide (r = 170098 ∨ r = 170099) = true) :
    bandOf r ∈ ioBands ∧ r ≠ ALLOC :=
  io_of_band (Or.inl (by simp at h; omega))

/-- **The interior shooter.** -/
theorem interiorShooter_of {sh : Stmt} {F : ℕ → ℕ}
    (hsh : ShooterOK sh oracleBands F (gradeCtx O) OkModel) :
    ShooterOK (shI sh) ioBands (FI F) (gradeCtx O) OkI := by
  intro P W c hw hpre hcost
  obtain ⟨hG, hHW, hX, hcap, hMDWF, hreg, M, hMD, hOk, hsP, heP, hs1, he1, hin1, hin2, hwt, o,
    hol, ho, hof, hoA⟩ := hpre
  have hW := hHW
  unfold hostWords at hW
  beta_reduce at hcost
  have hQ : (Qof P).n = P.n := qn'
  obtain ⟨c₁, k₁, e₁, hk₁, a99, a98, F₁⟩ := load_exec (P := P) c hw (by omega)
  have w₁ := e₁.wb_right
  have f₁ : ∀ r, r ≠ 170098 → r ≠ 170099 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    F₁.1 r (by simp [h1, h2])
  have Fr₁ : Frame ioBands c c₁ k₁ := frameIO_of_frameB (fun r h => load_io h) F₁ k₁
  have rk : ∀ i, i < 20 → rd c₁ bShoot i = rd c bShoot i := fun i hi =>
    f₁ _ (by unfold bandReg bShoot; omega) (by unfold bandReg bShoot; omega)
  have hm₁ : c₁.nmem = c.nmem := F₁.2.2.1
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := f₁ _ (by decide) (by decide)
  have r0 := rk 0 (by norm_num)
  have r1 := rk 1 (by norm_num)
  have r2 := rk 2 (by norm_num)
  have r3 := rk 3 (by norm_num)
  have r4 := rk 4 (by norm_num)
  have r8 := rk 8 (by norm_num)
  have r9 := rk 9 (by norm_num)
  have r13 := rk 13 (by norm_num)
  have ho₁ : OriginIn c₁ (bandReg bShoot 5) o := ShotList.originIn_copy ho
    (f₁ _ (by decide) (by decide)) (f₁ _ (by decide) (by decide)) (f₁ _ (by decide) (by decide))
  by_cases hk : c.nmem (c.nreg 140000) = 0
  · -- a chain descriptor: the chain shooter itself
    have hlt : c₁.nreg 170099 < c₁.nreg 170098 := by rw [a99, a98, hk]; omega
    have hOk' := okModel_of_okI hMD hk hOk
    obtain ⟨c₂, k₂, e₂, hk₂, hpost, F₂⟩ := hsh P W c₁ w₁ (by
      beta_reduce
      simp only [r0, r1, r2, r3, r4, r9, r13, hm₁, hA₁]
      exact ⟨hG, hHW, hX, hcap, hMDWF, hreg, M, hMD, hOk', hsP, heP, hs1, he1, hin1, hin2, hwt, o,
        hol, ho₁, hof, hoA⟩) (by
      beta_reduce
      rw [r9, hA₁]
      have : F (rd c bShoot 9) ≤ FI F (rd c bShoot 9) := by unfold FI; omega
      omega)
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true hlt e₂), ?_, fun M' o' hM' ho' => ?_,
      (Fr₁.trans (F₂.mono oracleBands_sub_io le_rfl)).mono (by simp) (by omega)⟩
    · beta_reduce at hk₂ ⊢
      rw [r9] at hk₂
      have : F (rd c bShoot 9) + 3 ≤ FI F (rd c bShoot 9) := by unfold FI; omega
      omega
    · have hp := hpost M' o' (by rw [r0, hm₁]; exact hM') (ShotList.originIn_copy ho'
        (f₁ _ (by decide) (by decide)) (f₁ _ (by decide) (by decide))
        (f₁ _ (by decide) (by decide)))
      simp only [r1, r2, r3, r4, r8] at hp
      exact hp
  · -- the interior model
    have hge : ¬ c₁.nreg 170099 < c₁.nreg 170098 := by rw [a99, a98]; omega
    obtain ⟨hk1, hbit, hMI⟩ : c.nmem (rd c bShoot 0) = 1 ∧
        (c.nmem (rd c bShoot 0 + 1) = 1 ↔ Mountain.LeftInside (Qof P)) ∧
        M = interiorModel (Qof P) := by
      rcases hMD with ⟨h0, -⟩ | h
      · exact absurd h0 hk
      · exact h
    subst hMI
    have hD : DistinctHeights (Qof P) := (goodShear_epsOf hG.2).2.1
    have hn3 : 3 ≤ (Qof P).n := by rw [hQ]; exact Chazelle.Jordan.simple_three_le hG.1
    have hmn : (interiorModel (Qof P)).W.n = (Qof P).n := mi_n
    have hol' : o.Lt (Qof P).n (interiorModel (Qof P)) := by rw [hQ]; exact hol
    obtain ⟨hoL, hoE, hb1, hb2⟩ := oSym_spec hD hn3 hol' (by rw [hQ]; exact hof)
    -- the set-up
    obtain ⟨c₂, k₂, e₂, hk₂, S₂, h70, hA₂, F₂⟩ := frontI_exec (O := O) c₁ w₁ hG hHW
      (by show (gradeCtx O).holds P c₁.nmem (rd c₁ bShoot 13) (c₁.nreg ALLOC)
          rw [hm₁, hA₁, r13]; exact hX)
      (by show rd c₁ bShoot 9 ≤ (gradeCtx O).cap P c₁.nmem (rd c₁ bShoot 13)
          rw [hm₁, r9, r13]; exact hcap)
      (by show rd c₁ bShoot 0 + 6 ≤ c₁.nreg ALLOC
          rw [hA₁, r0]; exact hMDWF.1)
      (by show c₁.nmem (rd c₁ bShoot 0 + 1) = 1 ↔ _
          rw [hm₁, r0]; exact hbit) ho₁ hol (by
        rw [hA₁]; have : 8 ≤ FI F (rd c bShoot 9) := by unfold FI; omega
        omega)
    have w₂ := e₂.wb_right
    have se1 : (statOf P c₁ o).e₁ = rd c bShoot 1 := r1
    have sh1 : (statOf P c₁ o).h₁ = rd c bShoot 2 := r2
    have se2 : (statOf P c₁ o).e₂ = rd c bShoot 3 := r3
    have sh2 : (statOf P c₁ o).h₂ = rd c bShoot 4 := r4
    have sγ : (statOf P c₁ o).γ = rd c bShoot 9 := r9
    have sdir : (statOf P c₁ o).dir = rd c bShoot 8 := r8
    have so : (statOf P c₁ o).o = oSym (Qof P) o := rfl
    have q : QFacts (Qof P) (statOf P c₁ o).e₁ (statOf P c₁ o).h₁ (statOf P c₁ o).e₂
        (statOf P c₁ o).h₂ := by
      rw [se1, sh1, se2, sh2]
      exact ⟨hn3, hD, by rw [← hmn]; exact hs1, by rw [← hmn]; exact he1,
        by rw [hQ]; exact hsP, by rw [hQ]; exact heP⟩
    obtain ⟨c₃, k₃, e₃, hk₃, hhit, hno, F₃⟩ := queryI_exec hsh c₂ w₂ S₂ h70 q
      (by rw [se1, sh1, se2, sh2, sγ]; exact hwt) (by rw [so, hoE]; exact hb1)
      (by rw [so, hoE]; exact hb2) (by rw [so, ← hQ]; exact hoL)
      (by rw [so, hoE, se1, sh1, se2, sh2]; exact hoA) (by
        rw [hA₂, hA₁, sγ]
        unfold FI at hcost
        exact room_q hcost)
    refine ⟨c₃, _, .seq e₁ (.ifLtN_false hge (.seq e₂ e₃)), ?_, fun M' o' hM' ho' => ?_,
      ((Fr₁.trans F₂).trans F₃).mono (by simp) (by omega)⟩
    · beta_reduce
      rw [sγ] at hk₃
      unfold FI
      exact cost_q hk₁ hk₂ hk₃
    · have hM'I : M' = interiorModel (Qof P) := by
        rcases hM' with ⟨h0, -⟩ | ⟨-, -, h⟩
        · rw [hk1] at h0; exact absurd h0 (by norm_num)
        · exact h
      subst hM'I
      have hoo : o' = o := ShotList.originIn_unique ho' ho
      subst hoo
      rw [so, hoE, se1, sh1, se2, sh2, sdir] at hhit hno
      exact ⟨hhit, hno⟩

end exec

end

end IOrc

end Chazelle.Core
