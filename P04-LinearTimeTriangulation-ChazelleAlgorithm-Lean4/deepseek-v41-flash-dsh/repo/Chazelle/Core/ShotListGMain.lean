module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.ShotListGLev

/-!
# The model-generic shot list, part 5: the wrapper and its contract

`shotListG kc xc sh R` is the sweep's wrapper `ShotList.shotList sh R` with the generic cutting
block and leaf: the same registers, the same initialisation (`shInit`: `R + 34` holds the address
after the model descriptor), the same loop over the arcs.  `shotListG_exec`: for any model `M`
with a key comparison `kc` (`KeyG`) and an abscissa comparison `xc` (`XG`) under a stable
environment `E`, the wrapper establishes the sweep's postcondition `ShotPost` from `ShotPreG`
(the sweep's `ShotPre` with the chain requirements replaced by `ModelDescAt … M`, `E`, and the
admissible height `Y` of the origin), within `shotCostG` steps and the frame of the caller's band
and the oracle bands.
-/

namespace Chazelle.Core

namespace ShotListG

open Machine Machine.Stmt Programs SignK SweepPrim ShotList
open Chazelle.Chain (sideInArc)
open Chazelle.Visibility (rayPt)

@[expose] public section

/-- **The wrapper**: shoot at every arc, cut by the holes, and keep the first hit. -/
def shotListG (kc xc : ℕ → ℕ → ℕ → ℕ → Stmt) (sh : Stmt) (R : ℕ) : Stmt :=
  .seq (shInit R) (.whileLtN (R + 28) (R + 2)
    (.seq (loadArc R) (.seq (levFG kc xc sh R 3 0) (stepArc R))))

/-- **The precondition of the wrapper** for the model `M`, the environment `E` and the
admissible heights `Y`. -/
def ShotPreG (X : MemCtx) (Ok : Polygon → Model → Prop) (R : ℕ) (P : Polygon) (W : ℕ)
    (M : Model) (E : Config → Prop) (Y : ℝ → Prop) (c : Config) : Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧
    X.holds P c.nmem (c.nreg (R + 8)) (c.nreg ALLOC) ∧
    c.nreg (R + 7) ≤ X.cap P c.nmem (c.nreg (R + 8)) ∧
    ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg R) ∧ ModelDescAt c.nmem (c.nreg R) (Qof P) M ∧
    HReg P c.nmem (c.nreg R) ∧ E c ∧ Ok P M ∧
    c.nreg (R + 1) + 4 * c.nreg (R + 2) ≤ c.nreg ALLOC ∧ c.nreg (R + 9) ≤ 3 ∧
    (∀ j < c.nreg (R + 2), PieceOK M (Qof P) P.n (arcAt c.nmem (c.nreg (R + 1)) j) ∧
      M.arcWt (M.key (Qof P) (arcAt c.nmem (c.nreg (R + 1)) j).1)
        (M.key (Qof P) (arcAt c.nmem (c.nreg (R + 1)) j).2) ≤ c.nreg (R + 7)) ∧
    (∀ j < c.nreg (R + 9), c.nreg (R + 10 + 2 * j) < M.W.n ∧ c.nreg (R + 11 + 2 * j) < M.W.n ∧
      c.nreg (R + 10 + 2 * j) ≠ c.nreg (R + 11 + 2 * j)) ∧
    ∃ o : Origin, OriginIn c (R + 3) o ∧ o.Lt P.n M ∧
      ((∃ q, o = .walk ⟨q, 0⟩) ∨ (M.InnerPt (o.eval M (Qof P)) ∧
        ∀ x, o = .walk x → ProperPos M (Qof P) P.n x)) ∧
      Y (o.eval M (Qof P)).2 ∧
      Avoid M (Qof P) c.nmem (c.nreg (R + 1)) (c.nreg (R + 2)) (holeList c R) (o.eval M (Qof P))

/-- The cost of the wrapper: `A + 1` rounds of `16` nodes. -/
def shotCostG (Fg K A : ℕ) : ℕ := (A + 1) * (16 * nodeG Fg K)

/-- **The contract of the model-generic wrapper**, with the register frame: besides the oracle
bands, only the block `R … R + 299` changes. -/
theorem shotListG_execR {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {Bo : Finset ℕ} (hsh' : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ Bo)
    (hXl : X.CapLocal) {R : ℕ} (hR : RegsOK R) {P : Polygon} {W : ℕ} {M : Model}
    (hRB : bandOf R ∉ Bo) (hBo : oracleBands ⊆ Bo) {E : Config → Prop} (hS : Stable Bo W R E) {Y : ℝ → Prop} {kc xc : ℕ → ℕ → ℕ → ℕ → Stmt}
    {Bk Bx : ℕ → Bool} {K : ℕ} (hk : KeyG P W M R E kc Bk K) (hBk : OpW Bk)
    (hx : XG P W M R E Y xc Bx K) (hBx : OpW Bx) (c : Config) (hw : WordsBounded W c)
    (pre : ShotPreG X Ok R P W M E Y c)
    (hroom : c.nreg ALLOC + shotCostG (F (c.nreg (R + 7))) K (c.nreg (R + 2)) ≤ W) :
    ∃ c' k, Exec P W (shotListG kc xc sh R) c c' k ∧
      k ≤ shotCostG (F (c.nreg (R + 7))) K (c.nreg (R + 2)) ∧ ShotPost R P c c' ∧
      FrameR Bo (fun r => R ≤ r ∧ r < R + 300) c c' k := by
  have hsh := shooterOKE_of hsh'
  obtain ⟨hG, hHW, hX, hcap, hmwf, hMD, hreg, hE, hOk, hAB, hH3, harcs, hholes, o, ho,
    hol, hof, hoy, havoid⟩ := pre
  have hR' := hR; unfold RegsOK at hR'
  set Q := Qof P
  set D := c.nreg R
  set AB := c.nreg (R + 1)
  set A := c.nreg (R + 2)
  set Fg := F (c.nreg (R + 7))
  set G := nodeG Fg K with hG'
  set hl := holeList c R with hhl
  set z := o.eval M Q
  set σ := dirOf (c.nreg (R + 6))
  set Bi := levCostG G 3 + 20 with hBi
  have hlc : levCostG G 3 = 15 * G := by simp [levCostG]
  have hG1 : 1000 ≤ G := by rw [hG']; unfold nodeG; omega
  have hW8 : 8 ≤ W := by unfold hostWords at hHW; omega
  have hD6 := hmwf.1
  have hroom' : c.nreg ALLOC + (A + 1) * (16 * G) ≤ W := hroom
  have hA0 : c.nreg ALLOC + 16 * G ≤ W := by
    have : 16 * G ≤ (A + 1) * (16 * G) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- initialisation
  obtain ⟨c₁, k₁, e₁, hk₁, i30, i31, i32, i33, i34, i20, i28, i36, i37, i35, f₁⟩ :=
    shInit_exec (P := P) (R := R) c hw (by omega) (by omega)
  have k1 : ∀ r, (r < R + 20 ∨ R + 40 ≤ r) → c₁.nreg r = c.nreg r := fun r hr =>
    f₁.1 r (by simp only [Bmid, decide_eq_false_iff_not]; omega)
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := k1 _ (by unfold ALLOC; omega)
  have hM1 : c₁.nmem = c.nmem := f₁.2.2.1
  have F01 : FrameR Bo (fun r => R + 9 ≤ r ∧ r < R + 300) c c₁ k₁ :=
    FrameR.of_frameB f₁ (fun r hr => by
      simp only [Bmid, decide_eq_true_eq] at hr; left; omega)
      (by simp only [Bmid, decide_eq_false_iff_not]; unfold ALLOC; omega) k₁
  -- the holes of the recursion
  have holes_ok : HolesOK (M.key Q) hl := by
    refine holesOK_of M Q (fun g hg => ?_)
    simp only [hhl, holeList, List.mem_map, List.mem_range] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    exact ⟨rfl, rfl, (hholes j (by omega)).2.2⟩
  -- the invariant
  let I : Config → Prop := fun cc =>
    WordsBounded W cc ∧ (∀ i, i < 20 → cc.nreg (R + i) = c.nreg (R + i)) ∧
    cc.nreg (R + 30) = 0 ∧ cc.nreg (R + 31) = 1 ∧ cc.nreg (R + 32) = 2 ∧ cc.nreg (R + 33) = 3 ∧
    cc.nreg (R + 37) = 4 ∧ cc.nreg (R + 28) ≤ A ∧ cc.nreg (R + 36) = AB + 4 * cc.nreg (R + 28) ∧
    (∀ a, a < c.nreg ALLOC → cc.nmem a = c.nmem a) ∧ c.nreg ALLOC ≤ cc.nreg ALLOC ∧
    cc.nreg ALLOC + (A - cc.nreg (R + 28)) * Bi ≤ W ∧ ShotCtxG P W X Ok R M E cc ∧
    OriginIn cc (R + 3) o ∧ BestG P M R cc (sofJ M Q hl c.nmem AB (cc.nreg (R + 28))) z σ
  let Wr : ℕ → Prop := fun r => R + 16 ≤ r ∧ r < R + 300
  have I₁ : I c₁ := by
    refine ⟨e₁.wb_right, fun i hi => k1 _ (by omega), i30, i31, i32, i33, i37, by omega,
      by rw [i36, i28]; rfl, fun a _ => by rw [hM1], by rw [hA1], ?_, ?_, ?_, ?_⟩
    · rw [hA1, i28]
      have : (A - 0) * Bi ≤ (A + 1) * (16 * G) := by
        rw [hBi, hlc, Nat.sub_zero]
        exact Nat.mul_le_mul (by omega) (by omega)
      omega
    · refine ⟨⟨hS c c₁ k₁ hE e₁.wb_right F01, hG, hHW, ?_, ?_, i30, i31, ?_⟩, ?_, ?_, hOk, ?_, ?_⟩
      · rw [hM1, k1 R (by omega)]; exact hMD
      · rw [hM1, hA1, k1 _ (by omega)]; exact hmwf
      · rw [i34, k1 R (by omega)]
      · rw [hM1, hA1, k1 _ (by omega)]; exact hX
      · rw [hM1, k1 _ (by omega), k1 _ (by omega)]; exact hcap
      · rw [k1 _ (by omega)]; exact i35
      · rw [hM1, k1 R (by omega)]; exact hreg
    · exact originIn_copy ho (k1 _ (by omega)) (k1 _ (by omega)) (k1 _ (by omega))
    · rw [i28, sofJ_zero]
      refine ⟨by rw [i20]; omega, fun h => by rw [i20] at h; omega, fun _ => fun t _ h => ?_⟩
      exact h
  -- one iteration
  have body : ∀ cc, I cc → cc.nreg (R + 28) < cc.nreg (R + 2) →
      ∃ c' k, Exec P W (.seq (loadArc R) (.seq (levFG kc xc sh R 3 0) (stepArc R))) cc c' k ∧
        I c' ∧ k ≤ Bi ∧ A - c'.nreg (R + 28) < A - cc.nreg (R + 28) ∧
        FrameR Bo Wr cc c' k := by
    intro cc ⟨hwc, hin, c30, c31, c32, c33, c37, hjK, hptr, hmem, hAl, hrm, hctx, hoc, hbest⟩ hlt
    set j := cc.nreg (R + 28) with hj
    have hK2 : cc.nreg (R + 2) = A := hin 2 (by omega)
    rw [hK2] at hlt
    -- load the arc
    obtain ⟨c₂, k₂, e₂, hk₂, pc₂, f₂⟩ := loadArc_exec (P := P) (R := R) cc hwc c31 (by
      rw [hptr]; have hWc := hwc.1 ALLOC; omega)
    have k2 : ∀ r, ¬ (R + 38 ≤ r ∧ r < R + 44) → c₂.nreg r = cc.nreg r := fun r hr =>
      f₂.1 r (by simp only [decide_eq_false_iff_not]; exact hr)
    have harc : pieceR c₂ (rL R 0) = arcAt c.nmem AB j := by
      rw [show rL R 0 = R + 40 by unfold rL; omega, pc₂, hptr, arcAt_ptr]
      simp only [arcAt, Prod.mk.injEq, WPos.mk.injEq]
      refine ⟨⟨hmem _ (by omega), hmem _ (by omega)⟩, hmem _ (by omega), hmem _ (by omega)⟩
    have F02 : FrameR Bo Wr cc c₂ k₂ := FrameR.of_frameB f₂ (fun r hr => by
      simp only [decide_eq_true_eq] at hr; left; exact ⟨by omega, by omega⟩)
      (by simp only [decide_eq_false_iff_not]; unfold ALLOC; omega) _
    have ctx₂ : ShotCtxG P W X Ok R M E c₂ := ShotCtxG.frame hXl hS hctx e₂.wb_right F02
      (fun r hr => ⟨by omega, hr.2⟩) (fun i hi => k2 _ (by omega))
    have ho₂ : OriginIn c₂ (R + 3) o := originIn_copy hoc (k2 _ (by omega)) (k2 _ (by omega))
      (k2 _ (by omega))
    have g6 : c₂.nreg (R + 6) = c.nreg (R + 6) := by rw [k2 _ (by omega), hin 6 (by omega)]
    have g7 : c₂.nreg (R + 7) = c.nreg (R + 7) := by rw [k2 _ (by omega), hin 7 (by omega)]
    have hkl : ∀ ℓ, ℓ ≤ 3 → c₂.nreg (R + 30 + ℓ) = ℓ := by
      intro ℓ hℓ
      interval_cases ℓ
      · rw [k2 _ (by omega)]; exact c30
      · rw [k2 _ (by omega)]; exact c31
      · rw [k2 _ (by omega)]; exact c32
      · rw [k2 _ (by omega)]; exact c33
    have hhl2 : holeList c₂ R = hl := by
      simp only [hhl, holeList]
      rw [k2 _ (by omega), hin 9 (by omega)]
      refine List.map_congr_left (fun i hi => ?_)
      simp only [List.mem_range] at hi
      simp only [holeAt, Prod.mk.injEq, WPos.mk.injEq, and_true]
      refine ⟨?_, ?_⟩
      · rw [k2 _ (by omega), show R + 10 + 2 * i = R + (10 + 2 * i) by omega, hin _ (by omega)]
      · rw [k2 _ (by omega), show R + 11 + 2 * i = R + (11 + 2 * i) by omega, hin _ (by omega)]
    have hlv : levLeaves M Q c₂ R 3 0 (pieceR c₂ (rL R 0)) =
        leaves (M.key Q) hl (arcAt c.nmem AB j) := by
      rw [levLeaves_eq M Q c₂ R hkl 3 0 (by omega), holesFrom_eq c₂ R hkl, hhl2, harc]
    have hjK' := hlt
    have best₂ : BestG P M R c₂ (sofJ M Q hl c.nmem AB j) z (dirOf (c₂.nreg (R + 6))) := by
      rw [g6]
      exact hbest.congr (k2 (R + 20) (by omega)) (k2 (R + 21) (by omega))
        (k2 (R + 22) (by omega))
    obtain ⟨hpok, hwt⟩ := harcs j hjK'
    have hA2 : c₂.nreg ALLOC = cc.nreg ALLOC := k2 _ (by unfold ALLOC; omega)
    have hroomj := hrm
    have hKj : Bi ≤ (A - j) * Bi := Nat.le_mul_of_pos_left _ (by omega)
    obtain ⟨c₃, k₃, e₃, hk₃, b₃, fr₃⟩ := levG_exec hsh hBs hXl hR hRB hBo hS hk hBk hx hBx hol hof hoy
      3 0 c₂ (sofJ M Q hl c.nmem AB j) (by omega) e₂.wb_right ctx₂ ho₂
      (by rw [harc]; exact hpok)
      (fun j' _ hj' hj'' => by
        rw [hkl j' (by omega), k2 _ (by omega), hin 9 (by omega)] at hj''
        have := hholes j' (by omega)
        rw [k2 _ (by omega), k2 _ (by omega),
          show R + 10 + 2 * j' = R + (10 + 2 * j') by omega, hin _ (by omega),
          show R + 11 + 2 * j' = R + (11 + 2 * j') by omega, hin _ (by omega)]
        rw [show R + 10 + 2 * j' = R + (10 + 2 * j') by omega,
          show R + 11 + 2 * j' = R + (11 + 2 * j') by omega] at this
        exact ⟨this.1, this.2.1⟩)
      (fun p hp => by
        rw [hlv] at hp
        rw [g7]
        exact ⟨le_trans (leaf_wt M Q holes_ok hp) hwt,
          leaf_avoid M Q holes_ok hp (fun p' t h1 h2 h3 h4 h5 => havoid p' t h1 h2 h3 h4 j hjK' h5)⟩)
      best₂ (by rw [g7, hA2]; show _ + levCostG G 3 ≤ W; omega)
    rw [hlv, g6] at b₃
    rw [g7] at hk₃
    replace hk₃ : k₃ ≤ levCostG G 3 := hk₃
    have k3 : ∀ i, i < 300 → ¬ WrLev R 0 (R + i) → c₃.nreg (R + i) = c₂.nreg (R + i) :=
      fun i hi hw' => fr₃.1 _ (band_RB hR hRB hi) (by have := hR; unfold RegsOK at this; unfold ALLOC; omega) hw'
    have nw : ∀ i, (i < 20 ∨ (28 ≤ i ∧ i < 44)) → ¬ WrLev R 0 (R + i) := fun i hi => by
      unfold WrLev rL; omega
    -- advance
    have d31 : c₃.nreg (R + 31) = 1 := by
      rw [k3 31 (by omega) (nw 31 (by omega)), k2 _ (by omega), c31]
    have d37 : c₃.nreg (R + 37) = 4 := by
      rw [k3 37 (by omega) (nw 37 (by omega)), k2 _ (by omega), c37]
    have d28 : c₃.nreg (R + 28) = j := by rw [k3 28 (by omega) (nw 28 (by omega)), k2 _ (by omega)]
    have d36 : c₃.nreg (R + 36) = AB + 4 * j := by
      rw [k3 36 (by omega) (nw 36 (by omega)), k2 _ (by omega), hptr]
    have hAc : AB + 4 * A ≤ W := by have := hw.1 ALLOC; omega
    obtain ⟨c₄, k₄, e₄, hk₄, s28, s36, f₄⟩ := stepArc_exec (P := P) (R := R) c₃ e₃.wb_right d31 d37
      (by rw [d28]; omega) (by rw [d36]; omega)
    have k4 : ∀ r, r ≠ R + 28 → r ≠ R + 36 → c₄.nreg r = c₃.nreg r := fun r h1 h2 =>
      f₄.1 r (by simp [h1, h2])
    have F34 : FrameR Bo Wr c₃ c₄ k₄ := FrameR.of_frameB f₄ (fun r hr => by
      simp only [Bool.or_eq_true, beq_iff_eq] at hr; left; omega) (by simp; unfold ALLOC; omega) _
    have F24 : FrameR Bo Wr c₂ c₄ (k₃ + k₄) :=
      (fr₃.mono le_rfl (fun r hr => by unfold WrLev rL at hr; omega) le_rfl).trans F34
    have F04 := F02.trans F24
    have ex : Exec P W (.seq (loadArc R) (.seq (levFG kc xc sh R 3 0) (stepArc R))) cc c₄
      (k₂ + (k₃ + k₄)) := .seq e₂ (.seq e₃ e₄)
    have reg4 : ∀ i, (i < 20 ∨ (29 ≤ i ∧ i < 36) ∨ i = 37) → c₄.nreg (R + i) = cc.nreg (R + i) :=
      fun i hi => by
        rw [k4 _ (by omega) (by omega), k3 i (by omega) (nw i (by omega)), k2 _ (by omega)]
    refine ⟨c₄, _, ex, ⟨e₄.wb_right, fun i hi => by rw [reg4 i (by omega), hin i hi],
      by rw [reg4 30 (by omega), c30], by rw [reg4 31 (by omega), c31],
      by rw [reg4 32 (by omega), c32], by rw [reg4 33 (by omega), c33],
      by rw [reg4 37 (by omega), c37], by rw [s28, d28]; omega,
      by rw [s36, s28, d36, d28]; ring, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_⟩,
      by omega, by rw [s28, d28]; omega, F04⟩
    · rw [F04.2.2.1 a (by omega), hmem a ha]
    · have := F04.2.2.2.2.2.1; omega
    · have := F04.2.2.2.2.2.2; rw [s28, d28]
      have hsub : (A - (j + 1)) * Bi + Bi = (A - j) * Bi := by
        rw [← Nat.succ_mul]; congr 1; omega
      omega
    · exact ShotCtxG.frame hXl hS hctx e₄.wb_right F04 (fun r hr => ⟨by omega, hr.2⟩)
        (fun i hi => reg4 i (by omega))
    · exact originIn_copy hoc (reg4 3 (by omega)) (reg4 4 (by omega)) (reg4 5 (by omega))
    · rw [s28, d28, sofJ_succ]
      exact b₃.congr (k4 (R + 20) (by omega) (by omega)) (k4 (R + 21) (by omega) (by omega))
        (k4 (R + 22) (by omega) (by omega))
  -- the loop
  obtain ⟨c', kL, eL, hIc, hnt, hkL, frL⟩ := whileLtN_rel (P := P) (W := W) (a := R + 28)
    (b := R + 2) (body := .seq (loadArc R) (.seq (levFG kc xc sh R 3 0) (stepArc R))) I
    (FrameR Bo Wr) (fun cc => A - cc.nreg (R + 28)) Bi (fun cc h => h.1)
    (FrameR.refl _ _) (fun _ _ _ _ _ h1 h2 => h1.trans h2)
    (fun _ _ _ _ h hk => h.mono le_rfl (fun _ h => h) hk) body _ c₁ rfl I₁
  obtain ⟨-, hin, -, -, -, -, -, hjK, -, -, -, -, -, -, hbest⟩ := hIc
  have hK2 : c'.nreg (R + 2) = A := hin 2 (by omega)
  have hjE : c'.nreg (R + 28) = A := by rw [hK2] at hnt; omega
  rw [hjE] at hbest
  rw [i28, Nat.sub_zero] at hkL
  -- the frame
  have f₁' : FrameR Bo (fun r => R ≤ r ∧ r < R + 300) c c₁ k₁ :=
    F01.mono le_rfl (fun r h => ⟨by omega, h.2⟩) le_rfl
  have fL : FrameR Bo (fun r => R ≤ r ∧ r < R + 300) c₁ c' kL :=
    frL.mono le_rfl (fun r h => by obtain ⟨h1, h2⟩ := h; exact ⟨by omega, h2⟩) le_rfl
  have fT := f₁'.trans fL
  -- the cost
  have hcost : k₁ + kL ≤ shotCostG Fg K A := by
    unfold shotCostG
    have h1 : (Bi + 2) * A ≤ (16 * G) * A := Nat.mul_le_mul_right _ (by rw [hBi, hlc]; omega)
    rw [Nat.add_one_mul, Nat.mul_comm A]
    rw [← hG']
    omega
  refine ⟨c', k₁ + kL, .seq e₁ eL, hcost, ?_, fT⟩
  -- the postcondition
  intro M' o' hMD' ho'
  have hM' : M' = M := NFLoc.modelDesc_unique hMD' hMD
  have ho'' : o' = o := originIn_unique ho' ho
  rw [hM', ho'']
  refine ⟨hbest.1, sofJ M Q hl c.nmem AB A, ?_, ?_, fun h => ?_, hbest.2.2⟩
  · rintro x ⟨p, t, hp, ht0, ht1, ⟨j, hj, hc⟩, hno, rfl⟩
    simp only [sofJ, Set.mem_iUnion, Finset.mem_range]
    exact ⟨j, hj, mem_pcSet_leaves M Q holes_ok _ hp ht0 ht1 hc hno⟩
  · intro x hx
    simp only [sofJ, hiSet, Set.mem_iUnion, Finset.mem_range] at hx ⊢
    obtain ⟨j, hj, hx⟩ := hx
    exact ⟨j, hj, pcSet_leaves_sub M Q holes_ok _ hx⟩
  · exact hbest.2.1 h

end

end ShotListG

end Chazelle.Core
