module

public import Chazelle.Core.ShotListMain

/-!
# Shooting at a list of arcs with holes: the register frame

`ShotList.shotList_execR`: the wrapper `shotList sh R` meets its contract with the register
frame `FrameR oracleBands (R … R + 299)` (the proof of `shotList_meets`, which establishes it
before weakening to the band frame), so that a caller keeps its other registers of the band of
`R`.
-/

namespace Chazelle.Core

namespace ShotList

open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Chain (sideInArc)
open Chazelle.Visibility (rayPt)

@[expose] public section

/-- **The wrapper with its register frame**: besides the oracle bands, only the block
`R … R + 299` changes (`shotList_meets` with `FrameR`). -/
theorem shotList_execR {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {R : ℕ} (hR : RegsOK R) {P : Polygon} {W : ℕ} (c : Config)
    (hw : WordsBounded W c) (pre : ShotPre X Ok R P W c)
    (hroom : c.nreg ALLOC + shotCost (F (c.nreg (R + 7))) (c.nreg (R + 2)) ≤ W) :
    ∃ c' k, Exec P W (shotList sh R) c c' k ∧ k ≤ shotCost (F (c.nreg (R + 7))) (c.nreg (R + 2)) ∧
      ShotPost R P c c' ∧ FrameR oracleBands (fun r => R ≤ r ∧ r < R + 300) c c' k := by
  obtain ⟨hG, hHW, hX, hcap, hmwf, h0, hAB, hH3, H, C, hC, hreg, hOk, hm, harcs, hholes, o, ho,
    hol, hof, hoy, havoid⟩ := pre
  have hR' := hR; unfold RegsOK at hR'
  set M := chainModel C with hM
  set Q := Qof P
  set D := c.nreg R
  set AB := c.nreg (R + 1)
  set K := c.nreg (R + 2)
  set Fg := F (c.nreg (R + 7))
  set hl := holeList c R with hhl
  set z := o.eval M Q
  set σ := dirOf (c.nreg (R + 6))
  set Bi := levCost Fg 3 + 20 with hBi
  have eD : D = c.nreg R := rfl
  have eAB : AB = c.nreg (R + 1) := rfl
  have eK : K = c.nreg (R + 2) := rfl
  have hlc : levCost Fg 3 = 15 * (Fg + 30000) := by simp [levCost, treeCost]
  have hLB : levCost (F (c.nreg (R + 7))) 3 + 20 = Bi := rfl
  have hW8 : 8 ≤ W := by unfold hostWords at hHW; omega
  have hD6 := hmwf.1
  have hroom' : c.nreg ALLOC + shotCost Fg K ≤ W := hroom
  unfold shotCost at hroom'
  -- initialisation
  obtain ⟨c₁, k₁, e₁, hk₁, i30, i31, i32, i33, i34, i20, i28, i36, i37, i35, f₁⟩ :=
    shInit_exec (P := P) (R := R) c hw (by omega) (by omega)
  have k1 : ∀ r, (r < R + 20 ∨ R + 40 ≤ r) → c₁.nreg r = c.nreg r := fun r hr =>
    f₁.1 r (by simp only [Bmid, decide_eq_false_iff_not]; omega)
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := k1 _ (by unfold ALLOC; omega)
  have hM1 : c₁.nmem = c.nmem := f₁.2.2.1
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
    cc.nreg (R + 37) = 4 ∧ cc.nreg (R + 28) ≤ K ∧ cc.nreg (R + 36) = AB + 4 * cc.nreg (R + 28) ∧
    (MemEqBelow (c.nreg ALLOC) cc.nmem c.nmem) ∧ c.nreg ALLOC ≤ cc.nreg ALLOC ∧
    cc.nreg ALLOC + (K - cc.nreg (R + 28)) * Bi ≤ W ∧ ShotCtx P W X Ok R cc H C ∧
    OriginIn cc (R + 3) o ∧ BestOK P C R cc (sofJ M Q hl c.nmem AB (cc.nreg (R + 28))) z σ
  let Wr : ℕ → Prop := fun r => R + 16 ≤ r ∧ r < R + 300
  have I₁ : I c₁ := by
    refine ⟨e₁.wb_right, fun i hi => k1 _ (by omega), i30, i31, i32, i33, i37, by omega,
      by rw [i36, i28]; rfl, fun a _ => by rw [hM1], by rw [hA1], ?_, ?_, ?_, ?_⟩
    · rw [hA1, i28]
      have : (K - 0) * Bi ≤ (K + 1) * (16 * Fg + 500000) := by
        rw [hBi, hlc, Nat.sub_zero]
        exact Nat.mul_le_mul (by omega) (by omega)
      omega
    · refine ⟨hG, hHW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hOk, hm, i30, i31, ?_⟩
      · ram_rw [hM1, hA1, k1]; exact hX
      · ram_rw [hM1, k1, k1]; exact hcap
      · ram_rw [hM1, hA1, k1]; exact hmwf
      · ram_rw [hM1, k1 R]; exact h0
      · ram_rw [hM1, k1 R]; exact hC
      · ram_rw [i34, k1 R]
      · ram_rw [hM1, k1 R]; exact hreg
      · ram_rw [k1]; exact i35
    · exact originIn_copy ho (k1 _ (by omega)) (k1 _ (by omega)) (k1 _ (by omega))
    · rw [i28, sofJ_zero]
      refine ⟨by rw [i20]; omega, fun h => by rw [i20] at h; omega, fun _ => fun t _ h => ?_⟩
      exact h
  -- one iteration
  have body : ∀ cc, I cc → cc.nreg (R + 28) < cc.nreg (R + 2) →
      ∃ c' k, Exec P W (.seq (loadArc R) (.seq (levF sh R 3 0) (stepArc R))) cc c' k ∧ I c' ∧
        k ≤ Bi ∧ K - c'.nreg (R + 28) < K - cc.nreg (R + 28) ∧
        FrameR oracleBands Wr cc c' k := by
    intro cc ⟨hwc, hin, c30, c31, c32, c33, c37, hjK, hptr, hmem, hAl, hrm, hctx, hoc, hbest⟩ hlt
    set j := cc.nreg (R + 28) with hj
    have hK2 : cc.nreg (R + 2) = K := hin 2 (by omega)
    rw [hK2] at hlt
    have hWA : c.nreg ALLOC ≤ W := by have := hw.1 ALLOC; exact this
    -- load the arc
    obtain ⟨c₂, k₂, e₂, hk₂, pc₂, f₂⟩ := loadArc_exec (P := P) (R := R) cc hwc c31 (by
      rw [hptr]; have := hctx.2.2.2.2.1.1; have hWc := hwc.1 ALLOC; omega)
    have k2 : ∀ r, ¬ (R + 38 ≤ r ∧ r < R + 44) → c₂.nreg r = cc.nreg r := fun r hr =>
      f₂.1 r (by simp only [decide_eq_false_iff_not]; exact hr)
    have harc : pieceR c₂ (rL R 0) = arcAt c.nmem AB j := by
      rw [show rL R 0 = R + 40 by unfold rL; omega, pc₂, hptr, arcAt_ptr]
      simp only [arcAt, Prod.mk.injEq, WPos.mk.injEq]
      refine ⟨⟨hmem _ (by omega), hmem _ (by omega)⟩, hmem _ (by omega), hmem _ (by omega)⟩
    have F02 : FrameR oracleBands Wr cc c₂ k₂ := FrameR.of_frameB f₂ (fun r hr => by
      simp only [decide_eq_true_eq] at hr; left; exact ⟨by omega, by omega⟩)
      (by simp only [decide_eq_false_iff_not]; unfold ALLOC; omega) _
    have ctx₂ : ShotCtx P W X Ok R c₂ H C := ShotCtx.frame hXl hctx (F02.mono le_rfl
      (fun _ h => h) le_rfl) (fun i hi => k2 _ (by omega))
    have ho₂ : OriginIn c₂ (R + 3) o := originIn_copy hoc (k2 _ (by omega)) (k2 _ (by omega))
      (k2 _ (by omega))
    have g6 : c₂.nreg (R + 6) = c.nreg (R + 6) := by ram_rw [k2, hin 6]
    have g7 : c₂.nreg (R + 7) = c.nreg (R + 7) := by ram_rw [k2, hin 7]
    have hk : ∀ ℓ, ℓ ≤ 3 → c₂.nreg (R + 30 + ℓ) = ℓ := by
      intro ℓ hℓ
      interval_cases ℓ
      · ram_rw [k2]; exact c30
      · ram_rw [k2]; exact c31
      · ram_rw [k2]; exact c32
      · ram_rw [k2]; exact c33
    have hhl2 : holeList c₂ R = hl := by
      simp only [hhl, holeList]
      ram_rw [k2, hin 9]
      refine List.map_congr_left (fun i hi => ?_)
      simp only [List.mem_range] at hi
      simp only [holeAt, Prod.mk.injEq, WPos.mk.injEq, and_true]
      refine ⟨?_, ?_⟩
      · ram_rw [k2, show R + 10 + 2 * i = R + (10 + 2 * i) by omega, hin]
      · ram_rw [k2, show R + 11 + 2 * i = R + (11 + 2 * i) by omega, hin]
    have hlv : levLeaves M Q c₂ R 3 0 (pieceR c₂ (rL R 0)) =
        leaves (M.key Q) hl (arcAt c.nmem AB j) := by
      ram_rw [levLeaves_eq M Q c₂ R hk 3 0, holesFrom_eq c₂ R hk, hhl2, harc]
    have hjK' : j < K := hlt
    have best₂ : BestOK P C R c₂ (sofJ M Q hl c.nmem AB j) z (dirOf (c₂.nreg (R + 6))) := by
      rw [g6]
      exact hbest.congr (k2 (R + 20) (by omega)) (k2 (R + 21) (by omega))
        (k2 (R + 22) (by omega)) (k2 (R + 24) (by omega)) (k2 (R + 24 + 1) (by omega))
        (k2 (R + 24 + 2) (by omega)) (k2 (R + 24 + 3) (by omega))
    obtain ⟨hpok, hwt⟩ := harcs j hjK'
    have hA2 : c₂.nreg ALLOC = cc.nreg ALLOC := k2 _ (by unfold ALLOC; omega)
    have hroomj : cc.nreg ALLOC + (K - j) * Bi ≤ W := hrm
    have hKj : Bi ≤ (K - j) * Bi := Nat.le_mul_of_pos_left _ (by omega)
    obtain ⟨c₃, k₃, e₃, hk₃, b₃, fr₃⟩ := lev_exec hsh hBs hXl hR (H := H) (C := C) hol hof hoy
      3 0 c₂ (sofJ M Q hl c.nmem AB j) (by omega) e₂.wb_right ctx₂ ho₂ (by rw [harc]; exact hpok)
      (fun j' _ hj' hj'' => by
        ram_rw [hk j', k2, hin 9] at hj''
        have := hholes j' (by omega)
        ram_rw [k2, k2,
          show R + 10 + 2 * j' = R + (10 + 2 * j') by omega, hin,
          show R + 11 + 2 * j' = R + (11 + 2 * j') by omega, hin]
        rw [show R + 10 + 2 * j' = R + (10 + 2 * j') by omega,
          show R + 11 + 2 * j' = R + (11 + 2 * j') by omega] at this
        exact ⟨this.1, this.2.1⟩)
      (fun p hp => by
        rw [hlv] at hp
        rw [g7]
        exact ⟨le_trans (leaf_wt M Q holes_ok hp) hwt,
          leaf_avoid M Q holes_ok hp (fun p' t h1 h2 h3 h4 h5 => havoid p' t h1 h2 h3 h4 j hjK' h5)⟩)
      best₂ (by rw [g7, hA2]; omega)
    rw [hlv, g6] at b₃
    rw [g7] at hk₃
    have k3 : ∀ i, i < 300 → ¬ WrLev R 0 (R + i) → c₃.nreg (R + i) = c₂.nreg (R + i) :=
      fun i hi hw' => frameR_keep hR fr₃ hi hw'
    have nw : ∀ i, (i < 20 ∨ (28 ≤ i ∧ i < 44)) → ¬ WrLev R 0 (R + i) := fun i hi => by
      unfold WrLev rL; omega
    -- advance
    have d31 : c₃.nreg (R + 31) = 1 := by ram_rw [k3 31 (by omega) (nw 31 (by omega)), k2, c31]
    have d37 : c₃.nreg (R + 37) = 4 := by ram_rw [k3 37 (by omega) (nw 37 (by omega)), k2, c37]
    have d28 : c₃.nreg (R + 28) = j := by ram_rw [k3 28 (by omega) (nw 28 (by omega)), k2]
    have d36 : c₃.nreg (R + 36) = AB + 4 * j := by
      ram_rw [k3 36 (by omega) (nw 36 (by omega)), k2, hptr]
    have hAc : AB + 4 * K ≤ W := by have := hw.1 ALLOC; omega
    obtain ⟨c₄, k₄, e₄, hk₄, s28, s36, f₄⟩ := stepArc_exec (P := P) (R := R) c₃ e₃.wb_right d31 d37
      (by rw [d28]; omega) (by rw [d36]; omega)
    have k4 : ∀ r, r ≠ R + 28 → r ≠ R + 36 → c₄.nreg r = c₃.nreg r := fun r h1 h2 =>
      f₄.1 r (by simp [h1, h2])
    have F34 : FrameR oracleBands Wr c₃ c₄ k₄ := FrameR.of_frameB f₄ (fun r hr => by
      simp only [Bool.or_eq_true, beq_iff_eq] at hr; left; omega) (by simp; unfold ALLOC; omega) _
    have F24 : FrameR oracleBands Wr c₂ c₄ (k₃ + k₄) :=
      (fr₃.mono le_rfl (fun r hr => by unfold WrLev rL at hr; omega) le_rfl).trans F34
    have F04 := F02.trans F24
    have ex : Exec P W (.seq (loadArc R) (.seq (levF sh R 3 0) (stepArc R))) cc c₄
      (k₂ + (k₃ + k₄)) := .seq e₂ (.seq e₃ e₄)
    have reg4 : ∀ i, (i < 20 ∨ (29 ≤ i ∧ i < 36) ∨ i = 37) → c₄.nreg (R + i) = cc.nreg (R + i) :=
      fun i hi => by
        ram_rw [k4, k3 i (by omega) (nw i (by omega)), k2]
    refine ⟨c₄, _, ex, ⟨e₄.wb_right, fun i hi => by ram_rw [reg4 i, hin i hi],
      by ram_rw [reg4 30, c30], by ram_rw [reg4 31, c31],
      by ram_rw [reg4 32, c32], by ram_rw [reg4 33, c33],
      by ram_rw [reg4 37, c37], by rw [s28, d28]; omega,
      by rw [s36, s28, d36, d28]; ring, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_⟩,
      by omega, by rw [s28, d28]; omega, F04⟩
    · ram_rw [F04.2.2.1 a, hmem a ha]
    · have := F04.2.2.2.2.2.1; omega
    · have := F04.2.2.2.2.2.2; rw [s28, d28]
      have hsub : (K - (j + 1)) * Bi + Bi = (K - j) * Bi := by
        rw [← Nat.succ_mul]; congr 1; omega
      omega
    · exact ShotCtx.frame hXl hctx F04 (fun i hi => reg4 i (by omega))
    · exact originIn_copy hoc (reg4 3 (by omega)) (reg4 4 (by omega)) (reg4 5 (by omega))
    · rw [s28, d28, sofJ_succ]
      exact b₃.congr (k4 (R + 20) (by omega) (by omega)) (k4 (R + 21) (by omega) (by omega))
        (k4 (R + 22) (by omega) (by omega)) (k4 (R + 24) (by omega) (by omega))
        (k4 (R + 24 + 1) (by omega) (by omega)) (k4 (R + 24 + 2) (by omega) (by omega))
        (k4 (R + 24 + 3) (by omega) (by omega))
  -- the loop
  obtain ⟨c', kL, eL, hIc, hnt, hkL, frL⟩ := Exec.whileLtN_bounded_frame (P := P) (W := W) (a := R + 28)
    (b := R + 2) (body := .seq (loadArc R) (.seq (levF sh R 3 0) (stepArc R))) I
    (fun cc => K - cc.nreg (R + 28)) Bi (FrameR oracleBands Wr) (fun _ h => h.1)
    (fun d => (FrameR.refl _ _ d).mono le_rfl (fun _ h => h) (by decide)) (fun f g => (f.trans g).mono le_rfl (fun _ h => h) (by omega)) body I₁
  obtain ⟨-, hin, -, -, -, -, -, hjK, -, -, -, -, hctx, -, hbest⟩ := hIc
  have hK2 : c'.nreg (R + 2) = K := hin 2 (by omega)
  have hjE : c'.nreg (R + 28) = K := by rw [hK2] at hnt; omega
  rw [hjE] at hbest
  rw [i28, Nat.sub_zero] at hkL
  -- the frame
  have f₁' : FrameR oracleBands (fun r => R ≤ r ∧ r < R + 300) c c₁ k₁ :=
    FrameR.of_frameB f₁ (fun r hr => by
      simp only [Bmid, decide_eq_true_eq] at hr; left; omega)
      (by simp only [Bmid, decide_eq_false_iff_not]; unfold ALLOC; omega) k₁
  have fL : FrameR oracleBands (fun r => R ≤ r ∧ r < R + 300) c₁ c' kL :=
    frL.mono le_rfl (fun r h => by obtain ⟨h1, h2⟩ := h; exact ⟨by omega, h2⟩) le_rfl
  have fT := f₁'.trans fL
  have toF : Frame (insert (bandOf R) oracleBands) c c' (k₁ + kL) := by
    obtain ⟨r₁, rr₁, m₁, rm₁, o₁, a₁, b₁⟩ := fT
    have hb : ∀ r, bandOf r ∉ insert (bandOf R) oracleBands →
        bandOf r ∉ oracleBands ∧ ¬ (R ≤ r ∧ r < R + 300) := fun r hr =>
      ⟨fun h => hr (Finset.mem_insert_of_mem h), fun h => hr (by
        rw [band_block hR h.1 h.2]; exact Finset.mem_insert_self _ _)⟩
    exact ⟨fun r hr ha => r₁ r (hb r hr).1 ha (hb r hr).2,
      fun r hr => rr₁ r (hb r hr).1 (hb r hr).2, m₁, rm₁, o₁, a₁, b₁⟩
  -- the cost
  have hcost : k₁ + kL ≤ shotCost Fg K := by
    unfold shotCost
    have h1 : (Bi + 2) * K ≤ (16 * Fg + 500000) * K :=
      Nat.mul_le_mul_right _ (by rw [hBi, hlc]; omega)
    rw [Nat.add_one_mul, Nat.mul_comm K]
    omega
  refine ⟨c', k₁ + kL, .seq e₁ eL, hcost, ?_, fT⟩
  -- the postcondition
  intro M' o' hMD ho'
  have hM' : M' = M := NFLoc.modelDesc_unique hMD (Or.inl ⟨h0, H, C, hC, rfl⟩)
  have ho'' : o' = o := originIn_unique ho' ho
  subst hM' ho''
  refine ⟨hbest.1, sofJ M Q hl c.nmem AB K, ?_, ?_, fun h => ?_, hbest.2.2⟩
  · rintro x ⟨p, t, hp, ht0, ht1, ⟨j, hj, hc⟩, hno, rfl⟩
    simp only [sofJ, Set.mem_iUnion, Finset.mem_range]
    exact ⟨j, hj, mem_pcSet_leaves M Q holes_ok _ hp ht0 ht1 hc hno⟩
  · intro x hx
    simp only [sofJ, hiSet, Set.mem_iUnion, Finset.mem_range] at hx ⊢
    obtain ⟨j, hj, hx⟩ := hx
    exact ⟨j, hj, pcSet_leaves_sub M Q holes_ok _ hx⟩
  · obtain ⟨t, a1, a2, a3, a4, -⟩ := hbest.2.1 h
    exact ⟨t, a1, a2, a3, a4⟩

end

end ShotList

end Chazelle.Core
