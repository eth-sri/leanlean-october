module

public import Chazelle.Golf

public import Chazelle.Core.RestoreTShotOps
public import Chazelle.Core.RestoreTIRec

/-!
# WP-E, the candidate test on the RAM: the abscissa comparison of the shot wrapper

`xcR a b d e` compares the abscissae of the points of two walk positions at one height (the
wrapper's `XG` contract): an abscissa record of each (`gRec`: `absKey` in a chain model, `iRec`
in the interior model), then `absCmp`.  The first record is saved in `10700 … 10703` (band
`bSign`, outside the registers of the primitives).

* `hostReg_run`: the host of the chain descriptor is regular throughout a run (G10/G11);
* `gRec_exec`: the record of one position, with the radius of the model (`KindRad`);
* `xcR_xG`: `xcR` is an abscissa comparison of the wrapper, for the admissible heights `YR M`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim SignK NFLoc ShotList ShotListG

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-! ## The programs -/

/-- The inputs of `absKey`. -/
def cRecL (a b : ℕ) : List (ℕ × ℕ) := [(50200, 83020), (50201, a), (50202, b)]

/-- The abscissa record of a chain position. -/
def cRec (a b : ℕ) : Stmt := .seq (block (copies (cRecL a b))) absKey

/-- The abscissa record of a position, in either model. -/
def gRec (a b : ℕ) : Stmt := .ifLtN 83021 83023 (cRec a b) (iRec a b)

/-- Saving the first record. -/
def recSave : List (ℕ × ℕ) := [(10700, 50210), (10701, 50211), (10702, 50212), (10703, 50213)]

/-- The two records into the inputs of `absCmp`. -/
def recLoad : List (ℕ × ℕ) := [(50201, 10700), (50202, 10701), (50203, 10702), (50204, 10703),
  (50205, 50210), (50206, 50211), (50207, 50212), (50208, 50213)]

/-- **The abscissa comparison of the test.** -/
def xcR (a b d e : ℕ) : Stmt :=
  .seq (gRec a b) (.seq (block (copies recSave)) (.seq (gRec d e)
    (.seq (block (copies recLoad)) absCmp)))

/-- The registers written by `xcR`. -/
def BxR (r : ℕ) : Bool :=
  Bprim r || decide (50200 ≤ r ∧ r < 50210) || decide (10700 ≤ r ∧ r < 10704)

theorem wr_gRec (a b : ℕ) : wr BgK (gRec a b) = true := by
  have h1 : wr BgK absKey = true := wr_mono wr_absKey (fun r h => ⊚ BgK, h)
  have h2 : wr BgK (iRec a b) = true := wr_mono (wr_iRec a b) (fun r h => by
    ϴ' BiR, decide_eq_true_eq at h
    simp only [BgK, Bprim, Bool.or_eq_true, decide_eq_true_eq]; omega)
  simp only [gRec, cRec, cRecL, copies, wr, block, wrOK, h1, h2, List.map_cons, List.map_nil,
    Bool.and_true]
  decide

theorem wr_xcR (a b d e : ℕ) : wr BxR (xcR a b d e) = true := by
  have h1 : wr BxR absCmp = true := wr_mono wr_absCmp (fun r h => ⊚ BxR, h)
  have h2 : ∀ a b, wr BxR (gRec a b) = true := fun a b =>
    wr_mono (wr_gRec a b) (fun r h => by
      ϴ' BgK, Bool.or_eq_true at h; simp only [BxR, Bool.or_eq_true]; tauto)
  ϴ xcR, wr, h2, h1, Bool.and_true, Bool.true_and
  ϴ recSave, recLoad, copies, block, wr, wrOK, List.map_cons, List.map_nil
  decide

theorem opW_BxR : OpW BxR := fun r hr => by
  ϴ' BxR, Bool.or_eq_true, decide_eq_true_eq at hr
  rcases hr with (hr | hr) | hr
  · exact (opW_BgK r (⊚ BgK, hr))
  · exact (opW_BgK r (⊚ BgK, hr))
  · refine ⟨?_, by unfold ALLOC; omega⟩
    have : bandOf r = bSign := by unfold bandOf bSign; omega
    rw [this]; decide

/-! ## The radius of the model -/

/-- The radius of the abscissa records of the model of a run: the box radius of the chain of the
descriptor, or `coordBound Q + 1` in the interior model. -/
def KindRad (P : Polygon) (M : Model) (c : Config) (Rd : ℝ) : Prop :=
  (c.nreg 83021 = 0 ∧ ∃ H C, ChainDescAt c.nmem (c.nreg 83020) (Qof P) H C ∧ M = chainModel C ∧
    ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 83020) ∧ HostRegular (Qof P).n H ∧
    Rd = C.radius) ∨
  (c.nreg 83021 = 1 ∧ M = interiorModel (Qof P) ∧
    (c.nmem (c.nreg 83020) = 1 ↔ Mountain.LeftInside (Qof P)) ∧
    Rd = Jordan.coordBound (Qof P) + 1)

/-- **The radius of a run.** -/
theorem kindRad_run (hE : TGood P W M N c₀) (hI : TInv W c₀ c) : ∃ Rd, KindRad P M c Rd := by
  have h21 := hI.h21
  have h20 := hI.h20
  have i0 := hI.hin 83000 (by norm_num) (by norm_num)
  have hD := hE.hwfMD.1
  rcases hE.kind with ⟨h0, C, hM⟩ | ⟨h1, hMi, hbit⟩
  · obtain ⟨H, C', hC, hM', hwf⟩ := hI.chain hE hM
    refine ⟨C'.radius, Or.inl ⟨by rw [h21, h0], H, C', hC, hM', hwf, ?_, rfl⟩⟩
    have hr : HReg P c.nmem (c₀.nreg 83000) :=
      hreg_keep hE.hwfMD hE.hMD hE.hreg (fun a ha => hI.hm a ha)
    exact hr (by rw [hI.hm _ (by omega)]; exact h0) H C' (by rw [← h20]; exact hC)
  · refine ⟨_, Or.inr ⟨by rw [h21, h1], hMi, ?_, rfl⟩⟩
    rw [h20, hI.hm _ (by omega)]; exact hbit

/-- The radius survives a frame that keeps the memory and the registers `83020`, `83021` and the
allocator. -/
theorem KindRad.frame {Rd : ℝ} {c' : Config} (h : KindRad P M c Rd) (hm : c'.nmem = c.nmem)
    (h20 : c'.nreg 83020 = c.nreg 83020) (h21 : c'.nreg 83021 = c.nreg 83021)
    (hA : c'.nreg ALLOC = c.nreg ALLOC) : KindRad P M c' Rd := by
  unfold KindRad; rw [hm, h20, h21, hA]; exact h

/-! ## One record -/

/-- **The abscissa record of one position.** -/
theorem gRec_exec (hE : TGood P W M N c₀) (hI : TInv W c₀ c) {Rd : ℝ} (hK : KindRad P M c Rd)
    {a b : ℕ} (ha : InR a) (hb : InR b)
    (hp : ProperPos M (Qof P) P.n ⟨c.nreg a, c.nreg b⟩) (he : c.nreg a < M.W.n)
    (hy : ∀ C : Chain, M = chainModel C → |(M.pos (Qof P) ⟨c.nreg a, c.nreg b⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + 16800 ≤ W) :
    ∃ c' k, Exec P W (gRec a b) c c' k ∧ k ≤ 16800 ∧
      AbsRec P c' 50210 (M.pos (Qof P) ⟨c.nreg a, c.nreg b⟩).1 Rd ∧ FrameB BgK c c' := by
  unfold InR at ha hb
  have h23 := hI.h23
  have hG := hE.hG
  have hHW := hE.hW
  rcases hK with ⟨h21, H, C, hC, hMC, hwf, hreg, rfl⟩ | ⟨h21, hMi, hbit, rfl⟩
  · -- a chain model: `absKey`
    obtain ⟨c₁, c', k, h1, -, -, ex, hk, hout, -⟩ := callPrim absKey_meets (cRecL a b)
      (by simp only [cRecL, List.mem_cons, List.not_mem_nil, or_false]
          rintro q (rfl | rfl | rfl) r (rfl | rfl | rfl) <;> simp only <;> omega)
      (by simp [cRecL]) (by simp [cRecL]) (src := 83020) (by simp [cRecL]) hI.hw hG hHW hwf hC
      (fun c₁ h1 _ hm => by
        have q0 := h1 (50200, 83020) (by simp [cRecL])
        have q1 := h1 (50201, a) (by simp [cRecL])
        have q2 := h1 (50202, b) (by simp [cRecL])
        simp only at q0 q1 q2
        refine ⟨⟨by rw [q1, ← hMC]; exact he, by rw [q1, q2, ← hMC]; exact hp,
          by rw [q1, q2, ← hMC]; exact hy C hMC⟩, fun H' hH' => ?_⟩
        rw [hm, q0] at hH'
        have := NFLoc.hostAt_unique hH' hC.1
        subst this
        have hn : (Qof P).n = P.n := shear_n _ _
        rw [← hn]; exact hreg)
      (by omega)
    have q1 := h1 (50201, a) (by simp [cRecL])
    have q2 := h1 (50202, b) (by simp [cRecL])
    simp only at q1 q2
    have hr : AbsRec P c' 50210 ((chainModel C).pos (Qof P) ⟨c₁.nreg 50201, c₁.nreg 50202⟩).1
      C.radius := hout
    rw [q1, q2, ← hMC] at hr
    have ex' : Exec P W (gRec a b) c c' (k + 1) := .ifLtN_true (by rw [h21, h23]; omega) ex
    exact ⟨c', _, ex', by simp [cRecL] at hk; omega, hr, exec_frameB ex' (wr_gRec a b)⟩
  · -- the interior model: `iRec`
    subst hMi
    have hn := interior_n (P := P)
    obtain ⟨c', k, ex, hk, hr, -⟩ := iRec_exec (P := P) (W := W) hG
      (by unfold hostWords at hHW; omega) hI.hw (a := a) (b := b) hbit rfl hI.h22 ha hb hp
      (by rw [← hn]; exact he)
    have ex' : Exec P W (gRec a b) c c' (k + 2) := .ifLtN_false (by rw [h21, h23]; omega) ex
    exact ⟨c', _, ex', by omega, hr, exec_frameB ex' (wr_gRec a b)⟩

/-! ## The comparison -/

/-- The admissible heights of the test's shots: inside the box of a chain model. -/
def YR (M : Model) (y : ℝ) : Prop := ∀ C : Chain, M = chainModel C → |y| < C.radius

/-- **`xcR` is an abscissa comparison of the wrapper.** -/
theorem xcR_xG (hE : TGood P W M N c₀) :
    XG P W M RS0 (TInv W c₀) (YR M) xcR BxR 34000 := by
  intro a b d e ha hb hd he c hw hctx hp1 he1 hp2 he2 hyy hY hroom
  have hI : TInv W c₀ c := hctx.1
  have inR : ∀ r, InB RS0 r → InR r := fun r h => by unfold InB RS0 at h; unfold InR; omega
  have ha' := inR a ha
  have hb' := inR b hb
  have hd' := inR d hd
  have he' := inR e he
  unfold InR at ha' hb' hd' he'
  obtain ⟨Rd, hK⟩ := kindRad_run hE hI
  -- the first record
  obtain ⟨c₁, k₁, e₁, hk₁, r₁, f₁⟩ := gRec_exec hE hI hK (inR a ha) (inR b hb) hp1 he1 hY
    (by omega)
  have g₁ : ∀ r, 80000 ≤ r → r < 90000 → c₁.nreg r = c.nreg r := fun r h1 h2 => f₁.1 r (by
    simp only [BgK, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := f₁.1 _ (by simp [BgK, Bprim, ALLOC])
  -- save it
  obtain ⟨c₂, e₂, v₂, f₂⟩ := copies_run (P := P) recSave c₁ e₁.wb_right
    (by simp only [recSave, List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl) q (rfl | rfl | rfl | rfl) <;> simp)
    (by simp [recSave])
  simp only [recSave, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₂
  obtain ⟨s0, s1, s2, s3⟩ := v₂
  have k2 : ∀ r, ¬ (10700 ≤ r ∧ r < 10704) → c₂.nreg r = c₁.nreg r := fun r hr =>
    f₂.1 r (by simp [recSave]; omega)
  have r₂ : AbsRec P c₂ 10700 (M.pos (Qof P) ⟨c.nreg a, c.nreg b⟩).1 Rd :=
    absRec_copy r₁ s0 (by rw [s1]) (by rw [s2]) (by rw [s3])
  have f₁' : FrameB BxR c c₁ := frameB_mono f₁ (fun r h => by
    simp only [BgK, Bool.or_eq_true] at h; simp only [BxR, Bool.or_eq_true]; tauto)
  have F02 : FrameB BxR c c₂ := f₁'.trans (frameB_mono f₂ (fun r hr => by
    simp [recSave] at hr; simp only [BxR, Bool.or_eq_true, decide_eq_true_eq]; right; omega))
  have g₂ : ∀ r, 80000 ≤ r → r < 90000 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [k2 r (by omega)]; exact g₁ r h1 h2
  have hA2 : c₂.nreg ALLOC = c.nreg ALLOC := by rw [k2 _ (by unfold ALLOC; omega), hA1]
  have hI2 : TInv W c₀ c₂ := stable_tinv (Bo := oracleBands) (by decide) c c₂ 0 hI e₂.wb_right
    (FrameR.of_frameB F02 (fun r hr => Or.inr (opW_BxR r hr).1) (opW_alloc opW_BxR) 0)
  have hK2 : KindRad P M c₂ Rd := hK.frame F02.2.2.1 (g₂ _ (by norm_num) (by norm_num))
    (g₂ _ (by norm_num) (by norm_num)) hA2
  -- the second record
  obtain ⟨c₃, k₃, e₃, hk₃, r₃, f₃⟩ := gRec_exec hE hI2 hK2 (inR d hd) (inR e he)
    (by rw [g₂ d hd'.1 hd'.2, g₂ e he'.1 he'.2]; exact hp2)
    (by rw [g₂ d hd'.1 hd'.2]; exact he2)
    (fun C hC => by rw [g₂ d hd'.1 hd'.2, g₂ e he'.1 he'.2, ← hyy]; exact hY C hC)
    (by rw [hA2]; omega)
  rw [g₂ d hd'.1 hd'.2, g₂ e he'.1 he'.2] at r₃
  have r₂' : AbsRec P c₃ 10700 (M.pos (Qof P) ⟨c.nreg a, c.nreg b⟩).1 Rd :=
    absRec_copy r₂ (f₃.1 _ (by decide)) (f₃.1 _ (by decide)) (f₃.1 _ (by decide))
      (f₃.1 _ (by decide))
  -- load both
  obtain ⟨c₄, e₄, v₄, f₄⟩ := copies_run (P := P) recLoad c₃ e₃.wb_right
    (by simp only [recLoad, List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
          q (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp)
    (by simp [recLoad])
  simp only [recLoad, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₄
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := v₄
  have x1 : AbsRec P c₄ 50201 (M.pos (Qof P) ⟨c.nreg a, c.nreg b⟩).1 Rd :=
    absRec_copy r₂' l1 (by rw [l2]) (by rw [l3]) (by rw [l4])
  have x2 : AbsRec P c₄ 50205 (M.pos (Qof P) ⟨c.nreg d, c.nreg e⟩).1 Rd :=
    absRec_copy r₃ l5 (by rw [l6]) (by rw [l7]) (by rw [l8])
  have hA4 : c₄.nreg ALLOC = c.nreg ALLOC := by
    rw [f₄.1 _ (by simp [recLoad, ALLOC]), f₃.1 _ (by simp [BgK, Bprim, ALLOC]), hA2]
  have hP3 : P.n + 3 ≤ W := by have := hE.hW; unfold hostWords at this; omega
  obtain ⟨c₅, k₅, e₅, hk₅, post₅, -⟩ := absCmp_meets P W c₄ e₄.wb_right
    ⟨hE.hG, hP3, _, _, Rd, x1, x2⟩ (by rw [hA4]; show _ + 260 ≤ W; omega)
  replace hk₅ : k₅ ≤ 260 := hk₅
  have bit := post₅ _ _ Rd x1 x2
  have ex : Exec P W (xcR a b d e) c c₅ _ := .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  refine ⟨c₅, _, ex, by simp only [recSave, recLoad, List.length_cons, List.length_nil]; omega,
    bit, exec_frameB ex (wr_xcR a b d e)⟩

end

end Restore

end Chazelle.Core
