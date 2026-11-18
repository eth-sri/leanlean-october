module

public import Chazelle.Core.DownPhaseDrvBRegA
public import Chazelle.Core.DownPhaseDrvBPieces2
public import Chazelle.Core.DownPhaseDrvRHostSpec

/-!
# Down-phase base (D9), RAM: the host of a region

`hostS sH`: the host of region `r` into a fresh `HostAt` block (`r212022`, items `r212021`,
points `r212016`): the host RAM `sH` (`DrvR.HostRamSpec`) for `K > 0`, the whole walk `host0`
for `K = 0` (`hostS_exec`).  `HostOK`, `ExpOK`: the bodies of `HostRamSpec` and `ExpSpec`.
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs SignK WalkKey
open BuildRam (FrameM FrameM.mono FrameM.trans FrameB.toM)
open DrvR (regHost)

@[expose] public section

/-- The body of `DrvR.HostRamSpec`. -/
def HostOK (sH : Stmt) (κH : ℕ) : Prop :=
  Meets sH {bDownDrv}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ c.nreg 215002 ≤ 1 ∧
      (c.nreg 215002 = 1 ↔ Mountain.LeftInside (Qof P)) ∧
      ∃ (L : List (ℕ × ℕ × ℕ)) (E : List ℕ), L ≠ [] ∧
        ChordTriplesOK (interiorModel (Qof P)) (Qof P) L ∧ E.Perm (List.range (2 * L.length)) ∧
        E.Pairwise (BuildNF.codeLe (interiorModel (Qof P)) (Qof P) L) ∧
        (interiorModel (Qof P)).DegLe
          ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P))
            (Qof P)) 4 ∧
        NFWithin c.nmem (c.nreg 215000) (c.nreg ALLOC)
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) ∧
        c.nreg 215001 < (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions)
    (fun P c c' =>
      (∀ q, bandOf q = bDownDrv → (q < 215000 ∨ 216000 ≤ q) → c'.nreg q = c.nreg q) ∧
      ∀ (L : List (ℕ × ℕ × ℕ)) (E : List ℕ), L ≠ [] →
        ChordTriplesOK (interiorModel (Qof P)) (Qof P) L → E.Perm (List.range (2 * L.length)) →
        E.Pairwise (BuildNF.codeLe (interiorModel (Qof P)) (Qof P) L) →
        NFAt c.nmem (c.nreg 215000) (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) →
        let H := regHost (decide (c.nreg 215002 = 1)) (Qof P).n
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 215001)
        c.nreg ALLOC ≤ c'.nreg 215010 ∧ c'.nreg 215010 + 3 * H.length + 1 ≤ c'.nreg ALLOC ∧
          HostAt c'.nmem (c'.nreg 215010) H ∧ c'.nreg 215011 = H.length ∧
          c'.nreg 215012 = (H.pts (Qof P).n).length)
    (fun _ _ => κH)

theorem hostOK_of (h : DrvR.HostRamSpec) : ∃ sH κH, HostOK sH κH := h

/-- The body of `ExpSpec`. -/
def ExpOK (sE : Stmt) (κE : ℕ) : Prop :=
  ∀ (P : Polygon) (W : ℕ) (c : Config) (H : Host) (li : Bool),
    WordsBounded W c → HostAt c.nmem (c.nreg 212022) H → HostWF P.n H →
    c.nreg 212021 = H.length → c.nreg 212016 = (H.pts P.n).length →
    c.nreg 212011 = (if li then 1 else 0) → c.nreg 212010 = P.n →
    c.nreg 212000 = 1 → c.nreg 212001 = 0 → c.nreg 212002 = 2 →
    c.nreg 212022 + 3 * H.length + 1 ≤ c.nreg 212015 →
    c.nreg 212015 + 3 * (H.pts P.n).length ≤ W →
    ∃ c' k, Exec P W sE c c' k ∧ k ≤ κE * ((H.pts P.n).length + H.length + 1) ∧
      PtArrB c'.nmem (c.nreg 212015) (wlist li (H.pts P.n)) ∧
      (∀ a, (a < c.nreg 212015 ∨ c.nreg 212015 + 3 * (H.pts P.n).length ≤ a) →
        c'.nmem a = c.nmem a) ∧
      FrameM (fun r => decide (212023 ≤ r ∧ r ≤ 212031)) c c'

theorem expOK_of (h : ExpSpec) : ∃ sE κE, ExpOK sE κE := h

/-- The host RAM call (`K > 0`). -/
def hostK (sH : Stmt) : Stmt :=
  .seq (block [.copyN 215000 210005, .copyN 215001 212014, .copyN 215002 212011])
    (.seq sH (block [.copyN 212022 215010, .copyN 212021 215011, .copyN 212016 215012]))

/-- **The host of the region.** -/
def hostS (sH : Stmt) : Stmt := .ifLtN 212001 212012 (hostK sH) host0


section exec

variable {P : Polygon} {W : ℕ}

/-- A register frame within band `bDownDrv` is a `bDownDrv` frame. -/
theorem frame21_of_B {B : ℕ → Bool} {c c' : Config} {k : ℕ}
    (hB : ∀ r, B r = true → bandOf r = bDownDrv) (hf : FrameB B c c') (hrr : c'.rreg = c.rreg) :
    Frame {bDownDrv} c c' k := by
  have hA : c'.nreg ALLOC = c.nreg ALLOC := hf.1 _ (by
    cases h : B ALLOC
    · rfl
    · have := hB _ h; unfold ALLOC bandOf bDownDrv at this; omega)
  exact frame21 (fun r h => Or.inl (hB r h)) (FrameB.toM hf) (fun a _ => by rw [hf.2.2.1]) hrr
    (by omega) (by omega)

set_option maxHeartbeats 8000000 in
/-- **The host of the region.** -/
theorem hostS_exec {sH : Stmt} {κH : ℕ} (hH : HostOK sH κH) {E : BEnv} (hE : BGood E) {r : ℕ}
    (hr : r < E.K + 1) (c : Config) (hw : WordsBounded E.W c) (R : BRegs E c)
    (h14 : c.nreg 212014 = r) (hlow : ∀ a, a < E.B₂ → c.nmem a = E.m₀ a)
    (hA : E.B₂ ≤ c.nreg ALLOC) (hroom : c.nreg ALLOC + κH + 20 ≤ E.W) :
    ∃ c' k, ∃ H : Host, Exec E.P E.W (hostS sH) c c' k ∧ k ≤ κH + 20 ∧
      HostAt c'.nmem (c'.nreg 212022) H ∧ HostWF E.P.n H ∧ c'.nreg 212021 = H.length ∧
      c'.nreg 212016 = (H.pts E.P.n).length ∧ E.pts r = wlist E.li (H.pts E.P.n) ∧
      c.nreg ALLOC ≤ c'.nreg 212022 ∧ c'.nreg 212022 + 3 * H.length + 1 ≤ c'.nreg ALLOC ∧
      (∀ q, bandOf q = bDownDrv → (q < 215000 ∨ 216000 ≤ q) → q ≠ 212016 → q ≠ 212021 →
        q ≠ 212022 → q ≠ 212032 → q ≠ 212035 → c'.nreg q = c.nreg q) ∧
      Frame {bDownDrv} c c' k := by
  have hQn := hE.hQn
  have hn3 := hE.hn3
  rcases Nat.eq_zero_or_pos E.K with hK | hK
  · -- the whole walk
    obtain ⟨c', k, e, hk, v22, vA, hH0, v16, v21, hm, FM, F⟩ := host0_exec (P := E.P) c hw R.n
      (by omega) R.c0 R.c1 (by omega)
    have ex : Exec E.P E.W (hostS sH) c c' (k + 2) :=
      .ifLtN_false (by rw [R.c1, R.K, hK]; omega) e
    refine ⟨c', k + 2, [HostItem.run 0 (E.P.n - 1)], ex, by omega, by rw [v22]; exact hH0,
      fun it hit => ?_, by rw [v21]; rfl, ?_, ?_, by rw [v22], by rw [v22, vA]; simp,
      fun q hq1 _ a b d e f => FM.1 q (by
        have h9 : q ≠ 9999 := by intro h; subst h; simp [bandOf, bDownDrv] at hq1
        simp [a, b, d, e, f, h9]),
      F.mono le_rfl (by omega)⟩
    · simp only [List.mem_singleton] at hit; subst hit; exact ⟨by omega, by omega⟩
    · rw [v16]; simp [Host.pts, HostItem.pts]; omega
    · rw [BGood.pts_zero hK, hQn]
  · -- the host RAM
    have hr' : r < E.N.nRegions := by rw [hE.nRegions]; exact hr
    obtain ⟨c₁, k₁, e₁, hk₁, v0, v1, v2, g₁, m₁, rr₁⟩ : ∃ c₁ k₁, Exec E.P E.W
        (block [.copyN 215000 210005, .copyN 215001 212014, .copyN 215002 212011]) c c₁ k₁ ∧
        k₁ = 3 ∧ c₁.nreg 215000 = E.H ∧ c₁.nreg 215001 = r ∧
        c₁.nreg 215002 = (if E.li then 1 else 0) ∧
        (∀ q, q ≠ 215000 → q ≠ 215001 → q ≠ 215002 → c₁.nreg q = c.nreg q) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg := by
      exec_block
      refine ⟨rfl, ?_, ?_, ?_, fun q a b d => ?_, rfl, rfl⟩ <;> config_simp
      · exact R.h5
      · exact h14
      · exact R.li
      · simp [a, b, d]
    have w₁ := e₁.wb_right
    have A₁ : c₁.nreg ALLOC = c.nreg ALLOC := g₁ _ (by decide) (by decide) (by decide)
    have hNW : NFWithin c₁.nmem E.H (c₁.nreg ALLOC) E.N := by
      rw [A₁]
      exact (hE.hNF.transport (fun a ha => by rw [m₁]; exact hlow a ha)).mono hA
    have hLne : E.L ≠ [] := List.ne_nil_of_length_pos hK
    obtain ⟨c₂, k₂, e₂, hk₂, ⟨pk, pH⟩, F₂⟩ := hH E.P E.W c₁ w₁
      ⟨hE.hG, hE.hWh, by rw [v2]; split_ifs <;> omega,
        by rw [v2, ← hE.hli]; cases E.li <;> simp, E.L, E.E, hLne, hE.hok, hE.hperm, hE.hsort,
        hE.hdeg, by rw [v0]; exact hNW, by rw [v1]; exact hr'⟩
      (by show c₁.nreg ALLOC + κH ≤ E.W; rw [A₁]; omega)
    have hp := pH E.L E.E hLne hE.hok hE.hperm hE.hsort (by rw [v0]; exact hNW.nfAt)
    dsimp only at hp
    have hdec : decide (c₁.nreg 215002 = 1) = E.li := by rw [v2]; cases E.li <;> simp
    rw [hdec, v1] at hp
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hp
    have w₂ := e₂.wb_right
    obtain ⟨c₃, k₃, e₃, hk₃, u22, u21, u16, g₃, m₃, rr₃⟩ : ∃ c₃ k₃, Exec E.P E.W
        (block [.copyN 212022 215010, .copyN 212021 215011, .copyN 212016 215012]) c₂ c₃ k₃ ∧
        k₃ = 3 ∧ c₃.nreg 212022 = c₂.nreg 215010 ∧ c₃.nreg 212021 = c₂.nreg 215011 ∧
        c₃.nreg 212016 = c₂.nreg 215012 ∧
        (∀ q, q ≠ 212022 → q ≠ 212021 → q ≠ 212016 → c₃.nreg q = c₂.nreg q) ∧
        c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg := by
      exec_block
      refine ⟨rfl, ?_, ?_, ?_, fun q a b d => ?_, rfl, rfl⟩ <;> config_simp
      simp [a, b, d]
    have ex : Exec E.P E.W (hostS sH) c c₃ (k₁ + (k₂ + k₃) + 1) :=
      .ifLtN_true (by rw [R.c1, R.K]; exact hK) (.seq e₁ (.seq e₂ e₃))
    set H := regHost E.li (Qof E.P).n E.N r with hHd
    have hwf : HostWF E.Q.n H := by
      obtain ⟨-, -, -, -, -, -, -, hwf⟩ := DownMath.walk_rep ((hE.ctx hK).rc hr') hE.hli
      rw [hHd]; unfold regHost; split_ifs
      · exact hwf
      · intro it hit; exact hwf it (List.mem_reverse.1 hit)
    have F₁ : Frame {bDownDrv} c c₁ k₁ := frame21_of_B
      (B := fun q => decide (q = 215000 ∨ q = 215001 ∨ q = 215002))
      (fun q h => by simp only [decide_eq_true_eq] at h; rcases h with h | h | h <;> subst h <;> rfl)
      (exec_frameB e₁ (by decide)) rr₁
    have F₃ : Frame {bDownDrv} c₂ c₃ k₃ := frame21_of_B
      (B := fun q => decide (q = 212022 ∨ q = 212021 ∨ q = 212016))
      (fun q h => by simp only [decide_eq_true_eq] at h; rcases h with h | h | h <;> subst h <;> rfl)
      (exec_frameB e₃ (by decide)) rr₃
    have F := (F₁.trans (F₂.trans F₃))
    simp only [Finset.union_self] at F
    have A₃ : c₃.nreg ALLOC = c₂.nreg ALLOC := g₃ _ (by decide) (by decide) (by decide)
    have hk₂' : k₂ ≤ κH := hk₂
    refine ⟨c₃, _, H, ex, by omega, by rw [u22, m₃]; exact hb3, by rw [← hQn]; exact hwf,
      by rw [u21]; exact hb4, by rw [u16, hb5, hQn], ?_, by rw [u22, ← A₁]; exact hb1,
      by rw [u22, A₃]; exact hb2, fun q hq1 hq2 a b d _ _ => ?_, F.mono le_rfl (by omega)⟩
    · rw [BGood.pts_pos hK, hHd]; unfold regPts; rw [hQn]
    · rw [g₃ q d b a, pk q hq1 hq2, g₁ q (by omega) (by omega) (by omega)]

end exec

end

end DrvB

end Chazelle.Core
