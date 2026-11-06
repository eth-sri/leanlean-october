module

public import Chazelle.Core.SweepEvFace2

/-!
# The sweep (WP-D), stages 2–3: the region faced at a walk vertex of `C₂` (task D1, RAM part 2)

`face`: the prefix `faceLoc` (spine answer `j`, the regions of the arcs at `j - 1`, `j`, `j + 1`,
the ends of the arc at `j`), the normalisation of both ends (`normS`), and the selection
`faceSel`: `fR := ` the region of the arc at `j`, replaced (before, `fA = 0`) by the region of the
arc at `j - 1` when the arc at `j` starts at the vertex `(fE, 0)`, or (after, `fA = 1`) by the
region of the arc at `j + 1` when it ends there (`face_before_eq`, `face_after_eq`, …).

**`faceTask : FaceTask`**, cost `30000 (TLR + 1)`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sideInArc)
open OracleQ (sj sk ek succP predP)

@[expose] public section

/-! ## The selection -/

/-- `fR := src` if the position `(xe, xh)` (normalised) is the vertex `(fE, 0)`. -/
def faceChk (xe xh src : ℕ) : Stmt :=
  .ifLtN xe fE .skip (.ifLtN fE xe .skip (.ifLtN K0 xh .skip (block [.copyN fR src])))

/-- The selection of the answer. -/
def faceSel : Stmt :=
  .seq (block [.copyN fR lR1]) (.ifLtN fA K1 (faceChk fSE fSH lR0) (faceChk fEE fEH lR2))

/-- **The procedure `face`.** -/
def face : Stmt :=
  .seq faceLoc (.seq (normS (sw 21) fSE fSH fO) (.seq (normS (sw 21) fEE fEH fO) faceSel))

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem iscr_fR : IScr fR := iscr_sw (by unfold fR sw; norm_num) (by unfold fR sw; norm_num)

theorem faceChk_irs {xe xh src : ℕ} (hI : IInv W c₀ c) (hk0 : c.nreg K0 = 0) :
    IRS P W c₀ (faceChk xe xh src) c 7 (fun c' =>
      c'.nreg fR = (if c.nreg xe = c.nreg fE ∧ c.nreg xh = 0 then c.nreg src else c.nreg fR) ∧
      (∀ r, r ≠ fR → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  unfold faceChk
  by_cases h1 : c.nreg xe < c.nreg fE
  · refine (IRS.ifT h1 (IRS.skip (K := 0) hI ⟨?_, fun _ _ => rfl, rfl⟩)).mono (by omega)
      (fun _ h => h)
    rw [ite_eq_right (by omega)]
  by_cases h2 : c.nreg fE < c.nreg xe
  · refine (IRS.ifF h1 (IRS.ifT h2 (IRS.skip (K := 0) hI ⟨?_, fun _ _ => rfl, rfl⟩))).mono
      (by omega) (fun _ h => h)
    rw [ite_eq_right (by omega)]
  by_cases h3 : c.nreg K0 < c.nreg xh
  · refine (IRS.ifF h1 (IRS.ifF h2 (IRS.ifT h3 (IRS.skip (K := 0) hI ⟨?_, fun _ _ => rfl, rfl⟩))))
      |>.mono (by omega) (fun _ h => h)
    rw [ite_eq_right (by omega)]
  · refine (IRS.ifF h1 (IRS.ifF h2 (IRS.ifF h3 (IRS.block [.copyN fR src] hI
      ⟨iscr_fR, trivial⟩)))).mono (by simp) ?_
    rintro c' rfl
    refine ⟨?_, fun r hr => ?_, rfl⟩
    · simp only [regB, regI, upd, ite_true]
      rw [ite_eq_left ⟨by omega, by omega⟩]
    · simp only [regB, regI, upd, ite_eq_right hr]

theorem faceSel_irs (hI : IInv W c₀ c) (hk0 : c.nreg K0 = 0) :
    IRS P W c₀ faceSel c 10 (fun c' =>
      c'.nreg fR = (if c.nreg fA < c.nreg K1 then
          (if c.nreg fSE = c.nreg fE ∧ c.nreg fSH = 0 then c.nreg lR0 else c.nreg lR1)
        else (if c.nreg fEE = c.nreg fE ∧ c.nreg fEH = 0 then c.nreg lR2 else c.nreg lR1)) ∧
      (∀ r, r ≠ fR → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  unfold faceSel
  refine (IRS.seq (IRS.block [.copyN fR lR1] hI ⟨iscr_fR, trivial⟩) ?_).mono (K := 1 + (7 + 2))
    (by norm_num) (fun _ h => h)
  rintro c₁ hI₁ - - hc1
  have v1 : c₁.nreg fR = c.nreg lR1 := by
    rw [hc1]; simp only [regB, regI, upd, ite_true]
  have o1 : ∀ r, r ≠ fR → c₁.nreg r = c.nreg r := by
    intro r hr; rw [hc1]; simp only [regB, regI, upd, ite_eq_right hr]
  have hm1 : c₁.nmem = c.nmem := by rw [hc1]
  have n : ∀ q, (q = fA ∨ q = K1 ∨ q = K0 ∨ q = fSE ∨ q = fSH ∨ q = fEE ∨ q = fEH ∨ q = fE ∨
      q = lR0 ∨ q = lR1 ∨ q = lR2) → c₁.nreg q = c.nreg q := by
    intro q hq
    apply o1
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [fR, fA, K1, K0, fSE, fSH, fEE, fEH, fE, lR0, lR1, lR2, sw]
  have hk0' : c₁.nreg K0 = 0 := by rwa [n K0 (by simp)]
  by_cases hA : c₁.nreg fA < c₁.nreg K1
  · refine (IRS.ifT hA (faceChk_irs hI₁ hk0')).mono le_rfl ?_
    rintro c' ⟨h1, h2, h3⟩
    rw [n fA (by simp), n K1 (by simp)] at hA
    refine ⟨?_, fun r hr => (h2 r hr).trans (o1 r hr), h3.trans hm1⟩
    rw [h1, ite_eq_left hA, v1, n fSE (by simp), n fSH (by simp), n fE (by simp), n lR0 (by simp)]
  · refine (IRS.ifF hA (faceChk_irs hI₁ hk0')).mono le_rfl ?_
    rintro c' ⟨h1, h2, h3⟩
    rw [n fA (by simp), n K1 (by simp)] at hA
    refine ⟨?_, fun r hr => (h2 r hr).trans (o1 r hr), h3.trans hm1⟩
    rw [h1, ite_eq_right hA, v1, n fEE (by simp), n fEH (by simp), n fE (by simp), n lR2 (by simp)]

/-! ## The task -/

set_option maxRecDepth 20000 in
theorem face_cost (L : ℕ) : faceLocK L + (11015 + (11015 + 10)) ≤ 30000 * (L + 1) := by
  unfold faceLocK; omega

set_option maxRecDepth 20000 in
theorem face_room1 {a L W : ℕ} (h : a + 30000 * (L + 1) ≤ W) : a + faceLocK L ≤ W := by
  unfold faceLocK; omega

set_option maxRecDepth 20000 in
theorem face_room2 {a L W : ℕ} (h : a + 30000 * (L + 1) ≤ W) : a + 11015 ≤ W := by
  have h1 : 30000 ≤ 30000 * (L + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos L)
  generalize 30000 * (L + 1) = X at h h1
  omega

set_option maxRecDepth 20000 in
theorem face_room3 {a b L W : ℕ} (h : a + 30000 * (L + 1) ≤ W) (hb : b ≤ a + 11015) :
    b + 11015 ≤ W := by
  have h1 : 30000 ≤ 30000 * (L + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos L)
  generalize 30000 * (L + 1) = X at h h1
  omega

end

end SweepEv

end Chazelle.Core
