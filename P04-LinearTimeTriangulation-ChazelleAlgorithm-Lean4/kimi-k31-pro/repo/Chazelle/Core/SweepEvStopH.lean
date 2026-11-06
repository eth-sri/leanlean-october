module

public import Chazelle.Core.SweepEvStopM3
public import Chazelle.Core.SweepEvGenM
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
set_option maxRecDepth 20000

/-!
# The sweep (WP-D), stage 2: a positive height code for a walk position (RAM)

`hHgt dsc nr` (after the generator's (`SweepEvGen`) `gHgt`, for any chain descriptor register `dsc` and walk-length
register `nr`): normalise the position `(lE, lH)` and give a vertex position a positive height
code naming its height (`hHgt_irs`), as the local hit needs (`LHGeo`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- The registers allowed as descriptor or length registers: fixed, or of stage 2. -/
def DR (r : ℕ) : Prop := (240000 ≤ r ∧ r < 240700) ∨ (244000 ≤ r ∧ r < 246000)

/-! ## A positive height code -/

/-- **The vertex fix**: the edge (`2m + 6 ↦ 6`, the other copy of the top), its symbolic point,
the height code `i + 1` (vertex `i`) or `h + 1` (a point of an edge at the height of vertex `h`). -/
def hFix (dsc nr : ℕ) : Stmt :=
  .seq (block [.addN (sw 722) lE K1])
    (.seq (.ifLtN (sw 722) nr (.instr (.copyN (sw 723) lE)) (.instr (.copyN (sw 723) K6)))
      (.seq (callSym dsc (sw 723) lH (sw 724))
        (.ifLtN (sw 724) K1 (.instr (.addN lH (sw 724 + 1) K1))
          (.instr (.addN lH (sw 724 + 2) K1)))))

/-- **A positive height code**: normalise; at a vertex, fix the code. -/
def hHgt (dsc nr : ℕ) : Stmt := .seq (normS dsc lE lH (sw 720)) (.ifLtN lH K1 (hFix dsc nr) .skip)

theorem hFix_irs {dsc nr : ℕ} (hdr : DR dsc) (hnr : DR nr) {C : Chain} (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W c dsc C)
    (hn : c.nreg nr = 2 * C.m + 7) {e : ℕ} (hE : c.nreg lE = e) (hH : c.nreg lH = 0)
    (h6 : 6 ≤ e) (he : e ≤ 2 * C.m + 6) (hroom : c.nreg ALLOC + 31013 ≤ W) (hPW : P.n + 1 ≤ W) :
    IRS P W c₀ (hFix dsc nr) c 31013 (fun c' => ∃ k, c'.nreg lH = k + 1 ∧ k < P.n ∧
        ((Qof P).vtx k).2 = ((chainModel C).pos (Qof P) ⟨e, 0⟩).2 ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ lH → (r < sw 722 ∨ sw 726 < r) → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hKc := hK.fix hI
  obtain ⟨k0, k1, k6, -, -, -, -⟩ := hKc
  have hW2 : 2 * C.m + 7 ≤ W := hctx.2.2.2.2.2
  unfold hFix
  -- 1. `e + 1`
  refine IRS.seq (K₁ := 1) (K₂ := 31012)
    ((IRS.block [.addN (sw 722) lE K1] hI ⟨⟨iscr_sw (by ufo sw) (by ufo sw),
      by rwo [hE, k1]⟩, trivial⟩).mono le_rfl (fun _ => id)) ?_
  rintro c₁ hI₁ hA₁ hA₁' hc₁
  have q22 : c₁.nreg (sw 722) = e + 1 := by
    rw [hc₁]; simp only [regB, regI, upd_same]; rw [hE, k1]
  have q1 : ∀ r, r ≠ sw 722 → c₁.nreg r = c.nreg r := fun r hr => by
    rw [hc₁]; simp only [regB, regI]; exact upd_other _ _ _ hr
  have qm1 : c₁.nmem = c.nmem := by rw [hc₁]
  have qN : c₁.nreg nr = 2 * C.m + 7 := by rwx [q1 _ (by unfold DR at hnr; (try ufo sw))]
  -- 2. the edge `e'`
  have hstep2 : IRS P W c₀ (.ifLtN (sw 722) nr (.instr (.copyN (sw 723) lE))
      (.instr (.copyN (sw 723) K6))) c₁ 3 (fun c' => ∃ e', c'.nreg (sw 723) = e' ∧ 6 ≤ e' ∧
        e' < 2 * C.m + 6 ∧ (chainModel C).pos (Qof P) ⟨e', 0⟩ = (chainModel C).pos (Qof P) ⟨e, 0⟩ ∧
        (∀ r, r ≠ sw 723 → c'.nreg r = c₁.nreg r) ∧ c'.nmem = c₁.nmem) := by
    refine IRS.ite (fun hlt => ?_) (fun hlt => ?_)
    · refine (IRS.instr1 hI₁ (i := .copyN (sw 723) lE) (iscr_sw (by ufo sw)
        (by ufo sw))).mono (by omega) ?_
      rintro c' rfl
      rw [q22, qN] at hlt
      refine ⟨e, ?_, h6, by omega, rfl, fun r hr => ?_, rfl⟩
      · simp only [regI, upd_same]
        rwx [q1 _ (by ufo lE sw)]
      · simp only [regI]; exact upd_other _ _ _ hr
    · refine (IRS.instr1 hI₁ (i := .copyN (sw 723) K6) (iscr_sw (by ufo sw)
        (by ufo sw))).mono (by omega) ?_
      rintro c' rfl
      rw [q22, qN] at hlt
      have he' : e = 2 * C.m + 6 := by omega
      refine ⟨6, ?_, le_rfl, by have := C.one_le; omega, ?_, fun r hr => ?_, rfl⟩
      · simp only [regI, upd_same]
        rwx [q1 _ (by ufo K6 sw)]
      · rw [he', pos_top_copies]
      · simp only [regI]; exact upd_other _ _ _ hr
  refine IRS.seq (K₁ := 3) (K₂ := 31009) hstep2 ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨e', q23, he6, he', hpe, q2, qm2⟩
  have hH₂ : c₂.nreg lH = 0 := by
    rwx [q2 _ (by ufo lH sw), q1 _ (by ufo lH sw)]
  have hctx₂ : ChainCtx P W c₂ dsc C := hctx.transport
    (by rw [q2 _ (by unfold DR at hdr; (try ufo sw)), q1 _ (by unfold DR at hdr; (try ufo sw))])
    (fun a _ => by rw [qm2, qm1]) (by rw [q2 _ (by ufo ALLOC sw), q1 _ (by ufo ALLOC sw)])
  have hA₂e : c₂.nreg ALLOC = c.nreg ALLOC := by
    rw [q2 _ (by ufo ALLOC sw), q1 _ (by ufo ALLOC sw)]
  -- 3. the symbolic point
  refine IRS.seq (K₁ := 31006) (K₂ := 3) (callSym_irs (o := sw 724) hI₂ hctx₂
    ⟨by ufo DR at hdr, by ufo DR at hdr, by ufo sw, by ufo sw,
      by ufo lH sw, by ufo lH sw⟩ ⟨by ufo sw, by ufo sw⟩
    (by rwx [q23]) (by rwx [q23])
    (by rw [q23, hH₂]; exact ⟨le_rfl, zero_lt_one, Nat.zero_le _⟩)
    (by rw [hH₂]; exact ⟨fun _ => rfl, fun _ => rfl⟩) (by rwo [hA₂e])) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨⟨s, hs, hsl, hse⟩, q3, hA₃'', qm3⟩
  rw [q23, hH₂, hpe] at hse
  obtain ⟨hkl, hkh⟩ := symHgt (P := P) hs hsl
  rw [hse] at hkh
  set k := if c₃.nreg (sw 724) = 0 then c₃.nreg (sw 724 + 1) else c₃.nreg (sw 724 + 2) with hkd
  have k1₃ : c₃.nreg K1 = 1 := (Consts.fix hK hI₃).2.1
  -- 4. the code
  have hfin : ∀ (j : ℕ), (j = sw 724 + 1 ∨ j = sw 724 + 2) → c₃.nreg j = k →
      IRS P W c₀ (.instr (.addN lH j K1)) c₃ 1 (fun c' => ∃ k, c'.nreg lH = k + 1 ∧ k < P.n ∧
        ((Qof P).vtx k).2 = ((chainModel C).pos (Qof P) ⟨e, 0⟩).2 ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ lH → (r < sw 722 ∨ sw 726 < r) → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
    intro j hj hjk
    refine (IRS.instr1 hI₃ (i := .addN lH j K1) ⟨iscr_sw (by ufo lH sw)
      (by ufo lH sw), by rwo [hjk, k1₃]⟩).mono le_rfl ?_
    rintro c' rfl
    refine ⟨k, ?_, hkl, hkh, fun r hr1 hr2 hr3 hr4 => ?_, ?_, fun a ha => ?_⟩
    · simp only [regI, upd_same]; rw [hjk, k1₃]
    · simp only [regI]
      rw [upd_other _ _ _ hr2, q3 r hr1 (by ufo sw at hr3 ⊢) hr4,
        q2 _ (by ufo sw at hr3 ⊢), q1 _ (by ufo sw at hr3 ⊢)]
    · simp only [regI]
      rw [upd_other _ _ _ (show ALLOC ≠ lH by ufo lH ALLOC sw)]
      rwx [← hA₂e]
    · simp only
      rw [qm3 a (by rwx [hA₂e]), qm2, qm1]
  refine (IRS.ite (K := 1) (fun hlt => ?_) (fun hlt => ?_)).mono (by omega) (fun _ => id)
  · have h0 : c₃.nreg (sw 724) = 0 := by rwo [k1₃] at hlt
    exact hfin (sw 724 + 1) (Or.inl rfl) (by rw [hkd, ite_eq_left h0])
  · have h0 : c₃.nreg (sw 724) ≠ 0 := by rwo [k1₃] at hlt
    exact hfin (sw 724 + 2) (Or.inr rfl) (by rw [hkd, ite_eq_right h0])

/-- **A positive height code** naming the height of the arrival position, with the same
parameter and point. -/
theorem hHgt_irs {dsc nr : ℕ} (hdr : DR dsc) (hnr : DR nr) {C : Chain} (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W c dsc C)
    (hn : c.nreg nr = 2 * C.m + 7) {x : WPos} (hE : c.nreg lE = x.edge)
    (hH : c.nreg lH = x.hgt) (he : x.edge < (chainModel C).W.n)
    (hpp : ProperPos (chainModel C) (Qof P) P.n x) (hcl : PosClass C (Qof P) x)
    (hy : |((chainModel C).pos (Qof P) x).2| < C.radius)
    (hroom : c.nreg ALLOC + 42030 ≤ W) (hPW : P.n + 1 ≤ W) :
    IRS P W c₀ (hHgt dsc nr) c 42030 (fun c' => ∃ k, c'.nreg lE = x.edge ∧ c'.nreg lH = k + 1 ∧ k < P.n ∧
      ((Qof P).vtx k).2 = ((chainModel C).pos (Qof P) x).2 ∧
      (chainModel C).param (Qof P) ⟨x.edge, k + 1⟩ = (chainModel C).param (Qof P) x ∧
      (chainModel C).pos (Qof P) ⟨x.edge, k + 1⟩ = (chainModel C).pos (Qof P) x ∧
      ProperPos (chainModel C) (Qof P) P.n ⟨x.edge, k + 1⟩ ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ lH → (r < sw 720 ∨ sw 726 < r) → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hKc := hK.fix hI
  have hR := C.radius_pos
  unfold hHgt
  have hxw : (⟨c.nreg lE, c.nreg lH⟩ : WPos) = x := by rw [hE, hH]
  -- 1. normalise
  refine IRS.seq (K₁ := 11015) (K₂ := 31015) (normS_irs hI hKc hctx
    ⟨by ufo DR at hdr, by ufo DR at hdr, by ufo lE sw,
      by ufo lE sw, by ufo lH sw, by ufo lH sw⟩
    ⟨by ufo sw, by ufo sw, by ufo lE sw, by ufo lH sw,
      by ufo lE sw, by ufo lH sw, by ufo lE lH sw⟩
    (by rwx [hE]) (by rwx [hxw]) (fun _ _ _ _ => by rwx [hxw])
    (by omega)) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨q1E, q1H, q1, hA₁'', qm1⟩
  rw [hxw] at q1H
  set h₁ := nhgt (chainModel C) (Qof P) x with hh₁
  obtain ⟨hpp₁, hpar₁, hpos₁, hnorm₁⟩ := nhgt_facts (u := x) hpp
  rw [← hh₁] at hpp₁ hpar₁ hpos₁ hnorm₁
  have hK₁ := hK.fix hI₁
  have k1₁ : c₁.nreg K1 = 1 := hK₁.2.1
  have hE₁ : c₁.nreg lE = x.edge := q1E.trans hE
  have keep1 : ∀ r, bandOf r ∉ oracleBands → r ≠ lH → (r < sw 720 ∨ sw 726 < r) → r ≠ ALLOC →
      c₁.nreg r = c.nreg r := fun r h1 h2 h3 h4 =>
    q1 r h1 h2 (by ufo sw at h3 ⊢) (by ufo sw at h3 ⊢) h4
  refine (IRS.ite (K := 31013) (fun hlt => ?_) (fun hlt => ?_)).mono (by omega) (fun _ => id)
  · -- a vertex: fix the code
    have h0 : h₁ = 0 := by rwo [k1₁, q1H] at hlt
    have hpar0 : (chainModel C).param (Qof P) x = 0 := by
      rw [← hpar₁]; exact hnorm₁.1 h0
    have hposv : (chainModel C).pos (Qof P) x = (chainModel C).pos (Qof P) ⟨x.edge, 0⟩ := by
      rwr [pos_eq_sidePt', pos_eq_sidePt', hpar0]
    have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
    have he6 : 6 ≤ x.edge ∧ x.edge ≤ 2 * C.m + 6 := by
      rcases hcl with h | ⟨h6, hlt⟩ | ⟨hend, -⟩
      · exfalso
        rw [hposv, pos_eq_sidePt'] at hy
        simp only [show (chainModel C).param (Qof P) ⟨x.edge, 0⟩ = 0 from rfl,
          Chazelle.Chain.sidePt_zero, hW] at hy
        rcases h with h | h <;> rw [h] at hy
        · rw [C.sideWalk_vtx_one] at hy; simp only at hy; rw [abs_of_pos hR] at hy
          exact lt_irrefl _ hy
        · rw [C.sideWalk_vtx_three] at hy; simp only at hy; rw [abs_neg, abs_of_pos hR] at hy
          exact lt_irrefl _ hy
      · exact ⟨h6, by omega⟩
      · exact ⟨by omega, by omega⟩
    have hctx₁ : ChainCtx P W c₁ dsc C := hctx.transport
      (keep1 dsc (by exact not_oracle_sw (by ufo DR at hdr) (by ufo DR at hdr))
        (by unfold DR at hdr; ufo lH sw) (by unfold DR at hdr; (try ufo sw)) (by unfold DR at hdr; ufo ALLOC))
      qm1 hA₁''
    have hn₁ : c₁.nreg nr = 2 * C.m + 7 := by
      rw [keep1 nr (by exact not_oracle_sw (by ufo DR at hnr) (by ufo DR at hnr))
        (by unfold DR at hnr; ufo lH sw) (by unfold DR at hnr; (try ufo sw))
        (by unfold DR at hnr; ufo ALLOC)]; exact hn
    refine (hFix_irs hdr hnr hI₁ hK hctx₁ hn₁ hE₁ (by rw [q1H, h0]) he6.1 he6.2 (by omega) hPW).mono
      le_rfl ?_
    rintro c' ⟨k, hk1, hkl, hkh, hk2, hk3, hk4⟩
    rw [← hposv] at hkh
    obtain ⟨vpar, vpos⟩ := vtx_fix (M := chainModel C) (Q := Qof P) (e := x.edge) (h' := k)
      (by rwx [← hposv])
    refine ⟨k, ?_, hk1, hkl, hkh, by rw [vpar, hpar0], by rw [vpos, ← hposv],
      ⟨by rw [vpar], by rw [vpar]; exact zero_lt_one, by show k + 1 ≤ P.n; omega⟩,
      fun r h1 h2 h3 h4 => ?_, le_trans hA₁'' hk3, fun a ha => ?_⟩
    · rw [hk2 lE (by unfold lE sw; exact not_oracle_sw (by omega) (by omega))
        (by ufo lE lH sw) (Or.inr (by ufo lE sw)) (by ufo lE ALLOC sw)]
      exact hE₁
    · rw [hk2 r h1 h2 (by ufo sw at h3 ⊢) h4]
      exact keep1 r h1 h2 h3 h4
    · rw [hk4 a (lt_of_lt_of_le ha hA₁''), qm1 a ha]
  · -- inside an edge: the code is positive
    have hpos0 : h₁ ≠ 0 := by rwo [k1₁, q1H] at hlt
    obtain ⟨k, hk⟩ : ∃ k, h₁ = k + 1 := ⟨h₁ - 1, by omega⟩
    have hparne : (chainModel C).param (Qof P) ⟨x.edge, h₁⟩ ≠ 0 := fun h =>
      hpos0 (hnorm₁.2 h)
    have hkh := hgt_of_pos (M := chainModel C) (Q := Qof P) (x := ⟨x.edge, h₁⟩) (h := k) hk hparne
    rw [hpos₁] at hkh
    refine IRS.skip hI₁ ⟨k, hE₁, by rw [q1H, hk], by
      have := hpp₁.2.2; sio only at this, hkh, by rwx [← hk],
      by rwx [← hk], by rwx [← hk], keep1, hA₁'', qm1⟩

end

end SweepEv

end Chazelle.Core
