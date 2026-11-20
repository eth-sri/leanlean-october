module
public import Chazelle.Machine.Frames
public import Chazelle.Programs.Address
public import Chazelle.Programs.Verification

public import Chazelle.Core.SweepEvGenM

/-!
# The sweep (WP-D), stage 3: the genuineness check, RAM blocks

* `gSetL`: the inputs of the local hit (`gSet_val`);
* `gFix`: a positive height code for a vertex position, from its symbolic point (`gFix_irs`);
* `gHgt`: normalise the arrival position, then fix a vertex position (`gHgt_irs`): the position
  gets a positive height code naming its height, with the same parameter and point.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The inputs of the local hit -/

/-- The inputs of the local hit: the descriptors and the normal form of `C₁`, the arrival
position, the reverse direction, the walk length, the tag `0`, the empty accumulator. -/
def gSetL : List Instr :=
  [.copyN lMD MD₁, .copyN lCD CD₁, .copyN lNF (sw 3), .copyN lE (eA + 1), .copyN lH (eA + 2),
    .subN lD K1 oD, .copyN lN cN1, .constN lT 0, .constN accA 0]

theorem gSet_val (m f : ℕ → ℕ) :
    regB m gSetL f lMD = f MD₁ ∧ regB m gSetL f lCD = f CD₁ ∧ regB m gSetL f lNF = f (sw 3) ∧
    regB m gSetL f lE = f (eA + 1) ∧ regB m gSetL f lH = f (eA + 2) ∧
    regB m gSetL f lD = f K1 - f oD ∧ regB m gSetL f lN = f cN1 ∧ regB m gSetL f lT = 0 ∧
    regB m gSetL f accA = 0 ∧
    (∀ q, (q < 241100 ∨ 241107 < q) → q ≠ accA → regB m gSetL f q = f q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq hq' => regB_other _ _ _ (fun i hi => by
    simp only [gSetL, List.mem_cons, List.not_mem_nil, or_false] at hi
    grind [dstI, lMD, lCD, lNF, lE, lH, lD, lN, lT, sw])⟩ <;>
  · rfl

theorem gSet_ok (m f : ℕ → ℕ) (hW : 0 ≤ W) : okB W m gSetL f := by
  simp only [gSetL, okB, okI]
  exact ⟨guarded iscr_sw,
    guarded iscr_sw,
    guarded iscr_sw,
    guarded iscr_sw,
    guarded iscr_sw,
    guarded iscr_sw,
    guarded iscr_sw,
    ⟨guarded iscr_sw, hW⟩,
    ⟨guarded iscr_sw, hW⟩, trivial⟩

/-! ## A positive height code -/

/-- **The vertex fix**: the edge (`2m + 6 ↦ 6`, the other copy of the top), its symbolic point,
the height code `i + 1` (vertex `i`) or `h + 1` (a point of an edge at the height of vertex `h`). -/
def gFix : Stmt :=
  .seq (block [.addN (sw 722) lE K1])
    (.seq (.ifLtN (sw 722) cN1 (.instr (.copyN (sw 723) lE)) (.instr (.copyN (sw 723) K6)))
      (.seq (callSym CD₁ (sw 723) lH (sw 724))
        (.ifLtN (sw 724) K1 (.instr (.addN lH (sw 724 + 1) K1))
          (.instr (.addN lH (sw 724 + 2) K1)))))

/-- **A positive height code**: normalise; at a vertex, fix the code. -/
def gHgt : Stmt := .seq (normS CD₁ lE lH (sw 720)) (.ifLtN lH K1 gFix .skip)

set_option maxRecDepth 20000 in
theorem gFix_irs {C : Chain} (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W c CD₁ C)
    (hn : c.nreg cN1 = 2 * C.m + 7) {e : ℕ} (hE : c.nreg lE = e) (hH : c.nreg lH = 0)
    (h6 : 6 ≤ e) (he : e ≤ 2 * C.m + 6) (hroom : c.nreg ALLOC + 31013 ≤ W) (hPW : P.n + 1 ≤ W) :
    IRS P W c₀ gFix c 31013 (fun c' => ∃ k, c'.nreg lH = k + 1 ∧ k < P.n ∧
        ((Qof P).vtx k).2 = ((chainModel C).pos (Qof P) ⟨e, 0⟩).2 ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ lH → (r < sw 722 ∨ sw 726 < r) → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hKc := hK.fix hI
  obtain ⟨k0, k1, k6, -, -, -, -⟩ := hKc
  have hW2 : 2 * C.m + 7 ≤ W := hctx.2.2.2.2.2
  unfold gFix
  -- 1. `e + 1`
  refine IRS.seq (K₁ := 1) (K₂ := 31012)
    ((IRS.block [.addN (sw 722) lE K1] hI ⟨⟨guarded iscr_sw,
      by grind⟩, trivial⟩).mono le_rfl (fun _ h => h)) ?_
  rintro c₁ hI₁ hA₁ hA₁' hc₁
  have q22 : c₁.nreg (sw 722) = e + 1 := by
    rw [hc₁]; simp only [regB, regI, upd_same]; rw [hE, k1]
  have q1 : AgreeExcept [sw 722] c₁.nreg c.nreg := fun r hr => by
    rw [hc₁]; exact upd_other _ _ _ hr
  have qm1 : c₁.nmem = c.nmem := by simp_all
  have qN : c₁.nreg cN1 = 2 * C.m + 7 := by simp_all [cN1, sw]
  -- 2. the edge `e'`
  have hstep2 : IRS P W c₀ (.ifLtN (sw 722) cN1 (.instr (.copyN (sw 723) lE))
      (.instr (.copyN (sw 723) K6))) c₁ 3 (fun c' => ∃ e', c'.nreg (sw 723) = e' ∧ 6 ≤ e' ∧
        e' < 2 * C.m + 6 ∧ (chainModel C).pos (Qof P) ⟨e', 0⟩ = (chainModel C).pos (Qof P) ⟨e, 0⟩ ∧
        (AgreeExcept [sw 723] c'.nreg c₁.nreg) ∧ c'.nmem = c₁.nmem) := by
    refine IRS.ite (fun hlt => ?_) (fun hlt => ?_)
    · refine (IRS.instr1 hI₁ (i := .copyN (sw 723) lE) (guarded iscr_sw)).mono (by omega) ?_
      rintro c' rfl
      rw [q22, qN] at hlt
      refine ⟨e, ?_, h6, by omega, rfl, fun r hr => ?_, rfl⟩
      · simp only [regI, upd_same]
        simp_all [lE, sw]
      · exact upd_other _ _ _ hr
    · refine (IRS.instr1 hI₁ (i := .copyN (sw 723) K6) (guarded iscr_sw)).mono (by omega) ?_
      rintro c' rfl
      rw [q22, qN] at hlt
      have he' : e = 2 * C.m + 6 := by omega
      refine ⟨6, ?_, le_rfl, by have := C.one_le; omega, ?_, fun r hr => ?_, rfl⟩
      · simp only [regI, upd_same]
        simp_all [K6, sw]
      · rw [he', pos_top_copies]
      · exact upd_other _ _ _ hr
  refine IRS.seq (K₁ := 3) (K₂ := 31009) hstep2 ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨e', q23, he6, he', hpe, q2, qm2⟩
  have hH₂ : c₂.nreg lH = 0 := by
    rw [at_index q2 _, at_index q1 _]; exact hH
  have hctx₂ : ChainCtx P W c₂ CD₁ C := guarded (hctx.transport
    (by rw [q2 _ (by decide), q1 _ (by decide)])
    (fun a _ => by rw [qm2, qm1]))
  have hA₂e : c₂.nreg ALLOC = c.nreg ALLOC := by
    rw [at_index q2 _, at_index q1 _]
  -- 3. the symbolic point
  refine IRS.seq (K₁ := 31006) (K₂ := 3) (callSym_irs hI₂ hctx₂
    ⟨by decide, by decide, by decide, by decide,
      by decide, by decide⟩ ⟨by decide, by decide⟩
    (by rwa [q23]) (by rwa [q23])
    (by rw [q23, hH₂]; exact ⟨le_rfl, zero_lt_one, Nat.zero_le _⟩)
    (by rw [hH₂]; exact ⟨fun _ => rfl, fun _ => rfl⟩) (by rw [hA₂e]; omega)) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨⟨s, hs, hsl, hse⟩, q3, hA₃'', qm3⟩
  rw [q23, hH₂, hpe] at hse
  obtain ⟨hkl, hkh⟩ := symHgt hs hsl
  rw [hse] at hkh
  set k := if c₃.nreg (sw 724) = 0 then c₃.nreg (sw 724 + 1) else c₃.nreg (sw 724 + 2) with hkd
  have k1₃ := (Consts.fix hK hI₃).2.1
  -- 4. the code
  have hfin : ∀ (j : ℕ), (j = sw 724 + 1 ∨ j = sw 724 + 2) → c₃.nreg j = k →
      IRS P W c₀ (.instr (.addN lH j K1)) c₃ 1 (fun c' => ∃ k, c'.nreg lH = k + 1 ∧ k < P.n ∧
        ((Qof P).vtx k).2 = ((chainModel C).pos (Qof P) ⟨e, 0⟩).2 ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ lH → (r < sw 722 ∨ sw 726 < r) → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (AgreeBelow (c.nreg ALLOC) c'.nmem c.nmem)) := by
    intro j hj hjk
    refine (IRS.instr1 hI₃ (i := .addN lH j K1) ⟨guarded iscr_sw, by grind⟩).mono le_rfl ?_
    rintro c' rfl
    refine ⟨k, ?_, hkl, hkh, fun r hr1 hr2 hr3 hr4 => ?_, ?_, fun a ha => ?_⟩
    · frame_simp [regI, upd_same, hjk, k1₃]
    · simp only [regI]
      rw [upd_other _ _ _ hr2, q3 r hr1 (by address_omega) hr4,
        at_index q2 _, at_index q1 _]
    · block_post [regI, upd_other, hA₂e]
    · grind
  refine (IRS.ite (K := 1) (fun hlt => ?_) (fun hlt => ?_)).mono (by omega) (fun _ h => h)
  · 
    grind
  all_goals grind

set_option maxRecDepth 20000 in
/-- **A positive height code** naming the height of the arrival position, with the same
parameter and point. -/
theorem gHgt_irs {C : Chain} (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W c CD₁ C)
    (hn : c.nreg cN1 = 2 * C.m + 7) {x : WPos} (hE : c.nreg lE = x.edge)
    (hH : c.nreg lH = x.hgt) (he : x.edge < (chainModel C).W.n)
    (hpp : ProperPos (chainModel C) (Qof P) P.n x) (hcl : PosClass C (Qof P) x)
    (hy : |((chainModel C).pos (Qof P) x).2| < C.radius)
    (hroom : c.nreg ALLOC + 42030 ≤ W) (hPW : P.n + 1 ≤ W) :
    IRS P W c₀ gHgt c 42030 (fun c' => ∃ k, c'.nreg lE = x.edge ∧ c'.nreg lH = k + 1 ∧ k < P.n ∧
      ((Qof P).vtx k).2 = ((chainModel C).pos (Qof P) x).2 ∧
      (chainModel C).param (Qof P) ⟨x.edge, k + 1⟩ = (chainModel C).param (Qof P) x ∧
      (chainModel C).pos (Qof P) ⟨x.edge, k + 1⟩ = (chainModel C).pos (Qof P) x ∧
      ProperPos (chainModel C) (Qof P) P.n ⟨x.edge, k + 1⟩ ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ lH → (r < sw 720 ∨ sw 726 < r) → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hR := C.radius_pos
  unfold gHgt
  have hxw : (⟨c.nreg lE, c.nreg lH⟩ : WPos) = x := by simp_all
  -- 1. normalise
  refine IRS.seq (K₁ := 11015) (K₂ := 31015) (guarded (normS_irs hI (hK.fix hI) hctx
    ⟨by decide, by decide, by decide,
      by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩
    (by simp_all) (by simp_all) (fun _ _ _ _ => by simp_all))) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨q1E, q1H, q1, hA₁'', qm1⟩
  rw [hxw] at q1H
  set h₁ := nhgt (chainModel C) (Qof P) x with hh₁
  obtain ⟨hpp₁, hpar₁, hpos₁, hnorm₁⟩ := nhgt_facts hpp
  rw [← hh₁] at hpp₁ hpar₁ hpos₁ hnorm₁
  have k1₁ := (hK.fix hI₁).2.1
  have hE₁ := q1E.trans hE
  have keep1 : ∀ r, bandOf r ∉ oracleBands → r ≠ lH → (r < sw 720 ∨ sw 726 < r) → r ≠ ALLOC →
      c₁.nreg r = c.nreg r := fun r h1 h2 h3 h4 =>
    q1 r h1 h2 (by address_omega) (by address_omega) h4
  refine (IRS.ite (K := 31013) (fun hlt => ?_) (fun hlt => ?_)).mono (by omega) (fun _ h => h)
  · -- a vertex: fix the code
    have h0 : h₁ = 0 := by rw [k1₁, q1H] at hlt; omega
    have hpar0 : (chainModel C).param (Qof P) x = 0 := by
      rw [← hpar₁]; exact hnorm₁.1 h0
    have hposv : (chainModel C).pos (Qof P) x = (chainModel C).pos (Qof P) ⟨x.edge, 0⟩ := by
      rw [pos_eq_sidePt', pos_eq_sidePt', hpar0]; rfl
    have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
    have he6 : 6 ≤ x.edge ∧ x.edge ≤ 2 * C.m + 6 := by
      rcases hcl with h | ⟨h6, hlt⟩ | ⟨hend, -⟩
      · grind [pos_eq_sidePt', Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_one, abs_of_pos, C.sideWalk_vtx_three, abs_neg, lt_irrefl]
      · exact ⟨h6, by omega⟩
      · grind
    have hctx₁ := hctx.transport
      (keep1 CD₁ (by decide)
        (by decide) (guarded Or.inl) (by decide))
      qm1 hA₁''
    have hn₁ : c₁.nreg cN1 = 2 * C.m + 7 := by
      rw [keep1 cN1 (by decide)
        (by decide) (guarded Or.inl)
        (by decide)]; exact hn
    refine (gFix_irs hI₁ hK hctx₁ hn₁ hE₁ (by rw [q1H, h0]) he6.1 he6.2 (by omega) hPW).mono
      le_rfl ?_
    rintro c' ⟨k, hk1, hkl, hkh, hk2, hk3, hk4⟩
    rw [← hposv] at hkh
    obtain ⟨vpar, vpos⟩ := vtx_fix
      (by rwa [← hposv])
    refine ⟨k, ?_, hk1, hkl, hkh, by rw [vpar, hpar0], by rw [vpos, ← hposv],
      ⟨by rw [vpar], by grind [zero_lt_one], by grind⟩,
      fun r h1 h2 h3 h4 => ?_, le_trans hA₁'' hk3, fun a ha => ?_⟩
    · block_post
    · grind [sw]
    all_goals grind
  · -- inside an edge: the code is positive
    have hpos0 : h₁ ≠ 0 := by rw [k1₁, q1H] at hlt; omega
    obtain ⟨k, hk⟩ : ∃ k, h₁ = k + 1 := ⟨h₁ - 1, by omega⟩
    have hparne := fun h =>
      hpos0 (hnorm₁.2 h)
    have hkh := hgt_of_pos (Q := Qof P) (x := ⟨x.edge, h₁⟩) hk hparne
    rw [hpos₁] at hkh
    refine IRS.skip hI₁ ⟨k, hE₁, by rw [q1H, hk], by
      have := hpp₁.2.2; simp only at this; omega, hkh, by rwa [← hk],
      by rwa [← hk], by rwa [← hk], keep1, hA₁'', qm1⟩

end

end SweepEv

end Chazelle.Core
