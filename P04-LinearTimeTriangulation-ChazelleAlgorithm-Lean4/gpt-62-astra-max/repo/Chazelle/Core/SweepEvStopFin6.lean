module
public import Chazelle.Core.ModelAccess
public import Chazelle.Cost.Invariant
public import Chazelle.Machine.Frames
public import Chazelle.Programs.Address
public import Chazelle.Programs.Evidence
public import Chazelle.Programs.RegisterProof
public import Chazelle.Programs.Verification

public import Chazelle.Core.SweepEvStopFin5

/-!
# The sweep (WP-D), stage 2, the finish of a stop origin: the labels (RAM)

`slfLabS sl`: the label count `slfN` and the labels `slfL0, slfL1` of the stop chord: none unless
it is anchored (`slfA`) and not a pocket (bits `slfO + 3`, `slfO + 7`); then the regions above and
below its parent (`slfLdL`, read from the normal form), else the regions faced at the counterpart
of its stretch attachment (`slfStr`, the stretch labels `sl` of `StrLabTask`).  Post `SlfLabOK`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Chain (SideAttach sidePt)

@[expose] public section

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

def slfP : ℕ := sw 4101
def slfY : ℕ := sw 4102

def slfLdL : List Instr :=
  [.subN slfP oPar K1, .addN slfY (sw 4) K3, .loadN slfY slfY, .addN slfY slfY slfP,
    .addN slfY slfY slfP, .addN slfY slfY slfP, .addN slfY slfY slfP, .addN slfY slfY slfP,
    .addN slfY slfY K3, .loadN slfL0 slfY, .addN slfY slfY K1, .loadN slfL1 slfY,
    .constN slfN 2]

theorem slfLdL_val (m f : ℕ → ℕ) (hk1 : f K1 = 1) (hk3 : f K3 = 3) :
    regB m slfLdL f slfL0 = m (m (f (sw 4) + 3) + 5 * (f oPar - 1) + 3) ∧
    regB m slfLdL f slfL1 = m (m (f (sw 4) + 3) + 5 * (f oPar - 1) + 4) ∧
    regB m slfLdL f slfN = 2 ∧
    ∀ q, q ≠ slfP → q ≠ slfY → q ≠ slfL0 → q ≠ slfL1 → q ≠ slfN → regB m slfLdL f q = f q := by
  have e1 : f 240611 = 1 := hk1
  have e3 : f 240616 = 3 := hk3
  refine ⟨?_, ?_, ?_, fun q h1 h2 h3 h4 h5 => ?_⟩
  · simp only [slfLdL, regB, regI, upd, slfP, slfY, slfL0, slfL1, slfN, oPar, K1, K3, sw]
    grind
  · simp only [slfLdL, regB, regI, upd, slfP, slfY, slfL0, slfL1, slfN, oPar, K1, K3, sw]
    grind
  · block_post
  · exact regB_other m slfLdL f (fun i hi => by
      simp only [slfLdL, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [dstI] <;> intro he <;> subst he <;> simp_all)

theorem slfLdL_ok {W : ℕ} (m f : ℕ → ℕ) (hk1 : f K1 = 1) (hk3 : f K3 = 3) (hb : f (sw 4) + 3 ≤ W)
    (_hp : 0 < f oPar)
    (hb2 : m (f (sw 4) + 3) + 5 * (f oPar - 1) + 4 ≤ W) (hW : 2 ≤ W) :
    okB W m slfLdL f := by
  register_block


/-- The registers of the label step. -/
def slfLabR (r : ℕ) : Prop :=
  r = slfN ∨ r = slfL0 ∨ r = slfL1 ∨ r = slfP ∨ r = slfY ∨ StrR r

/-- The pick of the stretch attachment. -/
def slfPick : Stmt :=
  .ifLtN K0 slfO (block [.copyN slfSE (oF0 + 1), .copyN slfSH (oF0 + 2)])
    (block [.copyN slfSE (a1F + 1), .copyN slfSH (a1F + 2)])

/-- The labels faced at the counterpart of the stretch attachment. -/
def slfStr (sl : Stmt) : Stmt :=
  .seq slfPick (.seq sl (block [.copyN slfL0 frA, .copyN slfL1 frB, .constN slfN 2]))

/-- **The label step.** -/
def slfLabS (sl : Stmt) : Stmt :=
  .seq (.instr (.constN slfN 0))
    (.ifLtN K0 slfA (.ifLtN K0 (slfO + 3) (.ifLtN K0 (slfO + 7)
      (.ifLtN K0 oPar (block slfLdL) (slfStr sl)) .skip) .skip) .skip)

/-- The contract body of the stretch labels (`StrLabTask`). -/
def StrLabSpec (sl : Stmt) (κ : ℕ → ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      c.nreg slfSE < (chainModel J.whole).W.n →
      ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg slfSE, c.nreg slfSH⟩ →
      |((chainModel J.whole).pos (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩).2| < J.whole.radius →
      (∃ e, e ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P)) ∧
        (∀ c ∈ N₂.F (chainModel J.right) (Qof P), ¬ e ⊆ c) ∧
        SideAttach (chainModel J.whole).W e (c.nreg slfSE)
          ((chainModel J.whole).param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩)) →
      0 < oW J (c.nreg slfSE + (chainModel J.whole).param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩) →
      oW J (c.nreg slfSE + (chainModel J.whole).param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩) < Lst J →
      c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ sl c (κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1)) (fun c' =>
        c'.nreg frA < N₂.nRegions ∧ c'.nreg frB < N₂.nRegions ∧
        (∃ d, d < Lst J ∧
          ((chainModel J.whole).param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩ = 0 → d ≠ 0) ∧
          c.nreg slfSE = (gW J + d) % (chainModel J.whole).W.n ∧
          AfterFaces (chainModel J.right) (cpA J d)
            ((chainModel J.whole).param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩)
            (regOf (chainModel J.right) (Qof P) N₂ (c'.nreg frA)) ∧
          (0 < (chainModel J.whole).param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩ →
            BeforeFaces (chainModel J.right) (cpA J d)
              ((chainModel J.whole).param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩)
              (regOf (chainModel J.right) (Qof P) N₂ (c'.nreg frB))) ∧
          ((chainModel J.whole).param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩ = 0 →
            BeforeFaces (chainModel J.right) (cpB J d) 0
              (regOf (chainModel J.right) (Qof P) N₂ (c'.nreg frB)))) ∧
        (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
        (∀ r, bandOf r ∉ oracleBands → ¬ StrR r → r ≠ ALLOC → c'.nreg r = c.nreg r))

theorem strLabSpec_of (h : StrLabTask) : ∃ sl κ, StrLabSpec sl κ := h

/-- The frame of a block. -/
theorem slfFr_block {R : ℕ → Prop} (l : List Instr) (c : Config) (hR : ∀ i ∈ l, R (dstI i))
    (hA : ∀ i ∈ l, dstI i ≠ ALLOC) :
    SlfFr R c { c with nreg := regB c.nmem l c.nreg } :=
  ⟨fun _r _ hr _ => regB_other _ _ _ (fun i hi h => hr (h ▸ hR i hi)),
    (regB_other _ _ _ hA).ge, fun _ _ => rfl⟩

/-- A stop attachment usable as the stretch attachment. -/
def SlfAtt (P : Polygon) (J : Merge.Junction) (e : Set Point) (c : Config) (pe ph : ℕ) : Prop :=
  SlfPos P J c pe ph ∧
    |((chainModel J.whole).pos (Qof P) ⟨c.nreg pe, c.nreg ph⟩).2| < J.whole.radius ∧
    SideAttach (chainModel J.whole).W e (c.nreg pe)
      ((chainModel J.whole).param (Qof P) ⟨c.nreg pe, c.nreg ph⟩)

/-- The facts of the label step. -/
def SlfLabOK (P : Polygon) (J : Merge.Junction) (N₂ : NF) (e : Set Point) (anc nl l₀ l₁ : ℕ) :
    Prop :=
  nl ≤ 2 ∧ (0 < nl → l₀ < N₂.nRegions) ∧ (1 < nl → l₁ < N₂.nRegions) ∧
    (anc = 1 → (∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s → oW J (q + s) ≠ 0) →
      (∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s ∧ (Lst J : ℝ) ≤ oW J (q + s)) →
      EvSideLab J (N₂.F (chainModel J.right) (Qof P)) (labSet J (Qof P) N₂ nl l₀ l₁ 0 0) e)

theorem slfCopy2_irs (hI : IInv W c₀ c) {r₁ a₁ r₂ a₂ : ℕ}
    (h₁ : 240700 ≤ r₁ ∧ r₁ < 250000) (h₂ : 240700 ≤ r₂ ∧ r₂ < 250000) (hne : r₁ ≠ r₂)
    (ha : a₂ ≠ r₁) :
    IRS P W c₀ (block [.copyN r₁ a₁, .copyN r₂ a₂]) c 2 (fun c' => c'.nreg r₁ = c.nreg a₁ ∧
      c'.nreg r₂ = c.nreg a₂ ∧ (∀ q, q ≠ r₁ → q ≠ r₂ → c'.nreg q = c.nreg q) ∧
      c'.nmem = c.nmem ∧ c'.nreg ALLOC = c.nreg ALLOC) := by
  refine (IRS.block [.copyN r₁ a₁, .copyN r₂ a₂] hI
    ⟨iscr_sw h₁.1 h₁.2, iscr_sw h₂.1 h₂.2, trivial⟩).mono le_rfl ?_
  invariant_facts; block_post [regB, regI, upd_other, ALLOC]

theorem SlfAtt.congr {e : Set Point} {pe ph : ℕ} {c c' : Config} (h : SlfAtt P J e c pe ph)
    (he : c'.nreg pe = c.nreg pe) (hh : c'.nreg ph = c.nreg ph) : SlfAtt P J e c' pe ph := by
  simp_all [SlfAtt, SlfPos]

theorem slfOff_nonneg {e h : ℕ} (hp : SlfPos P J c e h) : 0 ≤ slfOff P J c e h := by
  have hgn : gW J < J.whole.chainModel.W.n := by
    unfold gW; rw [cm_n]; have := tpos_lt J.whole J.m₁; omega
  exact off_nonneg (by have := hp.2.1.1; positivity) (by exact_mod_cast hgn)

set_option maxHeartbeats 8000000 in
/-- **The labels faced at the counterpart of the stretch attachment.** -/
theorem slfStr_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {sl : Stmt}
    {κ : ℕ → ℕ} (hsl : StrLabSpec sl κ) {kind k b : ℕ} (hD : OrgD P J N₂ kind k b)
    (hat₀ : SlfAtt P J (stopSet J (Qof P) N₂ kind k b) c (oF0 + 1) (oF0 + 2))
    (hat₁ : SlfAtt P J (stopSet J (Qof P) N₂ kind k b) c (a1F + 1) (a1F + 2))
    (b0 : BitIs c slfO (slfOff P J c (oF0 + 1) (oF0 + 2) < Lst J))
    (hanc : slfOff P J c (oF0 + 1) (oF0 + 2) < Lst J ∨ slfOff P J c (a1F + 1) (a1F + 2) < Lst J)
    (h0₀ : 0 < slfOff P J c (oF0 + 1) (oF0 + 2)) (h0₁ : 0 < slfOff P J c (a1F + 1) (a1F + 2))
    (hnopar : ∀ cc ∈ N₂.F (chainModel J.right) (Qof P), ¬ stopSet J (Qof P) N₂ kind k b ⊆ cc)
    (hroom : c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) + 4 ≤ W) :
    IRS P W c₀ (slfStr sl) c (4 + (κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) + 3)) (fun c' =>
      c'.nreg slfN = 2 ∧ c'.nreg slfL0 < N₂.nRegions ∧ c'.nreg slfL1 < N₂.nRegions ∧
      ((∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W (stopSet J (Qof P) N₂ kind k b) q s →
          oW J (q + s) ≠ 0) →
        (∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W (stopSet J (Qof P) N₂ kind k b)
          q s ∧ (Lst J : ℝ) ≤ oW J (q + s)) →
        EvSideLab J (N₂.F (chainModel J.right) (Qof P))
          (labSet J (Qof P) N₂ 2 (c'.nreg slfL0) (c'.nreg slfL1) 0 0)
          (stopSet J (Qof P) N₂ kind k b)) ∧
      SlfFr slfLabR c c') := by
  have hSE : 240700 ≤ slfSE ∧ slfSE < 250000 := by decide
  have hSH : 240700 ≤ slfSH ∧ slfSH < 250000 := by decide
  have hEH : slfSE ≠ slfSH := by decide
  obtain ⟨pe, ph, hat, hpos, hlt, hpick⟩ : ∃ pe ph,
      SlfAtt P J (stopSet J P.Qof N₂ kind k b) c pe ph ∧ 0 < slfOff P J c pe ph ∧
      slfOff P J c pe ph < Lst J ∧ IRS P W c₀ slfPick c 4 (fun c₁ =>
        c₁.nreg slfSE = c.nreg pe ∧ c₁.nreg slfSH = c.nreg ph ∧
        (AgreeExcept [slfSE, slfSH] c₁.nreg c.nreg) ∧ c₁.nmem = c.nmem ∧
        c₁.nreg ALLOC = c.nreg ALLOC) := by
    unfold slfPick
    by_cases hb : c.nreg K0 < c.nreg slfO
    · 
      exact ⟨_, _, hat₀, h0₀, (b0.2.1 (by have := b0.1; omega)), (IRS.ifT hb (guarded (slfCopy2_irs hI hSE hSH hEH))).mono le_rfl (fun _ h => h)⟩
    · have hn := fun h => hb (by
        rw [((E.hK.fix hI).1), b0.2.2 h]; norm_num)
      exact ⟨_, _, hat₁, h0₁, hanc.resolve_left hn, (IRS.ifF hb (slfCopy2_irs hI hSE hSH hEH
        (by decide))).mono (by norm_num) (fun _ h => h)⟩
  unfold slfStr
  refine IRS.seq (K₁ := 4) (K₂ := κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) + 3) hpick ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨e1, e2, fr1, m1, al1⟩
  have hat' : SlfAtt P J (stopSet J P.Qof N₂ kind k b) c₁ slfSE slfSH := by
    unfold SlfAtt SlfPos at *; rwa [e1, e2]
  have ho : slfOff P J c₁ slfSE slfSH = slfOff P J c pe ph := by unfold slfOff; rw [e1, e2]
  obtain ⟨hm, -⟩ := stop_mem E.hP E.hNF₂ hD.ok hD.free
  refine IRS.seq (K₁ := κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1)) (K₂ := 3)
    (guarded (hsl sh Bs F X Ok P W c₀ c₁ J N₁ N₂ E hI₁ hat'.1.1 hat'.1.2.1 hat'.2.1
      ⟨_, hm, hnopar, hat'.2.2⟩ (lt_of_lt_of_eq hpos ho.symm) (lt_of_eq_of_lt ho hlt))) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hfa, hfb, ⟨d, hd, htd, hpd, hAf, hB1, hB0⟩, hm2, hal2, fr2⟩
  simp only [e1, e2] at htd hpd hAf hB1 hB0
  have hL0 : 240700 ≤ slfL0 ∧ slfL0 < 250000 := by decide
  have hL1 : 240700 ≤ slfL1 ∧ slfL1 < 250000 := by decide
  have hN' : 240700 ≤ slfN ∧ slfN < 250000 := by decide
  refine (IRS.block [.copyN slfL0 frA, .copyN slfL1 frB, .constN slfN 2] hI₂
    ⟨iscr_sw hL0.1 hL0.2, iscr_sw hL1.1 hL1.2, ⟨iscr_sw hN'.1 hN'.2, (by have := hI.hw.1 ALLOC; omega)⟩, trivial⟩).mono
    (by simp) ?_
  rintro c₃ rfl
  have v2 : regB c₂.nmem [.copyN slfL0 frA, .copyN slfL1 frB, .constN slfN 2] c₂.nreg slfN = 2 := rfl
  refine ⟨v2, hfa, hfb,
    fun hnp hC1 => ?_, ?_⟩
  · exact guarded (slf_lab_str E hD hat.2.2 hnp hC1 hnopar hd htd hpd hfa)
  · have hSR : ∀ r, (r = slfSE ∨ r = slfSH) → slfLabR r := by
      rintro r (rfl | rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by decide,
          by decide⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by decide,
          by decide⟩))))))
    refine SlfFr.trans ⟨fun r _ hr _ => fr1 r (fun h => hr (hSR r (Or.inl h)))
        (fun h => hr (hSR r (Or.inr h))), al1.ge, fun a _ => by rw [m1]⟩ ?_
    refine SlfFr.trans ⟨fun r h1 hr h3 => fr2 r h1 (fun h => hr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr h)))))) h3, hal2, hm2⟩ ?_
    refine slfFr_block _ _ (fun i hi => ?_) (fun i hi => ?_)
    · simp at hi
      rcases hi with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · solve_by_elim [Or.inr]
      · exact Or.inl rfl
    · simp at hi
      rcases hi with rfl | rfl | rfl <;> simp only [dstI, slfL0, slfL1, slfN, ALLOC, sw] <;>
        omega

set_option maxHeartbeats 16000000 in
/-- **The label step.** -/
theorem slfLab_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {sl : Stmt}
    {κ : ℕ → ℕ} (hsl : StrLabSpec sl κ) {kind k b : ℕ} (hD : OrgD P J N₂ kind k b)
    (hat₀ : SlfAtt P J (stopSet J (Qof P) N₂ kind k b) c (oF0 + 1) (oF0 + 2))
    (hat₁ : SlfAtt P J (stopSet J (Qof P) N₂ kind k b) c (a1F + 1) (a1F + 2))
    (b0 : BitIs c slfO (slfOff P J c (oF0 + 1) (oF0 + 2) < Lst J))
    (b3 : BitIs c (slfO + 3) (0 < slfOff P J c (oF0 + 1) (oF0 + 2)))
    (b7 : BitIs c (slfO + 7) (0 < slfOff P J c (a1F + 1) (a1F + 2)))
    (ha1 : c.nreg slfA ≤ 1)
    (ha : c.nreg slfA = 1 ↔ (slfOff P J c (oF0 + 1) (oF0 + 2) < Lst J ∨
      slfOff P J c (a1F + 1) (a1F + 2) < Lst J))
    (hnp : (∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W (stopSet J (Qof P) N₂ kind k b)
      q s → oW J (q + s) ≠ 0) →
      slfOff P J c (oF0 + 1) (oF0 + 2) ≠ 0 ∧ slfOff P J c (a1F + 1) (a1F + 2) ≠ 0)
    (hpar : SlfParOK P J N₂ (stopSet J (Qof P) N₂ kind k b) (c.nreg oPar))
    (hroom : c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) + 4 ≤ W) :
    IRS P W c₀ (slfLabS sl) c (κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) + 40) (fun c' =>
      SlfLabOK P J N₂ (stopSet J (Qof P) N₂ kind k b) (c.nreg slfA) (c'.nreg slfN)
        (c'.nreg slfL0) (c'.nreg slfL1) ∧ SlfFr slfLabR c c') := by
  unfold slfLabS
  let addr := κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1)
  refine (IRS.seq (K₁ := 1) (K₂ := addr + 39)
    (set1_irs hI (by unfold slfN sw; omega) (Nat.zero_le _)) ?_).mono (by omega) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨n1, q1, m1⟩
  obtain ⟨k0, k1, -, -, -, -, k3⟩ := E.hK.fix hI₁
  have fr01 : SlfFr slfLabR c c₁ := ⟨fun r _ hr _ => q1 r (fun h => hr (Or.inl h)),
    (at_index q1 ALLOC).ge, fun a _ => by rw [m1]⟩
  have qr : ∀ r ≥ 240000, r < 250000 → r ≠ slfN → c₁.nreg r = c.nreg r :=
    fun r _ _ h => q1 r h
  have skp : ¬ (c.nreg slfA = 1 ∧ 0 < slfOff P J c (oF0 + 1) (oF0 + 2) ∧
      0 < slfOff P J c (a1F + 1) (a1F + 2)) →
      IRS P W c₀ .skip c₁ 0 (fun c' => SlfLabOK P J N₂ (stopSet J P.Qof N₂ kind k b)
        (c.nreg slfA) (c'.nreg slfN) (c'.nreg slfL0) (c'.nreg slfL1) ∧ SlfFr slfLabR c c') :=
    fun hnt => IRS.skip hI₁ ⟨⟨by omega, fun h => by omega, fun h => by omega,
      fun hA hnp' _ => absurd ⟨hA, lt_of_le_of_ne (slfOff_nonneg hat₀.1) (hnp hnp').1.symm,
        lt_of_le_of_ne (slfOff_nonneg hat₁.1) (hnp hnp').2.symm⟩ hnt⟩, fr01⟩
  have eA : c₁.nreg slfA = c.nreg slfA := at_index qr _
  by_cases hA : c₁.nreg K0 < c₁.nreg slfA
  swap
  · exact (IRS.ifF hA (skp (fun h => guarded hA))).mono (by omega)
      (fun _ h => h)
  refine (IRS.ifT (K := addr + 37) hA ?_).mono (by omega)
    (fun _ h => h)
  have e3 : c₁.nreg (slfO + 3) = c.nreg (slfO + 3) := at_index qr _
  by_cases h3 : c₁.nreg K0 < c₁.nreg (slfO + 3)
  swap
  · exact (IRS.ifF h3 (skp (fun h => h3 (by rw [k0, e3, b3.2.2 h.2.1]; norm_num)))).mono
      (by omega) (fun _ h => h)
  refine (IRS.ifT (K := addr + 35) h3 ?_).mono (by omega)
    (fun _ h => h)
  have e7 : c₁.nreg (slfO + 7) = c.nreg (slfO + 7) := at_index qr _
  by_cases h7 : c₁.nreg K0 < c₁.nreg (slfO + 7)
  swap
  · exact (IRS.ifF h7 (skp (fun h => h7 (by rw [k0, e7, b7.2.2 h.2.2]; norm_num)))).mono
      (by omega) (fun _ h => h)
  refine (IRS.ifT (K := addr + 33) h7 ?_).mono (by omega)
    (fun _ h => h)
  have hp₀ := b3.2.1 (by have := b3.1; omega)
  have hp₁ := b7.2.1 (by have := b7.1; omega)
  have hanc := guarded ha.1
  have eP : c₁.nreg oPar = c.nreg oPar := at_index qr _
  by_cases hq : c₁.nreg K0 < c₁.nreg oPar
  · -- the labels of the parent
    have hpp : 0 < c.nreg oPar := by rw [eP] at hq; omega
    have hNW := E.nw₂' hI₁
    obtain ⟨b1, hb2, -⟩ := Restore.nf_bounds hNW
    have hiK : c.nreg oPar - 1 < N₂.nChords := by have := hpar.1; omega
    have hb2' := hb2 _ hiK
    rw [← eP] at hb2' hiK
    refine (IRS.ifT (K := 13) hq (IRS.block slfLdL hI₁ (guarded (slfLdL_ok c₁.nmem c₁.nreg k1 k3)))).mono (by omega) ?_
    rintro c' rfl
    obtain ⟨v0, v1, v2, -⟩ := slfLdL_val c₁.nmem c₁.nreg k1 k3
    obtain ⟨-, -, -, r3, r4⟩ := hNW.holds.2.2.2.2.2.1 _ hiK
    rw [r3] at v0
    rw [r4] at v1
    rw [eP] at v0 v1 hiK
    obtain ⟨hu, hdn, -⟩ := (regOf_spec E.hNF₂).2.1 _ hiK
    refine ⟨⟨by simp only; omega, fun _ => by simp only; rwa [v0],
      fun _ => by simp only; rwa [v1], fun _ hnp' hC1 => ?_⟩, ?_⟩
    · simp [v0, v1, v2]
      rcases hanc with hl | hl
      · exact slf_lab_par E hD hat₀.2.2 hp₀ hl hnp' hC1 hiK (hpar.2.2 hpp)
      · exact from_facts slf_lab_par
    · refine fr01.trans (slfFr_block _ _ (fun i hi => ?_) (fun i hi => ?_))
      · simp only [slfLdL, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [dstI, slfLabR]
      · simp only [slfLdL, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [dstI, slfP, slfY, slfL0, slfL1, slfN, ALLOC, sw] <;> omega
  · -- the labels at the stretch
    have hnopar : ∀ cc ∈ N₂.F (J.right.chainModel) P.Qof,
        ¬ stopSet J P.Qof N₂ kind k b ⊆ cc := fun cc hcc hsub => by
      have := (hpar.2.1 cc hcc hsub).1; omega
    have r01 := at_index qr (oF0 + 1)
    have r02 := at_index qr (oF0 + 2)
    have r11 := at_index qr (a1F + 1)
    have r12 := at_index qr (a1F + 2)
    have o0 := slfOff_congr (P := P) (J := J) r01 r02
    have o1 := slfOff_congr (P := P) (J := J) r11 r12
    have e0 : c₁.nreg slfO = c.nreg slfO := at_index qr _
    refine (IRS.ifF (K := addr + 7) hq
      ((slfStr_irs E hI₁ hsl hD (hat₀.congr r01 r02) (hat₁.congr r11 r12)
        (by rw [o0]; exact b0.of_eq e0) (by rwa [o0, o1]) (by rwa [o0])
        (by rwa [o1]) hnopar (by grind)).mono (by omega)
        (fun _ h => h))).mono (by omega) ?_
    rintro c' ⟨hn2, hl0, hl1, hlab, fr⟩
    exact ⟨⟨by omega, fun _ => hl0, fun _ => hl1, fun _ hnp' hC1 => by
      grind⟩, fr01.trans fr⟩

end

end SweepEv

end Chazelle.Core
