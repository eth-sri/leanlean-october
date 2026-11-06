module

public import Chazelle.MacT
public import Chazelle.Core.SweepEvStopSort3
public import Chazelle.Core.SweepEvStepL5
public import Chazelle.Core.SweepEvGenR
public import Chazelle.Core.SweepIoLHit3
public import Chazelle.Core.SweepIoLoop
public import Chazelle.Core.SweepEvFace
public import Chazelle.Core.SweepChainT
public import Chazelle.Core.DownPhaseTransWt
public import Chazelle.Core.SweepIoBruteLoop

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
  [.subN slfP oPar K1, .addN slfY ztbz K3, .loadN slfY slfY, .addN slfY slfY slfP,
    .addN slfY slfY slfP, .addN slfY slfY slfP, .addN slfY slfY slfP, .addN slfY slfY slfP,
    .addN slfY slfY K3, .loadN slfL0 slfY, .addN slfY slfY K1, .loadN slfL1 slfY,
    .constN slfN 2]
theorem slfLdL_val (m f : ℕ → ℕ) (hk1 : f K1 = 1) (hk3 : f K3 = 3) :
    regB m slfLdL f slfL0 = m (m ztwkt + 5 * ztlnt + 3) ∧
    regB m slfLdL f slfL1 = m (m ztwkt + 5 * ztlnt + 4) ∧
    regB m slfLdL f slfN = 2 ∧
    ∀ q, q ≠ slfP → q ≠ slfY → q ≠ slfL0 → q ≠ slfL1 → q ≠ slfN → regB m slfLdL f q = f q := by
  zubx
  zubtd
  refine ⟨?_, ?_, ?_, fun q h1 h2 h3 h4 h5 => ?_⟩
  · zubjv

  · zubjv

  · rfl
  · exact regB_other m slfLdL f (fun i hi => by
      zucaa
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        zvmwd <;> intro he <;> subst he <;> simp_all)
theorem slfLdL_ok {W : ℕ} (m f : ℕ → ℕ) (hk1 : f K1 = 1) (hk3 : f K3 = 3) (hb : f ztbz + 3 ≤ W)
    (_hp : 0 < f oPar)
    (hb2 : m ztwkt + 5 * ztlnt + 4 ≤ W) (hW : 2 ≤ W) :
    okB W m slfLdL f := by
  zubx
  zubtd
  have s : ∀ j, 4054 ≤ j → j ≤ 4110 → IScr ztjfo := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  zufuk
  have hb2' : m ztcnb + 5 * (f 244064 - 1) + 4 ≤ W := hb2
  simp only [slfLdL, okB, okI, regI, upd, slfP, slfY, slfL0, slfL1, slfN, oPar, K1, K3, sw]
  grind

/-- The registers of the label step. -/
def slfLabR (r : ℕ) : Prop :=
  r = slfN ∨ r = slfL0 ∨ r = slfL1 ∨ r = slfP ∨ r = slfY ∨ StrR r

/-- The pick of the stretch attachment. -/
def slfPick : Stmt :=
  .ifLtN K0 slfO (block [.copyN slfSE ztjf, .copyN slfSH ztms])
    (block [.copyN slfSE ztlq, .copyN slfSH ztoo])

/-- The labels faced at the counterpart of the stretch attachment. -/
def slfStr (sl : Stmt) : Stmt :=
  .seq slfPick (.seq sl (block [.copyN slfL0 frA, .copyN slfL1 frB, .constN slfN 2]))

/-- **The label step.** -/
def slfLabS (sl : Stmt) : Stmt :=
  .seq (.instr (.constN slfN 0))
    (.ifLtN K0 slfA (.ifLtN K0 ztfup (.ifLtN K0 zthkl
      (.ifLtN K0 oPar (block slfLdL) ztwek) .skip) .skip) .skip)

/-- The contract body of the stretch labels (`StrLabTask`). -/
def StrLabSpec (sl : Stmt) (κ : ℕ → ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      c.nreg slfSE < (chainModel J.whole).W.n →
      ProperPos ztbm zta P.n ztst →
      |((chainModel J.whole).pos (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩).2| < J.whole.radius →
      (∃ e, e ∈ F₂plus J ztwis ∧
        ztxzf ∧
        SideAttach (chainModel J.whole).W e ztere
          ztwqd) →
      0 < oW J ztwsw →
      oW J ztwsw < Lst J →
      c.nreg ALLOC + κ zto * ztgf ≤ W →
      IRS P W c₀ sl c ztxen (fun c' =>
        c'.nreg frA < N₂.nRegions ∧ c'.nreg frB < N₂.nRegions ∧
        (∃ d, d < Lst J ∧
          ztxqf ∧
          c.nreg slfSE = ztefg % (chainModel J.whole).W.n ∧
          AfterFaces ztj ztbcq
            ztwqd
            ztxhh ∧
          (0 < (chainModel J.whole).param zta ztst →
            BeforeFaces ztj ztbcq
              ztwqd
              ztwva) ∧
          ((chainModel J.whole).param zta ztst = 0 →
            BeforeFaces ztj zterj 0
              ztwva)) ∧
        zth ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
        ztfcw)
theorem strLabSpec_of (h : StrLabTask) : ∃ sl κ, StrLabSpec sl κ := h

/-- The frame of a block. -/
theorem slfFr_block {R : ℕ → Prop} (l : List Instr) (c : Config) (hR : ∀ i ∈ l, R ztcpw)
    (hA : ∀ i ∈ l, dstI i ≠ ALLOC) :
    SlfFr R c { c with nreg := regB c.nmem l c.nreg } :=
  ⟨fun _r _ hr _ => regB_other _ _ _ by_grind,
    (regB_other _ _ _ hA).ge, by_simp_all⟩

/-- A stop attachment usable as the stretch attachment. -/
def SlfAtt (P : Polygon) (J : Merge.Junction) (e : Set Point) (c : Config) (pe ph : ℕ) : Prop :=
  SlfPos P J c pe ph ∧
    |((chainModel J.whole).pos (Qof P) ⟨c.nreg pe, c.nreg ph⟩).2| < J.whole.radius ∧
    SideAttach (chainModel J.whole).W e ztqiy
      ((chainModel J.whole).param zta ztpn)

/-- The facts of the label step. -/
def SlfLabOK (P : Polygon) (J : Merge.Junction) (N₂ : NF) (e : Set Point) (anc nl l₀ l₁ : ℕ) :
    Prop :=
  nl ≤ 2 ∧ (0 < nl → l₀ < N₂.nRegions) ∧ (1 < nl → l₁ < N₂.nRegions) ∧
    (anc = 1 → ztwnd →
      ztwly →
      EvSideLab J ztwis (labSet J zta N₂ nl l₀ l₁ 0 0) e)
theorem slfCopy2_irs (hI : IInv W c₀ c) {r₁ a₁ r₂ a₂ : ℕ}
    (h₁ : 240700 ≤ r₁ ∧ r₁ < 250000) (h₂ : 240700 ≤ r₂ ∧ r₂ < 250000) (hne : r₁ ≠ r₂)
    (ha : a₂ ≠ r₁) :
    IRS P W c₀ (block [.copyN r₁ a₁, .copyN r₂ a₂]) c 2 (fun c' => c'.nreg r₁ = c.nreg a₁ ∧
      c'.nreg r₂ = c.nreg a₂ ∧ (∀ q, q ≠ r₁ → q ≠ r₂ → c'.nreg q = c.nreg q) ∧
      c'.nmem = c.nmem ∧ c'.nreg ALLOC = c.nreg ALLOC) := by
  have hA1 : r₁ ≠ ALLOC := by unfold ALLOC; omega
  have hA2 : r₂ ≠ ALLOC := by unfold ALLOC; omega
  refine (IRS.block [.copyN r₁ a₁, .copyN r₂ a₂] hI
    ⟨iscr_sw h₁.1 h₁.2, iscr_sw h₂.1 h₂.2, trivial⟩).mono le_rfl ?_
  zuu
  refine ⟨?_, ?_, fun q h1 h2 => ?_, rfl, ?_⟩
  · zuie
  · zuie
  · zuie
  · zumxi; rw [upd_other _ _ _ ztvap, upd_other _ _ _ ztvao]
theorem SlfAtt.congr {e : Set Point} {pe ph : ℕ} {c c' : Config} (h : SlfAtt P J e c pe ph)
    (he : c'.nreg pe = c.nreg pe) (hh : c'.nreg ph = c.nreg ph) : SlfAtt P J e c' pe ph := by
  zujqe
theorem slfOff_nonneg {e h : ℕ} (hp : SlfPos P J c e h) : 0 ≤ slfOff P J c e h := by
  have hgn : ztboy := by
    zugq
  unfold slfOff
  zumot
  exact off_nonneg (by have := hp.2.1.1; positivity) by_simp_all
set_option maxHeartbeats 8000000 in
/-- **The labels faced at the counterpart of the stretch attachment.** -/
theorem slfStr_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {sl : Stmt}
    {κ : ℕ → ℕ} (hsl : StrLabSpec sl κ) {kind k b : ℕ} (hD : OrgD P J N₂ kind k b)
    (hat₀ : SlfAtt P J ztwja c ztjf ztms)
    (hat₁ : SlfAtt P J ztwja c ztlq ztoo)
    (b0 : BitIs c slfO ztwvc)
    (hanc : slfOff P J c ztjf ztms < Lst J ∨ slfOff P J c ztlq ztoo < Lst J)
    (h0₀ : 0 < slfOff P J c ztjf ztms) (h0₁ : 0 < slfOff P J c ztlq ztoo)
    (hnopar : ∀ cc ∈ N₂.F ztj zta, ¬ stopSet J zta N₂ kind k b ⊆ cc)
    (hroom : c.nreg ALLOC + κ zto * ztgf + 4 ≤ W) :
    IRS P W c₀ ztwek c (4 + (κ zto * ztgf + 3)) (fun c' =>
      c'.nreg slfN = 2 ∧ c'.nreg slfL0 < N₂.nRegions ∧ c'.nreg slfL1 < N₂.nRegions ∧
      ((∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W ztwja q s →
          oW J ztej ≠ 0) →
        (∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W ztwja
          q s ∧ (Lst J : ℝ) ≤ oW J ztej) →
        EvSideLab J ztwis
          (labSet J zta N₂ 2 ztqhf ztqhg 0 0)
          ztwja) ∧
      SlfFr slfLabR c c') := by
  zuiba
  have hSE : 240700 ≤ slfSE ∧ slfSE < 250000 := by_decide
  have hSH : 240700 ≤ slfSH ∧ slfSH < 250000 := by_decide
  have hEH : slfSE ≠ slfSH := by_decide
  obtain ⟨pe, ph, hat, hpos, hlt, hpick⟩ : ∃ pe ph,
      SlfAtt P J ztwja c pe ph ∧ 0 < slfOff P J c pe ph ∧
      slfOff P J c pe ph < Lst J ∧ IRS P W c₀ slfPick c 4 (fun c₁ =>
        c₁.nreg slfSE = c.nreg pe ∧ c₁.nreg slfSH = c.nreg ph ∧
        (∀ q, q ≠ slfSE → q ≠ slfSH → c₁.nreg q = c.nreg q) ∧ c₁.nmem = c.nmem ∧
        c₁.nreg ALLOC = c.nreg ALLOC) := by
    unfold slfPick
    by_cases hb : c.nreg K0 < c.nreg slfO
    · have hl : slfOff P J c _ _ < Lst J := b0.2.1 (by have := b0.1; omega)
      exact ⟨_, _, hat₀, h0₀, hl, (IRS.ifT hb (slfCopy2_irs hI hSE hSH hEH
        by_decide)).mono le_rfl by_simp_all⟩
    · have hn : ¬ slfOff P J c _ _ < Lst J := fun h => hb (by
        rw [k0, b0.2.2 h]; norm_num)
      exact ⟨_, _, hat₁, h0₁, hanc.resolve_left hn, (IRS.ifF hb (slfCopy2_irs hI hSE hSH hEH
        by_decide)).mono by_norm_num by_simp_all⟩
  unfold slfStr
  refine IRS.seq hpick ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨e1, e2, fr1, m1, al1⟩
  have hat' : SlfAtt P J ztwja c₁ slfSE slfSH := by
    zujqe
  have ho : slfOff P J c₁ slfSE slfSH = slfOff P J c pe ph := by unfold slfOff; simp_all
  obtain ⟨hm, -⟩ := stop_mem E.hP E.hNF₂ hD.ok hD.free
  refine IRS.seq
    (hsl sh Bs F X Ok P W c₀ c₁ J N₁ N₂ E hI₁ hat'.1.1 hat'.1.2.1 hat'.2.1
      ⟨_, hm, hnopar, hat'.2.2⟩ (lt_of_lt_of_eq hpos ho.symm) (lt_of_eq_of_lt ho hlt)
      by_omega) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hfa, hfb, ⟨d, hd, htd, hpd, hAf, hB1, hB0⟩, hm2, hal2, fr2⟩
  simp only [e1, e2] at htd hpd hAf hB1 hB0
  have hL0 : 240700 ≤ slfL0 ∧ slfL0 < 250000 := by_decide
  have hL1 : 240700 ≤ slfL1 ∧ slfL1 < 250000 := by_decide
  zujzr
  zudoc
  refine (IRS.block [.copyN slfL0 frA, .copyN slfL1 frB, .constN slfN 2] hI₂
    ⟨iscr_sw hL0.1 hL0.2, iscr_sw hL1.1 hL1.2, ⟨iscr_sw hN'.1 hN'.2, hW2⟩, trivial⟩).mono
    by_simp ?_
  rintro c₃ rfl
  have v0 : regB c₂.nmem [.copyN slfL0 frA, .copyN slfL1 frB, .constN slfN 2] c₂.nreg slfL0 =
      c₂.nreg frA := by
    rfl
  have v1 : regB c₂.nmem [.copyN slfL0 frA, .copyN slfL1 frB, .constN slfN 2] c₂.nreg slfL1 =
      c₂.nreg frB := by
    rfl
  have v2 : regB c₂.nmem [.copyN slfL0 frA, .copyN slfL1 frB, .constN slfN 2] c₂.nreg slfN = 2 := by
    rfl
  refine ⟨v2, by_grind, by_grind,
    fun hnp hC1 => ?_, ?_⟩
  · simp only; rw [v0, v1]
    exact slf_lab_str E hD hat.2.2 hnp hC1 hnopar hd htd hpd hfa hfb hAf hB1 hB0
  · have hSR : ∀ r, (r = slfSE ∨ r = slfSH) → slfLabR r := by
      rintro r (rfl | rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by_decide,
          by decide⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by_decide,
          by decide⟩))))))
    refine SlfFr.trans ⟨fun r _ hr _ => fr1 r (fun h => hr (hSR r zteg))
        (fun h => hr (hSR r ztbho)), al1.ge, by_grind⟩ ?_
    refine SlfFr.trans ⟨fun r h1 hr h3 => fr2 r h1 ztzfc h3, hal2, hm2⟩ ?_
    refine slfFr_block _ _ ztdp ztdp
    · zuvx
      zuiec
      · exact Or.inr ztp
      · exact Or.inr ztwiz
      · zulej
    · zuvx
      rcases hi with rfl | rfl | rfl <;> simp only [dstI, slfL0, slfL1, slfN, ALLOC, sw] <;>
        omega
set_option maxHeartbeats 16000000 in
/-- **The label step.** -/
theorem slfLab_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {sl : Stmt}
    {κ : ℕ → ℕ} (hsl : StrLabSpec sl κ) {kind k b : ℕ} (hD : OrgD P J N₂ kind k b)
    (hat₀ : SlfAtt P J ztwja c ztjf ztms)
    (hat₁ : SlfAtt P J ztwja c ztlq ztoo)
    (b0 : BitIs c slfO ztwvc)
    (b3 : BitIs c ztfup ztyhd)
    (b7 : BitIs c zthkl ztyhe)
    (ha1 : c.nreg slfA ≤ 1)
    (ha : c.nreg slfA = 1 ↔ (slfOff P J c ztjf ztms < Lst J ∨
      slfOff P J c ztlq ztoo < Lst J))
    (hnp : (∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W ztwja
      q s → oW J ztej ≠ 0) →
      slfOff P J c ztjf ztms ≠ 0 ∧ slfOff P J c ztlq ztoo ≠ 0)
    (hpar : SlfParOK P J N₂ ztwja (c.nreg oPar))
    (hroom : c.nreg ALLOC + κ zto * ztgf + 4 ≤ W) :
    IRS P W c₀ ztwei c (κ zto * ztgf + 40) (fun c' =>
      SlfLabOK P J N₂ ztwja (c.nreg slfA) ztvgz
        ztqhf ztqhg ∧ SlfFr slfLabR c c') := by
  zueqm
  have hnn₀ := slfOff_nonneg hat₀.1
  have hnn₁ := slfOff_nonneg hat₁.1
  zujzr
  unfold slfLabS
  refine (IRS.seq (K₂ := κ zto * ztgf + 39)
    (set1_irs hI hN' ztbg) ?_).mono by_omega (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨n1, q1, m1⟩
  obtain ⟨k0, k1, -, -, -, -, k3⟩ := E.hK.fix hI₁
  have fr01 : SlfFr slfLabR c c₁ := ⟨fun r _ hr _ => q1 r ztwnm,
    by omega, by_simp_all⟩
  have qr : ∀ r, 240000 ≤ r → r < 250000 → r ≠ slfN → c₁.nreg r = c.nreg r :=
    by simp_all
  have skp : ¬ (c.nreg slfA = 1 ∧ 0 < slfOff P J c _ _ ∧
      0 < slfOff P J c _ _) →
      IRS P W c₀ .skip c₁ 0 (fun c' => SlfLabOK P J N₂ _
        _ ztvgz ztqhf ztqhg ∧ SlfFr slfLabR c c') :=
    fun hnt => IRS.skip hI₁ ⟨⟨by_omega, by_grind, by_grind,
      fun hA hnp' _ => absurd ⟨hA, lt_of_le_of_ne hnn₀ by_grind,
        lt_of_le_of_ne hnn₁ (hnp hnp').2.symm⟩ hnt⟩, fr01⟩
  have eA : c₁.nreg slfA = c.nreg slfA := qr _ by_decide
    by_decide by_decide
  by_cases hA : c₁.nreg K0 < c₁.nreg slfA
  swap
  · exact (IRS.ifF hA (skp by_grind)).mono by_omega
      by_grind
  have hanc1 : c.nreg slfA = 1 := by_omega
  refine (IRS.ifT (K := κ zto * ztgf + 37) hA ?_).mono by_omega
    ztb
  have e3 : c₁.nreg _ = c.nreg ztfup := qr _ by_decide
    by_decide by_decide
  by_cases h3 : c₁.nreg K0 < c₁.nreg ztfup
  swap
  · exact (IRS.ifF h3 (skp (fun h => h3 (by rw [k0, e3, b3.2.2 h.2.1]; norm_num)))).mono
      by_omega by_grind
  refine (IRS.ifT (K := κ zto * ztgf + 35) h3 ?_).mono by_omega
    ztb
  have e7 : c₁.nreg _ = c.nreg zthkl := qr _ by_decide
    by_decide by_decide
  by_cases h7 : c₁.nreg K0 < c₁.nreg zthkl
  swap
  · exact (IRS.ifF h7 (skp (fun h => h7 (by rw [k0, e7, b7.2.2 h.2.2]; norm_num)))).mono
      by_omega by_grind
  refine (IRS.ifT (K := κ zto * ztgf + 33) h7 ?_).mono by_omega
    ztb
  have hp₀ : ztoqh := b3.2.1 (by zvnak at h3; have := b3.1; omega)
  have hp₁ : ztoqh := b7.2.1 (by rw [e7] at h7; have := b7.1; omega)
  have hanc := ha.1 hanc1
  have eP : c₁.nreg oPar = c.nreg oPar := qr _ by_decide
    by_decide by_decide
  by_cases hq : c₁.nreg K0 < c₁.nreg oPar
  · -- the labels of the parent
    have hpp : 0 < c.nreg oPar := by_omega
    have hNW := E.nw₂' hI₁
    zucnq
    have hW := hI₁.hw.1 ALLOC
    have hiK : c.nreg oPar - 1 < N₂.nChords := by have := hpar.1; omega
    have hb2' := hb2 _ hiK
    rw [← eP] at hb2' hiK
    refine (IRS.ifT (K := 13) hq (IRS.block slfLdL hI₁ (slfLdL_ok c₁.nmem c₁.nreg k1 k3
      by_omega by_omega by_omega by_omega))).mono by_omega ?_
    zuu
    obtain ⟨v0, v1, v2, -⟩ := slfLdL_val c₁.nmem c₁.nreg k1 k3
    have hNA : NFAt c₁.nmem _ N₂ := hNW.holds
    obtain ⟨-, -, -, r3, r4⟩ := hNA.2.2.2.2.2.1 _ hiK
    rw [r3] at v0
    rw [r4] at v1
    rw [eP] at v0 v1 hiK
    obtain ⟨hu, hdn, -⟩ := (regOf_spec hN).2.1 _ hiK
    refine ⟨⟨by_rfl, by_grind,
      by grind, fun _ hnp' hC1 => ?_⟩, ?_⟩
    · simp only; rw [v0, v1, v2]
      rcases hanc with hl | hl
      · exact slf_lab_par E hD hat₀.2.2 hp₀ hl hnp' hC1 hiK ztvvy
      · exact slf_lab_par E hD hat₁.2.2 hp₁ hl hnp' hC1 hiK ztvvy
    · refine fr01.trans (slfFr_block _ _ ztdp ztdp)
      · zucaa
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [dstI, slfLabR, true_or, or_true]
      · zucaa
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [dstI, slfP, slfY, slfL0, slfL1, slfN, ALLOC, sw] <;> omega
  · -- the labels at the stretch
    have hp0 : c.nreg oPar = 0 := by_omega
    have hnopar : ∀ cc ∈ N₂.F _ _,
        ¬ stopSet J _ N₂ kind k b ⊆ cc := fun cc hcc hsub => by
      have := (hpar.2.1 cc hcc hsub).1; omega
    have r01 := qr ztjf by_decide by_decide
      by_decide
    have r02 := qr ztms by_decide by_decide
      by_decide
    have r11 := qr ztlq by_decide by_decide
      by_decide
    have r12 := qr ztoo by_decide by_decide
      by_decide
    zubfb

    have e0 : ztsgr := qr _ by_decide
      by_decide by_decide
    have hAl : ztdc := by_grind
    refine (IRS.ifF (K := κ zto * ztgf + 7) hq
      ((slfStr_irs E hI₁ hsl hD zttna zttnb
        (by zuntr; exact b0.of_eq e0) by_grind by_grind
        by_grind hnopar by_omega).mono by_omega
        ztb)).mono by_omega ?_
    rintro c' ⟨hn2, hl0, hl1, hlab, fr⟩
    exact ⟨⟨by_omega, by_omega, by_omega, by_grind⟩, fr01.trans fr⟩
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)
@[expose] public section
theorem m2c_wall_left {C : Chain} {Q : Polygon} {N : NF} (hN : IsNF ztc Q N) {k b : ℕ}
    (hk : k < N.nChords) (hb : b ≤ 1) :
    sideLeft (chainModel C).W (endPos N k ztlp).edge
      ((chainModel C).param Q ztxoa)
      (rayPt ((chainModel C).pos Q ztxoa) ztkz 1) := by
  obtain ⟨y, l, r, hlr, heq, hl, hr, -⟩ := rec_ends hN hk
  zuftf
  zubhr
  · have he : ztiou := by_rfl
    rw [he, dirOf_zero]
    have := sideLeft_of_attach hA.2 ztbt ztto
      (fun s hs0 hs => by
        show rayPt ((chainModel C).pos Q (N.chord k).rpos) (-1) s ∈ _
        rw [hr, heq]
        refine ztrau <;> zvmxf <;> linarith)
    tauto
  · have he : ztiov := by_rfl
    rw [he, dirOf_one]
    have := sideLeft_of_attach hA.1 ztp ztto
      (fun s hs0 hs => by
        show rayPt ((chainModel C).pos Q (N.chord k).lpos) 1 s ∈ _
        rw [hl, heq]
        refine ztrau <;> zvmxf <;> linarith)
    tauto

/-! ## The program -/

/-- Set the local hit's input from the position `(e, h)` and the direction code `oB`. -/
def m2cSet (e h : ℕ) : List Instr := [.copyN lE e, .copyN lH h, .copyN lD oB]

/-- **Shared and top codes.** -/
def m2cS (sh : Stmt) : Stmt :=
  .seq (callArr zted oPE oPH oB m2F)
    (.ifLtN m2F K1 (noRes r2F)
      (.seq (block (m2cSet pE2 pH2)) ztxky))

/-- **Wall codes.** -/
def m2cW (sh : Stmt) : Stmt :=
  .seq (block (m2cSet oPE oPH)) ztxky

/-- **The candidate of `C₂`.** -/
def m2c (sh : Stmt) : Stmt :=
  .ifLtN oKd K1 ztvyp ztjdf
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable (m f : ℕ → ℕ)
theorem m2cSet_val {e h : ℕ} (_he : e ≠ lE ∧ e ≠ lH) (hh : h ≠ lE) :
    regB m zteua f lE = f e ∧ regB m zteua f lH = f h ∧
      regB m zteua f lD = f oB ∧
      (∀ q, q ≠ lE → q ≠ lH → q ≠ lD → regB m zteua f q = f q) := by
  have n1 : lE ≠ lH := by_decide
  have n2 : lE ≠ lD := by_decide
  have n3 : lH ≠ lD := by_decide
  have nb : oB ≠ lE ∧ oB ≠ lH := by_decide
  refine ztdwx <;>
    simp [m2cSet, regB, regI, upd, nb.1,
      nb.2, *]
theorem m2cSet_ok (e h : ℕ) : okB W m zteua f :=
  ⟨iscr_sw by_decide by_decide,
    iscr_sw by_decide by_decide,
    iscr_sw by_decide by_decide, trivial⟩

/-- The cost of a branch. -/
def m2cK (T Fg D : ℕ) : ℕ := 35007 + (3 + ztpcp + 2)
theorem m2cK_le (T Fg D : ℕ) : m2cK T Fg D + 4 ≤ ztryn * ztbbs := by
  have h1 : lhRunK T Fg D + 7 ≤ genK Fg D T := by unfold lhRunK genK; omega
  have h2 := genK_le Fg D T
  have h3 : ztryn * ztbbs = κGen D * ztbbs + 40000 * ztbbs := by
    ring
  have h4 : 40000 ≤ 40000 * ztbbs := Nat.le_mul_of_pos_right _ ztqat
  zugul
  have e : m2cK T Fg D + 4 = ztpcp + 35016 := by unfold m2cK; ring
  omega
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}
variable {r : ℕ}
theorem m2c_M2R_lh (h : LHSW r2F r) : M2R r := by
  rcases h with (h | h) | h
  · tauto
  · exact Or.inr (Or.inl ⟨by_omega, by unfold sw at *; omega⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by_tauto,
      by tauto⟩)))
theorem m2c_M2R_set (h : r = lE ∨ r = lH ∨ r = lD) : M2R r := by
  left; rcases h with rfl | rfl | rfl <;> simp [lE, lH, lD, sw]
theorem m2c_nr (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) :
    c.nreg zthy = 2 * J.right.m + 7 := by
  zubuy
  zubos
  exact hst.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The local hit of `C₂` from a position** `(e, h)`, saved at `r2F`. -/
theorem m2c_lh_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hM : MCtx P W J.right N₂ ztbmp gMD2 gCD2 ztbz c) {e h : ℕ}
    (he : e ≠ lE ∧ e ≠ lH) (hh : h ≠ lE) (hb : c.nreg oB ≤ 1)
    (hxe : c.nreg e < (chainModel J.right).W.n)
    (hpp : ProperPos ztj zta P.n ztkv)
    (hcl : PosClass J.right zta ztkv)
    (hy : |((chainModel J.right).pos zta ⟨c.nreg e, c.nreg h⟩).2| < J.right.radius)
    (hon : (chainModel J.right).pos zta ztkv ∈ J.right.set ∨
      |((chainModel J.right).pos (Qof P) ⟨c.nreg e, c.nreg h⟩).1| = J.right.radius)
    {Gd : Prop}
    (hGd : Gd → sideLeft (chainModel J.right).W ztvjk
        ((chainModel J.right).param zta ztkv)
        (rayPt ztynh ztwow 1) ∧
      ((chainModel J.right).pos zta ztkv).2 ≤ J.right.top.2)
    (hroom : c.nreg ALLOC +
      (3 + ztbajp) ≤ W) :
    IRS P W c₀ (.seq (block zteua) ztxky) c
      (3 + ztbajp) (fun c' =>
      ResOK P J.right ztynh
        ztwow Gd r2F c' ∧
      EFr (fun r => ztkdk ∨ LHSW r2F r) c c') := by
  refine IRS.seq (IRS.block zteua hI (m2cSet_ok _ _ e h)) ?_
  zugn
  obtain ⟨vE, vH, vD, vo⟩ := m2cSet_val c.nmem c.nreg he hh
  have v1E : ztsgp := by_simp_all
  have v1H : c₁.nreg lH = c.nreg h := by_simp_all
  have v1D : c₁.nreg lD = c.nreg oB := by_simp_all
  have k1 : ∀ q, q ≠ lE → q ≠ lH → q ≠ lD → c₁.nreg q = c.nreg q := fun q a b d => by
    simp_all
  zull
  have hA1 : ztdc := k1 _ by_decide
    by_decide by_decide
  have hM₁ : ztygn :=
    MCtx.transport hM (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        exact k1 _ by_decide by_decide
          by_decide)
      (fun a _ => by zvmxz) ztqew
  have hnr : c₁.nreg zthy = 2 * J.right.m + 7 := m2c_nr E hI₁
  refine (lhSave_irs E.hsh E.hBs E.hXl ztxcg
    ztxcg ztwos
    ztwos ztkp hI₁ E.hK E.hG
    E.hWh hM₁ E.hP E.hNF₂ E.hX E.hcap E.hOk₂ E.hsg₂ E.hdeg₂ hnr (x := ztkv) v1E v1H
    by_omega hxe hpp hcl hy hon (Gd := Gd) by_simp_all
    by_omega).mono le_rfl ?_
  zuczf
  rw [v1D] at hres
  refine ⟨hres, EFr.trans ⟨fun r h1 h2 h3 => k1 r ?_ ?_ ?_, by zvnhf, fun a _ => by zvmxz⟩
    (hfr.mono fun r hr => Or.inr hr)⟩
  · omega
  · omega
  omega
theorem m2c_M2R_lh' (h : ztkdk ∨ LHSW r2F r) : M2R r := by
  zuy
  · exact m2c_M2R_set h
  · exact m2c_M2R_lh h
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}
theorem m2c_regs {r : ℕ} (h : r = m2F ∨ r = m2F + 1 ∨ r = m2F + 2 ∨ r = r2F) : M2R r := by
  rcases h with rfl | rfl | rfl | rfl
  · tauto
  · tauto
  · tauto
  tauto
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **Shared and top codes.** -/
theorem m2cS_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hM : MCtx P W J.right N₂ ztbmp gMD2 gCD2 ztbz c)
    (hD : OrgD P J N₂ ztka ztij ztfb)
    (hpos : OrgPos P J N₂ ztka ztij ztfb ztdzo ztdzp)
    (hk : c.nreg oKd ≠ 1)
    (hroom : c.nreg ALLOC + m2cK ztdg ztwiu zto ≤ W) :
    IRS P W c₀ ztvyp c (m2cK ztdg ztwiu zto)
      ztwlw := by
  zudvr

  obtain ⟨-, ha2, hay, haR, -⟩ := stOrig_facts E.hP E.hNF₂ hok
  have haR' := haR hk
  zufuj
  zullw
  obtain ⟨hpe, hpp, -, hpt, -, -⟩ := hpos
  zukbc
  have noArr : FreeAt J.right a ztwow → ∃ p t,
      Arrival (chainModel J.right).W a ztxtx p t :=
    fun hf => arrival_of_freeC J.right E.hP hσ (Or.inl haR') hf
  unfold m2cS m2cK
  unfold m2cK at hroom
  -- 1. the arrival position
  refine IRS.seq (callArr_irs (dsc := sw 21) (re := oPE) (rh := oPH) (rd := oB) (o := m2F)
    (C := J.right) hI ztpxh
    ⟨by_decide, by_decide, by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide⟩
    ⟨by_decide, by_decide⟩ hpe hpp by_simp_all by_omega) ?_
  rintro c₁ hI₁ - hA₁' ⟨hArr, k1, hA1, hm1⟩
  have k1' : ∀ r, bandOf r ∉ oracleBands → ¬ M2R r → r ≠ ALLOC → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => k1 r h1 (fun e => h2 (m2c_regs ztccj))
      (fun e => h2 (m2c_regs ztxgj)) (fun e => h2 (m2c_regs (Or.inr (Or.inr
        ztccj)))) h3
  have kq : ∀ q, (sw 4000 ≤ q ∧ q < sw 4024) ∨ (sw 0 ≤ q ∧ q < sw 700) → c₁.nreg q = c.nreg q :=
    fun q hq => k1' q (not_oracle_sw zteqr zteqr)
      (by unfold M2R; unfold sw at hq ⊢; omega) (by unfold ALLOC; unfold sw at hq; omega)
  have eB : ztmvh := kq _ ztwos
  have hK1 : ztcpf := (E.hK.fix hI₁).2.1
  have hM₁ : ztygn :=
    MCtx.transport hM (fun r hr => by
      zukx
      · zulze
      · zulze
      · zulzf
      · zulzf
      · exact kq _ ztxcg) hm1 hA1
  have efr1 : EFr M2R c c₁ := ⟨k1', hA1, hm1⟩
  obtain ⟨hf1, hf2, hf3⟩ := hArr
  zvmxe at hf2 hf3
  by_cases hfl : c₁.nreg m2F < c₁.nreg K1
  · -- no arrival: the empty result
    zuksq
    have hne : c₁.nreg m2F ≠ 1 := by_omega
    have hnf : ¬ FreeAt J.right a ztwow := fun hf => by
      grind
    refine (IRS.ifT by_omega (IRS.reg (r := r2F) (v := 0) hI₁
      ztbua
      (Exec.constN hI₁.hw r2F 0 ztbg))).mono by_omega ?_
    rintro c₂ rfl
    refine ⟨⟨⟨?_, fun h => ?_, fun hg => absurd hg hnf⟩, fun _ hg => absurd hg hnf⟩,
      EFr.trans efr1 ⟨fun r h1 h2 h3 => ?_, le_of_eq ?_, fun _ _ => rfl⟩⟩
    · simp
    · tauto
    · show upd c₁.nreg r2F 0 r = c₁.nreg r
      rw [upd_other _ _ _ (fun e => h2 (m2c_regs (Or.inr ztgei)))]
    rfl
  · -- the local hit from the arrival
    zuksq
    have h1 : c₁.nreg m2F = 1 := by_omega
    obtain ⟨hpe2, hpp2, harr⟩ := hf2 h1
    set x : WPos := ⟨c₁.nreg pE2, c₁.nreg pH2⟩ with hx
    have hxa : (chainModel J.right).pos zta x = a := harr.2.2.2.1
    have hsl : sideLeft (chainModel J.right).W (c₁.nreg pE2)
        ((chainModel J.right).param zta x)
        (rayPt ((chainModel J.right).pos zta x) (dirOf (c₁.nreg oB)) 1) := by
      have := harr.2.2.2.2
      zukxx
      rw [hxa, eB]; tauto
    refine (IRS.ifF by_omega (m2c_lh_irs E hI₁ hM₁ (e := pE2) (h := pH2)
      ⟨by_decide, by_decide⟩ by_decide by_omega
      hpe2 hpp2
      (posClass_of hpe2 hpp2.1 hpp2.2.1 by_grind ztzz)
      by_grind ztzz
      (Gd := FreeAt J.right a ztwow)
      (fun _ => ⟨hsl, by_grind⟩) by_omega)).mono le_rfl ?_
    rintro c₂ ⟨hres, hfr⟩
    rw [hxa, eB] at hres
    have k2 : ∀ q, q = pE2 ∨ q = pH2 → c₂.nreg q = c₁.nreg q := by
      zuco
      refine hfr.1 q (not_oracle_sw (by rcases hq with rfl | rfl <;> zuobu)
        (by rcases hq with rfl | rfl <;> zuobu)) ?_
        (by rcases hq with rfl | rfl <;> simp [pE2, pH2, ALLOC, sw])
      zunp
      · rcases hq with rfl | rfl <;> rcases h with h | h | h <;>
          simp [pE2, pH2, lE, lH, lD, sw] at h
      · rcases hq with rfl | rfl <;> rcases h with (h | h) | h <;>
          simp [pE2, pH2, r2F, sw] at h
    refine ⟨⟨hres, fun _ _ => ⟨by rw [k2 pE2 ztp]; tauto,
      by zunua; tauto,
      by zunua; tauto⟩⟩,
      EFr.trans efr1 (hfr.mono fun r hr => m2c_M2R_lh' hr)⟩
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **Wall codes.** -/
theorem m2cW_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hM : MCtx P W J.right N₂ ztbmp gMD2 gCD2 ztbz c)
    (hD : OrgD P J N₂ ztka ztij ztfb)
    (hpos : OrgPos P J N₂ ztka ztij ztfb ztdzo ztdzp)
    (hk : c.nreg oKd = 1)
    (hroom : c.nreg ALLOC +
      (3 + ztbajp) ≤ W) :
    IRS P W c₀ (m2cW sh) c
      (3 + ztbajp)
      ztwlw := by
  zudvr

  obtain ⟨-, ha2, hay, -, hax⟩ := stOrig_facts E.hP E.hNF₂ hok
  zufuj
  have hkk : ztuow := (hok.2.2.1 hk).1
  obtain ⟨hpe, hpp, hcl, hpt, -, hend⟩ := hpos
  have hxe : (zteyc : WPos) = endPos N₂ ztij ztcce := hend hk
  zukbc
  have hsl := m2c_wall_left E.hNF₂ hkk hb
  rw [← hxe] at hsl
  unfold m2cW
  refine (m2c_lh_irs E hI hM (e := oPE) (h := oPH) ztkp
    by_decide hb hpe hpp hcl by_simp_all
    (Or.inr (by zvmxe; tauto)) (Gd := FreeAt J.right a ztwow)
    (fun _ => ⟨hsl, by_simp_all⟩) hroom).mono le_rfl ?_
  zuczf
  zvmxe at hres
  exact ⟨⟨hres, fun h => absurd hk h⟩, hfr.mono fun r hr => m2c_M2R_lh' hr⟩
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **Task M2: the candidate of `C₂`.** -/
theorem m2Task : M2Task := by
  refine ⟨m2c, fun D => κGen D + 40000, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hM hD hpos hroom
  have hK := m2cK_le ztdg ztwiu zto
  have hK1 : ztfdp := (E.hK.fix hI).2.1
  have hr : c.nreg ALLOC + (m2cK ztdg ztwiu zto + 4) ≤ W :=
    le_trans (Nat.add_le_add_left hK _) hroom
  have hr' : c.nreg ALLOC + m2cK ztdg ztwiu zto ≤ W :=
    le_trans ztzuk hr
  unfold m2c
  zuhsj
  · refine (IRS.ifT h0 ztmmj).mono ?_
      ztb
    grind
  · have hin : IRS P W c₀ ztjdf c
        (m2cK ztdg ztwiu zto + 2)
        ztwlw := by
      zuhsq
      · exact IRS.ifT (K := m2cK ztdg ztwiu zto) h2
          ztmmj
      · zukcx
        have hle : 3 + ztbajp ≤
            m2cK ztdg ztwiu zto := by
          unfold m2cK; omega
        exact (IRS.ifF (K := m2cK ztdg ztwiu zto) h2
          ((m2cW_irs E hI hM hD hpos hk1 (le_trans zttaq hr')).mono hle
            ztb))
    refine (IRS.ifF h0 hin).mono ?_ ztb
    omega
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
def wC1 : ℕ := sw 4096
def wC2 : ℕ := sw 4097
def wBit : ℕ := sw 4047
def wnE : ℕ := sw 4048
def wnH : ℕ := sw 4049

/-- Compare the two candidates (the nearer along the ray). -/
def winCmp : Stmt :=
  .seq (callAbsCmp ztkdq ztogs wC1) (.seq (callAbsCmp ztogs ztkdq wC2)
    (.ifLtN K0 oB (.instr (.copyN wBit wC1)) (.instr (.copyN wBit wC2))))

/-- Select the candidate: `wBit = 1` for the candidate of `C₁`. -/
def winSel : Stmt := .ifLtN K0 r1F winCmp (.instr (.constN wBit 0))

/-- Its position in the walk of `C`. -/
def winConv : Stmt :=
  .ifLtN K0 wBit (.seq (convS ztbca ztna ztkdp wnE) (.instr (.copyN wnH ztogr)))
    (.seq (convS ztfg zthy zttyd wnE) (.instr (.copyN wnH zttye)))

/-- **The far end and its attachment.** -/
def stWin : Stmt := .seq winSel (.seq winConv (callArr ztjl wnE wnH oNB a1F))

/-- The registers `stWin` writes (besides the oracle bands). -/
def WinR (r : ℕ) : Prop :=
  ztgz ∨ ztph ∨ ztltw ∨
    ztltz

/-! ## The comparison -/

/-- The order of the abscissas along the ray. -/
theorem ray_lt_iff {a : Point} {b : ℕ} (hb : b ≤ 1) {τ₁ τ₂ : ℝ} :
    (if b = 1 then (rayPt a ztkz τ₁).1 < (rayPt a ztkz τ₂).1
      else (rayPt a ztkz τ₂).1 < (rayPt a ztkz τ₁).1) ↔ τ₁ < τ₂ := by
  zubhr
  · rw [ite_eq_right by_norm_num, rayPt_fst, rayPt_fst, dirOf_zero]
    grind
  · rw [ite_eq_left rfl, rayPt_fst, rayPt_fst, dirOf_one]
    simp
theorem winCmp_irs (hI : IInv W c₀ c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (hK : Consts c)
    {b : ℕ} (hb : b ≤ 1) (hB : c.nreg oB = b) {x₁ x₂ R : ℝ} (h₁ : AbsRec P c ztkdq x₁ R)
    (h₂ : AbsRec P c ztogs x₂ R) (hroom : c.nreg ALLOC + 600 ≤ W) :
    IRS P W c₀ winCmp c 541 (fun c' => c'.nreg wBit ≤ 1 ∧
      (c'.nreg wBit = 1 ↔ (if b = 1 then x₁ < x₂ else x₂ < x₁)) ∧
      EFr ztdoc c c') := by
  unfold winCmp
  refine IRS.seq (K₂ := 272) (callAbsCmp_irs hI hG hW
    ⟨by_decide, by_decide, by_decide,
      by decide⟩ ⟨by_decide, by_decide⟩ h₁ h₂
    by_omega) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨hb1, k1, -, m1⟩
  have kr := fun r h1 h2 h3 =>
    k1 r ztsg h3 ztu
  have h₁' : AbsRec P c₁ _ x₁ R := absRec_transport h₁
    ztcis
    ztcis
    ztcis
    ztcis
  have h₂' : AbsRec P c₁ _ x₂ R := absRec_transport h₂
    ztcis
    ztcis
    ztcis
    ztcis
  refine IRS.seq (K₂ := 3) (callAbsCmp_irs hI₁ hG hW
    ⟨by_decide, by_decide, by_decide,
      by decide⟩ ⟨by_decide, by_decide⟩ h₂' h₁'
    by_omega) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hb2, k2, -, m2⟩
  have kr2 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ wC1 → r ≠ wC2 → c₂.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 => (k2 r ztsg h4 ztu).trans
      by_grind
  have c2B : ztpnm := by
    rw [kr2 _ by_decide by_decide by_decide
      by_decide, hB]
  have c2K0 : ztpnk := by
    rw [kr2 _ by_decide by_decide by_decide
      by_decide]; exact hK.1
  have c2C1 : c₂.nreg wC1 = c₁.nreg wC1 :=
    k2 _ ztmr
      by_decide by_decide
  have fr : ∀ c', (∀ q, q ≠ wBit → c'.nreg q = c₂.nreg q) →
      c'.nmem = c₂.nmem → EFr ztdoc c c' := by
    intro c' hq hm
    refine ⟨fun r hr hX hra => ?_, ?_, fun a ha => ?_⟩
    · grind
    · rw [hq _ by_decide]; omega
    grind
  zura
  · have hb1' : ztplm := by_omega
    zuhiu
    zuvo
    refine ⟨by rw [a1, c2C1]; exact hb1.1, ?_, by_grind⟩
    rw [a1, c2C1, ite_eq_left hb1']; exact hb1.2
  · have hb0 : b ≠ 1 := by_omega
    zuhiu
    zuvo
    refine ⟨by rw [a1]; exact hb2.1, ?_, by_grind⟩
    rw [a1, ite_eq_right hb0]; exact hb2.2

/-! ## The selected position -/
theorem dirOf_rev' {b : ℕ} (hb : b ≤ 1) : dirOf ztlp = -dirOf b := by
  zubhr
  · rw [show 1 - 0 = 1 from rfl, dirOf_one, dirOf_zero]; norm_num
  rfl

/-- A candidate position: of the class of `convS`, its point on the chain or on a wall. -/
theorem winPos {C : Chain} {Q : Polygon} {n : ℕ} {a : Point} {σ τ : ℝ} {x : WPos}
    (he : x.edge < (chainModel C).W.n) (hpp : ProperPos ztc Q n x)
    (hpos : (chainModel C).pos Q x = rayPt a σ τ) (hon : OnCB C ztiu)
    (hy : |a.2| < C.radius) :
    PosClass C Q x ∧ (rayPt a σ τ ∈ C.set ∨
      (|(rayPt a σ τ).1| = C.radius ∧ |(rayPt a σ τ).2| < C.radius)) := by
  have hy' : |((chainModel C).pos Q x).2| < C.radius := by_simp_all
  zuied
  · refine ⟨posClass_of he hpp.1 hpp.2.1 hy' ztenp, Or.inl h⟩
    zvnbl; exact C.snd_le_top_of_mem_set h
  · refine ⟨posClass_of he hpp.1 hpp.2.1 hy' by_simp_all, Or.inr ztcxz⟩
    simp_all
  simp_all

/-- **The selected position in the walk of `C`.** -/
theorem winConv_irs {J : Merge.Junction} (hP : J.P.Simple) (hI : IInv W c₀ c) (hK : Consts c₀)
    (hfx : Fx P W J c) (hW : (chainModel J.whole).W.n ≤ W) {Z : Point}
    (h1 : c.nreg wBit = 1 → c.nreg ztkdp < (chainModel J.left).W.n ∧
      ProperPos ztbw zta P.n ztbqz ∧
      PosClass J.left zta ztbqz ∧
      (chainModel J.left).pos zta ztbqz = Z)
    (h0 : c.nreg wBit ≠ 1 → c.nreg zttyd < (chainModel J.right).W.n ∧
      ProperPos ztj zta P.n ztdxf ∧
      PosClass J.right zta ztdxf ∧
      (chainModel J.right).pos zta ztdxf = Z)
    (hK0 : c.nreg K0 = 0) (hb : c.nreg wBit ≤ 1) :
    IRS P W c₀ winConv c 25 (fun c' => c'.nreg wnE < (chainModel J.whole).W.n ∧
      ProperPos ztbm zta P.n ztrbb ∧
      (chainModel J.whole).pos zta ztrbb = Z ∧
      (∀ r, ¬ CvSet wnE r → r ≠ wnH → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  unfold winConv
  zura
  · have hw : c.nreg wBit = 1 := by_omega
    obtain ⟨a1, a2, a3, a4⟩ := h1 hw
    refine IRS.seq (K₂ := 1) (convL_irs hP hI hK hfx
      ⟨by_decide, by_decide, by_decide,
        by decide⟩
      ⟨iscr_sw by_decide by_decide, by_decide,
        by decide, by_decide⟩ a3 hW) ?_
    zuui

    have eH : c'.nreg wnH = c.nreg ztogr := by
      rw [b1, k1 _ (by unfold CvSet wnE cX cT cDd r1F sw; omega)]
    refine zticf
    · zuihp

    simp_all
  · have hw : c.nreg wBit ≠ 1 := by_omega
    obtain ⟨a1, a2, a3, a4⟩ := h0 hw
    refine IRS.seq (K₂ := 1) (convR_irs hP hI hK hfx
      ⟨by_decide, by_decide, by_decide,
        by decide⟩
      ⟨iscr_sw by_decide by_decide, by_decide,
        by decide, by_decide⟩ a3 hW) ?_
    zuui

    have eH : c'.nreg wnH = c.nreg zttye := by
      rw [b1, k1 _ (by unfold CvSet wnE cX cT cDd r2F sw; omega)]
    refine zticf
    · zuihp

    simp_all

/-! ## The far end and its attachment -/
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}
set_option maxHeartbeats 1000000 in
/-- **The far end of the stop chord and its attachment `A₁`.** -/
theorem stWin_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {kind k b : ℕ}
    (hD : OrgD P J N₂ kind k b) (hB : c.nreg oB = b) (hNB : c.nreg oNB = 1 - b)
    (h1 : ResOK P J.left ztwme ztkz
      (FreeAt J.left ztwme ztkz ∧
        (stOrig J zta N₂ kind k b).2 ≤ J.left.top.2) r1F c)
    (h2 : ResOK P J.right ztwme ztkz
      (FreeAt J.right ztwme ztkz) r2F c)
    (hroom : c.nreg ALLOC + 35600 ≤ W) :
    IRS P W c₀ stWin c 35600 (fun c' => c'.nreg ztlq < (chainModel J.whole).W.n ∧
      ProperPos ztbm zta P.n ztzif ∧
      Arrival (chainModel J.whole).W (farPt J.whole ztwme ztkz)
        ztkz (c'.nreg ztlq)
        ((chainModel J.whole).param zta ztzif) ∧
      EFr WinR c c') := by
  zubns
  have hb := hD.ok.2.1
  zullv
  obtain ⟨-, ha2, hay, -, -⟩ := stOrig_facts hP E.hNF₂ hD.ok
  zufpe
  set σ := dirOf b with hσdef
  have hf : FreeAt J.whole a σ := hD.free
  have hf2 := free_right hf ha2
  zuiw
  -- the candidate of `C₂`
  obtain ⟨τ₂, t2p, t2on, t2e, t2pp, t2pos, t2abs, t2g⟩ := h2.2.1 (h2.2.2 hf2)
  have t2h := t2g hf2
  obtain ⟨t2cl, t2z⟩ := winPos t2e t2pp t2pos t2on hay
  have hGood1 := h1.2.2
  -- the far end is on `C` or a wall
  have hZ : farPt J.whole a σ ∈ J.whole.set ∨
      (|(farPt J.whole a σ).1| = J.whole.radius ∧ |(farPt J.whole a σ).2| < J.whole.radius) := by
    rcases hit_cases ha2 hσ with hh | ⟨hl, hh⟩
    · unfold farPt; rw [hh, ← t2h]
      rcases t2z with z | z
      · exact Or.inl (J.right_set_subset z)
      · exact Or.inr z
    · have g1 : FreeAt J.left a σ ∧ a.2 ≤ J.left.top.2 := ztrcj
      obtain ⟨τ₁, t1p, t1on, t1e, t1pp, t1pos, -, t1g⟩ := h1.2.1 (hGood1 g1)
      obtain ⟨-, t1z⟩ := winPos t1e t1pp t1pos t1on hay
      unfold farPt; rw [hh, ← t1g g1]
      rcases t1z with z | z
      · exact Or.inl (J.left_set_subset z)
      · exact Or.inr z
  unfold stWin
  -- the selection
  have hsel : IRS P W c₀ winSel c 543 (fun c₁ => c₁.nreg wBit ≤ 1 ∧
      (c₁.nreg wBit = 1 → ∃ τ₁, 0 < τ₁ ∧ OnCB J.left ztruy ∧
        c.nreg ztkdp < (chainModel J.left).W.n ∧
        ProperPos ztbw zta P.n ztbqz ∧
        (chainModel J.left).pos zta ztbqz = rayPt a σ τ₁ ∧
        τ₁ = J.whole.hitParam a σ) ∧
      (c₁.nreg wBit ≠ 1 → τ₂ = J.whole.hitParam a σ) ∧
      EFr ztdoc c c₁) := by
    unfold winSel
    zura
    · have hf1 : c.nreg r1F = 1 := by have := h1.1; omega
      obtain ⟨τ₁, t1p, t1on, t1e, t1pp, t1pos, t1abs, t1g⟩ := h1.2.1 hf1
      refine (winCmp_irs hI E.hG (by have := E.hWh; unfold hostWords at this; omega) hK hb hB
        t1abs t2abs by_omega).mono by_norm_num ?_
      zuhjs
      rw [ray_lt_iff hb] at w2
      refine ⟨w1, fun hw => ⟨τ₁, t1p, t1on, t1e, t1pp, t1pos, ?_⟩, fun hw => ?_, w3⟩
      · have hlt := w2.1 hw
        exact win_min ha2 hσ hf t1p t1on t1g t2p t2on t2h ztp le_rfl hlt.le
      · have hle : τ₂ ≤ τ₁ := by_simp_all
        exact win_min ha2 hσ hf t1p t1on t1g t2p t2on t2h ztbt hle le_rfl
    · have hf0 : c.nreg r1F ≠ 1 := by rw [hK.1] at h; omega
      refine (set1_irs hI ztkp
        ztbg).mono by_norm_num ?_
      zuhjs
      refine ⟨by_omega, by_simp_all,
        fun _ => win_only2 ha2 hσ hf by_simp_all t2h, ?_⟩
      refine ⟨by_simp_all, ?_, by_simp_all⟩
      zukzb
  refine IRS.seq (K₂ := 25 + 35007) hsel ?_ |>.mono by_norm_num ztb
  rintro c₁ hI₁ - hA₁ ⟨s1, s2, s3, s4⟩
  have k1 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ wC1 → r ≠ wC2 → r ≠ wBit → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 h5 => s4.1 r ztsg by_tauto ztu
  have kreg : ∀ i, i < 3 → c₁.nreg _ = c.nreg zttyc ∧
      c₁.nreg _ = c.nreg (r2F + i) := fun i hi =>
    ⟨k1 _ ztozt ztozt (by unfold r1F wC1 sw; omega)
      (by unfold r1F wC2 sw; omega) (by unfold r1F wBit sw; omega),
     k1 _ ztozu ztozu (by unfold r2F wC1 sw; omega)
      (by unfold r2F wC2 sw; omega) (by unfold r2F wBit sw; omega)⟩
  have hyL := hay
  have hfar : farPt J.whole a σ = rayPt a σ _ := rfl
  have hc1 : zteib := by
    rw [k1 _ by_decide by_decide by_decide
      by_decide by_decide]; exact hK.1
  have hconv := winConv_irs (Z := farPt J.whole a σ) hP hI₁ E.hK ztpxk
    (by have := E.hWn; omega)
    (fun hw => by
      obtain ⟨τ₁, t1p, t1on, t1e, t1pp, t1pos, t1h⟩ := s2 hw
      obtain ⟨t1cl, -⟩ := winPos t1e t1pp t1pos t1on hyL
      rw [(kreg 1 by_norm_num).1, (kreg 2 by_norm_num).1]
      grind)
    (fun hw => by
      rw [(kreg 1 by_norm_num).2, (kreg 2 by_norm_num).2]
      grind) hc1 s1
  refine IRS.seq hconv ?_
  rintro c₂ hI₂ - hA₂ ⟨v1, v2, v3, k2, m2⟩
  have hfx₂ := E.fx hI₂
  have kA : zteic := k2 _ (by unfold CvSet wnE cX cT cDd ALLOC sw; omega)
    by_decide
  have c2NB : ztrgl := by
    rw [k2 _ (by unfold CvSet wnE cX cT cDd oNB sw; omega) by_decide,
      k1 _ by_decide by_decide by_decide
        by_decide by_decide, hNB]
  have hyZ : |((chainModel J.whole).pos zta ⟨c₂.nreg wnE, c₂.nreg wnH⟩).2| < J.whole.radius := by
    rw [v3, hfar, rayPt_snd]; omega
  refine (callArr_irs hI₂ hfx₂.ctxW ⟨by_decide, by_decide,
    by decide, by_decide, by_decide,
    by decide, by_decide, by_decide⟩
    ⟨by_decide, by_decide⟩ v1 v2 hyZ by_omega).mono le_rfl ?_
  rintro c' ⟨⟨f1, f2, f3⟩, k3, hA3, m3⟩
  rw [v3, c2NB, dirOf_rev' hb, neg_neg] at f2 f3
  have hσ' := SweepStop.neg_cases hσ
  have hfb := far_free J.whole (le_trans ha2 J.right_top_le) hσ hf
  have hexist := (freeAt_iff_arr J.whole hP hσ' hZ).1 hfb
  rw [neg_neg] at hexist
  have hf1 : c'.nreg a1F = 1 := by
    zuct
    obtain ⟨p, t, hA⟩ := hexist
    grind
  obtain ⟨e1, e2, e3⟩ := f2 hf1
  refine ⟨e1, e2, e3, fun r hr hX hra => ?_, ?_, fun x hx => ?_⟩
  · have hX' : ¬ (ztgz ∨ ztph ∨
      ztltw ∨ ztltz) := hX
    rw [k3 r hr ztggq ztggq
      ztggq hra,
      k2 r (by unfold CvSet wnE cX cT cDd sw at *; omega) (by unfold wnH sw at *; omega),
      s4.1 r hr (by unfold wC1 wC2 wBit sw at *; omega) hra]
  · have := s4.2.1; omega
  · rw [m3 x (by have := s4.2.1; omega), m2, s4.2.2 x hx]
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **The per-origin step.** -/
def orgProg (m2 m1 : Stmt → Stmt) (fin : Stmt) (sh : Stmt) : Stmt :=
  .seq stLoad (.ifLtN K0 oAd (.seq stA (.ifLtN K0 oF0
    ztgbr .skip)) .skip)

/-- A register outside the frame of a step is kept. -/
theorem EFr.keep {X : ℕ → Prop} {c c' : Config} (h : EFr X c c') {r : ℕ} (h1 : 240000 ≤ r)
    (h2 : r < 250000) (hX : ¬ X r) (hA : r ≠ ALLOC) : c'.nreg r = c.nreg r :=
  h.1 r ztsg hX hA

/-- **`OrgOut` lifts** over a prefix keeping the raw array, the memory and the registers outside
`SOrgR`. -/
theorem OrgOut.lift {J : Merge.Junction} {N : NF} {kind k b : ℕ} {c₁ c' : Config}
    (h : OrgOut P J N kind k b c₁ c') (hC : c₁.nreg gRC = c.nreg gRC)
    (hB : c₁.nreg gRB = c.nreg gRB) (hA : c.nreg ALLOC ≤ c₁.nreg ALLOC)
    (hm : ∀ a, a < c.nreg ALLOC → c₁.nmem a = c.nmem a)
    (hr : ∀ r, bandOf r ∉ oracleBands → ¬ SOrgR r → r ≠ ALLOC → c₁.nreg r = c.nreg r) :
    OrgOut P J N kind k b c c' := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := h
  rw [hC, hB] at *
  refine ⟨o1, o2, o3, o4, fun a ha hs => ?_, by_omega, fun r h1 h2 h3 => ?_⟩
  · grind
  simp_all

/-- **`OrgOut` without records**: for a code that is not admissible or not free. -/
theorem OrgOut.none {J : Merge.Junction} {N : NF} {kind k b : ℕ} {c' : Config}
    (hD : ¬ OrgD P J N kind k b) (hC : c'.nreg gRC = c.nreg gRC)
    (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)
    (hr : ∀ r, bandOf r ∉ oracleBands → ¬ SOrgR r → r ≠ ALLOC → c'.nreg r = c.nreg r) :
    OrgOut P J N kind k b c c' := by
  refine ⟨by rw [hC], by_omega, by_simp_all,
    by simp_all, by_simp_all, hA, hr⟩

/-! ## The specifications of the pieces -/
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

/-- The body of `M2Task`. -/
def M2Spec (m2 : Stmt → Stmt) (κ : ℕ → ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      MCtx P W J.right N₂ ztbmp gMD2 gCD2 ztbz c →
      OrgD P J N₂ ztka ztij ztfb →
      OrgPos P J N₂ ztka ztij ztfb ztdzo ztdzp →
      c.nreg ALLOC + κ zto * ztwit ≤ W →
      IRS P W c₀ ztvyo c ztbajz
        ztwlw

/-- The body of `M1Task`. -/
def M1Spec (m1 : Stmt → Stmt) (κ : ℕ → ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      OrgD P J N₂ ztka ztij ztfb →
      OrgPos P J N₂ ztka ztij ztfb ztdzo ztdzp →
      c.nreg ALLOC + κ zto * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ ztvyl c (κ zto * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))
        (fun c' => ResOK P J.left ztwmw
          ztwow
          (FreeAt J.left ztwmw
              ztwow ∧
            (stOrig J zta N₂ ztka ztij ztfb).2 ≤ J.left.top.2)
          r1F c' ∧ EFr M1R c c')

/-- The body of `FinTask`. -/
def FinSpec (fin : Stmt) (κ : ℕ → ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      OrgD P J N₂ ztka ztij ztfb →
      FinPre P J N₂ ztka ztij ztfb c →
      c₀.nreg ALLOC ≤ c.nreg gRB → c.nreg gRB + 11 * ztees ≤ c.nreg ALLOC →
      c.nreg ALLOC + κ zto * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ fin c (κ zto * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))
        ztwrn

/-! ## The main path -/
set_option maxHeartbeats 2000000 in
/-- **The main path** of the per-origin step: the candidates, the far end, the finish. -/
theorem orgMain_irs {m2 m1 : Stmt → Stmt} {fin : Stmt} {κ2 κ1 κF : ℕ → ℕ}
    (H2 : M2Spec m2 κ2) (H1 : M1Spec m1 κ1) (HF : FinSpec fin κF)
    (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hM : MCtx P W J.right N₂ ztbmp gMD2 gCD2 ztbz c)
    (hD : OrgD P J N₂ ztka ztij ztfb)
    (hpos : OrgPos P J N₂ ztka ztij ztfb ztdzo ztdzp)
    (hNB : c.nreg oNB = 1 - c.nreg oB)
    (hA0 : c.nreg ztjf < (chainModel J.whole).W.n ∧
      ProperPos ztbm zta P.n ztwvh ∧
      Arrival (chainModel J.whole).W ztwmw
        ztxtx ztyis
        ztbalc)
    (hR0 : c₀.nreg ALLOC ≤ c.nreg gRB) (hR1 : c.nreg gRB + 11 * ztees ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + (κ2 zto * ztwit +
      (κ1 zto * ztbqh *
        ztwit + (35600 + κF zto *
        ztbqh *
        ztwit))) ≤ W) :
    IRS P W c₀ ztgbr c
      (κ2 zto * ztwit +
      (κ1 zto * ztbqh *
        ztwit + (35600 + κF zto *
        ztbqh *
        ztwit)))
      ztwrn := by
  set kind := c.nreg oKd with hkind
  set k := c.nreg oKk with hk
  set b := c.nreg oB with hb
  set a := stOrig J _ N₂ kind k b with ha
  obtain ⟨-, ha2, -, -, -⟩ := stOrig_facts E.hP E.hNF₂ hD.ok
  -- 1. the candidate of `C₂`
  refine IRS.seq (H2 sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hM hD hpos by_omega) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨⟨r2, par2⟩, fr2⟩
  have e2 : ∀ r, 240000 ≤ r → r < 250000 → ¬ M2R r → r ≠ ALLOC → c₂.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 => fr2.keep h1 h2 h3 h4
  have n2 : ∀ r, sw 4010 ≤ r → r ≤ sw 4023 → c₂.nreg r = c.nreg r := fun r h1 h2 =>
    e2 r zteo zteo ztmeo
      ztum
  have c2Kd : zturs := n2 _ by_rfl by_decide
  have c2Kk : zturt := n2 _ by_decide by_decide
  have c2B : ztpnm := n2 _ by_decide by_decide
  have c2PE : c₂.nreg oPE = c.nreg oPE := n2 _ by_decide by_decide
  have c2PH : c₂.nreg oPH = c.nreg oPH := n2 _ by_decide by_decide
  have hD₂ : zthoh := by
    grind
  have hpos₂ : OrgPos P J N₂ ztvnc ztvnd ztvnb ztvne
      ztvnf := by_grind
  -- 2. the candidate of `C₁`
  refine IRS.seq ((H1 sh Bs F X Ok P W c₀ c₂ J N₁ N₂ E hI₂ hD₂ hpos₂ by_grind).mono
    by_grind ztb) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨r1, fr3⟩
  rw [c2Kd, c2Kk, c2B] at r1
  have e3 : ∀ r, 240000 ≤ r → r < 250000 → ¬ M1R r → r ≠ ALLOC → c₃.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 h4 => fr3.keep h1 h2 h3 h4
  have n3 : ∀ r, (sw 4010 ≤ r ∧ r ≤ sw 4026) ∨ ztltv →
      c₃.nreg r = c₂.nreg r := fun r h =>
    e3 r zteo zteo ztmen
      ztum
  have c3B : ztusp := by rw [n3 _ ztwos, c2B]
  have c3NB : c₃.nreg oNB = 1 - b := by
    rw [n3 _ ztwos,
      n2 _ by_decide by_decide, hNB]
  have r2' :=
    r2.transport fun i hi => n3 _ (Or.inr ⟨by unfold r2F sw; omega, by unfold r2F sw; omega⟩)
  -- 3. the far end
  refine IRS.seq (stWin_irs E hI₃ hD c3B c3NB r1 r2' by_omega) ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨w1, w2, w3, fr4⟩
  have e4 : ∀ r, 240000 ≤ r → r < 250000 → ¬ WinR r → r ≠ ALLOC → c₄.nreg r = c₃.nreg r :=
    fun r h1 h2 h3 h4 => fr4.keep h1 h2 h3 h4
  have n4 : ∀ r, sw 4000 ≤ r → r ≤ sw 4023 → c₄.nreg r = c.nreg r := by
    zucxf
    rw [e4 r zteo zteo (by unfold WinR sw at *; omega)
      ztum,
      e3 r zteo zteo ztmen
      ztum,
      e2 r zteo zteo ztmeo
      ztum]
  have c4Kd : c₄.nreg oKd = kind := n4 _ by_decide by_decide
  have c4Kk : c₄.nreg oKk = k := n4 _ by_decide by_decide
  have c4B : c₄.nreg oB = b := n4 _ by_decide by_decide
  have c4RB : c₄.nreg gRB = c.nreg gRB := n4 _ by_rfl by_decide
  have c4RC : c₄.nreg gRC = c.nreg gRC := n4 _ by_decide by_decide
  have hD₄ : OrgD P J N₂ ztvnu ztvnv ztvnt := by
    grind
  have hpre : FinPre P J N₂ ztvnu ztvnv ztvnt c₄ := by
    rw [c4Kd, c4Kk, c4B]
    have f1 : c₄.nreg _ = c.nreg ztjf :=
      n4 _ by_decide by_decide
    have f2 : c₄.nreg _ = c.nreg ztms :=
      n4 _ by_decide by_decide
    refine ⟨by_omega, by_grind, by_grind,
      w1, w2, w3, fun hk1 => ?_⟩
    have p1 : c₄.nreg pE2 = c₂.nreg pE2 := by
      rw [e4 _ by_decide by_decide (by unfold WinR pE2 sw; omega)
        by_decide,
        e3 _ by_decide by_decide (by unfold M1R pE2 sw; omega)
        by_decide]
    have p2 : c₄.nreg pH2 = c₂.nreg pH2 := by
      rw [e4 _ by_decide by_decide (by unfold WinR pH2 sw; omega)
        by_decide,
        e3 _ by_decide by_decide (by unfold M1R pH2 sw; omega)
        by_decide]
    zukyd
    exact par2 hk1 (free_right hD.free ha2)
  have hAl : c.nreg ALLOC ≤ c₄.nreg ALLOC := by_omega
  refine (HF sh Bs F X Ok P W c₀ c₄ J N₁ N₂ E hI₄ hD₄ hpre by_omega
    by_omega (by zupcy; omega)).mono (by zupcy) ?_
  intro c' hout
  rw [c4Kd, c4Kk, c4B] at hout
  refine OrgOut.lift hout c4RC c4RB hAl ztjwp ztnzk
  · rw [fr4.2.2 x by_omega, fr3.2.2 x by_omega, fr2.2.2 x hx]
  · have h2' : ¬ (ztgz ∨ r = gRC ∨ ztph ∨
      ztfuu ∨ ztbgd) := h2
    rw [fr4.1 r h1 (by unfold WinR at *; unfold sw at *; omega) h3,
      fr3.1 r h1 (by unfold M1R at *; unfold sw at *; omega) h3,
      fr2.1 r h1 (by unfold M2R at *; unfold sw at *; omega) h3]

/-! ## The per-origin step -/

/-- The cost constant of the per-origin step. -/
def κOrg (κ2 κ1 κF : ℕ → ℕ) (D : ℕ) : ℕ := 70663 + κ2 D + κ1 D + κF D
theorem org_cost_le (κ2 κ1 κF : ℕ → ℕ) (D M G : ℕ) (hM : 1 ≤ M) (hG : 1 ≤ G) :
    30 + (35029 + (κ2 D * G + ztgnd + 2) + 2) ≤
      κOrg κ2 κ1 κF D * M * G := by
  have hMG : 1 ≤ M * G := Nat.one_le_iff_ne_zero.2 zthbt
  have e : κOrg κ2 κ1 κF D * M * G =
      70663 * ztnmq + κ2 D * ztnmq + κ1 D * M * G + κF D * M * G := by
    unfold κOrg; ring
  have h2 : κ2 D * G ≤ κ2 D * ztnmq :=
    Nat.mul_le_mul_left _ by_nlinarith
  grind
set_option maxHeartbeats 2000000 in
/-- **The per-origin step** from its pieces. -/
theorem orgTask_of' (h2 : M2Task) (h1 : M1Task) (hF : FinTask) : OrgTask := by
  obtain ⟨m2, κ2, H2⟩ := h2
  obtain ⟨m1, κ1, H1⟩ := h1
  obtain ⟨fin, κF, HF⟩ := hF
  refine ⟨orgProg m2 m1 fin, κOrg κ2 κ1 κF, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hM hkd hb hk hR0 hR1 hroom
  zujmm
  set G := F _ + c₀.nreg TLR + 1 with hG
  set M := ztbqh with hMdef
  zujzn
  have hG1 : 1 ≤ G := by_omega
  have hcost := org_cost_le κ2 κ1 κF D M G hM1 hG1
  set Km := κ2 D * G + ztgnd with hKm
  zucqn

  zuiw
  unfold orgProg
  refine (IRS.seq (stLoad_irs E hI hkd hb hk (by
    omega)) ?_).mono hcost (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨⟨ld1, ld2, ld3, ld4⟩, fr1⟩
  have e1 : ∀ r, 240000 ≤ r → r < 250000 → ¬ LdW r → r ≠ ALLOC → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 => fr1.keep h1 h2 h3 h4
  have k1 : ∀ r, (sw 4000 ≤ r ∧ r ≤ sw 4012) ∨ (sw 4020 ≤ r ∧ r ≤ sw 4023) → c₁.nreg r = c.nreg r :=
    fun r h => e1 r zteo zteo
      (by unfold LdW LdW₀ oNB oPE oPH oAd tX tR sw at *; omega) ztum
  have c1Kd : ztuqv := k1 _ ztwos
  have c1Kk : ztuqw := k1 _ ztwos
  have c1B : ztuqt := k1 _ ztbaew
  have c1RB : ztsgm := k1 _ ztihm
  have c1RC : ztsgn := k1 _ ztwos
  have k1K0 : zteib := hK.1 ▸ (E.hK.fix hI₁).1
  have fr1S : ∀ r, bandOf r ∉ oracleBands → ¬ SOrgR r → r ≠ ALLOC → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => fr1.1 r h1 (fun hx => h2 (by
      unfold LdW LdW₀ oNB oPE oPH oAd tX tR at hx; unfold SOrgR; unfold sw at *; omega)) h3
  refine IRS.ite ztrqb ztrqb
  · -- an admissible code
    have hAd1 : c₁.nreg oAd = 1 := by_omega
    have hok := ld3.1 hAd1
    have hpos := ld4 hAd1
    refine IRS.seq (stA_irs E.hP E.hNF₂ hI₁ E.hK ztpxk hok c1B
      hpos.2.2.2.1 hpos.2.2.1 hpos.2.1 (by have := E.hWn; omega) by_omega) ?_
    rintro c₂ hI₂ hA₂ hA₂' ⟨f1, f2, f3, fr2⟩
    have e2 : ∀ r, 240000 ≤ r → r < 250000 → ¬ StAW r → r ≠ ALLOC → c₂.nreg r = c₁.nreg r :=
      fun r h1 h2 h3 h4 => fr2.keep h1 h2 h3 h4
    have k2 : ∀ r, sw 4000 ≤ r → r ≤ sw 4017 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
      e2 r zteo zteo
        (by unfold StAW CvSet oXE cX cT cDd oF0 sw at *; omega) ztum
    have c2Kd : zturs := by rw [k2 _ by_decide by_decide, c1Kd]
    have c2Kk : zturt := by rw [k2 _ by_decide by_decide, c1Kk]
    have c2B : ztpnm := by rw [k2 _ by_decide by_decide, c1B]
    have c2NB : ztrgl := by
      rw [k2 _ by_decide by_decide, ld1]
    have c2PE : c₂.nreg oPE = c₁.nreg oPE := k2 _ by_decide by_decide
    have c2PH : c₂.nreg oPH = c₁.nreg oPH := k2 _ by_decide by_decide
    have c2RB : ztshh := by rw [k2 _ by_rfl by_decide, c1RB]
    have c2RC : ztshi := by rw [k2 _ by_decide by_decide, c1RC]
    have k2K0 : ztpnk := hK.1 ▸ (E.hK.fix hI₂).1
    have fr2S :=
      fun r h1 h2 h3 => (fr2.1 r h1 (fun hx => h2 (by
        unfold StAW CvSet oXE cX cT cDd oF0 at hx; unfold SOrgR; unfold sw at *; omega)) h3).trans
        (fr1S r h1 h2 h3)
    have hmem2 : ztjbp := fun x hx => by
      rw [fr2.2.2 x by_omega, fr1.2.2 x hx]
    refine IRS.ite ztrqc ztrqc
    · -- a free direction
      have hF1 : c₂.nreg oF0 = 1 := by_omega
      have hDo : OrgD P J N₂ kind k b := ⟨hok, f2.1 hF1⟩
      have hM₂ : MCtx P W J.right N₂ ztbmp gMD2 gCD2 ztbz c₂ := by
        refine (hM.transport ztez fr1.2.2 fr1.2.1).transport ztez
          fr2.2.2 fr2.2.1
        · rcases hr with rfl | rfl | rfl | rfl | rfl <;>
            exact e1 _ by_decide
              by_decide
              (by simp only [LdW, LdW₀, oNB, oPE, oPH, oAd, tX, tR, gMD2, gCD2, TBR, TLR, sw]; omega)
              by_decide
        · rcases hr with rfl | rfl | rfl | rfl | rfl <;>
            exact e2 _ by_decide
              by_decide
              (by simp only [StAW, CvSet, oXE, cX, cT, cDd, oF0, gMD2, gCD2, TBR, TLR, sw]; omega)
              by_decide
      have hD₂ : zthoh := by
        grind
      have hpos₂ : OrgPos P J N₂ ztvnc ztvnd ztvnb ztvne
          ztvnf := by_grind
      have hA0 := f3 hF1
      have hmain := orgMain_irs H2 H1 HF E hI₂ hM₂ hD₂ hpos₂ by_omega
        (by rw [c2Kd, c2Kk, c2B]; omega) by_omega by_omega
        (by rw [c2Kd]; show c₂.nreg ALLOC + Km ≤ W; omega)
      rw [c2Kd, c2Kk, c2B] at hmain
      refine hmain.mono le_rfl (fun c' hout => OrgOut.lift hout c2RC c2RB by_omega hmem2 fr2S)
    · -- not free
      have hF0' : c₂.nreg oF0 ≠ 1 := by_omega
      refine IRS.skip hI₂ (OrgOut.none (fun hDo => hF0' (f2.2 hDo.free)) c2RC by_omega hmem2
        fr2S)
  · -- not admissible
    have hAd0 : c₁.nreg oAd ≠ 1 := by_omega
    refine IRS.skip hI₁ (OrgOut.none (fun hDo => hAd0 (ld3.2 hDo.ok)) c1RC fr1.2.1 fr1.2.2 fr1S)
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Chain (SideAttach sidePt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Values -/
theorem strD_eq {n g e : ℕ} (hg : g < n) (he : e < n) :
    (if e < g then e + n - g else e - g) = dOf n g e := by
  zujqj
  zus
  · zuey
  · rw [show e + n - g = (e - g) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
theorem strMod_eq {n s : ℕ} (hs : s < 2 * n) : (if s < n then s else s - n) = s % n := by
  zus
  · zuclg
  · zul

/-- **Corresponding positions along the right stretch** have the same parameter. -/
theorem str_param {J : Merge.Junction} (hP : J.P.Simple) {d : ℕ} (hd : d < Lst J) (Q : Polygon)
    (h : ℕ) :
    (chainModel J.whole).param Q ⟨ztefg % (chainModel J.whole).W.n, h⟩ =
      (chainModel J.right).param Q ⟨cpA J d, h⟩ := by
  zukaf
  have hc := hS.corr d hd
  obtain ⟨h1, h2⟩ := wab_of_sidePt hc
  exact (param_pos_of_wab h1 h2 Q h).1

/-! ## One-register steps -/
theorem slfAdd_irs (hI : IInv W c₀ c) {r a b : ℕ} (hr : 240700 ≤ r ∧ r < 250000)
    (hv : c.nreg a + c.nreg b ≤ W) :
    IRS P W c₀ ztder c 1 (fun c' => c'.nreg r = c.nreg a + c.nreg b ∧
      ztbcc ∧ c'.nmem = c.nmem) := by
  refine (IRS.instr1 (i := .addN r a b) hI ztrdn).mono le_rfl ?_
  zuu
  zumkd
theorem slfSub_irs (hI : IInv W c₀ c) {r a b : ℕ} (hr : 240700 ≤ r ∧ r < 250000) :
    IRS P W c₀ ztgwy c 1 (fun c' => c'.nreg r = c.nreg a - c.nreg b ∧
      ztbcc ∧ c'.nmem = c.nmem) := by
  refine (IRS.instr1 (i := .subN r a b) hI zttpo).mono le_rfl ?_
  zuu
  zumkd

/-! ## The arithmetic of the counterpart -/
def sflN : ℕ := sw 4118
def slD' : ℕ := sw 4120
def slQ' : ℕ := sw 4121
def slA : ℕ := sw 4122
def slD1 : ℕ := sw 4123
def slQ1 : ℕ := sw 4124
def slB : ℕ := sw 4125

/-- The offset `d` of the position. -/
def slDS : Stmt :=
  .ifLtN slfSE cGW (.seq (.instr (.addN slD' slfSE zthg)) (.instr (.subN slD' slD' cGW)))
    (.instr (.subN slD' slfSE cGW))

/-- `dq` of the offset in `src`. -/
def slQS (src dst : ℕ) : Stmt :=
  .ifLtN src ztyl (.instr (.copyN dst src)) (.instr (.addN dst src ztbsz))

/-- The reduction modulo `n₂`. -/
def slModS (r : ℕ) : Stmt := .ifLtN r zthy .skip (.instr (.subN r r zthy))

/-- The positions for the faced regions. -/
def slFS : Stmt :=
  .ifLtN K0 slfSH (.seq (.instr (.copyN fqE slA)) (.instr (.copyN fqH slfSH)))
    (.seq (.instr (.copyN fqE slB)) (.instr (.constN fqH 0)))

/-- **The counterpart positions.** -/
def slAr : Stmt :=
  .seq slDS (.seq (slQS slD' slQ') (.seq (.instr (.subN slD1 slD' K1)) (.seq (slQS slD1 slQ1)
    (.seq (.instr (.addN slA ztbex slQ')) (.seq (.instr (.addN slB ztbex slQ1))
    (.seq (.instr (.addN slB slB K1)) (.seq (slModS slA) (.seq (slModS slB)
    (.seq (.instr (.copyN fpE slA)) (.seq (.instr (.copyN fpH slfSH)) slFS))))))))))

/-- The registers `slAr` writes. -/
def SlArW (q : ℕ) : Prop := ztlua ∨ (sw 4120 ≤ q ∧ q ≤ sw 4125)

/-- A step keeping the registers outside `SlArW` and the memory. -/
def SlKp (c c' : Config) : Prop := (∀ q, ¬ SlArW q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem
theorem slQS_irs (hI : IInv W c₀ c) {src dst : ℕ}
    (hdr : 240700 ≤ dst ∧ dst < 250000) (hv : c.nreg src + c.nreg ztbsz ≤ W) :
    IRS P W c₀ (slQS src dst) c 3 (fun c' =>
      c'.nreg dst = dq ztyiu ztyij ztqiz ∧
      ztedc ∧ c'.nmem = c.nmem) := by
  unfold slQS
  zura
  · refine (copy1_irs hI hdr).mono le_rfl ?_
    zuvo
    exact ztice
  · refine (slfAdd_irs hI hdr hv).mono by_norm_num ?_
    zuvo
    exact ztice
theorem slModS_irs (hI : IInv W c₀ c) {r : ℕ} (hdr : 240700 ≤ r ∧ r < 250000)
    (hs : c.nreg r < 2 * c.nreg zthy) :
    IRS P W c₀ (slModS r) c 3 (fun c' => c'.nreg r = c.nreg r % c.nreg zthy ∧
      ztbcc ∧ c'.nmem = c.nmem) := by
  unfold slModS
  zura
  · refine IRS.skip hI ztdqf
    zuclg
  · refine (slfSub_irs hI hdr).mono by_norm_num ?_
    zuvo
    refine ztkip
    rw [a1, ← strMod_eq hs, ite_eq_right h]

/-- Register disequalities of the counterpart arithmetic. -/
local macro "rne" : tactic => `(tactic| (simp only [slfSE, slfSH, slD', slQ', slA, slD1, slQ1,
  slB, fpE, fpH, fqE, fqH, cGW, K0, K1, sflN, sw, SlArW, ALLOC] at * <;> omega))
set_option maxHeartbeats 2000000 in
/-- **The counterpart positions** as a run step. -/
theorem slAr_irs (hI : IInv W c₀ c) {n g g' n₂ : ℕ} (hE : c.nreg slfSE < n)
    (hn : c.nreg zthg = n) (hg : c.nreg cGW = g) (hgn : g < n) (hg' : c.nreg ztbex = g')
    (hn2 : c.nreg zthy = n₂) (hg'n : g' < n₂) (hK0 : c.nreg K0 = 0) (hK1 : c.nreg K1 = 1)
    (hq : dq ztyiu ztyij (dOf n g ztere) < n₂)
    (hq1 : dq ztyiu ztyij ztyvv < n₂)
    (hW : 2 * n ≤ W) (hn₂n : n₂ ≤ n) (hδ : c.nreg ztbsz ≤ n₂) :
    IRS P W c₀ slAr c 26 (fun c' =>
      c'.nreg fpE = ztxgx % n₂ ∧
      c'.nreg fpH = c.nreg slfSH ∧
      c'.nreg fqE = (if c.nreg slfSH = 0 then
        (g' + (dq ztyiu ztyij ztyvv + 1)) % n₂ else
        ztxgx % n₂) ∧
      c'.nreg fqH = (if c.nreg slfSH = 0 then 0 else c.nreg slfSH) ∧ SlKp c c') := by
  set d := dOf n g ztere with hd
  set L1 := c.nreg ztyl with hL1
  set δ := c.nreg ztbsz with hδd
  zufun
  unfold slAr
  -- 1. the offset
  have s1 : IRS P W c₀ slDS c 4 (fun c' => c'.nreg slD' = d ∧
      (∀ q, q ≠ slD' → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
    unfold slDS
    zura
    · refine IRS.seq (K₂ := 1) (slfAdd_irs hI (by rne) by_omega) ?_
      zufmb
      refine (slfSub_irs hI₁ (by rne)).mono le_rfl ?_
      zuhjj
      refine ⟨?_, by_simp_all, by_simp_all⟩
      rw [b1, a1, a2 _ (by rne), hn, hg, hd, ← strD_eq hgn hE, ite_eq_left by_omega]
    · refine (slfSub_irs hI (by rne)).mono by_norm_num ?_
      zuhjj
      refine ⟨?_, b2, b3⟩
      rw [b1, hg, hd, ← strD_eq hgn hE, ite_eq_right by_omega]
  refine IRS.seq (K₂ := 22) s1 ?_
  rintro c₁ hI₁ - - ⟨v1, k1, m1⟩
  have e1 : ∀ q, ¬ SlArW q → c₁.nreg q = c.nreg q := fun q hq => k1 q (by rne)
  -- 2. `dq d`
  refine IRS.seq (K₂ := 19) (slQS_irs hI₁ (by rne)
    by_grind) ?_
  rintro c₂ hI₂ - - ⟨v2, k2, m2⟩
  rw [v1, e1 _ (by rne), e1 _ (by rne)] at v2
  have e2 : ∀ q, ¬ SlArW q → c₂.nreg q = c.nreg q := fun q hq => (k2 q (by rne)).trans by_simp_all
  -- 3. `d - 1`
  refine IRS.seq (K₂ := 18) (slfSub_irs hI₂ (by rne)) ?_
  rintro c₃ hI₃ - - ⟨v3, k3, m3⟩
  rw [k2 _ (by rne), v1, e2 _ (by rne), hK1] at v3
  have e3 : ∀ q, ¬ SlArW q → c₃.nreg q = c.nreg q := fun q hq => (k3 q (by rne)).trans by_simp_all
  have c3Q : c₃.nreg slQ' = dq L1 δ d := by rw [k3 _ (by rne), v2]
  -- 4. `dq (d - 1)`
  refine IRS.seq (K₂ := 15) (slQS_irs hI₃ (by rne)
    by_grind) ?_
  zufmc
  rw [v3, e3 _ (by rne), e3 _ (by rne)] at v4
  have e4 : ∀ q, ¬ SlArW q → c₄.nreg q = c.nreg q := fun q hq => (k4 q (by rne)).trans by_simp_all
  have c4Q : c₄.nreg slQ' = dq L1 δ d := by rw [k4 _ (by rne), c3Q]
  -- 5. the sums
  refine IRS.seq (K₂ := 14) (slfAdd_irs hI₄ (by rne)
    (by rw [e4 _ (by rne), hg', c4Q]; omega)) ?_
  rintro c₅ hI₅ - - ⟨v5, k5, m5⟩
  rw [e4 _ (by rne), hg', c4Q] at v5
  have e5 : ∀ q, ¬ SlArW q → c₅.nreg q = c.nreg q := fun q hq => (k5 q (by rne)).trans by_grind
  have c5Q1 : c₅.nreg slQ1 = dq L1 δ (d - 1) := by rw [k5 _ (by rne), v4]
  refine IRS.seq (K₂ := 13) (slfAdd_irs hI₅ (by rne)
    (by rw [e5 _ (by rne), hg', c5Q1]; omega)) ?_
  rintro c₆ hI₆ - - ⟨v6, k6, m6⟩
  rw [e5 _ (by rne), hg', c5Q1] at v6
  have e6 : ∀ q, ¬ SlArW q → c₆.nreg q = c.nreg q := fun q hq => (k6 q (by rne)).trans by_grind
  have c6A : c₆.nreg slA = g' + dq L1 δ d := by rw [k6 _ (by rne), v5]
  refine IRS.seq (K₂ := 12) (slfAdd_irs hI₆ (by rne)
    (by rw [v6, e6 _ (by rne), hK1]; omega)) ?_
  rintro c₇ hI₇ - - ⟨v7, k7, m7⟩
  rw [v6, e6 _ (by rne), hK1] at v7
  have e7 : ∀ q, ¬ SlArW q → c₇.nreg q = c.nreg q := fun q hq => (k7 q (by rne)).trans by_grind
  have c7A : c₇.nreg slA = g' + dq L1 δ d := by rw [k7 _ (by rne), c6A]
  -- 6. the reductions
  have hn2' : c₇.nreg (sw 34) = n₂ := by rw [e7 _ (by rne), hn2]
  refine IRS.seq (K₂ := 9) (slModS_irs hI₇ (by rne)
    by_omega) ?_
  rintro c₈ hI₈ - - ⟨v8, k8, m8⟩
  rw [c7A, hn2'] at v8
  have e8 : ∀ q, ¬ SlArW q → c₈.nreg q = c.nreg q := fun q hq => (k8 q (by rne)).trans by_grind
  have c8B : c₈.nreg slB = g' + dq L1 δ (d - 1) + 1 := by rw [k8 _ (by rne), v7]
  have hn2'' : c₈.nreg (sw 34) = n₂ := by rw [e8 _ (by rne), hn2]
  refine IRS.seq (K₂ := 6) (slModS_irs hI₈ (by rne)
    by_omega) ?_
  rintro c₉ hI₉ - - ⟨v9, k9, m9⟩
  rw [c8B, hn2''] at v9
  have e9 := fun q hq => (k9 q (by rne)).trans (e8 q hq)
  have c9A : c₉.nreg slA = (g' + dq L1 δ d) % n₂ := by rw [k9 _ (by rne), v8]
  -- 7. the positions
  refine IRS.seq (K₂ := 5) (copy1_irs hI₉ (by rne)) ?_
  rintro c₁₀ hI₁₀ - - ⟨v10, k10, m10⟩
  rw [c9A] at v10
  have e10 :=
    fun q hq => (k10 q (by rne)).trans (e9 q hq)
  refine IRS.seq (K₂ := 4) (copy1_irs hI₁₀ (by rne)) ?_
  rintro c₁₁ hI₁₁ - - ⟨v11, k11, m11⟩
  rw [e10 _ (by rne)] at v11
  have e11 :=
    fun q hq => (k11 q (by rne)).trans (e10 q hq)
  have c11A : c₁₁.nreg slA = ztdus % n₂ := by
    rw [k11 _ (by rne), k10 _ (by rne), c9A]
  have c11B : c₁₁.nreg slB = (g' + (dq L1 δ ztku + 1)) % n₂ := by
    rw [k11 _ (by rne), k10 _ (by rne), v9, show g' + dq L1 δ _ + 1 =
      g' + (dq L1 δ _ + 1) by ring]
  have c11E : c₁₁.nreg fpE = (g' + dq L1 δ d) % n₂ := by rw [k11 _ (by rne), v10]
  have c11H : c₁₁.nreg slfSH = c.nreg slfSH := e11 _ (by rne)
  have c11K0 : c₁₁.nreg K0 = 0 := by rw [e11 _ (by rne), hK0]
  unfold slFS
  zura
  · have hH : c.nreg slfSH ≠ 0 := by_omega
    refine IRS.seq (K₂ := 1) (copy1_irs hI₁₁ (by rne)) ?_
    rintro c₁₂ hI₁₂ - - ⟨w1, w2, w3⟩
    refine (copy1_irs hI₁₂ (by rne)).mono le_rfl ?_
    zuhjq
    refine ⟨by rw [z2 _ (by rne), w2 _ (by rne), c11E], by rw [z2 _ (by rne), w2 _ (by rne), v11],
      by rw [z2 _ (by rne), w1, c11A, ite_eq_right hH], by rw [z1, w2 _ (by rne), c11H, ite_eq_right hH],
      fun q hq => by rw [z2 q (by rne), w2 q (by rne), e11 q hq], by_grind⟩
  · have hH : c.nreg slfSH = 0 := by_omega
    refine IRS.seq (K₂ := 1) (copy1_irs hI₁₁ (by rne)) ?_
    rintro c₁₂ hI₁₂ - - ⟨w1, w2, w3⟩
    refine (set1_irs hI₁₂ (by rne) (Nat.zero_le _)).mono by_norm_num ?_
    zuhjq
    refine ⟨by rw [z2 _ (by rne), w2 _ (by rne), c11E], by rw [z2 _ (by rne), w2 _ (by rne), v11],
      by rw [z2 _ (by rne), w1, c11B, ite_eq_left hH], by_grind,
      fun q hq => by rw [z2 q (by rne), w2 q (by rne), e11 q hq], by_grind⟩
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Chain (SideAttach sidePt)
@[expose] public section
def slProg (fr : Stmt) : Stmt := .seq (normS ztjl slfSE slfSH sflN) (.seq slAr fr)
set_option maxHeartbeats 4000000 in
theorem strLabTask : StrLabTask := by
  obtain ⟨fr, κF, HF⟩ := faceRTask
  refine ⟨slProg fr, fun D => 11041 + κF D, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hE hpp hy hex h0 hL hroom
  set T := c₀.nreg TLR with hT
  zujmn
  zubns
  have hfx := E.fx hI
  zuiw
  zuhf
  zuery
  have hmm : ztmtj := rfl
  zudpu
  zubau
  set x0 : WPos := ztst with hx0
  set t := (chainModel J.whole).param zta x0 with ht
  -- 1. the normalisation
  zufqq
  have hT1 : 11041 ≤ 11041 * ztxz := Nat.le_mul_of_pos_right _ (Nat.succ_pos T)
  have hsplit : (11041 + κF D) * ztxz = 11041 * ztxz + κF D * ztxz := by_ring
  have hroom1 : c.nreg ALLOC + 11015 ≤ W := by_omega
  unfold slProg
  refine IRS.seq (K₁ := 11015) (K₂ := 26 + κF D * ztxz) (normS_irs (C := J.whole) hI hK
    hfx.ctxW ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide⟩
    ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide⟩ hE hpp (fun _ _ _ _ => hy) hroom1) ?_ |>.mono
    by_grind ztb
  rintro c₁ hI₁ hA₁ hA₁' ⟨n1, n2, n3, n4, n5⟩
  set H := nhgt ztbm zta x0 with hH
  obtain ⟨hppH, hparH, -, hH0⟩ := nhgt_facts hpp
  rw [← ht] at hparH
  rw [hparH] at hH0
  have c1E : c₁.nreg slfSE = c.nreg slfSE := n1
  have c1H : c₁.nreg slfSH = H := n2
  have k1 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ slfSH → r ≠ sflN → r ≠ sflN + 1 → r ≠ ALLOC →
      c₁.nreg r = c.nreg r := fun r h1 h2 h3 h4 h5 h6 => n3 r ztsg h3 h4 h5 h6
  have hfx₁ := E.fx hI₁
  -- the offset
  have hgn : ztboy := by unfold gW; omega
  set d := dOf (chainModel J.whole).W.n ztead ztere with hd
  have hoff : oW J (c.nreg slfSE + t) = d + t := off_key' hgn hE hpp.1 hpp.2.1
  zueye
  have hdL : d < Lst J := by
    have : (d : ℝ) < Lst J := by linarith [hpp.1]
    zufc
  have hd0 : t = 0 → d ≠ 0 := fun h0' hd0 => by rw [h0', hd0] at h0; grind
  have hEd : c.nreg slfSE = ztefg % (chainModel J.whole).W.n := (add_dOf hgn hE).symm
  have hC0 := corr_right0 J hP (S₂ := ∅) ztzi finite_empty
  have hq : dq ztns ztpg d < (chainModel J.right).W.n := hC0.dq_lt hdL
  have hq1 : dq ztns ztpg ztku < (chainModel J.right).W.n := hC0.dq_lt (show d - 1 < Lst J by omega)
  -- 2. the counterpart positions
  have g0 := hfx₁.r40 1 by_norm_num
  have g2 := hfx₁.r40 2 by_norm_num
  have g4 := hfx₁.r40 4 by_norm_num
  simp only [cstR, List.getD_cons_zero, List.getD_cons_succ] at g0 g2 g4
  have e41 : c₁.nreg ztbex = 6 + tpos J.right 0 := g0
  have e42 : c₁.nreg ztyl = rL1 J := g2
  have e44 : c₁.nreg ztbsz = rδ J := g4
  have hδ7 : rδ J ≤ 7 := by unfold rδ; split_ifs <;> omega
  zubke
  refine IRS.seq (K₁ := 26) (K₂ := κF D * ztxz) (slAr_irs (n := (chainModel J.whole).W.n)
    (g := gW J) (g' := 6 + tpos J.right 0) (n₂ := (chainModel J.right).W.n) hI₁
    by_omega (by rw [hfx₁.nw, hn]) hfx₁.gw hgn e41 (by rw [hfx₁.n2, hn₂])
    by_omega hK₁.1 hK₁.2.1 by_grind
    by_grind (by have := E.hWn; omega) by_omega
    by_omega) ?_
  rintro c₂ hI₂ - - ⟨v1, v2, v3, v4, kp⟩
  simp only [e42, e44, c1E, c1H] at v1 v2 v3 v4
  have hcpA : c₂.nreg fpE = cpA J d := v1
  have hv3 : c₂.nreg fqE = if H = 0 then cpB J d else cpA J d := v3
  have hpar : (chainModel J.right).param zta ztkkc = t := by
    rw [← str_param hP hdL, ← hEd, hparH]
  have hppA : ProperPos ztj zta P.n ztkkc :=
    ⟨by zuogq; exact hppH.1, by zuogq; exact hppH.2.1, hppH.2.2⟩
  have hcpAn : cpA J d < (chainModel J.right).W.n := Nat.mod_lt _ by_omega
  have hcpBn : cpB J d < (chainModel J.right).W.n := Nat.mod_lt _ by_omega
  have hppB : ProperPos ztj zta P.n ⟨cpB J d, 0⟩ :=
    ⟨le_refl (0 : ℝ), by_simp, Nat.zero_le _⟩
  -- the non-cut
  obtain ⟨e, he, hno, heA⟩ := hex
  have hnc : 0 < t → ¬ (chainModel J.right).IsCut ztwis
      ((chainModel J.right).key zta ztkkc) := by
    intro htp
    rw [fr_key, hpar]
    refine noParCut J zta _ e hP E.hNF₂.1 he hno d t hdL htp hpp.2.1 ?_
    grind
  have hcases : t = 0 ∨ 0 < t := hpp.1.eq_or_lt.imp (fun h => h.symm) id
  have hfp : (chainModel J.right).param zta ztrbx = 0 ∨
      ¬ (chainModel J.right).IsCut ztwis
        ((chainModel J.right).key zta ztrbx) := by
    grind
  have hq_pos : (c₂.nreg fqE < (chainModel J.right).W.n ∧
      ProperPos ztj zta P.n ztkkl ∧
      ((chainModel J.right).param zta ztkkl = 0 ∨
        ¬ (chainModel J.right).IsCut ztwis
          ((chainModel J.right).key zta ztkkl))) := by
    rw [v3, v4]
    by_cases hH' : H = 0
    · rw [ite_eq_left hH', ite_eq_left hH']
      exact ⟨hcpBn, hppB, Or.inl rfl⟩
    grind
  have kA : zteic := kp.1 _ (by unfold SlArW ALLOC sw; omega)
  refine (HF sh Bs F X Ok P W c₀ c₂ J N₁ N₂ E hI₂ by_omega
    by_grind hfp hq_pos.1 hq_pos.2.1 hq_pos.2.2 (by
      grind)).mono le_rfl ?_
  rintro c' ⟨f1, f2, f3, f4, f5, f6, f7⟩
  refine ⟨f1, f2, ⟨d, hdL, hd0, hEd, ?_, fun htp => ?_, fun ht0 => ?_⟩, fun a ha => ?_, ?_,
    fun r hr hS hrA => ?_⟩
  · grind
  · have hH' : H ≠ 0 := fun h => htp.ne' (hH0.1 h)
    grind
  · have hH' : H = 0 := hH0.2 ht0
    rw [hv3, v4, ite_eq_left hH', ite_eq_left hH'] at f4; exact f4
  · rw [f5 a by_omega, kp.2, n5 a ha]
  · omega
  · have hS' : ¬ (FRR r ∨ ztltx ∨ ztlub) := hS
    have hband : 240000 ≤ r ∧ r < 250000 → True := fun _ => trivial
    rw [f7 r hr (fun h => hS' zteg) hrA]
    zugjp
    · rw [kp.1 r ztmep,
        k1 r hsw.1 hsw.2 ztmey ztdzd
          ztdzd hrA]
    · rw [kp.1 r ztmep,
        n3 r hr ztmey ztdzd
          ztdzd hrA]
open Chazelle.Visibility (rayPt rayPt_snd)
def slfFin (ps sl : Stmt) : Stmt := .seq slfOffs (.seq ztwej (.seq ztwei slfEmits))
variable {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-- The registers of the code, the attachments and the raw array. -/
def SlfSafe (r : ℕ) : Prop := sw 4000 ≤ r ∧ r ≤ sw 4053
variable {R : ℕ → Prop}
theorem slf_keep {c c' : Config} (h : SlfFr R c c')
    (hR : ∀ r, R r → ¬ SlfSafe r) {r : ℕ} (hr : SlfSafe r) : c'.nreg r = c.nreg r :=
  h.1 r (band_sw_not ⟨by unfold SlfSafe sw at hr; omega, by unfold SlfSafe sw at hr; omega⟩)
    by_grind (by unfold SlfSafe sw at hr; unfold ALLOC; omega)
theorem slfOffR_safe : ∀ r, slfOffR r → ¬ SlfSafe r := by
  intro r h h'; unfold slfOffR SlfSafe sw at *; omega
theorem parR_safe : ∀ r, ParR r → ¬ SlfSafe r := by
  intro r h h'; unfold ParR oPar SlfSafe sw at *; omega

/-- The registers of the finish before the emission. -/
def SlfFinR (r : ℕ) : Prop := slfOffR r ∨ ParR r ∨ slfLabR r
theorem slfFinR_sorg : ∀ r, SlfFinR r → SOrgR r := by
  intro r h
  unfold SlfFinR slfOffR ParR slfLabR StrR FRR frA frB slfN slfL0 slfL1 slfP slfY oPar SOrgR gRC
    sw at *
  omega

/-- **Transfer of the post** from the start of the emission. -/
theorem orgOut_transfer {N : NF} {kind k b : ℕ} {c₃ c' : Config}
    (hR : ∀ r, R r → SOrgR r) (fr : SlfFr R c c₃)
    (hRB : c₃.nreg gRB = c.nreg gRB) (hRC : c₃.nreg gRC = c.nreg gRC)
    (h : OrgOut P J N kind k b c₃ c') : OrgOut P J N kind k b c c' := by
  zumt
  rw [hRB, hRC] at *
  exact ⟨h1, h2, h3, h4, fun a ha hs => (h5 a (lt_of_lt_of_le ha fr.2.1) hs).trans (fr.2.2 a ha),
    fr.2.1.trans h6, fun r hb hs ha => (h7 r hb hs ha).trans (fr.1 r hb by_grind ha)⟩

/-- The cost bound. -/
theorem slf_cost {A B T Kp Ks Pc : ℕ} (hA : 1 ≤ A) (hB : T + 1 ≤ B) (hP : Pc ≤ Kp * A + 5) :
    44037 + (Pc + ((Ks * ztxz + 40) + 100)) ≤ (44200 + Kp + Ks) * A * B := by
  have hB1 : 1 ≤ B := by_omega
  have h1 : 1 ≤ A * B := Nat.one_le_iff_ne_zero.2 zthbt
  have h2 : Kp * A ≤ Kp * A * B := Nat.le_mul_of_pos_right _ by_omega
  have h3 : Ks * ztxz ≤ Ks * A * B := by
    calc Ks * ztxz ≤ Ks * B := Nat.mul_le_mul_left _ hB
      _ ≤ Ks * A * B := by
        zuogp; exact Nat.mul_le_mul_left _ zttau
  grind
set_option maxHeartbeats 32000000 in
/-- **Task Fin** from the stretch labels and the emission. -/
theorem finTask_of (hS : StrLabTask) (hEm : SlfEmitsSpec) : FinTask := by
  obtain ⟨ps, κp, hps⟩ := parTask
  obtain ⟨sl, κs, hsl⟩ := strLabSpec_of hS
  refine ⟨slfFin ps sl, fun D => 44200 + κp + κs D, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hD hpre hgA hraw hroom
  zubns
  zueqm
  generalize hkd : c.nreg oKd = kind at *
  generalize hkk : c.nreg oKk = k at *
  generalize hkb : c.nreg oB = b at *
  obtain ⟨he0, hpp0, hA0, he1, hpp1, hA1, hpre2⟩ := hpre
  zudim
  zueuj
  have hat₀ : SlfAtt P J ztwja c ztjf ztms := by
    have hpos : |((chainModel J.whole).pos zta ⟨c.nreg ztjf, c.nreg ztms⟩).2| <
        J.whole.radius := by rw [pos_eq_sidePt', hA0.2.2.2.1]; exact hy
    exact ⟨⟨he0, hpp0, ztzmc⟩, hpos, by_grind⟩
  have hat₁ : SlfAtt P J ztwja c ztlq ztoo := by
    have hpos : |((chainModel J.whole).pos zta ⟨c.nreg ztlq, c.nreg ztoo⟩).2| <
        J.whole.radius := by
      rw [pos_eq_sidePt', hA1.2.2.2.1]; tauto
    exact ⟨⟨he1, hpp1, ztzmc⟩, hpos, by_grind⟩
  obtain ⟨hbrk, hpk⟩ := anc_pocket_iff hP hN hD hA0 hA1
  -- the cost
  have hcost := slf_cost (A := if kind = 1 then 1 else N₁.nChords + N₂.nChords + 1)
    (B := F ztq + c₀.nreg TLR + 1) (T := c₀.nreg TLR) (Kp := κp)
    (Ks := κs zto)
    (Pc := if kind = 1 then 5 else κp * ztcer + 4) by_grind
    by_omega (by
      zus
      · omega
      grind)
  refine (?_ : IRS P W c₀ _ c _ _).mono
    by_omega ztb
  zufqq
  have hroom' : c.nreg ALLOC + (44037 + ((if kind = 1 then 5 else κp * ztcer + 4) +
      ((κs zto * ztgf + 40) + 100))) ≤ W := by
    omega
  unfold slfFin
  -- 1. the offsets
  refine IRS.seq (slfOffs_irs E hI hat₀.1 hat₁.1 by_omega) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨b0, b3, b4, b7, ha1, ha, fr1⟩
  have s1 : ∀ r, SlfSafe r → c₁.nreg r = c.nreg r := fun r hr => slf_keep fr1 slfOffR_safe hr
  have e1kd : ztuqv := by rw [s1 _ by_trivial, hkd]
  have e1kk : ztuqw := by rw [s1 _ by_trivial, hkk]
  have e1kb : ztuqt := by rw [s1 _ by_trivial, hkb]
  have e1pe : c₁.nreg pE2 = c.nreg pE2 := s1 _ by_trivial
  have e1ph : c₁.nreg pH2 = c.nreg pH2 := s1 _ by_trivial
  -- 2. the parent
  refine IRS.seq
    ((slfPar_irs E hI₁ (fun c' hI' => hps sh Bs F X Ok P W c₀ c' J N₁ N₂ E hI')
      by_grind
      by_grind
      by_grind).mono by_grind (fun _ h => h)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hpar, fr2⟩
  rw [e1kd, e1kk, e1kb] at hpar
  have s2 : ∀ r, SlfSafe r → c₂.nreg r = c₁.nreg r := fun r hr => slf_keep fr2 parR_safe hr
  have fr12 : SlfFr SlfFinR c c₂ :=
    (fr1.mono fun r h => Or.inl h).trans (fr2.mono by_grind)
  have g2 :=
    fun r h1 h2 h3 => fr12.1 r zthse h3 ztu
  have r01 := g2 ztjf by_decide by_decide
    ztfge
  have r02 := g2 ztms by_decide by_decide
    ztfge
  have r11 := g2 ztlq by_decide by_decide
    ztfgd
  have r12 := g2 ztoo by_decide by_decide
    ztfgd
  zubfb

  have k21 :=
    fun r h1 h2 h3 => fr2.1 r zthse h3 ztu
  have eO : ∀ i, i ≤ 8 → c₂.nreg _ = c₁.nreg ztuan := fun i hi =>
    k21 _ ztfgg ztfgg (by unfold ParR oPar slfO sw; omega)
  have eA2 : c₂.nreg slfA = c₁.nreg slfA :=
    k21 _ by_decide by_decide (by unfold ParR oPar slfA sw; omega)
  -- 3. the labels
  refine IRS.seq
    (slfLab_irs E hI₂ hsl hD zttna zttnb
      (by zuntr; exact b0.of_eq (eO 0 by_norm_num))
      (by zuntr; exact b3.of_eq (eO 3 by_norm_num))
      (by rw [o1]; exact b7.of_eq (eO 7 by_norm_num))
      by_omega (by rw [o0, o1, eA2]; exact ha)
      (fun h => by rw [o0, o1]; exact hpk.1 h) hpar by_omega) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨hlab, fr3⟩
  have fr13 := fr12.trans (fr3.mono fun r h => Or.inr ztbho)
  have g3 :=
    fun r h1 h2 h3 => fr13.1 r zthse h3 ztu
  have k32 :=
    fun r h1 h2 h3 => fr3.1 r zthse h3 ztu
  have safe : ∀ r, SlfSafe r → ¬ SlfFinR r := fun r hr h => by
    unfold SlfSafe SlfFinR slfOffR ParR slfLabR StrR FRR frA frB slfN slfL0 slfL1 slfP slfY oPar
      sw at *
    omega
  have g3s := fun r hr =>
    g3 r ztmeq ztmeq (safe r hr)
  have e3kd : c₃.nreg oKd = kind := by rw [g3s _ by_trivial, hkd]
  have e3kk : c₃.nreg oKk = k := by rw [g3s _ by_trivial, hkk]
  have e3kb : ztusp := by rw [g3s _ by_trivial, hkb]
  have e3a : c₃.nreg _ = c.nreg ztjf := g3s _ by_trivial
  have e3b : c₃.nreg _ = c.nreg ztms := g3s _ by_trivial
  have e3c : c₃.nreg _ = c.nreg ztlq := g3s _ by_trivial
  have e3d : c₃.nreg _ = c.nreg ztoo := g3s _ by_trivial
  have e3RB : c₃.nreg gRB = c.nreg gRB := g3s _ by_trivial
  have e3RC : c₃.nreg gRC = c.nreg gRC := g3s _ by_trivial
  have q0 := slfOff_congr (P := P) (J := J) e3a e3b
  have q1 := slfOff_congr (P := P) (J := J) e3c e3d
  have eO3 : ∀ i, i ≤ 8 → c₃.nreg ztuan = c₁.nreg _ := fun i hi => by
    rw [k32 _ ztfgg ztfgg
      (by unfold slfLabR StrR FRR frA frB slfN slfL0 slfL1 slfP slfY slfO sw; omega), eO i hi]
  have eA3 : c₃.nreg slfA = c₂.nreg slfA :=
    k32 _ by_decide by_decide
      (by unfold slfLabR StrR FRR frA frB slfN slfL0 slfL1 slfP slfY slfA sw; omega)
  have eP3 : c₃.nreg oPar = c₂.nreg oPar :=
    k32 _ by_decide by_decide
      (by unfold slfLabR StrR FRR frA frB slfN slfL0 slfL1 slfP slfY oPar sw; omega)
  -- 4. the emission
  have haux : (∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W
      ztwja q s ∧ (Lst J : ℝ) ≤ oW J ztej) →
      AuxOK P J N₂ ztwja
        (c₃.nreg slfA, c₃.nreg slfN, c₃.nreg slfL0, c₃.nreg slfL1, c₃.nreg oPar) := by
    intro hC1
    obtain ⟨n1, n2, n3, n4⟩ := hlab
    obtain ⟨p1, p2, p3⟩ := hpar
    rw [eA3, eA2]
    zupcp
    refine ⟨ha1, ?_, n1, n2, n3, fun h hnp => n4 by_omega hnp hC1, p1, p2, p3⟩
    rw [ha, hbrk]; rfl
  refine (hEm sh Bs F X Ok P W c₀ c₃ J N₁ N₂ E hI₃ by_grind
    by_grind (by rw [e3a, e3b]; exact hat₀.1)
    by_grind (by rw [e3c, e3d]; exact hat₁.1)
    (by rw [q0]; exact b0.of_eq (eO3 0 by_norm_num))
    (by zunrs; exact b4.of_eq (eO3 4 by_norm_num))
    (by rw [e3kd, e3kk, e3kb]; omega) by_omega
    by_omega by_omega).mono le_rfl ?_
  intro c' h
  rw [e3kd, e3kk, e3kb] at h
  exact orgOut_transfer slfFinR_sorg fr13 e3RB e3RC h

/-- **Task Fin: the finish of a stop origin.** -/
theorem finTask : FinTask := finTask_of strLabTask slfEmits_spec
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Set Filter Topology
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt sideLeft)
open Chazelle.Merge (FreeAt)
@[expose] public section
section M
variable (J : Merge.Junction)
theorem radius_right : J.right.radius = J.whole.radius := FuseMath.radius_of_P J rfl
theorem radius_left : J.left.radius = J.whole.radius := FuseMath.radius_of_P J rfl
variable {x : Point} {z : Point} {σ : ℝ}
theorem onCB_of_right (h : OnCB J.right x) : OnCB J.whole x := by
  zude
  · zulel
  · tauto
  tauto
theorem onCB_of_left (h : OnCB J.left x) : OnCB J.whole x := by
  zude
  · exact Or.inl ztpzf
  · tauto
  tauto
theorem freeAt_left_of (hz : z.2 ≤ J.left.top.2) (h : FreeAt J.whole z σ) :
    FreeAt J.left z σ := by
  zucfc

  zulex
theorem freeAt_right_of (hz : z.2 ≤ J.right.top.2) (h : FreeAt J.whole z σ) :
    FreeAt J.right z σ := by
  zucfc

  zuhcr
theorem whole_hit_cases (hσ : σ = 1 ∨ σ = -1) (hz₁ : z.2 ≤ J.left.top.2)
    (hz₂ : z.2 ≤ J.right.top.2) :
    J.whole.hitParam z σ = J.left.hitParam z σ ∨ J.whole.hitParam z σ = J.right.hitParam z σ := by
  rw [whole_hitParam_eq_min J ztqqy hσ, left_hitParam_eq J hz₁,
    right_hitParam_eq J hz₂]
  grind
theorem whole_hit_above (hσ : σ = 1 ∨ σ = -1) (hz₂ : z.2 ≤ J.right.top.2)
    (hz₁ : J.left.top.2 < z.2) (hf : FreeAt J.right z σ) :
    J.whole.hitParam z σ = J.right.hitParam z σ :=
  (whole_of_genuine_above₁ J hz₂ hz₁ hσ ((genuine_iff J.right hz₂ hσ).2 ⟨hf, rfl⟩)).2
end M

/-- **The first hit is a point of the chain or of the box.** -/
theorem hit_onCB (C : Chain) {z : Point} {σ : ℝ} (hz : z.2 ≤ C.top.2) (hσ : σ = 1 ∨ σ = -1)
    (hf : FreeAt C z σ) : 0 < C.hitParam z σ ∧ OnCB C (rayPt z σ ztbtm) := by
  obtain ⟨hT, hout, hin⟩ := Merge.hit_of_freeAt C hz hσ hf
  set T := C.hitParam z σ with hTd
  refine ⟨hT, ?_⟩
  rcases (Merge.not_mem_dom_iff C (p := rayPt z σ T) by_simp_all).1 hout with
    hb | hs
  · -- on the box boundary
    zubo
    have h2 : ztmxi := (C.dom_subset_box (hin ztld by_linarith by_linarith)).2
    have h1 : |z.1 + σ * T| ≤ C.radius := by
      zuum

      set δ := |z.1 + σ * T| - C.radius with hδ
      zukhq
      set t := T - min ztld ztbfe with ht
      have hm1 : min ztld ztbfe ≤ T / 2 := min_le_left _ _
      have hm2 : min ztld ztbfe ≤ δ / 2 := min_le_right _ _
      have hm0 : 0 < min ztld ztbfe := lt_min by_linarith by_linarith
      have hd := (C.dom_subset_box (hin t by_linarith by_linarith)).1
      zvogc at hd
      have hσa : ztguu := by_grind
      have e : z.1 + σ * T = ztkhn + σ * ztnpu := by_ring
      have h3 : |z.1 + σ * T| ≤ |z.1 + σ * t| + |σ * ztnpu| := by
        zvmwe; exact abs_add_le _ _
      have h4 : |σ * ztnpu| = T - t := by
        rw [abs_mul, hσa, one_mul, abs_of_nonneg by_grind]
      grind
    have : ¬ (|z.1 + σ * T| < C.radius ∧ |z.2| < C.radius) := hb
    zuhl
    zudlo
    grind
  tauto
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Set
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft)
@[expose] public section
variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {E : ℕ} {c₀ c : Config}
namespace AEnv
variable (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c)
omit hA in
include hI in
theorem fixr {r : ℕ} (hr : IFix r) : c.nreg r = c₀.nreg r := hI.hin r hr
include hA in
theorem hreg : HostRegular P.n H := by
  zubbs
  exact hJWF.2.2.2 H hJ.2.2.1
include hA hI in
theorem ctxW : ChainCtx P W c ztjl J.whole := by
  zubbs
  obtain ⟨hC, hw⟩ := chainDesc_keep hJWF.2.2.1 hJ.2.2 zttj hI.hA
  rw [← fixr hI (show IFix ztjl by unfold IFix sw; omega)] at hC hw
  exact ⟨hA.hG, hA.hWh, hw, ⟨H, hC, hA.hreg⟩, hA.hP, hA.hWm⟩
include hA hI in
/-- The local-hit context of the model of `C₂`. -/
theorem lctxR (h1 : c.nreg lMD = c₀.nreg ztqm) (h2 : c.nreg lCD = c₀.nreg ztqm + 1)
    (h3 : c.nreg lNF = c₀.nreg ztbz) : LCtx P W J.right N₂ E c := by
  zuqo
  have h0 : c₀.nmem ztbahe = 0 := by
    rcases d31 with ⟨h, -⟩ | ⟨-, -, hM⟩
    · zubh
    · zulxo
  obtain ⟨-, -, hEb, -⟩ := w21.2 H J.right d21
  have hcd : ChainDescAt c₀.nmem ztzlk zta H J.right :=
    MergeAsm.chainDescAt_copy d21 hEb ztcve ztnzd
  have hwf' : ChainWF P ztdq c₀.nmem ztzlk :=
    MergeAsm.chainWF_copy w21 d21 ztcve ztnzd
      (by have := w31.1; omega) le_rfl
  have hmwf : ModelDescWF P ztdq c₀.nmem ztbahe := ⟨w31.1, fun _ => hwf'⟩
  zunb

  refine
    { hG := hA.hG
      hWh := hA.hWh
      hctx := ⟨hA.hG, hA.hWh, by_simp_all, ztrad,
        hA.hP, by have := hA.hWm; have : ztmti := by
                    simp
                  omega⟩
      hcd := by_omega
      hmd := by zvmwp; exact Or.inl ⟨m0c, H, J.right, mdc, rfl⟩
      hmwf := by_simp_all
      hm0 := by_simp_all
      hP := hA.hP
      hNW := by zvncq; exact hA.hN₂.transport (fun a ha => hm a (by have := hA.hE; omega))
      hE := by have := hA.hE; have := hI.hA; omega
      hNF := hA.hNF₂
      htab := fun j hj => by
        zubsk
      hbig := by zupdd; exact hA.hbig₂
      hTB := by zupde; exact hA.hTB
      hTW := by zuopb; have := hA.hTW; have := hI.hA; omega }
include hA hI in
/-- The local-hit context of the model of `C₁`. -/
theorem lctxL (h1 : c.nreg lMD = c₀.nreg ztbbz) (h2 : c.nreg lCD = c₀.nreg ztbbz + 1)
    (h3 : c.nreg lNF = c₀.nreg ztea) : LCtx P W J.left N₁ E c := by
  zuqp
  have h0 : c₀.nmem ztbagz = 0 := by
    rcases d30 with ⟨h, -⟩ | ⟨-, -, hM⟩
    · zubh
    · zulxo
  obtain ⟨-, -, hEb, -⟩ := w20.2 H J.left d20
  have hcd : ChainDescAt c₀.nmem ztzlj zta H J.left :=
    MergeAsm.chainDescAt_copy d20 hEb ztcve ztnzc
  have hwf' : ChainWF P ztdq c₀.nmem ztzlj :=
    MergeAsm.chainWF_copy w20 d20 ztcve ztnzc
      (by have := w30.1; omega) le_rfl
  have hmwf : ModelDescWF P ztdq c₀.nmem ztbagz := ⟨w30.1, fun _ => hwf'⟩
  zunb

  refine
    { hG := hA.hG
      hWh := hA.hWh
      hctx := ⟨hA.hG, hA.hWh, by_simp_all, ztrad,
        hA.hP, by have := hA.hWm; have : ztpkj := by
                    simp
                  omega⟩
      hcd := by_omega
      hmd := by zvmwp; exact Or.inl ⟨m0c, H, J.left, mdc, rfl⟩
      hmwf := by_simp_all
      hm0 := by_simp_all
      hP := hA.hP
      hNW := by zvncq; exact hA.hN₁.transport (fun a ha => hm a (by have := hA.hE; omega))
      hE := by have := hA.hE; have := hI.hA; omega
      hNF := hA.hNF₁
      htab := fun j hj => by
        zubsk
      hbig := by zupdd; exact hA.hbig₁
      hTB := by zupde; exact hA.hTB
      hTW := by zuopb; have := hA.hTW; have := hI.hA; omega }
end AEnv

/-- **The facts of a side-1 query** at the candidate step. -/
theorem q1_facts {z : Point} (hq : QState P J 1 z c) :
    (chainModel J.right).pos zta zthz = z ∧
      c.nreg qE < (chainModel J.right).W.n ∧
      ProperPos ztj zta P.n zthz ∧
      |z.2| < J.right.radius ∧ z.2 ≤ J.right.top.2 ∧
      PosClass J.right zta zthz ∧
      LHGeo P J.right zthz ztql ∧
      (dirOf ztql = 1 ∨ dirOf ztql = -1) ∧ 1 ≤ c.nreg qH ∧ c.nreg qH ≤ P.n ∧
      ((Qof P).vtx ztbmn).2 = z.2 := by
  zuc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hq.hq
  have hz := hq.hz
  have hht := hq.hht
  simp only [sideChain_one] at h1 h4 h5 h6 h7 hz hht
  simp only at h2 h3
  have hσ : dirOf ztql = 1 ∨ dirOf ztql = -1 := SweepPrim.dirOf_cases _
  have hsec : sideLeft (chainModel J.right).W (c.nreg qE)
      ((chainModel J.right).param zta zthz)
      (rayPt ztyng ztba 1) := by
    have e : rayPt ztyng ztba 1 =
        (((chainModel J.right).pos zta zthz).1 + dirOf ztql,
          ((chainModel J.right).pos zta zthz).2) := by
      simp [Chazelle.Visibility.rayPt]
    simp_all
  have habs : |((chainModel J.right).pos zta ⟨c.nreg qE, c.nreg qH⟩).2| < J.right.radius :=
    query_abs h1 h4 h5 h6 hσ hsec
  have hpc := posClass_of h1 h4 h5 habs ztqbd
  zvncr at habs h6 hht
  refine ⟨hz, h1, ⟨h4, h5, by_simp_all⟩, habs, h6, hpc,
    ⟨c.nreg qH - 1, by_simp_all, by_omega, by_simp_all, hsec, by_simp_all⟩,
    hσ, h2, by_omega, hht.symm⟩
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Set
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sidePrev sideNext)
open Chazelle.Merge (FreeAt)
@[expose] public section
namespace Cand1
variable {J : Merge.Junction}

/-- **A position of the class off the box walls** is a point of the chain, on a tour edge. -/
theorem tour_set (C : Chain) (Q : Polygon) {x : WPos} (hc : PosClass C Q x)
    (hb : ¬ ztdiq) (h0 : 0 ≤ (chainModel C).param Q x)
    (h1 : (chainModel C).param Q x < 1) :
    (chainModel C).pos Q x ∈ C.set ∧ 6 ≤ x.edge ∧
      (ztbxz ∨
        ztgmw) := by
  zuik
  · omega
  · refine ⟨?_, hc.1, Or.inl hc⟩
    rw [pos_eq_sidePt' C Q x]
    have e : x.edge = ztcxd + 6 := by_omega
    zui
    exact C.sideWalk_tour_pt_mem C.sideBeta by_omega ztczk h0 h1
  · refine ⟨?_, by_omega, Or.inr hc⟩
    rw [pos_eq_sidePt' C Q x, hc.1, hc.2]
    exact C.sideWalk_tour_pt_mem C.sideBeta (i := 2 * C.m) le_rfl ztdnl le_rfl one_pos

/-- **The shared vertex in the model of `C₂`**: parameter `0`, and the edge is `cstR 1` or the
last walk edge when `cstR 1 = 6`. -/
theorem shared_iffR (hP : J.P.Simple) (Q : Polygon) {x : WPos}
    (hx : x.edge < (chainModel J.right).W.n) (h0 : 0 ≤ (chainModel J.right).param Q x)
    (h1 : (chainModel J.right).param Q x < 1) :
    (chainModel J.right).pos Q x = J.shared ↔ (chainModel J.right).param Q x = 0 ∧
      (x.edge = cstR J 1 ∨ (x.edge + 1 = 2 * J.m₂ + 7 ∧ cstR J 1 = 6)) := by
  rw [← J.right_vertex_zero, atEnd_iff J.right hP ztp Q hx h0 h1]
  have e : cstR J 1 = 6 + tpos J.right 0 := rfl
  simp_all

/-- **The top of `C₂`** among the positions of its model. -/
theorem top_iffR (hP : J.P.Simple) (Q : Polygon) {x : WPos}
    (hx : x.edge < (chainModel J.right).W.n) (h0 : 0 ≤ (chainModel J.right).param Q x)
    (h1 : (chainModel J.right).param Q x < 1) :
    (chainModel J.right).pos Q x = J.right.top ↔ (chainModel J.right).param Q x = 0 ∧
      (x.edge = 6 ∨ x.edge + 1 = 2 * J.m₂ + 7 ∨ x.edge = 6 + midT J.right) := by
  rw [atTop_iff J.right hP Q hx h0 h1]
  simp
theorem param_hgt0 (M : Model) (Q : Polygon) (e : ℕ) : M.param Q ztjy = 0 := rfl

/-- **The vertex position of the shared vertex in the model of `C₁`.** -/
theorem shared_posL (hP : J.P.Simple) (Q : Polygon) (n : ℕ) :
    cstL J 1 < (chainModel J.left).W.n ∧ ProperPos ztbw Q n ztrbp ∧
      (chainModel J.left).pos Q ztrbp = J.shared := by
  have hp0 := param_hgt0 ztbw Q (cstL J 1)
  zuhfi
  have ht := tpos_lt J.left J.m₁
  have e : cstL J 1 = 6 + tpos J.left J.m₁ := rfl
  have hlt : cstL J 1 < (chainModel J.left).W.n := by_omega
  refine ztxzp
  rw [show J.shared = J.left.vertex J.left.m from rfl,
    atEnd_iff J.left hP ztbt Q hlt ztjqe by_simp]
  simp_all

/-- `sideLeft` at a position depends only on the edge ends when the parameter is positive. -/
theorem sideLeft_congr {W W' : Polygon} {p p' : ℕ} {t : ℝ} (ht : t ≠ 0)
    (ha : W.vtx p = W'.vtx p') (hb : W.vtx ztwjb = W'.vtx ztgwe)
    (x : Point) : sideLeft W p t x ↔ sideLeft W' p' t x := by
  zulce
variable {P : Polygon} {z : Point}
/-- **The box twin**: a query position on a vertical side of the box satisfies `LHGeo` in the
model of `C₁` when it is not above the top of `C₁`. -/
theorem lhGeo_boxL {x : WPos} {d : ℕ} (he : x.edge = 1 ∨ x.edge = 3)
    (hg : LHGeo P J.right x d)
    (hy : |((chainModel J.right).pos zta x).2| < J.right.radius)
    (h₁ : ((chainModel J.right).pos zta x).2 ≤ J.left.top.2) :
    LHGeo P J.left x d ∧
      (chainModel J.left).pos zta x = (chainModel J.right).pos zta x ∧
      (chainModel J.left).param zta x = (chainModel J.right).param zta x := by
  obtain ⟨ha, hb, hpar, hpos⟩ := boxTwin_pos (C₁ := J.right) (C₂ := J.left) rfl he zta x.hgt
  zudrd
  have hR := J.right.radius_pos
  have ht : (chainModel J.right).param zta x ≠ 0 := by
    zubww
    have e : (chainModel J.right).pos zta x = (chainModel J.right).wa x.edge := by
      zuckw
    zugcs
    zukan
    zucfd

    · rw [J.right.sideWalk_vtx_one] at hy; grind
    · rw [J.right.sideWalk_vtx_three] at hy; grind
  have hx : (chainModel J.left).pos zta zthnv =
      (chainModel J.right).pos zta zthnv := hpos.symm
  have hp : (chainModel J.left).param zta x = (chainModel J.right).param zta x :=
    hpar.symm
  refine ⟨ztklg, hx, hp⟩
  · zukwl
  · rw [hx, hp]
    zugkb
  · zvnly; exact h₁

/-- **An arrival position** at a point with a height code naming its height satisfies `LHGeo`
with that code. -/
theorem lhGeo_arr {C : Chain} {z : Point} {σ : ℝ} {p : ℕ} {t : ℝ}
    (harr : Arrival (chainModel C).W z (-σ) p t) {h : ℕ} (hh : h < P.n)
    (hhz : ((Qof P).vtx h).2 = z.2) (htop : z.2 ≤ C.top.2) {d : ℕ} (hd : dirOf d = σ) :
    LHGeo P C ztdw d ∧ (chainModel C).pos zta ztdw = z ∧
      (chainModel C).param zta ztdw = t := by
  zueiv
  zubvb
  have hsec' : ztwnr := by
    simp_all
  zubdu

/-- **An endpoint query** starts at the origin `endOrigin j` in the direction `endDir j`. -/
theorem endQ_facts {Q : Polygon} {N : NF} (hN : IsNF ztj Q N) {j : ℕ}
    (hj : j < 2 * N.nChords) {e h d : ℕ}
    (hq : (e, h, d) = (sweepEndQ N.chords).getD j ztt) :
    (chainModel J.right).pos Q ztcq = endOrigin J Q N j ∧ dirOf d = endDir j := by
  obtain ⟨h1, h2⟩ := endOrigin_eq J hN hj
  have hl : N.nChords = N.chords.length := rfl
  have hj' : j < 2 * N.chords.length := by_omega
  unfold sweepEndQ at hq
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj'] at hq
  simp only [Option.map_some, Option.getD_some] at hq
  zuwv
  unfold endPos endDir
  have hc : N.chords.getD ztwm ztrp = N.chord ztwm := rfl
  zvnmd at hq
  by_cases hp : j % 2 = 0
  · rw [ite_eq_left hp] at hq
    zudlj

    rw [ite_eq_left hp, ite_eq_left hp]
    tauto
  · rw [ite_eq_right hp] at hq
    zudlj

    rw [ite_eq_right (show ¬ j % 2 = 0 from hp), ite_eq_right (show j % 2 ≠ 0 from hp)]
    tauto

/-- **The first hit of `C`** is a candidate when that of `C₂` is and, below the top of `C₁`,
that of `C₁` is. -/
theorem whole_mem {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hz₂ : z.2 ≤ J.right.top.2)
    (hf : FreeAt J.whole z σ) {L : Set ℝ} (h2 : J.right.hitParam z σ ∈ L)
    (h1 : z.2 ≤ J.left.top.2 → J.left.hitParam z σ ∈ L) : J.whole.hitParam z σ ∈ L := by
  by_cases hz₁ : z.2 ≤ J.left.top.2
  · rcases whole_hit_cases J hσ hz₁ hz₂ with e | e <;> zvmwe
    · simp_all
    omega
  · rw [whole_hit_above J hσ hz₂ (not_le.1 hz₁) (freeAt_right_of J hz₂ hf)]
    zucvi

/-- A point of `C₂` other than the shared vertex is not a point of `C₁`. -/
theorem not_mem_left (hP : J.P.Simple) {z : Point} (h2 : z ∈ J.right.set) (hs : z ≠ J.shared) :
    z ∉ J.left.set := fun h1 => by
  have h : ztmxf := ztwo
  rw [J.left_inter_right hP] at h
  simp_all

/-- A point of `C₂` is strictly inside the box. -/
theorem abs_lt_whole (h : z ∈ J.right.set) :
    |z.1| < J.whole.radius ∧ |z.2| < J.whole.radius := by
  have h' := J.whole.abs_le_coordBound_of_mem_set ztjjc
  have := J.whole.coordBound_lt_radius
  grind
end Cand1
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
namespace Cand1
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- The inputs of the local hit. -/
def setL (md nf nr e t : ℕ) : List Instr :=
  [.copyN lMD md, .addN lCD lMD K1, .copyN lNF nf, .copyN lE e, .copyN lH qH, .copyN lD qD,
    .copyN lN nr, .constN lT t]

/-- A register outside the inputs of the local hit. -/
def OutL (r : ℕ) : Prop := r < sw 1100 ∨ sw 1107 < r
variable (m f : ℕ → ℕ) {md nf nr e t : ℕ}
theorem setL_val (hmd : OutL md) (hnf : OutL nf) (hnr : OutL nr)
    (he : OutL e) :
    regB m ztkg f lMD = f md ∧ regB m ztkg f lCD = f md + f K1 ∧
    regB m ztkg f lNF = f nf ∧ regB m ztkg f lE = f e ∧
    regB m ztkg f lH = f qH ∧ regB m ztkg f lD = f qD ∧
    regB m ztkg f lN = f nr ∧ regB m ztkg f lT = t ∧
    ztxpe := by
  have ne : ∀ r, OutL r → r ≠ 241100 ∧ r ≠ 241101 ∧ r ≠ 241102 ∧ r ≠ 241103 ∧ r ≠ 241104 ∧
      r ≠ 241105 ∧ r ≠ 241106 ∧ r ≠ 241107 := fun r h => by unfold OutL sw at h; omega
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := ne _ hmd
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := ne _ hnf
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := ne _ hnr
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7⟩ := ne _ he
  refine ztfcx <;>
    simp [setL, regB, regI, upd, lMD, lCD, lNF, lE, lH, lD, lN, lT, sw, K1, qH, qD, *]
theorem setL_ok (_hmd : OutL md) (hW : f md + 1 ≤ W)
    (hk : f K1 = 1) (ht : t ≤ W) : okB W m ztkg f := by
  have s : ztxtp := fun j h1 h2 =>
    iscr_sw ztce ztce
  zueey

  refine ⟨s 1100 le_rfl by_norm_num, ztpfr,
    s 1102 by_norm_num by_norm_num, s 1103 by_norm_num by_norm_num,
    s 1104 by_norm_num by_norm_num, s 1105 by_norm_num by_norm_num,
    s 1106 by_norm_num by_norm_num, ztpfs, trivial⟩
  have e1 : upd f lMD (f md) lMD = f md := upd_same _ _ _
  zufsy

/-- **A local hit with its inputs.** -/
def lhs (md nf nr e t : ℕ) (sh : Stmt) : Stmt := .seq ztbafr ztkak

/-- The cost of `lhs`. -/
def lhsK (T Fg D : ℕ) : ℕ := 8 + localK T Fg ztef D

/-- The post-condition of a local hit with its inputs at the position `(e, qH)`. -/
def LhPost (P : Polygon) (C : Chain) (Mod : ℕ → Chain) (R₀ : ℝ) (z : Point) (L : Set ℝ)
    (e : ℕ) (c c' : Config) : Prop :=
  (∃ L', AccOK P accA Mod R₀ z ztba L' c' ∧ L ⊆ L' ∧
      ztbakq ∧
      ztxvf) ∧
    ztcfn ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth
section Run
variable {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction} {H : Host}
  {N₁ N₂ : NF} {E : ℕ}
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ}
set_option maxHeartbeats 4000000 in
/-- **The local hit with its inputs** (generic: the local-hit context from the inputs). -/
theorem lhs_irs (hsh : ShooterOK sh Bs F X Ok)
    (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal) (hA : AEnv P W X Ok J H N₁ N₂ E c₀)
    {C : Chain} {N : NF} {md nf nr e t : ℕ}
    (hfix : IFix md ∧ IFix nf ∧ IFix nr) (heo : OutL e) (hI : IInv W c₀ c)
    (hctx : ∀ c₁ : Config, IInv W c₀ c₁ → c₁.nreg lMD = c₀.nreg md →
      c₁.nreg lCD = c₀.nreg md + 1 → c₁.nreg lNF = c₀.nreg nf → LCtx P W C N E c₁)
    (hmdA : c₀.nreg md + 1 ≤ c₀.nreg ALLOC)
    (hOk : Ok P ztc)
    (hsg : (chainModel C).Semigranular ztwjq ztq)
    (hdeg : (chainModel C).DegLe ztwjq zto)
    (hnr : c₀.nreg nr = 2 * C.m + 7)
    {Mod : ℕ → Chain} {R₀ : ℝ} {L : Set ℝ} {z : Point}
    (he : c.nreg e < (chainModel C).W.n)
    (hpp : ProperPos ztc zta P.n ztbte)
    (hz : (chainModel C).pos zta ztbte = z)
    (hy : |z.2| < C.radius)
    (hloc : ztdmv ∨ ztmah)
    (hacc : AccOK P accA Mod R₀ z ztba L c) (ht : t ≤ 2) (hMod : Mod t = C)
    (hR : C.radius = R₀)
    (hroom : c.nreg ALLOC + lhsK ztdg ztwiu zto ≤ W) :
    IRS P W c₀ ztocx c
      ztbajg
      (LhPost P C Mod R₀ z L e c) := by
  zubbx

  have h8 : 8 ≤ lhsK ztdg ztwiu zto := by unfold lhsK; omega
  have hmdW : ztrgf := by
    zuksm
    have := hI.hA; omega
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, vo⟩ :=
    setL_val c.nmem c.nreg (t := t) zttuw zttux zttuy heo
  unfold lhs
  refine IRS.seq (K₁ := 8) (K₂ := localK ztdg ztwiu ztyem
      zto)
    ((IRS.block ztkg hI (setL_ok c.nmem c.nreg zttuw hmdW hK.2.1
      by_omega)).mono by_rfl (fun _ h => h)) ?_
  zubun
  subst hc₁
  simp only at *
  set c₁ : Config := { c with nreg := regB c.nmem (setL md nf nr e t) c.nreg } with hc₁d
  have r1 : ztlby := fun r hr => vo r hr
  have hL : LCtx P W C N E c₁ := hctx c₁ hI₁
    (by show regB _ _ _ lMD = _; zuobw)
    (by show regB _ _ _ lCD = _; zunud)
    (by show regB _ _ _ lNF = _; zuobx)
  obtain ⟨hAr, hCh⟩ := SweepEv.region_bounds hL.hP hL.hNF hdeg
  zuhvu
  have a1 : ztsgp := v4
  have a2 : c₁.nreg lH = c.nreg qH := v5
  have a3 : c₁.nreg lD = c.nreg qD := v6
  have hacc₁ : AccOK P accA Mod R₀ ztymu
      ztqlz L c₁ := by
    rw [a1, a2, a3, hz]
    exact hacc.transport zthhb
  have h := localHit_irs (x := ztkkh) (d := c₁.nreg lD)
    (Da := c₀.nreg ztbey + 1) (Dc := c₀.nreg ztbey) hsh hBs hXl hI₁ hA.hK hL hA.hX hA.hcap
    hOk hsg hAr hCh rfl rfl rfl
    by_simp_all
    by_simp_all
    by_simp_all
    by_simp_all
    hacc₁ by_simp_all
    by_simp_all hR
    (by rw [show c₁.nreg lN = c.nreg nr from v7, hI.hin _ hfr]; omega)
    (by
      have hA1 : ztdc := r1 _ ztnvi
      rw [eTL, hA1]; unfold lhsK at hroom; omega)
  zubif

  rw [a1, a2, a3, hz] at a' g' geo'
  refine ⟨⟨L', a', s', g', fun hg => (geo' hg).2⟩, fun r h1 h2 h3 => ?_, hA', fun a ha => ?_⟩
  · zufmv

  grind

/-- **The local hit in the model of `C₂`** (model descriptor `sw 31`, normal form `sw 4`). -/
theorem lhsR_irs (hsh : ShooterOK sh Bs F X Ok)
    (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal) (hA : AEnv P W X Ok J H N₁ N₂ E c₀)
    {e t : ℕ} (heo : OutL e) (hI : IInv W c₀ c)
    {Mod : ℕ → Chain} {R₀ : ℝ} {L : Set ℝ} {z : Point}
    (he : c.nreg e < (chainModel J.right).W.n)
    (hpp : ProperPos ztj zta P.n ztbte)
    (hz : (chainModel J.right).pos zta ztbte = z)
    (hy : |z.2| < J.right.radius)
    (hloc : ztdmv ∨ (6 ≤ c.nreg e ∧ z ∈ J.right.set))
    (hacc : AccOK P accA Mod R₀ z ztba L c) (ht : t ≤ 2) (hMod : Mod t = J.right)
    (hR : J.right.radius = R₀)
    (hroom : c.nreg ALLOC + lhsK ztdg ztwiu zto ≤ W) :
    IRS P W c₀ (lhs ztqm ztbz zthy e t sh) c
      ztbajg
      (LhPost P J.right Mod R₀ z L e c) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h34, -, -, -, -, w31⟩ := hA.hst
  exact lhs_irs hsh hBs hXl hA
    ⟨by_trivial, by_trivial, by_trivial⟩ heo hI
    (fun c₁ hI₁ a b d => AEnv.lctxR hA hI₁ a b d) (by have := w31.1; omega) hA.hOk₂ hA.hsg₂
    hA.hdeg₂ h34 he hpp hz hy hloc hacc ht hMod hR hroom

/-- **The local hit in the model of `C₁`** (model descriptor `sw 30`, normal form `sw 3`). -/
theorem lhsL_irs (hsh : ShooterOK sh Bs F X Ok)
    (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal) (hA : AEnv P W X Ok J H N₁ N₂ E c₀)
    {e t : ℕ} (heo : OutL e) (hI : IInv W c₀ c)
    {Mod : ℕ → Chain} {R₀ : ℝ} {L : Set ℝ} {z : Point}
    (he : c.nreg e < (chainModel J.left).W.n)
    (hpp : ProperPos ztbw zta P.n ztbte)
    (hz : (chainModel J.left).pos zta ztbte = z)
    (hy : |z.2| < J.left.radius)
    (hloc : ztdmv ∨ (6 ≤ c.nreg e ∧ z ∈ J.left.set))
    (hacc : AccOK P accA Mod R₀ z ztba L c) (ht : t ≤ 2) (hMod : Mod t = J.left)
    (hR : J.left.radius = R₀)
    (hroom : c.nreg ALLOC + lhsK ztdg ztwiu zto ≤ W) :
    IRS P W c₀ (lhs ztbbz ztea ztna e t sh) c
      ztbajg
      (LhPost P J.left Mod R₀ z L e c) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h33, -, -, -, w30, -, -⟩ := hA.hst
  exact lhs_irs hsh hBs hXl hA
    ⟨by_trivial, by_trivial, by_trivial⟩ heo hI
    (fun c₁ hI₁ a b d => AEnv.lctxL hA hI₁ a b d) (by have := w30.1; omega) hA.hOk₁ hA.hsg₁
    hA.hdeg₁ h33 he hpp hz hy hloc hacc ht hMod hR hroom
end Run
end Cand1
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
def ShrStepSpec : Prop :=
  ∃ (shrB : Stmt → Stmt) (κS : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (L : Set ℝ),
      AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c →
      1 ≤ c.nreg qH → c.nreg qH ≤ P.n → ((Qof P).vtx ztbmn).2 = J.shared.2 →
      FreeAt J.whole J.shared ztba → c.nreg bL = 1 →
      AccOK P accA ztdm J.whole.radius J.shared
        ztba L c →
      c.nreg ALLOC + ztbakn ≤ W →
      IRS P W c₀ ztiax c
        ztbakn
        (fun c' =>
          (∃ L', AccOK P accA ztdm J.whole.radius J.shared
              ztba L' c' ∧ L ⊆ L' ∧
            ztxar ∧
            J.left.hitParam J.shared ztba ∈ L') ∧
          CandFr c c')
namespace Cand1
def tE : ℕ := sw 4800
def tH : ℕ := sw 4801
def nO : ℕ := sw 4802
def y34 : ℕ := sw 4804
def k2 : ℕ := sw 4805
def jx : ℕ := sw 4806
def tgt : ℕ := sw 4807
def m2 : ℕ := sw 4808
def ti : ℕ := sw 4809
def bt : ℕ := sw 4810
def tmp : ℕ := sw 4811
def dd : ℕ := sw 4812
def m2x : ℕ := sw 4813

/-- `t` if the registers `a`, `b` are equal, else `e`. -/
def ifEq (a b : ℕ) (t e : Stmt) : Stmt := .ifLtN a b e ztjdg

/-- Copies of the position, `2 m₂ + 6`, `K₂`, `qJ - K₂`. -/
def prepL : List Instr :=
  [.copyN tE qE, .copyN tH qH, .subN y34 zthy K1, .loadN k2 ztbz, .subN jx qJ k2]

/-- The fields of the chain descriptor of `C₂`. -/
def midL : List Instr :=
  [.addN tmp zted K2, .loadN m2 tmp, .addN tmp zted K3, .loadN ti tmp,
    .addN tmp zted K4, .loadN bt tmp, .addN dd ti ti, .addN m2x m2 m2]

/-- `tgt := 6 + midT C₂`. -/
def midB : Stmt :=
  .seq (block midL)
    (ifEq bt K1 (block [.subN tgt m2x dd, .addN tgt tgt K6])
      (.ifLtN ti m2 (block [.addN tgt dd K6]) (block [.copyN tgt K6])))

/-- The box class: the local hit at the box twin in the model of `C₁` if `bL = 1`. -/
def boxB (sh : Stmt) : Stmt := .ifLtN K0 bL ztxkz .skip

/-- The brute-force class: if `bL = 1`, the symbolic point and the brute-force shot. -/
def bruteB (bruteS : Stmt → Stmt) (sh : Stmt) : Stmt :=
  .ifLtN K0 bL (.seq (callSym zted qE qH ztwgf) ztqek) .skip

/-- A vertex position other than the shared vertex: top test for an endpoint query. -/
def topT (tabB : Stmt) (bruteS : Stmt → Stmt) (sh : Stmt) : Stmt :=
  .ifLtN jx k2
    (ifEq qE K6 ztepp (ifEq qE y34 ztepp
      (ifEq qE tgt ztepp tabB)))
    ztepp

/-- A position inside an edge. -/
def genT (tabB : Stmt) (bruteS : Stmt → Stmt) (sh : Stmt) : Stmt :=
  .ifLtN jx k2 tabB ztepp

/-- A vertex position: shared test. -/
def zeroT (tabB : Stmt) (shrB bruteS : Stmt → Stmt) (sh : Stmt) : Stmt :=
  ifEq qE ztbex ztiax
    (ifEq qE y34 (ifEq ztbex K6 ztiax ztlue) ztlue)

/-- A tour position. -/
def tourB (tabB : Stmt) (shrB bruteS : Stmt → Stmt) (sh : Stmt) : Stmt :=
  .seq (block prepL) (.seq (normS zted tE tH nO) (.seq midB
    ztgqk))

/-- **The candidate step of side `1`.** -/
def cand1P (tabB : Stmt) (shrB bruteS : Stmt → Stmt) (sh : Stmt) : Stmt :=
  .seq ztxla
    (ifEq qE K1 ztmcr (ifEq qE K3 ztmcr ztqxk))

/-! ## Run-step helpers -/
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
theorem irs_ifEq {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop}
    (ht : c.nreg a = c.nreg b → IRS P W c₀ t c K Q)
    (he : c.nreg a ≠ c.nreg b → IRS P W c₀ e c K Q) :
    IRS P W c₀ ztqri c ztfns Q := by
  unfold ifEq
  zubai
  · zuhcm
  · refine (IRS.ifF h1 ?_).mono (K := K + 2 + 2) by_omega ztb
    zubjz
    · zulxd
    · zulxc

/-! ## Frames -/

/-- The registers a candidate step may write (besides the oracle bands and the allocator). -/
def Alw (r : ℕ) : Prop :=
  ztdpo ∨ ztdpq ∨ ztbwg
theorem candFr_of {c c' : Config}
    (h : ∀ r, bandOf r ∉ oracleBands → ¬ Alw r → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) :
    CandFr c c' :=
  ⟨fun r h1 h2 h3 h4 h5 => h r h1 (by rintro (x | x | x) <;> tauto) h5, ha, hm⟩
theorem candFr_alw {c c' : Config} (h : CandFr c c') :
    ∀ r, bandOf r ∉ oracleBands → ¬ Alw r → r ≠ ALLOC → c'.nreg r = c.nreg r :=
  fun r h1 h2 h3 => h.1 r h1 (fun x => h2 ztvce) (fun x => h2 (Or.inr ztvce))
    (fun x => h2 (Or.inr (Or.inr x))) h3
theorem candFr_trans {c c₁ c₂ : Config} (h₁ : CandFr c c₁) (h₂ : CandFr c₁ c₂) : CandFr c c₂ :=
  candFr_of (fun r a b d => (candFr_alw h₂ r a b d).trans (candFr_alw h₁ r a b d))
    (h₁.2.1.trans h₂.2.1) (fun a ha => (h₂.2.2 a (by have := h₁.2.1; omega)).trans ztdux)

/-- The frame of a local hit. -/
theorem candFr_lhw {c c' : Config}
    (h : ∀ r, bandOf r ∉ oracleBands → ¬ LHW r → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) :
    CandFr c c' :=
  candFr_of (fun r a b d => h r a (by unfold LHW; unfold Alw sw at b; unfold sw; omega) d) ha hm

/-- The frame of a part. -/
theorem candFr_part {c c' : Config} (h : PartFr c c') : CandFr c c' :=
  candFr_of (fun r a b d => h.1 r a by_tauto
    ztjqp ztjqp d)
    h.2.1 h.2.2

/-- A frame that writes only allowed registers. -/
theorem candFr_regs {c c' : Config} {S : ℕ → Prop} (hS : ∀ r, S r → Alw r)
    (h : ∀ r, bandOf r ∉ oracleBands → ¬ S r → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) :
    CandFr c c' :=
  candFr_of by_grind ha hm

/-- The pipeline registers are kept. -/
theorem candFr_pipe {c c' : Config} (h : CandFr c c') {r : ℕ} (hr : sw 3200 ≤ r ∧ r < sw 3230) :
    c'.nreg r = c.nreg r :=
  candFr_alw h r ztzxh
    (by unfold Alw; unfold sw at hr ⊢; omega) (by unfold ALLOC; unfold sw at hr; omega)
theorem candFr_qE {c c' : Config} (h : CandFr c c') : c'.nreg qE = c.nreg qE :=
  candFr_pipe h by_decide
theorem candFr_qH {c c' : Config} (h : CandFr c c') : c'.nreg qH = c.nreg qH :=
  candFr_pipe h by_decide
theorem candFr_qD {c c' : Config} (h : CandFr c c') : c'.nreg qD = c.nreg qD :=
  candFr_pipe h by_decide
theorem candFr_bL {c c' : Config} (h : CandFr c c') : c'.nreg bL = c.nreg bL :=
  candFr_pipe h by_decide
theorem candFr_bR {c c' : Config} (h : CandFr c c') : c'.nreg bR = c.nreg bR :=
  candFr_pipe h by_decide
theorem candFr_qJ {c c' : Config} (h : CandFr c c') : c'.nreg qJ = c.nreg qJ :=
  candFr_pipe h by_decide

/-! ## The state after the local hit in the model of `C₂` -/
variable {J : Merge.Junction}

/-- **The state after the local hit in the model of `C₂`.** -/
def Mid (P : Polygon) (J : Merge.Junction) (z : Point) (c c' : Config) (L : Set ℝ) : Prop :=
  AccOK P accA ztdm J.whole.radius z ztba L c' ∧
    ztbalv ∧
    J.right.hitParam z ztba ∈ L ∧ CandFr c c'
variable {z : Point} {c' : Config} {L : Set ℝ}
/-- **A step that adds good candidates** keeps `Mid`. -/
theorem mid_step {c₂ c₃ : Config} {L L' : Set ℝ} (hM : Mid P J z c c₂ L)
    (hacc : AccOK P accA ztdm J.whole.radius z ztba
      L' c₃) (hsub : L ⊆ L')
    (hg : ∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.whole ztwod))
    (hF : CandFr c₂ c₃) : Mid P J z c c₃ L' :=
  ⟨hacc, fun τ hτ => (hg τ hτ).elim (fun h => hM.2.1 τ h) id, hsub hM.2.2.1,
    candFr_trans hM.2.2.2 hF⟩

/-- **The output**, from the first hit of `C₁` below its top. -/
theorem fin1 (hq : QState P J 1 z c)
    (hM : Mid P J z c c' L)
    (h1 : z.2 ≤ J.left.top.2 → J.left.hitParam z ztba ∈ L) :
    CandOut P J z c c' ∧ CandFr c c' := by
  obtain ⟨-, -, -, -, hz₂, -, -, hσ, -⟩ := q1_facts hq
  exact ⟨⟨L, hM.1, hM.2.1, whole_mem hσ hz₂ hq.hfree hM.2.2.1 h1⟩, hM.2.2.2⟩

/-- **The output**, from the table step. -/
theorem fin2 (hM : Mid P J z c c' L)
    (h : J.whole.hitParam z ztba ∈ L ∨
      J.whole.hitParam z ztba = J.right.hitParam z ztba) :
    CandOut P J z c c' ∧ CandFr c c' := by
  refine ⟨⟨L, hM.1, hM.2.1, ?_⟩, hM.2.2.2⟩
  zuy
  · zubh
  · zvmwc; exact hM.2.2.1

/-! ## The top edge of `C₂` -/

/-- A register outside `sw 4807 … 4813`. -/
def OutM (r : ℕ) : Prop := r < sw 4807 ∨ sw 4813 < r
set_option maxHeartbeats 1000000 in
theorem midB_irs (hI : IInv W c₀ c) (hK : Consts c) (hctx : ChainCtx P W c zted J.right) :
    IRS P W c₀ midB c 20 (fun c' => c'.nreg tgt = 6 + midT J.right ∧
      ztkih ∧ c'.nmem = c.nmem) := by
  obtain ⟨-, -, hwf, ⟨H, hC, -⟩, -, hWm⟩ := hctx
  obtain ⟨-, -, -, hm2, hti, hbt⟩ := hC
  have hB : c.nreg 240021 + 5 ≤ c.nreg ALLOC := hwf.1
  zuki
  have hT := J.right.topIdx_le
  obtain ⟨k0, k1, k6, k4, k5, k2', k3⟩ := hK
  have a2 : c.nmem (c.nreg 240021 + 2) = J.right.m := hm2
  have a3 : c.nmem (c.nreg 240021 + 3) = J.right.topIdx := hti
  have a4 : c.nmem (c.nreg 240021 + 4) = 1 ↔ J.right.sideBeta = true := hbt
  have kk2 : ztunw := k2'
  have kk3 : ztunx := k3
  have kk4 : ztlxs := k4
  have s : ∀ j, 4807 ≤ j → j ≤ 4813 → IScr ztgc := fun j h1 h2 =>
    iscr_sw ztce ztce
  -- the block
  have v : regB c.nmem midL c.nreg m2 = J.right.m ∧
      regB c.nmem midL c.nreg ti = J.right.topIdx ∧
      (regB c.nmem midL c.nreg bt = 1 ↔ J.right.sideBeta = true) ∧
      regB c.nmem midL c.nreg dd = 2 * J.right.topIdx ∧
      regB c.nmem midL c.nreg m2x = 2 * J.right.m ∧
      (∀ r, OutM r → regB c.nmem midL c.nreg r = c.nreg r) := by
    simp only [midL, regB, regI, upd, tmp, m2, ti, bt, dd, m2x, sw, K2, K3, K4]
    refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
    · simp_all
    · simp_all
    · simp_all
    · grind
    · grind
    · unfold OutM sw at hr
      grind
  obtain ⟨vm, vi, vb, vd, vx, vo⟩ := v
  have ok : okB W c.nmem midL c.nreg := by
    simp only [midL, okB, okI, regI]
    refine ⟨⟨s 4811 by_norm_num by_norm_num, ?_⟩, s 4808 by_norm_num by_norm_num,
      ⟨s 4811 by_norm_num by_norm_num, ?_⟩, s 4809 by_norm_num by_norm_num,
      ⟨s 4811 by_norm_num by_norm_num, ?_⟩, s 4810 by_norm_num by_norm_num,
      ⟨s 4812 by_norm_num by_norm_num, ?_⟩, ⟨s 4813 by_norm_num by_norm_num, ?_⟩, trivial⟩
    all_goals simp [upd, tmp, m2, ti, bt, dd, sw, K2, K3, K4, kk2, kk3, kk4, a2, a3]
    all_goals (have := J.right.topIdx_le; simp only [Merge.Junction.right_m] at hWm this; omega)
  refine IRS.seq (K₂ := 12) ((IRS.block midL hI ok).mono by_rfl
    ztb) ?_
  zuer
  have hb6 := k6
  have e6 : regB c.nmem midL c.nreg K6 = 6 := by
    tauto
  have e1 : regB c.nmem midL c.nreg K1 = 1 := by
    tauto
  have fin : ∀ (l : List Instr) (c₂ : Config), c₂ = { c with nreg := regB c.nmem midL c.nreg } →
      IInv W c₀ c₂ → l.length ≤ 2 → okB W c₂.nmem l c₂.nreg →
      (∀ i ∈ l, dstI i = tgt) →
      regB c₂.nmem l c₂.nreg tgt = 6 + midT J.right →
      IRS P W c₀ ztgfk c₂ 2 (fun c' => c'.nreg tgt = 6 + midT J.right ∧
        ztkih ∧ c'.nmem = c.nmem) := by
    intro l c₂ hc₂ hI₂ hlen hok hd hv
    refine (IRS.block l hI₂ hok).mono hlen ?_
    zuu
    refine ⟨hv, fun r hr => ?_, by zumxp⟩
    zubi
    rw [regB_other _ l _ (fun i hi h => by
      rw [hd i hi] at h; subst h; unfold OutM tgt sw at hr; omega)]
    simp_all
  have st : IScr tgt := s 4807 le_rfl by_norm_num
  refine irs_ifEq ztefa ztefa
  · zumpq
    have hβ : J.right.sideBeta = true := by_grind
    have hmid : midT J.right = 2 * J.right.m - 2 * J.right.topIdx := by unfold midT; grind
    refine (fin [.subN tgt m2x dd, .addN tgt tgt K6] _ rfl hI₁ by_simp ?_ ?_ ?_).mono
      by_norm_num by_grind
    · simp only [okB, okI, regI]
      refine ⟨st, ⟨st, ?_⟩, trivial⟩
      simp only [upd, tgt, m2x, dd, K6, sw] at *
      grind
    · decide
    · zudj
      simp only [upd, tgt, m2x, dd, K6, sw] at *
      grind
  · zumpq
    have hβ : J.right.sideBeta ≠ true := by_grind
    refine IRS.ite ztlof ztlof
    · zufpv

      have hmid : midT J.right = 2 * J.right.topIdx := by
        zujqq
      refine (fin [.addN tgt dd K6] _ rfl hI₁ by_simp ?_ ?_ ?_).mono
        by_norm_num by_grind
      · zudu
        grind
      · decide
      · zudj
        simp only [upd, tgt, dd, K6, sw] at *
        grind
    · zufpv

      have hmid : midT J.right = 0 := by
        zujqq
      refine (fin [.copyN tgt K6] _ rfl hI₁ by_simp ?_ ?_ ?_).mono
        by_norm_num by_grind
      · trivial
      · decide
      · zudj
        simp only [upd, tgt, K6, sw] at *
        grind
