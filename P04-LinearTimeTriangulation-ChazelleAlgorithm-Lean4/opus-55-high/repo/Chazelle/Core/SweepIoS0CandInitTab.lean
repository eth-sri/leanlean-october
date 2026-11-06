module

public import Chazelle.MacT
public import Chazelle.Core.SweepIoCand1B
public import Chazelle.Core.SweepIoLoop
public import Chazelle.Core.SweepEvStopSort3
public import Chazelle.Core.SweepEvGenR
public import Chazelle.Core.SweepEvStopFin6
public import Chazelle.Core.SweepIoLHit3
public import Chazelle.Core.SweepEvWinM2
public import Chazelle.Core.SweepEvOrg
public import Chazelle.Core.RestoreFComplete2
public import Chazelle.Core.FuseAsmMain
public import Chazelle.Core.SweepIoHoles
public import Chazelle.Core.SweepIoBruteLoop

namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep SweepEv
@[expose] public section
def kTb (κL TL : ℕ) : ℕ := 11141 + κL * zttdm
section tab
variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {Eb : ℕ} {c₀ c : Config} {rs : List ztcf}
  {ls : List ztck}
variable {lsS : Stmt} {κL : ℕ}
set_option maxHeartbeats 8000000 in
/-- **A table entry with flag `1`.** -/
theorem tbHit_irs (hls : LSBody lsS κL)
    (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c)
    (hB : c.nreg ipB = c₀.nreg ALLOC)
    (hAl : c₀.nreg ALLOC + 6 * c₀.nreg ztex ≤ c.nreg ALLOC)
    (hM5 : c.nreg ipM5 = 2 * J.right.m + 5) (hM6 : c.nreg ipM6 = 6 + midT J.right)
    {k s : ℕ} (hk : c.nreg ipJ = k) (hkK : k < N₂.nChords) (hs : c.nreg ipS = s) (hs1 : s ≤ 1)
    (ha : c.nreg ipA = c₀.nreg ztps + 3 * ztci)
    (hf : c.nmem ztyvu = 1)
    (hS : SInv P J N₂ ztzh ztwov ztwpq
      ztwpr ztdq c.nmem ztwuq ztci)
    (hroom : c.nreg ALLOC + kTb κL ztdg ≤ W) :
    IRS P W c₀ (tbHit lsS) c (kTb κL ztdg) (fun c' =>
      ztcxl ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      SInv P J N₂ ztzh ztwov ztwpq
        ztwpr ztdq c'.nmem ztwuq ztnfe) := by
  zuuj

  zugyq
  zulhz
  zubje

  have mc : ztezh :=
    fun d hd a ha => (hd.hm a ha).trans (hI.hm a ha).symm
  have hj : j < 2 * N₂.nChords := by_omega
  zulme
  zufbz
  obtain ⟨-, hpw⟩ := od.tw j hj
  have pw := hpw hf
  unfold tbHit
  -- the chord and the end
  have hb1 := IRS.block (P := P) [.copyN oK ipJ, .copyN oS ipS] hI (by
    zunje)
  refine IRS.seq (K₁ := 2) (K₂ := kTb κL ztdg - 2) hb1 ?_ |>.mono
    ztdmn ztb
  zufg
  set c₁ : Config := { c with nreg := regB c.nmem [.copyN oK ipJ, .copyN oS ipS] c.nreg }
    with hc₁
  have v1 : zthpp := fun r h1 h2 => by
    zunwy; rw [upd_other _ _ _ h2, upd_other _ _ _ h1]
  have vK : ztuqu := by
    tauto
  have vS : c₁.nreg oS = s := by
    tauto
  refine IRS.seq (K₂ := kTb κL ztdg - 2 - 11100)
    (orgHead_irs hI₁ e.hA.hK ztvpl e.hA.hNF₂ ztvpq le_rfl
      by_omega by_omega ztnvw) ?_ |>.mono
    ztdmn ztb
  zubpv
  zuhnq
  have k21 : ∀ r, bandOf r ∉ oracleBands → ztftx → r ≠ ALLOC →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 =>
    (fr₂ r h1 zteo h3).trans
      (v1 r ztmev ztmex)
  have mem2 : ztux := by_grind
  -- the class test
  zulik
  refine IRS.seq (K₂ := kTb κL ztdg - 2 - 11100 - 19) (cls_irs hI₂ hK₂) ?_
    |>.mono (by unfold kTb; omega) (fun _ h => h)
  rintro c₃ hI₃ hA₃ hA₃' ⟨vV, vV1, fr₃, hm₃⟩
  have e5 :=
    (k21 _ ztmr
      by_decide by_decide).trans hM5
  have e6 :=
    (k21 _ ztmr
      by_decide by_decide).trans hM6
  have e41 : c₂.nreg _ = cstR J 1 := (e.fix hI₂ by_norm_num).trans e.st0.2.1
  rw [e5, e6, e41, vE, vC, ← valid_test e.hA.hP e.hA.hNF₂ hkK hs1] at vV
  have k3 : ∀ r, bandOf r ∉ oracleBands → ztftx → r ≠ ALLOC → r ≠ ipV →
      c₃.nreg r = c.nreg r := by_grind
  have mem3 : ztblg := fun a ha => by
    grind
  have hp3 : ∀ r, PReg r → c₃.nreg r = c.nreg r := fun r hr => by
    apply k3 r
    · rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        exact not_oracle_sw by_decide
          by_decide
    · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [ipB, ipM6, ipM5, ipJ, ipKc, sw]
    · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [ipB, ipM6, ipM5, ipJ, ipKc, ALLOC, sw]
    · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [ipB, ipM6, ipM5, ipJ, ipKc, ipV, sw]
  have hK₃ := e.hA.hK.fix hI₃
  by_cases hv : c₃.nreg ipV < c₃.nreg K1
  · -- not regular
    have hv0 : ¬ ValidO J zta N₂ j := by
      intro h; have := vV.2 h; rw [this, hK₃.2.1] at hv; omega
    refine (IRS.ifT (K := 0) hv (IRS.skip hI₃ ⟨hp3, by_omega, ?_⟩)).mono
      ztdmn ztb
    exact (hS.congr by_grind by_omega by_omega by_omega).tabSkip
      by_grind
  -- regular
  have hvo : ValidO J _ N₂ j := vV.1 (by rw [hK₃.2.1] at hv; omega)
  refine IRS.ifF (K := kTb κL ztdg - 2 - 11100 - 19 - 2) hv ?_ |>.mono
    ztdmn ztb
  have a3 := (k3 _ (not_oracle_sw by_decide
    by_decide) by_decide by_decide
    by_decide).trans ha
  refine IRS.seq (K₂ := kTb κL ztdg - 2 - 11100 - 19 - 2 - 6)
    (tbTg_irs hI₃ hK₃ a3 by_omega) ?_ |>.mono ztdmn ztb
  rintro c₄ hI₄ hA₄ hA₄' ⟨g1, g2, g3, g4, gfr, gm⟩
  have q1 : c₄.nreg lsxE = c.nmem ztbjf := by rw [g3, mem3 _ by_omega]
  have q2 : c₄.nreg lsxH = c.nmem ztclb := by rw [g4, mem3 _ by_omega]
  refine IRS.seq (K₂ := 12)
    (e.search hls hI₄ by_grind ztnvw) ?_ |>.mono
    ztdmn ztb
  rintro c₅ hI₅ hA₅ hA₅' ⟨s1, s2, sfr, sA, sm⟩
  have hq : (⟨c₄.nreg lsxE, c₄.nreg lsxH⟩ : WPos) =
      ⟨c₄.nmem ztwtm, c₄.nmem ztwzg⟩ := by
    grind
  zujju
  have od₄ := e.odc hI₄.hm
  simp only [rd_sw] at od₄
  have hf₄ : c₄.nmem ztxut = 1 := by rw [mc c₄ hI₄ _ by_omega]; exact hf
  obtain ⟨ht, e1, e2, hvl⟩ := tab_step od₄ e.hA.hNF₂ rfl hkK hs1 hvo hf₄ s1 s2
  -- registers after the search
  have k5 : ∀ r, sw 4100 ≤ r → r ≤ sw 4129 → r ≠ ipV → r ≠ ipE → r ≠ ipH → r ≠ ipA →
      c₅.nreg r = c.nreg r := by
    intro r h1 h2 n1 n2 n3 n4
    rw [sfr r ztxxs
      ztmel ztum,
      gfr r n2 n3 n4 ztmet ztmeu]
    exact k3 r ztxxs
      zteo ztum n1
  have k5S := (k5 ipS by_decide by_decide
    by_decide by_decide by_decide
    by_decide).trans hs
  have k5B := (k5 ipB by_rfl by_decide
    by_decide by_decide by_decide
    by_decide).trans hB
  have k5E : c₅.nreg ipE = c₃.nreg oE := by
    rw [sfr _ ztmr
      (by unfold LSet ipE sw; omega) by_decide, g1]
  have k5H : c₅.nreg ipH = c₃.nreg oC := by
    rw [sfr _ ztmr
      (by unfold LSet ipH sw; omega) by_decide, g2]
  have c3E : c₃.nreg oE = (endPos N₂ k s).edge := by
    zuopf; exact vE
  have c3C : c₃.nreg oC = nhgt ztj zta ztlnp := by
    zuopf; exact vC
  have hK₅ := e.hA.hK.fix hI₅
  refine (slotSt_irs hI₅ hK₅ k5B rfl k5S le_rfl (by
    omega)).mono le_rfl ?_
  zuewf
  have wA := w2 ALLOC by_decide
  refine ⟨fun r hr => ?_, by_omega, ?_⟩
  · have hT : r ≠ ipT := by
      zublk
    rw [w2 r hT]
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact k5 _ by_decide
        by_decide
        by_decide
        by_decide
        by_decide
        by_decide
  · zumpe
    have m5 : ∀ a, a < B + 6 * E → c₅.nmem a = c.nmem a := fun a ha => by
      rw [sm a by_omega, gm, mem3 a by_omega]
    have hS₅ := hS.congr m5 by_omega by_omega by_omega
    have hv' : SlotVal P J ⟨c₅.nreg ipE, c₅.nreg ipH⟩ (ztci % 2)
        (logPt P J c₄.nmem AL (c₅.nreg lsI)) := by
      rw [k5E, k5H, c3E, c3C, show ztci % 2 = s by omega]
      omega
    have h := hS₅.tabStep (fun a ha => (mc c₄ hI₄ a ha).trans
      (mc c₅ hI₅ a ha).symm) by_omega by_omega by_omega ht e1 e2 hv'
    rw [show ztci % 2 = s by omega] at h
    zubh
set_option maxHeartbeats 4000000 in
/-- **A table entry.** -/
theorem tbOne_irs (hls : LSBody lsS κL)
    (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c)
    (hB : c.nreg ipB = c₀.nreg ALLOC)
    (hAl : c₀.nreg ALLOC + 6 * c₀.nreg ztex ≤ c.nreg ALLOC)
    (hM5 : c.nreg ipM5 = 2 * J.right.m + 5) (hM6 : c.nreg ipM6 = 6 + midT J.right)
    {sr k s : ℕ} (hsr : sr = K0 ∨ sr = K1) (hsv : c.nreg sr = s) (hs1 : s ≤ 1)
    (hk : c.nreg ipJ = k) (hkK : k < N₂.nChords)
    (hS : SInv P J N₂ ztzh ztwov ztwpq
      ztwpr ztdq c.nmem ztwuq ztci)
    (hroom : c.nreg ALLOC + ztwuy ≤ W) :
    IRS P W c₀ (tbOne lsS sr) c ztwuy (fun c' =>
      ztcxl ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      SInv P J N₂ ztzh ztwov ztwpq
        ztwpr ztdq c'.nmem ztwuq ztnfe) := by
  have htw := e.hA.htabw
  simp only [rd_sw] at htw
  zudni
  have hWc := hI.hw.1 ALLOC
  have hsr' : sr < sw 4100 ∨ sw 4129 < sr := by
    rcases hsr with rfl | rfl <;> simp [K0, K1, sw]
  unfold tbOne
  refine IRS.seq (K₂ := kTb κL ztdg + 2)
    (tbLd_irs hI hsr' (e.fix hI by_norm_num) hk hsv by_omega) ?_ |>.mono
    by_omega ztb
  rintro c₁ hI₁ hA₁ hA₁' ⟨l1, l2, l3, lfr, lm⟩
  have hp1 : ∀ r, PReg r → c₁.nreg r = c.nreg r := fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact lfr _ by_decide
        by_decide
        by_decide
        by_decide
  have hS₁ : SInv P J N₂ ztzh ztwov ztwpq
      ztwpr ztdq c₁.nmem ztwuq ztci := by
    simp_all
  zulih
  by_cases hf : c₁.nreg ipF < c₁.nreg K1
  · refine (IRS.ifT (K := 0) hf (IRS.skip hI₁
      ⟨hp1, hA₁, hS₁.tabSkip (fun h => by rw [l3, ← lm] at hf; rw [hK₁.2.1] at hf; omega)⟩)).mono
      by_omega ztb
  · zulme
    zufbz
    have hfl := (od.tw ztci by_omega).1
    have hf1 : c₁.nmem ztyvu = 1 := by
      rw [lm]; rw [l3, hK₁.2.1] at hf; omega
    refine IRS.ifF hf ?_
    refine (tbHit_irs hls e hI₁ ((hp1 _ ztp).trans hB) by_omega
      ((hp1 _ ztbh).trans hM5) ((hp1 _ ztwiz).trans hM6)
      ((hp1 _ ztbh).trans hk) hkK l1 hs1 l2 hf1 hS₁
      by_omega).mono le_rfl ?_
    grind
set_option maxHeartbeats 4000000 in
/-- **The two entries of a chord.** -/
theorem tbB_irs (hls : LSBody lsS κL)
    (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c)
    (hB : c.nreg ipB = c₀.nreg ALLOC)
    (hAl : c₀.nreg ALLOC + 6 * c₀.nreg ztex ≤ c.nreg ALLOC)
    (hM5 : c.nreg ipM5 = 2 * J.right.m + 5) (hM6 : c.nreg ipM6 = 6 + midT J.right)
    (hkK : c.nreg ipJ < N₂.nChords)
    (hS : SInv P J N₂ ztzh ztwov ztwpq
      ztwpr ztdq c.nmem ztwuq (2 * c.nreg ipJ))
    (hroom : c.nreg ALLOC + ztbaoz ≤ W) :
    IRS P W c₀ (tbB lsS) c ztbaoz (fun c' =>
      c'.nreg ipJ = c.nreg ipJ + 1 ∧ (∀ r, PReg r → r ≠ ipJ → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      SInv P J N₂ ztzh ztwov ztwpq
        ztwpr ztdq c'.nmem ztwuq (2 * (c.nreg ipJ + 1))) := by
  zulhz
  unfold tbB
  refine IRS.seq (K₂ := kTb κL ztdg + 9 + 1)
    (tbOne_irs hls e hI hB hAl hM5 hM6 ztp hK.1 by_norm_num rfl hkK
      by_omega by_omega) ?_ |>.mono by_omega (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨g1, g2, g3⟩
  zulih
  have pJ : PReg ipJ := Or.inr by_omega
  refine IRS.seq
    (tbOne_irs hls e hI₁ ((g1 _ ztp).trans hB) by_omega
      ((g1 _ ztbh).trans hM5) ((g1 _ ztwiz).trans hM6)
      ztbt hK₁.2.1 le_rfl by_simp_all hkK g3 by_omega) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨h1, h2, h3⟩
  zulik
  have j2 : c₂.nreg ipJ = c.nreg ipJ := by_simp_all
  refine (IRS.instr1 (i := .addN ipJ ipJ K1) hI₂ ⟨iscr_sw by_decide
    by_decide, by
      zuopg; have := hI.hw.1 ALLOC; have := e.hA.htabw; omega⟩).mono le_rfl ?_
  zuu
  refine ⟨?_, fun r hr hrJ => ?_, ?_, ?_⟩
  · zuneg; zuopg
  · zuwc
    simp_all
  · zuwc
    zunbw; omega
  omega

/-- **The table loop.** -/
theorem tbLoop_irs (hls : LSBody lsS κL)
    (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c)
    (hB : c.nreg ipB = c₀.nreg ALLOC)
    (hAl : c₀.nreg ALLOC + 6 * c₀.nreg ztex ≤ c.nreg ALLOC)
    (hM5 : c.nreg ipM5 = 2 * J.right.m + 5) (hM6 : c.nreg ipM6 = 6 + midT J.right)
    (hJ : c.nreg ipJ = 0) (hKc : c.nreg ipKc = N₂.nChords)
    (hS : SInv P J N₂ ztzh ztwov ztwpq
      ztwpr ztdq c.nmem ztwuq 0)
    (hroom : c.nreg ALLOC + ztbapa * N₂.nChords ≤ W) :
    IRS P W c₀ ztwgq c (ztbapa * N₂.nChords + 2)
      (fun c' => c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ipB = c.nreg ipB ∧
        SInv P J N₂ ztzh ztwov ztwpq
          ztwpr ztdq c'.nmem ztwuq ztbxu) := by
  let I : Config → Prop := fun d => (∀ r, PReg r → r ≠ ipJ → d.nreg r = c.nreg r) ∧
    c.nreg ALLOC ≤ d.nreg ALLOC ∧ d.nreg ipJ ≤ N₂.nChords ∧
    SInv P J N₂ ztzh ztwov ztwpq
      ztwpr ztdq d.nmem ztwuq (2 * d.nreg ipJ)
  have pKc : PReg ipKc := Or.inr by_omega
  have nKc : ipKc ≠ ipJ := by_decide
  have h := IRS.while (a := ipJ) (b := ipKc) I
    (fun d => N₂.nChords - d.nreg ipJ) _
    by_grind
    (fun d hId hd hlt hr => by
      obtain ⟨d1, d2, d3, d4⟩ := hd
      rw [d1 _ pKc nKc, hKc] at hlt
      refine (tbB_irs hls e hId ((d1 ipB ztp by_decide).trans hB)
        by_omega ((d1 ipM5 ztbh by_decide).trans hM5)
        ((d1 ipM6 ztwiz by_decide).trans hM6) hlt d4
        hr).mono le_rfl ?_
      grind)
    hI by_grind by_simp_all
  rw [hJ] at h
  zujnu
  zuevu
  rintro d ⟨⟨d1, d2, d3, d4⟩, d5⟩
  rw [d1 _ pKc nKc, hKc] at d5
  have : d.nreg ipJ = N₂.nChords := by_omega
  zvmwk at d4
  exact ⟨d2, d1 _ ztp by_decide, d4⟩
end tab
end
end S0C
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep SweepEv
@[expose] public section
theorem auxCore_of_sinv {P : Polygon} {J : Merge.Junction} {N₂ : NF} {c : Config}
    (h1 : c.nreg sB + 6 * c.nreg ztex ≤ c.nreg ALLOC)
    (h2 : c.nreg ztfx + 7 * c.nreg ztex ≤ c.nreg ALLOC)
    (h3 : c.nreg ztcwm + 5 * c.nreg ztsn ≤ c.nreg ALLOC)
    (h4 : c.nreg ztps + 3 * ztbxu ≤ c.nreg ALLOC)
    (hS : SInv P J N₂ ztzdz ztwml ztxcl ztzea
      zthvm c.nmem ztxwg ztbxu) : AuxCore P J N₂ c :=
  ⟨h1, h2, h3, h4, hS.1, hS.2.1, hS.2.2⟩

/-- `midT` from the fields of the chain descriptor. -/
theorem midT_desc {C : Chain} {m : ℕ → ℕ} {B : ℕ} {Q : Polygon} {H : Host}
    (h : ChainDescAt m B Q H C) :
    (if m ztow = 1 then 2 * m zthb - 2 * m ztkh
      else if m ztkh < m zthb then 2 * m ztkh else 0) = midT C := by
  obtain ⟨-, -, -, h2, h3, h4⟩ := h
  rw [h2, h3]
  unfold midT
  simp_all

/-- The cost constant. -/
def kIn (κL : ℕ) : ℕ := 30000 + 2 * κL
theorem cost_le (κL S E K t : ℕ) (ht : 1 ≤ t) :
    27 + ztldm + ((kSt κL ztso + 2) * S + 2) +
        ((2 * (kTb κL ztso + 9) + 3) * K + 2) + 1 ≤
      kIn κL * (S + E + 2 * K + 1) * t := by
  zucyb
  zudli
  unfold kSt kTb kIn
  grind

/-- The cost of the run part of the initialisation. -/
def kRun (κL TL S E K : ℕ) : ℕ :=
  27 + ztldm + ((kSt κL TL + 2) * S + 2) + ((2 * (kTb κL TL + 9) + 3) * K + 2)
section main
variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {Eb : ℕ} {c : Config} {rs : List ztcf}
  {ls : List ztck}
set_option maxHeartbeats 8000000 in
/-- **The run part of the initialisation** (all but the final write of `sw 620`). -/
theorem body_irs {lsS : Stmt} {κL : ℕ} (hls : LSBody lsS κL)
    (e : IE P W X Ok J H N₁ N₂ Eb c rs ls) (hw : WordsBounded W c)
    (hroom : c.nreg ALLOC + kRun κL zterd ztxwg ztxcl
      N₂.nChords + 1 ≤ W) :
    IRS P W c (.seq hdr (.seq zeroLoop (.seq ztwfb ztwgq))) c
      (kRun κL zterd ztxwg ztxcl N₂.nChords) (fun c' =>
        c'.nreg ipB = c.nreg ALLOC ∧ c.nreg ALLOC + 6 * c.nreg ztex ≤ c'.nreg ALLOC ∧
        SInv P J N₂ ztzdz ztwml ztxcl ztzea
          ztm c'.nmem ztxwg ztbxu) := by
  have hI0 : ztulb := ⟨hw, fun _ _ => rfl, le_rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have hK := e.hA.hK
  obtain ⟨-, -, -, -, -, -, -, -, d21, w21, -⟩ := e.hA.hst
  have hWc := hw.1 ALLOC
  have hd : c.nreg zted + 5 ≤ W := by have := w21.1; omega
  have f2 := d21.2.2.2.1
  have f3 := d21.2.2.2.2.1
  have hTm : c.nmem ztwya ≤ c.nmem ztwpc := by
    rw [f2, f3]; exact J.right.topIdx_le
  have hWm := e.hA.hWm
  have hmm : ztmti := sideChain_m_le J 1
  have h2m : 2 * c.nmem ztwpc + 6 ≤ W := by_omega
  have hst := e.st0
  unfold kRun at hroom ⊢
  refine (IRS.seq (K₁ := 27) (K₂ := (4 * ztzjr + 2) + (ztxrw + ztcgi))
    (hdr_irs hI0 hK hd by_omega hTm h2m) ?_).mono by_omega (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩
  have c1A : ztdc := a8 _ ztbuo
  zuiwf
  refine IRS.seq (K₁ := 4 * ztzjr + 2) (K₂ := ztxrw + ztcgi) ((zeroLoop_irs hI₁ hK₁ a2 by_omega
    by_omega).mono by_omega (fun _ h => h)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨z1, z2, z3, z4⟩
  rw [c1A] at z3
  have nA : ∀ r, r = ipB ∨ r = ipX ∨ r = ipJ ∨ r = ipKc ∨ r = ipM5 ∨ r = ipM6 → r ≠ ALLOC := by
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [ipB, ipX, ipJ, ipKc, ipM5, ipM6, ALLOC, sw]
  have b2 : c₂.nreg ipB = c.nreg ALLOC := (z2 _ (nA _ ztp)).trans a1
  have hS₂ : SInv P J N₂ ztzdz ztwml ztxcl
      ztzea ztm c₂.nmem 0 0 :=
    SInv.zero (fun a h1 h2 => z3 a h1 by_omega)
  have hfix : ∀ k, k < 700 → c.nreg ztcbe = c.nreg ztcbe := fun _ _ => rfl
  refine IRS.seq (K₁ := (kSt κL zterd + 2) * c.nreg ztsn + 2) (K₂ := ztcgi)
    (stLoop_irs hls e hI₂ b2 by_omega ((z2 _ (nA _ ztwiz)).trans a3) hS₂
      by_omega) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨p1, p2, p3⟩
  have pr : ∀ r, PReg r → c₃.nreg r = c₁.nreg r := fun r hr => by
    rw [p1 r hr]
    exact z2 r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [ipB, ipJ, ipKc, ipM5, ipM6, ALLOC, sw])
  refine (tbLoop_irs hls e hI₃ ztynt by_omega
    ((pr _ ztbajm).trans by_omega)
    ((pr _ ztwiz).trans (by rw [a7, midT_desc d21]; omega))
    ((pr _ ztbaje).trans a4)
    ((pr _ ztbakw).trans (a5.trans e.hA.hK₂)) p3
    by_omega).mono le_rfl ?_
  rintro c' ⟨t1, t2, t3⟩
  exact ⟨t2.trans ztynt, by_omega, t3⟩
set_option maxHeartbeats 4000000 in
/-- **The initialisation of the side-0 stop and table candidates.** -/
theorem initPart (hL : LSearchSpec) : InitPartSpec := by
  obtain ⟨lsS, κL, hls⟩ := hL
  refine ⟨initC lsS, fun _ => kIn κL, fun P W X Ok J H N₁ N₂ Eb c hw hA hroom => ?_,
    fun P J N₂ c v h => aux_sw11 h⟩
  obtain ⟨rs, ls, od⟩ := OD.of_out hA.hout
  have e : IE P W X Ok J H N₁ N₂ Eb c rs ls := ⟨hA, od⟩
  simp only [rd_sw] at hroom ⊢
  have hcost := cost_le κL ztxwg ztxcl N₂.nChords ztuc
    by_omega
  simp only [Nat.add_sub_cancel] at hcost
  obtain ⟨c₁, k₁, ex₁, hk₁, hI₁, hfr₁, q1, q2, q3⟩ :=
    body_irs hls e hw (by unfold kRun; omega)
  unfold kRun at hk₁
  have ex := Exec.seq ex₁ (Exec.copyN (P := P) hI₁.hw sB ipB)
  obtain ⟨r₁, rr₁, o₁, a₁, b₁⟩ := hfr₁
  have nS : ∀ r, bandOf r ∉ sweepBands ∪ oracleBands → r ≠ sB := by
    rintro r hr rfl
    zuitp
  have hsA : ALLOC ≠ sB := by_decide
  refine ⟨_, k₁ + 1, ex, by_omega, ?_, fun j hj hj' => ?_, ?_⟩
  · refine ⟨fun r hr hra => ?_, fun r hr => rr₁ r hr, fun a ha => hI₁.hm a ha,
      fun a ha => hI₁.hrm a ha, o₁, ?_, ?_⟩
    · zubi
      rw [upd_other _ _ _ (nS r hr)]
      exact r₁ r hr hra
    · simp only; zuocb; exact a₁
    · simp only; zuocb; omega
  · zubi
    zufok

  · apply aux_of_core
    have fx : ∀ k, k < 700 → k ≠ 620 →
        zthkv ztcbe = c.nreg ztcbe := fun k hk h620 => by
      zufok

    have hB : zthkv sB = c.nreg ALLOC := by rw [upd_same, q1]
    have hAl : zthkv ALLOC = c₁.nreg ALLOC := upd_other _ _ _ hsA
    zuerf
    have hst := hA.hstops
    zumey
    simp only [rd_sw] at hlog hst htw
    refine auxCore_of_sinv ?_ ?_ ?_ ?_ ?_
    · zubi
      rw [hB, hAl, fx 301 by_norm_num by_norm_num]; exact q2
    · zubi
      rw [hAl, fx 300 by_norm_num by_norm_num, fx 301 by_norm_num by_norm_num]; omega
    · zubi
      rw [hAl, fx 200 by_norm_num by_norm_num, fx 201 by_norm_num by_norm_num]; omega
    · grind
    grind
end main
theorem initPartSpec : InitPartSpec := initPart lsearchSpec
end
end S0C
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Set
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt SideAttach)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {E : ℕ} {c₀ c : Config}

/-- The cost of the slot part. -/
def hitK : ℕ := 7 + ztjfy
theorem onCB_whole_of_right {x : Point} (h : OnCB J.right x) : OnCB J.whole x := by
  zude
  · zulel
  · tauto
  tauto
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The slot part.** -/
theorem hit_irs (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hX : AuxCore P J N₂ c₀) (hI : IInv W c₀ c)
    {z : Point} {L : Set ℝ} (ht : c.nreg lsI < rd c₀ bSweep 301)
    (hpt : logPt P J c₀.nmem ztjt ztmgw = z)
    (hz : z ∈ J.left.set) (hzs : z ≠ J.shared) (hz2 : z.2 ≤ J.right.top.2)
    (hacc : AccOK P accA ztcys J.whole.radius z ztba L c)
    (hroom : c.nreg ALLOC + hitK ≤ W) :
    IRS P W c₀ cHit c hitK (fun c' => ∃ L', AccOK P accA ztcys J.whole.radius z
        ztba L' c' ∧ L ⊆ L' ∧
      ztwjm ∧
      (c₀.nmem (slotA ztghy ztmgw ztzgt) = 1 → ∀ τ, 0 < τ →
        (chainModel J.right).pos zta
          ⟨c₀.nmem (slotA ztghy ztmgw ztzgt + 1),
            c₀.nmem (slotA ztghy ztmgw ztzgt + 2)⟩ =
          rayPt z ztba τ → τ ∈ L') ∧
      FrQ c c') := by
  zudnn
  zuhx
  zuene

  set B := c₀.nreg sB with hBdef
  set s := qS d with hsdef
  set S := slotA B t s with hSdef
  zujne
  zubkr
  obtain ⟨b1, -, -, -, hsl, -, -⟩ := hX
  rw [rd_sw] at b1
  have hBc : c.nreg sB = B := hI.hin _ by_trivial
  zukdk
  zuivq
  zubnp
  have hE' : t < c₀.nreg ztex := ht
  have hS6 : S + 3 ≤ B + 6 * c₀.nreg ztex := by
    zunre; unfold slotA; have := qS_le d; nlinarith
  have hslot : SlotOK P J c₀.nmem B ztjt t s := hsl t ht s ztwcc
  -- the slot address
  have hok1 : okB W c.nmem cSlot c.nreg := cSlot_ok _ _ by_omega
  refine IRS.mono (K := cSlot.length + ztjfy) (IRS.seq
    (IRS.block cSlot hI hok1) ?_) by_rfl (fun _ h => h)
  zufg
  obtain ⟨v1S, k1⟩ := cSlot_val c.nmem c.nreg
  rw [hBc] at v1S
  set c₁ : Config := { c with nreg := regB c.nmem cSlot c.nreg } with hc₁
  zuiwf
  have hAc₁ : ztdc := k1 ALLOC by_decide
  have hd₁ : c₁.nreg qD = d := k1 qD by_decide
  refine IRS.seq (K₁ := 5) (cDir_irs hI₁ hK₁ (by
    grind)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨v2S, k2, hm2⟩
  zvnes at v2S
  have v2S' : c₂.nreg kS = S := by
    rw [v2S]; show regB c.nmem cSlot c.nreg kS + 3 * qS d = S
    rw [v1S, hSdef]; rfl
  have hK₂ : Consts c₂ := hK.fix hI₂
  have hok3 : okB W c₂.nmem cRead c₂.nreg := cRead_ok _ _ hK₂.2.1 by_omega
  refine IRS.seq (K₁ := cRead.length) (IRS.block cRead hI₂ hok3) ?_
  zubup
  obtain ⟨v3F, v3E, v3H, k3⟩ := cRead_val c₂.nmem c₂.nreg hK₂.2.1
  set c₃ : Config := { c₂ with nreg := regB c₂.nmem cRead c₂.nreg } with hc₃
  rw [v2S'] at v3F v3E v3H
  have hm₂ : ∀ a, a < c₀.nreg ALLOC → c₂.nmem a = c₀.nmem a := hI₂.hm
  have hF : c₃.nreg kF = c₀.nmem S := by
    grind
  have hPe : c₃.nreg kPe = c₀.nmem ztbgu := by
    grind
  have hPh : c₃.nreg kPh = c₀.nmem ztenx := by
    grind
  -- registers through the three steps
  have keep : ∀ q, q ≠ kS → q ≠ kF → q ≠ kPe → q ≠ kPh → c₃.nreg q = c.nreg q := by
    grind
  have nk : ∀ q, (q < sw 4100 ∨ sw 4111 < q) → c₃.nreg q = c.nreg q := fun q hq =>
    keep q (by unfold kS sw at *; omega) (by unfold kF sw at *; omega)
      (by unfold kPe sw at *; omega) (by unfold kPh sw at *; omega)
  have hAc₃ : ztcke := nk ALLOC by_decide
  have hd₃ : c₃.nreg qD = d := nk qD by_decide
  have hk1₃ : ztizo := hK.fix hI₃ |>.2.1
  have hk0₃ : c₃.nreg K0 = 0 := hK.fix hI₃ |>.1
  have hacc₃ : AccOK P accA ztcys J.whole.radius z σ L c₃ :=
    hacc.transport (fun j hj => nk ztbzh zthk)
  have hfr₃ : FrQ c c₃ := ⟨fun r _ hr _ => keep r ztchv
      ztchv
      ztchv
      ztchv, hAc₃.ge,
    fun a ha => by rw [hm2]⟩
  have hfl : c₀.nmem S ≤ 1 := hslot.1
  unfold cOffer
  by_cases hf : c₃.nreg K0 < c₃.nreg kF
  · -- a flagged slot: offer its origin
    rw [hk0₃, hF] at hf
    have hf1 : c₀.nmem S = 1 := by_omega
    obtain ⟨he, hpp, hc⟩ := hslot.2 hf1
    zukvt
    obtain ⟨hτ, hpos⟩ := cand_ray ztvox hc (z_mem_right_dom hA.hP hz hzs hz2)
      ztwic
    set τs := J.whole.hitParam ((chainModel J.right).pos zta ⟨c₀.nmem ztbgu, c₀.nmem ztenx⟩)
      ztmiq with hτs
    have hds : -dS s = σ := by rw [hsdef, dS_qS, neg_neg]
    rw [hds] at hpos
    have hMod : ModB J 1 1 ztqkn = J.right := by rw [hk1₃]; rfl
    have hctx₃ : ChainCtx P W c₃ zted (ModB J 1 1 ztqkn) := by
      zupdl; exact hA.ctxR hI₃
    have hn₃ : c₃.nreg zthy = 2 * (ModB J 1 1 ztqkn).m + 7 := by
      rw [hMod, hI₃.hin _ by_trivial]
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h34, -⟩ := hA.hst
      omega
    have hy : |z.2| < J.whole.radius := (J.left.set_subset_box hz).2
    refine (IRS.ifT by_omega (offerF_irs (L := L) (τ := τs) hI₃ hK hA.hG
      (by have := hA.hWh; unfold hostWords at this; omega)
      ⟨by_decide, by_decide⟩
      ⟨by_decide, by_decide, by_decide,
        by decide, by_decide, by_decide,
        by decide, by_decide, by_decide,
        by decide, by_decide, by_decide,
        by decide, by_decide⟩
      ⟨by_decide, by_decide,
        by decide, by_decide,
        by decide, by_decide,
        by decide, by_decide, by_decide,
        by decide, by_decide, by_decide,
        by decide, by_decide, by_decide,
        by decide, by_decide⟩
      ⟨by_decide, by_decide,
        by decide, by_decide,
        by decide, by_decide⟩
      by_grind by_omega hctx₃ (by zupdl; rfl) hn₃
      by_grind by_grind
      by_grind hy
      (by rw [hAc₃]; unfold hitK at hroom; omega))).mono by_omega ?_
    rintro c' ⟨⟨L', hacc', hL', hins⟩, hk', hal', hm'⟩
    rw [hd₃] at hacc'
    have hL'eq : L' = insert τs L := hins by_grind
    refine ⟨L', hacc', by rw [hL'eq]; simp, fun τ hτ' => ?_,
      fun _ τ hτ0 hτe => ?_, ?_⟩
    · rcases hL' with rfl | ⟨-, hon⟩
      · grind
      · rw [hL'eq] at hτ'
        rcases hτ' with rfl | h
        · rw [hMod, hd₃] at hon; exact Or.inr ⟨hτ, onCB_whole_of_right hon⟩
        grind
    · rw [hL'eq]
      have : τ = τs := rayPt_param hσ (by rw [← hτe, ← hpos])
      zukyy
    · refine hfr₃.trans ⟨fun r hr hq hra => hk' r hr (by
          unfold QSet at hq; unfold accA sw at *; omega)
        ztof
        ztof
        ztof hra, hal', hm'⟩
  · -- an empty slot
    have hf0 : c₀.nmem S = 0 := by_omega
    refine (IRS.ifF hf (IRS.skip (K := 0) hI₃ ⟨L, hacc₃, le_rfl, fun τ h => Or.inl h,
      fun h => absurd (hf0 ▸ h) by_norm_num, hfr₃⟩)).mono by_omega
      ztb
end
end S0C
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Set
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt SideAttach)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {E : ℕ} {c₀ c : Config}

/-- **The completeness of the slot read** (the hypothesis of `compl_of`). -/
def HC (P : Polygon) (J : Merge.Junction) (c₀ : Config) (z : Point) (zp zh d : ℕ) (L' : Set ℝ) :
    Prop :=
  ∀ i, i < rd c₀ bSweep 301 → c₀.nmem ztglr = zp →
    (chainModel J.whole).param zta ztwye =
      (chainModel J.whole).param zta ztyf →
    c₀.nmem ztznw = 1 →
    ∀ (o : Point) (τ : ℝ), CandAt J o ztbahh z → 0 < τ → o = rayPt z ztwf τ → τ ∈ L'

/-- The cost of the check. -/
def checkK : ℕ := 11 + (11008 + ztnfh)
theorem key_of_match {i zp zh : ℕ} {m : ℕ → ℕ} {AL : ℕ} (h1 : m ztbdu = zp)
    (h2 : (chainModel J.whole).param zta ztbwa =
      (chainModel J.whole).param zta ztyf) :
    (chainModel J.whole).key zta ztbwa =
      (chainModel J.whole).key zta ztyf := by
  unfold Model.key; zvmxx; tauto
theorem gW_lt_nat (J : Merge.Junction) : gW J < (chainModel J.whole).W.n := by
  have := gW_lt J; simp_all
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The check of the record found and the slot part.** -/
theorem check_irs (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hX : AuxCore P J N₂ c₀)
    (hI : IInv W c₀ c) {z : Point} {L : Set ℝ} {zp zh : ℕ}
    (hz : z ∈ J.left.set) (hzs : z ≠ J.shared) (hz2 : z.2 ≤ J.right.top.2)
    (hzP : zp < (chainModel J.whole).W.n)
    (hzPp : ProperPos ztbm zta P.n ztyf)
    (harr : Arrival (chainModel J.whole).W z ztwtj zp
      ztwyz)
    (hxE : c.nreg lsxE = zp) (hxH : c.nreg lsxH = zh)
    (ht : c.nreg lsI < rd c₀ bSweep 301)
    (hs1 : ∀ j, j < c.nreg lsI →
      lsPr P J c₀.nmem ztjt ztwnj ztyf j)
    (hs2 : ∀ j, c.nreg lsI ≤ j → j < rd c₀ bSweep 301 →
      ¬ lsPr P J c₀.nmem ztjt ztwnj ztyf j)
    (hacc : AccOK P accA ztcys J.whole.radius z ztba L c)
    (hroom : c.nreg ALLOC + checkK ≤ W) :
    IRS P W c₀ cCheck c checkK (fun c' => ∃ L', AccOK P accA ztcys J.whole.radius z
        ztba L' c' ∧ L ⊆ L' ∧
      ztwjm ∧
      HC P J c₀ z zp zh ztql L' ∧ FrQ c c') := by
  zudnn
  zuhx
  zuene

  set AL := rd c₀ bSweep 300 with hAL
  set G := c₀.nreg ztfg with hGdef
  have hXc := hX
  obtain ⟨-, b2, -, -, hsl, -, -⟩ := hX
  zuivq
  zubnp
  zukdk
  have hALc : c.nreg ztfx = AL := hI.hin _ by_trivial
  have hb2 : AL + 7 * rd c₀ bSweep 301 ≤ c₀.nreg ALLOC := b2
  -- the search result is the log record at the query position, if there is one
  have hmatch : ∀ i, i < rd c₀ bSweep 301 → c₀.nmem ztbdu = zp →
      (chainModel J.whole).param zta (logPos c₀.nmem AL i) =
        (chainModel J.whole).param zta ztyf → t = i := fun i hi h1 h2 =>
    search_eq hA hs1 hs2 hi zttqv
  -- the address block
  have hok1 : okB W c.nmem cAddr c.nreg := cAddr_ok _ _ hKc.2.1 by_omega
  refine IRS.seq (K₁ := cAddr.length) (K₂ := 11008 + ztnfh)
    (IRS.block cAddr hI hok1) ?_ |>.mono by_rfl ztb
  zufg
  obtain ⟨v1E, v1H, k1⟩ := cAddr_val c.nmem c.nreg hKc.2.1
  rw [hALc] at v1E v1H
  set c₁ : Config := { c with nreg := regB c.nmem cAddr c.nreg } with hc₁
  have nk1 : ∀ q, (q < sw 4100 ∨ sw 4102 < q) → c₁.nreg q = c.nreg q := fun q hq =>
    k1 q (by unfold kA sw at *; omega) (by unfold kE sw at *; omega) (by unfold kH sw at *; omega)
  have hlp := log_posW hA ht
  have hE1 : c₁.nreg kE = c₀.nmem ztdkq := by
    grind
  have hH1 : c₁.nreg kH = c₀.nmem ztnix := by
    grind
  have hxE1 : ztuqr := by_tauto
  have hxH1 : ztuqs := by_tauto
  have hG1 : c₁.nreg ztfg = G := hI₁.hin _ by_trivial
  have h6z : zh = 0 → 6 ≤ zp := fun h0 => query_h6 hz harr h0
  -- the comparison
  refine IRS.seq (K₁ := 11008) (callOff_irs (C := J.whole) (dsc := sw 2) (ex := kE) (hx := kH)
    (ey := lsxE) (hy := lsxH) (g := sw 40) (o := kO) hI₁ ztvsn
    by_decide by_decide
    (by rw [hE1]; exact hlp.1) by_omega
    (by rw [hG1, hGdef, aenv_gW hA]; exact gW_lt_nat J)
    (by zuoph; exact hlp.2.1) by_grind
    (by zuoph; exact hlp.2.2) by_omega
    (by unfold checkK hitK offerFK offerK at hroom; rw [show c₁.nreg ALLOC = c.nreg ALLOC from
      nk1 _ by_decide]; omega)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hb1, hb2', k2, hal2, hm2⟩
  rw [hE1, hH1, hxE1, hxH1, hG1] at hb1 hb2'
  set kt := (chainModel J.whole).key zta (logPos c₀.nmem AL t) with hkt
  set kx := (chainModel J.whole).key zta ztyf with hkx
  have hkt' : (chainModel J.whole).key zta ⟨c₀.nmem ztdkq, c₀.nmem ztnix⟩
      = kt := rfl
  rw [hkt'] at hb1 hb2'
  have nk2 : ∀ q, (q < sw 4100 ∨ sw 4105 < q) → bandOf q ∉ oracleBands → q ≠ ALLOC →
      c₂.nreg q = c.nreg q :=
    fun q hq hb hqa => by
      rw [k2 q hb ztmes ztmes hqa]
      zulzi
  have hfr2 : FrQ c c₂ := ⟨fun r hr hq hra => by
      rw [k2 r hr ztof
        ztof hra]
      exact k1 r ztof
        ztof
        ztof,
    by omega,
    fun a ha => hm2 a by_omega⟩
  have hk0₂ : ztpnk := (hK.fix hI₂).1
  have hacc₂ : AccOK P accA ztcys J.whole.radius z ztwf L c₂ :=
    hacc.transport (fun j hj => nk2 ztbzh zthk
      (nob zthk zthk) ztbjo)
  -- no offer when the record found is not at the query position
  have noOffer : ¬ (off (chainModel J.whole).W.n G kt = off (chainModel J.whole).W.n G kx) →
      ∀ K, IRS P W c₀ .skip c₂ K (fun c' => ∃ L', AccOK P accA ztcys J.whole.radius z
        ztwf L' c' ∧ L ⊆ L' ∧ ztxas ∧
        HC P J c₀ z zp zh d L' ∧ FrQ c c') := by
    intro hne K
    refine IRS.skip (K := K) hI₂ ⟨L, hacc₂, le_rfl, fun τ h => Or.inl h, ?_, hfr2⟩
    zufxm
    exfalso; apply hne
    have := hmatch i hi h1 h2
    rw [hkt, this, key_of_match h1 h2]
  by_cases hc1 : c₂.nreg K0 < c₂.nreg kO
  · zukum
    have hlt : off (chainModel J.whole).W.n G kt < off (chainModel J.whole).W.n G kx :=
      hb1.2.1 (by have := hb1.1; omega)
    exact (IRS.ifT by_omega (noOffer (ne_of_lt hlt) 0)).mono by_omega
      ztb
  · refine (IRS.ifF hc1 ?_).mono (K := 2 + hitK + 2) by_omega ztb
    zukum
    have hn1 : ¬ off (chainModel J.whole).W.n G kt < off (chainModel J.whole).W.n G kx :=
      fun h => by have := hb1.2.2 h; omega
    by_cases hc2 : c₂.nreg K0 < c₂.nreg zttqp
    · zukun
      have hlt : off (chainModel J.whole).W.n G kx < off (chainModel J.whole).W.n G kt :=
        hb2'.2.1 (by have := hb2'.1; omega)
      exact (IRS.ifT by_omega (noOffer (ne_of_gt hlt) 0)).mono by_omega
        ztb
    · refine (IRS.ifF (K := hitK) hc2 ?_).mono by_omega ztb
      zukun
      have hn2 : ¬ off (chainModel J.whole).W.n G kx < off (chainModel J.whole).W.n G kt :=
        fun h => by have := hb2'.2.2 h; omega
      -- the record found is at the query position
      obtain ⟨he, hpar⟩ := bits_eq (x := logPos c₀.nmem AL t) hA hlp.1 hzP hlp.2.1 hzPp hn1 hn2
      have hpt : logPt P J c₀.nmem AL t = z := by
        unfold logPt; rw [he, hpar]; exact harr.2.2.2.1
      have ht₂ : c₂.nreg lsI = t := nk2 _ by_decide
        zthiv by_decide
      have hd₂ : c₂.nreg qD = d := nk2 _ by_decide
        zthiv by_decide
      refine (hit_irs hA hXc hI₂
        by_omega by_grind hz hzs hz2
        ztnts
        (by unfold checkK at hroom; have := hA₂'
            rw [show c₁.nreg ALLOC = c.nreg ALLOC from nk1 _ by_decide] at this
            omega)).mono le_rfl ?_
      rintro c' ⟨L', hacc', hLL, hsnd, hcmp, hfr'⟩
      rw [hd₂] at hacc' hsnd
      rw [hd₂, ht₂] at hcmp
      refine ⟨L', hacc', hLL, hsnd, ?_, hfr2.trans hfr'⟩
      intro i hi h1 h2 hf o τ hc hτ ho
      have hti := hmatch i hi h1 h2
      rw [← hti] at hf
      have hslot := hsl t ht zthzj ztwcc
      have hpt' : logPt P J c₀.nmem ztjt t = z := hpt
      have heq := slot_eq hA.hP hslot hf hpt' hz hzs hz2 hc
      exact hcmp hf τ hτ (heq.trans ho)
end
end S0C
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Set
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt SideAttach)
open Chazelle.Merge (FreeAt)
@[expose] public section
def LSearchOK (lsearch : Stmt) (κ : ℕ) : Prop :=
  ∀ (P : Polygon) (W : ℕ) (J : Merge.Junction) (c₀ c : Config),
    IInv W c₀ c → Consts c₀ → ChainCtx P W c ztjl J.whole →
    ztug →
    c.nreg TBR + c.nreg TLR ≤ c.nreg ALLOC →
    c.nreg ztex < 2 ^ c.nreg TLR →
    c.nreg ztfx + 7 * c.nreg ztex ≤ c.nreg ALLOC →
    c.nreg ztfg < (chainModel J.whole).W.n →
    (∀ j, j < c.nreg ztex → SweepEv.PosW P J ztwun
      ztwrr) →
    SweepEv.PosW P J ztmgx ztmgy →
    (∀ i j, i ≤ j → j < c.nreg ztex →
      lsPr P J c.nmem ztwml ztwmp ztbih j →
      lsPr P J c.nmem ztwml ztwmp ztbih i) →
    c.nreg ALLOC + κ * ztuc ≤ W →
    IRS P W c₀ lsearch c ztxzd (fun c' =>
      c'.nreg lsI ≤ c.nreg ztex ∧
      (∀ j, j < c'.nreg lsI →
        lsPr P J c.nmem ztwml ztwmp ztbih j) ∧
      (∀ j, c'.nreg lsI ≤ j → j < c.nreg ztex →
        ¬ lsPr P J c.nmem ztwml ztwmp ztbih j) ∧
      ztrn ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth)
theorem lsearchOK_of (h : LSearchSpec) : ∃ ls κ, LSearchOK ls κ := h

/-- The constant of the per-query cost. -/
def qK (κL : ℕ) : ℕ := κL + checkK + 10

/-- The predicate of the search does not depend on the memory outside the log. -/
theorem lsPr_congr {P : Polygon} {J : Merge.Junction} {m m' : ℕ → ℕ} {AL G E : ℕ} {x : WPos}
    {j : ℕ} (hm : ∀ a, a < AL + 7 * E → m a = m' a) (hj : j < E) :
    lsPr P J m AL G x j ↔ lsPr P J m' AL G x j := by
  zumtl
  grind
theorem frQ_partFr {c c' : Config} (h : FrQ c c') : PartFr c c' :=
  ⟨fun r hr h1 _ h3 hra => h.1 r hr (fun hq => by
      zubht
      · exact h1 zteo
      · exact h3 zteo) hra, h.2.1, h.2.2⟩
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The per-query clause of `S0CandSpec`** for `candQ ls`. -/
theorem candQ_spec {ls : Stmt} {κL : ℕ} (hLs : LSearchOK ls κL) :
    ∀ (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop) (J : Merge.Junction)
      (H : Host) (N₁ N₂ : NF) (E : ℕ) (c₀ c : Config) (L : Set ℝ) (z : Point),
      AEnv P W X Ok J H N₁ N₂ E c₀ → Aux P J N₂ c₀ → IInv W c₀ c →
      z ∈ J.left.set → z ≠ J.shared → z.2 ≤ J.right.top.2 →
      FreeAt J.whole z ztba →
      c.nreg zP < (chainModel J.whole).W.n →
      ProperPos ztbm zta P.n ztlo →
      Arrival (chainModel J.whole).W z ztwtj ztdmx
        ztwmc →
      c.nreg bL = 1 → c.nreg bR = 1 →
      AccOK P accA ztdm J.whole.radius z ztba L c →
      c.nreg ALLOC + qK κL * ztgf ≤ W →
      IRS P W c₀ (candQ ls) c (qK κL * ztgf)
        (fun c' =>
          (∃ L', AccOK P accA ztdm J.whole.radius z
              ztba L' c' ∧ L ⊆ L' ∧
            ztwjm ∧
            (∀ (rs : List ztcf), rs.length = rd c₀ bSweep 201 →
              StopRecsAt c₀.nmem ztdpi rs →
              ∀ r ∈ rs, r.1 = c.nreg zP →
                (chainModel J.whole).param zta ztbhg =
                  (chainModel J.whole).param zta ztlo →
                dirOf r.2.2.2.2 = -dirOf ztql →
                ∀ τ, 0 < τ → stopOrig J zta N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2 =
                  rayPt z ztba τ → τ ∈ L') ∧
            (∀ j, j < 2 * N₂.nChords →
              tabOf J zta c₀.nmem ztdaf j =
                some ztxbi →
              endDir j = -dirOf ztql → endOrigin J zta N₂ j ∈ J.right.set →
              endOrigin J zta N₂ j ≠ J.shared → endOrigin J zta N₂ j ≠ J.right.top →
              ∀ τ, 0 < τ → endOrigin J zta N₂ j = rayPt z ztba τ →
                τ ∈ L')) ∧
          PartFr c c') := by
  intro P W X Ok J H N₁ N₂ E c₀ c L z hA hAux hI hz hzs hz2 _hfree hzP hzPp harr hbL hbR hacc
    hroom
  have hX := core_of_aux hAux
  rw [hbL, hbR] at hacc ⊢
  zudnn
  zuhx
  set zp := c.nreg zP with hzpdef
  set zh := c.nreg zPh with hzhdef
  set d := c.nreg qD with hddef
  zugmr
  zuki
  zubnp
  have fix : ztyac := fun k hk =>
    hI.hin _ ztze
  -- copy the query position
  have hcost : cIn.length + (κL * ztgf + (checkK + 2)) ≤
      qK κL * ztgf := by
    have : cIn.length = 2 := by_rfl
    zvmwk; unfold qK
    grind
  refine IRS.seq
    (IRS.block cIn hI (cIn_ok _ _)) ?_ |>.mono hcost ztb
  zufg
  obtain ⟨v1E, v1H, k1⟩ := cIn_val c.nmem c.nreg
  set c₁ : Config := { c with nreg := regB c.nmem cIn c.nreg } with hc₁
  have nk1 : ∀ q, (q < sw 4020 ∨ sw 4021 < q) → c₁.nreg q = c.nreg q := fun q hq =>
    k1 q ztmet ztmeu
  have fix1 : ∀ k, k < 700 → c₁.nreg _ = c₀.nreg ztcbe := fun k hk =>
    hI₁.hin _ ztze
  have hAc₁ : ztdc := nk1 _ by_decide
  have hxE1 : ztuqr := v1E
  have hxH1 : ztuqs := v1H
  zuerf
  rw [rd_sw, rd_sw] at hlog
  have hm1 := hm
  have h6z := (query_h6 hz harr)
  have hcongr : ∀ x : WPos, ∀ j, j < c₀.nreg _ →
      (lsPr P J c₁.nmem ztvmu ztyjc x j ↔
        lsPr P J c₀.nmem ztjt _ x j) := fun x j hj => by
    rw [fix1 300 by_norm_num, fix1 40 by_norm_num]
    exact lsPr_congr (E := c₀.nreg ztex) (fun a ha => hm1 a by_omega) hj
  have hTLR : ztguk := fix1 601 by_norm_num
  have hTBR : ztsgk := fix1 600 by_norm_num
  -- the binary search
  have hsearch := hLs P W J c₀ c₁ hI₁ hK ztvsn
    (fun j hj => by
      rw [hTLR] at hj; rw [hTBR, hm1 _ (by have := hA.hTW; omega)]; exact hA.htab j hj)
    (by zunqq; have := hA.hTW; omega)
    (by rw [fix1 301 by_norm_num, hTLR]; have := hA.hbigE; rw [rd_sw, rd_sw] at this; omega)
    by_grind
    (by rw [fix1 40 by_norm_num, aenv_gW hA]; exact gW_lt_nat J)
    (fun j hj => by
      zuihx
      rw [fix1 300 by_norm_num, hm1 _ by_omega, hm1 _ by_omega]
      exact log_posW hA hj)
    (by rw [hxE1, hxH1]; exact ⟨hzP, hzPp, h6z⟩)
    (fun i j hij hj hpr => by
      zuihx
      rw [hcongr _ i by_omega]
      rw [hcongr _ j hj] at hpr
      exact log_mono hA _ hij hj hpr)
    by_grind
  rw [hTLR] at hsearch
  refine IRS.seq hsearch ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨ht0, hs1, hs2, k2, hal2, hm2⟩
  rw [fix1 301 by_norm_num] at ht0 hs2
  rw [hxE1, hxH1] at hs1 hs2
  have hs1' : ∀ j, j < c₂.nreg lsI →
      lsPr P J c₀.nmem _ _ ztyf j := fun j hj =>
    (hcongr _ j by_omega).1 by_grind
  have hs2' : ∀ j, c₂.nreg lsI ≤ j → j < rd c₀ bSweep 301 →
      ¬ lsPr P J c₀.nmem _ _ ztyf j := fun j hj1 hj2 h =>
    hs2 j hj1 hj2 ((hcongr _ j hj2).2 h)
  have nk2 : ∀ q, bandOf q ∉ oracleBands → (q < sw 4000 ∨ sw 4021 < q) → q ≠ ALLOC →
      c₂.nreg q = c.nreg q := fun q hb hq hqa => by
    rw [k2 q hb ztmel hqa]
    zulzi
  have hfr2 : FrQ c c₂ := ⟨fun r hr hq hra => by
      rw [k2 r hr (fun h => hq (by right; unfold LSet at h; unfold sw at *; omega)) hra]
      exact k1 r ztof
        ztof,
    by omega, fun a ha => by_grind⟩
  have hd₂ := nk2 qD zthiv
    by_decide by_decide
  have hacc₂ : AccOK P accA _ J.whole.radius z _ L c₂ :=
    hacc.transport (fun j hj => nk2 _ (nob zthk
      zthk) (by unfold accA sw; omega) (by unfold accA ALLOC sw; omega))
  have hxE2 : c₂.nreg lsxE = zp := by
    rw [k2 _ zthiv
      (by unfold LSet lsxE sw; omega) by_decide]; omega
  have hxH2 : c₂.nreg lsxH = zh := by
    rw [k2 _ zthiv
      (by unfold LSet lsxH sw; omega) by_decide]; omega
  have h301 : c₂.nreg ztex = rd c₀ bSweep 301 := hI₂.hin _ by_trivial
  -- the final assembly from the completeness of the slot read
  have fin : ∀ c' L', AccOK P accA _ J.whole.radius z _ L' c' → L ⊆ L' →
      (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.whole _)) →
      HC P J c₀ z zp zh d L' → FrQ c c' →
      ((∃ L', AccOK P accA ztcys J.whole.radius z ztwf L' c' ∧ L ⊆ L' ∧
            ztxas ∧
            (∀ (rs : List _), rs.length = rd c₀ bSweep 201 →
              StopRecsAt c₀.nmem _ rs →
              ∀ r ∈ rs, r.1 = zp →
                (chainModel J.whole).param _ ztbhg =
                  (chainModel J.whole).param _ ztyf →
                dirOf r.2.2.2.2 = -dirOf d →
                ∀ τ, 0 < τ → stopOrig J _ N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2 =
                  rayPt z _ τ → τ ∈ L') ∧
            (∀ j, j < 2 * N₂.nChords →
              tabOf J _ c₀.nmem _ j =
                some (zp, (chainModel J.whole).param _ ztyf) →
              endDir j = -dirOf d → endOrigin J _ N₂ j ∈ J.right.set →
              endOrigin J _ N₂ j ≠ J.shared → endOrigin J _ N₂ j ≠ J.right.top →
              ∀ τ, 0 < τ → endOrigin J _ N₂ j = rayPt z _ τ →
                τ ∈ L')) ∧
          PartFr c c') := fun c' L' hacc' hLL hsnd hHC hfr => by
    obtain ⟨hst, htb⟩ := compl_of hA hX harr hHC
    exact ⟨⟨L', hacc', hLL, hsnd, hst, htb⟩, frQ_partFr hfr⟩
  refine IRS.ite ztefc ztefc
  · zukrv
    refine (check_irs hA hX hI₂ hz hzs hz2 hzP hzPp by_grind hxE2 hxH2 ht
      hs1' hs2' ztnts (by
        omega)).mono le_rfl ?_
    rintro c' ⟨L', hacc', hLL, hsnd, hHC, hfr⟩
    rw [hd₂] at hacc' hsnd hHC
    exact fin c' L' hacc' hLL hsnd hHC (hfr2.trans hfr)
  · zukrv
    refine IRS.skip hI₂ (fin c₂ L hacc₂ le_rfl by_grind ?_ hfr2)
    zufxm
    exfalso
    have := search_eq hA hs1' hs2' hi zttqv
    omega

/-- **`InitSpec` for a larger cost function.** -/
theorem initSpec_mono {init : Stmt} {Aux' : Polygon → Merge.Junction → NF → Config → Prop}
    {κ κ' : ℕ → ℕ} (h : InitSpec init Aux' κ) (hκ : ∀ D, κ D ≤ κ' D) :
    InitSpec init Aux' κ' := by
  refine ztfzi
  have hle : κ _ * ztbbd *
      ztuc ≤ κ' ztxgn *
        ztbbd * ztuc :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hκ _))
  obtain ⟨c', k, ex, hk, hfr, hreg, hx⟩ := h.1 P W X Ok J H N₁ N₂ E c hw hA
    (le_trans zttaq hroom)
  grind

/-- **`S0CandSpec` from the initialisation contract.** -/
theorem s0CandSpec_of (hI : InitPartSpec) : S0CandSpec := by
  obtain ⟨initC, κI, hInit⟩ := hI
  obtain ⟨ls, κL, hLs⟩ := lsearchOK_of lsearchSpec
  refine ⟨initC, candQ ls, Aux, fun D => κI D + qK κL,
    initSpec_mono hInit by_omega,
    fun P W J N₂ c₀ c h hI => aux_iinv h hI, ?_⟩
  intro P W X Ok J H N₁ N₂ E c₀ c L z hA hAux hI hz hzs hz2 hfree hzP hzPp harr hbL hbR hacc hroom
  have hle : qK κL * ztgf ≤ (κI zto + qK κL) * ztgf :=
    by simp_all
  exact (candQ_spec hLs P W X Ok J H N₁ N₂ E c₀ c L z hA hAux hI hz hzs hz2 hfree hzP hzPp
    harr hbL hbR hacc by_grind).mono hle by_grind
end
end S0C
@[expose] public section
theorem s0CandSpec : S0CandSpec := S0C.s0CandSpec_of S0C.initPartSpec
end
end SweepIo
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {J : Merge.Junction} {P : Polygon} {N : NF}

/-- **A wall code** in the walk of `C₁`: the box twin of the origin's position. -/
theorem m1c_wall (hP : J.P.Simple) (hN : IsNF ztj zta N) {k b e h : ℕ}
    (hok : StOK P J N 1 k b) (hpos : OrgPos P J N 1 k b e h) :
    zthgo ∧ e < (chainModel J.left).W.n ∧
      ProperPos ztbw zta P.n ztcq ∧
      (chainModel J.left).pos zta ztcq = stOrig J zta N 1 k b ∧
      |(stOrig J (Qof P) N 1 k b).2| < J.left.radius ∧
      |(stOrig J (Qof P) N 1 k b).1| = J.left.radius ∧
      sideLeft (chainModel J.left).W e ((chainModel J.left).param zta ztcq)
        (rayPt (stOrig J zta N 1 k b) ztkz 1) := by
  have hok' := hok
  obtain ⟨-, hb, hw, -⟩ := hok
  obtain ⟨hk, hlt⟩ := hw rfl
  obtain ⟨he, hpp, hcl, hz, -, hend⟩ := hpos
  have hx : (ztcq : WPos) = endPos N k ztlp := hend rfl
  have he6 : e < 6 := by_grind
  have hbox : ztpok := by
    rcases hcl with h' | h' | h'
    · zuclh
    · grind
    simp_all
  obtain ⟨-, -, hy, -, hx1⟩ := stOrig_facts hP hN hok'
  obtain ⟨ha, hbw, hpar, hposT⟩ :=
    boxTwin_pos (C₁ := J.right) (C₂ := J.left) rfl hbox zta h
  have hR : 0 < J.whole.radius := J.whole.radius_pos
  -- the ray in the left sector in the walk of `C₂`
  zuivo
  rw [← hx] at hA
  obtain ⟨y, a', b', hab, hset, hl, hr, -⟩ := rec_ends hN hk
  have hpt : sidePt (chainModel J.right).W e ztyne =
      (chainModel J.right).pos zta ztcq := rfl
  have hin : ∀ s, 0 < s → s < b' - a' →
      rayPt (sidePt (chainModel J.right).W e ztyne)
        ztkz s ∈ (N.chord k).toSet ztj zta := by
    zuetg
    rw [hpt, hx, hset]
    zubhr
    · have e1 : ztiou := by_rfl
      rw [e1, hr, dirOf_zero]
      zugzg

    · have e1 : ztiov := by_rfl
      rw [e1, hl, dirOf_one]
      zugzg

  have hsl₂ := SweepStop.sideLeft_of_attach hA (SweepStop.dirOf_cases' b) (ε := b' - a') by_linarith hin
  rw [hpt, hz] at hsl₂
  -- the parameter is positive
  have ht : (chainModel J.right).param zta ztcq ≠ 0 := by
    zubww
    have e0 : (chainModel J.right).pos zta ztcq = (chainModel J.right).wa e := by
      zuckw
    zvncr at e0
    zvokq at hy
    zukan
    unfold Model.wa at hy
    rw [hW] at hy
    rcases hbox with h' | h' <;> zvmxl at hy
    · rw [J.right.sideWalk_vtx_one] at hy; simp [show J.right.radius = J.whole.radius from rfl, abs_of_pos hR] at hy
    · rw [J.right.sideWalk_vtx_three] at hy; simp [show J.right.radius = J.whole.radius from rfl, abs_of_pos hR] at hy
  refine ⟨hbox, by zvokr; omega,
    by unfold ProperPos; rw [← hpar]; tauto, by_simp_all, hy, hx1 rfl, ?_⟩
  rw [← hpar]
  exact (Cand1.sideLeft_congr ht ha hbw _).1 hsl₂
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
def m1o : ℕ := sw 4027

/-- The output register of `callSym` (the symbolic point at `brOS = m1s + 1`). -/
def m1s : ℕ := sw 4079
def m1cL0 : List Instr := [.copyN lE zttsx, .copyN lH zttsy, .copyN lD oB]
def m1cL1 : List Instr := [.copyN lE oPE, .copyN lH oPH, .copyN lD oB]
def m1cCp : List Instr :=
  [.copyN r1F brF, .copyN ztkdp ztepo, .copyN ztogr ztfpg,
    .copyN ztkdq ztnso, .copyN (r1F + 4) zttgz, .copyN (r1F + 5) zttha,
    .copyN (r1F + 6) ztthb]

/-- The shared code. -/
def m1cK0 (sh : Stmt) : Stmt :=
  .seq (callArr CD₁ ztbuy K0 oB m1o)
    (.ifLtN K0 m1o (.seq (block m1cL0) ztyri) ztqty)

/-- The wall code. -/
def m1cK1 (sh : Stmt) : Stmt := .seq (block m1cL1) ztyri

/-- The top code. -/
def m1cK2 (br : Stmt → Stmt) (sh : Stmt) : Stmt :=
  .seq (SweepIo.callSym zted K6 K0 m1s)
    (.seq (callKb cT1 brOS 1 m1o)
      (.ifLtN K0 m1o ztqty (.seq (block [.copyN brOD oB]) (.seq ztqej (block m1cCp)))))

/-- **The candidate of `C₁`.** -/
def m1cP (br : Stmt → Stmt) (sh : Stmt) : Stmt :=
  .ifLtN oKd K1 ztvym (.ifLtN oKd K2 ztvyn zttsw)

/-- The body of `BruteTask`. -/
def StbBody (br : Stmt → Stmt) (κ : ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      ∀ s : SymPt, SymPtIn c brOS s → s.Lt P.n → s.eval zta ∉ J.left.set →
      |(s.eval (Qof P)).1| < J.whole.radius → |(s.eval (Qof P)).2| < J.whole.radius →
      (s.eval zta).2 ≤ J.left.top.2 → c.nreg brOD ≤ 1 →
      c.nreg ALLOC + κ * ztfok * ztwju ≤ W →
      IRS P W c₀ ztqej c ztbapr
        ztbaoq
theorem stbBody_of (h : BruteTask) : ∃ br κ, StbBody br κ := h

/-! ## Small run steps -/
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **No result.** -/
theorem m1c_noRes {C : Chain} {a : Point} {σ : ℝ} {G : Prop} (hI : IInv W c₀ c) (hng : ¬ G) :
    IRS P W c₀ ztqty c 1 (fun c' => ResOK P C a σ G r1F c' ∧
      (∀ r, r ≠ r1F → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  refine (IRS.instr1 (i := .constN r1F 0) hI ⟨iscr_sw by_decide
    by_decide, Nat.zero_le _⟩).mono le_rfl ?_
  zuu
  have h0 : c.nreg r1F = c.nreg r1F := rfl
  have e0 : regI c.nmem (.constN r1F 0) c.nreg r1F = 0 := upd_same _ _ _
  refine ⟨⟨by_simp_all,
    fun h => by
      simp_all,
    fun g => absurd g hng⟩, fun r hr => upd_other _ _ _ hr, rfl⟩
variable (m f : ℕ → ℕ) (J : Merge.Junction) (Q : Polygon) (N : NF) (k b : ℕ)
theorem m1cL0_val :
    regB m m1cL0 f lE = f zttsx ∧ regB m m1cL0 f lH = f zttsy ∧
      regB m m1cL0 f lD = f oB ∧
      (∀ q, q ≠ lE → q ≠ lH → q ≠ lD → regB m m1cL0 f q = f q) := by
  refine ztdwx
  · rfl
  · rfl
  · rfl
  · simp only [m1cL0, regB, regI]
    simp_all
theorem m1cL1_val :
    regB m m1cL1 f lE = f oPE ∧ regB m m1cL1 f lH = f oPH ∧ regB m m1cL1 f lD = f oB ∧
      (∀ q, q ≠ lE → q ≠ lH → q ≠ lD → regB m m1cL1 f q = f q) := by
  refine ztdwx
  · rfl
  · rfl
  · rfl
  · simp only [m1cL1, regB, regI]
    simp_all
theorem m1cL_ok {W : ℕ} (m f : ℕ → ℕ) : okB W m m1cL0 f ∧ okB W m m1cL1 f := by
  have s : ztwrf := fun j h1 h2 =>
    iscr_sw ztce ztce
  simp only [m1cL0, m1cL1, okB, okI]
  exact ⟨⟨s 1103 by_norm_num by_norm_num, s 1104 by_norm_num by_norm_num,
    s 1105 by_norm_num by_norm_num, trivial⟩, ⟨s 1103 by_norm_num by_norm_num,
    s 1104 by_norm_num by_norm_num, s 1105 by_norm_num by_norm_num, trivial⟩⟩
theorem m1cCp_val :
    (∀ i, i < 7 → regB m m1cCp f zttyc = f (brF + i)) ∧
      (∀ q, (q < r1F ∨ r1F + 6 < q) → regB m m1cCp f q = f q) := by
  refine ⟨fun i hi => ?_, fun q hq => ?_⟩
  · interval_cases i <;> simp [m1cCp, regB, regI, upd, r1F, brF, sw]
  · zunn
    simp only [m1cCp, List.mem_cons, List.not_mem_nil, or_false] at hi
    unfold r1F sw at hq
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dstI, r1F, sw] <;> omega
theorem m1cCp_ok {W : ℕ} (m f : ℕ → ℕ) : okB W m m1cCp f := by
  have s : ztwrf := fun j h1 h2 =>
    iscr_sw ztce ztce
  simp only [m1cCp, okB, okI]
  exact ⟨s 4030 by_norm_num by_norm_num, s 4031 by_norm_num by_norm_num,
    s 4032 by_norm_num by_norm_num, s 4033 by_norm_num by_norm_num,
    s 4034 by_norm_num by_norm_num, s 4035 by_norm_num by_norm_num,
    s 4036 by_norm_num by_norm_num, trivial⟩
theorem stOrig_zero :
    stOrig J Q N 0 k b = J.shared := by_rfl
theorem stOrig_two :
    stOrig J Q N 2 k b = J.right.top := by_rfl
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

/-- The post of the candidate of `C₁`. -/
def M1Post (P : Polygon) (J : Merge.Junction) (N : NF) (c c' : Config) : Prop :=
  ResOK P J.left ztyru ztwow
    (FreeAt J.left ztyru ztwow ∧
      (stOrig J zta N ztka ztij ztfb).2 ≤ J.left.top.2) r1F c' ∧
    EFr M1R c c'
theorem m1c_efr {X Y Z : ℕ → Prop} {c₁ c₂ : Config} (h₁ : EFr X c c₁) (h₂ : EFr Y c₁ c₂)
    (hX : ∀ r, X r → Z r) (hY : ∀ r, Y r → Z r) : EFr Z c c₂ :=
  ⟨fun r a b d => (h₂.1 r a (fun h => b (hY r h)) d).trans (h₁.1 r a (fun h => b (hX r h)) d),
    h₁.2.1.trans h₂.2.1, fun a ha => (h₂.2.2 a (by have := h₁.2.1; omega)).trans ztdux⟩
variable (r : ℕ)
/-- The local-hit registers, the save registers `r1F …` lie in `M1R`. -/
theorem lhsw_m1r (h : LHSW r1F r) : M1R r := by
  unfold LHSW LHR r1F at h; unfold M1R; unfold sw at h ⊢; omega

/-- The local-hit inputs lie in `M1R`. -/
theorem lin_m1r (h : r = lE ∨ r = lH ∨ r = lD) : M1R r := by
  unfold lE lH lD at h; unfold M1R; unfold sw at h ⊢; omega
theorem efr_lin (c : Config) (l : List Instr)
    (h : ∀ q, q ≠ lE → q ≠ lH → q ≠ lD → regB c.nmem l c.nreg q = c.nreg q) :
    EFr (fun r => r = lE ∨ r = lH ∨ r = lD) c { c with nreg := regB c.nmem l c.nreg } := by
  refine ⟨fun r _ hr _ => h r (fun e => hr ztccj) (fun e => hr ztxgj)
    (fun e => hr ztgei), ?_, fun _ _ => rfl⟩
  show c.nreg ALLOC ≤ regB c.nmem l c.nreg ALLOC
  rw [h ALLOC by_decide by_decide
    by_decide]
theorem dr_m1 : DR MD₁ ∧ DR CD₁ ∧ DR ztea ∧ DR ztna := by
  tauto
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

/-- The walk length of `C₁` at `sw 33`. -/
theorem m1c_n33 (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) :
    c.nreg ztna = 2 * J.left.m + 7 := by
  zugow
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h33, -⟩ := hst
  rw [hI.hin _ by_trivial]; omega
set_option maxRecDepth 20000 in
/-- **The wall code.** -/
theorem m1cK1_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hD : OrgD P J N₂ ztka ztij ztfb)
    (hpos : OrgPos P J N₂ ztka ztij ztfb ztdzo ztdzp)
    (hk : c.nreg oKd = 1) {K : ℕ}
    (hK : lhRunK ztdg ztwiu zto + 10 ≤ K)
    (hroom : c.nreg ALLOC + K ≤ W) :
    IRS P W c₀ ztvyn c K ztjkc := by
  have hok : StOK P J N₂ 1 ztij ztfb := hk ▸ hD.ok
  have hps : OrgPos P J N₂ 1 ztij ztfb ztdzo ztdzp := hk ▸ hpos
  obtain ⟨hbx, hlt, hpp, hz, hy, hx1, hsl⟩ := m1c_wall E.hP E.hNF₂ hok hps
  zufuj
  obtain ⟨v1, v2, v3, vo⟩ := m1cL1_val c.nmem c.nreg
  zufix
  unfold m1cK1 M1Post
  zujja
  refine (IRS.seq (K₁ := 3) (K₂ := lhRunK ztdg ztwiu zto + 7)
    ((IRS.block m1cL1 hI (m1cL_ok _ _).2).mono by_rfl ztb) ?_).mono
    by_omega ztb
  zufg
  have eA : regB c.nmem m1cL1 c.nreg ALLOC = c.nreg ALLOC :=
    vo _ by_decide by_decide
      by_decide
  have h33 : regB c.nmem m1cL1 c.nreg ztna = 2 * J.left.m + 7 := by
    have := m1c_n33 E hI₁; omega
  refine (lhSave_irs (x := zteyc)
    (Gd := FreeAt J.left (stOrig J zta N₂ 1 ztij ztfb) ztwow ∧
      (stOrig J zta N₂ 1 ztij ztfb).2 ≤ J.left.top.2)
    E.hsh E.hBs E.hXl d1 d2 d3 d4 by_decide hI₁ E.hK E.hG E.hWh (mctx1 E hI₁)
    E.hP E.hNF₁ E.hX E.hcap E.hOk₁ E.hsg₁ E.hdeg₁ h33 v1 v2 by_simp_all
    hlt hpp (Or.inl hbx) by_simp_all ztcgy ?_
    by_omega).mono le_rfl ?_
  · simp_all
  · zuczf
    have e3 : ({ c with nreg := regB c.nmem m1cL1 c.nreg } : Config).nreg lD = c.nreg oB := v3
    rw [e3, hz] at hres
    exact ⟨hres, m1c_efr (efr_lin c m1cL1 vo) hfr lin_m1r lhsw_m1r⟩
theorem efr_noRes {c c' : Config} (h : ∀ r, r ≠ r1F → c'.nreg r = c.nreg r)
    (hm : c'.nmem = c.nmem) : EFr M1R c c' :=
  ⟨fun r _ hr _ => h r (fun e => hr (by zvmwe; tauto)),
    by rw [h ALLOC by_decide], fun a _ => by zvmwi⟩
set_option maxRecDepth 20000 in
/-- **The shared code.** -/
theorem m1cK0_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hD : OrgD P J N₂ ztka ztij ztfb)
    (hk : c.nreg oKd = 0) {K : ℕ}
    (hK : lhRunK ztdg ztwiu zto + 35020 ≤ K)
    (hroom : c.nreg ALLOC + K ≤ W) :
    IRS P W c₀ ztvym c K ztjkc := by
  zufui
  zullw
  zugow
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h45, -⟩ := hst
  have e46 : ztzje := by
    zuiis
  obtain ⟨sl, spp, spos⟩ := Cand1.shared_posL E.hP zta P.n
  zugnq
  have hshL : J.shared ∈ J.left.set := J.shared_mem_left
  have hsy : ztsns := absy_lt J.left hshL
  have hst1 : J.shared.2 ≤ J.left.top.2 := J.left.snd_le_top_of_mem_set hshL
  zufix
  obtain ⟨R, hRd⟩ : ∃ R, R = lhRunK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) := zths
  rw [← hRd] at hK
  unfold m1cK0 M1Post
  rw [hk, stOrig_zero]
  refine (IRS.seq (K₁ := 35007)
    (K₂ := R + 12)
    (callArr_irs (P := P) (dsc := CD₁) (re := sw 46) (rh := K0) (rd := oB) (o := m1o)
      (C := J.left) hI ztuxt by_decide by_decide
      by_omega by_simp_all by_simp_all
      by_omega) ?_).mono by_omega (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨⟨hf1, harr, hnarr⟩, hfr1, hal1, hm1⟩
  rw [e46, k0, spos] at harr hnarr
  have fr1 : EFr (fun r => r = m1o ∨ r = m1o + 1 ∨ r = m1o + 2) c c₁ :=
    ⟨fun r a b d => hfr1 r a (fun e => b ztccj) (fun e => b ztxgj)
      (fun e => b ztgei) d, hal1, hm1⟩
  have m1o_m1r : ∀ r, (r = m1o ∨ r = m1o + 1 ∨ r = m1o + 2) → M1R r := by
    intro r h; unfold m1o at h; unfold M1R; unfold sw at h ⊢; omega
  have eB : ztmvh := hfr1 _ (not_oracle_sw by_decide
    by_decide) by_decide by_decide
    by_decide by_decide
  zulib
  refine (IRS.ite (K := R + 10) ztyq ztyq).mono
    (show R + 10 + 2 ≤ R + 12 by omega) ztb
  · zuksp
    have hf : c₁.nreg m1o = 1 := by_omega
    obtain ⟨hpn, hppA, hA⟩ := harr hf
    obtain ⟨v1, v2, v3, vo⟩ := m1cL0_val c₁.nmem c₁.nreg
    refine (IRS.seq (K₁ := 3)
      (K₂ := R + 7)
      ((IRS.block m1cL0 hI₁ (m1cL_ok _ _).1).mono by_rfl ztb) ?_).mono
      by_omega ztb
    zubuo
    have eA : regB c₁.nmem m1cL0 c₁.nreg ALLOC = c₁.nreg ALLOC :=
      vo _ by_decide by_decide
        by_decide
    have h33 : regB c₁.nmem m1cL0 c₁.nreg ztna = 2 * J.left.m + 7 := by
      have := m1c_n33 E hI₂; omega
    have hpt : (chainModel J.left).pos zta ztdxg =
        J.shared := hA.2.2.2.1
    have hcl : PosClass J.left zta ztdxg :=
      posClass_of hpn hppA.1 hppA.2.1 by_grind ztzz
    have hsec := hA.2.2.2.2
    zubvb
    refine (lhSave_irs (x := ztdxg)
      (Gd := FreeAt J.left J.shared ztwow ∧ J.shared.2 ≤ J.left.top.2)
      E.hsh E.hBs E.hXl d1 d2 d3 d4 by_decide hI₂ E.hK E.hG E.hWh (mctx1 E hI₂)
      E.hP E.hNF₁ E.hX E.hcap E.hOk₁ E.hsg₁ E.hdeg₁ h33 v1 v2
      by_grind
      hpn hppA hcl by_grind ztzz ?_
      by_grind).mono by_omega ?_
    · grind
    · zuczf
      have e3 : ({ c₁ with nreg := regB c₁.nmem m1cL0 c₁.nreg } : Config).nreg lD =
          c.nreg oB := by_grind
      rw [e3, hpt] at hres
      exact ⟨hres, m1c_efr fr1 (m1c_efr (efr_lin c₁ m1cL0 vo) hfr lin_m1r lhsw_m1r) m1o_m1r
        ztng⟩
  · zuksp
    have hng : ¬ (FreeAt J.left J.shared ztwow ∧ J.shared.2 ≤ J.left.top.2) := by
      intro g
      obtain ⟨p, t, hA⟩ := (freeAt_iff_arr J.left E.hP hσ (Or.inl hshL)).1 g.1
      grind
    refine (m1c_noRes (C := J.left) (a := J.shared) (σ := dirOf ztfb) hI₁ hng).mono
      by_omega ?_
    zuhjm
    exact ⟨hres, m1c_efr fr1 zttjr m1o_m1r ztng⟩
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
theorem efr_regs {S Z : ℕ → Prop} {c c' : Config} (hS : ∀ r, S r → Z r)
    (h : ∀ r, bandOf r ∉ oracleBands → ¬ S r → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) :
    EFr Z c c' :=
  ⟨fun r a b d => h r a (fun x => b (hS r x)) d, ha, hm⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The top code.** -/
theorem m1cK2_irs {br : Stmt → Stmt} {κB : ℕ} (hBr : StbBody br κB)
    (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hD : OrgD P J N₂ ztka ztij ztfb)
    (hk : c.nreg oKd = 2) {K : ℕ}
    (hK : 16970 + κB * ztfok * ztwju ≤ K)
    (hroom : c.nreg ALLOC + K ≤ W) :
    IRS P W c₀ zttsw c K ztjkc := by
  zufui
  have hok : StOK P J N₂ 2 ztij ztfb := hk ▸ hD.ok
  have htop0 : J.right.topIdx ≠ 0 := hok.2.2.2 rfl
  have hK0 := E.hK.fix hI
  have htopR : J.right.top ∈ J.right.set := J.right.top_mem_set
  have hpos6 : (chainModel J.right).pos zta ztbcw = J.right.top := SweepStop.right_top_pos _
  zudod
  have hm2 := J.right.one_le
  obtain ⟨KB, hKBd⟩ : ∃ KB, KB = κB * (N₁.nChords + 1) * (F (c₀.nreg (sw 5)) + 1) :=
    ⟨_, rfl⟩
  rw [← hKBd] at hK
  unfold m1cK2 M1Post
  rw [hk, stOrig_two]
  refine (IRS.seq (K₁ := 16707) (K₂ := 251 + ztsys)
    (SweepIo.callSym_irs (P := P) (dsc := sw 21) (re := K6) (rh := K0) (o := m1s) (C := J.right) hI
      ztpxh by_decide by_decide
      (by rw [hK0.2.2.1, cm_n]; omega)
      (by rw [hK0.2.2.1, hK0.1]; exact ⟨le_refl _, by
          simp,
        Nat.zero_le _⟩)
      (by rw [hK0.2.2.1, hK0.1, hpos6]; exact absy_lt J.right htopR)
      (Or.inl ⟨by zupcs, by zupcs; omega⟩) by_omega) ?_).mono
    (show 16707 + (251 + ztsys) ≤ K by omega) ztb
  rintro c₁ hI₁ hA₁ hA₁' ⟨sp, hsp, hlt, hev, hfr1, hal1, hm1⟩
  rw [hK0.2.2.1, hK0.1, hpos6] at hev
  have fr1 : EFr M1R c c₁ := efr_regs (S := fun r => m1s ≤ r ∧ r ≤ m1s + 3)
    (fun r h => by unfold m1s at h; unfold M1R; unfold sw at h ⊢; omega)
    (fun r a b d => hfr1 r a by_omega d) hal1 hm1
  obtain ⟨t1, ht1, ht1l, ht1e⟩ := (E.hO.fix hI₁).t1
  have hsp' : SymPtIn c₁ brOS sp := hsp
  refine IRS.seq (K₁ := 251) (K₂ := KB + 12)
    (callKb_irs (a := cT1) (b := brOS) (op := 1) (o := m1o) by_norm_num hI₁ E.hG hW3
      by_decide by_decide by_decide ht1 hsp'
      ht1l hlt by_omega) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hf2, hiff2, hfr2, hal2, hm2'⟩
  rw [ht1e, hev] at hiff2
  have fr2 : EFr M1R c₁ c₂ := efr_regs (S := fun r => r = m1o)
    (fun r h => by zvmwc; unfold m1o M1R sw; omega) (fun r a b d => hfr2 r a b d) hal2 hm2'
  zuhef
  have kB : ∀ r, 240000 ≤ r → r < 250000 → r ≠ m1o → (r < m1s ∨ m1s + 3 < r) → r ≠ ALLOC →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 h4 h5 =>
    (hfr2 r ztsg h3 h5).trans (hfr1 r ztsg h4 h5)
  have eB : c₂.nreg oB = c.nreg oB := kB _ by_decide by_decide
    by_decide by_decide by_decide
  refine (IRS.ite (K := KB + 10) ztyq ztyq).mono
    (show KB + 10 + 2 ≤ KB + 12 by omega) ztb
  · -- above the top of `C₁`: no result
    zuksr
    have hab : J.left.top.2 < J.right.top.2 := (hiff2.1 by_omega)
    have hng : ¬ (FreeAt J.left J.right.top ztwow ∧
        J.right.top.2 ≤ J.left.top.2) := fun g => by_grind
    refine (m1c_noRes (C := J.left) (a := J.right.top) (σ := dirOf ztfb) hI₂ hng).mono
      by_omega ?_
    zuhjm
    exact ⟨hres, m1c_efr ztzgm zttjr
      ztng ztng⟩
  · zuksr
    have hle : J.right.top.2 ≤ J.left.top.2 := by
      zukr
      have := hiff2.2 (by push Not at hc; exact hc)
      omega
    -- the direction
    have hokB : okB W c₂.nmem [Instr.copyN brOD oB] c₂.nreg :=
      ⟨iscr_sw by_decide by_decide, trivial⟩
    refine (IRS.seq (K₁ := 1) (K₂ := KB + 7)
      ((IRS.block [Instr.copyN brOD oB] hI₂ hokB).mono by_simp ztb) ?_).mono
      (show 1 + (KB + 7) ≤ KB + 10 by omega) ztb
    zukob
    have v3 : c₃.nreg brOD = c.nreg oB := by
      zuktr
    have vo3 : ∀ q, q ≠ brOD → c₃.nreg q = c₂.nreg q :=
      fun q hq => by zvnar; zumxi; exact upd_other _ _ _ hq
    zuyu
    have hA3eq : ztbox := vo3 _ by_decide
    have fr3 : EFr M1R c₂ c₃ :=
      efr_regs (S := fun r => r = brOD) (fun r h => by zvmwc; unfold brOD M1R sw; omega)
        (fun r _ b _ => vo3 r b) by_omega (fun _ _ => by rw [hm3])
    -- the symbolic point is still at `brOS`
    have kS : ∀ i, i < 3 → c₃.nreg ztthe = c₁.nreg ztthe := fun i hi => by
      rw [vo3 _ (by unfold brOS brOD sw; omega)]
      exact hfr2 _ (not_oracle_sw ztozn ztozn)
        (by unfold brOS m1o sw; omega) (by unfold brOS ALLOC sw; omega)
    have hsp3 : SymPtIn c₃ brOS sp :=
      symPtIn_copy hsp' (kS 0 by_norm_num) (kS 1 by_norm_num) (kS 2 by_norm_num)
    have hab := Cand1.abs_lt_whole (J := J) htopR
    have hbr := hBr sh Bs F X Ok P W c₀ c₃ J N₁ N₂ E hI₃ sp hsp3 hlt
      (by rw [hev]; exact top_not_left E.hP htop0) by_grind
      by_grind by_grind
      by_omega
      by_omega
    rw [← hKBd] at hbr
    refine IRS.seq (K₁ := KB) (K₂ := 7) hbr ?_
    rintro c₄ hI₄ hA₄ hA₄' ⟨g1, gs, gf, gm, ga, gr⟩
    have e4 : dirOf (c₃.nreg brOD) = dirOf ztfb := by zunrr
    rw [e4, hev] at gs gf
    have fr4 : EFr M1R c₃ c₄ :=
      efr_regs (S := BrR) (fun r h => by unfold BrR at h; unfold M1R; unfold sw at h ⊢; omega)
        gr ga gm
    obtain ⟨cv, co⟩ := m1cCp_val c₄.nmem c₄.nreg
    refine (IRS.block m1cCp hI₄ (m1cCp_ok _ _)).mono by_rfl ?_
    zuu
    have fr5 : EFr M1R c₄ { c₄ with nreg := regB c₄.nmem m1cCp c₄.nreg } :=
      efr_regs (S := fun r => r1F ≤ r ∧ r ≤ r1F + 6)
        (fun r h => by unfold r1F at h; unfold M1R; unfold sw at h ⊢; omega)
        (fun r _ b _ => co r by_omega)
        by_rfl ztcj
    have c0 : ({ c₄ with nreg := regB c₄.nmem m1cCp c₄.nreg } : Config).nreg r1F =
        c₄.nreg brF := by_rfl
    refine ⟨⟨by_omega, fun h1 => ?_, fun g => by_grind⟩,
      m1c_efr (m1c_efr ztzgm (m1c_efr fr3 fr4
        ztng ztng) (fun r h => h) (fun r h => h)) fr5 (fun r h => h)
        ztng⟩
    rw [c0] at h1
    obtain ⟨τ, a1, a2, a3, a4, a5, a6, a7⟩ := gs h1
    have c1 : ({ c₄ with nreg := regB c₄.nmem m1cCp c₄.nreg } : Config).nreg (r1F + 1) =
        c₄.nreg ztepo := cv 1 by_norm_num
    have c2 : ({ c₄ with nreg := regB c₄.nmem m1cCp c₄.nreg } : Config).nreg (r1F + 2) =
        c₄.nreg ztfpg := cv 2 by_norm_num
    refine ⟨τ, a1, a2, by_omega, by_grind, by_grind,
      absRec_transport a6 (cv 3 by_norm_num) (cv 4 by_norm_num) (cv 5 by_norm_num)
        (cv 6 by_norm_num), fun g => a7 g.1⟩
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
theorem m1c_lhRunK_le (T Fg D : ℕ) : lhRunK T Fg D ≤ κGen D * ztbbs := by
  have := genK_le Fg D T
  unfold genK at this
  unfold lhRunK
  omega
set_option maxRecDepth 20000 in
/-- **Task M1: the candidate of `C₁`** of a stop origin. -/
theorem m1Task : M1Task := by
  obtain ⟨br, κB, hBr⟩ := stbBody_of bruteTask
  refine ⟨m1cP br, fun D => κGen D + κB + 60000, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hD hpos hroom
  zubmr
  have hkd : ztuov := hD.ok.1
  zuiw
  obtain ⟨M, hMd⟩ : ∃ M, M = (if c.nreg oKd = 1 then 1 else N₁.nChords + N₂.nChords + 1) :=
    ⟨_, rfl⟩
  rw [← hMd] at hroom ⊢
  zujzn
  have hLK := m1c_lhRunK_le ztdg ztwiu zto
  set Q := F ztq + c₀.nreg TLR + 1 with hQ
  set G := κGen zto with hG
  have hQ1 : 1 ≤ Q := by_omega
  have hMQ : 1 ≤ M * Q := Nat.one_le_iff_ne_zero.2 by_positivity
  have e : ztpzb * M * Q = G * M * Q + κB * M * Q + 60000 * (M * Q) := by_ring
  have hp2 : G * Q ≤ G * M * Q := by
    rw [show G * M * Q = M * (G * Q) by ring]; exact Nat.le_mul_of_pos_left _ by_omega
  set B := ztpzb * M * Q with hB
  unfold m1cP
  refine (IRS.ite (K := B - 2) ztfrp ztfrp).mono by_omega ztb
  · zuksn
    exact m1cK0_irs E hI hD by_omega by_omega by_omega
  · zuksn
    refine (IRS.ite (K := B - 4) ztyq ztyq).mono by_omega ztb
    · zukso
      exact m1cK1_irs E hI hD hpos by_omega by_omega by_omega
    · zukso
      zukcy
      have hMe : M = N₁.nChords + N₂.nChords + 1 := by_simp_all
      have hp1 : κB * ztfok * ztwju ≤ κB * M * Q :=
        Nat.mul_le_mul ztdfv by_omega
      exact m1cK2_irs hBr E hI hD hk2 by_omega by_omega
end
end SweepEv
namespace S0Math
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Merge (FreeAt)
open WalkEmbed Sweep
@[expose] public section
noncomputable def hPoly (F : Set ztf) (hfin : F.Finite) : Polygon :=
  ⟨hfin.toFinset.toList.map fun c => ztblh⟩
theorem chordFamily_hPoly (C : Chain) {F : Set ztf} (hfin : F.Finite)
    (hF : F ⊆ Merge.augChords C) : (chainModel C).ChordFamily (hPoly F hfin) F := by
  refine ⟨hfin, hF, fun c hc => ?_⟩
  have hmem : ztblh ∈ (hPoly F hfin).vertices := by
    simp only [hPoly]
    exact List.mem_map.2 ztrbe
  zufxx
  obtain ⟨y, a, b, -, -, hcd, hl, -⟩ := Merge.augChords_spec ztlz
  refine ztlwd
  have hv : (hPoly F hfin).vtx h = ztblh := by
    unfold Polygon.vtx
    simp_all
  simp_all

/-! ## The query point -/
variable (J : Merge.Junction)

/-- **A point of `C₁` other than the shared vertex, not above the top of `C₂`, is in the domain of
`C₂`.** -/
theorem left_pt_right_dom (hP : J.P.Simple) {z : Point} (hz : z ∈ J.left.set)
    (hzv : z ≠ J.shared) (hz2 : z.2 ≤ J.right.top.2) : z ∈ J.right.dom := by
  zumv
  rcases (Merge.not_mem_dom_iff J.right hz2).1 h with hb | hs
  · apply hb
    rw [FuseMath.radius_of_P J (C' := J.right) rfl, ← FuseMath.radius_of_P J (C' := J.left) rfl]
    exact J.left.set_subset_box hz
  · have : ztmxf := ⟨hz, hs⟩
    zuect
variable {z : Point}
/-- A point of `C₁` is strictly inside the box of `C`. -/
theorem left_pt_abs (hz : z ∈ J.left.set) : |z.2| < J.whole.radius := by
  zufot
  exact (J.left.set_subset_box hz).2

/-- **The first hit of `C₁`**: unless the hit point of `C` is on `C₂` and off `C₁`, the first hit
of `C` is the first hit of `C₁`. -/
theorem left_hit_of (hz₁ : z.2 ≤ J.left.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hfree : FreeAt J.whole z σ)
    (hc : ¬ (rayPt z σ ztbyn ∈ J.right.set ∧
      rayPt z σ ztbyn ∉ J.left.set)) :
    J.left.hitParam z σ = J.whole.hitParam z σ := by
  have hz' : ztsnr := hz₁.trans J.left_top_le
  zuchz

  zuhfv
  have hfree₁ : Merge.FreeAt J.left z σ := by
    zuiud
    zulex
  obtain ⟨hT₁, hw₁D, hdom₁⟩ := Merge.hit_of_freeAt J.left hz₁ hσ hfree₁
  have hwD₁ : rayPt z σ T ∉ J.left.dom := by
    zuhgp
    rcases (Merge.not_mem_dom_iff J.whole (p := rayPt z σ T) by_simp_all).1 hwD
      with h | h
    · zuhrs
      zufot
      exact J.left.dom_subset_box hmem
    · zukpk
      zuy
      · exact J.left.not_mem_set_of_mem_dom hmem h
      · exact hc ⟨h, fun h' => J.left.not_mem_set_of_mem_dom hmem h'⟩
  rcases lt_trichotomy ztnlt T with h | h | h
  · exact absurd (dom_left J (hdom _ hT₁ h) by_simp_all) hw₁D
  · zubh
  simp_all

/-- **The first hit of `C₂`**: if the hit point of `C` is on `C₂` (and the query is not above the
top of `C₂`), the first hit of `C` is the first hit of `C₂`. -/
theorem right_hit_of (hz₂ : z.2 ≤ J.right.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hfree : FreeAt J.whole z σ) (hw : rayPt z σ ztbyn ∈ J.right.set) :
    J.right.hitParam z σ = J.whole.hitParam z σ := by
  have hz' : ztsnr := hz₂.trans J.right_top_le
  obtain ⟨hT, -, hdom⟩ := Merge.hit_of_freeAt J.whole hz' hσ hfree
  set T := J.whole.hitParam z σ with hTdef
  zuhfv
  have hfree₂ : Merge.FreeAt J.right z σ := by
    zuiud
    zuhcr
  obtain ⟨hT₂, hw₂D, hdom₂⟩ := Merge.hit_of_freeAt J.right hz₂ hσ hfree₂
  rcases lt_trichotomy ztsyl T with h | h | h
  · exact absurd (dom_right J (hdom _ hT₂ h) by_simp_all) hw₂D
  · zubh
  · exact absurd hw (J.right.not_mem_set_of_mem_dom (hdom₂ T hT h))

/-! ## Regions faced near a key -/
section Gen
variable {M : Model}

/-- **The region faced just after a key**: a non-cut position inside a walk edge, after the key
with no cut in between, faces the region faced just after the key. -/
theorem after_of_near (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {g : ℕ} (hg : g < M.W.n) {U : Set Point} (hU : U ∈ M.regions F) {pa : ℕ} {ta : ℝ}
    (hpa : pa < M.W.n) (hta : 0 ≤ ta) {q : ℕ} {u : ℝ} (hq : q < M.W.n)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hqc : ¬ M.IsCut F ztzq) (hqf : M.Faces q u U)
    (hlt : off M.W.n g ztbf < off M.W.n g ztzq)
    (hgap : ∀ x, M.IsCut F x → 0 ≤ x → x < M.W.n →
      ¬ (off M.W.n g ztbf < off M.W.n g x ∧ off M.W.n g x < off M.W.n g ztzq)) :
    AfterFaces M pa ta U := by
  zueqz
  have hgn : ztehn := by_simp_all
  obtain ⟨δ₁, hδ₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (eventually_not_cut_after hM hF hfin ztejf)
  zucmv
  set D := off M.W.n g ztxy - off M.W.n g ztejf with hD
  have hD0 : 0 < D := by_linarith
  refine ⟨min δ₁ D, lt_min hδ₁' hD0, fun s hs0 hs1 hs2 => ?_⟩
  have hsD : s < D := lt_of_lt_of_le hs1 ztgh
  have hsδ : s < δ₁ := lt_of_lt_of_le hs1 ztff
  have hnc : ¬ M.IsCut F ztjcn := by
    have := hsub ⟨hs0, hsδ⟩
    grind
  have hts : ta + s ∈ Ioo (0 : ℝ) 1 := ⟨by_linarith, hs2⟩
  obtain ⟨U', hU', hf'⟩ := hM.exists_faces_of_not_cut hF hfin hpa hts hnc
  have hoff : off M.W.n g ztjcn = off M.W.n g ztejf + s :=
    off_add_small hg hpa hta hs0.le hs2
  have heq := same_region_of_gap hM hF hfin hg0 hgn hU' hU hpa hq hts hu hnc hqc hf' hqf
    by_grind (fun x hx hx0 hxn ⟨h1, h2⟩ => hgap x hx hx0 hxn ztuga)
  grind

/-- **A region faced just after a position** is faced at a non-cut position of the same edge, at an
offset just after it. -/
theorem near_after (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {g : ℕ} (hg : g < M.W.n) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {U : Set Point} (hW : AfterFaces M p t U) {ε : ℝ} (hε : 0 < ε) :
    ∃ s, 0 < s ∧ s < ε ∧ t + s ∈ Ioo (0 : ℝ) 1 ∧ ¬ M.IsCut F ztwoq ∧
      M.Faces p ztuf U ∧
      off M.W.n g ztwoq = off M.W.n g ztdj + s := by
  obtain ⟨s, hs0, hsε, hs1, hnc, hf⟩ := faces_near_after hM hF hfin ht0 ht1 hW hε
  exact ⟨s, hs0, hsε, ztomr, hnc, hf, off_add_small hg hp ht0 hs0.le hs1⟩
end Gen
end
end S0Math
end Chazelle.Core
namespace Chazelle.Core
namespace S0Math
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Merge (FreeAt)
open WalkEmbed Sweep
@[expose] public section
variable (J : Merge.Junction)
theorem gW_lt : gW J < (chainModel J.whole).W.n := by
  zuhf
  have := tpos_lt J.whole J.m₁
  unfold gW; omega
theorem getD_mem {α : Type*} {l : List α} {i : ℕ} (hi : i < l.length) (d : α) :
    l.getD i d ∈ l := by
  simp_all
set_option maxHeartbeats 2000000 in
/-- **The labels of the region faced at a position, from the event log.** -/
theorem labels_of_log (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite)
    {es : List ztwws} (hlog : LogOK J S₂ es) {i : ℕ} (hi : i < es.length)
    {pz : ℕ} {tz : ℝ} (hpz : pz < (chainModel J.whole).W.n) (htz0 : 0 ≤ tz) (htz1 : tz < 1)
    (hLst : (Lst J : ℝ) < oW J zthe)
    (hlo : oW J ztwpp ≤ oW J zthe)
    (hhi : i + 1 < es.length →
      oW J zthe < oW J ztwvu)
    {U : Set Point} (hU : U ∈ (chainModel J.whole).regions ztbi)
    (hface : AfterFaces ztbm pz tz U ∨ BeforeFaces ztbm pz tz U) :
    ∀ V ∈ (chainModel J.right).regions S₂, RLabel J S₂ U V →
      V ∈ (es.getD i ztfj).2.2 ∨ (0 < i ∧ V ∈ (es.getD ztei ztfj).2.2) ∨
        GapLab J S₂ V := by
  zugb
  zuhwr
  have hfin : (F₂plus J S₂).Finite := F₂plus_finite J hS₂f
  have hg := gW_lt J
  have hg0 : (0 : ℝ) ≤ (gW J : ℝ) := Nat.cast_nonneg _
  have hgn : (gW J : ℝ) < (chainModel J.whole).W.n := by_simp_all
  set d : ℕ × ℝ × Set ztf := ztfj with hd
  have hent : ∀ j, j < es.length → (es.getD j d).1 < (chainModel J.whole).W.n ∧
      0 ≤ (es.getD j d).2.1 ∧ (es.getD j d).2.1 < 1 :=
    fun j hj => by
      obtain ⟨h1, h2, h3, -⟩ := hlog.2.1 _ zttlf
      simp_all
  have hlab : ∀ j, j < es.length →
      LabIn J S₂ (es.getD j d).1 (es.getD j d).2.1 (es.getD j d).2.2 :=
    fun j hj => hlog.2.2.2.2.2.2 _ zttlf
  -- the offsets
  set x := oW J ((pz : ℝ) + tz) with hx
  set k := oW J (((es.getD i d).1 : ℝ) + (es.getD i d).2.1) with hk
  have hxn : x < (chainModel J.whole).W.n := off_lt (Corr.key_mem hpz htz0 htz1).2 hg0
  -- the next cut after the entry `i`
  obtain ⟨ub, hxub, hgub⟩ : ∃ ub : ℝ, x < ub ∧ ∀ y, (chainModel J.whole).IsCut (F₂plus J S₂) y →
      0 ≤ y → y < (chainModel J.whole).W.n → ¬ (k < oW J y ∧ oW J y < ub) := by
    by_cases h : i + 1 < es.length
    · exact ⟨_, hhi h, hlog.2.2.2.2.1 i h⟩
    · refine ⟨(chainModel J.whole).W.n, hxn, ?_⟩
      have hlast : es.getD i d ∈ es.getLast? := by
        rw [List.getLast?_eq_getElem?, show es.length - 1 = i by omega,
          List.getD_eq_getElem _ _ hi]
        simp
      exact hlog.2.2.2.2.2.1 _ hlast
  -- positions with the offset of the entry are the entry
  have hpos_eq : x = k → pz = (es.getD i d).1 ∧ tz = (es.getD i d).2.1 := fun h => by
    obtain ⟨e1, e2, e3⟩ := hent i hi
    have := off_inj hg0 hgn (Corr.key_mem hpz htz0 htz1).1 (Corr.key_mem hpz htz0 htz1).2
      (Corr.key_mem e1 e2 e3).1 (Corr.key_mem e1 e2 e3).2 h
    exact Chazelle.Chain.sideKey_inj htz0 htz1 e2 e3 this
  -- the label conclusion from the region faced just after the entry `i` or `i - 1`
  have finI : AfterFaces ztbm (es.getD i d).1 (es.getD i d).2.1 U →
      ∀ V ∈ (chainModel J.right).regions S₂, RLabel J S₂ U V →
        V ∈ (es.getD i d).2.2 ∨ (0 < i ∧ V ∈ (es.getD ztei d).2.2) ∨ GapLab J S₂ V := by
    intro hA V hV hl
    rcases hlab i hi U hU hA V hV hl with h | h
    · grind
    grind
  -- the region after a non-cut position after the entry
  have viaNear : ∀ (q : ℕ) (u : ℝ), q < (chainModel J.whole).W.n → u ∈ Ioo (0 : ℝ) 1 →
      ¬ (chainModel J.whole).IsCut ztbi ztzq → (chainModel J.whole).Faces q u U →
      k < oW J ztzq → oW J ztzq < ub →
      AfterFaces ztbm (es.getD i d).1 (es.getD i d).2.1 U := by
    intro q u hq hu hnc hf h1 h2
    obtain ⟨e1, e2, -⟩ := hent i hi
    exact after_of_near hM hF hfin hg hU e1 e2 hq hu hnc hf h1
      (fun y hy hy0 hyn ⟨a1, a2⟩ => hgub y hy hy0 hyn ⟨a1, lt_trans a2 h2⟩)
  rcases hface with hA | hB
  · zuklq
    · obtain ⟨s, hs0, hsε, hts, hnc, hf, hoff⟩ :=
        near_after hM hF hfin hg hpz htz0 htz1 hA (ε := ub - x) by_linarith
      have hoff' : oW J ((pz : ℝ) + ztucj) = x + s := hoff
      refine finI (viaNear pz ztucj hpz hts hnc hf ?_ ?_)
      · grind
      grind
    grind
  · zuklq
    · obtain ⟨q, u, hq, hu, hnc, hf, h1, h2⟩ := faces_near_before hM hF hfin hg hpz htz0 htz1
        ztxsg hB (ε := x - k) by_linarith
      have h1' : x - (x - k) < oW J ztxy := h1
      zujyo
      exact finI (viaNear q u hq hu hnc hf by_linarith by_linarith)
    · -- the position is the entry `i`: `i > 0` and the entry `i - 1` faces the region
      have hi0 : ztphs := by
        zuccr
        zugre
        zukco
        have hhead : es.getD 0 d ∈ es.head? := by
          cases es with
          | nil => simp at hi
          | cons a l => simp [hd]
        have := hlog.2.2.1 _ hhead
        grind
      have hi1 : i - 1 < es.length := by_omega
      have hcons : i - 1 + 1 < es.length := by_omega
      have hgap' := hlog.2.2.2.2.1 ztei hcons
      rw [show i - 1 + 1 = i by omega] at hgap'
      have hsort : oW J ztwrg < k := by
        have := List.pairwise_iff_getElem.1 hlog.2.2.2.1 ztei i hi1 hi by_omega
        rw [hk, List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi]
        omega
      obtain ⟨q, u, hq, hu, hnc, hf, h1, h2⟩ := faces_near_before hM hF hfin hg hpz htz0 htz1
        ztxsg hB
        (ε := k - oW J ztwrg) by_linarith
      obtain ⟨e1, e2, -⟩ := hent ztei hi1
      have h1' : x - (k - oW J ztwrg) <
          oW J ztxy := h1
      zujyo
      have hA' := after_of_near hM hF hfin hg hU e1 e2 hq hu hnc hf
        (show oW J _ < oW J ztxy by linarith)
        (fun y hy hy0 hyn ⟨a1, a2⟩ => hgap' y hy hy0 hyn ⟨a1, by
          have a2' : oW J y < oW J ztxy := a2
          grind⟩)
      intro V hV hl
      rcases hlab ztei hi1 U hU hA' V hV hl with h | h
      · grind
      grind
end
end S0Math
end Chazelle.Core
namespace Chazelle.Core
namespace S0Math
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed Sweep
@[expose] public section
variable (J : Merge.Junction)

/-- **The origins of the chords of `F₂⁺`.** -/
theorem F₂plus_origin {S₂ : Set ztf} {e : Set Point} (he : e ∈ F₂plus J S₂) :
    ∃ (o : Point) (d : ℝ), (d = 1 ∨ d = -1) ∧ FreeAt J.whole o d ∧ e = Merge.shoot J.whole o d ∧
      (o = J.shared ∨ o = J.right.top ∨
        ∃ c ∈ S₂, ztmig ∨ ztlmu) := by
  rcases he with ((⟨c₀, hc₀, hfr, rfl⟩ | ⟨c₀, hc₀, hfr, rfl⟩) | ⟨σ, hσ, hfr, rfl⟩) |
      ⟨σ, hσ, hfr, rfl⟩
  · grind
  · grind
  · exact ⟨J.shared, σ, hσ, hfr, rfl, Or.inl rfl⟩
  · have hv : ztxmm := by
      zubut
    refine ⟨J.right.top, σ, hσ, ?_, ?_, Or.inr ztp⟩
    · zufab
    · zufaa

/-- **A ray along a shot chord from its far end.** -/
theorem along_end {e : Set Point} (he : e ∈ Merge.augChords J.whole) {z o : Point} {σ d : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hd : d = 1 ∨ d = -1) (hzD : z ∉ J.whole.dom)
    (hoD : o ∉ J.whole.dom) (hzo : z ≠ o) (heo : e = Merge.shoot J.whole o d)
    (hfo : FreeAt J.whole o d) (hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ e) :
    rayPt z σ ztbyn = o ∧ d = -σ ∧ rayPt o d ztemx = z ∧
      0 < J.whole.hitParam z σ ∧ (∀ p ∈ e, p ∉ J.whole.dom → p = z ∨ p = o) ∧
      (∀ p ∈ e, p.2 = z.2) := by
  obtain ⟨y, l, r, hH, hy, hcd, -, -⟩ := Merge.augChords_spec he
  have hmem : ∀ p : Point, p ∈ e ↔ p.2 = y ∧ l ≤ p.1 ∧ p.1 ≤ r := by
    intro p; rw [hcd]; rfl
  zubwk
  have hends : ∀ p ∈ e, p ∉ J.whole.dom → p.1 = l ∨ p.1 = r := by
    intro p hp hpD
    obtain ⟨h1, h2, h3⟩ := (hmem p).1 hp
    zudt
    · rcases h3.lt_or_eq with h3 | h3
      · exact absurd (by
          have := hH.open_mem p.1 h2 h3
          grind) hpD
      simp_all
    simp_all
  zufzj
  zukho
  have hray : ∀ s, 0 < s → s < δ → z.2 = y ∧ l ≤ z.1 + σ * s ∧ z.1 + σ * s ≤ r := by
    intro s h0 h1
    have := (hmem _).1 (hsub zteyi)
    tauto
  have hzy : ztlbm := (hray ztbfe by_linarith by_linarith).1
  -- the side of `z`
  have hzlr : (σ = 1 ∧ z.1 = l) ∨ (σ = -1 ∧ z.1 = r) := by
    have hz1 : l ≤ z.1 ∧ z.1 ≤ r := by
      constructor
      · zubq

        set s := min ztbfe ztgwd with hs
        zudzp
        have hs1 := min_le_left ztbfe ztgwd
        have hs2 := min_le_right ztbfe ztgwd
        have := (hray s hs0 by_linarith).2.1
        zuieg
      · zubq

        set s := min ztbfe ztgwl with hs
        zudzp
        have hs1 := min_le_left ztbfe ztgwl
        have hs2 := min_le_right ztbfe ztgwl
        have := (hray s hs0 by_linarith).2.2
        zuieg
    have hze : ztpqq := (hmem z).2 ⟨hzy, hz1⟩
    have hs0 : (0 : ℝ) < min ztbfe ztxyo := lt_min by_linarith by_linarith
    have hs1 := min_le_left ztbfe ztxyo
    have h := hray (min ztbfe ztxyo) hs0 by_linarith
    rcases hends z hze hzD with h1 | h1 <;> rcases hσ with rfl | rfl
    · grind
    · grind
    · grind
    grind
  have hze : ztpqq := (hmem z).2 ⟨hzy, by_grind⟩
  -- the origin is the other end
  zudoz
  obtain ⟨hoy, -, -⟩ := (hmem o).1 hoe
  have hoz1 : o.1 ≠ z.1 := fun h => hzo (Prod.ext h.symm by_grind)
  have hoend := hends o hoe hoD
  set τ := r - l with hτ
  have hτ0 : ztrzs := by_linarith
  have hwo : rayPt z σ τ = o := by
    zubjw
    · zulqr

    · rw [rayPt_snd, hzy, hoy]
  have hg : Genuine J.whole z σ τ :=
    genuine_along_chord J.whole he hze hzD hσ hτ0 by_grind by_grind
  have hT : J.whole.hitParam z σ = τ :=
    ((genuine_iff J.whole by_grind hσ).1 hg).2
  -- the shot from the origin ends at `z`
  have ho2 : o.2 ≤ J.whole.top.2 := by_grind
  obtain ⟨hτo, hhD, -⟩ := Merge.hit_of_freeAt J.whole ho2 hd hfo
  have hhe : rayPt o d ztemx ∈ e := by
    zupdm; exact Geometry.right_mem_segment _ _
  have hh1 := hends _ hhe hhD
  rw [rayPt_fst] at hh1
  have hhz : rayPt o d ztemx = z := by
    zubjw
    · zulqr

    grind
  have hdσ : d = -σ := by
    grind
  refine ⟨by_grind, hdσ, hhz, by_grind, fun p hp hpD => ?_,
    fun p hp => by_grind⟩
  grind

/-- **An attachment of a chord along the ray is an arrival position of the reversed ray.** -/
theorem arrival_of_attach {W : Polygon} {e : Set Point} {p : ℕ} {t : ℝ} {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hA : SideAttach W e p t) (hpt : sidePt W p t = z)
    (hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ e) : Arrival W z (-σ) p t := by
  obtain ⟨hp, ht0, ht1, -, r, hr, hcl⟩ := hA
  refine ⟨hp, ht0, ht1, hpt, ?_⟩
  zuduy
  obtain ⟨s, ⟨hse, hsr⟩, hs0⟩ := ((hev.and ztmbi).and self_mem_nhdsWithin).exists
  zukfo
  have hdist : dist ztbwc z = s := dist_rayPt z hσ hs0'.le
  have h1 : sideLeft W p t ztbwc := by
    refine hcl _ hse ?_ ?_
    · zvmxe; intro h; simp_all
    simp_all
  zvnbr at h1 ⊢
  exact (sideLeft_rayPt_iff W p t σ hs0' one_pos).1 h1
variable (Q : Polygon) (N : NF)
/-- **The stop chord is the shot from its origin.** -/
theorem stopSet_eq (kind k b : ℕ) :
    stopSet J Q N kind k b = Merge.shoot J.whole (SweepIo.stopOrig J Q N kind k b) ztkz := by
  unfold stopSet SweepIo.stopOrig
  grind

/-- **The origin of an endpoint query out of range** is on the vertical line of the top of `C₂`
(the default chord record is the slit top). -/
theorem endOrigin_big {j : ℕ} (hj : N.nChords ≤ j / 2) :
    (endOrigin J Q N j).1 = J.right.top.1 := by
  have hch : N.chord ztwm = ztrp := by
    unfold NF.chord; exact List.getD_eq_default _ _ hj
  zuiym
  have hpos : (chainModel J.right).pos Q ztqzs = J.right.slitTop := by
    have hwa : (chainModel J.right).wa 0 = J.right.slitTop := rfl
    have hwb : (chainModel J.right).wb 0 = ((-J.right.radius, J.right.radius) : Point) := by
      rfl
    have hpar : (chainModel J.right).param Q ztqzs = 0 := by
      show (if ((chainModel J.right).wa 0).2 = ((chainModel J.right).wb 0).2 then 0 else _) = _
      rw [ite_eq_left by_rfl]
    zueew
    simp_all
  have hset : (N.chord ztwm).toSet ztj Q =
      hseg (Q.vtx 0).2 J.right.slitTop.1 J.right.slitTop.1 := by
    rw [hch]
    zumqj
    simp_all
  zulbr
  split_ifs
  · rw [hset, Merge.lend_hseg le_rfl]; rfl
  · rw [hset, Merge.rend_hseg le_rfl]; rfl
end
end S0Math
end Chazelle.Core
namespace Chazelle.Core
namespace S0Math
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed Sweep
@[expose] public section
variable (J : Merge.Junction)

/-- An end of a chord of `C₂` is off the domain of `C₂`, not above its top. -/
theorem end_off_right {c : Set Point} (hc : c ∈ Merge.augChords J.right) :
    Merge.lend c ∉ J.right.dom ∧ Merge.rend c ∉ J.right.dom ∧
      (Merge.lend c).2 ≤ J.right.top.2 ∧ (Merge.rend c).2 ≤ J.right.top.2 := by
  zubrv

  exact ⟨hH.left_not, hH.right_not, hy, hy⟩

/-- **(C4): the endpoint table.** -/
theorem case_C4 (hP : J.P.Simple) {Q : Polygon} {N₂ : NF} {T : ℕ → Option zthlt}
    (hT : TabOK J Q N₂ T) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hzR : z ∈ J.right.dom)
    {c : Set Point} (hc : c ∈ N₂.F ztj Q) {o : Point} {d : ℝ}
    (ho : ztmig ∨ ztlmu) (hfo : FreeAt J.whole o d)
    (hoR : o ∈ J.right.set) (hov : o ≠ J.shared) (hot : o ≠ J.right.top) (hdσ : d = -σ)
    (hoz : rayPt o d ztemx = z) {pz : ℕ} {tz : ℝ}
    (hA : Arrival (chainModel J.whole).W z (-σ) pz tz)
    (hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ Merge.shoot J.whole o d) :
    ∃ j, j < 2 * N₂.nChords ∧ T j = some ztoes ∧ endDir j = -σ ∧
      endOrigin J Q N₂ j ∈ J.right.set ∧ endOrigin J Q N₂ j ≠ J.shared ∧
      endOrigin J Q N₂ j ≠ J.right.top ∧ endOrigin J Q N₂ j = o := by
  have hd : d = 1 ∨ d = -1 := by_grind
  have ho2 := J.right.snd_le_top_of_mem_set hoR
  have ho2' := ho2.trans J.right_top_le
  have key : ∀ j, j < 2 * N₂.nChords → endOrigin J Q N₂ j = o → endDir j = d →
      ∃ j, j < 2 * N₂.nChords ∧ T j = some ztoes ∧ endDir j = -σ ∧
        endOrigin J Q N₂ j ∈ J.right.set ∧ endOrigin J Q N₂ j ≠ J.shared ∧
        endOrigin J Q N₂ j ≠ J.right.top ∧ endOrigin J Q N₂ j = o := by
    intro j hj hoj hdj
    obtain ⟨-, hm⟩ := hT j hj by_simp_all by_simp_all
      by_simp_all
    rw [hoj, hdj] at hm
    rcases hTj : T j with _ | ⟨p, t⟩
    · zugdm
      exfalso
      have hfr₂ : FreeAt J.right o d := by
        filter_upwards [hfo] with s hs
        exact dom_right J hs by_simp_all
      obtain ⟨-, hD₂, -⟩ := Merge.hit_of_freeAt J.right ho2 hd hfr₂
      simp_all
    · zugdm
      obtain ⟨hatt, hpt, -⟩ := hm
      rw [hoz] at hpt
      have harr : Arrival (chainModel J.whole).W z _ p t := arrival_of_attach hσ hatt hpt hev
      have hg : Genuine J.whole o d _ :=
        (genuine_iff J.whole ho2' hd).2 ⟨hfo, rfl⟩
      have h1 : Arrival (chainModel J.whole).W ztznp d p t := by
        simp_all
      have h2 : Arrival (chainModel J.whole).W ztznp d pz tz := by
        simp_all
      obtain ⟨rfl, rfl⟩ := arrival_unique hP ho2' hd hg h1 h2
      grind
  zugqq
  obtain ⟨k, hk, hkr⟩ := List.mem_iff_getElem.1 hr
  have hck : N₂.chord k = r := by unfold NF.chord; simp_all
  have hkn : k < N₂.nChords := hk
  rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine key ztckt by_omega ?_ ?_
    · zulbr
      simp_all
    · zumsn
  · refine key ztekz by_omega ?_ ?_
    · zulbr
      grind
    · zumsn

/-- **(C3): the top chords.** -/
theorem case_C3 (hP : J.P.Simple) {Q : Polygon} {N₂ : NF}
    (hN : IsNF ztj Q N₂) {rs : List ztcf}
    (hS : StopsOK J ztwzm (stopsOf J Q N₂ rs)) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hzR : z ∈ J.right.dom) {e : Set Point}
    (he : e ∈ F₂plus J ztwzm) (hfo : FreeAt J.whole J.right.top (-σ))
    (heo : e = Merge.shoot J.whole J.right.top (-σ)) (hze : z ∈ e)
    (hends : ∀ p ∈ e, p ∉ J.whole.dom → p = z ∨ p = J.right.top) (hey : ∀ p ∈ e, p.2 = z.2)
    (htopL : J.right.top ∉ J.left.set) (hT0 : 0 < J.whole.hitParam z σ)
    (hw : rayPt z σ ztbyn = J.right.top) {pz : ℕ} {tz : ℝ}
    (hA : Arrival (chainModel J.whole).W z (-σ) pz tz) (hLst : (Lst J : ℝ) ≤ oW J zthe)
    (hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ e) :
    ∃ r ∈ rs, r.1 = pz ∧ (chainModel J.whole).param Q ztbhg = tz ∧
      dirOf r.2.2.2.2 = -σ ∧
      SweepIo.stopOrig J Q N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2 = J.right.top := by
  have hS₂ : N₂.F _ Q ⊆ Merge.augChords J.right := hN.1.2.1
  zukv
  have hstop : StopChord2 J ztwzm e := Or.inr by_grind
  have hatt : SideAttach (chainModel J.whole).W e pz tz := by
    zuwq
    zubvb
    refine sideAttach_of_along J.whole hP ztfnm hp ht0 ht1 hσ ?_ ?_
    · grind
    grind
  obtain ⟨r, hr, hre⟩ := List.mem_map.1 (hS.2.1 e he hstop pz tz hatt hLst)
  simp only [Prod.mk.injEq] at hre
  obtain ⟨h1, h2, h3⟩ := hre
  refine ⟨r, hr, h1, h2, ?_⟩
  set o' := SweepIo.stopOrig J Q N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2 with ho'
  set d' := dirOf r.2.2.2.2 with hd'
  have hsh : Merge.shoot J.whole o' d' = e := (stopSet_eq J Q N₂ _ _ _).symm.trans h3
  have ho'e : o' ∈ e := by rw [← hsh]; exact origin_mem J
  have htope : J.right.top ∈ e := by zupdm; exact origin_mem J
  have hsh_off := fun h =>
    J.whole.not_mem_set_of_mem_dom h ztffl
  -- the origin of the record is the top of `C₂`
  have ho'top : o' = J.right.top := by
    zueyc
    unfold SweepIo.stopOrig
    by_cases hk0 : r.2.2.1 = 0
    · rw [ite_eq_left hk0]
      exfalso
      have hsm : J.shared ∈ e := by
        have := ho'e; rw [ho'] at this; unfold SweepIo.stopOrig at this
        grind
      rcases hends _ hsm hsh_off with h | h
      · exact J.right.not_mem_set_of_mem_dom by_grind J.shared_mem_right
      · exact htopL ztnzz
    by_cases hk1 : r.2.2.1 = 1
    swap
    · grind
    rw [ite_eq_right hk0, ite_eq_left hk1]
    · have hme : endOrigin J Q N₂ (2 * r.2.2.2.1 + if dirOf r.2.2.2.2 = 1 then 0 else 1) ∈ e := by
        have := ho'e; rw [ho'] at this; unfold SweepIo.stopOrig at this
        grind
      set j := 2 * r.2.2.2.1 + if dirOf r.2.2.2.2 = 1 then 0 else 1 with hj
      have hj2 : j / 2 = r.2.2.2.1 := by_grind
      by_cases hk : r.2.2.2.1 < N₂.nChords
      · -- a chord of `S₂`: its end is off the domain of `C₂`
        have hcF : (N₂.chord ztwm).toSet ztj Q ∈
            N₂.F ztj Q := by
          refine ⟨N₂.chord _, ?_, rfl⟩
          zudly
          rw [hj2, List.getD_eq_getElem _ _ hk]
          grind
        obtain ⟨hl, hr', hl2, hr2⟩ := end_off_right J (hS₂ hcF)
        have hoff : endOrigin J Q N₂ j ∉ J.right.dom ∧
            (endOrigin J Q N₂ j).2 ≤ J.right.top.2 := by
          unfold endOrigin; split_ifs
          · grind
          grind
        have hD := fun h =>
          hoff.1 (J.mem_right_dom_of_whole hoff.2 h)
        grind
      · -- out of range: the slit top's vertical line
        zumio
        have h1' := endOrigin_big J Q N₂ (j := j) by_omega
        grind
  -- the direction
  have hd'c : d' = 1 ∨ d' = -1 := dirOf_cases _
  rw [ho'top] at hsh
  have hzs : z ∈ Merge.shoot J.whole J.right.top d' := by_grind
  unfold Merge.shoot at hzs
  obtain ⟨lam, hlam0, hlam1, hzl⟩ := Geometry.mem_segment_iff_lerp.1 hzs
  have hz1 := congrArg Prod.fst hzl
  rw [Geometry.lerp_fst, rayPt_fst] at hz1
  have hw1 := congrArg Prod.fst hw
  rw [rayPt_fst] at hw1
  have hτ' := Merge.hitParam_nonneg J.whole J.right.top d'
  refine ⟨?_, ho'top⟩
  show d' = -σ
  rcases hd'c with h | h <;> rcases hσ with rfl | rfl <;> zvmwc at hz1 hτ' ⊢ <;>
    first | rfl | (exfalso; nlinarith [mul_nonneg hlam0 hτ']) | norm_num
end
end S0Math
namespace SweepIo
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Merge (FreeAt)
open WalkEmbed Sweep S0Math
@[expose] public section

/-- **The cases of the first hit of a side-0 query.** -/
theorem side0Math : Side0MathSpec := by
  intro P J N₂ rs ls T _hG hP hN hlog hstops htab z σ hσ hzL hzv hz2 hfree pz tz hA
  have hS₂ : ztrfs := hN.1.2.1
  have hS₂f : ztrfe := hN.1.1
  have hzR := left_pt_right_dom J hP hzL hzv hz2
  obtain ⟨hpz, htz0, htz1, hpt, hsec⟩ := hA
  have hLst : ztfzv :=
    Lst_lt_of_dom hP hpz htz0 htz1 by_simp_all
  refine ⟨hLst.le, fun i hi => ?_⟩
  have hz₁ := J.left.snd_le_top_of_mem_set hzL
  have hzD := fun h =>
    J.whole.not_mem_set_of_mem_dom h (J.left_set_subset hzL)
  by_cases hc : rayPt z σ ztbyn ∈ J.right.set ∧
      rayPt z σ ztbyn ∉ J.left.set
  swap
  · exact Or.inl (left_hit_of J hz₁ hσ hfree hc)
  have hR2 := right_hit_of J hz2 hσ hfree hc.1
  by_cases hB : ∃ e ∈ F₂plus J ztwis,
      ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ e
  · -- the ray runs along a chord of `F₂⁺`
    obtain ⟨e, he, hev⟩ := hB
    obtain ⟨o, d, hd, hfo, heo, hkind⟩ := F₂plus_origin J he
    zudoz
    have ho2 := F₂plus_snd_le J hS₂ he hoe
    have hoR' : o ∉ J.right.dom := by
      rcases hkind with rfl | rfl | ⟨c, hc', ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
      · exact fun h => J.right.not_mem_set_of_mem_dom h J.shared_mem_right
      · exact fun h => J.right.not_mem_set_of_mem_dom h J.right.top_mem_set
      · exact (end_off_right J zthxv).1
      · exact (end_off_right J zthxv).2.1
    have hoD := fun h => hoR' (J.mem_right_dom_of_whole ho2 h)
    have hzo : z ≠ o := by_grind
    obtain ⟨hwo, hdσ, hoz, hT0, hends, hey⟩ :=
      along_end J ztfnm hσ hd hzD hoD hzo heo hfo hev
    have hze : ztpqq := by rw [heo, ← hoz]; exact Geometry.right_mem_segment _ _
    rw [hwo] at hc
    by_cases hot : o = J.right.top
    · -- (C3): a top chord
      subst hot
      zurx
      have heo' : e = Merge.shoot J.whole J.right.top (-σ) := by_grind
      have hfo' : FreeAt J.whole J.right.top (-σ) := by_grind
      obtain ⟨r, hr, h1, h2, h3, h4⟩ := case_C3 J hP hN hstops hσ hzR he hfo' heo' hze
        by_omega hey hc.2 hT0 hwo ztlwi hLst.le hev
      grind
    · rcases hkind with rfl | rfl | ⟨c, hc', hco⟩
      · exact absurd J.shared_mem_left hc.2
      · grind
      · -- (C4): an endpoint query
        zubef
        have hov : o ≠ J.shared := fun h => hc.2 ztnzz
        obtain ⟨j, hj, hTj, hdj, h1, h2, h3, h4⟩ := case_C4 J hP htab hσ hzR hc' hco hfo hc.1
          hov hot hdσ hoz ztlwi by_grind
        grind
  · -- the ray starts in a region of `F₂⁺`
    zubvb
    have hFam := chordFamily_hPoly J.whole ztnld ztsxq
    obtain ⟨U, hU, hray, hface⟩ := leave_region J.whole hP hFam hσ hpz htz0 htz1 hpt hsec
      (left_pt_abs J hzL) by_simp_all
    have hface' : AfterFaces ztbm pz tz U ∨
        BeforeFaces ztbm pz tz U := by
      grind
    obtain ⟨V, hV, hVray, hlab⟩ := query_right J hP hS₂ hS₂f hU hz2 hσ hray hc.1 hc.2
    obtain ⟨hil, hlo, hhi⟩ := hi
    have hlen : ztygf := List.length_map _
    have hres := labels_of_log J hP hS₂ hS₂f hlog by_omega hpz htz0
      htz1 hLst hlo (fun h => hhi by_omega) hU hface' V hV hlab
    zuhl
    exact ⟨hR2, V, hV, hres, hVray⟩
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
@[expose] public section
def κ0 (κL κS : ℕ → ℕ) (D : ℕ) : ℕ :=
  3 * (8 + localK 0 0 ztef D + 5500 + 16 * ztzbb) + κL D + κS D + 62750
theorem localK_lin' (T Fg Da Dc : ℕ) :
    localK T Fg Da Dc = localK 0 0 Da Dc + 5500 * T + ztpub * ztjem := by
  zulbx

/-- **The cost bound.** -/
theorem kc0_le (κL κS : ℕ → ℕ) (c₀ : Config) (F : ℕ → ℕ) :
    Kc0 κL κS c₀ F ≤ κ0 κL κS zto * ztwit := by
  unfold Kc0 Kcls Kbr Kmain Klh lhsK κ0
  rw [localK_lin']
  grind

/-- A larger cost constant keeps an initialisation contract. -/
theorem initSpec_mono {init : Stmt} {Aux : Polygon → Merge.Junction → NF → Config → Prop}
    {κ κ' : ℕ → ℕ} (h : InitSpec init Aux κ) (hle : ∀ D, κ D ≤ κ' D) : InitSpec init Aux κ' := by
  refine ztfzi
  have hk : κ ztxgn * ztbbd *
      ztuc ≤
      κ' ztxgn * ztbbd *
      ztuc :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (hle _)) le_rfl
  obtain ⟨c', k, ex, hk', fr, hfix, haux⟩ := h.1 P W X Ok J H N₁ N₂ E c hw hA by_omega
  grind

/-- **The candidate step of side `0`.** -/
theorem cand0Spec (hM : Side0MathSpec) (hS : S0CandSpec) (hL : Lab0Spec) : Cand0Spec := by
  obtain ⟨initC, candC, Aux, κS, hInit, hRob, hSC⟩ := s0CandSpec_iff.1 hS
  obtain ⟨lab0, κL, hLab⟩ := lab0Spec_iff.1 hL
  refine ⟨initC, cand0 lab0 candC, Aux, κ0 κL κS,
    initSpec_mono hInit (fun D => by unfold κ0; omega), hRob, ?_⟩
  intro sh Bs F X Ok hsh hBs hXl P W c₀ c J H N₁ N₂ E z hA hAux hI hQ h0 hroom
  have hk := kc0_le κL κS c₀ F
  exact (cand0_irs hM hLab hSC hsh hBs hXl hA hAux hI hQ h0 by_omega).mono hk ztb

/-- **The candidate step of side `0`**, with the mathematics of side `0` (`side0Math`). -/
theorem cand0Spec_of (hS : S0CandSpec) (hL : Lab0Spec) : Cand0Spec :=
  cand0Spec side0Math hS hL
end
end SweepIo
end Chazelle.Core
section
set_option hygiene false
local macro "zqbdc" : tactic => `(tactic| (right; right; unfold sw at *; omega))
set_option hygiene true

/-!
# The sweep (WP-D), stage 2: the loop over the stop origins and the assembly of `StopTask`

`stopTask_of (hO : OrgTask) (hS : SortTask) : StopTask`: the model descriptor of `C₂`
(`md2Init`), the raw array (`11 (4 K₂ + 8)` words, `gRB`, `gRC := 0`), the per-origin step for the
codes `(0, 0, b)`, `(2, 0, b)` and `(1, k, b)` (`k < K₂`, `b ≤ 1`), the sort, and `StopOut` from
`stopsOK_of'` and `stop_complete`.  Loop registers `sw 4200 …`.
-/
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Registers of the loop -/
def slK : ℕ := sw 4200
def slN : ℕ := sw 4201
def slV : ℕ := sw 4202

/-- `n` increments of the allocator. -/
def slInc : ℕ → Stmt
  | 0 => .skip
  | n + 1 => .seq ztckm ztweg
theorem slInc_irs (hK : Consts c₀) : ∀ (n : ℕ) {c : Config}, IInv W c₀ c →
    c.nreg ALLOC + n ≤ W →
    IRS P W c₀ ztweg c n (fun c' => c'.nreg ALLOC = c.nreg ALLOC + n ∧
      ztjn ∧ c'.nmem = c.nmem)
  | 0, c, hI, _ => IRS.skip hI by_simp_all
  | n + 1, c, hI, hroom => by
    zuibe
    zuegb
    have h1 : IRS P W c₀ ztckm c 1 (fun c' =>
        c' = { c with nreg := upd c.nreg ALLOC (c.nreg ALLOC + c.nreg K1) }) := by
      refine IRS.ofExec hI ex le_rfl (fun r _ hr => ?_) rfl ztcj rfl rfl
        by_simp by_simp_all rfl
      simp_all
    refine (IRS.seq (K₂ := n) h1 ?_).mono by_omega ztb
    zuer
    have hA : ({ c with nreg := upd c.nreg ALLOC (c.nreg ALLOC + c.nreg K1) } : Config).nreg ALLOC =
        c.nreg ALLOC + 1 := by_simp_all
    refine (slInc_irs hK n hI₁ by_omega).mono le_rfl ?_
    zuvo
    refine ⟨by_omega, fun r hr => ?_, a3⟩
    simp_all
variable {J : Merge.Junction} {N₂ : NF} {c₁ M1 : Config} {o : Stmt} {Ko : ℕ → ℕ}
/-- The raw records only read their eleven words. -/
theorem slRawV_congr {N : NF} {m m' : ℕ → ℕ} {RB i : ℕ}
    (h : ∀ j, j < 11 → m' ztnoo = m ztnoo) (hv : RawV P J N m RB i) :
    RawV P J N m' RB i := by
  have e1 : rawRec m' RB i = rawRec m RB i := by
    unfold rawRec
    rw [show RB + 11 * i = RB + 11 * i + 0 by ring, h 0 by_norm_num, h 1 by_norm_num,
      h 3 by_norm_num, h 4 by_norm_num, h 5 by_norm_num]
  have e2 : rawDc m' RB i = rawDc m RB i := by unfold rawDc; simp_all
  have e3 : rawAux m' RB i = rawAux m RB i := by
    unfold rawAux
    simp_all
  unfold RawV at *; simp_all

/-- **The invariant of the origin loop** (`M1` the configuration after `md2Init`, the raw array
at `A0 = M1.ALLOC`, `u` codes done, the set `D` of done codes). -/
structure SlpInv (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c M1 : Config) (u : ℕ)
    (D : ℕ → ℕ → ℕ → Prop) (c' : Config) : Prop where
  rb : c'.nreg gRB = M1.nreg ALLOC
  room : M1.nreg ALLOC + 11 * (4 * N₂.nChords + 8) ≤ c'.nreg ALLOC
  cnt : c'.nreg gRC ≤ 2 * u
  valid : ∀ i, i < c'.nreg gRC → RawV P J N₂ c'.nmem zthrk i
  compl : ∀ kind k b, D kind k b → OrgD P J N₂ kind k b → ∀ (p : ℕ) (t : ℝ),
    SideAttach (chainModel J.whole).W ztwja p t →
    (Lst J : ℝ) ≤ oW J ztk → ∃ i, i < c'.nreg gRC ∧
      (rawRec c'.nmem zthrk i).1 = p ∧
      rPar P J ztznm = t ∧
      rSet P J N₂ ztznm = stopSet J zta N₂ kind k b
  memM : ∀ a, a < M1.nreg ALLOC → c'.nmem a = M1.nmem a
  regM : c'.nreg gMD2 = M1.nreg gMD2 ∧ c'.nreg gCD2 = M1.nreg gCD2
  regs : ∀ r, bandOf r ∉ oracleBands → ¬ S2R r → r ≠ ALLOC → c'.nreg r = c.nreg r
theorem slpOrgR_S2R {r : ℕ} (h : SOrgR r) : S2R r := by
  unfold SOrgR at h; unfold S2R
  rcases h with h | h | h | h | h
  · omega
  · right; right; subst h; decide
  · zqbdc
  · zqbdc
  · zqbdc

/-- The model context of `C₂` along the invariant. -/
theorem SlpInv.ctx {c M1 c' : Config} {u : ℕ}
    {D : ℕ → ℕ → ℕ → Prop} (hS : SlpInv P J N₂ c M1 u D c')
    (hctx : MCtx P W J.right N₂ ztbmp gMD2 gCD2 ztbz M1)
    (hIM : IInv W c₀ M1) (hI' : IInv W c₀ c') :
    MCtx P W J.right N₂ ztbmp gMD2 gCD2 ztbz c' := by
  have hA1 : M1.nreg ALLOC ≤ c'.nreg ALLOC := by have := hS.room; omega
  refine hctx.transport ztez hS.memM hA1
  zukx
  · exact hS.regM.1
  · exact hS.regM.2
  · exact (hI'.hin _ by_trivial).trans (hIM.hin _ by_trivial).symm
  · exact (hI'.hin _ by_trivial).trans
      (hIM.hin _ by_trivial).symm
  · exact (hI'.hin _ by_trivial).trans
      (hIM.hin _ by_trivial).symm
set_option maxHeartbeats 4000000 in
/-- **One per-origin step** keeps the invariant and adds its code. -/
theorem slOrg_step {M1 c' c'' : Config} {u : ℕ}
    {D : ℕ → ℕ → ℕ → Prop} (hS : SlpInv P J N₂ c M1 u D c') (hu : u + 1 ≤ 2 * N₂.nChords + 4)
    (hO : OrgOut P J N₂ ztjrm (c'.nreg oKk) (c'.nreg oB) c' c'') :
    SlpInv P J N₂ c M1 ztcol
      (fun kind k b => D kind k b ∨ (kind = c'.nreg oKd ∧ k = c'.nreg oKk ∧ b = c'.nreg oB)) c'' ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ SOrgR r → r ≠ ALLOC → c''.nreg r = c'.nreg r) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := hO
  have hcnt := hS.cnt
  rw [hS.rb] at o3 o4 o5
  have keepOld : ∀ i, i < c'.nreg gRC → ∀ j, j < 11 →
      c''.nmem _ = c'.nmem (M1.nreg ALLOC + 11 * i + j) :=
    fun i hi j hj => o5 _ (by have := hS.room; omega) by_omega
  have hR := fun r h1 h2 h3 =>
    o7 r ztsg h3 ztu
  have rB : ztsea := hR _ by_decide by_decide
    (by unfold SOrgR gRB gRC sw; omega)
  have rM : c''.nreg gMD2 = c'.nreg gMD2 := hR _ by_decide
    by_decide (by unfold SOrgR gMD2 gRC sw; omega)
  have rC : c''.nreg gCD2 = c'.nreg gCD2 := hR _ by_decide
    by_decide (by unfold SOrgR gCD2 gRC sw; omega)
  refine ⟨⟨by rw [rB, hS.rb], by have := hS.room; omega, by_omega,
    fun i hi => ?_, fun kind k b hD hOD p t hA hL => ?_, fun a ha => ?_,
    ⟨by rw [rM, hS.regM.1], by rw [rC, hS.regM.2]⟩, fun r h0 h1 h2 => ?_⟩, o7⟩
  · by_cases hi' : i < c'.nreg gRC
    · exact slRawV_congr by_simp_all (hS.valid i hi')
    simp_all
  · rcases hD with hD | ⟨rfl, rfl, rfl⟩
    · obtain ⟨i, hi, e1, e2, e3⟩ := hS.compl kind k b hD hOD p t hA hL
      have hrr : rawRec c''.nmem zthrk i = rawRec c'.nmem zthrk i := by
        unfold rawRec
        rw [show M1.nreg ALLOC + 11 * i = M1.nreg ALLOC + 11 * i + 0 by ring,
          keepOld i hi 0 by_norm_num, keepOld i hi 1 by_norm_num,
          keepOld i hi 3 by_norm_num, keepOld i hi 4 by_norm_num, keepOld i hi 5 by_norm_num]
      grind
    grind
  · rw [o5 a (by have := hS.room; omega) by_omega, hS.memM a ha]
  · rw [o7 r h0 (fun h => h1 (slpOrgR_S2R h)) h2, hS.regs r h0 h1 h2]

/-- The invariant survives changes of the code and loop registers `sw 4010 … sw 4999`. -/
theorem SlpInv.regChange {c M1 c' c'' : Config} {u : ℕ}
    {D : ℕ → ℕ → ℕ → Prop} (h : SlpInv P J N₂ c M1 u D c')
    (hr : ∀ r, ¬ (sw 4010 ≤ r ∧ r < sw 5000) → c''.nreg r = c'.nreg r)
    (hm : c''.nmem = c'.nmem) : SlpInv P J N₂ c M1 u D c'' := by
  have e : ∀ r, r < sw 4010 → c''.nreg r = c'.nreg r := by_simp_all
  have eA : ztsdz := e _ by_decide
  have eB : ztsea := e _ by_decide
  have eC : c''.nreg gRC = c'.nreg gRC := e _ by_decide
  refine ⟨by rw [eB]; exact h.rb, by rw [eA]; exact h.room, by rw [eC]; exact h.cnt,
    fun i hi => by zvmwi; exact h.valid i by_omega,
    fun kind k b hD hOD p t hA hL => ?_, fun a ha => by zvmwi; exact h.memM a ha,
    ⟨by zuoor; exact h.regM.1,
      by zuoor; exact h.regM.2⟩, fun r h0 h1 h2 => ?_⟩
  · obtain ⟨i, hi, e1⟩ := h.compl kind k b hD hOD p t hA hL
    grind
  · rw [← h.regs r h0 h1 h2]
    exact hr r (fun h' => h1 (by unfold S2R; right; right; unfold sw at *; omega))

/-- Set the code registers and run the per-origin step. -/
def slCode (o : Stmt) (kd : ℕ) (ins : Instr) (b : ℕ) : Stmt :=
  .seq (block [.constN oKd kd, ins, .constN oB b]) o
set_option maxHeartbeats 4000000 in
theorem slCode_irs {u : ℕ}
    {D : ℕ → ℕ → ℕ → Prop} {kd b kv : ℕ} {ins : Instr}
    (hctx : MCtx P W J.right N₂ ztbmp gMD2 gCD2 ztbz M1)
    (hO : ∀ c', IInv W c₀ c' → MCtx P W J.right N₂ ztbmp gMD2 gCD2 ztbz c' →
      c'.nreg oKd ≤ 2 → c'.nreg oB ≤ 1 → ztfqd →
      c₀.nreg ALLOC ≤ c'.nreg gRB →
      c'.nreg gRB + 11 * ztlki ≤ c'.nreg ALLOC → c'.nreg ALLOC + Ko ztjrm ≤ W →
      IRS P W c₀ o c' ztbaef ztgem)
    (hA0 : Consts c₀) (hIM : IInv W c₀ M1) (hI : IInv W c₀ c) (hS : SlpInv P J N₂ c₁ M1 u D c)
    (hins : (ins = .constN oKk 0 ∧ kv = 0) ∨ (ins = .copyN oKk slK ∧ kv = c.nreg slK))
    (hkd : kd ≤ 2) (hb : b ≤ 1) (hk : kd = 1 → kv < N₂.nChords)
    (hu : u + 1 ≤ 2 * N₂.nChords + 4) (hroom : c.nreg ALLOC + ztrij ≤ W) :
    IRS P W c₀ (slCode o kd ins b) c ztrij (fun c' => SlpInv P J N₂ c₁ M1 ztcol
      (fun kind k b' => D kind k b' ∨ (kind = kd ∧ k = kv ∧ b' = b)) c' ∧
      c'.nreg slK = c.nreg slK ∧ c'.nreg slN = c.nreg slN ∧ c'.nreg slV = c.nreg slV) := by
  have hKc := hA0.fix hI
  have ok : okB W c.nmem [.constN oKd kd, ins, .constN oB b] c.nreg := by
    rcases hins with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨ztkma,
        ⟨iscr_sw by_decide by_decide, by_omega⟩,
        ⟨iscr_sw by_decide by_decide, by_omega⟩, trivial⟩
    · exact ⟨ztkma,
        iscr_sw by_decide by_decide,
        ⟨iscr_sw by_decide by_decide, by_omega⟩, trivial⟩
  refine (IRS.seq (K₂ := Ko kd) (IRS.block _ hI ok) ?_).mono by_simp ztb
  zubib
  have vals : c₂.nreg oKd = kd ∧ c₂.nreg oKk = kv ∧ c₂.nreg oB = b ∧
      (∀ r, r ≠ oKd → r ≠ oKk → r ≠ oB → c₂.nreg r = c.nreg r) ∧ c₂.nmem = c.nmem := by
    subst hc2
    rcases hins with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      simp only [regB, regI, oKd, oKk, oB, slK, sw, Nat.reduceAdd]
      simp only [upd, Nat.reduceEqDiff, ite_true, ite_false]
      refine ⟨trivial, trivial, trivial, fun r h1 h2 h3 => ?_, trivial⟩
      simp only [h1, h2, h3, ite_false]
  obtain ⟨v1, v2, v3, v4, v5⟩ := vals
  have hS2 := hS.regChange (fun r hr => v4 r
    ztxgu ztxgu
    ztxgu) v5
  have hA2 : ztbae := v4 _ by_decide
    by_decide by_decide
  have hO2 := hO c₂ hI₂ (hS2.ctx hctx hIM hI₂) by_omega by_omega
    by_omega (by zupcq; exact hIM.hA)
    (by zupcq; have := hS2.room; have := hS2.cnt; omega)
    by_grind
  refine hO2.mono by_simp_all ?_
  zufxk
  obtain ⟨h1, h2⟩ := slOrg_step hS2 hu hc'
  rw [v1, v2, v3] at h1
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [h2 _ ztmr
      (by unfold SOrgR slK gRC sw; omega) by_decide,
      v4 _ by_decide by_decide by_decide]
  · rw [h2 _ ztmr
      (by unfold SOrgR slN gRC sw; omega) by_decide,
      v4 _ by_decide by_decide by_decide]
  · rw [h2 _ ztmr
      (by unfold SOrgR slV gRC sw; omega) by_decide,
      v4 _ by_decide by_decide by_decide]

/-- The allocation of the raw array: `44` words per round, `slV` rounds. -/
def slAlloc : Stmt := .whileLtN slK slV (.seq (slInc 44) ztnsh)
set_option maxHeartbeats 4000000 in
theorem slAlloc_irs (hK : Consts c₀) (hI : IInv W c₀ c) (h0 : c.nreg slK = 0)
    (hroom : c.nreg ALLOC + ztowi ≤ W) :
    IRS P W c₀ slAlloc c ztowi (fun c' =>
      c'.nreg ALLOC = c.nreg ALLOC + 44 * c.nreg slV ∧ c'.nreg slK = c.nreg slV ∧
      ztgsq ∧ c'.nmem = c.nmem) := by
  set V := c.nreg slV
  have hVW : V ≤ W := by_omega
  refine (IRS.while (Kb := 45) (fun c' => c'.nreg ALLOC = c.nreg ALLOC + 44 * c'.nreg slK ∧
      c'.nreg slK ≤ V ∧ ztgsq ∧ c'.nmem = c.nmem)
      (fun c' => V - c'.nreg slK) ?_ ?_ hI by_simp_all
      by_omega).mono by_omega ?_
  · rintro c' ⟨-, -, hr, -⟩ ht
    rw [hr slV by_decide by_decide] at ht; omega
  · rintro c' hI' ⟨a1, a2, a3, a4⟩ ht hroom'
    have hV' := a3 slV by_decide by_decide
    rw [hV'] at ht
    refine IRS.seq (K₂ := 1) (slInc_irs hK 44 hI' by_omega) ?_
    rintro c₁ hI₁ - - ⟨b1, b2, b3⟩
    have k1 := (hK.fix hI₁).2.1
    have hk1 : c₁.nreg slK = c'.nreg slK := b2 _ by_decide
    refine (IRS.block [.addN slK slK K1] hI₁ ⟨⟨iscr_sw by_decide
      by_decide, by_omega⟩, trivial⟩).mono le_rfl ?_
    rintro c'' rfl
    have v : ∀ r, r ≠ slK → regB c₁.nmem [.addN slK slK K1] c₁.nreg r = c₁.nreg r := by
      zubxc
    have vk : regB c₁.nmem [.addN slK slK K1] c₁.nreg slK = c'.nreg slK + 1 := by
      simp only [regB, regI, upd_same, k1, hk1]
    grind
  grind

/-- The codes done after the shared and top codes and the wall codes of the chords `< k₀`. -/
def slD (k₀ kind k b : ℕ) : Prop := b ≤ 1 ∧ (((kind = 0 ∨ kind = 2) ∧ k = 0) ∨ (kind = 1 ∧ k < k₀))
theorem SlpInv.monoD {c M1 c' : Config} {u u' : ℕ}
    {D D' : ℕ → ℕ → ℕ → Prop} (h : SlpInv P J N₂ c M1 u D c')
    (hD : ∀ kind k b, D' kind k b → D kind k b) (hu : u ≤ u') : SlpInv P J N₂ c M1 u' D' c' :=
  ⟨h.rb, h.room, by have := h.cnt; omega, h.valid,
    fun kind k b hd => h.compl kind k b by_simp_all, h.memM, h.regM, h.regs⟩

/-- The loop over the chords of `N₂` (both directions). -/
def slKLoop (o : Stmt) : Stmt :=
  .whileLtN slK slN (.seq (slCode o 1 ztsou 0)
    (.seq (slCode o 1 ztsou 1) ztnsh))
set_option maxHeartbeats 4000000 in
theorem slKLoop_irs
    (hctx : MCtx P W J.right N₂ ztbmp gMD2 gCD2 ztbz M1)
    (hO : ∀ c', IInv W c₀ c' → MCtx P W J.right N₂ ztbmp gMD2 gCD2 ztbz c' →
      c'.nreg oKd ≤ 2 → c'.nreg oB ≤ 1 → ztfqd →
      c₀.nreg ALLOC ≤ c'.nreg gRB →
      c'.nreg gRB + 11 * ztlki ≤ c'.nreg ALLOC → c'.nreg ALLOC + Ko ztjrm ≤ W →
      IRS P W c₀ o c' ztbaef ztgem)
    (hK : Consts c₀) (hIM : IInv W c₀ M1) (hI : IInv W c₀ c)
    (hS : SlpInv P J N₂ c₁ M1 4 ztwef c) (h0 : c.nreg slK = 0) (hN : c.nreg slN = N₂.nChords)
    (hroom : c.nreg ALLOC + ztzhq ≤ W) :
    IRS P W c₀ ztweh c ztzhq (fun c' =>
      SlpInv P J N₂ c₁ M1 (4 + 2 * N₂.nChords) (slD N₂.nChords) c') := by
  have hKW : N₂.nChords ≤ W := by_nlinarith
  refine (IRS.while (Kb := 7 + 2 * Ko 1) (fun c' => SlpInv P J N₂ c₁ M1 (4 + 2 * c'.nreg slK)
      (slD (c'.nreg slK)) c' ∧ c'.nreg slN = N₂.nChords ∧ c'.nreg slK ≤ N₂.nChords)
      (fun c' => N₂.nChords - c'.nreg slK) ?_ ?_ hI by_simp_all
      by_grind).mono by_simp ?_
  · omega
  · rintro c' hI' ⟨hS', hN', hk'⟩ ht hroom'
    rw [hN'] at ht
    set k := c'.nreg slK with hk_def
    refine (IRS.seq (K₂ := 4 + Ko 1) (slCode_irs hctx hO hK hIM hI' hS'
      ztxch by_norm_num by_norm_num (fun _ => ht) by_omega by_omega) ?_).mono
      by_omega ztb
    rintro c₂ hI₂ - hA₂' ⟨hS₂, k2, n2, -⟩
    refine (IRS.seq (K₂ := 1) (slCode_irs hctx hO hK hIM hI₂ hS₂
      ztxch by_norm_num by_norm_num by_simp_all
      by_omega by_omega) ?_).mono by_omega (fun _ h => h)
    rintro c₃ hI₃ - - ⟨hS₃, k3, n3, -⟩
    have k1 := (hK.fix hI₃).2.1
    refine (IRS.block [.addN slK slK K1] hI₃ ⟨⟨iscr_sw by_decide
      by_decide, by_omega⟩, trivial⟩).mono le_rfl ?_
    rintro c'' rfl
    have v : ∀ r, r ≠ slK → regB c₃.nmem [.addN slK slK K1] c₃.nreg r = c₃.nreg r := by
      zubxc
    have vk : regB c₃.nmem [.addN slK slK K1] c₃.nreg slK = k + 1 := by
      simp only [regB, regI, upd_same, k1, k3, k2, hk_def]
    have hS₄ := hS₃.regChange (c'' := { c₃ with nreg := regB c₃.nmem [.addN slK slK K1] c₃.nreg })
      (fun r hr => v r ztxgu) rfl
    refine ⟨⟨?_, by_grind,
      by simp_all⟩, by_grind⟩
    dsimp only at hS₄ ⊢
    rw [vk]
    refine hS₄.monoD ?_ by_omega
    rintro kind kk b ⟨hb, h | ⟨rfl, hlt⟩⟩
    · exact Or.inl (Or.inl ⟨hb, Or.inl h⟩)
    · zuotn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h | rfl
      · exact Or.inl (Or.inl ztuha)
      omega
  grind
theorem slp_clog_le {K L : ℕ} (hL : L = Nat.clog 2 K) (_hK : 1 ≤ K) {x : ℕ} (hx : x ≤ 16 * K) :
    Nat.clog 2 x ≤ L + 4 := by
  have h1 : K ≤ 2 ^ L := by zvnlm; exact Nat.le_pow_clog by_norm_num K
  have h2 : x ≤ 2 ^ ztsyw := by_grind
  exact (Nat.clog_le_of_le_pow h2)
theorem slp_cost (κo κs K₁ K₂ F T L : ℕ) (hL : L = Nat.clog 2 ztctf) (hT : T ≤ L + 3) :
    25 + (5 + (ztzbf + (1 + (ztblp +
      (ztblp + (ztblp +
      (ztblp + (((7 + 2 * (κo * 1 * ztjir) + 2) * K₂ + 2) +
      κs * ztckw * ztzch)))))))) ≤
    (24 * κo + 45 * κs + 400) * ztctf * (F + L + 1) := by
  have hc : Nat.clog 2 ztckw ≤ L + 4 := slp_clog_le hL by_omega by_omega
  set Kc := K₁ + K₂ + 1 with hKc
  set Y := F + L + 1 with hY
  have hX : F + T + 1 ≤ 4 * Y := by_omega
  have hY1 : 1 ≤ Y := by_omega
  have hK1 : 1 ≤ Kc := by_omega
  have e1 : κo * Kc * ztjir ≤ κo * Kc * ztsta := Nat.mul_le_mul_left _ hX
  have e2 : κo * 1 * ztjir ≤ κo * ztsta := by zuoev; exact Nat.mul_le_mul_left _ hX
  have e3 : κs * ztckw * ztzch ≤ κs * (9 * Kc) * (5 * Y) := by
    apply Nat.mul_le_mul by_grind by_omega
  grind

/-- The setup of the raw array. -/
def slSetup : List Instr :=
  [.copyN gRB ALLOC, .constN gRC 0, .loadN slN ztbz, .addN slV slN K2, .constN slK 0]

/-- **Stage 2**: the model descriptor of `C₂`, the raw array, the codes, the sort. -/
def slpStopP (o srt : Stmt) : Stmt :=
  .seq md2Init (.seq (block slSetup) (.seq slAlloc (.seq (block [.constN slK 0])
    (.seq (slCode o 0 ztjcu 0) (.seq (slCode o 0 ztjcu 1)
    (.seq (slCode o 2 ztjcu 0) (.seq (slCode o 2 ztjcu 1)
    (.seq ztweh srt))))))))
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **`StopTask` from the per-origin step and the sort.** -/
theorem stopTask_of (hO : OrgTask) (hS : SortTask) : StopTask := by
  obtain ⟨org, κo, hOrg⟩ := hO
  obtain ⟨srt, κs, hSrt⟩ := hS
  refine ⟨fun sh => slpStopP ztwbe srt, fun D => 24 * κo D + 45 * κs + 400, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hroom
  set Kc := N₁.nChords + N₂.nChords + 1 with hKc
  set XX := F ztq + c₀.nreg TLR + 1 with hXX
  set Ko : ℕ → ℕ := fun kd => κo zto * (if kd = 1 then 1 else Kc) * XX with hKo
  have hOc : ∀ c', IInv W c₀ c' → MCtx P W J.right N₂ _ gMD2 gCD2 _ c' →
      c'.nreg oKd ≤ 2 → c'.nreg oB ≤ 1 → ztfqd →
      c₀.nreg ALLOC ≤ c'.nreg gRB →
      c'.nreg gRB + 11 * ztlki ≤ c'.nreg ALLOC → c'.nreg ALLOC + Ko _ ≤ W →
      IRS P W c₀ _ c' (Ko _)
        _ :=
    fun c' h1 h2 h3 h4 h5 h6 h6' h7 => hOrg sh Bs F X Ok P W c₀ c' J N₁ N₂ E h1 h2 h3 h4 h5 h6 h6' h7
  zumbu
  have hcost := slp_cost (κo zto) κs N₁.nChords N₂.nChords ztwiu
    _ _ rfl E.hTLR
  set K₂ := N₂.nChords with hK₂d
  set R9 := κs * ztckw * ztdld with hR9
  set R8 := (ztdyh * K₂ + 2) + R9 with hR8
  set R7 := ztrii + R8 with hR7
  set R6 := ztrii + R7 with hR6
  set R5 := ztrih + R6 with hR5
  set R4 := ztrih + R5 with hR4
  set R3 := 1 + R4 with hR3
  set R2 := ztzbf + R3 with hR2
  set R1 := 5 + R2 with hR1
  have hKo0 : Ko 0 = κo zto * Kc * XX := by_rfl
  have hKo2 : Ko 2 = κo zto * Kc * XX := by_rfl
  have hKo1 : Ko 1 = κo zto * 1 * XX := by_rfl
  have hT : 25 + R1 ≤ (24 * κo zto + 45 * κs + 400) * Kc *
      (F ztq + Nat.clog 2 Kc + 1) := by
    simp only [hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hKo0, hKo2, hKo1]; omega
  have hroom' : c.nreg ALLOC + (25 + R1) ≤ W := by
    dsimp only at hroom; exact le_trans (Nat.add_le_add_left hT _) hroom
  refine (IRS.seq (md2Init_irs E hI by_omega) ?_).mono hT ztb
  have hRge : 47 * ztjjk + 8 ≤ R1 := by rw [hR1, hR2, hR3]; omega
  rintro c₁ hI₁ hA₁ hA₁' ⟨hctx₁, r1, a1, m1⟩
  -- the setup
  have hKc1 := hK.fix hI₁
  have hNW : ztyua := by
    rw [hI₁.hin _ by_trivial]
    exact E.hNW₂.transport hI₁.hm
  have hK2m : c₁.nmem _ = K₂ := hNW.holds.1
  have k2c := hKc1.2.2.2.2.2.1
  have okS : okB W c₁.nmem slSetup c₁.nreg := by
    simp only [slSetup, okB, okI, regI, gRB, gRC, slN, slV, slK, K2, ALLOC, sw, Nat.reduceAdd]
      at hK2m k2c ⊢
    simp only [upd, Nat.reduceEqDiff, ite_true, ite_false, hK2m, k2c]
    refine ⟨iscr_sw by_norm_num by_norm_num, ztgpa,
      iscr_sw by_norm_num by_norm_num, ⟨iscr_sw by_norm_num by_norm_num, ?_⟩,
      ⟨iscr_sw by_norm_num by_norm_num, by_omega⟩, trivial⟩
    have := hI₁.hw; omega
  refine IRS.seq (IRS.block _ hI₁ okS) ?_
  rintro M1 hIM hAMa hAMb hM1
  have vals : M1.nreg gRB = c₁.nreg ALLOC ∧ M1.nreg gRC = 0 ∧ M1.nreg slN = K₂ ∧
      M1.nreg slV = K₂ + 2 ∧ M1.nreg slK = 0 ∧
      (∀ r, r ≠ gRB → r ≠ gRC → r ≠ slN → r ≠ slV → r ≠ slK → M1.nreg r = c₁.nreg r) ∧
      M1.nmem = c₁.nmem := by
    subst hM1
    simp only [slSetup, gRB, gRC, slN, slV, slK, K2, ALLOC, sw, Nat.reduceAdd] at hK2m k2c ⊢
    simp only [regB, regI, upd, Nat.reduceEqDiff, ite_true, ite_false, hK2m, k2c]
    refine ⟨trivial, trivial, trivial, trivial, trivial, fun r h1 h2 h3 h4 h5 => ?_, trivial⟩
    simp only [h1, h2, h3, h4, h5, ite_false]
  obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := vals
  have hAM : M1.nreg ALLOC = c₁.nreg ALLOC := v6 _ by_decide
    by_decide by_decide by_decide
    by_decide
  have hctxM : MCtx P W J.right N₂ ztbmp gMD2 gCD2 ztbz M1 := by
    refine hctx₁.transport ztez (fun a _ => by zuouq) (by rw [hAM])
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact v6 _ by_decide
        by_decide
        by_decide
        by_decide
        by_decide
  -- the raw array
  refine IRS.seq (slAlloc_irs hK hIM v5 (by rw [v4]; omega)) ?_ |>.mono
    (by rw [v4, hR2]) ztb
  rintro c₃ hI₃ hA3a hA3b ⟨a3, k3, r3, m3⟩
  refine IRS.seq (IRS.block [.constN slK 0] hI₃
    ⟨⟨iscr_sw by_decide by_decide, Nat.zero_le _⟩, trivial⟩) ?_
  rintro c₄ hI₄ hA4a hA4b hc4
  have v4' : ∀ r, r ≠ slK → c₄.nreg r = c₃.nreg r := fun r hr => by
    zumyv; zumxi; exact upd_other _ _ _ hr
  have k4 : c₄.nreg slK = 0 := by zumyv; rfl
  have m4 : ztmvj := by zumyv
  have r4 : ∀ r, r ≠ slK → r ≠ ALLOC → c₄.nreg r = M1.nreg r := fun r h1 h2 => by
    rw [v4' r h1, r3 r h1 h2]
  have hA4 : c₄.nreg ALLOC = M1.nreg ALLOC + 44 * ztjjk := by
    rw [v4' _ by_decide, a3, v4]
  have hS4 : SlpInv P J N₂ c M1 0 (fun _ _ _ => False) c₄ := by
    refine ⟨by rw [r4 _ by_decide by_decide, v1, hAM],
      by zupcr; omega, by rw [r4 _ by_decide by_decide,
      v2], fun i hi => ?_, fun _ _ _ h => h.elim, fun a _ => by rw [m4, m3],
      ⟨r4 _ by_decide by_decide,
        r4 _ by_decide by_decide⟩,
      fun r h0 h1 h2 => ?_⟩
    · rw [r4 _ by_decide by_decide, v2] at hi; omega
    · have hS2R : ∀ x, sw 3000 ≤ x → x < sw 6000 → S2R x := fun x a b => Or.inr by_omega
      rw [r4 r ztwnf h2,
        v6 r ztwnf
          ztwnf
          ztwnf
          ztwnf
          ztwnf]
      exact r1 r (fun h => h1 (by
        unfold MD2W gMD2 gCD2 gTP gTV at h
        rcases h with rfl | rfl | rfl | rfl <;> exact hS2R _ by_decide by_decide)) h2
  have hK4 := k4
  have hN4 : c₄.nreg slN = K₂ := by
    rw [v4' _ by_decide, r3 _ by_decide
      by_decide, v3]
  -- the shared and top codes
  refine IRS.seq (slCode_irs hctxM hOc hK hIM hI₄ hS4
    ztwzn by_norm_num by_norm_num by_omega by_omega
    by_omega) ?_
  rintro c₅ hI₅ hA5a hA5b ⟨hS5, k5, n5, -⟩
  refine IRS.seq (slCode_irs hctxM hOc hK hIM hI₅ hS5
    ztwzn by_norm_num by_norm_num by_omega by_omega
    by_omega) ?_
  rintro c₆ hI₆ hA6a hA6b ⟨hS6, k6, n6, -⟩
  refine IRS.seq (slCode_irs hctxM hOc hK hIM hI₆ hS6
    ztwzn by_norm_num by_norm_num by_omega by_omega
    by_omega) ?_
  rintro c₇ hI₇ hA7a hA7b ⟨hS7, k7, n7, -⟩
  refine IRS.seq (slCode_irs hctxM hOc hK hIM hI₇ hS7
    ztwzn by_norm_num by_norm_num by_omega by_omega
    by_omega) ?_
  rintro c₈ hI₈ hA8a hA8b ⟨hS8, k8, n8, -⟩
  have hS8' : SlpInv P J N₂ c M1 4 ztwef c₈ := by
    refine hS8.monoD ?_ le_rfl
    rintro kind k b ⟨hb, ⟨h0k, rfl⟩ | ⟨-, hk⟩⟩
    · rcases h0k with rfl | rfl <;> rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl <;>
        simp
    · omega
  -- the wall codes
  refine IRS.seq (slKLoop_irs hctxM hOc hK hIM hI₈ hS8'
    (by rw [k8, k7, k6, k5, hK4]) (by rw [n8, n7, n6, n5, hN4]) (by
      have h1 : ztdyh * N₂.nChords + 2 ≤ R8 := by
        rw [hR8]; exact Nat.le_add_right _ _
      omega)) ?_
  rintro c₉ hI₉ hA₉ hA₉' hS9
  -- the sort
  have hcnt9 : c₉.nreg gRC ≤ 4 * K₂ + 8 := by have := hS9.cnt; omega
  have hsc : κs * ztrog * (Nat.clog 2 ztrog + 1) ≤ R9 := by
    rw [hR9]
    exact Nat.mul_le_mul ztdfv
      (by have := Nat.clog_mono_right 2 (show c₉.nreg gRC + 1 ≤ 4 * K₂ + 8 + 1 by omega); omega)
  refine (hSrt sh Bs F X Ok P W c₀ c₉ J N₁ N₂ E hI₉ ztdp
    (by rw [hS9.rb]; have := hS9.room; omega) by_omega).mono hsc ?_
  · obtain ⟨hok, hpw, -⟩ := hS9.valid i hi
    rw [hS9.rb]
    exact ⟨hpw, hok.2.2.2.2.1⟩
  rintro c' ⟨O, hO1, hO2, hO3, hO4, hO5, hO6, hO7, hO8, hO9, hO10, hO11, hO12⟩
  rw [hS9.rb] at hO2 hO3 hO5 hO6
  have hval : ∀ i ∈ O, RawV P J N₂ c₉.nmem _ i := fun i hi => hS9.valid i (hO1 i hi)
  have hnd : O.Nodup := hO2.imp fun {a b} h hab => by
    subst hab; unfold KLt at h; rcases h with h | ⟨-, h⟩ <;> exact lt_irrefl _ h
  have hlen : O.length ≤ 4 * K₂ + 8 := by
    have h1 : O.toFinset ⊆ Finset.range _ := fun x hx =>
      Finset.mem_range.2 (hO1 x (List.mem_toFinset.1 hx))
    have h2 := Finset.card_le_card h1
    rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at h2
    omega
  have hget : ∀ i (hi : i < O.length) (f : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ),
      (O.map f).getD i ztip = f (O[i]'hi) := fun i hi f => by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
  have hMc : ∀ a, a < c.nreg ALLOC → M1.nmem a = c.nmem a := fun a ha => by
    rw [v7, m1 a ha]
  refine ⟨O.map _, O.map _, by simp [hO4], by_simp, hO5, hO6, ?_, ?_, ?_,
    by simpa using hlen, by_omega, by simpa using hO8, by_omega, by simpa using hO10,
    fun a ha => ?_, fun r h0 h1 h2 => ?_⟩
  · -- the stops
    refine stopsOK_of'
      E.hP E.hNF₂ (fun x hx => (hS9.valid x ztpzs).1) ?_
      (fun y hy => List.mem_range.2 (hO1 y hy)) hO2
      (fun x hx => by
        obtain ⟨j, hj, hk⟩ := hO3 x ztpzs
        exact ⟨j, hj, hk⟩)
    zuibp
    obtain ⟨kind, k, b, hst, hfree, rfl⟩ := stop_complete E.hP E.hNF₂ hsc
    obtain ⟨hk2, hb1, hk1, htop⟩ := hst
    zubsx
    · zucuj
      obtain ⟨i, hi, e1, e2, e3⟩ := hS9.compl 1 k b ⟨hb1, Or.inr by_omega⟩
        ⟨⟨hk2, hb1, hk1, htop⟩, hfree⟩ p t hA hL
      exact ⟨i, List.mem_range.2 hi, e1, e2, e3⟩
    · have hso : stOrig J zta N₂ kind 0 b = stOrig J zta N₂ kind k b := by
        simp [stOrig, h1]
      have hss : stopSet J zta N₂ kind 0 b = stopSet J zta N₂ kind k b := by
        simp [stopSet, h1]
      obtain ⟨i, hi, e1, e2, e3⟩ := hS9.compl kind 0 b
        ⟨hb1, by_omega⟩
        ⟨⟨hk2, hb1, by_omega, htop⟩, by zuoyc; omega⟩ p t
        (by rw [hss]; exact hA) hL
      exact ⟨i, List.mem_range.2 hi, e1, e2, by rw [e3, hss]⟩
  · -- the word facts
    zuz
    zufyl
    obtain ⟨hok, hpw, -⟩ := hval i hi
    obtain ⟨⟨hk2, hb1, hk1, -⟩, -⟩ := hok
    exact ⟨hpw, hk2, hb1, by_omega⟩
  · -- the auxiliary data
    zug
    simp only [List.length_map] at hi
    rw [hget i hi, hget i hi]
    exact (hval _ ztdyp).2.2
  · rw [hO11 a by_omega, hS9.memM a by_omega, hMc a ha]
  · rw [hO12 r h0 (fun h => h1 ?_) h2, hS9.regs r h0 h1 h2]
    unfold SoR at h; unfold S2R
    zuzp
    · omega
    · omega
    · zqbdc
    · zqbdc
