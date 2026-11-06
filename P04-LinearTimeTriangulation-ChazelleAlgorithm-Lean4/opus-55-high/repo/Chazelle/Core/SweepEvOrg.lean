module

public import Chazelle.MacT
public import Chazelle.Core.SweepEvFace
public import Chazelle.Core.SweepIoGather
public import Chazelle.Core.DownPhaseOracleCuR1
public import Chazelle.Core.RestoreTHoleChain
public import Chazelle.Core.RestoreFComplete2
public import Chazelle.Core.FuseAsmMain

namespace Chazelle.Core
namespace SweepEv
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam
open Chazelle.Chain (sidePt)
@[expose] public section
def oK : ℕ := sw 2200
def oS : ℕ := sw 2201
def oX : ℕ := sw 2202
def oH : ℕ := sw 2203
def oL : ℕ := sw 2204
def oR : ℕ := sw 2205
def oUp : ℕ := sw 2206
def oDn : ℕ := sw 2207
def oE : ℕ := sw 2210
def oC : ℕ := sw 2211
def oFE : ℕ := sw 2212
def oFC : ℕ := sw 2213
def oD : ℕ := sw 2214
def oCl : ℕ := sw 2215
def oNo : ℕ := sw 2216
def oT : ℕ := sw 2218
def oJ : ℕ := sw 2219
def oSym : ℕ := sw 2220
def oAbsA : ℕ := sw 2224

/-! ## The program -/

/-- Read the record of chord `oK` of the normal form at `sw 4`. -/
def orgLoad : List Instr :=
  [.addN oX ztbz K3, .loadN oX oX, .addN oX oX oK, .addN oX oX oK, .addN oX oX oK,
    .addN oX oX oK, .addN oX oX oK, .loadN oH oX, .addN oX oX K1, .loadN oL oX,
    .addN oX oX K1, .loadN oR oX, .addN oX oX K1, .loadN oUp oX, .addN oX oX K1,
    .loadN oDn oX, .addN oC oH K1, .copyN oFC oC]

/-- Select the end. -/
def orgPick : Stmt :=
  .ifLtN oS K1 (block [.copyN oE oL, .copyN oFE oR, .constN oD 1])
    (block [.copyN oE oR, .copyN oFE oL, .constN oD 0])

/-- **Read and normalise the end `oS` of chord `oK`.** -/
def orgHead : Stmt := .seq (block orgLoad) (.seq orgPick (normS zted oE oC oNo))

/-! ## The register effect of the blocks -/
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable (m f : ℕ → ℕ)
theorem orgLoad_val (hk1 : f K1 = 1) (hk3 : f K3 = 3) :
    regB m orgLoad f oH = m ztbaki ∧
    regB m orgLoad f oL = m (m ztwkt + 5 * f oK + 1) ∧
    regB m orgLoad f oR = m (m ztwkt + 5 * f oK + 2) ∧
    regB m orgLoad f oUp = m (m ztwkt + 5 * f oK + 3) ∧
    regB m orgLoad f oDn = m (m ztwkt + 5 * f oK + 4) ∧
    regB m orgLoad f oC = m ztbaki + 1 ∧
    regB m orgLoad f oFC = m ztbaki + 1 := by
  zubx
  zubtd
  simp only [orgLoad, regB, regI, upd, oX, oK, oH, oL, oR, oUp, oDn, oC, oFC, K1, K3, sw]
  grind
theorem orgLoad_other {q : ℕ} (h : q < sw 2202 ∨ sw 2213 < q) :
    regB m orgLoad f q = f q :=
  regB_other m orgLoad f (fun i hi => by
    simp only [orgLoad, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> zvmwd <;> intro he <;> subst he <;>
      simp [oX, oH, oL, oR, oUp, oDn, oC, oFC, sw] at h)
theorem orgLoad_ok (hk1 : f K1 = 1) (hk3 : f K3 = 3) (hb : f ztbz + 3 ≤ W)
    (hb2 : m ztwkt + 5 * f oK + 4 ≤ W) (hh : m ztbaki + 1 ≤ W) :
    okB W m orgLoad f := by
  zubx
  zubtd
  have s : ∀ j, 2202 ≤ j → j ≤ 2213 → IScr ztjfo := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  zufuk
  have hb2' : m ztcnb + 5 * f 242200 + 4 ≤ W := hb2
  have hh' : m (m ztcnb + f 242200 + f 242200 + f 242200 + f 242200 + f 242200) + 1 ≤ W := by
    have : m ztcnb + f 242200 + f 242200 + f 242200 + f 242200 + f 242200 =
      m ztcnb + 5 * f 242200 := by_ring
    zujls
  simp only [orgLoad, okB, okI, regI, upd, oX, oK, oH, oL, oR, oUp, oDn, oC, oFC, K1, K3, sw]
  grind
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace Sweep
open WalkEmbed
@[expose] public section

/-- The ends of a chord of a normal form of a chain model are strictly inside the box band. -/
theorem endPos_band {C : Chain} {Q : Polygon} {N : NF} (hN : IsNF ztc Q N) {k : ℕ}
    (hk : k < N.nChords) (s : ℕ) :
    |((chainModel C).pos Q (endPos N k s)).2| < C.radius ∧
      |((chainModel C).pos Q (farEnd N k s)).2| < C.radius := by
  obtain ⟨y, a, b, hab, heq, hl, hr, -⟩ := rec_ends hN hk
  have hmem : ztxcx := by
    zuno

  obtain ⟨y', a', b', hH, -, heq', -, -⟩ :=
    Merge.augChords_spec ztglw
  have hab' := hH.lt
  have hD := hH.open_mem ((a' + b') / 2) by_linarith by_linarith
  have hbox := C.dom_subset_box hD
  have hyy : ztsne := by
    have h1 : ztwsj ∈ Visibility.hseg y a b := ztbci
    rw [← heq, heq'] at h1
    exact h1.1
  have hy : ztsnv := by rw [hyy]; exact hbox.2
  unfold endPos farEnd
  grind
end
end Sweep
namespace SweepEv
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
theorem band_sw_not {r : ℕ} (h : 240000 ≤ r ∧ r < 250000) : bandOf r ∉ oracleBands :=
  not_oracle_sw h.1 h.2

/-- **The selection of the end.** -/
theorem orgPick_irs (hI : IInv W c₀ c) (hk1 : c.nreg K1 = 1) (hs : c.nreg oS ≤ 1) :
    IRS P W c₀ orgPick c 5 (fun c' => c'.nmem = c.nmem ∧
      c'.nreg oE = (if c.nreg oS = 0 then c.nreg oL else c.nreg oR) ∧
      c'.nreg oFE = (if c.nreg oS = 0 then c.nreg oR else c.nreg oL) ∧
      c'.nreg oD = ztlpz ∧
      ∀ q, q ≠ oE → q ≠ oFE → q ≠ oD → c'.nreg q = c.nreg q) := by
  have hW := hI.hw
  unfold orgPick
  by_cases h0 : c.nreg oS < c.nreg K1
  · have hs0 : c.nreg oS = 0 := by_omega
    refine (IRS.ifT h0 (IRS.block [.copyN oE oL, .copyN oFE oR, .constN oD 1] hI ?_)).mono
      by_simp ?_
    · zucuh

      exact ⟨iscr_sw by_norm_num by_norm_num, iscr_sw by_norm_num by_norm_num,
        ⟨iscr_sw by_norm_num by_norm_num, by have := hW.1 K1; omega⟩, trivial⟩
    · zuu
      refine zthnp
      · zucex
      · zucex
      · simp [regB, regI, upd, oD, sw, ite_eq_left hs0]
      · zugzo

  · have hs1 : c.nreg oS ≠ 0 := by_omega
    refine (IRS.ifF h0 (IRS.block [.copyN oE oR, .copyN oFE oL, .constN oD 0] hI ?_)).mono
      by_simp ?_
    · zucuh

      exact ⟨iscr_sw by_norm_num by_norm_num, iscr_sw by_norm_num by_norm_num,
        ⟨iscr_sw by_norm_num by_norm_num, Nat.zero_le _⟩, trivial⟩
    · zuu
      refine zthnp
      · zucey
      · zucey
      · simp [regB, regI, upd, oD, sw, ite_eq_right hs1]
      · zugzo
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **Reading the end of a chord.** -/
theorem orgHead_irs {J : Merge.Junction} {N₂ : NF} {E : ℕ} (hI : IInv W c₀ c) (hK₀ : Consts c₀)
    (hctx : ChainCtx P W c zted J.right) (hNF : IsNF ztj zta N₂)
    (hNW : NFWithin c.nmem ztwrb E N₂) (hE : E ≤ c.nreg ALLOC)
    (hk : c.nreg oK < N₂.nChords) (hs : c.nreg oS ≤ 1)
    (hroom : c.nreg ALLOC + 11100 ≤ W) :
    IRS P W c₀ orgHead c 11100 (fun c' =>
      c'.nreg oH = (N₂.chord ztghn).h ∧ c'.nreg oUp = (N₂.chord ztghn).up ∧
      c'.nreg oDn = (N₂.chord ztghn).dn ∧
      c'.nreg oD = ztlpz ∧
      c'.nreg oE = (endPos N₂ ztghn ztmgz).edge ∧
      c'.nreg oC = nhgt ztj zta (endPos N₂ ztghn ztmgz) ∧
      c'.nreg oFE = (farEnd N₂ ztghn ztmgz).edge ∧
      c'.nreg oFC = (farEnd N₂ ztghn ztmgz).hgt ∧
      (∀ r, bandOf r ∉ oracleBands → (r < sw 2202 ∨ sw 2217 < r) → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zuyr
  zuch
  set k := c.nreg oK with hkdef
  set s := c.nreg oS with hsdef
  zudns
  zuicm
  zucnq
  have hW := hI.hw.1 ALLOC
  have hb : c.nreg ztbz + 3 ≤ W := by_omega
  have hb2 : c.nmem ztwxz + 5 * k + 4 ≤ W := by_grind
  obtain ⟨r0, r1, r2, r3, r4⟩ := hch k hk
  zugmi
  zuc
  have hPn : ztfku := by have := hctx.2.1; unfold hostWords at this; omega
  have hh : c.nmem (c.nmem ztwxz + 5 * k) + 1 ≤ W := by
    omega
  -- the load block
  refine IRS.seq (K₂ := 11100 - orgLoad.length)
    (IRS.block orgLoad hI (orgLoad_ok c.nmem c.nreg k1 k3 hb hb2 hh)) ?_ |>.mono by_rfl
    ztb
  zufg
  obtain ⟨vH, vL, vR, vUp, vDn, vC, vFC⟩ := orgLoad_val c.nmem c.nreg k1 k3
  set c₁ : Config := { c with nreg := regB c.nmem orgLoad c.nreg } with hc₁
  have ko : ∀ q, ztlry → c₁.nreg q = c.nreg q :=
    fun q hq => orgLoad_other _ _ hq
  have c1S := ko oS by_decide
  have c1K1 := (ko K1 by_decide).trans k1
  -- the end position
  zuftg
  have hlp := hA.1.1
  have hrp := hA.2.1
  have hpl : ztmts :=
    ⟨hA.1.2.1, hA.1.2.2.1, by show (N₂.chord k).h + 1 ≤ P.n; omega⟩
  have hpr : ztmtt :=
    ⟨hA.2.2.1, hA.2.2.2.1, by show (N₂.chord k).h + 1 ≤ P.n; omega⟩
  obtain ⟨hbandE, -⟩ := endPos_band hNF hk s
  -- the selection
  have hc1 := ko K1 by_decide
  refine IRS.seq (K₂ := 11100 - orgLoad.length - 5)
    (orgPick_irs hI₁ by_omega by_omega) ?_ |>.mono
    by_rfl ztb
  rintro c₂ hI₂ hA₂ hA₂' ⟨hm₂, vE, vFE, vD, k₂⟩
  have hl : orgLoad.length = 18 := rfl
  rw [c1S] at vE vFE vD
  have q₂ : ∀ q, q ≠ oE → q ≠ oFE → q ≠ oD → ztlry → c₂.nreg q = c.nreg q :=
    by grind
  have hE₂ : c₂.nreg oE = (endPos N₂ k s).edge := by
    zuogo; unfold endPos
    split_ifs
    · exact vL.trans r1
    · exact vR.trans r2
  have hFE₂ : c₂.nreg oFE = (farEnd N₂ k s).edge := by
    rw [vFE]; unfold farEnd
    split_ifs
    · exact vR.trans r2
    · exact vL.trans r1
  have hC₂ : c₂.nreg oC = (N₂.chord k).h + 1 := by
    rw [k₂ oC by_decide by_decide by_decide]
    grind
  have hFC₂ : c₂.nreg oFC = (N₂.chord k).h + 1 := by
    rw [k₂ oFC by_decide by_decide by_decide]
    grind
  have hpos : (ztkkm : WPos) = endPos N₂ k s := by
    rw [hE₂, hC₂]; unfold endPos; split_ifs <;> rfl
  have hctx₂ : ChainCtx P W c₂ zted J.right :=
    hctx.transport (by rw [q₂ _ by_decide by_decide
      by_decide by_decide])
      by_grind by_omega
  have hpp : ProperPos ztj zta P.n ztkkm := by
    zvnbl; unfold endPos; split_ifs
    · omega
    omega
  have he : c₂.nreg oE < (chainModel J.right).W.n := by
    rw [hE₂]; unfold endPos; split_ifs
    · tauto
    tauto
  refine (normS_irs hI₂ ztvtl hctx₂
    by_decide by_decide he hpp
    by_grind by_omega).mono
    by_omega ?_
  rintro c₃ ⟨vE₃, vC₃, k₃, hA₃, hm₃⟩
  refine ⟨?_, ?_, ?_, ?_, by_omega, by_grind, ?_, ?_, ?_, by_omega, ?_⟩
  · rw [k₃ oH ztbur by_decide
      by_decide by_decide by_decide]
    rw [k₂ oH by_decide by_decide by_decide]
    grind
  · rw [k₃ oUp ztbur by_decide
      by_decide by_decide by_decide]
    rw [k₂ oUp by_decide by_decide by_decide]
    grind
  · rw [k₃ oDn ztbur by_decide
      by_decide by_decide by_decide]
    rw [k₂ oDn by_decide by_decide by_decide]
    grind
  · rw [k₃ oD ztbur by_decide
      by_decide by_decide by_decide, vD]
  · rw [k₃ oFE ztbur by_decide
      by_decide by_decide by_decide, hFE₂]
  · rw [k₃ oFC ztbur by_decide
      by_decide by_decide by_decide, hFC₂]
    unfold farEnd; split_ifs <;> rfl
  · intro r hr hr2 hra
    rw [k₃ r hr (by unfold oC sw at *; omega) ztmew
      ztmew hra]
    rw [k₂ r (by unfold oE sw at *; omega) (by unfold oFE sw at *; omega) (by unfold oD sw at *; omega)]
    exact ko r zteo
  · zuge
    rw [hm₃ a by_omega, hm₂]
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sidePt)
@[expose] public section
def c2m : ℕ := sw 640
def cm : ℕ := sw 641
def cTop : ℕ := sw 642
def cS : ℕ := sw 643
def c2m6 : ℕ := sw 644
def cT1 : ℕ := sw 645
/-- The bit of the height test (an oracle register). -/
def oHb : ℕ := 50900

/-- The constants of the classification. -/
structure OrgK (P : Polygon) (J : Merge.Junction) (c : Config) : Prop where
  m2 : c.nreg c2m = 2 * J.right.m
  m1 : c.nreg cm = J.right.m
  top : c.nreg cTop = J.right.topIdx
  s : c.nreg cS = J.right.sideS J.right.sideBeta
  m26 : c.nreg c2m6 = 2 * J.right.m + 6
  t1 : ∃ s : SymPt, SymPtIn c cT1 s ∧ s.Lt P.n ∧ s.eval zta = J.left.top
theorem OrgK.fix {P : Polygon} {J : Merge.Junction} {W : ℕ} {c₀ c : Config} (h : OrgK P J c₀)
    (hI : IInv W c₀ c) : OrgK P J c := by
  have k : ∀ i, 640 ≤ i → i ≤ 647 → c.nreg ztcdy = c₀.nreg ztcdy := fun i h1 h2 =>
    hI.hin _ ztze
  obtain ⟨a, b, d, e, f, s, hs, hl, he⟩ := h
  refine ⟨(k 640 le_rfl by_norm_num).trans a, (k 641 by_norm_num by_norm_num).trans b,
    (k 642 by_norm_num by_norm_num).trans d, (k 643 by_norm_num by_norm_num).trans e,
    (k 644 by_norm_num by_norm_num).trans f, s, ?_, hl, he⟩
  exact symPtIn_transport hs (k 645 by_norm_num by_norm_num)
    (k 646 by_norm_num by_norm_num) (k 647 by_norm_num by_norm_num)

/-! ## Exact executions as run steps -/
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- An execution changing only scratch registers (listed) is a run step. -/
theorem irs_of_out {s : Stmt} {c' : Config} {k K : ℕ} {L : List ℕ} (hI : IInv W c₀ c)
    (ex : Exec P W s c c' k) (hk : k ≤ K) (ho : SweepIo.Out c c' L) (hL : ∀ r ∈ L, IScr r) :
    IRS P W c₀ s c K (fun c'' => c'' = c') := by
  obtain ⟨hr, hrr, hm, hrm, hout⟩ := ho
  have hA : ztble := hr ALLOC (fun h => alloc_not_scr (hL _ h))
  exact IRS.ofExec hI ex hk (fun r hr' _ => hr r (fun h => hr' (hL r h))) hrr
    ztdnr hrm hout ztchd by_omega rfl

/-! ## The vertex index -/
def oU : ℕ := sw 2232

/-- `oJ := sideE m ((S + (e - 6)) mod 2m)`, without words above `2m`. -/
def orgIdx : Stmt :=
  .seq (block [.subN oT oE K6, .subN oU c2m cS])
    (.seq ztfax
      (.seq (condSub oT oT c2m)
        (.ifLtN cm oT (.instr (.subN oJ c2m oT)) (.instr (.copyN oJ oT)))))
theorem orgIdx_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK : Consts c) (hO : OrgK P J c)
    (h6 : 6 ≤ c.nreg oE) (he : c.nreg oE ≤ 2 * J.right.m + 6) (hWm : 2 * J.right.m + 7 ≤ W) :
    IRS P W c₀ orgIdx c 12 (fun c' => c'.nmem = c.nmem ∧
      c'.nreg oJ = J.right.sideIdx J.right.sideBeta (c.nreg oE - 6) ∧
      ∀ r, r ≠ oT → r ≠ oU → r ≠ oJ → c'.nreg r = c.nreg r) := by
  obtain ⟨-, -, k6, -, -, -, -⟩ := hK
  obtain ⟨m2, m1, -, hS, -, -⟩ := hO
  have hSle := J.right.sideS_lt J.right.sideBeta
  zueri
  set i := c.nreg oE - 6 with hi
  set S := J.right.sideS J.right.sideBeta with hSdef
  set m := J.right.m with hmdef
  -- the block
  have e6 : c.nreg 240612 = 6 := k6
  have eS : c.nreg 240643 = S := hS
  have e2 : c.nreg 240640 = 2 * m := m2
  have eE : c.nreg 242210 = c.nreg oE := rfl
  have hb := IRS.block (P := P) [.subN oT oE K6, .subN oU c2m cS] hI (by
    simp only [okB, okI, oT, oU, sw]
    tauto)
  refine (IRS.seq (K₂ := 10) hb ?_).mono by_simp ztb
  zuer
  set c₁ : Config := { c with nreg := regB c.nmem [.subN oT oE K6, .subN oU c2m cS] c.nreg }
    with hc₁
  have v1 : c₁.nreg oT = i := by
    show regB c.nmem [.subN oT oE K6, .subN oU c2m cS] c.nreg oT = i
    zudj
    rw [upd_other _ _ _ by_decide, upd_same, k6]
  have v2 : c₁.nreg oU = 2 * m - S := by
    show regB c.nmem [.subN oT oE K6, .subN oU c2m cS] c.nreg oU = 2 * m - S
    zudj
    rw [upd_same, upd_other _ _ _ by_decide,
      upd_other _ _ _ by_decide, m2, hS]
  have o1 : ∀ r, r ≠ oT → r ≠ oU → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    simp only [hc₁, regB, regI, upd]; simp_all
  have c1S : c₁.nreg cS = S := (o1 cS by_decide by_decide).trans hS
  -- the sum modulo `2m`, at most `2m`
  have hstep : IRS P W c₀ ztfax c₁ 3
      (fun c' => c'.nmem = c₁.nmem ∧ c'.nreg oT ≤ 2 * m ∧
        (c'.nreg oT) % ztdk = ztbat % ztdk ∧ ∀ r, r ≠ oT → c'.nreg r = c₁.nreg r) := by
    by_cases hlt : c₁.nreg oT < c₁.nreg oU
    · zuimx
      refine (IRS.ifT by_omega (IRS.reg (P := P) hI₁
        ztbua (Exec.addN hI₁.hw oT oT cS
          by_omega))).mono by_omega ?_
      zuu
      simp only [upd_same, v1, c1S]
      refine ⟨by_simp, by_omega, by_grind, fun r hr => by_simp_all⟩
    · zuimx
      refine (IRS.ifF by_omega (IRS.reg (P := P) hI₁
        ztbua (Exec.subN hI₁.hw oT oT oU))).mono by_omega ?_
      zuu
      simp only [upd_same, v1, v2]
      refine ⟨by_simp, by_omega, ?_, fun r hr => by_simp_all⟩
      rw [show S + i = (i - ztbru) + 2 * m by omega, Nat.add_mod_right]
  refine IRS.seq (K₂ := 7) hstep ?_ |>.mono by_omega ztb
  rintro c₂ hI₂ - - ⟨hm₂, hle₂, hmod₂, k₂⟩
  have c2m2 : c₂.nreg c2m = 2 * m := by
    rw [k₂ c2m by_decide, o1 c2m by_decide
      by_decide, m2]
  obtain ⟨c₃, k₃, hk₃, e₃, v₃, o₃⟩ := condSub_exec (P := P) hI₂.hw oT oT c2m
  refine IRS.seq (K₂ := 3) (irs_of_out hI₂ e₃ (show k₃ ≤ 3 by omega) o₃
    (fun r hr => by simp at hr; subst hr; exact iscr_sw by_decide by_decide)) ?_ |>.mono
    by_omega ztb
  zudsw
  subst hc4
  have v3 : c₄.nreg oT = ztbat % ztdk := by
    rw [v₃, c2m2, ← hmod₂]
    zus
    · zukp
    · rw [show c₂.nreg oT = 2 * m by omega, Nat.mod_self]; omega
  have c3m : c₄.nreg c2m = 2 * m := by rw [o₃.1 c2m by_decide, c2m2]
  have c3m1 : c₄.nreg cm = m := by
    rw [o₃.1 cm by_decide, k₂ cm by_decide,
      o1 cm by_decide by_decide, m1]
  have hsIdx : J.right.sideIdx J.right.sideBeta i = Chazelle.Chain.sideE m (c₄.nreg oT) := by
    rw [Chazelle.Chain.sideIdx_eq, v3]
  have hmodlt : c₄.nreg oT < 2 * m := by zunrr; exact Nat.mod_lt _ by_omega
  by_cases hlt : c₄.nreg cm < c₄.nreg oT
  · refine (IRS.ifT hlt (IRS.reg (P := P) hI₄ ztbua
      (Exec.subN hI₄.hw oJ c2m oT))).mono by_omega ?_
    zuu
    refine ztgoa
    · zufb
      rw [hsIdx, c3m]
      unfold Chazelle.Chain.sideE
      grind
    · zubi
      zucqf
  · refine (IRS.ifF hlt (IRS.reg (P := P) hI₄ ztbua
      (Exec.copyN hI₄.hw oJ oT))).mono by_omega ?_
    zuu
    refine ztgoa
    · zufb
      rw [hsIdx]
      unfold Chazelle.Chain.sideE
      grind
    · zubi
      zucqf
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sidePt)
@[expose] public section
def orgHt : Stmt :=
  .seq (callSym zted oE oC oSym)
    (.seq (kbit cT1 oSym cT1 1 oHb) (.ifLtN oHb K1 (.instr (.constN oCl 1)) ztigd))
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
set_option maxRecDepth 20000 in
theorem orgHt_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK : Consts c) (hO : OrgK P J c)
    (hctx : ChainCtx P W c zted J.right) (h6 : 6 ≤ c.nreg oE)
    (he : c.nreg oE < 2 * J.right.m + 6)
    (hpp : ProperPos ztj zta P.n ztbcg)
    (hnorm : c.nreg oC = 0 ↔ (chainModel J.right).param zta ztbcg = 0)
    (hroom : c.nreg ALLOC + 31300 ≤ W) :
    IRS P W c₀ orgHt c 31300 (fun c' =>
      (∃ s : SymPt, SymPtIn c' oSym s ∧ s.Lt P.n ∧
        s.eval zta = (chainModel J.right).pos zta ztbcg) ∧
      (c'.nreg oCl = 1 ↔
        ((chainModel J.right).pos zta ztbcg).2 ≤ J.left.top.2) ∧
      c'.nreg oCl ≤ 1 ∧
      (∀ r, bandOf r ∉ oracleBands → ztlse → r ≠ oCl → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  obtain ⟨-, k1, -, -, -, -, -⟩ := hK
  zumbs
  have hPW : ztmd := by have := hctx.2.1; unfold hostWords at this; omega
  zufpd
  refine IRS.seq (K₂ := 294)
    (callSym_irs hI hctx by_decide
      by_decide h6 he hpp hnorm by_omega) ?_ |>.mono by_norm_num (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨⟨s, hs, hsl, hse⟩, k₁, hA₁'', hm₁⟩
  have hk1₁ : ztcpf := by
    rw [k₁ K1 ztbur by_decide
      by_decide, k1]
  obtain ⟨t, ht, htl, hte⟩ := hO.t1
  have ht₁ := symPtIn_transport ht
    (k₁ cT1 ztbur by_decide
      by_decide)
    (k₁ _ ztbur by_decide
      by_decide)
    (k₁ _ ztbur by_decide
      by_decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hb₂, hbit₂⟩ := kbit_exec (op := 1) (dst := oHb) hG hPW c₁ hI₁.hw
    by_decide by_decide by_decide
    by_decide by_norm_num htl hsl htl ht₁ hs ht₁
  have hOr : ∀ r, Bkb oHb r = true → bandOf r ∈ oracleBands := by
    zuz
    simp only [Bkb, WalkKey.Bk, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, oHb] at hr
    zubuj
    · exact band1_oracle by_omega by_omega
    · subst h; decide
  refine IRS.seq (K₂ := 6) (IRS.ofFrameB hI₁ e₂ hk₂ f₂ hOr rfl) ?_ |>.mono
    by_norm_num ztb
  zubup
  have hfr := f₂.1
  have hk1₂ : ztgat := by
    rw [hfr K1 by_rfl, hk1₁]
  have hs₂ := symPtIn_transport hs
    (hfr oSym by_rfl)
    zttnn
    zttnn
  have hbit : c₂.nreg oHb = 1 ↔ J.left.top.2 < a.2 := by
    rw [hbit₂]; zvnhd; simp_all
  have hfinal : ∀ v, v ≤ 1 → (v = 1 ↔ a.2 ≤ J.left.top.2) →
      IRS P W c₀ ztoup c₂ 3 (fun c' =>
        (∃ s : SymPt, SymPtIn c' oSym s ∧ s.Lt P.n ∧ s.eval zta = a) ∧
        (c'.nreg oCl = 1 ↔ a.2 ≤ J.left.top.2) ∧ c'.nreg oCl ≤ 1 ∧
        (∀ r, bandOf r ∉ oracleBands → ztlse → r ≠ oCl → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
    intro v hv hvi
    refine (IRS.reg hI₃ ztbua
      (Exec.constN hI₃.hw oCl v by_omega)).mono
      by_norm_num ?_
    zuu
    zufb
    refine ⟨⟨s, symPtIn_transport hs₂ by_rfl
      by_rfl
      by_rfl, hsl, hse⟩, hvi, hv,
      fun r hr h1 h2 hra => ?_, ?_, fun x hx => ?_⟩
    · rw [upd_other _ _ _ h2, hfr r (by
          grind)]
      simp_all
    · have h3 := hfr ALLOC (by
        rfl)
      rw [upd_other _ _ _ by_decide, h3]; omega
    · rw [f₂.2.2.1, hm₁ x hx]
  by_cases hb : c₂.nreg oHb < c₂.nreg K1
  · refine (IRS.ifT hb (hfinal 1 le_rfl ?_)).mono by_norm_num by_grind
    grind
  · refine (IRS.ifF hb (hfinal 0 by_norm_num ?_)).mono by_norm_num by_grind
    grind
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sidePt)
@[expose] public section

/-- A tour vertex: its index decides `v` and the top of `C₂`. -/
def orgVtx : Stmt :=
  .seq orgIdx (.ifLtN oJ K1 ztigd
    (.ifLtN oJ cTop orgHt (.ifLtN cTop oJ orgHt ztigd)))

/-- **The class of the end** `(oE, oC)`. -/
def orgCls : Stmt :=
  .ifLtN oE K6 ztouo
    (.ifLtN oE c2m6 (.ifLtN oC K1 orgVtx orgHt)
      (.ifLtN K0 oC ztouo orgVtx))

/-- The facts computed by `orgCls` for the point `a` of the end. -/
def ClsOut (P : Polygon) (J : Merge.Junction) (a : Point) (c c' : Config) : Prop :=
  c'.nreg oCl ≤ 2 ∧ (c'.nreg oCl = 2 ↔ a ∉ J.right.set) ∧
    (c'.nreg oCl = 1 ↔ a ∈ J.right.set ∧ a ≠ J.shared ∧ a ≠ J.right.top ∧ a.2 ≤ J.left.top.2) ∧
    (c'.nreg oCl = 1 → ∃ s : SymPt, SymPtIn c' oSym s ∧ s.Lt P.n ∧ s.eval zta = a) ∧
    (∀ r, bandOf r ∉ oracleBands → (r < oCl ∨ oU < r) → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ ztbgf
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable {J : Merge.Junction}
/-- A constant class. -/
theorem cls_const {a : Point} (hI : IInv W c₀ c) (hW : 2 ≤ W)
    {v : ℕ} (hv : v ≤ 2) (h2 : v = 2 ↔ a ∉ J.right.set)
    (h1 : v = 1 ↔ a ∈ J.right.set ∧ a ≠ J.shared ∧ a ≠ J.right.top ∧ a.2 ≤ J.left.top.2)
    (hn1 : v ≠ 1) {K : ℕ} (hK : 1 ≤ K) :
    IRS P W c₀ ztoup c K ztgdk := by
  refine (IRS.reg hI ztbua
    (Exec.constN hI.hw oCl v by_omega)).mono hK ?_
  zuu
  refine ⟨by_simp_all, by_simp_all, by_simp_all, fun h => absurd by_simp_all hn1,
    fun r _ hr hra => ?_, by_rfl,
    fun x _ => rfl⟩
  zubi
  rw [upd_other _ _ _ ztfqa]

/-- An `orgHt` leaf: the end is on `C₂`, neither `v` nor the top of `C₂`. -/
theorem cls_ht (hI : IInv W c₀ c) (hK : Consts c) (hO : OrgK P J c)
    (hctx : ChainCtx P W c zted J.right) (h6 : 6 ≤ c.nreg oE)
    (he : c.nreg oE < 2 * J.right.m + 6)
    (hpp : ProperPos ztj zta P.n ztbcg)
    (hnorm : c.nreg oC = 0 ↔ (chainModel J.right).param zta ztbcg = 0)
    {a : Point} (ha : (chainModel J.right).pos zta ztbcg = a)
    (hmem : a ∈ J.right.set) (hv : a ≠ J.shared) (ht : a ≠ J.right.top)
    (hroom : c.nreg ALLOC + 31300 ≤ W) {K : ℕ} (hK31 : 31300 ≤ K) :
    IRS P W c₀ orgHt c K ztgdk := by
  refine (orgHt_irs hI hK hO hctx h6 he hpp hnorm hroom).mono hK31 ?_
  rintro c' ⟨hsym, hcl, hle, hfr, hA, hm⟩
  rw [ha] at hsym hcl
  refine ⟨by_omega, by_grind, ?_, by_simp_all,
    fun r hr hr2 hra => hfr r hr (by unfold oSym oCl oU sw at *; omega)
      ztfqa hra, hA, hm⟩
  simp_all
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sidePt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
set_option maxHeartbeats 2000000 in
/-- **The class of the end.** -/
theorem orgCls_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK₀ : Consts c₀) (hO₀ : OrgK P J c₀)
    (hctx : ChainCtx P W c zted J.right) (he : c.nreg oE < 2 * J.right.m + 7)
    (hpp : ProperPos ztj zta P.n ztbcg)
    (hnorm : c.nreg oC = 0 ↔ (chainModel J.right).param zta ztbcg = 0)
    (hroom : c.nreg ALLOC + 31410 ≤ W) :
    IRS P W c₀ orgCls c 31410
      (ClsOut P J ((chainModel J.right).pos zta ztbcg) c) := by
  zuyr
  have hO := hO₀.fix hI
  zumce
  have hWm := hctx.2.2.2.2.2
  zudpx
  zubof
  zumfl
  have m2 := hO.m2
  have mtop := hO.top
  have m26 := hO.m26
  set e := c.nreg oE with hedef
  zufpd
  zuuy
  have hmemiff := pos_mem_set_iff J.right hP (x := ztbcg)
    by_simp_all hpp.1 hpp.2.1 hnorm
  simp only at hmemiff
  have hvzero := (Merge.Junction.right_vertex_zero J).symm
  have htop : J.right.top = J.right.vertex J.right.topIdx := rfl
  zudoc
  -- the vertex case
  have hvtx : c.nreg oC = 0 → 6 ≤ e → e ≤ 2 * J.right.m + 6 →
      IRS P W c₀ orgVtx c 31398 ztgdk := by
    intro h0 h6 h26
    have hav : a = J.right.vertex (J.right.sideIdx J.right.sideBeta ztbcs) :=
      pos_vertex J.right h6 h26 h0
    zuhxz
    refine IRS.seq (K₂ := 31386) (orgIdx_irs hI hK hO h6 h26 hWm) ?_ |>.mono
      by_norm_num ztb
    rintro c₁ hI₁ hA₁ hA₁' ⟨hm₁, vJ, k₁⟩
    have hle := J.right.sideIdx_le J.right.sideBeta ztbcs
    set idx := J.right.sideIdx J.right.sideBeta ztbcs with hidx
    have kk : ∀ r, (r < oT ∨ oU < r) → oJ ≠ r → c₁.nreg r = c.nreg r := fun r hr hj =>
      k₁ r ztljx ztljx ztvbg
    have k1₁ : ztcpf := by rw [kk K1 by_decide by_decide, k1]
    have kt₁ : ztuqp := by
      rw [kk cTop by_decide by_decide, mtop]
    have kE₁ := kk oE by_decide by_decide
    have kC₁ := kk oC by_decide
      by_decide
    have lift : ∀ c', ClsOut P J a c₁ c' → ClsOut P J a c c' := by
      rintro c' ⟨h1, h2, h3, h4, h5, h6', h7⟩
      refine ⟨h1, h2, h3, h4, fun r hr hr2 hra => ?_, by_omega, fun x hx => ?_⟩
      · rw [h5 r hr hr2 hra]
        exact kk r (by unfold oCl oT oU sw at *; omega) (by unfold oCl oJ oU sw at *; omega)
      grind
    have hv_iff : a = J.shared ↔ idx = 0 := by
      rw [hav, hvzero]
      exact ⟨(J.right.sideVertex_inj hP hle ztbg), by_grind⟩
    have ht_iff : a = J.right.top ↔ idx = J.right.topIdx := by
      rw [hav, htop]
      exact ⟨(J.right.sideVertex_inj hP hle J.right.topIdx_le), by_grind⟩
    have h2m : idx ≠ J.right.topIdx → e < 2 * J.right.m + 6 := by
      intro hne
      zukr
      zufqo
      rw [hidx, show e - 6 = 2 * J.right.m by omega, Chain.sideIdx_two_m]
    have hht : idx ≠ J.right.topIdx → a ≠ J.shared → IRS P W c₀ orgHt c₁ 31300 ztgdk := by
      intro hne hav0
      have hctx₁ : ztrfl :=
        hctx.transport (kk _ by_decide by_decide)
          by_grind hA₁
      refine (cls_ht hI₁ (hK₀.fix hI₁) (hO₀.fix hI₁) hctx₁ by_omega
          by_omega by_grind by_grind
          by_grind hamem hav0 by_grind by_omega le_rfl).mono le_rfl
          by_omega
    by_cases hj0 : c₁.nreg oJ < c₁.nreg K1
    · rw [vJ, k1₁] at hj0
      refine IRS.ifT (K := 31384) by_omega ?_ |>.mono by_norm_num
        by_omega
      refine cls_const hI₁ hW2 by_norm_num by_grind
        by_grind by_norm_num
        by_norm_num
    · have hj0' : ¬ idx < 1 := by_omega
      have hav0 : a ≠ J.shared := by_grind
      refine IRS.ifF (K := 31384) hj0 ?_ |>.mono by_norm_num ztb
      by_cases hlt : c₁.nreg oJ < c₁.nreg cTop
      · rw [vJ, kt₁] at hlt
        exact (IRS.ifT by_omega zttnp).mono by_norm_num
          by_grind
      · have hlt' : ¬ idx < J.right.topIdx := by_omega
        refine IRS.ifF (K := 31382) hlt ?_ |>.mono by_norm_num ztb
        by_cases hgt : c₁.nreg cTop < c₁.nreg oJ
        · rw [vJ, kt₁] at hgt
          exact (IRS.ifT by_omega zttnp).mono by_norm_num
            by_grind
        · have hgt' : ¬ J.right.topIdx < idx := by_omega
          have heq : idx = J.right.topIdx := by_omega
          refine (IRS.ifF hgt (cls_const hI₁ hW2 by_norm_num
            by_grind
            by_grind by_norm_num
            le_rfl)).mono by_norm_num lift
  by_cases h6 : c.nreg oE < c.nreg K6
  · rw [k6] at h6
    zuhzj
    exact (IRS.ifT by_omega (cls_const hI hW2 (K := 1) by_norm_num
      by_simp_all by_simp_all
      by_norm_num by_norm_num)).mono by_norm_num (fun _ h => h)
  · have h6' : ¬ e < 6 := by_omega
    refine IRS.ifF (K := 31408) h6 ?_ |>.mono by_norm_num ztb
    by_cases h26 : c.nreg oE < c.nreg c2m6
    · have h26' : e < 2 * J.right.m + 6 := by_omega
      refine IRS.ifT (K := 31406) h26 ?_ |>.mono by_norm_num ztb
      by_cases h0 : c.nreg oC < c.nreg K1
      · rw [k1] at h0
        exact (IRS.ifT by_omega (hvtx by_omega by_omega by_omega)).mono
          by_norm_num by_simp_all
      · have h0' : c.nreg oC ≠ 0 := by_omega
        have hpar : 0 < (chainModel J.right).param _ ztbcg :=
          lt_of_le_of_ne hpp.1 by_grind
        have hne := pos_ne_vertex J.right hP
          by_simp_all by_grind hpar hpp.2.1
        zuhxz
        exact (IRS.ifF h0 (cls_ht hI hK hO hctx by_omega h26' hpp hnorm rfl hamem
          by_simp_all by_simp_all by_omega le_rfl)).mono
          by_norm_num by_simp_all
    · have h26' : e = 2 * J.right.m + 6 := by_omega
      refine IRS.ifF (K := 31406) h26 ?_ |>.mono by_norm_num ztb
      by_cases hc : c.nreg K0 < c.nreg oC
      · zvnib at hc
        zuhzj
        exact (IRS.ifT by_omega (cls_const hI hW2 (K := 1) by_norm_num
          by_simp_all by_simp_all
          by_norm_num by_norm_num)).mono by_norm_num (fun _ h => h)
      · have hc' : c.nreg oC = 0 := by_omega
        exact (IRS.ifF hc (hvtx hc' by_omega by_omega)).mono by_norm_num by_simp_all
end
end SweepEv
end Chazelle.Core
section
set_option hygiene false
local macro "zqzy" : tactic => `(tactic| have hn : ztdh := C.sideWalk_n _)
local macro "zqzz" : tactic => `(tactic| have hm1 : ztwh := by zvmwl)
local macro "zqbaa" : tactic => `(tactic| simp only [List.mem_cons, List.not_mem_nil, or_false] at hi)
local macro "zqbab" : tactic => `(tactic| (rw [q1 _ zteqn, q1 _ zteqn]))
set_option hygiene true

/-!
# The sweep RAM (WP-D), answers: the local hit, part 2 (arcs, holes, shot)

The facts the shot wrapper needs: the gathered arcs are pieces of weight at most `γ`
(`nArc_piece`), the holes at a position on a vertical box side (`boxHole`), the shot block.
-/
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open OracleQ (sj sk ek succP predP)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Heights of walk positions -/

/-- **A position with a positive parameter off the horizontal box edges** lies strictly inside the
height band of the box. -/
theorem pos_abs_lt (C : Chain) (Q : Polygon) {n : ℕ} {x : WPos}
    (he : x.edge < (chainModel C).W.n) (hp : ProperPos ztc Q n x)
    (h0 : 0 < (chainModel C).param Q x) (hb : x.edge ≠ 0 ∧ x.edge ≠ 2 ∧ x.edge ≠ 4) :
    |((chainModel C).pos Q x).2| < C.radius := by
  zqzy
  have hpos : (chainModel C).pos Q x = sidePt ztcs x.edge
      _ := rfl
  zudbq
  zubo
  have ht1 := hp.2.1
  zumcm
  have hT' : -C.radius < C.top.2 := by
    have := lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set C.top_mem_set).2 C.coordBound_lt_radius
    grind
  obtain ⟨-, b1, -, b3, -, b5, b6⟩ := C.sidePt_box C.sideBeta t
  rcases (by omega : x.edge = 1 ∨ x.edge = 3 ∨ x.edge = 5 ∨ ztbxz ∨
    x.edge = 2 * C.m + 6) with h | h | h | ⟨h1, h2⟩ | h
  · rw [hpos, h, b1]; simp only; zvncj; constructor <;> nlinarith
  · rw [hpos, h, b3]; simp only; zvncj; constructor <;> nlinarith
  · zuobz; simp only; zvncj; constructor <;> nlinarith
  · have hmem : (chainModel C).pos Q x ∈ C.set := by
      zueyg
      exact C.sideWalk_tour_pt_mem C.sideBeta by_omega by_grind hp.1 ht1
    zuhuj
  · rw [hpos, h, b6]; simp only; zvncj; constructor <;> nlinarith

/-! ## The gathered arcs are pieces -/
variable {C : Chain} {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {N : NF} {E : ℕ}
/-- **The normalised arc of a valid normal form** is a piece of the shot of weight at most `γ`. -/
theorem nArc_piece (hP : C.P.Simple) {N : NF} (hNF : IsNF ztc zta N)
    {γ : ℕ} (hsg : (chainModel C).Semigranular ztwjq γ) {a : ℕ}
    (ha : a < N.arcs.length) :
    ShotList.PieceOK ztc zta P.n (nArc ztc zta N a) ∧
      (chainModel C).arcWt ((chainModel C).key zta (nArc ztc zta N a).1)
        ((chainModel C).key zta (nArc ztc zta N a).2) ≤ γ := by
  obtain ⟨⟨hps, hse, -⟩, ⟨hpe, hee, -⟩⟩ := arc_end_facts hP hNF ha
  zugls
  obtain ⟨-, -, -, reg, hRC, -, hArcs, -, -, -, -⟩ := hNF'
  obtain ⟨hreg, harc⟩ := hArcs.1 a ha
  have hU := hRC.1 _ hreg
  have endok : ∀ u : WPos, ProperPos ztc zta P.n u →
      u.edge < (chainModel C).W.n →
      ShotList.NormPos ztc zta P.n ztzkd ∧
        (Restore.normOf ztc zta u).edge < (chainModel C).W.n ∧
        ((Restore.normOf ztc zta u).hgt = 0 ∨
          (chainModel C).InnerPt ((chainModel C).pos zta
            ztzkd)) := by
    intro u hu hue
    obtain ⟨hN, he', hpos', -, hcase⟩ := Restore.normOf_facts hu
    refine ztrct
    zuklb
    · omega
    · right
      set v := Restore.normOf _ _ u
      have hve : v.edge < (chainModel C).W.n := by_omega
      have hb : v.edge ≠ 0 ∧ v.edge ≠ 2 ∧ v.edge ≠ 4 := by
        refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩ <;>
        · have := Model.param_horizontal (Q := Qof P) (x := v)
            (ShootCut.box_horizontal (C := C) by_omega)
          linarith
      exact Restore.innerPt_chain_walk C _ hve hN.1.1 hN.1.2.1.le
        (pos_abs_lt C _ hve hN.1 h hb)
  obtain ⟨n1, n2, n3⟩ := endok _ hps hse
  obtain ⟨m1, m2, m3⟩ := endok _ hpe hee
  refine ⟨⟨n1, m1, n2, m2, n3, m3⟩, ?_⟩
  zujqr
  rw [(Restore.normOf_facts hps).2.2.2.1, (Restore.normOf_facts hpe).2.2.2.1]
  exact (arcWt_le_weight _ harc).trans zttok

/-! ## The hole at a position on a vertical side of the box -/

/-- **The edge of a position inside a vertical side of the box** is a hole covering it, near it. -/
theorem boxHole_ok (C : Chain) (hP : C.P.Simple) (Q : Polygon) {e h : ℕ} (he : e = 1 ∨ e = 3)
    (h0 : 0 < (chainModel C).param Q ztcq) (h1 : (chainModel C).param Q ztcq < 1) :
    Restore.Cover ztc Q [ztbaam] ztwyw ∧
      Restore.Near ztc Q [ztbaam] ztwyw := by
  zqzy
  zubt
  have hen : e + 1 < (chainModel C).W.n := by_omega
  have kv : ∀ q : ℕ, (chainModel C).key Q ztkmm = q := by_simp_all
  have k0 := kv e
  have k1 : (chainModel C).key Q ztkku = ((e + 1 : ℕ) : ℝ) := by_simp_all
  refine ⟨fun p t hp ht0 ht1 hz => ?_, fun g hg p τ hp hτ0 hτ1 hc => ?_⟩
  · obtain ⟨rfl, rfl⟩ := SweepPrim.wall_unique C hP he h0 h1 hp ht0 ht1 hz
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    zubi
    zukwr
    zufdq
    simp_all
  · zvnns at hg
    subst hg
    simp only at hc
    rw [k0, k1] at hc
    obtain ⟨t₂, h20, h21, h2⟩ := Restore.edge_keys (chainModel C).W (e := e) by_omega hp hτ0 hτ1
      (by rw [Nat.mod_eq_of_lt hen]; exact hc)
    exact ⟨e, by_omega, ⟨_, h0.le, h1.le, rfl⟩, t₂, h20, h21, h2⟩

/-! ## The shot as a run step -/

/-- The shot block of the answers. -/
def RS : ℕ := 241300
theorem regsOK_RS : ShotList.RegsOK RS := by
  trivial

/-- **The shot** as a run step: the post `ShotPost`, writing only the oracle bands and the shot
block `RS … RS + 299`. -/
theorem shot_irs
 (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) (hI : IInv W c₀ c) (pre : ShotList.ShotPre X Ok RS P W c)
    (hroom : c.nreg ALLOC + ShotList.shotCost ztzbu ztbagq ≤ W) :
    IRS P W c₀ ztjmw c (ShotList.shotCost ztzbu ztbagq)
      (fun c' => ShotList.ShotPost RS P c c' ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → ¬ ztbmg →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  obtain ⟨c', k, ex, hk, hpost, hfr⟩ := ShotList.shotList_execR hsh hBs hXl regsOK_RS c hI.hw pre hroom
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfr
  have hio : ∀ r, bandOf r ∉ ioBands → bandOf r ∉ oracleBands ∧ ¬ ztbmg :=
    fun r hr => ⟨fun h => hr ztwbd, fun h => hr (by
      rw [band_sw ztnvl ztnvl]; decide)⟩
  refine ⟨c', k, ex, hk, ⟨ex.wb_right, fun q hq => ?_, le_trans hI.hA f6,
    fun a ha => (f3 a ztftc).trans ztduw,
    fun a ha => (f4 a ztftc).trans zttmj⟩,
    ⟨by_grind, by_grind,
      f5, f6, f7⟩, hpost, by_omega, f6, f3⟩
  zujpt
  rw [f1 q ztbet ztu
    zteqn]
  exact hI.hin q hq

/-! ## Transport of the context -/

/-- **The local-hit context survives** a step keeping its registers, the memory below the
allocator, and not lowering the allocator. -/
theorem LCtx.transport {c c' : Config} (h : LCtx P W C N E c)
    (hr : ∀ r, r = lMD ∨ r = lCD ∨ r = lNF ∨ r = TBR ∨ r = TLR → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    LCtx P W C N E c' := by
  obtain ⟨hG, hWh, hctx, hcd, hmd, hmwf, hm0, hP, hNW, hE, hNF, htab, hbig, hTB, hTW⟩ := h
  have rMD := hr lMD ztp
  have rCD := hr lCD by_omega
  have rNF := hr lNF by_omega
  have rTB := hr TBR by_omega
  have rTL := hr TLR by_omega
  zucou

  · omega
  zuebm
  refine ⟨hG, hWh, hctx.transport rCD hm hA, by_omega, ?_, by_simp_all,
    by simp_all, hP, by zupcu; exact hNW.transport by_grind,
    by omega, hNF, fun j hj => ?_, by_simp_all, by_omega,
    by omega⟩
  · zupct; exact Or.inl by_grind
  grind

/-! ## The gather of the three regions -/

/-- The gather of the list at `lL` (three regions). -/
def lhGather : Stmt := .seq (block [.copyN gNF lNF, .copyN gL lL, .copyN gC K3]) (gather lCD)

/-- The registers of the gather call. -/
def GCall (r : ℕ) : Prop := sw 1000 ≤ r ∧ r ≤ sw 1021
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The gather of the three regions** of the local hit. -/
theorem lhGather_irs {rs : List ℕ} (hI : IInv W c₀ c)
    (hK : Consts c₀) (hL : LCtx P W C N E c) (hrs3 : rs.length = 3)
    (hrs : ∀ r ∈ rs, r < N.nRegions)
    (hlist : ∀ i, i < 3 → c.nmem (c.nreg lL + i) = rs.getD i 0)
    (hLA : c.nreg lL + 3 ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + ztpug ≤ W) :
    IRS P W c₀ lhGather c ztpug (fun c' =>
      c'.nreg gBase = c.nreg ALLOC ∧ c'.nreg gK = (regArcs N rs).length ∧
      c'.nreg ALLOC = c.nreg ALLOC + 4 * (regArcs N rs).length ∧
      (∀ k, k < (regArcs N rs).length → ShotList.arcAt c'.nmem ztm k =
        nArc ztc zta N ztdxx) ∧
      zth ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ GCall r → r ≠ ALLOC → c'.nreg r = c.nreg r)) := by
  zuus
  have hok : okB W c.nmem [.copyN gNF lNF, .copyN gL lL, .copyN gC K3] c.nreg :=
    ⟨iscr_sw by_decide by_decide,
      iscr_sw by_decide by_decide,
      iscr_sw by_decide by_decide, trivial⟩
  refine IRS.seq (K₂ := gatherK N rs) zteei ?_ |>.mono by_simp ztb
  zugn
  have v1 : c₁.nreg gNF = c.nreg lNF ∧ c₁.nreg gL = c.nreg lL ∧ c₁.nreg gC = 3 := by
    zummx
    zusk
    · rfl
    · rfl
    · show regB c.nmem [.copyN gNF lNF, .copyN gL lL, .copyN gC K3] c.nreg gC = _
      simp only [regB, regI, upd, gNF, gL, gC, lNF, lL, K3, sw]; simp
      exact hK₀.2.2.2.2.2.2
  have k1 : ∀ r, r ≠ gNF → r ≠ gL → r ≠ gC → c₁.nreg r = c.nreg r := by
    intro r h1 h2 h3; zvmwl
    exact regB_other _ _ _ (fun i hi => by
      zqbaa
      rcases hi with rfl | rfl | rfl <;> zvmwd <;> intro h <;> subst h <;> simp_all)
  zqzz
  have hA1 : ztdc := k1 _ by_decide
    by_decide by_decide
  have hL1 := hL.transport (fun r hr => k1 r
    (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> unfold gNF <;> zumyy)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> unfold gL <;> zumyy)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> unfold gC <;> zumyy))
    by_simp_all hA1.ge
  refine (gather_irs hI₁ hK hL1.hctx ⟨by_decide, by_decide,
    fun h => by unfold GSet lCD sw at h; omega⟩ hL1.hP hL1.hNF hL1.hNW
    (by rw [v1.1, k1 lNF by_decide by_decide
      by_decide]) hL1.hE hrs
    by_simp_all
    by_omega by_omega
    by_omega).mono le_rfl ?_
  rintro c' ⟨⟨w1, w2, w3, w4, w5, w6, -, -, -⟩, -⟩
  zvnhf at w1 w3 w4 w5
  refine ⟨w1, w2, w3, w4, by_simp_all, fun r hr hg hra => ?_⟩
  rw [w6 r hr (fun h => hg (by unfold GSet sw at h; unfold GCall sw; omega)) hra]
  exact k1 r ztxws
    ztxws ztxws

/-! ## The holes -/
def lO : ℕ := sw 1120

/-- The hole of a position on a vertical box side: its edge. -/
def boxL : List Instr := [.constN 241309 1, .copyN 241310 lE, .addN 241311 lE K1]

/-- The holes at `x`: the edge on a vertical box side, else `chainH`. -/
def lhHoles : Stmt :=
  .ifLtN lE K6 (block boxL)
    (.seq (block [.copyN 243005 lE, .copyN 243006 lH]) (.seq (normS lCD 243005 243006 lO)
      (.seq (block [.copyN 243020 lCD, .constN 243022 0, .constN 243023 1]) chainH)))

/-- The registers the holes write (outside the oracle bands). -/
def HSet (r : ℕ) : Prop := (241309 ≤ r ∧ r ≤ 241315) ∨ (243000 ≤ r ∧ r < 243200) ∨ r = lO ∨
  r = lO + 1
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The holes** at the position `x = (lE, lH)`. -/
theorem lhHoles_irs (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W c lCD C)
    (he : c.nreg lE < (chainModel C).W.n)
    (hpp : ProperPos ztc zta P.n zthj)
    (hy : |((chainModel C).pos zta ⟨c.nreg lE, c.nreg lH⟩).2| < C.radius)
    (hloc : (c.nreg lE = 1 ∨ c.nreg lE = 3) ∨
      (6 ≤ c.nreg lE ∧ (chainModel C).pos zta zthj ∈ C.set))
    (hroom : c.nreg ALLOC + 11200 ≤ W) :
    IRS P W c₀ lhHoles c 11200 (fun c' =>
      HoleOut ztc zta c' ztwlk ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ HSet r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nreg ALLOC = c.nreg ALLOC ∧ c'.nmem = c.nmem) := by
  zuus
  zudet
  zuioj
  zqzy
  zubb
  zumej
  unfold lhHoles
  by_cases hbox : c.nreg lE < c.nreg K6
  · zuduv
    have hb : c.nreg lE = 1 ∨ c.nreg lE = 3 := by
      omega
    have hpar0 : 0 < (chainModel C).param _ x := ShootCut.box_param_pos' C _ hbox hpp.1 hy
    have hok : okB W c.nmem boxL c.nreg := by
      simp only [boxL, okB, okI, regI, upd, lE, K1, sw]
      simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_false]
      zujxc
      have eE : c.nreg 241103 = c.nreg lE := rfl
      refine ⟨ztgpa, iscr_sw by_norm_num by_norm_num,
        ⟨iscr_sw by_norm_num by_norm_num, by_omega⟩, trivial⟩
    refine (IRS.ifT by_omega zteei).mono by_decide ?_
    zuu
    zujxc
    have v9 : regB c.nmem boxL c.nreg 241309 = 1 := by
      rfl
    have v10 : regB c.nmem boxL c.nreg 241310 = c.nreg lE := by
      rfl
    have v11 : regB c.nmem boxL c.nreg 241311 = c.nreg lE + 1 := by
      simp only [boxL, regB, regI, upd, lE, K1, sw]; simp_all
    have vo : ∀ r, r ≠ 241309 → r ≠ 241310 → r ≠ 241311 → regB c.nmem boxL c.nreg r = c.nreg r :=
      fun r h1 h2 h3 => regB_other _ _ _ (fun i hi => by
        simp only [boxL, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> zvmwd <;> omega)
    set c' : Config := { c with nreg := regB c.nmem boxL c.nreg } with hc'
    have hl : ShotList.holeList c' 241300 = [(⟨c.nreg lE, 0⟩, ⟨c.nreg lE + 1, 0⟩)] := by
      rw [holeList_one _ v9]
      simp only [ShotList.holeAt]
      simp_all
    obtain ⟨hcov, hnear⟩ := boxHole_ok C hctx.2.2.2.2.1 _ hb hpar0 hpp.2.1
    have c9 : c'.nreg 241309 = 1 := v9
    refine ⟨⟨by_omega, fun j hj => ?_, by_simp_all, by_simp_all⟩,
      fun r hr hh hra => ?_, ?_, rfl⟩
    · rw [c9] at hj
      zudgu
      zumo
      grind
    · exact vo r ztxwt ztxwt
        ztxwt
    rfl
  · -- a point of the chain: `chainH`
    zuduv
    have h6 : 6 ≤ c.nreg lE := by_omega
    have hxC : (chainModel C).pos zta x ∈ C.set := by
      grind
    refine (IRS.ifF by_omega ?_).mono (K := 11198) by_omega ztb
    -- copy the position
    have hok1 : okB W c.nmem [.copyN 243005 lE, .copyN 243006 lH] c.nreg :=
      ⟨iscr_sw by_norm_num by_norm_num, iscr_sw by_norm_num by_norm_num, trivial⟩
    refine IRS.seq ztrjn ?_ |>.mono (K := 2 + (11015 + (3 + 100))) by_omega
      ztb
    zugn
    have v15 : c₁.nreg 243005 = c.nreg lE := by
      zubuz
    have v16 : c₁.nreg 243006 = c.nreg lH := by
      zubuz
    have k1o : ∀ r, r ≠ 243005 → r ≠ 243006 → c₁.nreg r = c.nreg r := by
      intro r h1 h2; zvmwl
      exact regB_other _ _ _ (fun i hi => by
        zqbaa
        rcases hi with rfl | rfl <;> zvmwd <;> omega)
    zqzz
    have hA1 : ztdc := k1o _ by_decide by_decide
    have hctx1 := hctx.transport (k1o _ by_decide
      by_decide) by_simp_all hA1.ge
    -- normalise it
    have hpp1 : ProperPos ztc zta P.n ⟨c₁.nreg 243005, c₁.nreg 243006⟩ := by
      simp_all
    refine IRS.seq (normS_exact (normS_irs hI₁
      ztqph hctx1 ⟨by_decide, by_decide, by_norm_num,
        by norm_num, by_norm_num, by_norm_num⟩
      ⟨by_decide, by_decide, by_decide,
        by decide, by_decide, by_decide, by_norm_num⟩
      by_omega hpp1 by_simp_all
      by_omega) ⟨by_norm_num, by_decide⟩) ?_
    rintro c₂ hI₂ - - ⟨⟨n25, n26, k2, -, -⟩, hA2, hm2⟩
    obtain ⟨hNP, hne, hnpos, -, hncase⟩ := Restore.normOf_facts hpp
    have hu2 : (⟨c₂.nreg 243005, c₂.nreg 243006⟩ : WPos) = Restore.normOf ztc zta x := by
      rw [n25, n26, v15, v16]; unfold nhgt
      rcases hn' : Restore.normOf _ _ x with ⟨e', h'⟩
      grind
    have hh6 : c₂.nreg 243006 = (Restore.normOf ztc zta x).hgt := by
      grind
    have k2o := k2
    have hctx2 := hctx1.transport
      (k2o _ ztmr
        by_decide by_decide by_decide
        by_decide) by_grind hA2.ge
    -- the descriptor and the constants
    have hok3 : okB W c₂.nmem [.copyN 243020 lCD, .constN 243022 0, .constN 243023 1] c₂.nreg :=
      ⟨iscr_sw by_norm_num by_norm_num, ⟨iscr_sw by_norm_num by_norm_num, Nat.zero_le _⟩,
        ⟨iscr_sw by_norm_num by_norm_num, by_omega⟩, trivial⟩
    refine IRS.seq ztrjp ?_
    zugbb
    have v20 : c₃.nreg 243020 = c₂.nreg lCD := by
      zudub
    have v22 : ztusa := by
      zudub
    have v23 : ztusb := by
      zudub
    have k3o : ∀ r, r ≠ 243020 → r ≠ 243022 → r ≠ 243023 → c₃.nreg r = c₂.nreg r := by
      intro r h1 h2 h3; zvnar
      exact regB_other _ _ _ (fun i hi => by
        zqbaa
        rcases hi with rfl | rfl | rfl <;> zvmwd <;> omega)
    zuyu
    have hA3 : ztbox := k3o _ by_decide by_decide
      by_decide
    have h35 : c₃.nreg 243005 = c₂.nreg 243005 := by_grind
    have h36 : c₃.nreg 243006 = c₂.nreg 243006 := by_grind
    obtain ⟨-, -, hwf, ⟨H, hCD, -⟩, hP, hWm⟩ := hctx2
    -- the holes
    obtain ⟨c', k, ex, hk, hout, hOut⟩ := chainH_exec (P := P) hI₃.hw (H := H)
      by_grind (by rw [v20, hA3]; exact hwf.1) hP hWm v22 v23
      (by rw [h35, h36, hu2]; exact hNP.1) by_omega
      by_grind by_grind
    have hHL : ∀ r, r ∈ holeL → HSet r := by
      zuz
      zubes
      unfold HSet; omega
    refine IRS.ofExec hI₃ ex by_omega (fun r hr hra => hOut.1 r (fun h => hr (by
      have := hHL r h; unfold HSet lO sw at this
      rcases this with h | h | h | h <;> exact iscr_sw by_omega by_omega))) hOut.2.1
      (fun a _ => by rw [hOut.2.2.1]) hOut.2.2.2.1 hOut.2.2.2.2
      (by zunba)
      (by zunba;
          omega) ⟨?_, fun r hr hh hra => ?_, ?_, ?_⟩
    · grind
    · rw [hOut.1 r by_grind, k3o r ztbmu
        ztbmu ztbmu,
        k2o r hr ztbmu ztzfb
          ztzfb hra,
        k1o r ztbmu ztbmu]
    · rw [hOut.1 ALLOC (fun h => by have := hHL _ h; unfold HSet ALLOC lO sw at this; omega), hA3, hA2,
        hA1]
    · rw [hOut.2.2.1, hm3, hm2, hm1]

/-! ## The shot and its hit -/

/-- The hit of a shot at a set off the domain containing the exit point is the exit point. -/
theorem firstHit_exit (C : Chain) {A : Set Point} {z : Point} {σ t : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hzt : z.2 ≤ C.top.2) (hf : Merge.FreeAt C z σ) (hA : A ⊆ C.domᶜ) (hF : FirstHit A z σ t)
    (hT : rayPt z σ ztbtm ∈ A) : t = C.hitParam z σ := by
  obtain ⟨hT0, -, hdom⟩ := Merge.hit_of_freeAt C hzt hσ hf
  obtain ⟨ht0, htA, hbefore⟩ := hF
  grind

/-- The shot block preparation. -/
def shPrepL : List Instr :=
  [.copyN 241300 lMD, .copyN 241301 gBase, .copyN 241302 gK, .constN 241303 2, .copyN 241304 lE,
    .copyN 241305 lH, .copyN 241306 lD, .copyN 241307 ztbcb, .copyN 241308 ztcwl]

/-- Offer the hit of the shot. -/
def lhOffer : Stmt := .ifLtN K0 241320 (offerF accA lCD 241321 241322 lT lD lN lO) .skip

/-- The shot of the local hit and the offer of its hit. -/
def lhShotOffer (sh : Stmt) : Stmt :=
  .seq (block shPrepL) (.seq ztjmw lhOffer)
theorem shPrepL_val (m f : ℕ → ℕ) :
    regB m shPrepL f 241300 = f lMD ∧ regB m shPrepL f 241301 = f gBase ∧
    regB m shPrepL f 241302 = f gK ∧ regB m shPrepL f 241303 = 2 ∧
    regB m shPrepL f 241304 = f lE ∧ regB m shPrepL f 241305 = f lH ∧
    regB m shPrepL f 241306 = f lD ∧ regB m shPrepL f 241307 = f ztbcb ∧
    regB m shPrepL f 241308 = f ztcwl ∧
    (∀ q, ztoey → regB m shPrepL f q = f q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => regB_other _ _ _ (fun i hi => by
    simp only [shPrepL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> zvmwd <;>
      omega)⟩ <;>
  · rfl

/-- The cost of the shot and its offer. -/
def shotOfferK (Fg K : ℕ) : ℕ := 9 + (ShotList.shotCost Fg K + (offerFK + 2))
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **The shot of the local hit** and the offer of its hit (filtered). -/
theorem lhShotOffer_irs
 (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {C : Chain} {N : NF} {E : ℕ} {rs : List ℕ} {Mod : ℕ → Chain} {R₀ : ℝ}
    {L : Set ℝ} (hI : IInv W c₀ c) (hK : Consts c₀) (hL : LCtx P W C N E c)
    (hX : X.holds P c₀.nmem ztxj ztdq)
    (hcap : c₀.nreg ztbcb ≤ X.cap P c₀.nmem ztxj)
    (hOk : Ok P ztc)
    (hsg : (chainModel C).Semigranular ztwjq ztq)
    (he : c.nreg lE < (chainModel C).W.n)
    (hpp : ProperPos ztc zta P.n zthj)
    (hy : |((chainModel C).pos zta ⟨c.nreg lE, c.nreg lH⟩).2| < C.radius)
    (hrs : ∀ a ∈ regArcs N rs, a < N.arcs.length)
    (hgK : c.nreg gK = (regArcs N rs).length)
    (hAB : c.nreg gBase + 4 * (regArcs N rs).length ≤ c.nreg ALLOC)
    (harcs : ∀ k, k < (regArcs N rs).length → ShotList.arcAt c.nmem ztqit k =
      nArc ztc zta N ztdxx)
    (hho : HoleOut ztc zta c ztwlk)
    (hacc : AccOK P accA Mod R₀ ztwlk
      ztmk L c)
    (htag : c.nreg lT ≤ 2) (hMod : Mod ztjsj = C) (hR : C.radius = R₀)
    (hn : c.nreg lN = 2 * C.m + 7)
    (hroom : c.nreg ALLOC + shotOfferK ztwiu (regArcs N rs).length ≤ W) :
    IRS P W c₀ ztvyg c (shotOfferK ztwiu (regArcs N rs).length)
      (fun c' => ∃ L', AccOK P accA Mod R₀ ztwlk
          ztmk L' c' ∧
        (L' = L ∨ ∃ τ, L' = insert τ L ∧ 0 < τ ∧
          OnCB C (rayPt ztwlk ztmk τ)) ∧
        (Merge.FreeAt C ztwlk ztmk →
          ((chainModel C).pos zta zthj).2 ≤ C.top.2 →
          rayPt ztwlk ztmk
              (C.hitParam ztwlk ztmk) ∈
            ShotList.loSet ztc zta c.nmem ztqit (regArcs N rs).length
              zttdb →
          C.hitParam ztwlk ztmk ∈ L') ∧
        (∀ r, bandOf r ∉ oracleBands → ¬ ztbmg → ztbni →
          r ≠ lO → r ≠ lO + 1 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zuus
  zuioj
  set z := (chainModel C).pos zta x with hz
  zufam
  set K := (regArcs N rs).length with hKd
  zusw
  have hWh := hL.hWh
  zufgg
  -- 1. prepare the shot block
  have hok : okB W c.nmem shPrepL c.nreg := by
    simp only [shPrepL, okB, okI]
    exact ⟨iscr_sw by_norm_num by_norm_num, iscr_sw by_norm_num by_norm_num,
      iscr_sw by_norm_num by_norm_num, ⟨iscr_sw by_norm_num by_norm_num, hW2⟩,
      iscr_sw by_norm_num by_norm_num, iscr_sw by_norm_num by_norm_num,
      iscr_sw by_norm_num by_norm_num, iscr_sw by_norm_num by_norm_num,
      iscr_sw by_norm_num by_norm_num, trivial⟩
  refine IRS.seq
    (IRS.block shPrepL hI hok) ?_ |>.mono by_rfl ztb
  zugn
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, po⟩ := shPrepL_val c.nmem c.nreg
  zqzz
  have q1 : ∀ q, ztoey → c₁.nreg q = c.nreg q := by_simp_all
  zuhwh
  have c0 : c₁.nreg RS = c.nreg lMD := by zvmwl; exact p0
  have c1' : c₁.nreg ztnoq = c.nreg gBase := by zvmwl; exact p1
  zufez
  have c7 : ztylo := by
    zury
  have c8 : ztylp := by
    zurz
  have hhl : ShotList.holeList c₁ RS = ShotList.holeList c RS := by
    unfold ShotList.holeList ShotList.holeAt
    zuooh
    zucr
    funext j
    zqbab
  have hori : OriginIn c₁ (RS + 3) ztuwc := by
    zusk
    · zvmwl; exact p3
    · zvmwl; exact p4
    · zvmwl; exact p5
  -- 2. the precondition of the shot
  have hL1 := hL.transport (fun r hr => q1 r (by
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> zumyy))
    by_simp_all hA1.ge
  zuiyh
  have hX1 : ztyll := by
    zuexb

  have hcap1 : ztxtf := by
    zubeh
  have hmd := hL1.hmd
  have hm0 := hL1.hm0
  have hmwf := hL1.hmwf
  have hreg := hL1.hctx.hostReg
  obtain ⟨-, -, hwfC, ⟨H, hCD, -⟩, hP, hWm⟩ := hL1.hctx
  have hcd1 := hL1.hcd
  obtain ⟨ho3, ho2, hcov, hnear⟩ := hho
  have h9 : c₁.nreg ztnot = c.nreg 241309 := q1 _ by_decide
  have hRS1 : c₁.nreg RS + 1 = c₁.nreg lCD := by rw [hcd1, c0, q1 lMD by_decide]
  have pre : ztiys := by
    refine ⟨hL.hG, hWh, hX1, hcap1, by_grind,
      by grind,
      by omega, by_omega, H, C, by_grind,
      by grind, hOk, hWm, fun j hj => ?_, fun j hj => ?_, .walk x, hori,
      ⟨he, hpp.2.2⟩, Or.inr ⟨Restore.innerPt_chain_walk C _ he hpp.1 hpp.2.1.le hy,
        fun x' hx' => by_grind⟩, hy, ?_⟩
    · zudfn

      have hmem := getD_mem_of_lt hj
      exact nArc_piece hP hL.hNF hsg by_grind
    · rw [h9] at hj
      zqbab
      exact ho2 j hj
    · rw [hhl, c1', c2', hm1]
      refine Restore.avoid_of_cover hcov ztjvu _ _ _
      unfold ShotList.holeList at hg
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
      zukpq
      have hj' : j < c.nreg 241309 := by
        have e9 : c.nreg (241300 + 9) = c.nreg 241309 := rfl
        omega
      exact ⟨rfl, (ho2 j hj').1⟩
  -- 3. the shot
  refine IRS.seq (shot_irs hsh hBs hXl hI₁ pre (by zvnja; unfold shotOfferK at hroom; omega)) ?_
    |>.mono (by zuooz) (fun _ h => h)
  zubse
  have hmdC : ztzov := by
    grind
  obtain ⟨hfl, A, hlo, hhi, hyes, hno⟩ := hpost ztc ztuwc hmdC hori
  have hσ6 : dirOf (c₁.nreg ztnor) = σ := by
    zungf; congr 1; zvmwl; exact p6
  rw [hσ6] at hyes hno
  have hev : Origin.eval _ _ (Origin.walk x) = z := rfl
  zujiv
  zutr

  have hAoff : A ⊆ C.domᶜ := by
    zucdk
    have := hhi hw
    zuwe

    zuisu
  -- registers after the shot
  have keep2 :=
    fun r h1 h2 h3 => k2 r ztsg ztu h3
  have keepc :=
    fun r h1 h2 h3 => (keep2 r h1 h2 by_omega).trans ztkdb
  have t2 : c₂.nreg lT = c.nreg lT := keepc _ by_decide by_decide
    by_decide
  have d2 : ztshj := keepc _ by_decide by_decide
    by_decide
  have n2 : c₂.nreg lN = c.nreg lN := keepc _ by_decide by_decide
    by_decide
  have cd2 : c₂.nreg lCD = c.nreg lCD := keepc _ by_decide by_decide
    by_decide
  have a2 : ztyab := fun j hj =>
    keepc _ zthk zthk ztnvn
  zuljj
  zuftj
  have hm2' : ztux := fun a ha => by
    zucjp
  have hctx2 : ChainCtx P W c₂ lCD C := by
    have := hL.hctx
    exact this.transport cd2 hm2' hA2'
  zudzv
  -- the completeness of the shot
  have complete : Merge.FreeAt C z σ → z.2 ≤ C.top.2 →
      rayPt z σ ztbtm ∈
        ShotList.loSet ztc zta c.nmem ztqit K zttdb →
      c₂.nreg 241320 = 1 ∧ ∀ t, FirstHit A z σ t → t = C.hitParam z σ := by
    intro hf hzt hlo'
    zuixb

    zuct
    zucss

  unfold lhOffer
  zukca
  zuhta
  · zugex
    zujye
    zublb
    have hroom2 : c₂.nreg ALLOC + offerFK ≤ W := by
      zvnja at hAb; unfold shotOfferK at hroom; omega
    refine (IRS.ifT by_omega (offerF_irs hI₂ hK hL.hG
      ztdha
      ⟨by_decide, by_decide⟩
      ⟨by_decide, by_decide, by_norm_num, by_norm_num, by_norm_num,
        by norm_num, by_decide, by_decide, by_decide,
        by decide, by_decide, by_decide,
        by decide, by_decide⟩
      ⟨by_norm_num, by_decide, by_decide, by_decide,
        by decide, by_decide, by_decide,
        by decide, by_decide, by_decide,
        by decide, by_decide, by_decide,
        by decide, by_decide, by_decide,
        by decide⟩
      ⟨by_decide, by_decide, by_decide,
        by decide, by_decide, by_decide⟩
      ztntg by_omega (by zuopc; omega)
      (by zuopc; exact hR) (by rw [n2, hn, t2, hMod]) ztdmd
      ztdmd ztjqh (by rw [hR] at hy; exact hy)
      hroom2)).mono by_omega ?_
    rintro c' ⟨⟨L', hacc', hL', hcomp⟩, k3, hA3, hm3⟩
    simp only [d2, t2, hMod] at hacc' hL' hcomp
    refine ⟨L', hacc', ?_, fun hf hzt hlo' => ?_, fun r hr hrs hra hro hro1 hrA => ?_,
      hA2'.trans hA3, fun a ha => by zuopa; exact hm2' a ha⟩
    · rcases hL' with h | ⟨h, hg⟩
      · zueou
      · exact Or.inr ⟨t, h, hFH.1, hg⟩
    · obtain ⟨-, ht⟩ := complete hf hzt hlo'
      rw [hcomp hzt, ← ht t hFH]
      simp
    · rw [k3 r hr hra (fun h => hrs ztli) hro hro1 hrA,
        k2 r hr hrA hrs]
      zulzn
  · refine (IRS.ifF hflag (IRS.skip (K := offerFK) hI₂ ⟨L, hacc2, Or.inl rfl, fun hf hzt hlo' => ?_,
      fun r hr hrs hra hro hro1 hrA => ?_, hA2', hm2'⟩)).mono by_omega (fun _ h => h)
    · zugex
      exact absurd (complete hf hzt hlo').1 by_omega
    · zuobv
      zulzn
end
end SweepIo
end Chazelle.Core
end
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt)
@[expose] public section
def MD₁ : ℕ := sw 650
def CD₁ : ℕ := sw 651

/-- The gathered arcs of the window (base, count). -/
def wGB : ℕ := sw 2420
def wGK : ℕ := sw 2421
def eF : ℕ := sw 2240
def eA : ℕ := sw 2243
def eRD : ℕ := sw 2246
def eNo : ℕ := sw 2247

/-! ## The frame of the stage-3 components -/

/-- **The frame of a component**: registers outside the oracle bands and the set `X` (and the
allocator) are unchanged, the allocator grows, the memory below it is kept. -/
def EFr (X : ℕ → Prop) (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ X r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth
theorem EFr.refl (X : ℕ → Prop) (c : Config) : EFr X c c :=
  ⟨fun _ _ _ _ => rfl, le_rfl, fun _ _ => rfl⟩
theorem EFr.trans {X : ℕ → Prop} {c₁ c₂ c₃ : Config} (h₁ : EFr X c₁ c₂) (h₂ : EFr X c₂ c₃) :
    EFr X c₁ c₃ :=
  ⟨fun r a b d => (h₂.1 r a b d).trans ztjyh, h₁.2.1.trans h₂.2.1,
    fun a ha => (h₂.2.2 a ztkan).trans ztdux⟩
theorem EFr.mono {X Y : ℕ → Prop} {c c' : Config} (h : EFr X c c') (hXY : ∀ r, X r → Y r) :
    EFr Y c c' :=
  ⟨fun r a b d => h.1 r a (fun hx => b (hXY r hx)) d, h.2.1, h.2.2⟩

/-! ## The program -/

/-- The shot block preparation (and the reversed direction code). -/
def evPrepL : List Instr :=
  [.copyN 241300 MD₁, .copyN 241301 wGB, .copyN 241302 wGK, .copyN 241303 oSym,
    .copyN 241304 zttur, .copyN 241305 zttus, .copyN 241306 oD, .copyN 241307 ztbcb,
    .copyN 241308 ztcwl, .constN 241309 0, .subN eRD K1 oD]

/-- The arrival and its normalisation. -/
def evArr : Stmt :=
  .seq (callArr CD₁ 241321 241322 eRD eA) (.ifLtN K0 eA (normS CD₁ ztle zthq eNo) .skip)

/-- **The shot of a candidate.** -/
def evShot (sh : Stmt) : Stmt :=
  .seq (block evPrepL) (.seq ztjmw (.seq (block [.copyN eF 241320])
    (.ifLtN K0 eF evArr .skip)))

/-- The registers written by `evShot` (besides the oracle bands and the allocator). -/
def ShW (r : ℕ) : Prop := ztbmg ∨ (eF ≤ r ∧ r ≤ eNo + 1)
theorem evPrepL_val (m f : ℕ → ℕ) :
    regB m evPrepL f 241300 = f MD₁ ∧ regB m evPrepL f 241301 = f wGB ∧
    regB m evPrepL f 241302 = f wGK ∧ regB m evPrepL f 241303 = f oSym ∧
    regB m evPrepL f 241304 = f zttur ∧ regB m evPrepL f 241305 = f zttus ∧
    regB m evPrepL f 241306 = f oD ∧ regB m evPrepL f 241307 = f ztbcb ∧
    regB m evPrepL f 241308 = f ztcwl ∧ regB m evPrepL f 241309 = 0 ∧
    regB m evPrepL f eRD = f K1 - f oD ∧
    (∀ q, zteus → q ≠ eRD → regB m evPrepL f q = f q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq hq' => regB_other _ _ _ (fun i hi => by
    simp only [evPrepL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      zvmwd <;> first | omega)⟩ <;>
  · rfl

/-! ## The contract -/

/-- The cost of `evShot`. -/
def evShotK (Fg K : ℕ) : ℕ := ShotList.shotCost Fg K + 50000

/-- **The outputs of the shot** from `a` in the direction `σ` at the arcs `(m, B, K)` of the model
of `C₁`: the hit flag, complete for genuine hits on the arcs; for a hit at `τ`, the arrival flag
and the normalised arrival position of `rayPt a σ τ`. -/
def ShotOut (P : Polygon) (J : Merge.Junction) (m : ℕ → ℕ) (B K : ℕ) (a : Point) (σ : ℝ)
    (c' : Config) : Prop :=
  c'.nreg eF ≤ 1 ∧
    (∀ τ₀, Genuine J.left a σ τ₀ →
      rayPt a σ τ₀ ∈ ShotList.loSet ztbw zta m B K [] → c'.nreg eF = 1) ∧
    (c'.nreg eF = 1 → ∃ τ, 0 < τ ∧
      (∀ τ₀, Genuine J.left a σ τ₀ →
        rayPt a σ τ₀ ∈ ShotList.loSet ztbw zta m B K [] → τ = τ₀) ∧
      c'.nreg eA ≤ 1 ∧
      (c'.nreg eA = 1 → c'.nreg ztle < (chainModel J.left).W.n ∧
        ProperPos ztbw zta P.n ztxzj ∧
        Arrival (chainModel J.left).W ztiu σ (c'.nreg ztle)
          ((chainModel J.left).param zta ztxzj) ∧
        (c'.nreg zthq = 0 ↔
          (chainModel J.left).param zta ztxzj = 0)) ∧
      (c'.nreg eA ≠ 1 → ∀ p t, ¬ Arrival (chainModel J.left).W ztiu σ p t))

/-- A normalised position: same parameter and point, and a zero code exactly at the vertex. -/
theorem nhgt_facts {M : Model} {Q : Polygon} {n : ℕ} {u : WPos} (hu : ProperPos M Q n u) :
    ProperPos M Q n ztdxn ∧ M.param Q ztdxn = M.param Q u ∧
      M.pos Q ztdxn = M.pos Q u ∧
      (nhgt M Q u = 0 ↔ M.param Q ztdxn = 0) := by
  obtain ⟨⟨hpp, hcase⟩, hedge, hpos, hkey, -⟩ := Restore.normOf_facts hu
  have he : (ztdxn : WPos) = Restore.normOf M Q u := by
    unfold nhgt; rw [← hedge]
  zucjo
  have hpar : M.param Q (Restore.normOf M Q u) = M.param Q u := by
    unfold Model.key at hkey; simp_all
  refine ⟨hpp, hpar, hpos, ztbwk⟩
  · rw [← he, h]; rfl
  grind
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- A valid origin lies in the domain of `C₁`. -/
theorem origin_mem_left_dom {J : Merge.Junction} (hP : J.P.Simple) {a : Point}
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared) (ha₁ : a.2 ≤ J.left.top.2) : a ∈ J.left.dom := by
  zuhbw
  rcases (Merge.not_mem_dom_iff J.left ha₁).1 hn with hb | hs
  · zujzy
    rw [hR] at hb; exact hb (J.right.set_subset_box haR)
  · exact not_mem_left_of_right hP haR hav hs

/-- The direction of a code `≤ 1` and of its complement. -/
theorem dirOf_rev {d : ℕ} (hd : d ≤ 1) : -dirOf (1 - d) = dirOf d := by
  unfold dirOf
  grind
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- **The shot of a candidate.** -/
theorem evShot_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {J : Merge.Junction} {N : NF} {L : List ℕ}
    (hI : IInv W c₀ c) (hK₀ : Consts c₀) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hP : J.P.Simple)
    (hX : X.holds P c₀.nmem ztxj ztdq)
    (hcap : c₀.nreg ztbcb ≤ X.cap P c₀.nmem ztxj)
    (hOk : Ok P ztbw) (hNF : IsNF ztbw zta N)
    (hsg : (chainModel J.left).Semigranular (N.F ztbw zta) ztq)
    (hmd : ModelDescAt c.nmem zthvf zta ztbw)
    (hmwf : ModelDescWF P ztm c.nmem zthvf) (hm0 : c.nmem zthvf = 0)
    (hctx : ChainCtx P W c CD₁ J.left) (hcd : c.nreg CD₁ = c.nreg MD₁ + 1)
    (hL : ∀ a ∈ L, a < N.arcs.length) (hgK : c.nreg wGK = L.length)
    (hAB : c.nreg wGB + 4 * L.length ≤ c.nreg ALLOC)
    (harcs : ∀ k, k < L.length → ShotList.arcAt c.nmem ztdcv k =
      nArc ztbw zta N zthbf)
    {s : SymPt} (hs : SymPtIn c oSym s) (hsl : s.Lt P.n)
    (haR : s.eval zta ∈ J.right.set) (hav : s.eval zta ≠ J.shared)
    (ha₁ : (s.eval zta).2 ≤ J.left.top.2) (hD : c.nreg oD ≤ 1)
    (hroom : c.nreg ALLOC + evShotK ztwiu L.length ≤ W) :
    IRS P W c₀ ztvpz c (evShotK ztwiu L.length) (fun c' =>
      ShotOut P J c.nmem ztdcv L.length ztwpu ztzel c' ∧
      EFr ShW c c') := by
  zuyr
  set a := s.eval zta with ha
  zufam
  set K := L.length with hKd
  zusw
  zufgg
  have hPW : ztmd := by unfold hostWords at hWh; omega
  have haD := origin_mem_left_dom hP haR hav ha₁
  zukad
  have hay : ztsnt := by
    zummt
    zudxk
  -- 1. prepare the shot block
  have hok : okB W c.nmem evPrepL c.nreg := by
    simp only [evPrepL, okB, okI]
    exact ⟨iscr_sw by_norm_num by_norm_num, iscr_sw by_norm_num by_norm_num,
      iscr_sw by_norm_num by_norm_num, iscr_sw by_norm_num by_norm_num,
      iscr_sw by_norm_num by_norm_num, iscr_sw by_norm_num by_norm_num,
      iscr_sw by_norm_num by_norm_num, iscr_sw by_norm_num by_norm_num,
      iscr_sw by_norm_num by_norm_num, ztgpa,
      iscr_sw by_decide by_decide, trivial⟩
  refine IRS.seq (K₂ := ShotList.shotCost ztwiu K + 49989)
    (IRS.block evPrepL hI hok) ?_ |>.mono
    (by simp only [evPrepL, evShotK, List.length_cons, List.length_nil]; omega) ztb
  zugn
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, pR, po⟩ := evPrepL_val c.nmem c.nreg
  zull
  have q1 : ∀ q, zteus → q ≠ eRD → c₁.nreg q = c.nreg q := by_simp_all
  have hA1 : ztdc := q1 _ by_decide by_decide
  have c0 : c₁.nreg RS = c.nreg MD₁ := by zvmwl; exact p0
  have c1' : c₁.nreg ztnoq = c.nreg wGB := by zvmwl; exact p1
  zufez
  have c6 : c₁.nreg ztnor = c.nreg oD := by zvmwl; exact p6
  have c7 : ztylo := by
    zury
  have c8 : ztylp := by
    zurz
  zuepo
  have cR : c₁.nreg eRD = 1 - c.nreg oD := by
    zvmwl; show regB c.nmem evPrepL c.nreg eRD = _; rw [pR, show c.nreg K1 = 1 from hK.2.1]
  have hhl : ztrfv := by
    unfold ShotList.holeList; rw [c9]; rfl
  have hori : ztlae := by
    show SymPtIn c₁ _ s
    exact symPtIn_transport hs ztmdm ztmdn
      ztmdo
  -- 2. the precondition of the shot
  zuiyh
  have hX1 : ztyll := by
    rw [c8]
    exact X.mono _ _ _ _ _ hI₁.hA (X.local_ _ _ _ _ _ by_grind hX)
  have hcap1 : ztxtf := by
    zubeh
  have hreg := hctx.hostReg
  obtain ⟨-, -, -, ⟨H, hCD, -⟩, -, hWm⟩ := id hctx
  have hmD : ModelDescAt c₁.nmem ztqkh zta ztbw := by
    grind
  have hRS1 : c₁.nreg RS + 1 = c.nreg CD₁ := by_omega
  have pre : ztiys := by
    refine ⟨hG, hWh, hX1, hcap1, by_grind, by_grind,
      by omega, by_omega, H, J.left,
      by grind, by_grind, hOk, hWm, fun j hj => ?_,
      by grind, .sym s, hori, hsl,
      Or.inr ⟨IOrc.innerPt_chain J.left ?_ ?_, by_grind⟩, hay, ?_⟩
    · zudfn

      exact nArc_piece hP hNF hsg (hL _ (getD_mem_of_lt hj))
    · zuhxf
      rw [hR]; exact (J.right.abs_le_coordBound_of_mem_set haR).1
    · zuhxf
      rw [hR]; exact (J.right.abs_le_coordBound_of_mem_set haR).2
    · zujbj
      exfalso
      have hM : ztezg := FactsChain.walkAx J.left hP
      apply hM.trace p hp t ht0 ht1
      show sidePt (chainModel J.left).W p t ∈ J.left.dom
      have : sidePt (chainModel J.left).W p t = Geometry.lerp ((chainModel J.left).wa p)
          ((chainModel J.left).wb p) t := rfl
      rw [this, hpt]; tauto
  -- 3. the shot
  refine IRS.seq (K₂ := 49989 - 11 + 11)
    (shot_irs hsh hBs hXl hI₁ pre (by zvnja; unfold evShotK at hroom; omega)) ?_
    |>.mono by_grind (fun _ h => h)
  zubse
  obtain ⟨hfl, A, hlo, hhi, hyes, hno⟩ := hpost ztbw ztuvq hmD hori
  rw [c6] at hyes hno
  have hev : Origin.eval ztbw _ ztvco = a := rfl
  zujiv
  zutr

  have hAoff : A ⊆ J.left.domᶜ := by
    zucdk
    have := hhi hw
    zuwe

    exact Sweep.arcSet_subset_compl_dom J.left hP _ _ hj
  -- registers after the shot
  have keep2 :=
    fun r h1 h2 h3 => k2 r ztsg ztu h3
  zuftj
  have hm2' : ztux := fun a ha => by
    zucjp
  have cd2 : c₂.nreg CD₁ = c.nreg CD₁ :=
    (keep2 _ by_decide by_decide by_decide).trans
      (q1 _ by_decide by_decide)
  zuixq
  have eR2 :=
    (keep2 _ by_decide by_decide by_decide).trans cR
  -- the frame so far
  have fr2 : EFr ShW c c₂ := by
    refine ⟨fun r hr hX hra => ?_, hA2', hm2'⟩
    zugjp
    · rw [keep2 r hsw.1 hsw.2 (fun h => hX zteg)]
      exact q1 r (by
        by_contra h; push Not at h; exact hX (Or.inl ⟨by unfold RS; omega, by unfold RS; omega⟩))
        (fun h => hX (Or.inr ztbbj))
    · rw [k2 r hr hra (fun h => hsw ⟨by unfold RS at h; omega, by unfold RS at h; omega⟩)]
      exact q1 r by_omega (fun h => hsw ⟨by unfold eRD sw at h; omega, by unfold eRD sw at h; omega⟩)
  -- 4. copy the flag
  have hok3 : okB W c₂.nmem [.copyN eF 241320] c₂.nreg :=
    ⟨iscr_sw by_decide by_decide, trivial⟩
  refine IRS.seq (K₁ := 1) (K₂ := 49977) (IRS.block [.copyN eF 241320] hI₂ hok3) ?_ |>.mono
    by_norm_num ztb
  zugbb
  have v3 : c₃.nreg eF = c₂.nreg 241320 := by
    zudub
  have k3 : ∀ r, r ≠ eF → c₃.nreg r = c₂.nreg r := fun r hr => by
    zvnar; zumxi; exact upd_other _ _ _ hr
  zuyu
  have hA3 : ztbox := k3 _ by_decide
  have fr3 := fr2.trans ⟨fun r _ hX _ => k3 r (fun h => hX (Or.inr ⟨by zvmwc, by
      zvmwc; decide⟩)), hA3.ge, by_grind⟩
  have hk0 := (hK₀.fix hI₃).1
  -- the uniqueness of the hit parameter for genuine hits
  have huniq : ∀ t, FirstHit A a σ t → ∀ τ₀, Genuine J.left a σ τ₀ →
      rayPt a σ τ₀ ∈ ShotList.loSet ztbw zta c.nmem ztdcv K [] →
      t = τ₀ := by
    intro t hFH τ₀ hg hτ₀
    obtain ⟨hfr, hhp⟩ := (genuine_iff J.left ha₁ hσ').1 hg
    rw [← hhp] at hτ₀ ⊢
    exact firstHit_exit J.left hσ' ha₁ hfr hAoff hFH ztvvo
  have hcompl : ∀ τ₀, Genuine J.left a σ τ₀ →
      rayPt a σ τ₀ ∈ ShotList.loSet ztbw zta c.nmem ztdcv K [] →
      c₂.nreg 241320 = 1 := by
    intro τ₀ hg hτ₀
    zuct
    exact hno hne τ₀ hg.1 ztvvo
  by_cases hf : c₃.nreg K0 < c₃.nreg eF
  · -- a hit
    zuijy
    zukca
    zujye
    zublb
    have hpos2' : (chainModel J.left).pos _ ztrbv = rayPt a σ t :=
      hpos2
    have he2' : c₂.nreg 241321 < (chainModel J.left).W.n := he2
    have hpp2' : ProperPos _ _ P.n ztrbv := hpp2
    have e3 : c₃.nreg 241321 = c₂.nreg 241321 := k3 _ by_decide
    have h3' : c₃.nreg 241322 = c₂.nreg 241322 := k3 _ by_decide
    have hctx3 :=
      hctx2.transport (k3 _ by_decide) by_grind hA3.ge
    have eR3 := (k3 _ by_decide).trans eR2
    have hK1 : evShotK _ K = ShotList.shotCost ztwiu K + 50000 :=
      rfl
    zvnja at hAb
    rw [hK1] at hroom
    generalize ShotList.shotCost _ K = S at hAb hroom
    have hroom3 : c₃.nreg ALLOC + 35007 ≤ W := by_grind
    refine IRS.mono (K := 49975 + 2) ztdfp by_norm_num
      ztb
    refine IRS.seq (K₂ := 14968) (callArr_irs hI₃ hctx3
      ⟨by_decide, by_decide, by_norm_num, by_norm_num, by_norm_num,
        by norm_num, by_decide, by_decide⟩
      ⟨by_decide, by_decide⟩ by_omega
      by_grind (by rw [e3, h3', hpos2']; tauto) hroom3) ?_ |>.mono
      by_norm_num ztb
    rintro c₄ hI₄ hA₄ hA₄' ⟨harr, k4, hal4, hm4⟩
    zumqg
    rw [e3, h3', eR3, hpos2'] at harr
    rw [dirOf_rev hD] at harr
    have k4' : ∀ r, bandOf r ∉ oracleBands → (r < eA ∨ eA + 2 < r) → r ≠ ALLOC →
        c₄.nreg r = c₃.nreg r := fun r hr h hra => k4 r hr by_omega
          by_omega by_omega hra
    have fr4 := fr3.trans ⟨fun r hr hX hra => k4' r hr (by
      by_contra h; push Not at h; exact hX (Or.inr ⟨by unfold eF eA sw at *; omega,
        by unfold eA eNo sw at *; omega⟩)) hra, hal4, hm4⟩
    have eF4 : c₄.nreg eF = 1 := by
      rw [k4' eF ztmr
        by_decide by_decide, v3, h1]
    obtain ⟨hfA, hA1', hA0⟩ := harr
    have hk04 := (hK₀.fix hI₄).1
    by_cases ha4 : c₄.nreg K0 < c₄.nreg eA
    · -- normalise the arrival position
      zukul
      have hfa1 : c₄.nreg eA = 1 := by_omega
      obtain ⟨hpe, hppA, hArr⟩ := hA1' hfa1
      have hctx4 := hctx3.transport (k4' _
        ztmr
        by_decide by_decide) hm4 hal4
      refine (IRS.ifT by_omega (normS_irs hI₄ ztqpk hctx4
        ⟨by_decide, by_decide, by_decide,
          by decide, by_decide, by_decide⟩
        ⟨by_decide, by_decide, by_decide,
          by decide, by_decide, by_decide,
          by norm_num⟩ hpe hppA (fun _ _ _ _ => by
            have e : (chainModel J.left).pos _ ⟨c₄.nreg _, c₄.nreg _⟩ =
                sidePt (chainModel J.left).W (c₄.nreg _)
                  ((chainModel J.left).param zta ⟨c₄.nreg ztle, c₄.nreg zthq⟩) := rfl
            rw [e, hArr.2.2.2.1]; exact hay)
        (by rw [hA3] at hA₄'; omega))).mono
        by_norm_num ?_
      rintro c₅ ⟨n1, n2, k5, hal5, hm5⟩
      have k5' := k5
      obtain ⟨hppN, hparN, hposN, hnz⟩ := nhgt_facts hppA
      have eA5 : c₅.nreg eA = 1 := by
        rw [k5' eA ztmr
          by_omega by_decide by_decide
          by_decide, hfa1]
      have eF5 : c₅.nreg eF = 1 := by
        rw [k5' eF ztmr
          by_decide by_decide by_decide
          by_decide, eF4]
      refine ⟨⟨by rw [eF5], by_omega, fun _ => ⟨t, hFH.1, huniq t hFH, by rw [eA5],
        fun _ => ?_, by_omega⟩⟩, fr4.trans ⟨fun r hr hX hra => k5' r hr ?_ ?_ ?_ hra,
          hal5, hm5⟩⟩
      · rw [n1, n2]
        refine ⟨hpe, hppN, ?_, hnz⟩
        rw [hparN]; omega
      · intro h; exact hX (Or.inr ⟨by zvmwc; decide, by zvmwc; decide⟩)
      · intro h; exact hX (Or.inr ⟨by zvmwc; decide, by_omega⟩)
      · intro h; exact hX (Or.inr ⟨by zvmwc; decide, by zvmwc⟩)
    · refine (IRS.ifF ha4 (IRS.skip (K := 0) hI₄ rfl)).mono by_norm_num ?_
      zuu
      zukul
      have hfa : c₄.nreg eA ≠ 1 := by_omega
      refine ⟨⟨by rw [eF4], by_omega, fun _ => ⟨t, hFH.1, huniq t hFH, hfA,
        fun h => absurd h hfa, by_omega⟩⟩, fr4⟩
  · -- no hit
    refine (IRS.ifF hf (IRS.skip (K := 0) hI₃ rfl)).mono by_norm_num ?_
    zuu
    zuijy
    have h0 : c₂.nreg 241320 ≠ 1 := by_omega
    refine ⟨⟨by_omega, fun τ₀ hg hτ₀ => absurd (hcompl τ₀ hg hτ₀) h0,
      by omega⟩, fr3⟩
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt)
@[expose] public section
def cB1 : ℕ := sw 652
def cN1 : ℕ := sw 653
def cE1 : ℕ := sw 654
def cLL : ℕ := sw 655
def cLD : ℕ := sw 656
def cGL : ℕ := sw 657
def cNW : ℕ := sw 658
def cLE : ℕ := sw 660
def cD : ℕ := sw 2260
def cV : ℕ := sw 2261
def cPs : ℕ := sw 2262
def cME : ℕ := sw 2263

/-- The constants of the map. -/
structure MapK (J : Merge.Junction) (c : Config) : Prop where
  b1 : c.nreg cB1 = b₁ J
  n1 : c.nreg cN1 = (chainModel J.left).W.n
  e1 : c.nreg cE1 = E₁ J
  ll : c.nreg cLL = lL1 J
  ld : c.nreg cLD = lδ J
  gl : c.nreg cGL = ztit % (chainModel J.whole).W.n
  nw : c.nreg cNW = (chainModel J.whole).W.n
  le : c.nreg cLE = lL1 J + lδ J
variable {J : Merge.Junction}
theorem MapK.fix {W : ℕ} {c₀ c : Config} (h : MapK J c₀)
    (hI : IInv W c₀ c) : MapK J c := by
  have k : ∀ i, 652 ≤ i → i ≤ 660 → c.nreg _ = c₀.nreg ztcdy := fun i h1 h2 =>
    hI.hin _ ztze
  obtain ⟨a, b, d, e, f, g, i, j⟩ := h
  exact ⟨(k 652 le_rfl by_norm_num).trans a, (k 653 by_norm_num by_norm_num).trans b,
    (k 654 by_norm_num by_norm_num).trans d, (k 655 by_norm_num by_norm_num).trans e,
    (k 656 by_norm_num by_norm_num).trans f, (k 657 by_norm_num by_norm_num).trans g,
    (k 658 by_norm_num by_norm_num).trans i, (k 660 by_norm_num by_norm_num).trans j⟩

/-! ## The program -/

/-- The gap tests (valid branches set `cV := 1`, the branch beyond the gap `cPs := d - lδ`). -/
def mapGap : Stmt :=
  .ifLtN cLL cD (.ifLtN cD cLE .skip (block [.subN cPs cD cLD, .constN cV 1]))
    (.ifLtN cD cLL ztigc (.ifLtN K0 zthq .skip ztigc))

/-- **The offset and validity of an arrival edge.** -/
def mapC : Stmt :=
  .seq (block [.addN cD ztle cN1, .subN cD cD cB1]) (.seq (condSub cD cD cN1)
    (.seq (block [.constN cV 0, .copyN cPs cD])
      (.ifLtN cD cE1 (.ifLtN K0 cLD mapGap ztigc) .skip)))

/-- **The walk edge of `M`.** -/
def mapE : Stmt := .seq (block [.addN cME cGL cPs]) (condSub cME cME cNW)

/-- The validity of a `b₁`-offset with a height code (the arithmetic conditions of `MValid`). -/
def MVal (J : Merge.Junction) (d h : ℕ) : Prop :=
  d < E₁ J ∧ ¬ ztrv ∧ ¬ (0 < lδ J ∧ d = lL1 J ∧ h ≠ 0)

/-! ## The run -/
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- The post of the map: the offset, the validity flag and `ψ`; only `cD, cV, cPs` change. -/
def MapPost (J : Merge.Junction) (c c' : Config) (d h : ℕ) : Prop :=
  c'.nreg cD = d ∧ c'.nreg cV ≤ 1 ∧ (c'.nreg cV = 1 ↔ MVal J d h) ∧
    (c'.nreg cV = 1 → c'.nreg cPs = ψ J d) ∧
    (∀ r, r ≠ cD → r ≠ cV → r ≠ cPs → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem

/-- Setting a scratch register to a constant. -/
theorem irs_const {r v : ℕ} (hI : IInv W c₀ c) (hr : IScr r) (hv : v ≤ W) :
    IRS P W c₀ ztcyq c 1 (fun c' => c'.nreg r = v ∧
      ztbcc ∧ c'.nmem = c.nmem) :=
  (IRS.reg hI hr ztjik).mono le_rfl by_simp_all
theorem iscr_sw' {i : ℕ} (h1 : 700 ≤ i) (h2 : i < 10000) : IScr ztcdy :=
  iscr_sw ztce ztce
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The gap tests.** -/
theorem mapGap_irs (hI : IInv W c₀ c) (hK : Consts c) (hM : MapK J c)
    {d : ℕ} (hd : c.nreg cD = d) (hv0 : c.nreg cV = 0) (hps : c.nreg cPs = d)
    (hδ : 0 < lδ J) (hdE : d < E₁ J) (hW : 1 ≤ W) :
    IRS P W c₀ mapGap c 7 (fun c' => MapPost J c c' d ztwrv) := by
  zudpx
  have hsc : IScr cV := iscr_sw' by_norm_num by_norm_num
  have hsp : IScr cPs := iscr_sw' by_norm_num by_norm_num
  zucay

  unfold mapGap
  by_cases h1 : c.nreg cLL < c.nreg cD
  · zuije
    refine IRS.mono (K := 5 + 2) (IRS.ifT ztktd ?_) by_norm_num ztb
    by_cases h2 : c.nreg cD < c.nreg cLE
    · zuijd
      refine IRS.mono (K := 0 + 2) (IRS.ifT ztktc ztsyg)
        by_norm_num ?_
      zuu
      refine ⟨hd, by_omega, ⟨by_simp_all, fun h => absurd by_omega h.2.1⟩,
        by simp_all, by_omega, rfl⟩
    · zuijd
      refine IRS.mono (IRS.ifF ztktc (IRS.block _ hI
        ⟨hsp, ⟨hsc, hW⟩, trivial⟩)) by_norm_num ?_
      zuu
      unfold MapPost
      zudj
      refine ⟨?_, ?_, ⟨fun _ => ⟨hdE, by_omega, by_grind⟩, fun _ => ?_⟩, fun _ => ?_,
        fun r h1' h2' h3' => ?_, trivial⟩
      · tauto
      · simp
      · simp
      · rw [upd_other _ _ _ nVP.symm, upd_same, hd, hM.ld]
        unfold ψ; simp_all
      simp_all
  · zuije
    refine IRS.mono (K := 5 + 2) (IRS.ifF ztktd ?_) by_norm_num ztb
    have hψ : ztguy := by unfold ψ; simp_all
    by_cases h3 : c.nreg cD < c.nreg cLL
    · zuijf
      refine IRS.mono (IRS.ifT ztkte ztrsl)
        by_norm_num ?_
      zuhjp
      refine ⟨by_grind, by_omega, ⟨fun _ => ⟨hdE, by_omega,
        by grind⟩, by_omega⟩, by_grind,
        by simp_all, v3⟩
    · zuijf
      have hdl : d = lL1 J := by_omega
      refine IRS.mono (K := 3 + 2) (IRS.ifF ztkte ?_) by_norm_num ztb
      by_cases h4 : c.nreg K0 < c.nreg zthq
      · zukwz
        refine IRS.mono (K := 0 + 2) (IRS.ifT by_omega ztsyg) by_norm_num ?_
        zuu
        refine ⟨hd, by_omega, ⟨by_simp_all, fun h => absurd by_omega h.2.2⟩,
          by simp_all, by_omega, rfl⟩
      · zukwz
        refine IRS.mono (IRS.ifF by_omega ztrsl)
          by_norm_num ?_
        zuhjp
        refine ⟨by_grind, by_omega, ⟨fun _ => ⟨hdE, by_omega,
          by simp_all⟩, by_omega⟩, by_grind,
          by simp_all, v3⟩
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The offset and validity of an arrival edge.** -/
theorem mapC_irs (hI : IInv W c₀ c) (hK₀ : Consts c₀) (hM₀ : MapK J c₀)
    (hpA : c.nreg ztle < (chainModel J.left).W.n)
    (hW : 2 * (chainModel J.left).W.n ≤ W) :
    IRS P W c₀ mapC c 20 (fun c' => MapPost J c c'
      (ztwrx % (chainModel J.left).W.n)
      ztwrv) := by
  zuyr
  zuclu
  zudpx
  zubae
  have hb : b₁ J < n₁ := by
    have := tpos_lt J.left J.m₁
    zuhfi
    zufd
    zumrz
  set pA := c.nreg _ with hpAd
  set d := ztils % n₁ with hdd
  have hsD : IScr cD := iscr_sw' by_norm_num by_norm_num
  have hsV : IScr cV := iscr_sw' by_norm_num by_norm_num
  have hsP : IScr cPs := iscr_sw' by_norm_num by_norm_num
  have nD : ∀ r, r = cD → r ≠ eA + 2 := by rintro r rfl; decide
  -- 1. `cD := pA + n₁ - b₁`
  have hok1 : okB W c.nmem [.addN cD ztle cN1, .subN cD cD cB1] c.nreg :=
    ⟨⟨hsD, by zupcj; omega⟩, hsD, trivial⟩
  refine IRS.seq (K₂ := 18) ztrjn ?_ |>.mono by_norm_num ztb
  zuer
  zudj
  set f₁ := upd _ cD
    _ with hf₁
  have v1 : f₁ cD = pA + n₁ - b₁ J := by
    rw [hf₁, upd_same, upd_same, upd_other _ _ _ by_decide, hM.n1, hM.b1]
  have o1 : ∀ r, r ≠ cD → f₁ r = c.nreg r := by_simp_all
  -- 2. `cD := d`
  obtain ⟨c₂, k₂, hk₂, ex₂, v₂, o₂⟩ := condSub_exec (P := P) (c := { c with nreg := f₁ })
    hI₁.hw cD cD cN1
  refine IRS.seq (K₂ := 15) (irs_of_out hI₁ ex₂ hk₂ o₂ by_grind) ?_ |>.mono
    by_norm_num ztb
  zubuo
  zuejb
  have hn1 : f₁ cN1 = n₁ := by rw [o1 _ by_decide, hM.n1]
  simp only at v₂
  rw [v1, hn1] at v₂
  have vd : c₂.nreg cD = d := by
    rw [v₂, hdd]
    zus
    · zukp
    · zul
  have o2 : ∀ r, r ≠ cD → c₂.nreg r = c.nreg r := by_grind
  have hm2 := om₂
  -- 3. `cV := 0`, `cPs := d`
  have hok3 : okB W c₂.nmem [.constN cV 0, .copyN cPs cD] c₂.nreg := ⟨⟨hsV, by_omega⟩, hsP, trivial⟩
  refine IRS.seq (K₂ := 13) ztrjp ?_ |>.mono by_norm_num ztb
  zudsv
  zudj
  zucay

  set f₃ := upd _ cPs _ with hf₃
  have d3 : f₃ cD = d := by_tauto
  have v3 : f₃ cV = 0 := by_rfl
  have p3 : f₃ cPs = d := by_tauto
  have o3 : ∀ r, r ≠ cD → r ≠ cV → r ≠ cPs → f₃ r = c.nreg r := fun r h1 h2 h3 => by
    rw [hf₃, upd_other _ _ _ h3, upd_other _ _ _ h2, o2 r h1]
  have e2 : f₃ _ = c.nreg zthq :=
    o3 _ by_decide by_decide by_decide
  have lift : ∀ c', MapPost J { c₂ with nreg := f₃ } c' d (f₃ (eA + 2)) →
      MapPost J c c' d ztwrv := by
    zuecf
    zvnlz at a3
    exact ⟨a1, a2, a3, a4, fun r h1 h2 h3 => by rw [a5 r h1 h2 h3]; grind,
      by grind⟩
  -- 4. the tests
  have hI₃' := hI₃
  have hK3 := hK₀.fix hI₃
  have hM3 : MapK J { c₂ with nreg := f₃ } := hM₀.fix hI₃
  by_cases hE : f₃ cD < f₃ cE1
  · have hdE : d < E₁ J := by have := hM3.e1; grind
    refine IRS.mono (K := 11 + 2) (IRS.ifT hE ?_) by_norm_num ztb
    have k03 : f₃ K0 = 0 := hK3.1
    by_cases hδ : f₃ K0 < f₃ cLD
    · have hδ' : zthoc := by
        have := hM3.ld; grind
      refine IRS.mono (K := 7 + 2) ztsyd by_norm_num ztb
      exact (mapGap_irs hI₃ hK3 hM3 d3 v3 p3 hδ' hdE by_omega).mono le_rfl lift
    · have hδ' : lδ J = 0 := by
        have := hM3.ld; grind
      refine IRS.mono (IRS.ifF hδ (irs_const hI₃ hsV by_omega)) by_norm_num ?_
      rintro c' ⟨w1, w2, w3⟩
      refine lift c' ⟨by rw [w2 _ nV.symm, Config.nreg_mk, d3], by_omega,
        ⟨fun _ => ⟨hdE, by_grind, by_grind⟩, by_omega⟩, fun _ => ?_,
        fun r _ h2 _ => w2 r h2, w3⟩
      rw [w2 _ nVP.symm]; simp only; rw [p3]
      zudwk
  · have hdE : ¬ d < E₁ J := by have := hM3.e1; grind
    refine IRS.mono (K := 0 + 2) (IRS.ifF hE zthau) by_norm_num ?_
    zuu
    refine lift _ ⟨d3, by_grind,
      ⟨by_grind, fun h => absurd h.1 hdE⟩,
      by grind, by_omega, rfl⟩
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt)
@[expose] public section
def cAW : ℕ := sw 2264
def cAF : ℕ := sw 2268
def cFr : ℕ := sw 2272

/-- **The far-end test.** -/
def farChk : Stmt :=
  .seq (callAbs CD₁ ztle zthq cAW) (.seq (callAbs zted oFE oFC cAF)
    (.ifLtN K0 oD (callAbsCmp cAW cAF cFr) (callAbsCmp cAF cAW cFr)))
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The far-end test**: `cFr = 1` iff the hit is before the far end in the direction `oD`. -/
theorem farChk_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK₀ : Consts c₀)
    (hctx1 : ChainCtx P W c CD₁ J.left) (hctx2 : ChainCtx P W c zted J.right)
    (he1 : c.nreg ztle < (chainModel J.left).W.n)
    (hpp1 : ProperPos ztbw zta P.n ztwvi)
    (hy1 : |((chainModel J.left).pos zta ⟨c.nreg ztle, c.nreg zthq⟩).2| <
      J.left.radius)
    (he2 : c.nreg oFE < (chainModel J.right).W.n)
    (hpp2 : ProperPos ztj zta P.n ztdqn)
    (hy2 : |((chainModel J.right).pos zta ⟨c.nreg oFE, c.nreg oFC⟩).2| < J.right.radius)
    (hD : c.nreg oD ≤ 1) (hroom : c.nreg ALLOC + 34000 ≤ W) :
    IRS P W c₀ farChk c 34000 (fun c' =>
      BitIs c' cFr (if c.nreg oD = 1 then
          ((chainModel J.left).pos zta ztwvi).1 <
            ((chainModel J.right).pos zta ztdqn).1
        else ((chainModel J.right).pos zta ztdqn).1 <
            ((chainModel J.left).pos zta ztwvi).1) ∧
      EFr ztfca c c') := by
  zuyr
  have hG := hctx1.1
  have hPW : ztmd := by have := hctx1.2.1; unfold hostWords at this; omega
  set x₁ := ((chainModel J.left).pos _ zteyb).1 with hx₁
  set x₂ := ((chainModel J.right).pos _ ztdqn).1 with hx₂
  refine IRS.seq (K₂ := 17293) (callAbs_irs hI hctx1
    ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide⟩
    ⟨by_decide, by_decide⟩ he1 hpp1 hy1 by_omega) ?_ |>.mono
    by_norm_num ztb
  rintro c₁ hI₁ hA₁ hA₁' ⟨hr₁, k₁, ha₁, hm₁⟩
  have kk₁ :=
    fun r h1 h2 h3 => k₁ r ztsg h3 ztu
  have hctx2' : ztrfl :=
    hctx2.transport (kk₁ _ by_decide by_decide by_decide) hm₁ ha₁
  have eFE : c₁.nreg oFE = c.nreg oFE := kk₁ _ by_decide by_decide
    by_decide
  have eFC : c₁.nreg oFC = c.nreg oFC := kk₁ _ by_decide by_decide
    by_decide
  refine IRS.seq (K₂ := 586) (callAbs_irs hI₁ hctx2'
    ⟨by_decide, by_decide, by_decide, by_decide,
      by decide, by_decide⟩
    ⟨by_decide, by_decide⟩ by_omega
    by_simp_all by_simp_all by_omega) ?_ |>.mono
    by_norm_num ztb
  rintro c₂ hI₂ hA₂ hA₂' ⟨hr₂, k₂, ha₂, hm₂⟩
  rw [eFE, eFC] at hr₂
  have kk₂ :=
    fun r h1 h2 h3 => k₂ r ztsg h3 ztu
  have hr₁' :=
    ShotList.absRec_copy hr₁ (kk₂ _ by_decide by_decide
      by_decide)
      ztjzp
      ztjzp
      ztjzp
  have hR : J.right.radius = J.left.radius := rfl
  rw [hR] at hr₂
  have eD : ztshk := by
    rw [kk₂ _ by_decide by_decide by_decide,
      kk₁ _ by_decide by_decide by_decide]
  zuibc
  have fr2 : EFr ztfca c c₂ := by
    refine ⟨fun r hr hX hra => ?_, ha₁.trans ha₂, fun a ha => by_grind⟩
    rw [k₂ r hr (by by_contra h; push Not at h; exact hX ⟨by unfold cAW cAF sw at *; omega,
      by unfold cAF cFr sw at *; omega⟩) hra]
    exact k₁ r hr (by by_contra h; push Not at h; exact hX ⟨by_omega,
      by unfold cAW cFr sw at *; omega⟩) hra
  have hroom2 : c₂.nreg ALLOC + 269 ≤ W := by_omega
  have fr3 : ∀ c', (∀ r, bandOf r ∉ oracleBands → r ≠ cFr → r ≠ ALLOC → c'.nreg r = c₂.nreg r) →
      c₂.nreg ALLOC ≤ c'.nreg ALLOC → ztdwt →
      EFr ztfca c c' := fun c' k₃ ha₃ hm₃ =>
    fr2.trans ⟨fun r hr hX hra => k₃ r hr (fun h => hX ⟨by zvmwc; decide,
      by zvmwc⟩) hra, ha₃, hm₃⟩
  by_cases hd : c₂.nreg K0 < c₂.nreg oD
  · zuile
    have hd1 : c.nreg oD = 1 ∨ 1 < c.nreg oD := by_omega
    refine IRS.mono (IRS.ifT by_omega (callAbsCmp_irs hI₂ hG hPW ⟨by_decide, by_decide,
        by decide, by_decide⟩
      ⟨by_decide, by_decide⟩ hr₁' hr₂ hroom2)) by_norm_num ?_
    zugaz
    have h1 : ztuor := by_omega
    refine ztomn
  · zuile
    have h0 : ztuos := by_omega
    refine IRS.mono (IRS.ifF by_omega (callAbsCmp_irs hI₂ hG hPW ⟨by_decide, by_decide,
        by decide, by_decide⟩
      ⟨by_decide, by_decide⟩ hr₂ hr₁' hroom2)) by_norm_num ?_
    zugaz
    refine ztomn

/-! ## The walk edge -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The walk edge of `M`**: `cME := (cGL + cPs) mod n` (`cGL, cPs < n`). -/
theorem mapE_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hM₀ : MapK J c₀)
    (hps : c.nreg cPs < (chainModel J.whole).W.n) (hW : 2 * (chainModel J.whole).W.n ≤ W) :
    IRS P W c₀ mapE c 4 (fun c' =>
      c'.nreg cME = (ztit % (chainModel J.whole).W.n + c.nreg cPs) %
        (chainModel J.whole).W.n ∧
      (∀ r, r ≠ cME → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  zuclu
  have hgl : ztwyn :=
    Nat.mod_lt _ by_omega
  have hsM : IScr cME := iscr_sw' by_norm_num by_norm_num
  refine IRS.seq (K₁ := 1) (K₂ := 3) (IRS.block [.addN cME cGL cPs] hI
    ⟨⟨hsM, by rw [hM.gl]; omega⟩, trivial⟩) ?_ |>.mono by_norm_num (fun _ h => h)
  zuer
  obtain ⟨c₂, k₂, hk₂, ex₂, v₂, o₂⟩ := condSub_exec (P := P)
    (c := { c with nreg := regB c.nmem [.addN cME cGL cPs] c.nreg }) hI₁.hw cME cME cNW
  refine (irs_of_out hI₁ ex₂ hk₂ o₂ by_simp_all).mono le_rfl ?_
  zuu
  zuejb
  zvmzj at v₂
  have hnw : upd c.nreg cME (c.nreg cGL + c.nreg cPs) cNW = (chainModel J.whole).W.n := by
    rw [upd_other _ _ _ by_decide, hM.nw]
  rw [hnw, hM.gl] at v₂
  refine ⟨?_, fun r hr => ?_, om₂⟩
  · rw [v₂]
    by_cases h : ztit % (chainModel J.whole).W.n + c.nreg cPs < (chainModel J.whole).W.n
    · rw [ite_eq_left h, Nat.mod_eq_of_lt h]
    · zubme
      generalize hX : ztit % (chainModel J.whole).W.n + c.nreg cPs = X at h ⊢
      have hX2 : X < 2 * (chainModel J.whole).W.n := by_omega
      zul
  · rw [or₂ r by_simp_all]
    zudj
    simp_all

/-! ## The table write -/
def cTB : ℕ := sw 661
def cTA : ℕ := sw 2273

/-- The address of the table record of the end `oS` of chord `oK`. -/
def tabAddrL : List Instr :=
  [.copyN cTA cTB, .addN cTA cTA oK, .addN cTA cTA oK, .addN cTA cTA oK, .addN cTA cTA oK,
    .addN cTA cTA oK, .addN cTA cTA oK, .addN cTA cTA oS, .addN cTA cTA oS, .addN cTA cTA oS]

/-- **The table write**: `(1, cME, eA + 2)` at `cTB + 3 (2 oK + oS)`. -/
def tabW : Stmt :=
  .seq (block tabAddrL) (.seq (.instr (.storeN cTA K1)) (.seq ztnsf
    (.seq (.instr (.storeN cTA cME)) (.seq ztnsf (.instr (.storeN cTA zthq))))))
theorem tabAddrL_val (m f : ℕ → ℕ) :
    regB m tabAddrL f cTA = f cTB + 3 * (2 * f oK + f oS) ∧
      ∀ q, q ≠ cTA → regB m tabAddrL f q = f q := by
  have hK : oK ≠ cTA := by_decide
  have hS : oS ≠ cTA := by_decide
  have hB : cTB ≠ cTA := by_decide
  refine ⟨?_, fun q hq => regB_other _ _ _ (fun i hi => by
    simp only [tabAddrL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      zvmwd <;> exact by_omega)⟩
  simp only [tabAddrL, regB, regI, upd_same, upd_other _ _ _ hK, upd_other _ _ _ hS]
  ring
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The table write.** -/
theorem tabW_irs (hI : IInv W c₀ c) (hK₀ : Consts c₀) (hT : c₀.nreg ALLOC ≤ c.nreg cTB)
    (hW : c.nreg cTB + 3 * ztqs + 2 ≤ W) :
    IRS P W c₀ tabW c 16 (fun c' =>
      c'.nmem = upd (upd (upd c.nmem (c.nreg cTB + 3 * ztqs) 1)
        (c.nreg cTB + 3 * ztqs + 1) ztdcu)
        (c.nreg cTB + 3 * ztqs + 2) ztwrv ∧
      (∀ r, r ≠ cTA → c'.nreg r = c.nreg r)) := by
  zuyr
  zubof
  have hsA : IScr cTA := iscr_sw' by_norm_num by_norm_num
  have hK' : oK ≠ cTA := by_decide
  have hS' : oS ≠ cTA := by_decide
  have hB' : cTB ≠ cTA := by_decide
  set A := c.nreg cTB + 3 * ztqs with hA
  have hok : okB W c.nmem tabAddrL c.nreg := by
    simp only [tabAddrL, okB, okI, regI, upd_same, upd_other _ _ _ hK', upd_other _ _ _ hS']
    grind
  obtain ⟨va, vo⟩ := tabAddrL_val c.nmem c.nreg
  have nK1 : K1 ≠ cTA := by_decide
  have nME : cME ≠ cTA := by_decide
  have nE2 : eA + 2 ≠ cTA := by_decide
  refine IRS.seq (K₂ := 6) (IRS.block tabAddrL hI hok) ?_
  zugn
  have a1 : c₁.nreg cTA = A := by_simp_all
  have o1 : ∀ q, q ≠ cTA → c₁.nreg q = c.nreg q := by_simp_all
  zufp
  refine IRS.seq (K₂ := 5) (IRS.store hI₁ by_omega) ?_
  zubib
  have r2 : c₂.nreg = c₁.nreg := by zumyw
  have m2 : c₂.nmem = upd c.nmem A 1 := by_simp_all
  refine IRS.seq (K₂ := 4) (IRS.block [.addN cTA cTA K1] hI₂
    ⟨⟨hsA, by_grind⟩, trivial⟩) ?_
  zugbb
  have a3 : c₃.nreg cTA = A + 1 := by
    zvnar; zvmzj; simp_all
  have o3 : ∀ q, q ≠ cTA → c₃.nreg q = c.nreg q := fun q hq => by
    zvnar; zumxi; simp_all
  have m3 : c₃.nmem = upd c.nmem A 1 := by_simp_all
  refine IRS.seq (K₂ := 3) (IRS.store hI₃ by_omega) ?_
  zudsw
  have r4 : c₄.nreg = c₃.nreg := by zumyv
  have m4 : c₄.nmem = upd ztrxs ztbo ztdcu := by
    simp_all
  refine IRS.seq (K₂ := 2) (IRS.block [.addN cTA cTA K1] hI₄
    ⟨⟨hsA, by_simp_all⟩, trivial⟩) ?_
  zukod
  have a5 : c₅.nreg cTA = A + 2 := by
    rw [hc5]; zvmzj; simp_all
  have o5 : ∀ q, q ≠ cTA → c₅.nreg q = c.nreg q := fun q hq => by
    rw [hc5]; zumxi; simp_all
  have m5 : c₅.nmem = upd ztrxs ztbo ztdcu := by_simp_all
  refine (IRS.store hI₅ by_omega).mono by_norm_num ?_
  simp_all
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam
@[expose] public section
def lblOf (c : Config) (bN bL : ℕ) : List ℕ :=
  (List.range (min ztvji 4)).map fun i => c.nreg ztctw

/-- Append unless listed or full. -/
def addL (l : List ℕ) (v : ℕ) : List ℕ := if v ∈ l ∨ 4 ≤ l.length then l else l ++ [v]
theorem lblOf_length (c : Config) (bN bL : ℕ) : (lblOf c bN bL).length = min ztvji 4 := by
  simp [lblOf]
variable {l : List ℕ}
theorem addL_length_le (h : l.length ≤ 4) (v : ℕ) : (addL l v).length ≤ 4 := by
  zuckx
theorem mem_addL {v x : ℕ} : x ∈ addL l v → x ∈ l ∨ x = v := by
  zuckx

/-- Run `s` if the registers `r`, `x` differ. -/
def neq (r x : ℕ) (s : Stmt) : Stmt := .ifLtN r x s (.ifLtN x r s .skip)

/-- **Append the value of `r`** to the label list `bN, bL`. -/
def addLab (bN bL r : ℕ) : Stmt :=
  .ifLtN bN K1 (block [.copyN bL r, .constN bN 1])
    (neq r bL (.ifLtN bN K2 (block [.copyN ztbzi r, .constN bN 2])
      (neq r ztbzi (.ifLtN bN K3 (block [.copyN ztfpc r, .constN bN 3])
        (neq r ztfpc (.ifLtN bN K4 (block [.copyN ztnru r, .constN bN 4])
          (neq r ztnru .skip)))))))
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
theorem neq_irs {r x : ℕ} {s : Stmt} {K : ℕ} {Q : Config → Prop} (hI : IInv W c₀ c)
    (hs : c.nreg r ≠ c.nreg x → IRS P W c₀ s c K Q) (hq : c.nreg r = c.nreg x → Q c) :
    IRS P W c₀ (neq r x s) c ztfns Q := by
  unfold neq
  by_cases h1 : c.nreg r < c.nreg x
  · exact (IRS.ifT h1 (hs by_omega)).mono by_omega ztb
  · by_cases h2 : c.nreg x < c.nreg r
    · exact (IRS.ifF h1 ztoxc).mono by_omega ztb
    · exact (IRS.ifF h1 (IRS.ifF h2 (IRS.skip (K := 0) hI (hq by_omega)))).mono by_omega
        ztb

/-- The registers of a label list. -/
def LblR (bN bL q : ℕ) : Prop := q = bN ∨ (bL ≤ q ∧ q < bL + 4)

/-- Two copies: the result of the block `[copyN (bL + i) r, constN bN (i + 1)]`. -/
theorem lab_set_irs {bN bL r i : ℕ} (hI : IInv W c₀ c) (hsN : IScr bN) (hsL : IScr ztctw)
    (hne : bN ≠ bL + i) (hW : i + 1 ≤ W) :
    IRS P W c₀ (block [.copyN ztctw r, .constN bN ztg]) c 2 (fun c' =>
      c'.nreg ztctw = c.nreg r ∧ c'.nreg bN = i + 1 ∧
      ztfyq ∧ c'.nmem = c.nmem) := by
  refine (IRS.block [.copyN ztctw r, .constN bN ztg] hI ⟨hsL, ⟨hsN, hW⟩, trivial⟩).mono
    le_rfl ?_
  zuu
  refine ⟨?_, ?_, fun q h1 h2 => ?_, rfl⟩ <;> zumxi
  · rw [upd_other _ _ _ ztnr, upd_same]
  · simp
  simp_all
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **Appending a label.** -/
theorem addLab_irs {bN bL r : ℕ} (hI : IInv W c₀ c) (hK : Consts c) (hsN : IScr bN)
    (hsL : ∀ i, i < 4 → IScr ztctw) (hNL : ∀ i, i < 4 → bN ≠ bL + i)
    (_hrN : r ≠ bN) (_hrL : ∀ i, i < 4 → r ≠ bL + i)
    (hKN : ∀ k, k = K1 ∨ k = K2 ∨ k = K3 ∨ k = K4 → ¬ LblR bN bL k)
    (hN : c.nreg bN ≤ 4) (hW : 4 ≤ W) :
    IRS P W c₀ (addLab bN bL r) c 30 (fun c' => c'.nreg bN ≤ 4 ∧
      lblOf c' bN bL = addL ztefk ztfgx ∧
      ztdpz ∧ c'.nmem = c.nmem) := by
  obtain ⟨-, k1, -, k4, -, k2, k3⟩ := hK
  have kK : ∀ k, k = K1 ∨ k = K2 ∨ k = K3 ∨ k = K4 → ∀ c' : Config,
      ztdpz → c'.nreg k = c.nreg k :=
    fun k hk c' h => h k (hKN k hk)
  have lbl : ∀ c' : Config, lblOf c' bN bL =
      (List.range (min (c'.nreg bN) 4)).map fun i => c'.nreg ztctw := fun _ => rfl
  have hlen : (lblOf c bN bL).length = c.nreg bN := by_grind
  -- the frame of a set
  have setFr : ∀ i, i < 4 → ∀ c' : Config, ztfyq →
      ∀ q, ¬ LblR bN bL q → c'.nreg q = c.nreg q := fun i hi c' h q hq =>
    h q (fun h' => hq ztxgk) (fun h' => hq zthrp)
  unfold addLab
  generalize hn : c.nreg bN = n at hN hlen
  interval_cases n
  · -- empty list
    refine (IRS.ifT by_omega (lab_set_irs (i := 0) hI hsN (hsL 0 by_norm_num)
      (hNL 0 by_norm_num) by_omega)).mono by_norm_num ?_
    zubia
    refine ⟨by_omega, ?_, setFr 0 by_norm_num c' v3, v4⟩
    rw [lbl c', lbl c, v2, hn]
    zvnhg at v1
    simp [addL, v1]
  -- the outcome "unchanged"
  · -- one label
    have hl : lblOf c bN bL = [c.nreg bL] := by_grind
    zupu

    · refine IRS.mono (K := 2 + 2) (IRS.ifT by_omega (lab_set_irs (i := 1) hI hsN
        (hsL 1 by_norm_num) (hNL 1 by_norm_num) by_omega)) by_norm_num ?_
      zubia
      refine ⟨by_omega, ?_, setFr 1 by_norm_num c' v3, v4⟩
      zuhdr
      zudkg
      simp [addL, List.range_succ, e0, v1, hne]
    · zujvn
  · -- two labels
    have hl : lblOf c bN bL = [c.nreg bL, c.nreg ztbzi] := by zuogl; rfl
    zupu

    · zucbv

      · refine IRS.mono (K := 2 + 2) (IRS.ifT by_omega (lab_set_irs (i := 2) hI hsN
          (hsL 2 by_norm_num) (hNL 2 by_norm_num) by_omega)) by_norm_num ?_
        zubia
        refine ⟨by_omega, ?_, setFr 2 by_norm_num c' v3, v4⟩
        zuhdr
        have e1 : ztzpf :=
          v3 _ by_omega ztnyv
        zudkg
        simp [addL, List.range_succ, e0, e1, v1, hne, hne']
      · zujvn
    · zujvn
  · -- three labels
    have hl : lblOf c bN bL = [c.nreg bL, c.nreg ztbzi, c.nreg ztfpc] := by
      zuogl; rfl
    zupu

    · zucbv

      · refine IRS.mono (K := 16 + 2) ztbyj by_norm_num
          ztb
        refine IRS.mono (K := 12 + 4) (neq_irs hI (fun hne'' => ?_) ztcng) le_rfl
          ztb
        · refine IRS.mono (K := 2 + 2) (IRS.ifT by_omega (lab_set_irs (i := 3) hI
            hsN (hsL 3 by_norm_num) (hNL 3 by_norm_num) by_omega)) by_norm_num ?_
          zubia
          refine ⟨by_omega, ?_, setFr 3 by_norm_num c' v3, v4⟩
          have e0 : ztmul :=
            v3 _ by_omega zthgy
          have e1 : ztzpf :=
            v3 _ by_omega ztnyv
          have e2 : c'.nreg ztfpc = c.nreg ztfpc :=
            v3 _ by_omega (fun h => hNL 2 by_norm_num h.symm)
          zudkg
          simp [addL, List.range_succ, e0, e1, e2, v1, hne, hne', hne'']
        · zujvn
      · zujvn
    · zujvn
  · -- full
    have hl4 : (lblOf c bN bL).length = 4 := hlen
    have hfull : ∀ v, addL ztefk v = lblOf c bN bL := fun v => by
      zuckx
    have hun : ∀ (K : ℕ), IRS P W c₀ .skip c K (fun c' => c'.nreg bN ≤ 4 ∧
        lblOf c' bN bL = addL ztefk ztfgx ∧
        ztdpz ∧ c'.nmem = c.nmem) := fun K =>
      IRS.skip hI ⟨by_omega, (hfull _).symm, fun _ _ => rfl, rfl⟩
    have hq : c.nreg bN ≤ 4 ∧ lblOf c bN bL = addL ztefk ztfgx ∧
        (∀ q, ¬ LblR bN bL q → c.nreg q = c.nreg q) ∧ c.nmem = c.nmem :=
      ⟨by_omega, (hfull _).symm, fun _ _ => rfl, rfl⟩
    refine IRS.mono (K := 28 + 2) ztbyj le_rfl ztb
    refine IRS.mono (K := 24 + 4) ztdoz le_rfl ztb
    refine IRS.mono (K := 22 + 2) ztbyj le_rfl ztb
    refine IRS.mono (K := 18 + 4) ztdoz le_rfl ztb
    refine IRS.mono (K := 16 + 2) ztbyj by_norm_num ztb
    refine IRS.mono (K := 12 + 4) ztdoz le_rfl ztb
    refine IRS.mono (K := 10 + 2) ztbyj by_norm_num ztb
    exact IRS.mono (K := 0 + 4) (neq_irs hI (fun _ => hun 0) (fun _ => hq)) by_norm_num
      ztb
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
def kE : ℕ := sw 2400
def kH : ℕ := sw 2401
def bF : ℕ := sw 2410
def bE : ℕ := sw 2411
def bH : ℕ := sw 2412
def bN : ℕ := sw 2413
def bL : ℕ := sw 2414
def cO : ℕ := sw 2280
def cO2 : ℕ := sw 2282
def cGW : ℕ := sw 659

/-- The offset (from `gW`) of a position of the walk of `C`. -/
noncomputable def offK (P : Polygon) (J : Merge.Junction) (e h : ℕ) : ℝ :=
  off (chainModel J.whole).W.n (gW J : ℝ) ((chainModel J.whole).key zta ztcq)

/-- Take the candidate. -/
def takeL : List Instr :=
  [.constN bF 1, .copyN bE cME, .copyN bH zthq, .constN bN 2, .copyN bL oUp, .copyN ztbzi oDn]

/-- Compare with the best candidate. -/
def offCmp' : Stmt :=
  .seq (callOff ztjl cME zthq bE bH cGW cO2)
    (.ifLtN K0 cO2 ztqei (.ifLtN K0 zttht .skip
      (.seq (addLab bN bL oUp) (addLab bN bL oDn))))

/-- **The offer of a candidate.** -/
def offerC : Stmt :=
  .seq (callOff ztjl cME zthq kE kH cGW cO)
    (.ifLtN K0 ztths (.ifLtN K0 bF offCmp' ztqei) .skip)

/-- The registers of the best candidate. -/
def BestR (q : ℕ) : Prop := q = bF ∨ q = bE ∨ q = bH ∨ LblR bN bL q

/-- The best-candidate state is unchanged. -/
def BestSame (c c' : Config) : Prop :=
  c'.nreg bF = c.nreg bF ∧ c'.nreg bE = c.nreg bE ∧ c'.nreg bH = c.nreg bH ∧
    lblOf c' bN bL = lblOf c bN bL ∧ c'.nreg bN = c.nreg bN

/-- **The outputs of the offer.** -/
def OfferOut (P : Polygon) (J : Merge.Junction) (c c' : Config) : Prop :=
  c'.nreg bF ≤ 1 ∧ c'.nreg bN ≤ 4 ∧
  (¬ offK P J ztwe ztbhr < offK P J ztdcu ztwrv → BestSame c c') ∧
  (offK P J ztwe ztbhr < offK P J ztdcu ztwrv →
    (c.nreg bF ≠ 1 ∨ offK P J ztdcu ztwrv < offK P J ztvo ztvp) →
    c'.nreg bF = 1 ∧ c'.nreg bE = c.nreg cME ∧ c'.nreg bH = c.nreg zthq ∧
    lblOf c' bN bL = [c.nreg oUp, c.nreg oDn] ∧ c'.nreg bN = 2) ∧
  (offK P J ztwe ztbhr < offK P J ztdcu ztwrv → c.nreg bF = 1 →
    offK P J ztdcu ztwrv = offK P J ztvo ztvp →
    c'.nreg bF = 1 ∧ c'.nreg bE = c.nreg bE ∧ c'.nreg bH = c.nreg bH ∧
    lblOf c' bN bL = addL (addL ztefk zthvl) zthvk) ∧
  (offK P J ztwe ztbhr < offK P J ztdcu ztwrv → c.nreg bF = 1 →
    offK P J ztvo ztvp < offK P J ztdcu ztwrv → BestSame c c') ∧
  EFr ztcvl c c'
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
theorem takeL_val (m f : ℕ → ℕ) :
    regB m takeL f bF = 1 ∧ regB m takeL f bE = f cME ∧ regB m takeL f bH = f zthq ∧
    regB m takeL f bN = 2 ∧ regB m takeL f bL = f oUp ∧ regB m takeL f ztbzi = f oDn ∧
    (∀ q, ¬ BestR q → regB m takeL f q = f q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q hq => regB_other _ _ _ ztdp⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [takeL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> zvmwd <;> intro h <;> apply hq
    · tauto
    · tauto
    · tauto
    · tauto
    · exact Or.inr ztzcq
    · exact Or.inr ztzcq
theorem lblOf_take {c c' : Config} (h1 : c'.nreg bN = 2) (h2 : c'.nreg bL = c.nreg oUp)
    (h3 : c'.nreg ztbzi = c.nreg oDn) : lblOf c' bN bL = [c.nreg oUp, c.nreg oDn] := by
  unfold lblOf; zvmwp; simp [List.range_succ, h2, h3]
theorem lblOf_congr {c c' : Config} (h : ∀ q, LblR bN bL q → c'.nreg q = c.nreg q) :
    lblOf c' bN bL = lblOf c bN bL := by
  zujqo
  rw [h bN ztp]
  zucfh
  zug
  zucpm
  exact h _ ztbh
theorem bestR_reg {q : ℕ} (h : BestR q ∨ (cO ≤ q ∧ q ≤ cO2 + 1)) : sw 2280 ≤ q ∧ q ≤ sw 2417 := by
  unfold BestR LblR bF bE bH bN bL cO cO2 sw at h
  zumvd
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **The offer of a candidate.** -/
theorem offerC_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK₀ : Consts c₀)
    (hctx : ChainCtx P W c ztjl J.whole) (hgw : c.nreg cGW = gW J)
    (hgn : gW J < (chainModel J.whole).W.n)
    (hc : PosW P J ztdcu ztwrv) (hk : PosW P J ztwe ztbhr)
    (hb : c.nreg bF = 1 → PosW P J ztvo ztvp) (hbF : c.nreg bF ≤ 1)
    (hbN : c.nreg bN ≤ 4) (hroom : c.nreg ALLOC + 22200 ≤ W) :
    IRS P W c₀ offerC c 22200 ztrka := by
  zuyr
  obtain ⟨k0, k1, -, -, -, -, -⟩ := hK
  zukar
  set oc := offK P J ztdcu ztwrv with hoc
  set ok := offK P J ztwe ztbhr with hok
  set ob := offK P J ztvo ztvp with hob
  zugmg
  -- 1. candidate against the key
  refine IRS.seq (K₂ := 11192) (callOff_irs hI hctx
    ⟨by_decide, by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide, by_decide⟩
    ⟨by_decide, by_decide⟩ hc.1 hk.1 by_omega
    hc.2.1 hk.2.1 hc.2.2 hk.2.2 by_omega) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨b1, b2, k₁, ha₁, hm₁⟩
  rw [hgw'] at b1 b2
  change BitIs c₁ cO (oc < ok) at b1
  change BitIs c₁ _ (ok < oc) at b2
  have kk₁ : ∀ r, ¬ (cO ≤ r ∧ r ≤ cO2 + 1) → bandOf r ∉ oracleBands → r ≠ ALLOC →
      c₁.nreg r = c.nreg r := fun r h1 h2 h3 => k₁ r h2 (fun h => h1 ⟨by_omega, by
        unfold cO cO2 sw at *; omega⟩) (fun h => h1 ⟨by_omega, by unfold cO cO2 sw at *; omega⟩) h3
  have ksw₁ :=
    fun r h1 h2 h3 => kk₁ r h3 ztsg ztu
  have k01 := (hK₀.fix hI₁).1
  have fr1 : EFr ztcvl c c₁ :=
    ⟨by_grind, ha₁, hm₁⟩
  have same1 : ztflf := fun r hr => ksw₁ r
    (by have := bestR_reg ztcgw; unfold sw at this; omega)
    (by have := bestR_reg ztcgw; unfold sw at this; omega)
    (by unfold BestR LblR bF bE bH bN bL cO cO2 sw at *; omega)
  have bs1 : BestSame c c₁ := ⟨same1 _ ztp, same1 _ ztwiz,
    same1 _ ztbh, lblOf_congr (fun q hq => same1 q ztbmd),
    same1 _ ztbaje⟩
  -- the take block from a configuration `c₂` agreeing with `c` outside the scratch
  have takeIRS : ∀ c₂ : Config, IInv W c₀ c₂ → EFr ztcvl c c₂ →
      (∀ r, r = cME ∨ r = eA + 2 ∨ r = oUp ∨ r = oDn → c₂.nreg r = c.nreg r) →
      ok < oc → (c.nreg bF ≠ 1 ∨ oc < ob) →
      IRS P W c₀ ztqei c₂ 6 ztrka := by
    intro c₂ hI₂ fr2 hr2 hlt0 hcase
    have hok : okB W c₂.nmem takeL c₂.nreg := by
      zuhqb
      exact ⟨ztkmb, iscr_sw' by_norm_num by_norm_num,
        iscr_sw' by_norm_num by_norm_num, ztkmb,
        iscr_sw' by_norm_num by_norm_num, iscr_sw by_decide
          by_decide, trivial⟩
    refine (IRS.block takeL hI₂ hok).mono le_rfl ?_
    zujgc
    obtain ⟨t1, t2, t3, t4, t5, t6, tO⟩ := takeL_val c₂.nmem c₂.nreg
    have e1 : c'.nreg bF = 1 := by zumyg; exact t1
    have e2 : c'.nreg bE = c.nreg cME := by zumyg; grind
    have e3 : c'.nreg bH = c.nreg zthq := by zumyg; grind
    have e4 : c'.nreg bN = 2 := by zumyg; exact t4
    have e5 : c'.nreg bL = c.nreg oUp := by zumyg; grind
    have e6 : c'.nreg ztbzi = c.nreg oDn := by
      zumyg; grind
    have hlb := lblOf_take e4 e5 e6
    refine ⟨by_omega, by_omega, by_grind, by_grind,
      fun h hb1 heq => ?_, fun h hb1 hlt => ?_, fr2.trans ⟨fun r hr hX hra => by
        zumyg; grind,
        by zumyg; rfl,
        fun a _ => by zumyg⟩⟩
    · grind
    grind
  have keepc₁ : ∀ r, r = cME ∨ r = eA + 2 ∨ r = oUp ∨ r = oDn → c₁.nreg r = c.nreg r := by
    rintro r (rfl | rfl | rfl | rfl)
    · zudmp
    · zudmp
    · zudmp
    · zudmp
  by_cases h2 : c₁.nreg K0 < c₁.nreg ztths
  · zudus
    have hlt := b2.2.1 (by have := b2.1; omega)
    refine IRS.mono (K := 11190 + 2) ztdfp by_norm_num ztb
    have bF1 := bs1.1
    by_cases h3 : c₁.nreg K0 < c₁.nreg bF
    · zuild
      have hbF1 : c.nreg bF = 1 := by_omega
      zulnz
      have hbP := hb hbF1
      have eBE := bs1.2.1
      have eBH := bs1.2.2.1
      have hctx₁ : ChainCtx P W c₁ _ J.whole := hctx.transport
        (ksw₁ _ by_decide by_decide by_decide) hm₁ ha₁
      have egw := (ksw₁ _ by_decide
        by_decide by_decide).trans hgw
      have eME := keepc₁ _ ztp
      have eE2 := keepc₁ _ ztwiz
      refine IRS.seq (K₂ := 180) (callOff_irs hI₁ hctx₁
        ⟨by_decide, by_decide, by_decide, by_decide,
          by decide, by_decide, by_decide,
          by decide, by_decide, by_decide,
          by decide, by_decide⟩
        ⟨by_decide, by_decide⟩ (by rw [eME]; exact hc.1)
        (by zupcf; exact hbP.1) by_omega (by zuoop; exact hc.2.1)
        (by zungw; exact hbP.2.1) (by zuoop; exact hc.2.2)
        (by zungw; exact hbP.2.2) by_omega) ?_
      rintro c₂ hI₂ hA₂ hA₂' ⟨d1, d2, k₂, ha₂, hm₂⟩
      rw [egw, eME, eE2, eBE, eBH] at d1 d2
      change BitIs c₂ cO2 _ at d1
      change BitIs c₂ _ _ at d2
      have kk₂ :=
        fun r h1 h2 h3 h4 => k₂ r ztsg h3 h4 ztu
      have fr2 := fr1.trans
        ⟨fun r hr hX hra => k₂ r hr (fun h => hX (Or.inr ⟨by zvmwc; decide,
          by omega⟩)) (fun h => hX (Or.inr ⟨by zvmwc; decide, by zvmwc⟩))
          hra, ha₂, hm₂⟩
      have keepc₂ : ∀ r, r = cME ∨ r = eA + 2 ∨ r = oUp ∨ r = oDn → c₂.nreg r = c.nreg r := by
        zuz
        rw [← keepc₁ r hr]
        rcases hr with rfl | rfl | rfl | rfl
        · exact kk₂ _ by_decide by_decide by_decide
            by_decide
        · exact kk₂ _ by_decide by_decide by_decide
            by_decide
        · exact kk₂ _ by_decide by_decide by_decide
            by_decide
        · exact kk₂ _ by_decide by_decide by_decide
            by_decide
      have same2 : ztflg := fun r hr => by
        rw [← same1 r hr]
        have := bestR_reg ztcgw
        exact kk₂ r ztnwc ztnwc
          zthfm
          zthfm
      have bs2 : BestSame c c₂ := ⟨same2 _ ztp, same2 _ ztwiz,
        same2 _ ztbh,
        lblOf_congr (fun q hq => same2 q ztbmd),
        same2 _ ztbaje⟩
      zuibc
      by_cases h4 : c₂.nreg K0 < c₂.nreg cO2
      · zukwv
        have hlt2 := d1.2.1 (by have := d1.1; omega)
        exact (IRS.ifT by_omega (takeIRS c₂ hI₂ fr2 keepc₂ hlt (Or.inr hlt2))).mono
          by_norm_num by_grind
      · zukwv
        have hnlt2 : ¬ oc < ob := fun h => by have := d1.2.2 h; omega
        refine IRS.mono (K := 176 + 2) ztbyj by_norm_num ztb
        by_cases h5 : c₂.nreg K0 < c₂.nreg zttht
        · zukww
          have hlt3 : ob < oc := d2.2.1 (by have := d2.1; omega)
          refine IRS.mono (K := 0 + 2) zthat by_norm_num ?_
          zuu
          exact ⟨by rw [bs2.1]; omega, by zupck; omega, fun h => absurd hlt h,
            fun _ h => by_grind,
            fun _ _ heq => absurd heq (ne_of_gt hlt3), fun _ _ _ => bs2, fr2⟩
        · zukww
          have heq : oc = ob := by
            have : ¬ ob < oc := fun h => by have := d2.2.2 h; omega
            grind
          refine IRS.mono (K := 60 + 2) ztbyj by_norm_num ztb
          have hsN : IScr bN := iscr_sw' by_norm_num by_norm_num
          have hsL : ∀ i, i < 4 → IScr ztctw := fun i hi =>
            iscr_sw ztozi ztozi
          have hNL : ∀ i, i < 4 → bN ≠ bL + i := fun i hi => by unfold bN bL sw; omega
          have hKN : ∀ k, k = K1 ∨ k = K2 ∨ k = K3 ∨ k = K4 → ¬ LblR bN bL k := by
            rintro k (rfl | rfl | rfl | rfl) <;> simp only [LblR, bN, bL, K1, K2, K3, K4, sw] <;> omega
          have hN2 : c₂.nreg bN ≤ 4 := by zupck; omega
          refine IRS.seq (K₂ := 30) (addLab_irs hI₂ ztvtl hsN hsL hNL
            by_decide (fun i hi => by unfold oUp bL sw; omega) hKN hN2 hW4) ?_
          rintro c₃ hI₃ hA₃ hA₃' ⟨g1, g2, g3, g4⟩
          refine (addLab_irs hI₃ (hK₀.fix hI₃) hsN hsL hNL
            by_decide (fun i hi => by unfold oDn bL sw; omega) hKN g1 hW4).mono
            le_rfl ?_
          zucph
          have nLF : ¬ LblR bN bL bF := by unfold LblR bN bL bF sw; omega
          have nLE : ¬ LblR bN bL bE := by unfold LblR bN bL bE sw; omega
          have nLH : ¬ LblR bN bL bH := by unfold LblR bN bL bH sw; omega
          have eUp : c₂.nreg oUp = c.nreg oUp := keepc₂ _ by_omega
          have eDn : ztmvi := by
            rw [g3 _ (by unfold LblR bN bL oDn sw; omega)]; exact keepc₂ _ by_omega
          have e1 : c'.nreg bF = c.nreg bF := by rw [f3 _ nLF, g3 _ nLF]; exact bs2.1
          refine ⟨by_omega, f1, by_grind,
            by grind,
            fun _ _ _ => ⟨by_omega, by rw [f3 _ nLE, g3 _ nLE]; exact bs2.2.1,
              by rw [f3 _ nLH, g3 _ nLH]; exact bs2.2.2.1, by rw [f2, g2, eDn, eUp, bs2.2.2.2.1]⟩,
            by grind, fr2.trans (EFr.trans
              ⟨fun r hr hX hra => g3 r ztyjg, hA₃, ?_⟩
              ⟨fun r hr hX hra => f3 r ztyjg, ?_, ?_⟩)⟩
          · grind
          · exact (f3 ALLOC (by unfold LblR bN bL ALLOC sw; omega)).ge
          grind
    · zuild
      refine IRS.mono (IRS.ifF by_omega
        (takeIRS c₁ hI₁ fr1 keepc₁ hlt by_omega)) by_norm_num by_grind
  · zudus
    have hnlt : ¬ ok < oc := fun h => by have := b2.2.2 h; omega
    zuflq
    zuu
    exact ⟨by rw [bs1.1]; omega, by rw [bs1.2.2.2.2]; omega, by_grind,
      by grind, by_grind, by_grind, fr1⟩
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
variable {J : Merge.Junction}

/-- **A genuine hit has one arrival position.** -/
theorem arrival_unique {C : Chain} (hP : C.P.Simple) {a : Point} (ha : a.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hg : Genuine C a σ τ) {p p' : ℕ} {t t' : ℝ}
    (hA : Arrival (chainModel C).W ztiu σ p t)
    (hA' : Arrival (chainModel C).W ztiu σ p' t') : p = p' ∧ t = t' := by
  obtain ⟨hτ, hdom, hwD⟩ := hg
  set w := rayPt a σ τ with hw
  have hback : ∀ s, rayPt w (-σ) s = rayPt a σ ztold := fun s => rayPt_back a σ τ s
  have hw2 : w.2 ≤ C.top.2 := by_simp_all
  zukv
  have hfree : FreeAt C w (-σ) := by
    filter_upwards [Ioo_mem_nhdsGT hτ] with s hs
    simp_all
  have he : Merge.shoot C w (-σ) ∈ Merge.augChords C :=
    Merge.shoot_mem_augChords C hw2 hwD hnσ hfree
  obtain ⟨hT, -, -⟩ := Merge.hit_of_freeAt C hw2 hnσ hfree
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∈ Merge.shoot C w (-σ) := by
    zunv
    unfold Merge.shoot
    zuewp
    refine ⟨s / C.hitParam w (-σ), div_nonneg hs.1.le hT.le, (div_le_one hT).2 hs.2.le, ?_⟩
    zubjw
    · zunkt
      grind
    simp
  have att : ∀ {q : ℕ} {u : ℝ}, Arrival (chainModel C).W w σ q u →
      SideAttach (chainModel C).W (Merge.shoot C w (-σ)) q u := by
    intro q u h
    obtain ⟨hq, hu0, hu1, hpt, hsec⟩ := h
    have he' := he
    have hev' := hev
    zvnbr at hsec hev' he'
    have := sideAttach_of_along C hP he' hq hu0 hu1 hnσ hsec hev'
    simp_all
  zubkf
  exact hM.attach_unique he (att hA) (att hA') (by rw [hA.2.2.2.1, hA'.2.2.2.1])
variable {P : Polygon}
/-- **A walk position strictly inside the height band of the box** is a `PosW` position. -/
theorem posW_of_inner {e h : ℕ} (he : e < (chainModel J.whole).W.n)
    (hpp : ProperPos ztbm zta P.n ztcq)
    (hy : |((chainModel J.whole).pos zta ⟨e, h⟩).2| < J.whole.radius) : SweepEv.PosW P J e h := by
  refine ⟨he, hpp, fun h0 => ?_⟩
  zulwd
  push Not at h6
  zubvi
  have hv : (chainModel J.whole).pos zta ztjy = (chainModel J.whole).W.vtx e := by
    show sidePt _ _ ((chainModel J.whole).param zta ztjy) = _
    rw [show (chainModel J.whole).param zta ztjy = 0 from rfl, Chazelle.Chain.sidePt_zero]
  rw [hv, Restore.chain_box_vtx_abs J.whole h6] at hy
  simp_all

/-- **An accepted candidate**: the chord of `C` seen from `a` in the direction `σ` belongs to
`F₂⁺`, ends at the position `(e, h)` of the `C₁` part, before the far end of the chord of `C₂`. -/
def CandOK (P : Polygon) (J : Merge.Junction) (S₂ : Set ztf) (a : Point) (σ : ℝ)
    (e h : ℕ) : Prop :=
  FreeAt J.whole a σ ∧ Merge.shoot J.whole a σ ∈ F₂plus J S₂ ∧
    SideAttach (chainModel J.whole).W ztxc e
      ztxjs ∧
    sidePt (chainModel J.whole).W e ztxjs =
      rayPt a σ zton ∧
    (Lst J : ℝ) ≤ oW J ztyeo ∧ SweepEv.PosW P J e h ∧
    J.whole.hitParam a σ < J.right.hitParam a σ

/-- `b₁ < n₁`. -/
theorem b₁_lt : b₁ J < (chainModel J.left).W.n := by
  have := tpos_lt J.left J.m₁
  have hn : ztbvd := cm_n J.left
  zufd
  zumrz

/-- **The checks of the RAM give an accepted candidate.** -/
theorem candOK_of (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {c : Set Point} (hc : c ∈ S₂)
    {a : Point} {σ : ℝ} (ha : ztla ∨ ztjm)
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared) (ha₁ : a.2 ≤ J.left.top.2) {τ : ℝ}
    (hg : Genuine J.left a σ τ) (hlt : τ < (Merge.rend c).1 - (Merge.lend c).1) {pA hN : ℕ}
    (hpA : pA < (chainModel J.left).W.n)
    (hpp : ProperPos ztbw zta P.n ztkmj)
    (hnorm : hN = 0 ↔ (chainModel J.left).param zta ztkmj = 0)
    (hA : Arrival (chainModel J.left).W ztiu σ pA
      ((chainModel J.left).param zta ztkmj))
    (hMV : SweepEv.MVal J ztfxs hN) :
    CandOK P J S₂ a σ (mEdge J ztfxs)
      hN := by
  zubae
  set d := ztils % n₁ with hd
  set t := (chainModel J.left).param zta ztkmj with ht
  have hb := (b₁_lt (J := J))
  have hpd : zthm % n₁ = pA := by
    rw [hd, Nat.add_mod_mod, show b₁ J + ztils = pA + n₁ by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hpA]
  obtain ⟨h1, h2, h3⟩ := hMV
  have hMV' : d < E₁ J ∧ ¬ ztrv ∧
      ¬ ztbft :=
    ⟨h1, h2, fun h => h3 ⟨h.1, h.2.1, fun h0 => h.2.2 ztvvt⟩⟩
  rw [← hpd] at hA
  obtain ⟨hfree, hhit, hmem, hS, hpt, hO⟩ := cand_sound hP hS₂ hS₂f hc ha haR hav ha₁ hg hlt hMV' hA
  zune
  obtain ⟨-, ha₂, -, hR, -, -⟩ := right_hit_end ztbac ha
  have hpar : (chainModel J.whole).param zta ztrdu = t := by
    rcases hpp.1.lt_or_eq with htp | ht0
    · have hv : ztult := ⟨h1, h2, fun h => h3 ⟨h.1, h.2.1, fun h0 => h.2.2 ztvvt⟩,
        fun h => absurd h htp.ne'⟩
      rw [param_corr hP hv htp, hpd]
    · have h0 : hN = 0 := hnorm.2 ht0.symm
      have ht0' : ztbhh := ht0.symm
      rw [ht0', h0]; rfl
  zuhf
  rw [← hpar] at hS hpt hO
  have hlt' : mEdge J d < (chainModel J.whole).W.n := by
    unfold mEdge; exact Nat.mod_lt _ by_omega
  refine ⟨hfree, hmem, hS, by_grind, ?_, posW_of_inner hlt'
    ⟨by zvokb; exact hpp.1, by zvokb; exact hpp.2.1, hpp.2.2⟩ ?_, ?_⟩
  · rw [hO]
    zujvt
    have : (0 : ℝ) ≤ (chainModel J.whole).param zta ztrdu := by zvokb; exact hpp.1
    linarith
  · show |(sidePt (chainModel J.whole).W ztbqk
      ((chainModel J.whole).param zta ⟨mEdge J d, hN⟩)).2| < J.whole.radius
    rw [hpt, rayPt_snd]
    have hRR : J.whole.radius = J.right.radius := rfl
    rw [hRR]
    zudxk
  grind

/-- **The `C₁` part is read within one turn of the walk of `C₁`.** -/
theorem E₁_le (hP : J.P.Simple) : E₁ J ≤ (chainModel J.left).W.n := by
  zuhf
  zucwn
  zufd
  zueod
  · have hlen : ztckb := by
      zubyk
    unfold E₁
    zulkl
    unfold llen lδ at *
    grind
  · zuot
    unfold E₁
    zucfl
    · obtain ⟨-, hlo, hτs, hLst⟩ := caseB_facts J hbox
      zucz
      omega
    · obtain ⟨hτs, hlo, hLst⟩ := caseC_facts J hVNT hbox
      zucz
      omega
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
variable {J : Merge.Junction}

/-- **The regions above and below a chord record** are on its sides. -/
theorem sideOf_rec {M : Model} {Q : Polygon} {N : NF} (hN : IsNF M Q N) {k : ℕ}
    (hk : k < N.nChords) :
    SideOf M 1 ztbpa (regOf M Q N (N.chord k).up) ∧
      SideOf M (-1) ztbpa (regOf M Q N (N.chord k).dn) := by
  obtain ⟨-, hsides, -⟩ := regOf_spec hN
  obtain ⟨-, -, h⟩ := hsides k hk
  refine ⟨fun z hz hzD => ?_, fun z hz hzD => ?_⟩
  · zucil

  · zucil

/-- **The side labels of a found chord.** -/
theorem evSideLab_fused (hP : J.P.Simple) {Q : Polygon} {N : NF}
    (hN : IsNF ztj Q N)
    (hF : (chainModel J.whole).ChordFamily Q ztbard)
    {k : ℕ} (hk : k < N.nChords) {a : Point} {σ : ℝ}
    (ha : (σ = 1 ∧ a = Merge.lend ztwyq) ∨
      (σ = -1 ∧ a = Merge.rend ztwyq))
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared) (hat : a ≠ J.right.top)
    (hfree : FreeAt J.whole a σ) :
    EvSideLab J ztwzl
      (labSet J Q N 2 (N.chord k).up (N.chord k).dn 0 0) ztxc := by
  set S₂ := N.F ztj Q with hS₂d
  set ch := (N.chord k).toSet ztj Q with hch
  have hS₂ : (chainModel J.right).ChordFamily Q S₂ := hN.1
  zuftz
  have hS₂f : S₂.Finite := hS₂.1
  have hchm : ch ∈ S₂ := by
    zuno

  have hf : Merge.shoot J.whole a σ ∈ F₂plus J S₂ := shoot_end_mem hchm ha hfree
  have hfc : Merge.shoot J.whole a σ ⊆ ch := shoot_sub_end hS₂a hchm ha
  zugb
  have hadm := F₂plus_subset J hS₂a hf
  have haD : a ∉ J.whole.dom := fun hd =>
    J.whole.not_mem_set_of_mem_dom hd ztmbj
  obtain ⟨pB, tB, hB, hpt⟩ := endpoint_attach hM hadm ztmmv haD
  have hoff := off_right_pt J hP hS₂a hS₂f hB.1 hB.2.1 hB.2.2.1 by_simp_all
    by_simp_all
  have hns : tB = 0 → sidePt (chainModel J.whole).W pB tB ≠ J.right.top := fun _ => by
    simp_all
  obtain ⟨hup, hdn⟩ := sideOf_rec hN hk
  zudiv
  obtain ⟨hup', hdn', -⟩ := (regOf_spec hN).2.1 k hk
  zucnd
  zuvm
  · refine ⟨regOf ztj Q N (N.chord k).up, Or.inl ⟨(N.chord k).up,
      Or.inl ztugc, rfl⟩, hreg.1 _ hup', ?_⟩
    exact sideLabel_sub J hP hS₂ hF hchm hf hfc hB hoff.1 hoff.2 hns ztp (hreg.1 _ hup')
      hup G hG hS
  · refine ⟨regOf ztj Q N (N.chord k).dn, Or.inl ⟨(N.chord k).dn,
      Or.inr (Or.inl ztugc), rfl⟩, hreg.1 _ hdn', ?_⟩
    exact sideLabel_sub J hP hS₂ hF hchm hf hfc hB hoff.1 hoff.2 hns ztbt (hreg.1 _ hdn')
      hdn G hG hS
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)
@[expose] public section
def cG : ℕ := sw 2250

/-- The registers the genuineness check may write. -/
def GR (r : ℕ) : Prop := ztgz ∨ r = cG ∨ ztph

/-- **The contract of the genuineness check** `g` (cost `KG`): from an arrival position
`(eA + 1, eA + 2)` of the hit `rayPt a σ τ` of `C₁` (direction code `oD`, abscissa record of `a`
at `oAbsA`), the bit `cG` tells whether the hit is genuine. -/
def GenOK (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction) (g : Stmt) (KG : ℕ) : Prop :=
  ∀ (c₁ : Config) (a : Point) (σ τ : ℝ), IInv W c₀ c₁ → c₁.nreg ALLOC + KG ≤ W →
    c₁.nreg oD ≤ 1 → σ = dirOf (c₁.nreg oD) → AbsRec P c₁ oAbsA a.1 J.left.radius →
    a ∈ J.right.set → a ≠ J.shared → a.2 ≤ J.left.top.2 → 0 < τ →
    c₁.nreg ztle < (chainModel J.left).W.n →
    ProperPos ztbw zta P.n ztxzm →
    Arrival (chainModel J.left).W ztiu σ (c₁.nreg ztle)
      ((chainModel J.left).param zta ztxzm) →
    IRS P W c₀ g c₁ KG (fun c' => BitIs c' cG (Genuine J.left a σ τ) ∧ EFr GR c₁ c')

/-- The tail after a genuine hit before the far end. -/
def evAccT : Stmt := .seq mapC (.ifLtN K0 cV (.seq mapE (.seq tabW offerC)) .skip)

/-- **One candidate.** -/
def evCand (sh g : Stmt) : Stmt :=
  .seq ztvpz (.ifLtN K0 eF (.ifLtN K0 eA (.seq g (.ifLtN K0 cG
    (.seq farChk (.ifLtN K0 cFr evAccT .skip)) .skip)) .skip) .skip)

/-- The table after writing the record `j`. -/
def tabUpd (m : ℕ → ℕ) (T j e h : ℕ) : ℕ → ℕ :=
  upd (upd (upd m ztctp 1) zteog e) zteoh h

/-- **The offer relation** for a candidate `(e, h)` with labels `u, d`. -/
def OfferRel (P : Polygon) (J : Merge.Junction) (c c' : Config) (e h u d : ℕ) : Prop :=
  c'.nreg bF ≤ 1 ∧ c'.nreg bN ≤ 4 ∧
  (¬ offK P J ztwe ztbhr < offK P J e h → BestSame c c') ∧
  (offK P J ztwe ztbhr < offK P J e h →
    (c.nreg bF ≠ 1 ∨ offK P J e h < offK P J ztvo ztvp) →
    c'.nreg bF = 1 ∧ c'.nreg bE = e ∧ c'.nreg bH = h ∧ lblOf c' bN bL = [u, d] ∧ c'.nreg bN = 2) ∧
  (offK P J ztwe ztbhr < offK P J e h → c.nreg bF = 1 →
    offK P J e h = offK P J ztvo ztvp →
    c'.nreg bF = 1 ∧ c'.nreg bE = c.nreg bE ∧ c'.nreg bH = c.nreg bH ∧
    lblOf c' bN bL = addL (addL ztefk u) d) ∧
  (offK P J ztwe ztbhr < offK P J e h → c.nreg bF = 1 →
    offK P J ztvo ztvp < offK P J e h → BestSame c c')

/-- A rejected candidate: memory below the allocator and best candidate unchanged. -/
def RejAt (c c' : Config) : Prop :=
  ztbgf ∧ BestSame c c'

/-- A candidate accepted at the position `(e, h)`. -/
def AccAt (P : Polygon) (J : Merge.Junction) (S₂ : Set ztf) (T j u d : ℕ) (a : Point)
    (σ : ℝ) (c c' : Config) (e h : ℕ) : Prop :=
  CandOK P J S₂ a σ e h ∧ (∀ x, x < c.nreg ALLOC → c'.nmem x = tabUpd c.nmem T j e h x) ∧
    OfferRel P J c c' e h u d

/-- **The result of a candidate**: rejected, or accepted at a position with `CandOK`. -/
def CandRes (P : Polygon) (J : Merge.Junction) (S₂ : Set ztf) (T j u d : ℕ) (a : Point)
    (σ : ℝ) (c c' : Config) : Prop :=
  RejAt c c' ∨ ∃ e h, AccAt P J S₂ T j u d a σ c c' e h

/-- The registers a candidate may write. -/
def CandR (r : ℕ) : Prop :=
  ztgz ∨ (sw 2240 ≤ r ∧ r ≤ sw 2283) ∨ BestR r ∨ ztph
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable {J : Merge.Junction}
theorem mEdge_eq (d : ℕ) :
    (ztit % (chainModel J.whole).W.n + ψ J d) % (chainModel J.whole).W.n = mEdge J d := by
  unfold mEdge; grind
theorem ψ_le (J : Merge.Junction) (d : ℕ) : ψ J d ≤ d := by
  zudwk
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **The accepting tail.** -/
theorem evAccT_irs {S₂ : Set ztf} (hI : IInv W c₀ c)
    (hK₀ : Consts c₀) (hM₀ : MapK J c₀) (hP : J.P.Simple) (hS₂ : S₂ ⊆ Merge.augChords J.right)
    (hS₂f : S₂.Finite) {ch : Set Point} (hch : ch ∈ S₂) {a : Point} {σ : ℝ}
    (ha : ztmpq ∨ ztlus) (haR : a ∈ J.right.set)
    (hav : a ≠ J.shared) (ha₁ : a.2 ≤ J.left.top.2) {τ : ℝ} (hg : Genuine J.left a σ τ)
    (hlt : τ < (Merge.rend ch).1 - (Merge.lend ch).1)
    (hpA : c.nreg ztle < (chainModel J.left).W.n)
    (hpp : ProperPos ztbw zta P.n ztwvi)
    (hnorm : c.nreg zthq = 0 ↔
      (chainModel J.left).param zta ztwvi = 0)
    (hA : Arrival (chainModel J.left).W ztiu σ (c.nreg ztle)
      ((chainModel J.left).param zta ztwvi))
    (hctx₀ : ChainCtx P W c₀ ztjl J.whole) (hgw₀ : c₀.nreg cGW = gW J)
    (hk : PosW P J ztwe ztbhr) (hb : c.nreg bF = 1 → PosW P J ztvo ztvp)
    (hbF : c.nreg bF ≤ 1) (hbN : c.nreg bN ≤ 4) (hT : c₀.nreg ALLOC ≤ c.nreg cTB)
    (hTW : c.nreg cTB + 3 * ztqs + 2 ≤ W)
    (hW : 2 * (chainModel J.whole).W.n ≤ W) (hroom : c.nreg ALLOC + 22300 ≤ W) :
    IRS P W c₀ evAccT c 22300 (fun c' =>
      (SweepEv.MVal J (ztwrx %
          (chainModel J.left).W.n) (c.nreg (eA + 2)) →
        AccAt P J S₂ ztdmu ztqs zthvl zthvk a σ c c'
          (mEdge J (ztwrx %
            (chainModel J.left).W.n)) (c.nreg (eA + 2))) ∧
      (¬ SweepEv.MVal J (ztwrx %
          (chainModel J.left).W.n) (c.nreg (eA + 2)) → RejAt c c') ∧
      ztbid ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC) := by
  have hn1 : (chainModel J.left).W.n ≤ (chainModel J.whole).W.n := by
    rw [cm_n, cm_n]; simp
  have hgn : ztboy := by
    zugq
  zubae
  set d := (c.nreg ztle + n₁ - b₁ J) % n₁ with hd
  set hN := c.nreg zthq with hhN
  -- 1. the map
  refine IRS.seq (K₁ := 20) (K₂ := 22280) (mapC_irs hI hK₀ hM₀ hpA by_omega) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨m1, m2, m3, m4, m5, m6⟩
  have kk₁ : ∀ r, r ≠ cD → r ≠ cV → r ≠ cPs → c₁.nreg r = c.nreg r := m5
  have k01 : zteib := (hK₀.fix hI₁).1
  have hA1 : ztdc := kk₁ _ by_decide
    by_decide by_decide
  have nCD : ∀ r, CandR r ∨ r = ALLOC ∨ True := fun _ => Or.inr (Or.inr trivial)
  by_cases hv : c₁.nreg K0 < c₁.nreg cV
  · zukwu
    have hv1 : c₁.nreg cV = 1 := by_omega
    have hMV : SweepEv.MVal J d hN := m3.1 hv1
    have hps : c₁.nreg cPs = ψ J d := m4 hv1
    refine IRS.mono (K := 22278 + 2) ztdfp le_rfl ztb
    have hψn : ψ J d < (chainModel J.whole).W.n := by
      have := ψ_le J d
      have : d < n₁ := Nat.mod_lt _ by_omega
      omega
    -- 2. the walk edge
    refine IRS.seq (K₁ := 4) (K₂ := 22274) (mapE_irs hI₁ hM₀ by_omega hW) ?_
    rintro c₂ hI₂ hA₂ hA₂' ⟨e2, k2, mm2⟩
    rw [hps, mEdge_eq] at e2
    have kk₂ : ∀ r, r ≠ cD → r ≠ cV → r ≠ cPs → r ≠ cME → c₂.nreg r = c.nreg r := fun r h1 h2 h3 h4 =>
      (k2 r h4).trans (kk₁ r h1 h2 h3)
    have eTB : c₂.nreg cTB = c.nreg cTB := kk₂ _ by_decide by_decide
      by_decide by_decide
    have eK : c₂.nreg oK = c.nreg oK := kk₂ _ by_decide by_decide
      by_decide by_decide
    have eS : c₂.nreg oS = c.nreg oS := kk₂ _ by_decide by_decide
      by_decide by_decide
    have eH2 : c₂.nreg zthq = hN := kk₂ _ by_decide by_decide
      by_decide by_decide
    -- 3. the table write
    refine IRS.seq (K₁ := 16) (K₂ := 22258) (tabW_irs hI₂ hK₀ by_omega
      by_omega) ?_
    rintro c₃ hI₃ hA₃ hA₃' ⟨mm3, k3⟩
    have kk₃ : ∀ r, r ≠ cD → r ≠ cV → r ≠ cPs → r ≠ cME → r ≠ cTA → c₃.nreg r = c.nreg r :=
      fun r h1 h2 h3 h4 h5 => (k3 r h5).trans (kk₂ r h1 h2 h3 h4)
    have kk₃' : ∀ r, (r < sw 2260 ∨ sw 2273 < r) → c₃.nreg r = c.nreg r := fun r hr =>
      kk₃ r (by unfold cD sw at *; omega) (by unfold cV sw at *; omega) (by unfold cPs sw at *; omega)
        (by unfold cME sw at *; omega) (by unfold cTA sw at *; omega)
    have eME3 : c₃.nreg cME = mEdge J d := by
      rw [k3 _ by_decide, e2]
    have eH3 : c₃.nreg zthq = hN := by rw [k3 _ by_decide, eH2]
    have hA3 : ztcke := kk₃' _ by_decide
    -- the candidate
    have hcand := candOK_of (S₂ := S₂) hP hS₂ hS₂f hch ha haR hav ha₁ hg hlt hpA hpp hnorm hA hMV
    have hposW : PosW P J (c₃.nreg cME) (c₃.nreg zthq) := by
      rw [eME3, eH3]; exact hcand.2.2.2.2.2.1
    have hctx₃ : ChainCtx P W c₃ ztjl J.whole :=
      hctx₀.transport (hI₃.hin _ by_trivial) hI₃.hm hI₃.hA
    have hgw₃ : c₃.nreg cGW = gW J := (hI₃.hin _ by_trivial).trans hgw₀
    have sameB : ztflh := fun r hr => kk₃' r
      ztcuj
    have eKE : c₃.nreg kE = c.nreg kE := kk₃' _ by_decide
    have eKH : c₃.nreg kH = c.nreg kH := kk₃' _ by_decide
    have eUp : ztshq := kk₃' _ by_decide
    have eDn : ztmvi := kk₃' _ by_decide
    have eBF := sameB _ ztp
    have eBE := sameB _ ztwiz
    have eBH := sameB _ ztbajm
    have eBN := sameB _ ztbaje
    have eLb : lblOf c₃ bN bL = lblOf c bN bL :=
      lblOf_congr (fun q hq => sameB q ztmbx)
    have bsame : ∀ c' : Config, BestSame c₃ c' → BestSame c c' := fun c' h =>
      ⟨h.1.trans eBF, h.2.1.trans eBE, h.2.2.1.trans eBH, h.2.2.2.1.trans eLb,
        h.2.2.2.2.trans eBN⟩
    refine (offerC_irs hI₃ hK₀ hctx₃ hgw₃ hgn hposW by_grind
      by_grind by_omega by_omega
      by_omega).mono by_norm_num ?_
    rintro c' ⟨o1, o2, o3, o4, o5, o6, ofr⟩
    rw [eKE, eKH, eME3, eH3] at o3
    rw [eKE, eKH, eME3, eH3, eBF, eBE, eBH, eUp, eDn] at o4
    rw [eKE, eKH, eME3, eH3, eBF, eBE, eBH, eLb, eUp, eDn] at o5
    rw [eKE, eKH, eME3, eH3, eBF, eBE, eBH] at o6
    refine ⟨fun _ => ⟨hcand, fun x hx => ?_, o1, o2, fun h => bsame c' (o3 h), o4,
      fun h1 h2 h3 => ?_, fun h1 h2 h3 => bsame c' (o6 h1 h2 h3)⟩, fun h => absurd hMV h,
      fun r hr hX hra => ?_, ?_⟩
    · rw [ofr.2.2 x by_omega, mm3, mm2, m6, eTB, eK, eS, e2, eH2]; rfl
    · grind
    · rw [ofr.1 r hr (fun h => hX (by
        zuy
        · exact Or.inr ztwkb
        · exact Or.inr (Or.inl ⟨by unfold cO sw at h; unfold sw; omega,
            by unfold cO2 sw at h; unfold sw; omega⟩))) hra]
      exact kk₃' r (by
        zufm
        exact hX (Or.inr ztfxv))
    · rw [← hA3]; exact ofr.2.1
  · zukwu
    have hnv : ¬ SweepEv.MVal J d hN := fun h => by_grind
    zuflq
    zuu
    refine ⟨fun h => absurd h hnv, fun _ => ⟨fun x _ => by zupcb, ?_⟩, fun r _ hr hra => ?_, hA1.ge⟩
    · have same : ztflf := fun r hr => kk₁ r
        (by unfold BestR LblR bF bE bH bN bL cD sw at *; omega)
        (by unfold BestR LblR bF bE bH bN bL cV sw at *; omega)
        (by unfold BestR LblR bF bE bH bN bL cPs sw at *; omega)
      exact ⟨same _ ztp, same _ ztwiz, same _ ztbajm,
        lblOf_congr (fun q hq => same q ztmbx),
        same _ ztbaje⟩
    · exact kk₁ r ztwzv
        ztwzv
        ztwzv
