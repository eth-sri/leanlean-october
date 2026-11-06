module

public import Chazelle.MacT
public import Chazelle.Core.OraclePrepOrd
public import Chazelle.Core.NFDecompBfs
public import Chazelle.Core.RestoreRound
public import Chazelle.Core.FuseMathCut
public import Chazelle.Core.BruteCorner

namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ OracleBook
@[expose] public section
theorem chords_mul_le {C : Chain} {Q : Polygon} {N : NF} {γ : ℕ} (hP : C.P.Simple)
    (hC : IsCanonicalNF ztc Q N γ 4) : N.chords.length * γ ≤ 60 * ztz := by
  zuiv
  zubm
  zuivx
  have := hM.lemma23_walk hF.2.1 hF.1 hC.2.1 hC.2.2.1
  zuhkt
  linarith

/-- **The preprocessing.** -/
def prepMainS : Stmt := .seq phA (.seq phB (.seq bookS (.seq ordStage (.seq hdrS payS))))

/-- The bands of the preprocessing. -/
def prepBands : Finset ℕ := {bSign, bSort, bLocate, bDecomp, bOPrep, bOQuery, bCluster}
theorem prepBands_sub : prepBands ⊆ oracleBands ∪ {bOPrep} := by_decide
set_option maxHeartbeats 64000000 in
/-- **The preprocessing meets its specification.** -/
theorem prep_meets : Meets prepMainS prepBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ ChainWF P ztm c.nmem zthzz ∧
      ∃ H C N, ChainDescAt c.nmem zthzz zta H C ∧
      C.P = Qof P ∧ NFWithin c.nmem ztiaa ztm N ∧
      IsCanonicalNF ztc zta N ztrvm 4)
    (fun P c c' => c.nreg ALLOC ≤ rd c' bOPrep 3 ∧ rd c' bOPrep 3 + 3 ≤ c'.nreg ALLOC ∧
      c'.nmem ztiaf = rd c bOPrep 0 ∧ c'.nmem ztpdh = rd c bOPrep 1 ∧
      c'.nmem ztpdi = rd c bOPrep 2 ∧
      ∀ m', ztdwr → OAt P m' ztiaf)
    (fun _ c => κq * (c.nmem ztiaa *
      zthbp + 1)) := by
  intro P W c hw ⟨hG, hHW, hwf, H, C, N, hD, hCQ, hNFw, hcan⟩ hroom
  zuhp
  have hr0 : rd c bOPrep 0 = c.nreg 110000 := rfl
  have hr1 : rd c bOPrep 1 = c.nreg 110001 := rfl
  have hr2 : rd c bOPrep 2 = c.nreg 110002 := rfl
  zufqq
  rw [hr0] at hwf hD hroom
  rw [hr1] at hNFw hroom
  rw [hr2] at hcan
  set D := c.nreg 110000 with hDdef
  set NB := c.nreg 110001 with hNBdef
  set γ := c.nreg 110002 with hγdef
  set A₀ := c.nreg ALLOC with hA₀def
  have hAl : ztdxq := rfl
  zuc
  zuiwp
  zulm
  have hA0 := arcs_pos hsimp hN
  have hNF := hNFw.nfAt
  zueav
  obtain ⟨-, -, -, hsl⟩ := hall H C hD
  have hW8 : ztiya := by
    have := C.m_lt; rw [hCQ, hQn] at this; have := C.one_le; unfold hostWords at hHW; omega
  -- the parameters
  have hcK := hNF.1
  have hcm : c.nmem _ = C.m := hD.2.2.2.1
  rw [hcK, hcm] at hroom
  have hγ1 := gamma_pos hsimp hcan
  have hK23 : N.chords.length ≤ 60 * ztz := by
    have := chords_mul_le hsimp hcan; nlinarith
  zubb
  have hRK1 := regions_eq hsimp hN
  have hA5 : N.arcs.length ≤ 5 * (N.chords.length + 1) := by
    zujyh
    omega
  set X := N.chords.length * (Nat.clog 2 C.m + 1) + 1 with hX
  set F := Fb N.chords.length with hF
  have hFX : F ≤ 40 * X := Fb_le hm1 hK23
  have hF1 := one_le_Fb N.chords.length
  have hKF := K_le_Fb N.chords.length
  have hroomF : A₀ + 50000000000 * F ≤ W := by
    have : κq * X ≤ W - A₀ := by_omega
    unfold κq at this; omega
  have hLF : Nat.clog 2 ztbbt ≤ F := clog_le_Fb by_omega
  have hALF : N.arcs.length * (Nat.clog 2 ztbbt + 1) ≤ 5 * F := mul_clog_le_Fb hA5 by_omega
  have hs500 : SortR.sortCost 500 N.chords.length ≤ 530 * ztdko := sortCost_le by_omega
  have hs20A : SortR.sortCost 20 ztgce ≤ 50 * ztdko := sortCost_le by_omega
  -- phase A
  obtain ⟨cA, kA, eA, hkA, FA, ch1, ch2, mdle, a9A, PLA, r25, r23, r24, r49, r205, r26, m0A, mdcA,
      tbA, lA, tabA, Alt, Klt, posA, pfA, pkA, chltA, chinjA, chsA⟩ :=
    phA_exec (P := P) hw hG hW8 hD hCQ hsl hNFw hN hAl hDA by_omega
  set MD := cA.nreg 120040 with hMD
  set CH := cA.nreg 120038 with hCH
  set A₁ := cA.nreg 9999 with hA₁
  have agA : ∀ a, a < A₀ → cA.nmem a = c.nmem a := FA.2.2.1
  -- phase B
  obtain ⟨cB, kB, eB, hkB, GB, k12B, alB1, alB2, CH1, CH2, Dl, hCH1, v1, v2, v8, v34, v37,
      pairsB, hC1, hC2, hnd, hmem, hDl⟩ :=
    phB_exec (P := P) (c := cA) eA.wb_right hG hHW hCQ hsl hD ztont hNFw hN agA PLA r205 pkA
      m0A mdcA by_omega tbA (by rw [lA]; omega) by_grind rfl
      by_omega
      by_omega
  rw [lA] at hkB
  set AB := cB.nreg ALLOC with hAB
  have hAB9 : cB.nreg 9999 = AB := rfl
  -- the book
  set B : BookData := ⟨N.arcs.length + 3, starList ztfii N.arcs.length, Dl⟩ with hB
  have hgok : GraphOK C _ N B := graphOK_of hN hsimp hnd hmem
  have hBN : B.N = N.arcs.length + 3 := rfl
  have hBE : B.E = N.arcs.length + 3 + (starList ztfii N.arcs.length ++ Dl).length := by
    show N.arcs.length + 3 + (starList _ N.arcs.length).length + Dl.length = _
    rw [List.length_append]; ring
  have hstarA : (starList ztfii N.arcs.length).length ≤ N.arcs.length := starList_length _ _
  have hBE8 : B.E ≤ 4 * N.arcs.length + 8 := by rw [hBE, List.length_append]; omega
  have hs20E : SortR.sortCost 20 ztbck ≤ 50 * ztdko := sortCost_le by_omega
  have hcl : clCost B.N B.E ≤ Cluster.clusterK * ztdko :=
    clCost_le by_grind
  have hclK : Cluster.clusterK = 200000 := rfl
  rw [hclK] at hcl
  have b11 : cB.nreg 120011 = 1 := by rw [k12B _ by_norm_num by_norm_num, PLA.one]
  have b12 : cB.nreg 120012 = 0 := by rw [k12B _ by_norm_num by_norm_num, PLA.zero]
  have b48 : cB.nreg 120048 = 2 := by rw [k12B _ by_norm_num by_norm_num, PLA.two]
  have b39 : cB.nreg 120039 = N.chords.length := by rw [k12B _ by_norm_num by_norm_num, PLA.rK]
  obtain ⟨cK, kK, eK, hkK, GK, k12K, v34K, alK1, alK2, hFLa, hLABa, hFLb, hLABb, hclF⟩ :=
    bookS_exec (P := P) (c := cB) eB.wb_right hG hCQ hcan hgok rfl v1 v2 v8 v34
      by_grind b11 b12 b48 b39 rfl pairsB
      by_grind
      by_grind
      by_omega by_omega by_omega
  set FL := cK.nreg 130004 with hFLd
  set LAB := cK.nreg 130005 with hLABd
  set AK := cK.nreg ALLOC with hAK
  have hAK9 : cK.nreg 9999 = AK := rfl
  have hs20μ : SortR.sortCost 20 ztenj ≤ 50 * ztdko := sortCost_le by_omega
  have hs20N : SortR.sortCost 20 B.N ≤ 50 * ztdko := hs20μ
  -- the order by label
  obtain ⟨cO, kO, eO, hkO, FO, alO1, alO2, KO, memO, hDLO, hORDO, hRKO, hordF⟩ :=
    ordStage_exec (P := P) (c := cK) eK.wb_right v34K rfl rfl
      (by rw [k12K _ by_norm_num by_norm_num, b11]) rfl hFLb hLABb
      by_omega
  set O := cO.nreg ALLOC with hOd
  have hO9 : cO.nreg 9999 = O := rfl
  -- the header
  obtain ⟨cH, kH, eH, hkH, h3H, h9H, RH, hdrH, hdr3, memH, rrH, rmH, oH⟩ :=
    hdrS_exec (P := P) (c := cO) (O := O) eO.wb_right rfl
      (by rw [FO.1 _ by_decide by_decide,
        k12K _ by_norm_num by_norm_num, b11]) by_omega
  -- the payment
  have hH26 : cH.nreg 120026 = A₀ := by
    rw [RH _ by_decide by_decide by_decide by_decide,
      FO.1 _ by_decide by_decide,
      k12K _ by_norm_num by_norm_num, k12B _ by_norm_num by_norm_num, r26]
  have hH11 : cH.nreg 120011 = 1 := by
    rw [RH _ by_decide by_decide by_decide by_decide,
      FO.1 _ by_decide by_decide,
      k12K _ by_norm_num by_norm_num, b11]
  obtain ⟨cP, kP, eP, hkP1, hkP2, RP, mP, rrP, rmP, oP⟩ := payS_exec (P := P) (c := cH) eH.wb_right
    hH26 h9H hH11
  have ex : Exec P W prepMainS c cP _ := .seq eA (.seq eB (.seq eK (.seq eO (.seq eH eP))))
  -- register facts of the end configuration
  have kO12 : ∀ r, 120010 ≤ r → r ≤ 120049 → cO.nreg r = cA.nreg r := fun r a b => by
    rw [FO.1 r ztdgx by_omega,
      k12K r a b, k12B r a b]
  have hP9 : cP.nreg ALLOC = O + 18 := by rw [hAL, RP _ by_decide by_decide, h9H]
  have hP3 : cP.nreg 110003 = O := by rw [RP _ by_decide by_decide, h3H]
  -- memory transports
  have mPH : ∀ a, cP.nmem a = cH.nmem a := fun a => by rw [mP]
  have mHO := fun a ha => memH a ztbbu
  have mOK : ∀ a, a < AK → cO.nmem a = cK.nmem a := memO
  have mKB : ∀ a, a < AB → cK.nmem a = cB.nmem a := GK.2.2.1
  have mBA : ∀ a, a < A₁ → cB.nmem a = cA.nmem a := GB.2.2.1
  have hA₁B : A₁ ≤ AB := by_omega
  have hABK : AB ≤ AK := alK1
  have hAKO : AK ≤ O := alO1
  have mPA : ∀ a, a < A₁ → cP.nmem a = cA.nmem a := fun a ha => by
    rw [mPH, mHO a by_omega, mOK a by_omega, mKB a by_omega, mBA a ha]
  have mP0 : ∀ a, a < A₀ → cP.nmem a = c.nmem a := fun a ha => by
    rw [mPA a by_omega, agA a ha]
  have mPO : ∀ a, a < O → cP.nmem a = cO.nmem a := fun a ha => by rw [mPH, mHO a ha]
  have mPK : ∀ a, a < AK → cP.nmem a = cK.nmem a := fun a ha => by
    rw [mPO a by_omega, mOK a ha]
  -- the cost
  have hz : 2 * N.arcs.length * (5500 * ztymm + 410) = 11000 * (N.arcs.length * ztymm) + 820 * N.arcs.length := by_ring
  have hkPE := hkP1
  have hEk := hkP2
  have hsubO : O + 18 - A₀ + A₀ = O + 18 := Nat.sub_add_cancel by_omega
  refine ⟨cP, _, ex, ?_, ?_, ?_⟩
  · -- the cost bound
    show _ ≤ κq * (c.nmem NB * (Nat.clog 2 (c.nmem ztmo) + 1) + 1)
    rw [hcK, hcm]
    have hk : kA + (kB + (kK + (kO + (kH + kP)))) ≤ 100000000 * F := by
      zvncr at hkB
      unfold κq at *
      omega
    unfold κq; nlinarith
  · -- the post-condition
    refine ⟨by show A₀ ≤ cP.nreg 110003; zuozx; omega,
      (by show cP.nreg 110003 + 3 ≤ _; omega), ?_, ?_, ?_, fun m' hm' => ?_⟩
    · show cP.nmem ztvku = c.nreg 110000
      rw [hP3, mPH, show O = O + 0 from rfl, hdrH 0 by_norm_num by_norm_num]
      show cO.nreg 120013 = _
      rw [kO12 _ by_norm_num by_norm_num, PLA.rD]
    · show cP.nmem (cP.nreg 110003 + 1) = c.nreg 110001
      rw [hP3, mPH, hdrH 1 by_norm_num by_norm_num]
      show cO.nreg 120014 = _
      rw [kO12 _ by_norm_num by_norm_num, PLA.rNB]
    · show cP.nmem (cP.nreg 110003 + 2) = c.nreg 110002
      rw [hP3, mPH, hdrH 2 by_norm_num by_norm_num]
      show cO.nreg 120049 = _
      rw [kO12 _ by_norm_num by_norm_num, r49]
    · show OAt P m' ztvku
      zuozx
      rw [hP9] at hm'
      refine ⟨O + 18, by rw [hm' _ by_omega, mPH, hdr3], by_omega, ?_⟩
      refine Robust.transport ?_ hm'
      refine qat_of (m := cP.nmem) (m₀ := c.nmem) (A₀ := A₀) (D := D) (NB := NB) (γ := γ) (O := O)
        (E := O + 18) (H := H) (C := C) (N := N) (B := B) (k := cK.nreg 60090)
        (POS := cA.nreg 120031) (FL := FL) (LAB := LAB) (DL := cO.nreg 60100)
        (nD := cO.nreg 60102) (ORD := cO.nreg 60007) (RK := cO.nreg 60110) (CH := CH) (MD := MD)
        (TB := cA.nreg 120041) (L := (Nat.clog 2 ztbbt)) (Vc := qvOf cA) hG hCQ hD ztont hNFw hcan mP0
        ?_ rfl by_omega ch2 tbA by_omega (by rw [posA, tbA]; omega)
        by_omega by_omega hDLO hORDO hRKO
        (by zunpu; omega)
        (fun i hi => by zunpu; exact mdcA i hi)
        (fun j hj => by rw [mPA _ (by rw [a9A, tbA]; omega)]; exact tabA j hj)
        Alt Klt rfl
        (fun j hj => by rw [mPA _ (by rw [a9A, posA, tbA]; omega)]; exact pfA j hj)
        (fun q hq => by zunpu; exact chltA q hq)
        (fun q q' hq hq' e => by
          rw [mPA _ by_omega, mPA _ by_omega] at e
          exact chinjA q q' hq hq' e)
        ⟨PLA.rCB, by show cA.nreg 120016 = _; rw [PLA.rm, hcm],
          by show cA.nreg 120015 = _; rw [PLA.rs, hD.2.2.1],
          by show cA.nreg 120022 = _; rw [PLA.tv, hD.2.2.1, hD.2.2.2.2.1]⟩
        (fun q q' hqq hq' => by
          rw [mPA _ by_omega, mPA _ by_omega]
          exact chsA q q' hqq hq')
        hgok rfl (hclF.mono mPK hFLb hLABb)
        (hordF.mono mPO (by rw [hBN] at hFLb; omega) (by rw [hBN] at hLABb; omega) hDLO hORDO
          hRKO)
      -- the header words
      zug
      rw [mPH]
      by_cases h3 : i = 3
      · subst h3; rw [hdr3]; rfl
      by_cases h17 : i = 17
      · subst h17
        rw [hdrH 17 hi h3]
        simp only [hdrRegs, hdrVals, List.getD_cons_zero, List.getD_cons_succ]
        rw [KO _ by_rfl (by unfold OKeep; omega)]; omega
      · rw [hdrH i hi h3]
        interval_cases i <;> simp only [hdrRegs, hdrVals, List.getD_cons_zero,
          List.getD_cons_succ] <;>
          first
            | rfl
            | exact absurd rfl h3
            | exact absurd rfl h17
            | (rw [kO12 _ by_norm_num by_norm_num]
               all_goals first
                 | exact PLA.rD
                 | exact PLA.rNB
                 | exact r49
                 | exact PLA.rA
                 | exact PLA.rK
                 | exact lA
                 | rfl)
            | (rw [FO.1 _ by_decide by_decide])
  · -- the frame
    have hS : ∀ S, S ⊆ prepBands → ∀ r, bandOf r ∉ prepBands → bandOf r ∉ S :=
      fun S hS r hr h => hr ztqpn
    refine ⟨fun r hr hra => ?_, fun r hr => ?_, by_omega, fun a ha => ?_, ?_, ?_, ?_⟩
    · have h11 : bandOf r ≠ 11 := fun h => hr (by simp [prepBands, bOPrep, h])
      unfold bandOf at h11
      rw [RP r by_omega by_omega, RH r by_omega by_omega by_omega by_omega,
        FO.1 r ztcil hra, GK.1 r ztcil hra,
        GB.1 r ztcil hra, FA.1 r ztcil hra]
    · rw [rrP, rrH, FO.2.1 r ztcil, GK.2.1 r ztcil,
        GB.2.1 r ztcil, FA.2.1 r ztcil]
    · rw [rmP, rmH, FO.2.2.2.1 a by_omega, GK.2.2.2.1 a by_omega,
        GB.2.2.2.1 a by_omega, FA.2.2.2.1 a ha]
    · rw [oP, oH, FO.2.2.2.2, GK.2.2.2.2, GB.2.2.2.2, FA.2.2.2.2]
    · zuksy
    · zuksy

/-- **The oracle of Lemma 3.6.** -/
noncomputable def lemma36Oracle : OracleIface where
  At := OAt
  prep := prepMainS
  query := qry
  bands := prepBands
  κ := κq

/-- **Lemma 3.6** (WP-H): the oracle is valid. -/
theorem lemma36Oracle_valid : lemma36Oracle.Valid :=
  ⟨prepBands_sub, prep_meets,
    query_meets ⟨by_decide, by_decide, by_decide⟩ le_rfl⟩
end
end OracleR
public section

/-- **WP-H: the Lemma 3.6 oracle.** -/
theorem oracleSpec : OracleSpec := ⟨OracleR.lemma36Oracle, OracleR.lemma36Oracle_valid⟩
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft)
open WalkEmbed
namespace Sweep
def Btw (p q r : ℝ) : Prop := (p < r ∧ r < q) ∨ (q < r ∧ r < p)
theorem Btw.symm {p q r : ℝ} (h : Btw p q r) : Btw q p r := Or.symm h

/-- **Four points on a line**: `x`, `y` are on different sides of the interval `(a, b)` iff
exactly one of `a`, `b` lies between `x` and `y`. -/
theorem xor_btw {a b x y : ℝ} (hab : a < b) (hxy : x ≠ y) (hxa : x ≠ a) (hxb : x ≠ b)
    (hya : y ≠ a) (hyb : y ≠ b) :
    (ztnqr ↔ ¬ zthdk) ↔ (Btw x y a ↔ ¬ Btw x y b) := by
  unfold Btw
  grind

/-- **Separation as betweenness of offsets.**  For keys on a cycle of length `n`, measured by
offsets from a base `g`: the interval `(a, b)` separates `x` from `y` iff exactly one of `a`, `b`
lies strictly between `x` and `y` in offsets. -/
theorem sep_iff_btw {n g a b x y : ℝ} (hg : 0 ≤ g) (hgn : g < n) (ha : 0 ≤ a) (han : a < n)
    (hb : 0 ≤ b) (hbn : b < n) (hx : 0 ≤ x) (hxn : x < n) (hy : 0 ≤ y) (hyn : y < n)
    (hab : a ≠ b) (hxy : x ≠ y) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) :
    (sideInArc a b x ↔ ¬ sideInArc a b y) ↔
      (Btw zthzb ztrub ztlrl ↔ ¬ Btw zthzb ztrub ztlrm) := by
  have hne : ztcrn :=
    fun hu hun hw hwn huw h => huw ztmmt
  have hoab := hne ha han hb hbn hab
  have hoxy := hne hx hxn hy hyn hxy
  have hoxa := hne hx hxn ha han hxa
  have hoxb := hne hx hxn hb hbn hxb
  have hoya := hne hy hyn ha han hya
  have hoyb := hne hy hyn hb hbn hyb
  rcases lt_or_gt_of_ne hoab with h | h
  · rw [sideInArc_iff_off hg hgn ha han hb hbn hx hxn h,
      sideInArc_iff_off hg hgn ha han hb hbn hy hyn h]
    exact xor_btw h hoxy hoxa hoxb hoya hoyb
  · rw [Chazelle.Chain.sideInArc_swap hab hxa hxb, Chazelle.Chain.sideInArc_swap hab hya hyb,
      sideInArc_iff_off hg hgn hb hbn ha han hx hxn h,
      sideInArc_iff_off hg hgn hb hbn ha han hy hyn h]
    have key := xor_btw h hoxy hoxb hoxa hoyb hoya
    grind

/-! ## Endpoints of admissible chords -/

/-- A point of an admissible chord outside the domain is an endpoint. -/
theorem end_of_not_mem {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) :
    ∃ a b : Point, a ≠ b ∧ c = Chazelle.segment a b ∧
      ∀ x ∈ c, x ∉ M.D → x = a ∨ x = b := by
  obtain ⟨a, b, hab, hcab, -, hopen, -, -⟩ := hM.ends c hc
  refine ⟨a, b, hab, hcab, fun x hx hxD => ?_⟩
  zugdr
  zufr
  zunm
  · zuji
    · simp_all
    simp_all
  · zuhhb

/-- An admissible chord inside another one containing both endpoints of the latter is equal to
it. -/
theorem eq_of_ends {M M₂ : Model} (hM : WalkAx M) (hM₂ : WalkAx M₂) {e c : Set Point}
    (he : e ∈ M.Adm) (hc : c ∈ M₂.Adm) (hec : e ⊆ c) {q y : Point} (hqy : q ≠ y) (hq : q ∈ e)
    (hy : y ∈ e) (hqD : q ∉ M₂.D) (hyD : y ∉ M₂.D) : e = c := by
  obtain ⟨a, b, hab, hcab, hend⟩ := end_of_not_mem hM₂ hc
  obtain ⟨a1, b1, -, heab, -⟩ := end_of_not_mem hM he
  have hqc := hend q (hec hq) hqD
  have hyc := hend y (hec hy) hyD
  have hconv : Convex ℝ e := by rw [heab]; exact Geometry.segment_convex _ _
  refine Set.Subset.antisymm hec ?_
  zummz
  rcases hqc with rfl | rfl <;> rcases hyc with rfl | rfl
  · simp_all
  · exact Geometry.segment_subset_of_convex hconv hq hy
  · exact Geometry.segment_subset_of_convex hconv hy hq
  simp_all

/-! ## Two walks agreeing along two pieces -/

/-- **A correspondence** between the walk of a model `M` (read from the vertex `g`) and the walk
of a model `M₂` (read from `g'`): they agree along a first piece of length `L1` and, after a gap of
`δ` walk vertices of `M₂` (the box of `C₂`, when `δ > 0`), along a second piece of length `L2`.
Chords of `S` (in `M₂`) through walk points of `M₂` other than the base point contain chords of
`F` (in `M`) through the same point; when there is a gap, a chord of `F` is attached at the split
vertex of `M` and has its other attachments outside the stretch; distinct chords of `F` are not
nested. -/
structure Corr (M M₂ : Model) (F S : Set ztf) (g g' L1 L2 δ : ℕ) : Prop where
  hM : WalkAx M
  hM₂ : WalkAx M₂
  hF : F ⊆ M.Adm
  hfin : F.Finite
  hS : S ⊆ M₂.Adm
  hSfin : S.Finite
  hg : g < M.W.n
  hg' : g' < M₂.W.n
  hL : L1 + L2 ≤ M.W.n
  hL₂ : L1 + δ + L2 ≤ M₂.W.n
  hδ : δ = 0 → L2 = 0
  hfull : 0 < δ → L1 + δ + L2 = M₂.W.n
  A1 : Agree M.W M₂.W g g' L1
  A2 : Agree M.W M₂.W zttkm ztdok L2
  noV : ∀ p < M₂.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → 0 < off M₂.W.n g' ztk →
    off M₂.W.n g' ztk < L1 + δ + L2 → sidePt M₂.W p t ≠ M₂.W.vtx g'
  trans : ∀ c ∈ S, ∀ q ∈ c, q ∉ M₂.D → q ≠ M₂.W.vtx g' → ∃ e ∈ F, q ∈ e ∧ e ⊆ c
  box : 0 < δ → ∃ e ∈ F, SideAttach M.W e ztbxk 0 ∧ ∀ (p : ℕ) (t : ℝ),
    SideAttach M.W e p t → sidePt M.W p t ≠ sidePt M.W ztbxk 0 →
      ¬ (0 < off M.W.n g ztk ∧ off M.W.n g ztk < L1 + L2)
  nest : ∀ e ∈ F, ∀ e' ∈ F, e ⊆ e' → e = e'

/-- The offset in the walk of `M₂` of the offset `d` of the walk of `M`. -/
def dq (L1 δ d : ℕ) : ℕ := if d < L1 then d else d + δ
namespace Corr
variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}
end Corr

/-! ## Collapsing the gap -/

/-- The offset of the walk of `M` corresponding to the offset `o` of the walk of `M₂` (the gap
`[L1, L1 + δ]` collapses to `L1`). -/
noncomputable def psi (L1 δ : ℕ) (o : ℝ) : ℝ :=
  if o ≤ L1 then o else if o ≤ (L1 : ℝ) + δ then L1 else o - δ
theorem psi_dq {L1 δ d : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    psi L1 δ ztnb = d + t := by
  unfold psi dq
  by_cases h : d < L1
  · rw [ite_eq_left h, ite_eq_left]
    zuhvb

  · zubme
    push_cast
    have hL : ztpgo := by_simp_all
    grind
theorem psi_mono {L1 δ : ℕ} {o o' : ℝ} (h : o ≤ o') : psi L1 δ o ≤ psi L1 δ o' := by
  zuhfw

  grind

/-- The gap of the walk of `M₂`. -/
def InGap (L1 δ : ℕ) (o : ℝ) : Prop := (L1 : ℝ) ≤ o ∧ o ≤ (L1 : ℝ) + δ
theorem psi_strict {L1 δ : ℕ} {o o' : ℝ} (h : o < o') (hg : ¬ InGap L1 δ o ∨ ¬ InGap L1 δ o') :
    psi L1 δ o < psi L1 δ o' := by
  zuhfw

  rcases hg with hg | hg <;> (unfold InGap at hg; push Not at hg) <;> split_ifs <;>
    first
    | linarith
    | (by_contra hc; push Not at hc; have := hg by_linarith; linarith)
theorem btw_psi {L1 δ : ℕ} {a b o : ℝ} (ha : ¬ InGap L1 δ a) (hb : ¬ InGap L1 δ b)
    (h : Btw a b o) : Btw ztrum ztrun ztruo := by
  zuwr
  · exact Or.inl ⟨psi_strict h1 ztbbu, psi_strict h2 (Or.inr hb)⟩
  · exact Or.inr ⟨psi_strict h1 ztvby, psi_strict h2 (Or.inr ha)⟩
theorem btw_of_psi {L1 δ : ℕ} {a b o : ℝ} (h : Btw ztrum ztrun ztruo) :
    Btw a b o := by
  zuwr
  · left
    constructor
    · zuhd
    · zuhd
  · right
    constructor
    · zuhd
    · zuhd
theorem not_inGap_dq {L1 δ d : ℕ} {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ¬ InGap L1 δ ztnb := by
  unfold InGap dq
  zubf
  split_ifs at h1 h2 with h
  · zuhvb

  · push_cast at h1 h2
    have : ztpgo := by_simp_all
    linarith
namespace Corr
variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}
end Corr
namespace Corr
variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}
end Corr
namespace Corr
variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}

/-- Keys of walk positions lie in `[0, n)`. -/
theorem key_mem {W : Polygon} {p : ℕ} (hp : p < W.n) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < W.n := by
  have : ztmrl := by exact_mod_cast hp
  grind
end Corr
end Sweep
end
end Chazelle.Core
section
set_option hygiene false
local macro "zqvm" : tactic => `(tactic| (have hL1pos : ztpgf := by zunfo
                                          have hne : ztkzb := by intro h; zupdn
                                          zuixz
                                          have hg'n : ztixg := by exact_mod_cast hC.hg'))
local macro "zqvn" : tactic => `(tactic| (have hfull := hC.hfull hδ
                                          have hL1n : L1 < M₂.W.n := by_omega
                                          have hdq : dq L1 δ d = d := by unfold dq; simp_all
                                          have hdq' : dq L1 δ d' = d' + δ := by unfold dq; simp_all))
local macro "zqvo" : tactic => `(tactic| (by_contra hlt; push Not at hlt))
local macro "zqvp" : tactic => `(tactic| obtain ⟨hp2, ht2⟩ := hC.key_of_off₂ (L := L1 + δ) by_omega hA.1 hA.2.1 hA.2.2.1 le_rfl one_pos by_grind)
local macro "zqvq" : tactic => `(tactic| obtain ⟨hp1, ht1⟩ := hC.key_of_off₂ (L := L1 + δ) by_omega hA₁.1 hA₁.2.1 hA₁.2.2.1 le_rfl one_pos by_grind)
local macro "zqvr" : tactic => `(tactic| rcases Nat.eq_zero_or_pos δ with h | h)
local macro "zqvs" : tactic => `(tactic| (have hLdr : (L1 : ℝ) ≤ d' := by_simp_all
                                          have hδr : (1 : ℝ) ≤ δ := by exact_mod_cast hδ))
local macro "zqvt" : tactic => `(tactic| (rintro rfl
                                          rcases attach_third hC.hM₂ (hC.hS hc) hA₁ hB₁ hAB₁ hB with ⟨h1, h2⟩ | ⟨h1, h2⟩))
local macro "zqvu" : tactic => `(tactic| (have hn₂ := hC.n₂_pos
                                          have hd : d < L1 + L2 := by_omega
                                          have hL2 : 0 < L2 := by_omega))
local macro "zqvv" : tactic => `(tactic| (have hB₁' := hB₁
                                          have hA'' := hA
                                          rw [hp1, ht1] at hB₁'
                                          rw [hp2, ht2] at hA''))
local macro "zqvw" : tactic => `(tactic| (have hA₁' := hA₁
                                          have hA'' := hA
                                          rw [hp1, ht1] at hA₁'
                                          rw [hp2, ht2] at hA''))
local macro "zqvx" : tactic => `(tactic| rintro c' hc' ⟨pa', pb', ta', tb', hA', hB', hAB', hiff'⟩)
local macro "zqvy" : tactic => `(tactic| obtain ⟨p₃, t₃, hA₃, hne₃⟩ := WalkAx.other_attach hC.hM ztfhs hAe)
local macro "zqvz" : tactic => `(tactic| obtain ⟨e', he', hqe', hec'⟩ := hC.trans c' hc' _ hA₁.2.2.2.1 hqD₀ hnoV)
local macro "zqwa" : tactic => `(tactic| have : (d : ℝ) + 1 ≤ L1 + L2 := by exact_mod_cast hd)
local macro "zqwb" : tactic => `(tactic| have : (d' : ℝ) + 1 ≤ L1 + L2 := by exact_mod_cast hd')
local macro "zqwc" : tactic => `(tactic| have hec' := eq_of_ends hC.hM hC.hM₂ heF hcS hec ztnr hqe hA₃.2.2.2.1 hqD hy₃D)
local macro "zqwd" : tactic => `(tactic| (have : ztgtl := by exact_mod_cast hdL
                                          zupdo))
local macro "zqwe" : tactic => `(tactic| rcases hin' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith)
set_option hygiene true

/-!
# The sweep (WP-D), part 4b: lemma (K) up to the gap (ties at the top, F2)

With a tie at the top of the chain of `M₂` (design doc §9.10) there may be no chord of `F`
separating the positions of the stretch before the gap from those after it, and lemma (K) fails
in general.  It survives up to the two regions of `S` at the sides of the gap: if two positions
of the stretch face the same region of `F` and their counterparts face different regions of `S`,
then the gap lies between them, the position before the gap has the region faced just after the
split vertex `(g' + L1)` of `M₂` (`AfterFaces`), and the position after the gap the region faced
just before `(g' + L1 + δ)` (`BeforeFaces`).

The gap facts needed (`CorrGap`, proved for a junction in `SweepLabelJ`):
* a chord of `S` attached strictly inside the gap meets the stretch in at most one point;
* at each copy of the split vertex of `M₂` at most one chord of `S` is attached;
* a chord of `F` through the split vertex of `M` is attached there.

* `sideInArc_rev_iff_off`, `no_cross_off`, `eventually_not_cut_after/before`: walk order and
  cuts in offsets (moved here from `SweepBracket`, `SweepQuery`).
* `label_gen3`: the generic lemma (K3).
-/
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft)
open WalkEmbed
namespace Sweep
theorem sideInArc_rev_iff_off {n g u w x : ℝ} (_hg : 0 ≤ g) (_hgn : g < n) (hu : 0 ≤ u)
    (hun : u < n) (hw : 0 ≤ w) (hwn : w < n) (hx : 0 ≤ x) (hxn : x < n)
    (huw : off n g u < off n g w) :
    sideInArc w u x ↔ off n g x < off n g u ∨ off n g w < off n g x := by
  unfold off at *
  zuiq

/-- **Non-crossing in offsets.**  If one attachment of a chord `d` lies strictly between the two
attachments of a chord `c` (in offsets from `g`), so does (weakly) every other attachment of
`d`. -/
theorem no_cross_off {M : Model} (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c d : Set Point} (hc : c ∈ F) (hd : d ∈ F) (hcd : c ≠ d)
    {pa pb px py : ℕ} {ta tb tx ty : ℝ} (hA : SideAttach M.W c pa ta)
    (hB : SideAttach M.W c pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    (hX : SideAttach M.W d px tx) (hY : SideAttach M.W d py ty) {g : ℝ} (hg0 : 0 ≤ g)
    (hgn : g < M.W.n) (hab : off M.W.n g ztbf < off M.W.n g ztbd)
    (hx1 : off M.W.n g ztbf < off M.W.n g ztcat)
    (hx2 : off M.W.n g ztcat < off M.W.n g ztbd) :
    off M.W.n g ztbf ≤ off M.W.n g ztdhy ∧
      off M.W.n g ztdhy ≤ off M.W.n g ztbd := by
  zucu

  obtain ⟨x0, x1⟩ := Corr.key_mem hX.1 hX.2.1 hX.2.2.1
  obtain ⟨y0, y1⟩ := Corr.key_mem hY.1 hY.2.1 hY.2.2.1
  zubqk
  have hy : off M.W.n g ztdhy < off M.W.n g ztbf ∨
      off M.W.n g ztbd < off M.W.n g ztdhy := by
    grind
  apply hM.no_cross hF hfin hc hd hcd hA hB hAB hX hY
  exact ⟨(sideInArc_iff_off hg0 hgn a0 a1 b0 b1 x0 x1 hab).2 by_simp_all,
    (sideInArc_rev_iff_off hg0 hgn a0 a1 b0 b1 y0 y1 hab).2 hy⟩
section NonCut
variable {M : Model}

/-- The keys just after a key are not cuts. -/
theorem eventually_not_cut_after (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (x : ℝ) : ∀ᶠ s in 𝓝[>] (0 : ℝ), ¬ M.IsCut F ztkgy := by
  zubap
  have h := (Filter.eventually_all_finite hK (l := 𝓝[>] (0 : ℝ))
    (p := fun y s => x + s ≠ y)).2 fun y _ => by
      zuiei
      · zusq
        grind
      · zuhde

  grind

/-- The keys just before a key are not cuts. -/
theorem eventually_not_cut_before (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (x : ℝ) : ∀ᶠ s in 𝓝[>] (0 : ℝ), ¬ M.IsCut F ztfvh := by
  zubap
  have h := (Filter.eventually_all_finite hK (l := 𝓝[>] (0 : ℝ))
    (p := fun y s => x - s ≠ y)).2 fun y _ => by
      zuieh
      · zusq
        grind
      · zuhdd

  grind
end NonCut

/-! ## Faced regions just after and just before a position -/

/-- The positions just after `(p, t)` (on the same walk edge) face `U`. -/
def AfterFaces (M : Model) (p : ℕ) (t : ℝ) (U : Set Point) : Prop :=
  ∃ δ > (0 : ℝ), ∀ s, 0 < s → s < δ → t + s < 1 → M.Faces p ztuf U

/-- The positions just before `(p, t)` (on the same walk edge if `0 < t`, on the previous one if
`t = 0`) face `U`. -/
def BeforeFaces (M : Model) (p : ℕ) (t : ℝ) (U : Set Point) : Prop :=
  ∃ δ > (0 : ℝ), (0 < t → ∀ s, 0 < s → s < δ → s < t → M.Faces p ztfuw U) ∧
    (t = 0 → ∀ s, 0 < s → s < δ → M.Faces ztcm zteb U)

/-! ## Correspondences without a separating chord -/

/-- **A correspondence without a separating chord at the gap** (F2, `Corr` minus `box`) between the walk of a model `M` (read from the vertex `g`) and the walk
of a model `M₂` (read from `g'`): they agree along a first piece of length `L1` and, after a gap of
`δ` walk vertices of `M₂` (the box of `C₂`, when `δ > 0`), along a second piece of length `L2`.
Chords of `S` (in `M₂`) through walk points of `M₂` other than the base point contain chords of
`F` (in `M`) through the same point; distinct chords of `F` are not nested.  (The gap needs no
separating chord: with ties at the top of the chain of `M₂` there may be none, and lemma (K)
holds up to the two regions at the sides of the gap, `SweepLabelGap.label_gen3`.) -/
structure Corr0 (M M₂ : Model) (F S : Set ztf) (g g' L1 L2 δ : ℕ) : Prop where
  hM : WalkAx M
  hM₂ : WalkAx M₂
  hF : F ⊆ M.Adm
  hfin : F.Finite
  hS : S ⊆ M₂.Adm
  hSfin : S.Finite
  hg : g < M.W.n
  hg' : g' < M₂.W.n
  hL : L1 + L2 ≤ M.W.n
  hL₂ : L1 + δ + L2 ≤ M₂.W.n
  hδ : δ = 0 → L2 = 0
  hfull : 0 < δ → L1 + δ + L2 = M₂.W.n
  A1 : Agree M.W M₂.W g g' L1
  A2 : Agree M.W M₂.W zttkm ztdok L2
  noV : ∀ p < M₂.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → 0 < off M₂.W.n g' ztk →
    off M₂.W.n g' ztk < L1 + δ + L2 → sidePt M₂.W p t ≠ M₂.W.vtx g'
  trans : ∀ c ∈ S, ∀ q ∈ c, q ∉ M₂.D → q ≠ M₂.W.vtx g' → ∃ e ∈ F, q ∈ e ∧ e ⊆ c
  nest : ∀ e ∈ F, ∀ e' ∈ F, e ⊆ e' → e = e'
namespace Corr0
variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}
theorem n_pos (hC : Corr0 M M₂ F S g g' L1 L2 δ) : 0 < M.W.n := by have := hC.hg; omega
theorem n₂_pos (hC : Corr0 M M₂ F S g g' L1 L2 δ) : 0 < M₂.W.n := by have := hC.hg'; omega
theorem dq_lt (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) :
    dq L1 δ d < M₂.W.n := by
  have := hC.hL₂; unfold dq; grind

/-- Agreeing points. -/
theorem sidePt_eq (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) (t : ℝ) :
    sidePt M.W ztwje t = sidePt M₂.W ztuj t := by
  zujql
  zus
  · exact hC.A1.sidePt_eq h t
  · have := hC.A2.sidePt_eq (d := d - L1) by_omega t
    rwa [show g + L1 + ztduf = g + d by omega,
      show g' + L1 + δ + ztduf = g' + ztjtf by omega] at this

/-- Agreeing attachments (away from the base and the split vertex). -/
theorem attach_iff (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) {t : ℝ}
    (hsec : t = 0 → d ≠ 0 ∧ d ≠ L1) (c : Set Point) :
    SideAttach M.W c ztwje t ↔ SideAttach M₂.W c ztuj t := by
  zujql
  zus
  · exact hC.A1.sideAttach_iff hC.n_pos hC.n₂_pos h (fun h0 => by
      grind) c
  · have := hC.A2.sideAttach_iff hC.n_pos hC.n₂_pos (d := d - L1) by_omega (t := t)
      ztlod c
    rwa [show g + L1 + ztduf = g + d by omega,
      show g' + L1 + δ + ztduf = g' + ztjtf by omega] at this

/-- The offset of a position of the stretch of `M`. -/
theorem off_M (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    off M.W.n g ztwjt = d + t :=
  off_key hC.hg (by have := hC.hL; omega) ht ht1

/-- The offset of the corresponding position of `M₂`. -/
theorem off_M₂ (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    off M₂.W.n g' ztydh = dq L1 δ d + t :=
  off_key hC.hg' (hC.dq_lt hd) ht ht1

/-- **Transfer of an attachment** from `M₂` to `M` along the stretch. -/
theorem transfer (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ L1) {c : Set Point} (hc : c ∈ S)
    (hA : SideAttach M₂.W c ztuj t) :
    ∃ e ∈ F, e ⊆ c ∧ sidePt M.W ztwje t ∈ e ∧
      SideAttach M.W e ztwje t := by
  have hpos : 0 < (dq L1 δ d : ℝ) + t := by
    zukmi
    · grind
    · have hd0 := (hsec h.symm).1
      have : 1 ≤ dq L1 δ d := by unfold dq; grind
      positivity
  have hlt : (dq L1 δ d : ℝ) + t < L1 + δ + L2 := by
    have : dq L1 δ d + 1 ≤ L1 + δ + L2 := by unfold dq; grind
    have : (dq L1 δ d : ℝ) + 1 ≤ L1 + δ + L2 := by exact_mod_cast this
    linarith
  have hq : sidePt M₂.W ztuj t ≠ M₂.W.vtx g' := by
    refine hC.noV _ ztfoj t ht ht1 ?_ ?_ <;> rw [hC.off_M₂ hd ht ht1]
    · omega
    omega
  have hqD : sidePt M₂.W ztuj t ∉ M₂.D :=
    hC.hM₂.trace _ ztfoj t ht ht1.le
  obtain ⟨e, he, hqe, hec⟩ := hC.trans c hc _ hA.2.2.2.1 hqD hq
  have hpt := hC.sidePt_eq hd t
  refine ⟨e, he, hec, by_simp_all, ?_⟩
  rw [hC.attach_iff hd hsec]
  obtain ⟨hp, ht0, ht1', -, r, hr, hl⟩ := hA
  exact ⟨hp, ht0, ht1', hqe, r, hr, fun x hx => hl x ztvuy⟩
end Corr0
namespace Corr0
variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}

/-- Decomposing a position of the walk of `M` by its offset from `g`. -/
theorem decomp (hC : Corr0 M M₂ F S g g' L1 L2 δ) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht : 0 ≤ t)
    (ht1 : t < 1) :
    (g + dOf M.W.n g p) % M.W.n = p ∧ off M.W.n g ztk = dOf M.W.n g p + t :=
  ⟨add_dOf hC.hg hp, off_key' hC.hg hp ht ht1⟩

/-- Decomposing a position of the walk of `M₂` by its offset from `g'`. -/
theorem decomp₂ (hC : Corr0 M M₂ F S g g' L1 L2 δ) {p : ℕ} (hp : p < M₂.W.n) {t : ℝ} (ht : 0 ≤ t)
    (ht1 : t < 1) :
    (g' + dOf M₂.W.n g' p) % M₂.W.n = p ∧ off M₂.W.n g' ztk = dOf M₂.W.n g' p + t :=
  ⟨add_dOf hC.hg' hp, off_key' hC.hg' hp ht ht1⟩

/-- A second attachment of a transferred chord (through a point `q` of a chord `c` of `S`) never
lies between two positions of the stretch unless the corresponding attachment of `c` does. -/
theorem other_not_btw (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d d' : ℕ} (hd : d < L1 + L2)
    (hd' : d' < L1 + L2) {t t' : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    {c : Set Point} (hc : c ∈ S) {pb : ℕ} {tb : ℝ} (hB : SideAttach M₂.W c pb tb)
    (hout : ¬ Btw ztnb ztrj ztwpg)
    {e : Set Point} (he : e ∈ F) (hec : e ⊆ c) {q : Point} (hqe : q ∈ e) (hqD : q ∉ M₂.D)
    (hqB : sidePt M₂.W pb tb ≠ q) {p₃ : ℕ} {t₃ : ℝ} (hA₃ : SideAttach M.W e p₃ t₃)
    (hne : sidePt M.W p₃ t₃ ≠ q) :
    ¬ Btw ztbcr ztcex ztcwd := by
  intro hb3
  zugmx
  zudox
  have hcS := hC.hS hc
  have heF := hC.hF he
  -- the offsets of the positions
  have hox0 : ztgti := by_grind
  have hox0' : ztmqu := by_grind
  have hoxL : ztkza := by
    zqwa
    grind
  have hoxL' : ztkzc := by
    zqwb
    grind
  zufyg
  set d₃ := dOf M.W.n g p₃ with hd₃def
  have ho₃b : 0 < (d₃ : ℝ) + t₃ ∧ (d₃ : ℝ) + t₃ < L1 + L2 := by
    zuotg
    rcases hb3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  have hd₃ : d₃ < L1 + L2 := by
    have : (d₃ : ℝ) < L1 + L2 := by linarith [hA₃.2.1, ho₃b.2]
    zufc
  -- the ends of `c`
  obtain ⟨a₀, b₀, hab₀, -, hend⟩ := end_of_not_mem hC.hM₂ hcS
  have hyb := hB.2.2.2.1
  have hybD := hC.hM₂.trace _ hB.1 _ hB.2.1 hB.2.2.1.le
  -- the other end of `c` is the point of the attachment `(pb, tb)`
  have hother : ∀ y ∈ c, y ∉ M₂.D → y ≠ q → y = sidePt M₂.W pb tb := by
    grind
  by_cases hsplit : t₃ = 0 ∧ d₃ = L1
  · -- the second attachment is at the split vertex
    obtain ⟨ht₃, hd₃L⟩ := hsplit
    have hL2 : 0 < L2 := by
      omega
    have hδ : ztcfy := by
      zqvr
      · exact absurd (hC.hδ h) by_omega
      omega
    have hpt₃ : sidePt M.W p₃ t₃ = M₂.W.vtx ztckj := by
      rw [ht₃, Chazelle.Chain.sidePt_zero, ← hp₃e, hd₃L]; exact hC.A1 L1 le_rfl
    have hy₃D : ztrha := by
      rw [hpt₃, ← Chazelle.Chain.sidePt_zero]
      exact hC.hM₂.trace _ ztbar 0 le_rfl zero_le_one
    zqwc
    have hyb₃ :=
      (hother _ ztvux hy₃D hne).symm
    -- the positions lie on both sides of the gap
    have hL1pos : ztpgf := by_grind
    have hx_side : ∀ {k : ℕ} {s : ℝ}, s ∈ Ioo (0 : ℝ) 1 → (k : ℝ) + s < L1 →
        ((dq L1 δ k : ℕ) : ℝ) + s < L1 := by
      zulnf
      have hk : k < L1 := by
        have : (k : ℝ) < L1 := by zuofw
        zufc
      zudcm
    have hx_side' : ∀ {k : ℕ} {s : ℝ}, s ∈ Ioo (0 : ℝ) 1 → (L1 : ℝ) < k + s →
        (L1 : ℝ) + δ < ((dq L1 δ k : ℕ) : ℝ) + s := by
      zulnf
      have hk : L1 ≤ k := by
        have : (L1 : ℝ) < k + 1 := by zunui
        have : L1 < k + 1 := by exact_mod_cast this
        omega
      unfold dq; zvmyd; grind
    obtain ⟨hpbe, hob⟩ := hC.decomp₂ hB.1 hB.2.1 hB.2.2.1
    set db := dOf M₂.W.n g' pb with hdbdef
    have hδR : ztblc := by_positivity
    -- the attachment `(pb, tb)` is outside the gap
    have hgap : off M₂.W.n g' ztbd < L1 ∨ (L1 : ℝ) + δ < off M₂.W.n g' ztbd := by
      rw [ho₃, ht₃, hd₃L, add_zero] at hb3
      rcases hb3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have a1 := hx_side ht h1
        have a2 := hx_side' ht' h2
        zuiry
        exact hout ztzz
      · have a1 := hx_side ht' h1
        have a2 := hx_side' ht h2
        zuiry
        exact hout ztbmd
    -- transfer `(pb, tb)` to the walk of `M` and compare with the split vertex
    have key : ∀ d₀ : ℕ, d₀ < L1 + L2 → (tb = 0 → d₀ ≠ 0 ∧ d₀ ≠ L1) →
        ztfho % M₂.W.n = pb → d₀ = L1 ∧ tb = 0 := by
      intro d₀ hd₀ hsec hpb
      have hB' : SideAttach M₂.W c ztzzs tb := by_grind
      obtain ⟨e'', he'', he''c, hpt'', hA''⟩ := hC.transfer hd₀ hB.2.1 hB.2.2.1 hsec hc hB'
      have he''e := hC.nest e'' he'' e he by_grind
      rw [he''e] at hA''
      have hpteq : sidePt M.W ztxyw tb = sidePt M.W p₃ t₃ := by
        rw [hC.sidePt_eq hd₀, hpb, hyb₃]
      obtain ⟨h1, h2⟩ := WalkAx.attach_unique hC.hM heF hA'' hA₃ hpteq
      rw [← hp₃e, hd₃L] at h1
      exact ⟨add_mod_inj (by have := hC.hL; omega) (by have := hC.hL; omega) h1, by_grind⟩
    have hobn : (db : ℝ) + tb < M₂.W.n := by
      have  := dOf_lt hn₂ g' pb
      have : (db : ℝ) + 1 ≤ M₂.W.n := by exact_mod_cast this
      zumib
    rw [hob] at hgap
    rcases hgap with hlow | hhigh
    · have hdb : db < L1 := by
        have : (db : ℝ) < L1 := by zuntw
        zufc
      by_cases h0 : db = 0 ∧ tb = 0
      · -- the base point is not the split vertex
        apply hC.noV ztckj ztbar 0 le_rfl zero_lt_one
        · zunij; grind
        · zunij
          grind
        · rw [Chazelle.Chain.sidePt_zero, ← hpt₃, ← hyb₃, ← hpbe, h0.1, h0.2, add_zero,
            Nat.mod_eq_of_lt hC.hg', Chazelle.Chain.sidePt_zero]
      · have hsec : tb = 0 → db ≠ 0 ∧ db ≠ L1 := by_grind
        have hdq : dq L1 δ db = db := by unfold dq; grind
        obtain ⟨h1, -⟩ := key db by_omega hsec by_grind
        omega
    · have hdb : ztsca := by
        zqvo
        have : ztkzd := by exact_mod_cast hlt
        zumib
      have hdbn : ztpoc := by
        have : ztkze := by
          have := hC.hfull hδ
          have : ((L1 + δ + L2 : ℕ) : ℝ) = M₂.W.n := by exact_mod_cast this
          push_cast at this; zuntw
        zufc
      have hsec : tb = 0 → db - δ ≠ 0 ∧ db - δ ≠ L1 := by
        intro htb
        rw [htb, add_zero] at hhigh
        have : L1 + δ < db := by exact_mod_cast hhigh
        omega
      have hdq : ztzji := by unfold dq; zvmyd; omega
      obtain ⟨h1, h2⟩ := key _ by_omega hsec by_grind
      grind
  · -- the second attachment is at a regular position of the stretch
    have hsec₃ : t₃ = 0 → d₃ ≠ 0 ∧ d₃ ≠ L1 := by
      zubww
      refine ⟨fun hz => ?_, by_grind⟩
      have := ho₃b.1; rw [hz, h0] at this; grind
    have hA₃' : SideAttach M.W e ((g + d₃) % M.W.n) t₃ := by_grind
    have hpt₃ : sidePt M.W p₃ t₃ = sidePt M₂.W ztfat t₃ := by
      rw [← hp₃e]; exact hC.sidePt_eq hd₃ t₃
    have hy₃D : ztrha := by
      rw [hpt₃]; exact hC.hM₂.trace _ ztbar _ hA₃.2.1 hA₃.2.2.1.le
    zqwc
    have hAc : SideAttach M₂.W c ztfat t₃ := by
      rw [← hec']; exact (hC.attach_iff hd₃ hsec₃ e).1 hA₃'
    have hyb₃ : sidePt M₂.W pb tb = sidePt M₂.W ztfat t₃ := by
      rw [← hpt₃]; exact (hother _ ztvux hy₃D hne).symm
    obtain ⟨h1, h2⟩ := WalkAx.attach_unique hC.hM₂ hcS hB hAc hyb₃
    apply hout
    have hob : off M₂.W.n g' ztbd = ((dq L1 δ d₃ : ℕ) : ℝ) + t₃ := by
      zvmza; exact hC.off_M₂ hd₃ hA₃.2.1 hA₃.2.2.1
    rw [hob]
    apply btw_of_psi
    rw [psi_dq ht.1.le ht.2, psi_dq ht'.1.le ht'.2, psi_dq hA₃.2.1 hA₃.2.2.1, ← ho₃]
    omega
end Corr0
namespace Corr0
variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}

/-- **Mirroring a separation**: if a chord of `S` has one attachment between the positions of
`M₂` corresponding to two positions of the stretch and the other not, a chord of `F` has one
attachment between the two positions of `M` and the other not. -/
theorem mirror (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d d' : ℕ} (hd : d < L1 + L2)
    (hd' : d' < L1 + L2) {t t' : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    {c : Set Point} (hc : c ∈ S) {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M₂.W c pa ta)
    (hB : SideAttach M₂.W c pb tb) (hAB : sidePt M₂.W pa ta ≠ sidePt M₂.W pb tb)
    (hin : Btw ztnb ztrj ztwqr)
    (hout : ¬ Btw ztnb ztrj ztwpg) :
    (∃ e ∈ F, ∃ (p₁ p₃ : ℕ) (t₁ t₃ : ℝ), SideAttach M.W e p₁ t₁ ∧ SideAttach M.W e p₃ t₃ ∧
      sidePt M.W p₁ t₁ ≠ sidePt M.W p₃ t₃ ∧ Btw ztbcr ztcex ztxoj ∧
      ¬ Btw ztbcr ztcex ztcwd) ∨ InGap L1 δ (off M₂.W.n g' (pa + ta)) := by
  zugmx
  zudox
  obtain ⟨hpae, hoa⟩ := hC.decomp₂ hA.1 hA.2.1 hA.2.2.1
  set da := dOf M₂.W.n g' pa with hdadef
  have hbx : ∀ {k : ℕ} {s : ℝ}, k < L1 + L2 → s ∈ Ioo (0 : ℝ) 1 →
      0 < ((dq L1 δ k : ℕ) : ℝ) + s ∧ ((dq L1 δ k : ℕ) : ℝ) + s < L1 + δ + L2 := by
    intro k s hk hs
    zuevy
    have : dq L1 δ k + 1 ≤ L1 + δ + L2 := by unfold dq; grind
    have : ((dq L1 δ k : ℕ) : ℝ) + 1 ≤ L1 + δ + L2 := by exact_mod_cast this
    grind
  obtain ⟨hx1, hx2⟩ := hbx hd ht
  obtain ⟨hx1', hx2'⟩ := hbx hd' ht'
  have hoab : 0 < off M₂.W.n g' ztbf ∧ off M₂.W.n g' ztbf < L1 + δ + L2 := by
    rcases hin with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hoa] at hoab hin
  have hbtw := btw_psi (not_inGap_dq ht.1 ht.2) (not_inGap_dq ht'.1 ht'.2) hin
  rw [psi_dq ht.1.le ht.2, psi_dq ht'.1.le ht'.2] at hbtw
  set q := sidePt M₂.W pa ta with hq
  have hqD := hC.hM₂.trace _ hA.1 _ hA.2.1 hA.2.2.1.le
  -- the transferred case
  have trans_case : ∀ d₀ : ℕ, d₀ < L1 + L2 → (ta = 0 → d₀ ≠ 0 ∧ d₀ ≠ L1) →
      ztfho % M₂.W.n = pa → (d₀ : ℝ) + ta = psi L1 δ (da + ta) →
      ∃ e ∈ F, ∃ (p₁ p₃ : ℕ) (t₁ t₃ : ℝ), SideAttach M.W e p₁ t₁ ∧ SideAttach M.W e p₃ t₃ ∧
        sidePt M.W p₁ t₁ ≠ sidePt M.W p₃ t₃ ∧ Btw ztbcr ztcex ztxoj ∧
        ¬ Btw ztbcr ztcex ztcwd := by
    intro d₀ hd₀ hsec hpa hpsi
    have hA' : SideAttach M₂.W c ztzzs ta := by_grind
    obtain ⟨e, he, hec, hpte, hAe⟩ := hC.transfer hd₀ hA.2.1 hA.2.2.1 hsec hc hA'
    have hptq : sidePt M.W ztxyw ta = q := by rw [hC.sidePt_eq hd₀, hpa]
    zqvy
    refine ⟨e, he, _, p₃, ta, t₃, hAe, hA₃, hne₃.symm, ?_, ?_⟩
    · rw [hC.off_M hd₀ hA.2.1 hA.2.2.1, hpsi]; omega
    · exact hC.other_not_btw hd hd' ht ht' hc hB hout he hec by_grind hqD
        zteno hA₃ by_grind
  by_cases hA1 : da < L1
  · have hdq : dq L1 δ da = da := by unfold dq; grind
    refine Or.inl (trans_case da by_omega (fun h0 => ztpfi)
      by_grind ?_)
    · have := hoab.1; rw [h0, hz] at this; grind
    · have := psi_dq (L1 := L1) (δ := δ) (d := da) hA.2.1 hA.2.2.1
      grind
  by_cases hA3 : (L1 : ℝ) + δ < da + ta
  · have hda : L1 + δ ≤ da := by
      zqvo
      have : (da : ℝ) + 1 ≤ L1 + δ := by exact_mod_cast hlt
      zujcb
    have hdq : dq L1 δ zttiw = da := by unfold dq; zvmyd; omega
    have hdan : da < L1 + δ + L2 := by
      have : (da : ℝ) < L1 + δ + L2 := by linarith [hA.2.1, hoab.2]
      zufc
    refine Or.inl (trans_case zttiw by_omega ztfrp by_grind ?_)
    · rw [h0, add_zero] at hA3
      have : L1 + δ < da := by exact_mod_cast hA3
      omega
    · have := psi_dq (L1 := L1) (δ := δ) (d := da - δ) hA.2.1 hA.2.2.1
      grind
  -- the gap
  push Not at hA1 hA3
  right
  rw [hoa]
  refine ⟨?_, hA3⟩
  have : (L1 : ℝ) ≤ da := by exact_mod_cast hA1
  zupbu
end Corr0

/-! ## The gap facts -/

/-- A point of the stretch of `M`: a position at offset in `(0, L)` from `g`. -/
def StrPt (M : Model) (g L : ℕ) (x : Point) : Prop :=
  ∃ d < L, ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ 0 < (d : ℝ) + t ∧ sidePt M.W ztwje t = x

/-- **The gap facts** of a correspondence with a gap (`δ > 0`): a chord of `S` attached strictly
inside the gap meets the stretch of `M` in at most one point; at each copy of the split vertex
of `M₂` at most one chord of `S` is attached; a chord of `F` through the split vertex of `M`,
inside a chord of `S` attached at a copy of the split vertex in `M₂`, is attached at the split
vertex of `M`. -/
structure CorrGap (M M₂ : Model) (F S : Set ztf) (g g' L1 L2 δ : ℕ) : Prop where
  gapOut : ∀ c ∈ S, ∀ (pa : ℕ) (ta : ℝ), SideAttach M₂.W c pa ta →
    (L1 : ℝ) < off M₂.W.n g' ztbf → off M₂.W.n g' ztbf < L1 + δ →
    ∀ x ∈ c, ∀ y ∈ c, StrPt M g zthbg x → StrPt M g zthbg y → x = y
  oneAt : ∀ k : ℕ, ztlql → ∀ c ∈ S, ∀ c' ∈ S,
    SideAttach M₂.W c ztgvz 0 → SideAttach M₂.W c' ztgvz 0 →
      c = c'
  splitAttach : ∀ k : ℕ, ztlql → ∀ c ∈ S,
    SideAttach M₂.W c ztgvz 0 → ∀ e ∈ F, e ⊆ c →
      sidePt M.W ztbxk 0 ∈ e → SideAttach M.W e ztbxk 0

/-- **A third attachment** of an admissible chord is one of two attachments at distinct
points. -/
theorem attach_third {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm)
    {px py pz : ℕ} {tx ty tz : ℝ} (hX : SideAttach M.W c px tx) (hY : SideAttach M.W c py ty)
    (hXY : sidePt M.W px tx ≠ sidePt M.W py ty) (hZ : SideAttach M.W c pz tz) :
    (pz = px ∧ tz = tx) ∨ (pz = py ∧ tz = ty) := by
  obtain ⟨a, b, -, -, hend⟩ := end_of_not_mem hM hc
  have hx := hend _ hX.2.2.2.1 (hM.trace _ hX.1 _ hX.2.1 hX.2.2.1.le)
  have hy := hend _ hY.2.2.2.1 (hM.trace _ hY.1 _ hY.2.1 hY.2.2.1.le)
  have hz := hend _ hZ.2.2.2.1 (hM.trace _ hZ.1 _ hZ.2.1 hZ.2.2.1.le)
  have key : sidePt M.W pz tz = sidePt M.W px tx ∨ sidePt M.W pz tz = sidePt M.W py ty := by
    grind
  rcases key with h | h
  · exact Or.inl (WalkAx.attach_unique hM hc hZ hX h)
  · exact Or.inr (WalkAx.attach_unique hM hc hZ hY h)
namespace Corr0
variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}

/-- A chord of `F` with exactly one attachment between two positions of the stretch separates
them. -/
theorem sepM (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d d' : ℕ} (hd : d < L1 + L2)
    (hd' : d' < L1 + L2) {t t' : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut F ztwjt)
    (hcut' : ¬ M.IsCut F ztwlq) (hne : (d : ℝ) + t ≠ d' + t')
    {e : Set Point} (he : e ∈ F) {p₁ p₃ : ℕ} {t₁ t₃ : ℝ} (hA₁ : SideAttach M.W e p₁ t₁)
    (hA₃ : SideAttach M.W e p₃ t₃) (hne₁₃ : sidePt M.W p₁ t₁ ≠ sidePt M.W p₃ t₃)
    (hb1 : Btw ztbcr ztcex ztxoj)
    (hb3 : ¬ Btw ztbcr ztcex ztcwd) :
    M.Separates e ztwjt ztwlq := by
  zugmx
  refine ⟨p₁, p₃, t₁, t₃, hA₁, hA₃, hne₁₃, ?_⟩
  have hk13 := WalkAx.key_ne_of_pt_ne hA₁ hA₃ hne₁₃
  obtain ⟨y0, y1⟩ := Corr.key_mem ztypm ht.1.le ht.2
  obtain ⟨y0', y1'⟩ := Corr.key_mem (Nat.mod_lt ztsb hn) ht'.1.le ht'.2
  obtain ⟨a0, a1⟩ := Corr.key_mem hA₁.1 hA₁.2.1 hA₁.2.2.1
  obtain ⟨b0, b1⟩ := Corr.key_mem hA₃.1 hA₃.2.1 hA₃.2.2.1
  zuiya
  have hgn : ztehn := by exact_mod_cast hC.hg
  have hyy : ((ztbe % M.W.n : ℕ) : ℝ) + t ≠ ((ztsb % M.W.n : ℕ) : ℝ) + t' := by
    zuq
    have h2 := congrArg (off M.W.n g) h
    rw [hC.off_M hd ht.1.le ht.2, hC.off_M hd' ht'.1.le ht'.2] at h2
    simp_all
  have hya : ∀ {p : ℕ} {s : ℝ}, SideAttach M.W e p s →
      ((ztbe % M.W.n : ℕ) : ℝ) + t ≠ p + s ∧ ((ztsb % M.W.n : ℕ) : ℝ) + t' ≠ p + s :=
    fun hP => ⟨fun h => hcut ztkkw, fun h => hcut' ztkkw⟩
  refine (sep_iff_btw hg0 hgn a0 a1 b0 b1 y0 y1 y0' y1' hk13 hyy by_grind by_grind
    by_grind by_grind).2 ?_
  rw [hC.off_M hd ht.1.le ht.2, hC.off_M hd' ht'.1.le ht'.2]
  grind

/-- **Both attachments of a chord of `F` stay between two positions of one region**: if two
positions of the stretch face the same region of `F`, a chord of `F` attached between them has
every attachment at another point between them too. -/
theorem btw_other (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d d' : ℕ} (hd : d < L1 + L2)
    (hd' : d' < L1 + L2) {t t' : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut F ztwjt)
    (hcut' : ¬ M.IsCut F ztwlq) {U : Set Point}
    (hU : U ∈ M.regions F) (hf : M.Faces ztwje t U)
    (hf' : M.Faces ztxlv t' U) (hne : (d : ℝ) + t ≠ d' + t') {e : Set Point}
    (he : e ∈ F) {p₁ p₃ : ℕ} {t₁ t₃ : ℝ} (hA₁ : SideAttach M.W e p₁ t₁)
    (hA₃ : SideAttach M.W e p₃ t₃) (hne₁₃ : sidePt M.W p₁ t₁ ≠ sidePt M.W p₃ t₃)
    (hb1 : Btw ztbcr ztcex ztxoj) :
    Btw ztbcr ztcex ztcwd := by
  by_contra hb3
  exact (hC.hM.eq_iff_not_separates hC.hF hC.hfin hU hU ztdtk
    ztdtk ht ht' hcut hcut' hf hf').1 rfl e he
    (hC.sepM hd hd' ht ht' hcut hcut' hne he hA₁ hA₃ hne₁₃ hb1 hb3)

/-- **The far attachment of a chord of `S` whose piece in `F` is attached between two positions
of one region** lies between their counterparts, and the piece has a second point in the
stretch. -/
theorem far_btw (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d d' : ℕ} (hd : d < L1 + L2)
    (hd' : d' < L1 + L2) {t t' : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut F ztwjt)
    (hcut' : ¬ M.IsCut F ztwlq) {U : Set Point}
    (hU : U ∈ M.regions F) (hf : M.Faces ztwje t U)
    (hf' : M.Faces ztxlv t' U) (hne : (d : ℝ) + t ≠ d' + t') {c : Set Point}
    (hc : c ∈ S) {pb : ℕ} {tb : ℝ} (hB : SideAttach M₂.W c pb tb) {e : Set Point} (he : e ∈ F)
    (hec : e ⊆ c) {q : Point} (hqe : q ∈ e) (hqD : q ∉ M₂.D) (hqB : sidePt M₂.W pb tb ≠ q)
    {pe : ℕ} {te : ℝ} (hAe : SideAttach M.W e pe te) (hpe : sidePt M.W pe te = q)
    (hbe : Btw ztbcr ztcex ztyfk) :
    Btw ztnb ztrj ztwpg ∧
      ∃ y ∈ c, StrPt M g zthbg y ∧ y ≠ q := by
  zqvy
  have hb3 := hC.btw_other hd hd' ht ht' hcut hcut' hU hf hf' hne he hAe hA₃ (Ne.symm hne₃) hbe
  have hne₃' : sidePt M.W p₃ t₃ ≠ q := by_simp_all
  refine ⟨by_contra fun hout => hC.other_not_btw hd hd' ht ht' hc hB hout he hec hqe hqD hqB
    hA₃ hne₃' hb3, ?_⟩
  have hlo : ztgti := by_grind
  have hlo' : ztmqu := by_grind
  have hhi : ztkza := by
    zqwa
    grind
  have hhi' : ztkzc := by
    zqwb
    grind
  zufyg
  have hb : 0 < (dOf M.W.n g p₃ : ℝ) + t₃ ∧ (dOf M.W.n g p₃ : ℝ) + t₃ < L1 + L2 := by
    zuotg; rcases hb3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  have hlt : dOf M.W.n g p₃ < L1 + L2 := by
    have : (dOf M.W.n g p₃ : ℝ) < L1 + L2 := by linarith [hA₃.2.1, hb.2]
    zufc
  exact ⟨sidePt M.W p₃ t₃, hec hA₃.2.2.2.1,
    ⟨dOf M.W.n g p₃, hlt, t₃, hA₃.2.1, hA₃.2.2.1, hb.1, by_simp_all⟩, hne₃'⟩

/-- A key of `M₂` at the offset `L + u` (`0 ≤ u < 1`) is the key of `((g' + L) mod n₂, u)`. -/
theorem key_of_off₂ (hC : Corr0 M M₂ F S g g' L1 L2 δ) {L : ℕ} (hL : L < M₂.W.n) {p : ℕ}
    {s u : ℝ} (hp : p < M₂.W.n) (hs0 : 0 ≤ s) (hs1 : s < 1) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (h : off M₂.W.n g' ztdvn = L + u) : p = zttkr % M₂.W.n ∧ s = u := by
  zudox
  obtain ⟨k0, k1⟩ := Corr.key_mem hp hs0 hs1
  obtain ⟨m0, m1⟩ := Corr.key_mem (Nat.mod_lt zttkr hn₂) hu0 hu1
  zuiyb
  have hgn : ztixg := by exact_mod_cast hC.hg'
  have e := off_inj hg0 hgn k0 k1 m0 m1 (h.trans (off_key hC.hg' hL hu0 hu1).symm)
  exact Chazelle.Chain.sideKey_inj hs0 hs1 hu0 hu1 e

/-- The counterpart of a non-cut position of the stretch is not a cut. -/
theorem not_cut₂ (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut F ztwjt) :
    ¬ M₂.IsCut S ztydh := by
  rintro ⟨c₀, hc₀, p, t₀, hA₀, hkey⟩
  obtain ⟨hp, ht0⟩ := Chazelle.Chain.sideKey_inj ht.1.le ht.2 hA₀.2.1 hA₀.2.2.1 hkey
  rw [← hp, ← ht0] at hA₀
  obtain ⟨e, he, -, -, hAe⟩ := hC.transfer hd ht.1.le ht.2 ztpbo hc₀ hA₀
  exact hcut ⟨e, he, _, t, hAe, rfl⟩

/-- A separation in `M₂` as betweenness of offsets from `g'`. -/
theorem sep₂_btw (hC : Corr0 M M₂ F S g g' L1 L2 δ) {c : Set Point} (hc : c ∈ S) {p p' : ℕ}
    {s s' : ℝ} (hp : p < M₂.W.n) (hp' : p' < M₂.W.n) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hs' : s' ∈ Ioo (0 : ℝ) 1) (hnc : ¬ M₂.IsCut S ztdvn) (hnc' : ¬ M₂.IsCut S ztkby)
    {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M₂.W c pa ta) (hB : SideAttach M₂.W c pb tb)
    (hAB : sidePt M₂.W pa ta ≠ sidePt M₂.W pb tb)
    (hiff : sideInArc ztbf ztbd ztdvn ↔ ¬ sideInArc ztbf ztbd ztkby) :
    (Btw ztzng ztznh ztwqr ↔
      ¬ Btw ztzng ztznh ztwpg) := by
  have hxs : (p : ℝ) + s ≠ p' + s' := by_grind
  have hxa : ∀ {q : ℕ} {u : ℝ}, SideAttach M₂.W c q u → (p : ℝ) + s ≠ q + u ∧
      (p' : ℝ) + s' ≠ q + u :=
    fun hP => ⟨fun h => hnc ztkjg, fun h => hnc' ztkjg⟩
  have hab := WalkAx.key_ne_of_pt_ne hA hB hAB
  obtain ⟨k0, k1⟩ := Corr.key_mem hp hs.1.le hs.2
  obtain ⟨s0, s1⟩ := Corr.key_mem hp' hs'.1.le hs'.2
  obtain ⟨ka0, ka1⟩ := Corr.key_mem hA.1 hA.2.1 hA.2.2.1
  obtain ⟨kb0, kb1⟩ := Corr.key_mem hB.1 hB.2.1 hB.2.2.1
  zuixz
  have hg'n : ztixg := by exact_mod_cast hC.hg'
  exact (sep_iff_btw hg'0 hg'n ka0 ka1 kb0 kb1 k0 k1 s0 s1 hab hxs by_grind by_grind
    by_grind by_grind).1 hiff

/-! ## The two sides of the gap -/

/-- **The side before the gap.**  Two positions `d < L1 ≤ d'` of the stretch face the same region
of `F`, and a chord `c ∈ S` attached in the gap separates their counterparts.  Then the region of
`S` faced at the counterpart of `d` is the one faced just after the split vertex of `M₂`. -/
theorem gapS_of (hC : Corr0 M M₂ F S g g' L1 L2 δ) (hG : CorrGap M M₂ F S g g' L1 L2 δ)
    {d d' : ℕ} (hdL : d < L1) (hLd : L1 ≤ d') (hd' : d' < L1 + L2) {t t' : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut F ztwjt)
    (hcut' : ¬ M.IsCut F ztwlq) {U : Set Point}
    (hU : U ∈ M.regions F) (hf : M.Faces ztwje t U)
    (hf' : M.Faces ztxlv t' U) {c : Set Point} (hc : c ∈ S) {pa pb : ℕ}
    {ta tb : ℝ} (hA : SideAttach M₂.W c pa ta) (hB : SideAttach M₂.W c pb tb)
    (hAg : InGap L1 δ ztwqr)
    (hout : ¬ Btw ztnb ztrj ztwpg)
    {V : Set Point} (hV : V ∈ M₂.regions S)
    (hfV : M₂.Faces ztuj t V) :
    AfterFaces M₂ ztckj 0 V := by
  zqvu
  have hδ : ztcfy := by
    zqvr
    · have := hC.hδ h; omega
    omega
  zqvn
  have hout' : ztbaqy := by
    simp_all
  have hdLr : ztmrg := by
    zqwd
  zqvs
  zqvm
  -- no cut just after the split vertex
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (eventually_not_cut_after hC.hM₂ hC.hS hC.hSfin (((g' + L1) % M₂.W.n : ℕ) : ℝ))
  zukxl
  refine ⟨min ε₀ 1, by_simp_all, fun s hs0 hsε hs1 => ?_⟩
  rw [zero_add] at hs1 ⊢
  zukfy
  have hnc : ¬ M₂.IsCut S _ := hsub ztuie
  obtain ⟨V'', hV'', hfV''⟩ := hC.hM₂.exists_faces_of_not_cut hC.hS hC.hSfin
    ztbar ztdxi hnc
  zuent
  zuixt
  refine (hC.hM₂.eq_iff_not_separates hC.hS hC.hSfin hV hV'' ztbar
    ztbar ht by_grind hc₂ hnc hfV hfV'').2 ?_
  zqvx
  have hsep := hC.sep₂_btw hc' ztbar ztbar ht by_grind hc₂ hnc hA'
    hB' hAB' hiff'
  rw [hC.off_M₂ hd ht.1.le ht.2, hdq, off_key hC.hg' hL1n hs0.le hs1] at hsep
  -- the attachment of `c'` between the two positions
  have core : ∀ {pa₁ pb₁ : ℕ} {ta₁ tb₁ : ℝ}, SideAttach M₂.W c' pa₁ ta₁ →
      SideAttach M₂.W c' pb₁ tb₁ → sidePt M₂.W pa₁ ta₁ ≠ sidePt M₂.W pb₁ tb₁ →
      Btw ztbcr ztnme ztznd →
      ¬ Btw ztbcr ztnme ztzne → False := by
    zugol
    have hin₁' : (d : ℝ) + t < off M₂.W.n g' ztbgz ∧
        off M₂.W.n g' ztbgz < L1 + s := by
      rcases hin₁ with h | ⟨h1, h2⟩
      · zubh
      grind
    -- no attachment strictly between the split vertex and `L1 + s`
    have hoaL : off M₂.W.n g' ztbgz ≤ L1 := by
      zqvo
      obtain ⟨hp, hu⟩ := hC.key_of_off₂ hL1n hA₁.1 hA₁.2.1 hA₁.2.2.1
        (u := off M₂.W.n g' _ - L1) by_linarith by_grind by_ring
      apply hsub ⟨by_grind,
        show off M₂.W.n g' ztbgz - L1 < ε₀ by linarith [hin₁'.2]⟩
      refine ztkjc
      grind
    zuhfm
    -- the piece of `c'` through the attachment, in `M`
    obtain ⟨e', he', hec', hqe', pe, te, hAe, hpe, hbe, hqS⟩ : ∃ e' ∈ F, e' ⊆ c' ∧
        sidePt M₂.W pa₁ ta₁ ∈ e' ∧ ∃ pe te, SideAttach M.W e' pe te ∧
          sidePt M.W pe te = sidePt M₂.W pa₁ ta₁ ∧ Btw ztbcr ztcex ztyfk ∧
          StrPt M g zthbg ztrwx := by
      zudit

      · -- a regular position before the split vertex
        have hdaL : dOf M₂.W.n g' pa₁ < L1 := by
          have : (dOf M₂.W.n g' pa₁ : ℝ) < L1 := by zupdp
          zufc
        have hdqa : dq L1 δ ztrom = dOf M₂.W.n g' pa₁ := by
          zudcm
        have hsec : ta₁ = 0 → dOf M₂.W.n g' pa₁ ≠ 0 ∧ dOf M₂.W.n g' pa₁ ≠ L1 := by
          zubww
          refine ztpfi
          have h1 := hin₁'.1
          rw [hoae, hz, h0] at h1
          zulnx
          zunfo
        have hA₁' : SideAttach M₂.W c' ((g' + dq L1 δ ztrom) % M₂.W.n) ta₁ := by
          grind
        obtain ⟨e', he', hec', hqe', hAe'⟩ :=
          hC.transfer by_omega hA₁.2.1 hA₁.2.2.1 hsec hc' hA₁'
        have hpt : sidePt M.W ((g + dOf M₂.W.n g' pa₁) % M.W.n) ta₁ = sidePt M₂.W pa₁ ta₁ := by
          rw [hC.sidePt_eq by_grind ta₁, hdqa, hpae]
        refine ⟨e', he', hec', by_grind, _, _, hAe', hpt, ?_,
          ⟨dOf M₂.W.n g' pa₁, by_omega, ta₁, hA₁.2.1, hA₁.2.2.1, by linarith [hin₁'.1, ht.1,
            (Nat.cast_nonneg d : (0 : ℝ) ≤ d)], hpt⟩⟩
        rw [hC.off_M by_grind hA₁.2.1 hA₁.2.2.1]
        left; constructor <;> linarith [hin₁'.1, ht'.1]
      · -- at the split vertex
        obtain ⟨hp1, ht1⟩ := hC.key_of_off₂ hL1n hA₁.1 hA₁.2.1 hA₁.2.2.1 le_rfl one_pos
          by_grind
        have hvtx : M.W.vtx _ = M₂.W.vtx _ :=
          hC.A1 L1 le_rfl
        have hu : ztylw := by
          zufno
        have hnoV : ztppz := by
          zukvm
          refine hC.noV _ ztbar 0 le_rfl one_pos ?_ ?_ <;>
            rw [off_key hC.hg' hL1n le_rfl one_pos]
          · linarith
          grind
        zqvz
        have hA₁P : SideAttach M₂.W c' ztckj 0 := by
          grind
        have hAe' := hG.splitAttach L1 ztp c' hc' hA₁P e' he' hec'
          by_grind
        refine ⟨e', he', hec', hqe', _, _, hAe', hu, ?_,
          ⟨L1, by_omega, 0, le_rfl, one_pos, by_linarith, hu⟩⟩
        rw [hC.off_M by_grind le_rfl one_pos]
        left; constructor <;> zupdn
    obtain ⟨hbtw, y, hyc, hyS, hyq⟩ := hC.far_btw hd hd' ht ht' hcut hcut' hU hf hf' hne hc' hB₁
      he' hec' hqe' hqD₀ ztqnt hAe hpe hbe
    zugdt

    have hob : (L1 : ℝ) + s ≤ off M₂.W.n g' ztcfc ∧
        off M₂.W.n g' ztcfc < d' + δ + t' := by
      zubry
      · refine ztufr
        zqvo
        exact hout₁ ztzz
      · zujvp
    -- `c'` is not `c`
    have hcc : ztsdw := by
      zqvt
      · exact hout' ztjqa
      simp_all
    zuicj
    have hab₁ : off M₂.W.n g' ztbgz < off M₂.W.n g' ztcfc := by
      grind
    by_cases hmid : off M₂.W.n g' ztbgz < off M₂.W.n g' ztbf ∧
        off M₂.W.n g' ztbf < off M₂.W.n g' ztcfc
    · obtain ⟨h1, h2⟩ := no_cross_off hC.hM₂ hC.hS hC.hSfin hc' hc ztvas hA₁ hB₁ hAB₁ hA
        hB hg'0 hg'n hab₁ hmid.1 hmid.2
      exact hout' ztzz
    have hge : off M₂.W.n g' ztcfc ≤ off M₂.W.n g' ztbf ∨
        off M₂.W.n g' ztbf = off M₂.W.n g' ztbgz := by
      grind
    zuklj
    · rcases lt_or_eq_of_le (le_trans hge hA2) with hlt | heq'
      · -- `c'` is attached strictly inside the gap
        exact hyq (hG.gapOut c' hc' pb₁ tb₁ hB₁ by_grind hlt y hyc _
          ztvuz hyS hqS)
      · -- both at the copy of the split vertex after the gap
        have hA' : ztorh := le_antisymm hA2 by_grind
        obtain ⟨hp1, ht1⟩ := hC.key_of_off₂ (L := L1 + δ) by_omega hB₁.1 hB₁.2.1 hB₁.2.2.1 le_rfl one_pos by_grind
        zqvp
        zqvv
        exact hcc (hG.oneAt _ ztbt c hc c' hc' hA'' hB₁')
    · -- both at the copy of the split vertex before the gap
      have hoaL1 : ztrgw := le_antisymm hoaL by_grind
      obtain ⟨hp1, ht1⟩ := hC.key_of_off₂ hL1n hA₁.1 hA₁.2.1 hA₁.2.2.1 le_rfl one_pos
        by_grind
      obtain ⟨hp2, ht2⟩ := hC.key_of_off₂ hL1n hA.1 hA.2.1 hA.2.2.1 le_rfl one_pos
        by_grind
      zqvw
      exact hcc (hG.oneAt L1 ztp c hc c' hc' hA'' hA₁')
  by_cases h : Btw ztbcr ztnme ztznf
  · zuite
  · zuitf

/-- **The side after the gap.**  Two positions `d < L1 ≤ d'` of the stretch face the same region
of `F`, and a chord `c ∈ S` attached in the gap separates their counterparts.  Then the region of
`S` faced at the counterpart of `d'` is the one faced just before the second copy
`(g' + L1 + δ)` of the split vertex in `M₂`. -/
theorem gapE_of (hC : Corr0 M M₂ F S g g' L1 L2 δ) (hG : CorrGap M M₂ F S g g' L1 L2 δ)
    {d d' : ℕ} (hdL : d < L1) (hLd : L1 ≤ d') (hd' : d' < L1 + L2) {t t' : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut F ztwjt)
    (hcut' : ¬ M.IsCut F ztwlq) {U : Set Point}
    (hU : U ∈ M.regions F) (hf : M.Faces ztwje t U)
    (hf' : M.Faces ztxlv t' U) {c : Set Point} (hc : c ∈ S) {pa pb : ℕ}
    {ta tb : ℝ} (hA : SideAttach M₂.W c pa ta) (hB : SideAttach M₂.W c pb tb)
    (hAg : InGap L1 δ ztwqr)
    (hout : ¬ Btw ztnb ztrj ztwpg)
    {V : Set Point} (hV : V ∈ M₂.regions S)
    (hfV : M₂.Faces ztbaai t' V) :
    BeforeFaces M₂ ztysu 0 V := by
  zqvu
  have hδ : ztcfy := by
    zqvr
    · have := hC.hδ h; omega
    omega
  zqvn
  have hout' : ztbaqy := by
    simp_all
  have hdLr : ztmrg := by
    zqwd
  zqvs
  have hL2r : (0 : ℝ) < L2 := by_simp_all
  zqvm
  have hnr : (M₂.W.n : ℝ) = L1 + δ + L2 := by exact_mod_cast hfull.symm
  -- the last edge of the gap
  set Q₀ := (g' + ztpzl) % M₂.W.n with hQ₀
  have hQ : (ztdok % M₂.W.n + M₂.W.n - 1) % M₂.W.n = Q₀ := by
    rw [hQ₀, show g' + L1 + δ = g' + (L1 + δ) by ring, mod_pred_mod hn₂ _ by_omega]
  have hLδn : L1 + δ - 1 < M₂.W.n := by_omega
  have hoffQ : ∀ u : ℝ, 0 ≤ u → u < 1 → off M₂.W.n g' ((Q₀ : ℝ) + u) = L1 + δ - 1 + u := by
    intro u hu0 hu1
    rw [hQ₀, off_key hC.hg' hLδn hu0 hu1]
    zunqu
    ring
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (eventually_not_cut_before hC.hM₂ hC.hS hC.hSfin ((Q₀ : ℝ) + 1))
  zukxl
  refine ⟨min ε₀ 1, lt_min hε₀ one_pos, fun h => absurd h ztgkw, fun _ s hs0 hsε => ?_⟩
  zuext
  have hs1 := lt_of_lt_of_le hsε ztgh
  zukfy
  have hnc : ¬ M₂.IsCut S ((Q₀ : ℝ) + zteb) := by
    have := hsub ztuie
    simp only [mem_ofPred_eq] at this
    grind
  zukfm
  obtain ⟨V'', hV'', hfV''⟩ := hC.hM₂.exists_faces_of_not_cut hC.hS hC.hSfin
    ztbar hs' hnc
  zuent
  have hc₂ := hC.not_cut₂ hd' ht' hcut'
  refine (hC.hM₂.eq_iff_not_separates hC.hS hC.hSfin hV hV'' ztbar
    ztbar ht' hs' hc₂ hnc hfV hfV'').2 ?_
  zqvx
  have hsep := hC.sep₂_btw hc' ztbar ztbar ht' hs' hc₂ hnc hA'
    hB' hAB' hiff'
  rw [hC.off_M₂ hd' ht'.1.le ht'.2, hdq', hoffQ _ hs'.1.le hs'.2] at hsep
  push_cast at hsep
  have core : ∀ {pa₁ pb₁ : ℕ} {ta₁ tb₁ : ℝ}, SideAttach M₂.W c' pa₁ ta₁ →
      SideAttach M₂.W c' pb₁ tb₁ → sidePt M₂.W pa₁ ta₁ ≠ sidePt M₂.W pb₁ tb₁ →
      Btw ztjtg ztxkd ztznd →
      ¬ Btw ztjtg ztxkd ztzne → False := by
    zugol
    have hin₁' : (L1 : ℝ) + δ - s < off M₂.W.n g' ztbgz ∧
        off M₂.W.n g' ztbgz < d' + δ + t' := by
      rcases hin₁ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · zujvp
      grind
    -- no attachment strictly between `L1 + δ - s` and the second copy of the split vertex
    have hoaL : (L1 : ℝ) + δ ≤ off M₂.W.n g' ztbgz := by
      zqvo
      obtain ⟨hp, hu⟩ := hC.key_of_off₂ hLδn hA₁.1 hA₁.2.1 hA₁.2.2.1
        (u := off M₂.W.n g' ztbgz - ztpzl) by_grind
        by_linarith (by zunqu; ring)
      apply hsub ⟨by_grind,
        show (L1 + δ : ℝ) - off M₂.W.n g' ztbgz < ε₀ by linarith [hin₁'.1]⟩
      refine ztkjc
      grind
    zuhfm
    have hoan : off M₂.W.n g' ztbgz < L1 + δ + L2 := by
      rw [← hnr]
      exact off_lt (Corr.key_mem hA₁.1 hA₁.2.1 hA₁.2.2.1).2 hg'0
    obtain ⟨e', he', hec', hqe', pe, te, hAe, hpe, hbe, hqS⟩ : ∃ e' ∈ F, e' ⊆ c' ∧
        sidePt M₂.W pa₁ ta₁ ∈ e' ∧ ∃ pe te, SideAttach M.W e' pe te ∧
          sidePt M.W pe te = sidePt M₂.W pa₁ ta₁ ∧ Btw ztbcr ztcex ztyfk ∧
          StrPt M g zthbg ztrwx := by
      zudit

      · -- a regular position after the gap
        set db := dOf M₂.W.n g' pa₁ with hdb
        have hdbL : ztsca := by
          zucuy
          have : ztkzd := by exact_mod_cast hh
          linarith [hA₁.2.2.1]
        have hdbn : ztpoc := by
          have : ztkze := by zupdp
          zufc
        have hdqa : ztzji := by unfold dq; zvmyd; omega
        have hsec : ta₁ = 0 → db - δ ≠ 0 ∧ db - δ ≠ L1 := by
          zubww
          refine ⟨by_omega, fun hz => ?_⟩
          have : db = L1 + δ := by_omega
          have h1 := hlt
          rw [hoae, this, h0] at h1
          grind
        have hA₁' : SideAttach M₂.W c' ((g' + dq L1 δ ztjtv) % M₂.W.n) ta₁ := by
          grind
        obtain ⟨e', he', hec', hqe', hAe'⟩ :=
          hC.transfer by_omega hA₁.2.1 hA₁.2.2.1 hsec hc' hA₁'
        have hpt : sidePt M.W ((g + ztjtv) % M.W.n) ta₁ = sidePt M₂.W pa₁ ta₁ := by
          rw [hC.sidePt_eq (by omega : db - δ < L1 + L2) ta₁, hdqa, hpae]
        have hcast : ((db - δ : ℕ) : ℝ) = db - δ := by push_cast [show δ ≤ db by omega]; ring
        refine ⟨e', he', hec', by_grind, _, _, hAe', hpt, ?_,
          ⟨db - δ, by_omega, ta₁, hA₁.2.1, hA₁.2.2.1, by_grind, hpt⟩⟩
        rw [hC.off_M (by omega : db - δ < L1 + L2) hA₁.2.1 hA₁.2.2.1, hcast]
        zujby
      · -- at the second copy of the split vertex
        zqvq
        have hvtx : M.W.vtx ztbxk = M₂.W.vtx ztjcj := by
          have := hC.A2 0 ztbg
          grind
        have hu : ztylw := by
          zufno
        have hnoV : ztppz := by
          zukvm
          refine hC.noV _ ztbar 0 le_rfl one_pos ?_ ?_ <;>
            rw [off_key hC.hg' by_omega le_rfl one_pos] <;> push_cast <;>
            linarith
        zqvz
        have hA₁P : SideAttach M₂.W c' ztjcj 0 := by
          grind
        have hAe' := hG.splitAttach _ ztbt c' hc' hA₁P e' he' hec'
          by_grind
        refine ⟨e', he', hec', hqe', _, _, hAe', hu, ?_,
          ⟨L1, by_omega, 0, le_rfl, one_pos, by_linarith, hu⟩⟩
        rw [hC.off_M by_omega le_rfl one_pos]
        zujby
    obtain ⟨hbtw, y, hyc, hyS, hyq⟩ := hC.far_btw hd hd' ht ht' hcut hcut' hU hf hf' hne hc' hB₁
      he' hec' hqe' hqD₀ ztqnt hAe hpe hbe
    zugdt

    have hob : (d : ℝ) + t < off M₂.W.n g' ztcfc ∧
        off M₂.W.n g' ztcfc ≤ L1 + δ - s := by
      zubry
      · zujfv
        zqvo
        exact hout₁ ztbmd
      grind
    have hcc : ztsdw := by
      zqvt
      · exact hout' ztjqa
      grind
    zuicj
    have hab₁ : off M₂.W.n g' ztcfc < off M₂.W.n g' ztbgz := by
      grind
    by_cases hmid : off M₂.W.n g' ztcfc < off M₂.W.n g' ztbf ∧
        off M₂.W.n g' ztbf < off M₂.W.n g' ztbgz
    · obtain ⟨h1, h2⟩ := no_cross_off hC.hM₂ hC.hS hC.hSfin hc' hc ztvas hB₁ hA₁
        (Ne.symm hAB₁) hA hB hg'0 hg'n hab₁ hmid.1 hmid.2
      exact hout' ztzz
    have hge : off M₂.W.n g' ztbf ≤ off M₂.W.n g' ztcfc ∨
        off M₂.W.n g' ztbf = off M₂.W.n g' ztbgz := by
      grind
    zuklj
    · rcases lt_or_eq_of_le (le_trans hA1 hge) with hlt | heq'
      · -- `c'` is attached strictly inside the gap
        exact hyq (hG.gapOut c' hc' pb₁ tb₁ hB₁ hlt by_grind y hyc _
          ztvuz hyS hqS)
      · -- both at the split vertex before the gap
        have hA' : ztrgw := le_antisymm by_grind hA1
        obtain ⟨hp1, ht1⟩ := hC.key_of_off₂ hL1n hB₁.1 hB₁.2.1 hB₁.2.2.1 le_rfl one_pos by_grind
        obtain ⟨hp2, ht2⟩ := hC.key_of_off₂ hL1n hA.1 hA.2.1 hA.2.2.1 le_rfl one_pos by_grind
        zqvv
        exact hcc (hG.oneAt L1 ztp c hc c' hc' hA'' hB₁')
    · -- both at the second copy of the split vertex
      have hoaL1 : ztorh := le_antisymm by_grind hoaL
      zqvq
      zqvp
      zqvw
      exact hcc (hG.oneAt _ ztbt c hc c' hc' hA'' hA₁')
  by_cases h : Btw ztjtg ztxkd ztznf
  · zuite
  · zuitf

/-- **Lemma (K3), generic form.**  Two positions of the stretch of `M` (inside walk edges, not
cuts of `F`) facing the same region of `F` correspond to positions of `M₂` facing the same region
of `S`, or the gap lies between them and their regions of `S` are the ones faced just after the
split vertex of `M₂` (before the gap) and just before its second copy (after the gap). -/
theorem label_gen3 (hC : Corr0 M M₂ F S g g' L1 L2 δ) (hG : 0 < δ → CorrGap M M₂ F S g g' L1 L2 δ)
    {d d' : ℕ} (hd : d < L1 + L2) (hd' : d' < L1 + L2) {t t' : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (ht' : t' ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut F ztwjt)
    (hcut' : ¬ M.IsCut F ztwlq) {U : Set Point}
    (hU : U ∈ M.regions F) (hf : M.Faces ztwje t U)
    (hf' : M.Faces ztxlv t' U) {V V' : Set Point} (hV : V ∈ M₂.regions S)
    (hV' : V' ∈ M₂.regions S) (hfV : M₂.Faces ztuj t V)
    (hfV' : M₂.Faces ztbaai t' V') :
    V = V' ∨ (0 < δ ∧ AfterFaces M₂ ztckj 0 V ∧
        BeforeFaces M₂ ztysu 0 V') ∨
      (0 < δ ∧ BeforeFaces M₂ ztysu 0 V ∧
        AfterFaces M₂ ztckj 0 V') := by
  by_cases hVV : V = V'
  · simp_all
  right
  zugmx
  zudox
  zuixt
  have hc₂' := hC.not_cut₂ hd' ht' hcut'
  obtain ⟨c, hc, hsepc⟩ : ∃ c ∈ S, M₂.Separates c (((g' + dq L1 δ d) % M₂.W.n : ℕ) + t)
      ((ztikt % M₂.W.n : ℕ) + t') := by
    zubaj

    exact hVV ((hC.hM₂.eq_iff_not_separates hC.hS hC.hSfin hV hV' ztbar
      ztbar ht ht' hc₂ hc₂' hfV hfV').2 hno)
  obtain ⟨pa, pb, ta, tb, hA, hB, hAB, hiff⟩ := hsepc
  have hsep := hC.sep₂_btw hc ztbar ztbar ht ht' hc₂ hc₂' hA hB hAB hiff
  rw [hC.off_M₂ hd ht.1.le ht.2, hC.off_M₂ hd' ht'.1.le ht'.2] at hsep
  -- the attachment between the counterparts is in the gap
  have hsame : ∀ {e : Set Point}, e ∈ F → ¬ M.Separates e _
      ztwlq := fun he hs =>
    (hC.hM.eq_iff_not_separates hC.hF hC.hfin hU hU zthp zthp ht ht'
      hcut hcut' hf hf').1 rfl _ he hs
  have hdd : ztkzb := by
    zuq
    obtain ⟨e1, e2⟩ := Chazelle.Chain.sideKey_inj ht.1.le ht.2 ht'.1.le ht'.2 h
    simp_all
  have gap_of : ∀ {pa pb : ℕ} {ta tb : ℝ}, SideAttach M₂.W c pa ta → SideAttach M₂.W c pb tb →
      sidePt M₂.W pa ta ≠ sidePt M₂.W pb tb →
      Btw ztnb ztrj ztwqr →
      ¬ Btw ztnb ztrj ztwpg →
      InGap L1 δ ztwqr := by
    intro pa pb ta tb hA hB hAB hin hout
    rcases hC.mirror hd hd' ht ht' hc hA hB hAB hin hout with
      ⟨e, he, p₁, p₃, t₁, t₃, hA₁, hA₃, hne, hb1, hb3⟩ | hg
    · exact absurd (hC.sepM hd hd' ht ht' hcut hcut' hdd he hA₁ hA₃ hne hb1 hb3) (hsame he)
    omega
  -- orient the separating chord
  obtain ⟨pa, pb, ta, tb, hA, hB, hin, hout⟩ : ∃ pa pb ta tb, SideAttach M₂.W c pa ta ∧
      SideAttach M₂.W c pb tb ∧
      Btw ztnb ztrj ztwqr ∧
      ¬ Btw ztnb ztrj ztwpg ∧
      InGap L1 δ ztwqr := by
    by_cases h : Btw ztnb ztrj ztwqr
    · exact ⟨pa, pb, ta, tb, hA, hB, h, hsep.1 h, gap_of hA hB hAB h ztqqt⟩
    · have h' := by_contra fun hn' => h (hsep.2 hn')
      exact ⟨pb, pa, tb, ta, hB, hA, h', h, gap_of hB hA zteno h' h⟩
  obtain ⟨hgap, hin', hout'⟩ := And.intro hout.2 (And.intro hin hout.1)
  -- the two positions lie on both sides of the gap
  have hng := not_inGap_dq (L1 := L1) (δ := δ) (d := d) ht.1 ht.2
  have hng' := not_inGap_dq (L1 := L1) (δ := δ) (d := d') ht'.1 ht'.2
  have hδ0 : ztiwv := Nat.cast_nonneg _
  have side : ∀ k : ℕ, ∀ s : ℝ, s ∈ Ioo (0 : ℝ) 1 → (k < L1 → ((dq L1 δ k : ℕ) : ℝ) + s < L1) ∧
      (L1 ≤ k → (L1 : ℝ) + δ < ((dq L1 δ k : ℕ) : ℝ) + s) := by
    intro k s hs
    constructor
    · zuibt
      have : (k : ℝ) + 1 ≤ L1 := by exact_mod_cast hk
      unfold dq; rw [ite_eq_left hk]; zunui
    · zuibt
      have : (L1 : ℝ) ≤ k := by exact_mod_cast hk
      unfold dq; zvmyd; push_cast; zuofw
  obtain ⟨hg1, hg2⟩ := hgap
  rcases lt_or_ge d L1 with hdL | hdL
  · have hLd : L1 ≤ d' := by
      zqvo
      have a1 := (side d t ht).1 hdL
      have a2 := (side d' t' ht').1 hlt
      zqwe
    have hδp : ztcfy := by
      zqvr
      · have := hC.hδ h; omega
      omega
    zulhw
    exact Or.inl ⟨hδp, hC.gapS_of hG' hdL hLd hd' ht ht' hcut hcut' hU hf hf' hc hA hB by_grind
      hout' hV hfV,
      hC.gapE_of hG' hdL hLd hd' ht ht' hcut hcut' hU hf hf' hc hA hB by_grind hout' hV' hfV'⟩
  · have hLd : d' < L1 := by
      zqvo
      have a1 := (side d t ht).2 hdL
      have a2 := (side d' t' ht').2 hlt
      zqwe
    have hδp : ztcfy := by
      zqvr
      · have := hC.hδ h; omega
      omega
    zulhw
    exact Or.inr ⟨hδp, hC.gapE_of hG' hLd hdL hd ht' ht hcut' hcut hU hf' hf hc hA hB by_grind
      ztqnv hV hfV,
      hC.gapS_of hG' hLd hdL hd ht' ht hcut' hcut hU hf' hf hc hA hB by_grind
      ztqnv hV' hfV'⟩
end Corr0
end Sweep
end
end Chazelle.Core
end
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf sideE sidePrev sideNext)
open Chazelle.Visibility (rayPt)
open WalkEmbed
namespace Sweep
section Vertex
variable (C : Chain)

/-- **A walk position at a chain vertex** is a tour vertex visiting it (the box, the slit and the
open tour edges contain no chain vertex). -/
theorem pos_eq_vertex (hP : C.P.Simple) (β : Bool) {p : ℕ} (hp : p < (C.sideWalk β).n) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) {k : ℕ} (hk : k ≤ C.m)
    (h : sidePt ztft p t = C.vertex k) :
    t = 0 ∧ ∃ i, i ≤ 2 * C.m ∧ p = i + 6 ∧ C.sideIdx β i = k := by
  zubo
  have hvk := C.vertex_mem_set hk
  have hb := C.abs_le_coordBound_of_mem_set hvk
  zugma
  have hvtop := C.vertex_snd_le_top hk
  zuop

  · exfalso
    interval_cases p
    · grind
    · grind
    · grind
    · grind
    · grind
    · rw [h5] at h; have := congrArg Prod.snd h; simp only at this
      nlinarith
  · exfalso
    rw [h6] at h; have := congrArg Prod.snd h; simp only at this
    nlinarith
  · rcases ht.lt_or_eq with htp | rfl
    · exfalso
      have hi2 : ztdrl := by
        grind
      rw [C.sidePt_tour β hi2] at h
      zumqk
      rcases C.sideTour_step β i with hs | hs
      · zukwa
        exact C.sideOpen_ne_vertex hP ztuij h
      · rw [← hs] at h
        have e : Geometry.lerp ztwww ztbalx
            t = Geometry.lerp ztbalx ztwww
            ztca := by
          zubvj
        zudtt
        exact C.sideOpen_ne_vertex hP ztbcx h
    · refine ztlwn
      rw [Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_tour β hi] at h
      exact C.sideVertex_inj hP ztdfj hk h

/-- Arithmetic of the tour positions at vertex `0`: offset `0`, or `2m` when the tour starts at
the box. -/
theorem vertex0_arith {m b i : ℕ} (hm : 0 < m) (hb : b ≤ 2 * m) (hi : i ≤ 2 * m)
    (h : ztbcn % ztdk = 0) :
    ztxqy % ztfk = 0 ∨
      (ztekf % ztdk = 0 ∧
        ztxqy % ztfk = 2 * m) := by
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h
  have hq2 : q ≤ 2 := by
    zubdj
  have hτ : ztekf % ztdk = if b = 0 then 0 else 2 * m - b := by
    split_ifs with hb0
    · simp_all
    · rw [Nat.mod_eq_of_lt (show 0 + 2 * m - b < 2 * m by omega)]; omega
  rw [hτ]
  have key : ∀ x, x < 2 * ztfk →
      x % ztfk = if x < 2 * m + 7 then x else x - ztfk := by
    zuetm
    · simp_all
    · zul
  interval_cases q <;> split_ifs with hb0 <;> zuopi <;> split_ifs <;> omega

/-- **The positions at vertex `0`** of the walk of a chain model, read from the tour position `0`:
offset `0`, or offset `2m` when the tour position `0` is the box. -/
theorem off_vertex0 (hP : C.P.Simple) {p : ℕ} (hp : p < (chainModel C).W.n) {t : ℝ} (ht : 0 ≤ t)
    (ht1 : t < 1) (h : sidePt (chainModel C).W p t = C.vertex 0) :
    off (chainModel C).W.n ((6 + tpos C 0 : ℕ) : ℝ) ztk = 0 ∨
      (tpos C 0 = 0 ∧ off (chainModel C).W.n ((6 + tpos C 0 : ℕ) : ℝ) ztk = 2 * C.m) := by
  obtain ⟨rfl, i, hi, rfl, hidx⟩ := pos_eq_vertex C hP C.sideBeta hp ht ht1 ztbg h
  zukk
  have hτ := tpos_lt C 0
  zubco
  zugwt
  have h0 : ztrkt % ztbb = 0 := by
    zugtp

    have := Nat.mod_lt ztwz hm
    split_ifs at hidx
    · tauto
    · omega
  have := vertex0_arith (m := C.m) (b := bS C) (i := i) by_omega ztveq hi h0
  zujqj
  zubdb
  zufqh

  · left; zvmwc; simp
  · zujga
end Vertex

/-! ## The families -/
section Families
variable (J : Merge.Junction)

/-- **The top chords of `C` at the top of `C₂`** (the vertex chords of `C` at its vertex
`m₁ + topIdx C₂`). -/
def topChords₂ : Set ztf :=
  {d | ∃ σ : ℝ, ztdd ∧ J.whole.DirFree ztrw σ ∧
    d = J.whole.chordSet ztrw σ}

/-- **The family `F₂⁺`** of the sweep, in the model of `C`: the fusion of `∅` and `S₂` (the chords
of `C` seen from the endpoints of the chords of `S₂`, and the shared chords) and the top chords
at the top of `C₂`. -/
def F₂plus (S₂ : Set ztf) : Set ztf := J.fusion ∅ S₂ ∪ topChords₂ J
theorem topChords₂_subset_chords : topChords₂ J ⊆ J.whole.chords := by
  zugbd
  have := J.right.topIdx_le
  exact ⟨_, σ, by_simp_all,
    hσ, hfree, rfl⟩
variable {S₂ : Set (Set Point)}
theorem F₂plus_subset (hS₂ : S₂ ⊆ Merge.augChords J.right) :
    F₂plus J S₂ ⊆ Merge.augChords J.whole := by
  zujgd
  · exact J.fusion_subset_augChords ztzi hS₂ he
  · exact Merge.chords_subset_augChords _ (topChords₂_subset_chords J he)
theorem F₂plus_finite (hS₂ : S₂.Finite) : (F₂plus J S₂).Finite :=
  (J.fusion_finite finite_empty hS₂).union (J.whole.chords_finite.subset (topChords₂_subset_chords J))

/-- Distinct augmented chords are not nested. -/
theorem augChords_nest {C : Chain} {e e' : Set Point} (he : e ∈ Merge.augChords C)
    (he' : e' ∈ Merge.augChords C) (h : e ⊆ e') : e = e' := by
  obtain ⟨y, a, b, hh, -, rfl⟩ := he
  obtain ⟨y', a', b', hh', -, rfl⟩ := he'
  zumcx
  have hp : (ztwsj : Point) ∈ Visibility.hseg y a b :=
    ⟨rfl, by_grind, by_grind⟩
  rcases Chain.hchordIn_inter hh hh' hp ztvrm with ⟨rfl, rfl, rfl⟩ | ⟨h1, -⟩
  · rfl
  grind

/-- **Endpoints of the chords of `S₂`** other than the shared vertex lie on chords of the fusion
inside them. -/
theorem trans_right (hP : J.P.Simple) {S₂ : Set ztf} (hS₂ : S₂ ⊆ Merge.augChords J.right) :
    ∀ c ∈ S₂, ∀ q ∈ c, q ∉ J.right.dom → q ≠ J.shared → ∃ e ∈ F₂plus J S₂, q ∈ e ∧ e ⊆ c := by
  zujaw
  zubdz

  zubhe

  · zubui
    · exact absurd ztwl
        hqD
    · zubqx

  · zubqw
end Families

/-! ## The correspondence for the right side of a junction -/
section CorrRight
variable (J : Merge.Junction)

/-- The length of the right stretch of the walk of `C` (read from the copy of the shared vertex
left towards `C₂`): the tour of `C₂`, and the box of `C` when it lies inside. -/
noncomputable def rlen : ℕ :=
  if 2 * J.whole.m - tpos J.whole J.m₁ < 2 * J.m₂ then 2 * J.m₂ + 7 else 2 * J.m₂

/-- The length of the first agreeing piece of the right correspondence (`Sweep.Corr`): the whole
stretch (with the box of `C`) in case Sh, the tour of `C₂` in case N, up to the box of `C₂` in
case G. -/
noncomputable def rL1 : ℕ :=
  if 2 * J.whole.m - tpos J.whole J.m₁ < 2 * J.m₂ then 2 * J.m₂ + 7
  else if 2 * J.m₂ ≤ 2 * J.right.m - tpos J.right 0 then 2 * J.m₂
  else 2 * J.right.m - tpos J.right 0

/-- The length of the second agreeing piece of the right correspondence (case G only). -/
noncomputable def rL2 : ℕ :=
  if 2 * J.whole.m - tpos J.whole J.m₁ < 2 * J.m₂ then 0
  else if 2 * J.m₂ ≤ 2 * J.right.m - tpos J.right 0 then 0
  else 2 * J.m₂ - ztbxt

/-- The gap of the right correspondence: the box block of `C₂` in case G. -/
noncomputable def rδ : ℕ :=
  if 2 * J.whole.m - tpos J.whole J.m₁ < 2 * J.m₂ then 0
  else if 2 * J.m₂ ≤ 2 * J.right.m - tpos J.right 0 then 0
  else 7
theorem rL1_add_rL2 : rL1 J + rL2 J = rlen J := by
  have := tpos_lt J.right 0
  zunc
  unfold rL1 rL2 rlen
  grind
end CorrRight

/-! ## Lemma (K) for a junction -/
section LabelRight
variable (J : Merge.Junction)

/-- **The label of a region of `F₂⁺`**: `RLabel J S₂ G V` says that some position inside a walk
edge of the right stretch of the walk of `C`, not a cut of `F₂⁺`, faces `G`, and the corresponding
position of the walk of `C₂` faces `V`. -/
def RLabel (S₂ : Set ztf) (G V : Set Point) : Prop :=
  ∃ d < rL1 J + rL2 J, ∃ t ∈ Ioo (0 : ℝ) 1,
    ¬ (chainModel J.whole).IsCut ztbi
        ((ztbabb % (chainModel J.whole).W.n : ℕ) + t) ∧
      (chainModel J.whole).Faces (ztbabb % (chainModel J.whole).W.n) t G ∧
      (chainModel J.right).Faces
        ((ztbrv + dq ztns ztpg d) % (chainModel J.right).W.n) t V
end LabelRight
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf sideE sidePrev sideNext)
open Chazelle.Visibility (rayPt)
open WalkEmbed
namespace Sweep
section VertexEnd
variable (C : Chain)

/-- Arithmetic of the tour positions at the last vertex `m`. -/
theorem vertexEnd_arith {m b i : ℕ} (hm : 0 < m) (hb : b ≤ 2 * m) (hi : i ≤ 2 * m)
    (h : ztbcn % ztdk = m) :
    ztxqz % ztfk = 0 ∨
      (zthin % ztdk = 0 ∧
        ztxqz % ztfk = 2 * m) := by
  have hq : b + i = ztbcn / ztdk * ztdk + m := by
    have := Nat.div_add_mod ztbcn ztdk
    grind
  have hq2 : ztbcn / ztdk ≤ 1 := by
    zuca
    have : 2 * ztdk ≤ ztbcn / ztdk * ztdk := Nat.mul_le_mul_right _ hc
    omega
  have key : ∀ x, x < 2 * ztfk →
      x % ztfk = if x < 2 * m + 7 then x else x - ztfk := by
    zuetm
    · zubql
    · zul
  have key2 : ∀ x, x < 2 * ztdk → x % ztdk = if x < 2 * m then x else x - 2 * m := by
    zuetm
    · zubql
    · zul
  rw [key2 _ by_omega]
  interval_cases hq' : ztbcn / ztdk <;> split_ifs <;> zuopi <;>
    zuwd

/-- **The positions at the last vertex** of the walk of a chain model, read from its tour
position: offset `0`, or offset `2m` when that tour position is `0`. -/
theorem off_vertexEnd (hP : C.P.Simple) {p : ℕ} (hp : p < (chainModel C).W.n) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (h : sidePt (chainModel C).W p t = C.vertex C.m) :
    off (chainModel C).W.n ((6 + tpos C C.m : ℕ) : ℝ) ztk = 0 ∨
      (tpos C C.m = 0 ∧ off (chainModel C).W.n ((6 + tpos C C.m : ℕ) : ℝ) ztk = 2 * C.m) := by
  obtain ⟨rfl, i, hi, rfl, hidx⟩ := pos_eq_vertex C hP C.sideBeta hp ht ht1 le_rfl h
  zukk
  have hτ := tpos_lt C C.m
  zubco
  zugwt
  have h0 : ztrkt % ztbb = C.m := by
    zugtp

    have := Nat.mod_lt ztwz hm
    split_ifs at hidx
    · tauto
    · omega
  have := vertexEnd_arith (m := C.m) (b := bS C) (i := i) by_omega ztveq hi h0
  zujqj
  zubdb
  zufqh

  · left; simp_all
  · right; exact ⟨h1, by zvmxx; simp⟩
end VertexEnd

/-! ## The families -/
section FamiliesL
variable (J : Merge.Junction)

/-- **The top chords of `C` at the top of `C₁`** (the vertex chords of `C` at its vertex
`topIdx C₁`). -/
def topChords₁ : Set ztf :=
  {d | ∃ σ : ℝ, ztdd ∧ J.whole.DirFree J.left.topIdx σ ∧
    d = J.whole.chordSet J.left.topIdx σ}

/-- **The family `F₁⁺`** of the mirror sweep, in the model of `C`. -/
def F₁plus (S₁ : Set ztf) : Set ztf := J.fusion S₁ ∅ ∪ topChords₁ J
theorem topChords₁_subset_chords : topChords₁ J ⊆ J.whole.chords := by
  zugbd
  have := J.left.topIdx_le
  exact ⟨_, σ, by simp only [Merge.Junction.whole_m, Merge.Junction.left_m] at this ⊢; omega,
    hσ, hfree, rfl⟩
variable {S₁ : Set (Set Point)}
theorem F₁plus_subset (hS₁ : S₁ ⊆ Merge.augChords J.left) :
    F₁plus J S₁ ⊆ Merge.augChords J.whole := by
  zujgd
  · exact J.fusion_subset_augChords hS₁ ztzi he
  · exact Merge.chords_subset_augChords _ (topChords₁_subset_chords J he)
theorem F₁plus_finite (hS₁ : S₁.Finite) : (F₁plus J S₁).Finite :=
  (J.fusion_finite hS₁ finite_empty).union (J.whole.chords_finite.subset (topChords₁_subset_chords J))

/-- **Endpoints of the chords of `S₁`** other than the shared vertex lie on chords of the fusion
inside them. -/
theorem trans_left (hP : J.P.Simple) {S₁ : Set ztf} (hS₁ : S₁ ⊆ Merge.augChords J.left) :
    ∀ c ∈ S₁, ∀ q ∈ c, q ∉ J.left.dom → q ≠ J.shared → ∃ e ∈ F₁plus J S₁, q ∈ e ∧ e ⊆ c := by
  zujaw
  obtain ⟨hL, hR⟩ := J.end_mem_fusion hP hS₁ ztzi ztjkr
  obtain ⟨y, a, b, hH, -, rfl, hl, hr⟩ := Merge.augChords_spec ztmkw
  zubhe

  · zubui
    · exact absurd ztwl
        hqD
    · zubqx

  · zubqw
end FamiliesL

/-! ## The correspondence for the left side of a junction -/
section CorrLeft
variable (J : Merge.Junction)

/-- The length of the left stretch of the walk of `C` (read from the copy of the shared vertex
left towards `C₁`). -/
noncomputable def llen : ℕ :=
  if 2 * J.whole.m - tpos J.whole ztbv < 2 * J.m₁ then 2 * J.m₁ + 7 else 2 * J.m₁

/-- The length of the first agreeing piece of the left correspondence. -/
noncomputable def lL1 : ℕ :=
  if 2 * J.whole.m - tpos J.whole ztbv < 2 * J.m₁ then 2 * J.m₁ + 7
  else if 2 * J.m₁ ≤ 2 * J.left.m - tpos J.left J.m₁ then 2 * J.m₁
  else 2 * J.left.m - tpos J.left J.m₁

/-- The length of the second agreeing piece of the left correspondence (case G only). -/
noncomputable def lL2 : ℕ :=
  if 2 * J.whole.m - tpos J.whole ztbv < 2 * J.m₁ then 0
  else if 2 * J.m₁ ≤ 2 * J.left.m - tpos J.left J.m₁ then 0
  else 2 * J.m₁ - ztnfc

/-- The gap of the left correspondence: the box block of `C₁` in case G. -/
noncomputable def lδ : ℕ :=
  if 2 * J.whole.m - tpos J.whole ztbv < 2 * J.m₁ then 0
  else if 2 * J.m₁ ≤ 2 * J.left.m - tpos J.left J.m₁ then 0
  else 7
theorem lL1_add_lL2 : lL1 J + lL2 J = llen J := by
  have := tpos_lt J.left J.m₁
  zufd
  unfold lL1 lL2 llen
  grind
end CorrLeft

/-! ## Lemma (K) for the left side -/
section LabelLeft
variable (J : Merge.Junction)
end LabelLeft
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideLeft sidePrev sideNext)
open Chazelle.Visibility (rayPt)
open WalkEmbed
namespace Sweep
variable (J : Merge.Junction)
theorem corr_left0 (hP : J.P.Simple) {S₁ : Set ztf}
    (hS₁ : S₁ ⊆ Merge.augChords J.left) (hS₁f : S₁.Finite) :
    Corr0 ztbm ztbw (F₁plus J S₁) S₁
      ztxfw ztgcv ztdov (lL2 J) ztety := by
  unfold lL1 lL2 lδ
  zugft
  set C₁ := J.left with hC₁
  zubqe
  set W₁ := (chainModel C₁).W with hW₁
  have hn : ztiyt := cm_n C
  have hn₁ : W₁.n = 2 * C₁.m + 7 := cm_n C₁
  have hwm : ztsav := rfl
  have hm1 : C₁.m = J.m₁ := rfl
  zufz

  set τ := tpos C ztbv with hτ_def
  set τ' := tpos C₁ J.m₁ with hτ'_def
  have hτ : τ < 2 * C.m := tpos_lt C _
  have hτ' : τ' < 2 * C₁.m := tpos_lt C₁ _
  set ℓ := 2 * J.m₁ with hℓ_def
  zugyu
  set s' := 2 * C₁.m - τ' with hs'_def
  have hT : ∀ e, e ≤ ℓ → tourV C ztbv e = tourV C₁ J.m₁ e :=
    fun e he => tourV_left J he
  zucvy
  have hM₁ := walkAx_chainModel (C := C₁) hP
  have hR : C₁.radius = C.radius := FuseMath.radius_of_P J rfl
  zukcb
  have hg' : 6 + τ' < W₁.n := by_omega
  have hv0 : W₁.vtx ztfmx = J.shared := by
    have := walk_tour C₁ J.m₁ 0 by_omega
    rw [add_zero, Nat.mod_eq_of_lt hg', tourV_left_zero] at this
    omega
  have hnoV : ∀ L : ℝ, (τ' = 0 → L ≤ 2 * C₁.m) → ∀ p < W₁.n, ∀ t : ℝ, 0 ≤ t → t < 1 →
      0 < off W₁.n ((6 + τ' : ℕ) : ℝ) ztk → off W₁.n ((6 + τ' : ℕ) : ℝ) ztk < L →
      sidePt W₁ p t ≠ W₁.vtx ztfmx := by
    zufxg
    rw [hv0, show J.shared = C₁.vertex C₁.m from rfl] at heq
    have hvx := off_vertexEnd C₁ hP hp ht ht1 heq
    grind
  have htrans : ∀ c ∈ S₁, ∀ q ∈ c, q ∉ (chainModel C₁).D → q ≠ W₁.vtx ztfmx →
      ∃ e ∈ F₁plus J S₁, q ∈ e ∧ e ⊆ c := by
    rw [hv0]; exact trans_left J hP hS₁
  have hnest : ∀ e ∈ F₁plus J S₁, ∀ e' ∈ F₁plus J S₁, e ⊆ e' → e = e' :=
    fun e he e' he' h => augChords_nest (F₁plus_subset J hS₁ he) (F₁plus_subset J hS₁ he') h
  have hFs := F₁plus_subset J hS₁
  have hFf := F₁plus_finite J hS₁f
  zukhv
  have hℓ' : ℓ ≤ 2 * C₁.m := by_omega
  have hℓ'R : (ℓ : ℝ) ≤ 2 * C₁.m := by_grind
  zudmg
  · -- case Sh
    have hss : ztppv := (left_box_eq J hsl).symm
    zubno
    zuger
    refine ⟨hM, hM₁, hFs, hFf, hS₁, hS₁f, hg, hg', by_grind,
      by grind, fun _ => rfl, fun h => absurd h ztgkw, hA, ?_,
      hnoV _ ztpbp, htrans, hnest⟩
    zuip
    zudqk
    simpa using hA ztole le_rfl
  zucyg

  · -- case N
    zucvr
    rw [ite_eq_right ztbew, ite_eq_right ztbew,
      ite_eq_right ztbew, ite_eq_left hsl', ite_eq_left hsl', ite_eq_left hsl']
    refine ⟨hM, hM₁, hFs, hFf, hS₁, hS₁f, hg, hg', by_grind,
      by grind, fun _ => rfl, fun h => absurd h ztgkw, hA, ?_,
      hnoV _ ztfrh, htrans, hnest⟩
    zuip
    zudqk
    zulsm
  -- case G
  zuzm

  zukfn
  rw [ite_eq_right ztbew, ite_eq_right ztbew,
    ite_eq_right ztbew, ite_eq_right zthkk,
    ite_eq_right zthkk, ite_eq_right zthkk]
  refine ⟨hM, hM₁, hFs, hFf, hS₁, hS₁f, hg, hg', by_grind,
    by grind, fun h => absurd h by_norm_num, fun _ => by_grind, hA1, ?_,
    hnoV _ ztpbp, htrans, hnest⟩
  · zuip
    have := hA2 d hd
    grind
end Sweep
end
end Chazelle.Core
section
set_option hygiene false
local macro "zqbdu" : tactic => `(tactic| (unfold sideCcw sideCross sideDot at h
                                           simp only at h
                                           rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩))
local macro "zqbdv" : tactic => `(tactic| (set C := J.whole with hC
                                           set C₂ := J.right with hC₂
                                           zubqe
                                           set W₂ := (chainModel C₂).W with hW₂
                                           have hn : ztiyt := cm_n C))
local macro "zqbdw" : tactic => `(tactic| (have hwm : ztsav := rfl
                                           have hm2 : C₂.m = J.m₂ := rfl
                                           zufz

                                           set τ := tpos C J.m₁ with hτ_def
                                           set τ' := tpos C₂ 0 with hτ'_def))
local macro "zqbdx" : tactic => `(tactic| (set s' := 2 * C₂.m - τ' with hs'_def
                                           have hT : ∀ e, e ≤ ℓ → tourV C J.m₁ e = tourV C₂ 0 e := fun e he => tourV_right J he))
local macro "zqbdy" : tactic => `(tactic| (obtain ⟨b1, b2⟩ := B
                                           obtain ⟨a1, a2⟩ := A))
local macro "zqbdz" : tactic => `(tactic| (obtain ⟨g1, g2, v26, v0, v25, v6, v5, v7⟩ := gap_walk J hδ
                                           have hn₂ := cm_n J.right))
local macro "zqbea" : tactic => `(tactic| (have hA1 := agree_G1 hT hsl hsl'
                                           have hA2 := agree_G2 hT hℓ' hsl hsl'
                                           have hs'1 : ztsaa := by_omega))
local macro "zqbeb" : tactic => `(tactic| (simp only [sideCcw, sideCross, sideDot] at hc ⊢
                                           rcases hc with hc | ⟨hc, hd⟩))
local macro "zqbec" : tactic => `(tactic| (refine Or.inr (Or.inr (Or.inr ⟨hc, hd, ?_⟩))
                                           by_cases hb2 : b2 = 0))
local macro "zqbed" : tactic => `(tactic| obtain ⟨hL1, hδ7, -, -, -⟩ := caseG_consts J hδ)
set_option hygiene true

/-!
# The sweep (WP-D), part 5b: the right correspondence without `TopStrict` (F2)

With ties at the top of `C₂` the top chord at the split vertex may end on `C₂`, so the
correspondence of `SweepLabelJ.corr_right` loses its separating chord.  This file gives the
correspondence without it (`corr_right0 : Corr0 …`) and the gap facts of case G
(`corrGap_right : CorrGap …`), so that lemma (K3) (`SweepLabelGap.Corr0.label_gen3`) applies.

* `ccw_up_left`, `ccw_up_right`, `ccw_lower_left`, `ccw_lower_right`: horizontal directions in
  corners at a top vertex, next to a vertical slit.
-/
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf sideCcw sideCross sideDot)
open Chazelle.Visibility (rayPt)
open WalkEmbed
namespace Sweep
variable {a x : ℝ}
/-- A horizontal direction in the corner from the upward slit to a direction `A` not above the
horizontal points west. -/
theorem ccw_up_left {A : Point} (ha : 0 < a) (hA : A.2 ≤ 0)
    (h : sideCcw (ztfmp : Point) (ztcxb : Point) A) : x < 0 := by
  zqbdu
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-- A horizontal direction in the corner from a direction `B` not above the horizontal to the
upward slit points east. -/
theorem ccw_up_right {B : Point} (ha : 0 < a) (hB : B.2 ≤ 0)
    (h : sideCcw B (ztcxb : Point) (ztfmp : Point)) : 0 < x := by
  zqbdu
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-- **A horizontal direction in a corner below the horizontal** forces the corner to turn
clockwise or to be a straight angle turned upwards: for `B`, `A` not above the horizontal,
`sideCcw B (σ₀, 0) A` gives `sideCross B A < 0` or `sideCross B A = 0 ∧ 0 < sideDot B A`. -/
theorem ccw_horiz_lower {σ₀ : ℝ} {A B : Point} (hA : A.2 ≤ 0) (hB : B.2 ≤ 0)
    (h0 : sideCcw B (ztolc : Point) A) :
    sideCross B A < 0 ∨ ztkfb := by
  zqbdy
  zulsl
  simp only [sideCcw, sideCross, sideDot] at h0 ⊢
  rcases h0 with ⟨h1, h2, h3⟩ | ⟨h1, -⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, -⟩
  · exfalso
    have : 0 < (-(b2 * σ₀)) * (σ₀ * a2) := mul_pos by_linarith by_linarith
    nlinarith [mul_nonneg (neg_nonneg.2 hB) (neg_nonneg.2 hA), sq_nonneg σ₀]
  · simp_all
  · exfalso
    have key : a2 * (b1 * a1 + b2 * a2) = b2 * ztnqz := by
      grind
    have hl := mul_nonneg_of_nonpos_of_nonpos hA h2.le
    have hsq : 0 < a1 ^ 2 + a2 ^ 2 := by
      zukr
      have ha1 : a1 = 0 := by nlinarith [sq_nonneg a1, sq_nonneg a2]
      simp_all
    have hb2 : ztsdt := by
      have : 0 ≤ b2 * ztnqz := by_simp_all
      have : 0 ≤ b2 := by
        simp_all
      linarith
    simp_all
  simp_all

/-- **The corner of a top vertex contains the corner before the slit**: if the corner from `B`
to `A` (both not above the horizontal) contains a horizontal direction, it contains every
horizontal direction of the corner from the upward slit to `A`. -/
theorem ccw_lower_left {a x σ₀ : ℝ} {A B : Point} (ha : 0 < a) (hA : A.2 ≤ 0) (hB : B.2 ≤ 0)
    (h0 : sideCcw B (ztolc : Point) A) (h : sideCcw (ztfmp : Point) (ztcxb : Point) A) :
    sideCcw B (ztcxb : Point) A := by
  have hx := ccw_up_left ha hA h
  have hAw : A.2 < 0 ∨ 0 < A.1 := by
    zqbdu
    · zuhgz
    · simp_all
    · simp_all
    · zuhgz
    grind
  have hc := ccw_horiz_lower hA hB h0
  zqbdy
  simp only at hA hB hAw
  zqbeb
  · refine Or.inr (Or.inl ⟨hc, Or.inr ?_⟩)
    rcases lt_or_eq_of_le hA with ha2 | ha2
    · nlinarith
    · exfalso
      zuipv

      · linarith
      · nlinarith
  · zqbec
    · right
      subst hb2
      have hb1 : b1 ≠ 0 := by rintro rfl; simp_all
      have ha2 : a2 = 0 := by
        simp_all
      zuipv

      · linarith
      · have : 0 < b1 := by_nlinarith
        nlinarith
    grind

/-- **The corner of a top vertex contains the corner after the slit**: if the corner from `B`
to `A` (both not above the horizontal) contains a horizontal direction, it contains every
horizontal direction of the corner from `B` to the upward slit. -/
theorem ccw_lower_right {a x σ₀ : ℝ} {A B : Point} (ha : 0 < a) (hA : A.2 ≤ 0) (hB : B.2 ≤ 0)
    (h0 : sideCcw B (ztolc : Point) A) (h : sideCcw B (ztcxb : Point) (ztfmp : Point)) :
    sideCcw B (ztcxb : Point) A := by
  have hx := ccw_up_right ha hB h
  have hBw : B.2 < 0 ∨ B.1 < 0 := by
    zqbdu
    · zuhgz
    · zujfz
    · zujfz
    · zuhgz
    · zuhgz
  have hc := ccw_horiz_lower hA hB h0
  zqbdy
  simp only at hA hB hBw
  zqbeb
  · refine Or.inr (Or.inl ⟨hc, Or.inl ?_⟩)
    rcases lt_or_eq_of_le hB with hb2 | hb2
    · nlinarith
    · exfalso
      zuipw

      · linarith
      · nlinarith
  · zqbec
    · right
      zuipw

      · linarith
      · nlinarith
    grind

/-! ## The correspondence without a separating chord -/
section CorrRight0
variable (J : Merge.Junction)
theorem corr_right0 (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) :
    Corr0 ztbm ztj ztbi S₂
      ztve ztbrv ztns ztqvh ztpg := by
  unfold rL1 rL2 rδ
  zqbdv
  have hn₂ : W₂.n = 2 * C₂.m + 7 := cm_n C₂
  zqbdw
  have hτ := tpos_lt C J.m₁
  zuehm

  zugyu
  zqbdx
  zucvy
  have hM₂ := walkAx_chainModel (C := C₂) hP
  have hR : C₂.radius = C.radius := FuseMath.radius_of_P J rfl
  zukcb
  have hg' : 6 + τ' < W₂.n := by_omega
  have hv0 : W₂.vtx ztfmx = J.shared := by
    have := walk_tour C₂ 0 0 by_omega
    rw [add_zero, Nat.mod_eq_of_lt hg', tourV_right_zero] at this
    omega
  have hnoV : ∀ L : ℝ, (τ' = 0 → L ≤ 2 * C₂.m) → ∀ p < W₂.n, ∀ t : ℝ, 0 ≤ t → t < 1 →
      0 < off W₂.n ((6 + τ' : ℕ) : ℝ) ztk → off W₂.n ((6 + τ' : ℕ) : ℝ) ztk < L →
      sidePt W₂ p t ≠ W₂.vtx ztfmx := by
    zufxg
    rw [hv0, ← J.right_vertex_zero] at heq
    rcases off_vertex0 C₂ hP hp ht ht1 heq with h | ⟨h0, h⟩
    · grind
    grind
  have htrans : ∀ c ∈ S₂, ∀ q ∈ c, q ∉ (chainModel C₂).D → q ≠ W₂.vtx ztfmx →
      ∃ e ∈ F₂plus J S₂, q ∈ e ∧ e ⊆ c := by
    rw [hv0]; exact trans_right J hP hS₂
  have hnest : ∀ e ∈ F₂plus J S₂, ∀ e' ∈ F₂plus J S₂, e ⊆ e' → e = e' :=
    fun e he e' he' h => augChords_nest ztfnm (F₂plus_subset J hS₂ he') h
  zudnk
  zujzh
  zukhv
  zukhw
  have hℓ'R : (ℓ : ℝ) ≤ 2 * C₂.m := by_grind
  zudmg
  · -- case Sh: the two boxes at the same offset
    have hss : ztppv := (right_box_eq J hsl).symm
    zubno
    zuger
    refine ⟨hM, hM₂, hFs, hFf, hS₂, hS₂f, hg, hg', by_grind,
      by grind, by_omega, by_omega, hA, ?_,
      by grind, htrans, hnest⟩
    zuip
    zudqk
    simpa using hA _ le_rfl
  zucyg

  · -- case N: no box inside the stretch
    zucvr
    rw [ite_eq_right by_grind, ite_eq_right ztbew,
      ite_eq_right ztbew, ite_eq_left hsl', ite_eq_left hsl', ite_eq_left hsl']
    refine ⟨hM, hM₂, hFs, hFf, hS₂, hS₂f, hg, hg', by_grind,
      by grind, by_omega, by_omega, hA, ?_,
      by grind, htrans, hnest⟩
    zuip
    zudqk
    zulsm
  -- case G: only the box of `C₂` inside the stretch
  push Not at hsl'
  zqbea
  rw [ite_eq_right by_grind, ite_eq_right ztbew,
    ite_eq_right ztbew, ite_eq_right by_grind,
    ite_eq_right by_grind, ite_eq_right by_grind]
  refine ⟨hM, hM₂, hFs, hFf, hS₂, hS₂f, hg, hg', by_grind,
    by grind, by_omega, by_grind, hA1, ?_,
    by grind, htrans, hnest⟩
  zuip
  have := hA2 d hd
  grind
end CorrRight0

/-! ## The gap facts in case G -/
section GapRight
variable (J : Merge.Junction)

/-- **The constants of case G** (a gap). -/
theorem caseG_consts (hδ : 0 < rδ J) : rL1 J = 2 * J.right.m - tpos J.right 0 ∧ rδ J = 7 ∧
    rL2 J = 2 * J.m₂ - ztbxt ∧
    2 * J.m₂ ≤ 2 * J.whole.m - tpos J.whole J.m₁ ∧
    2 * J.right.m - tpos J.right 0 < 2 * J.m₂ := by
  unfold rL1 rδ rL2 at *
  grind

/-- **Points of the stretch are points of `C₂`** in case G. -/
theorem strPt_mem_right (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) (hδ : 0 < rδ J) {x : Point}
    (hx : StrPt ztbm ztve ztqvg x) :
    x ∈ J.right.set := by
  obtain ⟨d, hd, t, ht0, ht1, -, rfl⟩ := hx
  zuv
  rw [hC.sidePt_eq hd t]
  zuuy
  zubtn
  zunc
  obtain ⟨h1, h2, h3, -, -⟩ := caseG_consts J hδ
  obtain ⟨i, hi, hq⟩ : ∃ i, i < 2 * J.right.m ∧
      ztfw % (chainModel J.right).W.n = i + 6 := by
    zujql
    rw [hn₂, h1, h2]
    split_ifs with hdl
    · exact ⟨tpos J.right 0 + d, by_omega, by zvmyc; ring⟩
    · refine ⟨d - ztbxt, by_omega, ?_⟩
      rw [show 6 + tpos J.right 0 + zttit = (d - ztbxt + 6) +
        ztqf by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
  zugvl
  exact J.right.sideWalk_tour_pt_mem _ hi.le by_grind ht0 ht1

/-- **Points strictly inside the gap are not points of `C₂`**: the slit above the top and the
sides of the box. -/
theorem gap_not_mem (hδ : 0 < rδ J) {pa : ℕ} {ta : ℝ} (hpa : pa < (chainModel J.right).W.n)
    (hta0 : 0 ≤ ta) (hta1 : ta < 1)
    (h1 : (rL1 J : ℝ) < off (chainModel J.right).W.n (6 + tpos J.right 0 : ℕ) ztbf)
    (h2 : off (chainModel J.right).W.n (6 + tpos J.right 0 : ℕ) ztbf < rL1 J + rδ J) :
    sidePt (chainModel J.right).W pa ta ∉ J.right.set := by
  zqbed
  set C₂ := J.right with hC₂
  zulkx
  have hτ' := tpos_lt C₂ 0
  have hg' : 6 + tpos C₂ 0 < (chainModel C₂).W.n := by_omega
  rw [off_key' hg' hpa hta0 hta1, hL1] at h1 h2
  rw [hδ7] at h2
  set e := dOf (chainModel C₂).W.n (6 + tpos C₂ 0) pa with he
  have hpae : (6 + tpos C₂ 0 + e) % (chainModel C₂).W.n = pa := add_dOf hg' hpa
  have hge : 2 * C₂.m - tpos C₂ 0 ≤ e := by
    zuca
    have : (e : ℝ) + 1 ≤ ((2 * C₂.m - tpos C₂ 0 : ℕ) : ℝ) := by exact_mod_cast hc
    linarith
  have hle : e ≤ 2 * C₂.m - tpos C₂ 0 + 6 := by
    zuca
    have : ((2 * C₂.m - tpos C₂ 0 : ℕ) : ℝ) + 7 ≤ e := by exact_mod_cast hc
    grind
  have hR := C₂.top_snd_lt_radius
  have hRp := C₂.radius_pos
  have hout : ∀ z : Point, (C₂.top.2 < z.2 ∨ C₂.radius ≤ |z.1| ∨ C₂.radius ≤ |z.2|) →
      z ∉ C₂.set := by
    intro z hz hmem
    have hb := C₂.set_subset_box hmem
    have htop := C₂.snd_le_top_of_mem_set hmem
    rcases hz with hz | hz | hz
    · linarith
    · exact absurd hb.1 ztwao
    · exact absurd hb.2 ztwao
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := C₂.sidePt_box C₂.sideBeta ta
  rw [cm_W] at hpa hpae ⊢
  rw [show (C₂.sideWalk C₂.sideBeta).n = 2 * C₂.m + 7 from hn₂] at hpae
  rw [← hpae]
  apply hout
  rcases Nat.eq_or_lt_of_le hge with heq | hlt
  · -- the slit above the top
    rw [← heq, show 6 + tpos C₂ 0 + (2 * C₂.m - tpos C₂ 0) = 2 * C₂.m + 6 by omega,
      Nat.mod_eq_of_lt by_omega, b6]
    left
    have hta : 0 < ta := by
      grind
    zubi
    nlinarith
  · obtain ⟨j, hj⟩ : ∃ j, e = 2 * C₂.m - tpos C₂ 0 + 1 + j := ⟨e - (2 * C₂.m - tpos C₂ 0 + 1),
      by omega⟩
    rw [show 6 + tpos C₂ 0 + e = j + ztptn by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt by_omega]
    have hj5 : j ≤ 5 := by_omega
    interval_cases j
    · grind
    · zupbj; right; left; simp only; zuogx
    · rw [b2]; right; right; simp only; zuogx
    · rw [b3]; right; left; simp only; rw [abs_of_pos hRp]
    · grind
    · rw [b5]; left; simp only; nlinarith

/-- **The split vertex of the walk of `C`** in case G: its point is the top of `C₂`, and its
left sector is the corner `tour(2m₂-1) → top → tour(1)` of the walk of `C₂`. -/
theorem split_facts (hδ : 0 < rδ J) :
    sidePt (chainModel J.whole).W
        ztif 0 = J.right.top ∧
      ∀ x, sideLeft (chainModel J.whole).W
          ztif 0 x ↔
        sideLeftOf ztztp J.right.top
          ztsym x := by
  obtain ⟨hL1, -, -, hsl0, hsl0'⟩ := caseG_consts J hδ
  rw [hL1]
  zqbdv
  zulkx
  zqbdw
  have hτ := by_omega
  zuehm

  zqbdx
  zukhw
  have hsl := hsl0
  have hsl' := hsl0'
  zqbea
  set k₀ := (6 + τ + s') % W.n with hk₀
  have hpt : W.vtx k₀ = C₂.top := by
    zugda
    have := walk_box C₂ 0 0 by_omega
    tauto
  have hprev : Chazelle.Chain.sidePrev W k₀ 0 = C₂.sideTour C₂.sideBeta ztpto := by
    unfold Chazelle.Chain.sidePrev
    rw [ite_eq_left rfl, hk₀, mod_pred_mod by_omega _ hs'1, hA1 _ by_omega,
      show 6 + τ' + zttzl = ztpto + 6 by omega,
      Nat.mod_eq_of_lt by_grind]
    zulxa
  have hnext : Chazelle.Chain.sideNext W k₀ = C₂.sideTour C₂.sideBeta 1 := by
    unfold Chazelle.Chain.sideNext
    zuijz
    rw [show (6 + τ' + s' + 7) % W₂.n = 6 by
        rw [hn₂, show 6 + τ' + s' + 7 = 6 + ztptn by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt by_omega],
      Nat.mod_eq_of_lt (show 6 + 1 < W₂.n by zupbv; omega)]
    zulxa
  have hpt' : sidePt W k₀ 0 = C₂.top := by rw [Chazelle.Chain.sidePt_zero, hpt]
  refine ⟨hpt', fun x => ?_⟩
  zuluz
  grind

/-- The walk of `C₂` around the copy of the top before the slit and after it (case G). -/
theorem gap_walk (hδ : 0 < rδ J) :
    ztuk % (chainModel J.right).W.n = 2 * J.right.m + 6 ∧
    ztbpg % (chainModel J.right).W.n = 6 ∧
    (chainModel J.right).W.vtx ztekv = J.right.top ∧
    (chainModel J.right).W.vtx 0 = J.right.slitTop ∧
    (chainModel J.right).W.vtx ztgcc =
      J.right.sideTour J.right.sideBeta ztdkj ∧
    (chainModel J.right).W.vtx 6 = J.right.top ∧
    (chainModel J.right).W.vtx 5 = J.right.slitTop ∧
    (chainModel J.right).W.vtx 7 = J.right.sideTour J.right.sideBeta 1 := by
  zqbed
  zuuy
  zubtn
  zueri
  rw [hL1, hδ7, hn₂]
  refine ⟨by rw [show 6 + tpos J.right 0 + ztbxt = 2 * J.right.m + 6
      by omega]; simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 6 + tpos J.right 0 + ztldk = 6 + ztqf
      by omega, Nat.add_mod_right]; simp
  · rw [cm_W, show 2 * J.right.m + 6 = 2 * J.right.m + 6 from rfl,
      J.right.sideWalk_vtx_tour _ le_rfl, J.right.sideTour_two_m]
  · rfl
  · rw [cm_W, show 2 * J.right.m + 5 = ztdkj + 6 by omega,
      J.right.sideWalk_vtx_tour _ by_omega]
  · rw [cm_W, show (6 : ℕ) = 0 + 6 from rfl, J.right.sideWalk_vtx_tour _ by_omega,
      J.right.sideTour_zero]
  · rfl
  · rw [cm_W, show (7 : ℕ) = 1 + 6 from rfl, J.right.sideWalk_vtx_tour _ by_omega]

/-- The slit of a chain leaves its top vertically. -/
theorem slitTop_sub_top (C : Chain) : C.slitTop - C.top = (ztpsj : Point) := by
  apply Geometry.point_ext <;> simp [Chain.slitTop]
theorem rayPt_sub_self (u : Point) (σ : ℝ) : rayPt u σ 1 - u = (ztwn : Point) := by
  apply Geometry.point_ext <;> zvmxf
theorem sideTour_sub_top_snd (C : Chain) (β : Bool) (i : ℕ) : (C.sideTour β i - C.top).2 ≤ 0 := by
  have := C.vertex_snd_le_top ztdfj
  simp only [Prod.snd_sub, Chain.sideTour]
  linarith

/-- **At each copy of the top of `C₂` next to the slit at most one chord of `S₂` is attached**
(the sector between the vertical slit and the tour contains only one horizontal direction). -/
theorem oneAt_right (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hδ : 0 < rδ J) :
    ∀ k : ℕ, ztecn → ∀ c ∈ S₂, ∀ c' ∈ S₂,
      SideAttach (chainModel J.right).W c ztqp 0 →
      SideAttach (chainModel J.right).W c' ztqp 0 →
        c = c' := by
  intro k hk c hc c' hc' hA hA'
  zuct
  zubnr
  have hS := hS₂
  zqbdz
  zueri
  zumcj
  obtain ⟨ce, cw, hce, hcw, hAe, hAw, hE, hW⟩ : ∃ ce cw, ce ∈ S₂ ∧ cw ∈ S₂ ∧
      SideAttach (chainModel J.right).W ce ztqp 0 ∧
      SideAttach (chainModel J.right).W cw ztqp 0 ∧
      (∀ z ∈ ce, (sidePt (chainModel J.right).W
        ztqp 0).1 ≤ z.1) ∧
      (∀ z ∈ cw, z.1 ≤ (sidePt (chainModel J.right).W
        ztqp 0).1) := by
    rcases hM₂.tie_pair hS hc hc' hne hA hA' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨c, c', hc, hc', hA, hA', h1, h2⟩
    · exact ⟨c', c, hc', hc, hA', hA, h2, h1⟩
  obtain ⟨-, s₁, s₂, hs₁, hs₂, hsE, hsW⟩ := hM₂.tie_setup (hS hce) (hS hcw) hAe hAw hE hW
  zuvk
  · rw [g1] at hsE
    have e1 : (chainModel J.right).wb ztekv = (chainModel J.right).W.vtx 0 := by
      rw [WalkAx.wb_eq, hn₂, show 2 * J.right.m + 6 + 1 = 2 * J.right.m + 7 by ring, Nat.mod_self]
    have e2 : (ztekv + (chainModel J.right).W.n - 1) % (chainModel J.right).W.n =
        2 * J.right.m + 5 := by
      rw [hn₂, show 2 * J.right.m + 6 + ztqf - 1 = ztgcc +
        ztqf by omega, Nat.add_mod_right]
      simp
    zudfo
    have := ccw_up_left by_linarith ztiba hsE
    linarith
  · rw [g2] at hsW
    have e1 : (chainModel J.right).wb 6 = (chainModel J.right).W.vtx 7 := by
      rw [WalkAx.wb_eq, hn₂, Nat.mod_eq_of_lt by_omega]
    have e2 : ztfzt := by
      rw [hn₂, show 6 + ztqf - 1 = 5 + ztqf by omega,
        Nat.add_mod_right]
      simp
    zudfp
    have := ccw_up_right by_linarith ztiba hsW
    linarith

/-- **A horizontal segment from a point**, as a set of ray points. -/
theorem seg_ray {u w : Point} (hwu : w ≠ u) (hwy : w.2 = u.2) :
    ∃ σ T : ℝ, ztdd ∧ 0 < T ∧
      (∀ s, 0 ≤ s → s ≤ T → rayPt u σ s ∈ Chazelle.segment u w) ∧
      ∀ z ∈ Chazelle.segment u w, ∃ s, 0 ≤ s ∧ s ≤ T ∧ z = rayPt u σ s := by
  have hne : w.1 ≠ u.1 := by_grind
  zuevn
  · refine ⟨-1, u.1 - w.1, Or.inr rfl, by_linarith, fun s hs0 hs1 => ?_, fun z hz => ?_⟩
    · refine ⟨s / ztojb, div_nonneg hs0 by_linarith, (div_le_one by_linarith).2 hs1, ?_⟩
      zufqm
      · zufbw
      simp_all
    · zufkw
      refine ⟨t * ztojb, by_simp_all, by_nlinarith, ?_⟩
      zufqm
      · zujou
      simp_all
  · refine ⟨1, w.1 - u.1, Or.inl rfl, by_linarith, fun s hs0 hs1 => ?_, fun z hz => ?_⟩
    · refine ⟨s / ztor, div_nonneg hs0 by_linarith, (div_le_one by_linarith).2 hs1, ?_⟩
      zufqm
      · zvnap; field_simp
      simp_all
    · zufkw
      refine ⟨t * ztor, by_simp_all, by_nlinarith, ?_⟩
      zufqm
      · simp
      simp_all

/-- **A chord of `F₂⁺` through the top of `C₂`, inside a chord of `S₂` attached at a copy of the
top next to the slit, is attached at the split vertex of the walk of `C`.** -/
theorem splitAttach_right (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hδ : 0 < rδ J) :
    ∀ k : ℕ, ztecn → ∀ c ∈ S₂,
      SideAttach (chainModel J.right).W c ztqp 0 →
      ∀ e ∈ F₂plus J S₂, e ⊆ c → sidePt (chainModel J.whole).W
        ztif 0 ∈ e →
        SideAttach (chainModel J.whole).W e
          ztif 0 := by
  intro k hk c hc hAc e he hec hue
  zugpq
  zqbdz
  zumh
  zueri
  zumcj
  zucvz
  have heA := F₂plus_subset J hS₂ he
  zukzy
  zvmxe at hue
  have huD : ztpqg := by
    zvnbr; exact hM.trace _ ztcv 0 le_rfl zero_le_one
  -- `e` is a horizontal segment from `u`
  obtain ⟨w, hwu, hwy, hew⟩ : ∃ w, w ≠ u ∧ w.2 = u.2 ∧ e = Chazelle.segment u w := by
    obtain ⟨a, b, hab, heq, hy, hopen, -, -⟩ := hM.ends e heA
    have hue' := hue
    zudac

    zunm
    · zuji
      · exact absurd (hs ▸ hopen s ztdxi) huD
      · zuikp
        exact ⟨a, by_grind, by_grind, by
          zuobk⟩
    · zuhny
      exact ⟨b, by_grind, by_simp_all, by_simp_all⟩
  zudey
  rw [hew] at hec
  -- the direction lies in the sector of `M₂` at the copy of the top
  set P := ztnhq % (chainModel J.right).W.n with hP_def
  have hvP : (chainModel J.right).W.vtx P = u := by
    zuvk
    · grind
    grind
  obtain ⟨-, -, -, -, r, hr, hl⟩ := hAc
  have hsl₂ : sideLeft (chainModel J.right).W P 0 zthzn := by
    zuiop
    have hε0 : ztbad := lt_min by_linarith hT
    have hz := hl _ (hec (hray ε hε0.le ztgh))
      (by zuopj; intro h
          have := congrArg Prod.fst h; zvnap at this
          rcases hσ with rfl | rfl <;> linarith)
      (by rw [Chazelle.Chain.sidePt_zero, hvP, dist_rayPt _ hσ hε0.le]
          exact lt_of_le_of_lt ztff by_linarith)
    have hq : u = sidePt (chainModel J.right).W P 0 := by zuopj
    zvnck at hz ⊢
    zuisi
  -- the direction lies in the sector of `M` at the split vertex
  obtain ⟨σ₀, -, hl₀⟩ := FuseMath.top_sector J.right hP
  have hB := sideTour_sub_top_snd J.right J.right.sideBeta 1
  have hA := sideTour_sub_top_snd J.right J.right.sideBeta ztdkj
  unfold sideLeftOf at hl₀
  rw [rayPt_sub_self] at hl₀
  have hsl : sideLeft (chainModel J.whole).W
      ztif 0 zthzn := by
    rw [hsec]
    zucfg
    rw [rayPt_sub_self]
    rw [Chazelle.Chain.sideLeft_zero] at hsl₂
    unfold sideLeftOf at hsl₂
    rw [hvP, rayPt_sub_self] at hsl₂
    zuvk
    · have e1 : ztnnt % (chainModel J.right).W.n = 0 := by
        rw [hP_def, g1, hn₂, show 2 * J.right.m + 6 + 1 = 2 * J.right.m + 7 by ring, Nat.mod_self]
      have e2 : ztlfl % (chainModel J.right).W.n =
          2 * J.right.m + 5 := by
        rw [hP_def, g1, hn₂, show 2 * J.right.m + 6 + ztqf - 1 =
          ztgcc + ztqf by omega, Nat.add_mod_right]
        simp
      rw [e1, e2, v0, v25, slitTop_sub_top] at hsl₂
      exact ccw_lower_left by_linarith hA hB hl₀ hsl₂
    · have e1 : ztnnt % (chainModel J.right).W.n = 7 := by
        rw [hP_def, g2, hn₂]; exact Nat.mod_eq_of_lt by_omega
      have e2 : ztlfl % (chainModel J.right).W.n = 5 := by
        rw [hP_def, g2, hn₂, show 6 + ztqf - 1 = 5 + ztqf by omega,
          Nat.add_mod_right]
        simp
      rw [e1, e2, v7, v5, slitTop_sub_top] at hsl₂
      exact ccw_lower_right by_linarith hA hB hl₀ hsl₂
  -- the attachment
  refine ⟨Nat.mod_lt _ by_omega, le_rfl, zero_lt_one,
    by grind, 1, one_pos, fun z hz hzu _ => ?_⟩
  rw [hew] at hz
  obtain ⟨s, hs0, -, rfl⟩ := hseg z hz
  have hs : ztxx := by
    zuvl
    · zubh
    · exfalso; apply hzu; rw [← h, hpt]; simp
  zvnbr at hsl ⊢
  zuish

/-- **The gap facts for the right side of a junction** (case G). -/
theorem corrGap_right (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) (hδ : 0 < rδ J) :
    CorrGap ztbm ztj ztbi S₂
      ztve ztbrv ztns ztqvh ztpg := by
  refine ⟨fun c hc pa ta hA h1 h2 x hx y hy hxS hyS => ?_, oneAt_right J hP hS₂ hδ,
    splitAttach_right J hP hS₂ hδ⟩
  zubnr
  have hw := gap_not_mem J hδ hA.1 hA.2.1 hA.2.2.1 h1 h2
  have hxs := strPt_mem_right J hP hS₂ hS₂f hδ hxS
  have hys := strPt_mem_right J hP hS₂ hS₂f hδ hyS
  obtain ⟨a, b, -, -, hend⟩ := end_of_not_mem hM₂ ztbac
  have notD : ∀ z ∈ J.right.set, z ∉ (chainModel J.right).D :=
    fun z hz hD => J.right.not_mem_set_of_mem_dom hD hz
  have hwD := hM₂.trace _ hA.1 _ hA.2.1 hA.2.2.1.le
  rcases hend _ hx by_simp_all with h1 | h1 <;> rcases hend _ hy by_simp_all with h2 | h2 <;>
    rcases hend _ hA.2.2.2.1 hwD with h3 | h3 <;>
    first
    | exact h1.trans h2.symm
    | exact by_simp_all
    | exact by_simp_all

/-- **The regions of `S₂` at the two sides of the slit of `C₂`** (case G): faced just after the
copy of the top before the slit, or just before the copy after it. -/
def GapLab (S₂ : Set ztf) (V : Set Point) : Prop :=
  0 < rδ J ∧ V ∈ (chainModel J.right).regions S₂ ∧
    (AfterFaces ztj ztwua 0 V ∨
      BeforeFaces ztj
        ztwty 0 V)

/-- **The label triple**: `V` is the label `λ` or a region at a side of the slit of `C₂`. -/
def LabS (S₂ : Set ztf) (L V : Set Point) : Prop := V = L ∨ GapLab J S₂ V

/-- Combining a valid label with lemma (E). -/
theorem labS_trans {S₂ : Set ztf} {L V₀ V' : Set Point} (h1 : LabS J S₂ L V₀)
    (h2 : V₀ = V' ∨ ztles) : LabS J S₂ L V' := by
  rcases h2 with rfl | ⟨-, h⟩
  · zubvv
  tauto

/-- **Lemma (K3) for a junction**: two labels of a region of `F₂⁺` are equal, or both are regions
at the sides of the slit of `C₂`. -/
theorem label_right3 (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi) {V V' : Set Point}
    (hV : V ∈ (chainModel J.right).regions S₂) (hV' : V' ∈ (chainModel J.right).regions S₂)
    (h : RLabel J S₂ G V) (h' : RLabel J S₂ G V') :
    V = V' ∨ ztfnn := by
  obtain ⟨d, hd, t, ht, hc, hf, hfV⟩ := h
  obtain ⟨d', hd', t', ht', hc', hf', hfV'⟩ := h'
  rcases (corr_right0 J hP hS₂ hS₂f).label_gen3 (corrGap_right J hP hS₂ hS₂f) hd hd' ht ht' hc hc'
    hG hf hf' hV hV' hfV hfV' with h | ⟨hδ, h1, h2⟩ | ⟨hδ, h1, h2⟩
  · simp_all
  · exact Or.inr ⟨⟨hδ, hV, Or.inl h1⟩, ⟨hδ, hV', Or.inr h2⟩⟩
  · exact Or.inr ⟨⟨hδ, hV, Or.inr h1⟩, ⟨hδ, hV', Or.inl h2⟩⟩
end GapRight
end Sweep
end
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqyv" : tactic => `(tactic| (obtain ⟨r₃, hr₃, hcl⟩ := hA'.2.2.2.2
                                          set s₂ := min ztcmw ztohc with hs₂
                                          zudph

                                          have hs₂r : ztsmm := lt_of_le_of_lt ztgh by_linarith))
local macro "zqyw" : tactic => `(tactic| by_cases hc2 : (chainModel J.right).IsCut S₂ ztieu)
local macro "zqyx" : tactic => `(tactic| (filter_upwards [hoff] with s hs
                                          filter_upwards [hs] with δ hδ))
local macro "zqyy" : tactic => `(tactic| (refine hchord x hx.1 hxs ?_
                                          intro hxF
                                          zuxo

                                          rw [hxs'] at h5))
local macro "zqyz" : tactic => `(tactic| (intro x hx hxl
                                          obtain ⟨hxD, hxc⟩ := hsf x hx hxl
                                          refine ztfwr
                                          rintro ⟨c, hcF, hxc'⟩))
local macro "zqza" : tactic => `(tactic| (obtain ⟨s₁, ⟨hs₁U, hs₁B⟩, hs₁pos⟩ := ((happ.and hball).and self_mem_nhdsWithin).exists
                                          have hs₁pos' := hs₁pos))
local macro "zqzb" : tactic => `(tactic| (filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr] with s hs hs'
                                          rw [mem_ball, dist_rayPt _ hτ ztmme]
                                          simp_all))
local macro "zqzc" : tactic => `(tactic| (intro c hc
                                          filter_upwards [happ] with s hs hsc
                                          exact (hUfree hs).2 ztkji))
local macro "zqzd" : tactic => `(tactic| (unfold sideDot; zumzm
                                          zunqe))
local macro "zqze" : tactic => `(tactic| (zunfp; omega))
local macro "zqzf" : tactic => `(tactic| have hHU := subset_region hU hHc hHfree hs₁H hs₁U')
set_option hygiene true

/-!
# The sweep (WP-D), part 6: queries (lemma (Q))

A query point `z` of the sweep (on the walk of `C₁`) whose ray, in the model of `C = J.whole`,
starts in the region `G` of `F₂⁺` and first hits `C` at a point `w` of `C₂` (not of `C₁`): then
the ray starts in a region `V` of `S₂` (in the model of `C₂`) and `V` is the label of `G`
(`RLabel`).  With lemma (K) (`label_right`) the label of `G` is unique, so the sweep, which knows
the label of the current region, answers the query by local shooting in `V` (and in the region of
`S₁` of the query, `SweepAnswer`).

## Generic part

* `approach_edge`, `approach_vertex`: a ray approaching a walk position from inside its left
  sector, inside a region `U`: the position is not a cut and faces `U` (inside a walk edge), or
  the positions just after / just before face `U` (at a walk vertex; when a chord is attached
  there, on the side given by the direction of the ray).  These are the facing statements behind
  `hit_mem_arcSet`, stated so that they can be used in two models with the same walk locally.
* `Corr.sideNext_eq`, `Corr.sidePrev_eq`, `Corr.sideLeft_eq`: the correspondence preserves
  sectors.

## The junction

* `pos_tour_of_mem_set`, `right_cover₂`, `right_vtx0`, `right_split_top`, `dom_right`,
  `dom_left`: bookkeeping.
* `query_right`: **lemma (Q)**.
* `answer_of_label`: **answering a query below both tops from its region of `S₁` and the label
  of its region of `F₂⁺`** (first hit on the arcs of the two regions = first hit of `C`).
-/
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft sideLeftOf sideCcw
  sideCross sideDot freeIn regionsIn sideLeft_edge sideLeft_zero sideLeft_not_self sideKey_inj
  sideCcw_smul)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)
open Chazelle.Jordan (offset SectorSide)
open WalkEmbed
namespace Sweep
section Approach
variable {M : Model}

/-- **A ray approaching a position inside a walk edge**: the position is not a cut and faces the
region of the ray. -/
theorem approach_edge (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : ∀ s > 0, sideLeft M.W p t ztxon)
    (happ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztbp τ s ∈ U) :
    ¬ M.IsCut F ztk ∧ M.Faces p t U := by
  obtain ⟨r, hr, hsf⟩ := sector_free hM hF hfin hp ht.1.le ht.2
  zubdr
  zund
  have hball : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztbp τ s ∈ ball ztbp r := by
    zqzb
  zqza
  have havoid : ∀ c ∈ F, ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztbp τ s ∉ c := by
    zqzc
  have hcut : ¬ M.IsCut F ztk := by
    rintro ⟨c, hcF, p', t', hA', hk⟩
    obtain ⟨hpp, htt⟩ := sideKey_inj ht.1.le ht.2 hA'.2.1 hA'.2.2.1 hk
    zudbb
    obtain ⟨d, hd, -, -, hcmem⟩ := attached_opposite hM ztgjz hA' hτ zttnd
    zqyv
    have hx₂ : ztwyk := by
      zudsr
      · zuq
        have := congrArg Prod.fst h
        zudv
        zubll
      · zqze
    have h1 := (sideLeft_edge hne ht _).1 ztfsl
    have h2 := (sideLeft_edge hne ht _).1 hx₂
    have hw0 : ztycn :=
      Geometry.det_lerp_self _ _ _
    zuqc

  refine ⟨hcut, ?_⟩
  have hfreeS : ztwnw := by
    zqyz
    exact hcut ztexz
  have hHc : IsPreconnected (ball ztbp r ∩
      {x : Point | 0 < 1 * det ztoy ztbakv x}) :=
    ((convex_ball _ r).inter zthqu).isPreconnected
  have hHfree : ball _ r ∩
      {x : Point | 0 < 1 * det _ _ x} ⊆
      freeIn M.D F := fun x hx =>
    hfreeS x hx.1 ((sideLeft_edge hne ht x).2 zthty)
  have hs₁H : rayPt _ τ s₁ ∈ ball _ r ∩
      {x : Point | 0 < 1 * det _ _ x} :=
    ⟨hs₁B, by simpa using (sideLeft_edge hne ht _).1 by_simp_all⟩
  zudhg
  filter_upwards [hM.eventually_offset_left hp ht hr] with δ hδ
  exact hHU ⟨hδ.1, by simpa using (sideLeft_edge hne ht _).1 hδ.2⟩

/-- **A ray approaching a walk vertex**: if no chord is attached there, the positions just after
and just before face the region of the ray; if a chord is attached there, the ray turns
counterclockwise from the next walk edge or clockwise from the previous one, and the positions
on that side face the region of the ray. -/
theorem approach_vertex (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n) (hp1 : 1 ≤ p) {τ : ℝ}
    (hτ : τ = 1 ∨ τ = -1)
    (hsec : ∀ s > 0, sideLeft M.W p 0 (rayPt ztfs τ s))
    (happ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∈ U) :
    (¬ M.IsCut F ztmm → (∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U) ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces ztoq zteb U) ∧
    (M.IsCut F ztmm →
      (0 < sideCross ztbajf (ztkn : Point) ∨
        0 < sideCross (ztkn : Point) ztwll) ∧
      (0 < sideCross ztbajf (ztkn : Point) →
        ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U) ∧
      (0 < sideCross (ztkn : Point) ztwll →
        ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces ztoq zteb U)) := by
  zuqu
  zubdr
  zund
  have hball : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∈ ball ztfs r := by
    zqzb
  zqza
  have havoid : ∀ c ∈ F, ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∉ c := by
    zqzc
  zudou
  zuee

  zufah

  have hav : ztiyw := by
    have := hM.nd _ ztwwc
    zudbf
  zuyp

  have hsecv : ztwyo :=
    fun x => sideLeft_zero _ _ _
  have hs₁B' : ztiea := by_grind
  have hs₁U' : ztlbd := by_grind
  refine ⟨fun hcut => ?_, fun hcut => ?_⟩
  · -- no chord is attached at the vertex: the whole sector is free
    have hfreeS : ∀ x ∈ ball ztfs r, sideLeft M.W p 0 x → x ∈ freeIn M.D F := by
      zqyz
      exact hcut ⟨c, hcF, p, 0, by_grind, rfl⟩
    zuzf
    have hHfree : ztddz := fun x hx =>
      hfreeS x ztdyx ztdxy
    have hs₁H : ztdar := by
      zujfx
      have := hsec s₁ hs₁pos'
      zubmc

    zqzf
    zujx
    · zqyx
      have := hHU hδ.2
      zubvd
    · zqyx
      have := hHU hδ.1
      zucqb
      show Jordan.offset ztffo ztffo _ δ ∈ U
      zubsi

  -- a chord is attached at the vertex
  obtain ⟨c, hcF, p', t', hA', hk⟩ := hcut
  obtain ⟨hpp, htt⟩ := sideKey_inj le_rfl one_pos hA'.2.1 hA'.2.2.1 hk
  zudbb
  obtain ⟨d, hd, -, hcD, hcmem⟩ := attached_opposite hM ztgjz hA' hτ zttnd
  zqyv
  have hx₂ : ztxtj := by
    zudsr
    · zuq
      have := congrArg Prod.fst h
      zudv
      zubll
    · zqze
  zuwk
  have hdm0 : ztxfe := by
    zuqm
    grind
  have hvdm : ztwyl := by
    grind
  have hdp : ztxby := by
    have := (hsecv _).1 ztfsl
    zurl
  have hdm : ztxbx := by
    have := (hsecv _).1 hx₂
    zubin
  -- the edge after the vertex does not go along the chord
  have hBdm : ¬ (sideCross ztfd (ztdx : Point) = 0 ∧
      0 < sideDot ztfd (ztdx : Point)) := by
    zubf
    zuxa
    have hb2 : ztplo := by
      grind
    zuhn

    zufvo
    zudpf
    zuck

    have e : ztccd := by
      zucky
      zubjw
      · zudcf
        have h3 : ztwwu := by
          zubyn
          zujcd
        linarith
      · zuqb

    zubuu
  -- the ray is on one side of the chord
  have hdich : ztwre := by
    zudl
    · grind
    · zucvi
    · grind
    · zucyt
      · zuist
      · zugkk
        zujh
        · grind
        · zubyz

      grind
  -- chord points through the sector are on the chord's ray
  have hchord : ∀ x ∈ ball v r, sideLeft M.W p 0 x → x ∉ ⋃₀ F →
      x ∈ freeIn M.D F := by
    zuetk

  have hray : ∀ x ∈ ball v r, sideLeft M.W p 0 x → x ∈ ⋃₀ F →
      ∃ s' : ℝ, 0 ≤ s' ∧ x - v = s' • (ztdx : Point) := by
    zucbz

    zueh

  refine ⟨hdich, fun h => ?_, fun h => ?_⟩
  · -- the ray is between the edge after the vertex and the chord
    obtain ⟨-, hHc, hoff⟩ := Chazelle.Chain.sideSector hvdm hbv (S := ∅) hr
      ztbqd
    have hHsec : ∀ x ∈ ball v r ∩ {x | sideLeftOf ztwji v b x},
        sideCcw ztfd ztsq (ztdx : Point) := by
      zuh
      zuhdj
      zuof
    have hHfree : ball v r ∩ {x | sideLeftOf ztwji v b x} ⊆
        freeIn M.D F := by
      zuh
      have hxs :=
        (hsecv x).2 ztgdj
      zqyy
      zugan
      · zubag
      · zqzd
    have hs₁H : ztbajs := by
      zujfx
      show sideLeftOf _ v b _
      zuns
      zuisw
    zqzf
    zqyx
    have := hHU hδ.2
    zubvd
  · -- the ray is between the chord and the edge before the vertex
    obtain ⟨-, hHc, hoff⟩ := Chazelle.Chain.sideSector hav hvdm (S := ∅) hr
      ztbqd
    have hHsec : ∀ x ∈ ball v r ∩ {x | sideLeftOf a v ztwji x},
        sideCcw (ztdx : Point) ztsq ztgg := by
      zuh
      zueph
      zuof
    have hHfree : ball v r ∩ {x | sideLeftOf a v ztwji x} ⊆
        freeIn M.D F := by
      zuh
      have hxs :=
        (hsecv x).2 ztfba
      zqyy
      zugam
      · zubag
      · zqzd
    have hs₁H : ztbajr := by
      zujfx
      show sideLeftOf a v _ _
      zuns
      zuisx
    zqzf
    zqyx
    have := hHU hδ.1
    zucqb
    show Jordan.offset ztffo ztffo _ δ ∈ U
    zubsi
end Approach

/-! ## Non-cut keys near a key -/

/-! ## Two walks along a correspondence: sectors -/
namespace Corr
variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}
end Corr
namespace Corr0
variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}

/-- Agreeing next points. -/
theorem sideNext_eq (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) :
    sideNext M.W ztwje = sideNext M₂.W ztuj := by
  zujql
  zus
  · exact hC.A1.sideNext_eq h
  · have := hC.A2.sideNext_eq (d := d - L1) by_omega
    rwa [show g + L1 + ztduf = g + d by omega,
      show g' + L1 + δ + ztduf = g' + ztjtf by omega] at this

/-- Agreeing previous points (away from the base and the split vertex). -/
theorem sidePrev_eq (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) {t : ℝ}
    (hsec : t = 0 → d ≠ 0 ∧ d ≠ L1) :
    sidePrev M.W ztwje t = sidePrev M₂.W ztuj t := by
  zujql
  zus
  · exact hC.A1.sidePrev_eq hC.n_pos hC.n₂_pos h ztlod
  · have := hC.A2.sidePrev_eq hC.n_pos hC.n₂_pos (d := d - L1) by_omega (t := t)
      ztlod
    rwa [show g + L1 + ztduf = g + d by omega,
      show g' + L1 + δ + ztduf = g' + ztjtf by omega] at this

/-- Agreeing left sectors (away from the base and the split vertex). -/
theorem sideLeft_eq (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) {t : ℝ}
    (hsec : t = 0 → d ≠ 0 ∧ d ≠ L1) :
    sideLeft M.W ztwje t = sideLeft M₂.W ztuj t := by
  funext x
  zuluz
  rw [hC.sidePrev_eq hd hsec, hC.sidePt_eq hd, hC.sideNext_eq hd]
end Corr0

/-! ## Chain facts for the queries -/

/-- A position of the walk of a chain model whose point is a point of the chain other than its
top is a position of the tour, before its last vertex. -/
theorem pos_tour_of_mem_set (C : Chain) (β : Bool) {p : ℕ} (hp : p < (C.sideWalk β).n) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (h : sidePt ztft p t ∈ C.set)
    (hne : sidePt ztft p t ≠ C.top) : ∃ i, i < 2 * C.m ∧ p = i + 6 := by
  have hb := C.abs_le_coordBound_of_mem_set h
  zugma
  have htop := C.snd_le_top_of_mem_set h
  zuop

  · exfalso
    interval_cases p
    · grind
    · grind
    · grind
    · grind
    · grind
    · rw [h5] at htop; simp only at htop; nlinarith
  · exfalso
    rw [h6] at htop; simp only at htop; nlinarith
  grind

/-- A horizontal subchord through an endpoint of a horizontal chord contains the start of the
ray from that endpoint along the chord. -/
theorem ray_sub_hseg {y a b y' a' b' : ℝ} (hab' : a' < b')
    (hsub : Visibility.hseg y' a' b' ⊆ Visibility.hseg y a b) {w : Point}
    (hw : w ∈ Visibility.hseg y' a' b') (hwend : w = ztdv ∨ w = ztdy) {τ : ℝ}
    (hτ : τ = 1 ∨ τ = -1) :
    ∃ ε > 0, ∀ s, 0 < s → s < ε → rayPt w τ s ∈ Visibility.hseg y a b →
      rayPt w τ s ∈ Visibility.hseg y' a' b' := by
  zucxu
  obtain ⟨hy1, ha1, hb1⟩ : ((a', y') : Point) ∈ Visibility.hseg y a b :=
    hsub ⟨rfl, le_rfl, hab'.le⟩
  obtain ⟨hy2, ha2, hb2⟩ : ((b', y') : Point) ∈ Visibility.hseg y a b :=
    hsub ⟨rfl, hab'.le, le_rfl⟩
  simp only at hy1 ha1 hb1 hy2 ha2 hb2
  rcases hτ with rfl | rfl <;> rcases hwend with rfl | rfl <;> simp only at hwy hwa hwb
  · refine ⟨b' - a, by_linarith, fun s hs0 hs1 _ => ztcg⟩ <;>
      zuhpx
  · refine ztkim
    exfalso
    obtain ⟨-, -, h⟩ := hc
    zuips

  · refine ztkim
    exfalso
    obtain ⟨-, h, -⟩ := hc
    zuips

  · refine ⟨b - a', by_linarith, fun s hs0 hs1 _ => ztcg⟩ <;>
      zuhpx
section Junction
variable (J : Merge.Junction)

/-- Points of the domain of `C` not above the top of `C₂` are in the domain of `C₂`. -/
theorem dom_right {x : Point} (hx : x ∈ J.whole.dom) (hx2 : x.2 ≤ J.right.top.2) :
    x ∈ J.right.dom := by
  zumv
  rcases (Merge.not_mem_dom_iff J.right hx2).1 h with h1 | h1
  · zufqn

  · exact J.whole.not_mem_set_of_mem_dom hx (J.right_set_subset h1)

/-- The base of the walk of `C₂` is the shared vertex. -/
theorem right_vtx0 : (chainModel J.right).W.vtx ztbrv = J.shared := by
  zuuy
  zubau
  have := walk_tour J.right 0 0 by_omega
  rw [add_zero, Nat.mod_eq_of_lt by_omega, tourV_right_zero] at this
  omega

/-- In case G, the vertex after the gap is the top of `C₂`. -/
theorem right_split_top (h : 0 < rδ J) :
    (chainModel J.right).W.vtx (ztbpg %
      (chainModel J.right).W.n) = J.right.top := by
  zubau
  have e : rL1 J + rδ J = 2 * J.right.m - tpos J.right 0 + 7 := by
    unfold rL1 rδ at *
    grind
  rw [e, show 6 + tpos J.right 0 + ztldk =
    6 + tpos J.right 0 + ztbxt + 7 by omega]
  exact walk_box J.right 0 7 le_rfl

/-- **Every tour position of `C₂` (before its last vertex) is covered by the correspondence.** -/
theorem right_cover₂ {i : ℕ} (hi : i < 2 * J.right.m) :
    ∃ d < rL1 J + rL2 J, dq ztns ztpg d =
      dOf (chainModel J.right).W.n ztbrv ztjgb := by
  zubtn
  zuuy
  zunc
  rw [hn₂, FuseMath.dOf_six by_omega by_omega]
  refine ⟨if (if tpos J.right 0 ≤ i then i - tpos J.right 0
      else i + ztqf - tpos J.right 0) < rL1 J
    then (if tpos J.right 0 ≤ i then i - tpos J.right 0
      else i + ztqf - tpos J.right 0)
    else (if tpos J.right 0 ≤ i then i - tpos J.right 0
      else i + ztqf - tpos J.right 0) - rδ J, ?_, ?_⟩ <;>
  · simp only [rL1, rL2, rδ, dq]
    grind
end Junction

/-! ## Lemma (Q) -/
section Query
variable (J : Merge.Junction)

/-- **Lemma (Q): a query sees `C₂` from the label of its region.**  Let the initial part of the
horizontal ray from `z` (not above the top of `C₂`) lie in the region `G` of `F₂⁺` (model of `C`),
and let the first hit of the ray in `C` be a point of `C₂` not on `C₁`.  Then the initial part of
the ray lies in a region `V` of `S₂` (model of `C₂`), and `V` is a label of `G`. -/
theorem query_right (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi) {z : Point}
    (hz : z.2 ≤ J.right.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hini : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ G)
    (hw2 : rayPt z σ ztbyn ∈ J.right.set)
    (hw1 : rayPt z σ ztbyn ∉ J.left.set) :
    ∃ V ∈ (chainModel J.right).regions S₂, (∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ V) ∧
      RLabel J S₂ G V := by
  have hCorr := corr_right0 J hP hS₂ hS₂f
  have hM := hCorr.hM
  have hM₂ := hCorr.hM₂
  zudnk
  zujzh
  have hGd : G ∈ regionsIn J.whole.dom _ := hG
  have hGfree : G ⊆ freeIn J.whole.dom _ := Chazelle.Chain.regionsIn_subset hGd
  have hfree := hini.mono fun t ht => (hGfree ht).1
  have hz' := hz.trans J.right_top_le
  zuchz

  set w := rayPt z σ T with hwdef
  have hray := ray_subset_region J.whole hFs hGd hσ hT hdom hini
  zukv
  have hback : ztxpz := by
    intro s; apply point_ext <;> simp [rayPt, hwdef]; ring
  have hwy : w.2 = z.2 := by_rfl
  have hbackG : ∀ s, 0 < s → s < T → rayPt w (-σ) s ∈ G := by_simp_all
  have happG : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∈ G := by
    zunv
    simp_all
  have hbackD : ∀ s, 0 < s → s < T → rayPt w (-σ) s ∈ J.right.dom := fun s h0 h1 => by
    refine dom_right J ?_ ?_
    · simp_all
    simp_all
  -- the hit point is neither the shared vertex nor the top of `C₂`
  have hwv : w ≠ J.shared := fun h => hw1 ztnzz
  have hwt : w ≠ J.right.top := by
    intro hwt
    have hkt : ztsbt := by
      have := J.right.topIdx_le
      simp only [Merge.Junction.whole_m, Merge.Junction.right_m] at this ⊢
      omega
    have hvert : J.whole.vertex _ = J.right.top :=
      Merge.Junction.whole_vertex_add J _
    have hdf : J.whole.DirFree ztrw (-σ) := by
      unfold Chain.DirFree
      zunv
      grind
    have he : J.whole.chordSet _ _ ∈ F₂plus J S₂ :=
      Or.inr ⟨-σ, hnσ, hdf, rfl⟩
    obtain ⟨hpar, -, -⟩ := Merge.hit_of_freeAt J.whole (J.whole.vertex_snd_le_top hkt) hnσ hdf
    have hpar' : 0 < J.whole.chordParam _ _ := hpar
    set s := min ztld (J.whole.chordParam ztrw (-σ) / 2) with hs
    zudzp
    have hsT : ztppt := lt_of_le_of_lt ztff by_linarith
    have hsP : s < J.whole.chordParam ztrw (-σ) :=
      lt_of_le_of_lt ztgh by_linarith
    have hmem : rayPt w (-σ) s ∈ J.whole.chordSet ztrw (-σ) := by
      rw [J.whole.chordSet_eq_openChordSet_union hkt hnσ hdf]
      left
      refine ⟨s, by_grind, ?_⟩
      grind
    exact (hGfree by_grind).2 ⟨_, he, hmem⟩
  -- a position of the walk of `C₂` at the hit point, whose sector contains the backward ray
  have hT2' : ztehc := by_linarith
  have hee : ztwym := by
    grind
  have hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp w ztwmv s ∈ J.right.dom := by
    zugg
    have e : lerp w ztwmv s = rayPt w (-σ) (s * ztld) := by
      apply point_ext <;> simp [lerp, rayPt]; ring
    zui
    exact hbackD _ ztqer ztepr
  have hP₂ := hP
  obtain ⟨p₂, t₂, hp₂, ht₂, ht₂1, hpt₂, hl₂⟩ :=
    J.right.sideSees_chordEnd hP₂ J.right.sideBeta hee by_simp hopen (Or.inl hw2)
  obtain ⟨i, hi, rfl⟩ := pos_tour_of_mem_set J.right J.right.sideBeta hp₂ ht₂ ht₂1
    by_grind by_grind
  -- the corresponding position of the walk of `C`
  obtain ⟨d, hd, hdq⟩ := right_cover₂ J hi
  zuuy
  zumh
  have hg' := hCorr.hg'
  have hpos₂ : ztfw % (chainModel J.right).W.n = i + 6 := by
    rw [hdq, show i + 6 = 6 + i by ring]
    exact add_dOf hg' by_omega
  have hpt₂' : sidePt (chainModel J.right).W _ t₂ = w := hpt₂
  zubdc
  have hPn : P < (chainModel J.whole).W.n := Nat.mod_lt _ hCorr.n_pos
  have hptW : sidePt (chainModel J.whole).W P t₂ = w := by
    rw [hPdef, hCorr.sidePt_eq hd t₂, hpos₂]; omega
  have hL1pos : 0 < rL1 J := by
    have := tpos_lt J.right 0
    zunc
    have := J.one_le_m₂
    unfold rL1; split_ifs <;> omega
  have hsecd : t₂ = 0 → d ≠ 0 ∧ d ≠ rL1 J := by
    zubww
    refine ⟨fun hd0 => hwv ?_, fun hdL => hwt ?_⟩
    · rw [← hpt₂', h0, Chazelle.Chain.sidePt_zero, ← hpos₂, hd0,
        show dq _ _ 0 = 0 by unfold dq; split_ifs; omega, add_zero,
        Nat.mod_eq_of_lt hg']
      exact right_vtx0 J
    · have hδ : ztixu := by
        by_contra hδ0
        have := hCorr.hδ by_omega
        omega
      rw [← hpt₂', h0, Chazelle.Chain.sidePt_zero, ← hpos₂, hdL,
        show dq _ _ _ = rL1 J + rδ J by unfold dq; split_ifs <;> omega]
      zulzp
  have hsecEq : sideLeft (chainModel J.whole).W P t₂ =
      sideLeft (chainModel J.right).W ztcy t₂ := by
    rw [hPdef, hCorr.sideLeft_eq hd hsecd, hpos₂]
  have hsec₂ : ∀ s > 0, sideLeft (chainModel J.right).W ztcy t₂
      (rayPt ztxhj (-σ) s) := by
    zugg
    have hl' : sideLeft (chainModel J.right).W ztcy t₂
        (rayPt ztxhj (-σ) ztld) := by
      zupdr; exact hl₂
    exact (sideLeft_rayPt_iff _ _ t₂ _ hT2' hs).1 hl'
  have hsecW : ∀ s > 0, sideLeft (chainModel J.whole).W P t₂
      (rayPt ztmoj (-σ) s) := by
    zugg
    rw [hsecEq, hptW, ← hpt₂']
    exact hsec₂ s hs
  have happW : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      rayPt ztmoj (-σ) s ∈ G := by
    zuoyu; omega
  -- the region of `S₂` of the backward ray
  have hnearS : ∀ c ∈ S₂, ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∉ c := by
    zung
    zubdz

    by_cases hwc : w ∈ Visibility.hseg y a b
    · have hwD₂ := fun h => J.right.not_mem_set_of_mem_dom h hw2
      have hwend : w = ztdv ∨ w = ztdy := by
        obtain ⟨hq2, hqa, hqb⟩ := hwc
        zugab
        · zubui
          · exact absurd (show w ∈ J.right.dom by
              rw [show w = zthla from Prod.ext rfl hq2]
              exact hH.open_mem w.1 h1 h2) hwD₂
          grind
        grind
      obtain ⟨e, he, hwe, hec⟩ : ∃ e ∈ J.fusion ∅ S₂, w ∈ e ∧ e ⊆ Visibility.hseg y a b := by
        rcases hwend with h | h
        · have hlw : Merge.lend zteej = w := by_grind
          rw [hlw] at hL
          exact hL hwv
        · have hrw : Merge.rend zteej = w := by_grind
          rw [hrw] at hR
          exact hR hwv
      obtain ⟨y', a', b', hH', -, rfl⟩ := F₂plus_subset J hS₂ (Or.inl he)
      obtain ⟨ε, hε, hsub⟩ := ray_sub_hseg hH'.lt hec hwe hwend hnσ
      filter_upwards [Ioo_mem_nhdsGT (lt_min hε hT)] with s hs hsc
      have hsε := lt_of_lt_of_le hs.2 ztff
      have hsT := lt_of_lt_of_le hs.2 ztgh
      exact (hGfree (hbackG s hs.1 hsT)).2 ⟨_, Or.inl he, hsub s hs.1 hsε hsc⟩
    · have hcont : Tendsto (rayPt w (-σ)) (𝓝[>] (0 : ℝ)) (𝓝 w) := by
        have := ((Chazelle.Visibility.continuous_rayPt w (-σ)).tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        grind
      exact hcont ((Chazelle.Chain.isClosed_hseg y a b).isOpen_compl.mem_nhds hwc)
  have hfreeS₂ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∈ freeIn J.right.dom S₂ := by
    have hall := (hS₂f.eventually_all).2 hnearS
    filter_upwards [hall, Ioo_mem_nhdsGT hT] with s hs hsT
    zuevy
    zuifl
    exact hs c hc hxc
  obtain ⟨ε₀, hε₀, hε₀sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hfreeS₂
  have hε₀' : (0 : ℝ) < ε₀ := hε₀
  have hx₀ : rayPt w _ ztcop ∈ freeIn J.right.dom S₂ :=
    hε₀sub ztbcx
  set V := connectedComponentIn (freeIn J.right.dom S₂) (rayPt w (-σ) ztcop) with hVdef
  have hV := Chazelle.Chain.mem_regionsIn hx₀
  have hsubV : rayPt w (-σ) '' Ioo 0 ε₀ ⊆ V := by
    refine subset_region hV (isPreconnected_Ioo.image _
      (Chazelle.Visibility.continuous_rayPt w _).continuousOn) ?_
      ⟨ε₀ / 2, ⟨by_linarith, by_linarith⟩, rfl⟩ (mem_connectedComponentIn hx₀)
    zubyg
    exact hε₀sub hs
  have happV : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∈ V := by
    filter_upwards [Ioo_mem_nhdsGT hε₀'] with s hs
    exact hsubV ⟨s, hs, rfl⟩
  have hzV : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ V := by
    have hall := ray_subset_region J.right hS₂ hV hnσ hT hbackD happV
    zunv
    have := hall ztctq by_grind by_grind
    grind
  refine ⟨V, hV, hzV, ?_⟩
  have happV' : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      rayPt ztxhj (-σ) s ∈ V := by
    zupdr; omega
  have hFs' := hFs
  have hS₂' := hS₂
  rcases ht₂.lt_or_eq with htpos | ht0
  · -- inside a walk edge: the position itself
    have ht' : t₂ ∈ Ioo (0 : ℝ) 1 := by_grind
    obtain ⟨hcutW, hfW⟩ := approach_edge hM hFs' hFf hG hPn ht' hnσ hsecW happW
    obtain ⟨-, hfV⟩ := approach_edge hM₂ hS₂' hS₂f hV hp₂ ht' hnσ hsec₂ happV'
    exact ⟨d, hd, t₂, ht', hcutW, hfW, by_grind⟩
  -- at a walk vertex: a side where both walks face the regions
  zudlw
  obtain ⟨hd0, hdL⟩ := hsecd rfl
  have hP1 : ztrzy := by
    by_contra hP0
    have hP0' : P = 0 := by_omega
    have h0 := (J.whole.sidePt_box J.whole.sideBeta 0).1
    have h1 : sidePt (chainModel J.whole).W P 0 =
        (J.whole.top.1 + 0 * (-J.whole.radius - J.whole.top.1), J.whole.radius) := by
      rw [hP0']; try exact h0
    have hy := congrArg Prod.snd (hptW.symm.trans h1)
    zumpv
    have := J.whole.top_snd_lt_radius
    grind
  have hvv : (chainModel J.whole).W.vtx P = (chainModel J.right).W.vtx ztcy := by
    rw [← Chazelle.Chain.sidePt_zero, ← Chazelle.Chain.sidePt_zero, hptW, hpt₂']
  have hbb : (chainModel J.whole).W.vtx (ztnnt % (chainModel J.whole).W.n) =
      (chainModel J.right).W.vtx (ztcim % (chainModel J.right).W.n) := by
    have := hCorr.sideNext_eq hd
    zukvo
    zufep
  have haa : (chainModel J.whole).W.vtx (ztdlg %
      (chainModel J.whole).W.n) = (chainModel J.right).W.vtx ((i + 6 + (chainModel J.right).W.n - 1) %
      (chainModel J.right).W.n) := by
    have := hCorr.sidePrev_eq hd hsecd
    zukvo
    zulvb

  obtain ⟨hWnc, hWc⟩ := approach_vertex hM hFs' hFf hG hPn hP1 hnσ hsecW happW
  obtain ⟨hVnc, hVc⟩ := approach_vertex hM₂ hS₂' hS₂f hV hp₂ by_omega hnσ hsec₂ happV'
  rw [hbb, haa, hvv] at hWc
  have key : (∀ᶠ s in 𝓝[>] (0 : ℝ), (chainModel J.whole).Faces P s G ∧
        (chainModel J.right).Faces ztcy s V) ∨
      (∀ᶠ s in 𝓝[>] (0 : ℝ), (chainModel J.whole).Faces (P - 1) zteb G ∧
        (chainModel J.right).Faces ztqqz zteb V) := by
    by_cases hcW : (chainModel J.whole).IsCut ztbi ((P : ℝ) + 0)
    · obtain ⟨hd1, hA, hB⟩ := hWc hcW
      rcases hd1 with h | h
      · left
        have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), (chainModel J.right).Faces ztcy s V := by
          zqyw
          · exact (hVc hc2).2.1 h
          · exact (hVnc hc2).1
        exact (hA h).and h2
      · right
        have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), (chainModel J.right).Faces ztqqz zteb V := by
          zqyw
          · exact (hVc hc2).2.2 h
          · exact (hVnc hc2).2
        exact (hB h).and h2
    · zqyw
      · obtain ⟨hd2, hA2, hB2⟩ := hVc hc2
        rcases hd2 with h | h
        · left; exact (hWnc hcW).1.and (hA2 h)
        · right; exact (hWnc hcW).2.and (hB2 h)
      · left; exact (hWnc hcW).1.and (hVnc hc2).1
  rcases key with key | key
  · obtain ⟨s, ⟨⟨hfW, hfV⟩, hnc⟩, hs⟩ := ((key.and
      (eventually_not_cut_after hM hFs' hFf (P : ℝ))).and (Ioo_mem_nhdsGT one_pos)).exists
    exact ⟨d, hd, s, hs, hnc, hfW, by rw [hpos₂]; omega⟩
  · obtain ⟨s, ⟨⟨hfW, hfV⟩, hnc⟩, hs⟩ := ((key.and
      (eventually_not_cut_before hM hFs' hFf (P : ℝ))).and (Ioo_mem_nhdsGT one_pos)).exists
    have hn0 := hCorr.n_pos
    have hPm : (6 + tpos J.whole J.m₁ + ztku) % (chainModel J.whole).W.n = P - 1 := by
      rw [← mod_pred_mod hn0 _ (show 1 ≤ d by omega)]
      exact prev_mod hPn hP1
    have hdq1 : ztxda := by
      zugip
    zuccz
    have hPm₂ : ztwpj % (chainModel J.right).W.n =
        i + 6 - 1 := by
      rw [hdq1, ← mod_pred_mod hCorr.n₂_pos _ hdq0, hpos₂]
      exact prev_mod hp₂ by_omega
    refine ⟨d - 1, by_omega, 1 - s, ztexq, ?_, ?_, ?_⟩
    · rw [hPm, Nat.cast_sub hP1]
      push_cast
      rw [show (P : ℝ) - 1 + zteb = P - s by ring]
      omega
    · rw [hPm]; omega
    · rw [hPm₂]; omega
end Query

/-! ## Answering a query from the label -/
section Answer
variable (J : Merge.Junction)

/-- Points of the domain of `C` not above the top of `C₁` are in the domain of `C₁`. -/
theorem dom_left {x : Point} (hx : x ∈ J.whole.dom) (hx2 : x.2 ≤ J.left.top.2) :
    x ∈ J.left.dom := by
  zumv
  rcases (Merge.not_mem_dom_iff J.left hx2).1 h with h1 | h1
  · zufqn

  · exact J.whole.not_mem_set_of_mem_dom hx (J.left_set_subset h1)
