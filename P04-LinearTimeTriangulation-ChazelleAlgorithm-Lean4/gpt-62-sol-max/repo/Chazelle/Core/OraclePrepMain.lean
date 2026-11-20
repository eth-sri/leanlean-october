module

public import Chazelle.Core.OraclePrepQAt
public import Chazelle.Core.SpecPhases

/-!
# Lemma 3.6 (WP-H), preprocessing part 36: the preprocessing meets its specification

`prepMainS := phA; phB; bookS; ordStage; hdrS; payS`.  `prep_meets`: it meets the preprocessing clause
of `OracleIface.Valid` for the structure predicate `OAt`, the bands `prepBands` and the cost
constant `κq` of the query.  `oracleSpec : OracleSpec`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ OracleBook

@[expose] public section

/-- **Lemma 2.3** for a canonical normal form of a chain: `K γ ≤ 60 (2 m + 7)`. -/
theorem chords_mul_le {C : Chain} {Q : Polygon} {N : NF} {γ : ℕ} (hP : C.P.Simple)
    (hC : IsCanonicalNF (chainModel C) Q N γ 4) : N.chords.length * γ ≤ 60 * (2 * C.m + 7) := by
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  have hM := walkAx_of_goodModel hGM
  have hF := hC.1.1
  have := hM.lemma23_walk hF.2.1 hF.1 hC.2.1 hC.2.2.1
  rw [hC.1.ncard_chords, walk_n] at this
  linarith

/-- **The preprocessing.** -/
def prepMainS : Stmt := .seq phA (.seq phB (.seq bookS (.seq ordStage (.seq hdrS payS))))

/-- The bands of the preprocessing. -/
def prepBands : Finset ℕ := {bSign, bSort, bLocate, bDecomp, bOPrep, bOQuery, bCluster}

theorem prepBands_sub : prepBands ⊆ oracleBands ∪ {bOPrep} := by decide

set_option maxHeartbeats 64000000 in
/-- **The preprocessing meets its specification.** -/
theorem prep_meets : OraclePrepMeets prepMainS prepBands κq OAt := by
  intro P W c hw ⟨hG, hHW, hwf, H, C, N, hD, hCQ, hNFw, hcan⟩ hroom
  have hAL : ALLOC = 9999 := rfl
  have hr0 : rd c bOPrep 0 = c.nreg 110000 := rfl
  have hr1 : rd c bOPrep 1 = c.nreg 110001 := rfl
  have hr2 : rd c bOPrep 2 = c.nreg 110002 := rfl
  beta_reduce at hroom
  rw [hr0] at hwf hD hroom
  rw [hr1] at hNFw hroom
  rw [hr2] at hcan
  set D := c.nreg 110000 with hDdef
  set NB := c.nreg 110001 with hNBdef
  set γ := c.nreg 110002 with hγdef
  set A₀ := c.nreg ALLOC with hA₀def
  have hAl : c.nreg 9999 = A₀ := rfl
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hN := hcan.1
  have hsimp : C.P.Simple := by rw [hCQ]; exact (shearInvariance (epsOf P) P).1 hG.1
  have hA0 := arcs_pos hsimp hN
  have hNF : NFAt c.nmem NB N := hNFw.nfAt
  obtain ⟨hDA, hall⟩ := hwf
  obtain ⟨-, -, -, hsl⟩ := hall H C hD
  have hW8 : 8 * P.n + 32 ≤ W := by
    have := C.m_lt; rw [hCQ, hQn] at this; have := C.one_le; unfold hostWords at hHW; omega
  -- the parameters
  have hcK : c.nmem NB = N.chords.length := hNF.1
  have hcm : c.nmem (D + 2) = C.m := hD.2.2.2.1
  rw [hcK, hcm] at hroom
  have hγ1 := gamma_pos hsimp hcan
  have hK23 : N.chords.length ≤ 60 * (2 * C.m + 7) := by
    have := chords_mul_le hsimp hcan; nlinarith
  have hm1 := C.one_le
  have hRK1 : N.regions.length = N.chords.length + 1 := regions_eq hsimp hN
  have hA5 : N.arcs.length ≤ 5 * (N.chords.length + 1) := by
    have h1 := arcs_le_regions hsimp hcan
    rw [regions_eq hsimp hN] at h1; exact h1
  set X := N.chords.length * (Nat.clog 2 C.m + 1) + 1 with hX
  set F := Fb N.chords.length with hF
  have hFX : F ≤ 40 * X := Fb_le hm1 hK23
  have hF1 := one_le_Fb N.chords.length
  have hKF := K_le_Fb N.chords.length
  have hroomF : A₀ + 50000000000 * F ≤ W := by
    have : κq * X ≤ W - A₀ := by omega
    unfold κq at this; omega
  have hLF : Nat.clog 2 (N.arcs.length + N.chords.length + 1) ≤ F := clog_le_Fb (by omega)
  have hALF : N.arcs.length * (Nat.clog 2 (N.arcs.length + N.chords.length + 1) + 1) ≤ 5 * F := mul_clog_le_Fb hA5 (by omega)
  have hs500 : SortR.sortCost 500 N.chords.length ≤ 530 * (64 * F + 1) := sortCost_le (by omega)
  have hs20A : SortR.sortCost 20 (2 * N.arcs.length + 5) ≤ 50 * (64 * F + 1) := sortCost_le (by omega)
  -- phase A
  obtain ⟨cA, kA, eA, hkA, FA, ch1, ch2, mdle, a9A, PLA, r25, r23, r24, r49, r205, r26, m0A, mdcA,
      tbA, lA, tabA, Alt, Klt, posA, pfA, pkA, chltA, chinjA, chsA⟩ :=
    phA_exec (P := P) hw hG hW8 hD hCQ hsl hNFw hN hAl hDA (by omega)
  set MD := cA.nreg 120040 with hMD
  set CH := cA.nreg 120038 with hCH
  set A₁ := cA.nreg 9999 with hA₁
  have agA : MemEqBelow A₀ cA.nmem c.nmem := fun a ha => FA.2.2.1 a ha
  -- phase B
  obtain ⟨cB, kB, eB, hkB, GB, k12B, alB1, alB2, CH1, CH2, Dl, hCH1, v1, v2, v8, v34, v37,
      pairsB, hC1, hC2, hnd, hmem, hDl⟩ :=
    phB_exec (P := P) (c := cA) eA.wb_right hG hHW hCQ hsl hD ⟨hDA, hall⟩ hNFw hN agA PLA r205 pkA
      m0A mdcA (by omega) tbA (by rw [lA]; exact tabA) (by rw [lA]; exact Alt) rfl
      (by rw [tbA, lA]; omega)
      (by rw [regions_eq hsimp hN]; omega)
  rw [lA] at hkB
  set AB := cB.nreg ALLOC with hAB
  have hAB9 : cB.nreg 9999 = AB := rfl
  -- the book
  set B : BookData := ⟨N.arcs.length + 3, starList (rgi N) N.arcs.length, Dl⟩ with hB
  have hgok : GraphOK C (Qof P) N B := graphOK_of hN hsimp hnd hmem
  have hBN : B.N = N.arcs.length + 3 := rfl
  have hBE : B.E = N.arcs.length + 3 + (starList (rgi N) N.arcs.length ++ Dl).length := by
    show N.arcs.length + 3 + (starList (rgi N) N.arcs.length).length + Dl.length = _
    rw [List.length_append]; ring
  have hstarA : (starList (rgi N) N.arcs.length).length ≤ N.arcs.length := starList_length _ _
  have hBE8 : B.E ≤ 4 * N.arcs.length + 8 := by rw [hBE, List.length_append]; omega
  have hs20E : SortR.sortCost 20 (2 * B.E) ≤ 50 * (64 * F + 1) := sortCost_le (by omega)
  have hcl : clCost B.N B.E ≤ Cluster.clusterK * (64 * F + 1) :=
    clCost_le (by show N.arcs.length + 3 + B.E ≤ 64 * (N.chords.length + 1); omega)
  have hclK : Cluster.clusterK = 200000 := rfl
  rw [hclK] at hcl
  have b11 : cB.nreg 120011 = 1 := by ram_rw [k12B, PLA.one]
  have b12 : cB.nreg 120012 = 0 := by ram_rw [k12B, PLA.zero]
  have b48 : cB.nreg 120048 = 2 := by ram_rw [k12B, PLA.two]
  have b39 : cB.nreg 120039 = N.chords.length := by ram_rw [k12B, PLA.rK]
  obtain ⟨cK, kK, eK, hkK, GK, k12K, v34K, alK1, alK2, hFLa, hLABa, hFLb, hLABb, hclF⟩ :=
    bookS_exec (P := P) (c := cB) eB.wb_right hG hCQ hcan hgok rfl v1 v2 v8 v34
      (by rw [v37, hBE]) b11 b12 b48 b39 rfl pairsB
      (by show CH1 + (starList (rgi N) N.arcs.length ++ Dl).length ≤ cB.nreg 9999; omega)
      (by show CH2 + (starList (rgi N) N.arcs.length ++ Dl).length ≤ cB.nreg 9999; omega)
      (by omega) (by omega) (by omega)
  set FL := cK.nreg 130004 with hFLd
  set LAB := cK.nreg 130005 with hLABd
  set AK := cK.nreg ALLOC with hAK
  have hAK9 : cK.nreg 9999 = AK := rfl
  have hs20μ : SortR.sortCost 20 (N.arcs.length + 3) ≤ 50 * (64 * F + 1) := sortCost_le (by omega)
  have hs20N : SortR.sortCost 20 B.N ≤ 50 * (64 * F + 1) := hs20μ
  -- the order by label
  obtain ⟨cO, kO, eO, hkO, FO, alO1, alO2, KO, memO, hDLO, hORDO, hRKO, hordF⟩ :=
    ordStage_exec (P := P) (c := cK) eK.wb_right v34K rfl rfl
      (by ram_rw [k12K, b11]) rfl hFLb hLABb
      (by omega)
  set O := cO.nreg ALLOC with hOd
  have hO9 : cO.nreg 9999 = O := rfl
  -- the header
  obtain ⟨cH, kH, eH, hkH, h3H, h9H, RH, hdrH, hdr3, memH, rrH, rmH, oH⟩ :=
    hdrS_exec (P := P) (c := cO) (O := O) eO.wb_right rfl
      (by ram_rw [FO.1,
        k12K, b11]) (by omega)
  -- the payment
  have hH26 : cH.nreg 120026 = A₀ := by
    ram_rw [RH,
      FO.1,
      k12K, k12B, r26]
  have hH11 : cH.nreg 120011 = 1 := by
    ram_rw [RH,
      FO.1,
      k12K, b11]
  obtain ⟨cP, kP, eP, hkP1, hkP2, RP, mP, rrP, rmP, oP⟩ := payS_exec (P := P) (c := cH) eH.wb_right
    hH26 h9H hH11
  have ex : Exec P W prepMainS c cP _ := .seq eA (.seq eB (.seq eK (.seq eO (.seq eH eP))))
  -- register facts of the end configuration
  have kO12 : ∀ r, 120010 ≤ r → r ≤ 120049 → cO.nreg r = cA.nreg r := fun r a b => by
    rw [FO.1 r (by simp [dBands, bSort, bDecomp, bOPrep, bandOf]; omega) (by rw [hAL]; omega),
      k12K r a b, k12B r a b]
  have hP9 : cP.nreg ALLOC = O + 18 := by ram_rw [hAL, RP, h9H]
  have hP3 : cP.nreg 110003 = O := by ram_rw [RP, h3H]
  -- memory transports
  have mPH : ∀ a, cP.nmem a = cH.nmem a := fun a => by rw [mP]
  have mHO : MemEqBelow O cH.nmem cO.nmem := fun a ha => memH a (Or.inl ha)
  have mOK : MemEqBelow AK cO.nmem cK.nmem := memO
  have mKB : MemEqBelow AB cK.nmem cB.nmem := GK.2.2.1
  have mBA : MemEqBelow A₁ cB.nmem cA.nmem := GB.2.2.1
  have hA₁B : A₁ ≤ AB := by omega
  have hABK : AB ≤ AK := alK1
  have hAKO : AK ≤ O := alO1
  have mPA : MemEqBelow A₁ cP.nmem cA.nmem := fun a ha => by
    ram_rw [mPH, mHO a, mOK a, mKB a, mBA a ha]
  have mP0 : MemEqBelow A₀ cP.nmem c.nmem := fun a ha => by
    ram_rw [mPA a, agA a ha]
  have mPO : MemEqBelow O cP.nmem cO.nmem := fun a ha => by rw [mPH, mHO a ha]
  have mPK : MemEqBelow AK cP.nmem cK.nmem := fun a ha => by
    ram_rw [mPO a, mOK a ha]
  -- the cost
  have hz : 2 * N.arcs.length * (5500 * ((Nat.clog 2 (N.arcs.length + N.chords.length + 1)) + 1) + 410) = 11000 * (N.arcs.length * ((Nat.clog 2 (N.arcs.length + N.chords.length + 1)) + 1)) + 820 * N.arcs.length := by ring
  have hkPE : kP ≤ 3 * (O + 18 - A₀) + 4 := hkP1
  have hEk : O + 18 - A₀ ≤ kP := hkP2
  have hsubO : O + 18 - A₀ + A₀ = O + 18 := Nat.sub_add_cancel (by omega)
  refine ⟨cP, _, ex, ?_, ?_, ?_⟩
  · -- the cost bound
    show _ ≤ κq * (c.nmem NB * (Nat.clog 2 (c.nmem (D + 2)) + 1) + 1)
    rw [hcK, hcm]
    have hk : kA + (kB + (kK + (kO + (kH + kP)))) ≤ 100000000 * F := by
      rw [hz] at hkB
      unfold κq at *
      omega
    change _ ≤ κq * X
    unfold κq
    omega
  · -- the post-condition
    refine ⟨by show A₀ ≤ cP.nreg 110003; rw [hP3]; omega,
      (by show cP.nreg 110003 + 3 ≤ _; rw [hP3, hP9]; omega), ?_, ?_, ?_, fun m' hm' => ?_⟩
    · show cP.nmem (cP.nreg 110003) = c.nreg 110000
      ram_rw [hP3, mPH, show O = O + 0 from rfl, hdrH 0]
      show cO.nreg 120013 = _
      ram_rw [kO12, PLA.rD]
    · show cP.nmem (cP.nreg 110003 + 1) = c.nreg 110001
      ram_rw [hP3, mPH, hdrH 1]
      show cO.nreg 120014 = _
      ram_rw [kO12, PLA.rNB]
    · show cP.nmem (cP.nreg 110003 + 2) = c.nreg 110002
      ram_rw [hP3, mPH, hdrH 2]
      show cO.nreg 120049 = _
      ram_rw [kO12, r49]
    · show OAt P m' (cP.nreg 110003)
      rw [hP3]
      rw [hP9] at hm'
      refine ⟨O + 18, by ram_rw [hm', mPH, hdr3], by omega, ?_⟩
      refine Robust.transport ?_ hm'
      refine qat_of (m := cP.nmem) (m₀ := c.nmem) (A₀ := A₀) (D := D) (NB := NB) (γ := γ) (O := O)
        (E := O + 18) (H := H) (C := C) (N := N) (B := B) (k := cK.nreg 60090)
        (POS := cA.nreg 120031) (FL := FL) (LAB := LAB) (DL := cO.nreg 60100)
        (nD := cO.nreg 60102) (ORD := cO.nreg 60007) (RK := cO.nreg 60110) (CH := CH) (MD := MD)
        (TB := cA.nreg 120041) (L := (Nat.clog 2 (N.arcs.length + N.chords.length + 1))) (Vc := qvOf cA) hG hCQ hD ⟨hDA, hall⟩ hNFw hcan mP0
        ?_ rfl (by omega) ch2 tbA (by rw [posA]) (by rw [posA, tbA]; omega)
        (by omega) (by omega) hDLO hORDO hRKO
        (by ram_rw [mPA]; exact m0A)
        (fun i hi => by ram_rw [mPA]; exact mdcA i hi)
        (fun j hj => by rw [mPA _ (by rw [a9A, tbA]; omega)]; exact tabA j hj)
        Alt Klt rfl
        (fun j hj => by rw [mPA _ (by rw [a9A, posA, tbA]; omega)]; exact pfA j hj)
        (fun q hq => by ram_rw [mPA]; exact chltA q hq)
        (fun q q' hq hq' e => by
          ram_rw [mPA, mPA] at e
          exact chinjA q q' hq hq' e)
        ⟨PLA.rCB, by show cA.nreg 120016 = _; rw [PLA.rm, hcm],
          by show cA.nreg 120015 = _; rw [PLA.rs, hD.2.2.1],
          by show cA.nreg 120022 = _; rw [PLA.tv, hD.2.2.1, hD.2.2.2.2.1]⟩
        (fun q q' hqq hq' => by
          ram_rw [mPA, mPA]
          exact chsA q q' hqq hq')
        hgok rfl (hclF.mono mPK hFLb hLABb)
        (hordF.mono mPO (by rw [hBN] at hFLb; omega) (by rw [hBN] at hLABb; omega) hDLO hORDO
          hRKO)
      -- the header words
      intro i hi
      rw [mPH]
      by_cases h3 : i = 3
      · subst h3; rw [hdr3]; rfl
      by_cases h17 : i = 17
      · subst h17
        rw [hdrH 17 hi h3]
        simp only [hdrRegs, hdrVals, List.getD_cons_zero, List.getD_cons_succ]
        rw [KO _ (by reg_omega) (by unfold OKeep; omega)]; exact v34K
      · rw [hdrH i hi h3]
        interval_cases i <;> simp only [hdrRegs, hdrVals, List.getD_cons_zero,
          List.getD_cons_succ] <;>
          first
            | rfl
            | exact absurd rfl h3
            | exact absurd rfl h17
            | (rw [kO12 _ (by norm_num) (by norm_num)]
               all_goals first
                 | exact PLA.rD
                 | exact PLA.rNB
                 | exact r49
                 | exact PLA.rA
                 | exact PLA.rK
                 | exact lA
                 | rfl)
            | (ram_rw [FO.1])
  · -- the frame
    have hS : ∀ S, S ⊆ prepBands → ∀ r, bandOf r ∉ prepBands → bandOf r ∉ S :=
      fun S hS r hr h => hr (hS h)
    refine ⟨fun r hr hra => ?_, fun r hr => ?_, fun a ha => mP0 a ha, fun a ha => ?_, ?_, ?_, ?_⟩
    · have h11 : bandOf r ≠ 11 := fun h => hr (by simp [prepBands, bOPrep, h])
      unfold bandOf at h11
      ram_rw [RP r, RH r (by omega) (by omega) (by omega) (by rw [hAL] at hra; exact hra),
        FO.1 r (hS _ (by decide) r hr) hra, GK.1 r (hS _ (by decide) r hr) hra,
        GB.1 r (hS _ (by decide) r hr) hra, FA.1 r (hS _ (by decide) r hr) hra]
    · rw [rrP, rrH, FO.2.1 r (hS _ (by decide) r hr), GK.2.1 r (hS _ (by decide) r hr),
        GB.2.1 r (hS _ (by decide) r hr), FA.2.1 r (hS _ (by decide) r hr)]
    · ram_rw [rmP, rmH, FO.2.2.2.1 a, GK.2.2.2.1 a,
        GB.2.2.2.1 a, FA.2.2.2.1 a ha]
    · rw [oP, oH, FO.2.2.2.2, GK.2.2.2.2, GB.2.2.2.2, FA.2.2.2.2]
    · rw [hP9]; omega
    · rw [hP9]; omega

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
    query_meets (by decide) le_rfl⟩

end

end OracleR

public section

/-- **WP-H: the Lemma 3.6 oracle.** -/
theorem oracleSpec : OracleSpec := ⟨OracleR.lemma36Oracle, OracleR.lemma36Oracle_valid⟩

end

end Chazelle.Core
