module

public import Chazelle.Core.OraclePrepQAt
public import Chazelle.Core.SpecPhases
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 64000000

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
  rw [chords_ncard hC.1, walk_n] at this
  linarith

/-- **The preprocessing.** -/
def prepMainS : Stmt := .seq phA (.seq phB (.seq bookS (.seq ordStage (.seq hdrS payS))))

/-- The bands of the preprocessing. -/
def prepBands : Finset ℕ := {bSign, bSort, bLocate, bDecomp, bOPrep, bOQuery, bCluster}

theorem prepBands_sub : prepBands ⊆ oracleBands ∪ {bOPrep} := by decide

/-- **The preprocessing meets its specification.** -/
theorem prep_meets : Meets prepMainS prepBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ ChainWF P (c.nreg ALLOC) c.nmem (rd c bOPrep 0) ∧
      ∃ H C N, ChainDescAt c.nmem (rd c bOPrep 0) (Qof P) H C ∧
      C.P = Qof P ∧ NFWithin c.nmem (rd c bOPrep 1) (c.nreg ALLOC) N ∧
      IsCanonicalNF (chainModel C) (Qof P) N (rd c bOPrep 2) 4)
    (fun P c c' => c.nreg ALLOC ≤ rd c' bOPrep 3 ∧ rd c' bOPrep 3 + 3 ≤ c'.nreg ALLOC ∧
      c'.nmem (rd c' bOPrep 3) = rd c bOPrep 0 ∧ c'.nmem (rd c' bOPrep 3 + 1) = rd c bOPrep 1 ∧
      c'.nmem (rd c' bOPrep 3 + 2) = rd c bOPrep 2 ∧
      ∀ m', (∀ a, a < c'.nreg ALLOC → m' a = c'.nmem a) → OAt P m' (rd c' bOPrep 3))
    (fun _ c => κq * (c.nmem (rd c bOPrep 1) *
      (Nat.clog 2 (c.nmem (rd c bOPrep 0 + 2)) + 1) + 1)) := by
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
    have := C.m_lt; rw [hCQ, hQn] at this; have := C.one_le; ufo hostWords at hHW
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
    ufo κq at this
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
  have agA : ∀ a, a < A₀ → cA.nmem a = c.nmem a := fun a ha => FA.2.2.1 a ha
  -- phase B
  obtain ⟨cB, kB, eB, hkB, GB, k12B, alB1, alB2, CH1, CH2, Dl, hCH1, v1, v2, v8, v34, v37,
      pairsB, hC1, hC2, hnd, hmem, hDl⟩ :=
    phB_exec (P := P) (c := cA) eA.wb_right hG hHW hCQ hsl hD ⟨hDA, hall⟩ hNFw hN agA PLA r205 pkA
      m0A mdcA (by omega) tbA (by rw [lA]; exact tabA) (by rw [lA]; exact Alt) rfl
      (by rwo [tbA, lA])
      (by rwo [regions_eq hsimp hN])
  rw [lA] at hkB
  set AB := cB.nreg ALLOC with hAB
  have hAB9 : cB.nreg 9999 = AB := rfl
  -- the book
  set B : BookData := ⟨N.arcs.length + 3, starList (rgi N) N.arcs.length, Dl⟩ with hB
  have hgok : GraphOK C (Qof P) N B := graphOK_of hN hsimp hnd hmem
  have hBN : B.N = N.arcs.length + 3 := rfl
  have hBE : B.E = N.arcs.length + 3 + (starList (rgi N) N.arcs.length ++ Dl).length := by
    show N.arcs.length + 3 + (starList (rgi N) N.arcs.length).length + Dl.length = _
    rwring [List.length_append]
  have hstarA : (starList (rgi N) N.arcs.length).length ≤ N.arcs.length := starList_length _ _
  have hBE8 : B.E ≤ 4 * N.arcs.length + 8 := by rwo [hBE, List.length_append]
  have hs20E : SortR.sortCost 20 (2 * B.E) ≤ 50 * (64 * F + 1) := sortCost_le (by omega)
  have hcl : clCost B.N B.E ≤ Cluster.clusterK * (64 * F + 1) :=
    clCost_le (by show N.arcs.length + 3 + B.E ≤ 64 * (N.chords.length + 1); omega)
  have hclK : Cluster.clusterK = 200000 := rfl
  rw [hclK] at hcl
  have b11 : cB.nreg 120011 = 1 := by rw [k12B _ (by norm_num) (by norm_num), PLA.one]
  have b12 : cB.nreg 120012 = 0 := by rw [k12B _ (by norm_num) (by norm_num), PLA.zero]
  have b48 : cB.nreg 120048 = 2 := by rw [k12B _ (by norm_num) (by norm_num), PLA.two]
  have b39 : cB.nreg 120039 = N.chords.length := by rw [k12B _ (by norm_num) (by norm_num), PLA.rK]
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
      (by rw [k12K _ (by norm_num) (by norm_num), b11]) rfl hFLb hLABb
      (by omega)
  set O := cO.nreg ALLOC with hOd
  have hO9 : cO.nreg 9999 = O := rfl
  -- the header
  obtain ⟨cH, kH, eH, hkH, h3H, h9H, RH, hdrH, hdr3, memH, rrH, rmH, oH⟩ :=
    hdrS_exec (P := P) (c := cO) (O := O) eO.wb_right rfl
      (by rw [FO.1 _ (by simp [dBands, bSort, bDecomp, bOPrep, bandOf]) (by decide),
        k12K _ (by norm_num) (by norm_num), b11]) (by omega)
  -- the payment
  have hH26 : cH.nreg 120026 = A₀ := by
    rw [RH _ (by decide) (by decide) (by decide) (by decide),
      FO.1 _ (by simp [dBands, bSort, bDecomp, bOPrep, bandOf]) (by decide),
      k12K _ (by norm_num) (by norm_num), k12B _ (by norm_num) (by norm_num), r26]
  have hH11 : cH.nreg 120011 = 1 := by
    rw [RH _ (by decide) (by decide) (by decide) (by decide),
      FO.1 _ (by simp [dBands, bSort, bDecomp, bOPrep, bandOf]) (by decide),
      k12K _ (by norm_num) (by norm_num), b11]
  obtain ⟨cP, kP, eP, hkP1, hkP2, RP, mP, rrP, rmP, oP⟩ := payS_exec (P := P) (c := cH) eH.wb_right
    hH26 h9H hH11
  have ex : Exec P W prepMainS c cP _ := .seq eA (.seq eB (.seq eK (.seq eO (.seq eH eP))))
  -- register facts of the end configuration
  have kO12 : ∀ r, 120010 ≤ r → r ≤ 120049 → cO.nreg r = cA.nreg r := fun r a b => by
    rw [FO.1 r (by sio [dBands, bSort, bDecomp, bOPrep, bandOf]) (by rwo [hAL]),
      k12K r a b, k12B r a b]
  have hP9 : cP.nreg ALLOC = O + 18 := by rw [hAL, RP _ (by decide) (by decide), h9H]
  have hP3 : cP.nreg 110003 = O := by rw [RP _ (by decide) (by decide), h3H]
  -- memory transports
  have mPH : ∀ a, cP.nmem a = cH.nmem a := fun a => by rw [mP]
  have mHO : ∀ a, a < O → cH.nmem a = cO.nmem a := fun a ha => memH a (Or.inl ha)
  have mOK : ∀ a, a < AK → cO.nmem a = cK.nmem a := memO
  have mKB : ∀ a, a < AB → cK.nmem a = cB.nmem a := GK.2.2.1
  have mBA : ∀ a, a < A₁ → cB.nmem a = cA.nmem a := GB.2.2.1
  have hA₁B : A₁ ≤ AB := by omega
  have hABK : AB ≤ AK := alK1
  have hAKO : AK ≤ O := alO1
  have mPA : ∀ a, a < A₁ → cP.nmem a = cA.nmem a := fun a ha => by
    rw [mPH, mHO a (by omega), mOK a (by omega), mKB a (by omega), mBA a ha]
  have mP0 : ∀ a, a < A₀ → cP.nmem a = c.nmem a := fun a ha => by
    rw [mPA a (by omega), agA a ha]
  have mPO : ∀ a, a < O → cP.nmem a = cO.nmem a := fun a ha => by rw [mPH, mHO a ha]
  have mPK : ∀ a, a < AK → cP.nmem a = cK.nmem a := fun a ha => by
    rw [mPO a (by omega), mOK a ha]
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
    ufnl κq
  · -- the post-condition
    refine ⟨by show A₀ ≤ cP.nreg 110003; rwo [hP3],
      (by show cP.nreg 110003 + 3 ≤ _; rwo [hP3, hP9]), ?_, ?_, ?_, fun m' hm' => ?_⟩
    · show cP.nmem (cP.nreg 110003) = c.nreg 110000
      rw [hP3, mPH, show O = O + 0 from rfl, hdrH 0 (by norm_num) (by norm_num)]
      show cO.nreg 120013 = _
      rw [kO12 _ (by norm_num) (by norm_num), PLA.rD]
    · show cP.nmem (cP.nreg 110003 + 1) = c.nreg 110001
      rw [hP3, mPH, hdrH 1 (by norm_num) (by norm_num)]
      show cO.nreg 120014 = _
      rw [kO12 _ (by norm_num) (by norm_num), PLA.rNB]
    · show cP.nmem (cP.nreg 110003 + 2) = c.nreg 110002
      rw [hP3, mPH, hdrH 2 (by norm_num) (by norm_num)]
      show cO.nreg 120049 = _
      rw [kO12 _ (by norm_num) (by norm_num), r49]
    · show OAt P m' (cP.nreg 110003)
      rw [hP3]
      rw [hP9] at hm'
      refine ⟨O + 18, by rw [hm' _ (by omega), mPH, hdr3], by omega, ?_⟩
      refine Robust.transport ?_ hm'
      refine qat_of (m := cP.nmem) (m₀ := c.nmem) (A₀ := A₀) (D := D) (NB := NB) (γ := γ) (O := O)
        (E := O + 18) (H := H) (C := C) (N := N) (B := B) (k := cK.nreg 60090)
        (POS := cA.nreg 120031) (FL := FL) (LAB := LAB) (DL := cO.nreg 60100)
        (nD := cO.nreg 60102) (ORD := cO.nreg 60007) (RK := cO.nreg 60110) (CH := CH) (MD := MD)
        (TB := cA.nreg 120041) (L := (Nat.clog 2 (N.arcs.length + N.chords.length + 1))) (Vc := qvOf cA) hG hCQ hD ⟨hDA, hall⟩ hNFw hcan mP0
        ?_ rfl (by omega) ch2 tbA (by rw [posA]) (by rwo [posA, tbA])
        (by omega) (by omega) hDLO hORDO hRKO
        (by rw [mPA _ (by omega)]; exact m0A)
        (fun i hi => by rw [mPA _ (by omega)]; exact mdcA i hi)
        (fun j hj => by rw [mPA _ (by rwo [a9A, tbA])]; exact tabA j hj)
        Alt Klt rfl
        (fun j hj => by rw [mPA _ (by rwo [a9A, posA, tbA])]; exact pfA j hj)
        (fun q hq => by rw [mPA _ (by omega)]; exact chltA q hq)
        (fun q q' hq hq' e => by
          rw [mPA _ (by omega), mPA _ (by omega)] at e
          exact chinjA q q' hq hq' e)
        ⟨PLA.rCB, by show cA.nreg 120016 = _; rw [PLA.rm, hcm],
          by show cA.nreg 120015 = _; rw [PLA.rs, hD.2.2.1],
          by show cA.nreg 120022 = _; rw [PLA.tv, hD.2.2.1, hD.2.2.2.2.1]⟩
        (fun q q' hqq hq' => by
          rw [mPA _ (by omega), mPA _ (by omega)]
          exact chsA q q' hqq hq')
        hgok rfl (hclF.mono mPK hFLb hLABb)
        (hordF.mono mPO (by rwo [hBN] at hFLb) (by rwo [hBN] at hLABb) hDLO hORDO
          hRKO)
      -- the header words
      intro i hi
      rw [mPH]
      by_cases h3 : i = 3
      · subst h3; rwr [hdr3]
      by_cases h17 : i = 17
      · subst h17
        rw [hdrH 17 hi h3]
        simp only [hdrRegs, hdrVals, List.getD_cons_zero, List.getD_cons_succ]
        rw [KO _ (by ufn bandOf) (by ufo OKeep)]; exact v34K
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
            | (rw [FO.1 _ (by simp [dBands, bSort, bDecomp, bOPrep, bandOf]) (by decide)])
  · -- the frame
    have hS : ∀ S, S ⊆ prepBands → ∀ r, bandOf r ∉ prepBands → bandOf r ∉ S :=
      fun S hS r hr h => hr (hS h)
    refine ⟨fun r hr hra => ?_, fun r hr => ?_, fun a ha => mP0 a ha, fun a ha => ?_, ?_, ?_, ?_⟩
    · have h11 : bandOf r ≠ 11 := fun h => hr (by simp [prepBands, bOPrep, h])
      unfold bandOf at h11
      rw [RP r (by omega) (by omega), RH r (by omega) (by omega) (by omega) (by rw [hAL] at hra; exact hra),
        FO.1 r (hS _ (by decide) r hr) hra, GK.1 r (hS _ (by decide) r hr) hra,
        GB.1 r (hS _ (by decide) r hr) hra, FA.1 r (hS _ (by decide) r hr) hra]
    · rw [rrP, rrH, FO.2.1 r (hS _ (by decide) r hr), GK.2.1 r (hS _ (by decide) r hr),
        GB.2.1 r (hS _ (by decide) r hr), FA.2.1 r (hS _ (by decide) r hr)]
    · rw [rmP, rmH, FO.2.2.2.1 a (by omega), GK.2.2.2.1 a (by omega),
        GB.2.2.2.1 a (by omega), FA.2.2.2.1 a ha]
    · rw [oP, oH, FO.2.2.2.2, GK.2.2.2.2, GB.2.2.2.2, FA.2.2.2.2]
    · rwo [hP9]
    · rwo [hP9]

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
    query_meets ⟨by decide, by decide, by decide⟩ le_rfl⟩

end

end OracleR

public section

/-- **WP-H: the Lemma 3.6 oracle.** -/
theorem oracleSpec : OracleSpec := ⟨OracleR.lemma36Oracle, OracleR.lemma36Oracle_valid⟩

end

end Chazelle.Core
