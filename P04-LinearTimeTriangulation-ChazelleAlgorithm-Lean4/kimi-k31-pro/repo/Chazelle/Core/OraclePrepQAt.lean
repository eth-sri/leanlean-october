module

public import Chazelle.Core.OraclePrepCost
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
set_option maxHeartbeats 16000000

/-!
# Lemma 3.6 (WP-H), preprocessing part 35: the structure from the memory facts

`qat_of`: from the memory facts established by the preprocessing (the header at `O`, the
descriptors, tables and arrays below `E = O + 18`, and the input descriptors below `A₀`), the
structure `QAt` holds for every memory agreeing below `E`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ OracleBook

@[expose] public section

/-- The values of the structure. -/
def qvFin (P : Polygon) (m₀ : ℕ → ℕ) (D NB A K POS FL LAB DL nD ORD RK CH MD TB L : ℕ) : QV where
  D := D
  NB := NB
  s := m₀ (D + 1)
  m := m₀ (D + 2)
  tIdx := m₀ (D + 3)
  β := m₀ (D + 4)
  sS := if m₀ (D + 4) = 1 then m₀ (D + 3) else 2 * m₀ (D + 2) - m₀ (D + 3)
  tv := (m₀ (D + 1) + m₀ (D + 3)) % P.n
  hz := 0
  σb := 0
  zo := none
  A := A
  POS := POS
  FL := FL
  LAB := LAB
  DL := DL
  nD := nD
  ORD := ORD
  RK := RK
  CH := CH
  K := K
  MD := MD
  TB := TB
  L := L
  CB := m₀ (NB + 3)
  AB := m₀ (NB + 4)
  RB := m₀ (NB + 5)
  SB := m₀ (NB + 6)
  LB := m₀ (NB + 7)
  μ := A + 3

/-- The words of the header. -/
def hdrVals (D NB γ E A POS FL LAB DL nD ORD RK CH K MD TB L μ : ℕ) : List ℕ :=
  [D, NB, γ, E, A, POS, FL, LAB, DL, nD, ORD, RK, CH, K, MD, TB, L, μ]

/-- **The structure from the memory facts.** -/
theorem qat_of {P : Polygon} {m m₀ : ℕ → ℕ} {A₀ D NB γ O E : ℕ} {H : Host} {C : Chain}
    {N : NF} {B : BookData} {k POS FL LAB DL nD ORD RK CH MD TB L : ℕ} {Vc : QV}
    (hG : GoodEnv P) (hCQ : C.P = Qof P)
    (hD : ChainDescAt m₀ D (Qof P) H C) (hwf : ChainWF P A₀ m₀ D)
    (hNFw : NFWithin m₀ NB A₀ N) (hcan : IsCanonicalNF (chainModel C) (Qof P) N γ 4)
    (hagree : ∀ a, a < A₀ → m a = m₀ a)
    (hhdr : ∀ i, i < 18 → m (O + i) = (hdrVals D NB γ E N.arcs.length POS FL LAB DL nD ORD RK CH
      N.chords.length MD TB L (N.arcs.length + 3)).getD i 0)
    (hE : E = O + 18)
    (hCHA : A₀ ≤ CH) (hCHM : CH + N.chords.length ≤ MD) (hTB : TB = MD + 6)
    (hPOS : TB + L ≤ POS) (hPOSO : POS + N.arcs.length ≤ O)
    (hFL : FL + (N.arcs.length + 3) ≤ O) (hLAB : LAB + (N.arcs.length + 3) ≤ O)
    (hDL : DL + nD ≤ O) (hORD : ORD + (N.arcs.length + 3) ≤ O)
    (hRK : RK + (N.arcs.length + 3) ≤ O)
    (hmd0 : m MD = 0) (hmdc : ∀ i, i < 5 → m (MD + 1 + i) = m₀ (D + i))
    (htab : ∀ j, j < L → m (TB + j) = 2 ^ j) (hAlt : N.arcs.length < 2 ^ L)
    (hKlt : N.chords.length < 2 ^ L) (hL : L = Nat.clog 2 (N.arcs.length + N.chords.length + 1))
    (hpos : ∀ j, j < N.arcs.length → m (POS + j) < N.arcs.length ∧
      N.seq.getD (m (POS + j)) 0 = j)
    (hchlt : ∀ q, q < N.chords.length → m (CH + q) < N.chords.length)
    (hchinj : ∀ q q', q < N.chords.length → q' < N.chords.length → m (CH + q) = m (CH + q') →
      q = q')
    (hVc : Vc.CB = m₀ (NB + 3) ∧ Vc.m = m₀ (D + 2) ∧ Vc.s = m₀ (D + 1) ∧
      Vc.tv = (m₀ (D + 1) + m₀ (D + 3)) % P.n)
    (hchsort : ∀ q q', q ≤ q' → q' < N.chords.length →
      ChLe P C Vc m₀ (m (CH + q)) (m (CH + q')))
    (hgok : GraphOK C (Qof P) N B) (hBN : B.N = N.arcs.length + 3)
    (hcl : ClFacts m B FL LAB k) (hord : OrdFacts m (N.arcs.length + 3) FL LAB DL nD ORD RK) :
    Robust E m fun m'' => ∃ V H C N B k, QAt P m'' O E V H C N B k := by
  intro m'' hm''
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hN := hcan.1
  have hsimp : C.P.Simple := by rw [hCQ]; exact (shearInvariance (epsOf P) P).1 hG.1
  have hA0 := arcs_pos hsimp hN
  obtain ⟨hNB7, hABb, hSBb⟩ := NFLoc.nfWithin_bounds hNFw hN hA0
  have hNB11 : NB + 11 < A₀ := NFLoc.robust_addr (fun m' hm' => (hNFw m' hm').2.2.2.2.1)
  obtain ⟨hDA, hall⟩ := hwf
  obtain ⟨hHl, hHwf, hHb, hCs⟩ := hall H C hD
  have hOE : O + 18 ≤ E := by omega
  have hA₀O : A₀ ≤ O := by omega
  have ag0 : ∀ a, a < A₀ → m'' a = m₀ a := fun a ha => by rw [hm'' a (by omega), hagree a ha]
  have agE : ∀ a, a < O → m'' a = m a := fun a ha => hm'' a (by omega)
  have hNF'' : NFAt m'' NB N := hNFw m'' ag0
  have hD'' : ChainDescAt m'' D (Qof P) H C := chainDescAt_agree hD hDA hHb ag0
  set A := N.arcs.length with hAdef
  set K := N.chords.length with hKdef
  set V := qvFin P m₀ D NB A K POS FL LAB DL nD ORD RK CH MD TB L with hV
  have hVA : V.A = A := rfl
  have hVK : V.K = K := rfl
  have hVL : V.L = L := rfl
  have hVCH : V.CH = CH := rfl
  have hh : ∀ i, i < 18 → m'' (O + i) = (hdrVals D NB γ E A POS FL LAB DL nD ORD RK CH K MD TB L
      (A + 3)).getD i 0 := fun i hi => by rw [hm'' _ (by omega)]; exact hhdr i hi
  obtain ⟨-, -, hd1, hd2, hd3, hd4⟩ := hD
  have hcb : ∀ i, i < K → m₀ (NB + 3) + 5 * i + 4 < A₀ := fun i hi => by
    have h1 : Robust A₀ m₀ fun m' => m' (m' (NB + 3) + (5 * i + 4)) = (N.chord i).dn :=
      fun m' hm' => by
        have := ((hNFw m' hm').2.2.2.2.2.1 i hi).2.2.2.2
        simpa only [Nat.add_assoc] using this
    have := (NFLoc.robust_addr2 h1).2; omega
  refine ⟨V, H, C, N, B, k, ?_⟩
  exact
    { lD := hh 0 (by norm_num)
      lNB := hh 1 (by norm_num)
      lE := hh 3 (by norm_num)
      lA := hh 4 (by norm_num)
      lPOS := hh 5 (by norm_num)
      lFL := hh 6 (by norm_num)
      lLAB := hh 7 (by norm_num)
      lDL := hh 8 (by norm_num)
      lnD := hh 9 (by norm_num)
      lORD := hh 10 (by norm_num)
      lRK := hh 11 (by norm_num)
      lCH := hh 12 (by norm_num)
      lK := hh 13 (by norm_num)
      lMD := hh 14 (by norm_num)
      lTB := hh 15 (by norm_num)
      lL := hh 16 (by norm_num)
      lμ := hh 17 (by norm_num)
      O_le := hOE
      ds := by show m'' (D + 1) = m₀ (D + 1); exact ag0 _ (by omega)
      dm := by show m'' (D + 2) = m₀ (D + 2); exact ag0 _ (by omega)
      dt := by show m'' (D + 3) = m₀ (D + 3); exact ag0 _ (by omega)
      dβ := by show m'' (D + 4) = m₀ (D + 4); exact ag0 _ (by omega)
      sS := rfl
      tv := rfl
      desc := by show ChainDescAt m'' D (Qof P) H C; exact hD''
      CQ := hCQ
      simple := hsimp
      hostLen := hHl
      hostWF := hHwf
      D_le := by show D + 5 ≤ E; omega
      host_le := by show m'' D + 3 * H.length + 4 ≤ E; rwo [ag0 _ (by omega)]
      s_lt := hCs
      nCB := by show m'' (NB + 3) = m₀ (NB + 3); exact ag0 _ (by omega)
      nAB := by show m'' (NB + 4) = m₀ (NB + 4); exact ag0 _ (by omega)
      nRB := by show m'' (NB + 5) = m₀ (NB + 5); exact ag0 _ (by omega)
      nSB := by show m'' (NB + 6) = m₀ (NB + 6); exact ag0 _ (by omega)
      nLB := by show m'' (NB + 7) = m₀ (NB + 7); exact ag0 _ (by omega)
      nf := by show NFAt m'' NB N; exact hNF''
      canon := by rwx [hh 2 (by norm_num)]
      hA := rfl
      hK := rfl
      regs := fun r hr => by
        have h1 : Robust A₀ m₀ fun m' => m' (m' (NB + 5) + (5 * r + 4)) = (N.region r).wt :=
          fun m' hm' => by
            have := ((hNFw m' hm').2.2.2.2.2.2.2.1 r hr).2.2.1
            simpa only [Nat.add_assoc] using this
        obtain ⟨h5, h54⟩ := NFLoc.robust_addr2 h1
        refine ⟨by show m₀ (NB + 5) + 5 * r + 4 < E; omega, fun t ht => ?_⟩
        show m₀ (NB + 7) + m'' (m₀ (NB + 5) + 5 * r + 1) + t < E
        rw [ag0 _ (by omega)]
        have := robust_addrF (E := A₀) (m := m₀)
          (f := fun m' => m' (NB + 7) + m' (m' (NB + 5) + 5 * r + 1) + t)
          (v := (N.region r).arcs.getD t 0)
          (fun m' hm' => by
            show m' (NB + 7) + m' (m' (NB + 5) + 5 * r + 1) + t =
              m₀ (NB + 7) + m₀ (m₀ (NB + 5) + 5 * r + 1) + t
            rw [hm' (NB + 7) (by omega), hm' (NB + 5) (by omega), hm' _ (by omega)])
          (fun m' hm' => ((hNFw m' hm').2.2.2.2.2.2.2.1 r hr).2.2.2.1 t ht)
        have h' : m₀ (NB + 7) + m₀ (m₀ (NB + 5) + 5 * r + 1) + t < A₀ := this
        omega
      pos := fun j hj => by
        rw [hVA] at hj
        show m'' (POS + j) < A ∧ N.seq.getD (m'' (POS + j)) 0 = j
        rw [agE _ (by omega)]; exact hpos j hj
      POS_le := by show POS + A ≤ E; omega
      gOK := hgok
      μ := hBN
      FL_le := by show FL + (A + 3) ≤ E; omega
      LAB_le := by show LAB + (A + 3) ≤ E; omega
      hlab := by
        have := (hcl.mono (m' := m'') (X := O) agE (by rwo [hBN]) (by rwo [hBN])).hlab
        exact this
      dl := (hord.mono (m' := m'') (X := O) agE hFL hLAB hDL hORD hRK).dl
      dl_all := (hord.mono (m' := m'') (X := O) agE hFL hLAB hDL hORD hRK).dl_all
      DL_le := by show DL + nD ≤ E; omega
      nD_le := by
        show nD ≤ 7 * k ^ 2
        rw [hord.nD_eq]
        have := hcl.card; rw [hBN] at this; exact this
      clus := fun l => by
        have := (hcl.mono (m' := m'') (X := O) agE (by rwo [hBN])
          (by rwo [hBN])).clus l
        rw [hBN] at this; exact this
      k_pos := hcl.k_pos
      μ_le := by have := hcl.μ_le; rw [hBN] at this; exact this
      μ_A := le_rfl
      k_min := by have := hcl.k_min; rw [hBN] at this; exact this
      ord_lt := (hord.mono (m' := m'') (X := O) agE hFL hLAB hDL hORD hRK).ord_lt
      ord_inj := (hord.mono (m' := m'') (X := O) agE hFL hLAB hDL hORD hRK).ord_inj
      ord_rk := (hord.mono (m' := m'') (X := O) agE hFL hLAB hDL hORD hRK).ord_rk
      ord_sorted := (hord.mono (m' := m'') (X := O) agE hFL hLAB hDL hORD hRK).ord_sorted
      ORD_le := by show ORD + (A + 3) ≤ E; omega
      RK_le := by show RK + (A + 3) ≤ E; omega
      ch_lt := fun q hq => by
        rw [hVK] at hq
        show m'' (CH + q) < K; rw [agE _ (by omega)]; exact hchlt q hq
      ch_inj := fun q q' hq hq' e => by
        rw [hVK] at hq hq'
        rw [hVCH] at e
        rw [agE _ (by omega), agE _ (by omega)] at e; exact hchinj q q' hq hq' e
      ch_sorted := fun q q' hqq hq' => by
        rw [hVK] at hq'
        show ChLe P C V m'' (m'' (CH + q)) (m'' (CH + q'))
        rw [agE _ (by omega), agE _ (by omega)]
        have hs := hchsort q q' hqq hq'
        have a1 := hchlt q (by omega)
        have a2 := hchlt q' hq'
        rw [chLe_V_congr (V' := V) hVc.1 hVc.2.1 hVc.2.2.1 hVc.2.2.2] at hs
        refine (chLe_congr fun x hx => ?_).1 hs
        have hxK : x < K := by rcases hx with rfl | rfl <;> assumption
        have := hcb x hxK
        exact ⟨(ag0 _ (by show m₀ (NB + 3) + 5 * x < A₀; omega)).symm,
          (ag0 _ (by show m₀ (NB + 3) + 5 * x + 1 < A₀; omega)).symm⟩
      tab := fun j hj => by
        rw [hVL] at hj
        show m'' (TB + j) = 2 ^ j; rw [agE _ (by omega)]; exact htab j hj
      A_lt := hAlt
      K_lt := hKlt
      L_le := by
        show L ≤ Nat.clog 2 (A + K) + 1
        rw [hL]; exact clog_succ_le _
      TB_le := by show TB + L ≤ E; omega
      CH_le := by show CH + K ≤ TB; omega
      NB_TB := by show NB + 12 ≤ TB; omega
      AB_TB := by show m₀ (NB + 4) + 5 * A ≤ TB; omega
      SB_TB := by show m₀ (NB + 6) + A ≤ TB; omega
      CB_TB := fun i hi => by have := hcb i hi; show m₀ (NB + 3) + 5 * i + 5 ≤ TB; omega
      md0 := by show m'' MD = 0; rwx [agE _ (by omega)]
      md := fun i hi => by
        show m'' (MD + 1 + i) = m'' (D + i)
        rw [agE _ (by omega), hmdc i hi, ag0 _ (by omega)]
      MD_le := by show MD + 6 ≤ E; omega }

end

end OracleR

end Chazelle.Core
