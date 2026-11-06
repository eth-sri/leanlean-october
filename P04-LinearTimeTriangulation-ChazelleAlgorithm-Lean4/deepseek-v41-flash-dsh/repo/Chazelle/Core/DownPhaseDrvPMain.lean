module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvPBuild
public import Chazelle.Core.DownPhaseDrvRPieceSpec
public import Chazelle.Core.BruteMain
public import Chazelle.Core.Granularize

/-!
# Down-phase pieces (D4): `DrvR.PieceSpec`

**`pieceSpec_of`**: from Lemma 4.1 (`Lemma41Spec O`), the procedure `pieceS` (descriptor part
`frontS`, chord list `listS`, build `buildS`, granularity enforcement `granS`; brute force,
`BuildNFSpec`, `GranularizeSpec` are the project's theorems `brute`, `buildNF`, `granularize`)
meets the contract `DrvR.PieceSpec O` of one piece of a region chain, with cost constant `κP`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace DrvP

open Machine Machine.Stmt Programs NFLoc SignK WalkKey
open BuildRegions (famOf)

@[expose] public section

/-- **The cost constant of a piece.** -/
def κP (κL κB κBd : ℕ) (κG : ℕ → ℕ) : ℕ :=
  141204 + κLst κL κB + 1950481 * κBd + 1950481 * κG 4 + 9

/-- The arithmetic of the cost of a piece. -/
theorem piece_cost (κL κB κBd κG4 μ X K : ℕ) (hX : μ + 1 ≤ X) (hK : K ≤ 1950480 * X) :
    (1204 * μ + 140000) + κLst κL κB * X + (κBd * (K + 1) + 4) + (κG4 * (K + 1) + 5) ≤
      (141204 + κLst κL κB + 1950481 * κBd + 1950481 * κG4 + 9) * X := by
  have e : (141204 + κLst κL κB + 1950481 * κBd + 1950481 * κG4 + 9) * X =
      141204 * X + κLst κL κB * X + κBd * (1950481 * X) + κG4 * (1950481 * X) + 9 * X := ⋆
  Ξ e
  have h1 : κBd * (K + 1) ≤ κBd * (1950481 * X) := Nat.mul_le_mul_left _ (⋄)
  have h2 : κG4 * (K + 1) ≤ κG4 * (1950481 * X) := Nat.mul_le_mul_left _ (⋄)
  have h3 : 141204 * (μ + 1) ≤ 141204 * X := Nat.mul_le_mul_left _ hX
  generalize κBd * (K + 1) = a at *
  generalize κBd * (1950481 * X) = b at *
  generalize κG4 * (K + 1) = a' at *
  generalize κG4 * (1950481 * X) = b' at *
  generalize κLst κL κB * X = d at *
  omega

/-- The model descriptor of a piece is robust. -/
theorem desc_robust {Q : Polygon} {H : Host} {C : Chain} {m₀ m : ℕ → ℕ} {A E HB : ℕ}
    (hH : Robust A m₀ (fun m' => HostAt m' HB H)) (hlow : ∀ a, a < A → m a = m₀ a)
    (hAE : A + 6 ≤ E) (hP : C.P = H.poly Q)
    (d0 : m A = 0) (d1 : m (A + 1) = HB) (d2 : m (A + 2) = C.s) (d3 : m (A + 3) = C.m)
    (d4 : m (A + 4) = C.topIdx) (d5 : m (A + 5) = 1 ↔ C.sideBeta = true) :
    Robust E m (fun m' => m' A = 0 ∧ ChainDescAt m' (A + 1) Q H C ∧ m' (A + 1) = HB) := by
  intro m' hm'
  have e0 : m' A = m A := hm' A (by omega)
  have e : ∀ i, 1 ≤ i → i < 6 → m' (A + i) = m (A + i) := fun i h1 hi => hm' _ (by omega)
  have e1 : m' (A + 1) = HB := by rw [e 1 (by norm_num) (by norm_num), d1]
  refine ⟨by rw [e0, d0], ⟨?_, hP, ?_, ?_, ?_, ?_⟩, e1⟩
  · rw [e1]; exact hH m' (fun a ha => (hm' a (by omega)).trans (hlow a ha))
  · rw [show A + 1 + 1 = A + 2 by ring, e 2 (by norm_num) (by norm_num), d2]
  · rw [show A + 1 + 2 = A + 3 by ring, e 3 (by norm_num) (by norm_num), d3]
  · rw [show A + 1 + 3 = A + 4 by ring, e 4 (by norm_num) (by norm_num), d4]
  · rw [show A + 1 + 4 = A + 5 by ring, e 5 (by norm_num) (by norm_num)]; exact d5

/-- The model descriptor of a piece is well formed. -/
theorem desc_wf {P : Polygon} {H : Host} {C : Chain} {m : ℕ → ℕ} {A E HB : ℕ}
    (hdesc : m A = 0 ∧ ChainDescAt m (A + 1) (Qof P) H C ∧ m (A + 1) = HB)
    (hAE : A + 6 ≤ E) (hHB : HB + 3 * H.length + 4 ≤ E) (hl : H.length ≤ 64)
    (hwf : HostWF P.n H) (hs : C.s < C.P.n) : ModelDescWF P E m A := by
  obtain ⟨h0, hd, h1⟩ := hdesc
  refine ⟨hAE, fun _ => ⟨⋄, fun H' C' hd' => ?_⟩⟩
  have hH' : H' = H := hostAt_unique hd'.1 hd.1
  subst hH'
  have hP : C'.P = C.P := Ρ hd'.2.1, hd.2.1
  have hs' : C'.s = C.s := Ρ ← hd'.2.2.1, hd.2.2.1
  refine ⟨hl, hwf, by rw [h1]; exact hHB, by rw [hs', hP]; exact hs⟩

theorem modelDescAt_of {Q : Polygon} {H : Host} {C : Chain} {m : ℕ → ℕ} {A HB : ℕ}
    (hdesc : m A = 0 ∧ ChainDescAt m (A + 1) Q H C ∧ m (A + 1) = HB) :
    ModelDescAt m A Q (chainModel C) :=
  Or.inl ⟨hdesc.1, H, C, hdesc.2.1, rfl⟩

theorem gradeCtx_frame {O : OracleIface} {P : Polygon} {m m' : ℕ → ℕ} {g A A' : ℕ}
    (h : (gradeCtx O).holds P m g A) (hm : ∀ a, a < A → m' a = m a) (hA : A ≤ A') :
    (gradeCtx O).holds P m' g A' :=
  (gradeCtx O).mono P m' g A A' hA ((gradeCtx O).local_ P m m' g A (fun a ha => (hm a ha).symm) h)


/-- **The pieces of a region chain (D4)**, from Lemma 4.1. -/
theorem pieceSpec_of {O : OracleIface} (hL : Lemma41Spec O) : DrvR.PieceSpec O := by
  classical
  obtain ⟨sL, κL, hLm⟩ := (lemma41Spec_iff O).1 hL
  obtain ⟨sB, κB, hBm⟩ := bruteSpec_iff.1 brute
  obtain ⟨sBd, κBd, hBdm⟩ := buildNFSpec_iff.1 buildNF
  obtain ⟨sG, κG, hGm⟩ := granularizeSpec_iff.1 granularize
  refine ⟨pieceS sL sB sBd sG, κP κL κB κBd κG, fun P W c hw hpre hroom => ?_⟩
  obtain ⟨hG, hW, hgr, hD4, hm1, hkind, H, hH, hHA, hl, hwf, hreg, hsimp, hsm, hleaf, hconn⟩ :=
    hpre
  obtain ⟨A, hA⟩ : ∃ A, c.nreg ALLOC = A := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ, c.nreg 218005 = μ := ⟨_, rfl⟩
  have hμX : μ + 1 ≤ lemma41Nat μ + 1 := by have := le_lemma41Nat μ; omega
  replace hroom : A + κP κL κB κBd κG * (lemma41Nat μ + 1) ≤ W := by
    rw [← hA, ← hμ]; exact hroom
  have hn : (Qof P).n = P.n := qof_n P
  have hNpts : (H.poly (Qof P)).n = (H.pts (Qof P).n).length := DownMath.host_poly_n _ _
  let CH : Chain := ⟨H.poly (Qof P), c.nreg 218001, c.nreg 218002, hm1, by rw [hNpts]; omega⟩
  have hCHP : CH.P = H.poly (Qof P) := rfl
  have hCHs : CH.s = c.nreg 218001 := rfl
  have hCHm : CH.m = c.nreg 218002 := rfl
  have hgh : c.nreg 218008 + 3 < A := by rw [← hA]; exact (ShootCut.grade_low hgr).1
  -- the leaf facts
  have hleaf' : ¬ c.nreg 218002 < 65 → c.nreg 218002 ≤ 2 ^ c.nreg 218005 ∧
      c.nreg 218005 ≤ c.nmem (c.nreg 218008) ∧ c.nreg 218004 + c.nreg 218002 + 1 ≤ (Qof P).n ∧
      ∀ k, k ≤ c.nreg 218002 →
        (H.pts (Qof P).n).getD (c.nreg 218001 + k) (.vtx 0) = .vtx (c.nreg 218004 + k) := by
    intro h65
    have hk1 : c.nreg 218003 = 1 := by
      by_contra hne
      have h0 : c.nreg 218003 = 0 := by omega
      have := (hconn h0).1; omega
    obtain ⟨a1, a2, a3, -, a5⟩ := hleaf hk1
    exact ⟨a1, a2, a3, a5⟩
  have hcost0 := piece_cost κL κB κBd (κG 4) μ (lemma41Nat μ + 1) 0 hμX (Nat.zero_le _)
  have hκP : κP κL κB κBd κG = 141204 + κLst κL κB + 1950481 * κBd + 1950481 * κG 4 + 9 := rfl
  rw [← hκP] at hcost0
  -- 1. the descriptor part
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, d10, d99, gin₁, gout₁, v20, v21, v22, ml₁, d0, d1, d2, d3, d4,
    d5⟩ := frontS_exec c hw hG hW hgr hm1 hH hHA hl hwf hsm hleaf'
      (by rw [hA, hμ]; generalize κLst κL κB * (lemma41Nat μ + 1) = d at hcost0
          generalize κP κL κB κBd κG * (lemma41Nat μ + 1) = e at hcost0 hroom
          omega) CH hCHP hCHs hCHm
  rw [hA] at d10 d99 ml₁ d0 d1 d2 d3 d4 d5
  rw [hμ] at hk₁
  have w₁ := e₁.wb_right
  have i₁ := gin₁
  -- 2. the chord list
  have hmem₁gh : c₁.nmem (c.nreg 218008) = c.nmem (c.nreg 218008) := ml₁ _ (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, gin₂, L, hCL, hK, hB, hok, hdeg, hwt, hKc⟩ :=
    listS_exec hLm hBm c₁ w₁ hG hW
      (by rw [i₁ _ (by norm_num) (by norm_num), d99]
          exact gradeCtx_frame (by rw [← hA]; exact hgr) (fun a ha => ml₁ a ha) (by omega))
      v21 v22 (by rw [i₁ _ (by norm_num) (by norm_num)]; exact hm1)
      (by rw [i₁ _ (by norm_num) (by norm_num)]; exact hkind)
      (fun hk => by
        simp only [i₁ _ (by norm_num : 218000 ≤ 218003) (by norm_num : 218003 < 218010),
          i₁ _ (by norm_num : 218000 ≤ 218002) (by norm_num : 218002 < 218010),
          i₁ _ (by norm_num : 218000 ≤ 218004) (by norm_num : 218004 < 218010),
          i₁ _ (by norm_num : 218000 ≤ 218005) (by norm_num : 218005 < 218010),
          i₁ _ (by norm_num : 218000 ≤ 218007) (by norm_num : 218007 < 218010),
          i₁ _ (by norm_num : 218000 ≤ 218008) (by norm_num : 218008 < 218010), hmem₁gh] at hk ⊢
        obtain ⟨a1, a2, a3, a4, -⟩ := hleaf hk
        exact ⟨a1, a2, by rw [hn] at a3; exact a3, a4⟩)
      (fun hk => by
        rw [i₁ _ (by norm_num) (by norm_num)] at hk
        rw [i₁ _ (by norm_num) (by norm_num), i₁ _ (by norm_num) (by norm_num)]
        exact hconn hk)
      CH hsimp (by rw [hCHm, i₁ _ (by norm_num) (by norm_num)])
      (fun hk CQ hQ hs hm => by
        rw [i₁ _ (by norm_num) (by norm_num)] at hk hs hm
        obtain ⟨-, -, a3, -, a5⟩ := hleaf hk
        rw [hn] at a3
        refine twin_leaf hQ hs (by rw [hm, hCHm]) hCHP (by rw [hCHs, hCHm, ← hn]; omega)
          (by rw [hCHm]; omega) (fun k hk' => ?_)
        rw [hCHs]; unfold pt; rw [← hn]; exact a5 k (by rw [hCHm] at hk'; exact hk'))
      (by rw [d99, i₁ _ (by norm_num) (by norm_num), hμ]
          generalize κLst κL κB * (lemma41Nat μ + 1) = d at hcost0 ⊢
          generalize κP κL κB κBd κG * (lemma41Nat μ + 1) = e at hcost0 hroom
          omega)
  rw [i₁ _ (by norm_num) (by norm_num), hμ] at hk₂ hKc
  rw [i₁ _ (by norm_num) (by norm_num)] at hwt
  have w₂ := e₂.wb_right
  -- the descriptor, robustly
  have hwf' : HostWF P.n H := by rw [← hn]; exact hwf
  have hR₁ : Robust (c₁.nreg ALLOC) c₁.nmem (fun m => m A = 0 ∧
      ChainDescAt m (A + 1) (Qof P) H CH ∧ m (A + 1) = c.nreg 218000) := by
    rw [d99]
    exact desc_robust (by rw [← hA]; exact hH) (fun a ha => ml₁ a ha) le_rfl hCHP d0 d1 d2 d3 d4 d5
  have hs_lt : CH.s < CH.P.n := by rw [hCHs, hCHP, hNpts]; omega
  have hA₂ : A + 6 ≤ c₂.nreg ALLOC := by rw [← d99]; exact F₂.2.2.2.2.2.1
  have hR₂ := hR₁.frame F₂
  have r10₂ : c₂.nreg 218010 = A := by
    rw [gin₂ _ (by decide) (by omega) (by omega), d10]
  have hcost := piece_cost κL κB κBd (κG 4) μ (lemma41Nat μ + 1)
    (L.length * (Nat.clog 2 L.length + 1)) hμX hKc
  rw [← hκP] at hcost
  have hk₂A : c₂.nreg ALLOC ≤ A + 6 + k₂ := by rw [← d99]; exact F₂.2.2.2.2.2.2
  -- 3. the build
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, gin₃, N₁, hN1, hN2, hN3, hN4⟩ := buildS_exec hBdm c₂ w₂ hG hW
    (by rw [r10₂]; exact desc_wf hR₂.holds hA₂ (by omega) hl hwf' hs_lt)
    (by rw [r10₂]; exact modelDescAt_of hR₂.holds) (Or.inl ⟨CH, hsimp, rfl⟩) hK hB hCL hok
    (by generalize κLst κL κB * (lemma41Nat μ + 1) = d at hcost hk₂
        generalize κP κL κB κBd κG * (lemma41Nat μ + 1) = e at hcost hroom
        generalize κBd * (L.length * (Nat.clog 2 L.length + 1) + 1) = f at hcost ⊢
        generalize κG 4 * (L.length * (Nat.clog 2 L.length + 1) + 1) = g at hcost
        omega)
  have w₃ := e₃.wb_right
  -- 4. the granularity enforcement
  have r10₃ : c₃.nreg 218010 = A := by rw [gin₃ _ (by decide) (by decide), r10₂]
  have r07₃ : c₃.nreg 218007 = c.nreg 218007 := by
    rw [gin₃ _ (by decide) (by decide), gin₂ _ (by decide) (by omega) (by omega),
      i₁ _ (by norm_num) (by norm_num)]
  have hR₃ := hR₂.frame F₃
  have hA₃ : A + 6 ≤ c₃.nreg ALLOC := hA₂.trans F₃.2.2.2.2.2.1
  have hk₃A := F₃.2.2.2.2.2.2
  have hlenN : N₁.chords.length = L.length := by rw [← hN4, List.length_map]
  have hFN : N₁.F (chainModel CH) (Qof P) = famOf (chainModel CH) (Qof P) L := BoxT.F_eq_famOf hN4
  obtain ⟨c₄, k₄, e₄, hk₄, F₄, gin₄, N₂, hM1, hM2, hcan⟩ := granS_exec hGm c₃ w₃ hG hW
    (by rw [r10₃]; exact desc_wf hR₃.holds hA₃ (by omega) hl hwf' hs_lt)
    (by rw [r10₃]; exact modelDescAt_of hR₃.holds) (Or.inl ⟨CH, hsimp, rfl⟩) hN2 hN3
    (by rw [hFN]; exact hdeg) (by rw [hFN, r07₃]; exact hwt)
    (by rw [hlenN]
        generalize κLst κL κB * (lemma41Nat μ + 1) = d at hcost hk₂
        generalize κP κL κB κBd κG * (lemma41Nat μ + 1) = e at hcost hroom
        generalize κBd * (L.length * (Nat.clog 2 L.length + 1) + 1) = f at hcost hk₃
        generalize κG 4 * (L.length * (Nat.clog 2 L.length + 1) + 1) = g at hcost ⊢
        omega)
  rw [hlenN] at hk₄
  rw [r07₃] at hcan
  have hR₄ := hR₃.frame F₄
  have hA₄ : A + 6 ≤ c₄.nreg ALLOC := hA₃.trans F₄.2.2.2.2.2.1
  have r10₄ : c₄.nreg 218010 = A := by rw [gin₄ _ (by decide) (by decide), r10₃]
  have ex : Exec P W (pieceS sL sB sBd sG) c c₄ (k₁ + (k₂ + (k₃ + k₄))) :=
    .seq e₁ (.seq e₂ (.seq e₃ e₄))
  have F := F₁.trans (F₂.trans (F₃.trans F₄))
  refine ⟨c₄, _, ex, ?_, ⟨fun q hq hq' => ?_, ?_, ?_, ?_, fun H' C' hH' hP' hs' hm' => ?_⟩,
    F.mono (by simp) le_rfl⟩
  · -- the cost
    show _ ≤ κP κL κB κBd κG * (lemma41Nat (c.nreg 218005) + 1)
    rw [hμ]
    generalize κLst κL κB * (lemma41Nat μ + 1) = d at hcost hk₂
    generalize κP κL κB κBd κG * (lemma41Nat μ + 1) = e at hcost hroom ⊢
    generalize κBd * (L.length * (Nat.clog 2 L.length + 1) + 1) = f at hcost hk₃
    generalize κG 4 * (L.length * (Nat.clog 2 L.length + 1) + 1) = g at hcost hk₄
    omega
  · -- the registers of the driver
    have hq21 : bandOf q = 21 := hq
    unfold bandOf at hq21
    rw [gin₄ q hq21 (by omega), gin₃ q hq21 (by omega), gin₂ q hq21 (by omega) (by omega),
      gout₁ q hq' (by omega) (by omega) (by omega) (by unfold ALLOC; omega)]
  · rw [r10₄, ← hA]
  · rw [hA]; exact le_trans (by omega) (le_trans hA₃ hM1)
  · rw [r10₄]; exact desc_wf hR₄.holds hA₄ (by omega) hl hwf' hs_lt
  · -- the descriptor and the normal form of the chain
    have hHH : H' = H := hostAt_unique hH' hH.holds
    subst hHH
    have hCC : C' = CH := chain_eq (by rw [hP', hCHP]) (by rw [hs', hCHs]) (by rw [hm', hCHm])
    subst hCC
    refine ⟨by rw [r10₄]; exact hR₄, N₂, hM2, canonical_cap hcan hD4⟩


end

end DrvP

end Chazelle.Core
