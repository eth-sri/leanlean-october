module

public import Chazelle.Core.MergeAsmMain
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 8000000

/-!
# WP-F merge assembly, part 7: `mergeSpec_of`

**Lemma 3.5** from the fusion, conformality restoration and granularity enforcement:
`mergeSpec_of : FuseSpec → RestoreSpec → GranularizeSpec → MergeSpec` (with Lemma 2.3,
`lemma23`, proved).  The program is `mergeMk` (`MergeAsmProg`); see `MergeAsmMain` for the plan.
-/

namespace Chazelle.Core

namespace MergeAsm

open Machine Machine.Stmt Programs SignK

@[expose] public section

theorem keepF {B : Finset ℕ} {c c' : Config} {k : ℕ} (hf : Frame B c c' k) (r : ℕ)
    (hr : bandOf r ∉ B) (hA : r ≠ ALLOC) : c'.nreg r = c.nreg r := hf.1 r hr hA

/-- **WP-F: Lemma 3.5.** -/
theorem mergeSpec_of (hF : FuseSpec) (hR : RestoreSpec) (hG : GranularizeSpec) : MergeSpec := by
  obtain ⟨fMk, κF, capF, hFu⟩ := hF
  obtain ⟨rMk, κR, cR, hRe⟩ := hR
  obtain ⟨gS, κG, hGr⟩ := hG
  obtain ⟨c23, h23⟩ := lemma23
  refine ⟨mergeMk fMk rMk gS, κM κF capF κR cR κG c23, ?_⟩
  intro sh cu Bs Bc F G H X Ok hloc hhalf hOkM hFm hGm hHm hBs hBc hsh hcu
  have hFuse := hFu sh Bs F X Ok hloc hBs hsh
  have hRes := hRe sh cu Bs Bc F G H X Ok hloc hhalf hOkM hBs hBc hsh hcu
  intro P W c hw hpre hroom
  obtain ⟨hGE, hWh, hX, hcap, hD4, hγ, hJWF, Hs, J, N₁, N₂, hJ, hPs, hSG, hOk1, hOk2,
    hOkw, hFull, hN1, hN2, ⟨γ₁, hγ₁, hc1⟩, ⟨γ₂, hγ₂, hc2⟩⟩ := hpre
  simp [fuseLoss] at hcap hγ hroom
  -- names
  obtain ⟨γ₀, hγ₀⟩ : ∃ x, rd c bMerge 5 = x := ⟨_, rfl⟩
  obtain ⟨γt, hγt⟩ : ∃ x, rd c bMerge 6 = x := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ x, rd c bMerge 7 = x := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ x, rd c bMerge 9 = x := ⟨_, rfl⟩
  obtain ⟨bw, hbw⟩ : ∃ x, rd c bMerge 2 = x := ⟨_, rfl⟩
  obtain ⟨A0, hA0⟩ : ∃ x, c.nreg ALLOC = x := ⟨_, rfl⟩
  rw [hγ₀] at hcap hγ hγ₁ hγ₂ hroom
  rw [hγt] at hγ
  rw [hD] at hD4 hFull hc1 hc2 hroom
  rw [hg, hA0] at hX
  rw [hg] at hcap
  rw [hbw] at hJ hJWF hroom
  have hK1 : c.nmem (rd c bMerge 3) = N₁.nChords := hN1.nfAt.1
  have hK2 : c.nmem (rd c bMerge 4) = N₂.nChords := hN2.nfAt.1
  have hm : c.nmem (bw + 2) = J.whole.m := hJ.2.2.2.2.2.1
  rw [hK1, hK2, hm] at hroom
  have hwfw : ChainWF P A0 c.nmem bw := by rw [← hA0]; exact hJWF.2.2.1
  have hbA : bw + 5 ≤ A0 := hwfw.1
  have hmn := chain_m_le hwfw hJ.2.2
  have hγtW : γt ≤ W := hγt ▸ hw.1 _
  have hgW : g ≤ W := hg ▸ hw.1 _
  have hA0W : A0 ≤ W := hA0 ▸ hw.1 _
  have hnW : 128 * P.n + 3 ≤ W := by ufo hostWords at hWh
  -- Lemma 2.3 and the oracle costs
  have hK1b := nChords_le_canonical h23 (C := J.left) hPs hc1
  have hK2b := nChords_le_canonical h23 (C := J.right) hPs hc2
  set β := βf c23 D with hβ
  set m := J.whole.m with hmdef
  set S := N₁.nChords + N₂.nChords + 1 with hSdef
  have hS : S ≤ β * (m + 1) := by
    have := S_le hK1b hK2b
    simp [Merge.Junction.left_m, Merge.Junction.right_m] at this
    rw [hβ, hmdef, Merge.Junction.whole_m]; unfold βf; exact this
  have hregW : HostRegular (Qof P).n Hs := by
    rw [show (Qof P).n = P.n from shear_n _ _]; exact hJWF.2.2.2 Hs hJ.2.2.1
  obtain ⟨hF1, hG1⟩ := oracle_pos_merge hloc hsh hcu hw hGE hWh (hA0 ▸ hX)
    hcap (by omega) (by omega) hgW (hA0 ▸ hwfw) hJ.2.2 hPs hOkw hregW
  set Fq := F (γ₀ + 1)
  set Gq := G (γ₀ + 1)
  set Hq := H (γ₀ + 1)
  set L := Nat.clog 2 (m + 1)
  set Y := Fq * Gq * (Hq + L + 1) with hY
  have hY1 : 1 ≤ Y := by
    have : 1 * 1 * 1 ≤ Fq * Gq * (Hq + L + 1) := by gcongr; omega
    omega
  set kr := supTo (fun d => κR d D) (capF D)
  set cr := supTo (fun d => cR d D) (capF D)
  set PF := κF D * (β + 2) * S * Y
  set PR := 8 * (β + 7) * kr * S * Y
  set PG := κG D * (8 * cr * (8 * cr * β + 1) + 1) * S * Y
  set SY := S * Y with hSYdef
  have hT : κM κF capF κR cR κG c23 D * S * Fq * Gq * (Hq + L + 1) =
      PF + PR + PG + 123 * SY := by
    sir only [κM, PF, PR, PG, hY, kr, cr, hβ, hSYdef]
  rw [hT] at hroom
  have hSY : S ≤ SY := Nat.le_mul_of_pos_right _ hY1
  -- 1. the arguments of the fusion
  obtain ⟨c1, k1, e1, hk1, f0, f1, f2, f3, f4, f5, f6, f8, fr1⟩ := setF_exec (P := P) c hw
  have F1 : Frame MB c c1 k1 := frame_band fr1 (by decide) (by decide) k1
  have m1 : c1.nmem = c.nmem := fr1.2.2.1
  have a1 : c1.nreg ALLOC = A0 := by rw [← hA0]; exact fr1.1 ALLOC (by decide)
  -- 2. the fusion
  have hpreF : GoodEnv P ∧ hostWords P.n ≤ W ∧
      X.holds P c1.nmem (rd c1 bFuse 8) (c1.nreg ALLOC) ∧
      rd c1 bFuse 5 ≤ X.cap P c1.nmem (rd c1 bFuse 8) ∧
      JunctionWF P (c1.nreg ALLOC) c1.nmem (rd c1 bFuse 0) (rd c1 bFuse 1) (rd c1 bFuse 2) ∧
      ∃ H J N₁ N₂, JunctionAt c1.nmem (rd c1 bFuse 0) (rd c1 bFuse 1) (rd c1 bFuse 2) (Qof P) H J ∧
        J.P.Simple ∧ SharedGeneric J ∧
        Ok P (chainModel J.left) ∧ Ok P (chainModel J.right) ∧ Ok P (chainModel J.whole) ∧
        NFWithin c1.nmem (rd c1 bFuse 3) (c1.nreg ALLOC) N₁ ∧
        NFWithin c1.nmem (rd c1 bFuse 4) (c1.nreg ALLOC) N₂ ∧
        IsNF (chainModel J.left) (Qof P) N₁ ∧ IsNF (chainModel J.right) (Qof P) N₂ ∧
        (chainModel J.left).DegLe (N₁.F (chainModel J.left) (Qof P)) (rd c1 bFuse 6) ∧
        (chainModel J.right).DegLe (N₂.F (chainModel J.right) (Qof P)) (rd c1 bFuse 6) ∧
        (chainModel J.left).Semigranular (N₁.F (chainModel J.left) (Qof P)) (rd c1 bFuse 5) ∧
        (chainModel J.right).Semigranular (N₂.F (chainModel J.right) (Qof P)) (rd c1 bFuse 5) := by
    rw [m1, a1, f0, f1, f2, f3, f4, f5, f6, f8, hγ₀, hD, hg, hbw]
    refine ⟨hGE, hWh, hX, by omega, ?_, Hs, J, N₁, N₂, hJ, hPs, hSG, hOk1, hOk2, hOkw,
      hA0 ▸ hN1, hA0 ▸ hN2, hc1.1, hc2.1, hc1.2.1, hc2.2.1,
      hc1.2.2.1.semigranular_of_le _ hγ₁, hc2.2.2.1.semigranular_of_le _ hγ₂⟩
    rwx [← hA0]
  have hcostF : κF (rd c1 bFuse 6) * (c1.nmem (rd c1 bFuse 3) + c1.nmem (rd c1 bFuse 4) + 1) *
      (F (rd c1 bFuse 5) + Nat.clog 2 (c1.nmem (rd c1 bFuse 3) + c1.nmem (rd c1 bFuse 4) + 1) + 1)
      ≤ PF := by
    rw [m1, f3, f4, f5, f6, hK1, hK2, hγ₀, hD]
    exact fuse_le hS (hFm (by omega)) hF1 hG1
  obtain ⟨c2, k2, e2, hk2, postF, frF⟩ := hFuse P W c1 e1.wb_right hpreF (by
    rw [a1]; beta_reduce; omega)
  have hk2' : k2 ≤ PF := hk2.trans hcostF
  have F2 : Frame MB c1 c2 k2 := frF.mono (by decide) le_rfl
  obtain ⟨Nf, hNfA, hNfW, hNf, -, hNfK, hNfD, hNfS⟩ := postF Hs J N₁ N₂
    (by rwx [m1, f0, f1, f2, hbw]) (by rw [m1, f3]; exact hN1.nfAt)
    (by rw [m1, f4]; exact hN2.nfAt)
  rw [f6, hD] at hNfD
  rw [f5, hγ₀] at hNfS
  simp [fuseLoss] at hNfS
  have hKf : Nf.nChords + 1 ≤ 8 * S := by rwo [hSdef]
  set Hf := rd c2 bFuse 7 with hHf
  -- 3. the model descriptor
  have a2 : A0 ≤ c2.nreg ALLOC := by rw [← a1]; exact frF.2.2.2.2.2.1
  have a2' : c2.nreg ALLOC ≤ A0 + k2 := by rw [← a1]; exact frF.2.2.2.2.2.2
  have r2 : ∀ r, bandOf r = bMerge → c2.nreg r = c.nreg r := fun r hr => by
    rw [keepF frF r (by rwd [hr]) (by intro h; rw [h] at hr; exact absurd hr (by decide)),
      fr1.1 r (by sid [inBand, hr])]
  have mem2 : ∀ a, a < A0 → c2.nmem a = c.nmem a := fun a ha => by
    rw [frF.2.2.1 a (by rwx [a1]), m1]
  obtain ⟨A, hA⟩ : ∃ x, c2.nreg ALLOC = x := ⟨_, rfl⟩
  obtain ⟨c3, k3, e3, hk3, v10, a3, v20, v21, h3A, h3c, m3, r3, rr3, rm3, o3⟩ :=
    descS_exec (P := P) c2 e2.wb_right hA (bw := bw) ((r2 _ (by decide)).trans hbw)
      (by omega) (by omega)
  have F3 : Frame MB c2 c3 k3 := hk3 ▸ descS_frame hA a3 m3 r3 rr3 rm3 o3
  have mem3 : ∀ a, a < A0 → c3.nmem a = c.nmem a := fun a ha => by
    rw [m3 a (Or.inl (by omega)), mem2 a ha]
  -- the fused normal form at `c3`
  have hNf3 : NFWithin c3.nmem Hf (c3.nreg ALLOC) Nf := hNfW.frame F3
  have hH3 : rd c3 bFuse 7 = Hf := r3 _ (Or.inl (by decide)) (by decide)
  obtain ⟨hHb, -, hRb, -, -, -⟩ := Gran.nf_areas hNf3
  have hRn : Nf.nRegions = Nf.nChords + 1 :=
    Gran.nRegions_eq hNf (walkAx_of_goodModel (Or.inl ⟨J.whole, hPs, rfl⟩))
  have hR0 := hRb 0 (by omega)
  have hRl := hRb (Nf.nRegions - 1) (by omega)
  -- 4. the maximum-degree loop
  obtain ⟨c4, k4, e4, hk4, v34, v31, v30, v32, m4, r4, fr4⟩ := mdInit_exec (P := P) c3
    e3.wb_right hH3 (by omega) (by omega)
  have hNfA3 := hNf3.nfAt
  have hR : c3.nmem (Hf + 2) = Nf.nRegions := hNfA3.2.2.1
  have hlens := lens_of_degLe hNf hNfD
  obtain ⟨c5, k5, e5, hk5, hall, hcap5, m5, r5⟩ := mdLoop_exec (P := P)
    (base := c3.nmem (Hf + 5) + 2) (R := Nf.nRegions) (Cap := capF D)
    (L := fun r => (Nf.region r).chords.length) (by omega) (by omega) hlens Nf.nRegions c4
    e4.wb_right (by rwx [r4 _ (by decide)]) (by rwx [r4 _ (by decide)])
    (by rw [v34, hR]) (fun r hr => by
      rw [m4, show c3.nmem (Hf + 5) + 2 + 5 * r = c3.nmem (Hf + 5) + 5 * r + 2 by ring]
      exact (hNfA3.2.2.2.2.2.2.2.1 r hr).2.1) (by rwo [v30]) (by simp [v31, v30, Nat.mul_zero, Nat.add_zero])
    (by rwo [v32]) (fun r hr => by rwo [v30] at hr)
  have fr5 := exec_frameB e5 wr_mdLoop
  obtain ⟨d₀, hd₀⟩ : ∃ x, c5.nreg 100032 = x := ⟨_, rfl⟩
  rw [hd₀] at hall hcap5
  have hDeg0 : (chainModel J.whole).DegLe (Nf.F (chainModel J.whole) (Qof P)) d₀ :=
    degLe_of_lens hNf hall
  -- 5. `γ_R`
  have r45 : ∀ r, bandOf r ≠ bMerge → c5.nreg r = c3.nreg r := fun r hr => by
    rw [fr5.1 r (by simp [inBand, hr]), fr4.1 r (by simp [inBand, hr])]
  have r35 : ∀ r, r < 100030 → c5.nreg r = c3.nreg r := fun r hr => by
    rw [r5 r (by omega) (by omega) (by omega) (by omega), r4 r hr]
  have mem5 : c5.nmem = c3.nmem := by rw [m5, m4]
  have hmW : 2 * m ≤ W := by omega
  obtain ⟨c6, k6, e6, hk6, v45, fr6, r6⟩ := gamS_exec (P := P) c5 e5.wb_right
    (by rwx [r35 _ (by decide)])
    (by show c5.nreg 100005 = γ₀; rw [r35 _ (by decide), r3 _ (Or.inl (by decide)) (by decide),
      r2 _ (by decide)]; exact hγ₀)
    (by show c5.nmem (c5.nreg 100002 + 2) = m
        rw [r35 _ (by decide), r3 _ (Or.inl (by decide)) (by decide), r2 _ (by decide), mem5,
          show c.nreg 100002 = bw from hbw, mem3 _ (by omega)]; exact hm)
    (by omega) hmW
    (by show c5.nreg 100002 + 2 ≤ W
        rw [r35 _ (by decide), r3 _ (Or.inl (by decide)) (by decide), r2 _ (by decide),
          show c.nreg 100002 = bw from hbw]; omega)
  set γR := min γ₀ (2 * m) + 1 with hγR
  have r56 : ∀ r, r < 100030 → c6.nreg r = c3.nreg r := fun r hr => by
    rw [r6 r (by omega)]; exact r35 r hr
  -- 6. restoration
  obtain ⟨c7, k7, e7, hk7, s0, s1, s2, s3, s4, s6, fr7⟩ := setR_exec (P := P) c6 e6.wb_right
  have r3c : ∀ r, bandOf r = bMerge → r < 100010 → c3.nreg r = c.nreg r := fun r hr hr' => by
    rw [r3 r (Or.inl hr') (by intro h; rw [h] at hr; exact absurd hr (by decide)), r2 r hr]
  rw [r56 _ (by decide), v10] at s0
  rw [show rd c6 bFuse 7 = c6.nreg 70007 from rfl, r56 _ (by decide),
    show c3.nreg 70007 = rd c3 bFuse 7 from rfl, hH3] at s1
  rw [r6 _ (by decide), hd₀] at s2
  rw [show rd c6 bMerge 7 = c6.nreg 100007 from rfl, r56 _ (by decide),
    r3c _ (by decide) (by decide), show c.nreg 100007 = rd c bMerge 7 from rfl, hD] at s3
  rw [v45] at s4
  rw [show rd c6 bMerge 9 = c6.nreg 100009 from rfl, r56 _ (by decide),
    r3c _ (by decide) (by decide), show c.nreg 100009 = rd c bMerge 9 from rfl, hg] at s6
  have F4 : Frame MB c3 c4 k4 := frame_band fr4 (by decide) (by decide) k4
  have F5 : Frame MB c4 c5 k5 := frame_band fr5 (by decide) (by decide) k5
  have F6 : Frame MB c5 c6 k6 := frame_band fr6 (by decide) (by decide) k6
  have F7 : Frame MB c6 c7 k7 := frame_band fr7 (by decide) (by decide) k7
  have mem7 : c7.nmem = c3.nmem := by rw [fr7.2.2.1, fr6.2.2.1, mem5]
  have a7 : c7.nreg ALLOC = A + 6 := by
    rw [fr7.1 ALLOC (by decide), fr6.1 ALLOC (by decide), fr5.1 ALLOC (by decide),
      fr4.1 ALLOC (by decide), a3]
  have Fc7 : Frame MB c c7 (k1 + (k2 + (k3 + (k4 + (k5 + (k6 + k7)))))) :=
    ftr F1 (ftr F2 (ftr F3 (ftr F4 (ftr F5 (ftr F6 F7)))))
  have hX0 : X.holds P c.nmem g (c.nreg ALLOC) := by rwx [hA0]
  have hold7 := holds_frame hX0 Fc7
  have cap7 := cap_frame hloc hX0 Fc7
  have mem7c : ∀ a, a < A0 → c7.nmem a = c.nmem a := fun a ha => by rw [mem7]; exact mem3 a ha
  have hcopy7 : ∀ j, j < 5 → c7.nmem (A + 1 + j) = c.nmem (bw + j) := fun j hj => by
    rw [mem7, h3c j hj, mem2 _ (by omega)]
  obtain ⟨hMD7, hMWF7⟩ := modelDesc_copy hwfw hJ.2.2 (by omega) mem7c (by rwx [mem7])
    hcopy7 (E' := c7.nreg ALLOC) (by omega)
  have hNf7 : NFWithin c7.nmem Hf (c7.nreg ALLOC) Nf := hNf3.frame (ftr F4 (ftr F5 (ftr F6 F7)))
  have hKf7 : c7.nmem Hf = Nf.nChords := hNf7.nfAt.1
  have hγRle : γR ≤ γ₀ + 1 := by rw [hγR]; have := min_le_left γ₀ (2 * m); omega
  have hγRm : γR ≤ 8 * (m + 1) := by rw [hγR]; have := min_le_right γ₀ (2 * m); omega
  have hpreR : GoodEnv P ∧ hostWords P.n ≤ W ∧
      X.holds P c7.nmem (rd c7 bRestore 6) (c7.nreg ALLOC) ∧
      rd c7 bRestore 4 ≤ X.cap P c7.nmem (rd c7 bRestore 6) ∧ 4 ≤ rd c7 bRestore 3 ∧
      ModelDescWF P (c7.nreg ALLOC) c7.nmem (rd c7 bRestore 0) ∧
      (c7.nmem (rd c7 bRestore 0) = 0 → ∀ H C,
        ChainDescAt c7.nmem (rd c7 bRestore 0 + 1) (Qof P) H C → HostRegular (Qof P).n H) ∧
      (c7.nmem (rd c7 bRestore 0) = 0 → ∀ H C,
        ChainDescAt c7.nmem (rd c7 bRestore 0 + 1) (Qof P) H C → C.P.Simple) ∧
      ∃ M N, ModelDescAt c7.nmem (rd c7 bRestore 0) (Qof P) M ∧ GoodModel M ∧ Ok P M ∧
        M.FullDegLe (Qof P) (rd c7 bRestore 3) ∧
        NFWithin c7.nmem (rd c7 bRestore 1) (c7.nreg ALLOC) N ∧ IsNF M (Qof P) N ∧
        M.DegLe (N.F M (Qof P)) (rd c7 bRestore 2) ∧
        M.Semigranular (N.F M (Qof P)) (rd c7 bRestore 4) := by
    rw [s0, s1, s2, s3, s4, s6, cap7]
    refine ⟨hGE, hWh, hold7, by omega, hD4, hMWF7, fun _ H' C' h' => ?_, fun _ H' C' h' => ?_,
      chainModel J.whole, Nf,
      hMD7,
      Or.inl ⟨J.whole, hPs, rfl⟩, hOkw, hFull, hNf7, hNf, hDeg0,
      semigranular_min_chain' hNfS⟩
    obtain ⟨-, -, hEb, -⟩ := hwfw.2 Hs J.whole hJ.2.2
    have hCd7 := chainDescAt_copy hJ.2.2 hEb mem7c hcopy7
    · rwx [NFLoc.hostAt_unique h'.1 hCd7.1]
    · obtain ⟨-, -, hEb, -⟩ := hwfw.2 Hs J.whole hJ.2.2
      have hCd7 := chainDescAt_copy hJ.2.2 hEb mem7c hcopy7
      rwx [h'.2.1, NFLoc.hostAt_unique h'.1 hCd7.1, ← hCd7.2.1]
  have hcostR : κR (rd c7 bRestore 2) (rd c7 bRestore 3) * (c7.nmem (rd c7 bRestore 1) + 1) *
      F (rd c7 bRestore 4) * G (rd c7 bRestore 4) *
      (H (rd c7 bRestore 4) + Nat.clog 2 (rd c7 bRestore 4) +
        Nat.clog 2 (c7.nmem (rd c7 bRestore 1) + 1) + 1) ≤ PR := by
    rw [s1, s2, s3, s4, hKf7]
    refine (restore_le hS hKf hγRm (hFm hγRle) (hGm hγRle) (hHm hγRle)).trans ?_
    have : κR d₀ D ≤ kr := le_supTo (f := fun d => κR d D) hcap5
    show 8 * (β + 7) * κR d₀ D * S * Y ≤ 8 * (β + 7) * kr * S * Y
    gcongr
  obtain ⟨c8, k8, e8, hk8, postR, frR⟩ := hRes P W c7 e7.wb_right hpreR (by
    rw [a7]; beta_reduce; have := hcostR; omega)
  have hk8' : k8 ≤ PR := hk8.trans hcostR
  have F8 : Frame MB c7 c8 k8 := frR.mono (by decide) le_rfl
  obtain ⟨Nr, -, hNrW, hNr, -, hNrD, hNrS, hNrK⟩ := postR (chainModel J.whole) Nf
    (by rwx [s0]) (by rw [s1]; exact hNf7.nfAt)
  rw [s3] at hNrD
  rw [s4] at hNrS
  rw [s2, s3] at hNrK
  -- 7. the arguments of granularity enforcement
  obtain ⟨c9, k9, e9, hk9, g0, g1, g2, g3, fr9⟩ := setG_exec (P := P) c8 e8.wb_right
  have r78 : ∀ r, bandOf r = bMerge → c8.nreg r = c7.nreg r := fun r hr =>
    keepF frR r (by rwd [hr]) (by intro h; rw [h] at hr; exact absurd hr (by decide))
  have r7 : ∀ r, bandOf r = bMerge → r < 100030 → c7.nreg r = c3.nreg r := fun r hr hr' => by
    rw [fr7.1 r (by sid [inBand, hr]), r56 r hr']
  rw [r78 _ (by decide), r7 _ (by decide) (by decide), v10] at g0
  rw [show rd c8 bMerge 7 = c8.nreg 100007 from rfl, r78 _ (by decide),
    r7 _ (by decide) (by decide), r3c _ (by decide) (by decide),
    show c.nreg 100007 = rd c bMerge 7 from rfl, hD] at g2
  rw [show rd c8 bMerge 6 = c8.nreg 100006 from rfl, r78 _ (by decide),
    r7 _ (by decide) (by decide), r3c _ (by decide) (by decide),
    show c.nreg 100006 = rd c bMerge 6 from rfl, hγt] at g3
  have F9 : Frame MB c8 c9 k9 := frame_band fr9 (by decide) (by decide) k9
  have mem9 : c9.nmem = c8.nmem := fr9.2.2.1
  have a9 : c9.nreg ALLOC = c8.nreg ALLOC := fr9.1 ALLOC (by decide)
  have a8 : c8.nreg ALLOC ≤ c7.nreg ALLOC + k8 := frR.2.2.2.2.2.2
  have he79 : ∀ a, a < c7.nreg ALLOC → c9.nmem a = c7.nmem a := fun a ha => by
    rw [mem9]; exact frR.2.2.1 a ha
  obtain ⟨-, hwhbound, -⟩ := hwfw.2 Hs J.whole hJ.2.2
  have hdesc7 : ∀ (H' : Host) (C' : Chain), ChainDescAt c.nmem bw (Qof P) H' C' →
      ChainDescAt c7.nmem (A + 1) (Qof P) H' C' := fun H' C' hC' => by
    obtain ⟨-, -, hb', -⟩ := hwfw.2 H' C' hC'
    exact chainDescAt_copy hC' (by omega) mem7c hcopy7
  obtain ⟨hMD9, hMWF9, -, -⟩ := modelDesc_agree hMWF7 (by rwx [mem7])
    (hdesc7 Hs J.whole hJ.2.2) he79
  have hNr9 : NFWithin c9.nmem (rd c8 bRestore 5) (c9.nreg ALLOC) Nr := hNrW.frame F9
  have hKr9 : c9.nmem (rd c8 bRestore 5) = Nr.nChords := hNr9.nfAt.1
  have hpreG : GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c9 bGran 2 ∧
      ModelDescWF P (c9.nreg ALLOC) c9.nmem (rd c9 bGran 0) ∧
      ∃ M N, ModelDescAt c9.nmem (rd c9 bGran 0) (Qof P) M ∧ GoodModel M ∧
        NFWithin c9.nmem (rd c9 bGran 1) (c9.nreg ALLOC) N ∧ IsNF M (Qof P) N ∧
        M.DegLe (N.F M (Qof P)) (rd c9 bGran 2) ∧
        M.Semigranular (N.F M (Qof P)) (rd c9 bGran 3) := by
    rw [g0, g1, g2, g3]
    exact ⟨hGE, hWh, by omega, hMWF9.mono (by rw [a9]; exact frR.2.2.2.2.2.1), chainModel J.whole,
      Nr, hMD9, Or.inl ⟨J.whole, hPs, rfl⟩, hNr9, hNr, hNrD,
      hNrS.mono _ (by omega)⟩
  have hcostG : κG (rd c9 bGran 2) *
      (c9.nmem (rd c9 bGran 1) * (Nat.clog 2 (c9.nmem (rd c9 bGran 1)) + 1) + 1) ≤ PG := by
    rw [g1, g2, hKr9]
    refine gran_le (c := cr) hS ?_ hF1 hG1 (by omega)
    have : cR d₀ D ≤ cr := le_supTo (f := fun d => cR d D) hcap5
    calc Nr.nChords ≤ cR d₀ D * (Nf.nChords + 1) := hNrK
      _ ≤ cr * (8 * S) := Nat.mul_le_mul this hKf
      _ = 8 * cr * S := by ring
  obtain ⟨c10, k10, e10, hk10, postG, frG⟩ := hGr P W c9 e9.wb_right hpreG (by
    rw [a9]; beta_reduce; have := hcostG; omega)
  have hk10' : k10 ≤ PG := hk10.trans hcostG
  have F10 : Frame MB c9 c10 k10 := frG.mono (by decide) le_rfl
  -- 8. the output
  obtain ⟨c11, k11, e11, hk11, o8, fr11⟩ := outS_exec (P := P) c10 e10.wb_right
  have F11 : Frame MB c10 c11 k11 :=
    NFLoc.frame_of_frameB fr11 (fun r hr => by
      simp [beq_iff_eq] at hr; subst hr; exact ⟨by decide, by decide⟩) k11
  have ex : Exec P W (mergeMk fMk rMk gS sh cu) c c11
      (k1 + (k2 + (k3 + (k4 + (k5 + (k6 + (k7 + (k8 + (k9 + (k10 + k11)))))))))) :=
    .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 (.seq e7 (.seq e8 (.seq e9
      (.seq e10 e11)))))))))
  have Fall : Frame MB c c11
      (k1 + (k2 + (k3 + (k4 + (k5 + (k6 + (k7 + (k8 + (k9 + (k10 + k11)))))))))) :=
    ftr F1 (ftr F2 (ftr F3 (ftr F4 (ftr F5 (ftr F6 (ftr F7 (ftr F8 (ftr F9 (ftr F10 F11)))))))))
  refine ⟨c11, _, ex, ?_, ?_, Fall⟩
  · -- the cost
    show _ ≤ κM κF capF κR cR κG c23 (rd c bMerge 7) *
      (c.nmem (rd c bMerge 3) + c.nmem (rd c bMerge 4) + 1) * F (rd c bMerge 5 + fuseLoss) *
        G (rd c bMerge 5 + fuseLoss) *
        (H (rd c bMerge 5 + fuseLoss) + Nat.clog 2 (c.nmem (rd c bMerge 2 + 2) + 1) + 1)
    rw [hD, hK1, hK2, hγ₀, hbw, hm]
    show _ ≤ κM κF capF κR cR κG c23 D * S * Fq * Gq * (Hq + L + 1)
    rw [hT]
    have h5 : k5 ≤ 56 * S + 2 := by omega
    omega
  · -- the postcondition
    intro Hs' J' N₁' N₂' hJ' hN1' hN2'
    rw [hbw] at hJ'
    obtain ⟨Nf', -, hNfW', -, -, -, -, -⟩ := postF Hs' J' N₁' N₂'
      (by rwx [m1, f0, f1, f2, hbw]) (by rwx [m1, f3])
      (by rwx [m1, f4])
    have hNf7' : NFWithin c7.nmem Hf (c7.nreg ALLOC) Nf' :=
      hNfW'.frame (ftr F3 (ftr F4 (ftr F5 (ftr F6 F7))))
    obtain ⟨hMD7', -⟩ := modelDesc_copy hwfw hJ'.2.2 (by omega) mem7c
      (by rwx [mem7]) hcopy7 (E' := c7.nreg ALLOC) (by omega)
    obtain ⟨Nr', -, hNrW', -⟩ := postR (chainModel J'.whole) Nf' (by rwx [s0])
      (by rw [s1]; exact hNf7'.nfAt)
    obtain ⟨hMD9', -, -, -⟩ := modelDesc_agree hMWF7 (by rwx [mem7])
      (hdesc7 Hs' J'.whole hJ'.2.2) he79
    obtain ⟨N'', hN''A, hN''W, -, hN''⟩ := postG (chainModel J'.whole) Nr' (by rwx [g0])
      (by rw [g1, mem9]; exact hNrW'.nfAt)
    rw [g2, g3] at hN''
    have a10 : c9.nreg ALLOC ≤ c10.nreg ALLOC := frG.2.2.2.2.2.1
    have a11 : c11.nreg ALLOC = c10.nreg ALLOC := fr11.1 ALLOC (by decide)
    have c9A : c.nreg ALLOC ≤ c9.nreg ALLOC := by
      have := (ftr F1 (ftr F2 (ftr F3 (ftr F4 (ftr F5 (ftr F6 (ftr F7 (ftr F8 F9)))))))).2.2.2.2.2.1
      exact this
    refine ⟨N'', ?_, ?_, by rwx [hγt, hD]⟩
    · rwo [o8]
    · rwx [o8, fr11.2.2.1, a11]

end

end MergeAsm

end Chazelle.Core
