module

public import Chazelle.Core.FuseAsmMain
public import Chazelle.Rwx

/-!
# WP-F fusion assembly, part 29: the fusion specification

**`fuseSpec_of : SweepSpecH → BuildNFSpec → FuseSpec`** (`BuildNFSpec` is proved:
`Chazelle.Core.buildNF`).  The driver `fuseRun` (`fuseRun_exec`) produces the normal form of
`J.fusion S₁ S₂ ∪ glueChords J`; its degree bound is `FuseDeg.fusionDegSpec` and its weight
bound `FuseMath.fusionWeightSpec`.
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK

@[expose] public section

theorem nf_F_congr {M : Model} {Q : Polygon} {N N' : NF} (h : N.chords = N'.chords) :
    N.F M Q = N'.F M Q := by
  unfold NF.F; rw [h]

theorem nChords_congr {N N' : NF} (h : N.chords = N'.chords) : N.nChords = N'.nChords := by
  unfold NF.nChords; rw [h]

/-- **WP-F: the fusion.** -/
theorem fuseSpec_of (hS : SweepSpecH) (hBd : BuildNFSpec) : FuseSpec := by
  obtain ⟨mk, κs, hSw⟩ := sweep_meets hS
  obtain ⟨sB, κB, hBM⟩ := build_meets hBd
  obtain ⟨capF, hcapF⟩ := FuseDeg.fusionDegSpec
  refine ⟨fun sh => fuseRun (mk sh) sB, fuseκ κs κB, capF, ?_⟩
  intro sh Bs F X Ok hloc hBs hsh P W c hw hpre hroom
  obtain ⟨hG, hHW, hX, hcap, hJWF, H, J, N₁, N₂, hJ, hPs, hgen, hOk1, hOk2, hOkw, hN1, hN2,
    hi1, hi2, hd1, hd2, hs1, hs2⟩ := hpre
  have hF : FCtx P W J H N₁ N₂ (c.nreg ALLOC) c :=
    ⟨hG, hHW, hJ, hJWF, hPs, hgen, hN1, hN2, hi1, hi2, le_rfl⟩
  have hP : FPre P X Ok J N₁ N₂ c := ⟨hOk1, hOk2, hOkw, hd1, hd2, hs1, hs2, hX, hcap⟩
  have hK1  := hN1.nfAt.1
  have hK2  := hN2.nfAt.1
  beta_reduce at hroom
  rw [hK1, hK2] at hroom
  obtain ⟨c', k, N, ex, hk, Fr, hle, hNW, hIs, hNF, hNk⟩ :=
    fuseRun_exec (hSw sh Bs F X Ok hloc hBs hsh) hBM hloc c hw hF hP hroom
  refine ⟨c', k, ex, by beta_reduce; rwx [hK1, hK2], ?_, Fr⟩
  intro H' J' N₁' N₂' hJ' hA1 hA2
  have eJ  := junction_eq hJ hJ'
  subst eJ
  have e1 := chords_eq_of_nfAt hN1.nfAt hA1
  have e2 := chords_eq_of_nfAt hN2.nfAt hA2
  rw [← nf_F_congr e1, ← nf_F_congr e2, ← nChords_congr e1, ← nChords_congr e2]
  refine ⟨N, hle, hNW, hIs, hNF, hNk, ?_, ?_⟩
  · rw [hNF]
    exact hcapF J (Qof P) _ _ _ hPs hgen hi1.1 hi2.1 hd1 hd2
  · rw [hNF]
    exact FuseMath.fusionWeightSpec J (Qof P) _ _ _ hPs hgen hi1.1 hi2.1 hs1 hs2

end

end FuseAsm

end Chazelle.Core
