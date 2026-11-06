import RequestProject.GenusControlledCapFillings
import RequestProject.PositiveCornerChainExtraction
import RequestProject.GenusControlledFillingComparison
import RequestProject.Tac
noncomputable section


/-! Cap coefficients of actual capped-cover cycles bound on the actual genus surface. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open Comb
variable (q : ℕ) [NeZero q]

theorem cornerSurfaceChain2_oldToFullCube
    c :
    cornerSurfaceChain2 (cmpRel (GenusVertex q)) (chain2 (oldToFullCube q) c) = 0 := by
  classical
  lin_ind c with c d hc hd => grind
  | f n =>
      have hn := oldToFullCube_face_ne_corner q f
      change chain1 (cornerSurfaceMap _) (cornerChain2 _
        (Finsupp.mapDomain (oldToFullCube q).onF (Finsupp.single f n))) = 0
      simp [Finsupp.mapDomain_single, cornerChain2, Finsupp.linearCombination_single, cornerTriangleEdge, hn]

theorem cornerSurfaceChain2_controlledCoverCap x :
    cornerSurfaceChain2 (cmpRel (GenusVertex q))
      (hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x)) =
        pathChain (gSig q (x.1.val, x.2)) := by
  rwd [controlledCoverCap_hurewicz, map_add, cornerSurfaceChain2_oldToFullCube,
    cornerSurfaceChain2_surfaceCornerFan, zero_add]

def capSurfaceFace : (cappedSpineCx q).F →
    (orderCx (NeSpx (cmpRel (GenusVertex q)))).E →₀ ℤ
  | .inl _ => 0
  | .inr x => pathChain (gSig q (x.1.val, x.2))

def capSurfaceChain2 : ((cappedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
    ((orderCx (NeSpx (cmpRel (GenusVertex q)))).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (capSurfaceFace q)

theorem cornerSurfaceChain2_controlledAugmentedChain2 c :
    cornerSurfaceChain2 (cmpRel (GenusVertex q)) (controlledAugmentedChain2 q c) =
      capSurfaceChain2 q c := by
  lin_ind c with c d hc hd => simp_all
  | f n =>
      rwd [controlledAugmentedChain2, Finsupp.linearCombination_single, map_smul,
        capSurfaceChain2, Finsupp.linearCombination_single]
      apply congrArg _
      obtain f | x := f
      · have h := cornerSurfaceChain2_oldToFullCube q
          (Finsupp.single (((genusSpineToOld q).comp (componentIncl (genusSpineCx q) (spineBase q))).onF f) 1)
        aesop
      · exact cornerSurfaceChain2_controlledCoverCap q x

/-- The actual augmented capping loops of every capped-cover cycle form a surface boundary. -/
theorem capSurfaceCycle_boundary c
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ d,
      Comb.bdry2 _ d = capSurfaceChain2 q (Finsupp.mapDomain Prod.snd c) := by
  cases' controlledAugmentedCycle_boundary3 q c hc with y hy
  refine ⟨-cornerSurfaceChain3 _ y, ?_⟩
  simp [map_neg, ← cornerSurfaceChain2_ordBoundary3, hy, cornerSurfaceChain2_controlledAugmentedChain2]
