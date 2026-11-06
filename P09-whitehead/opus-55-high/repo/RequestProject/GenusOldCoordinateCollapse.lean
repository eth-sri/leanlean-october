import RequestProject.GenusCutCoefficientCycles
import RequestProject.Tac


/-! The actual recovered ordinary old-spine coefficients vanish under the genus collapse. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem genus_oldCoordinate_collapse_zero_of_boundary d
    (hd : Comb.bdry2 (markedSpineCx q) d = 0)
    r
    (he : Finsupp.lmapDomain ℤ ℤ
      (qCubeToCoordinate ·.1)
      (qSquareCycleCoefficients (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d))) =
      Finsupp.linearCombination ℤ
        (fun t : QThreeCube (cmpRel (GenusVertex q)) => qCubeCoordinateFacetChain t.1) r) :
    CollapseChain.cmap (cubeBdry (V := GenusVertex q)) (genusChainCollapse q)
      (Finsupp.lmapDomain ℤ ℤ Sum.inl
        (Finsupp.lmapDomain ℤ ℤ
          (qCubeToCoordinate ·.1)
          (qSquareCycleCoefficients (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d))))) = 0 := by
  classical
  let x := Finsupp.lmapDomain ℤ ℤ
    (Sum.inl : Cube (GenusVertex q) → Cube (GenusVertex q) ⊕ Finset (GenusVertex q))
    (Finsupp.linearCombination ℤ
      (qCubeCoordinateFacetChain ·.1) r)
  have hsplit : (qThreeTruncatedCoordinateBoundary r) =
      x +
        Sum.elim (0 : Cube (GenusVertex q) → ℤ) (fun σ => -qThreeCutFaceChain r σ) := by
    funext f
    rw [qThreeTruncatedCoordinateBoundary_split, Finsupp.sub_apply]
    cases f with
    | inl g =>
        have hz : Finsupp.mapDomain
            Sum.inr
            (qThreeCutFaceChain r) (Sum.inl g) = 0 :=
          Finsupp.mapDomain_notin_range _ _ (by simp)
        aesop
    | inr σ =>
        have hc : Finsupp.mapDomain
            (Sum.inr : Finset (GenusVertex q) → Cube (GenusVertex q) ⊕ Finset (GenusVertex q))
            (qThreeCutFaceChain r) (Sum.inr σ) = qThreeCutFaceChain r σ :=
          Finsupp.mapDomain_apply_of_injective Sum.inr_injective _ σ
        tauto
  have hz := genus_truncated_three_boundary_collapse_zero q r
  rw [hsplit, CollapseChain.cmap_add,
    genus_cutFaceChain_collapse_zero_of_old_boundary q d hd r he, add_zero] at hz
  grind

/-- Every capped-cover cycle has an actual old-spine augmentation whose recovered
ordinary coordinate chain is killed by the chosen geometric genus collapse. -/
theorem cappedCoverCycle_oldCoordinate_collapse_zero
    c (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ d : (markedSpineCx q).F →₀ ℤ,
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧
      Comb.bdry2 (markedSpineCx q) d = 0 ∧
      CollapseChain.cmap (cubeBdry (V := GenusVertex q)) (genusChainCollapse q)
        (Finsupp.lmapDomain ℤ ℤ Sum.inl
          (Finsupp.lmapDomain ℤ ℤ
            (qCubeToCoordinate ·.1)
            (qSquareCycleCoefficients
              (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d))))) = 0 := by
  obtain ⟨d, r, hd, hcycle, hr⟩ := cappedCoverCycle_old_coordinate_boundary q c hc
  exact ⟨d, hd, hcycle, genus_oldCoordinate_collapse_zero_of_boundary q d hcycle r hr⟩
