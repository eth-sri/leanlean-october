import RequestProject.GenusSquareCoefficientSupport
import RequestProject.GenusOldCoordinateCollapse
import RequestProject.Tac
noncomputable section


/-! Actual recovered coordinate chains are supported on the surviving genus spine. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def markedSpineSquareCoefficients :=
  qSquareCycleCoefficients.comp (normalizeOrdChain2.comp (chain2 (markedSpineToFullCube q)))

def markedSpineCoordinateChain : ((markedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
    (Cube (GenusVertex q) →₀ ℤ) :=
  (Finsupp.lmapDomain ℤ ℤ
    (qCubeToCoordinate ·.1)).comp
      (markedSpineSquareCoefficients q)

def markedSpineExtendedCoordinateChain : ((markedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
    ((Cube (GenusVertex q) ⊕ Finset (GenusVertex q)) →₀ ℤ) :=
  (Finsupp.lmapDomain ℤ ℤ Sum.inl).comp (markedSpineCoordinateChain q)

theorem markedSpineCoordinateChain_zero_on_removed_square
    d g
    (hg : Sum.inl g ∈ (genusChainCollapse q).map Prod.snd) :
    markedSpineCoordinateChain q d g = 0 := by
  classical
  by_contra hn
  have hmem := Finsupp.mem_support_iff.mpr hn
  obtain ⟨s, hs, he⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
  obtain ⟨a, ha, hae⟩ := markedSpine_square_coefficient_support q d s
    (Finsupp.mem_support_iff.mp hs)
  have hnot := ha.2
  change Sum.inl (qCubeToCoordinate a.1) ∉ (genusChainCollapse q).map Prod.snd at hnot
  simp_all

theorem markedSpineExtendedCoordinateChain_zero_on_removed_face
    d f
    (hf : f ∈ (genusChainCollapse q).map Prod.snd) :
    markedSpineExtendedCoordinateChain q d f = 0 := by
  classical
  cases f with
  | inl g =>
      change Finsupp.mapDomain
        Sum.inl
        (markedSpineCoordinateChain q d) (Sum.inl g) = 0
      rw [Finsupp.mapDomain_apply_of_injective Sum.inl_injective]
      exact markedSpineCoordinateChain_zero_on_removed_square q d g hf
  | inr σ =>
      exact Finsupp.mapDomain_notin_range _ _ (by simp)

/-- The actual recovered coordinate chain of every old-spine two-chain is fixed by the
chosen geometric collapse because it has no coefficient on a removed face. -/
theorem markedSpineExtendedCoordinateChain_fixed d :
    CollapseChain.cmap (cubeBdry (V := GenusVertex q)) (genusChainCollapse q)
      (markedSpineExtendedCoordinateChain q d) = markedSpineExtendedCoordinateChain q d := by
  apply CollapseChain.cmap_of_forall_eq_zero
  intro p hp
  exact markedSpineExtendedCoordinateChain_zero_on_removed_face q d p.2
    (by grind)
