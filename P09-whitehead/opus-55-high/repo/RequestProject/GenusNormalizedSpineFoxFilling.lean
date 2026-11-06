import RequestProject.GenusUniversalCoveredSpine
import RequestProject.GenusSpineSubstitutedBoundary
import RequestProject.ReceivedTreeMarkedChains
import RequestProject.CrowellFinsupp
import RequestProject.BlockFamilyBlockwiseFinsupp
import RequestProject.Tac


/-! Convert a geometrically normalized pre-substitution spine filling to the
full named Fox filling, preserving the marked coefficients and the original
face coordinates. The geometric choice is made by the surface construction;
this file supplies its exact algebraic interface. Awaiting Lean verification. -/
noncomputable section
open scoped Classical
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb BlockFamily
variable (q : ℕ) [NeZero q]

theorem sum_namedSpineRel {M} [AddCommMonoid M]
    (f : NamedSpineRel q → M) :
    (∑ m, f m) = (∑ j : SpinePresentationRel q, f (Sum.inl j)) +
      ∑ i : Fin q × Bool, f (Sum.inr i) := by
  have hu : Finset.univ =
      @Finset.univ _
        (instFintypeSum (SpinePresentationRel q) (Fin q × Bool)) :=
    by grind
  simp_all

def namedSpineSurfaceWord : FreeGroup (NamedSpineGen q) :=
  commWord (fun i => FreeGroup.of (Sum.inr i)) (finitePairs q)

def namedSpineSurfaceMarkingCoefficient (i : Fin q × Bool) :
    MonoidAlgebra ℤ (PresGroup (namedSpinePresentation q)) :=
  quotRingHom ℤ _
    (fox (Sum.inr i) (namedSpineSurfaceWord q))

def normalizedNamedSpineVector (d : (universalNamedSpineCover q).F →₀ ℤ) :
    NamedSpineRel q → MonoidAlgebra ℤ (PresGroup (namedSpinePresentation q)) :=
  Sum.elim (ReceivedTree.cellCoefficient · d) (namedSpineSurfaceMarkingCoefficient q)

theorem universalSpineWordCoefficient (x : FreeGroupRing (SpinePresentationGen q)) :
    ReceivedTree.coefficientMap (markedSpineTree q) (universalSpineWordReceiver q) x =
      NamedPresentation.wordCoefficientMap (spinePresentation q) (spinePresentationMarkedWord q) x := by
  change MonoidAlgebra.mapDomainRingHom ℤ (universalSpineWordReceiver q)
      (MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' _) x) =
    MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' _)
      (MonoidAlgebra.mapDomainRingHom ℤ (FreeGroup.map Sum.inl) x)
  simp only [BlockMor.mapDomainRingHom_comp']
  congr 1

theorem namedSpineSurfaceWord_fox_internal z :
    fox (Sum.inl z) (namedSpineSurfaceWord q) = 0 := by
  have hw : namedSpineSurfaceWord q = FreeGroup.map Sum.inr
      (commWord (FreeGroup.of ·) (finitePairs q)) := by
    simp [namedSpineSurfaceWord, map_commWord, FreeGroup.map.of]
  rwd [hw]
  exact fox_map_of_not_mem_range Sum.inr (by simp) _

/-- An initial filling with this exact boundary exists before geometric
normalization. Its arbitrary homology class will subsequently be adjusted to
the explicitly constructed degree-one polygon. -/
theorem exists_universalNamedSpine_markedFilling :
    ∃ d,
      Comb.bdry2 (universalNamedSpineCover q) d =
        ReceivedTree.markedChain (markedSpineTree q) (universalSpineWordReceiver q)
          (treeMarkedSpineLoop q) (namedSpineSurfaceMarkingCoefficient q) := by
  have hw : namedSpineSurfaceWord q ∈ relSub (namedSpinePresentation q) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' _) (namedSpineSurfaceWord q) = 1
    rwd [namedSpineSurfaceWord, map_commWord]
    exact namedSpine_surface_filling q
  obtain ⟨c, hc⟩ := exists_coverSecondBoundary_of_mem_normalClosure
    (N := relSub (namedSpinePresentation q)) (ρ := namedSpinePresentation q)
    (fun m => Subgroup.subset_normalClosure ⟨m, rfl⟩) hw
  have hrow (a : NamedSpineGen q) :
      (∑ m, c m * foxMatrixPres _ a m) =
        quotRingHom ℤ _ (fox a (namedSpineSurfaceWord q)) := by
    have h := congrArg (· a) hc
    rwd [fsCoverSecondBoundary_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    exact h
  have hm (i : Fin q × Bool) : c (Sum.inr i) = namedSpineSurfaceMarkingCoefficient q i := by
    have h := hrow (Sum.inr i)
    simp_all [sum_namedSpineRel, namedSpinePresentation, NamedPresentation.matrix_marked_relator, NamedPresentation.matrix_marked_name, namedSpineSurfaceMarkingCoefficient]
  let d :=
    (ReceivedTree.cellCoordinates _).symm (fun j => c (Sum.inl j))
  refine ⟨d, ?_⟩
  apply ReceivedTree.bdry2_eq_markedChain_of_coordinates
    _ _
    _ _ d
  intro z
  rwd [ReceivedTree.cellCoefficient_bdry2]
  simp [d, ReceivedTree.cellCoefficient_coordinates_symm,
    universalSpineWordCoefficient, treeMarkedSpineLoop]
  have hz := hrow (Sum.inl z)
  rwd [namedSpineSurfaceWord_fox_internal, map_zero] at hz
  rwd [sum_namedSpineRel] at hz
  simp [namedSpinePresentation, NamedPresentation.matrix_internal_relator,
    NamedPresentation.matrix_internal_name, mul_neg, Finset.sum_neg_distrib,
    ← sub_eq_add_neg] at hz
  refine (sub_eq_zero.mp hz).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun x => x * NamedPresentation.wordCoefficientMap
    _ _
    (fox z (spinePresentationMarkedWord q i))) (hm i)

/-- Every actual filling with the prescribed marked boundary gives all Fox
coordinates, including the name-relator coordinates, with their exact signs. -/
theorem normalizedNamedSpineVector_boundary
    d
    (hd : Comb.bdry2 (universalNamedSpineCover q) d =
      ReceivedTree.markedChain (markedSpineTree q) (universalSpineWordReceiver q)
        (treeMarkedSpineLoop q) (namedSpineSurfaceMarkingCoefficient q))
    a :
    (∑ m, normalizedNamedSpineVector q d m * foxMatrixPres (namedSpinePresentation q) a m) =
      quotRingHom ℤ (relSub (namedSpinePresentation q)) (fox a (namedSpineSurfaceWord q)) := by
  cases a with
  | inl z =>
      have h := congrArg (ReceivedTree.cellCoefficient z.1) hd
      rwd [ReceivedTree.cellCoefficient_bdry2, ReceivedTree.cellCoefficient_markedChain] at h
      simp [universalSpineWordCoefficient, treeMarkedSpineLoop] at h
      rwd [namedSpineSurfaceWord_fox_internal, map_zero]
      simp_all [sum_namedSpineRel, namedSpinePresentation, NamedPresentation.matrix_internal_relator, NamedPresentation.matrix_internal_name, normalizedNamedSpineVector, Sum.elim_inl, Sum.elim_inr, mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg, spinePresentation, spinePresentationMarkedWord]
  | inr i =>
      simp [sum_namedSpineRel, namedSpinePresentation, NamedPresentation.matrix_marked_relator, NamedPresentation.matrix_marked_name, normalizedNamedSpineVector, namedSpineSurfaceMarkingCoefficient]

theorem spineReorderHom_fox a w :
    MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q)
      (quotRingHom ℤ (relSub (namedSpinePresentation q)) (fox a w)) =
    quotRingHom ℤ (relSub (markedSpineBeta q))
      (fox (Sum.swap a) (FreeGroup.map Sum.swap w)) := by
  simpa [fox_map Sum.swap (Equiv.sumComm _ _).injective] using
    spineReorderHom_coeff q _

theorem spineReorderHom_matrix a m :
    MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q)
      (foxMatrixPres (namedSpinePresentation q) a m) =
    foxMatrixPres (markedSpineBeta q) (Sum.swap a) m :=
  spineReorderHom_fox q a _

def normalizedMarkedSpineFilling (d : (universalNamedSpineCover q).F →₀ ℤ) :=
  Finsupp.equivFunOnFinite.symm (fun m =>
    MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q) (normalizedNamedSpineVector q d m))

@[simp] theorem normalizedMarkedSpineFilling_apply
    d m :
    normalizedMarkedSpineFilling q d m =
      MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q) (normalizedNamedSpineVector q d m) := by
  rfl

/-- This is the full pre-substitution B1 certificate for the normalized
reference; it can replace the arbitrary Crowell choice without changing any
of the later substitution or family arguments. -/
theorem normalizedMarkedSpineFilling_boundary
    d
    (hd : Comb.bdry2 (universalNamedSpineCover q) d =
      ReceivedTree.markedChain (markedSpineTree q) (universalSpineWordReceiver q)
        (treeMarkedSpineLoop q) (namedSpineSurfaceMarkingCoefficient q))
    a :
    (∑ m, normalizedMarkedSpineFilling q d m * foxMatrixPres (markedSpineBeta q) a m) =
      quotRingHom ℤ (relSub (markedSpineBeta q))
        (fox a (commWord (fun i => FreeGroup.of (Sum.inl i)) (finitePairs q))) := by
  have h := congrArg (MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q))
    (normalizedNamedSpineVector_boundary q d hd a.swap)
  simp only [map_sum, map_mul, spineReorderHom_matrix, spineReorderHom_fox,
    Sum.swap_swap] at h
  have hw : FreeGroup.map Sum.swap (namedSpineSurfaceWord q) =
      commWord (fun i => FreeGroup.of (Sum.inl i)) (finitePairs q) := by
    simp [namedSpineSurfaceWord, map_commWord, FreeGroup.map.of, Sum.swap_inr]
  simp_all
