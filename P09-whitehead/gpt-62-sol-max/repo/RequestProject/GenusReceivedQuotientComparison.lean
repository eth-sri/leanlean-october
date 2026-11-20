module

public import RequestProject.GenusFaithfulComparison
public import RequestProject.ReceivedTreeMarkedComparison
public import RequestProject.UniversalCoverPathTransport

@[expose] public section

/-! The received spine cover mapped to the actual named quotient.

-/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
variable {K Y Z : Complex2}

theorem pi1Map_baseEq_apply (f : Hom K Y) {a b : K.V} (h : a = b)
    (z : Pi1 K a) :
    pi1Map f b (pi1BaseEqEquiv h z) =
      pi1BaseEqEquiv (congrArg f.onV h) (pi1Map f a z) := by
  subst b
  rfl

theorem pi1Conj_baseEq_end {a b c : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a c) (h : b = c)
    (hp' : IsPath K.src K.tgt p a b) (z : Pi1 K b) :
    pi1Conj hp (pi1BaseEqEquiv h z) = pi1Conj hp' z := by
  subst c
  rfl

theorem pi1Conj_reverse_cancel {a b : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) (z : Pi1 K b) :
    pi1Conj (isPath_revPath hp) (pi1Conj hp z) = z := by
  erw [pi1Conj_pi1Conj]
  exact (pi1Conj_congr _ (show IsPath K.src K.tgt [] b b from rfl)
    (htpy_revPath_append hp) z).trans
    (pi1Conj_empty_apply b z)

theorem pi1Conj_cancel_reverse {a b : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) (z : Pi1 K a) :
    pi1Conj hp (pi1Conj (isPath_revPath hp) z) = z := by
  erw [pi1Conj_pi1Conj]
  exact (pi1Conj_congr _ (show IsPath K.src K.tgt [] a a from rfl)
    (htpy_append_revPath hp) z).trans
    (pi1Conj_empty_apply a z)

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
open scoped Classical

variable (q : ℕ) [NeZero q]

noncomputable def markedSpineToOld : Hom (markedSpineCx q)
    (orderCx (QOld (cmpRel (GenusVertex q)))) :=
  (genusSpineToOld q).comp (componentIncl (genusSpineCx q) (spineBase q))

theorem markedSpineToOld_root :
    (markedSpineToOld q).onV (markedSpineTree q).root = posQCube (gBase q) := by
  erw [markedSpineTree_root]
  rfl

/-- Naming the marked words does not change the geometric map from the
tree presentation of the connected spine. This identity holds on every word. -/
theorem namedSpineToOld_inclusion (z : PresGroup (spinePresentation q)) :
    namedSpineToOldEquiv q
      (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z) =
    pi1BaseEqEquiv (markedSpineToOld_root q)
      (pi1Map (markedSpineToOld q) (markedSpineTree q).root
        (SpanningTree.presToPi1 (markedSpineTree q) z)) := by
  have hnamed : (namedSpinePi1Equiv q).symm
      (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z) =
      SpanningTree.presToPi1 (markedSpineTree q) z := by
    change (spinePresentationPi1Equiv q).symm
      ((namedSpineGroupEquiv q).symm ((namedSpineGroupEquiv q) z)) = _
    erw [MulEquiv.symm_apply_apply]
    rfl
  change pi1Map (genusSpineToOld q) (spineBase q)
    (pi1Map (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineBase q)
      (pi1BaseEqEquiv (markedSpineTree_root q)
        ((namedSpinePi1Equiv q).symm
          (NamedPresentation.inclusion (spinePresentation q)
            (spinePresentationMarkedWord q) z)))) = _
  erw [hnamed]
  erw [← pi1Map_comp_apply (componentIncl (genusSpineCx q) (spineBase q))
    (genusSpineToOld q) (markedSpineBase q)]
  exact pi1Map_baseEq_apply (markedSpineToOld q) (markedSpineTree_root q) _

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (u : Fin q × Bool → FreeGroup α)
  (hrho : IsSpineRelator ρ q u)

noncomputable def markedSpineToNamedQuotient : Hom (markedSpineCx q)
    (namedQuotientCx ρ q u) :=
  (orderCxMap (qOldIncl (att := namedAtt ρ q u)) qOldIncl_monotone).comp
    (markedSpineToOld q)

theorem markedSpineToNamedQuotient_root :
    (markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root =
      qOldIncl (att := namedAtt ρ q u) (posQCube (gBase q)) :=
  congrArg (qOldIncl (att := namedAtt ρ q u)) (markedSpineToOld_root q)

noncomputable def spineQuotientCylinderPath :
    List ((namedQuotientCx ρ q u).E × Bool) :=
  [ordPos (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q))]

theorem spineQuotientCylinderPath_isPath :
    IsPath (namedQuotientCx ρ q u).src
      (namedQuotientCx ρ q u).tgt (spineQuotientCylinderPath q ρ u)
      (namedQuotientBase ρ q u)
      ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root) := by
  erw [markedSpineToNamedQuotient_root]
  solve_by_elim

/-- The geometric map on all spine words, with the actual cylinder path
accounting for the two different base vertices. -/
theorem namedSpineIntoQuotient_inclusion (z : PresGroup (spinePresentation q)) :
    namedSpineIntoQuotient ρ q u
      (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z) =
      pi1Conj (spineQuotientCylinderPath_isPath q ρ u)
        (pi1Map (markedSpineToNamedQuotient q ρ u) (markedSpineTree q).root
          (SpanningTree.presToPi1 (markedSpineTree q) z)) := by
  change pi1Conj (isPath_ordPos
      (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q)))
    (pi1Map (orderCxMap (qOldIncl (att := namedAtt ρ q u)) qOldIncl_monotone)
      (posQCube (gBase q))
      (namedSpineToOldEquiv q
        (NamedPresentation.inclusion (spinePresentation q)
          (spinePresentationMarkedWord q) z))) = _
  erw [namedSpineToOld_inclusion, pi1Map_baseEq_apply]
  erw [pi1Conj_baseEq_end
    (isPath_ordPos (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q)))
    (markedSpineToNamedQuotient_root q ρ u)
    (spineQuotientCylinderPath_isPath q ρ u)]
  erw [← pi1Map_comp_apply]
  rfl

noncomputable abbrev singleReceivedSpineCover : Complex2 :=
  receivedSpineCover ρ (fun _  => q) (fun _ => u) PUnit.unit

/-- The proved faithful comparison expressed at the old spine base vertex. -/
noncomputable def finiteSpineOldRootReceiver :
    SpineReplacementGroup ρ q u →*
      Pi1 (namedQuotientCx ρ q u)
        ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root) :=
  (pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))).comp
    (finiteSpineToQuotient ρ q u hrho)

theorem finiteSpineOldRootReceiver_compatible :
    (finiteSpineOldRootReceiver q ρ u hrho).comp
      (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit) =
      (pi1Map (markedSpineToNamedQuotient q ρ u) (markedSpineTree q).root).comp
        (SpanningTree.presToPi1 (markedSpineTree q)) := by
  apply MonoidHom.ext
  intro z
  change pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))
    (finiteSpineToQuotient ρ q u hrho
      (singleSpineNamedReceiver ρ q u
        (NamedPresentation.inclusion (spinePresentation q)
          (spinePresentationMarkedWord q) z))) = _
  have h := DFunLike.congr_fun (finiteSpineToQuotient_spine ρ q u hrho)
    (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z)
  erw [h]
  erw [namedSpineIntoQuotient_inclusion, pi1Conj_reverse_cancel]
  rfl

/-- A genuine cellular comparison, with compatibility now proved from the
actual substituted presentation instead of required as an extra hypothesis. -/
noncomputable def receivedSpineToQuotientOldRoot :
    Hom (singleReceivedSpineCover q ρ u)
      (uCover (namedQuotientCx ρ q u)
        ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root)) :=
  ReceivedTree.comparison (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
    (receivedSpineWordReceiver ρ (fun _  => q) (fun _ => u) PUnit.unit)
    (finiteSpineOldRootReceiver q ρ u hrho)
    (finiteSpineOldRootReceiver_compatible q ρ u hrho)

/-- The comparison now lands at the base vertex used by the old/star
relative filling theorem. The change of base is the actual cylinder path. -/
noncomputable def receivedSpineToQuotient :
    Hom (singleReceivedSpineCover q ρ u)
      (namedQuotientCover ρ q u) :=
  (shiftHom (spineQuotientCylinderPath_isPath q ρ u)).comp
    (receivedSpineToQuotientOldRoot q ρ u hrho)

theorem receivedSpineFaceChain_marked_boundary
    (β : SpineCoefficients ρ q u)
    (hβ : SpineInternalCycle ρ q u β) :
    Comb.bdry2 (singleReceivedSpineCover q ρ u)
      (singleReceivedSpineFaceChain q ρ u β) =
      ReceivedTree.markedChainMap (markedSpineTree q)
        (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)
        (fun i => (treeMarkedSpineLoop q i).1)
        (singleReceivedSpineMarkingChain q ρ u β) := by
  apply ReceivedTree.bdry2_eq_markedChain_of_coordinates
    (markedSpineTree q)
    (receivedSpineWordReceiver ρ (fun _  => q) (fun _ => u) PUnit.unit)
    (treeMarkedSpineLoop q) (fun i => β (Sum.inr i))
    (singleReceivedSpineFaceChain q ρ u β)
  intro z
  have hz := receivedSpineFaceChain_relative_boundary ρ (fun _ : PUnit.{1} => q)
    (fun _ => u) PUnit.unit β hβ z
  exact hz.trans (Finset.sum_congr rfl (fun i _ => congrArg (β (Sum.inr i) * ·)
    (receivedSpineWordReceiver_coeff ρ (fun _ => q) (fun _ => u) PUnit.unit
      (fox z (spinePresentationMarkedWord q i))).symm))

/-- Exact geometric marked boundary, retaining every coefficient of the
actual single-block ring. Only the B2 coordinate equation is assumed. -/
theorem receivedSpineToQuotient_relative_boundary
    (β : SpineCoefficients ρ q u)
    (hβ : SpineInternalCycle ρ q u β) :
    Comb.bdry2 (namedQuotientCover ρ q u)
      (chain2 (receivedSpineToQuotient q ρ u hrho)
      (singleReceivedSpineFaceChain q ρ u β)) =
      chain1 (shiftHom (spineQuotientCylinderPath_isPath q ρ u))
        (ReceivedTree.geometricMarkedChainMap (markedSpineTree q)
          (markedSpineToNamedQuotient q ρ u) (finiteSpineOldRootReceiver q ρ u hrho)
          (treeMarkedSpineLoop q)
          (singleReceivedSpineMarkingChain q ρ u β)) := by
  erw [receivedSpineToQuotient, chain2_comp_apply, bdry2_chain2,
    receivedSpineToQuotientOldRoot, ReceivedTree.comparison_bdry2,
    receivedSpineFaceChain_marked_boundary q ρ u β hβ, ReceivedTree.comparison_markedChainMap]

end FiniteChains.Davis.Genus
