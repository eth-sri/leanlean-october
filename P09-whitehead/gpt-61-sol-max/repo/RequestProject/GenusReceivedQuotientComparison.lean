import Mathlib.Tactic

import RequestProject.GenusFaithfulComparison
import RequestProject.ReceivedTreeMarkedComparison
import RequestProject.UniversalCoverPathTransport

/-! The received spine cover mapped to the actual named quotient.

-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {K Y Z : Complex2}

  (f : Hom K Y)
  (g : Hom Y Z)
theorem pi1Map_comp_apply   (a : K.V)
    (z : Pi1 K a) :
    pi1Map (g.comp f) a z = pi1Map g (f.onV a) (pi1Map f a z) := by
  refine Quotient.inductionOn z ?_
  intro p
  apply congrArg Pi1.mk
  apply Subtype.ext
  simp [mapPath, Hom.comp]

variable {a b : K.V}
theorem pi1Map_baseEq_apply   (h : a = b)
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

theorem pi1Conj_reverse_cancel  {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) (z : Pi1 K b) :
    pi1Conj (isPath_revPath hp) (pi1Conj hp z) = z := by
  rw  [pi1Conj_pi1Conj]
  exact (pi1Conj_congr _ (show IsPath K.src K.tgt [] b b from rfl)
    (htpy_revPath_append hp) z).trans
    (pi1Conj_empty_apply b z)

theorem pi1Conj_cancel_reverse  {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) (z : Pi1 K a) :
    pi1Conj hp (pi1Conj (isPath_revPath hp) z) = z := by
  rw  [pi1Conj_pi1Conj]
  exact (pi1Conj_congr _ (show IsPath K.src K.tgt [] a a from rfl)
    (htpy_append_revPath hp) z).trans
    (pi1Conj_empty_apply a z)

theorem chain1_comp_apply   (c : K.E →₀ ℤ) :
    chain1 (g.comp f) c = chain1 g (chain1 f c) := by
  dsimp [FiniteChains.Comb.chain1, FiniteChains.Comb.Hom.comp]
  rw (config := { transparency := .default }) [Finsupp.mapDomain_comp]

theorem chain2_comp_apply   (c : K.F →₀ ℤ) :
    chain2 (g.comp f) c = chain2 g (chain2 f c) := by
  dsimp [FiniteChains.Comb.Hom.comp]
  rw (config := { transparency := .default }) [Finsupp.mapDomain_comp]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
open scoped Classical

variable (q : ℕ) [NeZero q]

noncomputable def markedSpineToOld  :=
  (genusSpineToOld q).comp (componentIncl (genusSpineCx q) (spineBase q))

theorem markedSpineToOld_root :
    (markedSpineToOld q).onV (markedSpineTree q).root = posQCube (gBase q) := by
  rw  [markedSpineTree_root]
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
    classical solve_by_elim (transparency := .default) [symm, MulEquiv.symm_apply_apply]
  change pi1Map (genusSpineToOld q) (spineBase q)
    (pi1Map (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineBase q)
      (pi1BaseEqEquiv (markedSpineTree_root q)
        ((namedSpinePi1Equiv q).symm
          (NamedPresentation.inclusion (spinePresentation q)
            (spinePresentationMarkedWord q) z)))) = _
  rw  [hnamed]
  erw [← pi1Map_comp_apply (componentIncl (genusSpineCx q) (spineBase q))
    (genusSpineToOld q) (markedSpineBase q)]
  exact pi1Map_baseEq_apply (markedSpineToOld q) (markedSpineTree_root q) _

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

noncomputable def markedSpineToNamedQuotient  :=
  (orderCxMap (qOldIncl (att := namedAtt ρ q u)) qOldIncl_monotone).comp
    (markedSpineToOld q)

theorem markedSpineToNamedQuotient_root :
    (markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root =
      qOldIncl (att := namedAtt ρ q u) (posQCube (gBase q)) :=
  congrArg (qOldIncl (att := namedAtt ρ q u)) (markedSpineToOld_root q)

noncomputable def spineQuotientCylinderPath  :=
  [ordPos (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q))]

theorem spineQuotientCylinderPath_isPath :
    IsPath (orderCx (namedQuotientPos ρ q u)).src
      (orderCx (namedQuotientPos ρ q u)).tgt (spineQuotientCylinderPath q ρ u)
      (namedQuotientBase ρ q u)
      ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root) := by
  rw  [markedSpineToNamedQuotient_root]
  exact isPath_ordPos (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q))

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
  rw  [namedSpineToOld_inclusion, pi1Map_baseEq_apply]
  erw [pi1Conj_baseEq_end
    (isPath_ordPos (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q)))
    (markedSpineToNamedQuotient_root q ρ u)
    (spineQuotientCylinderPath_isPath q ρ u)]
  rw  [← pi1Map_comp_apply]
  rfl

noncomputable abbrev singleReceivedSpineCover  :=
  receivedSpineCover ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit

/-- The proved faithful comparison expressed at the old spine base vertex. -/
noncomputable def finiteSpineOldRootReceiver  :=
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
  rw  [show finiteSpineToQuotient ρ q u hrho
      (singleSpineNamedReceiver ρ q u
        (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z)) =
      namedSpineIntoQuotient ρ q u
        (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z)
      from h]
  rw  [namedSpineIntoQuotient_inclusion, pi1Conj_reverse_cancel]
  rfl

/-- A genuine cellular comparison, with compatibility now proved from the
actual substituted presentation instead of required as an extra hypothesis. -/
noncomputable def receivedSpineToQuotientOldRoot  :=
  ReceivedTree.comparison (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
    (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)
    (finiteSpineOldRootReceiver q ρ u hrho)
    (finiteSpineOldRootReceiver_compatible q ρ u hrho)

/-- The comparison now lands at the base vertex used by the old/star
relative filling theorem. The change of base is the actual cylinder path. -/
noncomputable def receivedSpineToQuotient  :=
  (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).comp
    (receivedSpineToQuotientOldRoot q ρ u hrho)

/-- Exact geometric marked boundary, retaining every coefficient of the
actual single-block ring. Only the B2 coordinate equation is assumed. -/
theorem receivedSpineToQuotient_relative_boundary
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    Comb.bdry2 (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u))
      (chain2 (receivedSpineToQuotient q ρ u hrho)
      (receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β)) =
      chain1 (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u))
        (ReceivedTree.geometricMarkedChainMap (markedSpineTree q)
          (markedSpineToNamedQuotient q ρ u) (finiteSpineOldRootReceiver q ρ u hrho)
          (treeMarkedSpineLoop q)
          ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i)))) := by
  rw  [receivedSpineToQuotient, chain2_comp_apply, bdry2_chain2]
  apply congrArg (chain1 (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)))
  apply ReceivedTree.comparison_relative_boundary
    (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
    (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)
    (finiteSpineOldRootReceiver q ρ u hrho)
    (finiteSpineOldRootReceiver_compatible q ρ u hrho)
    (treeMarkedSpineLoop q) (fun i => β (Sum.inr i))
    (receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β)
  intro z
  let βF  := β
  have hz0 := receivedSpineFaceChain_relative_boundary ρ (fun _ : PUnit.{1} => q)
    (fun _ => u) PUnit.unit βF
  have hz := hz0 (by
      intro t
      with_reducible
        convert hβ t using 1
        congr
      all_goals first
        | exact Subsingleton.elim _ _
        | (funext m
           with_reducible congr 2
           all_goals first | exact Subsingleton.elim _ _ | rfl)) z
  refine hz.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x => βF (Sum.inr i) * x)
  exact (receivedSpineWordReceiver_coeff ρ (fun _ : PUnit.{1} => q)
    (fun _ => u) PUnit.unit (fox z (spinePresentationMarkedWord q i))).symm

end FiniteChains.Davis.Genus
