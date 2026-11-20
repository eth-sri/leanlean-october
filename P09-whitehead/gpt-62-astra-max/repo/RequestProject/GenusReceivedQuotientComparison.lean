module

public import RequestProject.GenusFaithfulComparison
public import RequestProject.ReceivedTreeMarkedComparison
public import RequestProject.UniversalCoverPathTransport

@[expose] public section

/-! The received spine cover mapped to the actual named quotient.

-/
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FiniteChains.Comb
variable {K Y Z : Complex2}

variable (f : Hom K Y)

theorem pi1Map_comp_apply (g : Hom Y Z) (a : K.V)
    (z : Pi1 K a) :
    pi1Map (g.comp f) a z = pi1Map g _ (pi1Map f a z) := by
  refine Quotient.inductionOn z ?_
  intro p
  apply congrArg Pi1.mk
  simp [mapPath, Hom.comp, List.map_map, Function.comp_def]

theorem pi1Map_baseEq_apply {a b : K.V} (h : a = b)
    (z : Pi1 K a) :
    pi1Map f b (pi1BaseEqEquiv h z) =
      pi1BaseEqEquiv (congrArg f.onV h) (pi1Map f a z) := by
  subst b
  rfl

theorem pi1Conj_baseEq_end {a b c : K.V} {p : List _}
    (hp : IsPath K.src K.tgt p a c) (h : b = c)
    (hp' : IsPath K.src K.tgt p a b) (z : Pi1 K b) :
    pi1Conj hp (pi1BaseEqEquiv h z) = pi1Conj hp' z := by
  subst c
  rfl

section

variable {a b : K.V} {p : List (K.E × Bool)} (hp : IsPath K.src K.tgt p a b)
include a b p

theorem pi1Conj_reverse_cancel (z : Pi1 K b) :
    pi1Conj (isPath_revPath hp) (pi1Conj hp z) = z := by
  erw [pi1Conj_pi1Conj]
  exact (pi1Conj_congr _ _
    (htpy_revPath_append hp) z).trans
    (pi1Conj_empty_apply b z)

theorem pi1Conj_cancel_reverse (z : Pi1 K a) :
    pi1Conj hp (pi1Conj (isPath_revPath hp) z) = z := by
  erw [pi1Conj_pi1Conj]
  exact (pi1Conj_congr _ _
    (htpy_append_revPath hp) z).trans
    (pi1Conj_empty_apply a z)

end

variable (f : Hom K Y) (g : Hom Y Z)

theorem chain1_comp_apply (c : K.E →₀ ℤ) :
    chain1 (g.comp f) c = chain1 g (chain1 f c) := by
  change Finsupp.mapDomain (g.onE ∘ f.onE) c =
    Finsupp.mapDomain g.onE (Finsupp.mapDomain f.onE c)
  grind [Finsupp.mapDomain_comp]

theorem chain2_comp_apply (c : K.F →₀ ℤ) :
    chain2 (g.comp f) c = chain2 g (chain2 f c) := by
  change Finsupp.mapDomain (g.onF ∘ f.onF) c =
    Finsupp.mapDomain g.onF (Finsupp.mapDomain f.onF c)
  grind [Finsupp.mapDomain_comp]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
open scoped Classical

variable (q : ℕ) [NeZero q]

def markedSpineToOld : Hom (markedSpineCx q)
    (orderCx (QOld (cmpRel (GenusVertex q)))) :=
  (genusSpineToOld q).comp (componentIncl (genusSpineCx q) (spineBase q))

theorem markedSpineToOld_root :
    (markedSpineToOld q).onV (markedSpineTree q).root = posQCube (gBase q) := by
  erw [markedSpineTree_root]
  rfl

/-- Naming the marked words does not change the geometric map from the
tree presentation of the connected spine. This identity holds on every word. -/
theorem namedSpineToOld_inclusion (z : PresGroup _) :
    namedSpineToOldEquiv q
      (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z) =
    pi1BaseEqEquiv (markedSpineToOld_root q)
      (pi1Map (markedSpineToOld q) (markedSpineTree q).root
        (SpanningTree.presToPi1 (markedSpineTree q) z)) := by
  have hnamed : (namedSpinePi1Equiv q).symm
      (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z) =
      SpanningTree.presToPi1 _ z := by
    change (spinePresentationPi1Equiv q).symm
      ((namedSpineGroupEquiv q).symm ((namedSpineGroupEquiv q) z)) = _
    aesop
  change pi1Map _ _
    _ = _
  erw [hnamed]
  erw [← pi1Map_comp_apply (componentIncl (genusSpineCx q) (spineBase q))
    _ (markedSpineBase q)]
  apply pi1Map_baseEq_apply

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

def markedSpineToNamedQuotient :=
  (orderCxMap (qOldIncl (att := namedAtt ρ q u)) qOldIncl_monotone).comp
    (markedSpineToOld q)

theorem markedSpineToNamedQuotient_root :
    (markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root =
      qOldIncl (att := namedAtt ρ q u) (posQCube (gBase q)) :=
  congrArg _ (markedSpineToOld_root q)

def spineQuotientCylinderPath :=
  [ordPos (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q))]

theorem spineQuotientCylinderPath_isPath :
    IsPath (orderCx (namedQuotientPos ρ q u)).src
      (orderCx (namedQuotientPos ρ q u)).tgt (spineQuotientCylinderPath q ρ u)
      (namedQuotientBase ρ q u)
      ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root) := by
  erw [markedSpineToNamedQuotient_root]
  apply isPath_ordPos

/-- The geometric map on all spine words, with the actual cylinder path
accounting for the two different base vertices. -/
theorem namedSpineIntoQuotient_inclusion (z : PresGroup _) :
    namedSpineIntoQuotient ρ q u
      (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z) =
      pi1Conj (spineQuotientCylinderPath_isPath q ρ u)
        (pi1Map (markedSpineToNamedQuotient q ρ u) (markedSpineTree q).root
          (SpanningTree.presToPi1 (markedSpineTree q) z)) := by
  change pi1Conj _
    _ = _
  erw [namedSpineToOld_inclusion, pi1Map_baseEq_apply]
  erw [pi1Conj_baseEq_end
    _
    _
    _]
  erw [← pi1Map_comp_apply]
  rfl

abbrev singleReceivedSpineCover :=
  receivedSpineCover ρ _ (fun _ => u) PUnit.unit

/-- The proved faithful comparison expressed at the old spine base vertex. -/
def finiteSpineOldRootReceiver :=
  (pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))).comp
    (finiteSpineToQuotient ρ q u hrho)

theorem finiteSpineOldRootReceiver_compatible :
    (finiteSpineOldRootReceiver q ρ u hrho).comp
      (receivedSpineWordReceiver ρ _ (fun _ => u) PUnit.unit) =
      (pi1Map _ _).comp
        (SpanningTree.presToPi1 _) := by
  apply MonoidHom.ext
  intro z
  change pi1Conj _
    _ = _
  have h := DFunLike.congr_fun (finiteSpineToQuotient_spine ρ q u hrho)
    (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z)
  erw [show finiteSpineToQuotient ρ q u hrho
      _ =
      namedSpineIntoQuotient ρ q u
        _
      from h]
  erw [namedSpineIntoQuotient_inclusion, pi1Conj_reverse_cancel]
  rfl

/-- A genuine cellular comparison, with compatibility now proved from the
actual substituted presentation instead of required as an extra hypothesis. -/
def receivedSpineToQuotientOldRoot :=
  ReceivedTree.comparison _ _
    _
    _
    (finiteSpineOldRootReceiver_compatible q ρ u hrho)

/-- The comparison now lands at the base vertex used by the old/star
relative filling theorem. The change of base is the actual cylinder path. -/
def receivedSpineToQuotient :=
  (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).comp
    (receivedSpineToQuotientOldRoot q ρ u hrho)

/-- Exact geometric marked boundary, retaining every coefficient of the
actual single-block ring. Only the B2 coordinate equation is assumed. -/
theorem receivedSpineToQuotient_relative_boundary
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ _)
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    Comb.bdry2 _
      (chain2 (receivedSpineToQuotient q ρ u hrho)
      (receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β)) =
      chain1 (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u))
        (ReceivedTree.geometricMarkedChainMap (markedSpineTree q)
          (markedSpineToNamedQuotient q ρ u) (finiteSpineOldRootReceiver q ρ u hrho)
          (treeMarkedSpineLoop q)
          ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i)))) := by
  erw [receivedSpineToQuotient, chain2_comp_apply, bdry2_chain2]
  apply congrArg _
  apply ReceivedTree.comparison_relative_boundary
    _ _
    _
    _
    _
    _ (fun i => β _)
    _
  intro z
  let βF := β
  have hz0 := receivedSpineFaceChain_relative_boundary ρ _
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
  apply congrArg _
  exact (receivedSpineWordReceiver_coeff ρ _
    (fun _ => u) PUnit.unit _).symm

end FiniteChains.Davis.Genus
