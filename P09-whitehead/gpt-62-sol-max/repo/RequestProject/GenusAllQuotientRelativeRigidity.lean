module

public import RequestProject.GenusAllQuotientCorrections
public import RequestProject.FinsuppBasis
public import RequestProject.GenusAllQuotientReceivedSpine

@[expose] public section

/-! Recover the entire named relation vector from its genuine geometric
relative class. The scalar remains in the full quotient group until the last
coefficient-retraction step. These proof terms are not yet Lean-verified. -/
noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
variable {K : Complex2} (T : SpanningTree K) {G H I : Type} [Group G] [Group H]
  (φ : PresGroup (treeRel T) →* G)

theorem bdry2_translateCellChain (g : G) (c : (G × K.F) →₀ ℤ) :
    Comb.bdry2 (cover T φ) (translateCellChain g c) =
      translateCellChain g (Comb.bdry2 (cover T φ) c) :=
  DeckAction.faceChains_boundary (deck T φ) g c

theorem bdry2_multiplyCellChain (w : MonoidAlgebra ℤ G) (c : (G × K.F) →₀ ℤ) :
    Comb.bdry2 (cover T φ) (multiplyCellChain c w) =
      multiplyCellChain (Comb.bdry2 (cover T φ) c) w :=
  map_multiplyCellChain _ c _ (fun g => bdry2_translateCellChain T φ g c) w

theorem markedChainMap_translate (p : I → List (K.E × Bool))
    (g : G) (c : (G × I) →₀ ℤ) :
    markedChainMap T φ p (translateCellChain g c) =
      translateCellChain g (markedChainMap T φ p c) := by
  change markedChainMap T φ p (translateCellChain g c) =
    chain1 ((deck T φ).cellHom g) (markedChainMap T φ p c)
  finsupp_basis c [ translateCellChain ]
  intro x
  erw [translateCellChain, Finsupp.mapDomain_single, markedChainMap_single,
    markedChainMap_single, map_smul]
  congr 1
  erw [liftPath_translate]
  exact pathChain_map ((deck T φ).cellHom g) (liftPath T φ (p x.2) x.1)

theorem markedChainMap_multiply (p : I → List (K.E × Bool))
    (w : MonoidAlgebra ℤ G) (c : (G × I) →₀ ℤ) :
    markedChainMap T φ p (multiplyCellChain c w) =
      multiplyCellChain (markedChainMap T φ p c) w :=
  map_multiplyCellChain _ c _ (fun g => markedChainMap_translate T φ p g c) w

theorem markedChainMap_changeGroup (η : G →* H) (p : I → List (K.E × Bool))
    (c : (G × I) →₀ ℤ) :
    chain1 (changeGroup T φ η) (markedChainMap T φ p c) =
      markedChainMap T (η.comp φ) p
        (Finsupp.mapDomain (fun x : G × I => (η x.1, x.2)) c) := by
  finsupp_basis c
  intro x
  erw [Finsupp.mapDomain_single, markedChainMap_single, markedChainMap_single, map_smul]
  congr 1
  change Finsupp.mapDomain (changeGroup T φ η).onE (pathChain _) = _
  erw [← pathChain_map]
  exact congrArg pathChain (liftPath_map_group T φ η (p x.2) x.1)

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : IsSpineRelator ρ q u)

theorem allQuotientReceivedSpineToQuotient_chain2_translate
    (g : QuotientMarkingGroup q ρ u)
    (c : (allQuotientReceivedSpineCover q ρ u hrho).F →₀ ℤ) :
    chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
      (ReceivedTree.translateCellChain g c) =
      (namedQuotientDeck ρ q u).faceChains g
        (chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) c) := by
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ c) =
    Finsupp.mapDomain _ (Finsupp.mapDomain _ c)
  erw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  apply congrArg (fun f => Finsupp.mapDomain f c)
  funext x
  exact allQuotientReceivedSpineToQuotient_deckF q ρ u hrho g x.1 x.2

theorem allQuotientReceivedSpineToQuotient_chain2_multiply
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (c : (allQuotientReceivedSpineCover q ρ u hrho).F →₀ ℤ) :
    chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
      (ReceivedTree.multiplyCellChain c w) =
      Finsupp.linearCombination ℤ (fun g =>
        (namedQuotientDeck ρ q u).faceChains g
          (chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) c)) w.coeff :=
  ReceivedTree.map_multiplyCellChain _ c _ (fun g => allQuotientReceivedSpineToQuotient_chain2_translate q ρ u hrho g c) w

/-- Once polygon reconstruction identifies the genuine relative geometric
class, all named coefficients are a single multiple of the reference vector.
The only remaining inputs are explicit geometric equalities of actual chains. -/
theorem finiteSpine_relative_class_principal
    (β γ : SpineCoefficients ρ q u)
    (hβ : SpineInternalCycle ρ q u β)
    (hγ : SpineInternalCycle ρ q u γ)
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (hmark : quotientSurfaceMarkingChains q ρ u hrho
        (singleReceivedSpineMarkingChain q ρ u β) =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((namedQuotientDeck ρ q u).cellHom g)
        (quotientSurfaceMarkingChains q ρ u hrho
          (singleReceivedSpineMarkingChain q ρ u γ))) w.coeff)
    (hrel : ∃ y ∈ IncOn (fun p : UOrder (namedQuotientPos ρ q u)
        (namedQuotientBase ρ q u) => InQOld (uOrderEnd p)),
      Nerve.bdry y = universalNerveChain2
        (quotientCorrectedRelativeChain q ρ u hrho β -
          Finsupp.linearCombination ℤ (fun g =>
            (namedQuotientDeck ρ q u).faceChains g
              (quotientCorrectedRelativeChain q ρ u hrho γ)) w.coeff)) :
    ∃ a : MonoidAlgebra ℤ (SpineReplacementGroup ρ q u),
      ∀ m, β m = a * γ m := by
  let F  := finiteSpineToQuotient ρ q u hrho
  let cβ  :=
    singleReceivedSpineFaceChain q ρ u β
  let cγ  :=
    singleReceivedSpineFaceChain q ρ u γ
  let c  :=
    Finsupp.mapDomain (fun x => (F x.1, x.2)) cβ
  let d  :=
    Finsupp.mapDomain (fun x => (F x.1, x.2)) cγ
  let m  :=
    Finsupp.mapDomain (fun x => (F x.1, x.2))
    (singleReceivedSpineMarkingChain q ρ u β)
  let n  :=
    Finsupp.mapDomain (fun x => (F x.1, x.2))
    (singleReceivedSpineMarkingChain q ρ u γ)
  have hm : allQuotientSurfaceMarkingChains q ρ u m =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((namedQuotientDeck ρ q u).cellHom g)
        (allQuotientSurfaceMarkingChains q ρ u n)) w.coeff := by
    simpa only [quotientSurfaceMarkingChains_factor] using hmark
  have hmn : m = ReceivedTree.multiplyCellChain n w := by
    erw [← allQuotientSurfaceMarkingChains_multiply] at hm
    exact allQuotientSurfaceMarkingChains_injective q ρ u hm
  let M := ReceivedTree.markedChainMap (markedSpineTree q)
    (allQuotientSpineReceiver q ρ u hrho) (fun i => (treeMarkedSpineLoop q i).1)
  have hc : Comb.bdry2 (allQuotientReceivedSpineCover q ρ u hrho) c = M m := by
    change Comb.bdry2 _ (chain2 (receivedSpineChangeToAllQuotient q ρ u hrho) cβ) = _
    erw [bdry2_chain2, receivedSpineFaceChain_marked_boundary q ρ u β hβ]
    exact ReceivedTree.markedChainMap_changeGroup _ _ F _ _
  have hd : Comb.bdry2 (allQuotientReceivedSpineCover q ρ u hrho) d = M n := by
    change Comb.bdry2 _ (chain2 (receivedSpineChangeToAllQuotient q ρ u hrho) cγ) = _
    erw [bdry2_chain2, receivedSpineFaceChain_marked_boundary q ρ u γ hγ]
    exact ReceivedTree.markedChainMap_changeGroup _ _ F _ _
  have hcycle : Comb.bdry2 (allQuotientReceivedSpineCover q ρ u hrho)
      (c - ReceivedTree.multiplyCellChain d w) = 0 := by
    erw [map_sub, hc, ReceivedTree.bdry2_multiplyCellChain, hd, hmn]
    change M (ReceivedTree.multiplyCellChain n w) - ReceivedTree.multiplyCellChain (M n) w = 0
    erw [ReceivedTree.markedChainMap_multiply, sub_self]
  have hcmap  :=
    allQuotientReceivedSpineToQuotient_chain2_changeGroup q ρ u hrho cβ
  have hdmap  :=
    allQuotientReceivedSpineToQuotient_chain2_changeGroup q ρ u hrho cγ
  have hcorr : quotientCorrectedRelativeChain q ρ u hrho β -
      Finsupp.linearCombination ℤ (fun g =>
        (namedQuotientDeck ρ q u).faceChains g
          (quotientCorrectedRelativeChain q ρ u hrho γ)) w.coeff =
      chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
        (c - ReceivedTree.multiplyCellChain d w) := by
    erw [map_sub, allQuotientReceivedSpineToQuotient_chain2_multiply, hcmap, hdmap]
    simp only [quotientCorrectedRelativeChain, quotientMarkingCorrections_factor]
    exact allQuotientCorrection_cancel_difference q ρ u w m n
      (chain2 (receivedSpineToQuotient q ρ u hrho) cβ)
      (chain2 (receivedSpineToQuotient q ρ u hrho) cγ) hm
  have hcd : c = ReceivedTree.multiplyCellChain d w := by
    apply sub_eq_zero.mp
    apply allQuotientReceivedSpine_cycle_zero_of_quotient_old_boundary q ρ u hrho _ hcycle
    simpa only [hcorr] using hrel
  apply quotientNamedCoefficients_reflect_multiple q ρ u hrho β γ w
  · convert hcd using 1 <;> rfl
  · simpa only [m, n, F] using hmn

end FiniteChains.Davis.Genus
