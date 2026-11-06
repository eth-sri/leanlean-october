import RequestProject.GenusAllQuotientCorrections
import RequestProject.GenusAllQuotientReceivedSpine
import RequestProject.Tac


/-! Recover the entire named relation vector from its genuine geometric
relative class. The scalar remains in the full quotient group until the last
coefficient-retraction step. These proof terms are not yet Lean-verified. -/
noncomputable section
open scoped Classical

bwd

set_option maxHeartbeats 800000

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
variable {K : Complex2} (T : SpanningTree K) {G H I : Type} [Group G] [Group H]
  (φ : PresGroup (treeRel T) →* G)

theorem bdry2_translateCellChain g c :
    Comb.bdry2 (cover T φ) (translateCellChain g c) =
      translateCellChain g (Comb.bdry2 (cover T φ) c) :=
  DeckAction.faceChains_boundary (deck T φ) g c

theorem bdry2_multiplyCellChain w c :
    Comb.bdry2 (cover T φ) (multiplyCellChain c w) =
      multiplyCellChain (Comb.bdry2 (cover T φ) c) w := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp_all
  | single g n =>
      simp [multiplyCellChain, Finsupp.linearCombination_single, map_smul, bdry2_translateCellChain]

theorem markedChainMap_translate p
    g (c : (G × I) →₀ ℤ) :
    markedChainMap T φ p (translateCellChain g c) =
      translateCellChain g (markedChainMap T φ p c) := by
  change markedChainMap T φ p (translateCellChain g c) =
    chain1 ((deck T φ).cellHom g) (markedChainMap T φ p c)
  induction c using Finsupp.induction_linear with
  | zero => rfl
  | add c d hc hd =>
      simp_all [translateCellChain, Finsupp.mapDomain_add, map_add]
  | single x n =>
      rwd [translateCellChain, Finsupp.mapDomain_single, markedChainMap_single,
        markedChainMap_single, map_smul]
      congr 1
      rwd [liftPath_translate]
      exact pathChain_map ((deck T φ).cellHom g) _

theorem markedChainMap_multiply p
    w (c : (G × I) →₀ ℤ) :
    markedChainMap T φ p (multiplyCellChain c w) =
      multiplyCellChain (markedChainMap T φ p c) w := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp_all
  | single g n =>
      simp [multiplyCellChain, Finsupp.linearCombination_single, map_smul, markedChainMap_translate]

theorem markedChainMap_changeGroup (η : G →* H) p
    c :
    chain1 (changeGroup T φ η) (markedChainMap T φ p c) =
      markedChainMap T (η.comp φ) p
        (Finsupp.mapDomain (fun x : G × I => (η x.1, x.2)) c) := by
  lin_ind c with c d hc hd => simp [map_add, Finsupp.mapDomain_add, hc, hd]
  | x n =>
      rwd [Finsupp.mapDomain_single, markedChainMap_single, markedChainMap_single, map_smul]
      congr 1
      change Finsupp.mapDomain (changeGroup T φ η).onE (pathChain _) = _
      rwd [← pathChain_map]
      exact congrArg pathChain (liftPath_map_group T φ η _ x.1)

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

theorem receivedSpineFaceChain_marked_boundary
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    Comb.bdry2 (singleReceivedSpineCover q ρ u)
      (receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β) =
      ReceivedTree.markedChainMap (markedSpineTree q)
        (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)
        (fun i => (treeMarkedSpineLoop q i).1)
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) := by
  apply ReceivedTree.bdry2_eq_markedChain_of_coordinates
    _
    _
    _ _
    _
  intro z
  let βF := β
  have hz0 := receivedSpineFaceChain_relative_boundary ρ (fun _ => q)
    _ PUnit.unit βF
  have hwords : familyFiniteSpineWordBlock _ (fun _ => u) =
      finiteSpineWordBlock q u := by
    rfl
  have hz := hz0 (by
    intro t
    with_reducible
      convert hβ t using 1
      apply Finset.sum_congr rfl
      intro m hm
      congr 2
      all_goals grind) z
  refine hz.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg _
  exact (receivedSpineWordReceiver_coeff ρ _
    _ PUnit.unit _).symm

theorem allQuotientReceivedSpineToQuotient_chain2_translate
    (g : QuotientMarkingGroup q ρ u)
    (c : (allQuotientReceivedSpineCover q ρ u hrho).F →₀ ℤ) :
    chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
      (ReceivedTree.translateCellChain g c) =
      (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
        (chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) c) := by
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ c) =
    Finsupp.mapDomain _ (Finsupp.mapDomain _ c)
  rwd [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  apply congrArg (Finsupp.mapDomain · c)
  funext x
  exact allQuotientReceivedSpineToQuotient_deckF q ρ u hrho g x.1 x.2

theorem allQuotientReceivedSpineToQuotient_chain2_multiply
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (c : (allQuotientReceivedSpineCover q ρ u hrho).F →₀ ℤ) :
    chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
      (ReceivedTree.multiplyCellChain c w) =
      Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
          (chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) c)) w.coeff := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp [map_add, MonoidAlgebra.coeff_add, hw, hz]
  | single g n =>
      simp only [ReceivedTree.multiplyCellChain, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, MonoidAlgebra.coeffLinearEquiv_apply,
        MonoidAlgebra.coeff_single, Finsupp.linearCombination_single]
      rwd [map_smul,
        allQuotientReceivedSpineToQuotient_chain2_translate]

/-- Once polygon reconstruction identifies the genuine relative geometric
class, all named coefficients are a single multiple of the reference vector.
The only remaining inputs are explicit geometric equalities of actual chains. -/
theorem finiteSpine_relative_class_principal
    β γ
    (hβ : ∀ z,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (hγ : ∀ z,
      (∑ m, γ m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (hmark : quotientSurfaceMarkingChains q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
        (quotientSurfaceMarkingChains q ρ u hrho
          ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => γ (Sum.inr i))))) w.coeff)
    (hrel : ∃ y ∈ IncOn (fun p : UOrder (namedQuotientPos ρ q u)
        (namedQuotientBase ρ q u) => InQOld (uOrderEnd p)),
      Nerve.bdry y = universalNerveChain2
        (quotientCorrectedRelativeChain q ρ u hrho β -
          Finsupp.linearCombination ℤ (fun g =>
            (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
              (quotientCorrectedRelativeChain q ρ u hrho γ)) w.coeff)) :
    ∃ a,
      ∀ m, β m = a * γ m := by
  let F : PresGroup (substPresF ρ (finiteSpineWordBlock q u)) →*
      QuotientMarkingGroup q ρ u := finiteSpineToQuotient ρ q u hrho
  let cβ : (singleReceivedSpineCover q ρ u).F →₀ ℤ :=
    receivedSpineFaceChain ρ _ _ PUnit.unit β
  let cγ : (singleReceivedSpineCover q ρ u).F →₀ ℤ :=
    receivedSpineFaceChain ρ _ _ PUnit.unit γ
  let c : (QuotientMarkingGroup q ρ u × (markedSpineCx q).F) →₀ ℤ :=
    Finsupp.mapDomain (fun x => (F x.1, x.2)) cβ
  let d : (QuotientMarkingGroup q ρ u × (markedSpineCx q).F) →₀ ℤ :=
    Finsupp.mapDomain (fun x => (F x.1, x.2)) cγ
  let m : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ :=
    Finsupp.mapDomain (fun x => (F x.1, x.2))
    ((ReceivedTree.cellCoordinates _).symm (fun i => β (Sum.inr i)))
  let n : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ :=
    Finsupp.mapDomain (fun x => (F x.1, x.2))
    ((ReceivedTree.cellCoordinates _).symm (fun i => γ (Sum.inr i)))
  have hm : allQuotientSurfaceMarkingChains q ρ u m =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck _ _).cellHom g)
        (allQuotientSurfaceMarkingChains q ρ u n)) w.coeff := by
    simpa [quotientSurfaceMarkingChains_factor] using hmark
  have hmn : m = ReceivedTree.multiplyCellChain n w := by
    rwd [← allQuotientSurfaceMarkingChains_multiply] at hm
    exact allQuotientSurfaceMarkingChains_injective q ρ u hm
  let M := ReceivedTree.markedChainMap _
    (allQuotientSpineReceiver q ρ u hrho) (fun i => (treeMarkedSpineLoop q i).1)
  have hc : Comb.bdry2 (allQuotientReceivedSpineCover q ρ u hrho) c = M m := by
    change Comb.bdry2 _ (chain2 (receivedSpineChangeToAllQuotient q ρ u hrho) cβ) = _
    rwd [bdry2_chain2, receivedSpineFaceChain_marked_boundary q ρ u β hβ]
    exact ReceivedTree.markedChainMap_changeGroup _ _ F _ _
  have hd : Comb.bdry2 (allQuotientReceivedSpineCover q ρ u hrho) d = M n := by
    change Comb.bdry2 _ (chain2 (receivedSpineChangeToAllQuotient q ρ u hrho) cγ) = _
    rwd [bdry2_chain2, receivedSpineFaceChain_marked_boundary q ρ u γ hγ]
    exact ReceivedTree.markedChainMap_changeGroup _ _ F _ _
  have hcycle : Comb.bdry2 (allQuotientReceivedSpineCover q ρ u hrho)
      (c - ReceivedTree.multiplyCellChain d w) = 0 := by
    rwd [map_sub, hc, ReceivedTree.bdry2_multiplyCellChain, hd, hmn]
    grind [ReceivedTree.markedChainMap_multiply, sub_self]
  have hcmap : chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) c =
      chain2 (receivedSpineToQuotient q ρ u hrho) cβ :=
    allQuotientReceivedSpineToQuotient_chain2_changeGroup q ρ u hrho cβ
  have hdmap : chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) d =
      chain2 (receivedSpineToQuotient q ρ u hrho) cγ :=
    allQuotientReceivedSpineToQuotient_chain2_changeGroup q ρ u hrho cγ
  have hcorr : quotientCorrectedRelativeChain q ρ u hrho β -
      Finsupp.linearCombination ℤ (fun g =>
        (univDeck _ _).faceChains g
          (quotientCorrectedRelativeChain q ρ u hrho γ)) w.coeff =
      chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
        (c - ReceivedTree.multiplyCellChain d w) := by
    rwd [map_sub, allQuotientReceivedSpineToQuotient_chain2_multiply, hcmap, hdmap]
    simp only [quotientCorrectedRelativeChain, quotientMarkingCorrections_factor]
    exact allQuotientCorrection_cancel_difference q ρ u w m n
      _
      _ hm
  have hcd : c = ReceivedTree.multiplyCellChain d w := by
    apply sub_eq_zero.mp
    apply allQuotientReceivedSpine_cycle_zero_of_quotient_old_boundary q ρ u hrho _ hcycle
    simp_all
  apply quotientNamedCoefficients_reflect_multiple q ρ u hrho β γ w
  · tauto
  omega
