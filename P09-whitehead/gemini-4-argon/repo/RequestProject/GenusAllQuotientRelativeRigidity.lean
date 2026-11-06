module

public import RequestProject.GenusAllQuotientCorrections
public import RequestProject.GenusAllQuotientReceivedSpine

@[expose] public section

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
variable {K : Complex2} (T : SpanningTree K) {G H I : Type} [Group G] [Group H]
  (φ : PresGroup (treeRel T) →* G)

theorem bdry2_multiplyCellChain (w : MonoidAlgebra ℤ G) (c : (G × K.F) →₀ ℤ) :
    Comb.bdry2 (cover T φ) (multiplyCellChain c w) =
      multiplyCellChain (Comb.bdry2 (cover T φ) c) w := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp only [map_add, MonoidAlgebra.coeff_add, hw, hz]
  | single g n =>
      erw [multiplyCellChain, Finsupp.linearCombination_single, map_smul,
        DeckAction.faceChains_boundary (deck T φ) g c, multiplyCellChain,
        Finsupp.linearCombination_single]; rfl

theorem markedChainMap_translate (p : I → List (K.E × Bool))
    (g : G) (c : (G × I) →₀ ℤ) :
    markedChainMap T φ p (translateCellChain g c) =
      translateCellChain g (markedChainMap T φ p c) := by
  change markedChainMap T φ p (translateCellChain g c) =
    chain1 ((deck T φ).cellHom g) (markedChainMap T φ p c)
  induction c using Finsupp.induction_linear with
  | zero => simp [translateCellChain]
  | add c d hc hd =>
      simp only [translateCellChain, Finsupp.mapDomain_add, map_add] at hc hd ⊢
      erw [hc, hd]
  | single x n =>
      erw [translateCellChain, Finsupp.mapDomain_single, markedChainMap_single,
        markedChainMap_single, map_smul]
      congr 1
      erw [liftPath_translate]
      exact pathChain_map ((deck T φ).cellHom g) (liftPath T φ (p x.2) x.1)

theorem markedChainMap_multiply (p : I → List (K.E × Bool))
    (w : MonoidAlgebra ℤ G) (c : (G × I) →₀ ℤ) :
    markedChainMap T φ p (multiplyCellChain c w) =
      multiplyCellChain (markedChainMap T φ p c) w := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp only [map_add, MonoidAlgebra.coeff_add, hw, hz]
  | single g n =>
      erw [multiplyCellChain, Finsupp.linearCombination_single, map_smul,
        markedChainMap_translate, multiplyCellChain, Finsupp.linearCombination_single]

theorem markedChainMap_changeGroup (η : G →* H) (p : I → List (K.E × Bool))
    (c : (G × I) →₀ ℤ) :
    chain1 (changeGroup T φ η) (markedChainMap T φ p c) =
      markedChainMap T (η.comp φ) p
        (Finsupp.mapDomain (fun x : G × I => (η x.1, x.2)) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.mapDomain_add, hc, hd]
  | single x n =>
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
    (markedSpineTree q)
    (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)
    (treeMarkedSpineLoop q) (fun i => β (Sum.inr i))
    (receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β)
  intro z
  let βF : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ
        (familyFiniteSpineWordBlock (fun _ : PUnit.{1} => q) (fun _ => u)))) := β
  have hz0 := receivedSpineFaceChain_relative_boundary ρ (fun _ : PUnit.{1} => q)
    (fun _ => u) PUnit.unit βF
  have hwords : familyFiniteSpineWordBlock (fun _ : PUnit.{1} => q) (fun _ => u) =
      finiteSpineWordBlock q u := funext fun ⟨⟩ => rfl
  have hz := hz0 (fun t => by
    with_reducible
      convert hβ t using 1
      apply Finset.sum_congr rfl
      intro m _
      congr 2
      all_goals first
        | exact Subsingleton.elim _ _
        | rfl
        | exact congrArg (substPresF ρ) hwords) z
  exact hz.trans (Finset.sum_congr rfl fun i _ => congrArg (βF (Sum.inr i) * ·)
    (receivedSpineWordReceiver_coeff ρ (fun _ : PUnit.{1} => q)
      (fun _ => u) PUnit.unit (fox z (spinePresentationMarkedWord q i))).symm)

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
  | add w z hw hz => simp only [map_add, MonoidAlgebra.coeff_add, hw, hz]
  | single g n =>
      simp only [ReceivedTree.multiplyCellChain, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, MonoidAlgebra.coeffLinearEquiv_apply,
        MonoidAlgebra.coeff_single, Finsupp.linearCombination_single]
      erw [map_smul]
      refine congrArg (n • ·) ?_
      change Finsupp.mapDomain _ (Finsupp.mapDomain _ c) =
        Finsupp.mapDomain _ (Finsupp.mapDomain _ c)
      erw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
      exact congrArg (Finsupp.mapDomain · c)
        (funext fun x => allQuotientReceivedSpineToQuotient_deckF q ρ u hrho g x.1 x.2)

theorem finiteSpine_relative_class_principal
    (β γ : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (hγ : ∀ z : SpinePresentationGen q,
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
    ∃ a : MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))),
      ∀ m, β m = a * γ m := by
  let F : PresGroup (substPresF ρ (finiteSpineWordBlock q u)) →*
      QuotientMarkingGroup q ρ u := finiteSpineToQuotient ρ q u hrho
  let cβ := receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β
  let cγ := receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit γ
  let c := Finsupp.mapDomain (fun x => (F x.1, x.2)) cβ
  let d := Finsupp.mapDomain (fun x => (F x.1, x.2)) cγ
  let m := Finsupp.mapDomain (fun x => (F x.1, x.2))
    ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i)))
  let n := Finsupp.mapDomain (fun x => (F x.1, x.2))
    ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => γ (Sum.inr i)))
  have hm : allQuotientSurfaceMarkingChains q ρ u m =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
        (allQuotientSurfaceMarkingChains q ρ u n)) w.coeff := by
    simpa only [quotientSurfaceMarkingChains_factor] using hmark
  have hmn : m = ReceivedTree.multiplyCellChain n w :=
    allQuotientSurfaceMarkingChains_injective q ρ u
      (by rwa [← allQuotientSurfaceMarkingChains_multiply] at hm)
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
  have hcorr : quotientCorrectedRelativeChain q ρ u hrho β -
      Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
          (quotientCorrectedRelativeChain q ρ u hrho γ)) w.coeff =
      chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
        (c - ReceivedTree.multiplyCellChain d w) := by
    erw [map_sub, allQuotientReceivedSpineToQuotient_chain2_multiply,
      allQuotientReceivedSpineToQuotient_chain2_changeGroup q ρ u hrho cβ,
      allQuotientReceivedSpineToQuotient_chain2_changeGroup q ρ u hrho cγ]
    simp only [quotientCorrectedRelativeChain, quotientMarkingCorrections_factor]
    exact allQuotientCorrection_cancel_difference q ρ u w m n
      (chain2 (receivedSpineToQuotient q ρ u hrho) cβ)
      (chain2 (receivedSpineToQuotient q ρ u hrho) cγ) hm
  have hcd : c = ReceivedTree.multiplyCellChain d w :=
    sub_eq_zero.mp (allQuotientReceivedSpine_cycle_zero_of_quotient_old_boundary q ρ u hrho _
      hcycle (by simpa only [hcorr] using hrel))
  exact quotientNamedCoefficients_reflect_multiple q ρ u hrho β γ w
    (by convert hcd using 1 <;> rfl) (by simpa only [m, n, F] using hmn)
