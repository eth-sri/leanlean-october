import RequestProject.GenusQuotientRelativeCorrection
import RequestProject.UniversalOrderChainBridge
import RequestProject.Tac
noncomputable section


/-! The actual quotient correction stays over the old subposet, before and after
deck translation and conversion to nerve chains. Pending final Lean verification.
-/

bwd

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- Actual cover faces whose projected triangle lies in the chosen subposet. -/
def supportedUniversalFaces (S : P → Prop) :
    Submodule ℤ (UF (orderCx P) a →₀ ℤ) :=
  Finsupp.supported ℤ ℤ {t | t.1.2 ∈ ordTriOn S}

theorem mem_supportedUniversalFaces_iff S
    (c : UF (orderCx P) a →₀ ℤ) :
    c ∈ supportedUniversalFaces S ↔ ∀ t ∈ c.support, t.1.2 ∈ ordTriOn S := Iff.rfl

theorem chain2_mem_supportedUniversalFaces
    S (f : Hom K (uCover (orderCx P) a))
    (hf : ∀ t, (f.onF t).1.2 ∈ ordTriOn S) c :
    chain2 f c ∈ supportedUniversalFaces S := by
  apply Finsupp.supported_comap_lmapDomain ℤ ℤ f.onF {t | t.1.2 ∈ ordTriOn S}
  simp_all

/-- Deck translation changes the sheet and leaves every projected face unchanged. -/
theorem deck_mem_supportedUniversalFaces S
    g c
    (hc : c ∈ supportedUniversalFaces S) :
    (univDeck (orderCx P) a).faceChains g c ∈ supportedUniversalFaces S := by
  apply Finsupp.supported_comap_lmapDomain ℤ ℤ _ _
  exact hc

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
open scoped Classical
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))


theorem receivedSpineToQuotient_chain_old
    c :
    chain2 (receivedSpineToQuotient q ρ u hrho) c ∈ supportedUniversalFaces InQOld :=
  chain2_mem_supportedUniversalFaces InQOld _
    (by tauto) c

theorem oldCoverToNamedQuotient_face_old
    t :
    ((oldCoverToNamedQuotient q ρ u).onF t).1.2 ∈ ordTriOn InQOld := by
  tauto

theorem oldCoverToNamedQuotient_chain_old
    c :
    chain2 (oldCoverToNamedQuotient q ρ u) c ∈ supportedUniversalFaces InQOld :=
  chain2_mem_supportedUniversalFaces InQOld _
    (oldCoverToNamedQuotient_face_old q ρ u) c

theorem quotientMarkingCorrection_old
    g i :
    quotientMarkingCorrection q ρ u hrho g i ∈ supportedUniversalFaces InQOld :=
  deck_mem_supportedUniversalFaces InQOld _
    _
    (oldCoverToNamedQuotient_chain_old q ρ u _)

theorem quotientMarkingCorrections_old
    c :
    quotientMarkingCorrections q ρ u hrho c ∈ supportedUniversalFaces InQOld := by
  lin_ind c x n using aesop =>
      rwd [quotientMarkingCorrections, Finsupp.linearCombination_single]
      exact Submodule.smul_mem _ n (quotientMarkingCorrection_old q ρ u hrho x.1 x.2)

/-- Both the received faces and the explicit marking correction are supported on old faces. -/
theorem quotientCorrectedRelativeChain_old
    β :
    quotientCorrectedRelativeChain q ρ u hrho β ∈ supportedUniversalFaces InQOld :=
  Submodule.sub_mem _
    (receivedSpineToQuotient_chain_old q ρ u hrho _)
    (quotientMarkingCorrections_old q ρ u hrho _)

theorem quotientCorrectedRelativeChain_face_support
    β :
    ∀ t ∈ (quotientCorrectedRelativeChain q ρ u hrho β).support,
      t.1.2 ∈ ordTriOn InQOld :=
  (mem_supportedUniversalFaces_iff InQOld _).mp
    (quotientCorrectedRelativeChain_old q ρ u hrho β)

def quotientCorrectedRelativeNerveChain
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u)))) :=
  universalNerveChain2 (quotientCorrectedRelativeChain q ρ u hrho β)

theorem quotientCorrectedRelativeNerveChain_boundary
    β
    (hβ : ∀ z,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    Nerve.bdry (quotientCorrectedRelativeNerveChain q ρ u hrho β) =
      universalNerveChain1 (quotientSurfaceMarkingChains q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i)))) := by
  simp [quotientCorrectedRelativeNerveChain, universalNerveChain2_bdry, quotientCorrectedRelativeChain_boundary q ρ u hrho β hβ]
