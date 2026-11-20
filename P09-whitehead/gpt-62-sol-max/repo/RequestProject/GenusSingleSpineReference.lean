module

public import RequestProject.GenusNormalizedSpineBaseChange

@[expose] public section

/-! The fixed normalized reference in one actual substituted spine, and its
compatibility with the arbitrary-family reference. Awaiting Lean verification. -/
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

def singleFiniteSpineReference : NamedSpineRel q →₀
    MonoidAlgebra ℤ (SpineReplacementGroup ρ q u) :=
  finiteSpineFamilyFilling ρ (fun _  => q) (fun _ => u) PUnit.unit

theorem singleFiniteSpineReference_internal
    (hrho : IsSpineRelator ρ q u)
    (z : SpinePresentationGen q) :
    (∑ m, singleFiniteSpineReference ρ q u m *
      foxMatrixPres (spineReplacementPres ρ q u)
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0 := by
  letI : DecidableEq PUnit.{1} := Classical.decEq _
  have h := (finiteSpineFamilyFilling_isFilling ρ
    (fun _  => q) (fun _ => u) (fun s => by cases s; exact hrho)).internal
      PUnit.unit z
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)] at h
  exact h

theorem singleFiniteSpineReference_faceChain :
    singleReceivedSpineFaceChain q ρ u
      (singleFiniteSpineReference ρ q u) =
    Finsupp.mapDomain
      (fun x : PresGroup (namedSpinePresentation q) × SpinePresentationRel q =>
        (familySpineHom ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit x.1, x.2))
      (normalizedSpineReference q) :=
  finiteSpineFamilyFilling_faceChain ρ (fun _  => q) (fun _ => u) PUnit.unit

theorem singleFiniteSpineReference_markingChain :
    singleReceivedSpineMarkingChain q ρ u (singleFiniteSpineReference ρ q u) =
    Finsupp.mapDomain
      (fun x : PresGroup (namedSpinePresentation q) × (Fin q × Bool) =>
        (familySpineHom ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit x.1, x.2))
      (universalReferenceMarkingCoefficients q) :=
  finiteSpineFamilyFilling_markingChain ρ (fun _  => q) (fun _ => u) PUnit.unit



end FiniteChains.Davis.Genus
