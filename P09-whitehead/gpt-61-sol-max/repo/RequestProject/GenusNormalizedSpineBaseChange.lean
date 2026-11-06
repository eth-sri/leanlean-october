import Mathlib.Tactic

import RequestProject.GenusSpineFamilyGeneration
import RequestProject.GenusReceivedSpineCover

/-! Exact sheet and marking coordinates of the normalized reference after
arbitrary substitutions. Pending final Lean verification. -/
noncomputable section


set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.ReceivedTree
variable {G H E : Type u} [Group G] [Group H] (φ : G →* H)

/-- Changing the receiving group retains each cell coordinate and pushes
forward its full group-ring coefficient, including coincident sheets. -/
theorem cellCoefficient_mapSheets (e : E) (c : (G × E) →₀ ℤ) :
    cellCoefficient e (Finsupp.mapDomain (fun x : G × E => (φ x.1, x.2)) c) =
      MonoidAlgebra.mapDomainRingHom ℤ φ (cellCoefficient e c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all [Finsupp.mapDomain_add, map_add]
  | single x n =>
    aesop (add simp [FiniteChains.Comb.ReceivedTree.cellCoefficient_single])

theorem cellCoordinates_symm_mapSheets [Fintype E] (v : E → MonoidAlgebra ℤ G) :
    (cellCoordinates E).symm (fun e => MonoidAlgebra.mapDomainRingHom ℤ φ (v e)) =
      Finsupp.mapDomain (fun x : G × E => (φ x.1, x.2)) ((cellCoordinates E).symm v) := by
  apply (cellCoordinates E).injective
  funext e
  rw  [LinearEquiv.apply_symm_apply, ← cellCoefficient_eq_coordinates,
    cellCoefficient_mapSheets, cellCoefficient_coordinates_symm]

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb BlockFamily
variable {α Jr S : Type} (ρ : Jr ⊕ S → FreeGroup α)
  (q : S → ℕ) [∀ s, NeZero (q s)] (u : ∀ s, Fin (q s) × Bool → FreeGroup α)

variable (s : S)
theorem finiteSpineFamilyFilling_named_coeff  (m : NamedSpineRel (q s)) :
    finiteSpineFamilyFilling ρ q u s m =
      MonoidAlgebra.mapDomainRingHom ℤ (familySpineHom ρ q u s)
        (normalizedNamedSpineVector (q s) (normalizedSpineReference (q s)) m) := by
  change MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFamilyMarkedHom ρ q u s)
    (markedSpineFilling (q s) m) = _
  rw  [markedSpineFilling_named_coeff, BlockMor.mapDomainRingHom_comp']
  rfl

theorem finiteSpineFamilyFilling_faceChain  :
    receivedSpineFaceChain ρ q u s (finiteSpineFamilyFilling ρ q u s) =
      Finsupp.mapDomain
        (fun x : PresGroup (namedSpinePresentation (q s)) × SpinePresentationRel (q s) =>
          (familySpineHom ρ q u s x.1, x.2)) (normalizedSpineReference (q s)) := by
  apply (ReceivedTree.cellCoordinates (SpinePresentationRel (q s))).injective
  funext j
  rw  [← ReceivedTree.cellCoefficient_eq_coordinates,
    receivedSpineFaceChain_coefficient, ← ReceivedTree.cellCoefficient_eq_coordinates,
    ReceivedTree.cellCoefficient_mapSheets, finiteSpineFamilyFilling_named_coeff]
  rfl

theorem finiteSpineFamilyFilling_markingChain  :
    (ReceivedTree.cellCoordinates (Fin (q s) × Bool)).symm
      (fun i => finiteSpineFamilyFilling ρ q u s (Sum.inr i)) =
      Finsupp.mapDomain
        (fun x : PresGroup (namedSpinePresentation (q s)) × (Fin (q s) × Bool) =>
          (familySpineHom ρ q u s x.1, x.2)) (universalReferenceMarkingCoefficients (q s)) := by
  simp [finiteSpineFamilyFilling_named_coeff]
  exact ReceivedTree.cellCoordinates_symm_mapSheets (familySpineHom ρ q u s)
    (namedSpineSurfaceMarkingCoefficient (q s))

end FiniteChains.Davis.Genus
