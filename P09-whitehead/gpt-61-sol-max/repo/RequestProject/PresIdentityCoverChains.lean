import Mathlib.Tactic

import RequestProject.PresCoverRelativeConeCylinder
import RequestProject.PresCoverConeCircleProjection
import RequestProject.StrictNormalizedOneMaps

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000

namespace FiniteChains.PresModel.IdentityChains
open Comb Comb.StrictNormalized
variable {α J : Type u} (w : J → List (α × Bool))

def cover : IsPosetCover (id : PresPos w → PresPos w) :=
  ⟨monotone_id, Function.surjective_id,
    fun _ b h => ⟨b, ⟨h, rfl⟩, fun _ hz => hz.2⟩,
    fun _ b h => ⟨b, ⟨h, rfl⟩, fun _ hz => hz.2⟩⟩

/-- In the identity cover the actual lifted-apex labels are exactly the original labels. -/
def relatorEquiv : J ≃ PresCoverRelator w id where
  toFun j := ⟨(apexOf w j, j), rfl⟩
  invFun p := p.1.2
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext p.2.symm rfl)

abbrev Base := {p : PresPos w // p ∈ coneAdjBaseSet (S := circSet w)}

noncomputable def baseIso : Base w ≃o CylBase w := coneAdjBaseOrderIso

noncomputable def baseProjection  :=
  chain1 (strictOrderCxMap (baseIso w) (baseIso w).strictMono)

theorem baseProjection_injective : Function.Injective (baseProjection w) :=
  Finsupp.mapDomain_injective
    (strictOrderCxMap_onE_injective (baseIso w) (baseIso w).strictMono (baseIso w).injective)

abbrev baseIso_collapse (p : Base w)  :=
  FiniteChains.PresModel.cylinderCoverCollapse_projection w
    (FiniteChains.Comb.coneAdjCoverBaseEnd_isPosetCover id (FiniteChains.PresModel.IdentityChains.cover w)) p

variable (c : StrictOrdEdge (Base w) →₀ ℤ)
abbrev baseProjection_collapse   :=
  FiniteChains.Comb.StrictNormalized.mapOne_semiconj (⇑(FiniteChains.PresModel.IdentityChains.baseIso w))
    (OrderIso.strictMono (FiniteChains.PresModel.IdentityChains.baseIso w))
    (FiniteChains.PresModel.presCoverCylinderCollapse w id (FiniteChains.PresModel.IdentityChains.cover w))
    (FiniteChains.PresModel.presCoverCylinderCollapse_monotone w id (FiniteChains.PresModel.IdentityChains.cover w))
    (FiniteChains.Comb.cylCollapse (FiniteChains.PresModel.aHom w))
    (FiniteChains.Comb.cylCollapse_monotone (FiniteChains.PresModel.aHom w))
    (FiniteChains.PresModel.IdentityChains.baseIso_collapse w) c

variable (j : J)
def circleIntoCylinder  : RelatorCircle w j → CylBase w :=
  fun x => cylOuter (aHom w) x.val

theorem circleIntoCylinder_strictMono  : StrictMono (circleIntoCylinder w j) := by
  solve_by_elim []

noncomputable def cylinderBoundary   :=
  mapOne (circleIntoCylinder w j) (circleIntoCylinder_strictMono w j).monotone
    (relatorCircleFundamentalChain w j)

theorem baseIso_circle (p : PresCoverRelator w id) (x : RelatorCircle w p.1.2) :
    baseIso w (presCoverCircleCylinderInclusion w id (cover w) p x) =
      circleIntoCylinder w p.1.2 x := by
  apply (Sum.inl_injective : Function.Injective (Sum.inl : CylBase w → PresPos w))
  exact (coneAdjCoverBaseEnd_spec id
    (presCoverCircleCylinderInclusion w id (cover w) p x)).trans
      (presCoverConeCircleOrderIso_symm_projection w id (cover w) p.1.1 p.1.2 p.2 x)

theorem baseProjection_relatorBoundary (p : PresCoverRelator w id) :
    baseProjection w (presCoverCylinderRelatorBoundary w id (cover w) p) =
      cylinderBoundary w p.1.2 := by
  unfold FiniteChains.PresModel.presCoverCylinderRelatorBoundary
  rw (config := { transparency := .default }) [← mapOne_strict (baseIso w) (baseIso w).strictMono,
    ← mapOne_strict _ (presCoverCircleCylinderInclusion_strictMono w id (cover w) p)]
  erw [mapOne_comp (presCoverCircleCylinderInclusion w id (cover w) p)
    (presCoverCircleCylinderInclusion_strictMono w id (cover w) p).monotone
    (baseIso w) (baseIso w).monotone (relatorCircleFundamentalChain w p.1.2)]
  have he : baseIso w ∘ presCoverCircleCylinderInclusion w id (cover w) p =
      circleIntoCylinder w p.1.2 := funext (baseIso_circle w p)
  simp [*]
  rfl

/-- The actual cylinder retraction, in literal rose-edge coordinates. -/
noncomputable def roseProjection  :=
  (mapOne (cylRetr (aHom w)) (cylRetr_monotone (aHom w))).comp (baseProjection w)

theorem baseProjection_collapse_eq  :
    baseProjection w (normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c) =
      mapOne (cylIn (aHom w)) (cylIn_monotone (aHom w)) (roseProjection w c) := by
  rw (config := { transparency := .default }) [baseProjection_collapse]
  dsimp [FiniteChains.PresModel.IdentityChains.roseProjection]
  rw [mapOne_comp]; rfl

theorem collapsed_eq_zero_of_roseProjection_eq_zero
     (hc : roseProjection w c = 0) :
    normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c = 0 := by
  apply baseProjection_injective w
  rw (config := { transparency := .default }) [baseProjection_collapse_eq, hc, map_zero]

theorem roseProjection_collapse  :
    roseProjection w (normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c) = roseProjection w c := by
  change mapOne (cylRetr (aHom w)) _ (baseProjection w _) = _
  rw  [baseProjection_collapse_eq, mapOne_comp]
  change mapOne id monotone_id (roseProjection w c) = _
  exact mapOne_id _

def roseIntoBase (x : Rose α) : Base w :=
  ⟨ConeAdj.inc (cylIn (aHom w) x), ⟨cylIn (aHom w) x, rfl⟩⟩

theorem roseIntoBase_strictMono : StrictMono (roseIntoBase w) := by
  solve_by_elim []

abbrev baseIso_roseIntoBase (x : Rose α)  :=
  OrderIso.apply_symm_apply (FiniteChains.PresModel.IdentityChains.baseIso w)
    (FiniteChains.Comb.cylIn (FiniteChains.PresModel.aHom w) x)

noncomputable def roseInclusion  :=
  chain1 (strictOrderCxMap (roseIntoBase w) (roseIntoBase_strictMono w))

theorem roseProjection_inclusion (c : StrictOrdEdge (Rose α) →₀ ℤ) :
    roseProjection w (roseInclusion w c) = c := by
  dsimp [FiniteChains.PresModel.IdentityChains.roseProjection]
  rw (config := { transparency := .default }) [← mapOne_strict (baseIso w) (baseIso w).strictMono,
    ← mapOne_strict (roseIntoBase w) (roseIntoBase_strictMono w), mapOne_comp, mapOne_comp]
  have he : (cylRetr (aHom w) ∘ baseIso w) ∘ roseIntoBase w = id := by
    funext x
    exact congrArg (cylRetr (aHom w)) (baseIso_roseIntoBase w x)
  simpa [he] using (mapOne_id c)

end FiniteChains.PresModel.IdentityChains
