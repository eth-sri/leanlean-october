import RequestProject.PresCoverRelativeConeCylinder
import RequestProject.PresCoverConeCircleProjection
import RequestProject.StrictNormalizedOneMaps
import RequestProject.Tac
noncomputable section


bwd

set_option maxHeartbeats 800000

namespace FiniteChains.PresModel.IdentityChains
open Comb Comb.StrictNormalized
universe u
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

def baseIso : Base w ≃o CylBase w := coneAdjBaseOrderIso

def baseProjection :
    (StrictOrdEdge (Base w) →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (CylBase w) →₀ ℤ) :=
  chain1 (strictOrderCxMap (baseIso w) (baseIso w).strictMono)

theorem baseProjection_injective : Function.Injective (baseProjection w) :=
  Finsupp.mapDomain_injective
    (strictOrderCxMap_onE_injective _ _ (baseIso w).injective)

theorem baseIso_collapse (p : Base w) :
    baseIso w (presCoverCylinderCollapse w id (cover w) p) =
      cylCollapse (aHom w) (baseIso w p) :=
  cylinderCoverCollapse_projection w _ p

theorem baseProjection_collapse (c : StrictOrdEdge (Base w) →₀ ℤ) :
    baseProjection w (normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c) =
      normalizedStrictChain1 (cylCollapse (aHom w)) (cylCollapse_monotone (aHom w))
        (baseProjection w c) :=
  mapOne_semiconj _ _ _ _ _ _ (baseIso_collapse w) c

def circleIntoCylinder j : RelatorCircle w j → CylBase w :=
  fun x => cylOuter _ x.val

theorem circleIntoCylinder_strictMono j : StrictMono (circleIntoCylinder w j) := by
  tauto

def cylinderBoundary (j : J) :=
  mapOne _ (circleIntoCylinder_strictMono w j).monotone
    (relatorCircleFundamentalChain w j)

theorem baseIso_circle p x :
    baseIso w (presCoverCircleCylinderInclusion w id (cover w) p x) =
      circleIntoCylinder w p.1.2 x := by
  apply Sum.inl_injective
  exact (coneAdjCoverBaseEnd_spec id
    (presCoverCircleCylinderInclusion w id (cover w) p x)).trans
      (presCoverConeCircleOrderIso_symm_projection w id (cover w) p.1.1 p.1.2 p.2 x)

theorem baseProjection_relatorBoundary p :
    baseProjection w (presCoverCylinderRelatorBoundary w id (cover w) p) =
      cylinderBoundary w p.1.2 := by
  change chain1 (strictOrderCxMap _ (baseIso w).strictMono)
    (chain1 (strictOrderCxMap _
      (presCoverCircleCylinderInclusion_strictMono w id _ p)) _) = _
  rwd [← mapOne_strict _ _,
    ← mapOne_strict _ _]
  erw [mapOne_comp _
    _
    _ _ _]
  have he : baseIso w ∘ presCoverCircleCylinderInclusion w id (cover w) p =
      circleIntoCylinder w p.1.2 := funext (baseIso_circle w p)
  aesop

/-- The actual cylinder retraction, in literal rose-edge coordinates. -/
def roseProjection :=
  (mapOne _ (cylRetr_monotone (aHom w))).comp (baseProjection w)

theorem baseProjection_collapse_eq (c : StrictOrdEdge (Base w) →₀ ℤ) :
    baseProjection w (normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c) =
      mapOne (cylIn (aHom w)) (cylIn_monotone (aHom w)) (roseProjection w c) := by
  rwd [baseProjection_collapse]
  change mapOne (cylCollapse _) _ (baseProjection w c) =
    mapOne (cylIn _) _ (mapOne (cylRetr _) _ (baseProjection w c))
  rw [mapOne_comp]; rfl

theorem collapsed_eq_zero_of_roseProjection_eq_zero
    c (hc : roseProjection w c = 0) :
    normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c = 0 := by
  apply baseProjection_injective w
  rwd [baseProjection_collapse_eq, hc, map_zero]

theorem roseProjection_collapse (c : StrictOrdEdge (Base w) →₀ ℤ) :
    roseProjection w (normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c) = roseProjection w c := by
  change mapOne (cylRetr _) _ (baseProjection w _) = _
  rwd [baseProjection_collapse_eq, mapOne_comp]
  exact mapOne_id _

def roseIntoBase (x : Rose α) : Base w :=
  ⟨ConeAdj.inc (cylIn _ x), by tauto⟩

theorem roseIntoBase_strictMono : StrictMono (roseIntoBase w) := by
  tauto

theorem baseIso_roseIntoBase x : baseIso w (roseIntoBase w x) = cylIn (aHom w) x :=
  (baseIso w).apply_symm_apply _

def roseInclusion :
    (StrictOrdEdge (Rose α) →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (Base w) →₀ ℤ) :=
  chain1 (strictOrderCxMap _ (roseIntoBase_strictMono w))

theorem roseProjection_inclusion c :
    roseProjection w (roseInclusion w c) = c := by
  change mapOne (cylRetr _) _
    (chain1 (strictOrderCxMap _ (baseIso w).strictMono)
      (chain1 (strictOrderCxMap _ (roseIntoBase_strictMono w)) c)) = c
  rwd [← mapOne_strict _ _,
    ← mapOne_strict _ _, mapOne_comp, mapOne_comp]
  have he : (cylRetr _ ∘ baseIso w) ∘ roseIntoBase w = id := by
    funext x
    exact congrArg _ (baseIso_roseIntoBase w x)
  simpa [he] using (mapOne_id c)
