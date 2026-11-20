module

public import RequestProject.PresCoverRelativeConeCylinder
public import RequestProject.StrictNormalizedOneMaps

@[expose] public section

noncomputable section

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
    (strictOrderCxMap_onE_injective (baseIso w) (baseIso w).strictMono (baseIso w).injective)

theorem baseIso_collapse (p : Base w) :
    baseIso w (presCoverCylinderCollapse w id (cover w) p) =
      cylCollapse (aHom w) (baseIso w p) :=
  cylinderCoverCollapse_projection w (coneAdjCoverBaseEnd_isPosetCover id (cover w)) p

theorem baseProjection_collapse (c : StrictOrdEdge (Base w) →₀ ℤ) :
    baseProjection w (normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c) =
      normalizedStrictChain1 (cylCollapse (aHom w)) (cylCollapse_monotone (aHom w))
        (baseProjection w c) :=
  mapOne_semiconj (baseIso w) (baseIso w).strictMono _ _ _ _ (baseIso_collapse w) c

variable (j : J)

def circleIntoCylinder : RelatorCircle w j → CylBase w :=
  fun x => cylOuter (aHom w) x.val

theorem circleIntoCylinder_strictMono : StrictMono (circleIntoCylinder w j) := by
  solve_by_elim

def cylinderBoundary :=
  mapOne (circleIntoCylinder w j) (circleIntoCylinder_strictMono w j).monotone
    (relatorCircleFundamentalChain w j)

variable (p : PresCoverRelator w id)

theorem baseIso_circle (x : RelatorCircle w p.1.2) :
    baseIso w (presCoverCircleCylinderInclusion w id (cover w) p x) =
      circleIntoCylinder w p.1.2 x := by
  apply (Sum.inl_injective : Function.Injective (Sum.inl : CylBase w → PresPos w))
  exact (coneAdjCoverBaseEnd_spec id
    (presCoverCircleCylinderInclusion w id (cover w) p x)).trans
      (presCoverConeCircleOrderIso_symm_projection w id (cover w) p.1.1 p.1.2 p.2 x)

theorem baseProjection_relatorBoundary :
    baseProjection w (presCoverCylinderRelatorBoundary w id (cover w) p) =
      cylinderBoundary w p.1.2 := by
  change chain1 (strictOrderCxMap (baseIso w) (baseIso w).strictMono)
    (chain1 (strictOrderCxMap (presCoverCircleCylinderInclusion w id (cover w) p)
      (presCoverCircleCylinderInclusion_strictMono w id (cover w) p)) _) = _
  erw [← mapOne_strict (baseIso w) (baseIso w).strictMono,
    ← mapOne_strict _ (presCoverCircleCylinderInclusion_strictMono w id (cover w) p)]
  erw [mapOne_comp (presCoverCircleCylinderInclusion w id (cover w) p)
    (presCoverCircleCylinderInclusion_strictMono w id (cover w) p).monotone
    (baseIso w) (baseIso w).monotone (relatorCircleFundamentalChain w p.1.2)]
  have he : baseIso w ∘ presCoverCircleCylinderInclusion w id (cover w) p =
      circleIntoCylinder w p.1.2 := funext (baseIso_circle w p)
  aesop

/-- The actual cylinder retraction, in literal rose-edge coordinates. -/
def roseProjection :=
  (mapOne (cylRetr (aHom w)) (cylRetr_monotone (aHom w))).comp (baseProjection w)

variable (c : StrictOrdEdge (Base w) →₀ ℤ)

theorem baseProjection_collapse_eq :
    baseProjection w (normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c) =
      mapOne (cylIn (aHom w)) (cylIn_monotone (aHom w)) (roseProjection w c) := by
  erw [baseProjection_collapse]
  change mapOne (cylCollapse (aHom w)) _ (baseProjection w c) =
    mapOne (cylIn (aHom w)) _ (mapOne (cylRetr (aHom w)) _ (baseProjection w c))
  rw [mapOne_comp]; rfl

theorem collapsed_eq_zero_of_roseProjection_eq_zero (hc : roseProjection w c = 0) :
    normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c = 0 := by
  apply baseProjection_injective w
  erw [baseProjection_collapse_eq, hc, map_zero]

theorem roseProjection_collapse :
    roseProjection w (normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c) = roseProjection w c := by
  change mapOne (cylRetr (aHom w)) _ (baseProjection w _) = _
  erw [baseProjection_collapse_eq, mapOne_comp]
  apply mapOne_id

def roseIntoBase (x : Rose α) : Base w :=
  ⟨ConeAdj.inc (cylIn (aHom w) x), ⟨cylIn (aHom w) x, rfl⟩⟩

theorem roseIntoBase_strictMono : StrictMono (roseIntoBase w) := by
  solve_by_elim

theorem baseIso_roseIntoBase (x : Rose α) : baseIso w (roseIntoBase w x) = cylIn (aHom w) x :=
  (baseIso w).apply_symm_apply (cylIn (aHom w) x)

def roseInclusion :
    (StrictOrdEdge (Rose α) →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (Base w) →₀ ℤ) :=
  chain1 (strictOrderCxMap (roseIntoBase w) (roseIntoBase_strictMono w))

theorem roseProjection_inclusion (c : StrictOrdEdge (Rose α) →₀ ℤ) :
    roseProjection w (roseInclusion w c) = c := by
  change mapOne (cylRetr (aHom w)) _
    (chain1 (strictOrderCxMap (baseIso w) (baseIso w).strictMono)
      (chain1 (strictOrderCxMap (roseIntoBase w) (roseIntoBase_strictMono w)) c)) = c
  erw [← mapOne_strict (baseIso w) (baseIso w).strictMono,
    ← mapOne_strict (roseIntoBase w) (roseIntoBase_strictMono w), mapOne_comp, mapOne_comp]
  have he : (cylRetr (aHom w) ∘ baseIso w) ∘ roseIntoBase w = id := by
    funext x
    simp_all [baseIso_roseIntoBase]
  grind [mapOne_id]

end FiniteChains.PresModel.IdentityChains
