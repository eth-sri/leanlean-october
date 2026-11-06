import RequestProject.OrderCocycleCover
import RequestProject.BarycentricCocycleDescent
import RequestProject.BarycentricTwoChains
import RequestProject.ConeAdjPoset
import RequestProject.UniversalOrderChainBridge


/-! The actual barycentric realization of a descended surface cover in the
original universal order cover. Pending final Lean verification. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Davis
open Comb
variable {P Q G : Type u} [PartialOrder P] [PartialOrder Q] [Group G]
  (f : NeSpx (cmpRel P) → Q) (hf : Monotone f)
  (c : OrdCocycle Q G) (a : Q) (hc : IsConnected (orderCx Q))
  (hm : Function.Bijective (c.monodromy a))

def descendedSurfaceCocycle :=
  barycentricCocycle (c.comap f hf)

abbrev DescendedSurfaceCover := (descendedSurfaceCocycle f hf c).Cover

def descendedSurfaceProjection : DescendedSurfaceCover f hf c → P :=
  OrdCocycle.Cover.point

theorem descendedSurfaceProjection_isPosetCover :
    IsPosetCover (descendedSurfaceProjection f hf c) :=
  (descendedSurfaceCocycle f hf c).coverProjection_isPosetCover

def descendedSurfaceSimplex
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) :=
  barycentricMap _
    (descendedSurfaceProjection_isPosetCover f hf c).mono σ

theorem descendedSurfaceSimplex_monotone : Monotone (descendedSurfaceSimplex f hf c) :=
  barycentricMap_monotone _ (descendedSurfaceProjection_isPosetCover f hf c).mono

theorem descendedSurfaceSimplex_top
    σ :
    (chainMax σ).point ∈ (descendedSurfaceSimplex f hf c σ).1 :=
  Finset.mem_image.mpr ⟨chainMax σ, chainMax_mem σ, rfl⟩

def barycentricCoverReading
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) :=
  (chainMax σ).sheet * c.val (f (spx1 (chainMax σ).point))
    (f (descendedSurfaceSimplex f hf c σ))

/-- The top of each lifted simplex fixes the sheet of the whole flag. -/
def barycentricCoverRealization
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) :=
  c.pointReading a hc hm (f (descendedSurfaceSimplex f hf c σ))
    (barycentricCoverReading f hf c σ)

theorem barycentricCoverRealization_end
    σ :
    uOrderEnd (barycentricCoverRealization f hf c a hc hm σ) =
      f (descendedSurfaceSimplex f hf c σ) :=
  c.pointReading_end a hc hm _ _

theorem barycentricCoverRealization_read
    σ :
    c.readVertex a (barycentricCoverRealization f hf c a hc hm σ) =
      barycentricCoverReading f hf c σ :=
  c.pointReading_read a hc hm _ _

theorem barycentricCoverRealization_monotone :
    Monotone (barycentricCoverRealization f hf c a hc hm) := by
  intro σ τ hστ
  have htop := chainMax_monotone hστ
  have hσ : spx1 (chainMax σ).point ≤ descendedSurfaceSimplex f hf c σ := by
    intro p hp
    simp [spx1_val, Finset.mem_singleton] at hp
    subst p
    exact descendedSurfaceSimplex_top f hf c σ
  have hτ : descendedSurfaceSimplex f hf c σ ≤ descendedSurfaceSimplex f hf c τ :=
    descendedSurfaceSimplex_monotone f hf c hστ
  have hmσ : (chainMax σ).point ∈ (descendedSurfaceSimplex f hf c τ).1 :=
    by tauto
  have hread := edgeHop_read_via (c.comap f hf) htop.1
    _ hmσ (descendedSurfaceSimplex_top f hf c τ)
  have hval : (descendedSurfaceCocycle f hf c).val (chainMax σ).point (chainMax τ).point =
      c.val (f (spx1 (chainMax σ).point)) (f (descendedSurfaceSimplex f hf c τ)) *
        (c.val (f (spx1 (chainMax τ).point)) (f (descendedSurfaceSimplex f hf c τ)))⁻¹ := (barycentricCocycle_val _ htop.1).trans hread
  apply c.pointReading_le a hc hm (hf hτ)
  change ((chainMax σ).sheet * c.val (f (spx1 (chainMax σ).point))
      (f (descendedSurfaceSimplex f hf c σ))) *
      c.val (f (descendedSurfaceSimplex f hf c σ)) (f (descendedSurfaceSimplex f hf c τ)) =
    (chainMax τ).sheet * c.val (f (spx1 (chainMax τ).point))
      (f (descendedSurfaceSimplex f hf c τ))
  calc
    _ = (chainMax σ).sheet * c.val (f (spx1 (chainMax σ).point))
        (f (descendedSurfaceSimplex f hf c τ)) := by rw [mul_assoc, c.comp (hf hσ) (hf hτ)]
    _ = ((chainMax σ).sheet *
        (descendedSurfaceCocycle f hf c).val (chainMax σ).point (chainMax τ).point) *
        c.val (f (spx1 (chainMax τ).point)) (f (descendedSurfaceSimplex f hf c τ)) := by
      rw [hval]
      group
    _ = _ := by rw [htop.2]
