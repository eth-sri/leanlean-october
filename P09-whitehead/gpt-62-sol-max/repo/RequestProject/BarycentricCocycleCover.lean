module

public import RequestProject.OrderCocycleCover
public import RequestProject.BarycentricCocycleDescent
public import RequestProject.BarycentricTwoChains
public import RequestProject.ConeAdjPoset
public import RequestProject.UniversalOrderChainBridge

@[expose] public section

/-! The actual barycentric realization of a descended surface cover in the
original universal order cover. Pending final Lean verification. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {P Q G : Type u} [PartialOrder P] [PartialOrder Q] [Group G]
  (f : NeSpx (cmpRel P) → Q) (hf : Monotone f)
  (c : OrdCocycle Q G) (a : Q) (hc : IsConnected (orderCx Q))
  (hm : Function.Bijective (c.monodromy a))

def descendedSurfaceCocycle : OrdCocycle P G :=
  barycentricCocycle (c.comap f hf)

abbrev DescendedSurfaceCover := (descendedSurfaceCocycle f hf c).Cover

def descendedSurfaceProjection : DescendedSurfaceCover f hf c → P :=
  Sigma.fst

theorem descendedSurfaceProjection_isPosetCover :
    IsPosetCover (descendedSurfaceProjection f hf c) :=
  (descendedSurfaceCocycle f hf c).coverProjection_isPosetCover

def descendedSurfaceSimplex
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) : NeSpx (cmpRel P) :=
  barycentricMap (descendedSurfaceProjection f hf c)
    (descendedSurfaceProjection_isPosetCover f hf c).mono σ

theorem descendedSurfaceSimplex_monotone : Monotone (descendedSurfaceSimplex f hf c) :=
  barycentricMap_monotone _ (descendedSurfaceProjection_isPosetCover f hf c).mono

theorem descendedSurfaceSimplex_top
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) :
    (chainMax σ).1 ∈ (descendedSurfaceSimplex f hf c σ).1 :=
  Finset.mem_image.mpr ⟨chainMax σ, chainMax_mem σ, rfl⟩

def barycentricCoverReading
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) : G :=
  (chainMax σ).2 * c.val (f (spx1 (chainMax σ).1))
    (f (descendedSurfaceSimplex f hf c σ))

/-- The top of each lifted simplex fixes the sheet of the whole flag. -/
def barycentricCoverRealization
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) : UOrder Q a :=
  c.pointReading a hc hm (f (descendedSurfaceSimplex f hf c σ))
    (barycentricCoverReading f hf c σ)

theorem barycentricCoverRealization_end
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) :
    uOrderEnd (barycentricCoverRealization f hf c a hc hm σ) =
      f (descendedSurfaceSimplex f hf c σ) :=
  c.pointReading_end a hc hm _ _

theorem barycentricCoverRealization_read
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) :
    c.readVertex a (barycentricCoverRealization f hf c a hc hm σ) =
      barycentricCoverReading f hf c σ :=
  c.pointReading_read a hc hm _ _

theorem barycentricCoverRealization_monotone :
    Monotone (barycentricCoverRealization f hf c a hc hm) := by
  intro σ τ hστ
  have htop := chainMax_monotone hστ
  have hσ : spx1 (chainMax σ).1 ≤ descendedSurfaceSimplex f hf c σ := by
    intro p hp
    simp only [spx1_val, Finset.mem_singleton] at hp
    subst p
    exact descendedSurfaceSimplex_top f hf c σ
  have hτ  :=
    descendedSurfaceSimplex_monotone f hf c hστ
  have hmσ  :=
    hτ (descendedSurfaceSimplex_top f hf c σ)
  have hread := edgeHop_read_via (c.comap f hf) htop.1
    (descendedSurfaceSimplex f hf c τ) hmσ (descendedSurfaceSimplex_top f hf c τ)
  have hval : (descendedSurfaceCocycle f hf c).val (chainMax σ).1 (chainMax τ).1 =
      c.val (f (spx1 (chainMax σ).1)) (f (descendedSurfaceSimplex f hf c τ)) *
        (c.val (f (spx1 (chainMax τ).1)) (f (descendedSurfaceSimplex f hf c τ)))⁻¹ := by
    exact (barycentricCocycle_val (c.comap f hf) htop.1).trans hread
  apply c.pointReading_le a hc hm (hf hτ)
  change ((chainMax σ).2 * c.val (f (spx1 (chainMax σ).1))
      (f (descendedSurfaceSimplex f hf c σ))) *
      c.val (f (descendedSurfaceSimplex f hf c σ)) (f (descendedSurfaceSimplex f hf c τ)) =
    (chainMax τ).2 * c.val (f (spx1 (chainMax τ).1))
      (f (descendedSurfaceSimplex f hf c τ))
  calc
    _ = (chainMax σ).2 * c.val (f (spx1 (chainMax σ).1))
        (f (descendedSurfaceSimplex f hf c τ)) := by rw [mul_assoc, c.comp (hf hσ) (hf hτ)]
    _ = ((chainMax σ).2 *
        (descendedSurfaceCocycle f hf c).val (chainMax σ).1 (chainMax τ).1) *
        c.val (f (spx1 (chainMax τ).1)) (f (descendedSurfaceSimplex f hf c τ)) := by
      rw [hval]
      group
    _ = _ := by
      have hsheet := htop.2
      change (chainMax σ).2 * (descendedSurfaceCocycle f hf c).val
        (chainMax σ).1 (chainMax τ).1 = (chainMax τ).2 at hsheet
      rw [hsheet]

end FiniteChains.Davis
