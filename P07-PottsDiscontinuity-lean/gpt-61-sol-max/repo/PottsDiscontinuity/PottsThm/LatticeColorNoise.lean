module
public import Mathlib

public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Set Topology


noncomputable section

abbrev LatticeVertex := ℤ × ℤ

def latticeShiftEquiv (a : LatticeVertex) : LatticeVertex ≃ LatticeVertex where
  toFun x := x + a
  invFun x := x - a
  left_inv x := by simp
  right_inv x := by simp

theorem eventually_latticeShift_disjoint (F G : Finset LatticeVertex) :
    ∀ᶠ a : LatticeVertex in cofinite,
      Disjoint F (G.map (latticeShiftEquiv a).symm.toEmbedding) := by
  
  
  filter_upwards [((G ×ˢ F).image fun p => p.1 - p.2).eventually_cofinite_notMem] with a ha
  apply Finset.disjoint_left.mpr
  intro x hxF hxshift
  obtain ⟨y, hyG, hyx⟩ := Finset.mem_map.mp hxshift
  
  exact (ha (by
               apply Finset.mem_image.mpr
               refine ⟨(y, x), Finset.mem_product.mpr ⟨hyG, hxF⟩, ?_⟩
               have heq : y - a = x := hyx
               apply Prod.ext
               · grind
               · grind)).elim

end
end PottsDiscontinuity.PottsThm
