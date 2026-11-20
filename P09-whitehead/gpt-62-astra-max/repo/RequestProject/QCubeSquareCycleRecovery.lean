module

public import RequestProject.QCubeSquareBoundaryKernel

@[expose] public section

/-! Local recovery of cubical coefficients from actual two-dimensional strict cycles. -/
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

variable (c : QCube A) (a b : V) (hne : a ≠ b) (hs : c.spx = {a, b})

theorem squareRadialBoundary_off_square (t : (strictOrderCx (QCube A)).F)
    (hm : t.1.2.1 ≠ c) (ht : t.1.2.2 ≠ c) (n : ℤ) :
    squareRadialCoordinates c a b hne hs
      (Comb.bdry2 (strictOrderCx (QCube A)) (Finsupp.single t n)) = 0 := by
  let e01 : (strictOrderCx (QCube A)).E := ⟨(t.1.1, t.1.2.1), t.2.1⟩
  let e12 : (strictOrderCx (QCube A)).E := ⟨(t.1.2.1, t.1.2.2), t.2.2⟩
  let e02 : (strictOrderCx (QCube A)).E := ⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩
  have hb : Comb.bdry2 _ (Finsupp.single t 1) =
      Finsupp.single e01 1 + Finsupp.single e12 1 - Finsupp.single e02 1 := by
    simp [Comb.bdry2, strictOrderCx, pathChain, e01, e12, e02]
    abel
  have hn : Finsupp.single t n = n • Finsupp.single t 1 := by simp
  rw [hn, map_smul, map_smul, hb, map_sub, map_add,
    squareRadialCoordinates_off_top c a b hne hs e01 hm,
    squareRadialCoordinates_off_top c a b hne hs e12 ht,
    squareRadialCoordinates_off_top c a b hne hs e02 ht]
  simp

variable (z : (strictOrderCx (QCube A)).F →₀ ℤ) (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
include hz

theorem squareRadialBoundary_filter_top :
    squareRadialCoordinates c a b hne hs (Comb.bdry2 (strictOrderCx (QCube A)) z) =
    squareRadialCoordinates c a b hne hs (Comb.bdry2 (strictOrderCx (QCube A))
      (z.filter (fun t => t.1.2.2 = c))) := by
  classical
  conv_lhs => rw [← z.sum_single]
  conv_rhs => rw [← z.sum_single]
  simp only [Finsupp.sum, map_sum, Finsupp.filter_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases he : t.1.2.2 = c
  · simp_all
  · rw [Finsupp.filter_single_of_neg (fun t : (strictOrderCx (QCube A)).F => t.1.2.2 = c) he]
    have hm : t.1.2.1 ≠ c := by
      grind [qCube_triangle_dimensions]
    rw [squareRadialBoundary_off_square c a b hne hs t hm he, map_zero, map_zero]

/-- Every genuine two-dimensional cycle has on each square exactly its cubical coefficient
 times the actual strict square subdivision. -/
theorem cubeTwoCycle_square_component
    (hcycle : Comb.bdry2 _ z = 0) :
    z.filter (fun t => t.1.2.2 = c) =
      z (squareFlag c a b hne hs (false, 0, false)) • cubeSquareSubdivision c a b hne hs := by
  have hsupp : ∀ t ∈ (z.filter (fun t => t.1.2.2 = c)).support, t.1.2.2 = c := by
    simp_all
  have hint : squareRadialCoordinates c a b hne hs
      (Comb.bdry2 (strictOrderCx (QCube A)) (z.filter (fun t => t.1.2.2 = c))) = 0 := by
    rw [← squareRadialBoundary_filter_top c a b hne hs z hz, hcycle, map_zero]
  simpa only [Finsupp.filter_apply, squareFlag_top, if_true] using (squareChain_eq_scalar_subdivision c a b hne hs _ hsupp hint)

end FiniteChains.Davis
