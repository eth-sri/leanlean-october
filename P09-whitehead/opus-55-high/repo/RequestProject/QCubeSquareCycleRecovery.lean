import RequestProject.QCubeSquareBoundaryKernel
import RequestProject.Tac


/-! Local recovery of cubical coefficients from actual two-dimensional strict cycles. -/
open scoped Classical
bwd

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem squareRadialBoundary_off_square c a b hne
    hs t
    (hm : t.1.2.1 ≠ c) (ht : t.1.2.2 ≠ c) n :
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
  simp_all [hn, map_smul, hb, map_sub, map_add, squareRadialCoordinates_off_top c a b hne hs e01 hm, squareRadialCoordinates_off_top c a b hne hs e12 ht, squareRadialCoordinates_off_top c a b hne hs e02 ht]

theorem squareRadialBoundary_filter_top c a b hne
    hs z
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2) :
    squareRadialCoordinates c a b hne hs (Comb.bdry2 (strictOrderCx (QCube A)) z) =
    squareRadialCoordinates c a b hne hs (Comb.bdry2 (strictOrderCx (QCube A))
      (z.filter (·.1.2.2 = c))) := by
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
      intro hm
      have hdim := (qCube_triangle_dimensions t (hz t ht)).2.1
      simp_all
    grind [squareRadialBoundary_off_square c a b hne hs t hm he, map_zero]

/-- Every genuine two-dimensional cycle has on each square exactly its cubical coefficient
 times the actual strict square subdivision. -/
theorem cubeTwoCycle_square_component c a b hne
    hs z
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    z.filter (·.1.2.2 = c) =
      z (squareFlag c a b hne hs (false, 0, false)) • cubeSquareSubdivision c a b hne hs := by
  have hsupp : ∀ t ∈ (z.filter (·.1.2.2 = c)).support, t.1.2.2 = c := by
    simp
  have hint : squareRadialCoordinates c a b hne hs
      (Comb.bdry2 _ (z.filter (·.1.2.2 = c))) = 0 := by
    rw [← squareRadialBoundary_filter_top c a b hne hs z hz, hcycle, map_zero]
  have he := squareChain_eq_scalar_subdivision c a b hne hs _ hsupp hint
  simpa [Finsupp.filter_apply, squareFlag_top, if_true] using he
