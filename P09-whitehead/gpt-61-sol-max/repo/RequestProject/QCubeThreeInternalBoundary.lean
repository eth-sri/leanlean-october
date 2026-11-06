import Mathlib.Tactic

import RequestProject.StrictLowerConeBoundary
import RequestProject.QCubeImmediateFaces

/-! Top-cube isolation of actual strict tetrahedron boundaries in cube dimension three. -/
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

  (c : QCube A)
variable (t : StrictOrdTet (QCube A))
include t in
theorem strictTetBoundary_filter_off_top  
    (hm : t.1.2.2.1 ≠ c) (ht : t.1.2.2.2 ≠ c) :
    (strictOrdTetBoundary t).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) = 0 := by simp_all [strictOrdTetBoundary]

include t in
theorem strictOrdBoundary3_single_filter_off_top 
     (hm : t.1.2.2.1 ≠ c) (ht : t.1.2.2.2 ≠ c) (n : ℤ) :
    (strictOrdBoundary3 (Finsupp.single t n)).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) = 0 := by
  simp_all [strictOrdBoundary3, strictTetBoundary_filter_off_top]

variable (hc : c.spx.card = 3)
include hc in
/-- In dimension at most three, only tetrahedra topped by this cube contribute to its
internal triangle boundary. -/
theorem qCube_boundary3_filter_top  
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3) :
    (strictOrdBoundary3 y).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) =
    (strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c))).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) := by
  classical
  conv_lhs => rw  [← y.sum_single]
  conv_rhs => rw  [← y.sum_single]
  simp only [Finsupp.sum, map_sum, Finsupp.filter_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases he : t.1.2.2.2 = c
  · simp_all
  · rw  [Finsupp.filter_single_of_neg (fun t : StrictOrdTet (QCube A) => t.1.2.2.2 = c) he,
      map_zero, Finsupp.filter_zero]
    have hm : t.1.2.2.1 ≠ c := by
      classical grind [FiniteChains.Davis.qCube_tetrahedron_dimensions]
    exact strictOrdBoundary3_single_filter_off_top c t hm he _

include hc in
/-- A boundary supported in dimensions at most two has zero internal component at a three-cube. -/
theorem qCube_boundary3_internal_zero  
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    (strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c))).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) = 0 := by
  rw  [← qCube_boundary3_filter_top c hc y hy]
  apply (Finsupp.filter_eq_zero_iff _ _).mpr
  intro s hs
  by_contra hsz
  have hd := hb s (Finsupp.mem_support_iff.mpr hsz)
  rw  [hs, hc] at hd
  omega

include hc in
/-- Every three-cube component of such a chain is a fan over a proved actual lower two-cycle. -/
theorem qCube_three_component_lower_cycle  
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ z : (strictOrderCx (Set.Iio c)).F →₀ ℤ,
      Comb.bdry2 (strictOrderCx (Set.Iio c)) z = 0 ∧
      strictTopConeTriangleChain Subtype.val (fun _ _ h => h) c
        (fun x : Set.Iio c => x.2) z = y.filter (fun t => t.1.2.2.2 = c) := by
  apply exists_strictLowerConeCycle
  · simp_all
  · simp_all [qCube_boundary3_internal_zero]

end FiniteChains.Davis
