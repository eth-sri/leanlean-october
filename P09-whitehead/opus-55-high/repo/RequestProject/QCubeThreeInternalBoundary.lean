import RequestProject.StrictLowerConeBoundary
import RequestProject.QCubeImmediateFaces
import RequestProject.Tac


/-! Top-cube isolation of actual strict tetrahedron boundaries in cube dimension three. -/
open scoped Classical
bwd

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem strictTetBoundary_filter_off_top c t
    (hm : t.1.2.2.1 ≠ c) (ht : t.1.2.2.2 ≠ c) :
    (strictOrdTetBoundary t).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) = 0 := by
  simp [strictOrdTetBoundary, Finsupp.filter_sub, Finsupp.filter_add]
  simp_all

theorem strictOrdBoundary3_single_filter_off_top c
    t (hm : t.1.2.2.1 ≠ c) (ht : t.1.2.2.2 ≠ c) n :
    (strictOrdBoundary3 (Finsupp.single t n)).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) = 0 := by
  simp [strictOrdBoundary3, Finsupp.linearCombination_single, Finsupp.filter_smul, strictTetBoundary_filter_off_top c t hm ht, smul_zero]

/-- In dimension at most three, only tetrahedra topped by this cube contribute to its
internal triangle boundary. -/
theorem qCube_boundary3_filter_top c (hc : c.spx.card = 3)
    y
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3) :
    (strictOrdBoundary3 y).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) =
    (strictOrdBoundary3 (y.filter (·.1.2.2.2 = c))).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) := by
  classical
  conv_lhs => rwd [← y.sum_single]
  conv_rhs => rwd [← y.sum_single]
  simp [Finsupp.sum, map_sum, Finsupp.filter_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases he : t.1.2.2.2 = c
  · simp_all
  · rwd [Finsupp.filter_single_of_neg (fun t : StrictOrdTet (QCube A) => t.1.2.2.2 = c) he,
      map_zero, Finsupp.filter_zero]
    have hm : t.1.2.2.1 ≠ c := by
      intro hm
      have hd := (qCube_tetrahedron_dimensions t (hy t ht)).2.2.1
      simp_all
    exact strictOrdBoundary3_single_filter_off_top c t hm he _

/-- A boundary supported in dimensions at most two has zero internal component at a three-cube. -/
theorem qCube_boundary3_internal_zero c (hc : c.spx.card = 3)
    y
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    (strictOrdBoundary3 (y.filter (·.1.2.2.2 = c))).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) = 0 := by
  rwd [← qCube_boundary3_filter_top c hc y hy]
  apply (Finsupp.filter_eq_zero_iff _ _).mpr
  intro s hs
  by_contra hsz
  have hd := hb s (Finsupp.mem_support_iff.mpr hsz)
  simp_all

/-- Every three-cube component of such a chain is a fan over a proved actual lower two-cycle. -/
theorem qCube_three_component_lower_cycle (c : QCube A) (hc : c.spx.card = 3)
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ z : (strictOrderCx (Set.Iio c)).F →₀ ℤ,
      Comb.bdry2 (strictOrderCx (Set.Iio c)) z = 0 ∧
      strictTopConeTriangleChain Subtype.val (fun _ _ h => h) c
        (fun x : Set.Iio c => x.2) z = y.filter (·.1.2.2.2 = c) := by
  apply exists_strictLowerConeCycle
  · simp
  · exact qCube_boundary3_internal_zero c hc y hy hb
