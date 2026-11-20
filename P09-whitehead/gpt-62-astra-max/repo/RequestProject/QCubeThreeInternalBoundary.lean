module

public import RequestProject.StrictLowerConeBoundary
public import RequestProject.QCubeImmediateFaces

@[expose] public section

/-! Top-cube isolation of actual strict tetrahedron boundaries in cube dimension three. -/
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

variable (c : QCube A)

section

variable (t : StrictOrdTet (QCube A)) (hm : t.1.2.2.1 ≠ c) (ht : t.1.2.2.2 ≠ c)
include hm ht

theorem strictTetBoundary_filter_off_top :
    (relTetBoundary t).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) = 0 := by
  simp_all [relTetBoundary, Finsupp.filter_sub, Finsupp.filter_add, Finsupp.filter_single_of_neg]

theorem strictOrdBoundary3_single_filter_off_top (n : ℤ) :
    (strictOrdBoundary3 (Finsupp.single t n)).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) = 0 := by
  simp_all [strictOrdBoundary3, Finsupp.linearCombination_single, Finsupp.filter_smul, strictTetBoundary_filter_off_top, smul_zero]

end

variable (hc : c.spx.card = 3)
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
include hc hy

/-- In dimension at most three, only tetrahedra topped by this cube contribute to its
internal triangle boundary. -/
theorem qCube_boundary3_filter_top :
    (strictOrdBoundary3 y).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) =
    (strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c))).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) := by
  classical
  conv_lhs => rw (config := { transparency := .default }) [← y.sum_single]
  conv_rhs => rw (config := { transparency := .default }) [← y.sum_single]
  simp only [Finsupp.sum, map_sum, Finsupp.filter_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases he : t.1.2.2.2 = c
  · simp_all
  · erw [Finsupp.filter_single_of_neg (fun t : StrictOrdTet (QCube A) => t.1.2.2.2 = c) he,
      map_zero, Finsupp.filter_zero]
    have hm : t.1.2.2.1 ≠ c := by
      intro hm
      grind [qCube_tetrahedron_dimensions]
    apply strictOrdBoundary3_single_filter_off_top <;> assumption

variable (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2)
include hb

/-- A boundary supported in dimensions at most two has zero internal component at a three-cube. -/
theorem qCube_boundary3_internal_zero :
    (strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c))).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) = 0 := by
  erw [← qCube_boundary3_filter_top c hc y hy]
  apply (Finsupp.filter_eq_zero_iff _ _).mpr
  intro s hs
  by_contra hsz
  have hd := hb s (Finsupp.mem_support_iff.mpr hsz)
  grind

/-- Every three-cube component of such a chain is a fan over a proved actual lower two-cycle. -/
theorem qCube_three_component_lower_cycle :
    ∃ z : (strictOrderCx (Set.Iio c)).F →₀ ℤ,
      Comb.bdry2 _ z = 0 ∧
      strictTopConeTriangleChain Subtype.val (fun _ _ h => h) c
        (fun x : Set.Iio c => x.2) z = y.filter (fun t => t.1.2.2.2 = c) := by
  apply exists_strictLowerConeCycle
  · simp
  · apply qCube_boundary3_internal_zero <;> assumption

end FiniteChains.Davis
