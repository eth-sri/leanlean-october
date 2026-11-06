import Mathlib.Tactic

import RequestProject.QCubeFacets
import RequestProject.OrderThreeNormalization

/-! Strict quotient-cube order increases dimension, and all immediate faces are actual facets. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

  {d c : QCube A}
theorem qCube_spx_ne_of_lt  (h : d < c) : d.spx ≠ c.spx := by
  intro hs
  apply h.ne
  apply QCube.ext' hs
  intro v hv
  exact h.le.2 v hv

abbrev qCube_card_lt_of_lt  (h : d < c)  :=
  Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr
    ⟨h.le.1, qCube_spx_ne_of_lt h⟩)

/-- Fixing the only removed direction reconstructs the actual face, including its sign. -/
theorem qCube_eq_facet_of_spx_erase  (h : d ≤ c) (v : V)
    (hs : d.spx = c.spx.erase v) : d = qCubeFacet c v (d.sgn v) := by
  apply QCube.ext' hs
  intro w hw
  by_cases hwv : w = v
  · subst w
    simp
  · change d.sgn w = Function.update c.sgn v (d.sgn v) w
    rw [Function.update_of_ne hwv]
    apply h.2
    intro hc
    apply hw
    
    exact Finset.mem_erase.mpr ⟨hwv, hc⟩

variable (d c : QCube A)
/-- Every codimension-one face is one of the coordinate facets, with its actual fixed sign. -/
theorem exists_qCube_facet_of_card  (h : d ≤ c)
    (hcard : c.spx.card = d.spx.card + 1) :
    ∃ v ∈ c.spx, d = qCubeFacet c v (d.sgn v) := by
  have hdiff : (c.spx \ d.spx).card = 1 := by
    rw [Finset.card_sdiff_of_subset h.1, hcard]
    omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hdiff
  have hm : v ∈ c.spx \ d.spx := by rw [hv]; simp
  obtain ⟨hvc, hvd⟩ := Finset.mem_sdiff.mp hm
  refine ⟨v, hvc, qCube_eq_facet_of_spx_erase h v ?_⟩
  ext w
  constructor
  · intro hw
    exact Finset.mem_erase.mpr ⟨fun he => hvd (he ▸ hw), h.1 hw⟩
  · intro hw
    obtain ⟨hwv, hwc⟩ := Finset.mem_erase.mp hw
    by_contra hwd
    have hm  := Finset.mem_sdiff.mpr ⟨hwc, hwd⟩
    rw [hv, Finset.mem_singleton] at hm
    exact hwv hm

/-- The only two signs of a codimension-one face give the two actual coordinate facets. -/
theorem exists_qCube_zero_or_one_facet  (h : d ≤ c)
    (hcard : c.spx.card = d.spx.card + 1) :
    ∃ v ∈ c.spx, d = qCubeFacet c v 0 ∨ d = qCubeFacet c v 1 := by
  obtain ⟨v, hv, he⟩ := exists_qCube_facet_of_card d c h hcard
  refine ⟨v, hv, ?_⟩
  generalize d.sgn v = s at he
  fin_cases s
  · exact Or.inl he
  · exact Or.inr he

/-- A vertex strictly below an actual edge is one of that edge's two endpoints. -/
theorem qCube_vertex_below_edge  (h : d < c) (v : V)
    (hs : c.spx = {v}) : d = cubePositiveVertex c ∨ d = cubeNegativeVertex c v := by
  have hc : c.spx.card = 1 := by rw [hs]; simp
  have hd : d.spx.card = 0 := by
    have hh := qCube_card_lt_of_lt h
    omega
  obtain ⟨w, hw, he⟩ := exists_qCube_zero_or_one_facet d c h.le (by omega)
  have hwv : w = v := by simpa [hs] using hw
  subst w
  rcases he with he | he
  · simp_all [FiniteChains.Davis.qCubeFacet_zero_of_singleton]
  · simp_all [FiniteChains.Davis.qCubeFacet_one_of_singleton]

/-- A genuine triangle below dimension two is necessarily a vertex-edge-square flag. -/
theorem qCube_triangle_dimensions (t : (strictOrderCx (QCube A)).F)
    (ht : t.1.2.2.spx.card ≤ 2) :
    t.1.1.spx.card = 0 ∧ t.1.2.1.spx.card = 1 ∧ t.1.2.2.spx.card = 2 := by
  have h01 := qCube_card_lt_of_lt t.2.1
  have h12 := qCube_card_lt_of_lt t.2.2
  omega

/-- A genuine tetrahedron below dimension three has all four successive cube dimensions. -/
theorem qCube_tetrahedron_dimensions (t : StrictOrdTet (QCube A))
    (ht : t.1.2.2.2.spx.card ≤ 3) :
    t.1.1.spx.card = 0 ∧ t.1.2.1.spx.card = 1 ∧
    t.1.2.2.1.spx.card = 2 ∧ t.1.2.2.2.spx.card = 3 := by
  have h01 := qCube_card_lt_of_lt t.2.1
  have h12 := qCube_card_lt_of_lt t.2.2.1
  have h23 := qCube_card_lt_of_lt t.2.2.2
  omega

end FiniteChains.Davis
