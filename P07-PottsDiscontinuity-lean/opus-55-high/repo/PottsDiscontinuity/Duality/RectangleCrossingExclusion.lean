/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleDualAmbient
public import PottsDiscontinuity.Duality.RectangleDualPotential
public import PottsDiscontinuity.Duality.RectangleEvents
public import PottsDiscontinuity.Duality.RectanglePathIntersection
public import PottsDiscontinuity.TorusRC.LiftedInterpolation

@[expose] public section

namespace PottsDiscontinuity.FK
open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial PottsDiscontinuity.FK.Curves PottsDiscontinuity.TorusRC unitInterval
noncomputable section

/-- Actual bottom-to-top crossing by complementary dual edges, with endpoints
on the genuine lower and upper face-base rows of the expanded rectangle. -/
def rectangleComplementDualVerticalCrossingEvent (a : LatticeVertex) (w h : ℕ) :
    Set (Configuration (rectangleGraph a w h)) :=
  {A | ∃ u v : RectangleDualVertex a w h,
    u.1.2 = a.2 - 1 ∧ v.1.2 = a.2 + (h : ℤ) ∧
    ActualConnected (rectangleDualGraph a w h) (rectangleDualConfiguration a w h A) u v}

section
variable {V : Type*} {G : SimpleGraph V} (f : V → ℝ × ℝ)

theorem walkPath_range {u v : V} (p : G.Walk u v) {z} (hz : z ∈ Set.range (polygonWalkPath f p)) :
    z = f u ∧ p.length = 0 ∨ ∃ x y, s(x,y) ∈ p.edges ∧ z ∈ segment ℝ (f x) (f y) := by
  induction p with
  | nil => simp_all [polygonWalkPath]
  | @cons x _ _ h p ih =>
    rw [polygonWalkPath, Path.trans_range, Path.range_segment] at hz
    rcases hz with hz | hz
    · exact .inr ⟨_, _, by simp, hz⟩
    · rcases ih hz with ⟨rfl, -⟩ | ⟨x, y, he, hz⟩
      · exact .inr ⟨x, _, by simp, right_mem_segment ℝ _ _⟩
      · exact .inr ⟨x, y, by simp [he], hz⟩

theorem segment_of_sym2 {a b c d : V} (h : s(a,b) = s(c,d)) :
    segment ℝ (f a) (f b) = segment ℝ (f c) (f d) := by
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact segment_symm ℝ _ _
end

def dc (v : LatticeVertex) : ℝ × ℝ := (v.1 + 1 / 2, v.2 + 1 / 2)

theorem int_eq {m n : ℤ} (h1 : (m : ℝ) < n + 1) (h2 : (n : ℝ) < m + 1) : m = n := by
  have : m < n + 1 := by exact_mod_cast h1
  have : n < m + 1 := by exact_mod_cast h2
  omega

/-- A primal unit segment and a dual face-center segment meet only when the
dual bond crosses the primal one. -/
theorem cross {b d : LatticeBond} {z} (hb : z ∈ segment ℝ (cellEmbed b.source) (cellEmbed b.target))
    (hd : z ∈ segment ℝ (dc d.source) (dc d.target)) : primalBondOfDual d = b := by
  rcases b with ⟨⟨x, y⟩, _ | _⟩ <;> rcases d with ⟨⟨u, v⟩, _ | _⟩ <;>
    simp [segment_eq_image, LatticeBond.source, LatticeBond.target, primalBondOfDual, cellEmbed, dc, Prod.ext_iff] at hb hd ⊢
  all_goals obtain ⟨t, ht, h1, h2⟩ := hb; obtain ⟨s, hs, h3, h4⟩ := hd
  · obtain rfl := int_eq (m := y) (by linarith) (by linarith); linarith
  any_goals constructor <;> apply int_eq <;> push_cast <;> linarith
  obtain rfl := int_eq (m := x) (n := u) (by linarith) (by linarith); linarith

/-- An actual left-right open primal crossing and an actual bottom-top
complementary-dual crossing cannot coexist. The dual endpoints are on the true
expanded face-base rows; no boundary wiring is used. -/
theorem rectanglePrimalDualCrossings_exclusive (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    (hP : A ∈ rectangleHorizontalCrossingEvent a w h)
    (hD : A ∈ rectangleComplementDualVerticalCrossingEvent a w h) : False := by
  rcases hP with ⟨u, v, hu, hv, ⟨p⟩⟩
  rcases hD with ⟨uD, vD, huD, hvD, ⟨q⟩⟩
  have hux := (Finset.mem_filter.mp hu).2
  have hvx := (Finset.mem_filter.mp hv).2
  let L : LatticeVertex := (a.1 - 1, u.1.2)
  let R : LatticeVertex := (a.1 + w + 1, v.1.2)
  let pc := (Path.segment (cellEmbed L) (cellEmbed u.1)).trans
    ((polygonWalkPath (fun x : RectangleVertex a w h => cellEmbed x.1) p).trans (Path.segment (cellEmbed v.1) (cellEmbed R)))
  let qc := polygonWalkPath (fun x : RectangleDualVertex a w h => dc x.1) q
  let lo : ℝ × ℝ := ((a.1 : ℝ) - 1, (a.2 : ℝ) - 1 / 2)
  let hi : ℝ × ℝ := ((a.1 : ℝ) + w + 1, (a.2 : ℝ) + h + 1 / 2)
  have hpc : Set.range pc ⊆ Set.Icc lo hi := by
    have := (mem_latticeRectangle _ _ _ _).1 u.2
    have := (mem_latticeRectangle _ _ _ _).1 v.2
    simp only [pc, Path.trans_range, Path.range_segment, Set.union_subset_iff]
    refine ⟨(convex_Icc _ _).segment_subset ?_ ?_, Set.range_subset_iff.2 (polygonWalkPath_mem_Icc _ p _ _ fun x _ => ?_),
      (convex_Icc _ _).segment_subset ?_ ?_⟩
    all_goals
      try have := (mem_latticeRectangle _ _ _ _).1 x.2
      try rify at *
      simp [L, R, cellEmbed, lo, hi, Prod.le_def]
      and_intros <;> linarith
  have hqc : Set.range qc ⊆ Set.Icc lo hi := Set.range_subset_iff.2 <| polygonWalkPath_mem_Icc _ q _ _ fun x _ => by
    have := (mem_latticeRectangle _ _ _ _).1 x.2
    rify at *
    simp [dc, lo, hi, Prod.le_def]
    and_intros <;> linarith
  obtain ⟨s, t, hst⟩ := pathRectangle_crossing_intersection pc qc
    (fun t => (fun h => ⟨h.1.1, h.2.1, h.1.2, h.2.2⟩) (hpc ⟨t, rfl⟩)) (fun t => (fun h => ⟨h.1.1, h.2.1, h.1.2, h.2.2⟩) (hqc ⟨t, rfl⟩))
    (by rw [Path.source]; simp [L, cellEmbed, lo]) (by rw [Path.target]; simp [R, cellEmbed, hi])
    (by rw [Path.source]; simp [dc, lo, huD]; ring) (by rw [Path.target]; simp [dc, hi, hvD])
  obtain ⟨d, hd, hzD⟩ : ∃ d : RectangleDualEdgeCarrier a w h, d.primalEdge ∉ A ∧
      pc s ∈ segment ℝ (dc d.crossingBond.source) (dc d.crossingBond.target) := by
    rcases walkPath_range _ q ⟨t, hst.symm⟩ with ⟨-, hq⟩ | ⟨X, Y, he, hzs⟩
    · have := q.eq_of_length_eq_zero hq
      subst this; omega
    obtain ⟨g, hg, hgv⟩ : s(X, Y) ∈ openEdges _ _ := openGraph_edgeSet _ _ ▸ q.edges_subset_edgeSet he
    obtain ⟨e, rfl⟩ := (rectangleDualGraphEdgeEquiv a w h).surjective g
    refine ⟨e, (mem_rectangleDualConfiguration a w h A e).1 hg, ?_⟩
    rwa [← rectangleDualEdgeSource_val, ← rectangleDualEdgeTarget_val,
      segment_of_sym2 (fun x : RectangleDualVertex a w h => dc x.1) hgv]
  generalize hz : pc s = z at hzD
  have key : ∀ b : LatticeBond, z ∈ segment ℝ (cellEmbed b.source) (cellEmbed b.target) →
      rectanglePrimalEdgeBond a w h d.primalEdge = b := fun b hb => by simpa using cross hb hzD
  have hu' : (a.1, u.1.2) = u.1 := Prod.ext hux.symm rfl
  have hmem := rectanglePrimalEdgeBond_endpoints_mem_public a w h d.primalEdge
  have hzP : z ∈ Set.range pc := ⟨s, hz⟩
  simp only [pc, Path.trans_range, Path.range_segment, Set.mem_union] at hzP
  rcases hzP with h1 | h2 | h3
  · rw [key ⟨L, .horizontal⟩ (by simpa [LatticeBond.source, LatticeBond.target, L, hu'] using h1)] at hmem
    simp [LatticeBond.source, mem_latticeRectangle, L] at hmem
  · rcases walkPath_range _ p h2 with ⟨h2, -⟩ | ⟨X, Y, he, hzs⟩
    · have := (key ⟨u.1, .horizontal⟩ (h2 ▸ left_mem_segment ℝ _ _)).symm.trans (key ⟨u.1, .vertical⟩ (h2 ▸ left_mem_segment ℝ _ _))
      simp at this
    obtain ⟨e, he, hev⟩ : s(X, Y) ∈ openEdges _ _ := openGraph_edgeSet _ _ ▸ p.edges_subset_edgeSet he
    have hb : (rectanglePrimalEdgeBond a w h e).toSym2 = s(X.1, Y.1) :=
      (rectanglePrimalEdgeBond_toSym2_public a w h e).trans (hev ▸ rfl)
    have := (rectanglePrimalEdgeBond_toSym2_public a w h _).symm.trans ((congrArg LatticeBond.toSym2
      (key _ (by rwa [segment_of_sym2 cellEmbed hb]))).trans (rectanglePrimalEdgeBond_toSym2_public a w h e))
    exact hd (Subtype.ext (Sym2.map.injective Subtype.val_injective this) ▸ he)
  · rw [key ⟨v.1, .horizontal⟩ (by simpa [LatticeBond.source, LatticeBond.target, R, hvx] using h3)] at hmem
    simp [LatticeBond.target, mem_latticeRectangle, hvx] at hmem
end
end PottsDiscontinuity.FK
