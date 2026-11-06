module

public import PottsDiscontinuity.Potts.GhostBoxCorners

/-! Classification of the outer-box edges into literal bonds, cuts, and shell edges. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

/-- Inclusion of the inner induced graph into the outer induced graph. -/
def innerBoxGraphEmbedding (n : ℕ) :
    squareLattice.induce (box n : Set (ℤ × ℤ)) ↪g
      squareLattice.induce (box (n + 1) : Set (ℤ × ℤ)) :=
  squareLattice.induceHomOfLE (fun _ hx => box_subset_box_succ n hx)

def innerBoxEdgeEmbedding (n : ℕ) :
    (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet ↪ OuterBoxEdge n :=
  (innerBoxGraphEmbedding n).mapEdgeSet

theorem innerBoxEdgeEmbedding_inside (n : ℕ)
    (e : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet)
    (x : ↥(box (n + 1) : Set (ℤ × ℤ))) (hx : x ∈ (innerBoxEdgeEmbedding n e).val) :
    x.val ∈ box n := by
  change x ∈ Sym2.map (innerBoxGraphEmbedding n) e.val at hx
  obtain ⟨a, _, ha⟩ := Sym2.mem_map.mp hx
  exact ha ▸ a.property

def literalBondOuterEdge (n : ℕ) : LiteralBond (box n) → OuterBoxEdge n
  | .inl e => innerBoxEdgeEmbedding n e
  | .inr x => ghostOutwardEdge n x

theorem literalBondOuterEdge_injective (n : ℕ) : Function.Injective (literalBondOuterEdge n) := by
  rintro (e | x) (f | x) h
  · exact congrArg Sum.inl ((innerBoxEdgeEmbedding n).injective h)
  · exact (ghostOutwardNeighbor_not_mem n x <| innerBoxEdgeEmbedding_inside n e
      ⟨ghostOutwardNeighbor n x, ghostOutwardNeighbor_mem_outer n x⟩
      (by rw [show innerBoxEdgeEmbedding n e = ghostOutwardEdge n x from h]; exact Sym2.mem_mk_right _ _)).elim
  · exact (ghostOutwardNeighbor_not_mem n x <| innerBoxEdgeEmbedding_inside n f
      ⟨ghostOutwardNeighbor n x, ghostOutwardNeighbor_mem_outer n x⟩
      (by rw [show innerBoxEdgeEmbedding n f = ghostOutwardEdge n x from h.symm]; exact Sym2.mem_mk_right _ _)).elim
  · exact congrArg Sum.inr (ghostOutwardEdge_injective n h)

/-- A crossing edge is either the retained ghost edge or the omitted vertical
edge at a corner. The positive-radius hypothesis excludes the singleton box. -/
theorem crossingEdge_classification (n : ℕ) (hn : 0 < n)
    (x : BoundaryVertex (box n)) (y : ℤ × ℤ)
    (hxy : squareLattice.Adj x.val.val y) (hy : y ∉ box n) :
    y = ghostOutwardNeighbor n x ∨
      ∃ b : Bool × Bool, x.val.val = cornerPoint n b ∧ y = cornerOutwardPoint n b := by
  have hx := (mem_box_iff n x.val.val).mp x.val.property
  rw [mem_box_iff] at hy
  rw [FK.squareLattice_adj_iff] at hxy
  by_cases hx1 : x.val.val.1 = (n : ℤ)
  · by_cases hy1 : y.1 = (n : ℤ) + 1
    · left; rw [ghostOutwardNeighbor, ite_eq_left hx1]; ext <;> (try dsimp) <;> omega
    · right
      by_cases hx2 : x.val.val.2 = (n : ℤ)
      · refine ⟨(true, true), ?_, ?_⟩ <;> ext <;> dsimp [cornerPoint, cornerOutwardPoint] <;> omega
      · refine ⟨(true, false), ?_, ?_⟩ <;> ext <;> dsimp [cornerPoint, cornerOutwardPoint] <;> omega
  · by_cases hx1' : x.val.val.1 = -(n : ℤ)
    · by_cases hy1 : y.1 = -(n : ℤ) - 1
      · left; rw [ghostOutwardNeighbor, ite_eq_right hx1, ite_eq_left hx1']; ext <;> (try dsimp) <;> omega
      · right
        by_cases hx2 : x.val.val.2 = (n : ℤ)
        · refine ⟨(false, true), ?_, ?_⟩ <;> ext <;> dsimp [cornerPoint, cornerOutwardPoint] <;> omega
        · refine ⟨(false, false), ?_, ?_⟩ <;> ext <;> dsimp [cornerPoint, cornerOutwardPoint] <;> omega
    · left; rw [ghostOutwardNeighbor, ite_eq_right hx1, ite_eq_right hx1']
      split_ifs <;> ext <;> (try dsimp) <;> omega

def outerEdgeCoordinates (n : ℕ) (e : OuterBoxEdge n) : Sym2 (ℤ × ℤ) :=
  Sym2.map Subtype.val e.val

theorem outerEdgeCoordinates_injective (n : ℕ) : Function.Injective (outerEdgeCoordinates n) :=
  fun _ _ h => Subtype.ext (Sym2.map.injective Subtype.val_injective h)

@[simp] theorem outerEdgeCoordinates_ghost (n : ℕ) (x : BoundaryVertex (box n)) :
    outerEdgeCoordinates n (ghostOutwardEdge n x) = s(x.val.val, ghostOutwardNeighbor n x) := rfl

@[simp] theorem outerEdgeCoordinates_corner (n : ℕ) (b : Bool × Bool) :
    outerEdgeCoordinates n (cornerCutEdge n b) = s(cornerPoint n b, cornerOutwardPoint n b) := rfl

theorem literalBondOuterEdge_has_inner (n : ℕ) (b : LiteralBond (box n)) :
    ∃ x ∈ (literalBondOuterEdge n b).val, x.val ∈ box n := by
  cases b with
  | inl e =>
    exact ⟨innerBoxGraphEmbedding n e.val.out.1,
      Sym2.mem_map.mpr ⟨e.val.out.1, Sym2.out_fst_mem e.val, rfl⟩, e.val.out.1.property⟩
  | inr x =>
    exact ⟨⟨x.val.val, box_subset_box_succ n x.val.property⟩, Sym2.mem_mk_left _ _, x.val.property⟩

theorem literalBondOuterEdge_ne_corner (n : ℕ) (b : LiteralBond (box n)) (c : Bool × Bool) :
    literalBondOuterEdge n b ≠ cornerCutEdge n c := by
  cases b with
  | inr x => exact (cornerCutEdge_ne_ghostOutwardEdge n c x).symm
  | inl e =>
    exact fun h => cornerOutwardPoint_not_mem n c <| innerBoxEdgeEmbedding_inside n e
      ⟨cornerOutwardPoint n c, cornerOutwardPoint_mem n c⟩
      (by rw [show innerBoxEdgeEmbedding n e = cornerCutEdge n c from h]; exact Sym2.mem_mk_right _ _)

abbrev OuterShellEdge (n : ℕ) :=
  {e : OuterBoxEdge n // ∀ x ∈ e.val, x.val ∉ box n}

abbrev OuterEdgePiece (n : ℕ) := LiteralBond (box n) ⊕ ((Bool × Bool) ⊕ OuterShellEdge n)

def outerEdgeFromPiece (n : ℕ) : OuterEdgePiece n → OuterBoxEdge n
  | .inl b => literalBondOuterEdge n b
  | .inr (.inl b) => cornerCutEdge n b
  | .inr (.inr e) => e.val

private theorem literal_ne_shell (n : ℕ) (b : LiteralBond (box n)) (e : OuterShellEdge n) :
    literalBondOuterEdge n b ≠ e.val := fun h => by
  obtain ⟨x, hx, hi⟩ := literalBondOuterEdge_has_inner n b
  exact e.property x (h ▸ hx) hi

private theorem corner_ne_shell (n : ℕ) (b : Bool × Bool) (e : OuterShellEdge n) :
    cornerCutEdge n b ≠ e.val := fun h =>
  e.property ⟨cornerPoint n b, box_subset_box_succ n (cornerPoint_mem n b)⟩
    (h ▸ Sym2.mem_mk_left _ _) (cornerPoint_mem n b)

theorem outerEdgeFromPiece_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (outerEdgeFromPiece n) := by
  rintro (a | (c | e)) (b | (d | f)) h
  · exact congrArg Sum.inl (literalBondOuterEdge_injective n h)
  · exact (literalBondOuterEdge_ne_corner n a d h).elim
  · exact (literal_ne_shell n a f h).elim
  · exact (literalBondOuterEdge_ne_corner n b c h.symm).elim
  · exact congrArg (Sum.inr ∘ Sum.inl) (cornerCutEdge_injective n hn h)
  · exact (corner_ne_shell n c f h).elim
  · exact (literal_ne_shell n b e h.symm).elim
  · exact (corner_ne_shell n d e h.symm).elim
  · exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext h)

private theorem crossingEdge_in_range (n : ℕ) (hn : 0 < n)
    (u v : ↥(box (n + 1) : Set (ℤ × ℤ)))
    (huv : squareLattice.Adj u.val v.val) (hu : u.val ∈ box n) (hv : v.val ∉ box n) :
    ∃ b : OuterEdgePiece n,
      outerEdgeFromPiece n b = ⟨s(u, v), (squareLattice.induce _).mem_edgeSet.mpr huv⟩ := by
  let x : BoundaryVertex (box n) := ⟨⟨u.val, hu⟩, hu, v.val, huv, hv⟩
  rcases crossingEdge_classification n hn x v.val huv hv with h | ⟨b, hb, hvb⟩
  · exact ⟨.inl (.inr x), outerEdgeCoordinates_injective n
      (show s(u.val, ghostOutwardNeighbor n x) = s(u.val, v.val) by rw [h])⟩
  · exact ⟨.inr (.inl b), outerEdgeCoordinates_injective n (congrArg₂ Sym2.mk hb.symm hvb.symm)⟩

theorem outerEdgeFromPiece_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (outerEdgeFromPiece n) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
    have huv : squareLattice.Adj u.val v.val := (squareLattice.induce _).mem_edgeSet.mp he
    by_cases hu : u.val ∈ box n <;> by_cases hv : v.val ∈ box n
    · exact ⟨.inl (.inl ⟨s(⟨u.val, hu⟩, ⟨v.val, hv⟩), (squareLattice.induce _).mem_edgeSet.mpr huv⟩), rfl⟩
    · exact crossingEdge_in_range n hn u v huv hu hv
    · obtain ⟨b, hb⟩ := crossingEdge_in_range n hn v u huv.symm hv hu
      exact ⟨b, hb.trans (Subtype.ext Sym2.eq_swap)⟩
    · exact ⟨.inr (.inr ⟨⟨s(u, v), he⟩, fun x hx => (Sym2.mem_iff.mp hx).elim (· ▸ hu) (· ▸ hv)⟩), rfl⟩

/-- The exact edge-index decomposition used to sum out the wired shell and to
condition the four omitted corner bonds closed. -/
def outerBoxEdgeEquiv (n : ℕ) (hn : 0 < n) : OuterEdgePiece n ≃ OuterBoxEdge n :=
  Equiv.ofBijective (outerEdgeFromPiece n)
    ⟨outerEdgeFromPiece_injective n hn, outerEdgeFromPiece_surjective n hn⟩

end
end PottsDiscontinuity.Potts
