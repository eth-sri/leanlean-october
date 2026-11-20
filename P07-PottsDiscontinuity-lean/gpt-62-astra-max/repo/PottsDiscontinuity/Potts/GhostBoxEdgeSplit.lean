module

public import PottsDiscontinuity.Potts.GhostBoxCorners

/-! Classification of the outer-box edges into literal bonds, cuts, and shell edges. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

variable (n : ℕ) (hn : 0 < n) (b : LiteralBond (box n))

/-- Inclusion of the inner induced graph into the outer induced graph. -/
def innerBoxGraphEmbedding :
    squareLattice.induce (box n) ↪g
      squareLattice.induce (box (n + 1)) :=
  squareLattice.induceHomOfLE (fun _ hx => box_subset_box_succ n hx)

def innerBoxEdgeEmbedding :
    (squareLattice.induce (box n)).edgeSet ↪ OuterBoxEdge n :=
  (innerBoxGraphEmbedding n).mapEdgeSet

theorem innerBoxEdgeEmbedding_inside
    (e : (squareLattice.induce (box n)).edgeSet)
    (x : ↥(box (n + 1))) (hx : x ∈ (innerBoxEdgeEmbedding n e).val) :
    x.val ∈ box n := by
  obtain ⟨a, _, ha⟩ := Sym2.mem_map.mp hx
  exact ha ▸ a.property

def literalBondOuterEdge : LiteralBond (box n) → OuterBoxEdge n
  | .inl e => innerBoxEdgeEmbedding n e
  | .inr x => ghostOutwardEdge n x

theorem literalBondOuterEdge_injective : Function.Injective (literalBondOuterEdge n) := by
  intro a b h
  cases a with
  | inl e =>
      cases b with
      | inl f => exact congrArg Sum.inl ((innerBoxEdgeEmbedding n).injective h)
      | inr x =>
          exact (ghostOutwardNeighbor_not_mem n x
            (innerBoxEdgeEmbedding_inside n e _ (by
              rw [show innerBoxEdgeEmbedding n e = ghostOutwardEdge n x from h]
              exact Sym2.mem_mk_right _ _))).elim
  | inr x =>
      cases b with
      | inl e =>
          exact (ghostOutwardNeighbor_not_mem n x
            (innerBoxEdgeEmbedding_inside n e _ (by
              rw [show innerBoxEdgeEmbedding n e = ghostOutwardEdge n x from h.symm]
              exact Sym2.mem_mk_right _ _))).elim
      | inr y => exact congrArg Sum.inr (ghostOutwardEdge_injective n h)

include hn in
/-- A crossing edge is either the retained ghost edge or the omitted vertical
edge at a corner. The positive-radius hypothesis excludes the singleton box. -/
theorem crossingEdge_classification
    (x : BoundaryVertex (box n)) (y : ℤ × ℤ)
    (hxy : squareLattice.Adj x.val.val y) (hy : y ∉ box n) :
    y = ghostOutwardNeighbor x ∨
      ∃ b, x.val.val = cornerPoint n b ∧ y = cornerOutwardPoint n b := by
  have hx := (mem_box_iff n x.val.val).mp x.val.property
  rw [mem_box_iff] at hy
  rw [FK.squareLattice_adj_iff] at hxy
  by_cases hx1 : x.val.val.1 = n
  · by_cases hy1 : y.1 = n + 1
    · left
      rw [ghostOutwardNeighbor, ite_eq_left hx1]
      grind
    · right
      by_cases hx2 : x.val.val.2 = n
      · refine ⟨(true, true), ?_, ?_⟩ <;> ext <;> dsimp [cornerPoint, cornerOutwardPoint] <;> omega
      · refine ⟨(true, false), ?_, ?_⟩ <;> ext <;> dsimp [cornerPoint, cornerOutwardPoint] <;> omega
  · by_cases hx1' : x.val.val.1 = -n
    · by_cases hy1 : y.1 = -n - 1
      · left
        rw [ghostOutwardNeighbor, ite_eq_right hx1, ite_eq_left hx1']
        grind
      · right
        by_cases hx2 : x.val.val.2 = n
        · refine ⟨(false, true), ?_, ?_⟩ <;> ext <;> dsimp [cornerPoint, cornerOutwardPoint] <;> omega
        · refine ⟨(false, false), ?_, ?_⟩ <;> ext <;> dsimp [cornerPoint, cornerOutwardPoint] <;> omega
    · left
      rw [ghostOutwardNeighbor, ite_eq_right hx1, ite_eq_right hx1']
      grind

def outerEdgeCoordinates (e : OuterBoxEdge n) : Sym2 (ℤ × ℤ) :=
  Sym2.map Subtype.val e.val

theorem outerEdgeCoordinates_injective : Function.Injective (outerEdgeCoordinates n) := by
  intro e f h
  apply Subtype.ext
  exact Sym2.map.injective
    Subtype.val_injective h

theorem literalBondOuterEdge_has_inner :
    ∃ x ∈ (literalBondOuterEdge n b).val, x.val ∈ box n := by
  cases b with
  | inl e =>
      refine ⟨innerBoxGraphEmbedding n e.val.out.1, ?_, e.val.out.1.property⟩
      exact Sym2.mem_map.mpr ⟨e.val.out.1, Sym2.out_fst_mem e.val, rfl⟩
  | inr x =>
      exact ⟨⟨x.val.val, box_subset_box_succ n x.val.property⟩,
        Sym2.mem_mk_left _ _, x.val.property⟩

theorem literalBondOuterEdge_ne_corner (c : Bool × Bool) :
    literalBondOuterEdge n b ≠ cornerCutEdge n c := by
  cases b with
  | inr x => exact (cornerCutEdge_ne_ghostOutwardEdge n c x).symm
  | inl e =>
      intro h
      exact cornerOutwardPoint_not_mem n c (innerBoxEdgeEmbedding_inside n e _ (by
        rw [show innerBoxEdgeEmbedding n e = cornerCutEdge n c from h]
        exact Sym2.mem_mk_right _ _))

include n in
abbrev OuterShellEdge :=
  {e : OuterBoxEdge n // ∀ x ∈ e.val, x.val ∉ box n}

include n in
abbrev OuterEdgePiece := LiteralBond (box n) ⊕ ((Bool × Bool) ⊕ OuterShellEdge n)

def outerEdgeFromPiece : OuterEdgePiece n → OuterBoxEdge n
  | .inl b => literalBondOuterEdge n b
  | .inr (.inl b) => cornerCutEdge n b
  | .inr (.inr e) => e.val

private theorem literal_ne_shell (e : OuterShellEdge n) :
    literalBondOuterEdge n b ≠ e.val := by
  intro h
  obtain ⟨x, hx, hi⟩ := literalBondOuterEdge_has_inner n b
  grind

private theorem corner_ne_shell (b : Bool × Bool) (e : OuterShellEdge n) :
    cornerCutEdge n b ≠ e.val := by
  intro h
  exact e.property _ (by
    rw [← h]
    exact Sym2.mem_mk_left _ _) (cornerPoint_mem n b)

include hn in
theorem outerEdgeFromPiece_injective :
    Function.Injective (outerEdgeFromPiece n) := by
  intro a b h
  cases a with
  | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (literalBondOuterEdge_injective n h)
      | inr b =>
          cases b with
          | inl c => exact (literalBondOuterEdge_ne_corner n a c h).elim
          | inr e => exact (literal_ne_shell n a e h).elim
  | inr a =>
      cases a with
      | inl c =>
          cases b with
          | inl a => exact (literalBondOuterEdge_ne_corner n a c h.symm).elim
          | inr b =>
              cases b with
              | inl d => exact congrArg (fun z => Sum.inr (Sum.inl z)) (cornerCutEdge_injective n hn h)
              | inr e => exact (corner_ne_shell n c e h).elim
      | inr e =>
          cases b with
          | inl a => exact (literal_ne_shell n a e h.symm).elim
          | inr b =>
              cases b with
              | inl c => exact (corner_ne_shell n c e h.symm).elim
              | inr f => exact congrArg (fun z => Sum.inr (Sum.inr z)) (Subtype.ext h)

include hn in
private theorem crossingEdge_in_range
    (u v : ↥(box (n + 1)))
    (huv : squareLattice.Adj u.val v.val) (hu : u.val ∈ box n) (hv : v.val ∉ box n) :
    ∃ b,
      outerEdgeFromPiece n b = ⟨s(u, v), (squareLattice.induce _).mem_edgeSet.mpr huv⟩ := by
  let x : BoundaryVertex (box n) := ⟨⟨u.val, hu⟩, hu, v.val, huv, hv⟩
  rcases crossingEdge_classification n hn x v.val huv hv with h | ⟨b, hb, hvb⟩
  · refine ⟨.inl (.inr x), ?_⟩
    apply outerEdgeCoordinates_injective n
    change s(u.val, ghostOutwardNeighbor x) = s(u.val, v.val)
    grind
  · refine ⟨.inr (.inl b), ?_⟩
    apply outerEdgeCoordinates_injective n
    exact congrArg₂ Sym2.mk hb.symm hvb.symm

include hn in
theorem outerEdgeFromPiece_surjective :
    Function.Surjective (outerEdgeFromPiece n) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv := (squareLattice.induce _).mem_edgeSet.mp he
      by_cases hu : u.val ∈ box n
      · by_cases hv : v.val ∈ box n
        · exact ⟨.inl (.inl ⟨s(⟨u.val, hu⟩, ⟨v.val, hv⟩), (squareLattice.induce _).mem_edgeSet.mpr huv⟩), rfl⟩
        · solve_by_elim [crossingEdge_in_range]
      · by_cases hv : v.val ∈ box n
        · obtain ⟨b, hb⟩ := crossingEdge_in_range n hn v u huv.symm hv hu
          grind [Sym2.eq_swap]
        · refine ⟨.inr (.inr ⟨⟨s(u, v), he⟩, ?_⟩), rfl⟩
          grind

/-- The exact edge-index decomposition used to sum out the wired shell and to
condition the four omitted corner bonds closed. -/
def outerBoxEdgeEquiv {n : ℕ} (hn : 0 < n) : OuterEdgePiece n ≃ OuterBoxEdge n :=
  Equiv.ofBijective _
    ⟨outerEdgeFromPiece_injective n hn, outerEdgeFromPiece_surjective n hn⟩

end
end PottsDiscontinuity.Potts
