module

public import PottsDiscontinuity.Potts.GhostBoxEdgeSplit
public import PottsDiscontinuity.Potts.GhostBoundary

/-! Contraction of the wired outer shell, including its exact component partition. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

section
variable (n : ℕ)

def outerBoxWiring : FK.BoundaryCondition ↥(box (n + 1)) :=
  FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box (n + 1))}

/-- Restore a literal configuration and arbitrary shell bonds, with all four cuts closed. -/
def restoreGhostBonds {n : ℕ} (hn : 0 < n) (ω : LiteralBond (box n) → Bool)
    (η : OuterShellEdge n → Bool) : OuterBoxEdge n → Bool :=
  fun e => ((outerBoxEdgeEquiv hn).symm e).elim ω
    (fun b => b.elim (fun _ => false) η)

theorem restoreGhostBonds_piece (hn : 0 < n) (ω : LiteralBond (box n) → Bool)
    (η : OuterShellEdge n → Bool) (b : OuterEdgePiece n) :
    restoreGhostBonds hn ω η (outerEdgeFromPiece n b) =
      b.elim ω (fun c => c.elim (fun _ => false) η) := by
  change (((outerBoxEdgeEquiv hn).symm ((outerBoxEdgeEquiv hn) b)).elim ω
    (fun c => c.elim (fun _ => false) η)) = _
  simp

theorem collapseOuterBox_surjective : Function.Surjective (collapseOuterBox n) := by
  intro x
  cases x with
  | some x => exact ⟨⟨x.val, box_subset_box_succ n x.property⟩, collapseOuterBox_inner n x⟩
  | none =>
      have hnot : ((n : ℤ) + 1, 0) ∉ box n := by simp [mem_box_iff]
      exact ⟨⟨(n + 1, 0), (by grind [mem_box_iff])⟩, by simp [collapseOuterBox, hnot]⟩

theorem collapseOuterBox_ker :
    Setoid.ker (collapseOuterBox n) = (outerBoxWiring n).partition := by
  classical
  ext u v
  change collapseOuterBox n u = collapseOuterBox n v ↔
    u = v ∨ u.val ∈ vertexBoundary (box (n + 1)) ∧ v.val ∈ vertexBoundary (box (n + 1))
  rw [← outer_shell_iff_boundary u.property,
    ← outer_shell_iff_boundary v.property]
  by_cases hu : u.val ∈ box n
  · by_cases hv : v.val ∈ box n
    · constructor
      · intro h
        have hs : (some ⟨u.val, hu⟩ : Option ↥(box n)) = some ⟨v.val, hv⟩ := by
          simpa only [collapseOuterBox, dite_eq_left hu, dite_eq_left hv] using h
        grind
      · grind
    · constructor
      · intro h
        cases (by simpa only [collapseOuterBox, dite_eq_left hu, dite_eq_right hv] using h)
      · grind
  · by_cases hv : v.val ∈ box n
    · constructor
      · intro h
        cases (by simpa only [collapseOuterBox, dite_eq_right hu, dite_eq_left hv] using h)
      · grind
    · simp_all [collapseOuterBox, dite_eq_right hu, dite_eq_right hv]

@[simp] theorem collapseOuterBox_embedding (x : ↥(box n)) :
    collapseOuterBox n (innerBoxGraphEmbedding n x) = some x := collapseOuterBox_inner n x

end

theorem openGraph_bool_adj_iff {V : Type*} [Finite V] {G : SimpleGraph V}
    (ω : G.edgeSet → Bool) (u v : V) :
    (FK.openGraph (FK.boolConfigurationEquiv G ω)).Adj u v ↔
      ∃ h, ω ⟨s(u, v), G.mem_edgeSet.mpr h⟩ = true := by
  simp [FK.openGraph_adj, FK.openEdges_boolConfigurationEquiv]

variable (n : ℕ) (hn : 0 < n) (ω : LiteralBond (box n) → Bool) (η : OuterShellEdge n → Bool)

private theorem restored_edge_maps_reachable
    {e : OuterBoxEdge n} (he : restoreGhostBonds hn ω η e = true)
    (u v : ↥(box (n + 1))) (huv : s(u, v) = e.val) :
    (ghostOpenGraph ω).Reachable (collapseOuterBox n u) (collapseOuterBox n v) := by
  obtain ⟨b, rfl⟩ := outerEdgeFromPiece_surjective n hn e
  rw [restoreGhostBonds_piece] at he
  cases b with
  | inl b =>
      cases b with
      | inl e =>
          rcases e with ⟨e, heG⟩
          induction e using Sym2.inductionOn with
          | _ a b =>
              have hadj : (ghostOpenGraph ω).Adj (some a) (some b) :=
                (openGraph_bool_adj_iff _ a b).mpr ⟨((squareLattice.induce _).mem_edgeSet.mp heG), he⟩
              change _ = s(innerBoxGraphEmbedding n a, innerBoxGraphEmbedding n b) at huv
              rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · simpa only [collapseOuterBox_embedding] using hadj.reachable
              · simpa only [collapseOuterBox_embedding] using hadj.symm.reachable
      | inr x =>
          have hadj : (ghostOpenGraph ω).Adj (some x.val) none := ⟨x.property, he⟩
          rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simpa using hadj.reachable
          · simpa using hadj.symm.reachable
  | inr b =>
      cases b with
      | inl b => exact Bool.noConfusion he
      | inr e =>
          have hu' : collapseOuterBox n u = none := by simp [collapseOuterBox, (e.property u (huv ▸ Sym2.mem_mk_left u v))]
          have hv' : collapseOuterBox n v = none := by simp [collapseOuterBox, (e.property v (huv ▸ Sym2.mem_mk_right u v))]
          simp_all

/-- The outer wired partition is exactly the pullback of the literal ghost
connection partition. Shell bonds have no effect on this partition. -/
theorem outer_componentSetoid_eq_ghost_comap :
    FK.componentSetoid (outerBoxWiring n) (FK.boolConfigurationEquiv _ (restoreGhostBonds hn ω η)) =
      (ghostOpenGraph ω).reachableSetoid.comap (collapseOuterBox n) := by
  let carrier := Set (ℤ × ℤ)
  let domain := box (n + 1)
  let G := squareLattice.induce (domain : carrier)
  let R := FK.componentSetoid (outerBoxWiring n) (FK.boolConfigurationEquiv G (restoreGhostBonds hn ω η))
  let f := collapseOuterBox n
  have hker : Setoid.ker f ≤ R := by
    rw [show Setoid.ker f = (outerBoxWiring n).partition from collapseOuterBox_ker n]
    exact le_sup_right
  apply le_antisymm
  · apply sup_le
    · apply FK.reachableSetoid_le_of_adj
      intro u v h
      obtain ⟨huv, hh⟩ := (openGraph_bool_adj_iff _ u v).mp h
      exact restored_edge_maps_reachable n hn ω η hh u v rfl
    · rw [← collapseOuterBox_ker n]
      intro u v h
      change f u = f v at h
      change (ghostOpenGraph ω).reachableSetoid (f u) (f v)
      simp_all
  · have hmap : (ghostOpenGraph ω).reachableSetoid ≤ R.map f := by
      apply FK.reachableSetoid_le_of_adj
      intro u v h
      have hgen {a b : ↥(domain : carrier)} (hab : R a b) :
          (R.map f) (f a) (f b) :=
        Relation.EqvGen.rel _ _ (by grind)
      have hcross (x : ↥(box n : carrier))
          (hx : x.val ∈ vertexBoundary (box n)) (hh : ω (.inr ⟨x, hx⟩) = true) :
          (R.map f) (some x) none := by
        let a : ↥(domain : carrier) := ⟨x.val, box_subset_box_succ n x.property⟩
        let b : ↥(domain : carrier) :=
          ⟨ghostOutwardNeighbor ⟨x, hx⟩, ghostOutwardNeighbor_mem_outer ⟨x, hx⟩⟩
        have hb : restoreGhostBonds hn ω η (ghostOutwardEdge n ⟨x, hx⟩) = true := by
          rw [show ghostOutwardEdge n ⟨x, hx⟩ = outerEdgeFromPiece n (.inl (.inr ⟨x, hx⟩)) from rfl,
            restoreGhostBonds_piece]
          exact hh
        have hr := FK.actualConnected_component (outerBoxWiring n) ((openGraph_bool_adj_iff _ a b).mpr ⟨ghostOutwardNeighbor_adj n ⟨x, hx⟩, hb⟩).reachable
        simpa only [f, a, b, collapseOuterBox_inner, collapseOuterBox_outward] using hgen hr
      cases u with
      | none =>
          cases v with
          | none => exact h.elim
          | some x => obtain ⟨hx, hh⟩ := h; exact (hcross x hx hh).symm
      | some x =>
          cases v with
          | none => obtain ⟨hx, hh⟩ := h; exact hcross x hx hh
          | some y =>
              obtain ⟨hxy, hh⟩ := (openGraph_bool_adj_iff _ x y).mp h
              let a := innerBoxGraphEmbedding n x
              let b := innerBoxGraphEmbedding n y
              have hb : restoreGhostBonds hn ω η
                  (innerBoxEdgeEmbedding n ⟨s(x, y), (squareLattice.induce _).mem_edgeSet.mpr hxy⟩) = true := by
                rw [show innerBoxEdgeEmbedding n ⟨s(x, y), _⟩ =
                  outerEdgeFromPiece n (.inl (.inl ⟨s(x, y), _⟩)) from rfl, restoreGhostBonds_piece]
                exact hh
              have hr := FK.actualConnected_component (outerBoxWiring n) ((openGraph_bool_adj_iff _ a b).mpr ⟨hxy, hb⟩).reachable
              simpa only [f, a, b, collapseOuterBox_embedding] using hgen hr
    intro u v h
    exact (Setoid.ext_iff.mp (Setoid.comap_map_of_ker_le f R hker) u v).mp (hmap h)

theorem outer_componentCount_eq_ghost :
    FK.componentCount (outerBoxWiring n)
        (FK.boolConfigurationEquiv _ (restoreGhostBonds hn ω η)) =
      ghostComponentCount ω := by
  rw [FK.componentCount, outer_componentSetoid_eq_ghost_comap, Setoid.comap_eq]
  exact Nat.card_congr (Setoid.quotientKerEquivOfSurjective _
    (Quotient.mk_surjective.comp (collapseOuterBox_surjective n)))

end
end PottsDiscontinuity.Potts
