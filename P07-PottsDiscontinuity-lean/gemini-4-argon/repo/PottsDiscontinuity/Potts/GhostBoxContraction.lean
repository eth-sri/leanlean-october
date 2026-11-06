module

public import PottsDiscontinuity.Potts.GhostBoxEdgeSplit
public import PottsDiscontinuity.Potts.GhostBoundary

/-! Contraction of the wired outer shell, including its exact component partition. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

def outerBoxWiring (n : ℕ) : FK.BoundaryCondition ↥(box (n + 1) : Set (ℤ × ℤ)) :=
  FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box (n + 1))}

/-- Restore a literal configuration and arbitrary shell bonds, with all four cuts closed. -/
def restoreGhostBonds (n : ℕ) (hn : 0 < n) (ω : LiteralBond (box n) → Bool)
    (η : OuterShellEdge n → Bool) : OuterBoxEdge n → Bool :=
  fun e => ((outerBoxEdgeEquiv n hn).symm e).elim ω
    (fun b => b.elim (fun _ => false) η)

theorem restoreGhostBonds_piece (n : ℕ) (hn : 0 < n) (ω : LiteralBond (box n) → Bool)
    (η : OuterShellEdge n → Bool) (b : OuterEdgePiece n) :
    restoreGhostBonds n hn ω η (outerEdgeFromPiece n b) =
      b.elim ω (fun c => c.elim (fun _ => false) η) := by
  change (((outerBoxEdgeEquiv n hn).symm ((outerBoxEdgeEquiv n hn) b)).elim ω
    (fun c => c.elim (fun _ => false) η)) = _
  rw [Equiv.symm_apply_apply]

theorem collapseOuterBox_surjective (n : ℕ) : Function.Surjective (collapseOuterBox n)
  | some x => ⟨⟨x.val, box_subset_box_succ n x.property⟩, collapseOuterBox_inner n x⟩
  | none =>
      ⟨⟨((n : ℤ) + 1, 0), show ((n : ℤ) + 1, 0) ∈ box (n + 1) by rw [mem_box_iff]; dsimp; omega⟩,
        by simp [collapseOuterBox, show ((n : ℤ) + 1, 0) ∉ box n by rw [mem_box_iff]; dsimp; omega]⟩

theorem collapseOuterBox_ker (n : ℕ) :
    Setoid.ker (collapseOuterBox n) = (outerBoxWiring n).partition := by
  classical
  ext u v
  change collapseOuterBox n u = collapseOuterBox n v ↔
    u = v ∨ u.val ∈ vertexBoundary (box (n + 1)) ∧ v.val ∈ vertexBoundary (box (n + 1))
  rw [← outer_shell_iff_boundary n u.val u.property,
    ← outer_shell_iff_boundary n v.val v.property]
  by_cases hu : u.val ∈ box n <;> by_cases hv : v.val ∈ box n <;>
    simp [collapseOuterBox, hu, hv] <;> rintro rfl <;> contradiction

@[simp] theorem collapseOuterBox_embedding (n : ℕ) (x : ↥(box n : Set (ℤ × ℤ))) :
    collapseOuterBox n (innerBoxGraphEmbedding n x) = some x :=
  collapseOuterBox_inner n x

theorem openGraph_bool_adj_iff {V : Type*} [Finite V] (G : SimpleGraph V)
    (ω : G.edgeSet → Bool) (u v : V) :
    (FK.openGraph G (FK.boolConfigurationEquiv G ω)).Adj u v ↔
      ∃ h : G.Adj u v, ω ⟨s(u, v), G.mem_edgeSet.mpr h⟩ = true := by
  rw [FK.openGraph_adj, FK.openEdges_boolConfigurationEquiv]
  exact ⟨fun ⟨h, hh⟩ => ⟨G.mem_edgeSet.mp h, hh⟩, fun ⟨h, hh⟩ => ⟨G.mem_edgeSet.mpr h, hh⟩⟩

private theorem restored_edge_maps_reachable (n : ℕ) (hn : 0 < n)
    (ω : LiteralBond (box n) → Bool) (η : OuterShellEdge n → Bool)
    (e : OuterBoxEdge n) (he : restoreGhostBonds n hn ω η e = true)
    (u v : ↥(box (n + 1) : Set (ℤ × ℤ))) (huv : s(u, v) = e.val) :
    (ghostOpenGraph (box n) ω).Reachable (collapseOuterBox n u) (collapseOuterBox n v) := by
  obtain ⟨(⟨e, heG⟩ | x) | (b | e), rfl⟩ := outerEdgeFromPiece_surjective n hn e <;>
    rw [restoreGhostBonds_piece] at he
  · induction e using Sym2.inductionOn with
    | _ a b =>
        have hadj : (ghostOpenGraph (box n) ω).Adj (some a) (some b) :=
          (openGraph_bool_adj_iff _ _ a b).mpr ⟨(squareLattice.induce _).mem_edgeSet.mp heG, he⟩
        change s(u, v) = s(innerBoxGraphEmbedding n a, innerBoxGraphEmbedding n b) at huv
        rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          [simpa only [collapseOuterBox_embedding] using hadj.reachable;
           simpa only [collapseOuterBox_embedding] using hadj.symm.reachable]
  · have hadj : (ghostOpenGraph (box n) ω).Adj (some x.val) none := ⟨x.property, he⟩
    change s(u, v) = s(⟨x.val.val, _⟩, ⟨ghostOutwardNeighbor n x, _⟩) at huv
    rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      [simpa only [collapseOuterBox_inner, collapseOuterBox_outward] using hadj.reachable;
       simpa only [collapseOuterBox_inner, collapseOuterBox_outward] using hadj.symm.reachable]
  · exact Bool.noConfusion he
  · have hu : u.val ∉ box n := e.property u (huv ▸ Sym2.mem_mk_left u v)
    have hv : v.val ∉ box n := e.property v (huv ▸ Sym2.mem_mk_right u v)
    simp [collapseOuterBox, hu, hv]

/-- The outer wired partition is exactly the pullback of the literal ghost
connection partition. Shell bonds have no effect on this partition. -/
theorem outer_componentSetoid_eq_ghost_comap (n : ℕ) (hn : 0 < n)
    (ω : LiteralBond (box n) → Bool) (η : OuterShellEdge n → Bool) :
    FK.componentSetoid _ (outerBoxWiring n) (FK.boolConfigurationEquiv _ (restoreGhostBonds n hn ω η)) =
      (ghostOpenGraph (box n) ω).reachableSetoid.comap (collapseOuterBox n) := by
  let G := squareLattice.induce (box (n + 1) : Set (ℤ × ℤ))
  let C := FK.boolConfigurationEquiv G (restoreGhostBonds n hn ω η)
  let R := FK.componentSetoid G (outerBoxWiring n) C
  let f := collapseOuterBox n
  have hker : Setoid.ker f ≤ R := by
    rw [show Setoid.ker f = (outerBoxWiring n).partition from collapseOuterBox_ker n]
    exact le_sup_right
  refine le_antisymm (sup_le ?_ ?_) ?_
  · apply FK.reachableSetoid_le_of_adj; intro u v h
    obtain ⟨huv, hh⟩ := (openGraph_bool_adj_iff G (restoreGhostBonds n hn ω η) u v).mp h
    exact restored_edge_maps_reachable n hn ω η ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ hh u v rfl
  · rw [← collapseOuterBox_ker n]
    intro u v (h : f u = f v)
    change (ghostOpenGraph (box n) ω).reachableSetoid (f u) (f v)
    rw [h]
  · have hmap : (ghostOpenGraph (box n) ω).reachableSetoid ≤ R.map f := by
      apply FK.reachableSetoid_le_of_adj; intro u v h
      have hgen {a b : ↥(box (n + 1) : Set (ℤ × ℤ))} (hab : R a b) : (R.map f) (f a) (f b) :=
        Relation.EqvGen.rel _ _ ⟨a, b, hab, rfl, rfl⟩
      have hcross (x : ↥(box n : Set (ℤ × ℤ)))
          (hx : x.val ∈ vertexBoundary (box n)) (hh : ω (.inr ⟨x, hx⟩) = true) :
          (R.map f) (some x) none := by
        let a : ↥(box (n + 1) : Set (ℤ × ℤ)) := ⟨x.val, box_subset_box_succ n x.property⟩
        let b : ↥(box (n + 1) : Set (ℤ × ℤ)) :=
          ⟨ghostOutwardNeighbor n ⟨x, hx⟩, ghostOutwardNeighbor_mem_outer n ⟨x, hx⟩⟩
        have hb : restoreGhostBonds n hn ω η (ghostOutwardEdge n ⟨x, hx⟩) = true := by
          rw [show ghostOutwardEdge n ⟨x, hx⟩ = outerEdgeFromPiece n (.inl (.inr ⟨x, hx⟩)) from rfl,
            restoreGhostBonds_piece]; exact hh
        have hadj : (FK.openGraph G C).Adj a b :=
          (openGraph_bool_adj_iff G _ a b).mpr ⟨ghostOutwardNeighbor_adj n ⟨x, hx⟩, hb⟩
        simpa only [f, a, b, collapseOuterBox_inner, collapseOuterBox_outward] using
          hgen (FK.actualConnected_component G (outerBoxWiring n) C hadj.reachable)
      cases u <;> cases v
      · exact h.elim
      · exact (hcross _ h.1 h.2).symm
      · exact hcross _ h.1 h.2
      · obtain ⟨hxy, hh⟩ := (openGraph_bool_adj_iff _ (fun e => ω (.inl e)) _ _).mp h
        have hb : restoreGhostBonds n hn ω η
            (innerBoxEdgeEmbedding n ⟨s(_, _), (squareLattice.induce _).mem_edgeSet.mpr hxy⟩) = true := by
          rw [show innerBoxEdgeEmbedding n ⟨s(_, _), _⟩ =
            outerEdgeFromPiece n (.inl (.inl ⟨s(_, _), _⟩)) from rfl, restoreGhostBonds_piece]
          exact hh
        have hadj : (FK.openGraph G C).Adj (innerBoxGraphEmbedding n _) (innerBoxGraphEmbedding n _) :=
          (openGraph_bool_adj_iff G _ _ _).mpr ⟨hxy, hb⟩
        simpa only [f, collapseOuterBox_embedding] using
          hgen (FK.actualConnected_component G (outerBoxWiring n) C hadj.reachable)
    intro u v h
    exact (Setoid.ext_iff.mp (Setoid.comap_map_of_ker_le f R hker) u v).mp (hmap h)

theorem outer_componentCount_eq_ghost (n : ℕ) (hn : 0 < n)
    (ω : LiteralBond (box n) → Bool) (η : OuterShellEdge n → Bool) :
    FK.componentCount _ (outerBoxWiring n)
        (FK.boolConfigurationEquiv _ (restoreGhostBonds n hn ω η)) =
      ghostComponentCount (box n) ω := by
  rw [FK.componentCount, outer_componentSetoid_eq_ghost_comap, Setoid.comap_eq]
  exact Nat.card_congr (Setoid.quotientKerEquivOfSurjective _
    (Quotient.mk_surjective.comp (collapseOuterBox_surjective n)))

end
end PottsDiscontinuity.Potts
