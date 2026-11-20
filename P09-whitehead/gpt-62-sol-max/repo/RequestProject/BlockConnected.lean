module

public import RequestProject.BlockSpinePres

@[expose] public section

/-!
# The block is connected, so it carries a spanning tree

The marked presentation of the block is read off a spanning tree of the one-skeleton of the
order complex of the poset `FiniteChains.Davis.QOld A` of retained cubes.  This file proves that
such a tree exists: the block is connected.

The argument is the one for the cube complex `C(L)` with the all-positive vertex removed.  Every
cube lies above a vertex cube `(∅, ξ)` with `ξ ≠ 0` — for a cube with nonempty type one flips a
sign in one of its own directions, which does not change the cube — and two vertex cubes are
joined by flipping their signs one coordinate at a time through the edge cubes `({v}, ξ)`,
keeping the coordinate of a fixed vertex equal to `1` so that the removed vertex `(∅, 0)` is
never met.

* `FiniteChains.Davis.isConnected_orderCx_qOld` — the order complex of the block is connected;
* `FiniteChains.Davis.exists_spanningTree_qOld` — hence it has a spanning tree with any
  prescribed root, in particular rooted at a cell of the cut surface.
-/


namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- Being joined by an edge path in the block. -/
def ConnQ (a b : QOld A) : Prop :=
  ∃ p, IsPath (orderCx (QOld A)).src (orderCx (QOld A)).tgt p a b

namespace ConnQ

omit [Fintype V] in
theorem refl (a : QOld A) : ConnQ a a := ⟨[], rfl⟩

omit [Fintype V] in
theorem symm {a b : QOld A} (h : ConnQ a b) : ConnQ b a :=
  ⟨revPath h.choose, isPath_revPath h.choose_spec⟩

omit [Fintype V] in
theorem trans {a b c : QOld A} (h : ConnQ a b) (h' : ConnQ b c) : ConnQ a c :=
  ⟨h.choose ++ h'.choose, h.choose_spec.append h'.choose_spec⟩

omit [Fintype V] in
theorem of_le {a b : QOld A} (h : a ≤ b) : ConnQ a b := ⟨[ordPos h], isPath_ordPos h⟩

omit [Fintype V] in
theorem of_ge {a b : QOld A} (h : b ≤ a) : ConnQ a b := ⟨[ordNeg h], isPath_ordNeg h⟩

end ConnQ

/-- **A vertex cube**: the cube `(∅, ξ)` of a nonzero sign vector. -/
def vtxCube (ξ : V → ZMod 2) (hξ : ξ ≠ 0) : QOld A :=
  ⟨⟨∅, ξ, isSimplex_empty (A := A), fun v hv => absurd hv (Finset.notMem_empty v)⟩,
    fun h => hξ h.2⟩

/-- **An edge cube**: the cube `({v}, ξ)` with the sign at `v` normalised away. -/
def oneCube (v : V) (ξ : V → ZMod 2) : QOld A :=
  ⟨⟨{v}, Function.update ξ v 0, isSimplex_singleton (A := A) v, fun w hw => by
      simp_all⟩,
    fun h => by simpa using congrArg (fun s  => v ∈ s) h.1⟩

omit [Fintype V] in
theorem vtxCube_le_oneCube {ξ : V → ZMod 2} (hξ : ξ ≠ 0) (v : V) :
    (vtxCube ξ hξ : QOld A) ≤ oneCube v ξ := by
  refine ⟨Finset.empty_subset _, fun w hw => ?_⟩
  have hwv : w ≠ v := fun h => hw (by rw [h]; exact Finset.mem_singleton_self v)
  simp [oneCube, vtxCube, hwv]

omit [Fintype V] in
theorem vtxCube_update_le_oneCube {ξ : V → ZMod 2} (v : V) (a : ZMod 2)
    (h : Function.update ξ v a ≠ 0) :
    (vtxCube (Function.update ξ v a) h : QOld A) ≤ oneCube v ξ := by
  refine ⟨Finset.empty_subset _, fun w hw => ?_⟩
  have hwv : w ≠ v := fun h' => hw (by rw [h']; exact Finset.mem_singleton_self v)
  simp [oneCube, vtxCube, hwv]

/-- The support of a sign vector. -/
noncomputable def sgnSupport (ξ : V → ZMod 2) : Finset V :=
  Finset.univ.filter (fun v => ξ v ≠ 0)

omit [DecidableEq V] in
theorem mem_sgnSupport {ξ : V → ZMod 2} {v : V} : v ∈ sgnSupport ξ ↔ ξ v ≠ 0 := by
  simp [sgnSupport]

/-- The distinguished sign vector: `1` at `v₀` and `0` elsewhere. -/
def unitSgn (v₀ : V) : V → ZMod 2 := fun w => if w = v₀ then 1 else 0

omit [Fintype V] in
theorem unitSgn_ne_zero (v₀ : V) : unitSgn (V := V) v₀ ≠ 0 := by
  intro h
  simpa [unitSgn] using congrFun h v₀

/-- Sign vertices with nonzero support are connected by changes in one coordinate.
First set the distinguished coordinate, then erase all the other nonzero coordinates. -/
theorem signVertex_connected {X : Type*} {R : X → X → Prop}
    (hrefl : ∀ x, R x x) (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (vertex : ∀ ξ : V → ZMod 2, ξ ≠ 0 → X)
    (hmove : ∀ ξ hξ v b hb, R (vertex ξ hξ) (vertex (Function.update ξ v b) hb))
    (v₀ : V) (ξ : V → ZMod 2) (hξ : ξ ≠ 0) :
    R (vertex ξ hξ) (vertex (unitSgn v₀) (unitSgn_ne_zero v₀)) := by
  classical
  have nz (x : V → ZMod 2) (hx : x v₀ = 1) : x ≠ 0 := by
    intro h
    simpa [hx] using congrFun h v₀
  have key (n : ℕ) : ∀ (x : V → ZMod 2), (sgnSupport x).card = n → ∀ hx : x v₀ = 1,
      R (vertex x (nz x hx)) (vertex (unitSgn v₀) (unitSgn_ne_zero v₀)) := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hn hx
      by_cases he : ∃ w, w ≠ v₀ ∧ x w ≠ 0
      · obtain ⟨w, hw, hw₀⟩ := he
        let y := Function.update x w 0
        have hy : y v₀ = 1 := by simp [y, hw.symm, hx]
        have hsupport : sgnSupport y = (sgnSupport x).erase w := by
          ext a
          by_cases ha : a = w <;> simp [mem_sgnSupport, y, ha]
        have hlt : (sgnSupport y).card < (sgnSupport x).card := by
          rw [hsupport]
          exact Finset.card_erase_lt_of_mem (mem_sgnSupport.2 hw₀)
        exact htrans (hmove x (nz x hx) w 0 (nz y hy)) (ih _ (hn ▸ hlt) y rfl hy)
      · have h : x = unitSgn v₀ := by
          funext w
          by_cases hw : w = v₀
          · simp [unitSgn, hw, hx]
          · have : x w = 0 := by by_contra h; exact he ⟨w, hw, h⟩
            simp [unitSgn, hw, this]
        subst x
        exact hrefl _
  have hroot : Function.update ξ v₀ 1 v₀ = 1 := Function.update_self ..
  exact htrans (hmove ξ hξ v₀ 1 (nz _ hroot)) (key _ _ rfl hroot)

omit [Fintype V] in
/-- **Every cell of the block is joined to a vertex cube.** -/
theorem connQ_to_vtxCube (c : QOld A) :
    ∃ (ξ : V → ZMod 2) (hξ : ξ ≠ 0), ConnQ c (vtxCube ξ hξ) := by
  by_cases hs : c.1.spx = ∅
  · have hne  := fun h => c.2 ⟨hs, h⟩
    refine ⟨c.1.sgn, hne, ?_⟩
    have hEq : c = vtxCube c.1.sgn hne := by
      apply Subtype.ext
      exact QCube.ext' (by assumption) (fun v _ => rfl)
    tauto
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.2 hs
    refine ⟨Function.update c.1.sgn v 1, ?_, ?_⟩
    · intro h
      simpa using congrFun h v
    · refine ConnQ.of_ge ⟨Finset.empty_subset _, fun w hw => ?_⟩
      have hwv : w ≠ v := fun h => hw (h ▸ hv)
      simp [vtxCube, hwv]

/-- **The block is connected.** -/
theorem isConnected_orderCx_qOld [Nonempty V] : IsConnected (orderCx (QOld A)) := by
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have key : ∀ c : QOld A, ConnQ c (vtxCube (unitSgn v₀) (unitSgn_ne_zero v₀)) := by
    intro c
    obtain ⟨ξ, hξ, hc⟩ := connQ_to_vtxCube c
    exact hc.trans (signVertex_connected ConnQ.refl (fun h h' => h.trans h') vtxCube
      (fun _ hξ v b hb => (ConnQ.of_le (vtxCube_le_oneCube hξ v)).trans
        (ConnQ.of_ge (vtxCube_update_le_oneCube v b hb))) v₀ ξ hξ)
  intro a b
  exact ((key a).trans (key b).symm)

/-- **The block carries a spanning tree with any prescribed root**, in particular one rooted at a
cell of the cut surface. -/
theorem exists_spanningTree_qOld [Nonempty V] (r : QOld A) :
    ∃ T : SpanningTree (orderCx (QOld A)), T.root = r :=
  SpanningTree.exists_of_isConnected isConnected_orderCx_qOld r

end Davis
end FiniteChains
