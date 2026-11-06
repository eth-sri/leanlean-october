import RequestProject.FinitePosetCycleRealization
import RequestProject.OrderNerveRealizationMapCoordinates
import RequestProject.Tac


/-! The explicit cycle boundary parametrization is natural under a map
preserving the ordered vertex enumeration. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set Topology

bwd

namespace FiniteChains.RelativeAttachment

theorem arcConcat_natural {X Y} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) n v w
    F
    G
    (h : ∀ i t, f (F i t) = G i t) t :
    f (arcConcat n v F t) = arcConcat n w G t := by
  induction n generalizing t with
  | zero => tauto
  | succ n ih =>
    simp [arcConcat, Path.trans_apply]
    split_ifs
    · tauto
    tauto

end FiniteChains.RelativeAttachment

namespace FiniteChains.Comb
open RelativeAttachment

theorem orderNerveComparablePath_natural_bijective {P Q}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) hf
    (hb : Function.Bijective f) {a b} (h : a ≤ b ∨ b ≤ a)
    (h' : f a ≤ f b ∨ f b ≤ f a) t :
    orderNerveRealizationMap f hf (orderNerveComparablePath h t) =
      orderNerveComparablePath h' t := by
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  obtain ⟨p, rfl⟩ := hb.2 q
  simp [orderNerveRealizationCoordinates_map_injective f hf hb.1, orderNerveComparablePath_coordinates, hb.1.eq_iff]

namespace FinitePosetCycle

variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {n : ℕ}
  (C : FinitePosetCycle P n) (D : FinitePosetCycle Q n)
  (f : P → Q) (hf : Monotone f) (hv : ∀ i, f (C.vertex i) = D.vertex i)

include hv in
theorem vertex_map_bijective : Function.Bijective f := by
  constructor
  · intro a b hab
    obtain ⟨i, rfl⟩ := C.vertex.surjective a
    obtain ⟨j, rfl⟩ := C.vertex.surjective b
    simp_all
  · intro q
    obtain ⟨i, rfl⟩ := D.vertex.surjective q
    tauto

include hv in
theorem edge_natural (i : Fin (n + 1)) (t : I) :
    orderNerveRealizationMap f hf (C.edge i t) = D.edge i t := by
  have h' : f (C.vertex i.castSucc) ≤ f (C.vertex i.succ) ∨
      f (C.vertex i.succ) ≤ f (C.vertex i.castSucc) :=
    (C.consecutive i).imp (by tauto) (by tauto)
  have h := orderNerveComparablePath_natural_bijective f hf
    (C.vertex_map_bijective D f hv) (C.consecutive i) h' t
  apply h.trans
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  simp [edge, orderNerveComparablePath_coordinates, hv]

include hv in
theorem lastEdge_natural (t : I) :
    orderNerveRealizationMap f hf (C.lastEdge t) = D.lastEdge t := by
  have h' : f (C.vertex (Fin.last _)) ≤ f (C.vertex 0) ∨
      f (C.vertex 0) ≤ f (C.vertex (Fin.last _)) :=
    C.closing.imp (by tauto) (by tauto)
  have h := orderNerveComparablePath_natural_bijective f hf
    (C.vertex_map_bijective D f hv) C.closing h' t
  apply h.trans
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  simp [lastEdge, orderNerveComparablePath_coordinates, hv]

include hv in
theorem traversal_natural (t : I) :
    orderNerveRealizationMap f hf (C.traversal t) = D.traversal t := by
  have hp := arcConcat_natural _ n
    (orderNerveRealizationVertex ∘ C.vertex) (orderNerveRealizationVertex ∘ D.vertex)
    C.edge D.edge (C.edge_natural D f hf hv)
  simp [traversal, Path.trans_apply]
  split_ifs
  · exact hp _
  · exact C.lastEdge_natural D f hf hv _

theorem boundaryHomeomorph_traversal t :
    C.boundaryHomeomorph (C.traversal t) =
      unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t) := by
  apply C.boundaryHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply]
  change C.traversal t = simpleLoopBoundaryHomeomorph C.traversal
    C.traversal_surjective C.traversal_fiber
      (unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t))
  simp [simpleLoopBoundaryHomeomorph, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply, simpleLoopSquareHomeomorph_traversal]

include hv in
theorem boundaryHomeomorph_natural (x : orderNerveRealization P) :
    D.boundaryHomeomorph (orderNerveRealizationMap f hf x) = C.boundaryHomeomorph x := by
  obtain ⟨t, rfl⟩ := C.traversal_surjective x
  rw [C.traversal_natural D f hf hv, D.boundaryHomeomorph_traversal,
    C.boundaryHomeomorph_traversal]

theorem boundaryHomeomorph_natural_cast (D' : FinitePosetCycle Q m)
    hnm f' hf'
    (hv' : ∀ i, f' (C.vertex i) = D'.vertex (Fin.cast (congrArg (· + 2) hnm) i))
    x :
    D'.boundaryHomeomorph (orderNerveRealizationMap f' hf' x) = C.boundaryHomeomorph x := by
  subst m
  exact C.boundaryHomeomorph_natural D' f' hf' hv' x
