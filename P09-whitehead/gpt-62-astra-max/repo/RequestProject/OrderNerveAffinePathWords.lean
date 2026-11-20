module

public import RequestProject.OrderNerveAffineEdgePath
public import RequestProject.ContinuousEdgeWordHomotopies


@[expose] public section

/-! Actual affine realization of composable order-edge words, with exact
monotone-map naturality. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open ContinuousEdgeWords CategoryTheory Simplicial

variable {P : Type} [PartialOrder P]

def affineOrderWordPath (l : List _) {a b : P}
    (hl : IsPath _ _ l a b) :=
  realize (orderCx P).src (orderCx P).tgt _
    (fun e => orderNerveAffineEdgePath (P := P) e.property) l hl

theorem affineGermPath_coordinates (g : (orderCx P).E × Bool) (t : I) (p : P) :
    orderNerveRealizationCoordinates P
      (germPath (orderCx P).src (orderCx P).tgt (orderNerveRealizationVertex (P := P))
        (fun e => orderNerveAffineEdgePath (P := P) e.property) g t) p =
      (1 - t) * (if germSrc (orderCx P).src (orderCx P).tgt g = p then 1 else 0) +
        t * (if germTgt (orderCx P).src (orderCx P).tgt g = p then 1 else 0) := by
  rcases g with ⟨e, b⟩
  cases b
  · simp only [germPath, Path.symm_apply, Function.comp_apply, orderNerveAffineEdgePath_coordinates,
      unitInterval.coe_symm_eq, germSrc_false, germTgt_false]
    ring
  · apply orderNerveAffineEdgePath_coordinates

theorem comparablePath_homotopic_single {a b : P} (h : a ≤ b ∨ b ≤ a)
    (g : (orderCx P).E × Bool)
    (hs : a = germSrc _ (orderCx P).tgt g)
    (ht : germTgt _ (orderCx P).tgt g = b) :
    (orderNerveComparablePath h).Homotopic (affineOrderWordPath [g] ⟨hs, ht⟩) := by
  subst a
  subst b
  have he : orderNerveComparablePath h =
      germPath (orderCx P).src (orderCx P).tgt _
        (fun e => orderNerveAffineEdgePath (P := P) e.property) g := by
    apply Path.ext
    funext t
    apply orderNerveRealizationCoordinates_injective P
    ext <;> simp_all [orderNerveComparablePath_coordinates, affineGermPath_coordinates]
  erw [he]
  exact (Path.Homotopic.trans_refl _).symm

variable {Q : Type} [PartialOrder Q] (f : P → Q) (hf : Monotone f)
include Q

theorem affineWord_map_vertex (p : P) :
    orderNerveRealizationMap f hf (orderNerveRealizationVertex p) =
      orderNerveRealizationVertex (f p) := congrArg (fun k : TopCat.of (SimplexCategory.toTop.obj ⦋0⦌) ⟶
      orderNerveRealization Q => k default)
    (orderNerveRealizationSimplex_natural f hf (ComposableArrows.mk₀ p))

theorem affineGermPath_map (g : (orderCx P).E × Bool) (t : I) :
    orderNerveRealizationMap f hf
      (germPath (orderCx P).src (orderCx P).tgt (orderNerveRealizationVertex (P := P))
        (fun e => orderNerveAffineEdgePath (P := P) e.property) g t) =
      germPath (orderCx Q).src (orderCx Q).tgt _
        (fun e => orderNerveAffineEdgePath (P := Q) e.property)
        ((orderCxMap f hf).onE g.1, g.2) t := by
  rcases g with ⟨e, b⟩
  cases b
  · change orderNerveRealizationMap f hf
      (orderNerveAffineEdgePath e.property (unitInterval.symm t)) =
        orderNerveAffineEdgePath (hf e.property) _
    simpa only [orderNerveComparablePath, dif_pos e.property, dif_pos (hf e.property)] using
      orderNerveComparablePath_natural f hf (Or.inl e.property)
        (Or.inl (hf e.property)) _
  · change orderNerveRealizationMap f hf (orderNerveAffineEdgePath e.property t) =
      orderNerveAffineEdgePath (hf e.property) t
    simpa only [orderNerveComparablePath, dif_pos e.property, dif_pos (hf e.property)] using
      orderNerveComparablePath_natural f hf (Or.inl e.property) (Or.inl (hf e.property)) t

theorem affineOrderWordPath_map (l : List _) {a b : P}
    (hl : IsPath _ _ l a b) (t : I) :
    orderNerveRealizationMap f hf (affineOrderWordPath l hl t) =
      affineOrderWordPath (mapPath (orderCxMap f hf) l)
        (isPath_mapPath (orderCxMap f hf) hl) t := by
  induction l generalizing a t with
  | nil =>
    apply affineWord_map_vertex
  | cons g l ih =>
    obtain ⟨rfl, ht⟩ := hl
    simp only [affineOrderWordPath, realize, mapPath, List.map_cons, Path.trans_apply, Path.cast_coe]
    split_ifs with hhalf
    · apply affineGermPath_map
    · rcases g with ⟨e, direction⟩
      cases direction <;> simpa only [affineOrderWordPath, mapPath] using
        ih ht ⟨2 * t - 1, by grind⟩

end FiniteChains.Comb
