import RequestProject.OrderNerveAffineEdgePath
import RequestProject.ContinuousEdgeWordHomotopies
import RequestProject.CombPi1
import RequestProject.Tac


/-! Actual affine realization of composable order-edge words, with exact
monotone-map naturality. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
bwd

namespace FiniteChains.Comb
open ContinuousEdgeWords CategoryTheory Simplicial

variable {P : Type} [PartialOrder P]

def affineOrderWordPath l {a b : P}
    (hl : IsPathX (orderCx P) l a b) :=
  realize (orderCx P).src (orderCx P).tgt _
    (orderNerveAffineEdgePath (P := P) ·.property) l hl

theorem affineGermPath_coordinates g t p :
    orderNerveRealizationCoordinates P
      (germPath (orderCx P).src (orderCx P).tgt (orderNerveRealizationVertex (P := P))
        (orderNerveAffineEdgePath (P := P) ·.property) g t) p =
      (1 - t) * (if gSrcX (orderCx P) g = p then 1 else 0) +
        t * (if gTgtX (orderCx P) g = p then 1 else 0) := by
  cases' g with e b
  cases b
  · simp [germPath, Path.symm_apply, Function.comp_apply, orderNerveAffineEdgePath_coordinates,
      unitInterval.coe_symm_eq, germSrc_false, germTgt_false]
    ring
  · exact orderNerveAffineEdgePath_coordinates e.property t p

theorem comparablePath_homotopic_single {a b : P} h
    g
    (hs : a = gSrcX (orderCx P) g)
    (ht : gTgtX (orderCx P) g = b) :
    (orderNerveComparablePath h).Homotopic (affineOrderWordPath [g] ⟨hs, ht⟩) := by
  subst a
  subst b
  have he : orderNerveComparablePath h =
      germPath (orderCx P).src (orderCx P).tgt _
        (orderNerveAffineEdgePath (P := P) ·.property) g := by
    apply Path.ext
    funext t
    apply orderNerveRealizationCoordinates_injective P
    grind [orderNerveComparablePath_coordinates, affineGermPath_coordinates]
  rwd [he]
  exact (Path.Homotopic.trans_refl _).symm

theorem affineWord_map_vertex {Q} [PartialOrder Q]
    (f : P → Q) hf p :
    orderNerveRealizationMap f hf (orderNerveRealizationVertex p) =
      orderNerveRealizationVertex (f p) := congrArg (fun k : TopCat.of (SimplexCategory.toTop.obj ⦋0⦌) ⟶
      orderNerveRealization Q => k default)
    (orderNerveRealizationSimplex_natural f hf _)

theorem affineGermPath_map {Q} [PartialOrder Q]
    f hf g t :
    orderNerveRealizationMap f hf
      (germPath (orderCx P).src (orderCx P).tgt (orderNerveRealizationVertex (P := P))
        (orderNerveAffineEdgePath (P := P) ·.property) g t) =
      germPath (orderCx Q).src (orderCx Q).tgt (orderNerveRealizationVertex (P := Q))
        (orderNerveAffineEdgePath (P := Q) ·.property)
        ((orderCxMap f hf).onE g.1, g.2) t := by
  cases' g with e b
  cases b
  · change orderNerveRealizationMap f hf
      (orderNerveAffineEdgePath e.property (unitInterval.symm t)) =
        orderNerveAffineEdgePath (hf e.property) (unitInterval.symm t)
    simpa [orderNerveComparablePath, dif_pos e.property, dif_pos (hf e.property)] using
      orderNerveComparablePath_natural f hf (Or.inl e.property)
        (Or.inl (hf e.property)) _
  · change orderNerveRealizationMap f hf (orderNerveAffineEdgePath e.property t) =
      orderNerveAffineEdgePath (hf e.property) t
    simpa [orderNerveComparablePath, dif_pos e.property, dif_pos (hf e.property)] using
      orderNerveComparablePath_natural f hf (Or.inl e.property) (Or.inl (hf e.property)) t

theorem affineOrderWordPath_map {Q} [PartialOrder Q]
    (f : P → Q) hf l {a b : P}
    (hl : IsPathX (orderCx P) l a b) t :
    orderNerveRealizationMap f hf (affineOrderWordPath l hl t) =
      affineOrderWordPath (mapPath (orderCxMap f hf) l)
        (isPath_mapPath (orderCxMap f hf) hl) t := by
  induction l generalizing a t with
  | nil =>
    cases hl
    exact affineWord_map_vertex f hf b
  | cons g l ih =>
    obtain ⟨rfl, ht⟩ := hl
    simp [affineOrderWordPath, realize, mapPath, List.map_cons, Path.trans_apply, Path.cast_coe]
    split_ifs with hhalf
    · exact affineGermPath_map f hf g _
    · cases' g with e direction
      cases direction <;> simpa only [affineOrderWordPath, mapPath] using
        ih ht _
