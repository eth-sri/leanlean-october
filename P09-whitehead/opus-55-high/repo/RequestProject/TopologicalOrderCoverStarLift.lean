import RequestProject.HomeomorphContinuousMap
import RequestProject.TopologicalOrderCoverDeck
import RequestProject.OrderNerveRealizationStarContractible


/-! Actual continuous covering lifts over each closed vertex star. They
are obtained by lifting its explicit contraction, so no local path
connectedness or covering-classification hypothesis is added.
Unverified source. -/

noncomputable section
namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped unitInterval Classical

theorem orderNerveRealizationMap_vertex {P Q} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) hf v :
    orderNerveRealizationMap f hf (orderNerveRealizationVertex v) =
      orderNerveRealizationVertex (f v) := congrArg (fun k : TopCat.of (SimplexCategory.toTop.obj ⦋0⦌) ⟶
      orderNerveRealization Q => k default)
    (orderNerveRealizationSimplex_natural f hf _)

theorem orderNerveRealizationCone_vertex {P} [PartialOrder P]
    (v : P) hv t :
    orderNerveRealizationCone v hv t (orderNerveRealizationVertex v) =
      orderNerveRealizationVertex v := by
  apply orderNerveRealizationCoordinates_injective P
  grind [orderNerveRealizationCone_coordinates, orderNerveRealizationCoordinates_vertex]

namespace TopologicalOrderCover
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p)

def starCenter q : orderNerveVertexStar P q := ⟨q, Or.inl le_rfl⟩

theorem star_comparable q (v : orderNerveVertexStar P q) :
    v ≤ starCenter q ∨ starCenter q ≤ v := v.property

def starBaseMap q : C(orderNerveRealization (orderNerveVertexStar P q), orderNerveRealization P) :=
  ⟨orderNerveRealizationMap Subtype.val (by tauto),
    by fun_prop⟩

def starContraction q :
    (ContinuousMap.const (orderNerveRealization (orderNerveVertexStar P q))
      (orderNerveRealizationVertex q)).Homotopy (starBaseMap q) where
  toFun tx := starBaseMap q
    (orderNerveRealizationCone (starCenter q) (star_comparable q) (unitInterval.symm tx.1) tx.2)
  continuous_toFun := (starBaseMap q).continuous.comp
    ((orderNerveRealizationCone_continuous (starCenter q) (star_comparable q)).comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd))
  map_zero_left x := by
    rw [unitInterval.symm_zero, orderNerveRealizationCone_one]
    exact orderNerveRealizationMap_vertex _ _ _
  map_one_left x := by simp

def starLiftHomotopy (v : Cover p hp) :=
  hp.liftHomotopy _ (ContinuousMap.const _ (point p hp v))
    (fun x => ((starContraction v.1).apply_zero x).trans (point_projection p hp v).symm)

theorem starLiftHomotopy_projection v t
    x :
    p (starLiftHomotopy p hp v (t, x)) = starContraction v.1 (t, x) :=
  congrFun (hp.liftHomotopy_lifts _ _ _) _

theorem starLiftHomotopy_zero v
    x :
    starLiftHomotopy p hp v (0, x) = point p hp v := hp.liftHomotopy_zero _ _ _ x

def starLift (v : Cover p hp) :=
  (starLiftHomotopy p hp v).comp ⟨fun x => (1, x), continuous_const.prodMk continuous_id⟩

theorem starLift_projection v
    x :
    p (starLift p hp v x) = starBaseMap v.1 x :=
  (starLiftHomotopy_projection p hp v 1 x).trans (by simp)

theorem starLift_center v :
    starLift p hp v (orderNerveRealizationVertex (starCenter v.1)) = point p hp v := by
  let c := orderNerveRealizationVertex (starCenter v.1)
  let L := (starLiftHomotopy p hp v).comp
    ⟨fun t => (t, c), continuous_id.prodMk continuous_const⟩
  have hproj : ∀ t t', p (L t) = p (L t') := by
    intro t t'
    change p (starLiftHomotopy p hp v (t, c)) = p (starLiftHomotopy p hp v (t', c))
    rw [starLiftHomotopy_projection, starLiftHomotopy_projection]
    change starBaseMap v.1 (orderNerveRealizationCone _ _ (unitInterval.symm t) c) =
      starBaseMap v.1 (orderNerveRealizationCone _ _ (unitInterval.symm t') c)
    grind [orderNerveRealizationCone_vertex]
  exact (hp.const_of_comp L.continuous hproj 1 0).trans (starLiftHomotopy_zero p hp v c)
