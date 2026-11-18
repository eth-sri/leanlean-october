module

public import RequestProject.CombPi1
public import RequestProject.TopologicalOrderCoverDeck
public import RequestProject.GenusUniversalPolygonTransport
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.LinearAlgebra.Quotient.Basic
public import RequestProject.OrderNerveOneDecoding
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic
public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import RequestProject.CylinderPi1Surjective
public import RequestProject.GenusQuotientRelativeSupport
public import RequestProject.QCubeThreeFaceIndex
public import RequestProject.OrderNerveCommonSimplex
public import RequestProject.PresPosetReading
public import RequestProject.GenusCollapseIteration

@[expose] public section
noncomputable section
namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped unitInterval Classical

theorem orderNerveRealizationMap_vertex {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (v : P) :
    orderNerveRealizationMap f hf (orderNerveRealizationVertex v) =
      orderNerveRealizationVertex (f v) := by
  exact congrArg (fun k : TopCat.of (SimplexCategory.toTop.obj ⦋0⦌) ⟶
      orderNerveRealization Q => k default)
    (orderNerveRealizationSimplex_natural f hf (ComposableArrows.mk₀ v))

theorem orderNerveRealizationCone_vertex {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) (t : I) :
    orderNerveRealizationCone v hv t (orderNerveRealizationVertex v) =
      orderNerveRealizationVertex v := by
  apply orderNerveRealizationCoordinates_injective P
  funext q
  rw [orderNerveRealizationCone_coordinates, orderNerveRealizationCoordinates_vertex]
  split_ifs <;> ring

namespace TopologicalOrderCover
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p)

def starCenter (q : P) : orderNerveVertexStar P q := ⟨q, Or.inl le_rfl⟩

theorem star_comparable (q : P) (v : orderNerveVertexStar P q) :
    v ≤ starCenter q ∨ starCenter q ≤ v := v.property

def starBaseMap (q : P) : C(orderNerveRealization (orderNerveVertexStar P q), orderNerveRealization P) :=
  ⟨orderNerveRealizationMap Subtype.val (fun _ _ h => h),
    (orderNerveRealizationMap (Subtype.val : orderNerveVertexStar P q → P)
      (fun _ _ h => h)).hom.continuous⟩

def starContraction (q : P) :
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
  map_one_left x := by rw [unitInterval.symm_one, orderNerveRealizationCone_zero]

def starLiftHomotopy (v : Cover p hp) :
    C(I × orderNerveRealization (orderNerveVertexStar P v.1), E) :=
  hp.liftHomotopy (starContraction v.1).toContinuousMap (ContinuousMap.const _ (point p hp v))
    (fun x => ((starContraction v.1).apply_zero x).trans (point_projection p hp v).symm)

theorem starLiftHomotopy_projection (v : Cover p hp) (t : I)
    (x : orderNerveRealization (orderNerveVertexStar P v.1)) :
    p (starLiftHomotopy p hp v (t, x)) = starContraction v.1 (t, x) :=
  congrFun (hp.liftHomotopy_lifts _ _ _) (t, x)

theorem starLiftHomotopy_zero (v : Cover p hp)
    (x : orderNerveRealization (orderNerveVertexStar P v.1)) :
    starLiftHomotopy p hp v (0, x) = point p hp v := hp.liftHomotopy_zero _ _ _ x

def starLift (v : Cover p hp) : C(orderNerveRealization (orderNerveVertexStar P v.1), E) :=
  (starLiftHomotopy p hp v).comp ⟨fun x => (1, x), continuous_const.prodMk continuous_id⟩

theorem starLift_projection (v : Cover p hp)
    (x : orderNerveRealization (orderNerveVertexStar P v.1)) :
    p (starLift p hp v x) = starBaseMap v.1 x :=
  (starLiftHomotopy_projection p hp v 1 x).trans ((starContraction v.1).apply_one x)

theorem starLift_center (v : Cover p hp) :
    starLift p hp v (orderNerveRealizationVertex (starCenter v.1)) = point p hp v := by
  let c := orderNerveRealizationVertex (starCenter v.1)
  let L  := (starLiftHomotopy p hp v).comp
    ⟨fun t => (t, c), continuous_id.prodMk continuous_const⟩
  have hproj : ∀ t t', p (L t) = p (L t') := by
    intro t t'
    change p (starLiftHomotopy p hp v (t, c)) = p (starLiftHomotopy p hp v (t', c))
    rw [starLiftHomotopy_projection, starLiftHomotopy_projection]
    change starBaseMap v.1 (orderNerveRealizationCone _ _ (unitInterval.symm t) c) =
      starBaseMap v.1 (orderNerveRealizationCone _ _ (unitInterval.symm t') c)
    dsimp only [c]
    rw [orderNerveRealizationCone_vertex, orderNerveRealizationCone_vertex]
  exact (hp.const_of_comp L.continuous hproj 1 0).trans (starLiftHomotopy_zero p hp v c)

end TopologicalOrderCover
end FiniteChains.Comb

namespace FiniteChains.Comb.TopologicalOrderCover
open CategoryTheory Simplicial Topology
open scoped unitInterval Classical
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p)


def starLiftFibre (v : Cover p hp) (w : orderNerveVertexStar P v.1) :
    p ⁻¹' {orderNerveRealizationVertex w.val} :=
  ⟨starLift p hp v (orderNerveRealizationVertex w),
    (starLift_projection p hp v _).trans (orderNerveRealizationMap_vertex _ _ w)⟩

theorem starLiftFibre_center (v : Cover p hp) :
    starLiftFibre p hp v (starCenter v.1) = v.2 :=
  Subtype.ext (starLift_center p hp v)

theorem starLiftFibre_transport (v : Cover p hp)
    (w z : orderNerveVertexStar P v.1) (hwz : w ≤ z) :
    hp.monodromy (Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath (show w.val ≤ z.val from hwz)))
      (starLiftFibre p hp v w) = starLiftFibre p hp v z := by
  let γ := orderNerveRealizationEdgePath hwz
  let β : Path (orderNerveRealizationVertex w.val) (orderNerveRealizationVertex z.val) :=
    { toFun := fun t => starBaseMap v.1 (γ t)
      continuous_toFun := (starBaseMap v.1).continuous.comp γ.continuous
      source' := by rw [γ.source]; exact orderNerveRealizationMap_vertex _ _ w
      target' := by rw [γ.target]; exact orderNerveRealizationMap_vertex _ _ z }
  have hβσ : β.Homotopic (orderNerveRealizationEdgePath (show w.val ≤ z.val from hwz)) := by
    letI := orderNerveRealization_closedStar_contractible v.1
    apply paths_homotopic_of_range_subset
      (A := (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v.1))) (by
        exact inferInstanceAs (SimplyConnectedSpace
          (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v.1))))
    · rintro x ⟨t, rfl⟩
      exact (by
        have h := (orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar P (v.1)) (γ t)).property
        rw [orderNerveRealizationSubtypeHomeomorph_coe] at h
        exact h)
    · exact orderNerveRealizationEdgePath_supported (show w.val ≤ z.val from hwz) v.1 w.property z.property
  rw [← show Path.Homotopic.Quotient.mk β =
    Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath (show w.val ≤ z.val from hwz))
      from Quotient.sound hβσ]
  let Γ := (starLift p hp v).comp γ.toContinuousMap
  have h₀ : β 0 = p (starLiftFibre p hp v w).val :=
    β.source.trans (starLiftFibre p hp v w).property.symm
  have hΓ : Γ = hp.liftPath β (starLiftFibre p hp v w).val h₀ := by
    apply (hp.eq_liftPath_iff' h₀).mpr
    constructor
    · funext t
      exact starLift_projection p hp v (γ t)
    · change starLift p hp v (γ 0) = starLift p hp v (orderNerveRealizationVertex w)
      rw [γ.source]
  ext
  change hp.liftPath β (starLiftFibre p hp v w).val h₀ 1 =
    starLift p hp v (orderNerveRealizationVertex z)
  rw [← hΓ]
  change starLift p hp v (γ 1) = _
  rw [γ.target]

def projectedComparable (v w : Cover p hp) (hw : w ≤ v ∨ v ≤ w) :
    orderNerveVertexStar P v.1 :=
  ⟨w.1, hw.elim (fun h => Or.inl ((projection_monotone p hp) h))
    (fun h => Or.inr ((projection_monotone p hp) h))⟩

theorem starLift_vertex (v w : Cover p hp) (hw : w ≤ v ∨ v ≤ w) :
    starLift p hp v (orderNerveRealizationVertex (projectedComparable p hp v w hw)) =
      point p hp w := by
  let z := projectedComparable p hp v w hw
  have hz : starLiftFibre p hp v z = w.2 := by
    rcases hw with hwv | hvw
    · have hle : z ≤ starCenter v.1 := (projection_monotone p hp) hwv
      apply (hp.monodromy_bijective
        (Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath hle))).1
      rw [starLiftFibre_transport p hp v z (starCenter v.1) hle,
        starLiftFibre_center]
      exact (comparable_transport p hp hwv).symm
    · have hle  := (projection_monotone p hp) hvw
      have h := starLiftFibre_transport p hp v (starCenter v.1) z hle
      rw [starLiftFibre_center] at h
      exact h.symm.trans (comparable_transport p hp hvw)
  exact congrArg Subtype.val hz

end FiniteChains.Comb.TopologicalOrderCover

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

variable {S : Type} [PartialOrder S] {X E : Type}
  [TopologicalSpace X] [TopologicalSpace E]
  (p : C(E, X)) (hp : IsCoveringMap p)
  {J : Type} (A : J → Set S) (F : C(orderNerveRealization S, X))
  (l : ∀ j, C(orderNerveRealization (A j), E)) (v : S → E)
  (hl : ∀ j z, p (l j z) = F (orderNervePieceMap A j z))
  (hv : ∀ j (a : A j), l j (orderNerveRealizationVertex a) = v a.val)

include hp hl hv in
theorem orderNerveCoverLifts_agree (j k : J)
    (z : orderNerveRealization (A j)) (w : orderNerveRealization (A k))
    (he : orderNervePieceMap A j z = orderNervePieceMap A k w) : l j z = l k w := by
  let B  := A j ∩ A k
  let bj : B → A j := fun b => ⟨b.val, b.property.1⟩
  let bk : B → A k := fun b => ⟨b.val, b.property.2⟩
  have hj : Monotone bj := fun _ _ h => h
  have hk : Monotone bk := fun _ _ h => h
  have hz : orderNervePieceMap A j z ∈ orderNerveRealizationSupported S B := by
    rw (config := { transparency := .default }) [orderNerveRealizationSupported_inter]
    constructor
    · exact (orderNerveRealizationSubtypeHomeomorph (A j) z).property
    · rw (config := { transparency := .default }) [he]
      exact (orderNerveRealizationSubtypeHomeomorph (A k) w).property
  let t := (orderNerveRealizationSubtypeHomeomorph B).symm
    ⟨orderNervePieceMap A j z, hz⟩
  have ht : orderNerveRealizationMap Subtype.val (fun _ _ h => h) t =
      orderNervePieceMap A j z := by
    exact congrArg Subtype.val ((orderNerveRealizationSubtypeHomeomorph B).apply_symm_apply _)
  have htj : orderNerveRealizationMap bj hj t = z := by
    apply orderNerveRealizationMap_injective Subtype.val
      (fun _ _ h => h) Subtype.val_injective
    rw (config := { transparency := .default }) [orderNerveRealizationMap_comp]
    exact ht
  have htk : orderNerveRealizationMap bk hk t = w := by
    apply orderNerveRealizationMap_injective Subtype.val
      (fun _ _ h => h) Subtype.val_injective
    rw (config := { transparency := .default }) [orderNerveRealizationMap_comp]
    exact ht.trans he
  obtain ⟨n, s, r, hr⟩ := orderNerveRealizationSimplex_jointly_surjective B t
  let f : SimplexCategory.toTop.obj n → E := fun a =>
    l j (orderNerveRealizationMap bj hj (orderNerveRealizationSimplex B s a))
  let g : SimplexCategory.toTop.obj n → E := fun a =>
    l k (orderNerveRealizationMap bk hk (orderNerveRealizationSimplex B s a))
  have hf : Continuous f := (l j).continuous.comp
    ((orderNerveRealizationMap bj hj).hom.continuous.comp
      (orderNerveRealizationSimplex B s).hom.continuous)
  have hg : Continuous g := (l k).continuous.comp
    ((orderNerveRealizationMap bk hk).hom.continuous.comp
      (orderNerveRealizationSimplex B s).hom.continuous)
  have hfg : p ∘ f = p ∘ g := by
    funext a
    dsimp [f, g]
    rw (config := { transparency := .default }) [hl, hl]
    congr 1
    change orderNerveRealizationMap Subtype.val _
      (orderNerveRealizationMap bj hj _) =
      orderNerveRealizationMap Subtype.val _
        (orderNerveRealizationMap bk hk _)
    rw (config := { transparency := .default }) [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
    rfl
  obtain ⟨a, ha⟩ := orderNerveRealizationVertex_mem_simplex s 0
  have hbase : f a = g a := by
    have hleft : f a = v (s.obj 0).val :=
      (congrArg (fun u : orderNerveRealization B => l j (orderNerveRealizationMap bj hj u)) ha).trans
        ((congrArg (l j) (orderNerveRealizationMap_vertex bj hj (s.obj 0))).trans (hv j (bj (s.obj 0))))
    have hright : g a = v (s.obj 0).val :=
      (congrArg (fun u : orderNerveRealization B => l k (orderNerveRealizationMap bk hk u)) ha).trans
        ((congrArg (l k) (orderNerveRealizationMap_vertex bk hk (s.obj 0))).trans (hv k (bk (s.obj 0))))
    exact hleft.trans hright.symm
  have h := congrFun (hp.eq_of_comp_eq hf hg hfg a hbase) r
  simpa only [f, g, hr, htj, htk] using h

variable (hc : ∀ (n : SimplexCategory) (s : (nerve S).obj (Opposite.op n)),
  ∃ j, ∀ i, s.obj i ∈ A j)

def coverLiftValue (x : orderNerveRealization S) : E :=
  let y := (orderNervePieceQuotient_surjective A hc x).choose
  l y.1 y.2

include hp hl hv in
theorem coverLiftValue_piece (j : J) (z : orderNerveRealization (A j)) :
    coverLiftValue A l hc (orderNervePieceMap A j z) = l j z := by
  let y := (orderNervePieceQuotient_surjective A hc (orderNervePieceMap A j z)).choose
  apply orderNerveCoverLifts_agree p hp A F l v hl hv y.1 j y.2 z
  exact (orderNervePieceQuotient_surjective A hc (orderNervePieceMap A j z)).choose_spec

def orderNerveCoverLift : C(orderNerveRealization S, E) where
  toFun := coverLiftValue A l hc
  continuous_toFun := by
    apply (orderNervePieceQuotient_isQuotientMap A hc).continuous_iff.mpr
    have he : coverLiftValue A l hc ∘ orderNervePieceQuotient A =
        fun y => l y.1 y.2 := by
      funext y
      exact coverLiftValue_piece p hp A F l v hl hv hc y.1 y.2
    rw (config := { transparency := .default }) [he]
    exact continuous_sigma (fun j => (l j).continuous)

theorem orderNerveCoverLift_piece (j : J) (z : orderNerveRealization (A j)) :
    orderNerveCoverLift p hp A F l v hl hv hc (orderNervePieceMap A j z) = l j z :=
  coverLiftValue_piece p hp A F l v hl hv hc j z

theorem orderNerveCoverLift_projection (x : orderNerveRealization S) :
    p (orderNerveCoverLift p hp A F l v hl hv hc x) = F x := by
  obtain ⟨⟨j, z⟩, rfl⟩ := orderNervePieceQuotient_surjective A hc x
  erw [show orderNervePieceQuotient A ⟨j, z⟩ = orderNervePieceMap A j z from rfl,
    orderNerveCoverLift_piece]
  exact hl j z

end FiniteChains.Comb

namespace FiniteChains.Comb.TopologicalOrderCover
open CategoryTheory Simplicial Topology
open scoped Classical
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p)

def realizedProjection : C(orderNerveRealization (Cover p hp), orderNerveRealization P) :=
  ⟨orderNerveRealizationMap (projection p hp) (projection_monotone p hp),
    (orderNerveRealizationMap (projection p hp) (projection_monotone p hp)).hom.continuous⟩

def starProjection (v : Cover p hp) :
    orderNerveVertexStar (Cover p hp) v → orderNerveVertexStar P v.1 :=
  fun w => projectedComparable p hp v w.val w.property

theorem starProjection_monotone (v : Cover p hp) : Monotone (starProjection p hp v) :=
  fun _ _ h => projection_monotone p hp h

def localComparison (v : Cover p hp) :
    C(orderNerveRealization (orderNerveVertexStar (Cover p hp) v), E) :=
  (starLift p hp v).comp
    ⟨orderNerveRealizationMap (starProjection p hp v) (starProjection_monotone p hp v),
      (orderNerveRealizationMap (starProjection p hp v)
        (starProjection_monotone p hp v)).hom.continuous⟩

theorem localComparison_projection (v : Cover p hp)
    (z : orderNerveRealization (orderNerveVertexStar (Cover p hp) v)) :
    p (localComparison p hp v z) = realizedProjection p hp
      (orderNervePieceMap (orderNerveVertexStar (Cover p hp)) v z) := by
  erw [starLift_projection]
  erw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  rfl

theorem localComparison_vertex (v : Cover p hp)
    (w : orderNerveVertexStar (Cover p hp) v) :
    localComparison p hp v (orderNerveRealizationVertex w) = point p hp w.val := by
  change starLift p hp v (orderNerveRealizationMap _ _ _) = _
  erw [orderNerveRealizationMap_vertex]
  exact starLift_vertex p hp v w.val w.property

theorem vertexStars_cover_simplices (S : Type) [PartialOrder S]
    (n : SimplexCategory) (s : (nerve S).obj (Opposite.op n)) :
    ∃ v, ∀ i, s.obj i ∈ orderNerveVertexStar S v := by
  refine ⟨s.obj 0, fun i => Or.inr ?_⟩
  exact leOfHom (s.map (homOfLE (Fin.zero_le i)))

def realizationComparison : C(orderNerveRealization (Cover p hp), E) :=
  orderNerveCoverLift p hp (orderNerveVertexStar (Cover p hp))
    (realizedProjection p hp) (localComparison p hp) (point p hp)
    (localComparison_projection p hp) (localComparison_vertex p hp)
    (vertexStars_cover_simplices (Cover p hp))

theorem realizationComparison_projection (x : orderNerveRealization (Cover p hp)) :
    p (realizationComparison p hp x) = realizedProjection p hp x :=
  orderNerveCoverLift_projection p hp _ _ _ _ _ _ _ x

theorem realizationComparison_vertex (v : Cover p hp) :
    realizationComparison p hp (orderNerveRealizationVertex v) = point p hp v := by
  let w : orderNerveVertexStar (Cover p hp) v := ⟨v, Or.inl le_rfl⟩
  have he : orderNervePieceMap (orderNerveVertexStar (Cover p hp)) v
      (orderNerveRealizationVertex w) = orderNerveRealizationVertex v :=
    orderNerveRealizationMap_vertex _ _ w
  erw [← he]
  erw [orderNerveCoverLift_piece]
  exact localComparison_vertex p hp v w

end FiniteChains.Comb.TopologicalOrderCover

namespace FiniteChains.CoveringComparison
open Topology
open scoped unitInterval Classical
variable {Y E X : Type} [TopologicalSpace Y] [TopologicalSpace E] [TopologicalSpace X]
  (r : C(Y, X)) (p : C(E, X)) (hr : IsCoveringMap r) (hp : IsCoveringMap p)
  (f : C(Y, E)) (hover : ∀ y, p (f y) = r y)

def fibreMap (x : X) : r ⁻¹' {x} → p ⁻¹' {x} :=
  fun y => ⟨f y.val, (hover y.val).trans y.property⟩

theorem fibreMap_monodromy {x x' : X} (γ : Path x x') (y : r ⁻¹' {x}) :
    fibreMap r p f hover x' (hr.monodromy (Path.Homotopic.Quotient.mk γ) y) =
      hp.monodromy (Path.Homotopic.Quotient.mk γ) (fibreMap r p f hover x y) := by
  let Γ := hr.liftPath γ y.val (γ.source.trans y.property.symm)
  have hΓ : f.comp Γ = hp.liftPath γ (f y.val)
      (γ.source.trans ((hover y.val).trans y.property).symm) := by
    apply (hp.eq_liftPath_iff' _).mpr
    constructor
    · funext t
      exact (hover (Γ t)).trans
        (congrFun (hr.liftPath_lifts γ y.val (γ.source.trans y.property.symm)) t)
    · change f (Γ 0) = f y.val
      rw [hr.liftPath_zero]
  ext
  exact congrArg (fun k : C(unitInterval, E) => k 1) hΓ

include hr hp in
theorem fibreMap_bijective_of_joined {x x' : X} (hxx' : Joined x x')
    (hb : Function.Bijective (fibreMap r p f hover x')) :
    Function.Bijective (fibreMap r p f hover x) := by
  let γ := hxx'.somePath
  let a := hr.monodromy (Path.Homotopic.Quotient.mk γ)
  let b := hp.monodromy (Path.Homotopic.Quotient.mk γ)
  have ha : Function.Bijective a := hr.monodromy_bijective _
  have hb' : Function.Bijective b := hp.monodromy_bijective _
  have hs : ∀ y, fibreMap r p f hover x' (a y) = b (fibreMap r p f hover x y) :=
    fibreMap_monodromy r p hr hp f hover γ
  constructor
  · intro y z hyz
    apply ha.1
    apply hb.1
    rw [hs, hs, hyz]
  · intro e
    obtain ⟨y', hy'⟩ := hb.2 (b e)
    obtain ⟨y, rfl⟩ := ha.2 y'
    refine ⟨y, hb'.1 ?_⟩
    rw [← hs, hy']



def homeomorphOfFibrewise
    (hfib : ∀ x, Function.Bijective (fibreMap r p f hover x)) : Y ≃ₜ E :=
  (show IsLocalHomeomorph f by
    have h : (p ∘ f : Y → X) = r := funext hover
    have hc : IsLocalHomeomorph (p ∘ f) := by simpa only [h] using hr.isLocalHomeomorph
    exact hc.of_comp hp.isLocalHomeomorph f.continuous).toHomeomorphOfBijective
    (by
      constructor
      · intro y z hyz
        have hz  := (hover z).symm.trans
          ((congrArg p hyz).symm.trans (hover y))
        exact congrArg Subtype.val ((hfib (r y)).1
          (show fibreMap r p f hover (r y) ⟨y, rfl⟩ =
            fibreMap r p f hover (r y) ⟨z, hz⟩ from Subtype.ext hyz))
      · intro e
        obtain ⟨y, hy⟩ := (hfib (p e)).2 ⟨e, rfl⟩
        exact ⟨y.val, congrArg Subtype.val hy⟩)

end FiniteChains.CoveringComparison

namespace FiniteChains.Comb.TopologicalOrderCover
open CategoryTheory Simplicial Topology
open scoped Classical
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p) (hs : Function.Surjective p)

include hs in
theorem realizedProjection_isCoveringMap : IsCoveringMap (realizedProjection p hp) :=
  (projection_isPosetCover p hp hs).realizationMap_isCoveringMap

include hs in
theorem realizedProjection_vertex_fibre (q : P)
    (x : orderNerveRealization (Cover p hp))
    (hx : realizedProjection p hp x = orderNerveRealizationVertex q) :
    ∃ v : Cover p hp, v.1 = q ∧ x = orderNerveRealizationVertex v := by
  let hf := projection_isPosetCover p hp hs
  obtain ⟨v, hxv⟩ := orderNerveRealizationOpenStar_cover (Cover p hp) x
  have himg : realizedProjection p hp x ∈ orderNerveRealizationOpenStar P v.1 :=
    (orderNerveRealizationMap_mem_openStar_iff (projection p hp)
      (projection_monotone p hp) x v.1).mpr ⟨v, rfl, hxv⟩
  have hvq : v.1 = q := by
    rw [hx] at himg
    by_contra h
    have h'  := Ne.symm h
    simp only [orderNerveRealizationOpenStar, Set.mem_setOf_eq,
      orderNerveRealizationCoordinates_vertex, if_neg h'] at himg
    exact lt_irrefl _ himg
  refine ⟨v, hvq, hf.realizationMap_injOn_openStar v hxv ?_ ?_⟩
  · simp [orderNerveRealizationOpenStar, orderNerveRealizationCoordinates_vertex]
  · change realizedProjection p hp x = orderNerveRealizationMap _ _ _
    rw [orderNerveRealizationMap_vertex, hx]
    exact (congrArg (orderNerveRealizationVertex) hvq).symm


include hs in
theorem comparison_fibre_bijective (x : orderNerveRealization P) :
    Function.Bijective
      (CoveringComparison.fibreMap (realizedProjection p hp) p
        (realizationComparison p hp) (realizationComparison_projection p hp) x) := by
  obtain ⟨n, s, z, hz⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  have hj := orderNerveRealizationSimplex_joined_vertex s z 0
  rw [hz] at hj
  exact CoveringComparison.fibreMap_bijective_of_joined (realizedProjection p hp) p
    (realizedProjection_isCoveringMap p hp hs) hp (realizationComparison p hp)
    (realizationComparison_projection p hp) hj
    (by
      constructor
      · intro x y hxy
        obtain ⟨v, hv, hx⟩ := realizedProjection_vertex_fibre p hp hs (s.obj 0) x.val x.property
        obtain ⟨w, hw, hy⟩ := realizedProjection_vertex_fibre p hp hs (s.obj 0) y.val y.property
        have hpoint : point p hp v = point p hp w := by
          have h := congrArg Subtype.val hxy
          change realizationComparison p hp x.val = realizationComparison p hp y.val at h
          simpa only [hx, hy, realizationComparison_vertex] using h
        have hvw : v = w := by
          cases v with
          | mk a e =>
            cases w with
            | mk b e' =>
              dsimp at hv hw
              have hab  := hv.trans hw.symm
              clear hv hw
              subst b
              refine Sigma.ext rfl ?_
              exact heq_of_eq (Subtype.ext hpoint)
        ext
        rw [hx, hy, hvw]
      · intro e
        let v : Cover p hp := ⟨(s.obj 0), e⟩
        refine ⟨⟨orderNerveRealizationVertex v, ?_⟩, ?_⟩
        · exact orderNerveRealizationMap_vertex _ _ v
        · ext
          exact realizationComparison_vertex p hp v)

def realizationHomeomorph : orderNerveRealization (Cover p hp) ≃ₜ E :=
  CoveringComparison.homeomorphOfFibrewise (realizedProjection p hp) p
    (realizedProjection_isCoveringMap p hp hs) hp (realizationComparison p hp)
    (realizationComparison_projection p hp) (comparison_fibre_bijective p hp hs)

end FiniteChains.Comb.TopologicalOrderCover

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.TopologicalSingular

open Set Topology

def coordinate (n : ℕ) (i : Fin (n + 1)) : C(Domain n, unitInterval) :=
  ⟨fun z => ⟨z.val i, mem_Icc_of_mem_stdSimplex z.property i⟩,
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _⟩

theorem triangle_face_zero (z : Domain 1) :
    (stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) z).val = ![0, z.val 0, z.val 1] := by
  funext j
  simp only [stdSimplex.map, FunOnFinite.linearMap_apply_apply]
  change (∑ k : Fin 2 with (0 : Fin 3).succAbove k = j, z.val k) = _
  rw [Finset.sum_filter, Fin.sum_univ_two]
  fin_cases j <;> norm_num [Fin.succAbove, Fin.ext_iff, Fin.lt_def, Fin.le_def]

theorem triangle_face_one (z : Domain 1) :
    (stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) z).val = ![z.val 0, 0, z.val 1] := by
  funext j
  simp only [stdSimplex.map, FunOnFinite.linearMap_apply_apply]
  change (∑ k : Fin 2 with (1 : Fin 3).succAbove k = j, z.val k) = _
  rw [Finset.sum_filter, Fin.sum_univ_two]
  fin_cases j <;> norm_num [Fin.succAbove, Fin.ext_iff, Fin.lt_def, Fin.le_def]

theorem triangle_face_two (z : Domain 1) :
    (stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) z).val = ![z.val 0, z.val 1, 0] := by
  funext j
  simp only [stdSimplex.map, FunOnFinite.linearMap_apply_apply]
  change (∑ k : Fin 2 with (2 : Fin 3).succAbove k = j, z.val k) = _
  rw [Finset.sum_filter, Fin.sum_univ_two]
  fin_cases j <;> norm_num [Fin.succAbove, Fin.ext_iff, Fin.lt_def, Fin.le_def]

def squareTriangle0 : C(Domain 2, unitInterval × unitInterval) :=
  ⟨fun z => (coordinate 2 2 z, unitInterval.symm (coordinate 2 0 z)),
    (coordinate 2 2).continuous.prodMk (unitInterval.continuous_symm.comp (coordinate 2 0).continuous)⟩

def squareTriangle1 : C(Domain 2, unitInterval × unitInterval) :=
  ⟨fun z => (unitInterval.symm (coordinate 2 0 z), coordinate 2 2 z),
    (unitInterval.continuous_symm.comp (coordinate 2 0).continuous).prodMk (coordinate 2 2).continuous⟩

theorem squareTriangle0_faces (z : Domain 1) :
    squareTriangle0 (stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) z) =
        (stdSimplexHomeomorphUnitInterval z, 1) ∧
    squareTriangle0 (stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) z) =
        (stdSimplexHomeomorphUnitInterval z, stdSimplexHomeomorphUnitInterval z) ∧
    squareTriangle0 (stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) z) =
        (0, stdSimplexHomeomorphUnitInterval z) := by
  have hz := z.property.2
  rw [Fin.sum_univ_two] at hz
  refine ⟨?_, ?_, ?_⟩ <;>
    (apply Prod.ext <;> apply Subtype.ext <;>
      simp only [squareTriangle0, ContinuousMap.coe_mk, coordinate, unitInterval.coe_symm_eq,
        triangle_face_zero, triangle_face_one, triangle_face_two,
        stdSimplexHomeomorphUnitInterval] <;>
      (dsimp [Matrix.vecHead, Matrix.vecTail]; all_goals linarith))

theorem squareTriangle1_faces (z : Domain 1) :
    squareTriangle1 (stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) z) =
        (1, stdSimplexHomeomorphUnitInterval z) ∧
    squareTriangle1 (stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) z) =
        (stdSimplexHomeomorphUnitInterval z, stdSimplexHomeomorphUnitInterval z) ∧
    squareTriangle1 (stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) z) =
        (stdSimplexHomeomorphUnitInterval z, 0) := by
  have hz := z.property.2
  rw [Fin.sum_univ_two] at hz
  refine ⟨?_, ?_, ?_⟩ <;>
    (apply Prod.ext <;> apply Subtype.ext <;>
      simp only [squareTriangle1, ContinuousMap.coe_mk, coordinate, unitInterval.coe_symm_eq,
        triangle_face_zero, triangle_face_one, triangle_face_two,
        stdSimplexHomeomorphUnitInterval] <;>
      (dsimp [Matrix.vecHead, Matrix.vecTail]; all_goals linarith))

end FiniteChains.TopologicalSingular
end

namespace FiniteChains.TopologicalSingular

open Set Topology

universe u
variable {X : Type u} [TopologicalSpace X]

theorem boundary_two_single (σ : Simplex X 2) (r : ℤ) :
    boundary 1 (Finsupp.single σ r) =
      Finsupp.single (face 0 σ) r - Finsupp.single (face 1 σ) r + Finsupp.single (face 2 σ) r := by
  rw [boundary_single, Fin.sum_univ_three]
  change 1 • _ + (-1 : ℤ) • _ + 1 • _ = _
  grind

theorem boundary_constant_two (x : X) (r : ℤ) :
    boundary 1 (Finsupp.single (ContinuousMap.const (Domain 2) x) r) =
      Finsupp.single (ContinuousMap.const (Domain 1) x) r := by
  rw [boundary_two_single]
  exact sub_add_cancel _ _

variable {a b : X} {p q : Path a b}

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology

/-- Coordinate identification used by the actual `GenLoop (Fin 2)` model. -/
def squareCoordinates : C(I × I, Fin 2 → I) where
  toFun z := ![z.1, z.2]
  continuous_toFun := by fun_prop

def cubeTriangle0 : Simplex (Fin 2 → I) 2 := squareCoordinates.comp squareTriangle0
def cubeTriangle1 : Simplex (Fin 2 → I) 2 := squareCoordinates.comp squareTriangle1

def cubeEdge (i : Fin 2) (v : I) : Simplex (Fin 2 → I) 1 :=
  ⟨fun z => Whitehead.squareEdge i v (stdSimplexHomeomorphUnitInterval z),
    (Whitehead.squareEdge_continuous i v).comp stdSimplexHomeomorphUnitInterval.continuous⟩

theorem cubeEdge_boundary (i : Fin 2) (v : I) (hv : v = 0 ∨ v = 1) (z : Domain 1) :
    cubeEdge i v z ∈ Cube.boundary (Fin 2) := by
  refine ⟨i, ?_⟩
  simpa [cubeEdge, Whitehead.squareEdge] using hv

theorem cubeTriangle_faces :
    face 0 cubeTriangle0 = cubeEdge 1 1 ∧ face 2 cubeTriangle0 = cubeEdge 0 0 ∧
    face 0 cubeTriangle1 = cubeEdge 0 1 ∧ face 2 cubeTriangle1 = cubeEdge 1 0 ∧
    face 1 cubeTriangle0 = face 1 cubeTriangle1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply ContinuousMap.ext
    intro z
    change squareCoordinates (squareTriangle0 (stdSimplex.map (SimplexCategory.δ 0) z)) = _
    rw [(squareTriangle0_faces z).1]
    funext i
    fin_cases i <;> simp [squareCoordinates, cubeEdge, Whitehead.squareEdge]
  · apply ContinuousMap.ext
    intro z
    change squareCoordinates (squareTriangle0 (stdSimplex.map (SimplexCategory.δ 2) z)) = _
    rw [(squareTriangle0_faces z).2.2]
    funext i
    fin_cases i <;> simp [squareCoordinates, cubeEdge, Whitehead.squareEdge]
  · apply ContinuousMap.ext
    intro z
    change squareCoordinates (squareTriangle1 (stdSimplex.map (SimplexCategory.δ 0) z)) = _
    rw [(squareTriangle1_faces z).1]
    funext i
    fin_cases i <;> simp [squareCoordinates, cubeEdge, Whitehead.squareEdge]
  · apply ContinuousMap.ext
    intro z
    change squareCoordinates (squareTriangle1 (stdSimplex.map (SimplexCategory.δ 2) z)) = _
    rw [(squareTriangle1_faces z).2.2]
    funext i
    fin_cases i <;> simp [squareCoordinates, cubeEdge, Whitehead.squareEdge]
  · apply ContinuousMap.ext
    intro z
    change squareCoordinates (squareTriangle0 (stdSimplex.map (SimplexCategory.δ 1) z)) =
      squareCoordinates (squareTriangle1 (stdSimplex.map (SimplexCategory.δ 1) z))
    rw [(squareTriangle0_faces z).2.1, (squareTriangle1_faces z).2.1]

/-- The two oriented triangles making up the parameter square. -/
def squareFundamentalChain : Chain (Fin 2 → I) 2 :=
  Finsupp.single cubeTriangle1 1 - Finsupp.single cubeTriangle0 1

theorem squareFundamentalChain_boundary : boundary 1 squareFundamentalChain =
    Finsupp.single (cubeEdge 0 1) 1 + Finsupp.single (cubeEdge 1 0) 1 -
      Finsupp.single (cubeEdge 1 1) 1 - Finsupp.single (cubeEdge 0 0) 1 := by
  simp only [squareFundamentalChain, map_sub, boundary_two_single,
    cubeTriangle_faces.1, cubeTriangle_faces.2.1, cubeTriangle_faces.2.2.1,
    cubeTriangle_faces.2.2.2.1, cubeTriangle_faces.2.2.2.2]
  abel

theorem squareFundamentalChain_boundary_supported :
    boundary 1 squareFundamentalChain ∈ subChains (Cube.boundary (Fin 2)) 1 := by
  rw [squareFundamentalChain_boundary]
  apply Submodule.sub_mem
  · apply Submodule.sub_mem
    · apply Submodule.add_mem
      · exact single_mem_subChains _ 1 _ 1 (cubeEdge_boundary 0 1 (Or.inr rfl))
      · exact single_mem_subChains _ 1 _ 1 (cubeEdge_boundary 1 0 (Or.inl rfl))
    · exact single_mem_subChains _ 1 _ 1 (cubeEdge_boundary 1 1 (Or.inr rfl))
  · exact single_mem_subChains _ 1 _ 1 (cubeEdge_boundary 0 0 (Or.inl rfl))

universe u v
variable {X : Type u} [TopologicalSpace X] {x : X}

def squareCycle (p : GenLoop (Fin 2) X x) : Chain X 2 :=
  map p.val 2 squareFundamentalChain

theorem squareCycle_boundary (p : GenLoop (Fin 2) X x) : boundary 1 (squareCycle p) = 0 := by
  have he i v (hv : v = 0 ∨ v = 1) :
      simplexMap p.val 1 (cubeEdge i v) = ContinuousMap.const (Domain 1) x := by
    apply ContinuousMap.ext
    intro z
    exact GenLoop.boundary p _ (cubeEdge_boundary i v hv z)
  rw [squareCycle, ← map_boundary, squareFundamentalChain_boundary, map_sub, map_sub, map_add,
    map_single, map_single, map_single, map_single,
    he 0 1 (Or.inr rfl), he 1 0 (Or.inl rfl), he 1 1 (Or.inr rfl), he 0 0 (Or.inl rfl)]
  abel

theorem squareCycle_const : squareCycle (GenLoop.const (N := Fin 2) (x := x)) = 0 := by
  rw [squareCycle, squareFundamentalChain, map_sub, map_single, map_single]
  exact sub_self _

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology

/-- A zero barycentric coordinate identifies an actual point of that face. -/
theorem domain_zero_coordinate_face {n : ℕ} (z : Domain (n + 1)) (i : Fin (n + 2))
    (hi : z.val i = 0) : ∃ w : Domain n, stdSimplex.map (SimplexCategory.δ i) w = z := by
  let w : Domain n := ⟨fun j => z.val (i.succAbove j), fun j => z.property.1 _, by
    have hs := z.property.2
    rw [Fin.sum_univ_succAbove (fun j => z.val j) i, hi, zero_add] at hs
    exact hs⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  funext k
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove w.val) k = z.val k
  rw [FunOnFinite.linearMap_apply_apply]
  by_cases hk : k = i
  · simp_all
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    simp [w, Finset.sum_filter]

/-- Collapse the upper triangle of the square onto an edge of the standard
triangle. On the lower triangle this map is exactly the identity simplex. -/
def squareToTriangle : C((Fin 2 → I), Domain 2) where
  toFun z := ⟨![1 - (z 0 : ℝ), max ((z 0 : ℝ) - z 1) 0, min (z 0 : ℝ) (z 1 : ℝ)], by
    constructor
    · intro i
      fin_cases i
      · exact sub_nonneg.mpr (z 0).property.2
      · exact le_max_right _ _
      · exact le_min (z 0).property.1 (z 1).property.1
    · rw [Fin.sum_univ_three]
      change 1 - (z 0 : ℝ) + max ((z 0 : ℝ) - z 1) 0 + min (z 0 : ℝ) (z 1 : ℝ) = 1
      rcases le_total (z 0 : ℝ) (z 1 : ℝ) with h | h
      · rw [max_eq_right (sub_nonpos.mpr h), min_eq_left h]
        ring
      · rw [max_eq_left (sub_nonneg.mpr h), min_eq_right h]
        ring⟩
  continuous_toFun := by fun_prop

theorem squareToTriangle_triangle1 (z : Domain 2) : squareToTriangle (cubeTriangle1 z) = z := by
  have hs : z.val 0 + z.val 1 + z.val 2 = 1 := by
    exact (Fin.sum_univ_three z.val).symm.trans z.property.2
  have h : z.val 2 ≤ 1 - z.val 0 := by linarith [z.property.1 1]
  apply Subtype.ext
  change ![1 - (1 - z.val 0), max ((1 - z.val 0) - z.val 2) 0,
    min (1 - z.val 0) (z.val 2)] = z.val
  funext i
  fin_cases i
  · simp
  · change max ((1 - z.val 0) - z.val 2) 0 = z.val 1
    rw [max_eq_left (sub_nonneg.mpr h)]
    linarith
  · exact min_eq_right h

theorem squareToTriangle_triangle0_zero (z : Domain 2) :
    (squareToTriangle (cubeTriangle0 z)).val 1 = 0 := by
  have hs : z.val 0 + z.val 1 + z.val 2 = 1 := by
    exact (Fin.sum_univ_three z.val).symm.trans z.property.2
  change max (z.val 2 - (1 - z.val 0)) 0 = 0
  apply max_eq_right
  linarith [z.property.1 1]

theorem squareToTriangle_boundary (z : Fin 2 → I) (hz : z ∈ Cube.boundary (Fin 2)) :
    ∃ i : Fin 3, (squareToTriangle z).val i = 0 := by
  obtain ⟨i, hi⟩ := hz
  fin_cases i
  · rcases hi with hi | hi
    · refine ⟨2, ?_⟩
      change z 0 = 0 at hi
      change min (z 0 : ℝ) (z 1) = 0
      rw [hi]
      exact min_eq_left (z 1).property.1
    · refine ⟨0, ?_⟩
      change z 0 = 1 at hi
      change 1 - (z 0 : ℝ) = 0
      rw [hi]
      exact sub_self _
  · rcases hi with hi | hi
    · refine ⟨2, ?_⟩
      change z 1 = 0 at hi
      change min (z 0 : ℝ) (z 1) = 0
      rw [hi]
      exact min_eq_right (z 0).property.1
    · refine ⟨1, ?_⟩
      change z 1 = 1 at hi
      change max ((z 0 : ℝ) - z 1) 0 = 0
      rw [hi]
      exact max_eq_right (sub_nonpos.mpr (z 0).property.2)

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology

def simplexMin {n : ℕ} (z : Domain n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty z.val

theorem simplexMin_nonneg {n : ℕ} (z : Domain n) : 0 ≤ simplexMin z :=
  Finset.le_inf' _ _ (fun i _ => z.property.1 i)

theorem simplexMin_le {n : ℕ} (z : Domain n) (i : Fin (n + 1)) : simplexMin z ≤ z.val i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem simplexMin_attained {n : ℕ} (z : Domain n) : ∃ i, simplexMin z = z.val i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty z.val
  exact ⟨i, hi⟩

theorem simplexMin_continuous (n : ℕ) : Continuous (simplexMin (n := n)) := by
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun i _ => (continuous_apply i).comp continuous_subtype_val)

def simplexBoundary (n : ℕ) : Set (Domain n) := {z | ∃ i, z.val i = 0}

theorem simplexMin_eq_zero_iff {n : ℕ} (z : Domain n) :
    simplexMin z = 0 ↔ z ∈ simplexBoundary n := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := simplexMin_attained z
    exact ⟨i, hi.symm.trans h⟩
  · rintro ⟨i, hi⟩
    exact le_antisymm (hi ▸ simplexMin_le z i) (simplexMin_nonneg z)

theorem simplexBoundary_isClosed (n : ℕ) : IsClosed (simplexBoundary n) := by
  have he : simplexBoundary n = {z | simplexMin z = 0} := by
    ext z
    exact (simplexMin_eq_zero_iff z).symm
  rw [he]
  exact isClosed_eq (simplexMin_continuous n) continuous_const

def prismDenom {n : ℕ} (w : I × Domain n) : ℝ :=
  max (1 - (w.1 : ℝ) / 2) (1 - (n + 1 : ℝ) * simplexMin w.2)

theorem prismDenom_pos {n : ℕ} (w : I × Domain n) : 0 < prismDenom w := by grind [le_max_left, prismDenom]

theorem prismDenom_le_one {n : ℕ} (w : I × Domain n) : prismDenom w ≤ 1 := by
  apply max_le
  · grind
  · have hp : 0 ≤ (n + 1) * simplexMin w.2 := mul_nonneg (by positivity) (simplexMin_nonneg _)
    linarith

theorem prismDenom_continuous (n : ℕ) : Continuous (prismDenom (n := n)) := by
  exact (continuous_const.sub (continuous_fst.subtype_val.div_const 2)).max
    (continuous_const.sub (continuous_const.mul ((simplexMin_continuous n).comp continuous_snd)))


def prismRetractTime {n : ℕ} (w : I × Domain n) : I :=
  ⟨2 + ((w.1 : ℝ) - 2) / prismDenom w, by
    have hd := prismDenom_pos w
    have htime : 1 - (w.1 : ℝ) / 2 ≤ prismDenom w := le_max_left _ _
    have hu := prismDenom_le_one w
    constructor
    · have he : (-2) ≤ ((w.1 : ℝ) - 2) / prismDenom w :=
        (le_div_iff₀ hd).mpr (by linarith)
      linarith
    · have he : ((w.1 : ℝ) - 2) / prismDenom w ≤ -1 :=
        (div_le_iff₀ hd).mpr (by linarith [w.1.property.2])
      linarith⟩

def prismRetractPoint {n : ℕ} (w : I × Domain n) : Domain n :=
  ⟨fun i => (w.2.val i - (1 - prismDenom w) / (n + 1 : ℝ)) / prismDenom w, by
    have hd := prismDenom_pos w
    have hk : 0 < (n + 1 : ℝ) := by positivity
    constructor
    · intro i
      apply div_nonneg _ hd.le
      apply sub_nonneg.mpr
      apply (div_le_iff₀ hk).mpr
      have hspace : 1 - (n + 1 : ℝ) * simplexMin w.2 ≤ prismDenom w := le_max_right _ _
      have hm := simplexMin_le w.2 i
      nlinarith
    · rw [← Finset.sum_div, Finset.sum_sub_distrib, w.2.property.2]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]
      field_simp [ne_of_gt hd, ne_of_gt hk]
      ring⟩



def simplexPrismSide (n : ℕ) : Set (I × Domain n) :=
  {w | w.1 = 0 ∨ w.2 ∈ simplexBoundary n}


/-- Radial retraction onto the bottom and all boundary faces of a prism. -/
def simplexPrismRetraction (n : ℕ) : C(I × Domain n, simplexPrismSide n) where
  toFun w := ⟨(prismRetractTime w, prismRetractPoint w), (by
    have hd := prismDenom_pos w
    have hk : (n + 1 : ℝ) ≠ 0 := by positivity
    rcases le_total (1 - (w.1 : ℝ) / 2) (1 - (n + 1 : ℝ) * simplexMin w.2) with h | h
    · right
      obtain ⟨i, hi⟩ := simplexMin_attained w.2
      refine ⟨i, ?_⟩
      change (w.2.val i - (1 - prismDenom w) / (n + 1 : ℝ)) / prismDenom w = 0
      rw [prismDenom, max_eq_right h, ← hi]
      field_simp [hk]
      ring
    · left
      apply Subtype.ext
      change 2 + ((w.1 : ℝ) - 2) / prismDenom w = 0
      have he : prismDenom w = 1 - (w.1 : ℝ) / 2 := max_eq_left h
      have hq : ((w.1 : ℝ) - 2) / prismDenom w = -2 := by
        apply (div_eq_iff (ne_of_gt hd)).mpr
        rw [he]
        ring
      rw [hq]
      ring)⟩
  continuous_toFun := (show Continuous (prismRetractTime (n := n)) by
    apply Continuous.subtype_mk
    exact continuous_const.add ((continuous_fst.subtype_val.sub continuous_const).div
      (prismDenom_continuous n) (fun w => ne_of_gt (prismDenom_pos w)))).prodMk
    (by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro i
      exact (((continuous_apply i).comp continuous_snd.subtype_val).sub
        ((continuous_const.sub (prismDenom_continuous n)).div_const _)).div
          (prismDenom_continuous n) (fun w => ne_of_gt (prismDenom_pos w))) |>.subtype_mk _

theorem simplexPrismRetraction_fixes {n : ℕ} (w : I × Domain n) (hw : w ∈ simplexPrismSide n) :
    (simplexPrismRetraction n w).val = w := by
  have hd := (by
    apply le_antisymm (prismDenom_le_one w)
    rcases hw with hw | hw
    · have he : 1 - (w.1 : ℝ) / 2 = 1 := by rw [hw]; norm_num
      exact he ▸ le_max_left _ _
    · have hm := (simplexMin_eq_zero_iff w.2).mpr hw
      have he : 1 - (n + 1) * simplexMin w.2 = 1 := by rw [hm]; ring
      exact he ▸ le_max_right _ _)
  apply Prod.ext
  · ext
    change 2 + (w.1 - 2) / prismDenom w = w.1
    rw [hd]
    ring
  · apply Subtype.ext
    funext i
    change (w.2.val i - (1 - prismDenom w) / (n + 1)) / prismDenom w = w.2.val i
    rw [hd]
    simp

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X]


/-- In a simply connected space, a singular edge whose two vertices are at
the basepoint contracts to the constant edge while fixing both vertices. -/
theorem singularEdge_nullhomotopic [SimplyConnectedSpace X] (x : X) (tau : Simplex X 1)
    (h0 : tau (stdSimplex.vertex 0) = x) (h1 : tau (stdSimplex.vertex 1) = x) :
    Nonempty (ContinuousMap.HomotopyRel tau (ContinuousMap.const (Domain 1) x) (simplexBoundary 1)) := by
  let p : Path x x := {
    toFun := fun t => tau (stdSimplexHomeomorphUnitInterval.symm t)
    continuous_toFun := tau.continuous.comp stdSimplexHomeomorphUnitInterval.symm.continuous
    source' := (congrArg tau (stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
      stdSimplexHomeomorphUnitInterval_zero.symm)).trans h0
    target' := (congrArg tau (stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
      stdSimplexHomeomorphUnitInterval_one.symm)).trans h1 }
  obtain ⟨G⟩ := SimplyConnectedSpace.paths_homotopic p (Path.refl x)
  refine ⟨{
    toFun := fun w => G (w.1, stdSimplexHomeomorphUnitInterval w.2)
    continuous_toFun := G.continuous.comp (continuous_fst.prodMk
      (stdSimplexHomeomorphUnitInterval.continuous.comp continuous_snd))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro z
    rw [G.apply_zero]
    change tau (stdSimplexHomeomorphUnitInterval.symm (stdSimplexHomeomorphUnitInterval z)) = tau z
    rw [stdSimplexHomeomorphUnitInterval.symm_apply_apply]
  · simp
  · intro t z hz
    change G (t, stdSimplexHomeomorphUnitInterval z) = tau z
    rcases (show stdSimplexHomeomorphUnitInterval z = 0 ∨ stdSimplexHomeomorphUnitInterval z = 1 by
      have hs  := (Fin.sum_univ_two z.val).symm.trans z.property.2
      obtain ⟨i, hi⟩ := hz
      fin_cases i
      · right
        ext
        change z.val 1 = 1
        change z.val 0 = 0 at hi
        linarith
      · left
        ext
        exact hi) with he | he
    · have hv  := stdSimplexHomeomorphUnitInterval.injective
        (he.trans stdSimplexHomeomorphUnitInterval_zero.symm)
      rw [he, G.source, hv, h0]
    · have hv  := stdSimplexHomeomorphUnitInterval.injective
        (he.trans stdSimplexHomeomorphUnitInterval_one.symm)
      rw [he, G.target, hv, h1]

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

def simplexPrismBoundaryValue (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (w : simplexPrismSide n) : X := by
  classical
  exact if h : w.val.2 ∈ simplexBoundary n then H (w.val.1, ⟨w.val.2, h⟩) else f w.val.2

theorem simplexPrismBoundaryValue_bottom (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z : simplexBoundary n, H (0, z) = f z)
    (w : simplexPrismSide n) (hw : w.val.1 = 0) : simplexPrismBoundaryValue f H w = f w.val.2 := by
  unfold simplexPrismBoundaryValue
  simp_all

theorem simplexPrismBoundaryValue_side (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (w : simplexPrismSide n)
    (hw : w.val.2 ∈ simplexBoundary n) :
    simplexPrismBoundaryValue f H w = H (w.val.1, ⟨w.val.2, hw⟩) := by
  simp only [simplexPrismBoundaryValue, dif_pos hw]


/-- Glue the prescribed initial map and the prescribed boundary homotopy. -/
def simplexPrismBoundaryMap (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z : simplexBoundary n, H (0, z) = f z) :
    C(simplexPrismSide n, X) :=
  ⟨simplexPrismBoundaryValue f H, (by
    let S : Set (simplexPrismSide n) := {w | w.val.1 = 0}
    let T : Set (simplexPrismSide n) := {w | w.val.2 ∈ simplexBoundary n}
    have hS : IsClosed S := isClosed_eq continuous_subtype_val.fst continuous_const
    have hT : IsClosed T := (simplexBoundary_isClosed n).preimage continuous_subtype_val.snd
    have hu : S ∪ T = Set.univ := by
      ext w
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      exact w.property
    have hcS : ContinuousOn (simplexPrismBoundaryValue f H) S := by
      apply (f.continuous.comp continuous_subtype_val.snd).continuousOn.congr
      intro w hw
      exact simplexPrismBoundaryValue_bottom f H hH w hw
    have hcT : ContinuousOn (simplexPrismBoundaryValue f H) T := by
      rw [continuousOn_iff_continuous_restrict]
      have hc : Continuous (fun w : T => H (w.val.val.1, ⟨w.val.val.2, w.property⟩)) := by
        apply H.continuous.comp
        exact continuous_subtype_val.subtype_val.fst.prodMk
          (continuous_subtype_val.subtype_val.snd.subtype_mk _)
      convert hc using 1
      funext w
      exact simplexPrismBoundaryValue_side f H w.val w.property
    rw [← continuousOn_univ, ← hu]
    exact hcS.union_of_isClosed hcT hS hT)⟩

/-- Extension over the entire simplex prism. -/
def simplexHomotopyExtension (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z : simplexBoundary n, H (0, z) = f z) :
    C(I × Domain n, X) :=
  (simplexPrismBoundaryMap f H hH).comp (simplexPrismRetraction n)

theorem simplexHomotopyExtension_zero (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z : simplexBoundary n, H (0, z) = f z)
    (z : Domain n) : simplexHomotopyExtension f H hH (0, z) = f z := by
  have he := simplexPrismRetraction_fixes (0, z) (Or.inl rfl)
  change simplexPrismBoundaryValue f H (simplexPrismRetraction n (0, z)) = _
  rw [simplexPrismBoundaryValue_bottom f H hH _ (congrArg Prod.fst he)]
  simp_all

theorem simplexHomotopyExtension_boundary (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z : simplexBoundary n, H (0, z) = f z)
    (t : I) (z : simplexBoundary n) : simplexHomotopyExtension f H hH (t, z.val) = H (t, z) := by
  have he := simplexPrismRetraction_fixes (t, z.val) (Or.inr z.property)
  have hz : (simplexPrismRetraction n (t, z.val)).val.2 ∈ simplexBoundary n := by
    rw [congrArg Prod.snd he]
    exact z.property
  change simplexPrismBoundaryValue f H (simplexPrismRetraction n (t, z.val)) = _
  rw [simplexPrismBoundaryValue_side f H _ hz]
  simp_all

/-- The standard topological simplex has the homotopy extension property
relative to its entire boundary, with no restriction on the target space. -/
theorem simplex_homotopy_extension (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z : simplexBoundary n, H (0, z) = f z) :
    ∃ g : C(Domain n, X), ∃ F : f.Homotopy g,
      ∀ (t : I) (z : simplexBoundary n), F (t, z.val) = H (t, z) := by
  let E := simplexHomotopyExtension f H hH
  let g : C(Domain n, X) := ⟨fun z => E (1, z), E.continuous.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨g, {
    toContinuousMap := E
    map_zero_left := simplexHomotopyExtension_zero f H hH
    map_one_left := fun _ => rfl }, ?_⟩
  exact simplexHomotopyExtension_boundary f H hH

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

theorem simplex_face_coordinate_zero (i : Fin (n + 2)) (z : Domain n) :
    (stdSimplex.map (SimplexCategory.δ i) z).val i = 0 := by
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove z.val) i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Fin.succAbove_ne]

def simplexFaceBoundary (i : Fin (n + 2)) : C(Domain n, simplexBoundary (n + 1)) where
  toFun z := ⟨stdSimplex.map (SimplexCategory.δ i) z, ⟨i, simplex_face_coordinate_zero i z⟩⟩
  continuous_toFun := (stdSimplex.continuous_map _).subtype_mk _

def simplexBoundaryPrismCover (n : ℕ) :
    C((Σ _ : Fin (n + 2), I × Domain n), I × simplexBoundary (n + 1)) where
  toFun w := (w.2.1, simplexFaceBoundary w.1 w.2.2)
  continuous_toFun := continuous_sigma fun i =>
    continuous_fst.prodMk ((simplexFaceBoundary i).continuous.comp continuous_snd)


/-- A coherent family of homotopies on the faces glues continuously over
the entire boundary. The target need not be Hausdorff. -/
theorem simplex_boundary_glue (H : Fin (n + 2) → C(I × Domain n, X))
    (hH : ∀ (i j : Fin (n + 2)) (t : I) (z w : Domain n),
      stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w →
        H i (t, z) = H j (t, w)) :
    ∃ F : C(I × simplexBoundary (n + 1), X),
      ∀ (i : Fin (n + 2)) (t : I) (z : Domain n), F (t, simplexFaceBoundary i z) = H i (t, z) := by
  let q := simplexBoundaryPrismCover n
  have hq  := (show Function.Surjective (simplexBoundaryPrismCover n) by
    rintro ⟨t, z⟩
    obtain ⟨i, hi⟩ := z.property
    obtain ⟨w, hw⟩ := domain_zero_coordinate_face z.val i hi
    refine ⟨⟨i, t, w⟩, ?_⟩
    apply Prod.ext
    · rfl
    · exact Subtype.ext hw)
  obtain ⟨r, hr⟩ := hq.hasRightInverse
  let F  := fun w => H (r w).1 (r w).2
  have he : ∀ w : (Σ _ : Fin (n + 2), I × Domain n), F (q w) = H w.1 w.2 := by
    intro w
    have htime := congrArg Prod.fst (hr (q w))
    have hpoint := congrArg (fun v : I × simplexBoundary (n + 1) => v.2.val) (hr (q w))
    change (r (q w)).2.1 = w.2.1 at htime
    change H (r (q w)).1 ((r (q w)).2.1, (r (q w)).2.2) = H w.1 (w.2.1, w.2.2)
    rw [htime]
    exact hH _ _ _ _ _ hpoint
  have hc : Continuous F := by
    apply (Topology.IsQuotientMap.of_surjective_continuous hq q.continuous).continuous_iff.mpr
    have h : Continuous (fun w : (Σ _ : Fin (n + 2), I × Domain n) => H w.1 w.2) :=
      continuous_sigma (fun i : Fin (n + 2) => (H i).continuous)
    convert h using 1
    funext w
    exact he w
  exact ⟨⟨F, hc⟩, fun i t z => he ⟨i, t, z⟩⟩

/-- Simultaneously extend prescribed homotopies on all faces of a simplex. -/
theorem simplex_face_homotopy_extension (f : C(Domain (n + 1), X))
    (H : Fin (n + 2) → C(I × Domain n, X))
    (hH : ∀ (i j : Fin (n + 2)) (t : I) (z w : Domain n),
      stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w →
        H i (t, z) = H j (t, w))
    (h0 : ∀ (i : Fin (n + 2)) (z : Domain n), H i (0, z) = face i f z) :
    ∃ g : C(Domain (n + 1), X), ∃ F : f.Homotopy g,
      ∀ (i : Fin (n + 2)) (t : I) (z : Domain n),
        F (t, stdSimplex.map (SimplexCategory.δ i) z) = H i (t, z) := by
  obtain ⟨B, hB⟩ := simplex_boundary_glue H hH
  have hz : ∀ z : simplexBoundary (n + 1), B (0, z) = f z := by
    intro z
    obtain ⟨i, hi⟩ := z.property
    obtain ⟨w, hw⟩ := domain_zero_coordinate_face z.val i hi
    have he : simplexFaceBoundary i w = z := Subtype.ext hw
    rw [← he, hB, h0]
    rfl
  obtain ⟨g, F, hF⟩ := simplex_homotopy_extension f B hz
  refine ⟨g, F, ?_⟩
  intro i t z
  exact (hF t (simplexFaceBoundary i z)).trans (hB i t z)

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

theorem simplex_face_coordinate_succAbove (i : Fin (n + 2)) (z : Domain n) (j : Fin (n + 1)) :
    (stdSimplex.map (SimplexCategory.δ i) z).val (i.succAbove j) = z.val j := by
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove z.val) (i.succAbove j) = z.val j
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter]

theorem simplex_face_injective (i : Fin (n + 2)) :
    Function.Injective (stdSimplex.map (SimplexCategory.δ i) : Domain n → Domain (n + 1)) := by
  intro z w h
  apply Subtype.ext
  funext j
  have he := congrArg (fun v : Domain (n + 1) => v.val (i.succAbove j)) h
  simpa only [simplex_face_coordinate_succAbove] using he

/-- A point common to two different faces is on the boundary of each face. -/
theorem simplex_face_intersection_boundary (i j : Fin (n + 2)) (hij : i ≠ j)
    (z w : Domain n)
    (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
    z ∈ simplexBoundary n ∧ w ∈ simplexBoundary n := by
  have one (i j : Fin (n + 2)) (hij : i ≠ j) (z w : Domain n)
      (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
      z ∈ simplexBoundary n := by
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    refine ⟨k, ?_⟩
    rw [← simplex_face_coordinate_succAbove i z k, hk, h]
    exact simplex_face_coordinate_zero j w
  grind

end FiniteChains.TopologicalSingular

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.TopologicalSingular
open CategoryTheory
universe u

def shortComplexCycleClass (S : ShortComplex (ModuleCat.{u} ℤ))
    (c : S.X₂) (hc : S.g c = 0) : S.homology :=
  S.homologyπ (S.moduleCatCyclesIso.inv ⟨c, hc⟩)

theorem shortComplexCycleClass_i (S : ShortComplex (ModuleCat.{u} ℤ))
    (c : S.X₂) (hc : S.g c = 0) :
    S.homologyι (shortComplexCycleClass S c hc) = S.pOpcycles c := by
  have he := congrArg (fun f => f (S.moduleCatCyclesIso.inv ⟨c, hc⟩)) S.homology_π_ι
  change S.homologyι (shortComplexCycleClass S c hc) =
    S.pOpcycles (S.iCycles (S.moduleCatCyclesIso.inv ⟨c, hc⟩)) at he
  have hi : S.iCycles (S.moduleCatCyclesIso.inv ⟨c, hc⟩) = c :=
    congrArg (fun f => f ⟨c, hc⟩) S.moduleCatCyclesIso_inv_iCycles
  rwa [hi] at he

theorem shortComplexCycleClass_eq_iff (S : ShortComplex (ModuleCat.{u} ℤ))
    (c d : S.X₂) (hc : S.g c = 0) (hd : S.g d = 0) :
    shortComplexCycleClass S c hc = shortComplexCycleClass S d hd ↔
      c - d ∈ LinearMap.range S.f.hom := by
  constructor
  · intro h
    apply (S.moduleCat_pOpcycles_eq_iff c d).mp
    simpa only [shortComplexCycleClass_i] using congrArg S.homologyι h
  · intro h
    apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
    rw [shortComplexCycleClass_i, shortComplexCycleClass_i]
    exact (S.moduleCat_pOpcycles_eq_iff c d).mpr h

theorem shortComplexCycleClass_zero (S : ShortComplex (ModuleCat.{u} ℤ)) :
    shortComplexCycleClass S 0 (map_zero S.g.hom) = 0 := by
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  rw [shortComplexCycleClass_i, map_zero, map_zero]

theorem shortComplexCycleClass_add (S : ShortComplex (ModuleCat.{u} ℤ))
    (c d : S.X₂) (hc : S.g c = 0) (hd : S.g d = 0) :
    shortComplexCycleClass S (c + d) (by rw [map_add, hc, hd, add_zero]) =
      shortComplexCycleClass S c hc + shortComplexCycleClass S d hd := by
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  simp only [map_add, shortComplexCycleClass_i]

theorem shortComplexCycleClass_natural {S T : ShortComplex (ModuleCat.{u} ℤ)}
    (φ : S ⟶ T) (c : S.X₂) (hc : S.g c = 0) (ht : T.g (φ.τ₂ c) = 0) :
    (ShortComplex.homologyMap φ) (shortComplexCycleClass S c hc) =
      shortComplexCycleClass T (φ.τ₂ c) ht := by
  apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
  rw [shortComplexCycleClass_i]
  have he := congrArg (fun f => f (S.moduleCatCyclesIso.inv ⟨c, hc⟩))
    (ShortComplex.π_homologyMap_ι φ)
  change T.homologyι ((ShortComplex.homologyMap φ) (shortComplexCycleClass S c hc)) =
    T.pOpcycles (φ.τ₂ (S.iCycles (S.moduleCatCyclesIso.inv ⟨c, hc⟩))) at he
  have hi : S.iCycles (S.moduleCatCyclesIso.inv ⟨c, hc⟩) = c :=
    congrArg (fun f => f ⟨c, hc⟩) S.moduleCatCyclesIso_inv_iCycles
  rwa [hi] at he

variable {X : Type u} [TopologicalSpace X]

theorem singularCycle_condition (n : ℕ) {c : Chain X (n + 1)} (hc : boundary n c = 0) :
    ((complex X).sc (n + 1)).g c = 0 := by
  change (complex X).d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) c = 0
  rw [ChainComplex.next_nat_succ, complex_d]
  exact hc

/-- The actual Mathlib homology class of an explicit positive-degree cycle. -/
def singularCycleClass (n : ℕ) (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    (complex X).homology (n + 1) :=
  shortComplexCycleClass ((complex X).sc (n + 1)) c (singularCycle_condition n hc)

theorem singularCycleClass_eq_iff (n : ℕ) (c d : Chain X (n + 1))
    (hc : boundary n c = 0) (hd : boundary n d = 0) :
    singularCycleClass n c hc = singularCycleClass n d hd ↔
      c - d ∈ LinearMap.range (boundary (n + 1)) := by
  rw [singularCycleClass, singularCycleClass, shortComplexCycleClass_eq_iff]
  change c - d ∈ LinearMap.range
    ((complex X).d ((ComplexShape.down ℕ).prev (n + 1)) (n + 1)).hom ↔ _
  rw [ChainComplex.prev, complex_d]
  rfl

theorem singularCycleClass_zero (n : ℕ) : singularCycleClass (X := X) n 0 (map_zero _) = 0 :=
  shortComplexCycleClass_zero _

theorem singularCycleClass_add (n : ℕ) (c d : Chain X (n + 1))
    (hc : boundary n c = 0) (hd : boundary n d = 0) :
    singularCycleClass n (c + d) (by rw [map_add, hc, hd, add_zero]) =
      singularCycleClass n c hc + singularCycleClass n d hd :=
  shortComplexCycleClass_add _ _ _ _ _

theorem singularCycleClass_natural {Y : Type u} [TopologicalSpace Y] (f : C(X, Y))
    (n : ℕ) (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    (HomologicalComplex.homologyMap (chainMap f) (n + 1)) (singularCycleClass n c hc) =
      singularCycleClass n (map f (n + 1) c) (by rw [← map_boundary, hc, map_zero]) := by
  exact shortComplexCycleClass_natural
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) (n + 1)).map
      (chainMap f)) c (singularCycle_condition n hc) _

end FiniteChains.TopologicalSingular
end

namespace FiniteChains.SingularPrism
open TopologicalSingular
open scoped unitInterval
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)

theorem prism_one_single_eq_zero_of_constant (tau : Simplex X 1) (r : ℤ) (y : Y)
    (h : ∀ t : I, ∀ z, H (t, tau z) = y) : prism H 1 (Finsupp.single tau r) = 0 := by
  have hs i : simplex H tau i = ContinuousMap.const (Domain 2) y := by
    apply ContinuousMap.ext
    intro z
    exact h _ _
  rw [prism_single, altSum, Fin.sum_univ_two]
  simp_all

theorem prism_one_eq_zero_of_constant_on (A : Set X) (y : Y)
    (hH : ∀ t : I, ∀ a ∈ A, H (t, a) = y) {c : Chain X 1} (hc : c ∈ subChains A 1) :
    prism H 1 c = 0 := by
  obtain ⟨b, rfl⟩ := hc
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add b c hb hc => simp_all
  | single tau r =>
    rw [TopologicalSingular.map_single]
    exact prism_one_single_eq_zero_of_constant H _ r y (fun t z => hH t _ (tau z).property)

end FiniteChains.SingularPrism

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- An actual homotopy relative to the square boundary gives an explicit
singular three-chain between the associated two-cycles. -/
theorem squareCycle_homotopic_difference_bounds {p q : GenLoop (Fin 2) X x}
    (h : GenLoop.Homotopic p q) :
    squareCycle q - squareCycle p ∈ LinearMap.range (boundary 2) := by
  obtain ⟨H⟩ := h
  refine ⟨SingularPrism.prism H.toHomotopy 2 squareFundamentalChain, ?_⟩
  have he := SingularPrism.prism_identity_succ H.toHomotopy 1 squareFundamentalChain
  have hz := SingularPrism.prism_one_eq_zero_of_constant_on H.toHomotopy
    (Cube.boundary (Fin 2)) x
    (fun t a ha => (H.eq_fst t ha).trans (GenLoop.boundary p a ha))
    squareFundamentalChain_boundary_supported
  rw [hz, add_zero] at he
  exact he

theorem squareCycle_map {Y : Type} [TopologicalSpace Y] {X : Type} [TopologicalSpace X]
    (f : C(X, Y)) {x : X} (p : GenLoop (Fin 2) X x) :
    squareCycle (Whitehead.mapSquare f p) = map f 2 (squareCycle p) := by
  change map (f.comp p.val) 2 squareFundamentalChain = _
  rw [map_comp, LinearMap.comp_apply]
  rfl

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology
open scoped Topology
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The homology class obtained from an actual based square. The relative
homotopy proof supplies the required three-dimensional singular filling. -/
def pi2CycleClass (x : X) : HomotopyGroup (Fin 2) X x → (complex X).homology 2 :=
  Quotient.lift (fun p => singularCycleClass 1 (squareCycle p) (squareCycle_boundary p))
    (fun _ _ h => (singularCycleClass_eq_iff 1 _ _ _ _).mpr
      (squareCycle_homotopic_difference_bounds h.symm))

theorem pi2CycleClass_mk (x : X) (p : GenLoop (Fin 2) X x) :
    pi2CycleClass x (Quotient.mk _ p) = singularCycleClass 1 (squareCycle p) (squareCycle_boundary p) := rfl

theorem pi2CycleClass_one (x : X) : pi2CycleClass x 1 = 0 := by
  change singularCycleClass 1 (squareCycle (GenLoop.const)) (squareCycle_boundary _) = 0
  simp only [squareCycle_const, singularCycleClass_zero]


/-- The canonical degree-two Hurewicz function lands in the exact integral
singular homology functor used by Whitehead's statement. Additivity and the
simply-connected isomorphism theorem are separate obligations. -/
def singularHurewicz2 (x : X) : HomotopyGroup (Fin 2) X x →
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)) :=
  fun z => (homologyMathlibIso (TopCat.of X) 2).hom (pi2CycleClass x z)

theorem singularHurewicz2_one (x : X) : singularHurewicz2 x 1 = 0 := by
  rw [singularHurewicz2, pi2CycleClass_one, map_zero]

theorem singularHurewicz2_natural (f : C(X, Y)) (x : X) (z : HomotopyGroup (Fin 2) X x) :
    ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom f)).hom (singularHurewicz2 x z)) =
        singularHurewicz2 (f x) (Whitehead.pi2Map f x z) := by
  have he := congrArg (fun g => g (pi2CycleClass x z))
    (homologyMathlibIso_natural (TopCat.ofHom f) 2)
  change (homologyMathlibIso (TopCat.of Y) 2).hom
    ((HomologicalComplex.homologyMap (chainMap f) 2) (pi2CycleClass x z)) =
      ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom f)).hom (singularHurewicz2 x z)) at he
  rw [(show (HomologicalComplex.homologyMap (chainMap f) 2) (pi2CycleClass x z) =
      pi2CycleClass (f x) (Whitehead.pi2Map f x z) by
    induction z using Quotient.inductionOn with
    | h p =>
      change (HomologicalComplex.homologyMap (chainMap f) 2)
        (singularCycleClass 1 (squareCycle p) (squareCycle_boundary p)) = singularCycleClass 1
          (squareCycle (Whitehead.mapSquare f p)) (squareCycle_boundary _)
      simpa only [squareCycle_map] using
        (singularCycleClass_natural f 1 (squareCycle p) (squareCycle_boundary p)))] at he
  exact he.symm

theorem singularHurewicz2_pushdown_zero_of_killsPi2 (f : C(X, Y)) (hf : Whitehead.KillsPi2 f)
    (x : X) (z : HomotopyGroup (Fin 2) X x) :
    ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom f)).hom (singularHurewicz2 x z)) = 0 := by
  rw [singularHurewicz2_natural, (Whitehead.killsPi2_iff f).mp hf x z, singularHurewicz2_one]

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology

def squareHalf : I := ⟨1 / 2, by constructor <;> norm_num⟩

def leftRectangle (a : I) : C((Fin 2 → I), Fin 2 → I) where
  toFun z := ![a * z 0, z 1]
  continuous_toFun := by fun_prop

def rightRectangle (a : I) : C((Fin 2 → I), Fin 2 → I) where
  toFun z := ![unitInterval.symm (unitInterval.symm a * unitInterval.symm (z 0)), z 1]
  continuous_toFun := by fun_prop

def leftRectangleSweep : ContinuousMap.Homotopy (leftRectangle 0) (leftRectangle squareHalf) where
  toFun w := leftRectangle (w.1 * squareHalf) w.2
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact ((continuous_fst.subtype_val.mul continuous_const).mul
        (((continuous_apply 0).comp continuous_snd).subtype_val)).subtype_mk _
    · change Continuous (fun w : I × (Fin 2 → I) => w.2 1)
      exact (continuous_apply 1).comp continuous_snd
  map_zero_left z := by simp
  map_one_left z := by simp

def rightRectangleSweep : ContinuousMap.Homotopy (rightRectangle 0) (rightRectangle squareHalf) where
  toFun w := rightRectangle (w.1 * squareHalf) w.2
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact unitInterval.continuous_symm.comp
        (((unitInterval.continuous_symm.comp
          ((continuous_fst.subtype_val.mul continuous_const).subtype_mk _)).subtype_val.mul
            ((unitInterval.continuous_symm.comp
              ((continuous_apply 0).comp continuous_snd)).subtype_val)).subtype_mk _)
    · change Continuous (fun w : I × (Fin 2 → I) => w.2 1)
      exact (continuous_apply 1).comp continuous_snd
  map_zero_left z := by simp
  map_one_left z := by simp

theorem rightRectangle_zero : rightRectangle 0 = ContinuousMap.id (Fin 2 → I) := by
  apply ContinuousMap.ext
  intro z
  funext i
  fin_cases i <;> simp [rightRectangle]

theorem rectangle_common_edge (a : I) (z : Domain 1) :
    leftRectangle a (cubeEdge 0 1 z) = rightRectangle a (cubeEdge 0 0 z) := by simp_all [leftRectangle, rightRectangle, cubeEdge, Whitehead.squareEdge]

theorem leftRectangle_horizontal_boundary (a v : I) (hv : v = 0 ∨ v = 1) (z : Domain 1) :
    leftRectangle a (cubeEdge 1 v z) ∈ Cube.boundary (Fin 2) := by
  refine ⟨1, ?_⟩
  simpa [leftRectangle, cubeEdge, Whitehead.squareEdge] using hv

theorem rightRectangle_horizontal_boundary (a v : I) (hv : v = 0 ∨ v = 1) (z : Domain 1) :
    rightRectangle a (cubeEdge 1 v z) ∈ Cube.boundary (Fin 2) := by
  refine ⟨1, ?_⟩
  simpa [rightRectangle, cubeEdge, Whitehead.squareEdge] using hv

theorem leftRectangle_outer_boundary (a : I) (z : Domain 1) :
    leftRectangle a (cubeEdge 0 0 z) ∈ Cube.boundary (Fin 2) := by
  exact ⟨0, Or.inl (by simp [leftRectangle, cubeEdge, Whitehead.squareEdge])⟩

theorem rightRectangle_outer_boundary (a : I) (z : Domain 1) :
    rightRectangle a (cubeEdge 0 1 z) ∈ Cube.boundary (Fin 2) := by
  exact ⟨0, Or.inr (by simp [rightRectangle, cubeEdge, Whitehead.squareEdge])⟩

theorem leftRectangle_zero_boundary (z : Fin 2 → I) :
    leftRectangle 0 z ∈ Cube.boundary (Fin 2) :=
  ⟨0, Or.inl (by simp [leftRectangle])⟩

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

def leftSquareSweep (p : GenLoop (Fin 2) X x) :
    ContinuousMap.Homotopy (p.val.comp (leftRectangle 0)) (p.val.comp (leftRectangle squareHalf)) :=
  (ContinuousMap.Homotopy.refl p.val).comp leftRectangleSweep

def rightSquareSweep (p : GenLoop (Fin 2) X x) :
    ContinuousMap.Homotopy (p.val.comp (rightRectangle 0)) (p.val.comp (rightRectangle squareHalf)) :=
  (ContinuousMap.Homotopy.refl p.val).comp rightRectangleSweep


/-- All six outer-edge prisms vanish. The two copies of the moving internal
edge are equal and have opposite signs. -/
theorem squareSweep_boundary_prisms_cancel (p : GenLoop (Fin 2) X x) :
    SingularPrism.prism (leftSquareSweep p) 1 (boundary 1 squareFundamentalChain) +
      SingularPrism.prism (rightSquareSweep p) 1 (boundary 1 squareFundamentalChain) = 0 := by
  have hlh v hv :
      SingularPrism.prism (leftSquareSweep p) 1 (Finsupp.single (cubeEdge 1 v) 1) = 0 :=
    SingularPrism.prism_one_single_eq_zero_of_constant _ _ 1 x
      (fun t z => GenLoop.boundary p _ (leftRectangle_horizontal_boundary (t * squareHalf) v hv z))
  have hrh v hv :
      SingularPrism.prism (rightSquareSweep p) 1 (Finsupp.single (cubeEdge 1 v) 1) = 0 :=
    SingularPrism.prism_one_single_eq_zero_of_constant _ _ 1 x
      (fun t z => GenLoop.boundary p _ (rightRectangle_horizontal_boundary (t * squareHalf) v hv z))
  have hlo : SingularPrism.prism (leftSquareSweep p) 1 (Finsupp.single (cubeEdge 0 0) 1) = 0 :=
    SingularPrism.prism_one_single_eq_zero_of_constant _ _ 1 x
      (fun t z => GenLoop.boundary p _ (leftRectangle_outer_boundary (t * squareHalf) z))
  have hro : SingularPrism.prism (rightSquareSweep p) 1 (Finsupp.single (cubeEdge 0 1) 1) = 0 :=
    SingularPrism.prism_one_single_eq_zero_of_constant _ _ 1 x
      (fun t z => GenLoop.boundary p _ (rightRectangle_outer_boundary (t * squareHalf) z))
  simp only [squareFundamentalChain_boundary, map_sub, map_add,
    hlh 0 (Or.inl rfl), hlh 1 (Or.inr rfl), hrh 0 (Or.inl rfl), hrh 1 (Or.inr rfl), hlo, hro]
  rw [(show SingularPrism.prism (leftSquareSweep p) 1 (Finsupp.single (cubeEdge 0 1) 1) =
      SingularPrism.prism (rightSquareSweep p) 1 (Finsupp.single (cubeEdge 0 0) 1) by
    rw [SingularPrism.prism_single, SingularPrism.prism_single, SingularPrism.altSum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply congrArg (fun tau => Finsupp.single tau 1)
    apply ContinuousMap.ext
    intro z
    change p (leftRectangle ((SingularPrism.prismMap i z).1 * squareHalf)
      (cubeEdge 0 1 (SingularPrism.prismMap i z).2)) =
        p (rightRectangle ((SingularPrism.prismMap i z).1 * squareHalf)
          (cubeEdge 0 0 (SingularPrism.prismMap i z).2))
    rw [rectangle_common_edge])]
  abel


/-- Splitting the parameter square into two rectangles changes its pushed
fundamental chain by an explicit singular boundary. -/
theorem squareCycle_rectangle_sum_difference_bounds (p : GenLoop (Fin 2) X x) :
    map (p.val.comp (leftRectangle squareHalf)) 2 squareFundamentalChain +
      map (p.val.comp (rightRectangle squareHalf)) 2 squareFundamentalChain - squareCycle p ∈
        LinearMap.range (boundary 2) := by
  refine ⟨SingularPrism.prism (leftSquareSweep p) 2 squareFundamentalChain +
    SingularPrism.prism (rightSquareSweep p) 2 squareFundamentalChain, ?_⟩
  have hl := SingularPrism.prism_identity_succ (leftSquareSweep p) 1 squareFundamentalChain
  have hr := SingularPrism.prism_identity_succ (rightSquareSweep p) 1 squareFundamentalChain
  rw [(show map (p.val.comp (leftRectangle 0)) 2 squareFundamentalChain = 0 by
    have he : p.val.comp (leftRectangle 0) = ContinuousMap.const _ x := by
      apply ContinuousMap.ext
      intro z
      exact GenLoop.boundary p _ (leftRectangle_zero_boundary z)
    rw [he, squareFundamentalChain, map_sub, map_single, map_single]
    exact sub_self _), sub_zero] at hl
  conv_rhs at hr => rw [rightRectangle_zero, ContinuousMap.comp_id]
  have hz := squareSweep_boundary_prisms_cancel p
  rw [map_add]
  change _ = _ - map p.val 2 squareFundamentalChain
  linear_combination (norm := abel) hl + hr - hz

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem transAt_leftRectangle (p q : GenLoop (Fin 2) X x) :
    (GenLoop.transAt 0 p q).val.comp (leftRectangle squareHalf) = p.val := by
  apply ContinuousMap.ext
  intro z
  change (if ((leftRectangle squareHalf z) 0 : ℝ) ≤ 1 / 2
    then p (Function.update (leftRectangle squareHalf z) 0
      (Set.projIcc 0 1 zero_le_one (2 * (leftRectangle squareHalf z) 0)))
    else q (Function.update (leftRectangle squareHalf z) 0
      (Set.projIcc 0 1 zero_le_one (2 * (leftRectangle squareHalf z) 0 - 1)))) = p z
  have hh : ((leftRectangle squareHalf z) 0 : ℝ) ≤ 1 / 2 := by
    change (1 / 2) * (z 0 : ℝ) ≤ 1 / 2
    nlinarith [(z 0).property.2]
  rw [if_pos hh]
  apply congrArg p
  funext i
  fin_cases i
  · simp only [Function.update_apply]
    rw [if_pos (by rfl)]
    have he : 2 * ((leftRectangle squareHalf z) 0) = (z 0 : ℝ) := by
      change 2 * ((1 / 2 : ℝ) * (z 0 : ℝ)) = _
      ring
    rw [he, Set.projIcc_of_mem zero_le_one (z 0).property]
    exact Subtype.ext rfl
  · rfl

theorem rightRectangle_half_coordinate (z : Fin 2 → I) :
    ((rightRectangle squareHalf z) 0 : ℝ) = (1 + (z 0 : ℝ)) / 2 := by
  change 1 - ((1 - (1 / 2)) * (1 - (z 0 : ℝ))) = _
  ring

theorem transAt_rightRectangle (p q : GenLoop (Fin 2) X x) :
    (GenLoop.transAt 0 p q).val.comp (rightRectangle squareHalf) = q.val := by
  apply ContinuousMap.ext
  intro z
  change (if ((rightRectangle squareHalf z) 0 : ℝ) ≤ 1 / 2
    then p (Function.update (rightRectangle squareHalf z) 0
      (Set.projIcc 0 1 zero_le_one (2 * (rightRectangle squareHalf z) 0)))
    else q (Function.update (rightRectangle squareHalf z) 0
      (Set.projIcc 0 1 zero_le_one (2 * (rightRectangle squareHalf z) 0 - 1)))) = q z
  split_ifs with h
  · have hz : z 0 = 0 := by
      ext
      have hr := rightRectangle_half_coordinate z
      change (z 0 : ℝ) = 0
      nlinarith [(z 0).property.1]
    have he : 2 * ((rightRectangle squareHalf z) 0 : ℝ) = 1 := by
      rw [rightRectangle_half_coordinate, hz]
      norm_num
    calc
      _ = x := GenLoop.boundary p _ ⟨0, Or.inr (by
        simp only [Function.update_self]
        rw [he]
        exact Set.projIcc_right _ )⟩
      _ = q z := (GenLoop.boundary q z ⟨0, Or.inl hz⟩).symm
  · apply congrArg q
    funext i
    fin_cases i
    · simp only [Function.update_apply]
      rw [if_pos (by rfl)]
      have he : 2 * ((rightRectangle squareHalf z) 0) - 1 = (z 0 : ℝ) := by
        rw [rightRectangle_half_coordinate]
        ring
      rw [he, Set.projIcc_of_mem zero_le_one (z 0).property]
      exact Subtype.ext rfl
    · simp [rightRectangle]

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology
open scoped Topology
variable {X : Type} [TopologicalSpace X] {x : X}


theorem squareCycleClass_transAt (p q : GenLoop (Fin 2) X x) :
    singularCycleClass 1 (squareCycle (GenLoop.transAt 0 p q)) (squareCycle_boundary _) =
      singularCycleClass 1 (squareCycle p) (squareCycle_boundary p) +
        singularCycleClass 1 (squareCycle q) (squareCycle_boundary q) := by
  rw [← singularCycleClass_add]
  apply Eq.symm
  exact (singularCycleClass_eq_iff 1 _ _ _ _).mpr (by
    have he := squareCycle_rectangle_sum_difference_bounds (GenLoop.transAt 0 p q)
    rwa [transAt_leftRectangle, transAt_rightRectangle] at he)

theorem pi2CycleClass_mul (x : X) (a b : HomotopyGroup (Fin 2) X x) :
    pi2CycleClass x (a * b) = pi2CycleClass x a + pi2CycleClass x b := by
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      calc
        _ = pi2CycleClass x (Quotient.mk _ (GenLoop.transAt 0 q p)) :=
          congrArg (pi2CycleClass x) (HomotopyGroup.mul_spec)
        _ = _ := by
          rw [pi2CycleClass_mk, pi2CycleClass_mk, pi2CycleClass_mk, squareCycleClass_transAt, add_comm]



/-- Vanishing of the genuine Hurewicz image is exactly the existence of an
integral singular filling of the square's fundamental cycle. -/
theorem singularHurewicz2_mk_eq_zero_iff (p : GenLoop (Fin 2) X x) :
    singularHurewicz2 x (Quotient.mk _ p) = 0 ↔
      ∃ b : Chain X 3, boundary 2 b = squareCycle p := by
  have hi := (ModuleCat.mono_iff_injective (homologyMathlibIso (TopCat.of X) 2).hom).mp
    inferInstance
  have he : singularHurewicz2 x (Quotient.mk _ p) = 0 ↔
      singularCycleClass 1 (squareCycle p) (squareCycle_boundary p) = 0 := by
    constructor
    · intro h
      apply hi
      rw [map_zero]
      exact h
    · intro h
      change (homologyMathlibIso (TopCat.of X) 2).hom
        (singularCycleClass 1 (squareCycle p) (squareCycle_boundary p)) = 0
      rw [h, map_zero]
  rw [he]
  constructor
  · intro h
    have hc := (singularCycleClass_eq_iff 1 (squareCycle p) 0 (squareCycle_boundary p) (map_zero _)).mp
      (h.trans (singularCycleClass_zero 1).symm)
    simpa using hc
  · intro h
    have hc := (singularCycleClass_eq_iff 1 (squareCycle p) 0 (squareCycle_boundary p) (map_zero _)).mpr
      (by simpa using h)
    exact hc.trans (singularCycleClass_zero 1)

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology
open scoped Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem basedTriangle_eq_of_zero_coordinate (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x)
    (z : Domain 2) (i : Fin 3) (hi : z.val i = 0) : tau z = x := by
  obtain ⟨w, hw⟩ := domain_zero_coordinate_face z i hi
  have he := congrArg (fun f : Simplex X 1 => f w) (h i)
  change tau (stdSimplex.map (SimplexCategory.δ i) w) = x at he
  rwa [hw] at he

/-- A triangle with all three faces at the basepoint is an actual based
square, by collapsing the upper triangle of the square onto an edge. -/
def basedTriangleSquare (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) : GenLoop (Fin 2) X x :=
  ⟨tau.comp squareToTriangle, by
    intro z hz
    obtain ⟨i, hi⟩ := squareToTriangle_boundary z hz
    exact basedTriangle_eq_of_zero_coordinate tau h _ i hi⟩

def basedTriangleCycle (tau : Simplex X 2) (x : X) : Chain X 2 :=
  Finsupp.single tau 1 - Finsupp.single (ContinuousMap.const (Domain 2) x) 1

theorem basedTriangleCycle_boundary (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) :
    boundary 1 (basedTriangleCycle tau x) = 0 := by
  rw [basedTriangleCycle, map_sub, boundary_two_single, boundary_constant_two, h 0, h 1, h 2]
  abel

/-- Exact chain identity; no subdivision or comparison hypothesis is used. -/
theorem squareCycle_basedTriangleSquare (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) :
    squareCycle (basedTriangleSquare tau h) = basedTriangleCycle tau x := by
  have he1 : simplexMap (basedTriangleSquare tau h).val 2 cubeTriangle1 = tau := by
    apply ContinuousMap.ext
    intro z
    change tau (squareToTriangle (cubeTriangle1 z)) = tau z
    rw [squareToTriangle_triangle1]
  have he0 : simplexMap (basedTriangleSquare tau h).val 2 cubeTriangle0 =
      ContinuousMap.const (Domain 2) x := by
    apply ContinuousMap.ext
    intro z
    exact basedTriangle_eq_of_zero_coordinate tau h _ 1 (squareToTriangle_triangle0_zero z)
  rw [squareCycle, squareFundamentalChain, map_sub, map_single, map_single, he1, he0]
  rfl

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]

def vertexNormalizationHomotopy (x : X) (tau : Simplex X 0) :
    tau.Homotopy (ContinuousMap.const (Domain 0) x) where
  toFun w := PathConnectedSpace.somePath (tau (stdSimplex.vertex 0)) x w.1
  continuous_toFun := (PathConnectedSpace.somePath _ _).continuous.comp continuous_fst
  map_zero_left z := by
    rw [Path.source]
    apply congrArg tau
    apply Subtype.ext
    funext i
    have hz := z.property.2
    simpa [stdSimplex.vertex, show i = 0 by omega] using hz.symm
  map_one_left _ := Path.target _

theorem vertexNormalizationHomotopy_apply (x : X) (tau : Simplex X 0) (t : I) (z : Domain 0) :
    vertexNormalizationHomotopy x tau (t, z) = PathConnectedSpace.somePath (tau z) x t := by
  have hz : stdSimplex.vertex 0 = z :=
    by
      apply Subtype.ext
      funext i
      have hz := z.property.2
      simpa [stdSimplex.vertex, show i = 0 by omega] using hz.symm
  change PathConnectedSpace.somePath (tau (stdSimplex.vertex 0)) x t = _
  rw [hz]

/-- Endpoint motion for every edge is chosen from the original endpoint
itself, so different edges incident at that endpoint move it identically. -/
theorem edgeVertexNormalization_exists (x : X) (tau : Simplex X 1) :
    ∃ g : Simplex X 1, ∃ F : tau.Homotopy g,
      ∀ (t : I) (z : Domain 1), z ∈ simplexBoundary 1 →
        F (t, z) = PathConnectedSpace.somePath (tau z) x t := by
  obtain ⟨g, F, hF⟩ := simplex_face_homotopy_extension tau
    (fun i => (vertexNormalizationHomotopy x (face i tau)).toContinuousMap)
    (by
      intro i j t z w h
      change vertexNormalizationHomotopy x (face i tau) (t, z) =
        vertexNormalizationHomotopy x (face j tau) (t, w)
      simp only [vertexNormalizationHomotopy_apply, face_apply]
      exact congrArg (fun a : X => PathConnectedSpace.somePath a x t) (congrArg tau h))
    (fun i z => (vertexNormalizationHomotopy x (face i tau)).apply_zero z)
  refine ⟨g, F, ?_⟩
  intro t z hz
  obtain ⟨i, hi⟩ := hz
  obtain ⟨w, hw⟩ := domain_zero_coordinate_face z i hi
  rw [← hw, hF]
  exact vertexNormalizationHomotopy_apply x (face i tau) t w

def edgeVertexNormalized (x : X) (tau : Simplex X 1) : Simplex X 1 :=
  (edgeVertexNormalization_exists x tau).choose

def edgeVertexHomotopy (x : X) (tau : Simplex X 1) :
    tau.Homotopy (edgeVertexNormalized x tau) :=
  (edgeVertexNormalization_exists x tau).choose_spec.choose

theorem edgeVertexHomotopy_boundary (x : X) (tau : Simplex X 1) (t : I)
    (z : Domain 1) (hz : z ∈ simplexBoundary 1) :
    edgeVertexHomotopy x tau (t, z) = PathConnectedSpace.somePath (tau z) x t :=
  (edgeVertexNormalization_exists x tau).choose_spec.choose_spec t z hz

theorem simplexOne_vertex_mem_boundary (i : Fin 2) :
    stdSimplex.vertex i ∈ simplexBoundary 1 := by
  fin_cases i
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

theorem edgeVertexNormalized_vertex (x : X) (tau : Simplex X 1) (i : Fin 2) :
    edgeVertexNormalized x tau (stdSimplex.vertex i) = x := by
  have he := edgeVertexHomotopy_boundary x tau 1 (stdSimplex.vertex i) (simplexOne_vertex_mem_boundary i)
  simp_all

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

def edgeVertexNullHomotopy (x : X) (tau : Simplex X 1) :
    ContinuousMap.HomotopyRel (edgeVertexNormalized x tau)
      (ContinuousMap.const (Domain 1) x) (simplexBoundary 1) :=
  Classical.choice (singularEdge_nullhomotopic x (edgeVertexNormalized x tau)
    (edgeVertexNormalized_vertex x tau 0) (edgeVertexNormalized_vertex x tau 1))

def normalizedEdgeHomotopy (x : X) (tau : Simplex X 1) :
    tau.Homotopy (ContinuousMap.const (Domain 1) x) :=
  (edgeVertexHomotopy x tau).trans (edgeVertexNullHomotopy x tau).toHomotopy

def normalizationVertexPath (x a : X) : Path a x :=
  (PathConnectedSpace.somePath a x).trans (Path.refl x)

/-- Endpoint motion depends only on the original point, for all singular
edges simultaneously; this is the coherence needed for triangle boundaries. -/
theorem normalizedEdgeHomotopy_boundary (x : X) (tau : Simplex X 1) (t : I)
    (z : Domain 1) (hz : z ∈ simplexBoundary 1) :
    normalizedEdgeHomotopy x tau (t, z) = normalizationVertexPath x (tau z) t := by
  rw [normalizedEdgeHomotopy, ContinuousMap.Homotopy.trans_apply,
    normalizationVertexPath, Path.trans_apply]
  split_ifs
  · exact edgeVertexHomotopy_boundary x tau _ z hz
  · exact (edgeVertexNullHomotopy x tau).eq_snd _ hz

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem normalizedEdgeHomotopies_coherent (x : X) (tau : Simplex X 2)
    (i j : Fin 3) (t : I) (z w : Domain 1)
    (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
    normalizedEdgeHomotopy x (face i tau) (t, z) = normalizedEdgeHomotopy x (face j tau) (t, w) := by grind [simplex_face_injective, normalizedEdgeHomotopy_boundary, face_apply, simplex_face_intersection_boundary]

theorem normalizedTriangle_exists (x : X) (tau : Simplex X 2) :
    ∃ g : Simplex X 2, ∃ F : tau.Homotopy g,
      ∀ (i : Fin 3) (t : I) (z : Domain 1),
        F (t, stdSimplex.map (SimplexCategory.δ i) z) = normalizedEdgeHomotopy x (face i tau) (t, z) :=
  simplex_face_homotopy_extension tau
    (fun i => (normalizedEdgeHomotopy x (face i tau)).toContinuousMap)
    (normalizedEdgeHomotopies_coherent x tau)
    (fun i z => (normalizedEdgeHomotopy x (face i tau)).apply_zero z)

def normalizedTriangle (x : X) (tau : Simplex X 2) : Simplex X 2 :=
  (normalizedTriangle_exists x tau).choose

def normalizedTriangleHomotopy (x : X) (tau : Simplex X 2) :
    tau.Homotopy (normalizedTriangle x tau) :=
  (normalizedTriangle_exists x tau).choose_spec.choose

theorem normalizedTriangleHomotopy_face (x : X) (tau : Simplex X 2)
    (i : Fin 3) (t : I) (z : Domain 1) :
    normalizedTriangleHomotopy x tau (t, stdSimplex.map (SimplexCategory.δ i) z) =
      normalizedEdgeHomotopy x (face i tau) (t, z) :=
  (normalizedTriangle_exists x tau).choose_spec.choose_spec i t z

theorem normalizedTriangle_face (x : X) (tau : Simplex X 2) (i : Fin 3) :
    face i (normalizedTriangle x tau) = ContinuousMap.const (Domain 1) x := by
  apply ContinuousMap.ext
  intro z
  have he := normalizedTriangleHomotopy_face x tau i 1 z
  rw [(normalizedTriangleHomotopy x tau).apply_one, (normalizedEdgeHomotopy x (face i tau)).apply_one] at he
  exact he

end FiniteChains.TopologicalSingular

section
open scoped Topology Topology.Homotopy unitInterval
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.TopologicalSingular

variable {d : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- Insert a fixed coordinate into a cube. -/
def cubeFace {d : ℕ} (i : Fin (d + 1)) (a : I) : C(I^Fin d, I^Fin (d + 1)) where
  toFun t := i.insertNth a t
  continuous_toFun := by fun_prop

@[simp]
theorem cubeFace_apply {d : ℕ} (i : Fin (d + 1)) (a : I) (t : I^Fin d) :
    cubeFace i a t = i.insertNth a t :=
  rfl

@[simp]
theorem cubeFace_apply_same {d : ℕ} (i : Fin (d + 1)) (a : I) (t : I^Fin d) :
    cubeFace i a t i = a := by simp

@[simp]
theorem cubeFace_apply_succAbove {d : ℕ} (i : Fin (d + 1)) (a : I)
    (t : I^Fin d) (j : Fin d) :
    cubeFace i a t (i.succAbove j) = t j := by simp

/-- The codimension-two cubical skeleton: at least two distinct coordinates are endpoints. -/
def cubeCodimTwo (d : ℕ) : Set (I^Fin d) :=
  {t | ∃ i j : Fin d, i ≠ j ∧ (t i = 0 ∨ t i = 1) ∧ (t j = 0 ∨ t j = 1)}


/-! ### The two routes around a square -/

/-- The bottom edge of the unit square, directed from left to right. -/
def squareBottom : Path ((0, 0) : I × I) (1, 0) where
  toFun t := (t, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The right edge of the unit square, directed from bottom to top. -/
def squareRight : Path ((1, 0) : I × I) (1, 1) where
  toFun t := (1, t)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The left edge of the unit square, directed from bottom to top. -/
def squareLeft : Path ((0, 0) : I × I) (0, 1) where
  toFun t := (0, t)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The top edge of the unit square, directed from left to right. -/
def squareTop : Path ((0, 1) : I × I) (1, 1) where
  toFun t := (t, 1)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The bottom-then-right route around the unit square. -/
def squareBottomRight : Path ((0, 0) : I × I) (1, 1) :=
  squareBottom.trans squareRight

/-- The left-then-top route around the unit square. -/
def squareLeftTop : Path ((0, 0) : I × I) (1, 1) :=
  squareLeft.trans squareTop

/-- Convex interpolation across the square gives a path homotopy between its two monotone
edge routes. -/
def squareBoundaryHomotopy :
    Path.Homotopy squareBottomRight squareLeftTop where
  toFun p :=
    (Set.Icc.convexComb (squareBottomRight p.2).1 (squareLeftTop p.2).1 p.1,
      Set.Icc.convexComb (squareBottomRight p.2).2 (squareLeftTop p.2).2 p.1)
  continuous_toFun := by fun_prop
  map_zero_left t := by simp
  map_one_left t := by simp
  prop' s t ht := by
    rcases ht with rfl | ht
    · simp
    · simp_all

@[simp]
theorem cubeFace_last_eq_snoc {m : ℕ} (a : I) (t : I^Fin m) :
    cubeFace (Fin.last m) a t = Fin.snoc t a := by simp

@[simp]
theorem cubeFace_penultimate_snoc {m : ℕ} (a b : I) (t : I^Fin m) :
    cubeFace (Fin.last m).castSucc a (Fin.snoc t b) = Fin.snoc (Fin.snoc t a) b := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      have hlast : (Fin.last m).castSucc.succAbove (Fin.last m) = Fin.last (m + 1) := by
        ext
        simp
      rw [← hlast, cubeFace_apply_succAbove]
      simp
  | cast j =>
      induction j using Fin.lastCases with
      | last => simp [cubeFace]
      | cast j => simp [cubeFace, Fin.insertNth_apply_below, Fin.snoc]

@[simp]
theorem update_last_eq_snoc_init {m : ℕ} (t : I^Fin (m + 1)) (a : I) :
    Function.update t (Fin.last m) a = Fin.snoc (Fin.init t) a := by
  conv_lhs => rw [← Fin.snoc_init_self t]
  exact Fin.update_snoc_last _ _ _

/-- The convex sweep from the bottom-right route to the left-top route, with `m` passive
coordinates prepended. -/
def squareSweepCube (m : ℕ) :
    C(I × (I^Fin (m + 1)), I^Fin (m + 2)) where
  toFun st :=
    Fin.snoc (Fin.snoc (Fin.init st.2) (squareBoundaryHomotopy (st.1, st.2 (Fin.last m))).1)
      (squareBoundaryHomotopy (st.1, st.2 (Fin.last m))).2
  continuous_toFun := by fun_prop

/-- Pointwise concatenation formula with the unclamped half-interval coordinates exposed. -/
theorem genLoop_transAt_apply_path {N : Type*} [DecidableEq N] (i : N)
    (f g : Ω^ N X x) (t : I^N) :
    (GenLoop.transAt i f g).val t =
      if h : (t i : ℝ) ≤ 1 / 2 then
        f (Function.update t i
          ⟨2 * t i, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨(t i).2.1, h⟩⟩)
      else
        g (Function.update t i
          ⟨2 * t i - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 h).le, (t i).2.2⟩⟩) := by
  change (if (t i : ℝ) ≤ 1 / 2 then
      f (Function.update t i (Set.projIcc 0 1 zero_le_one (2 * t i)))
    else g (Function.update t i (Set.projIcc 0 1 zero_le_one (2 * t i - 1)))) = _
  split_ifs with h
  · rw [Set.projIcc_of_mem _ ((unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨(t i).2.1, h⟩)]
  · rw [Set.projIcc_of_mem _ (unitInterval.two_mul_sub_one_mem_iff.2
      ⟨(not_le.1 h).le, (t i).2.2⟩)]

/-- A cubical shell is a map on a cube which collapses the codimension-two skeleton to the
chosen basepoint. -/
structure CubicalShell (d : ℕ) (X : Type*) [TopologicalSpace X] (x : X) where
  /-- The map on the ambient `(d+1)`-cube. -/
  map : C(I^Fin (d + 1), X)
  /-- The map is constant on the codimension-two cubical skeleton. -/
  codimTwo (t : I^Fin (d + 1)) (ht : t ∈ cubeCodimTwo (d + 1)) : map t = x

namespace CubicalShell

/-- The facet of a cubical shell at coordinate `i` and endpoint `a`, as a based generalized
loop. -/
def faceLoop (S : CubicalShell d X x) (i : Fin (d + 1)) (a : I)
    (ha : a = 0 ∨ a = 1) : Ω^ (Fin d) X x :=
  ⟨S.map.comp (cubeFace i a), fun t ht ↦ S.codimTwo _
    (by
      obtain ⟨j, hj⟩ := ht
      refine ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, ?_, ?_⟩
      · simpa using ha
      · simpa using hj)⟩

@[simp]
theorem faceLoop_apply (S : CubicalShell d X x) (i : Fin (d + 1)) (a : I)
    (ha : a = 0 ∨ a = 1) (t : I^Fin d) :
    (S.faceLoop i a ha).val t = S.map (cubeFace i a t) :=
  rfl

/-- The lower facet loop. -/
def lowerFaceLoop (S : CubicalShell d X x) (i : Fin (d + 1)) :
    Ω^ (Fin d) X x :=
  S.faceLoop i 0 (Or.inl rfl)

/-- The upper facet loop. -/
def upperFaceLoop (S : CubicalShell d X x) (i : Fin (d + 1)) :
    Ω^ (Fin d) X x :=
  S.faceLoop i 1 (Or.inr rfl)

@[simp]
theorem lowerFaceLoop_apply (S : CubicalShell d X x) (i : Fin (d + 1))
    (t : I^Fin d) :
    (S.lowerFaceLoop i).val t = S.map (cubeFace i 0 t) :=
  rfl

@[simp]
theorem upperFaceLoop_apply (S : CubicalShell d X x) (i : Fin (d + 1))
    (t : I^Fin d) :
    (S.upperFaceLoop i).val t = S.map (cubeFace i 1 t) :=
  rfl

/-- The sweep starts at the concatenation of the last lower face with the penultimate upper
face. -/
theorem squareSweepCube_zero {m : ℕ} (S : CubicalShell (m + 1) X x)
    (t : I^Fin (m + 1)) :
    S.map (squareSweepCube m (0, t)) =
      (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last (m + 1)))
        (S.upperFaceLoop (Fin.last m).castSucc)).val t := by
  change S.map (Fin.snoc (Fin.snoc (Fin.init t)
    (squareBoundaryHomotopy (0, t (Fin.last m))).1)
    (squareBoundaryHomotopy (0, t (Fin.last m))).2) = _
  rw [ContinuousMap.HomotopyWith.apply_zero, squareBottomRight]
  simp only [Path.coe_toContinuousMap]
  rw [Path.trans_apply, genLoop_transAt_apply_path]
  split_ifs with h
  · change S.map _ = S.map (cubeFace (Fin.last (m + 1)) 0 _)
    apply congrArg S.map
    rw [cubeFace_last_eq_snoc, update_last_eq_snoc_init]
    rfl
  · change S.map _ = S.map (cubeFace (Fin.last m).castSucc 1 _)
    apply congrArg S.map
    rw [update_last_eq_snoc_init, cubeFace_penultimate_snoc]
    rfl

/-- The sweep ends at the concatenation of the penultimate lower face with the last upper
face. -/
theorem squareSweepCube_one {m : ℕ} (S : CubicalShell (m + 1) X x)
    (t : I^Fin (m + 1)) :
    S.map (squareSweepCube m (1, t)) =
      (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last m).castSucc)
        (S.upperFaceLoop (Fin.last (m + 1)))).val t := by
  change S.map (Fin.snoc (Fin.snoc (Fin.init t)
    (squareBoundaryHomotopy (1, t (Fin.last m))).1)
    (squareBoundaryHomotopy (1, t (Fin.last m))).2) = _
  rw [ContinuousMap.HomotopyWith.apply_one, squareLeftTop]
  simp only [Path.coe_toContinuousMap]
  rw [Path.trans_apply, genLoop_transAt_apply_path]
  split_ifs with h
  · change S.map _ = S.map (cubeFace (Fin.last m).castSucc 0 _)
    apply congrArg S.map
    rw [update_last_eq_snoc_init, cubeFace_penultimate_snoc]
    rfl
  · change S.map _ = S.map (cubeFace (Fin.last (m + 1)) 1 _)
    apply congrArg S.map
    rw [cubeFace_last_eq_snoc, update_last_eq_snoc_init]
    rfl

/-- A facet of the ambient cube is constant at the shell basepoint. -/
def IsConstantFace (S : CubicalShell d X x) (i : Fin (d + 1)) (a : I) : Prop :=
  ∀ t : I^Fin (d + 1), t i = a → S.map t = x


theorem lowerFaceLoop_eq_const (S : CubicalShell d X x) (i : Fin (d + 1))
    (h : S.IsConstantFace i 0) :
    S.lowerFaceLoop i = GenLoop.const :=
  (by
    apply GenLoop.ext
    intro t
    exact h _ (by simp))

/-- All facets in the first `m` directions are constant, leaving only the last two coordinate
pairs potentially nonconstant. -/
def LeadingFacesConstant {m : ℕ} (S : CubicalShell (m + 1) X x) : Prop :=
  ∀ i : Fin m,
    S.IsConstantFace i.castSucc.castSucc 0 ∧ S.IsConstantFace i.castSucc.castSucc 1

/-- The square filling relates the two concatenations formed by the last four facets. -/
theorem lastTwoFaceLoops_homotopic {m : ℕ} (S : CubicalShell (m + 1) X x)
    (h : S.LeadingFacesConstant) :
    GenLoop.Homotopic
      (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last (m + 1)))
        (S.upperFaceLoop (Fin.last m).castSucc))
      (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last m).castSucc)
        (S.upperFaceLoop (Fin.last (m + 1)))) := by
  refine ⟨{
    toFun := fun st ↦ S.map (squareSweepCube m st)
    continuous_toFun := S.map.continuous.comp (squareSweepCube m).continuous
    map_zero_left := S.squareSweepCube_zero
    map_one_left := S.squareSweepCube_one
    prop' := fun s t ht ↦ ?_ }⟩
  have hstart := (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last (m + 1)))
    (S.upperFaceLoop (Fin.last m).castSucc)).property t ht
  apply Eq.trans ?_ hstart.symm
  obtain ⟨j, hj⟩ := ht
  obtain ⟨i, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
  · rcases h i with ⟨hi0, hi1⟩
    rcases hj with hj | hj
    · exact hi0 _ (by simpa [squareSweepCube, Fin.init_def] using hj)
    · exact hi1 _ (by simpa [squareSweepCube, Fin.init_def] using hj)
  · rcases hj with hj | hj
    · apply S.codimTwo
      refine ⟨(Fin.last m).castSucc, Fin.last (m + 1),
        Fin.castSucc_ne_last (Fin.last m), Or.inl ?_, Or.inl ?_⟩
      · simp [squareSweepCube, hj]
      · simp [squareSweepCube, hj]
    · apply S.codimTwo
      refine ⟨(Fin.last m).castSucc, Fin.last (m + 1),
        Fin.castSucc_ne_last (Fin.last m), Or.inr ?_, Or.inr ?_⟩
      · simp [squareSweepCube, hj]
      · simp [squareSweepCube, hj]

/-- The additive homotopy class of a lower facet. -/
def lowerFaceClass (S : CubicalShell d X x) (i : Fin (d + 1)) :
    Additive (HomotopyGroup (Fin d) X x) :=
  Additive.ofMul (⟦S.lowerFaceLoop i⟧ : HomotopyGroup (Fin d) X x)

/-- The additive homotopy class of an upper facet. -/
def upperFaceClass (S : CubicalShell d X x) (i : Fin (d + 1)) :
    Additive (HomotopyGroup (Fin d) X x) :=
  Additive.ofMul (⟦S.upperFaceLoop i⟧ : HomotopyGroup (Fin d) X x)

theorem lowerFaceClass_eq_zero [Nonempty (Fin d)] (S : CubicalShell d X x)
    (i : Fin (d + 1)) (h : S.IsConstantFace i 0) :
    S.lowerFaceClass i = 0 := by
  rw [lowerFaceClass, S.lowerFaceLoop_eq_const i h, ← HomotopyGroup.one_def]
  rfl

/-- The four face classes around the last-coordinate square satisfy the square boundary
relation. -/
theorem lastTwoFaceClass_relation {m : ℕ} [Nontrivial (Fin (m + 1))]
    (S : CubicalShell (m + 1) X x) (h : S.LeadingFacesConstant) :
    S.upperFaceClass (Fin.last m).castSucc + S.lowerFaceClass (Fin.last (m + 1)) =
      S.upperFaceClass (Fin.last (m + 1)) + S.lowerFaceClass (Fin.last m).castSucc := by
  have hq :
      ((· * ·) : HomotopyGroup (Fin (m + 1)) X x →
          HomotopyGroup (Fin (m + 1)) X x → HomotopyGroup (Fin (m + 1)) X x)
        ⟦S.upperFaceLoop (Fin.last m).castSucc⟧ ⟦S.lowerFaceLoop (Fin.last (m + 1))⟧ =
      ((· * ·) : HomotopyGroup (Fin (m + 1)) X x →
          HomotopyGroup (Fin (m + 1)) X x → HomotopyGroup (Fin (m + 1)) X x)
        ⟦S.upperFaceLoop (Fin.last (m + 1))⟧ ⟦S.lowerFaceLoop (Fin.last m).castSucc⟧ := by
    rw [HomotopyGroup.mul_spec,
      HomotopyGroup.mul_spec]
    exact Quotient.sound (S.lastTwoFaceLoops_homotopic h)
  exact congrArg Additive.ofMul hq

end CubicalShell

end FiniteChains.TopologicalSingular
end

section
open scoped Topology Topology.Homotopy unitInterval
namespace FiniteChains.TopologicalSingular

variable {j : ℕ}

/-- The boundary of the standard `j`-simplex: the points with a vanishing coordinate. -/
def bdry (j : ℕ) : Set (stdSimplex ℝ (Fin (j + 1))) := {x | ∃ i, x.1 i = 0}

/-- The `i`-th face inclusion `|Δ^j| → |Δ^{j+1}|`, inserting a zero in slot `i`. -/
def faceMap (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) : stdSimplex ℝ (Fin (j + 2)) :=
  ⟨i.insertNth 0 x.1, by
    refine ⟨(Fin.forall_iff_succAbove i).2 ⟨?_, fun k => ?_⟩, ?_⟩
    · rw [Fin.insertNth_apply_same]
    · rw [Fin.insertNth_apply_succAbove]; exact x.2.1 k
    · rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same]
      simp only [Fin.insertNth_apply_succAbove]
      rw [zero_add, x.2.2]⟩

@[simp]
theorem faceMap_coe_same (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) :
    (faceMap i x).1 i = 0 := by
  simp [faceMap]

@[simp]
theorem faceMap_coe_succAbove (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) (k : Fin (j + 1)) :
    (faceMap i x).1 (i.succAbove k) = x.1 k := by
  simp [faceMap]


/-- The stick-breaking map from the `d`-cube to the standard `d`-simplex. -/
def stickSimplex : (d : ℕ) → C(I^Fin d, stdSimplex ℝ (Fin (d + 1)))
  | 0 => ContinuousMap.const _ (stdSimplex.vertex (0 : Fin 1))
  | d + 1 =>
      { toFun := fun t =>
          ⟨Fin.cons (1 - (t 0 : ℝ))
              (fun i => (t 0 : ℝ) * stickSimplex d (fun j => t j.succ) i), by
            constructor
            · intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · exact sub_nonneg.mpr (t 0).2.2
              · exact mul_nonneg (t 0).2.1
                  ((stickSimplex d (fun j => t j.succ)).property.1 j)
            · rw [Fin.sum_univ_succ]
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [← Finset.mul_sum, stdSimplex.sum_eq_one]
              ring⟩
        continuous_toFun := by
          apply Continuous.subtype_mk
          apply continuous_pi
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simp only [Fin.cons_zero]
            fun_prop
          · simp only [Fin.cons_succ]
            have htail : Continuous (fun t : I^Fin (d + 1) => fun k : Fin d => t k.succ) := by
              fun_prop
            have hrec : Continuous
                (fun t : I^Fin (d + 1) => stickSimplex d (fun k : Fin d => t k.succ)) :=
              (stickSimplex d).continuous.comp htail
            exact (by fun_prop : Continuous fun t : I^Fin (d + 1) => (t 0 : ℝ)).mul
              (((continuous_apply j).comp continuous_subtype_val).comp hrec) }

@[simp]
theorem stickSimplex_zero (t : I^Fin 0) :
    stickSimplex 0 t = stdSimplex.vertex (0 : Fin 1) :=
  rfl

@[simp]
theorem stickSimplex_succ_zero (d : ℕ) (t : I^Fin (d + 1)) :
    stickSimplex (d + 1) t 0 = 1 - (t 0 : ℝ) :=
  rfl

@[simp]
theorem stickSimplex_succ_succ (d : ℕ) (t : I^Fin (d + 1)) (i : Fin (d + 1)) :
    stickSimplex (d + 1) t i.succ =
      (t 0 : ℝ) * stickSimplex d (fun j => t j.succ) i :=
  rfl


theorem stickSimplex_cons_val (d : ℕ) (a : I) (t : I^Fin d) :
    (⇑(stickSimplex (d + 1) (Fin.cons a t)) : Fin (d + 2) → ℝ) =
      (Fin.cons (1 - (a : ℝ))
        (fun i => (a : ℝ) * stickSimplex d t i) : Fin (d + 2) → ℝ) := rfl

/-! ### Cubical faces -/

theorem cubeFace_zero_eq_cons {d : ℕ} (a : I) (t : I^Fin d) :
    cubeFace (0 : Fin (d + 1)) a t = (Fin.cons a t : I^Fin (d + 1)) := by simp

theorem cubeFace_succ_eq_cons {d : ℕ} (i : Fin (d + 1)) (a : I)
    (t : I^Fin (d + 1)) :
    cubeFace i.succ a t =
      (Fin.cons (t 0) (cubeFace i a (Fin.tail t)) : I^Fin (d + 2)) := by
  rw [← Fin.cons_self_tail t]
  exact Fin.insertNth_succ_cons i a (t 0) (Fin.tail t)

/-! ### Compatibility with simplex faces -/

theorem faceMap_zero_val {d : ℕ} (s : stdSimplex ℝ (Fin (d + 1))) :
    (⇑(faceMap (0 : Fin (d + 2)) s) : Fin (d + 2) → ℝ) =
      (Fin.cons (0 : ℝ) (⇑s : Fin (d + 1) → ℝ) : Fin (d + 2) → ℝ) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rfl
  · rfl

theorem faceMap_succ_val {d : ℕ} (i : Fin (d + 1))
    (s : stdSimplex ℝ (Fin (d + 1))) :
    (⇑(faceMap i.succ s) : Fin (d + 2) → ℝ) =
      (Fin.cons (s 0)
        (i.insertNth (0 : ℝ) (fun j : Fin d => s j.succ)) :
          Fin (d + 2) → ℝ) := by
  change (@Fin.insertNth (d + 1) (fun _ : Fin (d + 2) => ℝ) i.succ
      (0 : ℝ) (⇑s)) = _
  rw [← Fin.cons_self_tail (⇑s), Fin.insertNth_succ_cons]
  simp

theorem mul_insertNth_zero {d : ℕ} (i : Fin (d + 1)) (a : ℝ) (f : Fin d → ℝ) :
    (fun j : Fin (d + 1) => a *
        (@Fin.insertNth d (fun _ : Fin (d + 1) => ℝ) i (0 : ℝ) f) j) =
      @Fin.insertNth d (fun _ : Fin (d + 1) => ℝ) i (0 : ℝ)
        (fun j : Fin d => a * f j) := by
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simp
  · simp

/-- The stick-breaking map sends every upper cube face to the simplex face with the same
index. -/
theorem stickSimplex_cubeFace_one : ∀ (d : ℕ) (i : Fin (d + 1)) (t : I^Fin d),
    stickSimplex (d + 1) (cubeFace i 1 t) = faceMap i.castSucc (stickSimplex d t) := by
  intro d
  induction d with
  | zero =>
      intro i t
      have hi  := Fin.eq_zero i
      subst i
      have hinput : cubeFace (0 : Fin 1) 1 t =
          (Fin.cons 1 t) := by
        exact Fin.insertNth_zero' 1 t
      rw [hinput]
      apply stdSimplex.ext
      rw [stickSimplex_cons_val,
        show (0 : Fin 1).castSucc = 0 by rfl, faceMap_zero_val]
      norm_num
  | succ d ih =>
      intro i t
      refine Fin.cases ?_ (fun i => ?_) i
      · have hinput : cubeFace 0 1 t =
            (Fin.cons 1 t : I^Fin (d + 2)) := by
          exact Fin.insertNth_zero' 1 t
        rw [hinput]
        apply stdSimplex.ext
        rw [stickSimplex_cons_val,
          show (0 : Fin (d + 2)).castSucc = (0 : Fin (d + 3)) by rfl,
          faceMap_zero_val]
        norm_num
      · have hinput : cubeFace i.succ 1 t =
            (Fin.cons (t 0) (cubeFace i 1 (Fin.tail t)) : I^Fin (d + 2)) := by
          rw [← Fin.cons_self_tail t]
          exact Fin.insertNth_succ_cons i 1 (t 0) (Fin.tail t)
        rw [hinput]
        apply stdSimplex.ext
        rw [stickSimplex_cons_val,
          show i.succ.castSucc = i.castSucc.succ by rfl,
          faceMap_succ_val i.castSucc]
        simp only [stickSimplex_succ_zero, stickSimplex_succ_succ]
        apply congrArg (fun f : Fin (d + 2) → ℝ =>
          (Fin.cons (1 - (t 0 : ℝ)) f : Fin (d + 3) → ℝ))
        rw [ih]
        exact mul_insertNth_zero i.castSucc (t 0 : ℝ)
          (⇑(stickSimplex d (Fin.tail t)) : Fin (d + 1) → ℝ)

/-- The final lower cube face is the final simplex face. -/
theorem stickSimplex_cubeFace_last_zero : ∀ (d : ℕ) (t : I^Fin d),
    stickSimplex (d + 1) (cubeFace (Fin.last d) 0 t) =
      faceMap (Fin.last (d + 1)) (stickSimplex d t) := by
  intro d
  induction d with
  | zero =>
      intro t
      have hinput : cubeFace (Fin.last 0) 0 t = (Fin.cons 0 t : I^Fin 1) := by
        exact Fin.insertNth_zero' 0 t
      rw [hinput]
      apply stdSimplex.ext
      rw [stickSimplex_cons_val,
        show Fin.last 1 = (0 : Fin 1).succ by rfl,
        faceMap_succ_val]
      funext j
      fin_cases j <;> norm_num [stickSimplex]
  | succ d ih =>
      intro t
      have hinput : cubeFace (Fin.last (d + 1)) 0 t =
          (Fin.cons (t 0) (cubeFace (Fin.last d) 0 (Fin.tail t))) := by
        rw [← Fin.cons_self_tail t]
        exact Fin.insertNth_succ_cons (Fin.last d) 0 (t 0) (Fin.tail t)
      rw [hinput]
      apply stdSimplex.ext
      rw [stickSimplex_cons_val,
        show Fin.last (d + 2) = (Fin.last (d + 1)).succ by rfl,
        faceMap_succ_val]
      simp only [stickSimplex_succ_zero, stickSimplex_succ_succ]
      apply congrArg (fun f : Fin (d + 2) → ℝ =>
        (Fin.cons (1 - (t 0)) f : Fin (d + 3) → ℝ))
      rw [ih]
      exact mul_insertNth_zero (Fin.last (d + 1)) (t 0)
        (⇑(stickSimplex d (Fin.tail t)))

/-- On the lower face in cube coordinate `i`, stick-breaking barycentric coordinate `i+1`
vanishes. -/
theorem stickSimplex_cubeFace_zero_succ : ∀ (d : ℕ) (i : Fin (d + 1)) (t : I^Fin d),
    stickSimplex (d + 1) (cubeFace i 0 t) i.succ = 0 := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
      intro i t
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [cubeFace_zero_eq_cons]
        change (0 : ℝ) * stickSimplex (d + 1) t 0 = 0
        ring
      · rw [cubeFace_succ_eq_cons]
        change (t 0 : ℝ) *
            stickSimplex (d + 1) (cubeFace i 0 (Fin.tail t)) i.succ = 0
        rw [ih]
        ring

/-- Every lower cube face is sent into the final simplex face. -/
theorem stickSimplex_cubeFace_zero_last : ∀ (d : ℕ) (i : Fin (d + 1)) (t : I^Fin d),
    stickSimplex (d + 1) (cubeFace i 0 t) (Fin.last (d + 1)) = 0 := by
  intro d
  induction d with
  | zero =>
      intro i t
      simpa only [show i = 0 by exact Fin.eq_zero i,
        show Fin.last 1 = (0 : Fin 1).succ by rfl] using
          stickSimplex_cubeFace_zero_succ 0 (0 : Fin 1) t
  | succ d ih =>
      intro i t
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [cubeFace_zero_eq_cons]
        change 0 * stickSimplex (d + 1) t (Fin.last (d + 1)) = 0
        ring
      · rw [cubeFace_succ_eq_cons]
        change (t 0) *
            stickSimplex (d + 1) (cubeFace i 0 (Fin.tail t)) (Fin.last (d + 1)) = 0
        rw [ih]
        ring

/-- The codimension-two skeleton of a standard simplex, expressed by two distinct vanishing
barycentric coordinates. -/
def simplexCodimTwo (d : ℕ) : Set (stdSimplex ℝ (Fin (d + 1))) :=
  {z | ∃ i j, i ≠ j ∧ z i = 0 ∧ z j = 0}

/-- A simplex face applied to a boundary point lands in the codimension-two skeleton. -/
theorem faceMap_mem_simplexCodimTwo {d : ℕ} (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 1))) (hz : z ∈ bdry d) :
    faceMap i z ∈ simplexCodimTwo (d + 1) := by
  obtain ⟨j, hj⟩ := hz
  refine ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm,
    faceMap_coe_same i z, ?_⟩
  change (faceMap i z).1 (i.succAbove j) = 0
  rw [faceMap_coe_succAbove, hj]

/-- Every nonfinal lower cube face lands in the codimension-two skeleton. -/
theorem stickSimplex_cubeFace_zero_mem_codimTwo {d : ℕ} (i : Fin (d + 1))
    (hi : i ≠ Fin.last d) (t : I^Fin d) :
    stickSimplex (d + 1) (cubeFace i 0 t) ∈ simplexCodimTwo (d + 1) := by
  have hlt  := Fin.lt_last_iff_ne_last.mpr hi
  have hsucc : i.succ ≠ Fin.last (d + 1) := by
    apply ne_of_lt
    rw [show Fin.last (d + 1) = (Fin.last d).succ by rfl]
    exact Fin.succ_lt_succ_iff.mpr hlt
  exact ⟨i.succ, Fin.last (d + 1), hsucc,
    stickSimplex_cubeFace_zero_succ d i t,
    stickSimplex_cubeFace_zero_last d i t⟩

/-- Stick-breaking carries the boundary of the cube into the boundary of the simplex. -/
theorem stickSimplex_mem_bdry (d : ℕ) (t : I^Fin d)
    (ht : t ∈ Cube.boundary (Fin d)) : stickSimplex d t ∈ bdry d := by
  cases d with
  | zero =>
      obtain ⟨i, _⟩ := ht
      exact Fin.elim0 i
  | succ d =>
      obtain ⟨i, hi | hi⟩ := ht
      · have hrep : t = cubeFace i 0 (Fin.removeNth i t) := by
          calc
            t = i.insertNth (t i) (Fin.removeNth i t) :=
              (Fin.insertNth_self_removeNth i t).symm
            _ = i.insertNth 0 (Fin.removeNth i t) := by rw [hi]
            _ = cubeFace i 0 (Fin.removeNth i t) := rfl
        rw [hrep]
        exact ⟨i.succ, stickSimplex_cubeFace_zero_succ d i (Fin.removeNth i t)⟩
      · have hrep : t = cubeFace i 1 (Fin.removeNth i t) := by
          calc
            t = i.insertNth (t i) (Fin.removeNth i t) :=
              (Fin.insertNth_self_removeNth i t).symm
            _ = i.insertNth 1 (Fin.removeNth i t) := by rw [hi]
            _ = cubeFace i 1 (Fin.removeNth i t) := rfl
        rw [hrep, stickSimplex_cubeFace_one]
        exact (⟨(i.castSucc), faceMap_coe_same (i.castSucc) (stickSimplex d (Fin.removeNth i t))⟩)

/-- Stick-breaking reflects the boundary: an interior cube point has no vanishing
barycentric coordinate. -/
theorem mem_cube_boundary_of_stickSimplex_mem_bdry : ∀ (d : ℕ) (t : I^Fin d),
    stickSimplex d t ∈ bdry d → t ∈ Cube.boundary (Fin d) := by
  intro d
  induction d with
  | zero =>
      intro t ht
      obtain ⟨i, hi⟩ := ht
      have hi0  := Fin.eq_zero i
      subst i
      norm_num [stickSimplex, stdSimplex.vertex] at hi
  | succ d ih =>
      intro t ht
      obtain ⟨i, hi⟩ := ht
      cases i using Fin.cases with
      | zero =>
        change 1 - (t 0 : ℝ) = 0 at hi
        have ht0 : (t 0 : ℝ) = 1 := by linarith
        exact ⟨0, Or.inr (Subtype.ext ht0)⟩
      | succ j =>
        rcases mul_eq_zero.mp hi with ht0 | htail
        · exact ⟨0, Or.inl (Subtype.ext ht0)⟩
        · obtain ⟨k, hk⟩ := ih (fun j => t j.succ) ⟨j, htail⟩
          exact ⟨k.succ, hk⟩

/-- Stick-breaking identifies precisely the cubical and simplicial boundaries. -/
theorem stickSimplex_mem_bdry_iff (d : ℕ) (t : I^Fin d) :
    stickSimplex d t ∈ bdry d ↔ t ∈ Cube.boundary (Fin d) :=
  ⟨mem_cube_boundary_of_stickSimplex_mem_bdry d t, stickSimplex_mem_bdry d t⟩

/-- Stick-breaking is injective away from the cubical boundary. -/
theorem stickSimplex_injective_of_not_mem_boundary : ∀ (d : ℕ) (t u : I^Fin d),
    t ∉ Cube.boundary (Fin d) → u ∉ Cube.boundary (Fin d) →
      stickSimplex d t = stickSimplex d u → t = u := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
      intro t u ht hu hstick
      have hheadReal : (t 0 : ℝ) = (u 0) := by
        have hzero := congrArg (fun z : stdSimplex ℝ (Fin (d + 2)) => z 0) hstick
        simp at hzero
        linarith
      have hhead  := Subtype.ext hheadReal
      have ht0 : (t 0 : ℝ) ≠ 0 := by
        intro ht0
        exact ht ⟨0, Or.inl (Subtype.ext ht0)⟩
      have httail : (fun j : Fin d => t j.succ) ∉ Cube.boundary (Fin d) := by
        rintro ⟨j, hj⟩
        exact ht ⟨j.succ, hj⟩
      have hutail : (fun j : Fin d => u j.succ) ∉ Cube.boundary (Fin d) := by
        rintro ⟨j, hj⟩
        exact hu ⟨j.succ, hj⟩
      have htailStick : stickSimplex d (fun j => t j.succ) =
          stickSimplex d (fun j => u j.succ) := by
        apply stdSimplex.ext
        funext j
        have hsucc := congrArg (fun z : stdSimplex ℝ (Fin (d + 2)) => z j.succ) hstick
        simp at hsucc
        rw [← hheadReal] at hsucc
        exact mul_left_cancel₀ ht0 hsucc
      have htail := ih (fun j => t j.succ) (fun j => u j.succ)
        httail hutail htailStick
      change Fin.tail t = Fin.tail u at htail
      rw [← Fin.cons_self_tail t, ← Fin.cons_self_tail u, hhead, htail]

/-- Every point of the standard simplex has stick-breaking coordinates. -/
theorem stickSimplex_surjective : ∀ d : ℕ, Function.Surjective (stickSimplex d) := by
  intro d
  induction d with
  | zero =>
      intro z
      refine ⟨default, ?_⟩
      apply stdSimplex.ext
      funext i
      have hi  := Fin.eq_zero i
      subst i
      simp [stickSimplex, stdSimplex.vertex]
  | succ d ih =>
      intro z
      let a  := 1 - z.1 0
      have ha0  := sub_nonneg.mpr (stdSimplex.le_one z 0)
      have ha1 : a ≤ 1 := by
        dsimp [a]
        exact sub_le_self 1 (z.property.1 0)
      by_cases ha : a = 0
      · let t : I^Fin (d + 1) := Fin.cons 0 (fun _ => 0)
        have hz0one : z.1 0 = 1 := by
          dsimp [a] at ha
          linarith
        refine ⟨t, ?_⟩
        apply stdSimplex.ext
        funext i
        cases i using Fin.cases with
        | zero =>
            change 1 - (t 0 : ℝ) = z.1 0
            simp [t, hz0one]
        | succ j =>
            change (t 0 : ℝ) * stickSimplex d (fun k => t k.succ) j = z.1 j.succ
            have hzsum := z.property.2
            rw [Fin.sum_univ_succ] at hzsum
            change z.1 0 + ∑ k : Fin (d + 1), z.1 k.succ = 1 at hzsum
            have hzj_le : z.1 j.succ ≤ ∑ k : Fin (d + 1), z.1 k.succ :=
              Finset.single_le_sum (fun k _ => z.property.1 k.succ) (Finset.mem_univ j)
            have htailsum : ∑ k : Fin (d + 1), z.1 k.succ = 0 := by
              have htailform : ∑ k : Fin (d + 1), z.1 k.succ = 1 - z.1 0 :=
                (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hzsum)
              rw [hz0one] at htailform
              simpa using htailform
            rw [htailsum] at hzj_le
            have hzjzero : z.1 j.succ = 0 :=
              le_antisymm hzj_le (z.property.1 j.succ)
            simp [t, hzjzero]
      · let ai : I := ⟨a, ha0, ha1⟩
        let y : stdSimplex ℝ (Fin (d + 1)) :=
          ⟨fun i => z.1 i.succ / a,
            fun i => div_nonneg (z.property.1 i.succ) ha0,
            by
              have hzsum := z.property.2
              rw [Fin.sum_univ_succ] at hzsum
              change z.1 0 + ∑ i : Fin (d + 1), z.1 i.succ = 1 at hzsum
              rw [← Finset.sum_div]
              have hsum : ∑ i : Fin (d + 1), z.1 i.succ = a := by
                have htailform : ∑ i : Fin (d + 1), z.1 i.succ = 1 - z.1 0 :=
                  (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hzsum)
                simpa [a] using htailform
              rw [hsum, div_self ha]⟩
        obtain ⟨u, hu⟩ := ih y
        refine ⟨Fin.cons ai u, ?_⟩
        apply stdSimplex.ext
        funext i
        cases i using Fin.cases with
        | zero =>
            change 1 - ai = z.1 0
            dsimp [ai, a]
            ring
        | succ j =>
            change ai * stickSimplex d u j = z.1 j.succ
            rw [hu]
            change a * (z.1 j.succ / a) = z.1 j.succ
            exact mul_div_cancel₀ _ ha

/-- Every parameterized simplex face takes the cubical boundary into the codimension-two
skeleton of the ambient simplex. -/
theorem faceMap_stickSimplex_mem_codimTwo {d : ℕ} (i : Fin (d + 2))
    (t : I^Fin d) (ht : t ∈ Cube.boundary (Fin d)) :
    faceMap i (stickSimplex d t) ∈ simplexCodimTwo (d + 1) :=
  faceMap_mem_simplexCodimTwo i _ (stickSimplex_mem_bdry d t ht)

/-- A parameterized cubical face, restricted to its own boundary, lands in the codimension-two
skeleton of the simplex. -/
theorem stickSimplex_cubeFace_mem_codimTwo {d : ℕ} (i : Fin (d + 1)) (a : I)
    (ha : a = 0 ∨ a = 1) (t : I^Fin d) (ht : t ∈ Cube.boundary (Fin d)) :
    stickSimplex (d + 1) (cubeFace i a t) ∈ simplexCodimTwo (d + 1) := by grind [stickSimplex_cubeFace_last_zero, stickSimplex_cubeFace_one, faceMap_stickSimplex_mem_codimTwo, stickSimplex_cubeFace_zero_mem_codimTwo, stickSimplex, simplexCodimTwo]

end FiniteChains.TopologicalSingular
end

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {Y : Type u} [TopologicalSpace Y] {n : ℕ}

/-- Coordinatewise straight-line interpolation stays in the standard simplex. -/
def simplexLinearHomotopy (f g : C(Y, Domain n)) : f.Homotopy g where
  toFun w := ⟨fun i => (1 - (w.1 : ℝ)) * (f w.2).val i + (w.1 : ℝ) * (g w.2).val i, by
    constructor
    · intro i
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr w.1.property.2) ((f w.2).property.1 i))
        (mul_nonneg w.1.property.1 ((g w.2).property.1 i))
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        (f w.2).property.2, (g w.2).property.2]
      ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact ((continuous_const.sub continuous_fst.subtype_val).mul
      ((continuous_apply i).comp (f.continuous.comp continuous_snd).subtype_val)).add
      (continuous_fst.subtype_val.mul
        ((continuous_apply i).comp (g.continuous.comp continuous_snd).subtype_val))
  map_zero_left z := by simp
  map_one_left z := by simp


def simplexLinearHomotopyRel (f g : C(Y, Domain n)) (S : Set Y)
    (h : ∀ z ∈ S, f z = g z) : ContinuousMap.HomotopyRel f g S where
  toHomotopy := simplexLinearHomotopy f g
  prop' t z hz := (by
    apply Subtype.ext
    funext i
    change (1 - (t : ℝ)) * (f z).val i + (t : ℝ) * (g z).val i = (f z).val i
    rw [(h z hz)]
    ring)

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem simplex_face_eq_faceMap {n : ℕ} (i : Fin (n + 2)) (z : Domain n) :
    stdSimplex.map (SimplexCategory.δ i) z = faceMap i z := by
  apply Subtype.ext
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · exact (simplex_face_coordinate_zero i z).trans (faceMap_coe_same i z).symm
  · exact (simplex_face_coordinate_succAbove i z k).trans (faceMap_coe_succAbove i z k).symm


/-- The triangulation and stick-coordinate parametrizations have exactly the
same boundary, so their comparison requires no orientation convention. -/
theorem squareToTriangle_eq_stickSimplex_on_boundary (z : Fin 2 → I)
    (hz : z ∈ Cube.boundary (Fin 2)) : squareToTriangle z = stickSimplex 2 z := by
  obtain ⟨i, hi⟩ := hz
  fin_cases i <;> rcases hi with hi | hi
  all_goals
    dsimp at hi
    apply Subtype.ext
    rw [(show (stickSimplex 2 z).val =
      ![1 - (z 0 : ℝ), (z 0) * (1 - (z 1)), (z 0) * (z 1)] by
      funext i
      fin_cases i
      · rfl
      · rfl
      · change (z 0) * ((z 1) * (stdSimplex.vertex 0 : Domain 0).val 0) = _
        simp)]
    funext j
    fin_cases j
    all_goals
      simp [squareToTriangle, hi, (z 0).property.1, (z 0).property.2,
        (z 1).property.1, (z 1).property.2,
        sub_nonneg.mpr (z 1).property.2, sub_nonpos.mpr (z 0).property.2]

def basedTriangleStickSquare (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) :
    GenLoop (Fin 2) X x :=
  ⟨tau.comp (stickSimplex 2), by
    intro z hz
    obtain ⟨i, hi⟩ := stickSimplex_mem_bdry 2 z hz
    exact basedTriangle_eq_of_zero_coordinate tau h _ i hi⟩

theorem basedTriangleSquare_homotopic_stick (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) :
    GenLoop.Homotopic (basedTriangleSquare tau h) (basedTriangleStickSquare tau h) :=
  ⟨(simplexLinearHomotopyRel squareToTriangle (stickSimplex 2) (Cube.boundary (Fin 2))
    squareToTriangle_eq_stickSimplex_on_boundary).compContinuousMap tau⟩

theorem basedTriangleStickSquare_pi2_eq (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) :
    (Quotient.mk _ (basedTriangleStickSquare tau h) : HomotopyGroup (Fin 2) X x) =
      Quotient.mk _ (basedTriangleSquare tau h) :=
  (Quotient.sound (basedTriangleSquare_homotopic_stick tau h)).symm

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

/-- The two orders of inserting the missing coordinates give the same face. -/
theorem simplex_double_face_swap (i : Fin (n + 3)) (k : Fin (n + 2)) (q : Domain n) :
    stdSimplex.map (SimplexCategory.δ i) (stdSimplex.map (SimplexCategory.δ k) q) =
      stdSimplex.map (SimplexCategory.δ (i.succAbove k))
        (stdSimplex.map (SimplexCategory.δ (k.predAbove i)) q) := by
  change stdSimplex.map i.succAbove (stdSimplex.map k.succAbove q) =
    stdSimplex.map (i.succAbove k).succAbove (stdSimplex.map (k.predAbove i).succAbove q)
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  have he : i.succAbove ∘ k.succAbove =
      (i.succAbove k).succAbove ∘ (k.predAbove i).succAbove := by
    funext a
    exact (Fin.succAbove_succAbove_succAbove_predAbove i k a).symm
  rw [he]

theorem singular_double_face_swap (tau : Simplex X (n + 2))
    (i : Fin (n + 3)) (k : Fin (n + 2)) :
    face k (face i tau) = face (k.predAbove i) (face (i.succAbove k) tau) := by
  apply ContinuousMap.ext
  intro q
  simp only [face_apply, simplex_double_face_swap i k q]

/-- A point in two different faces comes from one common codimension-two face,
with a single parameter in the lower-dimensional simplex. -/
theorem simplex_face_intersection_factor (i j : Fin (n + 3)) (hij : i ≠ j)
    (z w : Domain (n + 1))
    (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
    ∃ (k l : Fin (n + 2)) (q : Domain n),
      z = stdSimplex.map (SimplexCategory.δ k) q ∧
      w = stdSimplex.map (SimplexCategory.δ l) q ∧
      ∀ a : Domain n,
        stdSimplex.map (SimplexCategory.δ i) (stdSimplex.map (SimplexCategory.δ k) a) =
          stdSimplex.map (SimplexCategory.δ j) (stdSimplex.map (SimplexCategory.δ l) a) := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
  have hz : z.val k = 0 := by
    rw [← simplex_face_coordinate_succAbove i z k, hk, h]
    exact simplex_face_coordinate_zero j w
  obtain ⟨q, hq⟩ := domain_zero_coordinate_face z k hz
  have he a := simplex_double_face_swap i k a
  rw [hk] at he
  refine ⟨k, k.predAbove i, q, hq.symm, ?_, he⟩
  apply simplex_face_injective j
  rw [← h, ← hq]
  exact he q

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {j : ℕ}

theorem faceMap_injective (i : Fin (j + 2)) : Function.Injective (faceMap (j := j) i) := by
  intro x y h
  refine Subtype.ext (funext fun k => ?_)
  have := congrArg (fun z : stdSimplex ℝ (Fin (j + 2)) => z.1 (i.succAbove k)) h
  simpa using this

/-- The inverse of the `i`-th face inclusion, deleting the `i`-th coordinate. -/
def dropMap (i : Fin (j + 2)) {x : stdSimplex ℝ (Fin (j + 2))} (hx : x.1 i = 0) :
    stdSimplex ℝ (Fin (j + 1)) :=
  ⟨Fin.removeNth i x.1, fun k => x.2.1 _, by
    have h := x.2.2
    rw [Fin.sum_univ_succAbove _ i, hx, zero_add] at h
    exact h⟩

theorem faceMap_dropMap (i : Fin (j + 2)) {x : stdSimplex ℝ (Fin (j + 2))} (hx : x.1 i = 0) :
    faceMap i (dropMap i hx) = x := by
  refine Subtype.ext (funext fun k => ?_)
  refine Fin.succAboveCases i ?_ (fun k => ?_) k
  · simp_all
  · rw [faceMap_coe_succAbove]
    rfl

end FiniteChains.TopologicalSingular

section
open scoped Topology Topology.Homotopy unitInterval
namespace FiniteChains.TopologicalSingular

variable {d : ℕ}

/-- The least barycentric coordinate away from `i`. -/
def simplexHornMin (i : Fin (d + 2)) (z : stdSimplex ℝ (Fin (d + 2))) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun j : Fin (d + 1) ↦ z.1 (i.succAbove j)

theorem simplexHornMin_nonneg (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) : 0 ≤ simplexHornMin i z := by
  apply Finset.le_inf' Finset.univ_nonempty
  intro j hj
  exact z.2.1 _

theorem simplexHornMin_le (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) (j : Fin (d + 1)) :
    simplexHornMin i z ≤ z.1 (i.succAbove j) :=
  Finset.inf'_le _ (Finset.mem_univ j)

theorem exists_simplexHornMin_eq (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) :
    ∃ j : Fin (d + 1), simplexHornMin i z = z.1 (i.succAbove j) := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf'
    Finset.univ_nonempty
    (fun j ↦ z.1 (i.succAbove j))
  exact ⟨j, hj⟩

/-- The least coordinate away from the chosen face varies continuously. -/
theorem continuous_simplexHornMin (i : Fin (d + 2)) :
    Continuous (simplexHornMin i) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun j _ ↦ (continuous_apply (i.succAbove j)).comp continuous_subtype_val)

/-- Barycentric coordinates of the retraction onto the horn opposite face `i`. -/
def simplexHornRetractCoords (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) : Fin (d + 2) → ℝ :=
  i.insertNth (z.1 i + (d + 1 : ℝ) * simplexHornMin i z)
    (fun j ↦ z.1 (i.succAbove j) - simplexHornMin i z)

@[simp]
theorem simplexHornRetractCoords_same (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) :
    simplexHornRetractCoords i z i = z.1 i + (d + 1 : ℝ) * simplexHornMin i z := by
  simp [simplexHornRetractCoords]

@[simp]
theorem simplexHornRetractCoords_succAbove (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) (j : Fin (d + 1)) :
    simplexHornRetractCoords i z (i.succAbove j) =
      z.1 (i.succAbove j) - simplexHornMin i z := by
  simp [simplexHornRetractCoords]

theorem simplexHornRetractCoords_nonneg (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) (k : Fin (d + 2)) :
    0 ≤ simplexHornRetractCoords i z k := by
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) k
  · rw [simplexHornRetractCoords_same]
    have hd : 0 ≤ (d : ℝ) + 1 := by positivity
    exact add_nonneg (z.2.1 i)
      (mul_nonneg hd (simplexHornMin_nonneg i z))
  · rw [simplexHornRetractCoords_succAbove]
    exact sub_nonneg.mpr (simplexHornMin_le i z j)


/-- The explicit retraction of a simplex onto the horn obtained by deleting face `i`. -/
def simplexHornRetract (i : Fin (d + 2)) :
    C(stdSimplex ℝ (Fin (d + 2)), stdSimplex ℝ (Fin (d + 2))) where
  toFun z := ⟨simplexHornRetractCoords i z,
    simplexHornRetractCoords_nonneg i z, (by
      rw [Fin.sum_univ_succAbove _ i]
      simp
      have hz := z.2.2
      rw [Fin.sum_univ_succAbove _ i] at hz
      norm_num at hz ⊢
      linarith)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    refine Fin.succAboveCases i ?_ (fun j ↦ ?_) k
    · simp only [simplexHornRetractCoords_same]
      apply Continuous.add
      · exact (continuous_apply i).comp continuous_subtype_val
      · exact continuous_const.mul (continuous_simplexHornMin i)
    · simp only [simplexHornRetractCoords_succAbove]
      exact ((continuous_apply (i.succAbove j)).comp continuous_subtype_val).sub
        (continuous_simplexHornMin i)

@[simp]
theorem simplexHornRetract_apply_coe (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) (k : Fin (d + 2)) :
    (simplexHornRetract i z).1 k = simplexHornRetractCoords i z k :=
  rfl

/-- The horn opposite `i`, described as the points having a zero coordinate away from `i`. -/
def simplexHorn (i : Fin (d + 2)) : Set (stdSimplex ℝ (Fin (d + 2))) :=
  {z | ∃ j : Fin (d + 1), z.1 (i.succAbove j) = 0}

theorem simplexHornMin_eq_zero_of_mem (i : Fin (d + 2))
    {z : stdSimplex ℝ (Fin (d + 2))} (hz : z ∈ simplexHorn i) :
    simplexHornMin i z = 0 := by
  obtain ⟨j, hj⟩ := hz
  apply le_antisymm
  · simpa [hj] using simplexHornMin_le i z j
  · exact simplexHornMin_nonneg i z

theorem simplexHornRetract_eq_self_of_mem (i : Fin (d + 2))
    {z : stdSimplex ℝ (Fin (d + 2))} (hz : z ∈ simplexHorn i) :
    simplexHornRetract i z = z := by
  apply Subtype.ext
  funext k
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) k
  · simp [simplexHornRetractCoords, simplexHornMin_eq_zero_of_mem i hz]
  · simp [simplexHornRetractCoords, simplexHornMin_eq_zero_of_mem i hz]

end FiniteChains.TopologicalSingular
end

section
open scoped Topology
namespace FiniteChains.TopologicalSingular

variable {d : ℕ} {X : Type} [TopologicalSpace X]

/-- The closed region of the ambient simplex on which coordinate `j`, away from the missing
face `i`, realizes the least such coordinate. -/
def simplexHornFillRegion (i : Fin (d + 2)) (j : Fin (d + 1)) :
    Set (stdSimplex ℝ (Fin (d + 2))) :=
  {z | simplexHornMin i z = z.1 (i.succAbove j)}


/-- The minimum regions cover the entire ambient simplex. -/
theorem exists_mem_simplexHornFillRegion (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) :
    ∃ j : Fin (d + 1), z ∈ simplexHornFillRegion i j :=
  exists_simplexHornMin_eq i z

/-- On fill region `j`, the horn retraction lands on face `i.succAbove j`. -/
theorem simplexHornRetract_coord_eq_zero_of_mem_fillRegion
    (i : Fin (d + 2)) (j : Fin (d + 1))
    (z : stdSimplex ℝ (Fin (d + 2))) (hz : z ∈ simplexHornFillRegion i j) :
    (simplexHornRetract i z).1 (i.succAbove j) = 0 := by
  rw [simplexHornRetract_apply_coe, simplexHornRetractCoords_succAbove]
  exact sub_eq_zero.mpr hz.symm

/-- Coordinates on the remaining face obtained after applying the horn retraction. -/
def simplexHornFillFaceMap (i : Fin (d + 2)) (j : Fin (d + 1)) :
    C({z // z ∈ simplexHornFillRegion i j}, stdSimplex ℝ (Fin (d + 1))) where
  toFun z := dropMap (i.succAbove j)
    (simplexHornRetract_coord_eq_zero_of_mem_fillRegion i j z.1 z.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    change Continuous fun z : {z // z ∈ simplexHornFillRegion i j} ↦
      (simplexHornRetract i z.1).1 ((i.succAbove j).succAbove k)
    exact ((continuous_apply ((i.succAbove j).succAbove k)).comp continuous_subtype_val).comp
      ((simplexHornRetract i).continuous.comp continuous_subtype_val)

/-- The local face coordinates reconstruct the horn retraction. -/
theorem faceMap_simplexHornFillFaceMap (i : Fin (d + 2)) (j : Fin (d + 1))
    (z : {z // z ∈ simplexHornFillRegion i j}) :
    faceMap (i.succAbove j) (simplexHornFillFaceMap i j z) = simplexHornRetract i z.1 :=
  faceMap_dropMap (i.succAbove j)
    (simplexHornRetract_coord_eq_zero_of_mem_fillRegion i j z.1 z.2)

/-- A canonical index of a minimum region containing an ambient simplex point. -/
def simplexHornFillIdx (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) : Fin (d + 1) :=
  (exists_mem_simplexHornFillRegion i z).choose

theorem simplexHornFillIdx_spec (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) :
    z ∈ simplexHornFillRegion i (simplexHornFillIdx i z) :=
  (exists_mem_simplexHornFillRegion i z).choose_spec

/-- The pointwise horn filler obtained by selecting a minimum-coordinate face. -/
def simplexHornFillFun (i : Fin (d + 2))
    (g : Fin (d + 1) → C(stdSimplex ℝ (Fin (d + 1)), X))
    (z : stdSimplex ℝ (Fin (d + 2))) : X :=
  g (simplexHornFillIdx i z)
    (simplexHornFillFaceMap i (simplexHornFillIdx i z)
      ⟨z, simplexHornFillIdx_spec i z⟩)

/-- Compatibility of maps prescribed on all faces other than `i`. -/
def SimplexHornFaceCompatible (i : Fin (d + 2))
    (g : Fin (d + 1) → C(stdSimplex ℝ (Fin (d + 1)), X)) : Prop :=
  ∀ (j k : Fin (d + 1)) (y z : stdSimplex ℝ (Fin (d + 1))),
    faceMap (i.succAbove j) y = faceMap (i.succAbove k) z → g j y = g k z

/-- The selected-index definition of the filler agrees with any minimum region containing the
point. -/
theorem simplexHornFillFun_eq (i : Fin (d + 2))
    (g : Fin (d + 1) → C(stdSimplex ℝ (Fin (d + 1)), X))
    (hg : SimplexHornFaceCompatible i g) (z : stdSimplex ℝ (Fin (d + 2)))
    (j : Fin (d + 1)) (hj : z ∈ simplexHornFillRegion i j) :
    simplexHornFillFun i g z = g j (simplexHornFillFaceMap i j ⟨z, hj⟩) := by
  apply hg
  rw [faceMap_simplexHornFillFaceMap, faceMap_simplexHornFillFaceMap]

/-- Compatible maps on the faces of a topological horn extend continuously over the full
simplex. -/
def simplexHornFiller (i : Fin (d + 2))
    (g : Fin (d + 1) → C(stdSimplex ℝ (Fin (d + 1)), X))
    (hg : SimplexHornFaceCompatible i g) :
    C(stdSimplex ℝ (Fin (d + 2)), X) where
  toFun := simplexHornFillFun i g
  continuous_toFun := by
    let S : Fin (d + 1) → Set (stdSimplex ℝ (Fin (d + 2))) :=
      fun j ↦ simplexHornFillRegion i j
    refine (locallyFinite_of_finite S).continuous ?_ (fun j ↦ ?_) (fun j ↦ ?_)
    · refine Set.eq_univ_of_forall fun z ↦ ?_
      obtain ⟨j, hj⟩ := exists_mem_simplexHornFillRegion i z
      exact Set.mem_iUnion.2 ⟨j, hj⟩
    · exact (by
      apply isClosed_eq
      · exact continuous_simplexHornMin i
      · exact (continuous_apply (i.succAbove j)).comp continuous_subtype_val)
    · rw [continuousOn_iff_continuous_restrict]
      have heq : (S j).domRestrict (simplexHornFillFun i g) =
          fun z : S j ↦ g j (simplexHornFillFaceMap i j z) := by
        funext z
        exact simplexHornFillFun_eq i g hg z.1 j z.2
      rw [heq]
      exact (g j).continuous.comp (simplexHornFillFaceMap i j).continuous

/-- On every prescribed face, the topological horn filler recovers the given map. -/
theorem simplexHornFiller_face (i : Fin (d + 2))
    (g : Fin (d + 1) → C(stdSimplex ℝ (Fin (d + 1)), X))
    (hg : SimplexHornFaceCompatible i g) (j : Fin (d + 1))
    (y : stdSimplex ℝ (Fin (d + 1))) :
    simplexHornFiller i g hg (faceMap (i.succAbove j) y) = g j y := by
  have hmem : faceMap (i.succAbove j) y ∈ simplexHorn i :=
    ⟨j, faceMap_coe_same (i.succAbove j) y⟩
  have hregion : faceMap (i.succAbove j) y ∈ simplexHornFillRegion i j := by
    change simplexHornMin i (faceMap (i.succAbove j) y) =
      (faceMap (i.succAbove j) y).1 (i.succAbove j)
    rw [simplexHornMin_eq_zero_of_mem i hmem, faceMap_coe_same]
  rw [show simplexHornFiller i g hg (faceMap (i.succAbove j) y) =
      simplexHornFillFun i g (faceMap (i.succAbove j) y) from rfl,
    simplexHornFillFun_eq i g hg _ j hregion]
  apply congrArg (g j)
  apply faceMap_injective (i.succAbove j)
  rw [faceMap_simplexHornFillFaceMap,
    simplexHornRetract_eq_self_of_mem i hmem]


end FiniteChains.TopologicalSingular
end

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] {n : ℕ}

/-- Fill a horn using the actual singular-simplex and face operators of this
project. Agreement is required only where the prescribed faces intersect. -/
theorem singular_horn_filler_exists (i : Fin (n + 2))
    (g : ∀ j : Fin (n + 2), j ≠ i → Simplex X n)
    (hg : ∀ (j k : Fin (n + 2)) (hj : j ≠ i) (hk : k ≠ i)
      (z w : Domain n),
      stdSimplex.map (SimplexCategory.δ j) z = stdSimplex.map (SimplexCategory.δ k) w →
      g j hj z = g k hk w) :
    ∃ tau : Simplex X (n + 1), ∀ (j : Fin (n + 2)) (hj : j ≠ i), face j tau = g j hj := by
  let faces  :=
    fun k => g (i.succAbove k) (Fin.succAbove_ne i k)
  have hfaces : SimplexHornFaceCompatible i faces := by
    intro j k z w h
    apply hg (i.succAbove j) (i.succAbove k)
    simpa only [simplex_face_eq_faceMap] using h
  let tau  := simplexHornFiller i faces hfaces
  refine ⟨tau, ?_⟩
  intro j hj
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
  apply ContinuousMap.ext
  intro z
  change tau (stdSimplex.map (SimplexCategory.δ (i.succAbove k)) z) = faces k z
  rw [simplex_face_eq_faceMap]
  exact simplexHornFiller_face i faces hfaces k z

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

def singularDegeneracy (i : Fin (n + 1)) (tau : Simplex X n) :
    Simplex X (n + 1) := (simplices X).σ i tau

@[simp] theorem singular_face_const (i : Fin (n + 2)) (x : X) :
    face i (ContinuousMap.const (Domain (n + 1)) x) =
      ContinuousMap.const (Domain n) x := rfl

@[simp] theorem singular_degeneracy_const (i : Fin (n + 1)) (x : X) :
    singularDegeneracy i (ContinuousMap.const (Domain n) x) =
      ContinuousMap.const (Domain (n + 1)) x := rfl

@[simp] theorem singular_face_degeneracy_self (i : Fin (n + 1)) (tau : Simplex X n) :
    face i.castSucc (singularDegeneracy i tau) = tau :=
  CategoryTheory.ConcreteCategory.congr_hom ((simplices X).δ_comp_σ_self (i := i)) tau

@[simp] theorem singular_face_degeneracy_succ (i : Fin (n + 1)) (tau : Simplex X n) :
    face i.succ (singularDegeneracy i tau) = tau :=
  CategoryTheory.ConcreteCategory.congr_hom ((simplices X).δ_comp_σ_succ (i := i)) tau

theorem singular_face_degeneracy_le (i : Fin (n + 2)) (j : Fin (n + 1))
    (h : i ≤ j.castSucc) (tau : Simplex X (n + 1)) :
    face i.castSucc (singularDegeneracy j.succ tau) =
      singularDegeneracy j (face i tau) :=
  CategoryTheory.ConcreteCategory.congr_hom ((simplices X).δ_comp_σ_of_le h) tau

theorem singular_face_degeneracy_gt (i : Fin (n + 2)) (j : Fin (n + 1))
    (h : j.castSucc < i) (tau : Simplex X (n + 1)) :
    face i.succ (singularDegeneracy j.castSucc tau) =
      singularDegeneracy j (face i tau) :=
  CategoryTheory.ConcreteCategory.congr_hom ((simplices X).δ_comp_σ_of_gt h) tau

/-- Algebraic face compatibility suffices for a genuine topological horn filler. -/
theorem singular_horn_filler_of_face_compatible {Y : Type} [TopologicalSpace Y]
    (i : Fin (n + 3)) (g : ∀ j : Fin (n + 3), j ≠ i → Simplex Y (n + 1))
    (hg : ∀ (j : Fin (n + 3)) (k : Fin (n + 2))
      (hj : j ≠ i) (hk : j.succAbove k ≠ i),
      face k (g j hj) = face (k.predAbove j) (g (j.succAbove k) hk)) :
    ∃ tau : Simplex Y (n + 2), ∀ (j : Fin (n + 3)) (hj : j ≠ i),
      face j tau = g j hj := by
  apply singular_horn_filler_exists i g
  intro j k hj hk z w h
  by_cases hjk : j = k
  · subst k
    have hzw := simplex_face_injective j h
    subst w
    rfl
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq (Ne.symm hjk)
  have hz : z.val a = 0 := by
    rw [← simplex_face_coordinate_succAbove j z a, ha, h]
    exact simplex_face_coordinate_zero k w
  obtain ⟨q, hq⟩ := domain_zero_coordinate_face z a hz
  have hw : w = stdSimplex.map (SimplexCategory.δ (a.predAbove j)) q := by
    apply simplex_face_injective k
    rw [← h, ← hq]
    simpa only [ha] using simplex_double_face_swap j a q
  have hka : j.succAbove a ≠ i := by simpa only [ha] using hk
  have he := congrArg (fun t : Simplex Y n => t q) (hg j a hj hka)
  simpa only [face_apply, ha, hq, hw] using he

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem basedTetrahedron_eq_of_two_zero_coordinates (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x)
    (z : Domain 3) (i j : Fin 4) (hij : i ≠ j) (hi : z.val i = 0) (hj : z.val j = 0) :
    tau z = x := by
  obtain ⟨w, hw⟩ := domain_zero_coordinate_face z i hi
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
  have hz : w.val k = 0 := by
    rw [← simplex_face_coordinate_succAbove i w k, hk, hw, hj]
  obtain ⟨q, hq⟩ := domain_zero_coordinate_face w k hz
  have he := congrArg (fun f : Simplex X 1 => f q) (hedge i k)
  simpa only [face_apply, hq, hw, ContinuousMap.const_apply] using he

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem stickSimplex_mem_codimTwo_of_mem_cubeCodimTwo {d : ℕ} (t : Fin d → I)
    (ht : t ∈ cubeCodimTwo d) : stickSimplex d t ∈ simplexCodimTwo d := by
  obtain ⟨i, j, hij, hi, hj⟩ := ht
  cases d with
  | zero => omega
  | succ m =>
      obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
      let v  := Fin.removeNth i t
      have hv : v ∈ Cube.boundary (Fin m) := by
        refine ⟨k, ?_⟩
        change t (i.succAbove k) = 0 ∨ t (i.succAbove k) = 1
        rw [hk]
        exact hj
      have hrep  :=
        (Fin.insertNth_self_removeNth i t).symm
      rw [hrep]
      exact stickSimplex_cubeFace_mem_codimTwo i (t i) hi v hv

def tetrahedronStickShell (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x) : CubicalShell 2 X x where
  map := tau.comp (stickSimplex 3)
  codimTwo z hz := by
    obtain ⟨i, j, hij, hi, hj⟩ := stickSimplex_mem_codimTwo_of_mem_cubeCodimTwo z hz
    exact basedTetrahedron_eq_of_two_zero_coordinates tau hedge _ i j hij hi hj



theorem tetrahedronStickShell_lower_constant (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x)
    (i : Fin 3) (hi : i ≠ Fin.last 2) :
    (tetrahedronStickShell tau hedge).IsConstantFace i 0 := by
  intro t ht
  have hrep : t = cubeFace i 0 (Fin.removeNth i t) := by
    rw [← ht]
    exact (Fin.insertNth_self_removeNth i t).symm
  rw [hrep]
  obtain ⟨j, k, hjk, hj, hk⟩ :=
    stickSimplex_cubeFace_zero_mem_codimTwo i hi (Fin.removeNth i t)
  exact basedTetrahedron_eq_of_two_zero_coordinates tau hedge _ j k hjk hj hk


def tetrahedronFacePi2Class (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x)
    (i : Fin 4) : Additive (HomotopyGroup (Fin 2) X x) :=
  Additive.ofMul (Quotient.mk _ (basedTriangleSquare (face i tau) (hedge i)))

theorem tetrahedronStickShell_upperFaceClass (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x) (i : Fin 3) :
    (tetrahedronStickShell tau hedge).upperFaceClass i =
      tetrahedronFacePi2Class tau hedge i.castSucc := by
  unfold CubicalShell.upperFaceClass tetrahedronFacePi2Class
  rw [(show (tetrahedronStickShell tau hedge).upperFaceLoop i =
      basedTriangleStickSquare (face i.castSucc tau) (hedge i.castSucc) by
    apply GenLoop.ext
    intro z
    change tau (stickSimplex 3 (cubeFace i 1 z)) =
      tau (stdSimplex.map (SimplexCategory.δ i.castSucc) (stickSimplex 2 z))
    rw [stickSimplex_cubeFace_one, simplex_face_eq_faceMap]), basedTriangleStickSquare_pi2_eq]


/-- The genuine pi2 multiplication relation for a tetrahedron whose first
face is constant. This is the final-index simplicial multiplication case. -/
theorem tetrahedronStickShell_face_relation (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x)
    (hzero : face 0 tau = ContinuousMap.const (Domain 2) x) :
    tetrahedronFacePi2Class tau hedge 1 + tetrahedronFacePi2Class tau hedge 3 =
      tetrahedronFacePi2Class tau hedge 2 := by
  let S := tetrahedronStickShell tau hedge
  have hleading : S.LeadingFacesConstant := by
    intro i
    have hi  := Fin.eq_zero i
    subst i
    exact ⟨tetrahedronStickShell_lower_constant tau hedge 0 (by decide),
      (by
        intro t ht
        have hrep : t = cubeFace 0 1 (Fin.removeNth 0 t) := by
          rw [← ht]
          exact (Fin.insertNth_self_removeNth 0 t).symm
        rw [hrep]
        change tau (stickSimplex 3 (cubeFace 0 1 (Fin.removeNth 0 t))) = x
        rw [stickSimplex_cubeFace_one, ← simplex_face_eq_faceMap]
        exact congrArg (fun f : Simplex X 2 => f (stickSimplex 2 (Fin.removeNth 0 t))) hzero)⟩
  have h := S.lastTwoFaceClass_relation hleading
  change S.upperFaceClass 1 + S.lowerFaceClass 2 = S.upperFaceClass 2 + S.lowerFaceClass 1 at h
  have hlower  :=
    S.lowerFaceClass_eq_zero 1 (tetrahedronStickShell_lower_constant tau hedge 1 (by decide))
  rw [hlower, add_zero] at h
  simpa only [S, tetrahedronStickShell_upperFaceClass,
    (show (tetrahedronStickShell tau hedge).lowerFaceClass 2 =
      tetrahedronFacePi2Class tau hedge 3 by
      unfold CubicalShell.lowerFaceClass tetrahedronFacePi2Class
      rw [(show (tetrahedronStickShell tau hedge).lowerFaceLoop 2 =
      basedTriangleStickSquare (face 3 tau) (hedge 3) by
        apply GenLoop.ext
        intro z
        change tau (stickSimplex 3 (cubeFace (Fin.last 2) 0 z)) =
          tau (stdSimplex.map (SimplexCategory.δ 3) (stickSimplex 2 z))
        rw [stickSimplex_cubeFace_last_zero, simplex_face_eq_faceMap]
        rfl), basedTriangleStickSquare_pi2_eq]),
    show (1 : Fin 3).castSucc = 1 by decide,
    show (2 : Fin 3).castSucc = 2 by decide] using h

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] {x : X}

/-- A singular triangle whose three edges are the constant edge at `x`. -/
structure PointedSingularTriangle (X : Type) [TopologicalSpace X] (x : X) where
  map : Simplex X 2
  based : ∀ i : Fin 3, face i map = ContinuousMap.const (Domain 1) x

namespace PointedSingularTriangle

def pi2 (a : PointedSingularTriangle X x) :
    Additive (HomotopyGroup (Fin 2) X x) :=
  Additive.ofMul (Quotient.mk _ (basedTriangleSquare a.map a.based))

def constant (x : X) : PointedSingularTriangle X x :=
  ⟨ContinuousMap.const (Domain 2) x, fun _ => rfl⟩

@[simp] theorem constant_pi2 (x : X) : (constant x).pi2 = 0 := rfl

theorem pi2_congr (a b : PointedSingularTriangle X x) (h : a.map = b.map) :
    a.pi2 = b.pi2 := by
  cases a
  cases b
  cases h
  rfl

theorem degeneracy_zero_faces (a : PointedSingularTriangle X x) (i : Fin 4) :
    face i (singularDegeneracy 0 a.map) =
      ![a.map, a.map, (constant x).map, (constant x).map] i := by
  fin_cases i
  · exact singular_face_degeneracy_self 0 a.map
  · exact singular_face_degeneracy_succ 0 a.map
  · simpa [a.based, singular_degeneracy_const, constant, Fin.succ, Fin.castSucc, Fin.castAdd] using
      singular_face_degeneracy_gt 1 0 (by decide) a.map
  · simpa [a.based, singular_degeneracy_const, constant, Fin.succ, Fin.castSucc, Fin.castAdd] using
      singular_face_degeneracy_gt 2 0 (by decide) a.map

theorem degeneracy_one_faces (a : PointedSingularTriangle X x) (i : Fin 4) :
    face i (singularDegeneracy 1 a.map) =
      ![(constant x).map, a.map, a.map, (constant x).map] i := by
  fin_cases i
  · simpa [a.based, singular_degeneracy_const, constant, Fin.succ, Fin.castSucc, Fin.castAdd] using
      singular_face_degeneracy_le 0 0 (by decide) a.map
  · exact singular_face_degeneracy_self 1 a.map
  · exact singular_face_degeneracy_succ 1 a.map
  · simpa [a.based, singular_degeneracy_const, constant, Fin.succ, Fin.castSucc, Fin.castAdd] using
      singular_face_degeneracy_gt 2 1 (by decide) a.map

theorem degeneracy_two_faces (a : PointedSingularTriangle X x) (i : Fin 4) :
    face i (singularDegeneracy 2 a.map) =
      ![(constant x).map, (constant x).map, a.map, a.map] i := by
  fin_cases i
  · simpa [a.based, singular_degeneracy_const, constant, Fin.succ, Fin.castSucc, Fin.castAdd] using
      singular_face_degeneracy_le 0 1 (by decide) a.map
  · simpa [a.based, singular_degeneracy_const, constant, Fin.succ, Fin.castSucc, Fin.castAdd] using
      singular_face_degeneracy_le 1 1 (by decide) a.map
  · exact singular_face_degeneracy_self 2 a.map
  · exact singular_face_degeneracy_succ 2 a.map

theorem tetrahedron_face_pi2 (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x)
    (i : Fin 4) (a : PointedSingularTriangle X x) (ha : face i tau = a.map) :
    tetrahedronFacePi2Class tau hedge i = a.pi2 := by
  change (PointedSingularTriangle.mk (face i tau) (hedge i)).pi2 = a.pi2
  exact pi2_congr _ _ ha

/-- Multiplication obtained from the cubical shell when the first face is constant. -/
theorem first_face_constant_relation (a b c : PointedSingularTriangle X x)
    (tau : Simplex X 3)
    (hfaces : ∀ i : Fin 4,
      face i tau = ![(constant x).map, a.map, b.map, c.map] i) :
    a.pi2 + c.pi2 = b.pi2 := by
  have hedge : ∀ i j,
      face j (face i tau) = ContinuousMap.const (Domain 1) x := by
    intro i j
    rw [hfaces]
    fin_cases i <;> simp [a.based, b.based, c.based, constant]
  have h := tetrahedronStickShell_face_relation tau hedge (hfaces 0)
  rw [tetrahedron_face_pi2 tau hedge 1 a (hfaces 1),
    tetrahedron_face_pi2 tau hedge 3 c (hfaces 3),
    tetrahedron_face_pi2 tau hedge 2 b (hfaces 2)] at h
  exact h

end PointedSingularTriangle
end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] {x : X}

/-- Fill three pointed triangles and verify that every edge of the filler,
including the edges of its missing triangular face, is constant. -/
theorem pointed_triangle_horn_exists (i : Fin 4)
    (a : Fin 4 → PointedSingularTriangle X x) :
    ∃ tau : Simplex X 3,
      (∀ (j : Fin 4) (_hj : j ≠ i), face j tau = (a j).map) ∧
      (∀ (j : Fin 4) (k : Fin 3),
        face k (face j tau) = ContinuousMap.const (Domain 1) x) := by
  obtain ⟨tau, htau⟩ := singular_horn_filler_of_face_compatible i
    (fun j _ => (a j).map) (by
      intro j k hj hk
      rw [(a j).based, (a (j.succAbove k)).based])
  refine ⟨tau, htau, ?_⟩
  intro j k
  by_cases hj : j = i
  · subst j
    rw [singular_double_face_swap tau i k,
      htau (i.succAbove k) (Fin.succAbove_ne i k), (a (i.succAbove k)).based]
  · rw [htau j hj, (a j).based]

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X]

/-- The missing face of a four-dimensional horn, with its four faces computed.
This is an existence theorem for actual continuous singular tetrahedra. -/
theorem singular_four_horn_missing_one (T0 T2 T3 T4 : Simplex X 3)
    (h02 : face 1 T0 = face 0 T2)
    (h03 : face 2 T0 = face 0 T3)
    (h04 : face 3 T0 = face 0 T4)
    (h23 : face 2 T2 = face 2 T3)
    (h24 : face 3 T2 = face 2 T4)
    (h34 : face 3 T3 = face 3 T4) :
    ∃ W : Simplex X 3,
      face 0 W = face 0 T0 ∧ face 1 W = face 1 T2 ∧
      face 2 W = face 1 T3 ∧ face 3 W = face 1 T4 := by
  let g  := ![T0, T0, T2, T3, T4]
  have hg : ∀ j k (hj : j ≠ 1) (hk : j.succAbove k ≠ 1),
      face k (g j) = face (k.predAbove j) (g (j.succAbove k)) := by
    intro j k hj hk
    fin_cases j <;> fin_cases k <;>
      simp_all [g, Fin.succAbove, Fin.predAbove] <;> rfl
  obtain ⟨S, hS⟩ := singular_horn_filler_of_face_compatible 1
    (fun j _ => g j) hg
  refine ⟨face 1 S, ?_, ?_, ?_, ?_⟩
  · have h := singular_double_face_swap S 1 0
    simpa [g, show (1 : Fin 5).succAbove 0 = 0 from rfl,
      show (0 : Fin 4).predAbove 1 = 0 from rfl, hS 0 (by decide)] using h
  · have h := singular_double_face_swap S 1 1
    simpa [g, show (1 : Fin 5).succAbove 1 = 2 from rfl,
      show (1 : Fin 4).predAbove 1 = 1 from rfl, hS 2 (by decide)] using h
  · have h := singular_double_face_swap S 1 2
    simpa [g, show (1 : Fin 5).succAbove 2 = 3 from rfl,
      show (2 : Fin 4).predAbove 1 = 1 from rfl, hS 3 (by decide)] using h
  · have h := singular_double_face_swap S 1 3
    simpa [g, show (1 : Fin 5).succAbove 3 = 4 from rfl,
      show (3 : Fin 4).predAbove 1 = 1 from rfl, hS 4 (by decide)] using h

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular.PointedSingularTriangle
variable {X : Type} [TopologicalSpace X] {x : X}

/-- Move the constant face from the last index to the first using a genuine
four-dimensional horn filling, and apply the cubical multiplication relation. -/
theorem last_face_constant_relation (a b c : PointedSingularTriangle X x)
    (tau : Simplex X 3)
    (hfaces : ∀ i : Fin 4,
      face i tau = ![a.map, b.map, c.map, (constant x).map] i) :
    a.pi2 + c.pi2 = b.pi2 := by
  obtain ⟨W, h0, h1, h2, h3⟩ := singular_four_horn_missing_one
    (singularDegeneracy 2 a.map) (singularDegeneracy 1 c.map)
    tau (singularDegeneracy 0 a.map)
    (by simp [degeneracy_two_faces, degeneracy_one_faces])
    (by simp [degeneracy_two_faces, hfaces])
    (by simp [degeneracy_two_faces, degeneracy_zero_faces])
    (by simp [degeneracy_one_faces, hfaces])
    (by simp [degeneracy_one_faces, degeneracy_zero_faces])
    (by simp [hfaces, degeneracy_zero_faces])
  have hW : ∀ i : Fin 4,
      face i W = ![(constant x).map, c.map, b.map, a.map] i := by
    intro i
    fin_cases i <;> simp_all [degeneracy_two_faces, degeneracy_one_faces,
      degeneracy_zero_faces]
  have h := first_face_constant_relation c b a W hW
  exact (add_comm a.pi2 c.pi2).trans h

end FiniteChains.TopologicalSingular.PointedSingularTriangle

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] {x : X}

namespace PointedSingularTriangle

/-- The four actual pi2 classes on the boundary of a based-edge tetrahedron
satisfy the alternating relation, without any assumption that a face is constant. -/
theorem tetrahedron_relation (a b c d : PointedSingularTriangle X x)
    (tau : Simplex X 3)
    (hfaces : ∀ i : Fin 4, face i tau = ![a.map, b.map, c.map, d.map] i) :
    a.pi2 + c.pi2 = b.pi2 + d.pi2 := by
  obtain ⟨U, hU, hedgeU⟩ := pointed_triangle_horn_exists 1
    ![constant x, constant x, c, d]
  let e : PointedSingularTriangle X x := ⟨face 1 U, hedgeU 1⟩
  have hUfaces : ∀ i : Fin 4,
      face i U = ![(constant x).map, e.map, c.map, d.map] i := by
    intro i
    fin_cases i
    · simp_all
    · rfl
    · simp_all
    · simp_all
  have he  := first_face_constant_relation e c d U hUfaces
  obtain ⟨W, h0, h1, h2, h3⟩ := singular_four_horn_missing_one
    (singularDegeneracy 0 a.map) tau U (singularDegeneracy 2 d.map)
    (by simp [degeneracy_zero_faces, hfaces])
    (by simp [degeneracy_zero_faces, hUfaces])
    (by simp [degeneracy_zero_faces, degeneracy_two_faces])
    (by simp [hfaces, hUfaces])
    (by simp [hfaces, degeneracy_two_faces])
    (by simp [hUfaces, degeneracy_two_faces])
  have hWfaces : ∀ i : Fin 4,
      face i W = ![a.map, b.map, e.map, (constant x).map] i := by
    intro i
    fin_cases i <;> simp_all [degeneracy_zero_faces, degeneracy_two_faces]
  have hab  := last_face_constant_relation a b e W hWfaces
  calc
    a.pi2 + c.pi2 = a.pi2 + (e.pi2 + d.pi2) := by rw [he]
    _ = (a.pi2 + e.pi2) + d.pi2 := (add_assoc _ _ _).symm
    _ = b.pi2 + d.pi2 := by rw [hab]

end PointedSingularTriangle


/-- The alternating boundary of every singular tetrahedron with constant edges
vanishes in the genuine second homotopy group. -/
theorem tetrahedron_pi2_alternating_sum_eq_zero (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x) :
    ∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • tetrahedronFacePi2Class tau hedge i = 0 := by
  have hsum {A : Type} [AddCommGroup A] (f : Fin 4 → A) :
      ∑ i : Fin 4, (-1) ^ (i : ℕ) • f i = (f 0 + f 2) - (f 1 + f 3) := by
    norm_num [Fin.sum_univ_four]
    abel
  rw [hsum (tetrahedronFacePi2Class tau hedge),
    (show tetrahedronFacePi2Class tau hedge 0 + tetrahedronFacePi2Class tau hedge 2 =
      tetrahedronFacePi2Class tau hedge 1 + tetrahedronFacePi2Class tau hedge 3 by
      let a : Fin 4 → PointedSingularTriangle X x := fun i => ⟨face i tau, hedge i⟩
      exact PointedSingularTriangle.tetrahedron_relation (a 0) (a 1) (a 2) (a 3) tau
        (by intro i; fin_cases i <;> rfl)), sub_self]

end FiniteChains.TopologicalSingular

namespace FiniteChains.SingularPrism
open TopologicalSingular
open scoped unitInterval
universe u v w
variable {A : Type u} {B : Type v} {X : Type w}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
  {f g : C(A, X)} {f' g' : C(B, X)}

/-- A prism depends only on the homotopy restricted to its input simplex. -/
theorem prism_single_congr (H : f.Homotopy g) (K : f'.Homotopy g')
    {n : ℕ} (tau : Simplex A n) (eta : Simplex B n)
    (h : ∀ (t : I) (z : Domain n), H (t, tau z) = K (t, eta z)) (r : ℤ) :
    prism H n (Finsupp.single tau r) = prism K n (Finsupp.single eta r) := by
  have he i : simplex H tau i = simplex K eta i := by
    apply ContinuousMap.ext
    intro z
    exact h (prismMap i z).1 (prismMap i z).2
  rw [prism_single, prism_single]
  simp only [he]

end FiniteChains.SingularPrism

namespace FiniteChains.TopologicalSingular
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X]

def simplexHomotopyPrism {n : ℕ} {f g : Simplex X n} (H : f.Homotopy g) :
    Chain X (n + 1) :=
  SingularPrism.prism H n (Finsupp.single (ContinuousMap.id (Domain n)) 1)

def homotopyFamilyPrism (n : ℕ) (g : Simplex X n → Simplex X n)
    (H : ∀ tau : Simplex X n, tau.Homotopy (g tau)) : Chain X n →ₗ[ℤ] Chain X (n + 1) :=
  Finsupp.linearCombination ℤ (fun tau => simplexHomotopyPrism (H tau))

theorem homotopyFamilyPrism_single (n : ℕ) (g : Simplex X n → Simplex X n)
    (H : ∀ tau : Simplex X n, tau.Homotopy (g tau)) (tau : Simplex X n) (r : ℤ) :
    homotopyFamilyPrism n g H (Finsupp.single tau r) = r • simplexHomotopyPrism (H tau) :=
  Finsupp.linearCombination_single ℤ r tau

def simplexFamilyMap (n : ℕ) (g : Simplex X n → Simplex X n) :
    Chain X n →ₗ[ℤ] Chain X n := Finsupp.lmapDomain ℤ ℤ g

theorem simplexFamilyMap_single (n : ℕ) (g : Simplex X n → Simplex X n)
    (tau : Simplex X n) (r : ℤ) : simplexFamilyMap n g (Finsupp.single tau r) =
      Finsupp.single (g tau) r := Finsupp.mapDomain_single

variable (n : ℕ) (lo : Simplex X n → Simplex X n)
  (hi : Simplex X (n + 1) → Simplex X (n + 1))
  (L : ∀ tau : Simplex X n, tau.Homotopy (lo tau))
  (H : ∀ tau : Simplex X (n + 1), tau.Homotopy (hi tau))
  (compat : ∀ (tau : Simplex X (n + 1)) (i : Fin (n + 2)) (t : I) (z : Domain n),
    H tau (t, stdSimplex.map (SimplexCategory.δ i) z) = L (face i tau) (t, z))

include compat



/-- The prism formula remains valid when each singular simplex has its own
homotopy, provided those homotopies agree on every face. -/
theorem coherentPrism_identity (c : Chain X (n + 1)) :
    boundary (n + 1) (homotopyFamilyPrism (n + 1) hi H c) +
      homotopyFamilyPrism n lo L (boundary n c) = simplexFamilyMap (n + 1) hi c - c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp
    linear_combination (norm := abel) ha + hb
  | single tau r =>
    have hr : Finsupp.single tau r = r • Finsupp.single tau 1 := by simp
    rw [hr]
    simpa only [map_smul, homotopyFamilyPrism_single, one_smul, simplexFamilyMap_single,
      smul_add, smul_sub] using
      congrArg (fun b : Chain X (n + 1) => r • b) (show boundary (n + 1) (simplexHomotopyPrism (H tau)) +
      homotopyFamilyPrism n lo L (boundary n (Finsupp.single tau 1)) =
        Finsupp.single (hi tau) 1 - Finsupp.single tau 1 by
        have he := SingularPrism.prism_identity_succ_single (H tau) n
          (ContinuousMap.id (Domain (n + 1))) 1
        rw [(show SingularPrism.prism (H tau) n
      (boundary n (Finsupp.single (ContinuousMap.id (Domain (n + 1))) 1)) =
        homotopyFamilyPrism n lo L (boundary n (Finsupp.single tau 1)) by
          simp only [boundary_single, map_sum, map_zsmul, homotopyFamilyPrism_single, one_smul]
          apply Finset.sum_congr rfl
          intro i _
          apply congrArg (fun c : Chain X (n + 1) => (-1) ^ i.val • c)
          exact SingularPrism.prism_single_congr (H tau) (L (face i tau))
            (face i (ContinuousMap.id (Domain (n + 1)))) (ContinuousMap.id (Domain n))
            (compat tau i) 1)] at he
        simpa only [simplexHomotopyPrism, map_single, simplexMap, ContinuousMap.comp_id] using he)

theorem coherentPrism_cycle_difference_bounds (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    simplexFamilyMap (n + 1) hi c - c ∈ LinearMap.range (boundary (n + 1)) := by
  refine ⟨homotopyFamilyPrism (n + 1) hi H c, ?_⟩
  simpa only [hc, map_zero, add_zero] using coherentPrism_identity n lo hi L H compat c

theorem coherentPrism_preserves_cycles (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    boundary n (simplexFamilyMap (n + 1) hi c) = 0 := by
  obtain ⟨b, hb⟩ := coherentPrism_cycle_difference_bounds n lo hi L H compat c hc
  have he := boundary_boundary n b
  simp_all

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped Topology
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

def normalizedTriangleChain (x : X) : Chain X 2 →ₗ[ℤ] Chain X 2 :=
  simplexFamilyMap 2 (normalizedTriangle x)

theorem normalizedTriangleChain_single (x : X) (tau : Simplex X 2) (r : ℤ) :
    normalizedTriangleChain x (Finsupp.single tau r) = Finsupp.single (normalizedTriangle x tau) r :=
  simplexFamilyMap_single 2 (normalizedTriangle x) tau r


theorem normalizedTriangleChain_cycle (x : X) (c : Chain X 2) (hc : boundary 1 c = 0) :
    boundary 1 (normalizedTriangleChain x c) = 0 :=
  coherentPrism_preserves_cycles 1 (fun _ => ContinuousMap.const (Domain 1) x)
    (normalizedTriangle x) (normalizedEdgeHomotopy x) (normalizedTriangleHomotopy x)
    (normalizedTriangleHomotopy_face x) c hc

def normalizedCycleMap (x : X) : Chain X 2 →ₗ[ℤ] LinearMap.ker (boundary (X := X) 1) :=
  Finsupp.linearCombination ℤ (fun tau =>
    ⟨basedTriangleCycle (normalizedTriangle x tau) x,
      basedTriangleCycle_boundary _ (normalizedTriangle_face x tau)⟩)


def constantTriangleFromEdge (x : X) : Chain X 1 →ₗ[ℤ] Chain X 2 :=
  Finsupp.linearCombination ℤ (fun _ => Finsupp.single (ContinuousMap.const (Domain 2) x) 1)

omit [SimplyConnectedSpace X] in
theorem constantTriangleFromEdge_single (x : X) (tau : Simplex X 1) (r : ℤ) :
    constantTriangleFromEdge x (Finsupp.single tau r) = Finsupp.single (ContinuousMap.const (Domain 2) x) r := by
  simp [constantTriangleFromEdge, Finsupp.smul_single]


/-- For a cycle, the constant-triangle correction has zero total coefficient.
The resulting chain is a linear combination of based triangle cycles. -/

theorem normalizedCycleMap_class {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) (c : Chain X 2) (hc : boundary 1 c = 0) :
    singularCycleClass 1 (normalizedCycleMap x c).val (normalizedCycleMap x c).property =
      singularCycleClass 1 c hc := by
  apply (singularCycleClass_eq_iff 1 _ _ _ _).mpr
  rw [(show (normalizedCycleMap x c).val = normalizedTriangleChain x c by
    have he : (LinearMap.ker (boundary 1)).subtype.comp (normalizedCycleMap x) =
        normalizedTriangleChain x - (constantTriangleFromEdge x).comp
          ((boundary 1).comp (normalizedTriangleChain x)) := by
      apply Finsupp.lhom_ext
      intro tau r
      change (normalizedCycleMap x (Finsupp.single tau r)).val =
        normalizedTriangleChain x (Finsupp.single tau r) -
          constantTriangleFromEdge x (boundary 1 (normalizedTriangleChain x (Finsupp.single tau r)))
      rw [(show (normalizedCycleMap x (Finsupp.single tau r)).val =
      r • basedTriangleCycle (normalizedTriangle x tau) x by
        rw [normalizedCycleMap, Finsupp.linearCombination_single]
        rfl), normalizedTriangleChain_single, (show boundary 1 (Finsupp.single (normalizedTriangle x tau) r) =
      Finsupp.single (ContinuousMap.const (Domain 1) x) r by
        rw [boundary_two_single, normalizedTriangle_face, normalizedTriangle_face, normalizedTriangle_face]
        abel),
        constantTriangleFromEdge_single]
      simp [basedTriangleCycle, smul_sub, Finsupp.smul_single]
    have hp := DFunLike.congr_fun he c
    change (normalizedCycleMap x c).val = normalizedTriangleChain x c -
      constantTriangleFromEdge x (boundary 1 (normalizedTriangleChain x c)) at hp
    rwa [normalizedTriangleChain_cycle x c hc, map_zero, sub_zero] at hp)]
  exact (coherentPrism_cycle_difference_bounds 1 (fun _ => ContinuousMap.const (Domain 1) x)
    (normalizedTriangle x) (normalizedEdgeHomotopy x) (normalizedTriangleHomotopy x)
    (normalizedTriangleHomotopy_face x) c hc)

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

variable (lo : Simplex X n → Simplex X n)
  (hi : Simplex X (n + 1) → Simplex X (n + 1))
  (L : ∀ tau : Simplex X n, tau.Homotopy (lo tau))
  (H : ∀ tau : Simplex X (n + 1), tau.Homotopy (hi tau))
  (compat : ∀ (tau : Simplex X (n + 1)) (i : Fin (n + 2)) (t : I) (z : Domain n),
    H tau (t, stdSimplex.map (SimplexCategory.δ i) z) = L (face i tau) (t, z))

include compat

/-- Facewise homotopies that agree with one fixed lower-dimensional family
agree on all intersections, including higher-codimension intersections. -/
theorem compatibleFaceHomotopies_coherent (tau : Simplex X (n + 2))
    (i j : Fin (n + 3)) (t : I) (z w : Domain (n + 1))
    (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
    H (face i tau) (t, z) = H (face j tau) (t, w) := by
  by_cases hij : i = j
  · subst j
    rw [simplex_face_injective i h]
  · obtain ⟨k, l, q, hz, hw, he⟩ := simplex_face_intersection_factor i j hij z w h
    have hf : face k (face i tau) = face l (face j tau) := by
      apply ContinuousMap.ext
      intro a
      simp only [face_apply, he a]
    rw [hz, hw, compat, compat, hf]

/-- A coherent family through dimension `n+1` extends over every simplex of
dimension `n+2`, while preserving the chosen homotopies on its faces exactly. -/
theorem compatibleSimplexHomotopyExtension_exists (tau : Simplex X (n + 2)) :
    ∃ g : Simplex X (n + 2), ∃ F : tau.Homotopy g,
      ∀ (i : Fin (n + 3)) (t : I) (z : Domain (n + 1)),
        F (t, stdSimplex.map (SimplexCategory.δ i) z) = H (face i tau) (t, z) :=
  simplex_face_homotopy_extension tau (fun i => (H (face i tau)).toContinuousMap)
    (compatibleFaceHomotopies_coherent lo hi L H compat tau)
    (fun i z => (H (face i tau)).apply_zero z)

end FiniteChains.TopologicalSingular

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.TopologicalSingular
open CategoryTheory
universe u


theorem shortComplexCycleClass_surjective (S : ShortComplex (ModuleCat.{u} ℤ))
    (q : S.homology) : ∃ (c : S.X₂) (hc : S.g c = 0), shortComplexCycleClass S c hc = q := by
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance q
  have hc  := congrArg (fun f => f y) S.iCycles_g
  refine ⟨S.iCycles y, hc, ?_⟩
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  rw [shortComplexCycleClass_i, ← hy]
  exact (congrArg (fun f => f y) S.homology_π_ι).symm

variable {X : Type u} [TopologicalSpace X]


/-- Taking a homology class is linear on the actual kernel of the boundary. -/
def singularCycleClassLinear (n : ℕ) :
    LinearMap.ker (boundary (X := X) n) →ₗ[ℤ] (complex X).homology (n + 1) where
  toFun c := singularCycleClass n c.val c.property
  map_add' c d := singularCycleClass_add n c.val d.val c.property d.property
  map_smul' r c := by
    exact (show singularCycleClass n (r • (c.val)) (by rw [map_smul, (c.property), smul_zero]) =
      r • singularCycleClass n (c.val) (c.property) by
      simpa only [singularCycleClass, int_smul_eq_zsmul] using
        (by
          apply (ModuleCat.mono_iff_injective ((complex X).sc (n + 1)).homologyι).mp inferInstance
          simp only [map_zsmul, shortComplexCycleClass_i])).trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ ((complex X).homology (n + 1))) r _).symm

theorem singularCycleClass_representative (n : ℕ) (q : (complex X).homology (n + 1)) :
    ∃ (c : Chain X (n + 1)) (hc : boundary n c = 0), singularCycleClass n c hc = q := by
  obtain ⟨c, hc, hq⟩ := shortComplexCycleClass_surjective ((complex X).sc (n + 1)) q
  have hz : boundary n c = 0 := by
    change (complex X).d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) c = 0 at hc
    rw [ChainComplex.next_nat_succ, complex_d] at hc
    exact hc
  exact ⟨c, hz, hq⟩

end FiniteChains.TopologicalSingular
end

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology
open scoped Topology
variable {X : Type} [TopologicalSpace X]

def pi2CycleClassAddHom (x : X) :
    Additive (HomotopyGroup (Fin 2) X x) →+ (complex X).homology 2 := {
    toFun := fun a => pi2CycleClass x a.toMul
    map_zero' := pi2CycleClass_one x
    map_add' := fun a b => pi2CycleClass_mul x a.toMul b.toMul }

def pi2CycleClassLinear (x : X) :
    Additive (HomotopyGroup (Fin 2) X x) →ₗ[ℤ] (complex X).homology 2 where
  toFun := pi2CycleClassAddHom x
  map_add' := (pi2CycleClassAddHom x).map_add
  map_smul' r a := by
    exact (map_zsmul (pi2CycleClassAddHom x) r a).trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ ((complex X).homology 2)) r _).symm

variable [SimplyConnectedSpace X]

/-- A finite integral chain is sent to the sum of actual based squares
representing its normalized triangles. -/
def normalizedPi2Chain (x : X) :
    Chain X 2 →ₗ[ℤ] Additive (HomotopyGroup (Fin 2) X x) :=
  Finsupp.linearCombination ℤ (fun tau => Additive.ofMul
    (Quotient.mk _ (basedTriangleSquare (normalizedTriangle x tau) (normalizedTriangle_face x tau))))



theorem pi2CycleClass_surjective (x : X) : Function.Surjective (pi2CycleClass x) := by
  intro q
  obtain ⟨c, hc, hq⟩ := singularCycleClass_representative 1 q
  exact ⟨(normalizedPi2Chain x c).toMul, (show pi2CycleClass x (normalizedPi2Chain x c).toMul = singularCycleClass 1 c hc by
    have he := DFunLike.congr_fun (show (pi2CycleClassLinear x).comp (normalizedPi2Chain x) =
      (singularCycleClassLinear 1).comp (normalizedCycleMap x) by
      apply Finsupp.lhom_ext
      intro tau r
      simp only [LinearMap.comp_apply, normalizedPi2Chain, normalizedCycleMap,
        Finsupp.linearCombination_single]
      rw [(pi2CycleClassLinear x).map_smul, (singularCycleClassLinear 1).map_smul]
      apply congrArg (fun b : (complex X).homology 2 =>
        (inferInstance : Module ℤ ((complex X).homology 2)).smul r b)
      change pi2CycleClass x
        (Quotient.mk _ (basedTriangleSquare (normalizedTriangle x tau) (normalizedTriangle_face x tau))) =
          singularCycleClass 1 (basedTriangleCycle (normalizedTriangle x tau) x)
            (basedTriangleCycle_boundary _ (normalizedTriangle_face x tau))
      simp only [pi2CycleClass_mk, squareCycle_basedTriangleSquare]) c
    exact he.trans (normalizedCycleMap_class x c hc)).trans hq⟩

/-- Surjectivity of the genuine degree-two Hurewicz homomorphism, with the
actual Mathlib integral singular homology as codomain. -/
theorem singularHurewicz2_surjective (x : X) : Function.Surjective (singularHurewicz2 x) := by
  intro q
  obtain ⟨h, hh⟩ := (ModuleCat.epi_iff_surjective (homologyMathlibIso (TopCat.of X) 2).hom).mp
    inferInstance q
  obtain ⟨a, ha⟩ := pi2CycleClass_surjective x h
  refine ⟨a, ?_⟩
  change (homologyMathlibIso (TopCat.of X) 2).hom (pi2CycleClass x a) = q
  rw [ha, hh]


end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {X : Type} [TopologicalSpace X] {x : X}


/-- The only identifications made by stick coordinates occur on the boundary,
where a based cubical map is constant. -/
theorem genLoop_constant_on_stick_fiber (d : ℕ) (p : GenLoop (Fin d) X x)
    (t u : Fin d → I) (h : stickSimplex d t = stickSimplex d u) : p t = p u := by
  have hbd : t ∈ Cube.boundary (Fin d) ↔ u ∈ Cube.boundary (Fin d) := by
    rw [← stickSimplex_mem_bdry_iff, ← stickSimplex_mem_bdry_iff, h]
  by_cases ht : t ∈ Cube.boundary (Fin d)
  · rw [GenLoop.boundary p t ht, GenLoop.boundary p u (hbd.mp ht)]
  · exact congrArg p (stickSimplex_injective_of_not_mem_boundary d t u ht
      (fun hu => ht (hbd.mpr hu)) h)

/-- Every actual based square factors continuously through the stick-coordinate
triangle, exactly rather than merely up to free homotopy. -/


theorem pointed_triangle_pi2_surjective :
    Function.Surjective (PointedSingularTriangle.pi2 (X := X) (x := x)) := by
  intro q
  obtain ⟨p, hp⟩ := Quotient.exists_rep q.toMul
  obtain ⟨a, ha⟩ := (show ∃ a : PointedSingularTriangle X x,
      a.pi2 = Additive.ofMul (Quotient.mk _ p) by
    obtain ⟨a, ha⟩ := (show ∃ a : PointedSingularTriangle X x, basedTriangleStickSquare a.map a.based = p by
      let f  := fun z => p (stickSimplex_surjective 2 z).choose
      have hf t : f (stickSimplex 2 t) = p t :=
        genLoop_constant_on_stick_fiber 2 p _ t
          (stickSimplex_surjective 2 (stickSimplex 2 t)).choose_spec
      have hc  := (Topology.IsQuotientMap.of_surjective_continuous (stickSimplex_surjective 2)
    (stickSimplex 2).continuous).continuous_iff.mpr (by
        have he : f ∘ stickSimplex 2 = p := funext hf
        rw [he]
        exact p.val.continuous)
      let tau : Simplex X 2 := ⟨f, hc⟩
      have hbased : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x := by
        intro i
        apply ContinuousMap.ext
        intro z
        apply GenLoop.boundary p
        apply (stickSimplex_mem_bdry_iff 2 _).mp
        rw [(stickSimplex_surjective 2 (stdSimplex.map (SimplexCategory.δ i) z)).choose_spec]
        exact ⟨i, simplex_face_coordinate_zero i z⟩
      refine ⟨⟨tau, hbased⟩, ?_⟩
      apply GenLoop.ext
      exact hf)
    refine ⟨a, ?_⟩
    have h := basedTriangleStickSquare_pi2_eq a.map a.based
    rw [ha] at h
    exact congrArg Additive.ofMul h.symm)
  exact ⟨a, ha.trans (congrArg Additive.ofMul hp)⟩

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- Choose paths to the basepoint, choosing the constant path at the basepoint. -/
def stationaryPath (x a : X) : Path a x := by
  classical
  exact if h : a = x then h.symm ▸ Path.refl x else PathConnectedSpace.somePath a x

@[simp] theorem stationaryPath_self (x : X) : stationaryPath x x = Path.refl x := by
  simp [stationaryPath]

def stationaryVertexPath (x a : X) : Path a x :=
  (stationaryPath x a).trans (Path.refl x)

@[simp] theorem stationaryVertexPath_self (x : X) (t : I) :
    stationaryVertexPath x x t = x := by simp_all [stationaryVertexPath, stationaryPath_self, Path.trans_apply]

def stationaryVertexHomotopy (x : X) (tau : Simplex X 0) :
    tau.Homotopy (ContinuousMap.const (Domain 0) x) where
  toFun w := stationaryPath x (tau (stdSimplex.vertex 0)) w.1
  continuous_toFun := (stationaryPath _ _).continuous.comp continuous_fst
  map_zero_left z := by
    rw [Path.source]
    apply congrArg tau
    apply Subtype.ext
    funext i
    have hz := z.property.2
    simpa [stdSimplex.vertex, show i = 0 by omega] using hz.symm
  map_one_left _ := Path.target _

theorem stationaryVertexHomotopy_apply (x : X) (tau : Simplex X 0) (t : I) (z : Domain 0) :
    stationaryVertexHomotopy x tau (t, z) = stationaryPath x (tau z) t := by
  have hz : stdSimplex.vertex 0 = z :=
    by
      apply Subtype.ext
      funext i
      have hz := z.property.2
      simpa [stdSimplex.vertex, show i = 0 by omega] using hz.symm
  change stationaryPath x (tau (stdSimplex.vertex 0)) t = _
  rw [hz]


/-- Coherent edge contractions can be chosen stationary on the constant edge. -/
theorem stationaryEdgeHomotopy_exists (x : X) (tau : Simplex X 1) :
    ∃ F : tau.Homotopy (ContinuousMap.const (Domain 1) x),
      (∀ (t : I) (z : Domain 1), z ∈ simplexBoundary 1 →
        F (t, z) = stationaryVertexPath x (tau z) t) ∧
      (tau = ContinuousMap.const (Domain 1) x → ∀ (t : I) (z : Domain 1), F (t, z) = x) := by
  classical
  by_cases htau : tau = ContinuousMap.const (Domain 1) x
  · subst tau
    refine ⟨ContinuousMap.Homotopy.refl _, ?_, ?_⟩
    · intro t z _
      exact (stationaryVertexPath_self x t).symm
    · intro _ t z
      rfl
  obtain ⟨g, F, hF⟩ := (show ∃ g : Simplex X 1, ∃ F : tau.Homotopy g,
      ∀ t z, z ∈ simplexBoundary 1 →
        F (t, z) = stationaryPath x (tau z) t by
    obtain ⟨g, F, hF⟩ := simplex_face_homotopy_extension tau
      (fun i => (stationaryVertexHomotopy x (face i tau)).toContinuousMap)
      (by
        intro i j t z w h
        change stationaryVertexHomotopy x (face i tau) (t, z) =
          stationaryVertexHomotopy x (face j tau) (t, w)
        simp only [stationaryVertexHomotopy_apply, face_apply]
        exact congrArg (fun a : X => stationaryPath x a t) (congrArg tau h))
      (fun i z => (stationaryVertexHomotopy x (face i tau)).apply_zero z)
    refine ⟨g, F, ?_⟩
    intro t z hz
    obtain ⟨i, hi⟩ := hz
    obtain ⟨w, hw⟩ := domain_zero_coordinate_face z i hi
    rw [← hw, hF]
    exact stationaryVertexHomotopy_apply x (face i tau) t w)
  have hg i : g (stdSimplex.vertex i) = x := by
    have h := hF 1 (stdSimplex.vertex i) (simplexOne_vertex_mem_boundary i)
    rw [F.apply_one, Path.target] at h
    exact h
  obtain ⟨G⟩ := singularEdge_nullhomotopic x g (hg 0) (hg 1)
  refine ⟨F.trans G.toHomotopy, ?_, ?_⟩
  · intro t z hz
    rw [ContinuousMap.Homotopy.trans_apply, stationaryVertexPath, Path.trans_apply]
    split_ifs
    · exact hF _ z hz
    · exact G.eq_snd _ hz
  · simp_all

def stationaryEdgeHomotopy (x : X) (tau : Simplex X 1) :
    tau.Homotopy (ContinuousMap.const (Domain 1) x) :=
  (stationaryEdgeHomotopy_exists x tau).choose

theorem stationaryEdgeHomotopy_boundary (x : X) (tau : Simplex X 1) (t : I)
    (z : Domain 1) (hz : z ∈ simplexBoundary 1) :
    stationaryEdgeHomotopy x tau (t, z) = stationaryVertexPath x (tau z) t :=
  (stationaryEdgeHomotopy_exists x tau).choose_spec.1 t z hz

@[simp] theorem stationaryEdgeHomotopy_constant (x : X) (t : I) (z : Domain 1) :
    stationaryEdgeHomotopy x (ContinuousMap.const (Domain 1) x) (t, z) = x :=
  (stationaryEdgeHomotopy_exists x (ContinuousMap.const (Domain 1) x)).choose_spec.2 rfl t z

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem stationaryEdgeHomotopies_coherent (x : X) (tau : Simplex X 2)
    (i j : Fin 3) (t : I) (z w : Domain 1)
    (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
    stationaryEdgeHomotopy x (face i tau) (t, z) =
      stationaryEdgeHomotopy x (face j tau) (t, w) := by grind [simplex_face_injective, stationaryEdgeHomotopy_boundary, face_apply, simplex_face_intersection_boundary]

/-- Normalize coherently, choosing the identity homotopy whenever the input
triangle already has constant edges. -/
theorem stationaryTriangle_exists (x : X) (tau : Simplex X 2) :
    ∃ g : Simplex X 2, ∃ F : tau.Homotopy g,
      (∀ (i : Fin 3) (t : I) (z : Domain 1),
        F (t, stdSimplex.map (SimplexCategory.δ i) z) =
          stationaryEdgeHomotopy x (face i tau) (t, z)) ∧
      ((∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) → g = tau) := by
  by_cases htau : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x
  · refine ⟨tau, ContinuousMap.Homotopy.refl tau, ?_, fun _ => rfl⟩
    intro i t z
    rw [htau i, stationaryEdgeHomotopy_constant]
    exact congrArg (fun f : Simplex X 1 => f z) (htau i)
  · obtain ⟨g, F, hF⟩ := simplex_face_homotopy_extension tau
      (fun i => (stationaryEdgeHomotopy x (face i tau)).toContinuousMap)
      (stationaryEdgeHomotopies_coherent x tau)
      (fun i z => (stationaryEdgeHomotopy x (face i tau)).apply_zero z)
    exact ⟨g, F, hF, fun h => (htau h).elim⟩

def stationaryTriangle (x : X) (tau : Simplex X 2) : Simplex X 2 :=
  (stationaryTriangle_exists x tau).choose

def stationaryTriangleHomotopy (x : X) (tau : Simplex X 2) :
    tau.Homotopy (stationaryTriangle x tau) :=
  (stationaryTriangle_exists x tau).choose_spec.choose

theorem stationaryTriangleHomotopy_face (x : X) (tau : Simplex X 2)
    (i : Fin 3) (t : I) (z : Domain 1) :
    stationaryTriangleHomotopy x tau (t, stdSimplex.map (SimplexCategory.δ i) z) =
      stationaryEdgeHomotopy x (face i tau) (t, z) :=
  (stationaryTriangle_exists x tau).choose_spec.choose_spec.1 i t z

theorem stationaryTriangle_face (x : X) (tau : Simplex X 2) (i : Fin 3) :
    face i (stationaryTriangle x tau) = ContinuousMap.const (Domain 1) x := by
  apply ContinuousMap.ext
  intro z
  have h := stationaryTriangleHomotopy_face x tau i 1 z
  rw [(stationaryTriangleHomotopy x tau).apply_one,
    (stationaryEdgeHomotopy x (face i tau)).apply_one] at h
  exact h

theorem stationaryTriangle_eq_of_based (x : X) (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) :
    stationaryTriangle x tau = tau :=
  (stationaryTriangle_exists x tau).choose_spec.choose_spec.2 h

/-- The stationary normalization remains coherent on all four faces of every
singular tetrahedron, by the relative homotopy extension property. -/
theorem stationaryTetrahedron_exists (x : X) (tau : Simplex X 3) :
    ∃ T : Simplex X 3, ∀ i : Fin 4, face i T = stationaryTriangle x (face i tau) := by
  obtain ⟨T, F, hF⟩ := compatibleSimplexHomotopyExtension_exists
    (fun _ => ContinuousMap.const (Domain 1) x) (stationaryTriangle x)
    (stationaryEdgeHomotopy x) (stationaryTriangleHomotopy x)
    (stationaryTriangleHomotopy_face x) tau
  refine ⟨T, ?_⟩
  intro i
  apply ContinuousMap.ext
  intro z
  have h := hF i 1 z
  rw [F.apply_one, (stationaryTriangleHomotopy x (face i tau)).apply_one] at h
  exact h

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

def stationaryPointedTriangle (x : X) (tau : Simplex X 2) :
    PointedSingularTriangle X x :=
  ⟨stationaryTriangle x tau, stationaryTriangle_face x tau⟩

def stationaryPi2Chain (x : X) :
    Chain X 2 →ₗ[ℤ] Additive (HomotopyGroup (Fin 2) X x) :=
  Finsupp.linearCombination ℤ (fun tau => (stationaryPointedTriangle x tau).pi2)

theorem stationaryPi2Chain_single_of_based (x : X) (a : PointedSingularTriangle X x) (r : ℤ) :
    stationaryPi2Chain x (Finsupp.single a.map r) = r • a.pi2 := by
  rw [stationaryPi2Chain, Finsupp.linearCombination_single]
  apply congrArg (fun v : Additive (HomotopyGroup (Fin 2) X x) => r • v)
  apply PointedSingularTriangle.pi2_congr
  exact stationaryTriangle_eq_of_based x a.map a.based

theorem stationaryPi2Chain_basedTriangleCycle (x : X) (a : PointedSingularTriangle X x) :
    stationaryPi2Chain x (basedTriangleCycle a.map x) = a.pi2 := by
  rw [basedTriangleCycle, map_sub, stationaryPi2Chain_single_of_based x a 1]
  have hc := stationaryPi2Chain_single_of_based x (PointedSingularTriangle.constant x) 1
  change stationaryPi2Chain x (Finsupp.single (ContinuousMap.const (Domain 2) x) 1) =
    (1 : ℤ) • (PointedSingularTriangle.constant x).pi2 at hc
  simp_all



theorem stationaryPi2Chain_boundary (x : X) (b : Chain X 3) :
    stationaryPi2Chain x (boundary 2 b) = 0 :=
  DFunLike.congr_fun (show (stationaryPi2Chain x).comp (boundary 2) = 0 by
    apply Finsupp.lhom_ext
    intro tau r
    change stationaryPi2Chain x (boundary 2 (Finsupp.single tau r)) = 0
    have hs : Finsupp.single tau r = r • Finsupp.single tau (1 : ℤ) := by simp
    rw [hs, map_smul, map_smul, (show stationaryPi2Chain x (boundary 2 (Finsupp.single tau 1)) = 0 by
      obtain ⟨T, hT⟩ := stationaryTetrahedron_exists x tau
      have hedge : ∀ (i : Fin 4) (j : Fin 3),
          face j (face i T) = ContinuousMap.const (Domain 1) x := by
        intro i j
        rw [hT, stationaryTriangle_face]
      have h := tetrahedron_pi2_alternating_sum_eq_zero T hedge
      convert h using 1
      rw [boundary_single, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      simp only [stationaryPi2Chain, Finsupp.linearCombination_single, one_smul]
      apply congrArg (fun v : Additive (HomotopyGroup (Fin 2) X x) => (-1 : ℤ) ^ (i : ℕ) • v)
      exact (PointedSingularTriangle.tetrahedron_face_pi2 T hedge i
        (stationaryPointedTriangle x (face i tau)) (hT i)).symm), smul_zero]) b

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- A vanishing genuine Hurewicz class forces the actual based homotopy class
to be trivial. Every square is first represented by a pointed triangle; the
stationary normalization detects its class and kills its singular filling. -/
theorem singularHurewicz2_eq_zero_iff (x : X) (q : HomotopyGroup (Fin 2) X x) :
    singularHurewicz2 x q = 0 ↔ q = 1 := by
  constructor
  · intro hq
    obtain ⟨a, ha⟩ := pointed_triangle_pi2_surjective (Additive.ofMul q)
    have hrep : (Quotient.mk _ (basedTriangleSquare a.map a.based)) = q := congrArg Additive.toMul ha
    rw [← hrep] at hq
    obtain ⟨b, hb⟩ := (singularHurewicz2_mk_eq_zero_iff
      (basedTriangleSquare a.map a.based)).mp hq
    have hzero := stationaryPi2Chain_boundary x b
    rw [hb, squareCycle_basedTriangleSquare, stationaryPi2Chain_basedTriangleCycle] at hzero
    exact congrArg Additive.toMul (ha.symm.trans hzero)
  · rintro rfl
    exact singularHurewicz2_one x



end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology
open scoped Topology
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [SimplyConnectedSpace X]

/-- A map killing actual pi2 kills every H2 class when its domain is simply
connected, since the Hurewicz images exhaust that domain's H2. -/

theorem singularH2_map_eq_zero_of_killsPi2 (x : X) (f : C(X, Y)) (hf : Whitehead.KillsPi2 f) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  exact (by
    obtain ⟨a, rfl⟩ := singularHurewicz2_surjective x q
    exact singularHurewicz2_pushdown_zero_of_killsPi2 f hf x a)

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A zero map on integral H2 kills actual pi2 if the target is simply connected. -/
theorem killsPi2_of_singularH2_map_eq_zero [SimplyConnectedSpace Y]
    (f : C(X, Y))
    (hf : (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom f)) = 0) : Whitehead.KillsPi2 f := by
  apply (Whitehead.killsPi2_iff f).mpr
  intro x q
  apply (singularHurewicz2_eq_zero_iff (f x) _).mp
  rw [← singularHurewicz2_natural f x q, hf]
  rfl

theorem killsPi2_iff_singularH2_map_eq_zero [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    (x : X) (f : C(X, Y)) :
    Whitehead.KillsPi2 f ↔
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom f)) = 0 :=
  ⟨singularH2_map_eq_zero_of_killsPi2 x f, killsPi2_of_singularH2_map_eq_zero f⟩

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open CategoryTheory

/-- Representatives up to actual boundaries suffice to prove surjectivity
of Mathlib's canonical homology map. -/

theorem shortComplex_homologyMap_epi_of_representatives
    {S T : ShortComplex (ModuleCat ℤ)} (φ : S ⟶ T)
    (h : ∀ c : T.X₂, T.g c = 0 →
      ∃ z : S.X₂, S.g z = 0 ∧ ∃ b : T.X₁, T.f b = c - φ.τ₂ z) :
    Epi (ShortComplex.homologyMap φ) :=
  (ModuleCat.epi_iff_surjective _).mpr (by
    intro q
    obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).mp inferInstance q
    have hyz : T.g (T.iCycles y) = 0 := by
      exact congrArg (fun f => f y) T.iCycles_g
    obtain ⟨z, hz, b, hb⟩ := h (T.iCycles y) hyz
    let z'  := S.moduleCatCyclesIso.inv ⟨z, hz⟩
    have hzi : S.iCycles z' = z := by
      exact congrArg (fun f => f ⟨z, hz⟩) S.moduleCatCyclesIso_inv_iCycles
    refine ⟨S.homologyπ z', ?_⟩
    apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
    rw [← hy]
    have hmap := congrArg (fun f => f z') (ShortComplex.π_homologyMap_ι φ)
    change T.homologyι ((ShortComplex.homologyMap φ) (S.homologyπ z')) =
      T.pOpcycles (φ.τ₂ (S.iCycles z')) at hmap
    have hπ := congrArg (fun f => f y) T.homology_π_ι
    change T.homologyι (T.homologyπ y) = T.pOpcycles (T.iCycles y) at hπ
    rw [hmap, hπ, hzi]
    apply (T.moduleCat_pOpcycles_eq_iff _ _).mpr
    refine ⟨-b, ?_⟩
    rw [map_neg, hb]
    abel)

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open CategoryTheory

/-- A chain map is injective on homology when every cycle whose image bounds
already bounds in the source complex. -/

theorem shortComplex_homologyMap_mono_of_reflects_boundaries
    {S T : ShortComplex (ModuleCat ℤ)} (φ : S ⟶ T)
    (h : ∀ c : S.X₂, S.g c = 0 →
      (∃ b : T.X₁, T.f b = φ.τ₂ c) → ∃ a : S.X₁, S.f a = c) :
    Mono (ShortComplex.homologyMap φ) :=
  (ModuleCat.mono_iff_injective _).mpr (by
    have hzero : ∀ q : S.homology, (ShortComplex.homologyMap φ) q = 0 → q = 0 := by
      intro q hq
      obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance q
      have hy  := congrArg (fun f => f y) S.iCycles_g
      have ht : T.pOpcycles (φ.τ₂ (S.iCycles y)) = 0 := by
        have he := congrArg (fun f => f y) (ShortComplex.π_homologyMap_ι φ)
        change T.homologyι ((ShortComplex.homologyMap φ) (S.homologyπ y)) =
          T.pOpcycles (φ.τ₂ (S.iCycles y)) at he
        rw [hq, map_zero] at he
        exact he.symm
      obtain ⟨a, ha⟩ := h (S.iCycles y) hy ((T.moduleCat_pOpcycles_eq_zero_iff _).mp ht)
      apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
      rw [map_zero]
      have he := congrArg (fun f => f y) S.homology_π_ι
      change S.homologyι (S.homologyπ y) = S.pOpcycles (S.iCycles y) at he
      rw [he]
      exact (S.moduleCat_pOpcycles_eq_zero_iff _).mpr ⟨a, ha⟩
    intro a b hab
    apply sub_eq_zero.mp
    simp_all)

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
universe u
variable {X : Type u} [TopologicalSpace X]

/-- Subspace chains are precisely chains whose basis simplices stay in the subspace. -/
theorem subChains_eq_supported (A : Set X) (n : ℕ) :
    subChains A n = Finsupp.supported ℤ ℤ {σ : Simplex X n | ∀ z, σ z ∈ A} := by
  apply le_antisymm
  · rintro c ⟨b, rfl⟩
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b c hb hc => simpa using Submodule.add_mem _ hb hc
    | single σ r =>
      rw [map_single]
      exact Finsupp.single_mem_supported ℤ r (fun z => (σ z).property)
  · intro c hc
    have he := VertexChains.map_mem_of_supported
      {σ : Simplex X n | ∀ z, σ z ∈ A} (subChains A n) LinearMap.id 
      (fun σ hσ => single_mem_subChains A n σ 1 hσ) hc
    exact he

theorem single_mem_range_subChains {n : ℕ} (σ : Simplex X n) (r : ℤ) :
    Finsupp.single σ r ∈ subChains (Set.range σ) n :=
  single_mem_subChains _ _ _ _ (fun z => ⟨z, rfl⟩)

/-- A map carried by each basis simplex preserves every subspace chain module. -/
theorem carried_linearMap_mem_subChains {n k : ℕ} (f : Chain X n →ₗ[ℤ] Chain X k)
    (hf : ∀ σ : Simplex X n, f (Finsupp.single σ 1) ∈ subChains (Set.range σ) k)
    (A : Set X) {c : Chain X n} (hc : c ∈ subChains A n) : f c ∈ subChains A k := by
  rw [subChains_eq_supported] at hc
  apply VertexChains.map_mem_of_supported _ _ f ?_ hc
  intro σ hσ
  exact subChains_mono (by rintro _ ⟨z, rfl⟩; exact hσ z) k (hf σ)

end FiniteChains.TopologicalSingular

namespace FiniteChains.SingularSubdivision
open TopologicalSingular
universe u
variable {X : Type u} [TopologicalSpace X]

theorem fromModel_mem_subChains (A : Set X) {k l : ℕ} (m : Chain (Domain k) l)
    {c : Chain X k} (hc : c ∈ subChains A k) : fromModel m c ∈ subChains A l := by
  obtain ⟨b, rfl⟩ := hc
  exact ⟨fromModel m b, fromModel_naturality m (inclusion A) b⟩

theorem iterated_subdivide_mem_subChains (A : Set X) (k n : ℕ)
    {c : Chain X n} (hc : c ∈ subChains A n) :
    ((subdivide n)^[k]) c ∈ subChains A n := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact fromModel_mem_subChains A (model n) ih

theorem iteratedHomotopy_mem_subChains (A : Set X) (k n : ℕ)
    {c : Chain X n} (hc : c ∈ subChains A n) :
    iteratedHomotopy n k c ∈ subChains A (n + 1) := by
  induction k with
  | zero => rw [iteratedHomotopy_zero]; exact Submodule.zero_mem _
  | succ k ih =>
    rw [iteratedHomotopy_succ]
    exact Submodule.add_mem _
      (fromModel_mem_subChains A (homotopyModel n) (iterated_subdivide_mem_subChains A k n hc)) ih

end FiniteChains.SingularSubdivision

namespace FiniteChains.SingularSubdivision
open TopologicalSingular
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

structure SmallRefinementStage (U : ι → Set X) (n : ℕ) where
  smallMap : Chain X n →ₗ[ℤ] Chain X n
  homotopyMap : Chain X n →ₗ[ℤ] Chain X (n + 1)
  small : ∀ c, smallMap c ∈ smallChains U n
  small_support : ∀ σ : Simplex X n,
    smallMap (Finsupp.single σ 1) ∈ subChains (Set.range σ) n
  homotopy_support : ∀ σ : Simplex X n,
    homotopyMap (Finsupp.single σ 1) ∈ subChains (Set.range σ) (n + 1)
  on_boundary : ∀ c : Chain X (n + 1),
    boundary n (homotopyMap (boundary n c)) = boundary n c - smallMap (boundary n c)

theorem all_zero_chains_small (U : ι → Set X) (hcover : ∀ x, ∃ i, x ∈ U i)
    (c : Chain X 0) : c ∈ smallChains U 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => exact Submodule.add_mem _ hc hd
  | single σ r =>
    obtain ⟨i, hi⟩ := hcover (σ (stdSimplex.vertex 0))
    apply single_mem_small U 0 σ r
    refine ⟨i, fun z => ?_⟩
    letI : Subsingleton (Domain 0) := inferInstanceAs (Subsingleton (stdSimplex ℝ (Fin 1)))
    rwa [show z = stdSimplex.vertex 0 from Subsingleton.elim _ _]

def smallRefinementStageZero (U : ι → Set X) (hcover : ∀ x, ∃ i, x ∈ U i) :
    SmallRefinementStage U 0 where
  smallMap := LinearMap.id
  homotopyMap := 0
  small := all_zero_chains_small U hcover
  small_support σ := single_mem_range_subChains σ 1
  homotopy_support _ := Submodule.zero_mem _
  on_boundary _ := by simp

/-- Correct the boundary first, then subdivide. The correction and homotopy stay
inside the image of the original simplex. -/
theorem smallRefinementStep_exists (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n : ℕ} (s : SmallRefinementStage U n)
    (σ : Simplex X (n + 1)) :
    ∃ d : Chain X (n + 1), ∃ h : Chain X (n + 2),
      d ∈ smallChains U (n + 1) ∧ d ∈ subChains (Set.range σ) (n + 1) ∧
      h ∈ subChains (Set.range σ) (n + 2) ∧
      boundary (n + 1) h = Finsupp.single σ 1 - d - s.homotopyMap (boundary n (Finsupp.single σ 1)) := by
  let c := Finsupp.single σ 1 - s.homotopyMap (boundary n (Finsupp.single σ 1))
  have hc  :=
    Submodule.sub_mem _ (single_mem_range_subChains σ 1)
      (carried_linearMap_mem_subChains s.homotopyMap s.homotopy_support _
        (boundary_mem_subChains _ n (single_mem_range_subChains σ 1)))
  have hbc : boundary n c = s.smallMap (boundary n (Finsupp.single σ 1)) := by
    dsimp only [c]
    rw [map_sub, s.on_boundary]
    abel
  have hsmallbc : boundary n c ∈ smallChains U n := by
    rw [hbc]
    exact s.small _
  obtain ⟨k, hk⟩ := exists_subdivision_small U hU hcover (n + 1) c
  refine ⟨((subdivide (n + 1))^[k]) c - iteratedHomotopy n k (boundary n c),
    -iteratedHomotopy (n + 1) k c,
    Submodule.sub_mem _ hk (iteratedHomotopy_mem_small U k n hsmallbc),
    Submodule.sub_mem _ (iterated_subdivide_mem_subChains _ k (n + 1) hc)
      (iteratedHomotopy_mem_subChains _ k n (boundary_mem_subChains _ n hc)),
    Submodule.neg_mem _ (iteratedHomotopy_mem_subChains _ k (n + 1) hc), ?_⟩
  have he := eq_sub_of_add_eq (iteratedHomotopy_identity_succ k n c)
  rw [map_neg, he]
  dsimp only [c]
  abel

end FiniteChains.SingularSubdivision

namespace FiniteChains.SingularSubdivision
open TopologicalSingular
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

def smallRefinementNextMap (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n : ℕ} (s : SmallRefinementStage U n) :
    Chain X (n + 1) →ₗ[ℤ] Chain X (n + 1) :=
  Finsupp.linearCombination ℤ (fun σ => (smallRefinementStep_exists U hU hcover s σ).choose)

def smallRefinementNextHomotopy (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n : ℕ} (s : SmallRefinementStage U n) :
    Chain X (n + 1) →ₗ[ℤ] Chain X (n + 2) :=
  Finsupp.linearCombination ℤ
    (fun σ => (smallRefinementStep_exists U hU hcover s σ).choose_spec.choose)

theorem smallRefinementNextHomotopy_identity (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n : ℕ} (s : SmallRefinementStage U n)
    (c : Chain X (n + 1)) :
    boundary (n + 1) (smallRefinementNextHomotopy U hU hcover s c) =
      c - smallRefinementNextMap U hU hcover s c - s.homotopyMap (boundary n c) := by
  have he : (boundary (n + 1)).comp (smallRefinementNextHomotopy U hU hcover s) =
      LinearMap.id - smallRefinementNextMap U hU hcover s -
        s.homotopyMap.comp (boundary n) := by
    apply Finsupp.lhom_ext'
    intro σ
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      smallRefinementNextHomotopy, smallRefinementNextMap,
      Finsupp.lsingle_apply, Finsupp.linearCombination_single, one_smul]
    exact (smallRefinementStep_exists U hU hcover s σ).choose_spec.choose_spec.2.2.2
  exact DFunLike.congr_fun he c

def smallRefinementStageNext (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n : ℕ} (s : SmallRefinementStage U n) :
    SmallRefinementStage U (n + 1) where
  smallMap := smallRefinementNextMap U hU hcover s
  homotopyMap := smallRefinementNextHomotopy U hU hcover s
  small c := by
    induction c using Finsupp.induction_linear with
    | zero => simp only [map_zero, Submodule.zero_mem]
    | add c d hc hd => simpa only [map_add] using Submodule.add_mem _ hc hd
    | single σ r =>
      dsimp only [smallRefinementNextMap]
      rw [Finsupp.linearCombination_single]
      exact Submodule.smul_mem _ r
        (smallRefinementStep_exists U hU hcover s σ).choose_spec.choose_spec.1
  small_support σ := by
    dsimp only [smallRefinementNextMap]
    rw [Finsupp.linearCombination_single, one_smul]
    exact (smallRefinementStep_exists U hU hcover s σ).choose_spec.choose_spec.2.1
  homotopy_support σ := by
    dsimp only [smallRefinementNextHomotopy]
    rw [Finsupp.linearCombination_single, one_smul]
    exact (smallRefinementStep_exists U hU hcover s σ).choose_spec.choose_spec.2.2.1
  on_boundary c := by
    rw [smallRefinementNextHomotopy_identity, boundary_boundary, map_zero, sub_zero]

def smallRefinementStage (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) : (n : ℕ) → SmallRefinementStage U n
  | 0 => smallRefinementStageZero U hcover
  | n + 1 => smallRefinementStageNext U hU hcover (smallRefinementStage U hU hcover n)

def smallRefinement (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) : Chain X n →ₗ[ℤ] Chain X n :=
  (smallRefinementStage U hU hcover n).smallMap

def smallRefinementHomotopy (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) : Chain X n →ₗ[ℤ] Chain X (n + 1) :=
  (smallRefinementStage U hU hcover n).homotopyMap

theorem smallRefinementHomotopy_identity (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (c : Chain X (n + 1)) :
    boundary (n + 1) (smallRefinementHomotopy U hU hcover (n + 1) c) =
      c - smallRefinement U hU hcover (n + 1) c -
        smallRefinementHomotopy U hU hcover n (boundary n c) :=
  smallRefinementNextHomotopy_identity U hU hcover (smallRefinementStage U hU hcover n) c

theorem smallRefinement_boundary (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (c : Chain X (n + 1)) :
    boundary n (smallRefinement U hU hcover (n + 1) c) =
      smallRefinement U hU hcover n (boundary n c) := by
  have he := congrArg (boundary n) (smallRefinementHomotopy_identity U hU hcover n c)
  rw [boundary_boundary, map_sub, map_sub, smallRefinementHomotopy,
    (smallRefinementStage U hU hcover n).on_boundary] at he
  change 0 = boundary n c - boundary n (smallRefinement U hU hcover (n + 1) c) -
    (boundary n c - smallRefinement U hU hcover n (boundary n c)) at he
  linear_combination (norm := abel) he

theorem smallRefinement_mem_small (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (c : Chain X n) :
    smallRefinement U hU hcover n c ∈ smallChains U n :=
  (smallRefinementStage U hU hcover n).small c

/-- Refinement preserves every subspace, even though the subdivision count may
depend on the individual simplex. -/
theorem smallRefinement_support (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (A : Set X) {c : Chain X n}
    (hc : c ∈ subChains A n) : smallRefinement U hU hcover n c ∈ subChains A n :=
  carried_linearMap_mem_subChains _ (smallRefinementStage U hU hcover n).small_support A hc

end FiniteChains.SingularSubdivision

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- Restrict the comparable-vertex carrier to vertices that actually occur
at some point of the singular simplex. This restriction preserves acyclicity
and makes the carrier respect every vertex subcomplex. -/
def orderNerveTightCarrier {n : ℕ} (σ : Simplex (orderNerveRealization P) n) : Set P :=
  {p | (∃ z, σ z ∈ orderNerveRealizationOpenStar P p) ∧ p ∈ orderNerveSingularCarrier σ}

theorem orderNerveTightCarrier_face {n : ℕ} (σ : Simplex (orderNerveRealization P) (n + 1))
    (i : Fin (n + 2)) : orderNerveTightCarrier (face i σ) ⊆ orderNerveTightCarrier σ := by
  rintro p ⟨⟨z, hz⟩, hp⟩
  exact ⟨⟨_, hz⟩, orderNerveSingularCarrier_face σ i hp⟩

theorem orderNerveStarIndices_subset_tight {n : ℕ} (σ : Simplex (orderNerveRealization P) n) :
    orderNerveSingularStarIndices σ ⊆ orderNerveTightCarrier σ := by
  intro p hp
  exact ⟨⟨stdSimplex.vertex 0, hp _⟩, orderNerveSingularStarIndices_subset_carrier σ hp⟩

theorem orderNerveTightCarrier_acyclic {n : ℕ} (σ : OrderSmallSimplex P n) :
    Nerve.AcyclicIn (orderNerveTightCarrier σ.val) := by
  obtain ⟨v, hv⟩ := σ.property
  have hv' := orderNerveStarIndices_subset_tight σ.val hv
  apply Nerve.acyclicIn_of_subtype _ ⟨v, hv'⟩
  intro c hc hz
  exact orderNerve_cycle_bounds_of_comparable
    ⟨v, hv'⟩ (fun p => p.property.2 v hv) hc hz

theorem orderNerveTightCarrier_subset {n : ℕ} (σ : Simplex (orderNerveRealization P) n)
    (A : Set P) (hσ : ∀ z, σ z ∈ orderNerveRealizationSubcomplex P A) :
    orderNerveTightCarrier σ ⊆ A := by
  rintro p ⟨⟨z, hz⟩, _⟩
  by_contra hp
  have he := hσ z p hp
  change 0 < orderNerveRealizationCoordinates P (σ z) p at hz
  simp_all

theorem orderSmallToNerve0_tight (σ : OrderSmallSimplex P 0) :
    orderSmallToNerve0 (orderSmallSingle σ 1) ∈ Nerve.IncOn (orderNerveTightCarrier σ.val) := by
  rw [orderSmallToNerve0_single, one_smul]
  apply Nerve.of_mem_incOn (by simp)
  intro p hp
  have hp' : p = orderSmallChosenVertex σ := by simpa using hp
  rw [hp']
  exact orderNerveStarIndices_subset_tight σ.val σ.property.choose_spec

end FiniteChains.Comb

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- The data needed to extend a carried approximation by one degree. -/
structure OrderTightNerveStage (P : Type) [PartialOrder P] (n : ℕ) where
  map : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Nerve.Ch P
  carrier : ∀ σ : OrderSmallSimplex P n,
    map (orderSmallSingle σ 1) ∈ Nerve.IncOn (orderNerveTightCarrier σ.val)
  homogeneous : ∀ c, Nerve.lengthProjection (n + 1) (map c) = map c
  closed_boundary : ∀ c : smallChains (orderNerveRealizationOpenStar P) (n + 1),
    Nerve.bdry (map (smallBoundary (orderNerveRealizationOpenStar P) n c)) = 0

def orderTightNerveStageZero : OrderTightNerveStage P 0 where
  map := orderSmallToNerve0
  carrier := orderSmallToNerve0_tight
  homogeneous := orderSmallToNerve0_length
  closed_boundary c := by
    rw [orderSmallToNerve0_boundary]
    change augmentation (boundary 0 c.val) • _ = 0
    rw [augmentation_boundary, zero_smul]


/-- Every new simplex can be filled in its own acyclic order carrier. -/
theorem orderTightNerveStage_fill {n : ℕ} (s : OrderTightNerveStage P n)
    (σ : OrderSmallSimplex P (n + 1)) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (orderNerveTightCarrier σ.val) ∧
      Nerve.lengthProjection (n + 2) b = b ∧ Nerve.bdry b =
        s.map (smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ 1)) := by
  obtain ⟨b, hb, he⟩ := orderNerveTightCarrier_acyclic σ _
    (by
      rw [orderSmallSingle_boundary, map_sum]
      apply AddSubgroup.sum_mem
      intro i _
      rw [map_smul]
      apply AddSubgroup.zsmul_mem
      exact Nerve.incOn_mono (fun _ hp => orderNerveTightCarrier_face σ.val i hp)
        ((s.carrier) (orderSmallSimplexFace i σ))) (s.closed_boundary _)
  refine ⟨Nerve.lengthProjection (n + 2) b, Nerve.lengthProjection_mem_incOn _ hb,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  rw [← Nerve.lengthProjection_bdry, he]
  exact s.homogeneous _

def orderTightNerveStageNextMap {n : ℕ} (s : OrderTightNerveStage P n) :
    smallChains (orderNerveRealizationOpenStar P) (n + 1) →ₗ[ℤ] Nerve.Ch P :=
  (Finsupp.linearCombination ℤ (fun σ => (orderTightNerveStage_fill s σ).choose)).comp
    (orderSmallChainEquiv P (n + 1)).toLinearMap

theorem orderTightNerveStageNextMap_single {n : ℕ} (s : OrderTightNerveStage P n)
    (σ : OrderSmallSimplex P (n + 1)) :
    orderTightNerveStageNextMap s (orderSmallSingle σ 1) =
      (orderTightNerveStage_fill s σ).choose := by
  have he := (orderSmallChainEquiv P (n + 1)).apply_symm_apply (Finsupp.single σ 1)
  rw [orderSmallChainEquiv_symm_single] at he
  change (Finsupp.linearCombination ℤ (fun τ : OrderSmallSimplex P (n + 1) =>
    (orderTightNerveStage_fill s τ).choose))
      ((orderSmallChainEquiv P (n + 1)) (orderSmallSingle σ 1)) = _
  simp_all

theorem orderTightNerveStageNextMap_boundary {n : ℕ} (s : OrderTightNerveStage P n)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1)) :
    Nerve.bdry (orderTightNerveStageNextMap s c) =
      s.map (smallBoundary (orderNerveRealizationOpenStar P) n c) := by
  have he : Nerve.bdry.toIntLinearMap.comp (orderTightNerveStageNextMap s) =
      s.map.comp (smallBoundary (orderNerveRealizationOpenStar P) n) := by
    apply orderSmallSingle_spans
    intro σ
    change Nerve.bdry (orderTightNerveStageNextMap s (orderSmallSingle σ 1)) = _
    rw [orderTightNerveStageNextMap_single]
    exact (orderTightNerveStage_fill s σ).choose_spec.2.2
  exact DFunLike.congr_fun he c

def orderTightNerveStageNext {n : ℕ} (s : OrderTightNerveStage P n) :
    OrderTightNerveStage P (n + 1) where
  map := orderTightNerveStageNextMap s
  carrier σ := by
    rw [orderTightNerveStageNextMap_single]
    exact (orderTightNerveStage_fill s σ).choose_spec.1
  homogeneous c := by
    have he : (Nerve.lengthProjection (n + 2)).toIntLinearMap.comp
        (orderTightNerveStageNextMap s) = orderTightNerveStageNextMap s := by
      apply orderSmallSingle_spans
      intro σ
      change Nerve.lengthProjection (n + 2)
        (orderTightNerveStageNextMap s (orderSmallSingle σ 1)) = _
      rw [orderTightNerveStageNextMap_single]
      exact (orderTightNerveStage_fill s σ).choose_spec.2.1
    exact DFunLike.congr_fun he c
  closed_boundary c := by
    rw [orderTightNerveStageNextMap_boundary]
    have hd := DFunLike.congr_fun (smallBoundary_squared (orderNerveRealizationOpenStar P) n) c
    change smallBoundary (orderNerveRealizationOpenStar P) n
      (smallBoundary (orderNerveRealizationOpenStar P) (n + 1) c) = 0 at hd
    rw [hd, map_zero]

/-- A carried approximation exists simultaneously in all dimensions. -/
def orderTightNerveStage (P : Type) [PartialOrder P] :
    (n : ℕ) → OrderTightNerveStage P n
  | 0 => orderTightNerveStageZero
  | n + 1 => orderTightNerveStageNext (orderTightNerveStage P n)

def orderTightToNerve (P : Type) [PartialOrder P] (n : ℕ) :
    smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Nerve.Ch P :=
  (orderTightNerveStage P n).map

theorem orderTightToNerve_carrier (n : ℕ) (σ : OrderSmallSimplex P n) :
    orderTightToNerve P n (orderSmallSingle σ 1) ∈
      Nerve.IncOn (orderNerveTightCarrier σ.val) :=
  (orderTightNerveStage P n).carrier σ

theorem orderTightToNerve_length (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) n) :
    Nerve.lengthProjection (n + 1) (orderTightToNerve P n c) = orderTightToNerve P n c :=
  (orderTightNerveStage P n).homogeneous c

theorem orderTightToNerve_boundary (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1)) :
    Nerve.bdry (orderTightToNerve P (n + 1) c) =
      orderTightToNerve P n (smallBoundary (orderNerveRealizationOpenStar P) n c) :=
  orderTightNerveStageNextMap_boundary (orderTightNerveStage P n) c

theorem orderTightToNerve_mem_inc (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) n) :
    orderTightToNerve P n c ∈ Nerve.Inc P := by
  obtain ⟨d, rfl⟩ := (orderSmallChainEquiv P n).symm.surjective c
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simpa using (Nerve.Inc P).add_mem hd he
  | single σ r =>
    have hr : Finsupp.single σ r = r • Finsupp.single σ 1 := by simp
    rw [hr, map_smul, map_smul, orderSmallChainEquiv_symm_single]
    exact (Nerve.Inc P).zsmul_mem
      (Nerve.incOn_le_inc _ (orderTightToNerve_carrier n σ)) r

/-- The tightened approximation respects every induced vertex subcomplex. -/
theorem orderTightToNerve_supported (n : ℕ) (A : Set P)
    (c : smallChains (orderNerveRealizationOpenStar P) n)
    (hc : c.val ∈ subChains (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) n) :
    orderTightToNerve P n c ∈ Nerve.IncOn A := by
  obtain ⟨d, rfl⟩ := (orderSmallChainEquiv P n).symm.surjective c
  have hd : d ∈ Finsupp.supported ℤ ℤ {σ : OrderSmallSimplex P n |
      ∀ z, σ.val z ∈ orderNerveRealizationSubcomplex P A} := by
    rw [subChains_eq_supported, Finsupp.mem_supported] at hc
    rw [Finsupp.mem_supported]
    intro σ hσ
    apply hc
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hσ ⊢
    have he := congrArg (fun e : OrderSmallSimplex P n →₀ ℤ => e σ)
      ((orderSmallChainEquiv P n).apply_symm_apply d)
    change ((orderSmallChainEquiv P n).symm d).val σ.val = d σ at he
    rwa [he]
  exact VertexChains.map_mem_of_supported _ (Nerve.IncOn A).toIntSubmodule
    ((orderTightToNerve P n).comp (orderSmallChainEquiv P n).symm.toLinearMap)
    (by
      intro σ hσ
      change orderTightToNerve P n ((orderSmallChainEquiv P n).symm (Finsupp.single σ 1)) ∈ _
      rw [orderSmallChainEquiv_symm_single]
      exact Nerve.incOn_mono (fun _ hp => orderNerveTightCarrier_subset σ.val A hσ hp)
        (orderTightToNerve_carrier n σ)) hd

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

def orderRefinementSmall (P : Type) [PartialOrder P] (n : ℕ) :
    Chain (orderNerveRealization P) n →ₗ[ℤ] smallChains (orderNerveRealizationOpenStar P) n :=
  (smallRefinement (orderNerveRealizationOpenStar P) (orderNerveRealizationOpenStar_isOpen P)
    (orderNerveRealizationOpenStar_cover P) n).codRestrict _
      (smallRefinement_mem_small _ _ _ n)


def orderSingularToNerve (P : Type) [PartialOrder P] (n : ℕ) :
    Chain (orderNerveRealization P) n →ₗ[ℤ] Nerve.Ch P :=
  (orderTightToNerve P n).comp (orderRefinementSmall P n)

theorem orderSingularToNerve_boundary (n : ℕ) (c : Chain (orderNerveRealization P) (n + 1)) :
    Nerve.bdry (orderSingularToNerve P (n + 1) c) =
      orderSingularToNerve P n (boundary n c) := by
  erw [orderTightToNerve_boundary, (show smallBoundary (orderNerveRealizationOpenStar P) n (orderRefinementSmall P (n + 1) c) =
      orderRefinementSmall P n (boundary n c) by
    apply Subtype.ext
    exact smallRefinement_boundary _ _ _ n c)]
  rfl

theorem orderSingularToNerve_zero_boundary (c : Chain (orderNerveRealization P) 0) :
    Nerve.bdry (orderSingularToNerve P 0 c) =
      augmentation c • FreeAbelianGroup.of ([] : List P) := by
  erw [orderSmallToNerve0_boundary]
  rfl

theorem orderSingularToNerve_length (n : ℕ) (c : Chain (orderNerveRealization P) n) :
    Nerve.lengthProjection (n + 1) (orderSingularToNerve P n c) = orderSingularToNerve P n c :=
  orderTightToNerve_length n _

theorem orderSingularToNerve_mem_inc (n : ℕ) (c : Chain (orderNerveRealization P) n) :
    orderSingularToNerve P n c ∈ Nerve.Inc P := orderTightToNerve_mem_inc n _

theorem orderSingularToNerve_supported (n : ℕ) (A : Set P)
    {c : Chain (orderNerveRealization P) n}
    (hc : c ∈ subChains (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) n) :
    orderSingularToNerve P n c ∈ Nerve.IncOn A :=
  orderTightToNerve_supported n A _ (smallRefinement_support _ _ _ n _ hc)

/-- The return map on the original simplicial chains. -/
def orderNerveRoundTrip (P : Type) [PartialOrder P] (n : ℕ) :
    (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  (orderSingularToNerve P n).comp ((orderNerveExplicitSingularMap P).f n).hom

theorem orderNerveRoundTrip_boundary (n : ℕ) (c : ComposableArrows P (n + 1) →₀ ℤ) :
    Nerve.bdry (orderNerveRoundTrip P (n + 1) c) =
      orderNerveRoundTrip P n
        ((AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) n).hom c) := by
  have he := congrArg (fun f => f c) ((orderNerveExplicitSingularMap P).comm (n + 1) n)
  erw [complex_d, AlternatingFaceMapComplex.obj_d_eq] at he
  erw [orderSingularToNerve_boundary]
  exact congrArg (orderSingularToNerve P n) he

theorem orderNerveRoundTrip_supported (n : ℕ) (s : ComposableArrows P n) :
    orderNerveRoundTrip P n (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj) := by
  apply orderSingularToNerve_supported
  erw [orderNerveExplicitSingularMap_single]
  exact single_mem_subChains _ n _ 1 (orderNerveSingularSimplex_supported _ s (fun i => ⟨i, rfl⟩))

theorem orderNerveRoundTrip_zero_boundary (c : ComposableArrows P 0 →₀ ℤ) :
    Nerve.bdry (orderNerveRoundTrip P 0 c) = Nerve.bdry (orderNerveGradedEncode 0 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single s r =>
    change Nerve.bdry (orderSingularToNerve P 0 ((orderNerveExplicitSingularMap P).f 0 _)) = _
    erw [orderNerveExplicitSingularMap_single, orderSingularToNerve_zero_boundary,
      augmentation_single, orderNerveGradedEncode_single, map_zsmul, Nerve.bdry_of]
    simp [orderNerveVertexList, List.ofFn_succ, Nerve.bdryOn]

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
open scoped Simplicial
variable {P : Type} [PartialOrder P]

abbrev orderSimplicialBoundary (P : Type) [PartialOrder P] (n : ℕ) :=
  (AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) n).hom

theorem orderSimplicialBoundary_squared (n : ℕ) (c : ComposableArrows P (n + 2) →₀ ℤ) :
    orderSimplicialBoundary P n (orderSimplicialBoundary P (n + 1) c) = 0 := by
  apply orderNerveGradedEncode_injective n
  erw [orderNerveGradedEncode_boundary, orderNerveGradedEncode_boundary, Nerve.bdry_bdry, map_zero]

theorem orderNerveGradedEncode_length (n : ℕ) (c : ComposableArrows P n →₀ ℤ) :
    Nerve.lengthProjection (n + 1) (orderNerveGradedEncode n c) = orderNerveGradedEncode n c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single s r =>
    erw [orderNerveGradedEncode_single, map_zsmul, Nerve.lengthProjection_of,
      if_pos (orderNerveVertexList_length s)]

theorem orderNerveGradedEncode_single_supported (n : ℕ) (s : ComposableArrows P n) :
    orderNerveGradedEncode n (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj) := by
  erw [orderNerveGradedEncode_single, one_smul]
  apply Nerve.of_mem_incOn (orderNerveVertexList_chain s)
  intro p hp
  exact List.mem_ofFn.mp hp

theorem orderNerveSimplexCarrier_acyclic {n : ℕ} (s : ComposableArrows P n) :
    Nerve.AcyclicIn (Set.range s.obj) := by
  apply Nerve.acyclicIn_of_subtype _ ⟨s.obj 0, ⟨0, rfl⟩⟩
  intro c hc hz
  apply orderNerve_cycle_bounds_of_comparable ⟨s.obj 0, ⟨0, rfl⟩⟩ ?_ hc hz
  rintro ⟨p, ⟨i, rfl⟩⟩
  exact Or.inr (s.monotone (Fin.zero_le i))

theorem orderNerveSimplexCarrier_face {n : ℕ} (s : ComposableArrows P (n + 1))
    (i : Fin (n + 2)) : Set.range ((nerve P).δ i s).obj ⊆ Set.range s.obj := by
  rintro p ⟨j, rfl⟩
  exact ⟨i.succAbove j, rfl⟩

theorem orderSimplicialBoundary_map_carrier {n : ℕ}
    (f : (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P)
    (hf : ∀ s : ComposableArrows P n, f (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj))
    (s : ComposableArrows P (n + 1)) :
    f (orderSimplicialBoundary P n (Finsupp.single s 1)) ∈ Nerve.IncOn (Set.range s.obj) := by
  erw [mathlibOrderNerve_d_single, map_sum]
  apply AddSubgroup.sum_mem
  intro i _
  erw [map_smul]
  apply AddSubgroup.zsmul_mem
  exact Nerve.incOn_mono (fun _ hp => orderNerveSimplexCarrier_face s i hp) (hf _)

theorem orderSimplicialMap_mem_inc {n : ℕ}
    (f : (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P)
    (hf : ∀ s : ComposableArrows P n, f (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj))
    (c : ComposableArrows P n →₀ ℤ) : f c ∈ Nerve.Inc P := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa using (Nerve.Inc P).add_mem hc hd
  | single s r =>
    erw [show Finsupp.single s r = r • Finsupp.single s 1 by simp, map_smul]
    exact (Nerve.Inc P).zsmul_mem (Nerve.incOn_le_inc _ (hf s)) r

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
variable {P : Type} [PartialOrder P]

structure OrderReturnHomotopyStage (P : Type) [PartialOrder P] (n : ℕ) where
  map : (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P
  carrier : ∀ s, map (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj)
  homogeneous : ∀ c, Nerve.lengthProjection (n + 2) (map c) = map c
  on_boundary : ∀ c : ComposableArrows P (n + 1) →₀ ℤ,
    Nerve.bdry (map (orderSimplicialBoundary P n c)) =
      orderNerveGradedEncode n (orderSimplicialBoundary P n c) -
        orderNerveRoundTrip P n (orderSimplicialBoundary P n c)

theorem orderNerveCarriedFill {n : ℕ} (s : ComposableArrows P n) (c : Nerve.Ch P)
    (hc : c ∈ Nerve.IncOn (Set.range s.obj)) (hlen : Nerve.lengthProjection (n + 1) c = c)
    (hz : Nerve.bdry c = 0) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (Set.range s.obj) ∧
      Nerve.lengthProjection (n + 2) b = b ∧ Nerve.bdry b = c := by
  obtain ⟨b, hb, he⟩ := orderNerveSimplexCarrier_acyclic s c hc hz
  refine ⟨Nerve.lengthProjection (n + 2) b, Nerve.lengthProjection_mem_incOn _ hb,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  rw [← Nerve.lengthProjection_bdry, he, hlen]

theorem orderReturnHomotopyZero_fill (s : ComposableArrows P 0) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (Set.range s.obj) ∧
      Nerve.lengthProjection 2 b = b ∧ Nerve.bdry b =
        orderNerveGradedEncode 0 (Finsupp.single s 1) - orderNerveRoundTrip P 0 (Finsupp.single s 1) := by
  apply orderNerveCarriedFill s
  · exact AddSubgroup.sub_mem _ (orderNerveGradedEncode_single_supported 0 s)
      (orderNerveRoundTrip_supported 0 s)
  · rw [map_sub, orderNerveGradedEncode_length]
    congr 1
    exact orderSingularToNerve_length 0 _
  · rw [map_sub, orderNerveRoundTrip_zero_boundary, sub_self]

def orderReturnHomotopyZero : (ComposableArrows P 0 →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun s => (orderReturnHomotopyZero_fill s).choose)

theorem orderReturnHomotopyZero_single (s : ComposableArrows P 0) :
    orderReturnHomotopyZero (Finsupp.single s 1) = (orderReturnHomotopyZero_fill s).choose := by
  rw [orderReturnHomotopyZero, Finsupp.linearCombination_single, one_smul]


def orderReturnHomotopyStageZero : OrderReturnHomotopyStage P 0 where
  map := orderReturnHomotopyZero
  carrier s := by
    rw [orderReturnHomotopyZero_single]
    exact (orderReturnHomotopyZero_fill s).choose_spec.1
  homogeneous c := by
    have he : (Nerve.lengthProjection 2).toIntLinearMap.comp orderReturnHomotopyZero =
        (orderReturnHomotopyZero : (ComposableArrows P 0 →₀ ℤ) →ₗ[ℤ] Nerve.Ch P) := by
      apply Finsupp.lhom_ext'
      intro s
      apply LinearMap.ext_ring
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
      change Nerve.lengthProjection 2 (orderReturnHomotopyZero (Finsupp.single s 1)) = _
      rw [orderReturnHomotopyZero_single]
      exact (orderReturnHomotopyZero_fill s).choose_spec.2.1
    exact DFunLike.congr_fun he c
  on_boundary c := (by
    have he : Nerve.bdry.toIntLinearMap.comp orderReturnHomotopyZero =
        orderNerveGradedEncode 0 - orderNerveRoundTrip P 0 := by
      apply Finsupp.lhom_ext'
      intro s
      apply LinearMap.ext_ring
      simp
      rw [orderReturnHomotopyZero_single]
      exact (orderReturnHomotopyZero_fill s).choose_spec.2.2
    exact DFunLike.congr_fun he _)

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
variable {P : Type} [PartialOrder P]

theorem orderReturnHomotopyNext_fill {n : ℕ} (H : OrderReturnHomotopyStage P n)
    (s : ComposableArrows P (n + 1)) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (Set.range s.obj) ∧
      Nerve.lengthProjection (n + 3) b = b ∧ Nerve.bdry b =
        orderNerveGradedEncode (n + 1) (Finsupp.single s 1) -
          orderNerveRoundTrip P (n + 1) (Finsupp.single s 1) -
            H.map (orderSimplicialBoundary P n (Finsupp.single s 1)) := by
  apply orderNerveCarriedFill s
  · exact AddSubgroup.sub_mem _
      (AddSubgroup.sub_mem _ (orderNerveGradedEncode_single_supported (n + 1) s)
        (orderNerveRoundTrip_supported (n + 1) s))
      (orderSimplicialBoundary_map_carrier H.map H.carrier s)
  · erw [map_sub, map_sub, orderNerveGradedEncode_length, H.homogeneous]
    congr 2
    exact orderSingularToNerve_length (n + 1) _
  · erw [map_sub, map_sub, ← orderNerveGradedEncode_boundary,
      orderNerveRoundTrip_boundary, H.on_boundary, sub_self]

def orderReturnHomotopyNextMap {n : ℕ} (H : OrderReturnHomotopyStage P n) :
    (ComposableArrows P (n + 1) →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun s => (orderReturnHomotopyNext_fill H s).choose)

theorem orderReturnHomotopyNextMap_single {n : ℕ} (H : OrderReturnHomotopyStage P n)
    (s : ComposableArrows P (n + 1)) :
    orderReturnHomotopyNextMap H (Finsupp.single s 1) = (orderReturnHomotopyNext_fill H s).choose := by
  erw [orderReturnHomotopyNextMap, Finsupp.linearCombination_single, one_smul]

theorem orderReturnHomotopyNextMap_identity {n : ℕ} (H : OrderReturnHomotopyStage P n)
    (c : ComposableArrows P (n + 1) →₀ ℤ) :
    Nerve.bdry (orderReturnHomotopyNextMap H c) =
      orderNerveGradedEncode (n + 1) c - orderNerveRoundTrip P (n + 1) c -
        H.map (orderSimplicialBoundary P n c) := by
  let D : (ComposableArrows P (n + 1) →₀ ℤ) →ₗ[ℤ] (ComposableArrows P n →₀ ℤ) :=
    orderSimplicialBoundary P n
  have he : Nerve.bdry.toIntLinearMap.comp (orderReturnHomotopyNextMap H) =
      orderNerveGradedEncode (n + 1) - orderNerveRoundTrip P (n + 1) -
        H.map.comp D := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simp
    erw [orderReturnHomotopyNextMap_single]
    exact (orderReturnHomotopyNext_fill H s).choose_spec.2.2
  exact DFunLike.congr_fun he c

def orderReturnHomotopyStageNext {n : ℕ} (H : OrderReturnHomotopyStage P n) :
    OrderReturnHomotopyStage P (n + 1) where
  map := orderReturnHomotopyNextMap H
  carrier s := by
    rw (config := { transparency := .default }) [orderReturnHomotopyNextMap_single]
    exact (orderReturnHomotopyNext_fill H s).choose_spec.1
  homogeneous c := by
    have he : (Nerve.lengthProjection (n + 3)).toIntLinearMap.comp (orderReturnHomotopyNextMap H) =
        orderReturnHomotopyNextMap H := by
      apply Finsupp.lhom_ext'
      intro s
      apply LinearMap.ext_ring
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
      change Nerve.lengthProjection (n + 3) (orderReturnHomotopyNextMap H (Finsupp.single s 1)) = _
      rw (config := { transparency := .default }) [orderReturnHomotopyNextMap_single]
      exact (orderReturnHomotopyNext_fill H s).choose_spec.2.1
    exact DFunLike.congr_fun he c
  on_boundary c := by
    rw (config := { transparency := .default }) [orderReturnHomotopyNextMap_identity, orderSimplicialBoundary_squared, map_zero, sub_zero]

def orderReturnHomotopyStage (P : Type) [PartialOrder P] :
    (n : ℕ) → OrderReturnHomotopyStage P n
  | 0 => orderReturnHomotopyStageZero
  | n + 1 => orderReturnHomotopyStageNext (orderReturnHomotopyStage P n)

def orderReturnHomotopy (P : Type) [PartialOrder P] (n : ℕ) :
    (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  (orderReturnHomotopyStage P n).map

/-- Going through actual singular chains and returning to the nerve is
chain homotopic to the original simplicial chain map. -/
theorem orderReturnHomotopy_identity (n : ℕ) (c : ComposableArrows P (n + 1) →₀ ℤ) :
    Nerve.bdry (orderReturnHomotopy P (n + 1) c) =
      orderNerveGradedEncode (n + 1) c - orderNerveRoundTrip P (n + 1) c -
        orderReturnHomotopy P n (orderSimplicialBoundary P n c) :=
  orderReturnHomotopyNextMap_identity (orderReturnHomotopyStage P n) c

theorem orderReturnHomotopy_mem_inc (n : ℕ) (c : ComposableArrows P n →₀ ℤ) :
    orderReturnHomotopy P n c ∈ Nerve.Inc P :=
  orderSimplicialMap_mem_inc _ (orderReturnHomotopyStage P n).carrier c

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
variable {P : Type} [PartialOrder P]

/-- A genuine singular filling of a realized simplicial cycle produces an
actual simplicial filling, in every positive dimension. -/
theorem orderNerveExplicitSingular_reflects_boundaries (n : ℕ)
    (c : ComposableArrows P (n + 1) →₀ ℤ) (hc : orderSimplicialBoundary P n c = 0)
    (b : Chain (orderNerveRealization P) (n + 2))
    (hb : boundary (n + 1) b = (orderNerveExplicitSingularMap P).f (n + 1) c) :
    ∃ a : ComposableArrows P (n + 2) →₀ ℤ, orderSimplicialBoundary P (n + 1) a = c := by
  let w := orderSingularToNerve P (n + 2) b + orderReturnHomotopy P (n + 1) c
  have hw : w ∈ Nerve.Inc P := AddSubgroup.add_mem _
    (orderSingularToNerve_mem_inc _ _) (orderReturnHomotopy_mem_inc _ _)
  have hd : Nerve.bdry w = orderNerveGradedEncode (n + 1) c := by
    dsimp only [w]
    erw [map_add, orderSingularToNerve_boundary, hb, orderReturnHomotopy_identity,
      hc, map_zero, sub_zero]
    change orderNerveRoundTrip P (n + 1) c +
      (orderNerveGradedEncode (n + 1) c - orderNerveRoundTrip P (n + 1) c) = _
    abel
  refine ⟨orderNerveGradedDecode (n + 2) w, ?_⟩
  apply orderNerveGradedEncode_injective (n + 1)
  erw [orderNerveGradedEncode_boundary, orderNerveGradedEncode_decode _ hw,
    ← Nerve.lengthProjection_bdry, hd, orderNerveGradedEncode_length]

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Simplicial

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

/-- A genuine poset covering preserves the simplicial dimension bound upstairs. -/
theorem realization_hasDimensionLE (hf : IsPosetCover f) (d : ℕ)
    [(nerve Q).HasDimensionLE d] : (nerve P).HasDimensionLE d := by
  constructor
  intro n hn
  apply Set.eq_univ_of_forall
  intro s
  rw [SSet.mem_degenerate_iff_notMem_nonDegenerate]
  intro hs
  let t := (nerveMap hf.mono.functor).app _ s
  have ht : t ∈ (nerve Q).nonDegenerate n := by
    apply (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono t).mpr
    exact hf.strictMono.comp
      ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s).mp hs)
  have hdim := (nerve Q).dim_le_of_nonDegenerate ⟨t, ht⟩ d
  omega

end IsPosetCover
end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- The actual map on two-cycles induced by a monotone map. -/
def orderNerveCycleMap (f : P → Q) (hf : Monotone f) :
    LinearMap.ker (bdry2 (orderCx P)) →ₗ[ℤ] LinearMap.ker (bdry2 (orderCx Q)) where
  toFun c := ⟨chain2 (orderCxMap f hf) c.val, by
    change bdry2 (orderCx Q) (chain2 (orderCxMap f hf) c.val) = 0
    rw [bdry2_chain2, c.property]; exact map_zero _⟩
  map_add' c d := Subtype.ext (map_add _ _ _)
  map_smul' n c := Subtype.ext (map_smul _ _ _)

/-- The actual induced map on second integral order-nerve homology. -/
def orderNerveH2Map (f : P → Q) (hf : Monotone f) :
    OrderNerveH2 P →ₗ[ℤ] OrderNerveH2 Q :=
  (LinearMap.range (ordBoundary3Cycles P)).mapQ
    (LinearMap.range (ordBoundary3Cycles Q)) (orderNerveCycleMap f hf) (by
      intro c hc
      obtain ⟨y, rfl⟩ := hc
      exact ⟨Finsupp.mapDomain (ordTetMap f hf) y,
        Subtype.ext (chain2_ordBoundary3 f hf y).symm⟩)

/-- The induced homology map sends a cycle class to the class of its actual pushforward. -/
theorem orderNerveH2Map_class (f : P → Q) (hf : Monotone f)
    (c : OrdTri P →₀ ℤ) (hc : bdry2 (orderCx P) c = 0) :
    orderNerveH2Map f hf (orderNerveH2Class P c hc) =
      orderNerveH2Class Q (chain2 (orderCxMap f hf) c)
        (by rw [bdry2_chain2, hc]; exact map_zero _) := rfl

end FiniteChains.Comb

namespace FiniteChains.Comb
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- The genuine Mathlib chain map preserves its actual two-cycle kernel. -/
theorem mathlibOrderNerveChainMap_cycle (f : P → Q) (hf : Monotone f)
    (c : LinearMap.ker ((AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule P) 1).hom)) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule Q) 1).hom
      (((mathlibOrderNerveChainMap f hf).f 2).hom c.val) = 0 := by
  let d := (mathlibOrderNerveCycleEquiv P).symm c
  have he := congrArg Subtype.val ((mathlibOrderNerveCycleEquiv P).apply_symm_apply c)
  change (Finsupp.domLCongr (ordTriNerveEquiv P)) d.val = c.val at he
  simp only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_eq_mapDomain] at he
  have h := mathlibOrderNerveChainMap_two f hf d.val
  rw [he] at h
  rw [h, mathlibOrderNerve_d2, bdry2_chain2, d.property, map_zero,
    Finsupp.mapDomain_zero]

/-- The actual Mathlib chain map restricted to genuine two-cycles. -/
def mathlibOrderNerveCycleMap (f : P → Q) (hf : Monotone f) :
    LinearMap.ker ((AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule P) 1).hom) →ₗ[ℤ]
    LinearMap.ker ((AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule Q) 1).hom) where
  toFun c := ⟨((mathlibOrderNerveChainMap f hf).f 2).hom c.val,
    mathlibOrderNerveChainMap_cycle f hf c⟩
  map_add' c d := Subtype.ext (map_add ((mathlibOrderNerveChainMap f hf).f 2).hom c.val d.val)
  map_smul' n c := Subtype.ext (map_smul ((mathlibOrderNerveChainMap f hf).f 2).hom n c.val)

/-- The actual cycle-kernel comparison is natural under monotone maps. -/
theorem mathlibOrderNerveCycleEquiv_natural (f : P → Q) (hf : Monotone f)
    (c : LinearMap.ker (FiniteChains.Comb.bdry2 (orderCx P))) :
    mathlibOrderNerveCycleMap f hf (mathlibOrderNerveCycleEquiv P c) =
      mathlibOrderNerveCycleEquiv Q (orderNerveCycleMap f hf c) := by
  ext
  change ((mathlibOrderNerveChainMap f hf).f 2).hom
      ((Finsupp.domLCongr (ordTriNerveEquiv P)) c.val) =
    (Finsupp.domLCongr (ordTriNerveEquiv Q))
      (chain2 (orderCxMap f hf) c.val)
  simp only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_eq_mapDomain]
  exact mathlibOrderNerveChainMap_two f hf c.val

/-- The actual Mathlib cycle map preserves the actual three-boundary range. -/
theorem mathlibOrderNerveCycleMap_boundaries (f : P → Q) (hf : Monotone f) :
    LinearMap.range (mathlibOrderNerveBoundary3Cycles P) ≤
      (LinearMap.range (mathlibOrderNerveBoundary3Cycles Q)).comap
        (mathlibOrderNerveCycleMap f hf) := by
  rintro c ⟨y, rfl⟩
  obtain ⟨d, rfl⟩ := Finsupp.mapDomain_surjective (ordTetNerveEquiv P).surjective y
  refine ⟨((mathlibOrderNerveChainMap f hf).f 3).hom
    (Finsupp.mapDomain (ordTetNerveEquiv P) d), ?_⟩
  ext
  change (AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule Q) 2).hom
      (((mathlibOrderNerveChainMap f hf).f 3).hom
        (Finsupp.mapDomain (ordTetNerveEquiv P) d)) =
    ((mathlibOrderNerveChainMap f hf).f 2).hom
      ((AlgebraicTopology.AlternatingFaceMapComplex.objD
        (mathlibOrderNerveModule P) 2).hom
          (Finsupp.mapDomain (ordTetNerveEquiv P) d))
  rw [mathlibOrderNerveChainMap_three, mathlibOrderNerve_d3,
    mathlibOrderNerve_d3, mathlibOrderNerveChainMap_two, chain2_ordBoundary3]

/-- The map on genuine Mathlib differential homology quotients induced by the actual chain map. -/
def mathlibOrderNerveQuotientH2Map (f : P → Q) (hf : Monotone f) :
    (LinearMap.ker ((AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule P) 1).hom) ⧸
        LinearMap.range (mathlibOrderNerveBoundary3Cycles P)) →ₗ[ℤ]
    (LinearMap.ker ((AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule Q) 1).hom) ⧸
        LinearMap.range (mathlibOrderNerveBoundary3Cycles Q)) :=
  (LinearMap.range (mathlibOrderNerveBoundary3Cycles P)).mapQ
    (LinearMap.range (mathlibOrderNerveBoundary3Cycles Q))
    (mathlibOrderNerveCycleMap f hf) (mathlibOrderNerveCycleMap_boundaries f hf)

/-- The actual homology-quotient comparison is natural under monotone maps. -/
theorem mathlibOrderNerveH2Equiv_natural (f : P → Q) (hf : Monotone f)
    (z : OrderNerveH2 P) :
    mathlibOrderNerveQuotientH2Map f hf (mathlibOrderNerveH2Equiv P z) =
      mathlibOrderNerveH2Equiv Q (orderNerveH2Map f hf z) := by
  induction z using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk
      (mathlibOrderNerveCycleMap f hf (mathlibOrderNerveCycleEquiv P c)) =
        Submodule.Quotient.mk
          (mathlibOrderNerveCycleEquiv Q (orderNerveCycleMap f hf c))
    rw [mathlibOrderNerveCycleEquiv_natural]

/-- A proved zero homology map transports to the genuine Mathlib differential quotient map. -/
theorem mathlibOrderNerveQuotientH2Map_zero (f : P → Q) (hf : Monotone f)
    (hzero : orderNerveH2Map f hf = 0) :
    mathlibOrderNerveQuotientH2Map f hf = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := (mathlibOrderNerveH2Equiv P).surjective z
  rw [mathlibOrderNerveH2Equiv_natural, hzero, LinearMap.zero_apply, (mathlibOrderNerveH2Equiv Q).map_zero,
    LinearMap.zero_apply]

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory CategoryTheory.Limits
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- The actual monotone-map chain morphism on the degree-two differential segment. -/
def mathlibOrderNerveShortComplexMap (f : P → Q) (hf : Monotone f) :
    mathlibOrderNerveShortComplex P ⟶ mathlibOrderNerveShortComplex Q where
  τ₁ := (mathlibOrderNerveChainMap f hf).f 3
  τ₂ := (mathlibOrderNerveChainMap f hf).f 2
  τ₃ := (mathlibOrderNerveChainMap f hf).f 1
  comm₁₂ := by
    have h := (mathlibOrderNerveChainMap f hf).comm 3 2
    simpa only [mathlibOrderNerveShortComplex, AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, AlgebraicTopology.AlternatingFaceMapComplex.objD] using h
  comm₂₃ := by
    have h := (mathlibOrderNerveChainMap f hf).comm 2 1
    simpa only [mathlibOrderNerveShortComplex, AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, AlgebraicTopology.AlternatingFaceMapComplex.objD] using h

/-- Actual cycle and quotient maps form Mathlib's verified homology map data. -/
def mathlibOrderNerveLeftHomologyMapData (f : P → Q) (hf : Monotone f) :
    ShortComplex.LeftHomologyMapData (mathlibOrderNerveShortComplexMap f hf)
      (mathlibOrderNerveShortComplex P).moduleCatLeftHomologyData
      (mathlibOrderNerveShortComplex Q).moduleCatLeftHomologyData where
  φK := ModuleCat.ofHom (mathlibOrderNerveCycleMap f hf)
  φH := ModuleCat.ofHom (mathlibOrderNerveQuotientH2Map f hf)
  commi := rfl
  commf' := by
    apply ModuleCat.hom_ext
    ext c
    apply Subtype.ext
    have h := congrArg (fun m :
      ModuleCat.of ℤ (ComposableArrows P 3 →₀ ℤ) ⟶
        ModuleCat.of ℤ (ComposableArrows Q 2 →₀ ℤ) => m c)
      (mathlibOrderNerveShortComplexMap f hf).comm₁₂
    exact h.symm
  commπ := rfl

/-- The actual categorical homology map is conjugate to the genuine differential quotient map. -/
theorem mathlibOrderNerve_homologyMap_eq (f : P → Q) (hf : Monotone f) :
    ShortComplex.homologyMap (mathlibOrderNerveShortComplexMap f hf) =
      (mathlibOrderNerveShortComplex P).moduleCatHomologyIso.hom ≫
        ModuleCat.ofHom (mathlibOrderNerveQuotientH2Map f hf) ≫
          (mathlibOrderNerveShortComplex Q).moduleCatHomologyIso.inv :=
  (mathlibOrderNerveLeftHomologyMapData f hf).homologyMap_eq

/-- A proved zero order-homology map gives the zero actual categorical homology map. -/
theorem mathlibOrderNerve_homologyMap_zero (f : P → Q) (hf : Monotone f)
    (hzero : orderNerveH2Map f hf = 0) :
    ShortComplex.homologyMap (mathlibOrderNerveShortComplexMap f hf) = 0 := by
  rw [mathlibOrderNerve_homologyMap_eq,
    mathlibOrderNerveQuotientH2Map_zero f hf hzero]
  simp

/-- The categorical homology comparison commutes with the actual monotone-map homology map. -/
theorem mathlibOrderNerveCategoricalH2Equiv_natural (f : P → Q) (hf : Monotone f)
    (z : OrderNerveH2 P) :
    (ShortComplex.homologyMap (mathlibOrderNerveShortComplexMap f hf)).hom
      (mathlibOrderNerveCategoricalH2Equiv P z) =
        mathlibOrderNerveCategoricalH2Equiv Q (orderNerveH2Map f hf z) := by
  rw [mathlibOrderNerve_homologyMap_eq]
  change (mathlibOrderNerveShortComplex Q).moduleCatHomologyIso.symm.toLinearEquiv
    (mathlibOrderNerveQuotientH2Map f hf
      ((mathlibOrderNerveShortComplex P).moduleCatHomologyIso.toLinearEquiv
        ((mathlibOrderNerveShortComplex P).moduleCatHomologyIso.toLinearEquiv.symm
          (mathlibOrderNerveH2Equiv P z)))) = _
  rw [LinearEquiv.apply_symm_apply, mathlibOrderNerveH2Equiv_natural]
  rfl

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- The actual differential-segment identification commutes with chain maps. -/
theorem mathlibOrderNerveShortComplexIso_natural (f : P → Q) (hf : Monotone f) :
    mathlibOrderNerveShortComplexMap f hf ≫ (mathlibOrderNerveShortComplexIso Q).hom =
    (mathlibOrderNerveShortComplexIso P).hom ≫
      (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map
        (mathlibOrderNerveChainMap f hf) := by
  unfold mathlibOrderNerveShortComplexIso
  have h := (HomologicalComplex.natIsoSc' (ModuleCat ℤ) (ComplexShape.down ℕ) 3 2 1
    ((ComplexShape.down ℕ).prev_eq' (by decide))
    ((ComplexShape.down ℕ).next_eq' (by decide))).inv.naturality
      (mathlibOrderNerveChainMap f hf)
  simp only [Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  dsimp only [HomologicalComplex.isoSc', Iso.app] at h ⊢
  rw [← h]
  simp only [← Category.assoc]
  congr 1

/-- The segment and full-chain-complex homology maps agree under the proved identification. -/
theorem mathlibOrderNerveComplex_homologyMap_natural (f : P → Q) (hf : Monotone f) :
    ShortComplex.homologyMap (mathlibOrderNerveShortComplexMap f hf) ≫
      ((ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso
        (mathlibOrderNerveShortComplexIso Q)).hom =
    ((ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso
        (mathlibOrderNerveShortComplexIso P)).hom ≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map
        (mathlibOrderNerveChainMap f hf) := by
  change (ShortComplex.homologyFunctor (ModuleCat ℤ)).map _ ≫
      (ShortComplex.homologyFunctor (ModuleCat ℤ)).map _ =
    (ShortComplex.homologyFunctor (ModuleCat ℤ)).map _ ≫
      (ShortComplex.homologyFunctor (ModuleCat ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp, mathlibOrderNerveShortComplexIso_natural]

/-- A proved zero order-homology map induces zero on the actual full Mathlib chain complex. -/
theorem mathlibOrderNerveComplex_homologyMap_zero (f : P → Q) (hf : Monotone f)
    (hzero : orderNerveH2Map f hf = 0) :
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map
      (mathlibOrderNerveChainMap f hf) = 0 := by
  apply (cancel_epi (((ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso
    (mathlibOrderNerveShortComplexIso P)).hom)).mp
  rw [← mathlibOrderNerveComplex_homologyMap_natural,
    mathlibOrderNerve_homologyMap_zero f hf hzero]
  simp

/-- The actual order-cell homology equivalence is natural on full chain-complex homology. -/
theorem mathlibOrderNerveComplexH2Equiv_natural (f : P → Q) (hf : Monotone f)
    (z : OrderNerveH2 P) :
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map
      (mathlibOrderNerveChainMap f hf)).hom (mathlibOrderNerveComplexH2Equiv P z) =
      mathlibOrderNerveComplexH2Equiv Q (orderNerveH2Map f hf z) := by
  have h := congrArg (fun k : (mathlibOrderNerveShortComplex P).homology ⟶
      (AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule Q)).homology 2 =>
        k (mathlibOrderNerveCategoricalH2Equiv P z))
    (mathlibOrderNerveComplex_homologyMap_natural f hf)
  change (((ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso
      (mathlibOrderNerveShortComplexIso Q)).hom)
        ((ShortComplex.homologyMap (mathlibOrderNerveShortComplexMap f hf)).hom
          (mathlibOrderNerveCategoricalH2Equiv P z)) =
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map
      (mathlibOrderNerveChainMap f hf)).hom (mathlibOrderNerveComplexH2Equiv P z) at h
  rw [mathlibOrderNerveCategoricalH2Equiv_natural] at h
  exact h.symm

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory

/-- The realization unit induces an actual map to Mathlib integral singular homology.
This definition makes no claim that the map is an isomorphism. -/
def orderNerveSingularH2Comparison (P : Type) [PartialOrder P] :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).homology 2 ⟶
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) :=
  orderNerveRealizationH2Comparison P ≫
    (FiniteChains.freeSingularHomologyIso (orderNerveRealization P) 2).hom

/-- The actual singular-homology comparison is natural for monotone maps. -/
theorem orderNerveSingularH2Comparison_natural {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
      (mathlibOrderNerveChainMap f hf) ≫ orderNerveSingularH2Comparison Q =
    orderNerveSingularH2Comparison P ≫
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).map (orderNerveRealizationMap f hf)) := by
  unfold orderNerveSingularH2Comparison
  rw [← Category.assoc, orderNerveRealizationH2Comparison_natural, Category.assoc]
  change _ ≫ ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
      (AlgebraicTopology.AlternatingFaceMapComplex.map
        (Functor.whiskerRight (TopCat.toSSet.map (orderNerveRealizationMap f hf))
          (ModuleCat.free ℤ))) ≫ _) = _
  rw [FiniteChains.freeSingularHomologyIso_natural, Category.assoc]

/-- A zero order-homology pushdown annihilates all singular classes in the comparison image. -/
theorem orderNerveSingularH2Comparison_pushdown_zero {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (hzero : orderNerveH2Map f hf = 0) :
    orderNerveSingularH2Comparison P ≫
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).map (orderNerveRealizationMap f hf)) = 0 := by
  rw [← orderNerveSingularH2Comparison_natural,
    mathlibOrderNerveComplex_homologyMap_zero f hf hzero]
  exact CategoryTheory.Limits.zero_comp

/-- The actual order-cell second-homology classes map to genuine singular classes. -/
def orderCellSingularH2Map (P : Type) [PartialOrder P] :
    OrderNerveH2 P →ₗ[ℤ]
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) :=
  (orderNerveSingularH2Comparison P).hom.comp
    (mathlibOrderNerveComplexH2Equiv P).toLinearMap

/-- Naturality of the comparison from actual order-cell classes to singular classes. -/
theorem orderCellSingularH2Map_natural {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (z : OrderNerveH2 P) :
    ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).map (orderNerveRealizationMap f hf)).hom
        (orderCellSingularH2Map P z)) = orderCellSingularH2Map Q (orderNerveH2Map f hf z) := by
  have h := congrArg (fun k :
      (AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).homology 2 ⟶
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
          (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization Q)) =>
      k (mathlibOrderNerveComplexH2Equiv P z))
    (orderNerveSingularH2Comparison_natural f hf)
  change (orderNerveSingularH2Comparison Q).hom
      (((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
        (mathlibOrderNerveChainMap f hf)).hom (mathlibOrderNerveComplexH2Equiv P z)) =
    ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).map (orderNerveRealizationMap f hf)).hom
        (orderCellSingularH2Map P z)) at h
  rw [mathlibOrderNerveComplexH2Equiv_natural] at h
  exact h.symm

end FiniteChains.Comb
end

namespace FiniteChains.Comb
open TopologicalSingular

def orderSingularCarrierChains {P : Type} [PartialOrder P] {n : ℕ}
    (σ : Simplex (orderNerveRealization P) n) (k : ℕ) :
    Submodule ℤ (Chain (orderNerveRealization P) k) :=
  subChains (orderNerveRealizationSubcomplex P (orderNerveSingularCarrier σ) :
    Set (orderNerveRealization P)) k

theorem orderSingularCarrierChains_face {P : Type} [PartialOrder P] {n : ℕ}
    (σ : Simplex (orderNerveRealization P) (n + 1)) (i : Fin (n + 2)) (k : ℕ) :
    orderSingularCarrierChains (face i σ) k ≤ orderSingularCarrierChains σ k :=
  subChains_mono (orderNerveRealizationSubcomplex_mono (orderNerveSingularCarrier_face σ i)) k

theorem orderSingularCarrierChains_single {P : Type} [PartialOrder P] {n : ℕ}
    (σ : Simplex (orderNerveRealization P) n) (r : ℤ) :
    Finsupp.single σ r ∈ orderSingularCarrierChains σ n :=
  single_mem_subChains _ n σ r (orderNerveSingularSimplex_mem_carrier σ)

theorem orderSingularCarrierChains_cycle_bounds {P : Type} [PartialOrder P] {n : ℕ}
    (σ : Simplex (orderNerveRealization P) n)
    (hσ : (orderNerveSingularStarIndices σ).Nonempty) (k : ℕ)
    (c : Chain (orderNerveRealization P) (k + 1))
    (hc : c ∈ orderSingularCarrierChains σ (k + 1)) (hz : boundary k c = 0) :
    ∃ b : Chain (orderNerveRealization P) (k + 2),
      b ∈ orderSingularCarrierChains σ (k + 2) ∧ boundary (k + 1) b = c := by
  letI := orderNerveSingularCarrier_subcomplex_contractible σ hσ
  exact contractible_supported_cycle_bounds _ k c hc hz

theorem orderSingularCarrierChains_zero_bounds {P : Type} [PartialOrder P] {n : ℕ}
    (σ : Simplex (orderNerveRealization P) n)
    (hσ : (orderNerveSingularStarIndices σ).Nonempty)
    (c : Chain (orderNerveRealization P) 0)
    (hc : c ∈ orderSingularCarrierChains σ 0) (hz : augmentation c = 0) :
    ∃ b : Chain (orderNerveRealization P) 1,
      b ∈ orderSingularCarrierChains σ 1 ∧ boundary 0 b = c := by
  letI := orderNerveSingularCarrier_subcomplex_contractible σ hσ
  exact connected_supported_zero_bounds _ c hc hz

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory TopologicalSingular SingularSubdivision

def orderSmallVertexSimplex {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 0) : Simplex (orderNerveRealization P) 0 :=
  orderNerveSingularSimplex (ComposableArrows.mk₀ (orderSmallChosenVertex σ))


def orderSmallSingularApproximation0 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 0 →ₗ[ℤ] Chain (orderNerveRealization P) 0 :=
  (Finsupp.linearCombination ℤ (fun σ => Finsupp.single (orderSmallVertexSimplex σ) 1)).comp
    (orderSmallChainEquiv P 0).toLinearMap

theorem orderSmallSingularApproximation0_single {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 0) :
    orderSmallSingularApproximation0 (orderSmallSingle σ 1) =
      Finsupp.single (orderSmallVertexSimplex σ) 1 := by
  rw [← orderSmallChainEquiv_symm_single]
  simp only [orderSmallSingularApproximation0, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Finsupp.linearCombination_single, one_smul]

/-- The first comparison homotopy stays inside the simplex's actual CW carrier. -/
theorem orderSmallHomotopyZeroFill_exists {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 0) :
    ∃ b : Chain (orderNerveRealization P) 1, b ∈ orderSingularCarrierChains σ.val 1 ∧
      boundary 0 b = Finsupp.single σ.val 1 - Finsupp.single (orderSmallVertexSimplex σ) 1 := by
  apply orderSingularCarrierChains_zero_bounds σ.val σ.property
  · exact Submodule.sub_mem _ (orderSingularCarrierChains_single σ.val 1)
      (by
        apply single_mem_subChains
        intro z
        apply orderNerveSingularSimplex_supported
        intro i
        fin_cases i
        exact orderSmallChosenVertex_mem σ)
  · simp

def orderSmallHomotopy0 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 0 →ₗ[ℤ] Chain (orderNerveRealization P) 1 :=
  (Finsupp.linearCombination ℤ (fun σ => (orderSmallHomotopyZeroFill_exists σ).choose)).comp
    (orderSmallChainEquiv P 0).toLinearMap

theorem orderSmallHomotopy0_single {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 0) :
    orderSmallHomotopy0 (orderSmallSingle σ 1) = (orderSmallHomotopyZeroFill_exists σ).choose := by
  rw [← orderSmallChainEquiv_symm_single]
  simp only [orderSmallHomotopy0, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Finsupp.linearCombination_single, one_smul]

theorem orderSmallHomotopy0_carrier {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 0) :
    orderSmallHomotopy0 (orderSmallSingle σ 1) ∈ orderSingularCarrierChains σ.val 1 := by
  rw [orderSmallHomotopy0_single]
  grind

theorem orderSmallHomotopy0_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 0) :
    boundary 0 (orderSmallHomotopy0 c) = c.val - orderSmallSingularApproximation0 c := by
  have he : (boundary 0).comp orderSmallHomotopy0 =
      (smallChains (orderNerveRealizationOpenStar P) 0).subtype - orderSmallSingularApproximation0 := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, orderSmallHomotopy0_single,
      orderSmallSingularApproximation0_single]
    exact (orderSmallHomotopyZeroFill_exists σ).choose_spec.2
  exact DFunLike.congr_fun he c

end FiniteChains.Comb

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
open scoped Classical

theorem orderSmallToNerve1_single_carrier {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 1) :
    orderSmallToNerve1 (orderSmallSingle σ 1) ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) := by
  rw [orderSmallToNerve1_single, one_smul]
  exact (orderSmallOneFill_exists σ).choose_spec.1

theorem orderSmallToNerve1_length {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 1) :
    Nerve.lengthProjection 2 (orderSmallToNerve1 c) = orderSmallToNerve1 c := by
  have he : (Nerve.lengthProjection 2).toIntLinearMap.comp orderSmallToNerve1 =
      (orderSmallToNerve1 : smallChains (orderNerveRealizationOpenStar P) 1 →ₗ[ℤ] Nerve.Ch P) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      orderSmallToNerve1_single, one_smul]
    exact (orderSmallOneFill_exists σ).choose_spec.2.1
  exact DFunLike.congr_fun he c

/-- The boundary assigned to a small two-simplex has an actual triangle
filling in its own carrier. -/
theorem orderSmallTwoFill_exists {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 2) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) ∧
      Nerve.lengthProjection 3 b = b ∧ Nerve.bdry b =
        orderSmallToNerve1 (smallBoundary (orderNerveRealizationOpenStar P) 1 (orderSmallSingle σ 1)) := by
  let c := orderSmallToNerve1
    (smallBoundary (orderNerveRealizationOpenStar P) 1 (orderSmallSingle σ 1))
  have hc : c ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) := by
    dsimp only [c]
    rw [orderSmallSingle_boundary, map_sum]
    apply AddSubgroup.sum_mem
    intro i _
    rw [map_zsmul]
    apply AddSubgroup.zsmul_mem
    exact Nerve.incOn_mono (fun _ hp => orderSmallSimplexFace_carrier i σ hp)
      (orderSmallToNerve1_single_carrier (orderSmallSimplexFace i σ))
  have hcycle : Nerve.bdry c = 0 := by
    rw [orderSmallToNerve1_boundary]
    have he : smallBoundary (orderNerveRealizationOpenStar P) 0
        (smallBoundary (orderNerveRealizationOpenStar P) 1 (orderSmallSingle σ 1)) = 0 :=
      DFunLike.congr_fun (smallBoundary_squared (orderNerveRealizationOpenStar P) 0)
        (orderSmallSingle σ 1)
    rw [he, map_zero]
  obtain ⟨b, hb, he⟩ := orderNerveSingularCarrier_nerve_acyclic σ.val σ.property c hc hcycle
  refine ⟨Nerve.lengthProjection 3 b, Nerve.lengthProjection_mem_incOn _ hb,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  rw [← Nerve.lengthProjection_bdry, he]
  exact orderSmallToNerve1_length _

def orderSmallTwoFill {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 2) : Nerve.Ch P := (orderSmallTwoFill_exists σ).choose

def orderSmallToNerve2 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 2 →ₗ[ℤ] Nerve.Ch P :=
  (Finsupp.linearCombination ℤ orderSmallTwoFill).comp (orderSmallChainEquiv P 2).toLinearMap

theorem orderSmallToNerve2_single {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 2) (r : ℤ) :
    orderSmallToNerve2 (orderSmallSingle σ r) = r • orderSmallTwoFill σ := by
  rw [← orderSmallChainEquiv_symm_single]
  simp only [orderSmallToNerve2, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Finsupp.linearCombination_single]

theorem orderSmallToNerve2_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 2) :
    Nerve.bdry (orderSmallToNerve2 c) =
      orderSmallToNerve1 (smallBoundary (orderNerveRealizationOpenStar P) 1 c) := by
  have he : Nerve.bdry.toIntLinearMap.comp orderSmallToNerve2 =
      orderSmallToNerve1.comp (smallBoundary (orderNerveRealizationOpenStar P) 1) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      orderSmallToNerve2_single, one_smul]
    exact (orderSmallTwoFill_exists σ).choose_spec.2.2
  exact DFunLike.congr_fun he c

theorem orderSmallToNerve2_length {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 2) :
    Nerve.lengthProjection 3 (orderSmallToNerve2 c) = orderSmallToNerve2 c := by
  have he : (Nerve.lengthProjection 3).toIntLinearMap.comp orderSmallToNerve2 =
      (orderSmallToNerve2 : smallChains (orderNerveRealizationOpenStar P) 2 →ₗ[ℤ] Nerve.Ch P) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      orderSmallToNerve2_single, one_smul]
    exact (orderSmallTwoFill_exists σ).choose_spec.2.1
  exact DFunLike.congr_fun he c

theorem orderSmallToNerve2_mem_inc {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 2) : orderSmallToNerve2 c ∈ Nerve.Inc P := by
  obtain ⟨d, rfl⟩ := (orderSmallChainEquiv P 2).symm.surjective c
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simpa using (Nerve.Inc P).add_mem hd he
  | single σ r =>
    rw [orderSmallChainEquiv_symm_single, orderSmallToNerve2_single]
    exact (Nerve.Inc P).zsmul_mem
      (Nerve.incOn_le_inc _ (orderSmallTwoFill_exists σ).choose_spec.1) r

/-- A concrete order-cell two-chain assigned to each star-small singular chain. -/
def orderSmallCellularApproximation2 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 2 →ₗ[ℤ] (OrdTri P →₀ ℤ) :=
  decodeOrdNerve2.toIntLinearMap.comp orderSmallToNerve2

/-- The assigned order-cell chain is a cycle whenever the original small
singular chain is a cycle. Homological comparison still requires a homotopy. -/
theorem orderSmallCellularApproximation2_cycle {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 2)
    (hc : smallBoundary (orderNerveRealizationOpenStar P) 1 c = 0) :
    bdry2 (orderCx P) (orderSmallCellularApproximation2 c) = 0 := by
  apply (ordNerveChain2_cycle_iff _).mp
  change Nerve.bdry (ordNerveChain2 (decodeOrdNerve2 (orderSmallToNerve2 c))) = 0
  rw [ordNerveChain2_decode (orderSmallToNerve2_mem_inc c), orderSmallToNerve2_length,
    orderSmallToNerve2_boundary, hc, map_zero]

end FiniteChains.Comb

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision

theorem orderSmallToNerve2_single_carrier {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 2) :
    orderSmallToNerve2 (orderSmallSingle σ 1) ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) := by
  rw [orderSmallToNerve2_single, one_smul]
  exact (orderSmallTwoFill_exists σ).choose_spec.1

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

def orderCellSingularChain1 {P : Type} [PartialOrder P] :
    (OrdEdge P →₀ ℤ) →ₗ[ℤ] Chain (orderNerveRealization P) 1 :=
  ((orderNerveExplicitSingularMap P).f 1).hom.comp
    (Finsupp.lmapDomain ℤ ℤ (ordEdgeNerveEquiv P))

def orderCellSingularChain2 {P : Type} [PartialOrder P] :
    (OrdTri P →₀ ℤ) →ₗ[ℤ] Chain (orderNerveRealization P) 2 :=
  ((orderNerveExplicitSingularMap P).f 2).hom.comp
    (Finsupp.lmapDomain ℤ ℤ (ordTriNerveEquiv P))

theorem orderCellSingularChain1_single {P : Type} [PartialOrder P] (e : OrdEdge P) (r : ℤ) :
    orderCellSingularChain1 (Finsupp.single e r) =
      Finsupp.single (orderNerveSingularSimplex (ordEdgeNerveEquiv P e)) r := by
  change (orderNerveExplicitSingularMap P).f 1
    (Finsupp.mapDomain (ordEdgeNerveEquiv P) (Finsupp.single e r)) = _
  rw (config := { transparency := .default }) [Finsupp.mapDomain_single]
  exact orderNerveExplicitSingularMap_single _ _ _

theorem orderCellSingularChain2_single {P : Type} [PartialOrder P] (t : OrdTri P) (r : ℤ) :
    orderCellSingularChain2 (Finsupp.single t r) =
      Finsupp.single (orderNerveSingularSimplex (ordTriNerveEquiv P t)) r := by
  change (orderNerveExplicitSingularMap P).f 2
    (Finsupp.mapDomain (ordTriNerveEquiv P) (Finsupp.single t r)) = _
  rw (config := { transparency := .default }) [Finsupp.mapDomain_single]
  exact orderNerveExplicitSingularMap_single _ _ _

/-- The canonical realized cellular two-chain has exactly its singular boundary. -/
theorem orderCellSingularChain2_boundary {P : Type} [PartialOrder P] (c : OrdTri P →₀ ℤ) :
    boundary 1 (orderCellSingularChain2 c) = orderCellSingularChain1 (bdry2 (orderCx P) c) := by
  have h := congrArg (fun f => f (Finsupp.mapDomain (ordTriNerveEquiv P) c))
    ((orderNerveExplicitSingularMap P).comm 2 1).symm
  erw [complex_d, AlternatingFaceMapComplex.obj_d_eq] at h
  change (orderNerveExplicitSingularMap P).f 1
      ((AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1).hom
        (Finsupp.mapDomain (ordTriNerveEquiv P) c)) =
    boundary 1 (orderCellSingularChain2 c) at h
  erw [mathlibOrderNerve_d2] at h
  exact h.symm

end FiniteChains.Comb
end

namespace FiniteChains.Comb
open CategoryTheory TopologicalSingular


/-- Realizing an increasing one-chain preserves every vertex carrier. -/
theorem orderCellSingularDecode1_supported {P : Type} [PartialOrder P]
    (A : Set P) {c : Nerve.Ch P} (hc : c ∈ Nerve.IncOn A) :
    orderCellSingularChain1 (decodeOrdNerve1 c) ∈
      subChains (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) 1 := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    erw [decodeOrdNerve1_of]
    exact (by
      cases l with
      | nil => simp [decodeOrdEdgeList]
      | cons a l =>
        cases l with
        | nil => simp [decodeOrdEdgeList]
        | cons b l =>
          cases l with
          | cons c l => simp [decodeOrdEdgeList]
          | nil =>
            have hab : a ≤ b := by simpa [List.isChain_cons] using (hl.1)
            erw [decodeOrdEdgeList, dif_pos hab, orderCellSingularChain1_single]
            apply single_mem_subChains
            intro z
            apply orderNerveSingularSimplex_supported
            intro i
            fin_cases i
            · exact (hl.2) a (by simp)
            · exact (hl.2) b (by simp))
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | neg x _ hx => simp_all


/-- Realizing an increasing two-chain preserves every vertex carrier. -/
theorem orderCellSingularDecode2_supported {P : Type} [PartialOrder P]
    (A : Set P) {c : Nerve.Ch P} (hc : c ∈ Nerve.IncOn A) :
    orderCellSingularChain2 (decodeOrdNerve2 c) ∈
      subChains (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) 2 := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    erw [decodeOrdNerve2_of]
    exact (by
      cases l with
      | nil => simp [decodeOrdTriList]
      | cons a l =>
        cases l with
        | nil => simp [decodeOrdTriList]
        | cons b l =>
          cases l with
          | nil => simp [decodeOrdTriList]
          | cons c l =>
            cases l with
            | cons d l => simp [decodeOrdTriList]
            | nil =>
              have habc : a ≤ b ∧ b ≤ c := by simpa [List.isChain_cons] using (hl.1)
              erw [decodeOrdTriList, dif_pos habc, orderCellSingularChain2_single]
              apply single_mem_subChains
              intro z
              apply orderNerveSingularSimplex_supported
              intro i
              fin_cases i
              · exact (hl.2) a (by simp)
              · exact (hl.2) b (by simp)
              · exact (hl.2) c (by simp))
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | neg x _ hx => simp_all

end FiniteChains.Comb

namespace FiniteChains.Comb
open FreeAbelianGroup
universe u
variable {P : Type u}

@[simp] theorem decodeOrdNerve0_of (l : List P) :
    decodeOrdNerve0 (of l) = decodeOrdVertexList l := lift_apply_of _ _

theorem ordNerveChain0_decode (c : Nerve.Ch P) :
    ordNerveChain0 (decodeOrdNerve0 c) = Nerve.lengthProjection 1 c := by
  apply Nerve.ext_apply
    (F := ordNerveChain0.toAddMonoidHom.comp decodeOrdNerve0)
  intro l
  cases l with
  | nil => simp [decodeOrdVertexList]
  | cons a l =>
    cases l with
    | nil => simp [decodeOrdVertexList, ordNerveChain0]
    | cons b l => simp [decodeOrdVertexList]

end FiniteChains.Comb

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision

def orderSmallCellularApproximation0 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 0 →ₗ[ℤ] (P →₀ ℤ) :=
  decodeOrdNerve0.toIntLinearMap.comp orderSmallToNerve0

def orderSmallCellularApproximation1 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 1 →ₗ[ℤ] (OrdEdge P →₀ ℤ) :=
  decodeOrdNerve1.toIntLinearMap.comp orderSmallToNerve1

theorem orderSmallCellularApproximation0_single {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 0) (r : ℤ) :
    orderSmallCellularApproximation0 (orderSmallSingle σ r) =
      Finsupp.single (orderSmallChosenVertex σ) r := by simp_all [orderSmallToNerve0_single, map_zsmul, decodeOrdNerve0_of, decodeOrdVertexList, orderSmallCellularApproximation0]

theorem orderSmallToNerve1_mem_inc {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 1) : orderSmallToNerve1 c ∈ Nerve.Inc P := by
  obtain ⟨d, rfl⟩ := (orderSmallChainEquiv P 1).symm.surjective c
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simpa using (Nerve.Inc P).add_mem hd he
  | single σ r =>
    rw [orderSmallChainEquiv_symm_single, orderSmallToNerve1_single]
    exact (Nerve.Inc P).zsmul_mem
      (Nerve.incOn_le_inc _ (orderSmallOneFill_exists σ).choose_spec.1) r

theorem orderSmallCellularApproximation1_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 1) :
    bdry1 (orderCx P) (orderSmallCellularApproximation1 c) =
      orderSmallCellularApproximation0 (smallBoundary (orderNerveRealizationOpenStar P) 0 c) := by
  apply ordNerveChain0_injective
  rw [ordNerveChain0_bdry1]
  change Nerve.bdry (ordNerveChain1 (decodeOrdNerve1 (orderSmallToNerve1 c))) =
    ordNerveChain0 (decodeOrdNerve0 (orderSmallToNerve0 _))
  rw [ordNerveChain1_decode (orderSmallToNerve1_mem_inc c), orderSmallToNerve1_length,
    orderSmallToNerve1_boundary, ordNerveChain0_decode, orderSmallToNerve0_length]

theorem orderSmallCellularApproximation2_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 2) :
    bdry2 (orderCx P) (orderSmallCellularApproximation2 c) =
      orderSmallCellularApproximation1 (smallBoundary (orderNerveRealizationOpenStar P) 1 c) := by
  apply ordNerveChain1_injective
  rw [ordNerveChain1_bdry2]
  change Nerve.bdry (ordNerveChain2 (decodeOrdNerve2 (orderSmallToNerve2 c))) =
    ordNerveChain1 (decodeOrdNerve1 (orderSmallToNerve1 _))
  rw [ordNerveChain2_decode (orderSmallToNerve2_mem_inc c), orderSmallToNerve2_length,
    orderSmallToNerve2_boundary, ordNerveChain1_decode (orderSmallToNerve1_mem_inc _),
    orderSmallToNerve1_length]

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
open CategoryTheory TopologicalSingular SingularSubdivision

def orderCellSingularChain0 {P : Type} [PartialOrder P] :
    (P →₀ ℤ) →ₗ[ℤ] Chain (orderNerveRealization P) 0 :=
  Finsupp.lmapDomain ℤ ℤ (fun p => orderNerveSingularSimplex (ComposableArrows.mk₀ p))

theorem orderCellSingularChain0_single {P : Type} [PartialOrder P] (p : P) (r : ℤ) :
    orderCellSingularChain0 (Finsupp.single p r) =
      Finsupp.single (orderNerveSingularSimplex (ComposableArrows.mk₀ p)) r :=
  Finsupp.mapDomain_single

/-- The realized oriented edge has its target minus its source as boundary. -/
theorem orderCellSingularChain1_boundary {P : Type} [PartialOrder P] (c : OrdEdge P →₀ ℤ) :
    boundary 0 (orderCellSingularChain1 c) = orderCellSingularChain0 (P := P) (bdry1 (orderCx P) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e r =>
    have h0 : (nerve P).δ 0 (ordEdgeNerveEquiv P e) =
        ComposableArrows.mk₀ e.val.2 := by
      apply CategoryTheory.Functor.ext (fun i => by fin_cases i; rfl)
    have h1 : (nerve P).δ 1 (ordEdgeNerveEquiv P e) =
        ComposableArrows.mk₀ e.val.1 := by
      apply CategoryTheory.Functor.ext (fun i => by fin_cases i; rfl)
    erw [orderCellSingularChain1_single, boundary_single, Fin.sum_univ_two]
    simp only [orderNerveSingularSimplex_face, h0, h1, Fin.val_zero, Fin.val_one,
      pow_zero, pow_one, one_smul, neg_smul]
    erw [bdry1_single, map_smul, map_sub,
      orderCellSingularChain0_single, orderCellSingularChain0_single]
    simp [orderCx, sub_eq_add_neg]

theorem orderSmallSingularApproximation0_realization {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 0) :
    orderCellSingularChain0 (orderSmallCellularApproximation0 c) =
      orderSmallSingularApproximation0 c := by
  have he : orderCellSingularChain0.comp orderSmallCellularApproximation0 =
      (orderSmallSingularApproximation0 : smallChains (orderNerveRealizationOpenStar P) 0 →ₗ[ℤ] _) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, orderSmallCellularApproximation0_single,
      orderCellSingularChain0_single, orderSmallSingularApproximation0_single]
    rfl
  exact DFunLike.congr_fun he c

end FiniteChains.Comb
end

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision

def orderSmallSingularApproximation1 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 1 →ₗ[ℤ] Chain (orderNerveRealization P) 1 :=
  orderCellSingularChain1.comp orderSmallCellularApproximation1

def orderSmallSingularApproximation2 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 2 →ₗ[ℤ] Chain (orderNerveRealization P) 2 :=
  orderCellSingularChain2.comp orderSmallCellularApproximation2

theorem orderSmallSingularApproximation1_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 1) :
    boundary 0 (orderSmallSingularApproximation1 c) =
      orderSmallSingularApproximation0 (smallBoundary (orderNerveRealizationOpenStar P) 0 c) := by simp_all [orderCellSingularChain1_boundary, orderSmallCellularApproximation1_boundary, orderSmallSingularApproximation0_realization, orderSmallSingularApproximation1]

theorem orderSmallSingularApproximation2_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 2) :
    boundary 1 (orderSmallSingularApproximation2 c) =
      orderSmallSingularApproximation1 (smallBoundary (orderNerveRealizationOpenStar P) 1 c) := by simp_all [orderCellSingularChain2_boundary, orderSmallCellularApproximation2_boundary, orderSmallSingularApproximation2, orderSmallSingularApproximation1]

theorem orderSmallSingularApproximation1_carrier {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 1) :
    orderSmallSingularApproximation1 (orderSmallSingle σ 1) ∈
      orderSingularCarrierChains σ.val 1 := orderCellSingularDecode1_supported _ (orderSmallToNerve1_single_carrier σ)

theorem orderSmallSingularApproximation2_carrier {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 2) :
    orderSmallSingularApproximation2 (orderSmallSingle σ 1) ∈
      orderSingularCarrierChains σ.val 2 := orderCellSingularDecode2_supported _ (orderSmallToNerve2_single_carrier σ)

/-- A carried linear map sends every simplex boundary into the parent carrier. -/
theorem orderSmallBoundary_map_carrier {P : Type} [PartialOrder P] {n k : ℕ}
    (H : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Chain (orderNerveRealization P) k)
    (hH : ∀ τ : OrderSmallSimplex P n,
      H (orderSmallSingle τ 1) ∈ orderSingularCarrierChains τ.val k)
    (σ : OrderSmallSimplex P (n + 1)) :
    H (smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ 1)) ∈
      orderSingularCarrierChains σ.val k := by
  rw [orderSmallSingle_boundary, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  exact orderSingularCarrierChains_face σ.val i k (hH (orderSmallSimplexFace i σ))

end FiniteChains.Comb

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision

/-- Fill the comparison discrepancy on a one-simplex after correcting its endpoints. -/
theorem orderSmallHomotopyOneFill_exists {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 1) :
    ∃ b : Chain (orderNerveRealization P) 2, b ∈ orderSingularCarrierChains σ.val 2 ∧
      boundary 1 b = Finsupp.single σ.val 1 -
        orderSmallSingularApproximation1 (orderSmallSingle σ 1) -
        orderSmallHomotopy0 (smallBoundary (orderNerveRealizationOpenStar P) 0 (orderSmallSingle σ 1)) := by
  apply orderSingularCarrierChains_cycle_bounds σ.val σ.property 0
  · exact Submodule.sub_mem _
      (Submodule.sub_mem _ (orderSingularCarrierChains_single σ.val 1)
        (orderSmallSingularApproximation1_carrier σ))
      (orderSmallBoundary_map_carrier orderSmallHomotopy0 orderSmallHomotopy0_carrier σ)
  · rw [map_sub, map_sub, orderSmallSingularApproximation1_boundary, orderSmallHomotopy0_boundary]
    exact sub_self _

def orderSmallHomotopy1 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 1 →ₗ[ℤ] Chain (orderNerveRealization P) 2 :=
  (Finsupp.linearCombination ℤ (fun σ => (orderSmallHomotopyOneFill_exists σ).choose)).comp
    (orderSmallChainEquiv P 1).toLinearMap

theorem orderSmallHomotopy1_single {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 1) :
    orderSmallHomotopy1 (orderSmallSingle σ 1) = (orderSmallHomotopyOneFill_exists σ).choose := by
  have he := (orderSmallChainEquiv P 1).apply_symm_apply (Finsupp.single σ 1)
  rw [orderSmallChainEquiv_symm_single] at he
  change (Finsupp.linearCombination ℤ (fun τ : OrderSmallSimplex P 1 =>
    (orderSmallHomotopyOneFill_exists τ).choose))
      ((orderSmallChainEquiv P 1) (orderSmallSingle σ 1)) = _
  simp_all

theorem orderSmallHomotopy1_carrier {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 1) :
    orderSmallHomotopy1 (orderSmallSingle σ 1) ∈ orderSingularCarrierChains σ.val 2 := by
  rw [orderSmallHomotopy1_single]
  grind

theorem orderSmallHomotopy1_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 1) :
    boundary 1 (orderSmallHomotopy1 c) = c.val - orderSmallSingularApproximation1 c -
      orderSmallHomotopy0 (smallBoundary (orderNerveRealizationOpenStar P) 0 c) := by
  have he : (boundary 1).comp orderSmallHomotopy1 =
      (smallChains (orderNerveRealizationOpenStar P) 1).subtype - orderSmallSingularApproximation1 -
        orderSmallHomotopy0.comp (smallBoundary (orderNerveRealizationOpenStar P) 0) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, orderSmallHomotopy1_single]
    exact (orderSmallHomotopyOneFill_exists σ).choose_spec.2
  exact DFunLike.congr_fun he c

end FiniteChains.Comb

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision

/-- Fill the comparison discrepancy on a two-simplex after correcting its edges. -/
theorem orderSmallHomotopyTwoFill_exists {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 2) :
    ∃ b : Chain (orderNerveRealization P) 3, b ∈ orderSingularCarrierChains σ.val 3 ∧
      boundary 2 b = Finsupp.single σ.val 1 -
        orderSmallSingularApproximation2 (orderSmallSingle σ 1) -
        orderSmallHomotopy1 (smallBoundary (orderNerveRealizationOpenStar P) 1 (orderSmallSingle σ 1)) := by
  apply orderSingularCarrierChains_cycle_bounds σ.val σ.property 1
  · exact Submodule.sub_mem _
      (Submodule.sub_mem _ (orderSingularCarrierChains_single σ.val 1)
        (orderSmallSingularApproximation2_carrier σ))
      (orderSmallBoundary_map_carrier orderSmallHomotopy1 orderSmallHomotopy1_carrier σ)
  · rw [map_sub, map_sub, orderSmallSingularApproximation2_boundary, orderSmallHomotopy1_boundary]
    have hd : smallBoundary (orderNerveRealizationOpenStar P) 0
        (smallBoundary (orderNerveRealizationOpenStar P) 1 (orderSmallSingle σ 1)) = 0 :=
      DFunLike.congr_fun (smallBoundary_squared (orderNerveRealizationOpenStar P) 0)
        (orderSmallSingle σ 1)
    rw [hd, map_zero, sub_zero]
    exact sub_self _

def orderSmallHomotopy2 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 2 →ₗ[ℤ] Chain (orderNerveRealization P) 3 :=
  (Finsupp.linearCombination ℤ (fun σ => (orderSmallHomotopyTwoFill_exists σ).choose)).comp
    (orderSmallChainEquiv P 2).toLinearMap



/-- Realizing the cellular approximation preserves the actual singular class
of every star-small two-cycle. -/
theorem orderSmallCellularApproximation2_homologous {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 2)
    (hc : smallBoundary (orderNerveRealizationOpenStar P) 1 c = 0) :
    ∃ b : Chain (orderNerveRealization P) 3,
      boundary 2 b = c.val - orderCellSingularChain2 (orderSmallCellularApproximation2 c) := by
  refine ⟨orderSmallHomotopy2 c, ?_⟩
  rw [(show boundary 2 (orderSmallHomotopy2 c) = c.val - orderSmallSingularApproximation2 c -
      orderSmallHomotopy1 (smallBoundary (orderNerveRealizationOpenStar P) 1 c) by
    have he : (boundary 2).comp orderSmallHomotopy2 =
        (smallChains (orderNerveRealizationOpenStar P) 2).subtype - orderSmallSingularApproximation2 -
          orderSmallHomotopy1.comp (smallBoundary (orderNerveRealizationOpenStar P) 1) := by
      apply orderSmallSingle_spans
      intro σ
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, (show orderSmallHomotopy2 (orderSmallSingle σ 1) = (orderSmallHomotopyTwoFill_exists σ).choose by
        have he := (orderSmallChainEquiv P 2).apply_symm_apply (Finsupp.single σ 1)
        rw [orderSmallChainEquiv_symm_single] at he
        change (Finsupp.linearCombination ℤ (fun τ : OrderSmallSimplex P 2 =>
          (orderSmallHomotopyTwoFill_exists τ).choose))
            ((orderSmallChainEquiv P 2) (orderSmallSingle σ 1)) = _
        simp_all)]
      exact (orderSmallHomotopyTwoFill_exists σ).choose_spec.2
    exact DFunLike.congr_fun he c), hc, map_zero, sub_zero]
  rfl

end FiniteChains.Comb

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision

/-- Every actual singular two-cycle in an arbitrary order realization is
homologous to a realized finite cellular two-cycle. No local finiteness is used. -/
theorem orderNerveRealization_twoCycle_cellularRepresentative {P : Type} [PartialOrder P]
    (c : Chain (orderNerveRealization P) 2) (hc : boundary 1 c = 0) :
    ∃ z : OrdTri P →₀ ℤ, bdry2 (orderCx P) z = 0 ∧
      ∃ b : Chain (orderNerveRealization P) 3, boundary 2 b = c - orderCellSingularChain2 z := by
  obtain ⟨d, hd, hz, a, ha⟩ := orderNerveRealization_exists_small_cycle P 1 c hc
  let d' : smallChains (orderNerveRealizationOpenStar P) 2 := ⟨d, hd⟩
  have hd' : smallBoundary (orderNerveRealizationOpenStar P) 1 d' = 0 := Subtype.ext hz
  obtain ⟨b, hb⟩ := orderSmallCellularApproximation2_homologous d' hd'
  refine ⟨orderSmallCellularApproximation2 d', orderSmallCellularApproximation2_cycle d' hd',
    b - a, ?_⟩
  rw [map_sub, hb, ha]
  abel

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

/-- The actual realization unit is surjective on second singular homology. -/

theorem orderNerveSingularH2Comparison_factor (P : Type) [PartialOrder P] :
    orderNerveSingularH2Comparison P =
      HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) 2 ≫
        (homologyMathlibIso (orderNerveRealization P) 2).hom := by
  have he : orderNerveExplicitSingularMap P ≫ (complexMathlibIso (orderNerveRealization P)).hom =
      orderNerveRealizationChainComparison P ≫
        (FiniteChains.freeSingularChainComplexIso (orderNerveRealization P)).hom := by
    simp [orderNerveExplicitSingularMap, complexMathlibIso, Category.assoc]
  change (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
      (orderNerveRealizationChainComparison P) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
        (FiniteChains.freeSingularChainComplexIso (orderNerveRealization P)).hom =
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
      (orderNerveExplicitSingularMap P) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
        (complexMathlibIso (orderNerveRealization P)).hom
  grind

theorem orderNerveSingularH2Comparison_epi (P : Type) [PartialOrder P] :
    Epi (orderNerveSingularH2Comparison P) := by
  erw [orderNerveSingularH2Comparison_factor]
  letI := (show Epi (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) 2) by
    unfold HomologicalComplex.homologyMap HomologicalComplex.shortComplexFunctor
    apply shortComplex_homologyMap_epi_of_representatives
    intro c hc
    change ((complex (orderNerveRealization P)).d 2 ((ComplexShape.down ℕ).next 2)) c = 0 at hc
    erw [ChainComplex.next_nat_succ, complex_d] at hc
    obtain ⟨z, hz, b, hb⟩ := orderNerveRealization_twoCycle_cellularRepresentative c hc
    refine ⟨Finsupp.mapDomain (ordTriNerveEquiv P) z, ?_, ?_⟩
    · change (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).d 2
        ((ComplexShape.down ℕ).next 2) _ = 0
      erw [ChainComplex.next_nat_succ, AlternatingFaceMapComplex.obj_d_eq]
      erw [mathlibOrderNerve_d2, hz, Finsupp.mapDomain_zero]
    · change ∃ a : (complex (orderNerveRealization P)).X ((ComplexShape.down ℕ).prev 2),
        (complex (orderNerveRealization P)).d ((ComplexShape.down ℕ).prev 2) 2 a = _
      erw [ChainComplex.prev]
      refine ⟨b, ?_⟩
      erw [complex_d]
      exact hb)
  infer_instance

theorem orderCellSingularH2Map_surjective (P : Type) [PartialOrder P] :
    Function.Surjective (orderCellSingularH2Map P) := by
  intro x
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective _).mp (orderNerveSingularH2Comparison_epi P) x
  obtain ⟨z, rfl⟩ := (mathlibOrderNerveComplexH2Equiv P).surjective y
  exact ⟨z, hy⟩

/-- A zero cellular pushdown annihilates every actual singular second-homology
class, without any remaining comparison-image hypothesis. -/
theorem orderNerveSingularH2Map_zero_of_orderH2Map_zero {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (hzero : orderNerveH2Map f hf = 0) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (orderNerveRealizationMap f hf)) = 0 := by
  letI := orderNerveSingularH2Comparison_epi P
  apply (cancel_epi (orderNerveSingularH2Comparison P)).mp
  erw [orderNerveSingularH2Comparison_pushdown_zero f hf hzero, Limits.comp_zero]

end FiniteChains.Comb
end

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

/-- The canonical realization comparison is injective on every positive
singular homology group. -/
theorem orderNerveExplicitSingularHomology_mono (P : Type) [PartialOrder P] (n : ℕ) :
    Mono (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) (n + 1)) := by
  unfold HomologicalComplex.homologyMap HomologicalComplex.shortComplexFunctor
  apply shortComplex_homologyMap_mono_of_reflects_boundaries
  intro c hc hb
  change (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).d (n + 1)
    ((ComplexShape.down ℕ).next (n + 1)) c = 0 at hc
  rw [ChainComplex.next_nat_succ, AlternatingFaceMapComplex.obj_d_eq] at hc
  change ∃ b : (complex (orderNerveRealization P)).X ((ComplexShape.down ℕ).prev (n + 1)),
    (complex (orderNerveRealization P)).d ((ComplexShape.down ℕ).prev (n + 1)) (n + 1) b = _ at hb
  rw [ChainComplex.prev] at hb
  obtain ⟨b, hb⟩ := hb
  rw [complex_d] at hb
  obtain ⟨a, ha⟩ := orderNerveExplicitSingular_reflects_boundaries n c hc b hb
  change ∃ a : (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).X
    ((ComplexShape.down ℕ).prev (n + 1)),
    (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).d
      ((ComplexShape.down ℕ).prev (n + 1)) (n + 1) a = c
  rw [ChainComplex.prev]
  refine ⟨a, ?_⟩
  rw [AlternatingFaceMapComplex.obj_d_eq]
  exact ha



/-- An actual isomorphism, with the original natural comparison as forward map. -/
def orderCellSingularH2Equiv (P : Type) [PartialOrder P] :
    OrderNerveH2 P ≃ₗ[ℤ]
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
        (orderNerveRealization P)) :=
  LinearEquiv.ofBijective (orderCellSingularH2Map P)
    ⟨(by
      have h := (ModuleCat.mono_iff_injective _).mp (show Mono (orderNerveSingularH2Comparison P) by
        rw [orderNerveSingularH2Comparison_factor]
        letI := orderNerveExplicitSingularHomology_mono P 1
        infer_instance)
      exact h.comp (mathlibOrderNerveComplexH2Equiv P).injective), orderCellSingularH2Map_surjective P⟩

theorem orderCellSingularH2Equiv_natural {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (z : OrderNerveH2 P) :
    ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (orderNerveRealizationMap f hf)).hom (orderCellSingularH2Equiv P z)) =
        orderCellSingularH2Equiv Q (orderNerveH2Map f hf z) :=
  orderCellSingularH2Map_natural f hf z

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology

theorem orderH2Map_zero_of_orderNerveSingularH2Map_zero {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (hz : (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (orderNerveRealizationMap f hf)) = 0) : orderNerveH2Map f hf = 0 := by
  apply LinearMap.ext
  intro z
  apply (orderCellSingularH2Equiv Q).injective
  rw [← orderCellSingularH2Equiv_natural f hf, hz]
  simp

end FiniteChains.Comb

namespace FiniteChains.Comb
open TopologicalSingular
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- The zero-map test on order H2 is exactly finite three-fillability of every
pushed-forward two-cycle. -/
theorem orderNerveH2Map_eq_zero_iff (f : P → Q) (hf : Monotone f) :
    orderNerveH2Map f hf = 0 ↔
      ∀ (c : OrdTri P →₀ ℤ), bdry2 (orderCx P) c = 0 →
        ∃ b : OrdTet Q →₀ ℤ, ordBoundary3 b = chain2 (orderCxMap f hf) c := by
  constructor
  · intro hz c hc
    have h := congrArg (fun g : OrderNerveH2 P →ₗ[ℤ] OrderNerveH2 Q =>
      g (orderNerveH2Class P c hc)) hz
    erw [orderNerveH2Map_class] at h
    exact (orderNerveH2Class_eq_zero_iff Q _ _).mp h
  · intro hb
    apply LinearMap.ext
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H c =>
      erw [orderNerveH2Map_class]
      exact (orderNerveH2Class_eq_zero_iff Q _ _).mpr (hb c.val c.property)

/-- Exact bridge between actual topological pi2 and actual order homology on
the constructed universal covers. The lifting and Hurewicz comparisons are proved. -/
theorem killsPi2_orderRealization_iff_universalH2_zero
    (f : P → Q) (hf : Monotone f) (a : P)
    (hP : IsConnected (orderCx P)) (hQ : IsConnected (orderCx Q)) :
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩ ↔
      orderNerveH2Map (uOrderMap f hf a) (uOrderMap f hf a).monotone = 0 := by
  letI := uOrderRealization_simplyConnected a
  letI := uOrderRealization_simplyConnected (f a)
  let F : C(orderNerveRealization P, orderNerveRealization Q) :=
    ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩
  let G : C(orderNerveRealization (UOrder P a), orderNerveRealization (UOrder Q (f a))) :=
    ⟨orderNerveRealizationMap (uOrderMap f hf a) (uOrderMap f hf a).monotone,
      (orderNerveRealizationMap (uOrderMap f hf a) (uOrderMap f hf a).monotone).hom.continuous⟩
  have he : (uOrderRealizationProjection (f a)).comp G =
      F.comp (uOrderRealizationProjection a) := by
    apply ContinuousMap.ext
    exact uOrderMap_realization_projection f hf a
  have hk : Whitehead.KillsPi2 F ↔ Whitehead.KillsPi2 G := by
    erw [← Whitehead.killsPi2_covering_precomp_iff (uOrderRealizationProjection a)
      (uOrderRealizationProjection_isCoveringMap a hP)
      (uOrderRealizationProjection_surjective a hP) F, ← he]
    exact Whitehead.killsPi2_covering_postcomp_iff G (uOrderRealizationProjection (f a))
      (uOrderRealizationProjection_isCoveringMap (f a) hQ)
  erw [hk, killsPi2_iff_singularH2_map_eq_zero
    (orderNerveRealizationVertex (P := UOrder P a) (UV.base (orderCx P) a)) G]
  exact ⟨orderH2Map_zero_of_orderNerveSingularH2Map_zero _ _,
    orderNerveSingularH2Map_zero_of_orderH2Map_zero _ _⟩

/-- A cycle-level criterion for the genuine pi2-killing condition in Challenge. -/
theorem killsPi2_orderRealization_iff_universal_cycles_bound
    (f : P → Q) (hf : Monotone f) (a : P)
    (hP : IsConnected (orderCx P)) (hQ : IsConnected (orderCx Q)) :
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩ ↔
      ∀ (c : OrdTri (UOrder P a) →₀ ℤ), bdry2 (orderCx (UOrder P a)) c = 0 →
        ∃ b : OrdTet (UOrder Q (f a)) →₀ ℤ, ordBoundary3 b =
          chain2 (orderCxMap (uOrderMap f hf a) (uOrderMap f hf a).monotone) c := by
  erw [killsPi2_orderRealization_iff_universalH2_zero f hf a hP hQ,
    orderNerveH2Map_eq_zero_iff]

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- The genuine universal-cover endpoint strictly raises comparable vertices. -/
theorem uOrderEnd_strictMono : StrictMono (uOrderEnd (P := P) (a := a)) := by
  intro v w h
  apply lt_of_le_of_ne (uOrderEnd_monotone h.le)
  intro he
  exact (ne_of_lt h) (uOrder_up_injective (le_refl v) h.le he)

end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u}

/-- Dimension two persists in the actual path-class universal cover. -/

theorem presPos_cover_normalized_three_boundary_zero (w : J → List (α × Bool))
    (a : PresPos w) (y : OrdTet (UOrder (PresPos w) a) →₀ ℤ) :
    normalizeOrdChain2 (ordBoundary3 y) = 0 := by
  haveI := (show IsEmpty (StrictOrdTet (UOrder (PresPos w) a)) by
    refine ⟨fun t => ?_⟩
    have h01 := presPosDimension_strictMono w (uOrderEnd_strictMono t.2.1)
    have h12 := presPosDimension_strictMono w (uOrderEnd_strictMono t.2.2.1)
    have h23 := presPosDimension_strictMono w (uOrderEnd_strictMono t.2.2.2)
    have hb := presPosDimension_le_two w (uOrderEnd t.1.2.2.2)
    omega)
  have hy : normalizeOrdChain3 y = 0 := by
    ext t
    exact isEmptyElim t
  rw [normalizeOrdChain2_ordBoundary3, hy, map_zero]

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)

/-- An actual single coordinate triangle has exactly its single lifted-apex coefficient. -/
theorem presCoverRelatorChain_single_triangle (p : PresCoverRelator w f) (n : ℤ) :
    presCoverRelatorChain w f hf hpos
      (Finsupp.single (presCoverRelatorTriangle w f hf hpos p) n) = Finsupp.single p n := by
  exact Finsupp.comapDomain_single (presCoverRelatorTriangle w f hf hpos) p n
    (presCoverRelatorTriangle_injective w f hf hpos).injOn

/-- Actual triangles outside all coordinate-triangle fibres contribute no relator coefficients. -/
theorem presCoverRelatorChain_single_off_coordinates (t : StrictOrdTri P) (n : ℤ)
    (ht : ∀ j, (strictOrderCxMap f hf.strictMono).onF t ≠ presRelatorFirstTriangle w hpos j) :
    presCoverRelatorChain w f hf hpos (Finsupp.single t n) = 0 := by
  ext p
  rw [presCoverRelatorChain_apply]
  have hn : t ≠ presCoverRelatorTriangle w f hf hpos p := by
    intro he
    apply ht p.val.2
    rw [he]
    exact presCoverRelatorTriangle_projection w f hf hpos p
  simp [hn]

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
universe u
variable {α β J K P Q : Type u} [PartialOrder P] [PartialOrder Q]
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  (h : PresWordEmbedding w v) (hw : ∀ j, 0 < (w j).length) (hv : ∀ j, 0 < (v j).length)

/-- Renaming a presentation preserves its distinguished relator triangle. -/
theorem firstTriangle_map (j : J) :
    (strictOrderCxMap h.posMap h.posMap.strictMono).onF (presRelatorFirstTriangle w hw j) =
      presRelatorFirstTriangle v hv (h.cell j) := rfl

/-- A triangle mapped to a distinguished relator triangle was already one,
with the corresponding original relator label. -/
theorem firstTriangle_preimage (t : StrictOrdTri (PresPos w)) (j : K)
    (ht : (strictOrderCxMap h.posMap h.posMap.strictMono).onF t = presRelatorFirstTriangle v hv j) :
    ∃ i : J, h.cell i = j ∧ t = presRelatorFirstTriangle w hw i := by
  have he : h.posFun t.val.2.2 = apexOf v j := congrArg (fun s => s.val.2.2) ht
  have hj : ∃ i : J, h.cell i = j := by
    cases hp : t.val.2.2 with
    | inr i => exact ⟨i, Sum.inr.inj (by simpa only [hp, posFun, apexOf, ConeAdj.apex] using he)⟩
    | inl p => cases p <;> simp only [hp, posFun] at he <;> cases he
  obtain ⟨i, rfl⟩ := hj
  refine ⟨i, rfl, ?_⟩
  apply strictOrderCxMap_onF_injective h.posMap h.posMap.strictMono h.posMap.injective
  exact ht.trans (h.firstTriangle_map hw hv i).symm

variable (f : P → PresPos w) (hf : IsPosetCover f)
  (g : Q → PresPos v) (hg : IsPosetCover g)
  (k : P → Q) (hk : StrictMono k) (hc : ∀ p, g (k p) = h.posMap (f p))

/-- The actual map of lifted relator apices, with labels renamed by the inclusion. -/
def coverRelatorMap (p : PresCoverRelator w f) : PresCoverRelator v g :=
  ⟨(k p.val.1, h.cell p.val.2), (hc p.val.1).trans (congrArg h.posMap p.property)⟩

include hc in
theorem coverTriangle_projection (t : StrictOrdTri P) :
    (strictOrderCxMap g hg.strictMono).onF ((strictOrderCxMap k hk).onF t) =
      (strictOrderCxMap h.posMap h.posMap.strictMono).onF
        ((strictOrderCxMap f hf.strictMono).onF t) := by
  apply Subtype.ext
  exact Prod.ext (hc _) (Prod.ext (hc _) (hc _))

/-- The lift respects the distinguished triangles even when the induced group
map, and hence the map of universal-cover vertices, is not injective. -/
theorem coverRelatorTriangle_map (p : PresCoverRelator w f) :
    (strictOrderCxMap k hk).onF (presCoverRelatorTriangle w f hf hw p) =
      presCoverRelatorTriangle v g hg hv (h.coverRelatorMap f g k hc p) := by
  apply presCoverRelatorTriangle_unique v g hg hv
  · erw [h.coverTriangle_projection f hf g hg k hk hc,
      presCoverRelatorTriangle_projection, h.firstTriangle_map]
    rfl
  · rfl

/-- Every finite relator-coordinate chain transforms by the actual lifted map.
No injectivity or surjectivity of the map between covers is assumed. -/
theorem coverRelatorChain_map (c : StrictOrdTri P →₀ ℤ) :
    presCoverRelatorChain v g hg hv (chain2 (strictOrderCxMap k hk) c) =
      Finsupp.mapDomain (h.coverRelatorMap f g k hc) (presCoverRelatorChain w f hf hw c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc' hd' =>
    simp only [map_add, Finsupp.mapDomain_add, hc', hd']
  | single t n =>
    change presCoverRelatorChain v g hg hv
      (Finsupp.mapDomain (strictOrderCxMap k hk).onF (Finsupp.single t n)) = _
    erw [Finsupp.mapDomain_single]
    by_cases ht : ∃ j, (strictOrderCxMap f hf.strictMono).onF t = presRelatorFirstTriangle w hw j
    · obtain ⟨j, hj⟩ := ht
      let p : PresCoverRelator w f :=
        ⟨(t.val.2.2, j), congrArg (fun s : StrictOrdTri (PresPos w) => s.val.2.2) hj⟩
      have he : t = presCoverRelatorTriangle w f hf hw p :=
        presCoverRelatorTriangle_unique w f hf hw p t hj rfl
      rw (config := { transparency := .default }) [he, h.coverRelatorTriangle_map hw hv f hf g hg k hk hc,
        presCoverRelatorChain_single_triangle, presCoverRelatorChain_single_triangle,
        Finsupp.mapDomain_single]
    · rw (config := { transparency := .default }) [presCoverRelatorChain_single_off_coordinates w f hf hw t n
        (fun j hj => ht ⟨j, hj⟩), Finsupp.mapDomain_zero]
      apply presCoverRelatorChain_single_off_coordinates
      intro j hj
      rw (config := { transparency := .default }) [h.coverTriangle_projection f hf g hg k hk hc] at hj
      obtain ⟨i, _, hi⟩ := h.firstTriangle_preimage hw hv _ j hj
      exact ht ⟨i, hi⟩

end FiniteChains.PresModel.PresWordEmbedding
end

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
universe u t s
variable {α β J K : Type u} {G : Type t} {H : Type s} [Group G] [Group H]
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  (h : PresWordEmbedding w v) (a : α → G) (b : β → H) (φ : G →* H)
  (hb : ∀ i, b (h.gen i) = φ (a i))

include hb in
theorem wordVal_map (l : List (α × Bool)) :
    wordVal b (l.map (fun p => (h.gen p.1, p.2))) = φ (wordVal a l) := by
  have he : (FreeGroup.lift b).comp (FreeGroup.map h.gen) = φ.comp (FreeGroup.lift a) := by
    apply FreeGroup.ext_hom
    intro i
    simp [hb]
  exact DFunLike.congr_fun he (FreeGroup.mk l)

include hb in
theorem prefixVal_map (j : J) (k : ℕ) :
    prefixVal v b (h.cell j) k = φ (prefixVal w a j k) := by
  unfold prefixVal
  rw [h.word, ← List.map_take]
  exact h.wordVal_map a b φ hb _

include hb in
theorem roseVal_map (p q : Rose α) :
    roseVal b (h.roseMap p) (h.roseMap q) = φ (roseVal a p q) := by
  cases p <;> cases q <;> simp [roseMap, Function.Embedding.coeFn_mk, roseVal, hb, apply_ite]
  split_ifs <;> simp_all

include hb in
theorem trivVal_map (j : J) (k : ℕ) (c : CPos) :
    trivVal v b (h.cell j) k c = φ (trivVal w a j k c) := by
  have ha : aFun v (h.cell j, k, CPos.cedgL) = h.roseMap (aFun w (j, k, CPos.cedgL)) :=
    h.attaching_map (j, k, CPos.cedgL)
  have hr : roseVal b Rose.base (aFun v (h.cell j, k, CPos.cedgL)) =
      φ (roseVal a Rose.base (aFun w (j, k, CPos.cedgL))) := by
    rw [ha]
    exact h.roseVal_map a b φ hb Rose.base _
  cases c <;> simp only [trivVal, h.prefixVal_map a b φ hb, hr, map_mul, map_inv]

def cylinderFun : CylBase w → CylBase v
  | .inl p => .inl (h.roseMap p)
  | .inr p => .inr (h.circleFun p)

theorem posMap_inl (p : CylBase w) : h.posMap (.inl p) = .inl (h.cylinderFun p) := by
  cases p <;> rfl

theorem cylinderFun_retraction (p : CylBase w) :
    cylRetr (aHom v) (h.cylinderFun p) = h.roseMap (cylRetr (aHom w) p) := by
  cases p with
  | inl p => rfl
  | inr p => exact h.attaching_map p

variable (hw : ∀ j, wordVal a (w j) = 1) (hv : ∀ j, wordVal b (v j) = 1)

include hb in
/-- The complete presentation cocycle is natural under literal word embeddings. -/
theorem presCoc_map (p q : PresPos w) :
    (presCoc v b hv).val (h.posMap p) (h.posMap q) = φ ((presCoc w a hw).val p q) := by
  cases p with
  | inr j =>
    cases q with
    | inr k => exact (map_one φ).symm
    | inl q =>
      rw [h.posMap_inl]
      exact (map_one φ).symm
  | inl p =>
    cases q with
    | inl q =>
      rw [h.posMap_inl, h.posMap_inl]
      change roseVal b (cylRetr (aHom v) (h.cylinderFun p))
        (cylRetr (aHom v) (h.cylinderFun q)) =
          φ (roseVal a (cylRetr (aHom w) p) (cylRetr (aHom w) q))
      rw [h.cylinderFun_retraction, h.cylinderFun_retraction]
      exact h.roseVal_map a b φ hb _ _
    | inr j =>
      cases p with
      | inl r => exact (map_one φ).symm
      | inr c => exact h.trivVal_map a b φ hb c.1 c.2.1 c.2.2

include hb in
theorem readGerm_map (e : (orderCx (PresPos w)).E × Bool) :
    (presCoc v b hv).readGerm ((orderCxMap h.posMap h.posMap.monotone).onE e.1, e.2) =
      φ ((presCoc w a hw).readGerm e) := by
  rcases e with ⟨e, s⟩
  cases s <;> simp only [OrdCocycle.readGerm, Bool.false_eq_true, if_false, if_true]
  · rw [map_inv]
    exact congrArg Inv.inv (h.presCoc_map a b φ hb hw hv _ _)
  · exact h.presCoc_map a b φ hb hw hv _ _

include hb in
theorem readPath_map (p : List ((orderCx (PresPos w)).E × Bool)) :
    (presCoc v b hv).readPath (mapPath (orderCxMap h.posMap h.posMap.monotone) p) =
      φ ((presCoc w a hw).readPath p) := by
  induction p with
  | nil => simp
  | cons e p ih =>
    change (presCoc v b hv).readPath
      (((orderCxMap h.posMap h.posMap.monotone).onE e.1, e.2) ::
        mapPath (orderCxMap h.posMap h.posMap.monotone) p) = _
    rw [OrdCocycle.readPath_cons, OrdCocycle.readPath_cons,
      h.readGerm_map a b φ hb hw hv, ih, map_mul]

include hb in
/-- Naturality holds on the actual path-class universal cover, not just on loops. -/
theorem readVertex_map (x : PresPos w) (p : UV (orderCx (PresPos w)) x) :
    (presCoc v b hv).readVertex (h.posMap x)
      (@univLiftV (orderCx (PresPos w)) (orderCx (PresPos v)) x
        (orderCxMap h.posMap h.posMap.monotone) p) =
        φ ((presCoc w a hw).readVertex x p) := by
  induction p using Quotient.inductionOn with
  | h p => exact h.readPath_map a b φ hb hw hv p.val

end FiniteChains.PresModel.PresWordEmbedding

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
variable {α β J K : Type}
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  (h : PresWordEmbedding w v)

/-- The actual functorial lift to the two path-class universal covers. -/
def universalMap : UOrder (PresPos w) (ptBase w) →o UOrder (PresPos v) (ptBase v) :=
  uOrderMap h.posMap h.posMap.monotone (ptBase w)

theorem universalMap_end (p : UOrder (PresPos w) (ptBase w)) :
    uOrderEnd (h.universalMap p) = h.posMap (uOrderEnd p) :=
  uOrderMap_end h.posMap h.posMap.monotone (ptBase w) p

/-- Comparable distinct vertices remain distinct, even when the lift identifies
different vertices over the same source base vertex. -/
theorem universalMap_strictMono : StrictMono h.universalMap := by
  intro p q hpq
  apply lt_of_le_of_ne (h.universalMap.monotone hpq.le)
  intro he
  have hh  :=
    (h.universalMap_end p).symm.trans ((congrArg uOrderEnd he).trans (h.universalMap_end q))
  exact (ne_of_lt (uOrderEnd_strictMono hpq)) (h.posMap.injective hh)

def universalRelatorMap :
    PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)) →
      PresCoverRelator v (uOrderEnd (P := PresPos v) (a := ptBase v)) :=
  h.coverRelatorMap uOrderEnd uOrderEnd h.universalMap h.universalMap_end

theorem universalRelatorChain_map (hw : ∀ j, 0 < (w j).length) (hv : ∀ k, 0 < (v k).length)
    (c : StrictOrdTri (UOrder (PresPos w) (ptBase w)) →₀ ℤ) :
    presCoverRelatorChain v uOrderEnd (presUniversalEnd_isPosetCover v hv) hv
      (chain2 (strictOrderCxMap h.universalMap h.universalMap_strictMono) c) =
        Finsupp.mapDomain h.universalRelatorMap
          (presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hw) hw c) :=
  h.coverRelatorChain_map hw hv uOrderEnd (presUniversalEnd_isPosetCover w hw)
    uOrderEnd (presUniversalEnd_isPosetCover v hv) h.universalMap
    h.universalMap_strictMono h.universalMap_end c

variable (ρ : J → FreeGroup α) (σ : K → FreeGroup β)
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hv : ∀ j, FreeGroup.mk (v j) = σ j)

include hw hv in
theorem relator_compat (j : J) : σ (h.cell j) = FreeGroup.map h.gen (ρ j) := by
  rw [← hv (h.cell j), h.word]
  change FreeGroup.map h.gen (FreeGroup.mk (w j)) = FreeGroup.map h.gen (ρ j)
  rw [hw]

/-- The actual induced homomorphism of presented groups. -/
def groupHom : PresGroup ρ →* PresGroup σ :=
  presInclGroupHom h.gen ρ σ h.cell (h.relator_compat ρ σ hw hv)

@[simp] theorem groupHom_mk (x : FreeGroup α) :
    h.groupHom ρ σ hw hv (QuotientGroup.mk x) = QuotientGroup.mk (FreeGroup.map h.gen x) := rfl

/-- The lifted path class has the actual induced group coordinate. -/
theorem universal_reading_map (p : UOrder (PresPos w) (ptBase w)) :
    (presGroupCocycle σ v hv).readVertex (ptBase v) (h.universalMap p) =
      h.groupHom ρ σ hw hv ((presGroupCocycle ρ w hw).readVertex (ptBase w) p) :=
  h.readVertex_map (fun i => (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ))
    (fun i => (QuotientGroup.mk (FreeGroup.of i) : PresGroup σ)) (h.groupHom ρ σ hw hv)
    (fun _ => rfl) (presGroup_wordVal_eq_one ρ w hw) (presGroup_wordVal_eq_one σ v hv)
    (ptBase w) p

theorem universalRelatorGroupEquiv_map (hwp : ∀ j, 0 < (w j).length)
    (hvp : ∀ j, 0 < (v j).length)
    (p : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w))) :
    presUniversalRelatorGroupEquiv σ v hv hvp (h.universalRelatorMap p) =
      Prod.map (h.groupHom ρ σ hw hv) h.cell (presUniversalRelatorGroupEquiv ρ w hw hwp p) := by
  apply Prod.ext
  · exact h.universal_reading_map ρ σ hw hv p.val.1
  · rfl

/-- The full finite relator-coordinate chains commute with the actual lift,
including summation over group elements identified by the induced homomorphism. -/
theorem universalRelatorGroupChainEquiv_map (hwp : ∀ j, 0 < (w j).length)
    (hvp : ∀ j, 0 < (v j).length)
    (c : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)) →₀ ℤ) :
    presUniversalRelatorGroupChainEquiv σ v hv hvp (Finsupp.mapDomain h.universalRelatorMap c) =
      Finsupp.mapDomain (Prod.map (h.groupHom ρ σ hw hv) h.cell)
        (presUniversalRelatorGroupChainEquiv ρ w hw hwp c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [Finsupp.mapDomain_add, map_add, hc, hd]
  | single p n =>
    rw [Finsupp.mapDomain_single]
    simp only [presUniversalRelatorGroupChainEquiv, Finsupp.domLCongr_single,
      Finsupp.mapDomain_single, h.universalRelatorGroupEquiv_map ρ σ hw hv hwp hvp]

theorem universalRelatorChain_group_map (hwp : ∀ j, 0 < (w j).length)
    (hvp : ∀ j, 0 < (v j).length)
    (c : StrictOrdTri (UOrder (PresPos w) (ptBase w)) →₀ ℤ) :
    presUniversalRelatorGroupChainEquiv σ v hv hvp
      (presCoverRelatorChain v uOrderEnd (presUniversalEnd_isPosetCover v hvp) hvp
        (chain2 (strictOrderCxMap h.universalMap h.universalMap_strictMono) c)) =
      Finsupp.mapDomain (Prod.map (h.groupHom ρ σ hw hv) h.cell)
        (presUniversalRelatorGroupChainEquiv ρ w hw hwp
          (presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hwp) hwp c)) := by
  rw [h.universalRelatorChain_map, h.universalRelatorGroupChainEquiv_map]

end FiniteChains.PresModel.PresWordEmbedding

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
variable {α β J K : Type}
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  (h : PresWordEmbedding w v) (hw : ∀ j, 0 < (w j).length) (hv : ∀ k, 0 < (v k).length)

include hw hv in
/-- Dimension two removes all genuine three-boundaries in the universal
presentation model. Thus its actual pi2 map is zero exactly when the strict
universal two-cycle map is zero. -/
theorem killsPi2_iff_strict_cycles_zero :
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap h.posMap h.posMap.monotone,
        (orderNerveRealizationMap h.posMap h.posMap.monotone).hom.continuous⟩ ↔
      ∀ c : StrictOrdTri (UOrder (PresPos w) (ptBase w)) →₀ ℤ,
        Comb.bdry2 (strictOrderCx (UOrder (PresPos w) (ptBase w))) c = 0 →
          chain2 (strictOrderCxMap h.universalMap h.universalMap_strictMono) c = 0 := by
  erw [killsPi2_orderRealization_iff_universal_cycles_bound h.posMap h.posMap.monotone (ptBase w)
    (presPos_isConnected w (fun j => List.length_pos_iff.mp (hw j)))
    (presPos_isConnected v (fun j => List.length_pos_iff.mp (hv j)))]
  constructor
  · intro hz c hc
    have hi : Comb.bdry2 (orderCx (UOrder (PresPos w) (ptBase w)))
        (chain2 (strictOrderIncl _) c) = 0 := by
      erw [bdry2_chain2, hc, map_zero]
    obtain ⟨b, hb⟩ := hz (chain2 (strictOrderIncl _) c) hi
    have he := congrArg normalizeOrdChain2 hb
    have hn  :=
      normalizeOrdChain2_inclusion c
    erw [presPos_cover_normalized_three_boundary_zero,
      normalizeOrdChain2_strict_map h.universalMap h.universalMap_strictMono, hn] at he
    exact he.symm
  · intro hz c hc
    let d := chain2 (orderCxMap h.universalMap h.universalMap.monotone) c
    have hd : Comb.bdry2 (orderCx (UOrder (PresPos v) (ptBase v))) d = 0 := by
      erw [bdry2_chain2, hc, map_zero]
    have hn : normalizeOrdChain2 d = 0 := by
      erw [normalizeOrdChain2_strict_map h.universalMap h.universalMap_strictMono]
      exact hz _ (normalizeOrdChain2_cycle c hc)
    have he := ordNormalization_cycle_boundary d hd
    erw [hn, map_zero, sub_zero] at he
    exact ⟨ordNormalizationHomotopy2 d, he.symm⟩

variable [DecidableEq α]
  (ρ : J → FreeGroup α) (σ : K → FreeGroup β)
  (hwm : ∀ j, FreeGroup.mk (w j) = ρ j) (hvm : ∀ k, FreeGroup.mk (v k) = σ k)

/-- The actual Fox-kernel equivalence has exactly the lifted-relator group
coordinates used by the naturality theorem. -/
theorem foxCycle_coordinates
    (c : LinearMap.ker (Comb.bdry2 (strictOrderCx (UOrder (PresPos w) (ptBase w))))) :
    groupCellChainEquiv.symm (presUniversalTwoCycleFoxKernelEquiv ρ w hwm hw c).val =
      presUniversalRelatorGroupChainEquiv ρ w hwm hw
        (presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hw) hw c.val) := by
  erw [LinearEquiv.symm_apply_apply]
  rfl

include hw hv in
/-- Exact naturality with the Fox boundary kernel. -/
theorem strict_cycles_zero_iff_fox :
    (∀ c : StrictOrdTri (UOrder (PresPos w) (ptBase w)) →₀ ℤ,
      Comb.bdry2 (strictOrderCx (UOrder (PresPos w) (ptBase w))) c = 0 →
        chain2 (strictOrderCxMap h.universalMap h.universalMap_strictMono) c = 0) ↔
    ∀ z : LinearMap.ker ((coverSecondBoundary (relSub ρ) ρ).restrictScalars ℤ),
      Finsupp.mapDomain (Prod.map (h.groupHom ρ σ hwm hvm) h.cell)
        (groupCellChainEquiv.symm z.val) = 0 := by
  constructor
  · intro hz z
    obtain ⟨c, rfl⟩ := (presUniversalTwoCycleFoxKernelEquiv ρ w hwm hw).surjective z
    erw [foxCycle_coordinates hw ρ hwm c,
      ← h.universalRelatorChain_group_map ρ σ hwm hvm hw hv,
      hz c.val c.property, map_zero, map_zero]
  · intro hz c hc
    apply presCoverRelatorChain_cycle_injective v uOrderEnd (presUniversalEnd_isPosetCover v hv)
      hv _ 0 (by erw [bdry2_chain2, hc, map_zero]) (map_zero _) _
    apply (presUniversalRelatorGroupChainEquiv σ v hvm hv).injective
    erw [map_zero, map_zero, h.universalRelatorChain_group_map]
    have he := hz (presUniversalTwoCycleFoxKernelEquiv ρ w hwm hw ⟨c, hc⟩)
    rwa [foxCycle_coordinates hw ρ hwm] at he

include hw hv in
/-- The genuine topological pi2-killing condition is precisely the algebraic
Fox-cycle condition for this labelled presentation inclusion. All comparison
maps and naturality statements in this equivalence have been proved. -/
theorem killsPi2_iff_fox :
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap h.posMap h.posMap.monotone,
        (orderNerveRealizationMap h.posMap h.posMap.monotone).hom.continuous⟩ ↔
    ∀ z : LinearMap.ker ((coverSecondBoundary (relSub ρ) ρ).restrictScalars ℤ),
      Finsupp.mapDomain (Prod.map (h.groupHom ρ σ hwm hvm) h.cell)
        (groupCellChainEquiv.symm z.val) = 0 :=
  (h.killsPi2_iff_strict_cycles_zero hw hv).trans (h.strict_cycles_zero_iff_fox hw hv ρ σ hwm hvm)

end FiniteChains.PresModel.PresWordEmbedding

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
variable {α β J K : Type}
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  (h : PresWordEmbedding w v)

def realizationMap :
    C(orderNerveRealization (PresPos w), orderNerveRealization (PresPos v)) :=
  ⟨orderNerveRealizationMap h.posMap h.posMap.monotone,
    (orderNerveRealizationMap h.posMap h.posMap.monotone).hom.continuous⟩

variable [DecidableEq α]
  (ρ : J → FreeGroup α) (σ : K → FreeGroup β)
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hv : ∀ k, FreeGroup.mk (v k) = σ k)
  (hwp : ∀ j, 0 < (w j).length) (hvp : ∀ k, 0 < (v k).length)

end FiniteChains.PresModel.PresWordEmbedding

namespace FiniteChains
open Comb

variable {α β J K Q : Type} [DecidableEq α] [Group Q]

/-- The Fox-kernel condition is exactly the existing algebraic-cover cycle
condition, including for infinite sets of generators and relators. -/
theorem fox_kernel_vanish_iff_univCover (ρ : J → FreeGroup α)
    (φ : PresGroup ρ →* Q) (g : J → K) :
    (∀ z : LinearMap.ker ((coverSecondBoundary (relSub ρ) ρ).restrictScalars ℤ),
      Finsupp.mapDomain (Prod.map φ g) (groupCellChainEquiv.symm z.val) = 0) ↔
    ∀ c : PresGroup ρ × J →₀ ℤ, Comb.bdry2 (univCover ρ) c = 0 →
      Finsupp.mapDomain (Prod.map φ g) c = 0 := by
  have hb c :
      Comb.bdry2 (univCover ρ) c = 0 ↔
        coverSecondBoundary (relSub ρ) ρ (groupCellChainEquiv c) = 0 := by
    change Comb.bdry2 (univCover ρ) c = 0 ↔
      coverSecondBoundary (relSub ρ) ρ (fsCoords (relSub ρ) J c) = 0
    rw [fs_coverComplex_bdry2]
    exact (map_eq_zero_iff _ (fsCoords (relSub ρ) α).injective).symm
  constructor
  · intro hz c hc
    have he := hz ⟨groupCellChainEquiv c, (hb c).mp hc⟩
    simpa using he
  · simp_all

namespace PresModel.PresWordEmbedding
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  (h : PresWordEmbedding w v)
  (hw : ∀ j, 0 < (w j).length) (hv : ∀ k, 0 < (v k).length)
  (ρ : J → FreeGroup α) (σ : K → FreeGroup β)
  (hwm : ∀ j, FreeGroup.mk (w j) = ρ j) (hvm : ∀ k, FreeGroup.mk (v k) = σ k)

include hw hv in
/-- Actual topological pi2 vanishing agrees with the algebraic universal-cover
condition used in the presentation-chain arguments. -/
theorem killsPi2_iff_univCover :
    Whitehead.KillsPi2 h.realizationMap ↔
      ∀ c : PresGroup ρ × J →₀ ℤ, Comb.bdry2 (univCover ρ) c = 0 →
        Finsupp.mapDomain (Prod.map (h.groupHom ρ σ hwm hvm) h.cell) c = 0 :=
  (h.killsPi2_iff_fox hw hv ρ σ hwm hvm).trans
    (fox_kernel_vanish_iff_univCover ρ (h.groupHom ρ σ hwm hvm) h.cell)

variable [DecidableEq β]

include hw hv in
/-- The previously combinatorial pi2 hypothesis now has a proved comparison
with the actual topological pi2 of these presentation realizations. -/
theorem killsPi2_iff_combPi2 :
    Whitehead.KillsPi2 h.realizationMap ↔
      Comb.ZeroPi2 (presInclHom h.gen h.gen.injective ρ σ h.cell
        (h.relator_compat ρ σ hwm hvm)) :=
  (h.killsPi2_iff_univCover hw hv ρ σ hwm hvm).trans
    (zeroPi2_presInclHom_iff ρ h.gen h.gen.injective h.cell
      (h.relator_compat ρ σ hwm hvm)).symm

end PresModel.PresWordEmbedding
end FiniteChains
