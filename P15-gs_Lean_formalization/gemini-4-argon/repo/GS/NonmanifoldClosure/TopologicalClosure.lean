module

public import GS.NonmanifoldCompletion.NeighbourhoodModel
public import GS.Topology.Brouwer.Brouwer
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

noncomputable section
open Matrix GS GS.Nonmanifold GS.NonmanifoldCompletion Filter Set Metric Function
open scoped BigOperators Topology ContDiff unitInterval

namespace GS.NonmanifoldFinal

abbrev UnitSphere (κ : Type*) [Fintype κ] :=
  {x : EuclideanSpace ℝ κ // x ∈ Metric.sphere 0 1}

end GS.NonmanifoldFinal

namespace GS.NonmanifoldObstruction

structure ContinuousSectionPair (A B : Type*) [TopologicalSpace A]
    [TopologicalSpace B] where
  sectionMap : A → B
  retractionMap : B → A
  section_continuous : Continuous sectionMap
  retraction_continuous : Continuous retractionMap
  retraction_section : ∀ a, retractionMap (sectionMap a) = a

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def flattenImage (S : Set X) (A : Set S) : A ≃ₜ (Subtype.val '' A : Set X) where
  toFun a := ⟨a.val.val, ⟨a.val, a.property, rfl⟩⟩
  invFun x := ⟨⟨x.val, by obtain ⟨a, _, he⟩ := x.property; exact he ▸ a.property⟩, by
    obtain ⟨a, ha, he⟩ := x.property
    have hx : (⟨x.val, he ▸ a.property⟩ : S) = a := Subtype.ext he.symm
    simpa only [hx] using ha⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def restrictImage (h : X ≃ₜ Y) (A : Set X) : A ≃ₜ (h '' A) where
  toFun x := ⟨h x.val, ⟨x.val, x.property, rfl⟩⟩
  invFun y := ⟨h.symm y.val, by
    obtain ⟨x, hx, he⟩ := y.property
    rw [← he, h.symm_apply_apply]; exact hx⟩
  left_inv x := Subtype.ext (h.symm_apply_apply x.val)
  right_inv y := Subtype.ext (h.apply_symm_apply y.val)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem isOpen_flatten_of_subset_interior (S : Set X) (A : Set S)
    (hA : IsOpen A) (hinside : ∀ a ∈ A, a.val ∈ interior S) :
    IsOpen (Subtype.val '' A : Set X) := by
  let j : interior S → S := fun a => ⟨a.val, interior_subset a.property⟩
  have hImage : IsOpen (Subtype.val '' (j ⁻¹' A) : Set X) :=
    isOpen_interior.isOpenMap_subtype_val _ (hA.preimage (continuous_subtype_val.subtype_mk _))
  have he : (Subtype.val '' (j ⁻¹' A) : Set X) = Subtype.val '' A := by
    ext x
    exact ⟨fun ⟨a, ha, hx⟩ => ⟨j a, ha, hx⟩,
      fun ⟨a, ha, hx⟩ => ⟨⟨a.val, hinside a ha⟩, ha, hx⟩⟩
  exact he ▸ hImage

structure PointedOpenModel (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] (x : X) (y : Y) where
  source : Set X
  target : Set Y
  source_open : IsOpen source
  target_open : IsOpen target
  source_point : x ∈ source
  target_point : y ∈ target
  chart : source ≃ₜ target
  map_point : ∀ hx : x ∈ source, (chart ⟨x, hx⟩).val = y

def pointedOpenModel {x : X} {y : Y} (g : PointedNeighbourhoodModel X Y x y) :
    PointedOpenModel X Y x y := by
  let A : Set g.source := {a | a.val ∈ interior g.source ∧ (g.chart a).val ∈ interior g.target}
  let B : Set g.target := g.chart '' A
  have hA : IsOpen A := (isOpen_interior.preimage continuous_subtype_val).inter
    (isOpen_interior.preimage (continuous_subtype_val.comp g.chart.continuous))
  have hB : IsOpen B := g.chart.isOpenMap A hA
  have hxS : x ∈ g.source := mem_of_mem_nhds g.source_nhds
  have hpointA : (⟨x, hxS⟩ : g.source) ∈ A :=
    ⟨mem_interior_iff_mem_nhds.mpr g.source_nhds,
     (g.map_point hxS).symm ▸ mem_interior_iff_mem_nhds.mpr g.target_nhds⟩
  exact
    { source := Subtype.val '' A
      target := Subtype.val '' B
      source_open := isOpen_flatten_of_subset_interior g.source A hA fun _ ha => ha.1
      target_open := isOpen_flatten_of_subset_interior g.target B hB (by rintro _ ⟨_, ha, rfl⟩; exact ha.2)
      source_point := ⟨⟨x, hxS⟩, hpointA, rfl⟩
      target_point := ⟨g.chart ⟨x, hxS⟩, ⟨⟨x, hxS⟩, hpointA, rfl⟩, g.map_point hxS⟩
      chart := ((flattenImage g.source A).symm.trans (restrictImage g.chart A)).trans (flattenImage g.target B)
      map_point := fun _ => g.map_point hxS }

theorem original_pointed_open_model {q : ℕ} (hq : 0 < q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j ≠ 0) :
    Nonempty (PointedOpenModel ↥(localFamily q) (ModelCoordinates q)
      (familyBase Q₀ hQ₀) (modelCoordinatesZero q)) := by
  obtain ⟨g⟩ := original_pointed_neighbourhood_model hq Q₀ hQ₀ hentries
  exact ⟨pointedOpenModel g⟩

end GS.NonmanifoldObstruction

namespace GS.NonmanifoldFinal
open GS.NonmanifoldObstruction

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def EuclideanAt (x : X) : Prop :=
  ∃ (U : Set X), IsOpen U ∧ x ∈ U ∧
    ∃ (n : ℕ) (V : Set (EuclideanSpace ℝ (Fin n))), IsOpen V ∧
      Nonempty (U ≃ₜ V)

def subtypeOpenIntersection (S U : Set X) :
    ↥(Subtype.val ⁻¹' U : Set S) ≃ₜ ↥(S ∩ U) where
  toFun a := ⟨a.val.val, a.val.property, a.property⟩
  invFun a := ⟨⟨a.val, a.property.1⟩, a.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem euclideanAtSubset_iff (S : Set X) (x : X) (hx : x ∈ S) :
    EuclideanAtSubset S x ↔ EuclideanAt (⟨x, hx⟩ : S) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨_, U, hU, hxU, n, V, hV, ⟨h⟩⟩
    exact ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, hxU,
      n, V, hV, ⟨(subtypeOpenIntersection S U).trans h⟩⟩
  · rintro ⟨A, hA, hxA, n, V, hV, ⟨h⟩⟩
    obtain ⟨U, hU, hUA⟩ := isOpen_induced_iff.mp hA
    have hxU : x ∈ U := by change (⟨x, hx⟩ : S) ∈ Subtype.val ⁻¹' U; rwa [hUA]
    exact ⟨hx, U, hU, hxU, n, V, hV,
      ⟨(subtypeOpenIntersection S U).symm.trans ((Homeomorph.setCongr hUA).trans h)⟩⟩

theorem euclideanAt_of_homeomorph (h : X ≃ₜ Y) (x : X)
    (hx : EuclideanAt x) : EuclideanAt (h x) := by
  rcases hx with ⟨U, hU, ha, n, V, hV, ⟨c⟩⟩
  exact ⟨h '' U, h.isOpenMap U hU, ⟨x, ha, rfl⟩, n, V, hV,
    ⟨(restrictImage h U).symm.trans c⟩⟩

theorem euclideanAt_homeomorph (h : X ≃ₜ Y) (x : X) :
    EuclideanAt x ↔ EuclideanAt (h x) :=
  ⟨euclideanAt_of_homeomorph h x,
   fun hx => by simpa only [h.symm_apply_apply] using euclideanAt_of_homeomorph h.symm (h x) hx⟩

theorem euclideanAt_open_iff (S : Set X) (hS : IsOpen S) (x : S) :
    EuclideanAt x ↔ EuclideanAt x.val := by
  refine ⟨?_, ?_⟩
  · rintro ⟨A, hA, hx, n, V, hV, ⟨c⟩⟩
    exact ⟨Subtype.val '' A, hS.isOpenMap_subtype_val A hA,
      ⟨x, hx, rfl⟩, n, V, hV, ⟨(flattenImage S A).symm.trans c⟩⟩
  · rintro ⟨U, hU, hxU, n, V, hV, ⟨c⟩⟩
    let A : Set U := Subtype.val ⁻¹' S
    have hA : IsOpen A := hS.preimage continuous_subtype_val
    let B : Set V := c '' A
    have hC : IsOpen (Subtype.val '' B : Set (EuclideanSpace ℝ (Fin n))) :=
      hV.isOpenMap_subtype_val B (c.isOpenMap A hA)
    let D : Set S := Subtype.val ⁻¹' U
    let cD : D ≃ₜ A := ((subtypeOpenIntersection S U).trans
      (Homeomorph.setCongr (Set.inter_comm S U))).trans (subtypeOpenIntersection U S).symm
    exact ⟨D, hU.preimage continuous_subtype_val, hxU, n, Subtype.val '' B, hC,
      ⟨(cD.trans (restrictImage c A)).trans (flattenImage V B)⟩⟩

theorem euclideanAt_pointedOpenModel {x : X} {y : Y}
    (g : PointedOpenModel X Y x y) : EuclideanAt x ↔ EuclideanAt y := by
  let a : g.source := ⟨x, g.source_point⟩
  calc EuclideanAt x ↔ EuclideanAt a := (euclideanAt_open_iff g.source g.source_open a).symm
    _ ↔ EuclideanAt (g.chart a) := euclideanAt_homeomorph g.chart a
    _ ↔ EuclideanAt (g.chart a).val := euclideanAt_open_iff g.target g.target_open (g.chart a)
    _ ↔ EuclideanAt y := by rw [g.map_point g.source_point]

variable {ι κ ν : Type*}

def transportSectionPair {A A' B B' : Type*}
    [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace B] [TopologicalSpace B']
    (p : ContinuousSectionPair A B) (hA : A' ≃ₜ A) (hB : B ≃ₜ B') : ContinuousSectionPair A' B' where
  sectionMap a := hB (p.sectionMap (hA a))
  retractionMap b := hA.symm (p.retractionMap (hB.symm b))
  section_continuous := hB.continuous.comp (p.section_continuous.comp hA.continuous)
  retraction_continuous := hA.symm.continuous.comp (p.retraction_continuous.comp hB.symm.continuous)
  retraction_section a := by simp only [Homeomorph.symm_apply_apply, p.retraction_section]

abbrev PuncturedIn {X : Type*} (U : Set X) (x : X) := {p : X // p ∈ U ∧ p ≠ x}

def reindexReal (e : ι ≃ κ) : (ι → ℝ) ≃ₜ (κ → ℝ) where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def sumCoordinates : ((ι → ℝ) × (κ → ℝ)) ≃ₜ ((ι ⊕ κ) → ℝ) where
  toFun p := Sum.elim p.1 p.2
  invFun x := (fun i => x (.inl i), fun j => x (.inr j))
  left_inv _ := rfl
  right_inv x := by funext i; cases i <;> rfl
  continuous_toFun := by apply continuous_pi; intro i; cases i <;> dsimp <;> fun_prop
  continuous_invFun := by fun_prop

def reindexRankConeN (r : ℕ) [Fintype κ] [Fintype ν] (e : κ ≃ ν) :
    {W : Matrix (Fin (r + 1)) κ ℝ // W.rank ≤ 1} ≃ₜ
    {W : Matrix (Fin (r + 1)) ν ℝ // W.rank ≤ 1} where
  toFun W := ⟨W.val.reindex (Equiv.refl _) e, by simpa only [Matrix.rank_reindex] using W.property⟩
  invFun W := ⟨W.val.reindex (Equiv.refl _) e.symm, by simpa only [Matrix.rank_reindex] using W.property⟩
  left_inv W := by ext i j; simp
  right_inv W := by ext i j; simp
  continuous_toFun := by
    apply Continuous.subtype_mk; apply continuous_pi; intro i; apply continuous_pi; intro j
    exact (continuous_apply (e.symm j)).comp ((continuous_apply i).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk; apply continuous_pi; intro i; apply continuous_pi; intro j
    exact (continuous_apply (e j)).comp ((continuous_apply i).comp continuous_subtype_val)

abbrev FreeIndex (q : ℕ) := Fin q ⊕ (NonzeroIndex q ⊕ UpperIndex q)

def modelFreeCoordinates (q : ℕ) :
    ModelCoordinates q ≃ₜ ConeSpace (FreeIndex q) (UpperIndex q) where
  toFun p := (Sum.elim p.1 (Sum.elim p.2.1 p.2.2.1), p.2.2.2)
  invFun p := (fun i => p.1 (.inl i),
    fun j => p.1 (.inr (.inl j)), fun k => p.1 (.inr (.inr k)), p.2)
  left_inv _ := rfl
  right_inv p := Prod.ext (funext fun i => by cases i with | inl i => rfl | inr j => cases j <;> rfl) rfl
  continuous_toFun := by
    refine Continuous.prodMk ?_ (by fun_prop)
    apply continuous_pi; intro i; cases i with
    | inl _ => dsimp; fun_prop
    | inr j => cases j <;> dsimp <;> fun_prop
  continuous_invFun := by fun_prop

def modelToFin (q : ℕ) : ModelCoordinates q ≃ₜ
    ConeSpace (Fin (Fintype.card (FreeIndex q))) (Fin (Fintype.card (UpperIndex q))) :=
  (modelFreeCoordinates q).trans ((reindexReal (Fintype.equivFin _)).prodCongr (reindexRankConeN 1 (Fintype.equivFin _)))

@[simp] theorem modelToFin_zero (q : ℕ) :
    modelToFin q (modelCoordinatesZero q) = productZero :=
  Prod.ext (funext fun i => by
    simp [modelToFin, modelFreeCoordinates, reindexReal]
    cases (Fintype.equivFin (FreeIndex q)).symm i with | inl _ => rfl | inr j => cases j <;> rfl)
    (Subtype.ext (by ext; rfl))

def flattenConeProduct [Fintype ι] [Fintype κ] [DecidableEq κ] :
    ConeSpace ι κ ≃ₜ
      {p : (ι → ℝ) × Matrix (Fin 2) κ ℝ // p.2.rank ≤ 1} where
  toFun p := ⟨(p.1, p.2.val), p.2.property⟩
  invFun p := (p.val.1, ⟨p.val.2, p.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := Continuous.prodMk (by fun_prop)
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

theorem model_width_ge_three (q : ℕ) (hq : 3 ≤ q) :
    3 ≤ Fintype.card (UpperIndex q) := three_le_card_upperIndex q hq

end GS.NonmanifoldFinal

open GS.NonmanifoldObstruction GS.NonmanifoldFinal
open scoped BigOperators Topology ContDiff unitInterval

namespace GS.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def sphereNormalize {X : Type*} [TopologicalSpace X] (g : C(X, F))
    (hg : ∀ x, g x ≠ 0) : C(X, sphere (0 : F) 1) := by
  refine ⟨fun x => ⟨‖g x‖⁻¹ • g x, ?_⟩, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr (hg x))),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hg x))]
  · exact ((g.continuous.norm.inv₀ fun x => norm_ne_zero_iff.mpr (hg x)).smul
      g.continuous).subtype_mk _

theorem ne_zero_of_dist_lt_one {v w : F} (hv : ‖v‖ = 1)
    (h : dist w v < 1) : w ≠ 0 := fun hw => by simpa [hw, hv] using h

theorem line_ne_zero_of_dist_lt_one {v w : F} (hv : ‖v‖ = 1)
    (h : dist w v < 1) (t : unitInterval) :
    (1 - (t : ℝ)) • v + (t : ℝ) • w ≠ 0 :=
  ne_zero_of_dist_lt_one hv ((convex_ball v 1) (by simp) h (sub_nonneg.mpr t.property.2)
    t.property.1 (sub_add_cancel 1 (t : ℝ)))

theorem homotopic_sphereNormalize_of_dist_lt_one {X : Type*} [TopologicalSpace X]
    (f : C(X, sphere (0 : F) 1)) (g : C(X, F)) (hg : ∀ x, g x ≠ 0)
    (hclose : ∀ x, dist (g x) (f x : F) < 1) :
    f.Homotopic (sphereNormalize g hg) := by
  let a : C(unitInterval × X, F) :=
    ⟨fun z => (1 - (z.1 : ℝ)) • (f z.2 : F) + (z.1 : ℝ) • g z.2, by fun_prop⟩
  have ha (z) : a z ≠ 0 := line_ne_zero_of_dist_lt_one
    (mem_sphere_zero_iff_norm.mp (f z.2).property) (hclose z.2) z.1
  refine ⟨{ toContinuousMap := sphereNormalize a ha
            map_zero_left := fun x => Subtype.ext (by
              have hf : ‖(f x : F)‖ = 1 := mem_sphere_zero_iff_norm.mp (f x).property
              simp [sphereNormalize, a, hf])
            map_one_left := fun x => Subtype.ext (by simp [sphereNormalize, a]) }⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem exists_contDiff_dist_lt_on_compact (f : C(E, F)) {K : Set E}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ x ∈ K, dist (g x) (f x) < ε := by
  have hu : UniformContinuousOn f (cthickening 1 K) :=
    hK.cthickening.uniformContinuousOn_of_continuous (by fun_prop)
  rcases Metric.uniformContinuousOn_iff.mp hu (ε / 2) (half_pos hε) with ⟨δ, hδ, hfδ⟩
  rcases (map_continuous f).exists_contDiff_dist_le_of_forall_mem_ball_dist_le
    (lt_min one_pos hδ) with ⟨g, hgc, hg⟩
  refine ⟨g, hgc, fun x hx => (hg _ _ fun y hy => ?_).trans_lt (half_lt_self hε)⟩
  rw [mem_ball, lt_min_iff] at hy
  exact (hfδ _ (mem_cthickening_of_dist_le _ x _ _ hx hy.1.le) _
    (self_subset_cthickening _ hx) hy.2).le

theorem exists_contDiff_ne_zero_dist_lt_on_compact (f : C(E, F))
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F)
    {K : Set E} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ (∀ x, g x ≠ 0) ∧
      ∀ x ∈ K, dist (g x) (f x) < ε := by
  obtain ⟨g, hgc, hg⟩ := exists_contDiff_dist_lt_on_compact f hK (half_pos hε)
  have hdense := (hgc.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).dense_compl_range_of_finrank_lt_finrank hdim
  obtain ⟨y, hy, hyε⟩ := hdense.exists_dist_lt 0 (half_pos hε)
  refine ⟨fun x => g x - y, hgc.sub contDiff_const, fun x h => hy ⟨x, sub_eq_zero.mp h⟩, fun x hx => ?_⟩
  calc dist (g x - y) (f x) ≤ dist (g x - y) (g x) + dist (g x) (f x) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by simpa using hyε) (hg x hx)
    _ = ε := add_halves ε

theorem sphereMap_nullhomotopic_of_finrank_lt
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F)
    (f : C(sphere (0 : E) 1, sphere (0 : F) 1)) : f.Nullhomotopic := by
  let e : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let : TietzeExtension F := TietzeExtension.of_homeo e.toHomeomorph
  let fF : C(sphere (0 : E) 1, F) := ⟨fun x => f x, continuous_subtype_val.comp f.continuous⟩
  obtain ⟨f₀, hf₀⟩ := fF.exists_restrict_eq isClosed_sphere
  obtain ⟨g, hgc, hg0, hg⟩ :=
    exists_contDiff_ne_zero_dist_lt_on_compact f₀ hdim (isCompact_sphere (0 : E) 1) zero_lt_one
  let gC : C(E, F) := ⟨g, hgc.continuous⟩
  have hclose (x : sphere (0 : E) 1) : dist (gC.restrict _ x) (f x : F) < 1 := by
    have heq : f₀ x = (f x : F) := congrArg (fun h : C(sphere (0 : E) 1, F) => h x) hf₀
    simpa only [ContinuousMap.restrict_apply, gC, ContinuousMap.coe_mk, heq] using hg x x.property
  have hfg := homotopic_sphereNormalize_of_dist_lt_one f (gC.restrict _) (fun x => hg0 x) hclose
  have hn : (sphereNormalize gC hg0).Nullhomotopic := by
    simpa using (id_nullhomotopic E).comp_right (sphereNormalize gC hg0)
  obtain ⟨c, hc⟩ := hn.comp_left (⟨Subtype.val, continuous_subtype_val⟩ : C(sphere (0 : E) 1, E))
  exact ⟨c, hfg.trans hc⟩

omit [FiniteDimensional ℝ E] in
def unitBallClamp (x : E) : Metric.closedBall (0 : E) 1 :=
  ⟨(max 1 ‖x‖)⁻¹ • x, by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))]
    exact (inv_mul_le_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr
      (by simpa using le_max_right (1 : ℝ) ‖x‖)⟩

omit [FiniteDimensional ℝ E] in
theorem continuous_unitBallClamp : Continuous (unitBallClamp (E := E)) :=
  (((continuous_const.max continuous_norm).inv₀
    (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) ‖x‖)))).smul
    continuous_id).subtype_mk _

omit [FiniteDimensional ℝ E] in
@[simp] theorem unitBallClamp_coe (x : Metric.closedBall (0 : E) 1) :
    unitBallClamp (x : E) = x :=
  Subtype.ext (by simp [unitBallClamp, max_eq_left (mem_closedBall_zero_iff.mp x.property)])

theorem closedBall_fixedPoint
    (f : Metric.closedBall (0 : E) 1 → Metric.closedBall (0 : E) 1)
    (hf : Continuous f) : ∃ x, f x = x := by
  let n := Module.finrank ℝ E
  let e : E ≃L[ℝ] (Fin n → ℝ) := (Module.finBasis ℝ E).equivFunL
  let R : ℝ := ‖(e : E →L[ℝ] (Fin n → ℝ))‖ + 1
  let D : ℝ := 2 * (n + 1) * R
  have hR : 0 < R := by dsimp [R]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hcoord (x : Metric.closedBall (0 : E) 1) (i : Fin n) : |e x i| ≤ R := by
    calc |e x i| = ‖e x i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖e x‖ := norm_le_pi_norm (e x) i
      _ ≤ ‖(e : E →L[ℝ] (Fin n → ℝ))‖ * ‖(x : E)‖ := (e : E →L[ℝ] (Fin n → ℝ)).le_opNorm x
      _ ≤ ‖(e : E →L[ℝ] (Fin n → ℝ))‖ * 1 :=
        mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp x.property) (norm_nonneg _)
      _ ≤ R := by dsimp [R]; linarith
  let a : Metric.closedBall (0 : E) 1 → Fin n → ℝ := fun x i => (e x i + R) / D
  have ha0 (x : Metric.closedBall (0 : E) 1) (i : Fin n) : 0 ≤ a x i :=
    div_nonneg (by have := (abs_le.mp (hcoord x i)).1; linarith) hD.le
  have ha1 (x : Metric.closedBall (0 : E) 1) : ∑ i, a x i ≤ 1 := by
    have hi (i : Fin n) : a x i ≤ (2 * R) / D :=
      div_le_div_of_nonneg_right (by have := (abs_le.mp (hcoord x i)).2; linarith) hD.le
    calc ∑ i, a x i ≤ ∑ _i : Fin n, (2 * R) / D := Finset.sum_le_sum fun i _ => hi i
      _ = (n : ℝ) * (2 * R) / D := by simp [mul_div_assoc]
      _ ≤ 1 := (div_le_one hD).mpr (by dsimp [D]; nlinarith)
  let enc : Metric.closedBall (0 : E) 1 → stdSimplex ℝ (Fin (n + 1)) := fun x =>
    ⟨Fin.cons (1 - ∑ i, a x i) (a x),
      ⟨fun i => Fin.cases (sub_nonneg.mpr (ha1 x)) (ha0 x) i,
       by rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; ring⟩⟩
  have henc : Continuous enc := by
    apply Continuous.subtype_mk; apply continuous_pi; intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Continuous (fun x : Metric.closedBall (0 : E) 1 => 1 - ∑ j, (e (x : E) j + R) / D); fun_prop
    · change Continuous (fun x : Metric.closedBall (0 : E) 1 => (e (x : E) j + R) / D); fun_prop
  let dec : stdSimplex ℝ (Fin (n + 1)) → E := fun y => e.symm (fun i => D * y.val i.succ - R)
  have hdec : Continuous dec := e.symm.continuous.comp (continuous_pi fun i =>
    (continuous_const.mul ((continuous_apply i.succ).comp continuous_subtype_val)).sub continuous_const)
  have hdecenc (x : Metric.closedBall (0 : E) 1) : dec (enc x) = (x : E) := by
    apply e.injective; simp only [dec, ContinuousLinearEquiv.apply_symm_apply]
    ext i; change D * ((e (x : E) i + R) / D) - R = e (x : E) i; field_simp; ring
  let ret : stdSimplex ℝ (Fin (n + 1)) → Metric.closedBall (0 : E) 1 := fun y => unitBallClamp (dec y)
  have hret : Continuous ret := continuous_unitBallClamp.comp hdec
  have hretenc (x : Metric.closedBall (0 : E) 1) : ret (enc x) = x := by
    dsimp [ret]; rw [hdecenc, unitBallClamp_coe]
  obtain ⟨y, hy⟩ := Brouwer (n := ⟨n + 1, Nat.succ_pos _⟩) (enc ∘ f ∘ ret) (henc.comp (hf.comp hret))
  exact ⟨ret y, by simpa only [Function.comp_apply, hretenc] using congrArg ret hy⟩

abbrev UnitNormSphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1
abbrev UnitNormBall (E : Type*) [NormedAddCommGroup E] := Metric.closedBall (0 : E) 1

omit [FiniteDimensional ℝ E] in
def sphereConeMap : C(unitInterval × UnitNormSphere E, UnitNormBall E) where
  toFun p := ⟨(p.1 : ℝ) • (p.2 : E), by
    have hu : ‖(p.2 : E)‖ = 1 := by simpa using p.2.property
    simpa [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg p.1.property.1, hu] using p.1.property.2⟩
  continuous_toFun := by fun_prop

omit [FiniteDimensional ℝ E] in
@[simp] theorem sphereConeMap_norm (p : unitInterval × UnitNormSphere E) :
    ‖(sphereConeMap p : E)‖ = (p.1 : ℝ) := by
  have hu : ‖(p.2 : E)‖ = 1 := by simpa using p.2.property
  simp [sphereConeMap, norm_smul, Real.norm_eq_abs, abs_of_nonneg p.1.property.1, hu]

omit [FiniteDimensional ℝ E] in
theorem sphereConeMap_surjective (u : UnitNormSphere E) :
    Function.Surjective (sphereConeMap (E := E)) := by
  intro x
  by_cases hx : (x : E) = 0
  · exact ⟨(0, u), Subtype.ext (by simpa [sphereConeMap] using hx.symm)⟩
  · have hn : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let t : unitInterval := ⟨‖(x : E)‖, norm_nonneg _, by
      simpa only [UnitNormBall, Metric.mem_closedBall, dist_zero_right] using x.property⟩
    let v : UnitNormSphere E := ⟨‖(x : E)‖⁻¹ • (x : E), by
      simp [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]⟩
    exact ⟨(t, v), Subtype.ext (by simp [sphereConeMap, t, v, smul_smul, mul_inv_cancel₀ hn])⟩

omit [FiniteDimensional ℝ E] in
theorem homotopy_factors_sphereConeMap (u : UnitNormSphere E)
    (h : ContinuousMap.Homotopy (ContinuousMap.const _ u)
      (ContinuousMap.id (UnitNormSphere E))) :
    Function.FactorsThrough h.toContinuousMap (sphereConeMap (E := E)) := by
  intro a b hab
  have ht : a.1 = b.1 := Subtype.ext
    (by simpa only [sphereConeMap_norm] using congrArg (fun z : UnitNormBall E => ‖(z : E)‖) hab)
  by_cases hz : (a.1 : ℝ) = 0
  · have ha : a.1 = 0 := Subtype.ext hz
    have hb : b.1 = 0 := ht.symm.trans ha
    change h (a.1, a.2) = h (b.1, b.2)
    rw [ha, hb]; exact (h.map_zero_left a.2).trans (h.map_zero_left b.2).symm
  · have hu : a.2 = b.2 := Subtype.ext (by
      have he : (a.1 : ℝ) • (a.2 : E) = (a.1 : ℝ) • (b.2 : E) := by
        simpa only [sphereConeMap, ContinuousMap.coe_mk, ht] using congrArg Subtype.val hab
      simpa only [smul_smul, inv_mul_cancel₀ hz, one_smul] using congrArg (fun w : E => (a.1 : ℝ)⁻¹ • w) he)
    exact congrArg h (Prod.ext ht hu)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
def sphereInclusion : C(UnitNormSphere E, UnitNormBall E) :=
  ContinuousMap.inclusion Metric.sphere_subset_closedBall

omit [FiniteDimensional ℝ E] in
theorem exists_sphere_retraction_of_nullhomotopic [ProperSpace E]
    (hc : (ContinuousMap.id (UnitNormSphere E)).Nullhomotopic) :
    ∃ r : C(UnitNormBall E, UnitNormSphere E), r.comp sphereInclusion = ContinuousMap.id _ := by
  obtain ⟨u, ⟨h⟩⟩ := hc
  have hq : _root_.Topology.IsQuotientMap (sphereConeMap (E := E)) :=
    sphereConeMap.continuous.isClosedMap.isQuotientMap
      sphereConeMap.continuous (sphereConeMap_surjective u)
  let r := hq.lift h.symm.toContinuousMap (homotopy_factors_sphereConeMap u h.symm)
  refine ⟨r, ContinuousMap.ext fun v => ?_⟩
  have he := ContinuousMap.congr_fun
    (hq.lift_comp h.symm.toContinuousMap (homotopy_factors_sphereConeMap u h.symm)) (1, v)
  change r (sphereInclusion v) = v
  have hi : sphereConeMap (1, v) = sphereInclusion v := Subtype.ext (one_smul ℝ (v : E))
  rw [← hi]; exact he.trans (h.symm.map_one_left v)

omit [FiniteDimensional ℝ E] in
theorem sphere_id_not_nullhomotopic_of_fixedPoint [ProperSpace E]
    (hfp : ∀ f : C(UnitNormBall E, UnitNormBall E), ∃ x, f x = x) :
    ¬ (ContinuousMap.id (UnitNormSphere E)).Nullhomotopic := by
  intro hc
  obtain ⟨r, hr⟩ := exists_sphere_retraction_of_nullhomotopic hc
  let f : C(UnitNormBall E, UnitNormBall E) :=
    ⟨fun x => ⟨-(r x : E), by
      have he : ‖(r x : E)‖ = 1 := by simpa using (r x).property
      simp [Metric.mem_closedBall, dist_zero_right, he]⟩, by fun_prop⟩
  obtain ⟨x, hx⟩ := hfp f
  have hxe : -(r x : E) = (x : E) := congrArg Subtype.val hx
  have hxn : ‖(x : E)‖ = 1 := by rw [← hxe, norm_neg]; simpa using (r x).property
  let v : UnitNormSphere E := ⟨x, by simpa using hxn⟩
  have hrx : (r x : E) = (x : E) := by
    simpa [sphereInclusion, v, ContinuousMap.inclusion, Set.inclusion] using
      congrArg Subtype.val (ContinuousMap.congr_fun hr v)
  have hzero : (x : E) = 0 := by
    rw [hrx] at hxe
    have he : (2 : ℝ) • (x : E) = 0 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, add_smul, one_smul]
      exact neg_eq_iff_add_eq_zero.mp hxe
    simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul, smul_zero] using
      congrArg (fun z : E => (2 : ℝ)⁻¹ • z) he
  simpa [hzero] using hxn

end GS.Topology

namespace GS.NonmanifoldClosure

abbrev NormSphere (E : Type*) [NormedAddCommGroup E] := {x : E // ‖x‖ = 1}
abbrev PuncturedNormBall (E : Type*) [NormedAddCommGroup E] (r : ℝ) :=
  PuncturedIn {x : E | ‖x‖ < r} 0

def normSphereStandard (n : ℕ) :
    NormSphere (EuclideanSpace ℝ (Fin n)) ≃ₜ UnitSphere (Fin n) :=
  Homeomorph.setCongr (by ext x; change ‖x‖ = 1 ↔ dist x 0 = 1; rw [dist_zero_right])

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ballNormalize {r : ℝ} (x : PuncturedNormBall E r) : NormSphere E :=
  ⟨‖x.val‖⁻¹ • x.val, by
    have hp : 0 < ‖x.val‖ := norm_pos_iff.mpr x.property.2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    exact inv_mul_cancel₀ (ne_of_gt hp)⟩

def ballSection {r : ℝ} (hr : 0 < r) (v : NormSphere E) :
    PuncturedNormBall E r :=
  ⟨(r / 2) • v.val, by
    have hn : ‖(r / 2) • v.val‖ = r / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), v.property, mul_one]
    exact ⟨by change ‖(r / 2) • v.val‖ < r; linarith, fun hz => by rw [hz, norm_zero] at hn; linarith⟩⟩

theorem continuous_ballNormalize (r : ℝ) :
    Continuous (@ballNormalize E _ _ r) :=
  (((continuous_norm.comp continuous_subtype_val).inv₀
    fun x => norm_ne_zero_iff.mpr x.property.2).smul continuous_subtype_val).subtype_mk _

theorem continuous_ballSection {r : ℝ} (hr : 0 < r) :
    Continuous (ballSection (E := E) hr) :=
  (continuous_const.smul continuous_subtype_val).subtype_mk _

def radialRadius {r : ℝ} (p : unitInterval × PuncturedNormBall E r) : ℝ :=
  (1 - (p.1 : ℝ)) * (r / 2) + (p.1 : ℝ) * ‖p.2.val‖

theorem radialRadius_pos {r : ℝ} (hr : 0 < r)
    (p : unitInterval × PuncturedNormBall E r) : 0 < radialRadius p := by
  have h0 := p.1.property.1
  have h1 := p.1.property.2
  have hx : 0 < ‖p.2.val‖ := norm_pos_iff.mpr p.2.property.2
  have ha : 0 ≤ (1 - (p.1 : ℝ)) * (r / 2) := mul_nonneg (by linarith) (by linarith)
  by_cases ht : (p.1 : ℝ) = 0
  · simp [radialRadius, ht]; linarith
  · have hp : 0 < (p.1 : ℝ) * ‖p.2.val‖ :=
      mul_pos (lt_of_le_of_ne h0 (Ne.symm ht)) hx
    dsimp [radialRadius]; linarith

theorem radialRadius_lt {r : ℝ} (hr : 0 < r)
    (p : unitInterval × PuncturedNormBall E r) : radialRadius p < r := by
  have h0 := p.1.property.1
  have h1 := p.1.property.2
  have hx : ‖p.2.val‖ < r := p.2.property.1
  by_cases ht : (p.1 : ℝ) = 1
  · simpa [radialRadius, ht] using hx
  · have ht' : (p.1 : ℝ) < 1 := lt_of_le_of_ne h1 ht
    have ha : 0 < (1 - (p.1 : ℝ)) * (r / 2) := mul_pos (by linarith) (by linarith)
    have hb : 0 ≤ (p.1 : ℝ) * (r - ‖p.2.val‖) := mul_nonneg h0 (by linarith)
    dsimp [radialRadius]; nlinarith

def radialDeform {r : ℝ} (hr : 0 < r)
    (p : unitInterval × PuncturedNormBall E r) : PuncturedNormBall E r :=
  ⟨radialRadius p • (ballNormalize p.2).val, by
    have hn : ‖radialRadius p • (ballNormalize p.2).val‖ = radialRadius p := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (radialRadius_pos hr p),
        (ballNormalize p.2).property, mul_one]
    exact ⟨by change ‖radialRadius p • (ballNormalize p.2).val‖ < r; rw [hn]; exact radialRadius_lt hr p,
      fun hz => by rw [hz, norm_zero] at hn; linarith [radialRadius_pos hr p]⟩⟩

theorem continuous_radialDeform {r : ℝ} (hr : 0 < r) :
    Continuous (radialDeform (E := E) hr) := by
  apply Continuous.subtype_mk
  have hρ : Continuous (radialRadius : unitInterval × PuncturedNormBall E r → ℝ) := by
    unfold radialRadius; fun_prop
  exact hρ.smul (continuous_subtype_val.comp ((continuous_ballNormalize r).comp continuous_snd))

def puncturedBallHomotopy {r : ℝ} (hr : 0 < r) :
    ContinuousMap.Homotopy
      (⟨fun x => ballSection hr (ballNormalize x),
        (continuous_ballSection hr).comp (continuous_ballNormalize r)⟩ :
          C(PuncturedNormBall E r, PuncturedNormBall E r))
      (ContinuousMap.id (PuncturedNormBall E r)) where
  toFun := radialDeform hr
  continuous_toFun := continuous_radialDeform hr
  map_zero_left x := by apply Subtype.ext; simp [radialDeform, radialRadius, ballSection]
  map_one_left x := by
    apply Subtype.ext
    simp [radialDeform, radialRadius, ballNormalize, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr x.property.2)]

end GS.NonmanifoldClosure

namespace GS.Topology
open GS.NonmanifoldClosure

theorem sphere_retract_ball_dimension (m n : ℕ) {r : ℝ} (hr : 0 < r)
    (p : ContinuousSectionPair (UnitSphere (Fin m))
      (PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r)) : n = m := by
  let a : C(UnitSphere (Fin m), PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r) :=
    ⟨p.sectionMap, p.section_continuous⟩
  let b : C(PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r, UnitSphere (Fin m)) :=
    ⟨p.retractionMap, p.retraction_continuous⟩
  let v : C(PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r, UnitSphere (Fin n)) :=
    (⟨normSphereStandard n, (normSphereStandard n).continuous⟩ :
      C(NormSphere (EuclideanSpace ℝ (Fin n)), UnitSphere (Fin n))).comp
      ⟨ballNormalize, continuous_ballNormalize r⟩
  let w : C(UnitSphere (Fin n), PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r) :=
    (⟨ballSection hr, continuous_ballSection hr⟩ :
      C(NormSphere (EuclideanSpace ℝ (Fin n)),
        PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r)).comp
      ⟨(normSphereStandard n).symm, (normSphereStandard n).symm.continuous⟩
  let s := v.comp a
  let t := b.comp w
  have hid : ContinuousMap.Homotopic (t.comp s) (ContinuousMap.id (UnitSphere (Fin m))) := by
    refine ⟨{
      toFun := fun z => b (radialDeform hr (z.1, a z.2))
      continuous_toFun := b.continuous.comp
        ((continuous_radialDeform hr).comp (continuous_fst.prodMk (a.continuous.comp continuous_snd)))
      map_zero_left := fun x => by
        change b (radialDeform hr (0, a x)) = b (w (v (a x)))
        congr 1
        change radialDeform hr (0, a x) =
          ballSection hr ((normSphereStandard n).symm ((normSphereStandard n) (ballNormalize (a x))))
        rw [Homeomorph.symm_apply_apply]
        exact (puncturedBallHomotopy hr).map_zero_left (a x)
      map_one_left := fun x =>
        (congrArg b ((puncturedBallHomotopy hr).map_one_left (a x))).trans (p.retraction_section x) }⟩
  by_contra hne
  have hnull : (t.comp s).Nullhomotopic := by
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · exact (sphereMap_nullhomotopic_of_finrank_lt (by simpa using hnm) t).comp_left s
    · exact (sphereMap_nullhomotopic_of_finrank_lt (by simpa using hmn) s).comp_right t
  obtain ⟨c, hc⟩ := hnull
  exact sphere_id_not_nullhomotopic_of_fixedPoint
    (fun f => closedBall_fixedPoint f f.continuous) ⟨c, hid.symm.trans hc⟩

end GS.Topology

namespace GS.NonmanifoldClosure

variable {X : Type*} [TopologicalSpace X]
abbrev Eucl (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev NormBall (n : ℕ) (r : ℝ) := {z : Eucl n // ‖z‖ < r}

structure OpenEuclideanChart (X : Type*) [TopologicalSpace X] (n : ℕ) where
  source : Set X
  target : Set (Eucl n)
  source_open : IsOpen source
  target_open : IsOpen target
  chart : source ≃ₜ target

structure CenteredEuclideanChart (X : Type*) [TopologicalSpace X] (x : X) (n : ℕ) where
  source : Set X
  source_open : IsOpen source
  source_point : x ∈ source
  radius : ℝ
  radius_pos : 0 < radius
  chart : source ≃ₜ NormBall n radius
  map_point : ∀ hx : x ∈ source, (chart ⟨x, hx⟩).val = 0

def OpenEuclideanChart.restrict {n : ℕ} (c : OpenEuclideanChart X n)
    (U : Set X) (hU : IsOpen U) : OpenEuclideanChart X n := by
  let A : Set c.source := Subtype.val ⁻¹' U
  let B : Set c.target := c.chart '' A
  have hA : IsOpen A := hU.preimage continuous_subtype_val
  exact
    { source := c.source ∩ U
      target := Subtype.val '' B
      source_open := c.source_open.inter hU
      target_open := c.target_open.isOpenMap_subtype_val B (c.chart.isOpenMap A hA)
      chart := ((subtypeOpenIntersection c.source U).symm.trans
        (restrictImage c.chart A)).trans (flattenImage c.target B) }

theorem euclideanAt_iff_chart (x : X) :
    EuclideanAt x ↔ ∃ n, ∃ c : OpenEuclideanChart X n, x ∈ c.source :=
  ⟨fun ⟨U, hU, hx, n, V, hV, ⟨h⟩⟩ => ⟨n, ⟨U, V, hU, hV, h⟩, hx⟩,
   fun ⟨n, c, hx⟩ => ⟨c.source, c.source_open, hx, n, c.target, c.target_open, ⟨c.chart⟩⟩⟩

theorem exists_centeredChart {n : ℕ} (c : OpenEuclideanChart X n)
    (x : X) (hx : x ∈ c.source) :
    ∃ b : CenteredEuclideanChart X x n, b.source ⊆ c.source := by
  let a₀ : c.source := ⟨x, hx⟩
  let y : Eucl n := (c.chart a₀).val
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (c.target_open.mem_nhds (c.chart a₀).property)
  let A : Set c.source := {a | ‖(c.chart a).val - y‖ < r}
  have hA : IsOpen A := isOpen_Iio.preimage
    (((continuous_subtype_val.comp c.chart.continuous).sub continuous_const).norm)
  let j : NormBall n r → c.target := fun z =>
    ⟨y + z.val, hball (by
      rw [Metric.mem_ball, dist_eq_norm]
      change ‖y + z.val - y‖ < r
      simpa only [add_sub_cancel_left] using z.property)⟩
  let e : A ≃ₜ NormBall n r :=
    { toFun := fun a => ⟨(c.chart a.val).val - y, a.property⟩
      invFun := fun z => ⟨c.chart.symm (j z), by
        change ‖(c.chart (c.chart.symm (j z))).val - y‖ < r
        rw [c.chart.apply_symm_apply]
        change ‖y + z.val - y‖ < r
        simpa only [add_sub_cancel_left] using z.property⟩
      left_inv := fun a => by
        apply Subtype.ext; apply c.chart.injective; apply Subtype.ext
        simp only [c.chart.apply_symm_apply]
        change y + ((c.chart a.val).val - y) = (c.chart a.val).val; abel
      right_inv := fun z => by
        apply Subtype.ext; simp only [c.chart.apply_symm_apply]
        change y + z.val - y = z.val; abel
      continuous_toFun :=
        ((continuous_subtype_val.comp (c.chart.continuous.comp continuous_subtype_val)).sub
          continuous_const).subtype_mk _
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact c.chart.symm.continuous.comp ((continuous_const.add continuous_subtype_val).subtype_mk _) }
  exact ⟨{
    source := Subtype.val '' A
    source_open := c.source_open.isOpenMap_subtype_val A hA
    source_point := ⟨a₀, by change ‖y - y‖ < r; simpa using hr, rfl⟩
    radius := r
    radius_pos := hr
    chart := (flattenImage c.source A).symm.trans e
    map_point := fun _ => by change (c.chart ⟨x, hx⟩).val - y = 0; exact sub_self y },
    by rintro _ ⟨a, _, rfl⟩; exact a.property⟩

theorem exists_centeredChart_within {n : ℕ} (c : OpenEuclideanChart X n)
    (x : X) (hx : x ∈ c.source) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ b : CenteredEuclideanChart X x n, b.source ⊆ c.source ∩ U :=
  exists_centeredChart (c.restrict U hU) x ⟨hx, hxU⟩

def homeomorphPunctured {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {S : Set A} {T : Set B} (h : S ≃ₜ T) {x : A} (hx : x ∈ S) {y : B}
    (hy : (h ⟨x, hx⟩).val = y) : PuncturedIn S x ≃ₜ PuncturedIn T y where
  toFun p := ⟨(h ⟨p.val, p.property.1⟩).val, (h ⟨p.val, p.property.1⟩).property,
    fun he => p.property.2 (congrArg Subtype.val (h.injective (Subtype.ext (he.trans hy.symm))))⟩
  invFun z := ⟨(h.symm ⟨z.val, z.property.1⟩).val, (h.symm ⟨z.val, z.property.1⟩).property,
    fun he => z.property.2 (by
      have hh : h.symm ⟨z.val, z.property.1⟩ = ⟨x, hx⟩ := Subtype.ext he
      simpa only [h.apply_symm_apply, hy] using congrArg (fun a => (h a).val) hh)⟩
  left_inv p := by
    apply Subtype.ext
    exact congrArg (fun a : S => a.val) (h.symm_apply_apply ⟨p.val, p.property.1⟩)
  right_inv z := by
    apply Subtype.ext
    exact congrArg (fun a : T => a.val) (h.apply_symm_apply ⟨z.val, z.property.1⟩)
  continuous_toFun := (continuous_subtype_val.comp
    (h.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp
    (h.symm.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _

def CenteredEuclideanChart.punctured {x : X} {n : ℕ}
    (c : CenteredEuclideanChart X x n) :
    PuncturedIn c.source x ≃ₜ PuncturedNormBall (Eucl n) c.radius :=
  homeomorphPunctured c.chart c.source_point (c.map_point c.source_point)

def OpenEuclideanChart.punctured {n : ℕ} (c : OpenEuclideanChart X n)
    (x : X) (hx : x ∈ c.source) :
    PuncturedIn c.source x ≃ₜ PuncturedIn c.target (c.chart ⟨x, hx⟩).val :=
  homeomorphPunctured c.chart hx rfl

theorem normSphere_retract_open {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hU : IsOpen U) (y : E) (hy : y ∈ U) :
    Nonempty (ContinuousSectionPair (NormSphere E) (PuncturedIn U y)) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hy)
  let t := r / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have hne (p : PuncturedIn U y) : p.val - y ≠ 0 := sub_ne_zero.mpr p.property.2
  refine ⟨{
    sectionMap := fun v => ⟨y + t • v.val, hball (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht, v.property, mul_one]
      dsimp [t]; linarith), fun he => by
      have hz : t • v.val = 0 := by simpa using congrArg (· - y) he
      have hn := congrArg norm hz
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, v.property, mul_one, norm_zero] at hn
      linarith⟩
    retractionMap := fun p => ⟨‖p.val - y‖⁻¹ • (p.val - y), by
      have hp := norm_pos_iff.mpr (hne p)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ (ne_of_gt hp)]⟩
    section_continuous := (continuous_const.add (continuous_const.smul continuous_subtype_val)).subtype_mk _
    retraction_continuous := by
      apply Continuous.subtype_mk
      exact (((continuous_subtype_val.sub continuous_const).norm).inv₀
        fun p => norm_ne_zero_iff.mpr (hne p)).smul (continuous_subtype_val.sub continuous_const)
    retraction_section := fun v => by
      apply Subtype.ext
      change ‖y + t • v.val - y‖⁻¹ • (y + t • v.val - y) = v.val
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht, v.property, mul_one,
        smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul] }⟩

def SphereRetractionsOn (O : Set X) (x : X) (m : ℕ) : Prop :=
  ∀ U : Set X, IsOpen U → x ∈ U → U ⊆ O →
    Nonempty (ContinuousSectionPair (UnitSphere (Fin m)) (PuncturedIn U x))

theorem OpenEuclideanChart.sphereRetractions {m : ℕ} (c : OpenEuclideanChart X m)
    (x : X) (hx : x ∈ c.source) : SphereRetractionsOn c.source x m := by
  intro U hU hxU hsub
  let d := c.restrict U hU
  have hxd : x ∈ d.source := ⟨hx, hxU⟩
  obtain ⟨p⟩ := normSphere_retract_open d.target d.target_open (d.chart ⟨x, hxd⟩).val
    (d.chart ⟨x, hxd⟩).property
  have he : PuncturedIn d.source x ≃ₜ PuncturedIn U x :=
    Homeomorph.setCongr (by
      ext z
      change ((z ∈ c.source ∧ z ∈ U) ∧ z ≠ x) ↔ (z ∈ U ∧ z ≠ x)
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hsub h.1, h.1⟩, h.2⟩⟩)
  exact ⟨transportSectionPair p (normSphereStandard m).symm ((d.punctured x hxd).symm.trans he)⟩

variable {r : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

abbrev RankConeN (r : ℕ) (κ : Type*) [Fintype κ] :=
  {W : Matrix (Fin (r + 1)) κ ℝ // W.rank ≤ 1}

def rankConeZero (r : ℕ) {κ : Type*} [Fintype κ] : RankConeN r κ := ⟨0, by simp⟩

abbrev RankPivotN (r : ℕ) (j : κ) :=
  {W : Matrix (Fin (r + 1)) κ ℝ // W.rank ≤ 1 ∧ W 0 j ≠ 0}
abbrev PivotCoordinatesN (r : ℕ) (j : κ) := {x : κ → ℝ // x j ≠ 0} × (Fin r → ℝ)

def pivotEncodeN (r : ℕ) (j : κ) (W : RankPivotN r j) : PivotCoordinatesN r j :=
  (⟨W.val 0, W.property.2⟩, fun i => W.val i.succ j / W.val 0 j)

def pivotDecodeN (r : ℕ) (j : κ) (p : PivotCoordinatesN r j) : RankPivotN r j :=
  ⟨outer (Fin.cases 1 p.2) p.1.val, rank_outer_le_one _ _, by simpa [outer] using p.1.property⟩

def rankPivotHomeomorphN (r : ℕ) (j : κ) : RankPivotN r j ≃ₜ PivotCoordinatesN r j where
  toFun := pivotEncodeN r j
  invFun := pivotDecodeN r j
  left_inv W := by
    apply Subtype.ext; ext i k
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [pivotDecodeN, pivotEncodeN, outer]
    · have hm := GS.GlobalGeometry.rank_le_one_minorN W.val W.property.1 0 i.succ j k
      change (W.val i.succ j / W.val 0 j) * W.val 0 k = W.val i.succ k
      field_simp [W.property.2]; nlinarith [hm]
  right_inv p := Prod.ext (Subtype.ext (funext fun _ => by simp [pivotDecodeN, pivotEncodeN, outer]))
    (funext fun _ => by simp [pivotEncodeN, pivotDecodeN, outer, p.1.property])
  continuous_toFun := by
    unfold pivotEncodeN
    refine Continuous.prodMk ((continuous_apply 0).comp continuous_subtype_val |>.subtype_mk _) ?_
    apply continuous_pi; intro i
    have h₀ : Continuous (fun W : RankPivotN r j => W.val 0 j) :=
      (continuous_apply j).comp ((continuous_apply 0).comp continuous_subtype_val)
    have h₁ : Continuous (fun W : RankPivotN r j => W.val i.succ j) :=
      (continuous_apply j).comp ((continuous_apply i.succ).comp continuous_subtype_val)
    exact h₁.div h₀ fun W => W.property.2
  continuous_invFun := by
    unfold pivotDecodeN
    apply Continuous.subtype_mk
    apply continuous_pi; intro i; apply continuous_pi; intro k
    have hx : Continuous (fun p : PivotCoordinatesN r j => p.1.val k) :=
      (continuous_apply k).comp (continuous_subtype_val.comp continuous_fst)
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [outer]
    · exact hx
    · exact ((continuous_apply i).comp continuous_snd).mul hx

abbrev RegularCoordinatesN (r : ℕ) (ι κ : Type*) := (ι → ℝ) × ((κ → ℝ) × (Fin r → ℝ))

def regularCoordinatesEuclideanN (r : ℕ) : RegularCoordinatesN r ι κ ≃ₜ
    Eucl (Fintype.card ι + Fintype.card κ + r) := by
  let h₁ : RegularCoordinatesN r ι κ ≃ₜ (ι → ℝ) × ((κ ⊕ Fin r) → ℝ) :=
    (Homeomorph.refl _).prodCongr sumCoordinates
  let h₂ : RegularCoordinatesN r ι κ ≃ₜ ((ι ⊕ (κ ⊕ Fin r)) → ℝ) :=
    h₁.trans sumCoordinates
  have hcard : Fintype.card (ι ⊕ (κ ⊕ Fin r)) = Fintype.card ι + Fintype.card κ + r := by
    simp [Nat.add_assoc]
  let e := (Fintype.equivFin (ι ⊕ (κ ⊕ Fin r))).trans (Equiv.cast (congrArg Fin hcard))
  exact (h₂.trans (reindexReal e)).trans
    (EuclideanSpace.equiv (Fin (Fintype.card ι + Fintype.card κ + r)) ℝ).symm.toHomeomorph

def pivotProductSourceN (r : ℕ) (j : κ) : Set ((ι → ℝ) × RankConeN r κ) := {p | p.2.val 0 j ≠ 0}
def pivotProductDomainN (r : ℕ) (j : κ) : Set (RegularCoordinatesN r ι κ) := {p | p.2.1 j ≠ 0}

def pivotProductSplitN (r : ℕ) (j : κ) : pivotProductSourceN (ι := ι) r j ≃ₜ
    (ι → ℝ) × RankPivotN r j where
  toFun p := (p.val.1, ⟨p.val.2.val, p.val.2.property, p.property⟩)
  invFun p := ⟨(p.1, ⟨p.2.val, p.2.property.1⟩), p.2.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)
  continuous_invFun := (continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)).subtype_mk _

def pivotCoordinateFlattenN (r : ℕ) (j : κ) : ((ι → ℝ) × PivotCoordinatesN r j) ≃ₜ
    pivotProductDomainN (ι := ι) r j where
  toFun p := ⟨(p.1, (p.2.1.val, p.2.2)), p.2.1.property⟩
  invFun p := (p.val.1, (⟨p.val.2.1, p.property⟩, p.val.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.prodMk
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd))).subtype_mk _
  continuous_invFun := by fun_prop

def pivotProductChartN (r : ℕ) (j : κ) : OpenEuclideanChart ((ι → ℝ) × RankConeN r κ)
    (Fintype.card ι + Fintype.card κ + r) where
  source := pivotProductSourceN r j
  target := regularCoordinatesEuclideanN r '' pivotProductDomainN r j
  source_open := (isClosed_eq ((continuous_apply j).comp ((continuous_apply 0).comp
    (continuous_subtype_val.comp continuous_snd))) continuous_const).isOpen_compl
  target_open := (regularCoordinatesEuclideanN r).isOpenMap _
    (isClosed_eq (by fun_prop) continuous_const).isOpen_compl
  chart := (((pivotProductSplitN r j).trans
    ((Homeomorph.refl _).prodCongr (rankPivotHomeomorphN r j))).trans
    (pivotCoordinateFlattenN r j)).trans
    (restrictImage (regularCoordinatesEuclideanN r) (pivotProductDomainN r j))

def regularRayN (r : ℕ) (j : κ) (t : ℝ) : (ι → ℝ) × RankConeN r κ :=
  (0, ⟨outer (Fin.cases t 0) (fun k => if k = j then 1 else 0), rank_outer_le_one _ _⟩)

theorem exists_regular_in_openN (r : ℕ) (j : κ) (U : Set ((ι → ℝ) × RankConeN r κ))
    (hU : IsOpen U) (hzero : (0, rankConeZero r) ∈ U) :
    ∃ p : (ι → ℝ) × RankConeN r κ, p ∈ U ∧ p ∈ (pivotProductChartN (ι := ι) r j).source := by
  have h_cont : Continuous (regularRayN (ι := ι) r j) := by
    apply Continuous.prodMk continuous_const
    apply Continuous.subtype_mk
    apply continuous_pi; intro i; apply continuous_pi; intro k
    refine Fin.cases ?_ (fun _ => ?_) i <;> by_cases hkj : k = j <;>
      simp [outer, hkj] <;> fun_prop
  have h_z : regularRayN (ι := ι) r j 0 = (0, rankConeZero r) :=
    Prod.ext rfl (Subtype.ext (by ext i k; refine Fin.cases ?_ (fun _ => ?_) i <;> simp [regularRayN, rankConeZero, outer]))
  have hopen : IsOpen (regularRayN r j ⁻¹' U) := hU.preimage h_cont
  have hz : (0 : ℝ) ∈ regularRayN r j ⁻¹' U := by simpa only [Set.mem_preimage, h_z] using hzero
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hz)
  refine ⟨regularRayN r j (δ / 2), hball ?_, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith
  · change (regularRayN r j (δ / 2)).2.val 0 j ≠ 0; simp [regularRayN, outer]; linarith

end GS.NonmanifoldClosure

namespace GS.NonmanifoldTopology
open GS.NonmanifoldClosure

theorem chart_dimension_of_sphereRetractions
    {X : Type} [TopologicalSpace X] {m n : ℕ}
    (c : OpenEuclideanChart X n) (x : X) (hx : x ∈ c.source)
    (O : Set X) (hO : IsOpen O) (hxO : x ∈ O)
    (hret : SphereRetractionsOn O x m) : n = m := by
  obtain ⟨b, hb⟩ := exists_centeredChart_within c x hx O hO hxO
  obtain ⟨p⟩ := hret b.source b.source_open b.source_point (fun _ h => (hb h).2)
  exact GS.Topology.sphere_retract_ball_dimension m n b.radius_pos
    (transportSectionPair p (Homeomorph.refl _) b.punctured)

theorem dimensions_of_overlapping_charts
    {X : Type} [TopologicalSpace X] {m n : ℕ}
    (c : OpenEuclideanChart X n) (d : OpenEuclideanChart X m)
    (x : X) (hx : x ∈ c.source) (hy : x ∈ d.source) : n = m :=
  chart_dimension_of_sphereRetractions c x hx d.source d.source_open hy
    (d.sphereRetractions x hy)

theorem uniform_neighbourhood_of_compact_parameter
    {A K X : Type*} [TopologicalSpace A] [TopologicalSpace K]
    [TopologicalSpace X] [CompactSpace K]
    (F : A × K → X) (hF : Continuous F) (a : A) (U : Set X)
    (hU : IsOpen U) (ha : ∀ k, F (a, k) ∈ U) :
    ∃ V : Set A, IsOpen V ∧ a ∈ V ∧ ∀ t ∈ V, ∀ k, F (t, k) ∈ U := by
  let C : Set (A × K) := F ⁻¹' Uᶜ
  have hproj : IsClosed (Prod.fst '' C) :=
    isClosedMap_fst_of_compactSpace C (hU.isClosed_compl.preimage hF)
  refine ⟨(Prod.fst '' C)ᶜ, hproj.isOpen_compl, ?_, ?_⟩
  · rintro ⟨⟨t, k⟩, htk, rfl⟩; exact htk (ha k)
  · intro t ht k; by_contra hn; exact ht ⟨(t, k), hn, rfl⟩

structure IsolatedEuclideanRetract (X : Type*) [TopologicalSpace X]
    (x₀ : X) (m : ℕ) where
  sectionMap : Eucl m → X
  projectionMap : X → Eucl m
  section_continuous : Continuous sectionMap
  projection_continuous : Continuous projectionMap
  projection_section : ∀ x, projectionMap (sectionMap x) = x
  section_zero : sectionMap 0 = x₀
  projection_zero_iff : ∀ x, projectionMap x = 0 ↔ x = x₀

variable {X : Type} [TopologicalSpace X] {x₀ : X} {m : ℕ}

theorem IsolatedEuclideanRetract.punctured_sphere
    (r : IsolatedEuclideanRetract X x₀ m)
    (U : Set X) (hU : IsOpen U) (hx : x₀ ∈ U) :
    Nonempty (ContinuousSectionPair (UnitSphere (Fin m)) (PuncturedIn U x₀)) := by
  let F : ℝ × UnitSphere (Fin m) → X := fun p => r.sectionMap (p.1 • p.2.val)
  have hF : Continuous F := r.section_continuous.comp
    (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))
  obtain ⟨V, hV, h0, hVsub⟩ := uniform_neighbourhood_of_compact_parameter F hF 0 U hU
    (fun v => by simpa [F, r.section_zero] using hx)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hV 0 h0
  let t := δ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htV : t ∈ V := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]; dsimp [t]; linarith)
  have hnorm (v : UnitSphere (Fin m)) : ‖v.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using v.property
  have hne (p : PuncturedIn U x₀) : r.projectionMap p.val ≠ 0 :=
    fun he => p.property.2 ((r.projection_zero_iff p.val).mp he)
  refine ⟨{
    sectionMap := fun v => ⟨r.sectionMap (t • v.val), hVsub t htV v, fun he => by
      have hp := congrArg r.projectionMap he
      rw [r.projection_section, (r.projection_zero_iff x₀).mpr rfl] at hp
      have hn := congrArg norm hp
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hnorm v, mul_one, norm_zero] at hn
      exact (ne_of_gt ht) hn⟩
    retractionMap := fun x => ⟨‖r.projectionMap x.val‖⁻¹ • r.projectionMap x.val, by
      simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs]
      rw [abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr (hne x))),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hne x))]⟩
    section_continuous := (r.section_continuous.comp (continuous_subtype_val.const_smul t)).subtype_mk _
    retraction_continuous := by
      apply Continuous.subtype_mk
      exact (((r.projection_continuous.comp continuous_subtype_val).norm).inv₀
        (fun x => norm_ne_zero_iff.mpr (hne x))).smul
        (r.projection_continuous.comp continuous_subtype_val)
    retraction_section := fun v => by
      apply Subtype.ext
      change ‖r.projectionMap (r.sectionMap (t • v.val))‖⁻¹ •
        r.projectionMap (r.sectionMap (t • v.val)) = v.val
      rw [r.projection_section, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        hnorm v, mul_one, smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul] }⟩

theorem not_euclidean_of_retract_regular_charts
    (r : IsolatedEuclideanRetract X x₀ m) (k : ℕ) (hmk : m ≠ k)
    (hregular : ∀ U : Set X, IsOpen U → x₀ ∈ U →
      ∃ c : OpenEuclideanChart X k, ∃ x : X, x ∈ U ∧ x ∈ c.source) :
    ¬ EuclideanAt x₀ := by
  intro he
  obtain ⟨n, c, hc⟩ := (euclideanAt_iff_chart x₀).mp he
  have hn : n = m := chart_dimension_of_sphereRetractions c x₀ hc Set.univ isOpen_univ
    (Set.mem_univ _) (fun U hU hx _ => r.punctured_sphere U hU hx)
  obtain ⟨d, x, hxc, hxd⟩ := hregular c.source c.source_open hc
  exact hmk (hn.symm.trans (dimensions_of_overlapping_charts c d x hxc hxd))

def productIsolatedRetract {κ Y : Type} [Fintype κ] [TopologicalSpace Y]
    (y₀ : Y) (s : (κ → ℝ) → Y) (r : Y → (κ → ℝ))
    (hs : Continuous s) (hr : Continuous r)
    (hrs : ∀ v, r (s v) = v) (hs0 : s 0 = y₀) (hr0 : ∀ y, r y = 0 ↔ y = y₀)
    (e m : ℕ) (hc : Fintype.card (Fin e ⊕ κ) = m) :
    IsolatedEuclideanRetract ((Fin e → ℝ) × Y) (0, y₀) m :=
  let eqv := (Fintype.equivFin (Fin e ⊕ κ)).trans (Equiv.cast (congrArg Fin hc))
  let hE : ((Fin e → ℝ) × (κ → ℝ)) ≃ₜ Eucl m :=
    (sumCoordinates.trans (reindexReal eqv)).trans (EuclideanSpace.equiv (Fin m) ℝ).symm.toHomeomorph
  have hE0 : hE (0, 0) = 0 := by ext i; simp [hE, sumCoordinates, reindexReal]
  { sectionMap := (fun p : (Fin e → ℝ) × (κ → ℝ) => (p.1, s p.2)) ∘ hE.symm
    projectionMap := hE ∘ (fun p : (Fin e → ℝ) × Y => (p.1, r p.2))
    section_continuous := (continuous_fst.prodMk (hs.comp continuous_snd)).comp hE.symm.continuous
    projection_continuous := hE.continuous.comp (continuous_fst.prodMk (hr.comp continuous_snd))
    projection_section := fun x => by simp [hrs]
    section_zero := by
      rw [Function.comp_apply, hE.symm_apply_eq.mpr hE0.symm]
      exact Prod.ext rfl hs0
    projection_zero_iff := fun p => by
      rw [Function.comp_apply, ← hE0, hE.injective.eq_iff, Prod.ext_iff, Prod.ext_iff, hr0] }

theorem cone_not_euclidean (e d : ℕ) (hd : 2 ≤ d) :
    ¬ EuclideanAt (productZero : ConeSpace (Fin e) (Fin d)) := by
  have hd' : d - 2 + 2 = d := Nat.sub_add_cancel hd
  rw [← hd']
  apply not_euclidean_of_retract_regular_charts
    (productIsolatedRetract coneZero (planeToCone (d - 2)) coneToPlane
      (continuous_planeToCone _) continuous_coneToPlane
      (coneToPlane_planeToCone _) (planeToCone_zero _) coneToPlane_eq_zero_iff
      e (e + 2) (by simp))
    (Fintype.card (Fin e) + Fintype.card (Fin (d - 2 + 2)) + 1) (by simp)
  intro U hU h0
  let j : Fin (d - 2 + 2) := ⟨0, by omega⟩
  obtain ⟨p, hpc, hpr⟩ := exists_regular_in_openN 1 j U hU h0
  exact ⟨pivotProductChartN (ι := Fin e) 1 j, p, hpc, hpr⟩

end GS.NonmanifoldTopology

namespace GS.Results
open GS.NonmanifoldCompletion

theorem cone_rankOne_not_euclidean (d e : ℕ) (hd : 2 ≤ d) :
    ¬ EuclideanAtSubset
      {p : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ | p.2.rank ≤ 1} (0, 0) := by
  intro hE
  let S : Set ((Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) := {p | p.2.rank ≤ 1}
  have hz : ((0, 0) : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) ∈ S := by simp [S]
  exact GS.NonmanifoldTopology.cone_not_euclidean e d hd
    ((euclideanAt_homeomorph flattenConeProduct productZero).mpr
      ((euclideanAtSubset_iff S (0, 0) hz).mp hE))

theorem gs_not_euclidean_at {q : ℕ} (hq : 3 ≤ q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j ≠ 0) :
    ¬ EuclideanAtSubset (localFamily q) (basePoint Q₀) := by
  intro hEuclidean
  obtain ⟨g⟩ := original_pointed_open_model (by omega) Q₀ hQ₀ hentries
  have hFamily : EuclideanAt (familyBase Q₀ hQ₀) :=
    (euclideanAtSubset_iff (localFamily q) (basePoint Q₀) (familyBase Q₀ hQ₀).property).mp hEuclidean
  have hFin := (euclideanAt_homeomorph (modelToFin q) (modelCoordinatesZero q)).mp
    ((euclideanAt_pointedOpenModel g).mp hFamily)
  rw [modelToFin_zero] at hFin
  exact GS.NonmanifoldTopology.cone_not_euclidean _ _
    (le_trans (by decide : 2 ≤ 3) (model_width_ge_three q hq)) hFin

def reflectionBase (q : ℕ) : Mat q :=
  fun i j => (if i = j then 1 else 0) - 2 / (q : ℝ)

theorem reflectionBase_apply (q : ℕ) (i j : Fin q) :
    reflectionBase q i j = (if i = j then 1 else 0) - 2 / (q : ℝ) := rfl

theorem reflectionBase_symmetric (q : ℕ) :
    (reflectionBase q)ᵀ = reflectionBase q := by
  ext i j; simp [Matrix.transpose_apply, reflectionBase_apply, eq_comm]

theorem reflectionBase_mul_self (q : ℕ) (hq : 0 < q) :
    reflectionBase q * reflectionBase q = 1 := by
  let C : Mat q := fun _ _ => 2 / (q : ℝ)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hC : C * C = C + C := by ext i j; simp [C, Matrix.mul_apply]; field_simp [hqR]; ring
  change (1 - C) * (1 - C) = 1
  simp only [sub_mul, mul_sub, one_mul, mul_one, hC]; abel

theorem reflectionBase_orthogonal (q : ℕ) (hq : 0 < q) :
    Orthogonal (reflectionBase q) := by
  apply Orthogonal.of_transpose_mul
  rw [reflectionBase_symmetric, reflectionBase_mul_self q hq]

theorem reflectionBase_entries_ne_zero (q : ℕ) (hq : 3 ≤ q)
    (i j : Fin q) : reflectionBase q i j ≠ 0 := by
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := by linarith
  rw [reflectionBase_apply]; split_ifs <;> intro hz <;> field_simp [hq0] at hz <;> linarith

theorem reflectionBase_nonEuclidean (q : ℕ) (hq : 3 ≤ q) :
    basePoint (reflectionBase q) ∈ localFamily q ∧
      ¬ EuclideanAtSubset (localFamily q) (basePoint (reflectionBase q)) := by
  have hQ := reflectionBase_orthogonal q (by omega)
  exact ⟨basePoint_mem_localFamily (reflectionBase q) hQ,
    gs_not_euclidean_at hq (reflectionBase q) hQ (reflectionBase_entries_ne_zero q hq)⟩

theorem exists_nonEuclidean_point (q : ℕ) (hq : 3 ≤ q) :
    ∃ M : Mat (q * 2), M ∈ localFamily q ∧
      ¬ EuclideanAtSubset (localFamily q) M :=
  ⟨basePoint (reflectionBase q), reflectionBase_nonEuclidean q hq⟩

end GS.Results
