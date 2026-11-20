module

public import GS.OriginalLocalModel
public import GS.Core
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import GS.Topology.RankOne
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

noncomputable section

section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A pointed homeomorphism of neighbourhoods of the FULL GS family

The source contains a neighbourhood in localFamily itself. The target contains a neighbourhood in
the independent skew-coordinate cone model. Both neighbourhood claims are
proved using full-fibre coverage and estimates for the g map.

Neighbourhoods are not asserted to be open: the source and target may be the
compact images. A homeomorphism of these neighbourhoods is an equivalence of
the pointed local topological spaces. A final EuclideanAtSubset contradiction
still needs the topological cone obstruction and a restriction/transport lemma.

-/
open Matrix Filter GS
open scoped Topology
namespace GS.NonmanifoldCompletion

/-- Explicit pointed homeomorphism between neighbourhood subsets. -/
structure PointedNeighbourhoodModel (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] (x : X) (y : Y) where
  source : Set X
  target : Set Y
  source_nhds : source ∈ 𝓝 x
  target_nhds : target ∈ 𝓝 y
  chart : ↥source ≃ₜ ↥target
  map_point : ∀ hx : x∈source, (chart ⟨x,hx⟩).val = y

end GS.NonmanifoldCompletion

end

section

set_option autoImplicit false
open Set Topology
open scoped Topology
namespace GS.NonmanifoldFinal

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]


variable {ι κ : Type*}

/-- Relate the product of a cone subtype to the ambient subset in the ORIGINAL
ConeProductNonManifoldGoal, not to a replacement definition of the cone. -/
def flattenConeProduct [Fintype ι] [Fintype κ] :
    ((ι → ℝ) × RankOne 1 κ) ≃ₜ
      {p : (ι → ℝ) × Matrix (Fin 2) κ ℝ // p.2.rank ≤ 1} where
  toFun p := ⟨(p.1,p.2.val),p.2.property⟩
  invFun p := (p.val.1,⟨p.val.2,p.property⟩)
  left_inv p := rfl
  right_inv p := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    fun_prop


abbrev Eucl (n : ℕ) := EuclideanSpace ℝ (Fin n)

def EuclideanAt (x : X) : Prop :=
  ∃ n, ∃ e : OpenPartialHomeomorph X (Eucl n), x ∈ e.source

/-- Extend a homeomorphism between nonempty open subspaces to a chart. -/
def openBetween {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : IsOpen t)
    (e : s ≃ₜ t) (x : s) : OpenPartialHomeomorph X Y :=
  (((⟨s,hs⟩ : TopologicalSpace.Opens X).openPartialHomeomorphSubtypeCoe ⟨x⟩).symm.transHomeomorph e).trans
    ((⟨t,ht⟩ : TopologicalSpace.Opens Y).openPartialHomeomorphSubtypeCoe ⟨e x⟩)

@[simp] theorem openBetween_source {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : IsOpen t)
    (e : s ≃ₜ t) (x : s) : (openBetween hs ht e x).source = s := by
  simp [openBetween]

/-- Flatten an ambient restriction of a subtype. -/
def subtypeOpenIntersection (S U : Set X) : ↥(Subtype.val ⁻¹' U : Set S) ≃ₜ ↥(S ∩ U) where
  toEquiv := Equiv.subtypeSubtypeEquivSubtypeInter _ _
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem euclideanAtSubset_iff (S : Set X) (x : X) (hx : x ∈ S) :
    GS.EuclideanAtSubset S x ↔ EuclideanAt (⟨x,hx⟩ : S) := by
  constructor
  · rintro ⟨_,U,hU,hxU,n,V,hV,⟨h⟩⟩
    refine ⟨n, openBetween (hU.preimage continuous_subtype_val) hV
      ((subtypeOpenIntersection S U).trans h) ⟨⟨x,hx⟩,hxU⟩, ?_⟩
    rw [openBetween_source]
    exact hxU
  · rintro ⟨n,c,hc⟩
    obtain ⟨U,hU,hUA⟩ := isOpen_induced_iff.mp c.open_source
    refine ⟨hx,U,hU,?_,n,c.target,c.open_target,⟨?_⟩⟩
    · grind
    · exact (subtypeOpenIntersection S U).symm.trans
        ((Homeomorph.setCongr hUA).trans c.toHomeomorphSourceTarget)

theorem euclideanAt_partial (e : OpenPartialHomeomorph X Y) {x : X} (hx : x ∈ e.source) :
    EuclideanAt x ↔ EuclideanAt (e x) := by
  constructor
  · rintro ⟨n,c,hc⟩
    refine ⟨n,e.symm.trans c,⟨e.map_source hx,?_⟩⟩
    aesop
  · rintro ⟨n,c,hc⟩
    exact ⟨n,e.trans c,⟨hx,hc⟩⟩

theorem euclideanAt_homeomorph (h : X ≃ₜ Y) (x : X) :
    EuclideanAt x ↔ EuclideanAt (h x) :=
  euclideanAt_partial h.toOpenPartialHomeomorph (Set.mem_univ x)

theorem euclideanAt_of_homeomorph (h : X ≃ₜ Y) (x : X) : EuclideanAt x → EuclideanAt (h x) :=
  (euclideanAt_homeomorph h x).mp

theorem euclideanAt_openEmbedding {f : X → Y} (hf : Topology.IsOpenEmbedding f) (x : X) :
    EuclideanAt x ↔ EuclideanAt (f x) := by
  let : Nonempty X := ⟨x⟩
  simpa only [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply] using
    euclideanAt_partial (hf.toOpenPartialHomeomorph f) (Set.mem_univ x)

theorem euclideanAt_nhds {s : Set X} {x : X} (h : s ∈ 𝓝 x) :
    EuclideanAt (⟨x,mem_of_mem_nhds h⟩ : s) ↔ EuclideanAt x := by
  let a : interior s := ⟨x,mem_interior_iff_mem_nhds.mpr h⟩
  exact (euclideanAt_openEmbedding (Topology.IsOpenEmbedding.inclusion interior_subset
    (isOpen_interior.preimage continuous_subtype_val)) a).symm.trans
    (euclideanAt_openEmbedding isOpen_interior.isOpenEmbedding_subtypeVal a)

theorem euclideanAt_neighbourhoodModel {x : X} {y : Y}
    (g : GS.NonmanifoldCompletion.PointedNeighbourhoodModel X Y x y) : EuclideanAt x ↔ EuclideanAt y := by
  let a : g.source := ⟨x,mem_of_mem_nhds g.source_nhds⟩
  rw [← euclideanAt_nhds g.source_nhds, euclideanAt_homeomorph g.chart a]
  have h : g.chart a = ⟨y,mem_of_mem_nhds g.target_nhds⟩ := Subtype.ext (g.map_point a.property)
  rw [h, euclideanAt_nhds g.target_nhds]

end GS.NonmanifoldFinal

end
