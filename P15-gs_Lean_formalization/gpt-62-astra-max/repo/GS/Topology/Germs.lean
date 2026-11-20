module
public import GS.OriginalLocalModel
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
@[expose] public section

/-! Pointed local equivalence, using the ordinary partial-homeomorphism
calculus. Passing to a neighbourhood subtype changes no germ: its interior
embeds openly in both spaces. -/
noncomputable section
open Set Topology
open scoped Topology
namespace GS.Local
variable {X Y Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
abbrev Eucl (n : ℕ) := EuclideanSpace ℝ (Fin n)
def Model (x : X) (y : Y) := ∃ c : OpenPartialHomeomorph X Y, x ∈ c.source ∧ c x = y
variable {x : X} {y : Y} {z : Z} {w : W}
lemma Model.symm : Model x y → Model y x := fun ⟨c,h,e⟩ => e ▸ ⟨c.symm,c.map_source h,c.left_inv h⟩
lemma Model.trans : Model x y → Model y z → Model x z := by
  rintro ⟨c,h,rfl⟩ ⟨d,k,f⟩; exact ⟨c.trans d,⟨h,k⟩,f⟩
lemma Model.prod : Model x y → Model z w → Model (x,z) (y,w) := fun ⟨c,h,e⟩ ⟨d,k,f⟩ => ⟨c.prod d,⟨h,k⟩,Prod.ext e f⟩
lemma homeo (h : X ≃ₜ Y) (x : X) : Model x (h x) := ⟨h.toOpenPartialHomeomorph,trivial,rfl⟩
lemma embedding {f : X → Y} (h : IsOpenEmbedding f) (x : X) : Model x (f x) :=
  have : Nonempty X := ⟨x⟩; ⟨h.toOpenPartialHomeomorph f,trivial,rfl⟩
lemma within {s : Set X} (a : s) (h : s ∈ 𝓝 a.val) : Model a a.val := by
  let b : interior s := ⟨a.val,mem_interior_iff_mem_nhds.mpr h⟩
  exact (embedding (IsOpenEmbedding.inclusion interior_subset (isOpen_interior.preimage continuous_subtype_val)) b).symm.trans (embedding isOpen_interior.isOpenEmbedding_subtypeVal b)
lemma around {s : Set X} {t : Set Y} (h : s ≃ₜ t) (a : s) (hs : s ∈ 𝓝 a.val) (ht : t ∈ 𝓝 (h a).val) : Model a.val (h a).val :=
  (within a hs).symm.trans ((homeo h a).trans (within (h a) ht))

def Euclidean (x : X) := ∃ n, Model x (0 : Eucl n)
lemma Model.move (h : Model x y) : Euclidean x → Euclidean y := fun ⟨n,k⟩ => ⟨n,h.symm.trans k⟩
lemma center {E : Type*} [NormedAddCommGroup E] (a : E) : Model a (0 : E) := by
  exact ⟨(Homeomorph.addRight (-a)).toOpenPartialHomeomorph,trivial,add_neg_cancel a⟩
lemma of_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (c : OpenPartialHomeomorph X E) (hx : x ∈ c.source) : Euclidean x := by
  let n := Module.finrank ℝ E
  let e : E ≃L[ℝ] Eucl n := .ofFinrankEq (by simp [n,Eucl])
  exact ⟨n,Model.trans ⟨c,hx,rfl⟩ ((homeo e.toHomeomorph (c x)).trans (center _))⟩
lemma of_subset {S : Set X} (h : EuclideanAtSubset S x) : Euclidean (⟨x,h.1⟩ : S) := by
  obtain ⟨hx,U,hU,hu,n,V,hV,⟨c⟩⟩ := h
  let a : ↥(S ∩ U) := ⟨x,hx,hu⟩
  have i : IsOpenEmbedding (inclusion (inter_subset_left : S ∩ U ⊆ S)) := .inclusion _ (by
    simpa [preimage_inter] using hU.preimage (continuous_subtype_val (p := (· ∈ S))))
  exact ⟨n,(embedding i a).symm.trans ((homeo c a).trans ((embedding hV.isOpenEmbedding_subtypeVal (c a)).trans (center _)))⟩
end GS.Local
