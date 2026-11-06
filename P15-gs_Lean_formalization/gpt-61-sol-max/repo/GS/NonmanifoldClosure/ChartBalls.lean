
import GS.NonmanifoldClosure.PuncturedBall
import GS.NonmanifoldFinal.EuclideanTransport
import GS.NonmanifoldFinal.RetractTransport




/-!
# Euclidean charts restricted to centered balls

The dimension of a given chart is retained throughout. No dimension-invariance
principle is invoked. Centering and restriction are explicit homeomorphisms.
-/
open GS.NonmanifoldObstruction GS.NonmanifoldFinal
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

/-- Centered charts always have an open source and an actual open norm-ball target. -/
structure CenteredEuclideanChart (X : Type*) [TopologicalSpace X] (x : X) (n : ℕ) where
  source : Set X
  source_open : IsOpen source
  source_point : x ∈ source
  radius : ℝ
  radius_pos : 0 < radius
  chart : source ≃ₜ NormBall n radius
  map_point : ∀ hx : x ∈ source, (chart ⟨x,hx⟩).val = 0

/-- Restriction preserves the stated dimension and the ambient subspace topologies. -/
def OpenEuclideanChart.restrict (c : OpenEuclideanChart X n)
    (U : Set X) (hU : IsOpen U) : OpenEuclideanChart X n := by
  let A : Set c.source := Subtype.val ⁻¹' U
  let B := c.chart '' A
  have hA : IsOpen A := hU.preimage continuous_subtype_val
  have hB := c.chart.isOpenMap A hA
  exact
    { source := c.source ∩ U
      target := Subtype.val '' B
      source_open := c.source_open.inter hU
      target_open := c.target_open.isOpenMap_subtype_val B hB
      chart := ((subtypeOpenIntersection c.source U).symm.trans
        (c.chart.image A)).trans (flattenImage c.target B) }

theorem euclideanAt_iff_chart (x : X) :
    EuclideanAt x ↔ ∃ n, ∃ c : OpenEuclideanChart X n, x ∈ c.source := by
  constructor
  · rintro ⟨U,hU,hx,n,V,hV,⟨h⟩⟩
    exact ⟨n,⟨U,V,hU,hV,h⟩,hx⟩
  · rintro ⟨n,c,hx⟩
    exact ⟨c.source,c.source_open,hx,n,c.target,c.target_open,⟨c.chart⟩⟩

/-- Every chart can be centered at any point of its source. -/
theorem exists_centeredChart (c : OpenEuclideanChart X n)
    (x : X) (hx : x ∈ c.source) :
    ∃ b : CenteredEuclideanChart X x n, b.source ⊆ c.source := by
  let a₀ : c.source := ⟨x,hx⟩
  let y : Eucl n := (c.chart a₀).val
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    (c.target_open.mem_nhds (c.chart a₀).property)
  let A : Set c.source := {a | ‖(c.chart a).val - y‖ < r}
  have hA : IsOpen A := isOpen_Iio.preimage
    (((continuous_subtype_val.comp c.chart.continuous).sub continuous_const).norm)
  have ha₀ : a₀ ∈ A := by aesop
  have hf :=
    (Homeomorph.subRight y).isEmbedding.comp
      (Topology.IsEmbedding.subtypeVal.comp c.chart.isEmbedding)
  let e := hf.homeomorphOfSubsetRange (s := {z : Eucl n | ‖z‖ < r}) (by
    intro z hz
    have hmem : y+z ∈ c.target := hball (by aesop)
    exact ⟨c.chart.symm ⟨y+z,hmem⟩, by simp⟩)
  let S := Subtype.val '' A
  have hS := c.source_open.isOpenMap_subtype_val A hA
  have hxS : x ∈ S := ⟨a₀,ha₀,rfl⟩
  let b : CenteredEuclideanChart X x n :=
    { source := S
      source_open := hS
      source_point := hxS
      radius := r
      radius_pos := hr
      chart := (flattenImage c.source A).symm.trans e
      map_point := by
        intro hx'
        
        exact sub_self y }
  exact ⟨b,by aesop⟩



/-- Removing the chart center gives exactly the punctured ball, not the complement
of an entire singular stratum. -/
def CenteredEuclideanChart.punctured {x : X} (c : CenteredEuclideanChart X x n) :
    PuncturedIn c.source x ≃ₜ PuncturedNormBall (Eucl n) c.radius := by
  refine ((subtypeOpenIntersection c.source {a | a ≠ x}).symm.trans
    (c.chart.subtype ?_)).trans
      (subtypeOpenIntersection {z : Eucl n | ‖z‖ < c.radius} {z | z ≠ 0})
  intro a
  
  rw [← c.map_point c.source_point]
  apply not_congr
  change a.val = (⟨x,c.source_point⟩ : c.source).val ↔ _
  rw [← Subtype.ext_iff, ← Subtype.ext_iff, c.chart.injective.eq_iff]

end GS.NonmanifoldClosure
