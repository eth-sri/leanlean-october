module

public import GS.NonmanifoldClosure.PuncturedBall
public import GS.NonmanifoldFinal.EuclideanTransport
public import GS.NonmanifoldFinal.RetractTransport

@[expose] public section



/-!
# Euclidean charts restricted to centered balls

The dimension of a given chart is retained throughout. No dimension-invariance
principle is invoked. Centering and restriction are explicit homeomorphisms.
-/
noncomputable section
open GS.NonmanifoldObstruction GS.NonmanifoldFinal
namespace GS.NonmanifoldClosure

variable {X : Type*} [TopologicalSpace X]
section
variable (n : ℕ)
abbrev Eucl := EuclideanSpace ℝ (Fin n)
abbrev NormBall (r : ℝ) := {z : Eucl n // ‖z‖ < r}

end

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
def OpenEuclideanChart.restrict {n : ℕ} (c : OpenEuclideanChart X n)
    (U : Set X) (hU : IsOpen U) : OpenEuclideanChart X n where
  source := c.source ∩ U
  target := Subtype.val '' (c.chart '' (Subtype.val ⁻¹' U))
  source_open := c.source_open.inter hU
  target_open := c.target_open.isOpenMap_subtype_val _ (c.chart.isOpenMap _ (hU.preimage continuous_subtype_val))
  chart := ((subtypeOpenIntersection c.source U).symm.trans (Homeomorph.image c.chart _)).trans
    (flattenImage c.target _)

theorem euclideanAt_iff_chart (x : X) :
    EuclideanAt x ↔ ∃ n, ∃ c : OpenEuclideanChart X n, x ∈ c.source :=
  ⟨fun ⟨U,hU,hx,n,V,hV,⟨h⟩⟩ => ⟨n,⟨U,V,hU,hV,h⟩,hx⟩,
    fun ⟨n,c,hx⟩ => ⟨c.source,c.source_open,hx,n,c.target,c.target_open,⟨c.chart⟩⟩⟩

section
variable {n : ℕ} (c : OpenEuclideanChart X n) (x : X)
/-- Every chart can be centered at any point of its source. -/
theorem exists_centeredChart (hx : x ∈ c.source) :
    ∃ b : CenteredEuclideanChart X x n, b.source ⊆ c.source := by
  let y : Eucl n := (c.chart ⟨x,hx⟩).val
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (c.target_open.mem_nhds (c.chart ⟨x,hx⟩).property)
  let A : Set c.source := {a | ‖(c.chart a).val - y‖ < r}
  have hA : IsOpen A := isOpen_lt (by fun_prop) continuous_const
  let e : A ≃ₜ NormBall n r :=
    { toFun a := ⟨(c.chart a.val).val-y,a.property⟩
      invFun z := ⟨c.chart.symm ⟨y+z.val, hball (by simpa [y, dist_eq_norm] using z.property)⟩, by simpa [A] using z.property⟩
      left_inv a := by simp
      right_inv z := by simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact ⟨⟨_, c.source_open.isOpenMap_subtype_val A hA, ⟨⟨x,hx⟩, by simpa [A,y] using hr, rfl⟩, r, hr,
    (flattenImage c.source A).symm.trans e, fun _ => sub_self y⟩, by rintro z ⟨a,ha,rfl⟩; exact a.property⟩

/-- The centered source can additionally be required to lie in any prescribed
open neighborhood. This is used at both the singular and the regular point. -/
theorem exists_centeredChart_within (hx : x ∈ c.source) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ b : CenteredEuclideanChart X x n, b.source ⊆ c.source ∩ U :=
  exists_centeredChart (c.restrict U hU) x (by tauto)

end

/-- Removing the chart center gives exactly the punctured ball, not the complement
of an entire singular stratum. -/
def CenteredEuclideanChart.punctured {x : X} {n : ℕ}
    (c : CenteredEuclideanChart X x n) :
    PuncturedIn c.source x ≃ₜ PuncturedNormBall (Eucl n) c.radius where
  toFun p := ⟨(c.chart ⟨p.val,p.property.1⟩).val, by grind, by
    rw [← c.map_point c.source_point, Ne, ← Subtype.ext_iff, c.chart.injective.eq_iff]
    simpa using p.property.2⟩
  invFun z := ⟨(c.chart.symm ⟨z.val,z.property.1⟩).val, by simp, fun he => z.property.2 (by
    simpa [c.map_point] using congrArg (c.chart · |>.val) (Subtype.ext he : _ = (⟨x,c.source_point⟩ : c.source)))⟩
  left_inv p := by simp
  right_inv z := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end GS.NonmanifoldClosure
