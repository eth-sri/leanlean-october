module
public import GS.Spectral.Dimensions
@[expose] public section

/-! Transport from the actual shuffle family through the spectral patch. The
outer unitary frames are smooth factors; pack their coordinates together with
the free centre before applying a cone obstruction. -/
noncomputable section
open GS.Isometric GS.Local
open Matrix Set
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace GS.Spectral
variable {𝕜 : Type} [RCLike 𝕜] {q r : ℕ}
private lemma outer_chart (o : Fin q) (p : Outer 𝕜 o) : Euclidean p :=
  of_chart
    ((OpenPartialHomeomorph.pi fun i => groupChart (p.1 i)).prod (OpenPartialHomeomorph.pi fun j => groupChart (p.2 j)))
    ⟨fun _ _ => groupChart_source _,fun _ _ => groupChart_source _⟩

variable (Q : U 𝕜 q) (o : Fin q) (hne : ∀ i j, Q.val i j ≠ 0)
include hne in
lemma family_singularity (e : (ℝ × 𝕜) ≃L[ℝ] V r)
    (bad : ∀ n, ¬Euclidean ((0 : V n),(vertex : Target r (Width Q o)).2)) :
    unflat.symm (base Q) ∈ Family 𝕜 q ∧ ¬EuclideanAtSubset (Family 𝕜 q) (unflat.symm (base Q)) := by
  let x := familyBlocks.symm (marked Q o)
  refine ⟨x.property,fun hx => ?_⟩
  have g := local_model Q o hne (Classical.choice (slice_patch Q o hne)) e
  obtain ⟨n,k⟩ := outer_chart o (1 : Outer 𝕜 o)
  let d := Width Q o
  let lin : (Eucl n × V d) ≃L[ℝ] V (n+d) := ContinuousLinearEquiv.ofFinrankEq (E := Eucl n × V d) (F := V (n+d)) (by simp [Eucl,V])
  let c := (Homeomorph.prodAssoc (Eucl n) (V d) (Cone r d)).symm.trans (lin.toHomeomorph.prodCongr (Homeomorph.refl _))
  apply bad
  have h : Euclidean x := of_subset hx
  have hb : Euclidean (marked Q o) := by simpa [x] using (homeo familyBlocks x).move h
  have hu := (k.prod (homeo (Homeomorph.refl _) vertex)).move (g.move hb)
  have hz : c (0,vertex) = (0,(vertex : Target r d).2) := Prod.ext (map_zero lin) rfl
  exact hz ▸ (homeo c _).move hu
end GS.Spectral
