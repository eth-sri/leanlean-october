module
public import GS.Topology.Regular
public import GS.Topology.Dimension
@[expose] public section

/-! An isolated-zero retract on the matrix cone extends by identity on
free coordinates. A regular pivot in each vertex neighbourhood forces an
incompatible local dimension. -/
noncomputable section
open GS.Local Set Filter
open scoped Topology
namespace GS.RankLocus
variable {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {κ : Type} [Fintype κ] {r : ℕ}
/-- A ray missing the section, even after taking a product with a free factor. -/
theorem obstruction (p : Retract (tip : Locus r κ) E) (e : ℕ) (u : Fin r → ℝ)
    (off : ∀ t > 0, outer u (fun _ : κ => t) ∉ range p.lift) : ¬Euclidean ((0,tip) : Space e r κ) := by
  let m := e + Module.finrank ℝ E
  let h : ((Fin e → ℝ) × E) ≃L[ℝ] Eucl m := .ofFinrankEq (by simp [Eucl,m])
  let π := (ContinuousMap.id (Fin e → ℝ)).prodMap p.project
  let ι := (ContinuousMap.id (Fin e → ℝ)).prodMap p.lift
  let R : Retract ((0,tip) : Space e r κ) (Eucl m) := {
    lift := ι.comp h.symm, project := (⟨h,h.continuous⟩ : C(_,Eucl m)).comp π
    cancel x := by simp [π,ι,Prod.map,p.cancel]
    isolated x := by simp [π,Prod.ext_iff,p.isolated] }
  intro chart
  let f (t : ℝ) : Space e r κ := (0,outer u (fun _ => t))
  have hf : Continuous f := continuous_const.prodMk (Continuous.subtype_mk (by unfold Matrix.vecMulVec; fun_prop) _)
  have h0 : f 0 = (0,tip) := Prod.ext rfl (outer_zero u)
  have hit : ∀ᶠ t in 𝓝[>] (0:ℝ), f t ∈ range R.lift := mem_nhdsWithin_of_mem_nhds (hf.continuousAt.preimage_mem_nhds (by rw [h0]; exact section_fills R chart))
  obtain ⟨t,⟨z,eq⟩,ht⟩ := (hit.and self_mem_nhdsWithin).exists
  exact off t ht ⟨(h.symm z).2,congrArg Prod.snd eq⟩
end GS.RankLocus
