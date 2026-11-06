module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationReflectionMeasure
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationHomogeneity
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! # Preservation of the stationary adjoint equation under simultaneous reflection -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/- Simultaneous position–velocity reflection preserves the stationary adjoint equation. -/
theorem IsBellmanStationaryAdjointPair.reflect {μ η }
    (hpair : IsBellmanStationaryAdjointPair μ η) :
    IsBellmanStationaryAdjointPair (Measure.map bellmanReflection μ)
      (Measure.map bellmanReflection η) := by
  intro φ hφ hc hs
  let ψ := fun q : ℝ × ℝ => φ (-q)
  have hψ := hφ.comp contDiff_neg
  have hcψ : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.neg (ℝ × ℝ))
  have hsψ : tsupport ψ ⊆ {q : ℝ × ℝ | q ≠ (0, 0)} := by
    intro q hq hzero
    have hn := hs ((tsupport_comp_subset_preimage φ continuous_neg) hq)
    apply hn
    rw [hzero]
    simp only [Prod.neg_mk, neg_zero]
  have he := hpair ψ hψ hcψ hsψ
  rw [bellmanReflection.measurableEmbedding.integral_map,
    bellmanReflection.measurableEmbedding.integral_map]
  have htransport : (fun q : BellmanPuncturedPlane =>
      (bellmanReflection q).val.2 * fderiv ℝ φ (bellmanReflection q).val (1, 0)) =
      (fun q => q.val.2 * fderiv ℝ ψ q.val (1, 0)) := by
    funext q
    change (-q.val.2) * fderiv ℝ φ (-q.val) (1, 0) =
      q.val.2 * fderiv ℝ (fun z => φ (-z)) q.val (1, 0)
    rw [bellman_reflected_fderiv φ hφ]
    ring
  have hvv : (fun q : BellmanPuncturedPlane =>
      fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) (bellmanReflection q).val (0, 1)) =
      (fun q => fderiv ℝ (fun z => fderiv ℝ ψ z (0, 1)) q.val (0, 1)) := by
    funext q
    have _h_xinl_0 : fderiv ℝ (fun z => fderiv ℝ (fun w => φ (-w)) z (0, 1)) q.val (0, 1) =
      fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) (-q.val) (0, 1) := by
      let q := q.val
      have hjet := bellman_contDiff_direction hφ (0, 1)
      have he : (fun z => fderiv ℝ (fun w => φ (-w)) z (0, 1)) =
          (fun z => -(fderiv ℝ φ (-z) (0, 1))) := by
        funext z
        exact bellman_reflected_fderiv φ hφ z (0, 1)
      let g := fun z => fderiv ℝ φ z (0, 1)
      have hd := ((hjet.differentiable (by simp) (-q)).hasFDerivAt.comp q
        ((hasFDerivAt_id q).neg)).neg
      rw [he]
      change fderiv ℝ (-(g ∘ Neg.neg)) q (0, 1) = _
      rw [hd.fderiv]
      change -(fderiv ℝ g (-q) (-(0, 1))) = fderiv ℝ g (-q) (0, 1)
      rw [map_neg, neg_neg]
    exact _h_xinl_0.symm
  rw [htransport, hvv]
  exact he

/- Reflection preserves the complete genuine homogeneous adjoint-pair condition. -/
theorem IsBellmanAdjointPair.reflect {R β μ η}
    (hp : IsBellmanAdjointPair 1 R β μ η) :
    IsBellmanAdjointPair 1 R β (Measure.map bellmanReflection μ)
      (Measure.map bellmanReflection η) := by
  refine ⟨hp.1.reflect, hp.2.1.reflect, Or.inl ?_, ?_, ?_, hp.2.2.2.2.2.1.reflect,
    hp.2.2.2.2.2.2.1.reflect, hp.2.2.2.2.2.2.2.reflect⟩
  · intro he
    apply hp.left_ne_zero
    apply bellmanReflection.measurableEmbedding.map_injective
    simpa only [Measure.map_zero] using he
  · have he := Measure.map_mono hp.2.2.2.1 bellmanReflection.measurable
    rwa [Measure.map_smul _ bellmanReflection.measurable.aemeasurable] at he
  · have he := Measure.map_mono hp.2.2.2.2.1 bellmanReflection.measurable
    rwa [Measure.map_smul _ bellmanReflection.measurable.aemeasurable] at he

end HypoellipticAleksandrov.KineticAleksandrov
