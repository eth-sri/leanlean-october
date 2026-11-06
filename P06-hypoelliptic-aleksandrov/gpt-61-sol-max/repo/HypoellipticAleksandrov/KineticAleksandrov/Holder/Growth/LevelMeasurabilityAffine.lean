module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.LevelMeasurability
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-! # Boundedness and exact set transport for affine level sets -/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set MeasureTheory

variable {d : ℕ}

/-- Every bounded kinetic set has a compact coordinate envelope. -/
theorem bounded_kinetic_compact_envelope  {E : Set (KineticPoint d)}
    (hE : Bornology.IsBounded E) : ∃ K : Set (KineticPoint d), IsCompact K ∧ E ⊆ K := by
  let e := KineticPoint.isometryEquivProd d

  refine ⟨(KineticPoint.homeomorphProd d).symm '' closure (e '' E),
    (e.isometry.lipschitzWith.isBounded_image hE).isCompact_closure.image (KineticPoint.homeomorphProd d).symm.continuous, ?_⟩
  intro P hP
  exact ⟨e P, subset_closure ⟨P, hP, rfl⟩, e.symm_apply_apply P⟩

variable (P0 : KineticPoint d)

/-- A nonzero affine preimage of a bounded kinetic set remains bounded. -/
theorem isBounded_kineticAffine_preimage   {R : ℝ}
    (hR : R ≠ 0) {E : Set (KineticPoint d)} (hE : Bornology.IsBounded E) :
    Bornology.IsBounded (kineticAffine P0 R ⁻¹' E) := by
  obtain ⟨K, hK, hEK⟩ := bounded_kinetic_compact_envelope hE
  exact ((kineticAffineHomeomorph P0 R hR).isCompact_preimage.mpr hK).isBounded.subset
    (preimage_mono hEK)

variable (R : ℝ) {E : Set (KineticPoint d)}

/-- Affine images of bounded kinetic sets have compact coordinate envelopes. -/
theorem isBounded_kineticAffine_image    (hE : Bornology.IsBounded E) :
    Bornology.IsBounded (kineticAffine P0 R '' E) := by
  obtain ⟨K, hK, hEK⟩ := bounded_kinetic_compact_envelope hE
  exact (hK.image (continuous_kineticAffine P0 R)).isBounded.subset (image_mono hEK)

/-- Affine pullbacks of measurable levels are measurable in the same Lebesgue space. -/
theorem measurableSet_kineticAffine_preimage    (hE : MeasurableSet E) :
    MeasurableSet (kineticAffine P0 R ⁻¹' E) :=
  hE.preimage (continuous_kineticAffine P0 R).measurable

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
