module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionAPI
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderReflection
import Mathlib.Tactic

/-! # Compact closures and nonempty source comparison boundaries -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

variable {d : ℕ} (P₀ : KineticPoint d) {R : ℝ}

/-- Backward-cylinder closures are compact in physical coordinates. -/
theorem isCompact_closure_backwardCylinder  (R : ℝ) (hR : 0 < R) :
    IsCompact (closure (backwardCylinder P₀ R)) := by
  have h := (isCompact_closure_forwardCylinder (kineticReflection P₀) R hR).image
    (continuous_kineticReflection d)
  rw [kineticReflection_image_closure, kineticReflection_image_forwardCylinder,
    kineticReflection_involutive] at h
  exact h

/-- Every positive-radius source cylinder is nonempty. -/
theorem backwardCylinder_nonempty  (hR : 0 < R) : (backwardCylinder P₀ R).Nonempty := by
  refine ⟨⟨P₀.time - R ^ 2 / 2, P₀.position - (R ^ 2 / 2) • P₀.velocity,
    P₀.velocity⟩, ?_⟩
  refine ⟨?_, ?_, PDE.center_mem_euclideanBall _ hR, ?_⟩
  · simp_all
  · simp_all
  · have heq : relativePosition P₀
        ⟨P₀.time - R ^ 2 / 2, P₀.position - (R ^ 2 / 2) • P₀.velocity,
          P₀.velocity⟩ = 0 := by
      simp [relativePosition]
    rw [heq]
    exact PDE.center_mem_euclideanBall 0 (pow_pos hR 3)

/-- The bottom centre belongs to the source kinetic boundary. -/
theorem bottom_mem_kineticBoundary  (hR : 0 < R) :
    (⟨P₀.time-R^2, P₀.position-R^2 • P₀.velocity, P₀.velocity⟩ : KineticPoint d) ∈
      kineticBoundary P₀ R := by
  let f : ℝ → KineticPoint d := fun t =>
    ⟨t, P₀.position + (t-P₀.time) • P₀.velocity, P₀.velocity⟩
  have hf : Continuous f := KineticPoint.continuous_mk continuous_id
    (continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const))
    continuous_const
  have hsub : f '' Ioo (P₀.time-R^2) P₀.time ⊆ backwardCylinder P₀ R := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨ht.1, ht.2, PDE.center_mem_euclideanBall _ hR, ?_⟩
    have heq : relativePosition P₀ (f t) = 0 := by
      simp [relativePosition, f]
    rw [heq]
    exact PDE.center_mem_euclideanBall 0 (pow_pos hR 3)
  have ht : P₀.time-R^2 ∈ closure (Ioo (P₀.time-R^2) P₀.time) := by
    rw [closure_Ioo (sub_lt_self _ (sq_pos_of_pos hR)).ne]
    exact ⟨le_rfl, sub_le_self _ (sq_nonneg R)⟩
  have hm := closure_mono hsub (hf.continuousOn.image_closure
    (mem_image_of_mem f ht))
  aesop

/-- Comparison boundaries are nonempty for every positive radius. -/
theorem kineticBoundary_nonempty  (hR : 0 < R) : (kineticBoundary P₀ R).Nonempty :=
  ⟨_, bottom_mem_kineticBoundary P₀ hR⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder
