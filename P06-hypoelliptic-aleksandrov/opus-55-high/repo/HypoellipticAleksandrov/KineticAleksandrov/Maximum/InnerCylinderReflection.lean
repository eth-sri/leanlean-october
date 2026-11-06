module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderGeometry

/-! # Reflected inner cylinders and their exact boundaries -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set

variable {d : ℕ} (S : Set (KineticPoint d)) (Z₀ : KineticPoint d) (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (δ : ℝ) (hδ0 : 0 < δ)

/-- Applying an involutive reflection twice to a set gives the same set. -/
theorem kineticReflection_image_image  :
    kineticReflection '' (kineticReflection '' S) = S := by
  rw [image_image]
  have he : (fun x : KineticPoint d => kineticReflection _) = id :=
    funext kineticReflection_involutive
  simp_all

/-- Closure commutes with the reflection homeomorphism. -/
theorem kineticReflection_image_closure  :
    kineticReflection '' closure S = closure (kineticReflection '' S) :=
  (kineticReflectionHomeomorph d).image_closure S

/-- The inverse reflection maps forward cylinders onto backward cylinders. -/
theorem kineticReflection_image_forwardCylinder  :
    kineticReflection '' forwardCylinder Z₀ R hR =
      backwardCylinder (kineticReflection Z₀) R := by
  have h := congrArg (fun S => kineticReflection '' S)
    (kineticReflection_image_backwardCylinder (kineticReflection Z₀) R hR)
  rw [kineticReflection_image_image, kineticReflection_involutive] at h
  simp_all

/-- The inverse reflection maps exit boundaries onto kinetic boundaries. -/
theorem kineticReflection_image_exitBoundary  :
    kineticReflection '' exitBoundary Z₀ R hR = kineticBoundary (kineticReflection Z₀) R := by
  have h := congrArg (fun S => kineticReflection '' S)
    (kineticReflection_image_kineticBoundary (kineticReflection Z₀) R hR)
  rw [kineticReflection_image_image, kineticReflection_involutive] at h
  exact h.symm

/-- Inner boundary identification uses no arbitrary positive-radius witness. -/
theorem innerExitBoundary_eq_exitBoundary  (hδlt : δ < R ^ 2 / 2) :
    ∃ hr : 0 < innerRatio R hR δ hδ0 hδlt * R,
      innerExitBoundary Z₀ R hR δ hδ0 hδlt =
        exitBoundary (innerCentre Z₀ δ) (innerRatio R hR δ hδ0 hδlt * R) hr := by
  obtain ⟨hr,heq⟩ := innerCylinder_eq_forwardCylinder Z₀ R hR δ hδ0 hδlt
  have hs := (innerRatio_spec R hR δ hδ0 hδlt).2.2
  refine ⟨hr,?_⟩
  ext P
  rw [mem_innerExitBoundary_iff, mem_exitBoundary_iff]
  rw [heq,
    (innerCentre_relative Z₀ P δ).1]
  have ht : (innerCentre Z₀ δ).time + (innerRatio R hR δ hδ0 hδlt * R)^2 =
      Z₀.time+R^2-δ := by simp only [innerCentre]; linarith
  rw [ht]
  simp [PDE.euclideanSphere, PDE.euclideanSqDist, relativeVelocity, innerCentre, mul_pow]

private theorem reflected_innerCentre  :
    kineticReflection (innerCentre (kineticReflection P₀) δ) =
      ⟨P₀.time-δ,P₀.position-δ • P₀.velocity,P₀.velocity⟩ := by
  ext i <;> simp [kineticReflection,innerCentre] <;> ring

/-- Reflection identifies the inner cylinder with a genuine backward cylinder. -/
theorem kineticReflection_image_innerCylinder  (hδlt : δ < R ^ 2 / 2) :
    kineticReflection '' innerCylinder (kineticReflection P₀) R hR δ hδ0 hδlt =
      backwardCylinder
        ⟨P₀.time - δ, P₀.position - δ • P₀.velocity, P₀.velocity⟩
        (innerRatio R hR δ hδ0 hδlt * R) := by
  obtain ⟨hr,h⟩ := innerCylinder_eq_forwardCylinder (kineticReflection P₀) R hR δ hδ0 hδlt
  rw [h,kineticReflection_image_forwardCylinder,reflected_innerCentre]

/-- Reflection of the inner exit boundary is the shifted backward kinetic boundary. -/
theorem kineticReflection_image_innerExitBoundary  (hδlt : δ < R ^ 2 / 2) :
    kineticReflection '' innerExitBoundary (kineticReflection P₀) R hR δ hδ0 hδlt =
      kineticBoundary
        ⟨P₀.time - δ, P₀.position - δ • P₀.velocity, P₀.velocity⟩
        (innerRatio R hR δ hδ0 hδlt * R) := by
  obtain ⟨hr,h⟩ := innerExitBoundary_eq_exitBoundary (kineticReflection P₀) R hR δ hδ0 hδlt
  rw [h,kineticReflection_image_exitBoundary,reflected_innerCentre]

/-- Reflected inner closures lie in the original backward open cylinder. -/
theorem closure_reflected_innerCylinder_subset  (hδlt : δ < R ^ 2 / 2) :
    closure (kineticReflection ''
      innerCylinder (kineticReflection P₀) R hR δ hδ0 hδlt) ⊆ backwardCylinder P₀ R := by
  rw [← kineticReflection_image_closure]
  calc
    kineticReflection '' closure _ ⊆
        kineticReflection '' forwardCylinder _ R hR :=
      image_mono (closure_innerCylinder_subset _ R hR δ hδ0 hδlt)
    _ = backwardCylinder P₀ R := by
      rw [kineticReflection_image_forwardCylinder,kineticReflection_involutive]

/-- Reflected inner closures are compact in the same topology. -/
theorem isCompact_closure_reflected_innerCylinder  (hδlt : δ < R ^ 2 / 2) :
    IsCompact (closure (kineticReflection ''
      innerCylinder (kineticReflection P₀) R hR δ hδ0 hδlt)) := by
  rw [← kineticReflection_image_closure]
  exact (isCompact_closure_innerCylinder _ R hR δ hδ0 hδlt).image
    (continuous_kineticReflection d)

end HypoellipticAleksandrov.KineticAleksandrov
