module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderUniform
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderReflection

/-! # The reflected affine maps used in the Borel-coefficient boundary passage -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set

variable {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (δ : ℝ) (hδ0 : 0 < δ)

private theorem reflection_closure_backward  :
    kineticReflection '' closure (backwardCylinder P₀ R) =
      closure (forwardCylinder (kineticReflection P₀) R hR) := by
  rw [kineticReflection_image_closure,
    kineticReflection_image_backwardCylinder]

/-- Reflected retraction maps the original closure onto the inner backward closure. -/
theorem reflectedInnerRetraction_image_closure  (hδlt : δ < R ^ 2 / 2) :
    reflectedInnerRetraction P₀ R hR δ hδ0 hδlt '' closure (backwardCylinder P₀ R) =
      closure (backwardCylinder
        ⟨P₀.time - δ, P₀.position - δ • P₀.velocity, P₀.velocity⟩
        (innerRatio R hR δ hδ0 hδlt * R)) := by
  change (kineticReflection ∘ (innerRetraction _ R hR δ hδ0 hδlt ∘
    kineticReflection)) '' _ = _
  simp only [Function.comp_def]
  rw [← image_image,
    ← image_image (innerRetraction _ R hR δ hδ0 hδlt), reflection_closure_backward P₀ R hR,
    innerRetraction_image_closure,kineticReflection_image_closure,
    kineticReflection_image_innerCylinder]

/-- Reflected retraction is onto the inner kinetic boundary used by Borel passage. -/
theorem reflectedInnerRetraction_image_kineticBoundary  (hδlt : δ < R ^ 2 / 2) :
    reflectedInnerRetraction P₀ R hR δ hδ0 hδlt '' kineticBoundary P₀ R =
      kineticBoundary
        ⟨P₀.time - δ, P₀.position - δ • P₀.velocity, P₀.velocity⟩
        (innerRatio R hR δ hδ0 hδlt * R) := by
  change (kineticReflection ∘ (innerRetraction _ R hR δ hδ0 hδlt ∘
    kineticReflection)) '' _ = _
  simp only [Function.comp_def]
  rw [← image_image,
    ← image_image (innerRetraction _ R hR δ hδ0 hδlt), kineticReflection_image_kineticBoundary P₀ R hR,
    innerRetraction_image_exitBoundary,kineticReflection_image_innerExitBoundary]

/-- Reflection preserves the existing product-metric distance, used only topologically. -/
theorem dist_kineticReflection  (P Q : KineticPoint d) :
    dist (kineticReflection P) (kineticReflection Q) = dist P Q := by
  change dist (-P.time,(-P.position,P.velocity)) (-Q.time,(-Q.position,Q.velocity)) =
    dist (P.time,(P.position,P.velocity)) (Q.time,(Q.position,Q.velocity))
  simp only [Prod.dist_eq, dist_neg_neg]

/-- Uniform convergence of reflected retractions on the original backward closure. -/
theorem reflectedInnerRetraction_uniformly_to_identity  :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2), δ < η →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          dist (reflectedInnerRetraction P₀ R hR δ hδ0 hδlt P) P < ε := by
  intro ε hε
  obtain ⟨η,hη,he⟩ := innerRetraction_uniformly_to_identity (kineticReflection P₀) R hR ε hε
  refine ⟨η,hη,?_⟩
  intro δ hδ0 hδlt hδη P hP
  have hp : kineticReflection P ∈ closure (forwardCylinder (kineticReflection P₀) R hR) := by
    rw [← reflection_closure_backward]
    grind
  have h := he δ hδ0 hδlt hδη _ hp
  have hd := dist_kineticReflection
    (innerRetraction (kineticReflection P₀) R hR δ hδ0 hδlt (kineticReflection P))
    (kineticReflection P)
  rw [kineticReflection_involutive] at hd
  change dist (kineticReflection
    _) P < ε
  simp_all

end HypoellipticAleksandrov.KineticAleksandrov
