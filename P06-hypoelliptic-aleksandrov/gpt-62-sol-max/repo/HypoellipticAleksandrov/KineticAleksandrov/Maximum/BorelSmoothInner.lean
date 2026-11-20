module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelInnerError
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

/-! # Passing the coefficient limit on a fixed compact inner cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped MatrixOrder Matrix.Norms.Elementwise Topology ENNReal

/-- The coefficient limit preserves the complete source estimate on a fixed inner cylinder. -/
theorem borel_smooth_inner_limit {d : ℕ} (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (p : ℝ) (hp : 1 ≤ p) (alpha C₀ : ℝ) (localised : Bool)
    (hsmooth : BorelSmoothEstimate (d := d) lam Lam p alpha C₀ localised)
    (A : CoefficientField d) (hBorel : IsBorelCoefficient A)
    (hlo : HasLowerEllipticityAE lam A) (hhi : HasUpperEllipticityAE Lam A)
    (C : ℕ → CoefficientField d)
    (hC : ∀ j, IsSmoothCoefficient (C j) ∧ IsSymmetricCoefficient (C j) ∧
      HasLowerEllipticity lam (C j) ∧ HasUpperEllipticity Lam (C j))
    (hc : ∀ᵐ z ∂(volume : Measure (ℝ × PDE.Vec d)),
      Tendsto (fun j => coefficientAt (C j) z) atTop (𝓝 (coefficientAt A z)))
    {D : Set (KineticPoint d)} (u f : KineticPoint d → ℝ) (hreg : IsKineticC112On u D)
    (P₁ : KineticPoint d) (r : ℝ) (hr : 0 < r)
    (hK : IsCompact (closure (backwardCylinder P₁ r)))
    (hKD : closure (backwardCylinder P₁ r) ⊆ D) (hf : Measurable f)
    (hLp : MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₁ r)))
    (hsub : ∀ᵐ P ∂(volume.restrict (backwardCylinder P₁ r)),
      backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) :
    ∀ P ∈ closure (backwardCylinder P₁ r), u P ≤
      sSup ((fun P => max (u P) 0) '' kineticBoundary P₁ r) + C₀ * r ^ alpha *
      (eLpNorm (borelSource localised u f) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₁ r))).toReal := by
  classical
  let Q := backwardCylinder P₁ r
  let K := closure Q
  let H := kineticVelocityHessian u
  have hH : ContinuousOn H K := hreg.continuousOn_kineticVelocityHessian.mono hKD
  have hregQ := _root_.HypoellipticAleksandrov.Parabolic.IsKineticC112On.mono hreg (subset_closure.trans hKD)
  obtain ⟨_, hme, hte⟩ := borel_inner_error hlam hLam A hBorel hlo hhi C hC hc K hK H hH (zero_lt_one.trans_le hp)
  refine borel_estimate_of_defect (isOpen_backwardCylinder P₁ r hr) subset_closure hp localised
    hregQ.continuousOn hf hLp (e := fun j => borelCoefficientError (C j) A H) (fun _ _ => abs_nonneg _)
    hme hte ?_
  intro j g hgm hgp hg
  apply hsmooth (C j) (hC j).1 (hC j).2.1 (hC j).2.2.1 (hC j).2.2.2
    P₁ r hr u (f + g) (hreg.continuousOn.mono hKD) hregQ (hf.add hgm) hgp
  filter_upwards [hsub, hg] with P hP hEq
  have hd := borel_backwardOperator_sub (C j) A u P
  change backwardOperatorOfTimeVelocityCoefficient (C j) u P ≤ f P + g P
  rw [hEq]
  dsimp only [borelCoefficientError, H]
  have herror := hd.le.trans (neg_le_abs _)
  linarith only [herror, hP]

end HypoellipticAleksandrov.KineticAleksandrov
