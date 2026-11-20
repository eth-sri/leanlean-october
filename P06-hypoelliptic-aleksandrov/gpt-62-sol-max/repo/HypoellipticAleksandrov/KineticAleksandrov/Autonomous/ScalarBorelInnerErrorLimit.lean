module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarBorelInnerError
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

/-! # Passing the coefficient limit on a fixed compact inner cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped Topology ENNReal

/-- The coefficient limit preserves the complete source estimate on a fixed inner cylinder. -/
theorem scalar_borel_smooth_inner_limit (lam Lam : ℝ) (hlam : 0 < lam) (_hLam : lam ≤ Lam)
    (p : ℝ) (hp : 1 ≤ p) (alpha C₀ : ℝ) (localised : Bool)
    (hsmooth : ∀ a : ℝ → ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry a) →
      (∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (P₀ : Point) (R : ℝ), 0 < R → ∀ u f : Point → ℝ,
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) → Measurable f →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R), autonomousScalarOperator a u P ≤ f P) →
      ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
        sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) + C₀ * R ^ alpha *
        (eLpNorm (borelSource localised u f) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R))).toReal)
    (a : ℝ → ℝ → ℝ) (ha : Measurable (Function.uncurry a))
    (hb : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam)
    (C : ℕ → ℝ → ℝ → ℝ)
    (hC : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (C j)) ∧
      ∀ x v, lam ≤ C j x v ∧ C j x v ≤ Lam)
    (hc : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      Tendsto (fun j => C j z.1 z.2) atTop (𝓝 (a z.1 z.2)))
    {D : Set (Point)} (u f : Point → ℝ) (hreg : IsKineticC112On u D)
    (P₁ : Point) (r : ℝ) (hr : 0 < r)
    (hK : IsCompact (closure (backwardCylinder P₁ r)))
    (hKD : closure (backwardCylinder P₁ r) ⊆ D) (hf : Measurable f)
    (hLp : MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₁ r)))
    (hsub : ∀ᵐ P ∂(volume.restrict (backwardCylinder P₁ r)),
      autonomousScalarOperator a u P ≤ f P) :
    ∀ P ∈ closure (backwardCylinder P₁ r), u P ≤
      sSup ((fun P => max (u P) 0) '' kineticBoundary P₁ r) + C₀ * r ^ alpha *
      (eLpNorm (borelSource localised u f) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₁ r))).toReal := by
  classical
  let Q := backwardCylinder P₁ r
  let K := closure Q
  let H : Point → ℝ := fun P => kineticVelocityHessian u P 0 0
  have hH : ContinuousOn H K :=
    (continuous_apply 0).comp_continuousOn
      ((continuous_apply 0).comp_continuousOn
        (hreg.continuousOn_kineticVelocityHessian.mono hKD))
  have hregQ := _root_.HypoellipticAleksandrov.Parabolic.IsKineticC112On.mono hreg (subset_closure.trans hKD)
  obtain ⟨_, hme, hte⟩ := scalar_borel_inner_error hlam a ha hb C hC hc K hK H hH (zero_lt_one.trans_le hp)
  refine borel_estimate_of_defect (isOpen_backwardCylinder P₁ r hr) subset_closure hp localised
    hregQ.continuousOn hf hLp (e := fun j => scalarBorelError (C j) a H) (fun _ _ => abs_nonneg _)
    hme hte ?_
  intro j g hgm hgp hg
  apply hsmooth (C j) (hC j).1 (hC j).2
    P₁ r hr u (f + g) (hreg.continuousOn.mono hKD) hregQ (hf.add hgm) hgp
  filter_upwards [hsub, hg] with P hP hEq
  have hd := scalar_borel_operator_sub (C j) a u P
  change autonomousScalarOperator (C j) u P ≤ f P + g P
  rw [hEq]
  rw [neg_mul] at hd
  dsimp only [scalarBorelError, H]
  have herror := hd.le.trans (neg_le_abs _)
  linarith only [herror, hP]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
