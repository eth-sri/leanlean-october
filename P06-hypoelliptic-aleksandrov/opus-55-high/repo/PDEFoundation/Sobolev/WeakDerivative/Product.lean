module

public import PDEFoundation.Sobolev.WeakDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Products of weakly differentiable functions with smooth multipliers

This file proves the raw distributional product rule for multiplication by a
smooth scalar function. The multiplier need not have compact support or be
globally bounded: the compact support of each test function localizes every
Bochner integral.

The value and weak-derivative representatives are assumed locally integrable.
These hypotheses are analytically substantive because additivity of the
Bochner integral is not available for arbitrary non-integrable functions.

## Main results

- `HasWeakPartialDerivOn.mul_contDiff`: coordinate product rule.
- `HasWeakGradientOn.mul_contDiff`: vector-valued weak-gradient product rule.
-/

@[expose] public section

namespace PDE

namespace HasWeakPartialDerivOn

/-- Multiplication by a smooth scalar function obeys the weak product rule.

Only local integrability of the value and weak-partial representatives is
needed. The smooth multiplier may be noncompactly supported and unbounded.
-/
theorem mul_contDiff {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u gi φ : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u gi)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (huLoc : MeasureTheory.LocallyIntegrable u (volumeOn U))
    (hgiLoc : MeasureTheory.LocallyIntegrable gi (volumeOn U)) :
    HasWeakPartialDerivOn U i
      (fun x => φ x * u x)
      (fun x =>
        φ x * gi x + u x * (fderiv ℝ φ x) (basisVec i)) := by
  intro ψ hψSmooth hψCompact hψSubset
  let μU : MeasureTheory.Measure (Vec d) := volumeOn U
  let ei  := basisVec i
  let dφ  := fun x => (fderiv ℝ φ x) ei
  let dψ  := fun x => (fderiv ℝ ψ x) ei
  let ψφ  := fun x => φ x * ψ x
  have hφCont : Continuous φ := hφ.continuous
  have hψCont : Continuous ψ := hψSmooth.continuous
  have hdφCont : Continuous dφ := by
    simpa using
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψφSmooth : ContDiff ℝ _ ψφ :=
    hφ.mul hψSmooth
  have hψφCompact : HasCompactSupport ψφ := by
    simpa using! hψCompact.mul_left (f := φ)
  have hdψφCont :
      Continuous (fun x => (fderiv ℝ ψφ x) ei) := by
    simpa using
      (hψφSmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψφCompact :
      HasCompactSupport (fun x => (fderiv ℝ ψφ x) ei) := by
    simpa using
      hψφCompact.fderiv_apply (𝕜 := ℝ) ei
  have hψφSubset : tsupport ψφ ⊆ U :=
    (tsupport_mul_subset_right (f := φ) (g := ψ)).trans hψSubset
  have huWeak :
      (∫ x, u x * (fderiv ℝ ψφ x) ei ∂μU) =
        -∫ x, gi x * ψφ x ∂μU := by
    aesop
  have hψdφCont : Continuous (fun x => ψ x * dφ x) :=
    hψCont.mul hdφCont
  have hψdφCompact :
      HasCompactSupport (fun x => ψ x * dφ x) := by
    simpa only using! hψCompact.mul_right (f' := dφ)
  have huψdφIntegrable :
      MeasureTheory.Integrable
        (fun x => u x * (ψ x * dφ x)) μU := by
    simpa using
      huLoc.integrable_smul_right_of_hasCompactSupport
        hψdφCont hψdφCompact
  have huDψφIntegrable :
      MeasureTheory.Integrable
        (fun x => u x * (fderiv ℝ ψφ x) ei) μU := by
    simpa using
      huLoc.integrable_smul_right_of_hasCompactSupport
        hdψφCont hdψφCompact
  have hgiφψIntegrable :
      MeasureTheory.Integrable
        (fun x => gi x * (φ x * ψ x)) μU := by
    simpa using!
      hgiLoc.integrable_smul_right_of_hasCompactSupport
        (hφCont.mul hψCont) hψφCompact
  have hudφψIntegrable :
      MeasureTheory.Integrable
        (fun x => (u x * dφ x) * ψ x) μU := by
    grind
  have hproductDeriv :
      ∀ x, (fderiv ℝ ψφ x) ei =
        φ x * dψ x + ψ x * dφ x := by
    intro x
    have hφDiff : DifferentiableAt ℝ φ x :=
      hφ.contDiffAt.differentiableAt (by simp)
    have hψDiff : DifferentiableAt ℝ ψ x :=
      hψSmooth.contDiffAt.differentiableAt (by simp)
    rw [show ψφ = φ * ψ by rfl, fderiv_mul hφDiff hψDiff]
    aesop
  have hleft :
      (∫ x, (φ x * u x) * dψ x ∂μU) =
        ∫ x, u x * (φ x * dψ x) ∂μU := by
    grind
  have hsplit :
      (∫ x, u x * (φ x * dψ x) ∂μU) =
        (∫ x, u x * (fderiv ℝ ψφ x) ei ∂μU) -
          ∫ x, u x * (ψ x * dφ x) ∂μU := by
    calc
      (∫ x, u x * (φ x * dψ x) ∂μU) =
          ∫ x, u x * (fderiv ℝ ψφ x) ei -
            u x * (ψ x * dφ x) ∂μU := by
              grind
      _ = (∫ x, u x * (fderiv ℝ ψφ x) ei ∂μU) -
            ∫ x, u x * (ψ x * dφ x) ∂μU := by
              rw [MeasureTheory.integral_sub
                huDψφIntegrable huψdφIntegrable]
  have hright :
      -(∫ x, gi x * ψφ x ∂μU) -
          ∫ x, u x * (ψ x * dφ x) ∂μU =
        -∫ x, (φ x * gi x + u x * dφ x) * ψ x ∂μU := by
    have hgiTerm :
        (∫ x, gi x * ψφ x ∂μU) =
          ∫ x, gi x * (φ x * ψ x) ∂μU := by
      linarith
    have huTerm :
        (∫ x, u x * (ψ x * dφ x) ∂μU) =
          ∫ x, (u x * dφ x) * ψ x ∂μU := by
      grind
    have hsum :
        (∫ x, (φ x * gi x + u x * dφ x) * ψ x ∂μU) =
          (∫ x, gi x * (φ x * ψ x) ∂μU) +
            ∫ x, (u x * dφ x) * ψ x ∂μU := by
      calc
        (∫ x, (φ x * gi x + u x * dφ x) * ψ x ∂μU) =
            ∫ x, gi x * (φ x * ψ x) +
              (u x * dφ x) * ψ x ∂μU := by
                grind
        _ = (∫ x, gi x * (φ x * ψ x) ∂μU) +
              ∫ x, (u x * dφ x) * ψ x ∂μU := by
                rw [MeasureTheory.integral_add
                  hgiφψIntegrable hudφψIntegrable]
    linarith
  linarith

end HasWeakPartialDerivOn

namespace HasWeakGradientOn

/-- Multiplication by a smooth scalar function obeys the weak-gradient
product rule `D(φu) = φ Du + u Dφ`.

The value representative and every chosen weak-gradient coordinate must be
locally integrable with respect to restricted volume.
-/
theorem mul_contDiff {d : ℕ} {U : Set (Vec d)}
    {u φ : Vec d → ℝ} {Du : Vec d → Vec d}
    (h : HasWeakGradientOn U u Du)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (huLoc : MeasureTheory.LocallyIntegrable u (volumeOn U))
    (hDuLoc : ∀ i : Fin d,
      MeasureTheory.LocallyIntegrable
        (fun x => Du x i) (volumeOn U)) :
    HasWeakGradientOn U
      (fun x => φ x * u x)
      (fun x i =>
        φ x * Du x i + u x * (fderiv ℝ φ x) (basisVec i)) := by
  intro i
  exact (h i).mul_contDiff hφ huLoc (hDuLoc i)

end HasWeakGradientOn

end PDE
