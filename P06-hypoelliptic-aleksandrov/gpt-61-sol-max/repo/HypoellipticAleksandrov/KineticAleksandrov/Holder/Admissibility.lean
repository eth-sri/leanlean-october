module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import Mathlib.Tactic

/-! # Restriction and elementary consequences of source admissibility -/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

variable {d : ℕ}

/-- Smooth-near functions are continuous on the indicated set. -/
theorem IsSmoothNear.continuousOn  {psi : HypoellipticAleksandrov.KineticScalarField d}
    {E : Set (KineticPoint d)} (h : IsSmoothNear psi E) : ContinuousOn psi E := by
  obtain ⟨U, _, hEU, hpsi⟩ := h
  have hc := hpsi.continuousOn.comp
    (KineticPoint.homeomorphProd d).continuous.continuousOn
    (fun P hP => mem_image_of_mem _ hP)
  exact (hc.mono hEU).congr (fun P _ =>
    congrArg psi ((KineticPoint.equivProd d).symm_apply_apply P))

variable {A : FullKineticCoefficient d}

/-- Restriction preserves source admissibility without changing the constants. -/
theorem IsAdmissibleSupersolution.mono
    {O U : Set (KineticPoint d)} {p C_A : ℝ} {u : HypoellipticAleksandrov.KineticScalarField d}
    (hu : IsAdmissibleSupersolution A O p C_A u) (hUO : U ⊆ O) :
    IsAdmissibleSupersolution A U p C_A u :=
  ⟨hu.1.mono hUO, fun P R hR hQU psi hpsi =>
    hu.2 P R hR (hQU.trans hUO) psi hpsi⟩

variable {O : Set (KineticPoint d)}

/-- Increasing the comparison constant preserves the source inequality. -/
theorem IsAdmissibleSupersolution.mono_constant
     {p C_A C_B : ℝ} {u : HypoellipticAleksandrov.KineticScalarField d}
    (hu : IsAdmissibleSupersolution A O p C_A u) (hAB : C_A ≤ C_B) :
    IsAdmissibleSupersolution A O p C_B u := by
  refine ⟨hu.1, fun P R hR hQ psi hpsi => (hu.2 P R hR hQ psi hpsi).trans ?_⟩
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg hR.le _)) ENNReal.toReal_nonneg

/-- The source norm may use a nonnegative majorant even for signed comparison data. -/
theorem IsAdmissibleSupersolution.nonnegative_constant
      {p C_A : ℝ}
    {u : HypoellipticAleksandrov.KineticScalarField d} (hu : IsAdmissibleSupersolution A O p C_A u) :
    IsAdmissibleSupersolution A O p (max C_A 0) u :=
  hu.mono_constant (le_max_left _ _)

end HypoellipticAleksandrov.KineticAleksandrov.Holder
