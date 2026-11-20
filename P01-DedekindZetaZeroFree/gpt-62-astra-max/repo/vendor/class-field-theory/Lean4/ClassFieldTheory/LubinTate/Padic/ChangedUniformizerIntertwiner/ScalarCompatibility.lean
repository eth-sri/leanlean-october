module

public import ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.ScalarEndomorphisms

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Changed-uniformizer scalar compatibility

This module proves that the changed-uniformizer intertwiner commutes with every scalar endomorphism and identifies its coefficientwise Frobenius twist.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open SameUniformizer

/-- The semilinear changed-uniformizer comparison intertwines every scalar
endomorphism.  This is the formal-series compatibility used in the
cyclotomic action formula for the Lubin--Tate character. -/
theorem padicChangedUniformizerIntertwiner_endomorphism
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.subst
        (padicCompletedMultiplicativeScalarEndomorphism p a)
        (padicChangedUniformizerIntertwiner p u) =
      PowerSeries.subst
        (padicChangedUniformizerIntertwiner p u)
        (padicCompletedChangedStandardScalarEndomorphism p u a) := by
  let H := padicChangedUniformizerIntertwiner p u
  let M := padicCompletedMultiplicativeScalarEndomorphism p a
  let S := padicCompletedChangedStandardScalarEndomorphism p u a
  let E := padicCompletedMultiplicativeSeries p
  let Ebar := padicCompletedChangedStandardSeries p u
  let Phi := PowerSeries.map WittVector.frobenius H
  let epsilon :=
    (padicChangedUniformizerLinearCoefficient p u :
      padicCompletedUnramifiedWittRing p)
  let alpha :=
    padicValuationSubringToCompletedUnramifiedWittRing p a
  let A := PowerSeries.subst M H
  let B := PowerSeries.subst H S
  have hHconstant : PowerSeries.constantCoeff H = 0 := by
    simpa using
      padicChangedUniformizerIntertwiner_constantCoeff p u
  have hHlinear :
      HasLinearTerm H (fun _ : Unit => epsilon) := by
    apply powerSeries_hasLinearTerm_of_constantCoeff_coeff_one
      H epsilon hHconstant
    simpa only [H, epsilon] using
      padicChangedUniformizerIntertwiner_coeff_one p u
  have hMlinear :
      HasLinearTerm M (fun _ : Unit => alpha) := by
    simpa using
      padicCompletedMultiplicativeScalarEndomorphism_hasLinearTerm p a
  have hSlinear :
      HasLinearTerm S (fun _ : Unit => alpha) := by
    simpa using
      padicCompletedChangedStandardScalarEndomorphism_hasLinearTerm p u a
  have hHsubst :=
    hHlinear.hasSubst
  have hMsubst :=
    hMlinear.hasSubst
  have hEsubst :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      simpa using
        padicCompletedMultiplicativeSeries_constantCoeff p)
  have hPhiSubst :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      simpa using
        padicChangedUniformizerFrobenius_constantCoeff_eq_zero
          p H hHconstant)
  have hHfunctional :
      PowerSeries.subst H Ebar =
        PowerSeries.subst E Phi := by
    simpa only [H, Ebar, E, Phi,
      padicCompletedChangedStandardSeries,
      padicCompletedMultiplicativeSeries] using
      padicChangedUniformizerIntertwiner_functionalEquation p u
  have hMcommutes :
      PowerSeries.subst M E =
        PowerSeries.subst E M := by
    simpa using
      padicCompletedMultiplicativeScalarEndomorphism_commutes p a
  have hScommutes :
      PowerSeries.subst S Ebar =
        PowerSeries.subst Ebar S := by
    simpa using
      padicCompletedChangedStandardScalarEndomorphism_commutes p u a
  have hmapA :
      PowerSeries.map WittVector.frobenius A =
        PowerSeries.subst M Phi := by
    simp only [A, Phi]
    change MvPowerSeries.map _ _ = _
    rw [PowerSeries.map_subst hMsubst]
    change
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) = _
    rw [padicCompletedMultiplicativeScalarEndomorphism_frobenius]
  have hmapB :
      PowerSeries.map WittVector.frobenius B =
        PowerSeries.subst Phi S := by
    simp only [B, Phi]
    change MvPowerSeries.map _ _ = _
    rw [PowerSeries.map_subst hHsubst]
    change
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) = _
    rw [padicCompletedChangedStandardScalarEndomorphism_frobenius]
  have hAlinearRaw :=
    hHlinear.subst

      (fun _ => hMlinear)
  have hAlinear :
      HasLinearTerm A
        (fun _ : Unit => epsilon * alpha) := by
    simpa [A, PowerSeries.subst_def] using hAlinearRaw
  have hBlinearRaw :=
    hSlinear.subst

      (fun _ => hHlinear)
  have hBlinear :
      HasLinearTerm B
        (fun _ : Unit => alpha * epsilon) := by
    simpa [B, PowerSeries.subst_def] using hBlinearRaw
  refine
    padicChangedUniformizerIntertwiner_unique p u
      hAlinear.constantCoeff_eq_zero
      hBlinear.constantCoeff_eq_zero
      ?_ ?_ ?_
  · calc
    PowerSeries.coeff 1 A =
        epsilon * alpha :=
      hAlinear.coeff_single ()
    _ = alpha * epsilon := mul_comm _ _
    _ = PowerSeries.coeff 1 B :=
      (hBlinear.coeff_single ()).symm
  · calc
    PowerSeries.subst A Ebar =
        PowerSeries.subst M
          (PowerSeries.subst H Ebar) := by
      simpa using
        (PowerSeries.subst_comp_subst_apply
          hHsubst hMsubst Ebar).symm
    _ = PowerSeries.subst M
          (PowerSeries.subst E Phi) := by
      rw [hHfunctional]
    _ = PowerSeries.subst
          (PowerSeries.subst M E) Phi :=
      PowerSeries.subst_comp_subst_apply
        hEsubst hMsubst Phi
    _ = PowerSeries.subst
          (PowerSeries.subst E M) Phi := by
      rw [hMcommutes]
    _ = PowerSeries.subst E
          (PowerSeries.subst M Phi) :=
      (PowerSeries.subst_comp_subst_apply
        hMsubst hEsubst Phi).symm
    _ = PowerSeries.subst E
          (PowerSeries.map WittVector.frobenius A) := by
      rw [hmapA]
  · calc
    PowerSeries.subst B Ebar =
        PowerSeries.subst H
          (PowerSeries.subst S Ebar) := by
      simpa using
        (PowerSeries.subst_comp_subst_apply
          hSlinear.hasSubst hHsubst Ebar).symm
    _ = PowerSeries.subst H
          (PowerSeries.subst Ebar S) := by
      rw [hScommutes]
    _ = PowerSeries.subst
          (PowerSeries.subst H Ebar) S :=
      PowerSeries.subst_comp_subst_apply
        (PowerSeries.HasSubst.of_constantCoeff_zero' (by
          simpa using
            padicCompletedChangedStandardSeries_constantCoeff p u)) hHsubst S
    _ = PowerSeries.subst
          (PowerSeries.subst E Phi) S := by
      rw [hHfunctional]
    _ = PowerSeries.subst E
          (PowerSeries.subst Phi S) :=
      (PowerSeries.subst_comp_subst_apply
        hPhiSubst hEsubst S).symm
    _ = PowerSeries.subst E
          (PowerSeries.map WittVector.frobenius B) := by
      rw [hmapB]

/-- Witt-vector Frobenius on the coefficients of the changed-uniformizer
intertwiner is substitution by the multiplicative endomorphism attached to
the unit changing the uniformizer. -/
theorem padicChangedUniformizerIntertwiner_frobenius
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries.map WittVector.frobenius
        (padicChangedUniformizerIntertwiner p u) =
      PowerSeries.subst
        (padicCompletedMultiplicativeScalarEndomorphism p
          (u : (padicLocalField p).valuationSubring))
        (padicChangedUniformizerIntertwiner p u) := by
  let H := padicChangedUniformizerIntertwiner p u
  let U :=
    padicCompletedMultiplicativeScalarEndomorphism p
      u
  let E := padicCompletedMultiplicativeSeries p
  let Ebar := padicCompletedChangedStandardSeries p u
  let Phi := PowerSeries.map WittVector.frobenius H
  let Phi2 := PowerSeries.map WittVector.frobenius Phi
  let epsilon :=
    (padicChangedUniformizerLinearCoefficient p u :
      padicCompletedUnramifiedWittRing p)
  let alpha :=
    (padicValuationUnitToCompletedUnramifiedWittUnit p u :
      padicCompletedUnramifiedWittRing p)
  let A := PowerSeries.subst U H
  have hHconstant : PowerSeries.constantCoeff H = 0 := by
    simpa using
      padicChangedUniformizerIntertwiner_constantCoeff p u
  have hHlinear :
      HasLinearTerm H (fun _ : Unit => epsilon) := by
    apply powerSeries_hasLinearTerm_of_constantCoeff_coeff_one
      H epsilon hHconstant
    simpa only [H, epsilon] using
      padicChangedUniformizerIntertwiner_coeff_one p u
  have hUlinear :
      HasLinearTerm U (fun _ : Unit => alpha) := by
    change HasLinearTerm U
      (fun _ : Unit =>
        padicValuationSubringToCompletedUnramifiedWittRing p
          u)
    simpa only [U] using (padicCompletedMultiplicativeScalarEndomorphism_hasLinearTerm p
      u)
  have hHsubst :=
    hHlinear.hasSubst
  have hUsubst :=
    hUlinear.hasSubst
  have hEsubst :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      simpa using
        padicCompletedMultiplicativeSeries_constantCoeff p)
  have hHfunctional :
      PowerSeries.subst H Ebar =
        PowerSeries.subst E Phi := by
    simpa only [H, Ebar, E, Phi,
      padicCompletedChangedStandardSeries,
      padicCompletedMultiplicativeSeries] using
      padicChangedUniformizerIntertwiner_functionalEquation p u
  have hUcommutes :
      PowerSeries.subst U E =
        PowerSeries.subst E U := by
    simpa using
      padicCompletedMultiplicativeScalarEndomorphism_commutes p
        u
  have hmapA :
      PowerSeries.map WittVector.frobenius A =
        PowerSeries.subst U Phi := by
    simp only [A, Phi]
    change MvPowerSeries.map _ _ = _
    rw [PowerSeries.map_subst hUsubst]
    change
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) = _
    rw [padicCompletedMultiplicativeScalarEndomorphism_frobenius]
  have hPhiFunctional :
      PowerSeries.subst Phi Ebar =
        PowerSeries.subst E Phi2 := by
    have h :=
      congrArg (PowerSeries.map WittVector.frobenius) hHfunctional
    change MvPowerSeries.map _ _ = MvPowerSeries.map _ _ at h
    rw [PowerSeries.map_subst hHsubst,
      PowerSeries.map_subst hEsubst] at h
    change
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) =
        PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) at h
    rw [
      padicCompletedChangedStandardSeries_frobenius,
      padicCompletedMultiplicativeSeries_frobenius] at h
    simpa using h
  have hAfunctional :
      PowerSeries.subst A Ebar =
        PowerSeries.subst E
          (PowerSeries.map WittVector.frobenius A) := by
    calc
      PowerSeries.subst A Ebar =
          PowerSeries.subst U
            (PowerSeries.subst H Ebar) := by
        simpa using
          (PowerSeries.subst_comp_subst_apply
            hHsubst hUsubst Ebar).symm
      _ = PowerSeries.subst U
            (PowerSeries.subst E Phi) := by
        rw [hHfunctional]
      _ = PowerSeries.subst
            (PowerSeries.subst U E) Phi :=
        PowerSeries.subst_comp_subst_apply
          hEsubst hUsubst Phi
      _ = PowerSeries.subst
            (PowerSeries.subst E U) Phi := by
        rw [hUcommutes]
      _ = PowerSeries.subst E
            (PowerSeries.subst U Phi) :=
        (PowerSeries.subst_comp_subst_apply
          hUsubst hEsubst Phi).symm
      _ = PowerSeries.subst E
            (PowerSeries.map WittVector.frobenius A) := by
        rw [hmapA]
  have hAlinearRaw :=
    hHlinear.subst

      (fun _ => hUlinear)
  have hAlinear :
      HasLinearTerm A
        (fun _ : Unit => epsilon * alpha) := by
    simpa [A, PowerSeries.subst_def] using hAlinearRaw
  have hPhiLinear :
      PowerSeries.coeff 1 Phi = epsilon * alpha := by
    change
      WittVector.frobenius
          (PowerSeries.coeff 1 H) =
        epsilon * alpha
    rw [show PowerSeries.coeff 1 H = epsilon by
      simpa only [H, epsilon] using
        padicChangedUniformizerIntertwiner_coeff_one p u]
    simpa using
      padicChangedUniformizerLinearCoefficient_frobenius p u
  refine
    padicChangedUniformizerIntertwiner_unique p u
      ?_
      hAlinear.constantCoeff_eq_zero
      (hPhiLinear.trans (hAlinear.coeff_single ()).symm)
      ?_ hAfunctional
  · simpa using
    padicChangedUniformizerFrobenius_constantCoeff_eq_zero
      p H hHconstant
  · simpa using hPhiFunctional

end LubinTate

end
