module

public import ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.DefectCorrection

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Changed-uniformizer intertwiner construction

This module builds compatible finite-degree approximations, assembles the changed-uniformizer intertwiner, proves its functional equation, and establishes uniqueness.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open SameUniformizer

 structure PadicChangedUniformizerApproximation
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) where
  series : PowerSeries (padicCompletedUnramifiedWittRing p)
  constantCoeff_eq_zero :
    PowerSeries.constantCoeff series = 0
  coeff_one_eq :
    PowerSeries.coeff 1 series =
      (padicChangedUniformizerLinearCoefficient p u :
        padicCompletedUnramifiedWittRing p)

 noncomputable def padicChangedUniformizerApproximation
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    ℕ → PadicChangedUniformizerApproximation p u
  | 0 =>
      { series :=
          PowerSeries.monomial 1
            (padicChangedUniformizerLinearCoefficient p u :
              padicCompletedUnramifiedWittRing p)
        constantCoeff_eq_zero := by
          rw [← PowerSeries.coeff_zero_eq_constantCoeff,
            PowerSeries.coeff_monomial]
          simp
        coeff_one_eq := by simp }
  | n + 1 =>
      let A := padicChangedUniformizerApproximation p u n
      let m := n + 2
      let c :=
        padicChangedUniformizerCorrectionCoefficient
          p u A.series A.constantCoeff_eq_zero m (by omega)
      { series := A.series + PowerSeries.monomial m c
        constantCoeff_eq_zero := by
          rw [map_add, A.constantCoeff_eq_zero,
            ← PowerSeries.coeff_zero_eq_constantCoeff,
            PowerSeries.coeff_monomial]
          simp [m]
        coeff_one_eq := by
          rw [map_add, A.coeff_one_eq,
            PowerSeries.coeff_monomial]
          simp [m] }

private theorem padicChangedUniformizerApproximation_succ
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (n : ℕ) :
    (padicChangedUniformizerApproximation p u (n + 1)).series =
      (padicChangedUniformizerApproximation p u n).series +
        PowerSeries.monomial (n + 2)
          (padicChangedUniformizerCorrectionCoefficient p u
            (padicChangedUniformizerApproximation p u n).series
            (padicChangedUniformizerApproximation p u n).constantCoeff_eq_zero
            (n + 2) (by omega)) :=
  rfl

section

variable (p : ℕ) [Fact p.Prime] (u : (padicLocalField p).valuationSubringˣ)

private theorem
    padicChangedUniformizerApproximation_coeff_succ_eq_of_lt
    (n q : ℕ) (hq : q < n + 2) :
    PowerSeries.coeff q
        (padicChangedUniformizerApproximation p u (n + 1)).series =
      PowerSeries.coeff q
        (padicChangedUniformizerApproximation p u n).series := by
  rw [padicChangedUniformizerApproximation_succ, map_add,
    PowerSeries.coeff_monomial, ite_eq_right (Nat.ne_of_lt hq)]
  exact add_zero _

private theorem padicChangedUniformizerApproximation_coeff_eq_of_le
    (q : ℕ) {a b : ℕ} (hab : a ≤ b)
    (hq : q < a + 2) :
    PowerSeries.coeff q
        (padicChangedUniformizerApproximation p u b).series =
      PowerSeries.coeff q
        (padicChangedUniformizerApproximation p u a).series := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      rw [padicChangedUniformizerApproximation_coeff_succ_eq_of_lt
        p u b q (by omega)]
      exact ih

private theorem
    padicChangedUniformizerApproximation_succ_defect_coeff
    (n : ℕ) :
    PowerSeries.coeff (n + 2)
        (padicChangedUniformizerDefect p u
          (padicChangedUniformizerApproximation p u (n + 1)).series) =
      0 := by
  exact
    padicChangedUniformizerCorrectionCoefficient_kills_defect
      p u
      (padicChangedUniformizerApproximation p u n).series
      (padicChangedUniformizerApproximation p u n).constantCoeff_eq_zero
      (n + 2) (by omega)

/-- The actual semilinear changed-uniformizer series over the completed
unramified Witt ring. -/
noncomputable def padicChangedUniformizerIntertwiner :
    PowerSeries (padicCompletedUnramifiedWittRing p) :=
  PowerSeries.mk fun m =>
    PowerSeries.coeff m
      (padicChangedUniformizerApproximation p u m).series

@[simp]
theorem padicChangedUniformizerIntertwiner_coeff
    (m : ℕ) :
    PowerSeries.coeff m
        (padicChangedUniformizerIntertwiner p u) =
      PowerSeries.coeff m
        (padicChangedUniformizerApproximation p u m).series := by
  simp [padicChangedUniformizerIntertwiner]

theorem padicChangedUniformizerIntertwiner_constantCoeff :
    PowerSeries.constantCoeff
        (padicChangedUniformizerIntertwiner p u) = 0 := by
  simp [← PowerSeries.coeff_zero_eq_constantCoeff]
  simpa using
    (padicChangedUniformizerApproximation p u 0).constantCoeff_eq_zero

@[simp]
theorem padicChangedUniformizerIntertwiner_coeff_one :
    PowerSeries.coeff 1
        (padicChangedUniformizerIntertwiner p u) =
      (padicChangedUniformizerLinearCoefficient p u :
        padicCompletedUnramifiedWittRing p) := by
  simp
  grind [padicChangedUniformizerApproximation]

theorem padicChangedUniformizerIntertwiner_hasSubst :
    PowerSeries.HasSubst
      (padicChangedUniformizerIntertwiner p u) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (padicChangedUniformizerIntertwiner_constantCoeff p u)

end

variable (p : ℕ) [Fact p.Prime] (u : (padicLocalField p).valuationSubringˣ)

private theorem padicChangedUniformizerDefect_coeff_zero :
    PowerSeries.coeff 0
        (padicChangedUniformizerDefect p u
          (padicChangedUniformizerIntertwiner p u)) = 0 := by
  let H := padicChangedUniformizerIntertwiner p u
  have hH := padicChangedUniformizerIntertwiner_constantCoeff p u
  simp [padicChangedUniformizerDefect]
  change
    MvPowerSeries.constantCoeff
        (PowerSeries.subst
          (padicCompletedMultiplicativeSeries p)
          (PowerSeries.map WittVector.frobenius H)) -
      MvPowerSeries.constantCoeff
        (PowerSeries.subst H
          (padicCompletedChangedStandardSeries p u)) = 0
  rw [PowerSeries.constantCoeff_subst_eq_zero (padicCompletedMultiplicativeSeries_constantCoeff p)
      (PowerSeries.map WittVector.frobenius H) (padicChangedUniformizerFrobenius_constantCoeff_eq_zero p H hH),
    PowerSeries.constantCoeff_subst_eq_zero hH
      (padicCompletedChangedStandardSeries p u) (padicCompletedChangedStandardSeries_constantCoeff p u),
    sub_zero]

private theorem padicChangedUniformizerDefect_coeff_one :
    PowerSeries.coeff 1
        (padicChangedUniformizerDefect p u
          (padicChangedUniformizerIntertwiner p u)) = 0 := by
  let ε :=
    (padicChangedUniformizerLinearCoefficient p u :
      padicCompletedUnramifiedWittRing p)
  let V :=
    padicValuationUnitToCompletedUnramifiedWittUnit p u
  let H := padicChangedUniformizerIntertwiner p u
  have hH := padicChangedUniformizerIntertwiner_constantCoeff p u
  have hlinear :=
    padicChangedUniformizerLinearCoefficient_frobenius p u
  have hcongr :
      PowerSeries.coeff 1
          (padicChangedUniformizerDefect p u H) =
        PowerSeries.coeff 1
          (padicChangedUniformizerDefect p u
            (PowerSeries.monomial 1 ε)) := by
    apply padicChangedUniformizerDefect_coeff_eq_of_coeff_eq_le
      p u hH
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff,
        PowerSeries.coeff_monomial]
      simp
    · intro q hq
      interval_cases q
      · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hH, PowerSeries.coeff_monomial]
      · simpa using (padicChangedUniformizerIntertwiner_coeff_one p u)
  let P :=
    PowerSeries.monomial 1 ε
  have hPconstant : PowerSeries.constantCoeff P = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_monomial]
    simp
  have hPsubst :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hPconstant
  have hΦP :
      PowerSeries.map WittVector.frobenius P =
        PowerSeries.monomial 1 (WittVector.frobenius ε) := by
    apply PowerSeries.ext
    intro q
    rw [PowerSeries.coeff_map]
    change
      WittVector.frobenius
          (PowerSeries.coeff q (PowerSeries.monomial 1 ε)) =
        PowerSeries.coeff q
          (PowerSeries.monomial 1 (WittVector.frobenius ε))
    rw [PowerSeries.coeff_monomial, PowerSeries.coeff_monomial]
    by_cases hq : q = 1
    · simp [hq]
    · simp [hq]
  have hright :
      PowerSeries.coeff 1
          (PowerSeries.subst (padicCompletedMultiplicativeSeries p)
            (PowerSeries.map WittVector.frobenius P)) =
        WittVector.frobenius ε * p := by
    rw [hΦP, padicChangedUniformizer_subst_monomial,
      PowerSeries.coeff_C_mul,
      padicCompletedMultiplicativeSeries_coeff_pow_self]
    simp
  have hleft :
      PowerSeries.coeff 1
          (PowerSeries.subst P
            (padicCompletedChangedStandardSeries p u)) =
        ((V : padicCompletedUnramifiedWittRing p) * (p : padicCompletedUnramifiedWittRing p)) * ε := by
    rw [padicCompletedChangedStandardSeries_eq,
      PowerSeries.subst_add hPsubst,
      PowerSeries.subst_mul hPsubst,
      PowerSeries.subst_C,
      PowerSeries.subst_X hPsubst,
      PowerSeries.subst_pow hPsubst,
      PowerSeries.subst_X hPsubst,
      map_add]
    change
      PowerSeries.coeff 1
          (PowerSeries.C
              ((V : padicCompletedUnramifiedWittRing p) *
                (p : padicCompletedUnramifiedWittRing p)) * P) +
        PowerSeries.coeff 1 (P ^ p) =
      (V : padicCompletedUnramifiedWittRing p) * (p : padicCompletedUnramifiedWittRing p) * ε
    rw [PowerSeries.coeff_C_mul]
    have hpOneMul : 1 ≠ p * 1 := by
      simpa using ((Fact.out : p.Prime).one_lt.ne)
    rw [show P = PowerSeries.monomial 1 ε from rfl,
      PowerSeries.coeff_monomial, ite_eq_left rfl,
      PowerSeries.monomial_pow, PowerSeries.coeff_monomial,
      ite_eq_right hpOneMul]
    ring
  rw [hcongr, padicChangedUniformizerDefect, map_sub,
    hright, hleft]
  change WittVector.frobenius ε = ε * V at hlinear
  rw [hlinear]
  ring

private theorem padicChangedUniformizerDefect_coeff_succ_succ
    (n : ℕ) :
    PowerSeries.coeff (n + 2)
        (padicChangedUniformizerDefect p u
          (padicChangedUniformizerIntertwiner p u)) = 0 := by
  let A := padicChangedUniformizerApproximation p u (n + 1)
  calc
    _ =
        PowerSeries.coeff (n + 2)
          (padicChangedUniformizerDefect p u A.series) := by
      apply padicChangedUniformizerDefect_coeff_eq_of_coeff_eq_le
        p u
        (padicChangedUniformizerIntertwiner_constantCoeff p u)
        A.constantCoeff_eq_zero
      intro q hq
      let a := (n + 1)
      simp
      by_cases hqa : q ≤ a
      · grind [padicChangedUniformizerApproximation_coeff_eq_of_le]
      · have haq : a + 1 = q := by omega
        subst q
        rw [padicChangedUniformizerApproximation_coeff_succ_eq_of_lt
          p u a (a + 1) (by omega)]
    _ = 0 :=
      padicChangedUniformizerApproximation_succ_defect_coeff p u n

/-- The completed changed standard series after the actual intertwiner is
the Frobenius transform of the intertwiner after the multiplicative
series. This is the first changed-uniformizer identity. -/
theorem padicChangedUniformizerIntertwiner_functionalEquation :
    PowerSeries.subst
        (padicChangedUniformizerIntertwiner p u)
        (PowerSeries.map
          (padicValuationSubringToCompletedUnramifiedWittRing p)
          (standardLubinTateSeries
            (standardLubinTateChangedUniformizer_isUniformizer
              (padicMultiplicativeLubinTateSeries_isUniformizer p) u)).toPowerSeries) =
      PowerSeries.subst
        (PowerSeries.map
          (padicValuationSubringToCompletedUnramifiedWittRing p)
          (padicMultiplicativeLubinTateSeries p).toPowerSeries)
        (PowerSeries.map WittVector.frobenius
          (padicChangedUniformizerIntertwiner p u)) := by
  change
    PowerSeries.subst
        (padicChangedUniformizerIntertwiner p u)
        (padicCompletedChangedStandardSeries p u) =
      PowerSeries.subst
        (padicCompletedMultiplicativeSeries p)
        (PowerSeries.map WittVector.frobenius
          (padicChangedUniformizerIntertwiner p u))
  rw [← sub_eq_zero]
  apply PowerSeries.ext
  intro m
  simp
  have hrewrite :
      PowerSeries.coeff m
            (PowerSeries.subst
              (padicChangedUniformizerIntertwiner p u)
              (padicCompletedChangedStandardSeries p u)) -
          PowerSeries.coeff m
            (PowerSeries.subst
              (padicCompletedMultiplicativeSeries p)
              (PowerSeries.map WittVector.frobenius
                (padicChangedUniformizerIntertwiner p u))) =
        -PowerSeries.coeff m
          (padicChangedUniformizerDefect p u
            (padicChangedUniformizerIntertwiner p u)) := by
    unfold padicChangedUniformizerDefect
    rw [map_sub]
    ring
  rw [hrewrite]
  cases m with
  | zero =>
      simp [padicChangedUniformizerDefect_coeff_zero]
  | succ m =>
      cases m with
      | zero =>
          simp [padicChangedUniformizerDefect_coeff_one]
      | succ n =>
          simp [padicChangedUniformizerDefect_coeff_succ_succ]

/-- A zero-constant-coefficient solution of the changed-uniformizer
functional equation is determined by its linear coefficient. -/
theorem padicChangedUniformizerIntertwiner_unique
    {H H' : PowerSeries (padicCompletedUnramifiedWittRing p)}
    (hHconstant : PowerSeries.constantCoeff H = 0)
    (hH'constant : PowerSeries.constantCoeff H' = 0)
    (hlinear :
      PowerSeries.coeff 1 H = PowerSeries.coeff 1 H')
    (hH :
      PowerSeries.subst H
          (padicCompletedChangedStandardSeries p u) =
        PowerSeries.subst
          (padicCompletedMultiplicativeSeries p)
          (PowerSeries.map WittVector.frobenius H))
    (hH' :
      PowerSeries.subst H'
          (padicCompletedChangedStandardSeries p u) =
        PowerSeries.subst
          (padicCompletedMultiplicativeSeries p)
          (PowerSeries.map WittVector.frobenius H')) :
    H = H' := by
  have hHdefect :
      padicChangedUniformizerDefect p u H = 0 := by
    rw [padicChangedUniformizerDefect, hH, sub_self]
  have hH'defect :
      padicChangedUniformizerDefect p u H' = 0 := by
    rw [padicChangedUniformizerDefect, hH', sub_self]
  apply PowerSeries.ext
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
      by_cases hm0 : m = 0
      · simp_all
      by_cases hm1 : m = 1
      · subst m
        exact hlinear
      have hm : 2 ≤ m := by omega
      let c : padicCompletedUnramifiedWittRing p :=
        PowerSeries.coeff m H - PowerSeries.coeff m H'
      let A : PowerSeries (padicCompletedUnramifiedWittRing p) :=
        H' + PowerSeries.monomial m c
      have hAconstant : PowerSeries.constantCoeff A = 0 := by
        change PowerSeries.constantCoeff H' +
            PowerSeries.constantCoeff (PowerSeries.monomial m c) = 0
        rw [hH'constant,
          ← PowerSeries.coeff_zero_eq_constantCoeff,
          PowerSeries.coeff_monomial, ite_eq_right (Ne.symm hm0),
          zero_add]
      have hcoeff :
          ∀ q : ℕ, q ≤ m →
            PowerSeries.coeff q H = PowerSeries.coeff q A := by
        intro q hqm
        by_cases hq : q = m
        · subst q
          change PowerSeries.coeff m H =
            PowerSeries.coeff m H' +
              PowerSeries.coeff m (PowerSeries.monomial m c)
          simp
          dsimp only [c]
          ring
        · have hqLt : q < m := lt_of_le_of_ne hqm hq
          change PowerSeries.coeff q H =
            PowerSeries.coeff q H' +
              PowerSeries.coeff q (PowerSeries.monomial m c)
          rw [PowerSeries.coeff_monomial, ite_eq_right hq]
          simp only [add_zero]
          exact ih q hqLt
      have hdefectA :
          PowerSeries.coeff m
              (padicChangedUniformizerDefect p u A) =
            0 := by
        calc
          PowerSeries.coeff m
              (padicChangedUniformizerDefect p u A) =
              PowerSeries.coeff m
                (padicChangedUniformizerDefect p u H) := by
            symm
            exact
              padicChangedUniformizerDefect_coeff_eq_of_coeff_eq_le
                p u hHconstant hAconstant m hcoeff
          _ = 0 := by simp [hHdefect]
      have hcHomogeneous :
          (p : padicCompletedUnramifiedWittRing p) ^ m *
                WittVector.frobenius c -
              ((padicValuationUnitToCompletedUnramifiedWittUnit p u) :
                  padicCompletedUnramifiedWittRing p) *
                (p : padicCompletedUnramifiedWittRing p) * c =
            0 := by
        have hformula :=
          padicChangedUniformizerDefect_coeff_add_monomial
            p u H' hH'constant m hm c
        change
          PowerSeries.coeff m
              (padicChangedUniformizerDefect p u A) =
            PowerSeries.coeff m
                (padicChangedUniformizerDefect p u H') +
              (p : padicCompletedUnramifiedWittRing p) ^ m *
                WittVector.frobenius c -
              ((padicValuationUnitToCompletedUnramifiedWittUnit p u) :
                  padicCompletedUnramifiedWittRing p) *
                (p : padicCompletedUnramifiedWittRing p) * c at hformula
        rw [hdefectA, hH'defect, map_zero,
          zero_add] at hformula
        exact hformula.symm
      let V : (padicCompletedUnramifiedWittRing p)ˣ :=
        padicValuationUnitToCompletedUnramifiedWittUnit p u
      have hpne : (p : padicCompletedUnramifiedWittRing p) ≠ 0 :=
        WittVector.p_nonzero p (AlgebraicClosure (ZMod p))
      have hpow :
          (p : padicCompletedUnramifiedWittRing p) ^ m =
            (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
              (p : padicCompletedUnramifiedWittRing p) := by
        calc
          (p : padicCompletedUnramifiedWittRing p) ^ m =
              (p : padicCompletedUnramifiedWittRing p) ^ ((m - 1) + 1) := by
            congr 1
            omega
          _ = (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
              (p : padicCompletedUnramifiedWittRing p) := by
            rw [pow_succ]
      have hpCancel :
          (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
                WittVector.frobenius c =
            (V : padicCompletedUnramifiedWittRing p) * c := by
        apply mul_left_cancel₀ hpne
        have heq := sub_eq_zero.mp hcHomogeneous
        change
          (p : padicCompletedUnramifiedWittRing p) *
              ((p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
                WittVector.frobenius c) =
            (p : padicCompletedUnramifiedWittRing p) *
              ((V : padicCompletedUnramifiedWittRing p) * c)
        calc
          (p : padicCompletedUnramifiedWittRing p) *
                ((p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
                  WittVector.frobenius c) =
              (p : padicCompletedUnramifiedWittRing p) ^ m *
                WittVector.frobenius c := by
            rw [hpow]
            ring
          _ =
              (V : padicCompletedUnramifiedWittRing p) *
                (p : padicCompletedUnramifiedWittRing p) * c :=
            heq
          _ =
              (p : padicCompletedUnramifiedWittRing p) *
                ((V : padicCompletedUnramifiedWittRing p) * c) := by
            ring
      have hcFixed :
          c =
            ((V⁻¹ : (padicCompletedUnramifiedWittRing p)ˣ) :
                padicCompletedUnramifiedWittRing p) *
              (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
              WittVector.frobenius c := by
        calc
          c =
              ((V⁻¹ : (padicCompletedUnramifiedWittRing p)ˣ) :
                  padicCompletedUnramifiedWittRing p) *
                ((V : padicCompletedUnramifiedWittRing p) * c) := by
            simp
          _ =
              ((V⁻¹ : (padicCompletedUnramifiedWittRing p)ˣ) :
                  padicCompletedUnramifiedWittRing p) *
                ((p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
                  WittVector.frobenius c) := by
            rw [← hpCancel]
          _ =
              ((V⁻¹ : (padicCompletedUnramifiedWittRing p)ˣ) :
                  padicCompletedUnramifiedWittRing p) *
                (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
                WittVector.frobenius c := by
            ring
      have hunique :=
        existsUnique_padicChangedUniformizerCoefficient p u m hm 0
      have hcSolution :
          c =
            0 +
              ((V⁻¹ : (padicCompletedUnramifiedWittRing p)ˣ) :
                  padicCompletedUnramifiedWittRing p) *
                (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
                WittVector.frobenius c := by
        simpa only [zero_add] using hcFixed
      have hzeroSolution :
          (0 : padicCompletedUnramifiedWittRing p) =
            0 +
              ((V⁻¹ : (padicCompletedUnramifiedWittRing p)ˣ) :
                  padicCompletedUnramifiedWittRing p) *
                (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
                WittVector.frobenius 0 := by
        simp
      have hcZero : c = 0 :=
        hunique.unique hcSolution hzeroSolution
      exact sub_eq_zero.mp (by assumption)

end LubinTate

end
