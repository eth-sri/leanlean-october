module

public import QPBT.Combining.Points
public import QPBT.Combining.Lines
public import QPBT.Combining.ExtendedLines
public import QPBT.Combining.ErrorBounds
public import QPBT.Combining.Witnesses
public import QPBT.Combining.DirectLowDegree
public import QPBT.Games.DistanceTheorems.RoundingTransport
public import QPBT.Games.Sandwich.Pasting.Heterogeneous
public import QPBT.Games.Sandwich.Pasting.Assembly
public import QPBT.Games.Sandwich.Pasting.SchmidtMirror
public import QPBT.Games.Sandwich.Support
public import QPBT.Observables.WinImplications.Averages
public import QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice
public import QPBT.ExplicitConstants
public import QPBT.Games.ErrorFunctions
public import QPBT.Test.PauliBasisTest
public import QPBT.Test.SoundnessDefs
public import MIPStarRE.LDT.Preliminaries.Polynomials
public import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkCore
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus ProjectiveSetting

noncomputable section

/-! ## Section 1: Polynomial image, fiber, and retained-point bounds -/

namespace PolynomialImageBounds

section
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

def orderedIndicator (X Z : Quantum.Measurement F ι) (α β a : F) : Op ι :=
  ∑ bc : F × F, if α * bc.1 + β * bc.2 = a then X.effect bc.1 * Z.effect bc.2 else 0

def diagonalIndicator (X Z : Quantum.Measurement F ι) (α β a : F) : Op ι :=
  ∑ bc : F × F,
    if α * bc.1 + β * bc.2 = a then Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2 else 0

theorem orderedIndicator_gram_of_ne_zero (X Z : Quantum.Measurement F ι)
    (hX : Measurement.IsProjective X) (α β a : F) (hβ : β ≠ 0) :
    (orderedIndicator X Z α β a)ᴴ * orderedIndicator X Z α β a = diagonalIndicator X Z α β a := by
  classical
  unfold orderedIndicator diagonalIndicator
  rw [Matrix.conjTranspose_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun bc _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single bc]
  · by_cases h : α * bc.1 + β * bc.2 = a
    · simp only [if_pos h, Matrix.conjTranspose_mul, measurement_effect_hermitian]
      rw [mul_assoc (Z.effect bc.2), ← mul_assoc (X.effect bc.1),
        (hX bc.1).isIdempotentElem.eq, ← mul_assoc]
    · simp [h]
  · intro bc' _ hne
    by_cases h : α * bc.1 + β * bc.2 = a
    · by_cases h' : α * bc'.1 + β * bc'.2 = a
      · have hb : bc.1 ≠ bc'.1 := fun hb => hne (Prod.ext hb (mul_left_cancel₀ hβ
          (add_left_cancel (a := α * bc.1) (by simpa only [hb] using h.trans h'.symm)))).symm
        simp only [if_pos h, if_pos h', Matrix.conjTranspose_mul, measurement_effect_hermitian]
        rw [show Z.effect bc.2 * X.effect bc.1 * (X.effect bc'.1 * Z.effect bc'.2) =
            Z.effect bc.2 * (X.effect bc.1 * X.effect bc'.1) * Z.effect bc'.2 by simp only [mul_assoc],
          projective_effect_mul_effect_eq_zero X hX hb]
        simp
      · simp [h']
    · simp [h]
  · simp

theorem diagonalIndicator_bounds (X Z : Quantum.Measurement F ι)
    (hZ : Measurement.IsProjective Z) (α β a : F) :
    0 ≤ diagonalIndicator X Z α β a ∧ diagonalIndicator X Z α β a ≤ 1 := by
  obtain ⟨hpos, hsum⟩ := pastedMeasurement_isMeasurement X Z hZ
  change (∀ bc : F × F, 0 ≤ Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2) at hpos
  change (∑ bc : F × F, Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2) = 1 at hsum
  refine ⟨Finset.sum_nonneg fun bc _ => by split_ifs; exact hpos bc; exact le_rfl, ?_⟩
  exact (Finset.sum_le_sum fun bc _ => by split_ifs; exact le_rfl; exact hpos bc).trans_eq hsum

theorem orderedIndicator_zero (X Z : Quantum.Measurement F ι) (α a : F) :
    orderedIndicator X Z α 0 a = (X.postprocess (fun b => α * b)).effect a := by
  unfold orderedIndicator
  rw [Fintype.sum_prod_type, Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : α * b = a
  · simp only [zero_mul, add_zero, h, if_true]; rw [← Finset.mul_sum, Z.sum_eq_one, mul_one]
  · simp [h]

theorem orderedIndicator_gram_le_one (X Z : Quantum.Measurement F ι)
    (hX : Measurement.IsProjective X) (hZ : Measurement.IsProjective Z) (α β a : F) :
    (orderedIndicator X Z α β a)ᴴ * orderedIndicator X Z α β a ≤ 1 := by
  by_cases hβ : β = 0
  · subst β
    rw [orderedIndicator_zero, measurement_effect_hermitian,
      (SandwichProduct.postprocess_isProjective X hX (fun b => α * b) a).isIdempotentElem.eq]
    exact measurement_effect_le_one _ _
  · rw [orderedIndicator_gram_of_ne_zero X Z hX α β a hβ]
    exact (diagonalIndicator_bounds X Z hZ α β a).2

theorem abs_orderedIndicator_norm_sq_sub_diagonal_le (X Z : Quantum.Measurement F ι)
    (hX : Measurement.IsProjective X) (hZ : Measurement.IsProjective Z)
    (α β a : F) (ψ : EuclideanSpace ℂ ι) :
    |‖applyOperatorToState (orderedIndicator X Z α β a) ψ‖ ^ 2 -
        stateQForm ψ (diagonalIndicator X Z α β a)| ≤
      if β = 0 then ‖ψ‖ ^ 2 else 0 := by
  by_cases hβ : β = 0
  · rw [if_pos hβ]
    have hA0 := sq_nonneg ‖applyOperatorToState (orderedIndicator X Z α β a) ψ‖
    have hA1 : ‖applyOperatorToState (orderedIndicator X Z α β a) ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
      rw [MagicSquareRigidity.norm_applyOperatorToState_sq, ← stateQForm_one ψ]
      exact quadratic_form_mono (orderedIndicator_gram_le_one X Z hX hZ α β a) ψ
    have hD := diagonalIndicator_bounds X Z hZ α β a
    have hD0 := stateQForm_nonneg ψ hD.1
    have hD1 : stateQForm ψ (diagonalIndicator X Z α β a) ≤ ‖ψ‖ ^ 2 := by
      rw [← stateQForm_one ψ]; exact quadratic_form_mono hD.2 ψ
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [if_neg hβ, MagicSquareRigidity.norm_applyOperatorToState_sq,
      orderedIndicator_gram_of_ne_zero X Z hX α β a hβ]
    simp [stateQForm]

theorem sum_projective_state_norm_sq {Γ : Type*} [Fintype Γ]
    (S : Quantum.Measurement Γ ι) (hS : Measurement.IsProjective S)
    (ψ : EuclideanSpace ℂ ι) :
    ∑ g : Γ, ‖applyOperatorToState (S.effect g) ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  simp_rw [MagicSquareRigidity.norm_applyOperatorToState_sq, measurement_effect_hermitian,
    fun g => (hS g).isIdempotentElem.eq]
  change (∑ g : Γ, stateQForm ψ (S.effect g)) = ‖ψ‖ ^ 2
  rw [← stateQForm_finset_sum, S.sum_eq_one, stateQForm_one]

theorem avgOver_finTwo_snd_zero (c : ℝ) :
    avgOver (uniformDistribution (Fin 2 → F)) (fun v => if v 1 = 0 then c else 0) =
      (Fintype.card F : ℝ)⁻¹ * c := by
  change avgOver (uniformDistribution (Fin 2 → F))
    (fun v => if ((finTwoArrowEquiv F) v).2 = 0 then c else 0) = _
  rw [avgOver_uniform_equiv (finTwoArrowEquiv F)]
  simp only [Equiv.apply_symm_apply]
  rw [avgOver_uniform_snd (fun β : F => if β = 0 then c else 0)]
  simp [avgOver_uniform_eq_inv_card_mul_sum]

theorem avg_eval_eq_le {n D : ℕ} (p r : MvPolynomial (Fin n) F)
    (hne : p ≠ r) (hp : p.totalDegree ≤ D) (hr : r.totalDegree ≤ D) :
    avgOver (uniformDistribution (Fin n → F))
      (fun u => if MvPolynomial.eval u p = MvPolynomial.eval u r then 1 else 0) ≤
      (D : ℝ) / Fintype.card F := by
  have hsz := Preliminaries.schwartzZippel_totalDegree hne hp hr
  calc
    _ = (Preliminaries.polynomialAgreementProbability n F p r : ℝ) := by
      simp [avgOver_uniform_eq_inv_card_mul_sum,
        Preliminaries.polynomialAgreementProbability, div_eq_mul_inv, mul_comm]
    _ ≤ (((D : ℚ≥0) / Fintype.card F : ℚ≥0) : ℝ) := by exact_mod_cast hsz
    _ = _ := by simp

theorem avg_diagonalIndicator_le_of_not_linear {n : ℕ}
    (p : MvPolynomial (Fin 2) (MvPolynomial (Fin n) F))
    (hp : ¬ ∃ r s : MvPolynomial (Fin n) F,
      p = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1)
    (X Z : (Fin n → F) → Quantum.Measurement F ι)
    (hZ : ∀ u, Measurement.IsProjective (Z u)) (ψ : EuclideanSpace ℂ ι) :
    avgOver (uniformDistribution (Fin n → F)) (fun u =>
      avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
        stateQForm ψ (diagonalIndicator (X u) (Z u) (v 0) (v 1)
          (MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) p))))) ≤
      ((p.support.sup fun e => (p.coeff e).totalDegree) + max 1 p.totalDegree : ℕ) /
        (Fintype.card F : ℝ) * ‖ψ‖ ^ 2 := by
  classical
  have hex : ∃ e : Fin 2 →₀ ℕ, e ≠ Finsupp.single 0 1 ∧ e ≠ Finsupp.single 1 1 ∧ p.coeff e ≠ 0 := by
    have h01 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := fun h => by
      simpa using congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
    by_contra! h
    apply hp
    refine ⟨p.coeff (Finsupp.single 0 1), p.coeff (Finsupp.single 1 1), ?_⟩
    ext e
    by_cases h0 : e = Finsupp.single 0 1
    · subst e; simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, Ne.symm h01]
    · by_cases h1 : e = Finsupp.single 1 1
      · subst e; simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, h01]
      · simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, Ne.symm h0, Ne.symm h1, h e h0 h1]
  obtain ⟨e, he0, he1, he⟩ := hex
  let D : ℕ := p.support.sup fun e => (p.coeff e).totalDegree
  let E : ℝ := (max 1 p.totalDegree : ℕ) / (Fintype.card F : ℝ)
  let w (u : Fin n → F) (bc : F × F) : ℝ :=
    stateQForm ψ ((Z u).effect bc.2 * (X u).effect bc.1 * (Z u).effect bc.2)
  let f (u : Fin n → F) (v : Fin 2 → F) : F :=
    MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) p)
  have hw (u : Fin n → F) (bc : F × F) : 0 ≤ w u bc :=
    stateQForm_nonneg ψ ((pastedMeasurement_isMeasurement (X u) (Z u) (hZ u)).1 bc)
  have hsum (u : Fin n → F) : ∑ bc : F × F, w u bc = ‖ψ‖ ^ 2 := by
    rw [← stateQForm_one ψ, ← (pastedMeasurement_isMeasurement (X u) (Z u) (hZ u)).2,
      stateQForm_finset_sum]
    rfl
  have hexpand (u : Fin n → F) (v : Fin 2 → F) :
      stateQForm ψ (diagonalIndicator (X u) (Z u) (v 0) (v 1) (f u v)) =
        ∑ bc : F × F, (if f u v = v 0 * bc.1 + v 1 * bc.2 then 1 else 0) * w u bc := by
    rw [diagonalIndicator, stateQForm_finset_sum]
    refine Finset.sum_congr rfl fun bc _ => ?_
    by_cases h : f u v = v 0 * bc.1 + v 1 * bc.2
    · simp [h, w]
    · simp [Ne.symm h, h, stateQForm, applyOperatorToState]
  have hgood (u : Fin n → F) (hu : MvPolynomial.eval u (p.coeff e) ≠ 0) :
      avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
        stateQForm ψ (diagonalIndicator (X u) (Z u) (v 0) (v 1) (f u v))) ≤ E * ‖ψ‖ ^ 2 := by
    simp_rw [hexpand, avgOver_sum, avgOver_mul_const]
    rw [← hsum u, Finset.mul_sum]
    refine Finset.sum_le_sum fun bc _ => mul_le_mul_of_nonneg_right ?_ (hw u bc)
    have hne : MvPolynomial.map (MvPolynomial.eval u) p ≠
        MvPolynomial.C bc.1 * MvPolynomial.X 0 + MvPolynomial.C bc.2 * MvPolynomial.X 1 := fun h =>
      hu (by simpa [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X,
        Ne.symm he0, Ne.symm he1] using congrArg (fun q => q.coeff e) h)
    have hdeg : (MvPolynomial.map (MvPolynomial.eval u) p).totalDegree ≤ p.totalDegree :=
      Finset.sup_mono (MvPolynomial.support_map_subset _ _)
    have hlin : (MvPolynomial.C bc.1 * MvPolynomial.X (0 : Fin 2) +
        MvPolynomial.C bc.2 * MvPolynomial.X (1 : Fin 2)).totalDegree ≤ 1 :=
      (MvPolynomial.totalDegree_add _ _).trans (max_le
        ((MvPolynomial.totalDegree_mul _ _).trans (by simp))
        ((MvPolynomial.totalDegree_mul _ _).trans (by simp)))
    simpa [f, E, mul_comm] using avg_eval_eq_le _ _ hne
      (hdeg.trans (le_max_right 1 _)) (hlin.trans (le_max_left 1 _))
  have hpoint (u : Fin n → F) :
      avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
        stateQForm ψ (diagonalIndicator (X u) (Z u) (v 0) (v 1) (f u v))) ≤
        (if MvPolynomial.eval u (p.coeff e) = 0 then 1 else 0) * ‖ψ‖ ^ 2 + E * ‖ψ‖ ^ 2 := by
    by_cases hu : MvPolynomial.eval u (p.coeff e) = 0
    · simp only [hu, if_true, one_mul]
      refine (avgOver_uniform_le_const _ (‖ψ‖ ^ 2) fun v => ?_).trans
        (le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _)))
      rw [← stateQForm_one ψ]
      exact quadratic_form_mono (diagonalIndicator_bounds (X u) (Z u) (hZ u) _ _ _).2 ψ
    · simpa only [hu, if_false, zero_mul, zero_add] using hgood u hu
  have hbad : avgOver (uniformDistribution (Fin n → F))
      (fun u => if MvPolynomial.eval u (p.coeff e) = 0 then 1 else 0) ≤ (D : ℝ) / Fintype.card F := by
    simpa using avg_eval_eq_le (p.coeff e) 0 he
      (Finset.le_sup (f := fun j => (p.coeff j).totalDegree) (MvPolynomial.mem_support_iff.mpr he))
      (by simp)
  calc
    _ ≤ avgOver (uniformDistribution (Fin n → F)) (fun u =>
        (if MvPolynomial.eval u (p.coeff e) = 0 then 1 else 0) * ‖ψ‖ ^ 2 + E * ‖ψ‖ ^ 2) :=
      avgOver_mono _ _ _ hpoint
    _ ≤ (D : ℝ) / Fintype.card F * ‖ψ‖ ^ 2 + E * ‖ψ‖ ^ 2 := by
      rw [avgOver_add, avgOver_mul_const, avgOver_uniform_const]
      exact add_le_add (mul_le_mul_of_nonneg_right hbad (sq_nonneg _)) le_rfl
    _ = _ := by dsimp [D, E]; push_cast; ring

omit [DecidableEq ι] in
theorem sum_mass_le_residual_add_image {Γ : Type*} (s : Finset Γ)
    (ψ A : Γ → EuclideanSpace ℂ ι) :
    ∑ g ∈ s, ‖ψ g‖ ^ 2 ≤ 2 * ∑ g ∈ s, ‖ψ g - A g‖ ^ 2 + 2 * ∑ g ∈ s, ‖A g‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun g _ => ?_
  have htr := norm_add_le (ψ g - A g) (A g)
  rw [sub_add_cancel] at htr
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htr 2
  nlinarith [sq_nonneg (‖ψ g - A g‖ - ‖A g‖)]

theorem nonlinear_mass_le_ordered_error {n : ℕ} {Γ : Type*}
    (s : Finset Γ) (p : Γ → MvPolynomial (Fin 2) (MvPolynomial (Fin n) F))
    (hp : ∀ g ∈ s, ¬ ∃ r t : MvPolynomial (Fin n) F,
      p g = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1)
    (X Z : (Fin n → F) → Quantum.Measurement F ι)
    (hX : ∀ u, Measurement.IsProjective (X u))
    (hZ : ∀ u, Measurement.IsProjective (Z u)) (ψ : Γ → EuclideanSpace ℂ ι) :
    ∑ g ∈ s, ‖ψ g‖ ^ 2 ≤
      2 * avgOver (uniformDistribution (Fin n → F)) (fun u =>
        avgOver (uniformDistribution (Fin 2 → F)) (fun v => ∑ g ∈ s,
          ‖ψ g - applyOperatorToState (orderedIndicator (X u) (Z u) (v 0) (v 1)
            (MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) (p g)))) (ψ g)‖ ^ 2)) +
      2 * ∑ g ∈ s,
        (((p g).support.sup fun e => ((p g).coeff e).totalDegree) +
          max 1 (p g).totalDegree + 1 : ℕ) / (Fintype.card F : ℝ) * ‖ψ g‖ ^ 2 := by
  let A (u : Fin n → F) (v : Fin 2 → F) (g : Γ) : EuclideanSpace ℂ ι :=
    applyOperatorToState (orderedIndicator (X u) (Z u) (v 0) (v 1)
      (MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) (p g)))) (ψ g)
  have havg := avgOver_mono (uniformDistribution (Fin n → F)) _ _ fun u =>
    avgOver_mono (uniformDistribution (Fin 2 → F)) _ _ fun v =>
      sum_mass_le_residual_add_image s ψ (A u v)
  simp only [avgOver_uniform_const, avgOver_add, avgOver_const_mul] at havg
  have hnorm : avgOver (uniformDistribution (Fin n → F)) (fun u =>
      avgOver (uniformDistribution (Fin 2 → F)) (fun v => ∑ g ∈ s, ‖A u v g‖ ^ 2)) ≤
      ∑ g ∈ s, (((p g).support.sup fun e => ((p g).coeff e).totalDegree) +
        max 1 (p g).totalDegree + 1 : ℕ) / (Fintype.card F : ℝ) * ‖ψ g‖ ^ 2 := by
    simp_rw [avgOver_finset_sum]
    refine Finset.sum_le_sum fun g hg => ?_
    let fg (u : Fin n → F) (v : Fin 2 → F) := MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) (p g))
    calc
      _ ≤ avgOver (uniformDistribution (Fin n → F)) (fun u =>
          avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
            stateQForm (ψ g) (diagonalIndicator (X u) (Z u) (v 0) (v 1) (fg u v)) +
              (if v 1 = 0 then ‖ψ g‖ ^ 2 else 0))) :=
        avgOver_mono _ _ _ fun u => avgOver_mono _ _ _ fun v => by
          have := (le_abs_self _).trans
            (abs_orderedIndicator_norm_sq_sub_diagonal_le (X u) (Z u) (hX u) (hZ u) (v 0) (v 1) (fg u v) (ψ g))
          dsimp [A, fg] at this ⊢; linarith
      _ = avgOver (uniformDistribution (Fin n → F)) (fun u =>
          avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
            stateQForm (ψ g) (diagonalIndicator (X u) (Z u) (v 0) (v 1) (fg u v)))) +
            (Fintype.card F : ℝ)⁻¹ * ‖ψ g‖ ^ 2 := by
        simp_rw [avgOver_add, avgOver_finTwo_snd_zero, avgOver_uniform_const]
      _ ≤ (((p g).support.sup fun e => ((p g).coeff e).totalDegree) + max 1 (p g).totalDegree : ℕ) /
          (Fintype.card F : ℝ) * ‖ψ g‖ ^ 2 + (Fintype.card F : ℝ)⁻¹ * ‖ψ g‖ ^ 2 :=
        add_le_add (avg_diagonalIndicator_le_of_not_linear (p g) (hp g hg) X Z hZ (ψ g)) le_rfl
      _ = _ := by push_cast; ring
  change ∑ g ∈ s, ‖ψ g‖ ^ 2 ≤ 2 * avgOver (uniformDistribution (Fin n → F))
    (fun u => avgOver (uniformDistribution (Fin 2 → F)) (fun v => ∑ g ∈ s, ‖ψ g - A u v g‖ ^ 2)) + _
  linarith

theorem avg_weighted_fiber_le {n k C D : ℕ}
    (p : MvPolynomial (Fin n) (MvPolynomial (Fin k) F))
    (hp : ¬ ∃ r, p = MvPolynomial.C r)
    (hcoeff : ∀ e, (p.coeff e).totalDegree ≤ C) (hdegree : p.totalDegree ≤ D)
    (w : (Fin k → F) → F → ℝ) (M : ℝ)
    (hw : ∀ z b, 0 ≤ w z b) (hsum : ∀ z, ∑ b, w z b = M) :
    avgOver (uniformDistribution (Fin k → F)) (fun z => ∑ b : F,
      avgOver (uniformDistribution (Fin n → F))
        (fun x => if MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p) = b
          then 1 else 0) * w z b) ≤ ((C + D : ℕ) : ℝ) / Fintype.card F * M := by
  classical
  have hex : ∃ e : Fin n →₀ ℕ, e ≠ 0 ∧ p.coeff e ≠ 0 := by
    by_contra! h
    refine hp ⟨p.coeff 0, ?_⟩
    ext e
    by_cases he : e = 0
    · simp [he]
    · simp [MvPolynomial.coeff_C, Ne.symm he, h e he]
  obtain ⟨e, he, hc⟩ := hex
  have hbad : avgOver (uniformDistribution (Fin k → F))
      (fun z => if MvPolynomial.eval z (p.coeff e) = 0 then 1 else 0) ≤ (C : ℝ) / Fintype.card F := by
    simpa using avg_eval_eq_le (p.coeff e) 0 hc (hcoeff e) (by simp)
  have hM : 0 ≤ M := by rw [← hsum (fun _ => 0)]; exact Finset.sum_nonneg fun b _ => hw _ b
  have hpoint (z : Fin k → F) :
      (∑ b : F, avgOver (uniformDistribution (Fin n → F))
        (fun x => if MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p) = b
          then 1 else 0) * w z b) ≤
      (if MvPolynomial.eval z (p.coeff e) = 0 then 1 else 0) * M + (D : ℝ) / Fintype.card F * M := by
    by_cases hz : MvPolynomial.eval z (p.coeff e) = 0
    · simp only [hz, if_true, one_mul]
      refine (le_trans (b := M) ?_ (le_add_of_nonneg_right (mul_nonneg (by positivity) hM)))
      rw [← hsum z]
      refine Finset.sum_le_sum fun b _ => ?_
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (avgOver_uniform_le_const _ 1 fun x => by split_ifs <;> norm_num) (hw z b)
    · simp only [hz, if_false, zero_mul, zero_add]
      rw [← hsum z, Finset.mul_sum]
      refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right ?_ (hw z b)
      have hne : MvPolynomial.map (MvPolynomial.eval z) p ≠ MvPolynomial.C b := fun h =>
        hz (by simpa [MvPolynomial.coeff_map, MvPolynomial.coeff_C, Ne.symm he] using
          congrArg (fun q => q.coeff e) h)
      simpa using avg_eval_eq_le _ (MvPolynomial.C b) hne
        ((Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans hdegree) (by simp)
  calc
    _ ≤ avgOver (uniformDistribution (Fin k → F)) (fun z =>
        (if MvPolynomial.eval z (p.coeff e) = 0 then 1 else 0) * M + (D : ℝ) / Fintype.card F * M) :=
      avgOver_mono _ _ _ hpoint
    _ ≤ (C : ℝ) / Fintype.card F * M + (D : ℝ) / Fintype.card F * M := by
      rw [avgOver_add, avgOver_mul_const, avgOver_uniform_const]
      exact add_le_add (mul_le_mul_of_nonneg_right hbad hM) le_rfl
    _ = _ := by push_cast; ring

theorem avg_orderedIndicator_norm_sq_le_of_nonconstant {n k C D : ℕ}
    (p : MvPolynomial (Fin n) (MvPolynomial (Fin k) F))
    (hp : ¬ ∃ r, p = MvPolynomial.C r)
    (hcoeff : ∀ e, (p.coeff e).totalDegree ≤ C) (hdegree : p.totalDegree ≤ D)
    (r : (Fin n → F) → (Fin k → F) → F)
    (X : (Fin n → F) → Quantum.Measurement F ι)
    (Z : (Fin k → F) → Quantum.Measurement F ι)
    (hX : ∀ x, Measurement.IsProjective (X x))
    (hZ : ∀ z, Measurement.IsProjective (Z z)) (ψ : EuclideanSpace ℂ ι) :
    avgOver (uniformDistribution (Fin k → F)) (fun z =>
      avgOver (uniformDistribution (Fin n → F)) (fun x =>
        avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
          ‖applyOperatorToState (orderedIndicator (X x) (Z z) (v 0) (v 1)
            (v 0 * r x z + v 1 * MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p))) ψ‖ ^ 2))) ≤
      ((C + D + 2 : ℕ) : ℝ) / Fintype.card F * ‖ψ‖ ^ 2 := by
  classical
  let w (z : Fin k → F) (b : F) := stateQForm ψ ((Z z).effect b)
  have hsum (z : Fin k → F) : ∑ b, w z b = ‖ψ‖ ^ 2 := by
    rw [← stateQForm_finset_sum, (Z z).sum_eq_one, stateQForm_one]
  have hfiber := avg_weighted_fiber_le p hp hcoeff hdegree w (‖ψ‖ ^ 2)
    (fun z b => stateQForm_nonneg ψ ((Z z).pos b)) hsum
  have hlin (x : Fin n → F) (z : Fin k → F) :
      avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
        ‖applyOperatorToState (orderedIndicator (X x) (Z z) (v 0) (v 1)
          (v 0 * r x z + v 1 * MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p))) ψ‖ ^ 2) ≤
      2 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 +
        stateQForm ψ ((Z z).effect (MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p))) := by
    let rt := (r x z, MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p))
    let wz (bc : F × F) : ℝ := stateQForm ψ ((Z z).effect bc.2 * (X x).effect bc.1 * (Z z).effect bc.2)
    have hwz (bc : F × F) : 0 ≤ wz bc :=
      stateQForm_nonneg ψ ((pastedMeasurement_isMeasurement (X x) (Z z) (hZ z)).1 bc)
    have hsumz : ∑ bc, wz bc = ‖ψ‖ ^ 2 := by
      rw [← stateQForm_one ψ, ← (pastedMeasurement_isMeasurement (X x) (Z z) (hZ z)).2,
        stateQForm_finset_sum]
      rfl
    have hexp (v : Fin 2 → F) :
        stateQForm ψ (diagonalIndicator (X x) (Z z) (v 0) (v 1) (v 0 * rt.1 + v 1 * rt.2)) =
        ∑ bc : F × F, (if v 0 * bc.1 + v 1 * bc.2 = v 0 * rt.1 + v 1 * rt.2 then 1 else 0) * wz bc := by
      rw [diagonalIndicator, stateQForm_finset_sum]
      refine Finset.sum_congr rfl fun bc _ => by split_ifs <;> simp [wz, stateQForm, applyOperatorToState]
    have hcoll (bc : F × F) :
        avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
          if v 0 * bc.1 + v 1 * bc.2 = v 0 * rt.1 + v 1 * rt.2 then (1 : ℝ) else 0) =
          if bc = rt then 1 else (Fintype.card F : ℝ)⁻¹ := by
      rw [avgOver_uniform_equiv (finTwoArrowEquiv F)]
      exact affine_collision_average bc rt
    have hdiag : avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
        stateQForm ψ (diagonalIndicator (X x) (Z z) (v 0) (v 1) (v 0 * rt.1 + v 1 * rt.2))) ≤
        (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 + stateQForm ψ ((Z z).effect rt.2 * (X x).effect rt.1 * (Z z).effect rt.2) := by
      simp_rw [hexp, avgOver_sum, avgOver_mul_const, hcoll]
      refine (Finset.sum_le_sum fun bc _ => mul_le_mul_of_nonneg_right
        (show (if bc = rt then (1 : ℝ) else (Fintype.card F : ℝ)⁻¹) ≤
          (Fintype.card F : ℝ)⁻¹ + if bc = rt then 1 else 0 by split_ifs <;> simp) (hwz bc)).trans_eq ?_
      simp_rw [add_mul, Finset.sum_add_distrib]
      rw [← Finset.mul_sum, hsumz]; simp [wz]
    have hdrop : stateQForm ψ ((Z z).effect rt.2 * (X x).effect rt.1 * (Z z).effect rt.2) ≤
        stateQForm ψ ((Z z).effect rt.2) :=
      quadratic_form_mono (by
        simpa only [Matrix.star_eq_conjTranspose, measurement_effect_hermitian, mul_one,
          (hZ z rt.2).isIdempotentElem.eq] using
          star_left_conjugate_le_conjugate (measurement_effect_le_one (X x) rt.1) ((Z z).effect rt.2)) ψ
    have havg := avgOver_mono (uniformDistribution (Fin 2 → F)) _ _ (fun v =>
      (le_abs_self _).trans (abs_orderedIndicator_norm_sq_sub_diagonal_le
        (X x) (Z z) (hX x) (hZ z) (v 0) (v 1) (v 0 * rt.1 + v 1 * rt.2) ψ))
    rw [avgOver_sub, avgOver_finTwo_snd_zero] at havg
    dsimp [rt] at havg hdiag hdrop
    linarith
  have heval (z : Fin k → F) (x : Fin n → F) :
      stateQForm ψ ((Z z).effect (MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p))) =
      ∑ b : F, (if MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p) = b then 1 else 0) * w z b := by
    simp [w]
  calc
    _ ≤ avgOver (uniformDistribution (Fin k → F)) (fun z =>
        avgOver (uniformDistribution (Fin n → F)) (fun x =>
          2 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 +
          stateQForm ψ ((Z z).effect (MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p))))) :=
      avgOver_mono _ _ _ fun z => avgOver_mono _ _ _ fun x => hlin x z
    _ = 2 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 +
        avgOver (uniformDistribution (Fin k → F)) (fun z => ∑ b : F,
          avgOver (uniformDistribution (Fin n → F))
            (fun x => if MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p) = b
              then 1 else 0) * w z b) := by
      simp_rw [heval, avgOver_add, avgOver_uniform_const, avgOver_sum, avgOver_mul_const]
    _ ≤ 2 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 + ((C + D : ℕ) : ℝ) / Fintype.card F * ‖ψ‖ ^ 2 :=
      add_le_add le_rfl hfiber
    _ = _ := by push_cast; ring

theorem point_mismatch_le_ordered_error (X Z : Quantum.Measurement F ι)
    (hX : Measurement.IsProjective X) (hZ : Measurement.IsProjective Z)
    (r t : F) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (1 - X.effect r) ψ‖ ^ 2 ≤
      2 * avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
        ‖ψ - applyOperatorToState
          (orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) ψ‖ ^ 2) +
      4 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
  classical
  have hwrong : avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
      ‖applyOperatorToState ((1 - X.effect r) *
        orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) ψ‖ ^ 2) ≤
      2 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
    let w (bc : F × F) := stateQForm ψ (Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2)
    have hw (bc : F × F) : 0 ≤ w bc :=
      stateQForm_nonneg ψ ((pastedMeasurement_isMeasurement X Z hZ).1 bc)
    have hsum : ∑ bc, w bc = ‖ψ‖ ^ 2 := by
      rw [← stateQForm_one ψ, ← (pastedMeasurement_isMeasurement X Z hZ).2, stateQForm_finset_sum]; rfl
    have hweff (b : F) : (1 - X.effect r) * X.effect b = if b = r then 0 else X.effect b := by
      by_cases hb : b = r
      · simp [hb, sub_mul, (hX r).isIdempotentElem.eq]
      · rw [sub_mul, one_mul, projective_effect_mul_effect_eq_zero X hX (Ne.symm hb)]; simp [hb]
    have hgram (α β a : F) (hβ : β ≠ 0) :
        let T := (1 - X.effect r) * orderedIndicator X Z α β a
        Tᴴ * T = ∑ bc : F × F,
          if α * bc.1 + β * bc.2 = a ∧ bc.1 ≠ r then Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2 else 0 := by
      have hexpand : (1 - X.effect r) * orderedIndicator X Z α β a =
          ∑ bc : F × F, if α * bc.1 + β * bc.2 = a ∧ bc.1 ≠ r then X.effect bc.1 * Z.effect bc.2 else 0 := by
        rw [orderedIndicator, Finset.mul_sum]
        refine Finset.sum_congr rfl fun bc _ => ?_
        by_cases h : α * bc.1 + β * bc.2 = a
        · simp only [h, if_true, true_and, ← mul_assoc, hweff]; split_ifs <;> simp_all
        · simp [h]
      dsimp only
      rw [hexpand, Matrix.conjTranspose_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun bc _ => ?_
      rw [Finset.mul_sum, Finset.sum_eq_single bc]
      · by_cases h : α * bc.1 + β * bc.2 = a ∧ bc.1 ≠ r
        · simp only [if_pos h, Matrix.conjTranspose_mul, measurement_effect_hermitian]
          rw [mul_assoc (Z.effect bc.2), ← mul_assoc (X.effect bc.1), (hX bc.1).isIdempotentElem.eq, ← mul_assoc]
        · simp [h]
      · intro bc' _ hne
        by_cases h : α * bc.1 + β * bc.2 = a ∧ bc.1 ≠ r
        · by_cases h' : α * bc'.1 + β * bc'.2 = a ∧ bc'.1 ≠ r
          · have hb : bc.1 ≠ bc'.1 := fun hb => hne (Prod.ext hb (mul_left_cancel₀ hβ
              (add_left_cancel (a := α * bc.1) (by simpa only [hb] using h.1.trans h'.1.symm)))).symm
            simp only [if_pos h, if_pos h', Matrix.conjTranspose_mul, measurement_effect_hermitian]
            rw [show Z.effect bc.2 * X.effect bc.1 * (X.effect bc'.1 * Z.effect bc'.2) =
                Z.effect bc.2 * (X.effect bc.1 * X.effect bc'.1) * Z.effect bc'.2 by simp only [mul_assoc],
              projective_effect_mul_effect_eq_zero X hX hb]
            simp
          · simp [h']
        · simp [h]
      · simp
    have hpt (v : Fin 2 → F) :
        ‖applyOperatorToState ((1 - X.effect r) *
          orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) ψ‖ ^ 2 ≤
        (if v 1 = 0 then ‖ψ‖ ^ 2 else 0) + ∑ bc : F × F,
          (if v 0 * bc.1 + v 1 * bc.2 = v 0 * r + v 1 * t ∧ bc.1 ≠ r then 1 else 0) * w bc := by
      by_cases hv : v 1 = 0
      · rw [if_pos hv]
        refine (le_trans (b := ‖ψ‖ ^ 2) ?_ (le_add_of_nonneg_right
          (Finset.sum_nonneg fun bc _ => mul_nonneg (by split_ifs <;> norm_num) (hw bc))))
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [applyOperatorToState_mul]
        exact (MagicSquareRigidity.norm_applyOperatorToState_le
          (MagicSquareRigidity.conjTranspose_mul_le_one_of_isProj (hX r).one_sub) _).trans
          (MagicSquareRigidity.norm_applyOperatorToState_le (orderedIndicator_gram_le_one X Z hX hZ _ _ _) ψ)
      · rw [if_neg hv, zero_add, MagicSquareRigidity.norm_applyOperatorToState_sq]
        change stateQForm ψ _ ≤ _
        rw [hgram _ _ _ hv, stateQForm_finset_sum]
        exact le_of_eq (Finset.sum_congr rfl fun bc _ => by split_ifs <;> simp [w, stateQForm, applyOperatorToState])
    have hcoll (bc : F × F) :
        avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
          if v 0 * bc.1 + v 1 * bc.2 = v 0 * r + v 1 * t ∧ bc.1 ≠ r then (1 : ℝ) else 0) ≤
          (Fintype.card F : ℝ)⁻¹ := by
      by_cases hb : bc.1 = r
      · simp [hb, avgOver_uniform_const]
      · rw [avgOver_uniform_equiv (finTwoArrowEquiv F)]
        have hne : bc ≠ (r, t) := fun h => hb (congrArg Prod.fst h)
        simpa [finTwoArrowEquiv, hb, hne] using (affine_collision_average bc (r, t)).le
    have h := avgOver_mono (uniformDistribution (Fin 2 → F)) _ _ hpt
    simp only [avgOver_add, avgOver_sum, avgOver_mul_const, avgOver_finTwo_snd_zero] at h
    have hc := Finset.sum_le_sum (s := Finset.univ) fun bc _ => mul_le_mul_of_nonneg_right (hcoll bc) (hw bc)
    rw [← Finset.mul_sum, hsum] at hc
    linarith
  have hpoint (v : Fin 2 → F) :
      ‖applyOperatorToState (1 - X.effect r) ψ‖ ^ 2 ≤
        2 * ‖ψ - applyOperatorToState (orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) ψ‖ ^ 2 +
        2 * ‖applyOperatorToState ((1 - X.effect r) *
          orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) ψ‖ ^ 2 := by
    let T := orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)
    have h := sum_mass_le_residual_add_image (Finset.univ : Finset Unit)
      (fun _ => applyOperatorToState (1 - X.effect r) ψ)
      (fun _ => applyOperatorToState ((1 - X.effect r) * T) ψ)
    simp only [Finset.univ_unique, Finset.sum_singleton] at h
    have hcontract : ‖applyOperatorToState (1 - X.effect r) ψ -
        applyOperatorToState ((1 - X.effect r) * T) ψ‖ ≤ ‖ψ - applyOperatorToState T ψ‖ := by
      rw [applyOperatorToState_mul, show applyOperatorToState (1 - X.effect r) ψ -
          applyOperatorToState (1 - X.effect r) (applyOperatorToState T ψ) =
          applyOperatorToState (1 - X.effect r) (ψ - applyOperatorToState T ψ) by
        simp only [applyOperatorToState, map_sub]]
      exact MagicSquareRigidity.norm_applyOperatorToState_le
        (MagicSquareRigidity.conjTranspose_mul_le_one_of_isProj (hX r).one_sub) _
    exact h.trans (add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hcontract 2) (by norm_num)) le_rfl)
  have h := avgOver_mono (uniformDistribution (Fin 2 → F)) _ _ hpoint
  simp only [avgOver_uniform_const, avgOver_add, avgOver_const_mul] at h
  linarith

end
end PolynomialImageBounds

/-! ## Section 2: Pair completion -/

noncomputable def recoverCombinedPair {K : Type*} [CommSemiring K] {m : ℕ}
    (polynomial : MvPolynomial (Fin (2 * m + 2)) K) :
    MvPolynomial (Fin m) K × MvPolynomial (Fin m) K :=
  (MvPolynomial.eval₂ MvPolynomial.C (fun index =>
    match finCombineEquiv m index with
    | .inl (.inl coordinate) => MvPolynomial.X coordinate
    | .inl (.inr _) => 0
    | .inr scalar => if scalar = 0 then 1 else 0) polynomial,
   MvPolynomial.eval₂ MvPolynomial.C (fun index =>
    match finCombineEquiv m index with
    | .inl (.inl _) => 0
    | .inl (.inr coordinate) => MvPolynomial.X coordinate
    | .inr scalar => if scalar = 1 then 1 else 0) polynomial)

@[simp] theorem recoverCombinedPair_combinePoly {K : Type*} [CommSemiring K] {m : ℕ}
    (first second : MvPolynomial (Fin m) K) :
    recoverCombinedPair (combinePoly first second) = (first, second) := by
  simp [recoverCombinedPair, combinePoly, MvPolynomial.eval₂_rename,
    embX, embZ, alphaVar, betaVar, Function.comp_def, MvPolynomial.eval₂_eta]

theorem combinePoly_injective {K : Type*} [CommSemiring K] {m : ℕ} :
    Function.Injective (fun pair : MvPolynomial (Fin m) K × MvPolynomial (Fin m) K =>
      combinePoly pair.1 pair.2) :=
  (show Function.LeftInverse recoverCombinedPair _ from fun p => recoverCombinedPair_combinePoly p.1 p.2).injective

noncomputable def combinedPolyEmbedding (P : AdmissibleParams) :
    PolyPair P ↪ MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d where
  toFun pair := ⟨combinePoly pair.1.1 pair.2.1, combinePoly_mem_polyFunc P.hd pair.1.2 pair.2.2⟩
  inj' := by
    intro first second heq
    have hpoly : combinePoly first.1.1 first.2.1 = combinePoly second.1.1 second.2.1 :=
      congrArg Subtype.val heq
    have hpair : (first.1.1, first.2.1) = (second.1.1, second.2.1) :=
      combinePoly_injective hpoly
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hpair))
      (Subtype.ext (congrArg Prod.snd hpair))

theorem combinedPolyEmbedding_eval (P : AdmissibleParams)
    (u : Fin (2 * P.m + 2) → PauliScalar P) (pair : PolyPair P) :
    MvPolynomial.eval u (combinedPolyEmbedding P pair).1 =
      u (alphaVar P.m) * evalAt .X (projX u) pair + u (betaVar P.m) * evalAt .Z (projZ u) pair := by
  change MvPolynomial.eval u (combinePoly pair.1.1 pair.2.1) = _
  rw [combinePoly_eval]; rfl

noncomputable def combinedPairSubmeasurement (P : AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) carrier) :
    Quantum.Submeasurement (PolyPair P) carrier where
  effect pair := measurement.effect (combinedPolyEmbedding P pair)
  pos pair := measurement.pos _
  sum_le_one := by
    classical
    rw [← Finset.sum_image (fun _ _ _ _ h => (combinedPolyEmbedding P).injective h)]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun o _ _ => measurement.pos o)).trans measurement.sum_le_one

noncomputable def completedPairLabel (P : AdmissibleParams) (completionPair : PolyPair P) :
    MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d → PolyPair P :=
  Function.extend (combinedPolyEmbedding P) id (fun _ => completionPair)

@[simp] theorem completedPairLabel_combinedPolyEmbedding (P : AdmissibleParams)
    (completionPair pair : PolyPair P) :
    completedPairLabel P completionPair (combinedPolyEmbedding P pair) = pair :=
  (combinedPolyEmbedding P).injective.extend_apply _ _ _

noncomputable def completedPairMeasurement (P : AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) carrier)
    (completionPair : PolyPair P) : Quantum.Measurement (PolyPair P) carrier :=
  measurement.postprocess (completedPairLabel P completionPair)

theorem completedPairMeasurement_effect (P : AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) carrier)
    (completionPair pair : PolyPair P) :
    (completedPairMeasurement P measurement completionPair).effect pair =
      (combinedPairSubmeasurement P measurement).effect pair +
        if pair = completionPair then 1 - (combinedPairSubmeasurement P measurement).total else 0 := by
  classical
  have hmiss : 1 - (combinedPairSubmeasurement P measurement).total =
      ∑ p ∈ Finset.univ.filter (fun p => p ∉ Set.range (combinedPolyEmbedding P)), measurement.effect p := by
    have htot : (combinedPairSubmeasurement P measurement).total =
        ∑ p ∈ Finset.univ.filter (fun p => p ∈ Set.range (combinedPolyEmbedding P)), measurement.effect p := by
      change (∑ q, measurement.effect (combinedPolyEmbedding P q)) = _
      rw [← Finset.sum_image (fun _ _ _ _ h => (combinedPolyEmbedding P).injective h)]
      congr 1; ext; simp
    rw [htot, ← measurement.sum_eq_one]
    exact sub_eq_iff_eq_add.mpr ((Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun p => p ∈ Set.range (combinedPolyEmbedding P)) measurement.effect).symm.trans (add_comm _ _))
  rw [completedPairMeasurement, Quantum.Measurement.postprocess_effect, Finset.sum_filter,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => p ∈ Set.range (combinedPolyEmbedding P))]
  have hgood : Finset.univ.filter (fun p => p ∈ Set.range (combinedPolyEmbedding P)) =
      Finset.univ.image (combinedPolyEmbedding P) := by ext; simp
  rw [hgood, Finset.sum_image (fun _ _ _ _ h => (combinedPolyEmbedding P).injective h)]
  simp only [completedPairLabel_combinedPolyEmbedding]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ pair)]
  congr 1
  have hbad : (∑ p ∈ Finset.univ.filter (fun p => p ∉ Set.range (combinedPolyEmbedding P)),
      if completedPairLabel P completionPair p = pair then measurement.effect p else 0) =
      ∑ p ∈ Finset.univ.filter (fun p => p ∉ Set.range (combinedPolyEmbedding P)),
        if completionPair = pair then measurement.effect p else 0 :=
    Finset.sum_congr rfl fun p hp => by
      rw [completedPairLabel, Function.extend_apply' _ _ _ (Finset.mem_filter.mp hp).2]
  rw [hbad]
  by_cases heq : pair = completionPair
  · simp [heq, hmiss]
  · simp [heq, Ne.symm heq]

theorem completedPairMeasurement_projective (P : AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) carrier)
    (hprojective : Measurement.IsProjective measurement) (completionPair : PolyPair P) :
    Measurement.IsProjective (completedPairMeasurement P measurement completionPair) :=
  SandwichProduct.postprocess_isProjective measurement hprojective _

/-! ## Section 3: Extended direct low-degree strategy and passing value -/

namespace ExtendedLineGame

set_option synthInstance.maxSize 400

open PolynomialImageBounds

theorem directEvalOpt_eq_some_iff {params : DirectLdParams} {degree : ℕ}
    (line : DirectLineDesc params) (point : Fin params.m → DirectScalarQ params)
    (coeffs : DirectDegPoly params degree) (answer : DirectScalarQ params) :
    directEvalOpt line point coeffs = some answer ↔
      DirectEvaluatesTo line coeffs point answer := by
  classical
  unfold directEvalOpt
  split_ifs with hexists
  · simp only [Option.some.injEq]
    refine ⟨fun heq => by simpa [heq] using Classical.choose_spec hexists, fun heval => ?_⟩
    obtain ⟨t, ht⟩ := heval.1
    exact ((Classical.choose_spec hexists).2 t ht).symm.trans (heval.2 t ht)
  · simp only [reduceCtorEq, false_iff]
    exact fun heval => hexists ⟨answer, heval⟩

theorem directEvalOpt_eq_of_eval_eq {params : DirectLdParams} {d1 d2 : ℕ}
    (line : DirectLineDesc params) (point : Fin params.m → DirectScalarQ params)
    (c1 : DirectDegPoly params d1) (c2 : DirectDegPoly params d2)
    (heval : ∀ t, evalCoefficient c1 t = evalCoefficient c2 t) :
    directEvalOpt line point c1 = directEvalOpt line point c2 := by
  cases h2 : directEvalOpt line point c2 with
  | none =>
    cases h1 : directEvalOpt line point c1 with
    | none => rfl
    | some a =>
      have hs := (directEvalOpt_eq_some_iff line point c1 a).1 h1
      have h2' := (directEvalOpt_eq_some_iff line point c2 a).2
        ⟨hs.1, fun t ht => (heval t).symm.trans (hs.2 t ht)⟩
      rw [h2] at h2'; cases h2'
  | some a =>
    have hs := (directEvalOpt_eq_some_iff line point c2 a).1 h2
    exact (directEvalOpt_eq_some_iff line point c1 a).2
      ⟨hs.1, fun t ht => (heval t).trans (hs.2 t ht)⟩

theorem axis_degree_le (params : AdmissibleParams) :
    params.d + 1 ≤ params.m * params.d + 2 := by
  have := Nat.mul_le_mul_right params.d params.one_le_m; omega

def axisRead (params : AdmissibleParams)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1)) :
    DirectDegPoly params.extendedDirectLd params.d :=
  fun index => coeffs (Fin.castLE (axis_degree_le params) index)

theorem axisRead_eval (params : AdmissibleParams)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
    (hsupport : ∀ index, params.d < index.val → coeffs index = 0)
    (parameter : DirectScalarQ params.extendedDirectLd) :
    evalCoefficient (axisRead params coeffs) parameter = evalCoefficient coeffs parameter := by
  unfold evalCoefficient axisRead
  refine Fintype.sum_of_injective (Fin.castLE (axis_degree_le params))
    (Fin.castLE_injective _) _ (fun index => coeffs index * parameter ^ index.val) ?_ (fun _ => rfl)
  intro index hindex
  have hlarge : params.d < index.val := by
    by_contra h; exact hindex ⟨⟨index.val, by omega⟩, Fin.ext rfl⟩
  simp [hsupport index hlarge]

theorem diagonal_degree_le (params : AdmissibleParams) :
    params.m * params.d + 2 ≤ params.extendedDirectLd.m * params.extendedDirectLd.d + 1 := by
  change params.m * params.d + 2 ≤ (2 * params.m + 2) * params.d + 1
  have := params.hd; nlinarith

def diagonalRead (params : AdmissibleParams)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1)) :
    DirectDegPoly params.extendedDirectLd (params.extendedDirectLd.m * params.extendedDirectLd.d) :=
  fun index => if bound : index.val < params.m * params.d + 2 then coeffs ⟨index.val, bound⟩ else 0

theorem diagonalRead_eval (params : AdmissibleParams)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
    (parameter : DirectScalarQ params.extendedDirectLd) :
    evalCoefficient (diagonalRead params coeffs) parameter = evalCoefficient coeffs parameter := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE (diagonal_degree_le params))
    (Fin.castLE_injective _) _ _ ?_ (fun index => by simp [diagonalRead, index.isLt])
  intro index hindex
  have hlarge : ¬index.val < params.m * params.d + 2 := fun h => hindex ⟨⟨index.val, h⟩, Fin.ext rfl⟩
  simp [diagonalRead, hlarge]

def pointAnswer (params : AdmissibleParams) (answer : PauliScalar params) :
    DirectLdAnswer params.extendedDirectLd :=
  .pointVals (fun _ => (extendedDirectScalarEquiv params).symm answer)

def axisAnswer (params : AdmissibleParams)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1)) :
    DirectLdAnswer params.extendedDirectLd :=
  .alinePolys (fun _ => axisRead params coeffs)

def diagonalAnswer (params : AdmissibleParams)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1)) :
    DirectLdAnswer params.extendedDirectLd :=
  .dlinePolys (fun _ => diagonalRead params coeffs)

theorem axis_description_canonical (params : DirectLdParams) (sample : DirectLdSpace params) :
    directALineDescOf params (directLdMap params .aline sample) = directALineDescOf params sample := by
  simp [directALineDescOf, directLdMap, lineRepMap_apply_self]

theorem diagonal_description_canonical (params : DirectLdParams) (sample : DirectLdSpace params) :
    directDLineDescOf params (directLdMap params .dline sample) = directDLineDescOf params sample := by
  have hprefix : directPrefixProjection sample.index
      (directPrefixProjection sample.index sample.direction) =
        directPrefixProjection sample.index sample.direction := by
    funext index
    by_cases hindex : index.val < sample.index.val <;> simp [directPrefixProjection, hindex]
  simp [directDLineDescOf, directLdMap, hprefix, lineRepMap_apply_self]

def answerMeasurement {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
    {setting : ProjectiveSetting P epsilon} {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL)
    (side : PlayerSide) (question : DirectLdQuestion P.extendedDirectLd) :
    Measurement (DirectLdAnswer P.extendedDirectLd) (setting.ExpandedLocalSpace side) :=
  match question.1 with
  | .point =>
    let point := directPointToPauli P question.2.point
    (points.extendedQ side (projX point) (projZ point)
      (point (alphaVar P.m)) (point (betaVar P.m))).postprocess (pointAnswer P)
  | .aline =>
    (lines.Qline side (directALineDescOf P.extendedDirectLd question.2)).postprocess (axisAnswer P)
  | .dline =>
    (lines.Qline side (directDLineDescOf P.extendedDirectLd question.2)).postprocess (diagonalAnswer P)

theorem answerMeasurement_effect_eq_zero {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
    {setting : ProjectiveSetting P epsilon} {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL) (side : PlayerSide)
    (question : DirectLdQuestion P.extendedDirectLd)
    (answer : DirectLdAnswer P.extendedDirectLd)
    (hanswer : validDirectLdAnswer question.1 answer = false) :
    (answerMeasurement lines side question).effect answer = 0 := by
  classical
  rcases question with ⟨kind, question⟩
  cases kind <;> cases answer <;>
    simp_all [validDirectLdAnswer, answerMeasurement,
      MIPStarRE.Quantum.Measurement.postprocess, MIPStarRE.Quantum.Submeasurement.postprocess,
      pointAnswer, axisAnswer, diagonalAnswer]

theorem completedLinePointDefect_sums_le {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
    {setting : ProjectiveSetting P epsilon} {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL) :
    (completedLinePointDefect lines .AA' .BA'' (directALinePointDist P.extendedDirectLd) +
      completedLinePointDefect lines .AA' .BA'' (directDLinePointDist P.extendedDirectLd) ≤ 2 * deltaL) ∧
    (completedLinePointDefect lines .BB' .AB'' (directALinePointDist P.extendedDirectLd) +
      completedLinePointDefect lines .BB' .AB'' (directDLinePointDist P.extendedDirectLd) ≤ 2 * deltaL) := by
  have hhalf (p1 p2 : Placement) :
      completedLinePointDefect lines p1 p2 (directLinePointDist P.extendedDirectLd) =
        (completedLinePointDefect lines p1 p2 (directALinePointDist P.extendedDirectLd) +
          completedLinePointDefect lines p1 p2 (directDLinePointDist P.extendedDirectLd)) / 2 := by
    unfold completedLinePointDefect consistencyDefect
    rw [directLinePointDist, WinImplications.avgOver_mix]; ring
  refine ⟨?_, ?_⟩
  · have h := lines.consistent_alice
    change completedLinePointDefect lines .AA' .BA'' _ ≤ deltaL at h
    rw [hhalf] at h; linarith
  · have h := lines.consistent_bob
    change completedLinePointDefect lines .BB' .AB'' _ ≤ deltaL at h
    rw [hhalf] at h; linarith

def strategy {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
    {setting : ProjectiveSetting P epsilon} {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL) :
    Strategy (directLdGame P.extendedDirectLd) where
  ιA := setting.ExpandedLocalSpace .alice
  ιB := setting.ExpandedLocalSpace .bob
  ψ := pairState setting
  ψ_norm := pairState_norm setting
  A := answerMeasurement lines .alice
  B := answerMeasurement lines .bob

theorem outcomeWeight_eq_zero_of_invalid {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
    {setting : ProjectiveSetting P epsilon} {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL)
    (questionA questionB : DirectLdQuestion P.extendedDirectLd)
    (answerA answerB : DirectLdAnswer P.extendedDirectLd)
    (hinvalid : validDirectLdAnswer questionA.1 answerA = false ∨
      validDirectLdAnswer questionB.1 answerB = false) :
    outcomeWeight (strategy lines) questionA questionB answerA answerB = 0 := by
  rcases hinvalid with h | h
  · have hz := answerMeasurement_effect_eq_zero lines .alice questionA answerA h
    change (inner ℂ (pairState setting) (applyOperatorToState
      (heteroKron ((answerMeasurement lines .alice questionA).effect answerA)
        ((answerMeasurement lines .bob questionB).effect answerB)) (pairState setting))).re = 0
    rw [hz]; simp [heteroKron, applyOperatorToState]
  · have hz := answerMeasurement_effect_eq_zero lines .bob questionB answerB h
    change (inner ℂ (pairState setting) (applyOperatorToState
      (heteroKron ((answerMeasurement lines .alice questionA).effect answerA)
        ((answerMeasurement lines .bob questionB).effect answerB)) (pairState setting))).re = 0
    rw [hz]; simp [heteroKron, applyOperatorToState]

theorem strategy_value_eq {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
    {setting : ProjectiveSetting P epsilon} {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL) :
    (strategy lines).value = 1 -
      (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .aline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .dline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.aline, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.aline, .aline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.dline, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.dline, .dline)) / 9 := by
  have hmix (types : LdType × LdType) (ht : types = (.aline, .dline) ∨ types = (.dline, .aline)) :
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) types = 0 := by
    unfold directLdBranchRejectionProbability
    conv_rhs => rw [← avgOver_zero (uniformDistribution (DirectLdSpace P.extendedDirectLd))]
    refine avgOver_congr _ _ _ fun s => Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    by_cases hA : validDirectLdAnswer types.1 a = false
    · rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl hA)]; simp
    by_cases hB : validDirectLdAnswer types.2 b = false
    · rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr hB)]; simp
    rcases ht with rfl | rfl <;> cases a <;> cases b <;> simp_all [validDirectLdAnswer, directLdWinPredicate]
  have hv := directLdRejectionProbability_eq_one_sub_value P.extendedDirectLd (strategy lines)
  rw [directLdRejectionProbability, avgOver_ldType_pair,
    hmix _ (Or.inl rfl), hmix _ (Or.inr rfl)] at hv
  linarith

/-! ### Unified line/point, point/point, and same-line branch bounds -/

abbrev lineLdType : LineKind → LdType
  | .axis => .aline
  | .diagonal => .dline

abbrev lineDescOf (D : DirectLdParams) : LineKind → DirectLdSpace D → DirectLineDesc D
  | .axis => directALineDescOf D
  | .diagonal => directDLineDescOf D

abbrev linePointDistOf (D : DirectLdParams) :
    LineKind → Distribution (DirectLineDesc D × (Fin D.m → DirectScalarQ D))
  | .axis => directALinePointDist D
  | .diagonal => directDLinePointDist D

def onlyCoordinate {P : AdmissibleParams} : Fin P.extendedDirectLd.k :=
  ⟨0, by change 0 < 1; decide⟩

theorem eq_onlyCoordinate {P : AdmissibleParams} (i : Fin P.extendedDirectLd.k) :
    i = onlyCoordinate := by
  apply Fin.ext
  have hi : i.val < 1 := i.isLt
  change i.val = 0; omega

def pointGameRead {P : AdmissibleParams} :
    DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)
  | .pointVals values => some (extendedDirectScalarEquiv P (values onlyCoordinate))
  | _ => none

def lineGameRead {P : AdmissibleParams} (k : LineKind)
    (sample : DirectLdSpace P.extendedDirectLd) :
    DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P) := fun a =>
  match k, a with
  | .axis, .alinePolys coeffs =>
      (directEvalOpt (directALineDescOf P.extendedDirectLd sample) sample.point
        (coeffs onlyCoordinate)).map (extendedDirectScalarEquiv P)
  | .diagonal, .dlinePolys coeffs =>
      (directEvalOpt (directDLineDescOf P.extendedDirectLd sample) sample.point
        (coeffs onlyCoordinate)).map (extendedDirectScalarEquiv P)
  | _, _ => none

theorem rejectedMass_eq_mismatch {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
    {setting : ProjectiveSetting P epsilon} {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL)
    (tA tB : LdType) (qA qB : DirectLdSpace P.extendedDirectLd)
    {α : Type*} [DecidableEq α] (fA fB : DirectLdAnswer P.extendedDirectLd → α)
    (hiff : ∀ a b, validDirectLdAnswer tA a = true → validDirectLdAnswer tB b = true →
      (directLdWinPredicate P.extendedDirectLd (tA, qA) (tB, qB) a b = true ↔ fA a = fB b)) :
    directRejectedMass P.extendedDirectLd (strategy lines) (tA, qA) (tB, qB) =
      outcomeEventWeight (strategy lines) (tA, qA) (tB, qB) (fun a b => fA a ≠ fB b) := by
  classical
  unfold directRejectedMass outcomeEventWeight
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hinv : validDirectLdAnswer tA a = false ∨ validDirectLdAnswer tB b = false
  · rw [outcomeWeight_eq_zero_of_invalid lines (tA, qA) (tB, qB) a b hinv]; simp
  · have ha : validDirectLdAnswer tA a = true := Bool.eq_true_of_not_eq_false fun h => hinv (Or.inl h)
    have hb : validDirectLdAnswer tB b = true := Bool.eq_true_of_not_eq_false fun h => hinv (Or.inr h)
    by_cases heq : fA a = fB b
    · simp [(hiff a b ha hb).mpr heq, heq]
    · have hnw : directLdWinPredicate P.extendedDirectLd (tA, qA) (tB, qB) a b = false :=
        Bool.eq_false_iff.mpr fun hw => heq ((hiff a b ha hb).mp hw)
      simp [hnw, heq]

theorem point_read_effect {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
    {setting : ProjectiveSetting P epsilon} {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL) (side : PlayerSide)
    (sample : DirectLdSpace P.extendedDirectLd) (answer : Option (PauliScalar P)) :
    (((answerMeasurement lines side
        (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
      pointGameRead).effect answer) =
      ((points.Q side (projX (directPointToPauli P sample.point))
        (projZ (directPointToPauli P sample.point))).postprocess fun values =>
          some (directPointToPauli P sample.point (alphaVar P.m) * values.1 +
            directPointToPauli P sample.point (betaVar P.m) * values.2)).effect answer := by
  classical
  unfold answerMeasurement CombinedPointsWitness.extendedQ
  rw [MIPStarRE.Quantum.Measurement.postprocess_comp,
    MIPStarRE.Quantum.Measurement.postprocess_comp]
  rfl

theorem line_read_effect {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
    {setting : ProjectiveSetting P epsilon} {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL) (k : LineKind) (side : PlayerSide)
    (sample : DirectLdSpace P.extendedDirectLd) (answer : Option (PauliScalar P)) :
    (((answerMeasurement lines side
        (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) sample)).postprocess
      (lineGameRead k sample)).effect answer) =
      (((lines.Qline side (lineDescOf P.extendedDirectLd k sample)).postprocess
        (fun coeffs => (directEvalOpt (lineDescOf P.extendedDirectLd k sample)
          sample.point coeffs).map (extendedDirectScalarEquiv P))).effect answer) := by
  classical
  cases k with
  | axis =>
    dsimp only [lineLdType, lineDescOf]
    unfold answerMeasurement
    rw [axis_description_canonical, MIPStarRE.Quantum.Measurement.postprocess_comp]
    simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
    refine Finset.sum_congr rfl fun coeffs _ => ?_
    by_cases heff : (lines.Qline side (directALineDescOf P.extendedDirectLd sample)).effect coeffs = 0
    · simp [heff]
    · have hev : ∀ t, evalCoefficient (axisRead P coeffs) t = evalCoefficient coeffs t := fun t =>
        axisRead_eval P coeffs (by by_contra hs; exact heff (lines.axis_degree side _ coeffs rfl hs)) t
      change (if Option.map (extendedDirectScalarEquiv P)
          (directEvalOpt _ _ (axisRead P coeffs)) = answer then _ else _) = _
      rw [directEvalOpt_eq_of_eval_eq _ _ _ _ hev]
  | diagonal =>
    dsimp only [lineLdType, lineDescOf]
    unfold answerMeasurement
    rw [diagonal_description_canonical, MIPStarRE.Quantum.Measurement.postprocess_comp]
    simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
    refine Finset.sum_congr rfl fun coeffs _ => ?_
    change (if Option.map (extendedDirectScalarEquiv P)
        (directEvalOpt _ _ (diagonalRead P coeffs)) = answer then _ else _) = _
    rw [directEvalOpt_eq_of_eval_eq _ _ _ _ (diagonalRead_eval P coeffs)]

theorem line_point_win_iff {P : AdmissibleParams} (k : LineKind)
    (sample : DirectLdSpace P.extendedDirectLd)
    (a b : DirectLdAnswer P.extendedDirectLd)
    (ha : validDirectLdAnswer (lineLdType k) a = true)
    (hb : validDirectLdAnswer .point b = true) :
    directLdWinPredicate P.extendedDirectLd
        (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) sample)
        (.point, directLdMap P.extendedDirectLd .point sample) a b = true ↔
      lineGameRead k sample a = pointGameRead b := by
  cases k <;> cases a <;> cases b <;> simp [lineLdType, validDirectLdAnswer] at ha hb
  · rename_i coeffs values
    let line := directALineDescOf P.extendedDirectLd sample
    have hmem : sample.point ∈ line.pointSet := by
      simpa [line, DirectLineDesc.pointSet, directALineDescOf,
        DirectLineDesc.base, DirectLineDesc.direction] using
        mem_linePoints_lineRepMap (coordinateDirection sample.index) sample.point
    constructor
    · intro hwin
      have hcond : directAlinePointCondition P.extendedDirectLd
          (directLdMap P.extendedDirectLd .aline sample)
          (directLdMap P.extendedDirectLd .point sample) coeffs values := by
        simpa [lineLdType, directLdWinPredicate, validDirectLdAnswer] using hwin
      have hopt : directEvalOpt line sample.point (coeffs onlyCoordinate) = some (values onlyCoordinate) :=
        (directEvalOpt_eq_some_iff _ _ _ _).2 ⟨hmem, fun t ht =>
          hcond t (by simpa [line, directALineDescOf, directLdMap, DirectLineDesc.base, DirectLineDesc.direction] using ht) onlyCoordinate⟩
      simp [lineGameRead, pointGameRead, line, hopt]
    · intro hread
      have hopt : directEvalOpt line sample.point (coeffs onlyCoordinate) = some (values onlyCoordinate) := by
        cases h : directEvalOpt line sample.point (coeffs onlyCoordinate) with
        | none => simp [lineGameRead, pointGameRead, line, h] at hread
        | some v =>
          have hv : v = values onlyCoordinate :=
            (extendedDirectScalarEquiv P).injective (by simpa [lineGameRead, pointGameRead, line, h] using hread)
          rw [hv]
      have hev := (directEvalOpt_eq_some_iff _ _ _ _).1 hopt
      simp only [lineLdType, directLdWinPredicate, validDirectLdAnswer, Bool.and_self, ↓reduceIte, decide_eq_true_eq]
      intro t ht idx
      rw [eq_onlyCoordinate idx]
      exact hev.2 t (by simpa [line, directALineDescOf, directLdMap, DirectLineDesc.base, DirectLineDesc.direction] using ht)
  · rename_i coeffs values
    let line := directDLineDescOf P.extendedDirectLd sample
    have hmem : sample.point ∈ line.pointSet := by
      simpa [line, DirectLineDesc.pointSet, directDLineDescOf,
        DirectLineDesc.base, DirectLineDesc.direction] using
        mem_linePoints_lineRepMap (directPrefixProjection sample.index sample.direction) sample.point
    constructor
    · intro hwin
      have hcond : directDlinePointCondition P.extendedDirectLd
          (directLdMap P.extendedDirectLd .dline sample)
          (directLdMap P.extendedDirectLd .point sample) coeffs values := by
        simpa [lineLdType, directLdWinPredicate, validDirectLdAnswer] using hwin
      have hopt : directEvalOpt line sample.point (coeffs onlyCoordinate) = some (values onlyCoordinate) :=
        (directEvalOpt_eq_some_iff _ _ _ _).2 ⟨hmem, fun t ht =>
          hcond t (by simpa [line, directDLineDescOf, directLdMap, DirectLineDesc.base, DirectLineDesc.direction] using ht) onlyCoordinate⟩
      simp [lineGameRead, pointGameRead, line, hopt]
    · intro hread
      have hopt : directEvalOpt line sample.point (coeffs onlyCoordinate) = some (values onlyCoordinate) := by
        cases h : directEvalOpt line sample.point (coeffs onlyCoordinate) with
        | none => simp [lineGameRead, pointGameRead, line, h] at hread
        | some v =>
          have hv : v = values onlyCoordinate :=
            (extendedDirectScalarEquiv P).injective (by simpa [lineGameRead, pointGameRead, line, h] using hread)
          rw [hv]
      have hev := (directEvalOpt_eq_some_iff _ _ _ _).1 hopt
      simp only [lineLdType, directLdWinPredicate, validDirectLdAnswer, Bool.and_self, ↓reduceIte, decide_eq_true_eq]
      intro t ht idx
      rw [eq_onlyCoordinate idx]
      exact hev.2 t (by simpa [line, directDLineDescOf, directLdMap, DirectLineDesc.base, DirectLineDesc.direction] using ht)

theorem point_line_win_iff {P : AdmissibleParams} (k : LineKind)
    (sample : DirectLdSpace P.extendedDirectLd)
    (a b : DirectLdAnswer P.extendedDirectLd)
    (ha : validDirectLdAnswer .point a = true)
    (hb : validDirectLdAnswer (lineLdType k) b = true) :
    directLdWinPredicate P.extendedDirectLd
        (.point, directLdMap P.extendedDirectLd .point sample)
        (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) sample) a b = true ↔
      pointGameRead a = lineGameRead k sample b := by
  have hsymm : directLdWinPredicate P.extendedDirectLd
      (.point, directLdMap P.extendedDirectLd .point sample)
      (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) sample) a b =
    directLdWinPredicate P.extendedDirectLd
      (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) sample)
      (.point, directLdMap P.extendedDirectLd .point sample) b a := by
    cases k <;> cases a <;> cases b <;> rfl
  rw [hsymm]
  exact (line_point_win_iff k sample b a hb ha).trans eq_comm

theorem line_point_rejection_eq {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
    {setting : ProjectiveSetting P epsilon} {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL) (k : LineKind) :
    (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (lineLdType k, .point) =
      consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun s a => heteroKron (((answerMeasurement lines .alice
          (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)).postprocess (lineGameRead k s)).effect a) 1)
        (fun s a => heteroKron 1 (((answerMeasurement lines .bob
          (.point, directLdMap P.extendedDirectLd .point s)).postprocess pointGameRead).effect a))
        (pairState setting)) ∧
    (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (lineLdType k, .point) =
      completedLinePointDefect lines .AA' .BA'' (linePointDistOf P.extendedDirectLd k)) := by
  have h1 : directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (lineLdType k, .point) =
      consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun s a => heteroKron (((answerMeasurement lines .alice
          (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)).postprocess (lineGameRead k s)).effect a) 1)
        (fun s a => heteroKron 1 (((answerMeasurement lines .bob
          (.point, directLdMap P.extendedDirectLd .point s)).postprocess pointGameRead).effect a))
        (pairState setting) := by
    rw [directLdBranchRejectionProbability_eq_avgOver]
    refine (avgOver_congr _ _ _ fun s =>
      rejectedMass_eq_mismatch lines _ _ _ _ (lineGameRead k s) pointGameRead (line_point_win_iff k s)).trans ?_
    exact (WinImplications.consistencyDefect_postprocess_eq_mismatch
      (uniformDistribution (DirectLdSpace P.extendedDirectLd)) (strategy lines)
      (fun s => (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s))
      (fun s => (.point, directLdMap P.extendedDirectLd .point s))
      (lineGameRead k) (fun _ => pointGameRead)).symm
  refine ⟨h1, h1.trans ?_⟩
  unfold completedLinePointDefect consistencyDefect
  have hdist : ∀ f, avgOver (linePointDistOf P.extendedDirectLd k) f =
      avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun s => f (lineDescOf P.extendedDirectLd k s, s.point)) := by
    intro f; cases k <;> simp [linePointDistOf, lineDescOf, directALinePointDist, directDLinePointDist,
      Distribution.avgOver_map]
  rw [hdist]
  refine avgOver_congr _ _ _ fun s => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : a = b
  · simp [hab]
  · simp only [hab, if_false, consistency_term_eq_stateQForm]
    rw [line_read_effect lines k .alice s a, point_read_effect lines .bob s b, placed_product_stateQForm_eq]
    exact stateQForm_pairState_eq_AA'_BA'' setting _ _
      (Matrix.nonneg_iff_posSemidef.mp ((_ : Measurement _ _).pos a)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp ((_ : Measurement _ _).pos b)).isHermitian

theorem point_line_rejection_eq {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
    {setting : ProjectiveSetting P epsilon} {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL) (k : LineKind) :
    (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, lineLdType k) =
      consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun s a => heteroKron (((answerMeasurement lines .alice
          (.point, directLdMap P.extendedDirectLd .point s)).postprocess pointGameRead).effect a) 1)
        (fun s a => heteroKron 1 (((answerMeasurement lines .bob
          (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)).postprocess (lineGameRead k s)).effect a))
        (pairState setting)) ∧
    (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, lineLdType k) =
      completedLinePointDefect lines .BB' .AB'' (linePointDistOf P.extendedDirectLd k)) := by
  have h1 : directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, lineLdType k) =
      consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun s a => heteroKron (((answerMeasurement lines .alice
          (.point, directLdMap P.extendedDirectLd .point s)).postprocess pointGameRead).effect a) 1)
        (fun s a => heteroKron 1 (((answerMeasurement lines .bob
          (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)).postprocess (lineGameRead k s)).effect a))
        (pairState setting) := by
    rw [directLdBranchRejectionProbability_eq_avgOver]
    refine (avgOver_congr _ _ _ fun s =>
      rejectedMass_eq_mismatch lines _ _ _ _ pointGameRead (lineGameRead k s) (point_line_win_iff k s)).trans ?_
    exact (WinImplications.consistencyDefect_postprocess_eq_mismatch
      (uniformDistribution (DirectLdSpace P.extendedDirectLd)) (strategy lines)
      (fun s => (.point, directLdMap P.extendedDirectLd .point s))
      (fun s => (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s))
      (fun _ => pointGameRead) (lineGameRead k)).symm
  refine ⟨h1, h1.trans ?_⟩
  unfold completedLinePointDefect consistencyDefect
  have hdist : ∀ f, avgOver (linePointDistOf P.extendedDirectLd k) f =
      avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun s => f (lineDescOf P.extendedDirectLd k s, s.point)) := by
    intro f; cases k <;> simp [linePointDistOf, lineDescOf, directALinePointDist, directDLinePointDist,
      Distribution.avgOver_map]
  rw [hdist]
  refine avgOver_congr _ _ _ fun s => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : a = b
  · simp [hab]
  · simp only [hab, Ne.symm hab, if_false, consistency_term_eq_stateQForm]
    rw [point_read_effect lines .alice s a, line_read_effect lines k .bob s b,
      placed_product_stateQForm_eq, setting.place_comm .BB' .AB'' trivial]
    exact stateQForm_pairState_eq_AB''_BB' setting _ _
      (Matrix.nonneg_iff_posSemidef.mp ((_ : Measurement _ _).pos a)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp ((_ : Measurement _ _).pos b)).isHermitian

noncomputable def directPointExtendedQuestionEquiv (P : AdmissibleParams) :
    (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) ≃ ExtendedPointQuestion P :=
  (Equiv.piCongrRight fun _ => (extendedDirectScalarEquiv P).toEquiv).trans <|
    ((finCombineEquiv P.m).piCongrLeft fun _ => PauliScalar P).trans <|
      (Equiv.sumPiEquivProdPi fun _ : (Fin P.m ⊕ Fin P.m) ⊕ Fin 2 => PauliScalar P).trans <|
        (Equiv.sumPiEquivProdPi fun _ : Fin P.m ⊕ Fin P.m => PauliScalar P).prodCongr
          (piFinTwoEquiv fun _ => PauliScalar P)

theorem directPointExtendedQuestionEquiv_apply (P : AdmissibleParams)
    (u : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    directPointExtendedQuestionEquiv P u =
      ((projX (directPointToPauli P u), projZ (directPointToPauli P u)),
        (directPointToPauli P u (alphaVar P.m), directPointToPauli P u (betaVar P.m))) := by
  have hpi {I J K : Type} (e : I ≃ J) (f : I → K) (j : J) :
      (e.piCongrLeft fun _ => K) f j = f (e.symm j) := by
    simp only [Equiv.piCongrLeft_apply, eq_rec_constant]
  apply Prod.ext
  · apply Prod.ext <;> funext i
    · change (finCombineEquiv P.m).piCongrLeft (fun _ => PauliScalar P)
        (fun j => extendedDirectScalarEquiv P (u j)) (.inl (.inl i)) = _
      rw [hpi]; rfl
    · change (finCombineEquiv P.m).piCongrLeft (fun _ => PauliScalar P)
        (fun j => extendedDirectScalarEquiv P (u j)) (.inl (.inr i)) = _
      rw [hpi]; rfl
  · apply Prod.ext
    · change (finCombineEquiv P.m).piCongrLeft (fun _ => PauliScalar P)
        (fun j => extendedDirectScalarEquiv P (u j)) (.inr 0) = _
      rw [hpi]; rfl
    · change (finCombineEquiv P.m).piCongrLeft (fun _ => PauliScalar P)
        (fun j => extendedDirectScalarEquiv P (u j)) (.inr 1) = _
      rw [hpi]; rfl

theorem point_branch_rejection_info {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
    {setting : ProjectiveSetting P epsilon} {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL) :
    (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .point) =
      consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun s a => heteroKron (((answerMeasurement lines .alice
          (.point, directLdMap P.extendedDirectLd .point s)).postprocess pointGameRead).effect a) 1)
        (fun s a => heteroKron 1 (((answerMeasurement lines .bob
          (.point, directLdMap P.extendedDirectLd .point s)).postprocess pointGameRead).effect a))
        (pairState setting)) ∧
    (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .point) ≤ deltaQ) := by
  have hpwin (u : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)
      (a b : DirectLdAnswer P.extendedDirectLd)
      (ha : validDirectLdAnswer .point a = true) (hb : validDirectLdAnswer .point b = true) :
      directLdWinPredicate P.extendedDirectLd
          (directLdPointQuestionOf P.extendedDirectLd u)
          (directLdPointQuestionOf P.extendedDirectLd u) a b = true ↔
        pointGameRead a = pointGameRead b := by
    cases a <;> cases b <;> simp [validDirectLdAnswer] at ha hb
    rename_i vA vB
    simp only [directLdPointQuestionOf, directLdWinPredicate, validDirectLdAnswer,
      Bool.and_self, if_true, decide_eq_true_eq, pointGameRead, Option.some.injEq]
    exact ⟨fun h => by rw [h], fun h => funext fun i => by
      rw [eq_onlyCoordinate i]; exact (extendedDirectScalarEquiv P).injective h⟩
  have hpt : directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .point) =
      consistencyDefect (uniformDistribution (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
        (fun u a => heteroKron (((points.Q .alice (projX (directPointToPauli P u))
          (projZ (directPointToPauli P u))).postprocess fun v =>
            some (directPointToPauli P u (alphaVar P.m) * v.1 +
              directPointToPauli P u (betaVar P.m) * v.2)).effect a) 1)
        (fun u a => heteroKron 1 (((points.Q .bob (projX (directPointToPauli P u))
          (projZ (directPointToPauli P u))).postprocess fun v =>
            some (directPointToPauli P u (alphaVar P.m) * v.1 +
              directPointToPauli P u (betaVar P.m) * v.2)).effect a))
        (pairState setting) := by
    rw [directLdBranchRejectionProbability_point_point_eq]
    refine (avgOver_congr _ _ _ fun u =>
      rejectedMass_eq_mismatch lines _ _ _ _ pointGameRead pointGameRead (hpwin u)).trans ?_
    refine (WinImplications.consistencyDefect_postprocess_eq_mismatch
      (uniformDistribution (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
      (strategy lines) (directLdPointQuestionOf P.extendedDirectLd)
      (directLdPointQuestionOf P.extendedDirectLd)
      (fun _ => pointGameRead) (fun _ => pointGameRead)).symm.trans ?_
    apply consistencyDefect_congr <;> intro u a
    · exact congrArg (heteroKron · 1)
        (point_read_effect lines .alice ⟨u, P.extendedDirectLd.firstIndex, 0⟩ a)
    · exact congrArg (heteroKron 1 ·)
        (point_read_effect lines .bob ⟨u, P.extendedDirectLd.firstIndex, 0⟩ a)
  refine ⟨?_, ?_⟩
  · rw [hpt]
    symm
    refine (consistencyDefect_congr _ _ _ _ _ (pairState setting)
      (fun s a => congrArg (heteroKron · 1) (point_read_effect lines .alice s a))
      (fun s a => congrArg (heteroKron 1 ·) (point_read_effect lines .bob s a))).trans ?_
    unfold consistencyDefect
    let f : (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) → ℝ := fun u =>
      ∑ a, ∑ b, if a = b then 0 else
        (inner ℂ (pairState setting) ((EuclideanSpace.equiv _ ℂ).symm
          ((heteroKron (((points.Q .alice (projX (directPointToPauli P u))
              (projZ (directPointToPauli P u))).postprocess fun v =>
                some (directPointToPauli P u (alphaVar P.m) * v.1 +
                  directPointToPauli P u (betaVar P.m) * v.2)).effect a) 1 *
            heteroKron 1 (((points.Q .bob (projX (directPointToPauli P u))
              (projZ (directPointToPauli P u))).postprocess fun v =>
                some (directPointToPauli P u (alphaVar P.m) * v.1 +
                  directPointToPauli P u (betaVar P.m) * v.2)).effect b)).mulVec
            (pairState setting)))).re
    exact avgOver_uniform_equiv_fst (directLdSpacePointEquiv P.extendedDirectLd) f
  · rw [hpt]
    have hcongr : consistencyDefect (uniformDistribution (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
        (fun u a => heteroKron (((points.Q .alice (projX (directPointToPauli P u))
          (projZ (directPointToPauli P u))).postprocess fun v =>
            some (directPointToPauli P u (alphaVar P.m) * v.1 +
              directPointToPauli P u (betaVar P.m) * v.2)).effect a) 1)
        (fun u a => heteroKron 1 (((points.Q .bob (projX (directPointToPauli P u))
          (projZ (directPointToPauli P u))).postprocess fun v =>
            some (directPointToPauli P u (alphaVar P.m) * v.1 +
              directPointToPauli P u (betaVar P.m) * v.2)).effect a))
        (pairState setting) =
      consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
        (fun q a => heteroKron (((points.Q .alice q.1.1 q.1.2).postprocess fun v =>
          some (q.2.1 * v.1 + q.2.2 * v.2)).effect a) 1)
        (fun q a => heteroKron 1 (((points.Q .bob q.1.1 q.1.2).postprocess fun v =>
          some (q.2.1 * v.1 + q.2.2 * v.2)).effect a))
        (pairState setting) := by
      rw [← consistencyDefect_uniform_question_equiv (directPointExtendedQuestionEquiv P)]
      apply consistencyDefect_congr <;> intro u a
      · rw [directPointExtendedQuestionEquiv_apply]
      · rw [directPointExtendedQuestionEquiv_apply]
    rw [hcongr]
    have hpost : consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
        (fun q a => heteroKron (((points.Q .alice q.1.1 q.1.2).postprocess fun v =>
          some (q.2.1 * v.1 + q.2.2 * v.2)).effect a) 1)
        (fun q a => heteroKron 1 (((points.Q .bob q.1.1 q.1.2).postprocess fun v =>
          some (q.2.1 * v.1 + q.2.2 * v.2)).effect a))
        (pairState setting) ≤
      consistencyDefect (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
        (fun xz v => heteroKron ((points.Q .alice xz.1 xz.2).effect v) 1)
        (fun xz v => heteroKron 1 ((points.Q .bob xz.1 xz.2).effect v))
        (pairState setting) := by
      refine (avgOver_mono _ _ _ fun q => ?_).trans_eq (avgOver_uniform_fst _)
      simpa only [consistencyDefect, avgOver_uniform_const] using
        consistencyDefect_postprocess_le (uniformDistribution Unit)
          (fun _ => points.Q .alice q.1.1 q.1.2) (fun _ => points.Q .bob q.1.1 q.1.2)
          (pairState setting) (fun v => some (q.2.1 * v.1 + q.2.2 * v.2))
    refine hpost.trans ?_
    have htr : consistencyDefect (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
        (fun xz v => heteroKron ((points.Q .alice xz.1 xz.2).effect v) 1)
        (fun xz v => heteroKron 1 ((points.Q .bob xz.1 xz.2).effect v)) (pairState setting) =
      consistencyDefect (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
        (fun xz v => (setting.placedMeasurement .AA' (points.Q .alice xz.1 xz.2)).effect v)
        (fun xz v => (setting.placedMeasurement .BA'' (points.Q .bob xz.1 xz.2)).effect v)
        setting.psiHat := by
      unfold consistencyDefect
      refine avgOver_congr _ _ _ fun xz => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : a = b
      · simp [hab]
      · simp only [hab, if_false, consistency_term_eq_stateQForm,
          placedMeasurement_effect, placed_product_stateQForm_eq]
        exact stateQForm_pairState_eq_AA'_BA'' setting _ _
          (Matrix.nonneg_iff_posSemidef.mp ((points.Q .alice xz.1 xz.2).pos a)).isHermitian
          (Matrix.nonneg_iff_posSemidef.mp ((points.Q .bob xz.1 xz.2).pos b)).isHermitian
    rw [htr]
    refine (consistencyDefect_le_opFamilyDistSq_of_projective
      (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz => setting.placedMeasurement .AA' (points.Q .alice xz.1 xz.2))
      (fun xz => setting.placedMeasurement .BA'' (points.Q .bob xz.1 xz.2))
      setting.psiHat
      (fun xz => setting.placedMeasurement_isProjective .AA' _ (points.projective .alice xz.1 xz.2))
      (fun xz => setting.placedMeasurement_isProjective .BA'' _ (points.projective .bob xz.1 xz.2))).trans ?_
    have heq_op : opFamilyDistSq (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
        (fun xz v => (setting.placedMeasurement .AA' (points.Q .alice xz.1 xz.2)).effect v)
        (fun xz v => (setting.placedMeasurement .BA'' (points.Q .bob xz.1 xz.2)).effect v)
        setting.psiHat =
      opFamilyDistSq (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
        (fun xz v => setting.place .AA' ((points.Q .alice xz.1 xz.2).effect v))
        (fun xz v => setting.place .BA'' ((points.Q .bob xz.1 xz.2).effect v))
        setting.psiHat := by
      apply DistanceCalculus.opFamilyDistSq_congr <;> intro xz v
      · exact setting.placedMeasurement_effect .AA' (points.Q .alice xz.1 xz.2) v
      · exact setting.placedMeasurement_effect .BA'' (points.Q .bob xz.1 xz.2) v
    rw [heq_op]
    exact points.self_consistent .AA' .BA'' trivial

abbrev lineDegree (P : AdmissibleParams) : LineKind → ℕ
  | .axis => P.d
  | .diagonal => P.extendedDirectLd.m * P.extendedDirectLd.d

abbrev lineCoeffsRead (P : AdmissibleParams) (k : LineKind) :
    DirectDegPoly P.extendedDirectLd (P.m * P.d + 1) → DirectDegPoly P.extendedDirectLd (lineDegree P k) :=
  match k with
  | .axis => axisRead P
  | .diagonal => diagonalRead P

def lineGameCoeffs {P : AdmissibleParams} (k : LineKind)
    (a : DirectLdAnswer P.extendedDirectLd) : DirectDegPoly P.extendedDirectLd (lineDegree P k) :=
  match k, a with
  | .axis, .alinePolys c => c onlyCoordinate
  | .diagonal, .dlinePolys c => c onlyCoordinate
  | _, _ => 0

abbrev lineCanonicalQuestion {P : AdmissibleParams} (k : LineKind)
    (line : DirectLineDesc P.extendedDirectLd) : DirectLdQuestion P.extendedDirectLd :=
  match k with
  | .axis => (.aline, ⟨line.base, line.index, 0⟩)
  | .diagonal => (.dline, ⟨line.base, line.index, line.direction⟩)

set_option maxHeartbeats 600000 in
theorem parameterEvalDefect_le_completed_add_none {G : Game} {params : DirectLdParams} {degree : ℕ}
    (S : Strategy G) (qA : G.QuestionA) (qB : G.QuestionB)
    (rA : G.AnswerA → DirectDegPoly params degree)
    (rB : G.AnswerB → DirectDegPoly params degree)
    (line : DirectLineDesc params) (parameter : DirectScalarQ params) :
    outcomeEventWeight S qA qB (fun a b => evalCoefficient (rA a) parameter ≠ evalCoefficient (rB b) parameter) ≤
      outcomeEventWeight S qA qB (fun a b =>
        directEvalOpt line (line.base + parameter • line.direction) (rA a) ≠
          directEvalOpt line (line.base + parameter • line.direction) (rB b)) +
      aliceEventWeight S qA (fun a => directEvalOpt line (line.base + parameter • line.direction) (rA a) = none) +
      bobEventWeight S qB (fun b => directEvalOpt line (line.base + parameter • line.direction) (rB b) = none) := by
  classical
  rw [← outcome_event_weight_left_eq S qA qB, ← outcome_event_weight_right_eq S qA qB]
  unfold outcomeEventWeight
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  dsimp only
  have hw := outcomeWeight_nonneg S qA qB a b
  by_cases hp : evalCoefficient (rA a) parameter ≠ evalCoefficient (rB b) parameter
  · have hor : directEvalOpt line (line.base + parameter • line.direction) (rA a) ≠
        directEvalOpt line (line.base + parameter • line.direction) (rB b) ∨
      directEvalOpt line (line.base + parameter • line.direction) (rA a) = none ∨
      directEvalOpt line (line.base + parameter • line.direction) (rB b) = none := by
      cases hA : directEvalOpt line (line.base + parameter • line.direction) (rA a) with
      | none => exact Or.inr (Or.inl rfl)
      | some vA =>
        cases hB : directEvalOpt line (line.base + parameter • line.direction) (rB b) with
        | none => exact Or.inr (Or.inr rfl)
        | some vB =>
          refine Or.inl fun heq => hp ?_
          rw [((directEvalOpt_eq_some_iff _ _ _ _).mp hA).2 parameter rfl,
            Option.some.inj heq, ((directEvalOpt_eq_some_iff _ _ _ _).mp hB).2 parameter rfl]
    rcases hor with hc | hnA | hnB
    · rw [if_pos hp, if_pos hc]; split_ifs <;> linarith
    · rw [if_pos hp, if_pos hnA]; split_ifs <;> linarith
    · rw [if_pos hp, if_pos hnB]; split_ifs <;> linarith
  · rw [if_neg hp]; split_ifs <;> linarith

theorem same_line_rejection_le {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
    {setting : ProjectiveSetting P epsilon} {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL) (k : LineKind) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (lineLdType k, lineLdType k) ≤
      (6 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL)) +
        (lineDegree P k : ℝ) / (P.extendedDirectLd.q : ℝ) := by
  classical
  let wrap : DirectDegPoly P.extendedDirectLd (lineDegree P k) → DirectLdAnswer P.extendedDirectLd :=
    match k with
    | .axis => fun c => .alinePolys (fun _ => c)
    | .diagonal => fun c => .dlinePolys (fun _ => c)
  have hwrap : (fun c => wrap (lineCoeffsRead P k c)) =
      match k with | .axis => axisAnswer P | .diagonal => diagonalAnswer P := by
    cases k <;> rfl
  have hcan (s : DirectLdSpace P.extendedDirectLd) :
      lineCanonicalQuestion k (lineDescOf P.extendedDirectLd k s) =
        (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s) := by
    cases k <;> rfl
  have hans_eff (side : PlayerSide) (s : DirectLdSpace P.extendedDirectLd) (a : DirectLdAnswer P.extendedDirectLd) :
      (answerMeasurement lines side (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)).effect a =
        (((lines.Qline side (lineDescOf P.extendedDirectLd k s)).postprocess (lineCoeffsRead P k)).postprocess wrap).effect a := by
    cases k <;> dsimp only [lineLdType, lineDescOf, lineCoeffsRead, wrap]
    · unfold answerMeasurement
      rw [axis_description_canonical]
      exact (SandwichProduct.postprocess_postprocess_effect
        (lines.Qline side (directALineDescOf P.extendedDirectLd s)) (axisRead P)
        (fun c => DirectLdAnswer.alinePolys (fun _ => c)) a).symm
    · unfold answerMeasurement
      rw [diagonal_description_canonical]
      exact (SandwichProduct.postprocess_postprocess_effect
        (lines.Qline side (directDLineDescOf P.extendedDirectLd s)) (diagonalRead P)
        (fun c => DirectLdAnswer.dlinePolys (fun _ => c)) a).symm
  -- Step 1: exact branch rejection <= raw coefficient defect <= parameter-evaluated coefficient defect + d_k / q
  have hstep1 : directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (lineLdType k, lineLdType k) ≤
      consistencyDefect
        (Distribution.prod ((linePointDistOf P.extendedDirectLd k).map Prod.fst)
          (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
        (fun s v => heteroKron (((((lines.Qline .alice s.1).postprocess (lineCoeffsRead P k)).postprocess
          (fun c => evalCoefficient c s.2)).effect v)) 1)
        (fun s v => heteroKron 1 (((((lines.Qline .bob s.1).postprocess (lineCoeffsRead P k)).postprocess
          (fun c => evalCoefficient c s.2)).effect v)))
        (pairState setting) + (lineDegree P k : ℝ) / (P.extendedDirectLd.q : ℝ) := by
    have hrej : directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (lineLdType k, lineLdType k) =
        consistencyDefect ((linePointDistOf P.extendedDirectLd k).map Prod.fst)
          (fun line a => heteroKron ((((lines.Qline .alice line).postprocess (lineCoeffsRead P k)).postprocess wrap).effect a) 1)
          (fun line a => heteroKron 1 ((((lines.Qline .bob line).postprocess (lineCoeffsRead P k)).postprocess wrap).effect a))
          (pairState setting) := by
      rw [directLdBranchRejectionProbability_eq_avgOver]
      have hsm (s : DirectLdSpace P.extendedDirectLd) :=
        rejectedMass_eq_mismatch lines (lineLdType k) (lineLdType k)
          (directLdMap P.extendedDirectLd (lineLdType k) s)
          (directLdMap P.extendedDirectLd (lineLdType k) s) id id
          (fun a b ha hb => by cases k <;> cases a <;> cases b <;>
            simp_all [lineLdType, validDirectLdAnswer, directLdWinPredicate])
      refine (avgOver_congr _ _ _ hsm).trans ?_
      have hans_mis : avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
          (fun s => outcomeEventWeight (strategy lines)
            (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)
            (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s) (fun a b => id a ≠ id b)) =
        consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
          (fun s a => heteroKron ((answerMeasurement lines .alice
            (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)).effect a) 1)
          (fun s a => heteroKron 1 ((answerMeasurement lines .bob
            (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)).effect a))
          (pairState setting) := by
        unfold consistencyDefect outcomeEventWeight
        refine avgOver_congr _ _ _ fun s => ?_
        simp only [consistency_term_eq_stateQForm]
        simp_rw [placed_product_stateQForm_eq]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        by_cases heq : a = b
        · simp [heq]
        · simp [heq, outcomeWeight, strategy, stateQForm]; rfl
      rw [hans_mis]
      have hmap : ∀ f, avgOver ((linePointDistOf P.extendedDirectLd k).map Prod.fst) f =
          avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
            (fun s => f (lineDescOf P.extendedDirectLd k s)) := by
        intro f; cases k <;> simp [linePointDistOf, lineDescOf, directALinePointDist, directDLinePointDist,
          Distribution.map_map, Distribution.avgOver_map]
      unfold consistencyDefect
      rw [hmap]
      refine avgOver_congr _ _ _ fun s => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      dsimp only
      rw [hans_eff .alice s a, hans_eff .bob s b]
    rw [hrej]
    have hprob : ((linePointDistOf P.extendedDirectLd k).map Prod.fst).IsProbability := by
      cases k
      · exact (directALinePointDist_isProbability P.extendedDirectLd).map _
      · exact (directDLinePointDist_isProbability P.extendedDirectLd).map _
    exact (consistencyDefect_postprocess_le ((linePointDistOf P.extendedDirectLd k).map Prod.fst)
      (fun line => (lines.Qline .alice line).postprocess (lineCoeffsRead P k))
      (fun line => (lines.Qline .bob line).postprocess (lineCoeffsRead P k))
      (pairState setting) wrap).trans
      (consistencyDefect_directCoefficients_le_evaluated_add P.extendedDirectLd (lineDegree P k)
        ((linePointDistOf P.extendedDirectLd k).map Prod.fst) _ _ (pairState setting) hprob (pairState_norm setting))
  -- Step 2: identify parameter-evaluated coefficient defect with strategy parameter-eval defect
  have hstep2 : consistencyDefect
      (Distribution.prod ((linePointDistOf P.extendedDirectLd k).map Prod.fst)
        (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
      (fun s v => heteroKron (((((lines.Qline .alice s.1).postprocess (lineCoeffsRead P k)).postprocess
        (fun c => evalCoefficient c s.2)).effect v)) 1)
      (fun s v => heteroKron 1 (((((lines.Qline .bob s.1).postprocess (lineCoeffsRead P k)).postprocess
        (fun c => evalCoefficient c s.2)).effect v)))
      (pairState setting) =
    avgOver (linePointDistOf P.extendedDirectLd k) (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
        outcomeEventWeight (strategy lines) (lineCanonicalQuestion k sample.1) (lineCanonicalQuestion k sample.1)
          (fun a b => evalCoefficient (lineGameCoeffs k a) t ≠ evalCoefficient (lineGameCoeffs k b) t))) := by
    let μ := Distribution.prod (uniformDistribution (DirectLdSpace P.extendedDirectLd))
      (uniformDistribution (DirectScalarQ P.extendedDirectLd))
    have heff (side : PlayerSide) (s : DirectLdSpace P.extendedDirectLd) (t v : DirectScalarQ P.extendedDirectLd) :
        ((((lines.Qline side (lineDescOf P.extendedDirectLd k s)).postprocess (lineCoeffsRead P k)).postprocess
          (fun c => evalCoefficient c t)).effect v) =
        (((answerMeasurement lines side (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)).postprocess
          (fun a => evalCoefficient (lineGameCoeffs k a) t)).effect v) := by
      cases k <;> dsimp only [lineLdType, lineDescOf, lineCoeffsRead, lineDegree]
      · unfold answerMeasurement
        rw [axis_description_canonical, MIPStarRE.Quantum.Measurement.postprocess_comp,
          MIPStarRE.Quantum.Measurement.postprocess_comp]
        rfl
      · unfold answerMeasurement
        rw [diagonal_description_canonical, MIPStarRE.Quantum.Measurement.postprocess_comp,
          MIPStarRE.Quantum.Measurement.postprocess_comp]
        rfl
    have hm : consistencyDefect
        (Distribution.prod ((linePointDistOf P.extendedDirectLd k).map Prod.fst)
          (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
        (fun s v => heteroKron (((((lines.Qline .alice s.1).postprocess (lineCoeffsRead P k)).postprocess
          (fun c => evalCoefficient c s.2)).effect v)) 1)
        (fun s v => heteroKron 1 (((((lines.Qline .bob s.1).postprocess (lineCoeffsRead P k)).postprocess
          (fun c => evalCoefficient c s.2)).effect v)))
        (pairState setting) =
      consistencyDefect μ
        (fun s v => heteroKron (((answerMeasurement lines .alice
          (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s.1)).postprocess
            (fun a => evalCoefficient (lineGameCoeffs k a) s.2)).effect v) 1)
        (fun s v => heteroKron 1 (((answerMeasurement lines .bob
          (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s.1)).postprocess
            (fun a => evalCoefficient (lineGameCoeffs k a) s.2)).effect v))
        (pairState setting) := by
      unfold consistencyDefect
      dsimp only [μ]
      have hmap : ∀ f, avgOver ((linePointDistOf P.extendedDirectLd k).map Prod.fst) f =
          avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
            (fun s => f (lineDescOf P.extendedDirectLd k s)) := by
        intro f; cases k <;> simp [linePointDistOf, lineDescOf, directALinePointDist, directDLinePointDist,
          Distribution.map_map, Distribution.avgOver_map]
      simp only [SandwichProduct.avgOver_distribution_prod, hmap]
      refine avgOver_congr _ _ _ fun s => avgOver_congr _ _ _ fun t =>
        Finset.sum_congr rfl fun vA _ => Finset.sum_congr rfl fun vB _ => ?_
      rw [heff .alice s t vA, heff .bob s t vB]
    rw [hm]
    change consistencyDefect μ
      (fun s v => heteroKron ((((strategy lines).A
        (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s.1)).postprocess
          (fun a => evalCoefficient (lineGameCoeffs k a) s.2)).effect v) 1)
      (fun s v => heteroKron 1 ((((strategy lines).B
        (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s.1)).postprocess
          (fun a => evalCoefficient (lineGameCoeffs k a) s.2)).effect v))
      (strategy lines).ψ = _
    rw [WinImplications.consistencyDefect_postprocess_eq_mismatch]
    dsimp only [μ]
    rw [SandwichProduct.avgOver_distribution_prod]
    have hmap2 : ∀ f, avgOver (linePointDistOf P.extendedDirectLd k) f =
        avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
          (fun s => f (lineDescOf P.extendedDirectLd k s, s.point)) := by
      intro f; cases k <;> simp [linePointDistOf, lineDescOf, directALinePointDist, directDLinePointDist,
        Distribution.avgOver_map]
    rw [hmap2]
    refine avgOver_congr _ _ _ fun s => avgOver_congr _ _ _ fun t => ?_
    rw [hcan s]
  -- Step 3: resample & bound completed evaluation + none masses
  have hstep3 : avgOver (linePointDistOf P.extendedDirectLd k) (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
        outcomeEventWeight (strategy lines) (lineCanonicalQuestion k sample.1) (lineCanonicalQuestion k sample.1)
          (fun a b => evalCoefficient (lineGameCoeffs k a) t ≠ evalCoefficient (lineGameCoeffs k b) t))) ≤
      6 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) := by
    let F : DirectLineDesc P.extendedDirectLd ×
        (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) → ℝ := fun s =>
      outcomeEventWeight (strategy lines) (lineCanonicalQuestion k s.1) (lineCanonicalQuestion k s.1)
          (fun a b => directEvalOpt s.1 s.2 (lineGameCoeffs k a) ≠ directEvalOpt s.1 s.2 (lineGameCoeffs k b)) +
        aliceEventWeight (strategy lines) (lineCanonicalQuestion k s.1)
          (fun a => directEvalOpt s.1 s.2 (lineGameCoeffs k a) = none) +
        bobEventWeight (strategy lines) (lineCanonicalQuestion k s.1)
          (fun b => directEvalOpt s.1 s.2 (lineGameCoeffs k b) = none)
    have hres : avgOver ((linePointDistOf P.extendedDirectLd k).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun t =>
          F (line, line.base + t • line.direction)) =
        avgOver (linePointDistOf P.extendedDirectLd k) F := by
      cases k
      · exact avgOver_directALinePointDist_resample P.extendedDirectLd F
      · exact avgOver_directDLinePointDist_resample P.extendedDirectLd F
    have havg : avgOver (linePointDistOf P.extendedDirectLd k) (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
          outcomeEventWeight (strategy lines) (lineCanonicalQuestion k sample.1) (lineCanonicalQuestion k sample.1)
            (fun a b => evalCoefficient (lineGameCoeffs k a) t ≠ evalCoefficient (lineGameCoeffs k b) t))) ≤
        avgOver (linePointDistOf P.extendedDirectLd k) F := by
      rw [← hres, Distribution.avgOver_map]
      exact avgOver_mono _ _ _ fun s => avgOver_mono _ _ _ fun t =>
        parameterEvalDefect_le_completed_add_none (strategy lines) _ _ _ _ s.1 t
    have hdist : ∀ f, avgOver (linePointDistOf P.extendedDirectLd k) f =
        avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
          (fun s => f (lineDescOf P.extendedDirectLd k s, s.point)) := by
      intro f; cases k <;> simp [linePointDistOf, lineDescOf, directALinePointDist, directDLinePointDist,
        Distribution.avgOver_map]
    have hcread (s : DirectLdSpace P.extendedDirectLd) (a : DirectLdAnswer P.extendedDirectLd)
        (ha : validDirectLdAnswer (lineLdType k) a = true) :
        (directEvalOpt (lineDescOf P.extendedDirectLd k s) s.point (lineGameCoeffs k a)).map
          (extendedDirectScalarEquiv P) = lineGameRead k s a := by
      cases k <;> cases a <;> simp_all [lineLdType, validDirectLdAnswer, lineDescOf, lineGameCoeffs, lineGameRead]
    have hcmis (s : DirectLdSpace P.extendedDirectLd) :
        outcomeEventWeight (strategy lines)
          (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)
          (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)
          (fun a b => directEvalOpt (lineDescOf P.extendedDirectLd k s) s.point (lineGameCoeffs k a) ≠
            directEvalOpt (lineDescOf P.extendedDirectLd k s) s.point (lineGameCoeffs k b)) =
        outcomeEventWeight (strategy lines)
          (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)
          (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)
          (fun a b => lineGameRead k s a ≠ lineGameRead k s b) := by
      unfold outcomeEventWeight
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      dsimp only
      by_cases hinv : validDirectLdAnswer (lineLdType k) a = false ∨ validDirectLdAnswer (lineLdType k) b = false
      · rw [outcomeWeight_eq_zero_of_invalid lines _ _ a b hinv]; simp
      · have ha := Bool.eq_true_of_not_eq_false fun h => hinv (Or.inl h)
        have hb := Bool.eq_true_of_not_eq_false fun h => hinv (Or.inr h)
        exact if_congr ((Option.map_injective (extendedDirectScalarEquiv P).injective).ne_iff.symm.trans
          (by rw [hcread s a ha, hcread s b hb])) rfl rfl
    have hnoneA (s : DirectLdSpace P.extendedDirectLd) :
        aliceEventWeight (strategy lines)
          (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)
          (fun a => directEvalOpt (lineDescOf P.extendedDirectLd k s) s.point (lineGameCoeffs k a) = none) ≤
        directRejectedMass P.extendedDirectLd (strategy lines)
          (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)
          (.point, directLdMap P.extendedDirectLd .point s) := by
      rw [← outcome_event_weight_left_eq (strategy lines)
        (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)
        (.point, directLdMap P.extendedDirectLd .point s),
        rejectedMass_eq_mismatch lines _ _ _ _ (lineGameRead k s) pointGameRead (line_point_win_iff k s)]
      unfold outcomeEventWeight
      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
      dsimp only
      by_cases hinv : validDirectLdAnswer (lineLdType k) a = false ∨ validDirectLdAnswer .point b = false
      · rw [outcomeWeight_eq_zero_of_invalid lines _ _ a b hinv]; simp
      · have ha := Bool.eq_true_of_not_eq_false fun h => hinv (Or.inl h)
        have hb := Bool.eq_true_of_not_eq_false fun h => hinv (Or.inr h)
        have hpb : pointGameRead b ≠ none := by cases b <;> simp_all [validDirectLdAnswer, pointGameRead]
        by_cases hn : directEvalOpt (lineDescOf P.extendedDirectLd k s) s.point (lineGameCoeffs k a) = none
        · have hln : lineGameRead k s a = none := by rw [← hcread s a ha, hn]; rfl
          have hne : lineGameRead k s a ≠ pointGameRead b := fun heq => hpb (heq.symm.trans hln)
          rw [if_pos hn, if_pos hne]
        · rw [if_neg hn]; split_ifs; exact outcomeWeight_nonneg _ _ _ _ _; exact le_rfl
    have hnoneB (s : DirectLdSpace P.extendedDirectLd) :
        bobEventWeight (strategy lines)
          (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)
          (fun b => directEvalOpt (lineDescOf P.extendedDirectLd k s) s.point (lineGameCoeffs k b) = none) ≤
        directRejectedMass P.extendedDirectLd (strategy lines)
          (.point, directLdMap P.extendedDirectLd .point s)
          (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s) := by
      rw [← outcome_event_weight_right_eq (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point s)
        (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s),
        rejectedMass_eq_mismatch lines _ _ _ _ pointGameRead (lineGameRead k s) (point_line_win_iff k s)]
      unfold outcomeEventWeight
      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
      dsimp only
      by_cases hinv : validDirectLdAnswer .point a = false ∨ validDirectLdAnswer (lineLdType k) b = false
      · rw [outcomeWeight_eq_zero_of_invalid lines _ _ a b hinv]; simp
      · have ha := Bool.eq_true_of_not_eq_false fun h => hinv (Or.inl h)
        have hb := Bool.eq_true_of_not_eq_false fun h => hinv (Or.inr h)
        have hpa : pointGameRead a ≠ none := by cases a <;> simp_all [validDirectLdAnswer, pointGameRead]
        by_cases hn : directEvalOpt (lineDescOf P.extendedDirectLd k s) s.point (lineGameCoeffs k b) = none
        · have hln : lineGameRead k s b = none := by rw [← hcread s b hb, hn]; rfl
          have hne : pointGameRead a ≠ lineGameRead k s b := fun heq => hpa (heq.trans hln)
          rw [if_pos hn, if_pos hne]
        · rw [if_neg hn]; split_ifs; exact outcomeWeight_nonneg _ _ _ _ _; exact le_rfl
    have hsame : avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd)) (fun s =>
        outcomeEventWeight (strategy lines)
          (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)
          (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)
          (fun a b => lineGameRead k s a ≠ lineGameRead k s b)) ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (lineLdType k, .point) +
        2 * Real.sqrt (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .point) +
          directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, lineLdType k)) := by
      rw [← WinImplications.consistencyDefect_postprocess_eq_mismatch
        (uniformDistribution (DirectLdSpace P.extendedDirectLd)) (strategy lines)
        (fun s => (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s))
        (fun s => (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s))
        (lineGameRead k) (lineGameRead k)]
      let μ := uniformDistribution (DirectLdSpace P.extendedDirectLd)
      let A := fun s => leftPlacedMeasurement (ιB := setting.ExpandedLocalSpace .bob)
        ((answerMeasurement lines .alice (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)).postprocess
          (lineGameRead k s))
      let B := fun s => rightPlacedMeasurement (ιA := setting.ExpandedLocalSpace .alice)
        ((answerMeasurement lines .bob (.point, directLdMap P.extendedDirectLd .point s)).postprocess pointGameRead)
      let C := fun s => leftPlacedMeasurement (ιB := setting.ExpandedLocalSpace .bob)
        ((answerMeasurement lines .alice (.point, directLdMap P.extendedDirectLd .point s)).postprocess pointGameRead)
      let D := fun s => rightPlacedMeasurement (ιA := setting.ExpandedLocalSpace .alice)
        ((answerMeasurement lines .bob (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)).postprocess
          (lineGameRead k s))
      exact consistencyDefect_trans_le μ A B C D (pairState setting) _ _ _
        (uniformDistribution_isProbability _) (pairState_norm setting)
        (line_point_rejection_eq lines k).1.symm.le
        (point_branch_rejection_info lines).1.symm.le
        (point_line_rejection_eq lines k).1.symm.le
    conv_rhs at havg => rw [hdist]
    dsimp only [F] at havg
    simp only [hcan, hcmis, avgOver_add] at havg
    have hnA_avg : avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd)) (fun s =>
        aliceEventWeight (strategy lines) (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)
          (fun a => directEvalOpt (lineDescOf P.extendedDirectLd k s) s.point (lineGameCoeffs k a) = none)) ≤
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (lineLdType k, .point) := by
      rw [directLdBranchRejectionProbability_eq_avgOver]; exact avgOver_mono _ _ _ hnoneA
    have hnB_avg : avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd)) (fun s =>
        bobEventWeight (strategy lines) (lineLdType k, directLdMap P.extendedDirectLd (lineLdType k) s)
          (fun b => directEvalOpt (lineDescOf P.extendedDirectLd k s) s.point (lineGameCoeffs k b) = none)) ≤
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, lineLdType k) := by
      rw [directLdBranchRejectionProbability_eq_avgOver]; exact avgOver_mono _ _ _ hnoneB
    have hsums := completedLinePointDefect_sums_le lines
    have hLP_A := (line_point_rejection_eq lines .axis).2
    have hLP_D := (line_point_rejection_eq lines .diagonal).2
    have hPL_A := (point_line_rejection_eq lines .axis).2
    have hPL_D := (point_line_rejection_eq lines .diagonal).2
    dsimp only [lineLdType, linePointDistOf] at hLP_A hLP_D hPL_A hPL_D
    rw [← hLP_A, ← hLP_D] at hsums
    rw [← hPL_A, ← hPL_D] at hsums
    have hpp := (point_branch_rejection_info lines).2
    have hnn1 := directLdBranchRejectionProbability_nonneg P.extendedDirectLd (strategy lines) (.aline, .point)
    have hnn2 := directLdBranchRejectionProbability_nonneg P.extendedDirectLd (strategy lines) (.dline, .point)
    have hnn3 := directLdBranchRejectionProbability_nonneg P.extendedDirectLd (strategy lines) (.point, .aline)
    have hnn4 := directLdBranchRejectionProbability_nonneg P.extendedDirectLd (strategy lines) (.point, .dline)
    cases k <;> dsimp only [lineLdType] at havg hsame hnA_avg hnB_avg
    · have hsq : Real.sqrt (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .point) +
          directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .aline)) ≤
          Real.sqrt (deltaQ + 2 * deltaL) := Real.sqrt_le_sqrt (by linarith)
      linarith
    · have hsq : Real.sqrt (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .point) +
          directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .dline)) ≤
          Real.sqrt (deltaQ + 2 * deltaL) := Real.sqrt_le_sqrt (by linarith)
      linarith
  linarith

theorem strategy_value_ge_directPassingErrorEnvelope {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
    {setting : ProjectiveSetting P epsilon} {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL) :
    1 - directPassingErrorEnvelope (deltaQ + deltaL) ((P.m * P.d : ℝ) / (P.q : ℝ)) ≤
      (strategy lines).value := by
  let rej := directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .point) +
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .aline) +
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .dline) +
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.aline, .point) +
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.aline, .aline) +
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.dline, .point) +
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.dline, .dline)
  have hpoint := (point_branch_rejection_info lines).2
  have hsums := completedLinePointDefect_sums_le lines
  have hLP_A := (line_point_rejection_eq lines .axis).2
  have hLP_D := (line_point_rejection_eq lines .diagonal).2
  have hPL_A := (point_line_rejection_eq lines .axis).2
  have hPL_D := (point_line_rejection_eq lines .diagonal).2
  dsimp only [lineLdType, linePointDistOf] at hLP_A hLP_D hPL_A hPL_D
  have hmix : directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.aline, .point) +
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.dline, .point) +
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .aline) +
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .dline) ≤ 4 * deltaL := by
    rw [hLP_A, hLP_D, hPL_A, hPL_D]; linarith [hsums.1, hsums.2]
  have haxis := same_line_rejection_le lines .axis
  have hdiag := same_line_rejection_le lines .diagonal
  dsimp only [lineLdType, lineDegree] at haxis hdiag
  push_cast at hdiag
  have hcoll : (P.d : ℝ) / (P.q : ℝ) + ((2 * (P.m : ℝ) + 2) * (P.d : ℝ)) / (P.q : ℝ) ≤
      5 * ((P.m * P.d : ℝ) / (P.q : ℝ)) := by
    have h := extendedDirectLd_coefficientCollisionLoss_le_five_mul P
    dsimp [AdmissibleParams.extendedDirectLd] at h; push_cast at h
    rw [← add_div]; exact h
  have hsum : rej ≤ deltaQ + 16 * deltaL + 4 * Real.sqrt (deltaQ + 2 * deltaL) +
      5 * ((P.m * P.d : ℝ) / (P.q : ℝ)) := by dsimp [rej]; linarith
  have hcap : rej / 9 ≤ 1 := by
    have h := directLdRejectionProbability_le_one P.extendedDirectLd (strategy lines)
    rw [directLdRejectionProbability_eq_one_sub_value, strategy_value_eq lines] at h
    dsimp only [rej] at *; linarith
  have henv := seven_branch_capped_error_le_directPassingErrorEnvelope
    deltaQ deltaL ((P.m * P.d : ℝ) / (P.q : ℝ))
    points.delta_nonneg lines.delta_nonneg (by positivity)
  have hrej : rej / 9 ≤ directPassingErrorEnvelope (deltaQ + deltaL) ((P.m * P.d : ℝ) / (P.q : ℝ)) :=
    (le_min hcap (by linarith)).trans henv
  rw [strategy_value_eq lines]; change 1 - _ ≤ 1 - rej / 9; linarith

/-! ## Section 4: Rounded extended-polynomial ordered estimates -/

def extendedPolynomialRead (P : AdmissibleParams) (x : ExtendedPointQuestion P)
    (g : DirectPolyTuple P.extendedDirectLd) : PauliScalar P :=
  extendedDirectScalarEquiv P
    (evalDirectPolyTupleAt ((directPointExtendedQuestionEquiv P).symm x) g (0 : Fin 1))

def extendedPolynomialOrderedError {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (reverse : Bool) : ℝ :=
  avgOver (uniformDistribution (ExtendedPointQuestion P)) (fun x =>
    ∑ g, ‖applyOperatorToState (S.place p1 (R.effect g) *
      (1 - S.place p2
        (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
            x.2.1 * ab.1 + x.2.2 * ab.2 = extendedPolynomialRead P x g),
          if reverse then
            (S.pointMeasExp p2.side .Z x.1.2).effect ab.2 *
              (S.pointMeasExp p2.side .X x.1.1).effect ab.1
          else
            (S.pointMeasExp p2.side .X x.1.1).effect ab.1 *
              (S.pointMeasExp p2.side .Z x.1.2).effect ab.2))) S.psiHat‖ ^ 2)

set_option maxHeartbeats 800000 in
theorem rounded_polynomial_ordered_estimates_explicit :
    ∀ (P : AdmissibleParams) (ε δQ δL : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ) (_lines : ExtendedLinesWitness S points δL),
      let delta := deltaLd pauliBaselineLowDegreeConstant pauliBaselineLowDegreePower
        (directPassingErrorEnvelope (δQ + δL) ((P.m * P.d : ℝ) / P.q))
        P.q (2 * P.m + 2) P.d 1
      let eta := delta + Real.sqrt (220 * Real.rpow delta (1 / 4 : ℝ)) + 2 * Real.sqrt (2 * delta)
      ∃ RA : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace .alice),
      ∃ RB : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace .bob),
        Measurement.IsProjective RA ∧ Measurement.IsProjective RB ∧
        ∀ reverse : Bool,
          extendedPolynomialOrderedError S .AA' .BA'' RA reverse ≤ 4 * eta + 8 * δQ ∧
          extendedPolynomialOrderedError S .BB' .AB'' RB reverse ≤ 4 * eta + 8 * δQ := by
  classical
  have ha : 1 ≤ pauliBaselineLowDegreeConstant := by unfold pauliBaselineLowDegreeConstant; norm_num
  intro P ε δQ δL S points lines delta eta
  have hm := P.one_le_m
  have hd := P.hd
  have hq : 0 < P.q := by obtain ⟨k, _, hk⟩ := P.hq; rw [hk]; positivity
  have hpos : 0 < directPassingErrorEnvelope (δQ + δL) ((P.m * P.d : ℝ) / P.q) :=
    directPassingErrorEnvelope_pos _ _ (by positivity)
  obtain ⟨A, B, hB, hA, hAB⟩ :=
    direct_ld_soundness_of_k_eq_one_any_strategy_explicit P.extendedDirectLd _ rfl hpos
      (strategy lines) (strategy_value_ge_directPassingErrorEnvelope lines)
  change consistencyDefect _ _ _ _ ≤ delta at hA hB hAB
  have hdelta : 0 ≤ delta := by
    dsimp [delta, deltaLd]; have : 0 ≤ pauliBaselineLowDegreeConstant := by linarith
    positivity
  obtain ⟨RA, RB, hRA, hRB, _, _, htr⟩ :=
    projective_rounding_preserves_postprocessed_consistency
      (pairState S) (pairState_norm S) A B delta hdelta hAB
  have hround := htr
    (uniformDistribution (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
    (uniformDistribution_isProbability _) (fun u => evalDirectPolyTupleAt u)
  have hRApt := hround.1
    (fun u => ((strategy lines).B (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
      (directLdPointValuesOrZero P.extendedDirectLd)) delta hA
  have hRBpt := hround.2
    (fun u => ((strategy lines).A (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
      (directLdPointValuesOrZero P.extendedDirectLd)) delta hB
  rw [← two_mul delta] at hRApt hRBpt
  change consistencyDefect _ _ _ _ ≤ eta at hRApt hRBpt
  have hAsc := (consistencyDefect_postprocess_question_le
    (uniformDistribution (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
    (fun u => RA.postprocess (evalDirectPolyTupleAt u))
    (fun u => ((strategy lines).B (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
      (directLdPointValuesOrZero P.extendedDirectLd)) (pairState S)
    (fun _ values => extendedDirectScalarEquiv P (values (0 : Fin 1)))).trans hRApt
  have hBsc := (consistencyDefect_postprocess_question_le
    (uniformDistribution (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
    (fun u => ((strategy lines).A (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
      (directLdPointValuesOrZero P.extendedDirectLd))
    (fun u => RB.postprocess (evalDirectPolyTupleAt u)) (pairState S)
    (fun _ values => extendedDirectScalarEquiv P (values (0 : Fin 1)))).trans hRBpt
  change consistencyDefect _ _ _ (pairState S) ≤ eta at hAsc hBsc
  have hpsm (side : PlayerSide) (u : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
      (((answerMeasurement lines side (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
        (directLdPointValuesOrZero P.extendedDirectLd)).postprocess
          (fun values => extendedDirectScalarEquiv P (values (0 : Fin 1)))) =
        points.extendedQ side (directPointExtendedQuestionEquiv P u).1.1
          (directPointExtendedQuestionEquiv P u).1.2
          (directPointExtendedQuestionEquiv P u).2.1
          (directPointExtendedQuestionEquiv P u).2.2 := by
    rw [directPointExtendedQuestionEquiv_apply]
    simp only [answerMeasurement, directLdPointQuestionOf,
      MIPStarRE.Quantum.Measurement.postprocess_comp,
      pointAnswer, directLdPointValuesOrZero, RingEquiv.apply_symm_apply]
    apply MIPStarRE.Quantum.Measurement.ext; intro a
    change (∑ b ∈ Finset.univ.filter (fun b : PauliScalar P => b = a), _) = _
    erw [Finset.sum_filter, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
  have heqread (u : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
      extendedPolynomialRead P (directPointExtendedQuestionEquiv P u) =
        fun g => extendedDirectScalarEquiv P (evalDirectPolyTupleAt u g (0 : Fin 1)) := by
    funext g; unfold extendedPolynomialRead; rw [Equiv.symm_apply_apply]
  have hAq : consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
      (fun x c => heteroKron ((RA.postprocess (extendedPolynomialRead P x)).effect c) 1)
      (fun x c => heteroKron 1 ((points.extendedQ .bob x.1.1 x.1.2 x.2.1 x.2.2).effect c))
      (pairState S) ≤ eta := by
    rw [← consistencyDefect_uniform_question_equiv (directPointExtendedQuestionEquiv P)]
    refine le_trans (le_of_eq (consistencyDefect_congr _ _ _ _ _ (pairState S) (fun u c => ?_) (fun u c => ?_))) hAsc
    · apply congrArg (heteroKron · 1)
      rw [heqread u]
      exact (SandwichProduct.postprocess_postprocess_effect RA (evalDirectPolyTupleAt u)
        (fun values => extendedDirectScalarEquiv P (values (0 : Fin 1))) c).symm
    · exact congrArg (heteroKron 1 ·) (congrArg (fun M => M.effect c) (hpsm .bob u).symm)
  have hBq : consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
      (fun x c => heteroKron ((points.extendedQ .alice x.1.1 x.1.2 x.2.1 x.2.2).effect c) 1)
      (fun x c => heteroKron 1 ((RB.postprocess (extendedPolynomialRead P x)).effect c))
      (pairState S) ≤ eta := by
    rw [← consistencyDefect_uniform_question_equiv (directPointExtendedQuestionEquiv P)]
    refine le_trans (le_of_eq (consistencyDefect_congr _ _ _ _ _ (pairState S) (fun u c => ?_) (fun u c => ?_))) hBsc
    · exact congrArg (heteroKron · 1) (congrArg (fun M => M.effect c) (hpsm .alice u).symm)
    · apply congrArg (heteroKron 1 ·)
      rw [heqread u]
      exact (SandwichProduct.postprocess_postprocess_effect RB (evalDirectPolyTupleAt u)
        (fun values => extendedDirectScalarEquiv P (values (0 : Fin 1))) c).symm
  have hApl : consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
      (fun x a => S.place .AA' ((RA.postprocess (extendedPolynomialRead P x)).effect a))
      (fun x a => S.place .BA'' ((points.extendedQ .bob x.1.1 x.1.2 x.2.1 x.2.2).effect a)) S.psiHat ≤ eta := by
    refine le_trans (le_of_eq ?_) hAq
    unfold consistencyDefect
    refine avgOver_congr _ _ _ fun x => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rfl
    · simp only [consistency_term_eq_stateQForm, placed_product_stateQForm_eq]
      exact (stateQForm_pairState_eq_AA'_BA'' S _ _
        (Matrix.nonneg_iff_posSemidef.mp ((_ : Measurement _ _).pos a)).isHermitian
        (Matrix.nonneg_iff_posSemidef.mp ((_ : Measurement _ _).pos b)).isHermitian).symm
  have hBpl : consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
      (fun x a => S.place .BB' ((RB.postprocess (extendedPolynomialRead P x)).effect a))
      (fun x a => S.place .AB'' ((points.extendedQ .alice x.1.1 x.1.2 x.2.1 x.2.2).effect a)) S.psiHat ≤ eta := by
    refine le_trans (le_of_eq ?_) hBq
    unfold consistencyDefect
    refine avgOver_congr _ _ _ fun x => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : a = b
    · simp [hab]
    · simp only [hab, Ne.symm hab, if_false, consistency_term_eq_stateQForm, placed_product_stateQForm_eq]
      rw [S.place_comm .BB' .AB'' trivial]
      exact (stateQForm_pairState_eq_AB''_BB' S _ _
        (Matrix.nonneg_iff_posSemidef.mp ((_ : Measurement _ _).pos a)).isHermitian
        (Matrix.nonneg_iff_posSemidef.mp ((_ : Measurement _ _).pos b)).isHermitian).symm
  have hord (p1 p2 : Placement) (hop : p1.IsOpposite p2)
      (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
      (hR : Measurement.IsProjective R)
      (hpt : consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
        (fun x a => S.place p1 ((R.postprocess (extendedPolynomialRead P x)).effect a))
        (fun x a => S.place p2 ((points.extendedQ p2.side x.1.1 x.1.2 x.2.1 x.2.2).effect a)) S.psiHat ≤ eta)
      (rev : Bool) :
      extendedPolynomialOrderedError S p1 p2 R rev ≤ 4 * eta + 8 * δQ := by
    have h := points.ordered_dist_le p1 p2 hop R hR (extendedPolynomialRead P) eta hpt
    cases rev
    · simpa only [extendedPolynomialOrderedError, Bool.false_eq_true, if_false, mul_sub, mul_one, opFamilyDistSq] using h.1
    · simpa only [extendedPolynomialOrderedError, if_true, mul_sub, mul_one, opFamilyDistSq] using h.2
  exact ⟨RA, RB, hRA, hRB, fun rev =>
    ⟨hord .AA' .BA'' trivial RA hRA hApl rev, hord .BB' .AB'' trivial RB hRB hBpl rev⟩⟩

/-! ## Section 5: Scalar polynomial separation, completion, and pair consistency -/

theorem sumRingEquiv_degrees {F : Type*} [CommSemiring F] {k n d : ℕ}
    (p : MvPolynomial (Fin k ⊕ Fin n) F) (h : ∀ e ∈ p.support, ∀ i, e i ≤ d) :
    (∀ a, ((MvPolynomial.sumRingEquiv F (Fin k) (Fin n) p).coeff a).totalDegree ≤ n * d) ∧
      (MvPolynomial.sumRingEquiv F (Fin k) (Fin n) p).totalDegree ≤ k * d := by
  have ht {m : ℕ} {R : Type} [CommSemiring R] (q : MvPolynomial (Fin m) R)
      (hq : ∀ e ∈ q.support, ∀ i, e i ≤ d) : q.totalDegree ≤ m * d := by
    rw [MvPolynomial.totalDegree, Finset.sup_le_iff]; intro e he
    rw [Finsupp.sum_fintype _ _ (by simp)]
    exact (Finset.sum_le_sum fun i _ => hq e he i).trans_eq (by simp)
  have hcc (q : MvPolynomial (Fin k ⊕ Fin n) F) (a : Fin k →₀ ℕ) (b : Fin n →₀ ℕ) :
      ((MvPolynomial.sumRingEquiv F (Fin k) (Fin n) q).coeff a).coeff b =
        q.coeff (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (a, b)) := by
    simp [MvPolynomial.sumRingEquiv, AddMonoidAlgebra.curryRingEquiv, AddMonoidAlgebra.curryAddEquiv]
  have hc (a : Fin k →₀ ℕ) (b : Fin n →₀ ℕ)
      (hb : b ∈ ((MvPolynomial.sumRingEquiv F (Fin k) (Fin n) p).coeff a).support) :
      Finsupp.sumFinsuppAddEquivProdFinsupp.symm (a, b) ∈ p.support := by
    simpa only [MvPolynomial.mem_support_iff, hcc] using hb
  refine ⟨fun a => ?_, ?_⟩
  · rw [MvPolynomial.totalDegree, Finset.sup_le_iff]; intro b hb
    rw [Finsupp.sum_fintype _ _ (by simp)]
    exact (Finset.sum_le_sum fun i _ => by simpa using h _ (hc a b hb) (Sum.inr i)).trans_eq (by simp)
  · rw [MvPolynomial.totalDegree, Finset.sup_le_iff]; intro a ha
    obtain ⟨b, hb⟩ := MvPolynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp ha)
    rw [Finsupp.sum_fintype _ _ (by simp)]
    exact (Finset.sum_le_sum fun i _ => by simpa using h _ (hc a b hb) (Sum.inl i)).trans_eq (by simp)

def baseCoordinateEquiv (m : ℕ) : Fin (2 * m) ≃ Fin m ⊕ Fin m :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

def scalarBaseCoordinateEquiv (m : ℕ) : Fin (2 * m + 2) ≃ Fin 2 ⊕ Fin (2 * m) :=
  (finCombineEquiv m).trans
    ((Equiv.sumCongr (baseCoordinateEquiv m).symm (Equiv.refl _)).trans (Equiv.sumComm _ _))

def scalarPolynomial (P : AdmissibleParams) (g : DirectPolyTuple P.extendedDirectLd) :
    MvPolynomial (Fin 2) (MvPolynomial (Fin (2 * P.m)) (PauliScalar P)) :=
  MvPolynomial.sumRingEquiv _ _ _
    (MvPolynomial.rename (scalarBaseCoordinateEquiv P.m)
      (MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1))

theorem scalarPolynomial_renamed_exponents (P : AdmissibleParams)
    (g : DirectPolyTuple P.extendedDirectLd) :
    ∀ e ∈ (MvPolynomial.rename (scalarBaseCoordinateEquiv P.m)
      (MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1)).support,
      ∀ i, e i ≤ P.d := by
  intro e he i
  obtain ⟨v, hv, hvp⟩ := MvPolynomial.coeff_rename_ne_zero _ _ _ (MvPolynomial.mem_support_iff.mp he)
  have hmem := MvPolynomial.support_map_subset _ _ (MvPolynomial.mem_support_iff.mpr hvp)
  have hvbound := (MvPolynomial.le_degreeOf_of_mem_support _ hmem).trans
    (Preliminaries.degreeOf_le_of_mem_polyFunc (g (0 : Fin 1)).2 ((scalarBaseCoordinateEquiv P.m).symm i))
  change v ((scalarBaseCoordinateEquiv P.m).symm i) ≤ P.d at hvbound
  subst e; simpa only [Finsupp.mapDomain_equiv_apply] using hvbound

def blockCoefficientPolynomial (P : AdmissibleParams)
    (g : DirectPolyTuple P.extendedDirectLd) (a : Fin 2 →₀ ℕ) (reverse : Bool) :
    MvPolynomial (Fin P.m) (MvPolynomial (Fin P.m) (PauliScalar P)) :=
  MvPolynomial.sumRingEquiv _ _ _ (MvPolynomial.rename
    ((baseCoordinateEquiv P.m).trans (if reverse then Equiv.sumComm _ _ else Equiv.refl _))
    ((scalarPolynomial P g).coeff a))

theorem blockCoefficientPolynomial_renamed_exponents (P : AdmissibleParams)
    (g : DirectPolyTuple P.extendedDirectLd) (a : Fin 2 →₀ ℕ) (reverse : Bool) :
    ∀ e ∈ (MvPolynomial.rename ((baseCoordinateEquiv P.m).trans
      (if reverse then Equiv.sumComm _ _ else Equiv.refl _))
        ((scalarPolynomial P g).coeff a)).support, ∀ i, e i ≤ P.d := by
  intro e he i
  let eqv := (baseCoordinateEquiv P.m).trans (if reverse then Equiv.sumComm _ _ else Equiv.refl _)
  obtain ⟨v, hv, hvp⟩ := MvPolynomial.coeff_rename_ne_zero _ _ _ (MvPolynomial.mem_support_iff.mp he)
  have hcoeff : (MvPolynomial.rename (scalarBaseCoordinateEquiv P.m)
      (MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1)).coeff
      (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (a, v)) ≠ 0 := by
    simpa [scalarPolynomial, MvPolynomial.sumRingEquiv,
      AddMonoidAlgebra.curryRingEquiv, AddMonoidAlgebra.curryAddEquiv] using hvp
  have hb := scalarPolynomial_renamed_exponents P g _
    (MvPolynomial.mem_support_iff.mpr hcoeff) (.inr (eqv.symm i))
  change v (eqv.symm i) ≤ P.d at hb
  subst e; simpa only [Finsupp.mapDomain_equiv_apply] using hb

theorem eval_sumRingEquiv {F A B : Type*} [CommSemiring F]
    (p : MvPolynomial (A ⊕ B) F) (u : B → F) (v : A → F) :
    MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u)
      (MvPolynomial.sumRingEquiv F A B p)) = MvPolynomial.eval (Sum.elim v u) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => cases i <;> simp [hp]

def scalarBaseQuestionEquiv (P : AdmissibleParams) :
    ((Fin (2 * P.m) → PauliScalar P) × (Fin 2 → PauliScalar P)) ≃ ExtendedPointQuestion P :=
  (((baseCoordinateEquiv P.m).piCongrLeft fun _ => PauliScalar P).trans
    (Equiv.sumPiEquivProdPi fun _ : Fin P.m ⊕ Fin P.m => PauliScalar P)).prodCongr
      (finTwoArrowEquiv (PauliScalar P))

theorem scalarPolynomial_eval (P : AdmissibleParams)
    (g : DirectPolyTuple P.extendedDirectLd)
    (u : Fin (2 * P.m) → PauliScalar P) (v : Fin 2 → PauliScalar P) :
    MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) (scalarPolynomial P g)) =
      extendedPolynomialRead P (scalarBaseQuestionEquiv P (u, v)) g := by
  have hsdir : (directPointExtendedQuestionEquiv P).symm (scalarBaseQuestionEquiv P (u, v)) =
      fun i => (extendedDirectScalarEquiv P).symm (Sum.elim v u (scalarBaseCoordinateEquiv P.m i)) := by
    apply (directPointExtendedQuestionEquiv P).injective
    rw [Equiv.apply_symm_apply, directPointExtendedQuestionEquiv_apply]
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
    · funext i; simp [scalarBaseQuestionEquiv, scalarBaseCoordinateEquiv, projX, embX, directPointToPauli, Equiv.piCongrLeft_apply]
    · funext i; simp [scalarBaseQuestionEquiv, scalarBaseCoordinateEquiv, projZ, embZ, directPointToPauli, Equiv.piCongrLeft_apply]
    · simp [scalarBaseQuestionEquiv, scalarBaseCoordinateEquiv, alphaVar, directPointToPauli]
    · simp [scalarBaseQuestionEquiv, scalarBaseCoordinateEquiv, betaVar, directPointToPauli]
  rw [scalarPolynomial, eval_sumRingEquiv, MvPolynomial.eval_rename, MvPolynomial.eval_map]
  unfold extendedPolynomialRead evalDirectPolyTupleAt
  rw [hsdir]
  have h := (MvPolynomial.eval₂_comp (extendedDirectScalarEquiv P).toRingHom
    (fun i => (extendedDirectScalarEquiv P).symm (Sum.elim v u (scalarBaseCoordinateEquiv P.m i)))
    (g (0 : Fin 1)).1).symm
  change MvPolynomial.eval₂ (extendedDirectScalarEquiv P).toRingHom
    (fun i => extendedDirectScalarEquiv P ((extendedDirectScalarEquiv P).symm
      (Sum.elim v u (scalarBaseCoordinateEquiv P.m i)))) (g (0 : Fin 1)).1 = _ at h
  simp only [RingEquiv.apply_symm_apply] at h
  exact h

def fiberQuestionEquiv (P : AdmissibleParams) (reverse : Bool) :
    (((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) × (Fin 2 → PauliScalar P)) ≃
      ExtendedPointQuestion P :=
  (if reverse then Equiv.refl _ else Equiv.prodComm _ _).prodCongr
    ((finTwoArrowEquiv (PauliScalar P)).trans (if reverse then Equiv.prodComm _ _ else Equiv.refl _))

theorem scalarPolynomial_linear_read_fiber (P : AdmissibleParams)
    (g : DirectPolyTuple P.extendedDirectLd)
    (hg : ∃ r t : MvPolynomial (Fin (2 * P.m)) (PauliScalar P),
      scalarPolynomial P g = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1)
    (reverse : Bool) (x z : Fin P.m → PauliScalar P) (v : Fin 2 → PauliScalar P) :
    extendedPolynomialRead P (fiberQuestionEquiv P reverse ((z, x), v)) g =
      v 0 * MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z)
        (blockCoefficientPolynomial P g (Finsupp.single (if reverse then 1 else 0) 1) reverse)) +
      v 1 * MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z)
        (blockCoefficientPolynomial P g (Finsupp.single (if reverse then 0 else 1) 1) reverse)) := by
  obtain ⟨r, t, hg⟩ := hg
  let u : Fin (2 * P.m) → PauliScalar P := fun i => Sum.elim x z
    (((baseCoordinateEquiv P.m).trans (if reverse then Equiv.sumComm _ _ else Equiv.refl _)) i)
  let v' : Fin 2 → PauliScalar P := if reverse then ![v 1, v 0] else v
  have heq : scalarBaseQuestionEquiv P (u, v') = fiberQuestionEquiv P reverse ((z, x), v) := by
    cases reverse <;> simp [scalarBaseQuestionEquiv, fiberQuestionEquiv, u, v', Equiv.piCongrLeft_apply]
  have hbeval (a : Fin 2 →₀ ℕ) : MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z)
      (blockCoefficientPolynomial P g a reverse)) = MvPolynomial.eval u ((scalarPolynomial P g).coeff a) := by
    rw [blockCoefficientPolynomial, eval_sumRingEquiv, MvPolynomial.eval_rename]; rfl
  rw [← heq, ← scalarPolynomial_eval, hg, hbeval, hbeval, hg]
  have h01 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := fun h => by
    simpa using congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  simp only [map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.eval_C, MvPolynomial.eval_X]
  cases reverse <;>
    simp only [Bool.false_eq_true, MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X,
      h01, Ne.symm h01, ↓reduceIte, mul_one, mul_zero, zero_add, add_zero]
  · change MvPolynomial.eval u r * v 0 + MvPolynomial.eval u t * v 1 =
      v 0 * MvPolynomial.eval u r + v 1 * MvPolynomial.eval u t; ring
  · change MvPolynomial.eval u r * v 1 + MvPolynomial.eval u t * v 0 =
      v 0 * MvPolynomial.eval u t + v 1 * MvPolynomial.eval u r; ring

theorem exists_polyPair_of_scalar_separated (P : AdmissibleParams)
    (g : DirectPolyTuple P.extendedDirectLd)
    (hlin : ∃ r t : MvPolynomial (Fin (2 * P.m)) (PauliScalar P),
      scalarPolynomial P g = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1)
    (hX : ∃ r, blockCoefficientPolynomial P g (Finsupp.single 0 1) true = MvPolynomial.C r)
    (hZ : ∃ r, blockCoefficientPolynomial P g (Finsupp.single 1 1) false = MvPolynomial.C r) :
    ∃ pair : PolyPair P,
      MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1 =
        combinePoly pair.1.1 pair.2.1 := by
  have hsre_inr {F A B : Type} [CommSemiring F] (p : MvPolynomial B F) :
      MvPolynomial.sumRingEquiv F A B (MvPolynomial.rename Sum.inr p) = MvPolynomial.C p := by
    induction p using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  have hbconst (a : Fin 2 →₀ ℕ) (rev : Bool)
      (h : ∃ r, blockCoefficientPolynomial P g a rev = MvPolynomial.C r) :
      ∃ r : Poly P, (scalarPolynomial P g).coeff a = MvPolynomial.rename
        (fun i => ((baseCoordinateEquiv P.m).trans (if rev then Equiv.sumComm _ _ else Equiv.refl _)).symm (.inr i)) r.1 := by
    obtain ⟨r, hr⟩ := h
    have hmem : r ∈ Preliminaries.polyFunc P.m (PauliScalar P) P.d := by
      apply mem_polyFunc_of_degreeOf_le; intro i
      apply MvPolynomial.degreeOf_le_iff.mpr; intro b hb
      have hc : ((blockCoefficientPolynomial P g a rev).coeff 0).coeff b ≠ 0 := by
        simpa only [hr, MvPolynomial.coeff_C, ↓reduceIte] using MvPolynomial.mem_support_iff.mp hb
      have hsup : Finsupp.sumFinsuppAddEquivProdFinsupp.symm (0, b) ∈
          (MvPolynomial.rename ((baseCoordinateEquiv P.m).trans (if rev then Equiv.sumComm _ _ else Equiv.refl _))
            ((scalarPolynomial P g).coeff a)).support := by
        simpa [blockCoefficientPolynomial, MvPolynomial.sumRingEquiv,
          AddMonoidAlgebra.curryRingEquiv, AddMonoidAlgebra.curryAddEquiv] using hc
      simpa using blockCoefficientPolynomial_renamed_exponents P g a rev _ hsup (.inr i)
    refine ⟨⟨r, hmem⟩, ?_⟩
    let eqv := (baseCoordinateEquiv P.m).trans (if rev then Equiv.sumComm _ _ else Equiv.refl _)
    apply MvPolynomial.rename_injective eqv eqv.injective
    apply (MvPolynomial.sumRingEquiv (PauliScalar P) (Fin P.m) (Fin P.m)).injective
    change blockCoefficientPolynomial P g a rev = _
    rw [hr, MvPolynomial.rename_rename]
    have heq : eqv ∘ (fun i => eqv.symm (.inr i)) = Sum.inr := funext fun i => eqv.apply_symm_apply _
    change MvPolynomial.C r = MvPolynomial.sumRingEquiv _ _ _ (MvPolynomial.rename (eqv ∘ (fun i => eqv.symm (.inr i))) r)
    rw [heq, hsre_inr]
  obtain ⟨f, hf⟩ := hbconst _ true hX
  obtain ⟨h, hh⟩ := hbconst _ false hZ
  refine ⟨(f, h), ?_⟩
  apply MvPolynomial.rename_injective (scalarBaseCoordinateEquiv P.m) (scalarBaseCoordinateEquiv P.m).injective
  apply (MvPolynomial.sumRingEquiv (PauliScalar P) (Fin 2) (Fin (2 * P.m))).injective
  change scalarPolynomial P g = _
  have hexp : MvPolynomial.sumRingEquiv _ _ _
      (MvPolynomial.rename (scalarBaseCoordinateEquiv P.m) (combinePoly f.1 h.1)) =
    MvPolynomial.C (MvPolynomial.rename (fun i => (baseCoordinateEquiv P.m).symm (.inl i)) f.1) * MvPolynomial.X (0 : Fin 2) +
    MvPolynomial.C (MvPolynomial.rename (fun i => (baseCoordinateEquiv P.m).symm (.inr i)) h.1) * MvPolynomial.X 1 := by
    have hXe : scalarBaseCoordinateEquiv P.m ∘ embX P.m = Sum.inr ∘ (fun i => (baseCoordinateEquiv P.m).symm (.inl i)) := by
      funext i; simp [scalarBaseCoordinateEquiv, embX]
    have hZe : scalarBaseCoordinateEquiv P.m ∘ embZ P.m = Sum.inr ∘ (fun i => (baseCoordinateEquiv P.m).symm (.inr i)) := by
      funext i; simp [scalarBaseCoordinateEquiv, embZ]
    simp only [combinePoly, map_add, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_rename, hXe, hZe]
    rw [← MvPolynomial.rename_rename, ← MvPolynomial.rename_rename]
    simp only [hsre_inr]
    have ha : scalarBaseCoordinateEquiv P.m (alphaVar P.m) = .inl 0 := by simp [scalarBaseCoordinateEquiv, alphaVar]
    have hb : scalarBaseCoordinateEquiv P.m (betaVar P.m) = .inl 1 := by simp [scalarBaseCoordinateEquiv, betaVar]
    rw [ha, hb, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inl]; ring
  rw [hexp]
  obtain ⟨r, t, hlin⟩ := hlin
  have h01 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := fun hc => by
    simpa using congrArg (fun e : Fin 2 →₀ ℕ => e 0) hc
  simp only [hlin, MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X,
    h01, Ne.symm h01, ↓reduceIte, mul_one, mul_zero, add_zero, zero_add] at hf hh
  change r = MvPolynomial.rename (fun i => (baseCoordinateEquiv P.m).symm (.inl i)) f.1 at hf
  change t = MvPolynomial.rename (fun i => (baseCoordinateEquiv P.m).symm (.inr i)) h.1 at hh
  rw [hlin, hf, hh]

theorem placed_residual {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : Op (S.ExpandedLocalSpace p1.side)) (T : Op (S.ExpandedLocalSpace p2.side)) :
    applyOperatorToState (S.place p1 R) S.psiHat -
      applyOperatorToState (S.place p2 T) (applyOperatorToState (S.place p1 R) S.psiHat) =
      applyOperatorToState (S.place p1 R * (1 - S.place p2 T)) S.psiHat := by
  rw [← applyOperatorToState_mul, ← S.place_comm p1 p2 hopposite R T, mul_sub, mul_one]
  simp only [applyOperatorToState, map_sub, LinearMap.sub_apply]

theorem fiber_ordered_error_eq {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (reverse : Bool) :
    let ψ := fun g => applyOperatorToState (S.place p1 (R.effect g)) S.psiHat
    let X := fun x : Fin P.m → PauliScalar P => S.placedMeasurement p2
      (S.pointMeasExp p2.side (if reverse then .Z else .X) x)
    let Z := fun z : Fin P.m → PauliScalar P => S.placedMeasurement p2
      (S.pointMeasExp p2.side (if reverse then .X else .Z) z)
    avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun z =>
      avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun x =>
        avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v =>
          ∑ g, ‖ψ g - applyOperatorToState (orderedIndicator (X x) (Z z) (v 0) (v 1)
            (extendedPolynomialRead P (fiberQuestionEquiv P reverse ((z, x), v)) g)) (ψ g)‖ ^ 2))) =
      extendedPolynomialOrderedError S p1 p2 R reverse := by
  classical
  dsimp only
  let ψ := fun g => applyOperatorToState (S.place p1 (R.effect g)) S.psiHat
  let X := fun x : Fin P.m → PauliScalar P => S.placedMeasurement p2
    (S.pointMeasExp p2.side (if reverse then .Z else .X) x)
  let Z := fun z : Fin P.m → PauliScalar P => S.placedMeasurement p2
    (S.pointMeasExp p2.side (if reverse then .X else .Z) z)
  let A := fun (z x : Fin P.m → PauliScalar P) (v : Fin 2 → PauliScalar P) g =>
    applyOperatorToState (orderedIndicator (X x) (Z z) (v 0) (v 1)
      (extendedPolynomialRead P (fiberQuestionEquiv P reverse ((z, x), v)) g)) (ψ g)
  change avgOver _ (fun z => avgOver _ (fun x => avgOver _ (fun v => ∑ g, ‖ψ g - A z x v g‖ ^ 2))) = _
  rw [← avgOver_uniform_prod (fun z x =>
      avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v => ∑ g, ‖ψ g - A z x v g‖ ^ 2)),
    ← avgOver_uniform_prod (fun zx : (Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P) =>
      fun v => ∑ g, ‖ψ g - A zx.1 zx.2 v g‖ ^ 2)]
  unfold extendedPolynomialOrderedError
  rw [avgOver_uniform_equiv (fiberQuestionEquiv P reverse).symm]
  refine avgOver_congr _ _ _ fun ⟨⟨z, x⟩, v⟩ => Finset.sum_congr rfl fun g _ => ?_
  have hpind (a : PauliScalar P) : orderedIndicator (X x) (Z z) (v 0) (v 1) a =
      let y := fiberQuestionEquiv P reverse ((z, x), v)
      S.place p2 (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
          y.2.1 * ab.1 + y.2.2 * ab.2 = a),
        if reverse then (S.pointMeasExp p2.side .Z y.1.2).effect ab.2 * (S.pointMeasExp p2.side .X y.1.1).effect ab.1
        else (S.pointMeasExp p2.side .X y.1.1).effect ab.1 * (S.pointMeasExp p2.side .Z y.1.2).effect ab.2) := by
    dsimp only [X, Z]
    rw [S.place_finsetSum, Finset.sum_filter]
    simp only [orderedIndicator, ProjectiveSetting.placedMeasurement_effect]
    cases reverse
    · simp [fiberQuestionEquiv, ProjectiveSetting.place_mul]
    · exact Fintype.sum_equiv (Equiv.prodComm (PauliScalar P) (PauliScalar P)) _ _ fun ab => by
        simp [fiberQuestionEquiv, add_comm, ProjectiveSetting.place_mul]
  dsimp only [A]
  rw [hpind, placed_residual S p1 p2 hopposite]
  rfl

def separatedPolynomialMass {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p.side)) : ℝ := by
  classical
  exact ∑ g ∈ Finset.univ.filter (fun g => ¬ ∃ pair : PolyPair P,
      MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1 =
        combinePoly pair.1.1 pair.2.1),
    ‖applyOperatorToState (S.place p (R.effect g)) S.psiHat‖ ^ 2

theorem separatedPolynomialMass_le_ordered_errors {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) :
    separatedPolynomialMass S p1 R ≤
      4 * extendedPolynomialOrderedError S p1 p2 R false +
      2 * extendedPolynomialOrderedError S p1 p2 R true +
      (((12 * P.m * P.d + 4 * P.d + 10 : ℕ) : ℝ) / P.q) := by
  classical
  let ψ := fun g => applyOperatorToState (S.place p1 (R.effect g)) S.psiHat
  have hmass : ∑ g, ‖ψ g‖ ^ 2 = 1 := by
    simpa only [ψ, ProjectiveSetting.placedMeasurement_effect, S.psiHat_norm, one_pow] using
      sum_projective_state_norm_sq (S.placedMeasurement p1 R) (S.placedMeasurement_isProjective p1 R hR) S.psiHat
  have hcard : Fintype.card (PauliScalar P) = P.q := @FieldModel.card P.q P.model.toFieldModel
  -- 1. Scalar nonlinear mass bound
  let sN := Finset.univ.filter (fun g => ¬ ∃ r t : MvPolynomial (Fin (2 * P.m)) (PauliScalar P),
      scalarPolynomial P g = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1)
  have hN : ∑ g ∈ sN, ‖ψ g‖ ^ 2 ≤ 2 * extendedPolynomialOrderedError S p1 p2 R false +
      2 * (((2 * P.m + 2) * P.d + 1 : ℕ) : ℝ) / P.q := by
    let Xu := fun u : Fin (2 * P.m) → PauliScalar P => S.placedMeasurement p2
      (S.pointMeasExp p2.side .X (fun i => u ((baseCoordinateEquiv P.m).symm (.inl i))))
    let Zu := fun u : Fin (2 * P.m) → PauliScalar P => S.placedMeasurement p2
      (S.pointMeasExp p2.side .Z (fun i => u ((baseCoordinateEquiv P.m).symm (.inr i))))
    have hnl := nonlinear_mass_le_ordered_error sN (scalarPolynomial P)
      (fun g hg => (Finset.mem_filter.mp hg).2) Xu Zu
      (fun _ => S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
      (fun _ => S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _)) ψ
    have hdeg : (∑ g ∈ sN, (((scalarPolynomial P g).support.sup fun e =>
          ((scalarPolynomial P g).coeff e).totalDegree) + max 1 (scalarPolynomial P g).totalDegree + 1 : ℕ) /
          (Fintype.card (PauliScalar P) : ℝ) * ‖ψ g‖ ^ 2) ≤
        (((2 * P.m + 2) * P.d + 1 : ℕ) : ℝ) / P.q := by
      rw [hcard]
      calc _ ≤ ∑ g ∈ sN, ((((2 * P.m + 2) * P.d + 1 : ℕ) : ℝ) / P.q) * ‖ψ g‖ ^ 2 :=
            Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_right (by
                have hd := sumRingEquiv_degrees _ (scalarPolynomial_renamed_exponents P g)
                have hc : ((scalarPolynomial P g).support.sup fun e => ((scalarPolynomial P g).coeff e).totalDegree) ≤ 2 * P.m * P.d :=
                  Finset.sup_le fun e _ => hd.1 e
                have ho : max 1 (scalarPolynomial P g).totalDegree ≤ 2 * P.d := max_le (by have := P.hd; omega) hd.2
                exact_mod_cast (Nat.add_le_add_right (Nat.add_le_add hc ho) 1).trans_eq (by ring))
                (Nat.cast_nonneg _)) (sq_nonneg _)
        _ ≤ ∑ g, ((((2 * P.m + 2) * P.d + 1 : ℕ) : ℝ) / P.q) * ‖ψ g‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
        _ = _ := by rw [← Finset.mul_sum, hmass, mul_one]
    let fn := fun (u : Fin (2 * P.m) → PauliScalar P) (v : Fin 2 → PauliScalar P) g =>
      ‖ψ g - applyOperatorToState (orderedIndicator (Xu u) (Zu u) (v 0) (v 1)
        (MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) (scalarPolynomial P g)))) (ψ g)‖ ^ 2
    have hfullN : avgOver (uniformDistribution (Fin (2 * P.m) → PauliScalar P)) (fun u =>
        avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v => ∑ g, fn u v g)) =
        extendedPolynomialOrderedError S p1 p2 R false := by
      rw [← avgOver_uniform_prod (fun u v => ∑ g, fn u v g)]
      unfold extendedPolynomialOrderedError
      rw [avgOver_uniform_equiv (scalarBaseQuestionEquiv P).symm]
      refine avgOver_congr _ _ _ fun ⟨u, v⟩ => Finset.sum_congr rfl fun g _ => ?_
      dsimp only [fn]
      rw [scalarPolynomial_eval]
      have hXZ : orderedIndicator (Xu u) (Zu u) (v 0) (v 1)
          (extendedPolynomialRead P (scalarBaseQuestionEquiv P (u, v)) g) =
        S.place p2 (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
            (scalarBaseQuestionEquiv P (u, v)).2.1 * ab.1 + (scalarBaseQuestionEquiv P (u, v)).2.2 * ab.2 =
              extendedPolynomialRead P (scalarBaseQuestionEquiv P (u, v)) g),
          (S.pointMeasExp p2.side .X (scalarBaseQuestionEquiv P (u, v)).1.1).effect ab.1 *
            (S.pointMeasExp p2.side .Z (scalarBaseQuestionEquiv P (u, v)).1.2).effect ab.2) := by
        rw [S.place_finsetSum, Finset.sum_filter]
        simp [Xu, Zu, scalarBaseQuestionEquiv, Equiv.piCongrLeft_apply, orderedIndicator,
          ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul]
      rw [hXZ, placed_residual S p1 p2 hopposite]; rfl
    have herrN : avgOver (uniformDistribution (Fin (2 * P.m) → PauliScalar P)) (fun u =>
        avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v => ∑ g ∈ sN, fn u v g)) ≤
        extendedPolynomialOrderedError S p1 p2 R false := by
      rw [← hfullN]
      exact avgOver_mono _ _ _ fun u => avgOver_mono _ _ _ fun v =>
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    simpa only [mul_div_assoc] using hnl.trans (add_le_add
      (mul_le_mul_of_nonneg_left herrN (by norm_num)) (mul_le_mul_of_nonneg_left hdeg (by norm_num)))
  -- 2. Wrong-variable mass bound for reverse = false and true
  let sW (rev : Bool) := Finset.univ.filter (fun g =>
    (∃ r t : MvPolynomial (Fin (2 * P.m)) (PauliScalar P),
      scalarPolynomial P g = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1) ∧
    ¬ ∃ r, blockCoefficientPolynomial P g (Finsupp.single (if rev then 0 else 1) 1) rev = MvPolynomial.C r)
  have hW (rev : Bool) : ∑ g ∈ sW rev, ‖ψ g‖ ^ 2 ≤
      2 * extendedPolynomialOrderedError S p1 p2 R rev +
        2 * (((P.m * P.d + P.m * P.d + 2 : ℕ) : ℝ) / P.q) := by
    let X := fun x : Fin P.m → PauliScalar P => S.placedMeasurement p2
      (S.pointMeasExp p2.side (if rev then .Z else .X) x)
    let Z := fun z : Fin P.m → PauliScalar P => S.placedMeasurement p2
      (S.pointMeasExp p2.side (if rev then .X else .Z) z)
    let A := fun (z x : Fin P.m → PauliScalar P) (v : Fin 2 → PauliScalar P) g =>
      applyOperatorToState (orderedIndicator (X x) (Z z) (v 0) (v 1)
        (extendedPolynomialRead P (fiberQuestionEquiv P rev ((z, x), v)) g)) (ψ g)
    let B : ℝ := ((P.m * P.d + P.m * P.d + 2 : ℕ) : ℝ) / P.q
    have hnsum : avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun z =>
        avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun x =>
          avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v => ∑ g ∈ sW rev, ‖A z x v g‖ ^ 2))) ≤ B := by
      simp_rw [avgOver_finset_sum]
      calc _ ≤ ∑ g ∈ sW rev, B * ‖ψ g‖ ^ 2 := Finset.sum_le_sum fun g hg => by
            obtain ⟨hlin, hnon⟩ := (Finset.mem_filter.mp hg).2
            have hd := sumRingEquiv_degrees _ (blockCoefficientPolynomial_renamed_exponents P g
              (Finsupp.single (if rev then 0 else 1) 1) rev)
            have h := avg_orderedIndicator_norm_sq_le_of_nonconstant
              (blockCoefficientPolynomial P g (Finsupp.single (if rev then 0 else 1) 1) rev)
              hnon hd.1 hd.2
              (fun x z => MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z)
                (blockCoefficientPolynomial P g (Finsupp.single (if rev then 1 else 0) 1) rev))) X Z
              (fun _ => S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
              (fun _ => S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _)) (ψ g)
            simpa only [A, scalarPolynomial_linear_read_fiber P g hlin, hcard, B] using h
        _ ≤ ∑ g, B * ‖ψ g‖ ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => by dsimp [B]; positivity)
        _ = B := by rw [← Finset.mul_sum, hmass, mul_one]
    have herr : avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun z =>
        avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun x =>
          avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v => ∑ g ∈ sW rev, ‖ψ g - A z x v g‖ ^ 2))) ≤
        extendedPolynomialOrderedError S p1 p2 R rev := by
      rw [← fiber_ordered_error_eq S p1 p2 hopposite R rev]
      exact avgOver_mono _ _ _ fun z => avgOver_mono _ _ _ fun x => avgOver_mono _ _ _ fun v =>
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    have h := avgOver_mono (uniformDistribution (Fin P.m → PauliScalar P)) _ _ fun z =>
      avgOver_mono (uniformDistribution (Fin P.m → PauliScalar P)) _ _ fun x =>
        avgOver_mono (uniformDistribution (Fin 2 → PauliScalar P)) _ _ fun v =>
          sum_mass_le_residual_add_image (sW rev) ψ (A z x v)
    simp only [avgOver_uniform_const, avgOver_add, avgOver_const_mul] at h
    linarith
  -- 3. Union bound over the three excluded classes
  have hunion : separatedPolynomialMass S p1 R ≤
      ∑ g ∈ sN, ‖ψ g‖ ^ 2 + ∑ g ∈ sW false, ‖ψ g‖ ^ 2 + ∑ g ∈ sW true, ‖ψ g‖ ^ 2 := by
    simp only [separatedPolynomialMass, sN, sW, Finset.sum_filter, Bool.false_eq_true, ↓reduceIte]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun g _ => ?_
    by_cases hlin : ∃ r t : MvPolynomial (Fin (2 * P.m)) (PauliScalar P),
        scalarPolynomial P g = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1
    · by_cases hX : ∃ r, blockCoefficientPolynomial P g (Finsupp.single 0 1) true = MvPolynomial.C r
      · by_cases hZ : ∃ r, blockCoefficientPolynomial P g (Finsupp.single 1 1) false = MvPolynomial.C r
        · have him := exists_polyPair_of_scalar_separated P g hlin hX hZ
          simp only [hlin, hX, hZ, not_true_eq_false, and_false, ↓reduceIte, zero_add]
          split_ifs with hout; exact le_rfl; exact (hout him).elim
        · simp only [hlin, hX, hZ, not_false_eq_true, not_true_eq_false, and_true, and_false, ↓reduceIte, zero_add, add_zero]
          split_ifs <;> nlinarith [sq_nonneg ‖ψ g‖]
      · simp only [hlin, hX, not_false_eq_true, not_true_eq_false, true_and, ↓reduceIte, zero_add]
        split_ifs <;> nlinarith [sq_nonneg ‖ψ g‖]
    · simp only [hlin, not_false_eq_true, false_and, ↓reduceIte, add_zero]
      split_ifs <;> nlinarith [sq_nonneg ‖ψ g‖]
  exact hunion.trans ((add_le_add (add_le_add hN (hW false)) (hW true)).trans_eq (by push_cast; ring))

def directPolynomialEquiv (P : AdmissibleParams) :
    DirectPolyTuple P.extendedDirectLd ≃
      Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d where
  toFun g := ⟨MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1, by
    rw [MvPolynomial.mem_restrictDegree]; intro s hs i
    exact (MvPolynomial.mem_restrictDegree _ _ _).mp (g 0).2 s (MvPolynomial.support_map_subset _ _ hs) i⟩
  invFun p := fun _ => ⟨MvPolynomial.map (extendedDirectScalarEquiv P).symm.toRingHom p.1, by
    rw [MvPolynomial.mem_restrictDegree]; intro s hs i
    exact (MvPolynomial.mem_restrictDegree _ _ _).mp p.2 s (MvPolynomial.support_map_subset _ _ hs) i⟩
  left_inv g := by
    funext i; rw [Subsingleton.elim i (0 : Fin 1)]
    exact Subtype.ext ((MvPolynomial.mapEquiv _ (extendedDirectScalarEquiv P)).symm_apply_apply _)
  right_inv p := Subtype.ext ((MvPolynomial.mapEquiv _ (extendedDirectScalarEquiv P)).apply_symm_apply _)

def directCombinedEmbedding (P : AdmissibleParams) :
    PolyPair P ↪ DirectPolyTuple P.extendedDirectLd :=
  (combinedPolyEmbedding P).trans (directPolynomialEquiv P).symm.toEmbedding

def directPairMeasurement {P : AdmissibleParams} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (R : DirectPolyMeasTuple P.extendedDirectLd ι)
    (pair₀ : PolyPair P) : Quantum.Measurement (PolyPair P) ι :=
  completedPairMeasurement P (R.postprocess (directPolynomialEquiv P)) pair₀

theorem directPairMeasurement_projective {P : AdmissibleParams} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (R : DirectPolyMeasTuple P.extendedDirectLd ι)
    (hR : Measurement.IsProjective R) (pair₀ : PolyPair P) :
    Measurement.IsProjective (directPairMeasurement R pair₀) :=
  completedPairMeasurement_projective P _ (SandwichProduct.postprocess_isProjective R hR _) pair₀

theorem directCombinedEmbedding_read (P : AdmissibleParams)
    (x : ExtendedPointQuestion P) (pair : PolyPair P) :
    extendedPolynomialRead P x (directCombinedEmbedding P pair) =
      x.2.1 * evalAt .X x.1.1 pair + x.2.2 * evalAt .Z x.1.2 pair := by
  let u := (directPointExtendedQuestionEquiv P).symm x
  have heval : extendedPolynomialRead P x (directCombinedEmbedding P pair) =
      MvPolynomial.eval (directPointToPauli P u) (combinedPolyEmbedding P pair).1 := by
    let p : Preliminaries.polyFunc (2 * P.m + 2) (DirectScalarQ P.extendedDirectLd) P.d :=
      directCombinedEmbedding P pair (0 : Fin 1)
    have hp := congrArg Subtype.val ((directPolynomialEquiv P).apply_symm_apply (combinedPolyEmbedding P pair))
    change MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom p.1 = _ at hp
    rw [← hp]
    change extendedDirectScalarEquiv P (MvPolynomial.eval u p.1) = _
    rw [MvPolynomial.eval_map]
    exact (MvPolynomial.eval₂_comp (extendedDirectScalarEquiv P).toRingHom u p.1).symm
  rw [heval, combinedPolyEmbedding_eval]
  have hx' : x = ((projX (directPointToPauli P u), projZ (directPointToPauli P u)),
      (directPointToPauli P u (alphaVar P.m), directPointToPauli P u (betaVar P.m))) :=
    ((directPointExtendedQuestionEquiv P).apply_symm_apply x).symm.trans (directPointExtendedQuestionEquiv_apply P u)
  rw [hx']

theorem directPairMeasurement_consistency_le_ordered_error {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (pair₀ : PolyPair P) (reverse : Bool) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun x a => S.place p1 (((directPairMeasurement R pair₀).postprocess
        (evalAt (if reverse then .Z else .X) x)).effect a))
      (fun x a => S.place p2
        ((S.pointMeasExp p2.side (if reverse then .Z else .X) x).effect a)) S.psiHat ≤
      separatedPolynomialMass S p1 R +
        2 * extendedPolynomialOrderedError S p1 p2 R reverse + 4 / P.q := by
  classical
  let W : PauliKind := if reverse then .Z else .X
  let C := directPairMeasurement R pair₀
  let B := fun x => S.pointMeasExp p2.side W x
  let ψ := fun g => applyOperatorToState (S.place p1 (R.effect g)) S.psiHat
  have hmass : ∑ g, ‖ψ g‖ ^ 2 = 1 := by
    simpa only [ψ, ProjectiveSetting.placedMeasurement_effect, S.psiHat_norm, one_pow] using
      sum_projective_state_norm_sq (S.placedMeasurement p1 R) (S.placedMeasurement_isProjective p1 R hR) S.psiHat
  -- Retained mass identity
  have hret_mass : (∑ pair : PolyPair P, ‖ψ (directCombinedEmbedding P pair)‖ ^ 2) =
      1 - separatedPolynomialMass S p1 R := by
    have hgood : Finset.univ.image (directCombinedEmbedding P) =
        Finset.univ.filter (fun g => ∃ pair : PolyPair P,
          MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1 =
            combinePoly pair.1.1 pair.2.1) := by
      ext g
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
      constructor
      · rintro ⟨pair, rfl⟩
        exact ⟨pair, congrArg Subtype.val ((directPolynomialEquiv P).apply_symm_apply (combinedPolyEmbedding P pair))⟩
      · rintro ⟨pair, hp⟩
        exact ⟨pair, (directPolynomialEquiv P).injective
          (((directPolynomialEquiv P).apply_symm_apply _).trans (Subtype.ext hp.symm))⟩
    rw [← Finset.sum_image (f := fun g => ‖ψ g‖ ^ 2) (fun _ _ _ _ h => (directCombinedEmbedding P).injective h), hgood]
    have hsp := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun g => ∃ pair : PolyPair P, MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1 =
        combinePoly pair.1.1 pair.2.1) (fun g => ‖ψ g‖ ^ 2)
    rw [hmass] at hsp
    exact eq_sub_of_add_eq hsp
  -- Retained mismatch bound
  let retMismatch := avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun x =>
    ∑ pair : PolyPair P, ‖applyOperatorToState (1 - S.place p2 ((B x).effect (evalAt W x pair)))
      (ψ (directCombinedEmbedding P pair))‖ ^ 2)
  have hmismatch_le : retMismatch ≤ 2 * extendedPolynomialOrderedError S p1 p2 R reverse + 4 / P.q := by
    let Xm := fun x : Fin P.m → PauliScalar P => S.placedMeasurement p2 (B x)
    let Zm := fun z : Fin P.m → PauliScalar P => S.placedMeasurement p2
      (S.pointMeasExp p2.side (if reverse then .X else .Z) z)
    let Am := fun (z x : Fin P.m → PauliScalar P) (v : Fin 2 → PauliScalar P) g =>
      applyOperatorToState (orderedIndicator (Xm x) (Zm z) (v 0) (v 1)
        (extendedPolynomialRead P (fiberQuestionEquiv P reverse ((z, x), v)) g)) (ψ g)
    have hret1 : ∑ pair, ‖ψ (directCombinedEmbedding P pair)‖ ^ 2 ≤ 1 := by
      rw [← hmass, ← Finset.sum_image (f := fun g => ‖ψ g‖ ^ 2) (fun _ _ _ _ h => (directCombinedEmbedding P).injective h)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    have hread (z x : Fin P.m → PauliScalar P) (v : Fin 2 → PauliScalar P) (pair : PolyPair P) :
        extendedPolynomialRead P (fiberQuestionEquiv P reverse ((z, x), v)) (directCombinedEmbedding P pair) =
          v 0 * evalAt W x pair + v 1 * evalAt (if reverse then .X else .Z) z pair := by
      rw [directCombinedEmbedding_read]; cases reverse <;> simp [W, fiberQuestionEquiv, finTwoArrowEquiv, add_comm]
    have hpt (z x : Fin P.m → PauliScalar P) :
        (∑ pair : PolyPair P, ‖applyOperatorToState (1 - (Xm x).effect (evalAt W x pair))
          (ψ (directCombinedEmbedding P pair))‖ ^ 2) ≤
        2 * avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v => ∑ g, ‖ψ g - Am z x v g‖ ^ 2) + 4 / P.q := by
      have h (pair : PolyPair P) := point_mismatch_le_ordered_error (Xm x) (Zm z)
        (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
        (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
        (evalAt W x pair) (evalAt (if reverse then .X else .Z) z pair) (ψ (directCombinedEmbedding P pair))
      simp_rw [← hread z x] at h
      have hs := Finset.sum_le_sum (s := Finset.univ) fun pair _ => h pair
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← avgOver_sum] at hs
      have herr : avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v =>
          ∑ pair, ‖ψ (directCombinedEmbedding P pair) - Am z x v (directCombinedEmbedding P pair)‖ ^ 2) ≤
        avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v => ∑ g, ‖ψ g - Am z x v g‖ ^ 2) :=
        avgOver_mono _ _ _ fun v => by
          rw [← Finset.sum_image (f := fun g => ‖ψ g - Am z x v g‖ ^ 2)
            (fun _ _ _ _ h => (directCombinedEmbedding P).injective h)]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
      have hcard : Fintype.card (PauliScalar P) = P.q := @FieldModel.card P.q P.model.toFieldModel
      have hc := mul_le_mul_of_nonneg_left hret1 (show 0 ≤ 4 * (Fintype.card (PauliScalar P) : ℝ)⁻¹ by positivity)
      rw [hcard, mul_one] at hc
      change _ ≤ 2 * avgOver _ (fun v => ∑ pair,
        ‖ψ (directCombinedEmbedding P pair) - Am z x v (directCombinedEmbedding P pair)‖ ^ 2) +
        4 * (Fintype.card (PauliScalar P) : ℝ)⁻¹ * _ at hs
      rw [hcard] at hs; rw [div_eq_mul_inv]; linarith
    have h := avgOver_mono (uniformDistribution (Fin P.m → PauliScalar P)) _ _ fun z =>
      avgOver_mono (uniformDistribution (Fin P.m → PauliScalar P)) _ _ (hpt z)
    dsimp only [Am, Xm, Zm] at h
    simp only [avgOver_uniform_const, avgOver_add, avgOver_const_mul,
      ProjectiveSetting.placedMeasurement_effect] at h
    rw [fiber_ordered_error_eq S p1 p2 hopposite R reverse] at h
    exact h
  -- Consistency defect <= separatedPolynomialMass + retMismatch
  let retOverlap := avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun x =>
    ∑ pair : PolyPair P, stateQForm S.psiHat
      (S.place p1 (R.effect (directCombinedEmbedding P pair)) * S.place p2 ((B x).effect (evalAt W x pair))))
  have hmismatch_eq : retMismatch = 1 - separatedPolynomialMass S p1 R - retOverlap := by
    have hp (x : Fin P.m → PauliScalar P) (pair : PolyPair P) :
        ‖applyOperatorToState (1 - S.place p2 ((B x).effect (evalAt W x pair)))
          (ψ (directCombinedEmbedding P pair))‖ ^ 2 =
        ‖ψ (directCombinedEmbedding P pair)‖ ^ 2 - stateQForm S.psiHat
          (S.place p1 (R.effect (directCombinedEmbedding P pair)) * S.place p2 ((B x).effect (evalAt W x pair))) := by
      have hM := S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ W x) (evalAt W x pair)
      have hG := S.placedMeasurement_isProjective p1 R hR (directCombinedEmbedding P pair)
      simp only [ProjectiveSetting.placedMeasurement_effect] at hM hG
      have hcomm := S.place_comm p1 p2 hopposite (R.effect (directCombinedEmbedding P pair)) ((B x).effect (evalAt W x pair))
      rw [MagicSquareRigidity.norm_applyOperatorToState_sq]
      change stateQForm _ _ = _
      have hsub (φ : EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB))
          (M N : Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB)) :
          stateQForm φ (M - N) = stateQForm φ M - stateQForm φ N := by
        simp [stateQForm, applyOperatorToState]
      rw [hM.one_sub.isSelfAdjoint.isHermitian.eq, hM.one_sub.isIdempotentElem.eq,
        hsub, stateQForm_one, stateQForm_applyOperatorToState_eq_of_isProj S.psiHat hG hcomm.symm, hcomm]
    dsimp only [retMismatch, retOverlap]
    simp_rw [hp, Finset.sum_sub_distrib, avgOver_sub, avgOver_uniform_const, hret_mass]
  have hdiag (x : Fin P.m → PauliScalar P) :
      (∑ a : PauliScalar P, stateQForm S.psiHat
        (S.place p1 ((C.postprocess (evalAt W x)).effect a) * S.place p2 ((B x).effect a))) =
      ∑ pair : PolyPair P, stateQForm S.psiHat
        (S.place p1 (C.effect pair) * S.place p2 ((B x).effect (evalAt W x pair))) := by
    simp_rw [Quantum.Measurement.postprocess_effect, S.place_finsetSum, Finset.sum_mul, stateQForm_finset_sum]
    calc _ = ∑ a : PauliScalar P, ∑ pair ∈ Finset.univ.filter (fun pair => evalAt W x pair = a),
          stateQForm S.psiHat (S.place p1 (C.effect pair) * S.place p2 ((B x).effect (evalAt W x pair))) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun pair hp => by rw [(Finset.mem_filter.mp hp).2]
      _ = _ := Finset.sum_fiberwise Finset.univ (evalAt W x) _
  have hret_le (x : Fin P.m → PauliScalar P) :
      (∑ pair : PolyPair P, stateQForm S.psiHat
        (S.place p1 (R.effect (directCombinedEmbedding P pair)) * S.place p2 ((B x).effect (evalAt W x pair)))) ≤
      ∑ pair : PolyPair P, stateQForm S.psiHat
        (S.place p1 (C.effect pair) * S.place p2 ((B x).effect (evalAt W x pair))) := by
    refine Finset.sum_le_sum fun pair _ => ?_
    have hpadd (M N : Op (S.ExpandedLocalSpace p1.side)) : S.place p1 (M + N) = S.place p1 M + S.place p1 N := by
      ext i j; cases p1 <;> simp only [ProjectiveSetting.place, Matrix.add_apply, add_mul, mul_add]
    dsimp only [C, directPairMeasurement]
    rw [completedPairMeasurement_effect, hpadd, add_mul, stateQForm_add]
    have heff : (combinedPairSubmeasurement P (R.postprocess (directPolynomialEquiv P))).effect pair =
        R.effect (directCombinedEmbedding P pair) := by
      simpa only [combinedPairSubmeasurement, directCombinedEmbedding,
        Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.apply_symm_apply] using
        SandwichProduct.postprocess_effect_of_injective R (directPolynomialEquiv P)
          (directPolynomialEquiv P).injective ((directPolynomialEquiv P).symm (combinedPolyEmbedding P pair))
    rw [heff]
    refine le_add_of_nonneg_right (stateQForm_nonneg _ (Commute.mul_nonneg (S.place_nonneg p1 ?_)
      (S.place_nonneg p2 ((B x).pos _)) (S.place_comm p1 p2 hopposite _ _)))
    split_ifs
    · exact sub_nonneg.mpr (combinedPairSubmeasurement P _).total_le_one
    · exact le_rfl
  have hdef : consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun x a => S.place p1 ((C.postprocess (evalAt W x)).effect a))
      (fun x a => S.place p2 ((B x).effect a)) S.psiHat ≤ 1 - retOverlap := by
    unfold consistencyDefect
    simp_rw [consistency_term_eq_stateQForm]
    have heq (x : Fin P.m → PauliScalar P) := point_defect_eq
      (S.placedMeasurement p1 (C.postprocess (evalAt W x))) (S.placedMeasurement p2 (B x)) S.psiHat
    simp only [ProjectiveSetting.placedMeasurement_effect, S.psiHat_norm, one_pow] at heq
    simp_rw [heq, hdiag]
    simpa only [avgOver_sub, avgOver_uniform_const, retOverlap] using
      avgOver_mono (uniformDistribution (Fin P.m → PauliScalar P)) _ _ fun x => sub_le_sub_left (hret_le x) 1
  change consistencyDefect _ (fun x a => S.place p1 ((C.postprocess (evalAt W x)).effect a))
    (fun x a => S.place p2 ((B x).effect a)) S.psiHat ≤ _
  linarith

theorem exists_pairWitness_of_points_lines :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (P : AdmissibleParams) (ε δQ δL : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ) (_lines : ExtendedLinesWitness S points δL),
      let delta := deltaLd a b
        (directPassingErrorEnvelope (δQ + δL) ((P.m * P.d : ℝ) / P.q))
        P.q (2 * P.m + 2) P.d 1
      let eta := delta + Real.sqrt (220 * Real.rpow delta (1 / 4 : ℝ)) + 2 * Real.sqrt (2 * delta)
      Nonempty (GlobalPairWitness S (8 * (4 * eta + 8 * δQ) +
        (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q))) := by
  refine ⟨pauliBaselineLowDegreeConstant, pauliBaselineLowDegreePower,
    by unfold pauliBaselineLowDegreeConstant; norm_num,
    by unfold pauliBaselineLowDegreePower; norm_num,
    by unfold pauliBaselineLowDegreePower; norm_num, ?_⟩
  intro P ε δQ δL S points lines delta eta
  obtain ⟨RA, RB, hRA, hRB, horder⟩ := rounded_polynomial_ordered_estimates_explicit P ε δQ δL S points lines
  let pair₀ : PolyPair P := (0, 0)
  have hmassA : separatedPolynomialMass S .AA' RA ≤ 6 * (4 * eta + 8 * δQ) +
      (((12 * P.m * P.d + 4 * P.d + 10 : ℕ) : ℝ) / P.q) := by
    have := separatedPolynomialMass_le_ordered_errors S .AA' .BA'' trivial RA hRA
    have := (horder false).1; have := (horder true).1; linarith
  have hmassB : separatedPolynomialMass S .BB' RB ≤ 6 * (4 * eta + 8 * δQ) +
      (((12 * P.m * P.d + 4 * P.d + 10 : ℕ) : ℝ) / P.q) := by
    have := separatedPolynomialMass_le_ordered_errors S .BB' .AB'' trivial RB hRB
    have := (horder false).2; have := (horder true).2; linarith
  have hA (rev : Bool) := directPairMeasurement_consistency_le_ordered_error S .AA' .BA'' trivial RA hRA pair₀ rev
  have hB (rev : Bool) := directPairMeasurement_consistency_le_ordered_error S .BB' .AB'' trivial RB hRB pair₀ rev
  have hbound : 6 * (4 * eta + 8 * δQ) + (((12 * P.m * P.d + 4 * P.d + 10 : ℕ) : ℝ) / P.q) +
      2 * (4 * eta + 8 * δQ) + 4 / P.q =
      8 * (4 * eta + 8 * δQ) + (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q) := by push_cast; ring
  refine ⟨{
    Smeas := fun side => match side with
      | .alice => directPairMeasurement RA pair₀
      | .bob => directPairMeasurement RB pair₀
    projective := fun side => by
      cases side
      · exact directPairMeasurement_projective RA hRA pair₀
      · exact directPairMeasurement_projective RB hRB pair₀
    point_consistent_alice := fun W => by
      cases W
      · exact (hA false).trans ((add_le_add (add_le_add hmassA
          (mul_le_mul_of_nonneg_left (horder false).1 (by norm_num))) le_rfl).trans_eq hbound)
      · exact (hA true).trans ((add_le_add (add_le_add hmassA
          (mul_le_mul_of_nonneg_left (horder true).1 (by norm_num))) le_rfl).trans_eq hbound)
    point_consistent_bob := fun W => by
      cases W
      · exact (hB false).trans ((add_le_add (add_le_add hmassB
          (mul_le_mul_of_nonneg_left (horder false).2 (by norm_num))) le_rfl).trans_eq hbound)
      · exact (hB true).trans ((add_le_add (add_le_add hmassB
          (mul_le_mul_of_nonneg_left (horder true).2 (by norm_num))) le_rfl).trans_eq hbound) }⟩

end ExtendedLineGame

/-! ## Section 6: Global polynomial-pair witness theorem -/

theorem exists_globalPairWitness :
    ∃ a b : ℝ, 1 < a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
        Nonempty (GlobalPairWitness S (deltaQld a b ε P.m P.d P.q)) := by
  classical
  obtain ⟨deltaQ, hdeltaQ, hpoints⟩ := exists_combinedPointsWitness
  obtain ⟨deltaP, hdeltaP, hlines⟩ := exists_combinedLinesWitness_ofPointsWitness deltaQ hdeltaQ
  obtain ⟨constant, hconstant, hnear⟩ := subline_joint_overlap_near_one_at
  obtain ⟨deltaCombine, hdeltaCombine, hcomb⟩ :=
    exists_combining_polynomial_bound deltaQ hdeltaQ deltaP hdeltaP constant hconstant.le
  obtain ⟨a, b, ha, hb, hb1, hpairs⟩ := ExtendedLineGame.exists_pairWitness_of_points_lines
  obtain ⟨A, B, hA, hB, hB1, hscalar⟩ :=
    exists_actual_rounded_global_pair_error_bound deltaQ hdeltaQ deltaCombine hdeltaCombine
      1 a b (by norm_num) ha hb hb1
  refine ⟨A, B, hA, hB, hB1, fun P ε S => ?_⟩
  obtain ⟨points⟩ := hpoints P ε S
  obtain ⟨lines0⟩ := hlines P ε S points
  obtain ⟨sublines⟩ := exists_subLineWitness P
  have hdef_one {X α : Type} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
      (μ : Distribution X) (hμ : μ.IsProbability) (p1 p2 : Placement) (hop : p1.IsOpposite p2)
      (M1 : X → Measurement α (S.ExpandedLocalSpace p1.side))
      (M2 : X → Measurement α (S.ExpandedLocalSpace p2.side)) :
      consistencyDefect μ (fun x c => S.place p1 ((M1 x).effect c))
        (fun x c => S.place p2 ((M2 x).effect c)) S.psiHat ≤ 1 :=
    (avgOver_mono μ _ (fun _ => 1) fun x =>
      consistencyDefect_integrand_le_one S p1 p2 hop (M1 x) (M2 x)).trans_eq
      (avgOver_const_of_isProbability μ hμ 1)
  have hplaced (p1 p2 : Placement) (hop : p1.IsOpposite p2) :
      consistencyDefect (directLinePointDist P.extendedDirectLd)
        (fun s ans => S.place p1
          (((sublines.extendedMeasurement lines0 p1.side s.1).postprocess
            (fun poly => (directEvalOpt s.1 s.2 poly).map (extendedDirectScalarEquiv P))).effect ans))
        (fun s ans => S.place p2
          (((points.Q p2.side (projX (directPointToPauli P s.2))
            (projZ (directPointToPauli P s.2))).postprocess (fun v => some
              ((directPointToPauli P s.2) (alphaVar P.m) * v.1 +
                (directPointToPauli P s.2) (betaVar P.m) * v.2))).effect ans))
        S.psiHat ≤ 1 * (P.m : ℝ) * deltaCombine ε ((P.m * P.d : ℕ) / (P.q : ℝ)) := by
    rw [one_mul]
    refine (le_min (hdef_one _ (directLinePointDist_isProbability _) p1 p2 hop _ _) ?_).trans
      (hcomb ε ((P.m * P.d : ℕ) / (P.q : ℝ)) (P.m : ℝ) S.eps_nonneg (by positivity)
        (by exact_mod_cast P.one_le_m))
    exact (sublines.extended_consistencyDefect_le lines0 p1 p2 hop).trans
      ((le_abs_self _).trans (by
        simpa only [abs_sub_comm] using
          hnear P ε (deltaQ ε) (deltaP ε ((P.m * P.d : ℕ) / (P.q : ℝ)))
            S points lines0 sublines p1 p2 hop))
  let extLines : ExtendedLinesWitness S points
      (1 * (P.m : ℝ) * deltaCombine ε ((P.m * P.d : ℕ) / (P.q : ℝ))) := {
    Qline := sublines.extendedMeasurement lines0
    axis_degree := sublines.extendedMeasurement_axis_degree lines0
    consistent_alice := by with_unfolding_all exact hplaced .AA' .BA'' trivial
    consistent_bob := by with_unfolding_all exact hplaced .BB' .AB'' trivial
  }
  obtain ⟨pair⟩ := hpairs P ε (deltaQ ε)
    (1 * (P.m : ℝ) * deltaCombine ε ((P.m * P.d : ℕ) / (P.q : ℝ))) S points extLines
  have hbound := hscalar P ε S.eps_nonneg
  simp only [Nat.cast_mul] at hbound
  refine ⟨{ pair with
    point_consistent_alice := fun W =>
      (le_min (hdef_one _ (uniformDistribution_isProbability _) .AA' .BA'' trivial _ _)
        (pair.point_consistent_alice W)).trans
        (by with_unfolding_all simpa only [Nat.cast_mul, Real.rpow_eq_pow] using hbound)
    point_consistent_bob := fun W =>
      (le_min (hdef_one _ (uniformDistribution_isProbability _) .BB' .AB'' trivial _ _)
        (pair.point_consistent_bob W)).trans
        (by with_unfolding_all simpa only [Nat.cast_mul, Real.rpow_eq_pow] using hbound) }⟩

end

end MIPStarRE.QPBT
