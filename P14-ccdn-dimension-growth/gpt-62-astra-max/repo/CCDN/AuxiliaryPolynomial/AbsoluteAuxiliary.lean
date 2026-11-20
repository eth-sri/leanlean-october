/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Algebra.ProjectiveTranslation
public import CCDN.Height.IntegerCoefficientHeight
public import CCDN.AuxiliaryPolynomial.DegreeSelection
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates
import CCDN.AuxiliaryPolynomial.HypersurfacePositionHeight

/-! Homogeneous auxiliary forms under a determinant lower bound. Pulling the
forms back lets us use the arithmetic estimate in the original coordinates. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma hypersurfaceAbsoluteAuxiliaryConstant_pos (n : ℕ) : 0 < hypersurfaceAbsoluteAuxiliaryConstant n :=
  zero_lt_one.trans_le (hypersurfaceAbsoluteAuxiliaryConstant_one_le n)

abbrev hypersurfaceAuxiliaryDegreeBound (n d : ℕ) (B A H : ℝ) := hypersurfaceAbsoluteAuxiliaryConstant n * auxDegreeBound n d B A H

/-- One degree selection works for both the ordinary good-prime estimates and smooth congruence classes. -/
theorem auxiliary_from_evaluation_lower {n d t : ℕ} (f : IntegerPolynomial (n+3)) (hf : f.IsHomogeneous d)
    (hf0 : f ≠ 0) (hd : 0 < d) (z : Fin t → IntPoint (n+3)) (hz : ∀ i, eval (z i) f = 0)
    {B A Q : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B) (hA : 0 < A) (hQ : 0 ≤ Q) (hdet : EvaluationLower z d A Q) :
    ∃ M : ℕ, (M:ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n d B A (integerCoefficientHeight f) + (n+2 : ℝ)*Q ∧
      ∃ g, IsPointAuxiliary f g M z := by
  obtain ⟨a, ha, hL, hcoeff⟩ := exists_hypersurface_leading_coefficient_translation f hf hf0
  let g := homogeneousTranslation ℤ a f
  let w := fun i => homogeneousPointTranslation (-a) (z i)
  have hw (i) : eval (w i) g = 0 := by
    rw [show g = _ from rfl, homogeneousTranslation_eval]
    change eval (homogeneousPointTranslation a _) f = 0
    simpa using (show eval (homogeneousPointTranslation (- -a) _) f = 0 by rw [homogeneousPointTranslation_inverse]; exact hz i)
  have hD : EvaluationLower w d A Q := by
    intro s N M b F hs hF
    dsimp only
    intro hi
    have he : (Matrix.of fun i j => eval (z (b i)) (homogeneousTranslation ℤ (-a) (F j))) =
        Matrix.of fun i j => eval (w (b i)) (F j) := by simp [homogeneousTranslation_eval, w, homogeneousPointTranslation]
    rw [← he] at hi ⊢
    exact hdet b _ hs (by solve_by_elim [homogeneousTranslation_homogeneous]) hi
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hB' : 1 ≤ (d+1 : ℝ)*B := one_le_mul_of_one_le_of_one_le (by simp) hB
  obtain ⟨M,hM,hQM,hscale,hth,hbound⟩ := select_auxiliary_degree hd hB hA (abs_pos.mpr (by exact_mod_cast hL))
    (by exact_mod_cast integerCoefficientHeight_pos f hf0) hQ
    (integerCoefficientHeight_le f (by positivity) hcoeff)
  obtain ⟨G, hG⟩ := auxiliary_at_degree .lex g (homogeneousTranslation_homogeneous a hf) (by simpa [g]) hd w hw
    hB' (fun i => homogeneousPointTranslation_box hB a ha _ (hbox i))
    (show 4*((d+1)*B) ≤ (d+1)^3*B by
      have h : 4 ≤ (d+1 : ℝ)^2 := by nlinarith [sq_nonneg (d-1)]
      nlinarith only [mul_le_mul_of_nonneg_right h (zero_le_one.trans hB')]) hA hD hM hQM hscale hth
  refine ⟨M,hbound,homogeneousTranslation ℤ _ G, (homogeneousTranslation ℤ _).injective.ne (by simpa using hG.ne_zero),
    homogeneousTranslation_homogeneous _ hG.isHomogeneous, fun i => by rw [homogeneousTranslation_eval]; exact hG.eval_eq_zero i, ?_⟩
  intro h
  apply hG.not_dvd
  have hh := map_dvd (homogeneousTranslation ℤ a).toRingHom h
  change g ∣ homogeneousTranslation ℤ a ((homogeneousTranslation ℤ a).symm G) at hh
  rwa [AlgEquiv.apply_symm_apply] at hh

/-- The absolutely irreducible case of CCDN Theorem 3.1.1. The constant depends
only on dimension. The coefficient height and bad-prime factor belong to the
original equation. -/
theorem hypersurface_absolute_auxiliary_degree
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d t : ℕ}
    (f : IntegerPolynomial (n + 3)) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B) :
    ∃ (bad : Finset ℕ) (M : ℕ),
      (∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p) ∧
      (M : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n d B (primeSetFactor bad)
        (integerCoefficientHeight f) ∧
      ∃ g : IntegerPolynomial (n + 3), g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ i, eval (z i) g = 0) ∧ ¬ f ∣ g := by
  obtain ⟨bad,hbad⟩ := exists_hypersurface_bad_prime_finset f hf hd hir
  obtain ⟨M,hM,g,hg⟩ := auxiliary_from_evaluation_lower f hf (ne_zero_of_irreducible_map hir) hd z hz hB hbox
    (Real.exp_pos _) (le_refl 0) (A := primeSetFactor bad) (fun a F hs hF hi => by
      have h := hypersurface_determinant_log_lower_at_rank_congruence hs f hf hd
        (F := F) (z := fun i => z (a i)) ⟨hF, fun i => hprim _, fun i => hz _, hi⟩ bad ∅ (by simp) (by simp) 0 (by simp)
        (fun p _ hp hcut => hasGoodReduction_of_not_mem hbad p (Finset.mem_sdiff.mp hp).2 hcut)
      simpa using h)
  exact ⟨bad,M,hbad,by simpa using hM,g,hg.ne_zero,hg.isHomogeneous,hg.eval_eq_zero,hg.not_dvd⟩

end
end CCDN
