/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IntegerLinearForms
import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Projection.ProjectiveClosureProjection
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import CCDN.Hilbert.FullDimension
import CCDN.Projection.BoundedClosureElimination
import CCDN.Projection.ClosureIntegralComposition
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Constructive bounded linear Noether normalization. The coefficients of
the integer linear forms are bounded by n! (d+1)^n, and the map of projective closures
fixing the homogenizing coordinate is integral as well. -/

namespace CCDN
section
open MvPolynomial

section
variable (n d : ℕ)

/-- The coefficient bound `n! * (d + 1) ^ n` for the bounded linear Noether normalization of a
degree-`d` variety in `n` variables. -/
def integerNormalizationHeight : ℕ := n.factorial * (d + 1) ^ n

end

lemma integerNormalizationHeight_mono (n : ℕ) {d e : ℕ} (h : d ≤ e) :
    integerNormalizationHeight n d ≤ integerNormalizationHeight n e := by
  dsimp [integerNormalizationHeight]
  gcongr

lemma integerNormalizationHeight_step (n d : ℕ) :
    n * integerNormalizationHeight n d * (d + 1) ≤
      integerNormalizationHeight (n + 1) d := by
  dsimp [integerNormalizationHeight]
  rw [Nat.factorial_succ, pow_succ]
  nlinarith [Nat.zero_le (n.factorial * (d + 1) ^ n * (d + 1))]

variable (m k : ℕ) (I : Ideal (MvPolynomial (Fin (m + 1 + k)) ℚ)) [I.IsPrime] (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d)
include hdimdeg

/-- Integer linear normalization of a prime quotient of positive Hilbert dimension. The
resulting polynomial map is injective and integral, and so is the induced map of projective
closures fixing the homogenizing coordinate. -/
theorem exists_bounded_integer_normalization
    :
    ∃ a : Fin (m + 1) → Fin (m + 1 + k) → ℤ,
      (∀ i j, |a i j| ≤ integerNormalizationHeight (m + 1 + k) d) ∧
      (projectionCoordinateMap I (fun i => integerLinearForm (a i))).IsIntegral ∧
      Function.Injective (projectionCoordinateMap I (fun i => integerLinearForm (a i))) := by
  induction k generalizing d with
  | zero =>
    let a : Fin (m + 1) → Fin (m + 1) → ℤ := fun i j => if j = i then 1 else 0
    have heq : projectionCoordinateMap I (fun i => integerLinearForm (a i)) =
        Ideal.Quotient.mkₐ ℚ I := by
      ext i
      simp [projectionCoordinateMap, a, integerLinearForm_identity]
    have hI0 := ideal_eq_bot_of_full_hilbert_dimension I (Ideal.IsPrime.ne_top ‹I.IsPrime›)
      (by simpa using hdimdeg.natDegree_eq)
    refine ⟨a, ?_, ?_, ?_⟩
    · intro i j
      have hH : (1 : ℤ) ≤ integerNormalizationHeight (m + 1) d := by
        exact_mod_cast Nat.succ_le_of_lt (show 0 < integerNormalizationHeight (m + 1) d by
            dsimp [integerNormalizationHeight]
            positivity)
      grind
    · rw [heq]
      exact RingHom.isIntegral_of_surjective _ (Ideal.Quotient.mkₐ_surjective ℚ I)
    · rw [heq]
      apply (RingHom.injective_iff_ker_eq_bot _).mpr
      change RingHom.ker ((Ideal.Quotient.mkₐ ℚ I) :
        MvPolynomial (Fin (m + 1)) ℚ →+* MvPolynomial (Fin (m + 1)) ℚ ⧸ I) = ⊥
      simp_all
  | succ k ih =>
    obtain ⟨c, e, hc, he, hed, hintc, hprime, hdimdegJ⟩ : ∃ (c : Fin (m + 1 + k) → Fin ((m + 1 + k) + 1) → ℤ) (e : ℕ),
        (∀ i j, |c i j| ≤ d + 1) ∧ 0 < e ∧ e ≤ d ∧
        let a := fun i => integerLinearForm (c i)
            let ψ := projectionCoordinateMap I a
            ψ.IsIntegral ∧ (RingHom.ker ψ).IsPrime ∧
            HasProjectiveDimensionDegree (RingHom.ker ψ) m e := by
        obtain ⟨f, hf, hfi, hfd⟩ := exists_mem_ideal_degree_le_multiplicity I d hdimdeg
          (by simp_all)
        let F := renameEquiv ℚ (finSuccEquiv (m + 1 + k)) f
        have hFdeg := totalDegree_renameEquiv (finSuccEquiv (m + 1 + k)) f
        obtain ⟨b, hbound, hb, hdir⟩ := exists_bounded_full_degree_direction F (by
          intro h
          apply hf
          exact (renameEquiv ℚ (finSuccEquiv (m + 1 + k))).injective (h.trans (map_zero _).symm))
        have hdir' : eval (Fin.cons (b none : ℚ) (fun i => (b (some i) : ℚ)))
            (homogeneousComponent f.totalDegree f) ≠ 0 := by
          rw [hFdeg] at hdir
          change eval (fun i => (b i : ℚ))
            (homogeneousComponent f.totalDegree (rename (finSuccEquiv (m + 1 + k)) f)) ≠ 0 at hdir
          rw [← rename_homogeneousComponent, eval_rename] at hdir
          convert hdir using 1
          congr 1
          congr 1
          funext i
          refine Fin.cases rfl (fun j => rfl) i
        have hcone : (projectionCoordinateMap (projectiveClosureIdeal I)
            (closureProjectionCoordinates
              (fun i => integerLinearForm (finEliminationMatrix b i)))).IsIntegral := by
          let H := projectiveClosureIdeal I
          let e := renameEquiv ℚ (closurePivotEquiv (m + 1 + k))
          let J := H.map e
          let F := e (scaledHomogenize f.totalDegree 1 f)
          let c := closureEliminationDirection b
          have hc : (c none : ℚ) ≠ 0 := (mod_cast hb)
          have hFhom : F.IsHomogeneous f.totalDegree :=
            (scaledHomogenize_homogeneous 1 f le_rfl).rename_isHomogeneous
          have hFdeg := hFhom.totalDegree (by
            intro h
            have hh : scaledHomogenize f.totalDegree 1 f = 0 := e.injective (by grind)
            apply hf
            simpa [affineChart_scaledHomogenize_one, map_zero] using
              congrArg (affineChart ((m + 1 + k) + 1)) hh)
          have hFdir : eval (fun i => (c i : ℚ))
              (homogeneousComponent F.totalDegree F) ≠ 0 := by
            rw [hFdeg, homogeneousComponent_eq_self hFhom]
            exact (show eval (fun i => (closureEliminationDirection b i : ℚ))
                    (rename (closurePivotEquiv (m + 1 + k)) (scaledHomogenize f.totalDegree 1 f)) =
                  eval (Fin.cons (b none : ℚ) (fun i => (b (some i) : ℚ)))
                    (homogeneousComponent f.totalDegree f) by
                rw [eval_rename]
                change eval (fun i => (closureEliminationDirection b (closurePivotEquiv (m + 1 + k) i) : ℚ))
                  (scaledHomogenize f.totalDegree 1 f) = _
                rw [closureEliminationDirection_comp, scaledHomogenize_one_eval_at_infinity f le_rfl]).trans_ne hdir'
          have hFmem : F ∈ J := by
            apply Ideal.mem_map_of_mem
            rw [homogeneous_mem_projectiveClosureIdeal_iff I _
              (scaledHomogenize_homogeneous 1 f le_rfl), affineChart_scaledHomogenize_one]
            exact hfi
          have hraw : (coordinateEliminationMap J
              (hypersurfaceAffineCoordinates 0 (fun i => (c i : ℚ)) hc)).IsIntegral := by
            apply coordinateEliminationMap_isIntegral J _
              (normalizedHypersurfaceCoordinates 0 (fun i => (c i : ℚ)) hc F)
            · exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hFmem)
            · exact normalizedHypersurfaceCoordinates_monic 0 _ hc F hFdir
          rw [coordinateEliminationMap_eq_projection] at hraw
          have hint := integerEliminationMap_isIntegral J c hc hraw
          have hJ : J = H.map
              (e : MvPolynomial (Fin ((m + 1 + k) + 2)) ℚ →+*
                MvPolynomial (Option (Fin ((m + 1 + k) + 1))) ℚ) := rfl
          let φ := (Ideal.quotientEquivAlg H J e hJ).symm
          have hφ := RingHom.isIntegral_of_surjective _ φ.surjective
          have hcomp := RingHom.IsIntegral.trans
            (projectionCoordinateMap J (integerEliminationCoordinates c)).toRingHom φ.toRingHom
            hint hφ
          let a := fun i => integerLinearForm (finEliminationMatrix b i)
          let ψ := projectionCoordinateMap H (closureProjectionCoordinates a)
          let χ : MvPolynomial (Fin ((m + 1 + k) + 1)) ℚ →ₐ[ℚ] MvPolynomial (Fin ((m + 1 + k) + 1)) ℚ :=
            aeval (Fin.cons (C (b none : ℚ) * X 0) (fun i => X i.succ))
          have heq : φ.toAlgHom.comp (projectionCoordinateMap J (integerEliminationCoordinates c)) =
              ψ.comp χ := by
            ext i
            simp only [AlgHom.comp_apply, projectionCoordinateMap, aeval_X,
              Ideal.Quotient.mkₐ_eq_mk]
            change φ ((Ideal.Quotient.mk J) (integerEliminationCoordinates c i)) = ψ (χ (X i))
            dsimp only [φ]
            rw [Ideal.quotientEquivAlg_symm, Ideal.quotientEquivAlg_mk]
            refine Fin.cases ?_ (fun j => ?_) i
            · simp [integerEliminationCoordinates, c, closureEliminationDirection, e,
                ψ, χ, projectionCoordinateMap, closureProjectionCoordinates]
            · simp [integerEliminationCoordinates, c, closureEliminationDirection, e,
                ψ, χ, projectionCoordinateMap, closureProjectionCoordinates, a,
                integerLinearForm_finEliminationMatrix]
          change (φ.toAlgHom.comp
            (projectionCoordinateMap J (integerEliminationCoordinates c))).IsIntegral at hcomp
          rw [heq] at hcomp
          exact RingHom.IsIntegral.tower_top χ.toRingHom ψ.toRingHom hcomp
        let c := finEliminationMatrix b
        have hint := affine_projection_integral_of_closure_integral I
          (fun i => integerLinearForm (c i)) hcone
        obtain ⟨e, he, hed, hker⟩ := integral_linear_projection_dimension_degree I
          (fun i => integerLinearForm (c i)) (fun i => linearForm_totalDegree_le _) hint hdimdeg
        exact ⟨c, e, (by
          apply finEliminationMatrix_height
          grind), he, hed, hint, RingHom.ker_isPrime _, hker⟩
    let ψ := projectionCoordinateMap I (fun i => integerLinearForm (c i))
    let J := RingHom.ker ψ
    have : J.IsPrime := hprime
    obtain ⟨a, ha, hinta, hinja⟩ := ih J e hdimdegJ
    let a' : Fin (m + 1) → Fin (m + 1 + (k + 1)) → ℤ :=
      fun i j => ∑ t, a i t * c t j
    let ψa := projectionCoordinateMap J (fun i => integerLinearForm (a i))
    let φ := Ideal.kerLiftAlg ψ
    have hφ := hintc.kerLift
    have hcomp := RingHom.IsIntegral.trans ψa.toRingHom φ.toRingHom hinta hφ
    have heq : φ.comp ψa = projectionCoordinateMap I (fun i => integerLinearForm (a' i)) := by
      ext i
      simp only [AlgHom.comp_apply, ψa, projectionCoordinateMap, aeval_X,
        Ideal.Quotient.mkₐ_eq_mk]
      change (Ideal.Quotient.mk I)
        (aeval (fun t => integerLinearForm (c t)) (integerLinearForm (a i))) =
          (Ideal.Quotient.mk I) (integerLinearForm (a' i))
      rw [integerLinearForm_comp]
      rfl
    refine ⟨a', ?_, ?_, ?_⟩
    · intro i j
      have hbound := integerLinearForm_matrix_height (a i) c
        (integerNormalizationHeight (m + 1 + k) e) (d + 1) (ha i)
        (fun i j => by grind) j
      simp at hbound
      apply hbound.trans
      have hmono := integerNormalizationHeight_mono (m + 1 + k) hed
      have hstep := integerNormalizationHeight_step (m + 1 + k) d
      exact_mod_cast (Nat.mul_le_mul_right (d + 1)
        (Nat.mul_le_mul_left (m + 1 + k) hmono)).trans hstep
    · change (φ.comp ψa).IsIntegral at hcomp
      grind
    · rw [← heq]
      exact (Ideal.kerLiftAlg_injective ψ).comp hinja
