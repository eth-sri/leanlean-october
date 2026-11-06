/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IdealZeroLocus
import CCDN.Hilbert.FilteredIntersection
import CCDN.Algebra.PolynomialSection
import CCDN.Hilbert.LinearProjectionFiltration
import CCDN.Projection.CurveRationalInverse

/-! Polynomial reconstruction controls exceptional points and finite
point counts. The error is d times the reconstruction denominator's degree;
a uniform O(d^2) bound requires a low-degree denominator. -/

namespace CCDN
section
open MvPolynomial

/-- For every finite set of source points, projection loses at most
 d*deg(Q) points, where Q is any proper reconstruction denominator. -/
theorem projection_card_le_image_add {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]
    [DecidableEq (σ → K)]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime] (d : ℕ)
    (hdegree : HasFilteredCurveDegree I d)
    (a : σ → MvPolynomial τ K) (ha : ∀ j, (a j).totalDegree ≤ 1)
    (Q : MvPolynomial σ K) (P : τ → MvPolynomial σ K)
    (hQ : aeval a Q ∉ I) (hP : ∀ i, aeval a Q * X i - aeval a (P i) ∈ I)
    (S : Finset (τ → K)) (hS : ∀ z ∈ S, z ∈ idealZeroLocus I) :
    let π : (τ → K) → (σ → K) := fun z j => eval z (a j)
    S.card ≤ (S.image π).card + d * Q.totalDegree := by
  classical
  let π : (τ → K) → (σ → K) := fun z j => eval z (a j)
  let T := S.filter (fun z => eval z (aeval a Q) = 0)
  let G := S.filter (fun z => eval z (aeval a Q) ≠ 0)
  have hT : T.card ≤ d * Q.totalDegree := by
    have hh := polynomial_section_card_le_degree I d hdegree (aeval a Q) hQ Q.totalDegree
      (by simpa using aeval_totalDegree_le a ha Q) (fun z : T => z.val) Subtype.val_injective
      (fun z => hS z.val (Finset.mem_filter.mp z.property).1)
      (fun z => (Finset.mem_filter.mp z.property).2)
    simp_all
  have hG : G.card ≤ (S.image π).card := by
    apply Finset.card_le_card_of_injOn π
    · intro z hz
      grind
    · intro z hz w hw he
      obtain ⟨hzS, hzQ⟩ := Finset.mem_filter.mp hz
      obtain ⟨hwS, _⟩ := Finset.mem_filter.mp hw
      have hev (p : MvPolynomial σ K) : eval z (aeval a p) = eval w (aeval a p) := by
        change eval z (eval₂ C a p) = eval w (eval₂ C a p)
        rw [← eval_assoc, ← eval_assoc]
        change eval (fun j => eval z (a j)) p = eval (fun j => eval w (a j)) p
        grind
      funext i
      apply mul_left_cancel₀ hzQ
      have hz' := (hS z hzS) _ (hP i)
      have hw' := (hS w hwS) _ (hP i)
      simp only [eval_sub, eval_mul, eval_X, sub_eq_zero] at hz' hw'
      rw [hz', hev (P i), hev Q]
      exact hw'.symm
  have hcard : T.card + G.card = S.card := Finset.card_filter_add_card_filter_not _
  change S.card ≤ (S.image π).card + _
  omega

