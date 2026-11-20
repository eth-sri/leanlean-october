module

public import QPBT.Games.Sandwich.Defs

/-! # Quantitative support for sandwiched measurements

This module develops the consistency and operator-distance estimates used
in the quantitative sandwich argument.

## References

Blueprint `lem:ld-sandwich` and `lem:ld-sandwich-measurement`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

namespace SandwichProduct

section

variable {X α β ιA ιB : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
  (A : Measurement α ιA) (B : Measurement α ιB) (ψ : EuclideanSpace ℂ (ιA × ιB))

/-- The consistency defect of tensor-placed local measurements is the average
of their pointwise off-diagonal tensor overlap. This is the formalization-only
identity `lem:sandwich-placed-defect-expansion` used in the proof of
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:952-994`. -/
theorem consistencyDefect_placed_eq_avg_point
    (μ : Distribution X) (A : X → Measurement α ιA)
    (B : X → Measurement α ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    bipartiteDefect μ
        A
        B ψ =
      avgOver μ (fun x => ∑ a : α, ∑ a' : α, if a = a' then 0 else
        stateQForm ψ (heteroKron ((A x).effect a) ((B x).effect a'))) := by
  simp [bipartiteDefect]
  apply avgOver_congr
  intro x
  congr 1 with a
  congr 1 with a'
  by_cases haa' : a = a'
  · simp [haa']
  · rw [consistency_term_eq_stateQForm, placed_product_stateQForm_eq]

end

/-- The contribution of distinct codewords which have the same readout. -/
def collisionPart {Γ R : Type*} [Fintype Γ] [DecidableEq Γ] [DecidableEq R]
    (f : Γ → R) (w : Γ → Γ → ℝ) :=
  ∑ a, ∑ b, if a = b then 0 else if f a = f b then w a b else 0

theorem readout_agreement_eq {Γ R : Type*} [Fintype Γ] [DecidableEq Γ] [DecidableEq R]
    (f : Γ → R) (w : Γ → Γ → ℝ) :
    (∑ a, ∑ b, if f a = f b then w a b else 0) = ∑ a, w a a + collisionPart f w := by
  simp only [collisionPart, ← Finset.sum_add_distrib]
  congr 1 with a
  have hs (b : Γ) : (if f a = f b then w a b else 0) =
      (if a = b then w a b else 0) + (if a = b then 0 else if f a = f b then w a b else 0) := by
    by_cases h : a = b <;> simp [h]
  simp only [Finset.sum_congr rfl (fun b _ => hs b), Finset.sum_add_distrib]
  simp

/-- Average collision contribution for any nonnegative pair weights and any
(possibly unnormalized) law on evaluation points. -/
theorem weighted_collision_le {Γ Y R : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype Y] [DecidableEq R]
    (t : Y → ℝ) (eval : Γ → Y → R) (w : Γ → Γ → ℝ) {k : ℝ}
    (hw : ∀ a b, 0 ≤ w a b)
    (hk : ∀ a b, a ≠ b → (∑ y, t y * (if eval a y = eval b y then 1 else 0)) ≤ k) :
    (∑ y, t y * collisionPart (fun a => eval a y) w) ≤ (∑ a, ∑ b, if a = b then 0 else w a b) * k := by
  simp only [collisionPart, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases h : a = b
  · simp [h]
  · simpa [h, mul_ite, ite_mul, Finset.sum_mul, mul_comm (w a b)] using
      mul_le_mul_of_nonneg_right (hk a b h) (hw a b)

theorem placed_offdiag_eq {α I J : Type*} [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Measurement α I) (B : Measurement α J) (ψ : EuclideanSpace ℂ (I × J)) :
    (∑ a, ∑ b, if a = b then 0 else stateQForm ψ (heteroKron (A.effect a) (B.effect b))) =
      ‖ψ‖ ^ 2 - ∑ a, stateQForm ψ (heteroKron (A.effect a) (B.effect a)) := by
  simpa only [leftPlacedMeasurement, rightPlacedMeasurement, Measurement.ofSumEqOne,
    placed_product_stateQForm_eq] using point_defect_eq (leftPlacedMeasurement A) (rightPlacedMeasurement B) ψ

theorem placed_offdiag_le_one {α I J : Type*} [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Measurement α I) (B : Measurement α J) {ψ : EuclideanSpace ℂ (I × J)}
    (hψ : ‖ψ‖ = 1) : (∑ a, ∑ b, if a = b then 0 else stateQForm ψ (heteroKron (A.effect a) (B.effect b))) ≤ 1 := by
  rw [placed_offdiag_eq, hψ, one_pow]
  exact sub_le_self _ (Finset.sum_nonneg fun a _ => stateQForm_nonneg _ (kronecker_nonneg (A.pos a) (B.pos a)))

section

variable {Y Γ R ιA ιB : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype Γ]
  [DecidableEq Γ] [Fintype R] [DecidableEq R] [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
  [DecidableEq ιB] (A : Measurement Γ ιA) (B : Measurement Γ ιB)
  (ψ : EuclideanSpace ℂ (ιA × ιB)) (eval : Γ → Y → R) (ε : ℝ) (hψ : ‖ψ‖ = 1) (hε : 0 ≤ ε)

include hε hψ in
set_option maxHeartbeats 600000 in
-- The collision estimate expands two nested outcome sums at each evaluation point.
/-- Averaged diagonal overlap after evaluation exceeds the original diagonal
overlap by at most the collision probability. This is the formalization-only
estimate `lem:sandwich-evaluated-diagonal-overlap` used in the proof of
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:975-987`. -/
theorem avg_diagonal_postprocess_stateQForm_le
    (hcollision : ∀ g g' : Γ, g ≠ g' →
      avgOver (uniformDistribution Y)
        (fun y => if eval g y = eval g' y then 1 else 0) ≤ ε) :
    avgOver (uniformDistribution Y) (fun y =>
      ∑ r : R, stateQForm ψ
        (heteroKron
          ((A.postprocess (fun g => eval g y)).effect r)
          ((B.postprocess (fun g => eval g y)).effect r))) ≤
      (∑ g : Γ, stateQForm ψ (heteroKron (A.effect g) (B.effect g))) + ε := by
  simp_rw [diagonal_postprocess_stateQForm_eq_pair_sum, readout_agreement_eq]
  rw [avgOver_add, avgOver_uniform_const, avgOver_eq_sum_univ]
  apply add_le_add_right
  apply (weighted_collision_le _ _ _ (fun a b => stateQForm_nonneg ψ
    (kronecker_nonneg (A.pos a) (B.pos b))) (by simpa [avgOver_eq_sum_univ] using hcollision)).trans
  exact mul_le_of_le_one_left hε (placed_offdiag_le_one A B hψ)

include hε hψ in
set_option maxHeartbeats 600000 in
-- Complementary overlaps require simultaneous expansions before averaging.
/-- Taking complements converts the diagonal-overlap estimate into a
pointwise consistency-defect estimate. This is the formalization-only estimate
`lem:sandwich-point-codeword-defect` used in the proof of `lem:ld-sandwich`;
detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:975-987`. -/
theorem point_codeword_defect_le_avg_evaluated_add
    (hcollision : ∀ g g' : Γ, g ≠ g' →
      avgOver (uniformDistribution Y)
        (fun y => if eval g y = eval g' y then 1 else 0) ≤ ε) :
    (∑ g : Γ, ∑ g' : Γ, if g = g' then 0 else
      stateQForm ψ (heteroKron (A.effect g) (B.effect g'))) ≤
      avgOver (uniformDistribution Y) (fun y =>
        ∑ r : R, ∑ r' : R, if r = r' then 0 else
          stateQForm ψ
            (heteroKron
              ((A.postprocess (fun g => eval g y)).effect r)
              ((B.postprocess (fun g => eval g y)).effect r'))) + ε := by
  have hdiag_avg := avg_diagonal_postprocess_stateQForm_le
    A B ψ eval ε hψ hε hcollision
  simp_rw [placed_offdiag_eq, avgOver_sub, avgOver_uniform_const]
  linarith

end

set_option maxHeartbeats 600000 in
-- The proof rearranges question, evaluation, and two outcome sums.
/-- If distinct codewords collide under a random evaluation with probability
at most `ε`, their full-outcome consistency defect is at most the evaluated
defect plus `ε`. This is the formalization-only estimate
`lem:sandwich-codeword-defect` for the first step of `lem:ld-sandwich`;
detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:975-987`. -/
theorem consistencyDefect_codewords_le_evaluated_add
    {X Y Γ R ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Γ] [DecidableEq Γ] [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement Γ ιA)
    (B : X → Measurement Γ ιB) (ψ : EuclideanSpace ℂ (ιA × ιB))
    (eval : Γ → Y → R) (ε : ℝ)
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) (hε : 0 ≤ ε)
    (hcollision : ∀ g g' : Γ, g ≠ g' →
      avgOver (uniformDistribution Y)
        (fun y => if eval g y = eval g' y then 1 else 0) ≤ ε) :
    bipartiteDefect μ
        A
        B ψ ≤
      bipartiteDefect (Distribution.prod μ (uniformDistribution Y))
        (fun xy => (A xy.1).postprocess (fun g => eval g xy.2))
        (fun xy => (B xy.1).postprocess (fun g => eval g xy.2)) ψ + ε := by
  simp_rw [consistencyDefect_placed_eq_avg_point, avgOver_prod]
  have h := avgOver_mono μ _ _ fun x => point_codeword_defect_le_avg_evaluated_add
    (A x) (B x) ψ eval ε hψ hε hcollision
  simpa only [avgOver_add, avgOver_const_of_isProbability μ hμ] using h

variable {α β γ ι : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ]
  [DecidableEq γ] [Fintype ι] [DecidableEq ι] (M : Measurement α ι)
  (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (f : α → β) (hf : Function.Injective f)
  (b : β) (a : α)

include hM in
/-- Coarsening the outcomes of a projective measurement preserves
projectivity. This is the formalization-only fact
`lem:sandwich-postprocess-projective` used in the palindromic construction of
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem postprocess_isProjective : MIPStarRE.QPBT.Measurement.IsProjective (M.postprocess f) := by
  classical
  intro b
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · change _ =
      (M.postprocess f).effect b
    simp only [MIPStarRE.Quantum.Measurement.postprocess_effect]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    calc
      _ =
          ∑ a ∈ Finset.univ.filter (fun a => f a = b),
            ∑ a' ∈ Finset.univ.filter (fun a' => f a' = b),
              if a' = a then M.effect a else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro a' _
        by_cases haa' : a' = a
        · subst a'
          simp [(hM a).isIdempotentElem.eq]
        · rw [if_neg haa']
          solve_by_elim [DistanceCalculus.projective_effect_mul_effect_eq_zero]
      _ = _ := by
        simp_all
  · exact
      (Matrix.nonneg_iff_posSemidef.mp ((M.postprocess f).pos b)).isHermitian.eq

include hf in
/-- An injective relabeling does not merge the effect at a relabeled
outcome. This is the formalization-only identity
`lem:sandwich-injective-postprocess` used to identify product outcomes in
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem postprocess_effect_of_injective :
    (M.postprocess f).effect (f a) = M.effect a := by
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  rw [Fintype.sum_eq_single a]
  · simp
  · intro z hza
    rw [if_neg]
    grind

include hM in
/-- A projective joint effect selects its matching postprocessing fiber when
multiplied on the right. This is the formalization-only identity
`lem:sandwich-postprocess-effect-right` used in the joint-family comparison for
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem effect_mul_postprocess_effect :
    M.effect a * (M.postprocess f).effect b =
      if f a = b then M.effect a else 0 := by
  have h := congrArg Matrix.conjTranspose
    (DistanceCalculus.postprocess_effect_mul_effect M hM f b a)
  rw [Matrix.conjTranspose_mul,
    measurement_effect_hermitian M a,
    measurement_effect_hermitian (M.postprocess f) b] at h
  by_cases hab : f a = b
  · simpa [hab, measurement_effect_hermitian M a] using h
  · simpa [hab] using h

end SandwichProduct

end MIPStarRE.QPBT
