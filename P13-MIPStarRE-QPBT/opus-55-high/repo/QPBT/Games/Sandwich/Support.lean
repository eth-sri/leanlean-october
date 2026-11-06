module

public import QPBT.Games.DistanceTheorems
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

/-- Averaging over the product of two finite distributions is iterated
averaging. This is the formalization-only identity
`lem:sandwich-product-average` used in the proof of `lem:ld-sandwich`; detailed
source argument `references/neexp-paper/05_quantum_preliminaries.tex:952-994`. -/
theorem avgOver_distribution_prod {X Y : Type*}
    [DecidableEq X] [DecidableEq Y] (μ : Distribution X) (ν : Distribution Y)
    (f : X × Y → ℝ) :
    avgOver (Distribution.prod μ ν) f =
      avgOver μ (fun x => avgOver ν (fun y => f (x, y))) := by
  unfold avgOver
  calc
    (∑ p ∈ μ.support.product ν.support,
        (μ.weight p.1 * ν.weight p.2) * f p) =
        ∑ x ∈ μ.support, ∑ y ∈ ν.support,
          (μ.weight x * ν.weight y) * f (x, y) := by
      exact Finset.sum_product' μ.support ν.support
        (fun x y => (μ.weight x * ν.weight y) * f (x, y))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      grind

/-- The diagonal overlap after a common relabeling is the sum over pairs of
original outcomes with equal labels. This is the formalization-only identity
`lem:sandwich-diagonal-postprocess` used in the proof of `lem:ld-sandwich`;
detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:952-994`. -/
theorem diagonal_postprocess_stateQForm_eq_pair_sum
    {α β ιA ιB : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α ιA) (B : Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (f : α → β) :
    (∑ b : β, stateQForm ψ
      (heteroKron ((A.postprocess f).effect b) ((B.postprocess f).effect b))) =
      ∑ a : α, ∑ a' : α, if f a = f a' then
        stateQForm ψ (heteroKron (A.effect a) (B.effect a')) else 0 := by
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, heteroKron_finset_sum_left,
    heteroKron_finset_sum_right, stateQForm_finset_sum]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp
  exact Finset.sum_comm

/-- The consistency defect of tensor-placed local measurements is the average
of their pointwise off-diagonal tensor overlap. This is the formalization-only
identity `lem:sandwich-placed-defect-expansion` used in the proof of
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:952-994`. -/
theorem consistencyDefect_placed_eq_avg_point
    {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA)
    (B : X → Measurement α ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    consistencyDefect μ
        (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ =
      avgOver μ (fun x => ∑ a : α, ∑ a' : α, if a = a' then 0 else
        stateQForm ψ (heteroKron ((A x).effect a) ((B x).effect a'))) := by
  refine avgOver_congr _ _ _ fun x => Fintype.sum_congr _ _ fun a => Fintype.sum_congr _ _ fun a' => ?_
  split_ifs
  · rfl
  · rw [consistency_term_eq_stateQForm, placed_product_stateQForm_eq]

-- The collision estimate expands two nested outcome sums at each evaluation point.
/-- Averaged diagonal overlap after evaluation exceeds the original diagonal
overlap by at most the collision probability. This is the formalization-only
estimate `lem:sandwich-evaluated-diagonal-overlap` used in the proof of
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:975-987`. -/
theorem avg_diagonal_postprocess_stateQForm_le
    {Y Γ R ιA ιB : Type*}
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Γ] [DecidableEq Γ] [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement Γ ιA) (B : Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (eval : Γ → Y → R) (ε : ℝ)
    (hψ : ‖ψ‖ = 1) (hε : 0 ≤ ε)
    (hcollision : ∀ g g' : Γ, g ≠ g' →
      avgOver (uniformDistribution Y)
        (fun y => if eval g y = eval g' y then 1 else 0) ≤ ε) :
    avgOver (uniformDistribution Y) (fun y =>
      ∑ r : R, stateQForm ψ
        (heteroKron
          ((A.postprocess (fun g => eval g y)).effect r)
          ((B.postprocess (fun g => eval g y)).effect r))) ≤
      (∑ g : Γ, stateQForm ψ (heteroKron (A.effect g) (B.effect g))) + ε := by
  let w : Γ → Γ → ℝ := fun g g' =>
    stateQForm ψ (heteroKron (A.effect g) (B.effect g'))
  have hw (g g' : Γ) : 0 ≤ w g g' :=
    stateQForm_nonneg _ (MIPStarRE.Quantum.kronecker_nonneg (A.pos g) (B.pos g'))
  have hpoint := point_defect_eq (leftPlacedMeasurement (ιB := ιB) A)
    (rightPlacedMeasurement (ιA := ιA) B) ψ
  simp only [leftPlacedMeasurement, rightPlacedMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne, placed_product_stateQForm_eq, hψ] at hpoint
  have hO : (∑ g : Γ, ∑ g' : Γ, if g = g' then 0 else w g g') ≤ 1 :=
    hpoint.trans_le (by linarith [Finset.sum_nonneg fun g (_ : g ∈ Finset.univ) => hw g g])
  simp_rw [diagonal_postprocess_stateQForm_eq_pair_sum, avgOver_sum]
  calc
    _ ≤ ∑ g : Γ, ∑ g' : Γ, ((if g = g' then w g g' else 0) +
        ε * if g = g' then 0 else w g g') := by
      gcongr with g _ g' _
      split_ifs with h
      · subst h; simp [w, avgOver_uniform_const]
      · simp only [zero_add, ← boole_mul _ (stateQForm ψ _)]
        rw [avgOver_mul_const]
        exact mul_le_mul_of_nonneg_right (hcollision g g' h) (hw g g')
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left hO hε
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true]
      linarith

-- Complementary overlaps require simultaneous expansions before averaging.
/-- Taking complements converts the diagonal-overlap estimate into a
pointwise consistency-defect estimate. This is the formalization-only estimate
`lem:sandwich-point-codeword-defect` used in the proof of `lem:ld-sandwich`;
detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:975-987`. -/
theorem point_codeword_defect_le_avg_evaluated_add
    {Y Γ R ιA ιB : Type*}
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Γ] [DecidableEq Γ] [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement Γ ιA) (B : Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (eval : Γ → Y → R) (ε : ℝ)
    (hψ : ‖ψ‖ = 1) (hε : 0 ≤ ε)
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
  have hfull := point_defect_eq
    (leftPlacedMeasurement (ιB := ιB) A)
    (rightPlacedMeasurement (ιA := ιA) B) ψ
  simp only [leftPlacedMeasurement, rightPlacedMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne] at hfull
  simp_rw [placed_product_stateQForm_eq] at hfull
  have hevaluated (y : Y) := point_defect_eq
    (leftPlacedMeasurement (ιB := ιB)
      (A.postprocess (fun g => eval g y)))
    (rightPlacedMeasurement (ιA := ιA)
      (B.postprocess (fun g => eval g y))) ψ
  simp only [leftPlacedMeasurement, rightPlacedMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne] at hevaluated
  simp_rw [placed_product_stateQForm_eq] at hevaluated
  have heval_avg : avgOver (uniformDistribution Y) (fun y =>
      ∑ r : R, ∑ r' : R, if r = r' then 0 else
        stateQForm ψ
          (heteroKron
            ((A.postprocess (fun g => eval g y)).effect r)
            ((B.postprocess (fun g => eval g y)).effect r'))) =
      1 - avgOver (uniformDistribution Y) (fun y =>
        ∑ r : R, stateQForm ψ
          (heteroKron
            ((A.postprocess (fun g => eval g y)).effect r)
            ((B.postprocess (fun g => eval g y)).effect r))) := by
    simp_rw [hevaluated]
    rw [avgOver_sub, avgOver_uniform_const]
    rw [hψ]
    norm_num
  grind [one_pow]

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
    consistencyDefect μ
        (fun x g => heteroKron ((A x).effect g) 1)
        (fun x g => heteroKron 1 ((B x).effect g)) ψ ≤
      consistencyDefect (Distribution.prod μ (uniformDistribution Y))
        (fun xy r => heteroKron
          (((A xy.1).postprocess (fun g => eval g xy.2)).effect r) 1)
        (fun xy r => heteroKron 1
          (((B xy.1).postprocess (fun g => eval g xy.2)).effect r)) ψ + ε := by
  let w : X → Γ → Γ → ℝ := fun x g g' =>
    stateQForm ψ (heteroKron ((A x).effect g) ((B x).effect g'))
  have hpoint (x : X) :
      (∑ g : Γ, ∑ g' : Γ, if g = g' then 0 else w x g g') ≤
        avgOver (uniformDistribution Y) (fun y =>
          ∑ r : R, ∑ r' : R, if r = r' then 0 else
            stateQForm ψ
              (heteroKron
                (((A x).postprocess (fun g => eval g y)).effect r)
                (((B x).postprocess (fun g => eval g y)).effect r'))) + ε := by
    exact point_codeword_defect_le_avg_evaluated_add
      (A x) (B x) ψ eval ε hψ hε hcollision
  rw [consistencyDefect_placed_eq_avg_point μ A B]
  rw [consistencyDefect_placed_eq_avg_point
    (Distribution.prod μ (uniformDistribution Y))
    (fun xy => (A xy.1).postprocess (fun g => eval g xy.2))
    (fun xy => (B xy.1).postprocess (fun g => eval g xy.2))]
  rw [avgOver_distribution_prod]
  calc
    avgOver μ (fun x =>
        ∑ g : Γ, ∑ g' : Γ, if g = g' then 0 else w x g g') ≤
        avgOver μ (fun x =>
          avgOver (uniformDistribution Y) (fun y =>
            ∑ r : R, ∑ r' : R, if r = r' then 0 else
              stateQForm ψ
                (heteroKron
                  (((A x).postprocess (fun g => eval g y)).effect r)
                  (((B x).postprocess (fun g => eval g y)).effect r'))) + ε) := by
      apply avgOver_mono
      exact hpoint
    _ = avgOver μ (fun x =>
          avgOver (uniformDistribution Y) (fun y =>
            ∑ r : R, ∑ r' : R, if r = r' then 0 else
              stateQForm ψ
                (heteroKron
                  (((A x).postprocess (fun g => eval g y)).effect r)
                  (((B x).postprocess (fun g => eval g y)).effect r')))) +
        avgOver μ (fun _ => ε) := avgOver_add _ _ _
    _ = _ := by simp_all [avgOver_const_of_isProbability]

/-- Coarsening the outcomes of a projective measurement preserves
projectivity. This is the formalization-only fact
`lem:sandwich-postprocess-projective` used in the palindromic construction of
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem postprocess_isProjective {α β ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : α → β) : MIPStarRE.QPBT.Measurement.IsProjective (M.postprocess f) := by
  intro b
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · change (M.postprocess f).effect b * (M.postprocess f).effect b =
      (M.postprocess f).effect b
    simp only [MIPStarRE.Quantum.Measurement.postprocess_effect]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    calc
      (∑ a ∈ Finset.univ.filter (fun a => f a = b),
          ∑ a' ∈ Finset.univ.filter (fun a' => f a' = b),
            M.effect a * M.effect a') =
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
        simp_all [DistanceCalculus.projective_effect_mul_effect_eq_zero, Ne.symm]
      _ = ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a := by
        simp_all
  · exact
      (Matrix.nonneg_iff_posSemidef.mp ((M.postprocess f).pos b)).isHermitian.eq

/-- Performing two outcome relabelings has the same effects as their
composition. This is the formalization-only identity
`lem:sandwich-postprocess-compose` used to align the coordinate marginals in
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:952-994`. It reads at a
single outcome the equality of the twice-relabeled measurement with the
measurement relabeled along the composite map. -/
theorem postprocess_postprocess_effect {α β γ ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (f : α → β) (g : β → γ) (c : γ) :
    ((M.postprocess f).postprocess g).effect c =
      (M.postprocess (fun a => g (f a))).effect c := by
  rw [MIPStarRE.Quantum.Measurement.postprocess_comp]

/-- An injective relabeling does not merge the effect at a relabeled
outcome. This is the formalization-only identity
`lem:sandwich-injective-postprocess` used to identify product outcomes in
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem postprocess_effect_of_injective {α β ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (f : α → β) (hf : Function.Injective f) (a : α) :
    (M.postprocess f).effect (f a) = M.effect a := by
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  rw [Fintype.sum_eq_single a]
  · simp
  grind

/-- A projective joint effect selects its matching postprocessing fiber when
multiplied on the right. This is the formalization-only identity
`lem:sandwich-postprocess-effect-right` used in the joint-family comparison for
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem effect_mul_postprocess_effect {α β ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : α → β) (b : β) (a : α) :
    M.effect a * (M.postprocess f).effect b =
      if f a = b then M.effect a else 0 := by
  have h := congrArg Matrix.conjTranspose
    (DistanceCalculus.postprocess_effect_mul_effect M hM f b a)
  rw [Matrix.conjTranspose_mul,
    DistanceCalculus.measurement_effect_hermitian M a,
    DistanceCalculus.measurement_effect_hermitian (M.postprocess f) b] at h
  by_cases hab : f a = b
  · simp_all [DistanceCalculus.measurement_effect_hermitian]
  simp_all

end SandwichProduct

theorem consistencyDefect_placed_eq_one_sub
    {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA)
    (B : X → α → Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB))
    (hψ : ‖ψ‖ = 1) (hB : ∀ x, ∑ a, B x a = 1) :
    consistencyDefect μ
        (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 (B x a)) ψ =
      avgOver μ (fun x => 1 - ∑ a, stateQForm ψ (heteroKron ((A x).effect a) (B x a))) := by
  refine avgOver_congr μ _ _ fun x => ?_
  simp only [consistency_term_eq_stateQForm, placed_product_stateQForm_eq, sum_if_eq_zero_else,
    Finset.sum_sub_distrib, ← stateQForm_finset_sum, ← heteroKron_finset_sum_right, hB,
    ← heteroKron_finset_sum_left, (A x).sum_eq_one, heteroKron_one_one, stateQForm_one, hψ]
  norm_num

end MIPStarRE.QPBT
