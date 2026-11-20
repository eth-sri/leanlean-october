module

public import QPBT.Games.DistanceTheorems
public import QPBT.Games.DistributionAux
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
      avgOver μ (fun x => avgOver ν (fun y => f (x, y))) :=
  Distribution.avgOver_prod μ ν f

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
    bipartiteDefect μ
        A
        B ψ =
      avgOver μ (fun x => ∑ a : α, ∑ a' : α, if a = a' then 0 else
        stateQForm ψ (heteroKron ((A x).effect a) ((B x).effect a'))) := by
  simp only [bipartiteDefect, consistencyDefect, placed_product_stateQForm_eq]

section

variable {Y Γ R ιA ιB : Type*}
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Γ] [DecidableEq Γ] [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement Γ ιA) (B : Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (eval : Γ → Y → R) (ε : ℝ)
    (hψ : ‖ψ‖ = 1) (hε : 0 ≤ ε)
    (hcollision : ∀ g g' : Γ, g ≠ g' →
      avgOver (uniformDistribution Y)
        (fun y => if eval g y = eval g' y then 1 else 0) ≤ ε)
include Y Γ R ιA ιB A B ψ eval ε hψ hε hcollision

set_option maxHeartbeats 600000 in
-- The collision estimate expands two nested outcome sums at each evaluation point.
/-- Averaged diagonal overlap after evaluation exceeds the original diagonal
overlap by at most the collision probability. This is the formalization-only
estimate `lem:sandwich-evaluated-diagonal-overlap` used in the proof of
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:975-987`. -/
theorem avg_diagonal_postprocess_stateQForm_le :
    avgOver (uniformDistribution Y) (fun y =>
      ∑ r : R, stateQForm ψ
        (heteroKron
          ((A.postprocess (fun g => eval g y)).effect r)
          ((B.postprocess (fun g => eval g y)).effect r))) ≤
      (∑ g : Γ, stateQForm ψ (heteroKron (A.effect g) (B.effect g))) + ε := by
  classical
  let w : Γ → Γ → ℝ := fun g g' =>
    stateQForm ψ (heteroKron (A.effect g) (B.effect g'))
  have hw (g g' : Γ) : 0 ≤ w g g' := by
    apply stateQForm_nonneg
    exact MIPStarRE.Quantum.kronecker_nonneg (A.pos g) (B.pos g')
  change _ ≤ (∑ g : Γ, w g g) + ε
  simp_rw [diagonal_postprocess_stateQForm_eq_pair_sum, avgOver_sum]
  refine le_trans (b := ∑ g, ∑ g', (if g = g' then 1 else ε) * w g g') ?_ ?_
  · refine Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun g' _ => ?_
    rw [avgOver_ite_const]
    apply mul_le_mul_of_nonneg_right _ (hw g g')
    by_cases h : g = g'
    · subst g'
      simp [avgOver_uniform_const]
    · simpa only [if_neg h] using hcollision g g' h
  · rw [sum_diagWeighted, show (∑ g, ∑ g', w g g') = 1 by
      simp [w, sum_tensor_effect_stateQForm, hψ]]
    nlinarith [mul_nonneg hε (Finset.sum_nonneg (s := Finset.univ) fun g _ => hw g g)]

set_option maxHeartbeats 600000 in
-- Complementary overlaps require simultaneous expansions before averaging.
/-- Taking complements converts the diagonal-overlap estimate into a
pointwise consistency-defect estimate. This is the formalization-only estimate
`lem:sandwich-point-codeword-defect` used in the proof of `lem:ld-sandwich`;
detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:975-987`. -/
theorem point_codeword_defect_le_avg_evaluated_add :
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
  simp only [leftPlacedMeasurement_effect, rightPlacedMeasurement_effect] at hfull
  simp_rw [placed_product_stateQForm_eq] at hfull
  have hevaluated (y : Y) := point_defect_eq
    (leftPlacedMeasurement (ιB := ιB)
      (A.postprocess (fun g => eval g y)))
    (rightPlacedMeasurement (ιA := ιA)
      (B.postprocess (fun g => eval g y))) ψ
  simp only [leftPlacedMeasurement_effect, rightPlacedMeasurement_effect] at hevaluated
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
  rw [hfull, hψ, one_pow, heval_avg]
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
  simp only [bipartiteDefect, consistencyDefect, placed_product_stateQForm_eq,
    Distribution.avgOver_prod]
  rw [← avgOver_const_of_isProbability μ hμ ε, ← avgOver_add]
  exact avgOver_mono _ _ _ fun x =>
    point_codeword_defect_le_avg_evaluated_add (A x) (B x) ψ eval ε hψ hε hcollision

section

variable {α β ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι)

/-- Coarsening the outcomes of a projective measurement preserves
projectivity. This is the formalization-only fact
`lem:sandwich-postprocess-projective` used in the palindromic construction of
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem postprocess_isProjective (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : α → β) : MIPStarRE.QPBT.Measurement.IsProjective (M.postprocess f) := by
  intro b
  refine ⟨?_, measurement_effect_hermitian _ _⟩
  change (M.postprocess f).effect b * (M.postprocess f).effect b = _
  conv_lhs => arg 2; rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  rw [Finset.mul_sum]
  conv_rhs => rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [postprocess_effect_mul_effect M hM, if_pos (Finset.mem_filter.mp ha).2]

/-- Postprocessing includes the original effect in its new outcome's fiber. -/
theorem effect_le_postprocess_effect {α β I : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype I] [DecidableEq I]
    (M : Measurement α I) (f : α → β) (a : α) : M.effect a ≤ (M.postprocess f).effect (f a) := by
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  exact Finset.single_le_sum (fun b _ => M.pos b) (by simp)

/-- Relabeling a measurement gives zero effect to outcomes outside the image. -/
theorem postprocess_effect_eq_zero_of_notMem
    {α β V : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Fintype V] [DecidableEq V]
    (M : MIPStarRE.Quantum.Measurement α V) (f : α → β) {b : β}
    (hb : b ∉ Set.range f) :
    (M.postprocess f).effect b = 0 := by
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp_all

/-- An injective relabeling does not merge the effect at a relabeled
outcome. This is the formalization-only identity
`lem:sandwich-injective-postprocess` used to identify product outcomes in
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem postprocess_effect_of_injective (f : α → β) (hf : Function.Injective f) (a : α) :
    (M.postprocess f).effect (f a) = M.effect a := by
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  rw [Fintype.sum_eq_single a]
  · simp
  · intro z hza
    rw [if_neg]
    exact fun h => hza (hf h)

end

section

variable {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι)
include α ι M

/-- Completing an outcome space by `none` preserves its original effects. -/
theorem postprocess_some_effect (a : α) : (M.postprocess some).effect (some a) = M.effect a :=
  postprocess_effect_of_injective M some (Option.some_injective _) a

/-- The extra outcome of this completion has zero effect. -/
theorem postprocess_some_effect_none : (M.postprocess some).effect none = 0 :=
  postprocess_effect_eq_zero_of_notMem M some (by simp)

end

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
  · simpa [hab, DistanceCalculus.measurement_effect_hermitian M a] using h
  · simpa [hab] using h

end SandwichProduct

end MIPStarRE.QPBT
