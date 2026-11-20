module

public import QPBT.Games.Sandwich.Pasting.CodewordConsistency
public import QPBT.Games.Sandwich.Pasting.OverlapCalculus

/-! # The pinched reduction of the pasting estimate -/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus Pasting

section

variable {R Γ I : Type*} [Fintype R] [Fintype Γ]
    [Fintype I] [DecidableEq I] (P : Measurement R I) (G : Measurement Γ I)
    (hG : QPBT.Measurement.IsProjective G)
include R Γ I P G hG

private noncomputable def pinchedMeasurement : Measurement R I :=
  Measurement.ofSumEqOne (fun a => pinchOp G (P.effect a))
    (fun a => pinchOp_nonneg G (P.pos a)) (by
      rw [← pinchOp_sum, P.sum_eq_one, pinchOp_one_of_projective G hG])

/-- The full POVM of X-then-Z ordered sandwich effects. -/
noncomputable def pastedPOVM : Measurement (R × Γ) I :=
  Measurement.ofSumEqOne (fun ag => pastedMeasurement P.effect G.effect ag.1 ag.2)
    (fun ag => by
      simpa only [pastedMeasurement, measurement_effect_hermitian] using
        Matrix.nonneg_iff_posSemidef.mpr
          ((Matrix.nonneg_iff_posSemidef.mp (P.pos ag.1)).conjTranspose_mul_mul_same
            (G.effect ag.2))) (by
      rw [Fintype.sum_prod_type]
      exact (pinchedMeasurement P G hG).sum_eq_one)

end

private theorem pasted_marginal {R Γ Ω I : Type*} [Fintype R] [DecidableEq R]
    [Fintype Γ] [DecidableEq Γ] [Fintype Ω] [DecidableEq Ω] [Fintype I] [DecidableEq I]
    (P : Measurement R I) (G : Measurement Γ I) (hG : QPBT.Measurement.IsProjective G)
    (f : Γ → Ω) (b : Ω) :
    ((pastedPOVM P G hG).postprocess (f ∘ Prod.snd)).effect b = (G.postprocess f).effect b := by
  simp only [Measurement.postprocess_effect, Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  dsimp only [Function.comp_apply]
  by_cases h : f g = b <;> simp only [h, if_true, if_false, Finset.sum_const_zero,
    pastedPOVM, pastedMeasurement, Measurement.ofSumEqOne, ← Finset.sum_mul,
    ← Finset.mul_sum, P.sum_eq_one, mul_one, (hG g).isIdempotentElem.eq]

/-- Disagreement of paired answers is bounded by the sum of marginal disagreements. -/
private theorem consistencyDefect_pair_le {X R S I J : Type*}
    [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (D : Distribution X) (A : X → Measurement (R × S) I) (B : X → Measurement (R × S) J)
    (ψ : EuclideanSpace ℂ (I × J)) :
    bipartiteDefect D A B ψ ≤
    bipartiteDefect D (fun x => (A x).postprocess Prod.snd)
        (fun x => (B x).postprocess Prod.snd) ψ +
    bipartiteDefect D (fun x => (A x).postprocess Prod.fst)
        (fun x => (B x).postprocess Prod.fst) ψ := by
  rw [SandwichProduct.consistencyDefect_placed_eq_avg_point D A B,
    SandwichProduct.consistencyDefect_placed_eq_avg_point D
      (fun x => (A x).postprocess Prod.snd) (fun x => (B x).postprocess Prod.snd),
    SandwichProduct.consistencyDefect_placed_eq_avg_point D
      (fun x => (A x).postprocess Prod.fst) (fun x => (B x).postprocess Prod.fst), ← avgOver_add]
  apply avgOver_mono
  intro x
  rw [point_placed_defect_postprocess, point_placed_defect_postprocess]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  have h : 0 ≤ stateQForm ψ (heteroKron ((A x).effect a) ((B x).effect b)) :=
    stateQForm_nonneg ψ (kronecker_nonneg ((A x).pos a) ((B x).pos b))
  by_cases ha : a.1 = b.1 <;> by_cases hb : a.2 = b.2 <;> simp [ha, hb, h, Prod.ext_iff]

section EvaluatedPasting

variable {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype Γ₁] [DecidableEq Γ₁]
    [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]

/-- Evaluate the two polynomial outcomes of a pasted POVM at their sampled points. -/
noncomputable def pastedEvaluation
    (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₁ : X → Measurement Γ₁ ι) (G₂ : X → Measurement Γ₂ ι)
    (hG₂ : ∀ x, QPBT.Measurement.IsProjective (G₂ x)) (q : (X × Y₁) × Y₂) :=
  (pastedPOVM (G₁ q.1.1) (G₂ q.1.1) (hG₂ q.1.1)).postprocess
    (fun g => (eval₁ g.1 q.1.2, eval₂ g.2 q.2))

set_option maxHeartbeats 500000 in
-- The postprocessed block comparison expands two nested outcome sums.
/-- The pasted family can be checked using its two marginals. -/
theorem consistencyDefect_pasted_le_marginal_add_pinched
    (D : Distribution ((X × Y₁) × Y₂))
    (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₁ : X → Measurement Γ₁ ι) (G₂ : X → Measurement Γ₂ ι)
    (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ι)
    (ψ : EuclideanSpace ℂ (ι × ι))
    (hG₂ : ∀ x, QPBT.Measurement.IsProjective (G₂ x)) :
    bipartiteDefect D A (pastedEvaluation eval₁ eval₂ G₁ G₂ hG₂) ψ ≤
      bipartiteDefect D
        (fun q => (A q).postprocess Prod.snd)
        (fun q => (G₂ q.1.1).postprocess
          (fun g => eval₂ g q.2)) ψ +
      consistencyDefect D
        (fun q a₁ => heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
        (fun q a₁ => heteroKron 1 (∑ g : Γ₂, (G₂ q.1.1).effect g *
          ((G₁ q.1.1).postprocess (fun g' => eval₁ g' q.1.2)).effect a₁ *
          (G₂ q.1.1).effect g)) ψ := by
  classical
  let B := pastedEvaluation eval₁ eval₂ G₁ G₂ hG₂
  have h := consistencyDefect_pair_le D A B ψ
  have hfst (q : (X × Y₁) × Y₂) (a : R₁) : ((B q).postprocess Prod.fst).effect a =
      ∑ g : Γ₂, (G₂ q.1.1).effect g *
        (((G₁ q.1.1).postprocess (fun g' => eval₁ g' q.1.2)).effect a) * (G₂ q.1.1).effect g := by
    simp only [B, pastedEvaluation, Measurement.postprocess_comp, Measurement.postprocess_effect, Finset.sum_filter,
      Fintype.sum_prod_type, pastedPOVM, Measurement.ofSumEqOne, pastedMeasurement]
    rw [Finset.sum_comm]
    simp [Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul]
  have hsnd (q : (X × Y₁) × Y₂) (a : R₂) : ((B q).postprocess Prod.snd).effect a =
      ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect a := by
    dsimp only [B, pastedEvaluation]
    rw [Measurement.postprocess_comp]
    exact pasted_marginal (G₁ q.1.1) (G₂ q.1.1) (hG₂ q.1.1) (fun g => eval₂ g q.2) a
  simpa only [bipartiteDefect, hfst, hsnd] using! h

end EvaluatedPasting

/-- Pinching increases the first marginal defect by at most the square root of
its commutator mass with the fine projective measurement. -/
theorem consistencyDefect_pinched_le_marginal_add_sqrt
    {X Y₁ Y₂ R₁ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
    (D : Distribution ((X × Y₁) × Y₂)) (G₂ : X → Measurement Γ₂ ι)
    (P A : ((X × Y₁) × Y₂) → Measurement R₁ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (K : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1)
    (hG₂ : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (G₂ x))
    (hK : avgOver D (fun q => ∑ a : R₁, ∑ g : Γ₂,
      ‖applyOperatorToState (heteroKron 1 ((P q).effect a * (G₂ q.1.1).effect g -
        (G₂ q.1.1).effect g * (P q).effect a)) ψ‖ ^ 2) ≤ K) :
    consistencyDefect D (fun q a => heteroKron ((A q).effect a) 1)
        (fun q a => heteroKron 1 (∑ g : Γ₂, (G₂ q.1.1).effect g * (P q).effect a *
          (G₂ q.1.1).effect g)) ψ ≤
      bipartiteDefect D A P ψ + Real.sqrt K := by
  classical
  let M := fun q => pinchedMeasurement (P q) (G₂ q.1.1) (hG₂ q.1.1)
  let T := fun q => tensorMeasurement (A q) (G₂ q.1.1)
  let C (q : (X × Y₁) × Y₂) (ag : R₁ × Γ₂) : Op (ι × ι) := heteroKron 1
    ((P q).effect ag.1 * (G₂ q.1.1).effect ag.2 - (G₂ q.1.1).effect ag.2 * (P q).effect ag.1)
  have hm := measurement_mass_le_one D T ψ hD hψ
  have habs := abs_overlap_le_sqrt D C (fun q ag => (T q).effect ag) ψ
    (by simpa only [opFamilyDistSq, sub_zero, C, Fintype.sum_prod_type] using hK) hm
  rw [overlap_symm] at habs
  let w (N : ((X × Y₁) × Y₂) → Measurement R₁ ι) :=
    avgOver D (fun q => ∑ a, stateQForm ψ (heteroKron ((A q).effect a) ((N q).effect a)))
  have hdiff : overlap D (fun q ag => (T q).effect ag) C ψ = w M - w P := by
    unfold overlap w
    rw [← avgOver_sub]
    apply avgOver_congr
    intro q
    simp only [T, tensorMeasurement, Measurement.ofSumEqOne, C, M, pinchedMeasurement,
      Fintype.sum_prod_type, heteroKron_conjTranspose, measurement_effect_hermitian,
      heteroKron_mul, mul_one, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp_rw [← stateQForm_finset_sum, ← heteroKron_finset_sum_right, ← stateQForm_sub,
      ← heteroKron_sub_right]
    congr 2
    simp_rw [mul_sub, ← mul_assoc, fun g => (hG₂ q.1.1 g).isIdempotentElem.eq,
      Finset.sum_sub_distrib, ← Finset.sum_mul, (G₂ q.1.1).sum_eq_one, one_mul, pinchOp]
  rw [hdiff] at habs
  change bipartiteDefect D A M ψ ≤ _
  rw [consistencyDefect_placed_eq_one_sub_overlap D A M ψ hD hψ,
    consistencyDefect_placed_eq_one_sub_overlap D A P ψ hD hψ]
  change 1 - w M ≤ 1 - w P + _
  linarith [(neg_le_abs (w M - w P)).trans habs]

end MIPStarRE.QPBT
