module

public import QPBT.Games.Sandwich.Pasting.CodewordConsistency

/-! # The pinched reduction of the pasting estimate

This module records step 1 of the proof of the adopted statement of
`lem:pasting`: the defect of the pasted family is at most the defect of the
second marginal comparison plus the pinched defect.

## References

`lem:pasting` in `blueprint/src/chapter/ch12_qpbt_games.tex:960-990`, with the
proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

variable {X α β γ δ ιA ι : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
  [Fintype ι] [DecidableEq ι] [Fintype ιA] [DecidableEq ιA]

/-- Joint POVM obtained by measuring `G` and then `P`. -/
noncomputable def pastedPOVM (P : Measurement α ι) {G : Measurement β ι}
    (hG : Measurement.IsProjective G) : Measurement (α × β) ι :=
  Measurement.ofSumEqOne (fun ab => pastedMeasurement P.effect G.effect ab.1 ab.2)
    (fun ab => effect_sandwich_nonneg G ab.2 (P.pos ab.1))
    (by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [pastedMeasurement, ← Finset.sum_mul, ← Finset.mul_sum, P.sum_eq_one,
        mul_one, fun b => (hG b).isIdempotentElem.eq, G.sum_eq_one])

variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
  (P : Measurement α ι) {G : Measurement β ι} (hG : Measurement.IsProjective G)
  (f : α → γ) (g : β → δ)

noncomputable def pinchedPOVM := (pastedPOVM P hG).postprocess Prod.fst

noncomputable def evalPasted := (pastedPOVM P hG).postprocess (Prod.map f g)

theorem pinchedPOVM_effect (a : α) :
    (pinchedPOVM P hG).effect a = ∑ b, G.effect b * P.effect a * G.effect b := by
  simp only [pinchedPOVM, Measurement.postprocess_effect, Finset.sum_filter,
    Fintype.sum_prod_type, pastedPOVM, Measurement.ofSumEqOne, pastedMeasurement]
  rw [Finset.sum_comm]
  simp

theorem evalPasted_effect (v : γ × δ) :
    (evalPasted P hG f g).effect v = ∑ a, ∑ b, if (f a, g b) = v then
      pastedMeasurement P.effect G.effect a b else 0 := by
  simp only [evalPasted, Measurement.postprocess_effect, Finset.sum_filter,
    Fintype.sum_prod_type, pastedPOVM, Measurement.ofSumEqOne, Prod.map_apply]

theorem evalPasted_fst : (evalPasted P hG f g).postprocess Prod.fst =
    pinchedPOVM (P.postprocess f) hG := by
  rw [evalPasted, Measurement.postprocess_comp]
  apply Quantum.Measurement.ext
  intro v
  simp only [pinchedPOVM_effect, Measurement.postprocess_effect, Finset.sum_filter,
    Fintype.sum_prod_type, pastedPOVM, Measurement.ofSumEqOne, Prod.map_apply, pastedMeasurement]
  rw [Finset.sum_comm]
  congr 1 with b
  simp [Finset.mul_sum, Finset.sum_mul, apply_ite]

theorem evalPasted_snd : (evalPasted P hG f g).postprocess Prod.snd = G.postprocess g := by
  rw [evalPasted, Measurement.postprocess_comp]
  apply Quantum.Measurement.ext
  intro v
  simp only [Measurement.postprocess_effect, Finset.sum_filter, Fintype.sum_prod_type,
    pastedPOVM, Measurement.ofSumEqOne, Prod.map_apply, pastedMeasurement]
  rw [Finset.sum_comm]
  congr 1 with b
  split_ifs <;> simp [*, ← Finset.sum_mul, ← Finset.mul_sum, P.sum_eq_one, (hG b).isIdempotentElem.eq]

variable [Fintype X] [DecidableEq X] {D : Distribution X} {ψ : EuclideanSpace ℂ (ιA × ι)}

/-- Union bound on disagreement of two pairs of classical readouts. -/
theorem bipartiteDefect_pair_le (A : X → Measurement (α × β) ιA) (B : X → Measurement (α × β) ι) :
    bipartiteDefect D A B ψ ≤
      bipartiteDefect D (fun x => (A x).postprocess Prod.snd) (fun x => (B x).postprocess Prod.snd) ψ +
      bipartiteDefect D (fun x => (A x).postprocess Prod.fst) (fun x => (B x).postprocess Prod.fst) ψ := by
  simp_rw [SandwichProduct.consistencyDefect_placed_eq_avg_point]
  rw [← avgOver_add]
  apply avgOver_mono
  intro x
  have hx := born_payoff_postprocess ψ (A x) (B x) Prod.fst Prod.fst (fun i j => if i = j then 0 else 1)
  have hy := born_payoff_postprocess ψ (A x) (B x) Prod.snd Prod.snd (fun i j => if i = j then 0 else 1)
  simp only [ite_mul, zero_mul, one_mul] at hx hy
  rw [hx, hy, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have h := stateQForm_nonneg ψ (kronecker_nonneg ((A x).pos a) ((B x).pos b))
  by_cases h₁ : a.1 = b.1 <;> by_cases h₂ : a.2 = b.2 <;> simp [Prod.ext_iff, h₁, h₂] <;> exact h

private theorem abs_pinch_overlap_gap_le_sqrt (A : Measurement α ιA) (hψ : ‖ψ‖ = 1) :
    |diagonalOverlap ψ A P - diagonalOverlap ψ A (pinchedPOVM P hG)| ≤
      Real.sqrt (∑ a, ∑ b, ‖applyOperatorToState (heteroKron 1
        (P.effect a * G.effect b - G.effect b * P.effect a)) ψ‖ ^ 2) := by
  let C a b := P.effect a * G.effect b - G.effect b * P.effect a
  have hd (a : α) : (∑ b, G.effect b * P.effect a * G.effect b) - P.effect a =
      ∑ b, G.effect b * C a b := by
    simp only [C, mul_sub, ← mul_assoc, fun b => (hG b).isIdempotentElem.eq,
      Finset.sum_sub_distrib, ← Finset.sum_mul, G.sum_eq_one, one_mul]
  have hb := abs_sum_effect_mul_le (tensorMeasurement A G)
    (fun p => heteroKron 1 (C p.1 p.2)) hψ
  have he (p : α × β) : (tensorMeasurement A G).effect p = heteroKron (A.effect p.1) (G.effect p.2) := rfl
  simp only [he, Fintype.sum_prod_type, heteroKron_mul, mul_one] at hb
  have hs (a : α) : (∑ b, stateQForm ψ (heteroKron (A.effect a) (G.effect b * C a b))) =
      stateQForm ψ (heteroKron (A.effect a) ((pinchedPOVM P hG).effect a)) -
      stateQForm ψ (heteroKron (A.effect a) (P.effect a)) := by
    rw [← stateQForm_finset_sum, ← heteroKron_finset_sum_right, ← hd, pinchedPOVM_effect,
      heteroKron_sub_right, stateQForm_sub]
  simpa only [hs, Finset.sum_sub_distrib, diagonalOverlap, abs_sub_comm] using hb

/-- Pinching increases the consistency defect by at most the square root of the commutator mass. -/
theorem consistencyDefect_pinched_le_marginal_add_sqrt (A : X → Measurement α ιA)
    (P : X → Measurement α ι) {G : X → Measurement β ι} (hG : ∀ x, Measurement.IsProjective (G x))
    {K : ℝ} (hD : D.IsProbability) (hψ : ‖ψ‖ = 1)
    (hK : avgOver D (fun x => ∑ a, ∑ b, ‖applyOperatorToState (heteroKron 1
      ((P x).effect a * (G x).effect b - (G x).effect b * (P x).effect a)) ψ‖ ^ 2) ≤ K) :
    bipartiteDefect D A (fun x => pinchedPOVM (P x) (hG x)) ψ ≤
      bipartiteDefect D A P ψ + Real.sqrt K := by
  simp only [bipartiteDefect_eq_one_sub ψ _ _ hD hψ]
  have h := Preliminaries.avgOver_abs_le_sqrt_of_pointwise D _ _
    (fun x => abs_pinch_overlap_gap_le_sqrt (P x) (hG x) (A x) hψ)
    (fun x => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
    hD.weight_sum_eq_one.le
  rw [avgOver_sub] at h
  linarith [(le_abs_self _).trans (h.trans (Real.sqrt_le_sqrt hK))]

end MIPStarRE.QPBT
