/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module
public import Mathlib

public import PottsDiscontinuity.FK.Probability

/-!
# Products and changes of carrier for finite normalized weights

The product PMF is constructed by independently sampling the two given PMFs
using mathlib's `bind` and `map`. Its point masses and both marginals are proved
below. No spatial FK independence assertion is assumed here.
-/

@[expose] public section

namespace PottsDiscontinuity.FK.FiniteProbability

open scoped BigOperators

noncomputable section

variable {α β : Type*}

/-- Sample the two factors separately and retain both outcomes. -/
def productPMF (p : PMF α) (q : PMF β)  :=
  p.bind  fun a => q.map (Prod.mk a) 

open scoped Classical in
lemma map_mk_apply (q : PMF β) (a : α) (x : α × β) :
    q.map (Prod.mk a) x = if x.1 = a then q x.2 else 0 := by
  aesop

lemma productPMF_apply (p : PMF α) (q : PMF β) (x : α × β) :
    productPMF p q x = p x.1 * q x.2 := by
  
  rw [productPMF, PMF.bind_apply]
  simp_rw [map_mk_apply]
  simp_all

lemma productPMF_map_fst (p : PMF α) (q : PMF β) :
    (productPMF p q).map Prod.fst = p := by
  simp only [productPMF, PMF.map_bind, PMF.map_comp]
  change  p.bind (fun a => q.map (Function.const β a))  = p
  simp_all

lemma map_equiv_apply (p : PMF α) (e : α ≃ β) (b : β) :
    p.map e b = p (e.symm b) := by
  classical
  simp only [PMF.map_apply, ← e.symm_apply_eq, tsum_ite_eq']

section

variable [Fintype α] [Fintype β]

lemma partition_product (w : α → ℝ) (v : β → ℝ) :
    partition (fun x : α × β => w x.1 * v x.2) = partition w * partition v := by
  unfold partition
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]

lemma partition_equiv (e : α ≃ β) (v : β → ℝ) :
    partition (fun a => v (e a)) = partition v :=
  e.sum_comp v

variable [Nonempty α] [Nonempty β]

section

variable (w : α → ℝ) (v : β → ℝ) (hw : ∀ a, 0 < w a) (hv : ∀ b, 0 < v b)
include hw hv

lemma probability_product  (x : α × β) :
    probability (fun x : α × β => w x.1 * v x.2)
        (fun x => mul_pos (hw x.1) (hv x.2)) x =
      probability w hw x.1 * probability v hv x.2 := by
  grind [probability, partition_product]

lemma pmf_product  :
    pmf (fun x : α × β => w x.1 * v x.2) (fun x => mul_pos (hw x.1) (hv x.2)) =
      productPMF (pmf w hw) (pmf v hv) := by
  ext x
  rw [productPMF_apply]
  change ENNReal.ofReal (probability (fun x  => w x.1 * v x.2)
      (fun x => mul_pos (hw x.1) (hv x.2)) x) =
    ENNReal.ofReal (probability w hw x.1) * ENNReal.ofReal (probability v hv x.2)
  rw [probability_product w v hw hv x, ENNReal.ofReal_mul (probability_pos w hw x.1).le]

end

/-- Push a law given by pulled-back weights onto the original finite carrier. -/
lemma pmf_map_equiv (e : α ≃ β) (v : β → ℝ) (hv : ∀ b, 0 < v b) :
    (pmf (fun a => v (e a))  fun a => hv (e a) ).map e = pmf v hv := by
  ext b
  rw [map_equiv_apply, pmf_apply, pmf_apply, e.apply_symm_apply, partition_equiv]

/-- Reindex any positive weight family after proving the exact weight identity. -/
lemma pmf_map_equiv_of_weight_eq (e : α ≃ β) (w : α → ℝ) (v : β → ℝ)
    (hw : ∀ a, 0 < w a) (hv : ∀ b, 0 < v b)
    (h : ∀ a, w a = v (e a)) : (pmf w hw).map e = pmf v hv := by
  have hweights  := funext h
  subst w
  exact pmf_map_equiv e v hv

end

end

end PottsDiscontinuity.FK.FiniteProbability
