import Mathlib

macro "sum_ring_nf" : tactic => `(tactic|
  (iterate 3
    (all_goals try simp only [pow_two, sub_eq_add_neg, mul_neg, neg_mul, add_div,
      mul_add, add_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.mul_sum, Finset.sum_mul, List.sum_map_add, ← List.sum_map_mul_left,
      ← List.sum_map_mul_right, mul_zero, mul_one, zero_mul, add_zero]
     all_goals try simp only [mul_assoc, mul_comm, mul_left_comm]
     all_goals ring_nf (config := { ifUnchanged := .silent })
     all_goals try simp only [mul_assoc, mul_comm, mul_left_comm])
   ))

macro "sum_ring" : tactic => `(tactic| (sum_ring_nf; all_goals ring1))

/-- Normalize products of positive real powers through the exponential. -/
macro "rpow_ring" : tactic => `(tactic|
  (try simp (disch := positivity) only [← Real.rpow_neg_one, Real.rpow_def_of_pos,
      Real.log_exp]
   ring_nf (config := { ifUnchanged := .silent })
   try simp only [mul_assoc, mul_comm, mul_left_comm]
   try simp only [← Real.exp_add, ← Real.exp_neg, ← Real.exp_sub, ← Real.exp_nat_mul]
   all_goals (congr 1 <;> ring)))

/- Let `bound` descend into finite sums and weaken strict hypotheses when needed. -/
attribute [bound] Finset.sum_nonneg List.sum_nonneg
attribute [aesop unsafe 50% apply (rule_sets := [Bound])] le_of_lt
