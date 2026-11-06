module
public import Mathlib

public import PottsDiscontinuity.FK.Parameters
public import PottsDiscontinuity.Frozen.Defs.RCCriticalParameter

/-!
# Dual edge parameter

This module proves the algebra of planar FK duality, including the fixed point.
It does not assert a duality identity for probability measures.
-/

@[expose] public section

namespace PottsDiscontinuity.Duality

/-- The FK dual edge parameter, for a positive cluster weight and an interior
edge probability. The admissibility lemmas below specify that domain. -/
noncomputable def dualParameter (q p : ℝ) : ℝ :=
  q * (1 - p) / (p + q * (1 - p))

section

variable {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
include hq hp hp1

lemma dualParameter_den_pos  :
    0 < p + q * (1 - p) :=
  by
    nlinarith

lemma dualParameter_pos  :
    0 < dualParameter q p :=
  div_pos (mul_pos hq (sub_pos.mpr hp1)) (dualParameter_den_pos hq hp hp1)

lemma dualParameter_lt_one  :
    dualParameter q p < 1 := by
  rw [dualParameter, div_lt_one (dualParameter_den_pos hq hp hp1)]
  linarith only [hp]

lemma one_sub_dualParameter  :
    1 - dualParameter q p = p / (p + q * (1 - p)) := by
  unfold dualParameter
  field_simp [(dualParameter_den_pos hq hp hp1).ne']
  ring

end

/-- The existing critical parameter lies in the interior for every `q ≥ 1`. -/
lemma rcCriticalParameter_mem_Ioo (q : Set.Ici (1 : ℝ)) :
    (rcCriticalParameter q : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
  
  have hs  := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one q.property)
  
  constructor
  · exact div_pos hs (by positivity)
  · exact (div_lt_one (by positivity)).2 (by linarith only )

/-- The parameter `√q / (1 + √q)` is fixed by planar FK parameter duality. -/
theorem dualParameter_rcCriticalParameter (q : Set.Ici (1 : ℝ)) :
    dualParameter q (rcCriticalParameter q) = rcCriticalParameter q := by
  have hq  := lt_of_lt_of_le zero_lt_one q.property
  
  
  have hsub : 1 - Real.sqrt q / (1 + Real.sqrt q) =
      1 / (1 + Real.sqrt q) := by
    field_simp
    ring
  change dualParameter q (Real.sqrt q / (1 + Real.sqrt q)) =
    Real.sqrt q / (1 + Real.sqrt q)
  rw [dualParameter, hsub, ← mul_div_assoc, ← add_div,
    div_div_div_cancel_right₀ (by positivity)]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  nlinarith only [ Real.sq_sqrt hq.le ]

/-- FK parameters at the dual edge probability, preserving the cluster weight. -/
noncomputable def dualParameters (θ : FK.Parameters) : FK.Parameters where
  val := θ.val
  property := θ.property
  edgeProbability := ⟨dualParameter θ.val (FK.edgeParameter θ),
    dualParameter_pos (FK.clusterWeight_pos θ) (FK.edgeParameter_pos θ)
      (FK.edgeParameter_lt_one θ),
    dualParameter_lt_one (FK.clusterWeight_pos θ) (FK.edgeParameter_pos θ)
      (FK.edgeParameter_lt_one θ)⟩

end PottsDiscontinuity.Duality
