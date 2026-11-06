module

public import PottsDiscontinuity.FK.Parameters
public import PottsDiscontinuity.Frozen.Defs.RCCriticalParameter

/-!
# Dual edge parameter

This module proves the algebra of planar FK duality, including the fixed point.
It does not assert a duality identity for probability measures.
-/

@[expose] public noncomputable section

namespace PottsDiscontinuity.Duality

/-- The FK dual edge parameter, for a positive cluster weight and an interior
edge probability. The admissibility lemmas below specify that domain. -/
def dualParameter (q p : ℝ) : ℝ :=
  q * (1 - p) / (p + q * (1 - p))

section
variable {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
include hq hp hp1
theorem dualParameter_den_pos  :
    0 < p + q * (1 - p) :=
  by positivity

theorem dualParameter_pos  :
    0 < dualParameter q p :=
  div_pos (mul_pos hq (sub_pos.mpr hp1)) (dualParameter_den_pos hq hp hp1)

theorem dualParameter_lt_one  :
    dualParameter q p < 1 := by
  rw [dualParameter, div_lt_one (dualParameter_den_pos hq hp hp1)]
  linarith

theorem one_sub_dualParameter  :
    1 - dualParameter q p = p / (p + q * (1 - p)) := by
  unfold dualParameter
  field_simp [(dualParameter_den_pos hq hp hp1).ne']
  ring
end

section
variable (q : Set.Ici (1 : ℝ))
/-- The existing critical parameter lies in the interior for every `q ≥ 1`. -/
theorem rcCriticalParameter_mem_Ioo  :
    (rcCriticalParameter q : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hq : 0 < (q : ℝ) := by grind
  change 0 < Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) ∧
    Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) < 1
  constructor
  · positivity
  · exact (div_lt_one (by positivity)).2 (by simp)

/-- The parameter `√q / (1 + √q)` is fixed by planar FK parameter duality. -/
theorem dualParameter_rcCriticalParameter  :
    dualParameter q (rcCriticalParameter q) = rcCriticalParameter q := by
  change dualParameter q (Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ))) =
    Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ))
  grind [dualParameter, Real.sqrt]
end

/-- FK parameters at the dual edge probability, preserving the cluster weight. -/
def dualParameters (θ : FK.Parameters) : FK.Parameters where
  val := θ.val
  property := θ.property
  edgeProbability := ⟨dualParameter θ.val (FK.edgeParameter θ),
    dualParameter_pos (FK.clusterWeight_pos θ) (FK.edgeParameter_pos θ)
      (FK.edgeParameter_lt_one θ),
    dualParameter_lt_one (FK.clusterWeight_pos θ) (FK.edgeParameter_pos θ)
      (FK.edgeParameter_lt_one θ)⟩

end PottsDiscontinuity.Duality
