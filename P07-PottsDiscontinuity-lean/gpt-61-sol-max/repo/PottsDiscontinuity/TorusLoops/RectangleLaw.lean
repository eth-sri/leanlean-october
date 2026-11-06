module
public import Mathlib

public import PottsDiscontinuity.TorusLoops.RectangleFK

/-!
# The seam-closed torus fiber and the free rectangle FK law

The torus configurations with both cut seams closed are in bijection with
configurations of the fixed rectangle graph. Their pointwise weights differ
by one constant seam factor. Consequently the torus probability of a
seam-closed lifted event is at most its normalized free-rectangle probability.
-/

@[expose] public section

open scoped BigOperators

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus
open PottsDiscontinuity.TorusRC
open PottsDiscontinuity.FK

noncomputable section

variable {N M : ℕ}

local instance rectangleLawEdgeFintype (hN : Even N) (hM : Even M) :
    Fintype (rectangleBaseGraph hN hM).edgeSet := Fintype.ofFinite _



/-- A torus configuration is seam-closed when every deleted indexed edge is
closed. -/
def rectangleSeamsClosed (A : RCConfig N M)  :=
  ∀ v : Fin N × Fin M, v.1.val = 0 ∨ v.2.val = 0 → A v = false

/-- Lift an event on the free rectangle configurations to its seam-closed
fiber in the torus sample space. -/
def rectangleClosedLiftEvent (hN : Even N) (hM : Even M)
    (E : Set (Configuration (rectangleBaseGraph hN hM)))  :=
  {A | rectangleSeamsClosed A ∧ rectangleConfigurationOfRC hN hM A ∈ E}

/-- Equivalence between rectangle FK configurations and seam-closed torus
configurations. -/
noncomputable def rectangleConfigurationClosedFiberEquiv
    (hN : Even N) (hM : Even M) :
    Configuration (rectangleBaseGraph hN hM) ≃
      {A : RCConfig N M // rectangleSeamsClosed A} where
  toFun C := ⟨rectangleRCConfigOfConfiguration hN hM C,
    rectangleRCConfigOfConfiguration_closedOnSeams hN hM C⟩
  invFun A := rectangleConfigurationOfRC hN hM A.val
  left_inv C := rectangleConfigurationOfRC_rectangleRCConfigOfConfiguration hN hM C
  right_inv A := by
    apply Subtype.ext
    exact rectangleRCConfigOfConfiguration_rectangleConfigurationOfRC
      hN hM A.val A.property

/-- Unnormalized free-rectangle FK weight of an event. -/
noncomputable def rectangleFKEventWeight (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ))
    (E : Set (Configuration (rectangleBaseGraph hN hM))) : ℝ := by
  classical
  exact ∑ C, E.indicator
      (FK.weight (rectangleBaseGraph hN hM) (rectangleFKParameters q)
        (BoundaryCondition.free ∅)) C

/-- Normalized free-rectangle FK probability of an event. -/
noncomputable def rectangleFKEventProbability (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ))
    (E : Set (Configuration (rectangleBaseGraph hN hM))) : ℝ :=
  rectangleFKEventWeight hN hM q E /
    FK.partitionFunction (rectangleBaseGraph hN hM) (rectangleFKParameters q)
      (BoundaryCondition.free ∅)

/-- Unnormalized torus weight of the rectangle-event lift on the closed seam
fiber. -/
noncomputable def rectangleTorusClosedLiftWeight (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ))
    (E : Set (Configuration (rectangleBaseGraph hN hM))) : ℝ := by
  classical
  exact ∑ A : {A : RCConfig N M // rectangleSeamsClosed A},
      if rectangleConfigurationOfRC hN hM A.val ∈ E then
        torusRCWeight hN hM q A.val else 0

section

variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
include hN hM q

/-- The closed-fiber event weight is exactly the rectangle event weight times
the constant seam factor. -/
theorem rectangleTorusClosedLiftWeight_eq
    
    (E : Set (Configuration (rectangleBaseGraph hN hM))) :
    rectangleTorusClosedLiftWeight hN hM q E =
      (1 - (rcCriticalParameter q).val) ^
          (rectangleSeamIndices (N := N) (M := M)).card *
        rectangleFKEventWeight hN hM q E := by
  classical
  let e := rectangleConfigurationClosedFiberEquiv hN hM
  unfold rectangleTorusClosedLiftWeight rectangleFKEventWeight
  rw [← e.sum_comp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  let A := e C
  
  have hrec : rectangleConfigurationOfRC hN hM A.val = C := e.symm_apply_apply C
  by_cases hE : C ∈ E
  · change (if rectangleConfigurationOfRC hN hM A.val ∈ E then
        torusRCWeight hN hM q A.val else 0) = _
    have hAE : rectangleConfigurationOfRC hN hM A.val ∈ E := by
      rw [hrec]
      exact hE
    have hw := torusRCWeight_eq_seamFactor_mul_rectangleFKWeight
      hN hM q A.val  A.property 
    rw [hrec] at hw
    simpa [hAE, hE] using hw
  · aesop

/-- Every torus event probability is its unnormalized weight sum divided by
the torus partition function. -/
private theorem phi_T_probability_eq_weightSum_div
    
    (E : Set (RCConfig N M)) :
    phi_T_probability hN hM q E =
      (∑ A, E.indicator (torusRCWeight hN hM q) A) /
        torusRCPartition hN hM q := by
  
  erw [phi_T_probability_eq_sum]
  have hterms :
       ∑ A, E.indicator (torusRCMass hN hM q) A  =
        ∑ A, E.indicator (torusRCWeight hN hM q) A /
          torusRCPartition hN hM q := by
    apply Finset.sum_congr rfl
    intro A _
    by_cases hA : A ∈ E <;> simp [hA, torusRCMass]
  rw [hterms, ← Finset.sum_div]

section

variable (E : Set (Configuration (rectangleBaseGraph hN hM)))


private theorem rectangleClosedLiftEvent_weight_sum
    
     :
     ∑ A, (rectangleClosedLiftEvent hN hM E).indicator
      (torusRCWeight hN hM q) A  = rectangleTorusClosedLiftWeight hN hM q E := by
  classical
  let P : RCConfig N M → Prop := rectangleSeamsClosed
  let g  := (rectangleClosedLiftEvent hN hM E).indicator
    (torusRCWeight hN hM q)
  
  have hpos :
       ∑ A : {A : RCConfig N M // P A}, g A.val  =
        rectangleTorusClosedLiftWeight hN hM q E := by
    
    apply Finset.sum_congr rfl
    intro A _
    dsimp [g, P, rectangleClosedLiftEvent]
    
     
    have hclosed : rectangleSeamsClosed A.val := A.property
    by_cases hE : rectangleConfigurationOfRC hN hM A.val ∈ E <;> simp [hclosed, hE]
  have hzero :
       ∑ A : {A : RCConfig N M // ¬ P A}, g A.val  = 0 := by
    apply Finset.sum_eq_zero
    
    dsimp [g, P, rectangleClosedLiftEvent]
    simp only [Set.indicator_apply]
    all_goals grind
  calc
     ∑ A, (rectangleClosedLiftEvent hN hM E).indicator
        (torusRCWeight hN hM q) A  =
       ∑ A : {A : RCConfig N M // P A}, g A.val  +
        ∑ A : {A : RCConfig N M // ¬ P A}, g A.val := (Fintype.sum_subtype_add_sum_subtype P g).symm
    _ = rectangleTorusClosedLiftWeight hN hM q E := by rw [hpos, hzero, add_zero]

/-- The torus probability of a lifted event is its unnormalized closed-fiber
weight divided by the torus partition function. -/
theorem phi_T_probability_rectangleClosedLift_eq
    
     :
    phi_T_probability hN hM q (rectangleClosedLiftEvent hN hM E) =
      rectangleTorusClosedLiftWeight hN hM q E / torusRCPartition hN hM q := by
  rw [phi_T_probability_eq_weightSum_div,
    rectangleClosedLiftEvent_weight_sum]

/-- Every normalized seam-closed lifted event is bounded by its probability
under the free rectangle FK law. -/
theorem phi_T_probability_rectangleClosedLift_le_rectangleFK
    
     :
    phi_T_probability hN hM q (rectangleClosedLiftEvent hN hM E) ≤
      rectangleFKEventProbability hN hM q E := by
  classical
  let ZT := torusRCPartition hN hM q
  let ZR := FK.partitionFunction (rectangleBaseGraph hN hM)
    (rectangleFKParameters q) (BoundaryCondition.free ∅)
  let nR := rectangleFKEventWeight hN hM q E
  let f := (1 - (rcCriticalParameter q).val) ^
    (rectangleSeamIndices (N := N) (M := M)).card
  
  
  
  have hdenom : f * ZR ≤ ZT := by
    have hsum :
        rectangleTorusClosedLiftWeight hN hM q Set.univ =
          ∑ A : {A : RCConfig N M // rectangleSeamsClosed A},
            torusRCWeight hN hM q A.val := by
      grind +locals
    have hclosedSum :
        rectangleTorusClosedLiftWeight hN hM q Set.univ ≤ ZT := by
      rw [hsum]
      unfold ZT torusRCPartition FK.FiniteProbability.partition
      rw [← Fintype.sum_subtype_add_sum_subtype
        (rectangleSeamsClosed (N := N) (M := M))
         (torusRCWeight hN hM q) ]
      
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun A a => LT.lt.le (torusRCWeight_pos hN hM q ↑A))
    
    have hrectsum : rectangleFKEventWeight hN hM q Set.univ = ZR := by
      unfold rectangleFKEventWeight ZR FK.partitionFunction FK.FiniteProbability.partition
      simp
    rw [ rectangleTorusClosedLiftWeight_eq hN hM q Set.univ , hrectsum] at hclosedSum
    simpa [f] using hclosedSum
  have hprobT :
      phi_T_probability hN hM q (rectangleClosedLiftEvent hN hM E) = f * nR / ZT := by
    grind [phi_T_probability_rectangleClosedLift_eq, rectangleTorusClosedLiftWeight_eq]
  have hprobR : rectangleFKEventProbability hN hM q E = nR / ZR := rfl
  rw [hprobT, hprobR]
  rw [div_le_div_iff₀ (torusRCPartition_pos hN hM q) (FK.partitionFunction_pos
                             (rectangleBaseGraph hN hM) (rectangleFKParameters q) (BoundaryCondition.free ∅))]
  calc
    f * nR * ZR = nR * (f * ZR) := by ring
    _ ≤ nR * ZT := mul_le_mul_of_nonneg_left hdenom (by
                                                       
                                                       apply Finset.sum_nonneg
                                                       intro C _
                                                       by_cases hC : C ∈ E <;> simp [hC]
                                                       exact (FK.weight_pos (rectangleBaseGraph hN hM)
                                                         (rectangleFKParameters q) (BoundaryCondition.free ∅) C).le)

end

end

end

end PottsDiscontinuity.TorusLoops
