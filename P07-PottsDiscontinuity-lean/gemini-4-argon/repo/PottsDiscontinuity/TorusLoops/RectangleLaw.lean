module

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

local instance rectangleLawEdgeDecidableEq (hN : Even N) (hM : Even M) :
    DecidableEq (rectangleBaseGraph hN hM).edgeSet := Classical.decEq _

/-- A torus configuration is seam-closed when every deleted indexed edge is
closed. -/
def rectangleSeamsClosed (A : RCConfig N M) : Prop :=
  ∀ v : Fin N × Fin M, v.1.val = 0 ∨ v.2.val = 0 → A v = false

/-- Lift an event on the free rectangle configurations to its seam-closed
fiber in the torus sample space. -/
def rectangleClosedLiftEvent (hN : Even N) (hM : Even M)
    (E : Set (Configuration (rectangleBaseGraph hN hM))) : Set (RCConfig N M) :=
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
  left_inv := rectangleConfigurationOfRC_rectangleRCConfigOfConfiguration hN hM
  right_inv A := Subtype.ext <|
    rectangleRCConfigOfConfiguration_rectangleConfigurationOfRC hN hM A.val A.property

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

/-- The closed-fiber event weight is exactly the rectangle event weight times
the constant seam factor. -/
theorem rectangleTorusClosedLiftWeight_eq
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (Configuration (rectangleBaseGraph hN hM))) :
    rectangleTorusClosedLiftWeight hN hM q E =
      (1 - (rcCriticalParameter q).val) ^
          (rectangleSeamIndices (N := N) (M := M)).card *
        rectangleFKEventWeight hN hM q E := by
  classical
  let e := rectangleConfigurationClosedFiberEquiv hN hM
  unfold rectangleTorusClosedLiftWeight rectangleFKEventWeight
  rw [← e.sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  have hrec : rectangleConfigurationOfRC hN hM (e C).val = C := e.symm_apply_apply C
  have hw := torusRCWeight_eq_seamFactor_mul_rectangleFKWeight hN hM q (e C).val (e C).property
  rw [hrec] at hw
  by_cases hE : C ∈ E <;> simp [hrec, hE, hw]

/-- The torus probability of a lifted event is its unnormalized closed-fiber
weight divided by the torus partition function. -/
theorem phi_T_probability_rectangleClosedLift_eq
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (Configuration (rectangleBaseGraph hN hM))) :
    phi_T_probability hN hM q (rectangleClosedLiftEvent hN hM E) =
      rectangleTorusClosedLiftWeight hN hM q E / torusRCPartition hN hM q := by
  classical
  rw [phi_T_probability_eq_sum, show (∑ A, (rectangleClosedLiftEvent hN hM E).indicator
      (torusRCMass hN hM q) A) =
      (∑ A, (rectangleClosedLiftEvent hN hM E).indicator (torusRCWeight hN hM q) A) /
        torusRCPartition hN hM q by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun A _ => ?_
    by_cases hA : A ∈ rectangleClosedLiftEvent hN hM E <;> simp [hA, torusRCMass],
    ← Fintype.sum_subtype_add_sum_subtype (rectangleSeamsClosed (N := N) (M := M))]
  congr 1
  rw [show (∑ A : {A : RCConfig N M // ¬ rectangleSeamsClosed A},
      (rectangleClosedLiftEvent hN hM E).indicator (torusRCWeight hN hM q) A.val) = 0 from
    Finset.sum_eq_zero fun A _ => by simp [rectangleClosedLiftEvent, A.property], add_zero]
  refine Finset.sum_congr rfl fun A _ => ?_
  by_cases hE : rectangleConfigurationOfRC hN hM A.val ∈ E <;>
    simp [rectangleClosedLiftEvent, A.property, hE]

/-- Every normalized seam-closed lifted event is bounded by its probability
under the free rectangle FK law. -/
theorem phi_T_probability_rectangleClosedLift_le_rectangleFK
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (Configuration (rectangleBaseGraph hN hM))) :
    phi_T_probability hN hM q (rectangleClosedLiftEvent hN hM E) ≤
      rectangleFKEventProbability hN hM q E := by
  classical
  let ZT := torusRCPartition hN hM q
  let ZR := FK.partitionFunction (rectangleBaseGraph hN hM)
    (rectangleFKParameters q) (BoundaryCondition.free ∅)
  let nR := rectangleFKEventWeight hN hM q E
  let f := (1 - (rcCriticalParameter q).val) ^ (rectangleSeamIndices (N := N) (M := M)).card
  have hZR : 0 < ZR := FK.partitionFunction_pos _ _ _
  have hZT : 0 < ZT := torusRCPartition_pos hN hM q
  have hnum : 0 ≤ nR := Finset.sum_nonneg fun C _ => by
    by_cases hC : C ∈ E <;> simp [hC, (FK.weight_pos _ _ _ C).le]
  have hdenom : f * ZR ≤ ZT := by
    have hfactor := rectangleTorusClosedLiftWeight_eq hN hM q Set.univ
    simp only [rectangleTorusClosedLiftWeight, Set.mem_univ, ite_true,
      rectangleFKEventWeight, Set.indicator_univ] at hfactor
    change _ = f * ZR at hfactor
    rw [← hfactor]
    unfold ZT torusRCPartition FK.FiniteProbability.partition
    rw [← Fintype.sum_subtype_add_sum_subtype (rectangleSeamsClosed (N := N) (M := M))]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun A _ => (torusRCWeight_pos hN hM q A.val).le)
  rw [phi_T_probability_rectangleClosedLift_eq, rectangleTorusClosedLiftWeight_eq]
  change f * nR / ZT ≤ nR / ZR
  rw [div_le_div_iff₀ hZT hZR]
  nlinarith

end

end PottsDiscontinuity.TorusLoops
