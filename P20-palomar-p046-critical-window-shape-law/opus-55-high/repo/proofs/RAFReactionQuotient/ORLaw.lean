module

public import proofs.RAFEmergenceApprox.GenericHistory

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold

variable {R J : Type*} [Fintype R]

    (π : R → J)

def fieldOR  (ω : R → Prop) (j : J) : Prop :=
  ∃ r, π r = j ∧ ω r

variable (p : I)

variable (E : J → Prop → Prop)

variable (j : J)

/-- Predicates on disjoint quotient fibres are independent, including a whole
family of other fibres. -/
theorem fibre_event_indep
     (S : Finset J) (hj : j ∉ S) :
    IndepFun (fun ω : R → Prop => E j $ fieldOR π ω j)
      (∀ k ∈ S, E k $ fieldOR π · k)
      (RAFEmergenceApprox.Generic.colLaw R p) := by
  have he := (iIndepFun_pi (fun _ : R => aemeasurable_id) (μ := fun _ : R => ambientCoordLaw p)
    ).indepFun_finset (Finset.univ.filter (π · = j)) (Finset.univ.filter (π · ∈ S))
    (Finset.disjoint_left.mpr $ by grind) (measurable_pi_apply ·) |>.comp
    (measurable_of_finite fun v => E j (∃ r, v r))
    (measurable_of_finite fun v => ∀ k ∈ S, E k (∃ r, π r.val = k ∧ v r))
  convert he using 2
  · simp [fieldOR]
  · exact forall₂_congr fun k hk => iff_of_eq $ congrArg (E k) $ propext $ by simp [fieldOR]; grind
  rfl

theorem fibre_events_product
    (S : Finset J) :
    RAFEmergenceApprox.Generic.colLaw R p {ω | ∀ j ∈ S, E j $ fieldOR π ω j} =
      ∏ j ∈ S, RAFEmergenceApprox.Generic.colLaw R p {ω | E j $ fieldOR π ω j} := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    have hi := (fibre_event_indep π p E j S hj).measure_inter_preimage_eq_mul
      {True} {True} (MeasurableSet.singleton True) $ MeasurableSet.singleton True
    aesop


theorem fieldOR_independent   :
    iIndepFun (fun j (ω : R → Prop) => fieldOR π ω j)
      (RAFEmergenceApprox.Generic.colLaw R p) := by
  refine iIndepFun_iff_measure_inter_preimage_eq_mul.2 fun S sets _ => ?_
  convert fibre_events_product π p (fun j z => z ∈ sets j) S using 2 <;> aesop

theorem fieldOR_closed_probability    :
    RAFEmergenceApprox.Generic.colLaw R p {ω | ¬ fieldOR π ω j} =
      (toNNReal (σ p) : ENNReal) ^ (Finset.univ.filter $ fun r => π r = j).card := by
  convert RAFEmergenceApprox.Generic.closed_probability _ _ using 3
  simp [fieldOR]

end RAFReactionQuotient
