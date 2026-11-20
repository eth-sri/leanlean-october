module

public import PottsDiscontinuity.Infra.ClopenProbability

public import PottsDiscontinuity.Potts.GhostBoxCylinders

/-! Local finite edge observations and their probabilities under box limits. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace

/-- Read precisely the internal bonds of the frozen domain. -/
def frozenObservation (V : Finset (ℤ × ℤ)) (ω : FK.LatticeConfiguration) :
    FK.Configuration (squareLattice.induce (V : Set (ℤ × ℤ))) :=
  FK.boolConfigurationEquiv _ (fun e => ω (FK.frozenEdgeEmbedding V e))

abbrev boxObservation (n : ℕ) := frozenObservation (box n)

def boxObservationEvent (n : ℕ)
    (S : Set (FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ))))) :
    Set FK.LatticeConfiguration := boxObservation n ⁻¹' S

theorem boxObservationEvent_isClopen (n : ℕ)
    (S : Set (FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ))))) :
    IsClopen (boxObservationEvent n S) :=
  (isClopen_discrete ((FK.boolConfigurationEquiv _) ⁻¹' S)).preimage
    (continuous_pi (fun e => continuous_apply (FK.frozenEdgeEmbedding (box n) e)))

theorem boxObservation_dependsOn (n : ℕ)
    (S : Set (FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ))))) :
    RCInfinite.DependsOn (RCInfinite.boxEdges (0, 0) n) (boxObservationEvent n S) := by
  rw [boxEdges_origin_eq_range]
  intro ω η h
  have he : boxObservation n ω = boxObservation n η := congrArg (FK.boolConfigurationEquiv _)
    (funext fun e => h _ ⟨e, rfl⟩)
  change boxObservation n ω ∈ S ↔ boxObservation n η ∈ S
  rw [he]

theorem observation_ext_eq (V : Finset (ℤ × ℤ))
    (f : FK.Configuration (squareLattice.induce (V : Set (ℤ × ℤ))) → FK.LatticeConfiguration)
    (hf : ∀ C e, f C (FK.frozenEdgeEmbedding V e) = decide (e ∈ C)) (C) :
    frozenObservation V (f C) = C := by
  ext e
  simp [frozenObservation, hf]

theorem boxObservation_upper_of_extension (i : Fin 2) (n : ℕ)
    (S : Set (FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))))
    (hS : IsUpperSet S) :
    IsUpperSet (RCInfinite.boxExtension i (0, 0) n ⁻¹' boxObservationEvent n S) := by
  suffices ∀ V (hV : FK.latticeBox (0, 0) n = V)
      (T : Set (FK.Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))) (hT : IsUpperSet T),
      IsUpperSet (RCInfinite.boxExtension i (0, 0) n ⁻¹' (frozenObservation V ⁻¹' T)) from
    this _ (FK.latticeBox_origin_eq_box n) S hS
  rintro _ rfl T hT
  intro C D hCD hC
  change frozenObservation _ (RCInfinite.boxExtension i (0, 0) n D) ∈ T
  change frozenObservation _ (RCInfinite.boxExtension i (0, 0) n C) ∈ T at hC
  have hf (A : FK.Configuration (FK.boxGraph (0, 0) n)) :
      frozenObservation (FK.latticeBox (0, 0) n) (RCInfinite.boxExtension i (0, 0) n A) = A :=
    observation_ext_eq (FK.latticeBox (0, 0) n) (RCInfinite.boxExtension i (0, 0) n)
      (fun B e => (RCInfinite.boxExtension_at i (0, 0) n B e).trans
        (congrArg (@decide (e ∈ B)) (Subsingleton.elim _ _))) A
  rw [hf D]
  exact hT hCD (hf C ▸ hC)

open RCInfinite in
/-- The clopen observation comparison passes to the limit with either boundary condition. -/
theorem boxObservation_limit_compare (θ : FK.Parameters) (i : Fin 2)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (boxMeasure θ i (0, 0)) atTop (𝓝 μ))
    (m : ℕ) (S : Set (FK.Configuration (squareLattice.induce (box m : Set (ℤ × ℤ)))))
    (hS : IsUpperSet S) :
    comparisonSign i * μ.toMeasure.real (boxObservationEvent m S) ≤
      comparisonSign i * (boxMeasure θ i (0, 0) m).toMeasure.real (boxObservationEvent m S) := by
  have hcl := boxObservationEvent_isClopen m S
  apply le_of_tendsto ((ProbabilityMeasure.tendsto_real_clopen hμ hcl).const_mul _)
  filter_upwards [eventually_ge_atTop m] with n hn
  simpa only [Set.inter_univ, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    box_event_joint_compare θ i (FK.latticeBox_mono (0, 0) hn) (boxObservationEvent m S)
      Set.univ hcl.isOpen.measurableSet MeasurableSet.univ (boxObservation_dependsOn m S)
      (by simp [RCInfinite.DependsOn]) (boxObservation_upper_of_extension i m S hS)

@[simp] theorem boxObservation_openExtension_self (n : ℕ)
    (C : FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :
    boxObservation n (openExtension (box n) C) = C :=
  observation_ext_eq _ (openExtension (box n)) (openExtension_at (box n)) C

end
end PottsDiscontinuity.Potts
