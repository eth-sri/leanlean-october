module

public import PottsDiscontinuity.Potts.GhostBoxCylinders

/-! Local finite edge observations and their probabilities under box limits. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace

/-- Read precisely the internal bonds of the frozen box. -/
def boxObservation (n : ℕ) (ω : FK.LatticeConfiguration) :
    FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ))) :=
  FK.boolConfigurationEquiv _ (fun e => ω (FK.frozenEdgeEmbedding (box n) e))

section
variable {n : ℕ} (S : Set (FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))))
include S

def boxObservationEvent :
    Set FK.LatticeConfiguration := {ω | boxObservation n ω ∈ S}

theorem boxObservationEvent_isClopen :
    IsClopen (boxObservationEvent S) := (isClopen_discrete {η | FK.boolConfigurationEquiv _ η ∈ S}).preimage
    (continuous_pi (fun e => continuous_apply (FK.frozenEdgeEmbedding (box n) e)))

end

section
variable (θ : FK.Parameters) {m n : ℕ} (h : m ≤ n)

theorem boxObservation_openExtension
    (C : FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :
    boxObservation m (openExtension (box n) C) =
      FK.embeddedConfigurationRestriction _ _ (nestedBoxEmbedding h) (nestedBox_map_le h) C := by
  ext e
  unfold boxObservation
  rw [FK.mem_embeddedConfigurationRestriction, FK.mem_boolConfigurationEquiv]
  rw [← nestedEdgeEmbedding_compatible h e, openExtension_at, decide_eq_true_eq]

theorem openBoxProbabilityMeasure_observation
    (S : Set (FK.Configuration (squareLattice.induce (box m : Set (ℤ × ℤ))))) :
    (openBoxProbabilityMeasure θ n).toMeasure (boxObservationEvent S) =
      FK.measure _ θ (FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box n)})
        (nestedBoxEvent h S) := by
  change (((FK.law _ θ (FK.frozenBoundaryCondition (box n) 1)).map
    (openExtension (box n))).toMeasure _) = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    (boxObservationEvent_isClopen S).isOpen.measurableSet]
  congr 1
  ext C
  exact congrArg (fun A => A ∈ S) (boxObservation_openExtension h C) |>.to_iff

end

variable (θ : FK.Parameters) (n : ℕ)
    (S : Set (FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))))

/-- Every increasing event on a finite box has wired-limit probability at
most its probability with that finite box boundary wired. -/
theorem wired_limit_observation_le
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ))
    (m : ℕ) {S : Set (FK.Configuration (squareLattice.induce (box m : Set (ℤ × ℤ))))}
    (hS : IsUpperSet S) :
    μ.toMeasure.real (boxObservationEvent S) ≤
      (FK.measure _ θ (FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box m)}) S).toReal := by
  have ht := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ
    (boxObservationEvent_isClopen S)
  have hreal : Tendsto (fun n => (openBoxProbabilityMeasure θ n).toMeasure.real
      (boxObservationEvent S)) atTop (𝓝 (μ.toMeasure.real (boxObservationEvent S))) := by
    simpa only [openBoxProbabilityMeasure_eq_wired, ProbabilityMeasure.measureReal_eq_coe_coeFn,
      Function.comp_def] using NNReal.continuous_coe.continuousAt.tendsto.comp ht
  apply le_of_tendsto hreal
  filter_upwards [eventually_ge_atTop m] with n hn
  rw [Measure.real, openBoxProbabilityMeasure_observation θ hn]
  exact FK.embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior (nestedBox_map_le hn) θ
    (fun _ hx _ hxy => nestedBox_interior_closed _ hx hxy)
    (fun _ hx => nestedBox_avoids_boundary _ hx) hS

theorem nestedBoxEvent_refl :
    nestedBoxEvent (Nat.le_refl n) S = S := by
  ext C
  have hC : FK.embeddedConfigurationRestriction _ _ (nestedBoxEmbedding (Nat.le_refl n))
      (nestedBox_map_le (Nat.le_refl n)) C = C := by
    ext e
    rw [FK.mem_embeddedConfigurationRestriction]
    have he : FK.embeddedEdgeEmbedding _ _ (nestedBoxEmbedding (Nat.le_refl n))
        (nestedBox_map_le (Nat.le_refl n)) e = e := by
      apply Subtype.ext
      change Sym2.map (nestedBoxEmbedding (Nat.le_refl n)) e.val = e.val
      have hf : (nestedBoxEmbedding (Nat.le_refl n) : _ → _) = id :=
        funext (fun x => Subtype.ext rfl)
      simp [hf, Sym2.map_id]
    grind
  exact congrArg (fun A => A ∈ S) hC |>.to_iff

theorem openBoxProbabilityMeasure_observation_self :
    (openBoxProbabilityMeasure θ n).toMeasure (boxObservationEvent S) =
      FK.measure _ θ (FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box n)}) S := by
  rw [openBoxProbabilityMeasure_observation θ (Nat.le_refl n), nestedBoxEvent_refl]

@[simp] theorem boxObservation_openExtension_self
    (C : FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :
    boxObservation n (openExtension (box n) C) = C := by
  ext e
  unfold boxObservation
  rw [FK.mem_boolConfigurationEquiv, openExtension_at, decide_eq_true_eq]

end
end PottsDiscontinuity.Potts
