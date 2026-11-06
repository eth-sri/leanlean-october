module

public import proofs.RAFEmergenceApprox.GenericHistory
public import proofs.RAFEmergenceApprox.ThresholdSweep
public import proofs.HordijkSteelThreshold.InfiniteProductTranspose
public import proofs.HordijkSteelThreshold.WordContourProbability
public import proofs.HordijkSteelThreshold.WordEffectiveClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

noncomputable def fixedPoolParameter (p : I) (k : ℕ) : I := σ ((σ p)^k)

variable {X R : Type*} [Fintype X] [Fintype R]

theorem pool_statistic (p : I) (C : Finset X) (stat : Finset R → Prop) :
    RAFEmergenceApprox.Generic.law (X := X) (fun _ : R => p)
      {ω | stat (RAFEmergenceApprox.Generic.catalystActive ω C)} =
      RAFEmergenceApprox.Generic.colLaw R (fixedPoolParameter p C.card)
        {q | stat (Finset.univ.filter q)} := by
  have hcol : (RAFEmergenceApprox.Generic.colLaw X p).map (fun v => ∃ x ∈ C, v x) =
      ambientCoordLaw (fixedPoolParameter p C.card) := by
    apply probability_prop_eq_of_false
    rw [Measure.map_apply (measurable_of_finite _) (.singleton _),
      show (fun v : X → Prop => ∃ x ∈ C, v x) ⁻¹' {False} = {v | ¬ ∃ x ∈ C, v x} by ext; simp,
      RAFEmergenceApprox.Generic.closed_probability, ambientCoordLaw_false]
    simp only [fixedPoolParameter, symm_symm, ← ENNReal.coe_pow]
    congr 1
  have hmap : (RAFEmergenceApprox.Generic.law (X := X) (fun _ : R => p)).map (fun ω r => ∃ x ∈ C, ω r x) =
      RAFEmergenceApprox.Generic.colLaw R (fixedPoolParameter p C.card) := by
    change (Measure.pi (fun _ : R => RAFEmergenceApprox.Generic.colLaw X p)).map _ = _
    rw [Measure.pi_map_pi (f := fun (_ : R) (v : X → Prop) => ∃ x ∈ C, v x)
      (fun _ => (measurable_of_finite _).aemeasurable)]
    simp_rw [hcol]; rfl
  rw [← hmap, Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  congr 1; ext ω; exact Iff.of_eq (congrArg stat (by ext; simp))

theorem mass_ge_static (p : I) (closure : Finset R → Finset X)
    (hclosure : Monotone closure) (k T : ℕ) :
    RAFEmergenceApprox.Generic.colLaw R (fixedPoolParameter p (finiteInitialSegment X k).card)
      {q | k ≤ (closure (Finset.univ.filter q)).card} ≤
    RAFEmergenceApprox.Generic.law (X := X) (fun _ : R => p)
      {ω | k ≤ (closure (peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω) closure T)).card} := by
  rw [← pool_statistic p (finiteInitialSegment X k) (fun A => k ≤ (closure A).card),
    RAFEmergenceApprox.Generic.peeling_statistic _ closure hclosure T (fun A => k ≤ (closure A).card)]
  refine measure_mono fun ω hω => hω.trans <| Finset.card_le_card <| hclosure <|
    RAFEmergenceApprox.scalar_barrier_subset _ closure
      ((RAFEmergenceApprox.Generic.catalystActive_mono ω).comp (finiteInitialSegment_mono _))
      hclosure k (hω.trans (Finset.card_le_univ _)) hω T

noncomputable abbrev catalystActive {n : ℕ} (ω : AmbientCoord n → Prop)
    (C : Finset (Molecule n)) : Finset (Reaction n) :=
  RAFEmergenceApprox.Generic.catalystActive (fun r x => ω (x, r)) C

@[simp] theorem mem_catalystActive {n : ℕ} (ω : AmbientCoord n → Prop)
    (C : Finset (Molecule n)) (r : Reaction n) :
    r ∈ catalystActive ω C ↔ ∃ x ∈ C, ω (x, r) :=
  RAFEmergenceApprox.Generic.mem_catalystActive _ C r

theorem catalystActive_mono {n : ℕ} (ω : AmbientCoord n → Prop) :
    Monotone (catalystActive ω) :=
  RAFEmergenceApprox.Generic.catalystActive_mono _

theorem ambientPi_map_law (n : ℕ) (lambda : ℝ) :
    (ambientPiMeasure n lambda).map (fun ω (r : Reaction n) (x : Molecule n) => ω (x, r)) =
      RAFEmergenceApprox.Generic.law (X := Molecule n) (fun _ : Reaction n => catalysisP n lambda) := by
  change (ambientPiMeasure n lambda).map (MeasurableEquiv.curry (Reaction n) (Molecule n) Prop ∘
    MeasurableEquiv.piCongrLeft (fun _ : Reaction n × Molecule n => Prop) (Equiv.prodComm (Molecule n) (Reaction n))) = _
  rw [← Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _), ambientPiMeasure,
    Measure.infinitePi_map_piCongrLeft (fun _ : Reaction n × Molecule n => ambientCoordLaw (catalysisP n lambda)),
    Measure.infinitePi_map_curry (fun (_ : Reaction n) (_ : Molecule n) => ambientCoordLaw (catalysisP n lambda))]
  simp [RAFEmergenceApprox.Generic.law, RAFEmergenceApprox.Generic.colLaw, Measure.infinitePi_eq_pi]

theorem fixedPool_closure_statistic {n : ℕ} (lambda : ℝ) (C : Finset (Molecule n))
    (closure : Finset (Reaction n) → Finset (Molecule n)) (P : Finset (Molecule n) → Prop) :
    ambientPiMeasure n lambda {ω | P (closure (catalystActive ω C))} =
      staticReactionMeasure n (fixedPoolParameter (catalysisP n lambda) C.card)
        {ω | P (closure (staticOpenReactions ω))} := by
  have h := pool_statistic (R := Reaction n) (catalysisP n lambda) C (fun S => P (closure S))
  rw [← ambientPi_map_law n lambda, Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet] at h
  simpa [staticReactionMeasure, RAFEmergenceApprox.Generic.colLaw, Measure.infinitePi_eq_pi, staticOpenReactions] using h

theorem source_mass_ge_iid_static {n : ℕ} (lambda : ℝ)
    (closure : Finset (Reaction n) → Finset (Molecule n)) (hclosure : Monotone closure) (k T : ℕ) :
    staticReactionMeasure n (fixedPoolParameter (catalysisP n lambda)
      (finiteInitialSegment (Molecule n) k).card) {ω | k ≤ (closure (staticOpenReactions ω)).card} ≤
    ambientPiMeasure n lambda {ω | k ≤ (closure (peelingActiveAt (catalystActive ω) closure T)).card} := by
  have h := mass_ge_static (R := Reaction n) (catalysisP n lambda) closure hclosure k T
  rw [← ambientPi_map_law n lambda, Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet] at h
  simpa [staticReactionMeasure, RAFEmergenceApprox.Generic.colLaw, Measure.infinitePi_eq_pi, staticOpenReactions] using h

end HordijkSteelThreshold
