module

public import proofs.RAFEmergenceApprox.ThresholdSweep
public import proofs.RAFEmergenceApprox.GenericHistory
public import proofs.HordijkSteelThreshold.WordContourProbability
public import proofs.HordijkSteelThreshold.WordEffectiveClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval
open RAFEmergenceApprox.Generic
open scoped ENNReal

variable (p : I)

variable (k : ℕ)

noncomputable def fixedPoolParameter   : I := σ $ (σ p)^k

@[simp] theorem fixedPoolParameter_coe   :
    (fixedPoolParameter p k : ℝ) = 1-(1-(p : ℝ))^k := by
  rfl


theorem union_card_le {Ω X R : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset X)
    (t : Finset R) (E : X → R → Set Ω) {c : ℝ≥0∞} (hc : ∀ x r, μ (E x r) = c) {a b : ℕ}
    (hs : s.card ≤ a) (ht : t.card ≤ b) :
    μ {ω | ∃ x ∈ s, ∃ r ∈ t, ω ∈ E x r} ≤ a * b * c := by
  calc _ = μ (⋃ x ∈ s, ⋃ r ∈ t, E x r) := by congr 1; ext; simp
    _ ≤ ∑ x ∈ s, ∑ r ∈ t, μ (E x r) := (measure_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum fun _ _ => measure_biUnion_finset_le _ _)
    _ ≤ _ := by
      simp only [hc, Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
      gcongr

theorem ambient_eq_law (n : ℕ) (lambda : ℝ) :
    ambientPiMeasure n lambda = (RAFEmergenceApprox.Generic.law (X := Molecule n)
      (fun _ : Reaction n => catalysisP n lambda)).map (fun ω c => ω c.2 c.1) := by
  rw [ambientPiMeasure, Measure.infinitePi_eq_pi]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (by fun_prop) $ .univ_pi hs]
  have : (fun ω c => ω c.2 c.1) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun r => Set.univ.pi fun x => s (x,r)) := by
    grind
  simp [this, RAFEmergenceApprox.Generic.law, RAFEmergenceApprox.Generic.colLaw,
    Fintype.prod_prod_type_right]

variable {X R : Type*} [Fintype X] [Fintype R]

theorem law_coord (p : R → I) (r : R) (x : X) : law (X := X) p {ω | ω r x} = toNNReal (p r) :=
  ((measurePreserving_eval (colLaw X $ p ·) r).measure_preimage (s := {v | v x})
    (by measurability)).trans $ ((measurePreserving_eval (fun _ => ambientCoordLaw $ p r) x).measure_preimage
    (s := {P | P}) $ by measurability).trans $ by simp [ambientCoordLaw]

theorem pool_statistic  (C : Finset X) (stat : Finset R → Prop) :
    law (X := X) (fun _ => p) {ω | stat $ RAFEmergenceApprox.Generic.catalystActive ω C} =
      Measure.pi (fun _ : R => ambientCoordLaw $ fixedPoolParameter p C.card)
        {q | stat $ Finset.univ.filter q} := by
  have : (law (X := X) (fun _ : R => p)).map (fun ω r => ∃ x ∈ C, ω r x) =
      Measure.pi (fun _ : R => ambientCoordLaw $ fixedPoolParameter p C.card) := by
    rw [law, Measure.pi_map_pi (f := fun _ (v : X → Prop) => ∃ x ∈ C, v x)
      (fun _ => (measurable_of_finite _).aemeasurable)]
    refine congrArg _ $ funext fun r => probability_prop_eq_of_false _ _ (measurable_of_finite _) ?_
    rw [closed_probability]
    simp [fixedPoolParameter, ambientCoordLaw]
    rfl
  rw [← this, Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  rfl

theorem mass_ge_static  (closure : Finset R → Finset X) (hclosure : Monotone closure)
    (k T : ℕ) :
    Measure.pi (fun _ : R => ambientCoordLaw $ fixedPoolParameter p (finiteInitialSegment X k).card)
      {q | k ≤ (closure $ Finset.univ.filter q).card} ≤
    law (X := X) (fun _ => p) {ω | k ≤ (closure $ peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω) closure T).card} := by
  rw [← pool_statistic p _ $ fun A => k ≤ (closure A).card]
  have he := congrArg (· {H | k ≤ (closure $ Finset.univ.filter $ H $ Fin.last T).card})
    (activeTrace_map_eq_scalar (X := X) (fun _ => p) closure hclosure T)
  unfold activeTrace at he
  simp only [Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet, Set.preimage,
    Set.mem_ofPred_eq, Finset.filter_mem_eq_inter, Finset.univ_inter, Fin.val_last] at he
  rw [he]
  refine measure_mono fun ω hω => hω.trans $ Finset.card_le_card $ hclosure ?_
  exact RAFEmergenceApprox.scalar_barrier_subset _ closure
    ((RAFEmergenceApprox.Generic.catalystActive_mono ω).comp $ finiteInitialSegment_mono _) hclosure k
    (hω.trans $ Finset.card_le_univ _) hω T

end HordijkSteelThreshold
