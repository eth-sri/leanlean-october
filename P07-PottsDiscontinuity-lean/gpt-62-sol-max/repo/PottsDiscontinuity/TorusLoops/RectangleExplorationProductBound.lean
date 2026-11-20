module

public import PottsDiscontinuity.TorusLoops.RectangleRootCrossings
public import PottsDiscontinuity.TorusExploration.ConditionalConnectionBound

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open MeasureTheory Torus FK FK.FiniteProbability TorusExploration Zhang
open scoped Classical
noncomputable section
variable {N M : ℕ}
local instance rectangleExplorationEdgeFintype {V : Type*} [Finite V] (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite _

/-- The rectangle FK probability of an event, with the large graph and free
boundary condition bundled to keep exploration estimates readable. -/
@[irreducible] noncomputable def rectangleBaseEventProbability (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (Configuration (rectangleBaseGraph hN hM))) : ℝ :=
  (measure (rectangleBaseGraph hN hM) (rectangleFKParameters q)
    (BoundaryCondition.free ∅) E).toReal

/-- Free infinite-volume one-arm probability at radius `k` in the rotated
lattice. -/
@[irreducible] noncomputable def rectangleFreeOneArmProbability
    (q : Set.Ici (1 : ℝ)) (k : ℕ) : ℝ :=
  (((Classical.choose (freeBoxLimit_existsUnique (rectangleFKParameters q))
    (oneArmEvent k) : NNReal) : ℝ))

/-- All listed roots cross to the right in distinct actual open clusters. -/
def rectangleDistinctRootCrossingEvent (hN : Even N) (hM : Even M)
    (roots : List (FaceVertex N M true)) :
    Set (Configuration (rectangleBaseGraph hN hM)) :=
  {A | (∀ x ∈ roots, A ∈ rectangleRootCrossingEvent hN hM x) ∧
    roots.Nodup ∧
    (∀ x ∈ roots, ∀ y ∈ roots, x ≠ y →
      ¬ ActualConnected (rectangleBaseGraph hN hM) A x y)}

private theorem distinctRoots_record_invariant (hN : Even N) (hM : Even M)
    (roots : List (FaceVertex N M true)) (A B : Configuration (rectangleBaseGraph hN hM))
    (h : clusterRecord _ roots.toFinset B = clusterRecord _ roots.toFinset A) :
    B ∈ rectangleDistinctRootCrossingEvent hN hM roots ↔ A ∈ rectangleDistinctRootCrossingEvent hN hM roots := by
  have hr x (hx : x ∈ roots) y := seed_connection_iff_of_record _ _ _ _ h (List.mem_toFinset.mpr hx) y
  constructor
  · rintro ⟨hc, hn, hd⟩
    exact ⟨fun x hx => let ⟨v, hv, hr'⟩ := hc x hx; ⟨v, hv, (hr x hx v).1 hr'⟩,
      hn, fun x hx y hy hxy hh => hd x hx y hy hxy ((hr x hx y).2 hh)⟩
  · rintro ⟨hc, hn, hd⟩
    exact ⟨fun x hx => let ⟨v, hv, hr'⟩ := hc x hx; ⟨v, hv, (hr x hx v).2 hr'⟩,
      hn, fun x hx y hy hxy hh => hd x hx y hy hxy ((hr x hx y).1 hh)⟩

private theorem induced_crossing_le_oneArm (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (T : Set (FaceVertex N M true)) (u : T) (hu : u.val.val.1.val = 0) :
    (measure ((rectangleBaseGraph hN hM).induce T) (rectangleFKParameters q) (BoundaryCondition.free ∅)
      (rootedConnection _ u {v | v.val.val.1.val + 1 = N})).toReal ≤ rectangleFreeOneArmProbability q (N / 2 - 1) := by
  let G := rectangleBaseGraph hN hM
  let I := G.induce T
  let θ := rectangleFKParameters q
  let f := inducedVertexEmbedding T
  let hIG := inducedVertexGraph_le G T
  let E := rootedConnection I u {v | v.val.val.1.val + 1 = N}
  let W := rectangleRootCrossingEvent hN hM u.val
  let i := E.indicator (fun _ => (1 : ℝ))
  have hi : Monotone i := by
    intro A B hAB
    by_cases ha : A ∈ E
    · have hb : B ∈ E := by
        obtain ⟨v, hv, hr⟩ := ha
        exact ⟨v, hv, actualConnected_mono hAB hr⟩
      simp [i, ha, hb]
    · rw [show i A = 0 from Set.indicator_of_notMem ha _]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  rw [fk_measureReal_eq_expectation]
  refine (embedded_free_expectation_le I G f hIG θ ∅ ∅ i (Set.indicator_nonneg fun _ _ => zero_le_one) hi).trans ?_
  refine (expectation_mono _ _ (W.indicator fun _ => (1 : ℝ)) ?_).trans ?_
  · intro A
    let R := embeddedConfigurationRestriction I G f hIG A
    by_cases ha : R ∈ E
    · have hww : A ∈ W := by
        obtain ⟨v, hv, ⟨p⟩⟩ := ha
        exact ⟨v.val, hv, ⟨p.map ⟨Subtype.val, fun h => (inducedRestriction_open_adj G T A _ _).1 h⟩⟩⟩
      change i (R) ≤ _
      simp [i, ha, hww]
    · change i (R) ≤ _
      rw [show i R = 0 from Set.indicator_of_notMem ha _]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  · rw [← fk_measureReal_eq_expectation, ← rectangleFKEventProbability_eq_measure]
    simpa [rectangleFreeOneArmProbability] using
          rectangleFKProbability_rootCrossing_le_freeOneArm hN hM u.val hu q

/-- Explore the tail's clusters first, then charge at most one one-arm event for
 the new root. The record and the conditional law are the same as for the
 exploration of prescribed endpoint pairs. -/
private theorem rectangle_step (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (roots : List (FaceVertex N M true)) (u : FaceVertex N M true) (hu : u.val.1.val = 0) :
    rectangleBaseEventProbability hN hM q (rectangleDistinctRootCrossingEvent hN hM (u :: roots)) ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) *
        rectangleBaseEventProbability hN hM q (rectangleDistinctRootCrossingEvent hN hM roots) := by
  let G := rectangleBaseGraph hN hM
  let θ := rectangleFKParameters q
  let K : Set (FaceVertex N M true) := {v | v.val.1.val + 1 = N}
  let E := rectangleDistinctRootCrossingEvent hN hM roots
  let H := freshConnection G roots.toFinset u K
  have hsubset : rectangleDistinctRootCrossingEvent hN hM (u :: roots) ⊆ E ∩ H := by
    rintro A ⟨hc, hn, hd⟩
    refine ⟨⟨fun x hx => hc x (List.mem_cons_of_mem u hx), (List.nodup_cons.mp hn).2,
        fun x hx y hy => hd x (List.mem_cons_of_mem u hx) y (List.mem_cons_of_mem u hy)⟩,
      ?_, hc u (List.mem_cons_self ..)⟩
    rintro ⟨x, hx, hr⟩
    have hx' := List.mem_toFinset.mp hx
    exact hd x (List.mem_cons_of_mem u hx') u (List.mem_cons_self ..)
      (fun he => (List.nodup_cons.mp hn).1 (he ▸ hx')) hr
  have hρ : 0 ≤ rectangleFreeOneArmProbability q (N / 2 - 1) := by simp [rectangleFreeOneArmProbability]
  unfold rectangleBaseEventProbability
  refine (MeasureTheory.measureReal_mono hsubset).trans ?_
  simp only [MeasureTheory.Measure.real_def, fk_measureReal_eq_expectation]
  exact record_step_le (law G θ (BoundaryCondition.free ∅)) (fkLaw_full_support G θ _) (clusterRecord G roots.toFinset)
    E H (distinctRoots_record_invariant hN hM roots) _
    (fun A _ => freshConnection_conditional_le G θ roots.toFinset A u K _ hρ
      (fun hx => induced_crossing_le_oneArm hN hM q _ ⟨u, hx⟩ hu))

/-- The probability of distinct left-to-right crossings from any finite list
of left-boundary roots is at most the one-arm probability to the list length. -/
theorem rectangleDistinctRootCrossingEvent_probability_le_pow
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (roots : List (FaceVertex N M true))
    (hleft : ∀ u ∈ roots, u.val.1.val = 0) :
    rectangleBaseEventProbability hN hM q
        (rectangleDistinctRootCrossingEvent hN hM roots) ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) ^ roots.length := by
  classical
  have hρ : 0 ≤ rectangleFreeOneArmProbability q (N / 2 - 1) := by
    simp [rectangleFreeOneArmProbability]
  induction roots with
  | nil =>
      simp [rectangleDistinctRootCrossingEvent, rectangleBaseEventProbability,
        PottsDiscontinuity.FK.measure]
  | cons u roots ih =>
      have hu := hleft u (by simp)
      have htail : ∀ x ∈ roots, x.val.1.val = 0 := by
        intro x hx
        exact hleft x (by simp [hx])
      calc
        rectangleBaseEventProbability hN hM q
            (rectangleDistinctRootCrossingEvent hN hM (u :: roots)) ≤
            rectangleFreeOneArmProbability q (N / 2 - 1) *
              rectangleBaseEventProbability hN hM q
                (rectangleDistinctRootCrossingEvent hN hM roots) := rectangle_step hN hM q roots u hu
        _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) *
              rectangleFreeOneArmProbability q (N / 2 - 1) ^ roots.length :=
          mul_le_mul_of_nonneg_left (ih htail) hρ
        _ = rectangleFreeOneArmProbability q (N / 2 - 1) ^ (roots.length + 1) := by
          rw [pow_succ]
          ring

end
end PottsDiscontinuity.TorusLoops
