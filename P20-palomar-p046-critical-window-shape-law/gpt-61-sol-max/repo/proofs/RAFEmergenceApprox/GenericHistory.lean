
import proofs.HordijkSteelThreshold.CatalystPoolBlocks
import proofs.HordijkSteelThreshold.PeelingHistory
import Mathlib.Tactic




namespace HordijkSteelThreshold

variable (P : ℕ → Prop)

/-- A decreasing Boolean history is on exactly before its death index.
Death zero means initially absent; death T+1 means surviving the horizon. -/
def decreasingHistory  (T d : ℕ)  :=
  ∀ t ≤ T, P t ↔ t < d

/-- Exact column weight, including initially absent and horizon-surviving
columns. Only cardinalities of deterministic nested pools enter. -/
noncomputable def columnHistoryWeight (q : ENNReal) (sizes : ℕ → ℕ) (T d : ℕ)  :=
  if d = 0 then q ^ sizes 0
  else if T < d then 1 - q ^ sizes T
  else q ^ sizes d - q ^ sizes (d - 1)

variable (X : Type*)

variable [Fintype X]

/-- Deterministic nested sets realizing every possible finite pool size. -/
noncomputable def finiteInitialSegment   (k : ℕ)  :=
  (Finset.univ.filter fun i : Fin (Fintype.card X) => i.val < k).map
    (Fintype.equivFin X).symm.toEmbedding

theorem finiteInitialSegment_mono   :
    Monotone (finiteInitialSegment X) := by
  intro a b hab
  apply Finset.map_subset_map.mpr
  grind

theorem card_finiteInitialSegment  
    (k : ℕ) (hk : k ≤ Fintype.card X) :
    (finiteInitialSegment X k).card = k := by
  rw [finiteInitialSegment, Finset.card_map, Fin.card_filter_val_lt, min_eq_right hk]

end HordijkSteelThreshold

namespace RAFEmergenceApprox.Generic
open MeasureTheory unitInterval HordijkSteelThreshold

variable {X R : Type*} [Fintype X] [Fintype R]

noncomputable def colLaw (X : Type*) [Fintype X] (p : I)  :=
  Measure.pi (fun _ : X => ambientCoordLaw p)

instance colLaw_probability (p : I) : IsProbabilityMeasure (colLaw X p) := by
  unfold colLaw
  infer_instance

variable (p : R → I)

noncomputable def law : Measure (R → X → Prop) :=
  Measure.pi (fun r => colLaw X (p r))

instance law_probability  : IsProbabilityMeasure (law (X := X) p) := by
  unfold law
  infer_instance

variable (ω : R → X → Prop)

variable (C : Finset X) (r : R)

def catalystPoolOpen    :=
  ∃ x ∈ C, ω r x

theorem closed_probability (p : I) (C : Finset X) :
    colLaw X p {v | ¬ ∃ x ∈ C, v x} = toNNReal (σ p)^C.card := by
  simpa [colLaw,Set.pi,ambientCoordLaw] using
    (Measure.pi_pi_finset (μ := fun _ : X => ambientCoordLaw p) (fun _ => {False}) C)

noncomputable def catalystActive  
    (C : Finset X) : Finset R := by
  classical
  exact Finset.univ.filter (catalystPoolOpen ω C)

omit [Fintype X] in
theorem catalystActive_mono   :
    Monotone (catalystActive ω) := by
  intro C D h r hr
  grind [catalystActive, RAFEmergenceApprox.Generic.catalystPoolOpen]

variable (closure : Finset R → Finset X) (hclosure : Monotone closure) (T : ℕ)
include hclosure

theorem peeling_statistic_eq_scalar (stat : Finset R → Prop) :
    law (X := X) p {ω | stat (peelingActiveAt (catalystActive ω) closure T)} =
    law (X := X) p {ω | stat (peelingActiveAt
      (fun C => catalystActive ω (finiteInitialSegment X C.card)) closure T)} := by
  classical
  let trace (response : Finset X → Finset R) : Fin (T+1) → Finset R :=
    fun t => peelingActiveAt response closure t
  have h : (law p).map (fun ω => trace (catalystActive ω)) =
      (law p).map (fun ω => trace (fun C => catalystActive ω (finiteInitialSegment X C.card))) := by
    apply Measure.ext_of_singleton
    intro H
    let history := fun t => H ⟨min t T, by omega⟩
    have he (response : Finset X → Finset R) :
        trace response = H ↔ ∀ t ≤ T, peelingActiveAt response closure t = history t := by
      simp +contextual [trace, funext_iff, Fin.forall_iff, history]
    simp only [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton H),
      Set.preimage, Set.mem_singleton_iff, he]
    by_cases hg : Antitone history
    ·
      choose death hpattern using fun r : R => show ∃ d, ∀ t ≤ T, r ∈ history t ↔ t < d from by
        by_cases h : ∃ t, r ∉ history t
        · refine ⟨Nat.find h, ?_⟩
          intro t ht
          constructor
          · grind [Antitone]
          simp_all
        · refine ⟨T + 1, ?_⟩
          simp_all
      have he (transform : Finset X → Finset X) :
          {ω : R → X → Prop | ∀ t ≤ T,
            peelingActiveAt (fun C => catalystActive ω (transform C)) closure t = history t} =
          {ω | ∀ r, decreasingHistory
            (fun t => catalystPoolOpen ω (transform (prescribedPoolAt closure history t)) r) T (death r)} := by
        
        simp only [peeling_history_iff]
        simp [Finset.ext_iff, decreasingHistory, catalystActive]
        aesop
      have hm (C : ℕ → Finset X) (hC : Antitone C) :
          law p {ω | ∀ r, decreasingHistory (fun t => catalystPoolOpen ω (C t) r) T (death r)} =
            ∏ r, columnHistoryWeight (toNNReal (σ (p r))) (fun t => (C t).card) T (death r) := by
        rw [show {ω | ∀ r, decreasingHistory (fun t => catalystPoolOpen ω (C t) r) T (death r)} =
            Set.univ.pi (fun r => {v | decreasingHistory (fun t => ∃ x ∈ C t, v x) T (death r)}) by
          simp [Set.pi, catalystPoolOpen], law, Measure.pi_pi]
        apply Finset.prod_congr rfl
        intro r _
        generalize death r = d
        let pr := p r
        have hm (v : X → Prop) (a b : ℕ) (hab : a ≤ b) :
            (∃ x ∈ C b, v x) → ∃ x ∈ C a, v x := by tauto
        let E (t : ℕ) := {v : X → Prop | ¬ ∃ x ∈ C t, v x}
        have he (P : ℕ → Prop) (hP : ∀ a b, a ≤ b → P b → P a) :
            decreasingHistory P T d ↔ if d = 0 then ¬ P 0 else if T < d then P T else ¬ P d ∧ P (d-1) := by
          clear * - hP
          split_ifs <;> grind [decreasingHistory]
        simp_rw [he _ (hm _)]
        unfold columnHistoryWeight
        split_ifs with hz hs
        · exact closed_probability pr (C 0)
        · simpa only [E, Set.compl_ofPred, not_not, closed_probability, measure_univ] using
            measure_compl (μ := colLaw X pr) (s := E T) (Set.toFinite _).measurableSet (measure_ne_top _ _)
        · simpa only [E, Set.sdiff_eq, Set.inter_ofPred_eq_sep, Set.mem_ofPred_eq, Set.compl_ofPred,
            not_not, closed_probability] using
            measure_sdiff (μ := colLaw X pr) (s₁ := E d) (s₂ := E (d-1))
              (by intro v hv hp; exact hv (hm v (d-1) d (by omega) hp))
              (Set.toFinite _).measurableSet.nullMeasurableSet (measure_ne_top _ _)
      have hid := he id
      dsimp only [id] at hid
      simp_all
      have hc : Antitone (prescribedPoolAt closure history) := by
                   apply antitone_nat_of_succ_le
                   simp_all [prescribedPoolAt] ; aesop
      rw [hm _ hc, hm _ (fun a b h => finiteInitialSegment_mono X (Finset.card_le_card (hc h)))]
      simp_rw [card_finiteInitialSegment X _ (Finset.card_le_univ _)]
    · have empty (A : (R → X → Prop) → ℕ → Finset R) (hA : ∀ ω, Antitone (A ω)) :
          {ω | ∀ t ≤ T, A ω t = history t} = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun ω h => hg (by grind [Antitone])
      rw [empty _ fun ω => peelingActiveAt_antitone _ _ (catalystActive_mono ω) hclosure,
        empty _ (fun ω => peelingActiveAt_antitone _ _ (by
          intro C D h
          exact catalystActive_mono ω (finiteInitialSegment_mono X (Finset.card_le_card h))) hclosure)]
  replace h := congrArg (fun μ => μ {H | stat (H ⟨T, Nat.lt_succ_self T⟩)}) h
  simpa [Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet, trace] using h


end RAFEmergenceApprox.Generic

namespace HordijkSteelThreshold
open MeasureTheory RAF.Polymer RAF.Concrete

noncomputable def catalystActive {n : ℕ} (ω : AmbientCoord n → Prop)
    (C : Finset (Molecule n)) : Finset (Reaction n) := by
  classical
  exact Finset.univ.filter (catalystPoolOpen ω C)

theorem ambient_columns_map (n : ℕ) (lambda : ℝ) :
    (ambientPiMeasure n lambda).map (fun ω r x => ω (x,r)) =
      RAFEmergenceApprox.Generic.law (X := Molecule n) (fun _ : Reaction n => catalysisP n lambda) := by
  let S := MeasurableEquiv.piCongrLeft (fun _ : Reaction n × Molecule n => Prop)
    (Equiv.prodComm (Molecule n) (Reaction n))
  let C := MeasurableEquiv.curry (Reaction n) (Molecule n) Prop
  change (ambientPiMeasure n lambda).map (C ∘ S) = _
  rw [← Measure.map_map C.measurable S.measurable]
  change ((Measure.infinitePi _).map S).map C = _
  rw [Measure.infinitePi_map_piCongrLeft
    (fun _ : Reaction n × Molecule n => ambientCoordLaw (catalysisP n lambda))
    (Equiv.prodComm (Molecule n) (Reaction n)),
    Measure.infinitePi_map_curry (fun _ _ => ambientCoordLaw (catalysisP n lambda))]
  simp_rw [Measure.infinitePi_eq_pi]
  rfl

end HordijkSteelThreshold
