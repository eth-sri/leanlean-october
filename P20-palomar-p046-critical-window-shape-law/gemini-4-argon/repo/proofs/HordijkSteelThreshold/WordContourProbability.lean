module

public import proofs.HordijkSteelThreshold.WordDetourSelection
public import proofs.HordijkSteelThreshold.DisjointDetourProbability

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer unitInterval

def contourDetoursFailed {L N w : ℕ} {Ω : Type*} (hL : 2*w ≤ L)
    (C : Finset (WordBasicEdge L N)) (field : Reaction N → Ω → Prop) (ω : Ω) : Prop :=
  ∀ d ∈ wordContourDetours w C, detourFailed field (wordDetourSourceReactions hL d) ω

noncomputable def staticReactionMeasure (N : ℕ) (a : I) : Measure (Reaction N → Prop) :=
  Measure.infinitePi (fun _ => ambientCoordLaw a)

noncomputable instance staticReactionMeasure_probability (N : ℕ) (a : I) :
    IsProbabilityMeasure (staticReactionMeasure N a) := by
  unfold staticReactionMeasure; infer_instance

theorem staticReaction_contour_failure {L N w k : ℕ} (hL : 2*w ≤ L)
    (hk : 5*k ≤ w) (C : Finset (WordBasicEdge L N)) (a : I) :
    staticReactionMeasure N a {ω | contourDetoursFailed hL C (fun r ω => ω r) ω} ≤
      ((1-(toNNReal a : ENNReal)^2)^k)^C.card := by
  obtain ⟨T, hT, hd, hc⟩ := wordContour_disjoint_detours hL C
  have hkt : k * C.card ≤ T.card := by have := Nat.mul_le_mul_right C.card hk; nlinarith
  have hopen (r : Reaction N) : staticReactionMeasure N a {ω | ω r} = (toNNReal a : ENNReal) := by
    have h : staticReactionMeasure N a ((fun ω => ω r) ⁻¹' {True}) = (toNNReal a : ENNReal) := by
      rw [staticReactionMeasure, ← Measure.map_apply (measurable_pi_apply r) (.singleton True),
        Measure.infinitePi_map_eval]
      simp [ambientCoordLaw]
    simpa only [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true] using h
  refine (measure_mono (t := {ω | ∀ d ∈ T, detourFailed (fun r ω => ω r) (wordDetourSourceReactions hL d) ω})
      fun _ (h : contourDetoursFailed _ _ _ _) d hdT => h d (hT hdT)).trans <|
    (measure_disjoint_detours_failed_le (staticReactionMeasure N a) (fun r ω => ω r)
      (iIndepFun_infinitePi fun _ => measurable_id) (fun r => measurable_pi_apply r)
      (toNNReal a : ENNReal) (by exact_mod_cast a.2.2) hopen
      (wordDetourSourceReactions hL) T hd fun d _ => wordDetourSourceReactions_card hL d).trans <|
    (pow_le_pow_of_le_one zero_le tsub_le_self hkt).trans_eq (pow_mul _ _ _)

end HordijkSteelThreshold
