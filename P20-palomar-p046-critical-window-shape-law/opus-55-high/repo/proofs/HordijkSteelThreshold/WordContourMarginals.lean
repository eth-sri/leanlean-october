module

public import proofs.HordijkSteelThreshold.WordContourProbability
public import proofs.HordijkSteelThreshold.WordMoleculeContourCount
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer unitInterval

theorem wordMoleculeContourEnvelope_member_card {L N b : ℕ} {s : List Bool}
    {C : Finset $ WordBasicEdge L N} (hC : C ∈ wordMoleculeContourEnvelope L N s b) :
    C.card = b := by
  obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hC
  exact (Finset.mem_filter.mp he).2.1

noncomputable def contourBudget (a : I) (k : ℕ) : ENNReal :=
  (molecularContourConstant : ENNReal) * (1-(toNNReal a : ENNReal)^2)^k

/-- A per-molecule envelope of all positive-size disabled contours. Its
probability bounds actual smaller-side membership by the compiled anchor theorem. -/
def moleculeContourBad {L N w : ℕ} (hL : 2*w ≤ L) (s : List Bool)
    (ω : Reaction N → Prop) : Prop :=
  ∃ j : ℕ, ∃ C ∈ wordMoleculeContourEnvelope L N s $ j+1,
    contourDetoursFailed hL C (fun r ω => ω r) ω

/-- Uniform bad-side marginal; no independence between contours is required. -/
theorem measure_moleculeContourBad_le {L N w k : ℕ} (hL : 2*w ≤ L)
    (hk : 5*k ≤ w) (s : List Bool) (a : I) :
    staticReactionMeasure N a {ω | moleculeContourBad hL s ω} ≤
      contourBudget a k / (1-contourBudget a k) := by
  calc
    _ ≤ ∑' j : ℕ, ∑ C ∈ wordMoleculeContourEnvelope L N s $ j+1, staticReactionMeasure N a
        {ω | contourDetoursFailed hL C (fun r ω => ω r) ω} :=
      (measure_mono $ by exact fun ω ⟨j, C, hC, h⟩ => Set.mem_iUnion.2 ⟨j, Set.mem_biUnion hC h⟩).trans
        ((measure_iUnion_le _).trans $ ENNReal.tsum_le_tsum fun j => measure_biUnion_finset_le _ _)
    _ ≤ ∑' j : ℕ, ∑ _C ∈ wordMoleculeContourEnvelope L N s $ j+1, ((1-(toNNReal a : ENNReal)^2)^k)^(j+1) :=
      ENNReal.tsum_le_tsum fun j => Finset.sum_le_sum fun C hC => by
        rw [← wordMoleculeContourEnvelope_member_card hC]
        set F := fun r (ω : Reaction N → Prop) => ω r
        obtain ⟨T, hT, hd, hc⟩ := wordContour_disjoint_detours hL C
        have hkt : k*C.card ≤ T.card := by nlinarith
        calc
          _ ≤ staticReactionMeasure N a {ω | ∀ d ∈ T, detourFailed F (wordDetourSourceReactions hL d) ω} :=
            measure_mono $ by tauto
          _ ≤ (1-(toNNReal a)^2)^T.card := by
            have hind : iIndepFun F (staticReactionMeasure N a) :=
              iIndepFun_pi fun _ => aemeasurable_id
            have hmarg r : staticReactionMeasure N a {ω | ω r} = toNNReal a :=
              ((measurePreserving_eval (fun _ => ambientCoordLaw a) r).measure_preimage (s := {P | P})
                (by measurability)).trans $ by simp [ambientCoordLaw]
            clear hkt hc hT
            induction T using Finset.induction_on with
            | empty => simp
            | @insert i T hi ih =>
              have hp := (show IndepFun (detourFailed F $ wordDetourSourceReactions hL i)
                (∀ j ∈ T, detourFailed F (wordDetourSourceReactions hL j) ·) _ from
                (hind.indepFun_finset _ (T.biUnion _) ((Finset.disjoint_biUnion_right ..).2 $ by grind)
                measurable_pi_apply).comp
                (measurable_of_finite fun v : wordDetourSourceReactions hL i → Prop =>
                  ¬ ∀ r, ∀ hr : r ∈ wordDetourSourceReactions hL i, v ⟨r,hr⟩)
                (measurable_of_finite fun v : T.biUnion (wordDetourSourceReactions hL) → Prop => ∀ j, ∀ hj : j ∈ T,
                  ¬ ∀ r, ∀ hr : r ∈ wordDetourSourceReactions hL j, v ⟨r, Finset.mem_biUnion.mpr ⟨j,hj,hr⟩⟩)
                ).measure_inter_preimage_eq_mul {True} {True} (.singleton True) $ .singleton True
              simp only [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true] at hp
              simp_rw [Finset.forall_mem_insert, Set.ofPred_and]
              rw [hp, Finset.card_insert_of_notMem hi, pow_succ',
                show {ω | detourFailed F (wordDetourSourceReactions hL i) ω} =
                  (⋂ r ∈ wordDetourSourceReactions hL i, F r ⁻¹' {True})ᶜ by
                  ext; simp [detourFailed, F],
                prob_compl_eq_one_sub $ Finset.measurableSet_biInter _ fun r _ => measurable_pi_apply r $ .singleton _,
                hind.measure_inter_preimage_eq_mul _ (sets := fun _ => {True}) fun _ _ => .singleton _]
              simp only [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true, F, hmarg, Finset.prod_const]
              exact mul_le_mul' (tsub_le_tsub_left (pow_le_pow_of_le_one zero_le (by exact_mod_cast a.property.2)
                (wordDetourSourceReactions_card hL i)) _) $ ih $ by simp_all
          _ ≤ (1-(toNNReal a)^2)^(k*C.card) := pow_le_pow_of_le_one zero_le tsub_le_self hkt
          _ = _ := pow_mul _ _ _
    _ ≤ ∑' j : ℕ, (contourBudget a k)^(j+1) := ENNReal.tsum_le_tsum fun j => by
      rw [Finset.sum_const, nsmul_eq_mul, contourBudget, mul_pow]
      gcongr
      exact_mod_cast wordMoleculeContourEnvelope_card L N s _ $ by omega
    _ = _ := by rw [ENNReal.tsum_geometric_add_one, div_eq_mul_inv]

end HordijkSteelThreshold
