
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Nat.Defs
import proofs.HordijkSteelThreshold.WordDetourSource
import proofs.HordijkSteelThreshold.CatalystPoolBlocks




namespace HordijkSteelThreshold

variable {L N w : ℕ}
open Classical

variable {I R : Type*} (S : Finset I) (support : I → Finset R)

/-- A finite family of supports of size at most two, each coordinate used at
most three times, has a pairwise-disjoint subfamily of at least one fifth its size. -/
theorem exists_disjoint_detours 
    (hsize : ∀ i ∈ S, (support i).card ≤ 2)
    (huse : ∀ r, (S.filter (fun j => r ∈ support j)).card ≤ 3) :
    ∃ T ⊆ S, (∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support i) (support j)) ∧
      S.card ≤ 5*T.card := by
  classical
  let detourConflicts (i : I) := (S.erase i).filter fun j => ¬ Disjoint (support i) (support j)
  let family := S.powerset.filter fun T =>
    ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support i) (support j)
  
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image family Finset.card ⟨∅, by simp [family]⟩
  simp only [family, Finset.mem_filter, Finset.mem_powerset] at hT
  refine ⟨T, hT.1, hT.2, ?_⟩
  
  calc
    S.card ≤ (T.biUnion fun j => insert j (detourConflicts j)).card :=
      Finset.card_le_card (by
                            intro i hi
                            by_cases hiT : i ∈ T
                            · exact Finset.mem_biUnion.mpr ⟨i, hiT, Finset.mem_insert_self _ _⟩
                            · have hex : ∃ j ∈ T, ¬ Disjoint (support i) (support j) := by
                                by_contra hn
                                
                                have hnew : insert i T ∈ family := by grind
                                simpa [hiT] using hmax _ hnew
                              
                              grind [Disjoint.symm])
    _ ≤ T.card * 5 := Finset.card_biUnion_le_card_mul _ _ _ (by
      intro j hj
      have hc : (detourConflicts j).card ≤ 4 := by
                   let hi := hT.1 hj
                   let hsize := hsize j (hT.1 hj)
                   classical
                   
                   calc
                     _ ≤ ((support j).biUnion fun r => (S.filter fun j => r ∈ support j).erase j).card :=
                       Finset.card_le_card (by
                                             intro j hj
                                             obtain ⟨hjS, hnot⟩ := Finset.mem_filter.mp hj
                                             obtain ⟨r, hri, hrj⟩ := Finset.not_disjoint_iff.mp hnot
                                             exact Finset.mem_biUnion.mpr ⟨r, hri, Finset.mem_erase.mpr
                                               ⟨(Finset.mem_erase.mp hjS).1, Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hjS).2, hrj⟩⟩⟩)
                     _ ≤ (support j).card * 2 := Finset.card_biUnion_le_card_mul _ _ _ (by
                       intro r hr
                       have hm : j ∈ S.filter fun j => r ∈ support j := Finset.mem_filter.mpr ⟨hi, hr⟩
                       have hc := Finset.card_erase_add_one hm
                       have hu := huse r
                       omega)
                     _ ≤ 4 := by omega
      exact (Finset.card_insert_le _ _).trans (by omega))
    _ = 5*T.card := Nat.mul_comm _ _

noncomputable def wordContourDetours {L N : ℕ} (w : ℕ)
    (C : Finset (WordBasicEdge L N)) : Finset (WordShortKey L N w) :=
  C.product Finset.univ


variable {R Ω : Type*}

def detourFailed  (field : R → Ω → Prop) (B : Finset R) (ω : Ω)  :=
  ¬ ∀ r ∈ B, field r ω





open MeasureTheory ProbabilityTheory RAF.Polymer unitInterval

/-- All w detours for every edge of the fixed contour fail. -/
def contourDetoursFailed {L N w : ℕ} {Ω : Type*} (hL : _ ≤ L)
    (C : _) (field : Reaction N → _) (ω : Ω)  :=
  ∀ d ∈ wordContourDetours w C, detourFailed field (wordDetourSourceReactions hL d) ω

variable {k : ℕ}

/- Integer amplification k avoids fractional-power rounding: choose w>=5*k.
At w=5*k this is the paper exponent w*|C|/5 exactly. -/

section
variable (N : ℕ) (a : I)

/-- The literal iid static reaction field; distinct split-position IDs are coordinates. -/
noncomputable def staticReactionMeasure  : Measure (Reaction N → Prop) :=
  Measure.pi fun _ => ambientCoordLaw a

noncomputable instance staticReactionMeasure_probability  :
    IsProbabilityMeasure (staticReactionMeasure N a) := by
  unfold staticReactionMeasure
  infer_instance






end

set_option maxHeartbeats 800000 in
/-- Unconditional fixed-contour failure estimate in the actual iid source field. -/
theorem staticReaction_contour_failure  (hL : 2*w ≤ L)
    (hk : 5*k ≤ w) (C : _) (a : I) :
    staticReactionMeasure N a {ω | contourDetoursFailed hL C (fun r ω => ω r) ω} ≤
      ((1-toNNReal a^2)^k)^C.card := by
  let μ := staticReactionMeasure N a
  let field : Reaction N → (Reaction N → Prop) → Prop := fun r ω => ω r
  let b : ENNReal := toNNReal a
  have hb : (toNNReal a : ENNReal) ≤ 1 := by exact_mod_cast a.property.2
  let z0 := 1-b^2
  classical
  obtain ⟨T, hT, hd, hc⟩ := exists_disjoint_detours (wordContourDetours w C)
    (wordDetourSourceReactions hL)
    (fun d _ => wordDetourSourceReactions_card hL d) (by
      intro b
      have hsub : ((wordContourDetours w C).filter fun d =>
          b ∈ wordDetourSourceReactions hL d) ⊆
          Finset.univ.filter fun d => b ∈ wordDetourSourceReactions hL d := Finset.filter_subset_filter _ (Finset.subset_univ _)
      convert (Finset.card_le_card hsub).trans ((by
                                                  by_cases ha : ∃ r : WordShortKey L N w, wordShortSourceOption hL r = some b
                                                  · obtain ⟨r, hr⟩ := ha
                                                  
                                                    exact (Finset.card_le_card (by
                                                                                 intro d hd
                                                                                 obtain ⟨s, hs, hsa⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hd).2
                                                                                 have he  := Option.mem_toFinset.mp hsa
                                                                                 have hsr : s = r := by
                                                                                   simp only [wordShortSourceOption] at he hr
                                                                                   split_ifs at he hr <;> try contradiction
                                                                                   simp only [Option.some.injEq] at he hr
                                                                                   have hq := (Option.some.inj he).trans hr.symm
                                                                                   have hw := congrArg (fun a => (moleculeWord (RAF.Concrete.reactionProduct a), RAF.Concrete.reactionLeftLength a)) hq
                                                                                   simp at hw
                                                                                   cases hs : s.1.2 <;> cases hr : r.1.2 <;> grind [sourceShortSplit, sourceWordMolecule_length, boundedFoodWord_nonroot_length]
                                                                                 exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsr ▸ hs⟩)).trans (by
                                                      have hf := wordDetourLower_fiber_card r
                                                      simpa [wordDetourKeys, Finset.filter_or, Finset.filter_eq, eq_comm] using
                                                        (Finset.card_union_le {r} (Finset.univ.filter fun d : WordShortKey L N w =>
                                                          wordDetourLower d = some r)).trans (show _ ≤ 3 from by simpa [Nat.add_comm] using Nat.succ_le_succ hf))
                                                  · simp_all [wordDetourSourceReactions])) using 1
      congr 1
      ext d
      simp)
  simp [wordContourDetours] at hc
  calc
    _ ≤ μ {ω | ∀ d ∈ T, detourFailed field (wordDetourSourceReactions hL d) ω} := by
      apply measure_mono
      intro ω h d hdT
      exact h d (hT hdT)
    _ ≤ z0^T.card := by
      have hformula : μ {ω | ∀ d ∈ T, detourFailed field (wordDetourSourceReactions hL d) ω} =
          ∏ d ∈ T, (1-b^(wordDetourSourceReactions hL d).card) := by
        let support := wordDetourSourceReactions (N := N) hL
        let C := MeasurableEquiv.piCurry (fun (i : T) (_ : support i.val) => Prop)
        let proj := fun (ω : Reaction N → Prop) (x : Σ i : T, support i.val) => field x.2.val ω
        have hinj : Function.Injective (fun x : Σ i : T, support i.val => x.2.val) :=
          Subtype.val_injective.comp (Set.sigmaToiUnion_injective
            (fun i : T => (support i.val : Set (Reaction N))) (by
              intro i j hij
              exact Finset.disjoint_coe.mpr (hd _ i.property _ j.property
                (Subtype.val_injective.ne hij))))
        have hlaw : μ.map (C ∘ proj) =
            Measure.pi (fun i : T => Measure.pi (fun _ : support i.val => ambientCoordLaw a)) := by
          dsimp only [μ, staticReactionMeasure]
          rw [← Measure.infinitePi_eq_pi, ← Measure.map_map C.measurable (measurable_of_finite _),
            Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : Reaction N => ambientCoordLaw a) hinj]
          simpa only [Measure.infinitePi_eq_pi] using
            (Measure.infinitePi_map_piCurry (fun (i : T) (_ : support i.val) => ambientCoordLaw a))
        have hfail (i : T) :
            (Measure.pi fun _ : support i.val => ambientCoordLaw a) {v | ¬ ∀ r, v r} =
              1-b^(support i.val).card := by
          change (Measure.pi fun _ : support i.val => ambientCoordLaw a) {v | ∀ r, v r}ᶜ = _
          rw [measure_compl (by measurability) (measure_ne_top _ _), measure_univ]
          congr 1
          simpa [Set.pi, ambientCoordLaw, b] using
            (Measure.pi_pi (μ := fun _ : support i.val => ambientCoordLaw a) (fun _ => {True}))
        have he : {ω | ∀ d ∈ T, detourFailed field (support d) ω} =
            (C ∘ proj) ⁻¹' Set.univ.pi (fun i : T => {v | ¬ ∀ r : support i.val, v r}) := by
          ext ω
          simp [C, proj, Set.pi, detourFailed, Sigma.curry]
        rw [he, ← Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet,
          hlaw, Measure.pi_pi]
        simp only [hfail]
        exact Finset.prod_coe_sort T (fun d => 1-b^(support d).card)
      rw [hformula]
      calc
        _ ≤ ∏ _i ∈ T, z0 := Finset.prod_le_prod fun i _ =>
          tsub_le_tsub_left (pow_le_pow_of_le_one zero_le hb
            (wordDetourSourceReactions_card hL i)) _
        _ = _ := by simp
    _ ≤ z0^(k*C.card) := pow_le_pow_of_le_one zero_le
      tsub_le_self (by

                                   nlinarith)
    _ = _ := pow_mul _ _ _

end HordijkSteelThreshold
