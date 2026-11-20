module

public import ADR11.Computation.Shapes
meta import ADR11.Computation.Small
public import ADR11.Identifiability.Factors

@[expose] public section

namespace ADR11
open Finset Real _root_.ADR11.Computation

def quartetCode (a : Fin 3) : ℕ := if a = 0 then 3 else if a = 1 then 5 else 9

/-- The three binary unrooted gene trees on four leaves. -/
def quartet (a : Fin 3) : For 4 := unroot (codedHierarchy 4 [quartetCode a])

def quartetTrees := univ.image quartet

noncomputable def quartetScale (τ : TreeOn 4) (a : Fin 3) : ℝ :=
  edgeFactor τ (decC 4 (quartetCode a)) * edgeFactor τ (decC 4 (15 - quartetCode a))

noncomputable def scaleAvg (v : Fin 3 → ℝ) : ℝ := (v 0 + v 1 + v 2) / 3

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
set_option linter.unusedSimpArgs false in
theorem quartet_values (τ : TreeOn 4)
    (a : Fin 3) :
    τ.unrootedDist id (quartet a) = 1 / 3 - quartetScale τ a + scaleAvg (quartetScale τ) := by
  obtain ⟨cs, hm, hτ⟩ := exists_code τ (by decide)
  change cs ∈ quartetRootings at hm
  rw [dist_small_poly τ hτ]
  rw [rootings_literal.1] at hm
  verify_readings hm a [quartetScale, quartetCode, scaleAvg, edgeFactor, hτ]

private theorem quartet_values_zero (τ : TreeOn 4) {T : For 4}
    (hT : T ∉ quartetTrees) : τ.unrootedDist id T = 0 := by
  have hle := sum_le_sum_of_subset_of_nonneg (subset_univ (insert T quartetTrees))
    (fun U _ _ => τ.unrootedDist_nonneg id U)
  rw [sum_insert hT, quartetTrees, sum_image (by decide), Fin.sum_univ_three, τ.unrootedDist_sum] at hle
  simp only [quartet_values, scaleAvg] at hle
  linarith [τ.unrootedDist_nonneg id T]

private theorem quartet_scale_length (τ : TreeOn 4) (a : Fin 3) :
    quartetScale τ a = exp (-τ.unrootedLength (decC 4 (quartetCode a))) := by
  fin_cases a <;> rw [unrooted_factor τ (by decide) (by decide) (by decide)] <;> rfl

private theorem quartet_scale_absent (τ : TreeOn 4) (a : Fin 3)
    (h : decC 4 (quartetCode a) ∉ unroot τ.clusters) : quartetScale τ a = 1 := by
  simp [quartet_scale_length, (τ.unrootedLength_eq_zero_iff _).2 h]

section
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 1000 in
private theorem quartet_certificate : ∀ U ∈ smallTopologies 4, ∀ V ∈ smallTopologies 4,
    (∃ a : Fin 3, decC 4 (quartetCode a) ∉ U ∧ decC 4 (quartetCode a) ∉ V) ∧
    ((∀ a : Fin 3, decC 4 (quartetCode a) ∈ U ↔ decC 4 (quartetCode a) ∈ V) → U = V) := by decide +kernel
end

private theorem quartet_scales_dist (τ τ' : TreeOn 4) :
    τ.unrootedDist id = τ'.unrootedDist id ↔ ∀ a : Fin 3, quartetScale τ a = quartetScale τ' a := by
  constructor
  · intro h
    obtain ⟨a, hA, hA'⟩ := (quartet_certificate _ (topology_mem τ (by decide)) _ (topology_mem τ' (by decide))).1
    have e j := congrFun h (quartet j)
    simp_rw [quartet_values] at e
    have w := e a
    rw [quartet_scale_absent τ a hA, quartet_scale_absent τ' a hA'] at w
    intro j
    linarith [e j]
  · intro h
    have he := funext h
    funext T
    by_cases hT : T ∈ quartetTrees
    · obtain ⟨a, -, rfl⟩ := mem_image.1 hT
      simp [quartet_values, he]
    · rw [quartet_values_zero τ hT, quartet_values_zero τ' hT]

private theorem quartet_scales_metric (τ τ' : TreeOn 4) :
    (∀ a : Fin 3, quartetScale τ a = quartetScale τ' a) ↔ τ.SameUnrootedMetricTree τ' := by
  constructor
  · intro h
    have lengths (A : Cl 4) (hc : #A = 2) : τ.unrootedLength A = τ'.unrootedLength A := by
      obtain ⟨a, rfl | rfl⟩ := (by decide : ∀ A : Cl 4, #A = 2 →
        ∃ a : Fin 3, A = decC 4 (quartetCode a) ∨ A = (decC 4 (quartetCode a))ᶜ) A hc <;>
        simpa only [SpeciesTree.unrootedLength_compl, quartet_scale_length _ a, exp_eq_exp, neg_inj] using h a
    have e := (quartet_certificate _ (topology_mem τ (by decide)) _ (topology_mem τ' (by decide))).2 fun a => by
      have hc : #(decC 4 (quartetCode a)) = 2 := by fin_cases a <;> decide
      exact not_iff_not.mp (by rw [← τ.unrootedLength_eq_zero_iff, ← τ'.unrootedLength_eq_zero_iff, lengths _ hc])
    refine ⟨e, fun A _ hA hA' => ?_⟩
    apply lengths
    have := card_compl A
    simp only [Fintype.card_fin] at this
    omega
  · intro h a
    rw [quartet_scale_length τ a, quartet_scale_length τ' a, h.length_eq]
    all_goals fin_cases a <;> decide

/-- Four-taxon gene tree distributions identify exactly the unrooted metric species tree. -/
theorem quartet_identifiability {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := by
  let e := Fintype.equivFinOfCardEq hX
  rw [← σ.unrootedDist_relabel_eq_iff σ' e, ← σ.sameUnrootedMetricTree_relabel_iff σ' e,
    quartet_scales_dist, quartet_scales_metric]

private noncomputable def unitTree (cs : List ℕ) (h : IsHierarchy (codedHierarchy 4 cs)) : TreeOn 4 :=
  ⟨_, h.1, h.2.1, h.2.2.1, h.2.2.2, fun _ => 1, by intros; norm_num⟩

set_option linter.unusedSimpArgs false in
private theorem quartet_ambiguity_fin : ∃ σ σ' : TreeOn 4, σ.IsBinary ∧ σ'.IsBinary ∧
    σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  let τ := unitTree [3, 7] (by unfold IsHierarchy IsForest; decide)
  let τ' := unitTree [3, 11] (by unfold IsHierarchy IsForest; decide)
  refine ⟨τ, τ', by unfold SpeciesTree.IsBinary; decide, by unfold SpeciesTree.IsBinary; decide,
    (quartet_scales_dist _ _).2 ?_, fun h => (by decide : codedHierarchy 4 [3, 7] ≠ codedHierarchy 4 [3, 11]) h.1⟩
  intro a
  fin_cases a <;> simp (config := {decide := true}) [quartetScale, quartetCode, edgeFactor, τ, τ', unitTree]

/-- The root is not identifiable on four taxa, even for binary trees. -/
theorem quartet_ambiguity {X : Type*} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 4) :
    ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧
      σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  obtain ⟨τ, τ', hb, hb', hd, hn⟩ := quartet_ambiguity_fin
  let e := (Fintype.equivFinOfCardEq hX).symm
  exact ⟨τ.relabel e, τ'.relabel e, τ.isBinary_relabel e hb,
    τ'.isBinary_relabel e hb', (τ.unrootedDist_relabel_eq_iff τ' e).2 hd,
    fun h => hn ((τ.sameRootedMetricTree_relabel_iff τ' e).1 h)⟩

end ADR11
