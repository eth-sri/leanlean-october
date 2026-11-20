module

public import NearlyMinimax.HistoryConnectedCount


@[expose] public section

/-!
# Uniform positivity of the actual finite history density

The connected-subset count is applied to the actual upper polymers, and their
actual signed order weights are bounded by the uniform mark bound. A finite
geometric sum then gives the source activity estimate and positivity threshold.
No activity, partition positivity, or deletion equation is assumed.
-/

noncomputable section
namespace NearlyMinimax

/-- Small-activity radius for the deletion expansion at maximum degree `Δ`. -/
abbrev historyActivityRadius (Δ : ℕ) : ℝ := 1 / (2 + 8 * Δ^2)

theorem history_finite_geom_sum_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    (∑ j ∈ Finset.range N, r ^ j) ≤ 1 / (1 - r) := by
  apply (le_div_iff₀ (sub_pos.2 hr1)).2
  rw [geom_sum_mul_neg]
  exact sub_le_self _ (pow_nonneg hr N)

theorem history_degree_activity_threshold {D ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ε ≤ 1 / (2 + 2 * D ^ 2)) :
    0 ≤ 2 * D ^ 2 * ε ∧ 2 * D ^ 2 * ε < 1 ∧ ε / (1 - 2 * D ^ 2 * ε) ≤ 1 / 2 := by
  have hs := (le_div_iff₀ (by positivity)).1 hsmall
  have hp : 0 < 1 - 2 * D ^ 2 * ε := by
    nlinarith
  refine ⟨by positivity, by linarith, (div_le_iff₀ hp).2 ?_⟩
  nlinarith

variable {α : Type*} [PartialOrder α] [DecidableEq α] [Fintype α]

section
variable {weight : α → ℝ} {ρ t B : ℝ} (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B) (hw : ∀ x, |weight x| ≤ B)
    {D : ℕ} (hD : ∀ x : α, (historyCoverGraph α).degree x ≤ D)
    (hsmall : t * B / ρ ≤ 1 / (2 + 2 * (D : ℝ) ^ 2))
include hD

theorem historyUpperRows_card_by_size (R : Finset α) (x : α) (j : ℕ) :
    ((historyGasRows (historyUpperPolymers Finset.univ) historyMaximalPieces R x).filter
      (fun P => P.card - 1 = j)).card ≤ D ^ (2 * j) := by
  classical
  calc
    _ ≤ (graphConnectedSubsets (historyCoverGraph α) x (j + 1)).card := by
      apply Finset.card_le_card
      intro P hP
      obtain ⟨hProw, hsize⟩ := Finset.mem_filter.1 hP
      obtain ⟨hPpoly, hxmax, _⟩ := Finset.mem_filter.1 hProw
      grind [historyMaximalPieces_subset, mem_graphConnectedSubsets, historyUpperPolymer_coverGraph_connected]
    _ ≤ _ := by
      solve_by_elim [graph_connected_subsets_card_le]

include hρ ht hB hw hsmall in
theorem historyUpperRows_activity_le (R : Finset α) (x : α) :
    (∑ P ∈ historyGasRows (historyUpperPolymers Finset.univ) historyMaximalPieces R x,
      |historyComponentWeight weight ρ t P| * 2 ^ ((historyMaximalPieces P).card - 1)) ≤ 1 / 2 := by
  classical
  let A := historyGasRows (historyUpperPolymers Finset.univ) historyMaximalPieces R x
  let ε := t * B / ρ
  have hε  := div_nonneg (mul_nonneg ht hB) hρ.le
  have hthreshold := history_degree_activity_threshold hε hsmall
  have hmap : ∀ P ∈ A, P.card - 1 ∈ Finset.range (Fintype.card α) := by
    intro P hP
    grind [Finset.card_pos.2 ⟨x, (historyMaximalPieces_subset P (Finset.mem_filter.1 hP).2.1)⟩, Finset.card_le_univ P]
  have hterm : ∀ P ∈ A,
      |historyComponentWeight weight ρ t P| * 2 ^ ((historyMaximalPieces P).card - 1) ≤
        ε ^ P.card * 2 ^ (P.card - 1) := by
    intro P hP
    have hc := historyComponentWeight_abs_le P hρ ht hB (fun y _ => hw y)
    exact mul_le_mul hc (pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_right (Finset.card_le_card (historyMaximalPieces_subset P)) 1))
      (by positivity) (pow_nonneg hε _)
  have hfiber : ∀ j,
      (∑ P ∈ A.filter (fun P => P.card - 1 = j),
        |historyComponentWeight weight ρ t P| * 2 ^ ((historyMaximalPieces P).card - 1)) ≤
          D ^ (2 * j) * (ε ^ (j + 1) * 2 ^ j) := by
    intro j
    calc
      _ ≤ ∑ _P ∈ A.filter (fun P => P.card - 1 = j), ε ^ (j + 1) * 2 ^ j := by
        apply Finset.sum_le_sum
        intro P hP
        obtain ⟨hPA, hsize⟩ := Finset.mem_filter.1 hP
        have hxP := historyMaximalPieces_subset P (Finset.mem_filter.1 hPA).2.1
        grind
      _ = (A.filter (fun P => P.card - 1 = j)).card * (ε ^ (j + 1) * 2 ^ j) := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast historyUpperRows_card_by_size hD R x j
  calc
    _ = _ :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ _ := Finset.sum_le_sum (fun j _ => hfiber j)
    _ = ε * ∑ j ∈ Finset.range (Fintype.card α), (2 * D ^ 2 * ε) ^ j := by
      rw [Finset.mul_sum]
      ring
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (history_finite_geom_sum_le hthreshold.1 hthreshold.2.1 _) hε
    _ = _ := by ring
    _ ≤ _ := hthreshold.2.2

include hρ ht hB hw hsmall in
/-- Actual finite history-density positivity, with activity derived from the cover graph. -/
theorem historyUpperDensity_positive_of_degree_bound :
    ∀ R, 0 < historyRestrictedUpperDensity weight ρ t Finset.univ R ∧ ∀ x ∈ R,
      historyRestrictedUpperDensity weight ρ t Finset.univ (R.erase x) / 2 ≤
        historyRestrictedUpperDensity weight ρ t Finset.univ R ∧
      historyRestrictedUpperDensity weight ρ t Finset.univ R ≤
        3 / 2 * historyRestrictedUpperDensity weight ρ t Finset.univ (R.erase x) := by
  apply historyRestrictedUpperDensity_positive
  intro R x hx
  apply historyUpperRows_activity_le <;> assumption

end

omit [Fintype α] in
@[simp] theorem historyRestrictedUpperDensity_empty (weight : α → ℝ) (ρ t : ℝ) (S : Finset α) :
    historyRestrictedUpperDensity weight ρ t S ∅ = 1 := by
  rw [historyRestrictedUpperDensity_eq_gas]
  exact historyGasPartition_empty (historyUpperPolymers S) historyMaximalPieces
    (historyComponentWeight weight ρ t) (fun _ hP => historyUpperPolymer_support_nonempty hP)

/-- The actual finite history density has the source's uniform maximal-piece bounds. -/
theorem historyUpperDensity_bounds_of_degree_bound {weight : α → ℝ} {ρ t B : ℝ}
    (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B) (hw : ∀ x, |weight x| ≤ B)
    {D : ℕ} (hD : ∀ x, (historyCoverGraph α).degree x ≤ D)
    (hsmall : t * B / ρ ≤ 1 / (2 + 2 * D ^ 2)) :
    (1 / 2) ^ (historyMaximalPieces (Finset.univ : Finset α)).card ≤
        historyScaledUpperDensity weight ρ Finset.univ t ∧
      historyScaledUpperDensity weight ρ Finset.univ t ≤
        (3 / 2) ^ (historyMaximalPieces (Finset.univ : Finset α)).card := by
  have hb := deletion_ratios_global_bounds
    (historyRestrictedUpperDensity_empty weight ρ t Finset.univ) (fun R x hx => ((historyUpperDensity_positive_of_degree_bound hρ ht hB hw hD hsmall) R).2 x hx)
    (historyMaximalPieces Finset.univ)
  have heq : historyRestrictedUpperDensity weight ρ t Finset.univ (historyMaximalPieces Finset.univ) =
      historyScaledUpperDensity weight ρ Finset.univ t := by
    unfold historyRestrictedUpperDensity
    rw [historyRestrictedUpperSets_full, historyScaledUpperDensity_eq_components]
  rwa [heq] at hb

end NearlyMinimax

namespace NearlyMinimax

/-- The source threshold `1/(2+8 Delta^2)` applies to the actual dependent-word heap. -/
theorem wordHeap_density_bounds {J : Type*} [Fintype J] [DecidableEq J]
    {word : List J} {dependent : J → J → Prop}
    [Std.Refl dependent] [Std.Symm dependent]
    {Δ : ℕ} (hlabels : DegreeAtMost dependent Δ)
    (weight : WordHeapPiece word dependent → ℝ) {ρ t B : ℝ}
    (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B) (hw : ∀ x, |weight x| ≤ B)
    (hsmall : t * B / ρ ≤ historyActivityRadius Δ) :
    (1 / 2) ^ Fintype.card J ≤ historyScaledUpperDensity weight ρ Finset.univ t ∧
      historyScaledUpperDensity weight ρ Finset.univ t ≤ (3 / 2) ^ Fintype.card J := by
  have hD : ∀ x, (historyCoverGraph (WordHeapPiece word dependent)).degree x ≤ 2 * Δ := fun x => (wordHeapCoverGraph_degree_le x).trans (Nat.mul_le_mul_left 2 (hlabels _))
  have hb := historyUpperDensity_bounds_of_degree_bound hρ ht hB hw hD (by
    convert hsmall using 1
    push_cast
    ring)
  have hc := wordHeap_maximal_card_le_labels (Finset.univ : Finset (WordHeapPiece word dependent))
  refine ⟨?_, ?_⟩
  · exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hc).trans hb.1
  · exact hb.2.trans (pow_le_pow_right₀ (by norm_num) hc)

end NearlyMinimax
