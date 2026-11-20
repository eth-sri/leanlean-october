module

public import NearlyMinimax.HistoryPositivity

@[expose] public section

/-!
# A concrete finite signed history-component gas

The connected upper components in `lower_heaps` carry nonempty supports of
maximal history pieces. Compatible families have pairwise disjoint supports.
This module defines the genuine finite sum over such families and proves its
deletion recurrence, so the positivity theorem can be applied without assuming
the recurrence of the partition function.

The identification of these polymers with all connected upper sets of a marked
history, and the multiplicativity of their order-volume coefficients, are
separate from this finite combinatorial module.
-/

noncomputable section
namespace NearlyMinimax

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

section
variable (P : Finset β) (support : β → Finset α) (weight : β → ℝ) (S : Finset α)

def CompatibleHistoryFamily (F : Finset β) : Prop :=
  ∀ p ∈ F, ∀ q ∈ F, p ≠ q → Disjoint (support p) (support q)

def historyGasFamilies : Finset (Finset β) := by
  classical
  exact P.powerset.filter (fun F => CompatibleHistoryFamily support F ∧ ∀ p ∈ F, support p ⊆ S)

def historyGasPartition : ℝ :=
  ∑ F ∈ historyGasFamilies P support S, ∏ p ∈ F, weight p

def historyGasRows (x : α) : Finset β :=
  P.filter (fun p => x ∈ support p ∧ support p ⊆ S)

end

omit [DecidableEq β] in
theorem mem_historyGasFamilies {P : Finset β} {support : β → Finset α} {S : Finset α} {F : Finset β} :
    F ∈ historyGasFamilies P support S ↔
      F ⊆ P ∧ CompatibleHistoryFamily support F ∧ ∀ p ∈ F, support p ⊆ S := by
  classical
  simp [historyGasFamilies]

omit [DecidableEq β] in
theorem historyGasPartition_empty (P : Finset β) (support : β → Finset α) (weight : β → ℝ)
    (hne : ∀ p ∈ P, (support p).Nonempty) : historyGasPartition P support weight ∅ = 1 := by
  classical
  unfold historyGasPartition
  have hfamilies : historyGasFamilies P support ∅ = {∅} := by
    ext F
    rw [Finset.mem_singleton, mem_historyGasFamilies]
    constructor
    · grind
    · intro hF
      subst F
      simp [CompatibleHistoryFamily]
  rw [hfamilies]
  simp

section
variable {P : Finset β} {support : β → Finset α} {S : Finset α} {F : Finset β} {p : β}

theorem historyGasFamily_unique_at (hF : F ∈ historyGasFamilies P support S) {p q : β} {x : α}
    (hp : p ∈ F) (hq : q ∈ F) (hxp : x ∈ support p) (hxq : x ∈ support q) : p = q := by
  exact Decidable.byContradiction fun hpq => Finset.disjoint_left.mp ((mem_historyGasFamilies.mp hF).right.left p hp q hq hpq) hxp hxq

theorem historyGasFamily_erase_component (hF : F ∈ historyGasFamilies P support S) (hp : p ∈ F) :
    F.erase p ∈ historyGasFamilies P support (S \ support p) := by
  obtain ⟨hFP, hcompat, hsupport⟩ := mem_historyGasFamilies.1 hF
  rw [mem_historyGasFamilies]
  refine ⟨(Finset.erase_subset _ _).trans hFP, ?_, ?_⟩
  · exact fun q hq r hr => hcompat q (Finset.mem_of_mem_erase hq) r (Finset.mem_of_mem_erase hr)
  · exact fun q hq ⦃x⦄ hx => And.casesOn (Finset.mem_erase.mp hq) fun hqp hqF => Finset.mem_sdiff.mpr ⟨hsupport q hqF hx, fun hxp => Finset.disjoint_left.mp (hcompat q hqF p hp hqp) hx hxp⟩

theorem historyGasFamily_insert_component (hF : F ∈ historyGasFamilies P support (S \ support p))
    (hp : p ∈ P) (hps : support p ⊆ S) : insert p F ∈ historyGasFamilies P support S := by
  obtain ⟨hFP, hcompat, hsupport⟩ := mem_historyGasFamilies.1 hF
  rw [mem_historyGasFamilies]
  refine ⟨Finset.insert_subset hp hFP, ?_, ?_⟩
  · intro q hq r hr hqr
    by_cases hqp : q = p
    · subst q
      apply Finset.disjoint_left.2
      grind
    · by_cases hrp : r = p
      · subst r
        apply Finset.disjoint_left.2
        grind
      · aesop
  · grind

end

omit [DecidableEq β] in
theorem historyGasComponent_not_mem {P : Finset β} {support : β → Finset α} {S : Finset α}
    {F : Finset β} {p : β} {x : α} (hF : F ∈ historyGasFamilies P support (S \ support p))
    (hxp : x ∈ support p) : p ∉ F := by
  exact fun hp => (Finset.mem_sdiff.mp ((mem_historyGasFamilies.mp hF).right.right p hp hxp)).right hxp

omit [DecidableEq β] in
theorem historyGasFamilies_erase (P : Finset β) (support : β → Finset α) (S : Finset α) (x : α) :
    historyGasFamilies P support (S.erase x) =
      (historyGasFamilies P support S).filter (fun F => ¬ ∃ p ∈ F, x ∈ support p) := by
  classical
  ext F
  rw [mem_historyGasFamilies, Finset.mem_filter, mem_historyGasFamilies]
  grind

section
variable (P : Finset β) (support : β → Finset α) (weight : β → ℝ) (S : Finset α) (x : α)

def historyGasActiveFamilies :
    Finset (Finset β) := by
  classical
  exact (historyGasFamilies P support S).filter (fun F => ∃ p ∈ F, x ∈ support p)

theorem historyGas_active_sum :
    (∑ F ∈ historyGasActiveFamilies P support S x, ∏ p ∈ F, weight p) =
      ∑ p ∈ historyGasRows P support S x, weight p * historyGasPartition P support weight (S \ support p) := by
  classical
  have hsum : (∑ i ∈ (historyGasRows P support S x).sigma (fun p => historyGasFamilies P support (S \ support p)), weight i.1 * ∏ p ∈ i.2, weight p) =
      ∑ F ∈ historyGasActiveFamilies P support S x, ∏ p ∈ F, weight p := by
    apply Finset.sum_bij (fun i _ => insert i.1 i.2)
    · intro i hi
      obtain ⟨hip, hiF⟩ := Finset.mem_sigma.1 hi
      obtain ⟨hiP, hix, hiS⟩ := Finset.mem_filter.1 hip
      apply Finset.mem_filter.2
      grind [historyGasFamily_insert_component]
    · intro i hi j hj heq
      obtain ⟨hip, hiF⟩ := Finset.mem_sigma.1 hi
      obtain ⟨hjp, hjF⟩ := Finset.mem_sigma.1 hj
      obtain ⟨hiP, hix, hiS⟩ := Finset.mem_filter.1 hip
      obtain ⟨hjP, hjx, hjS⟩ := Finset.mem_filter.1 hjp
      have hpq := historyGasFamily_unique_at (historyGasFamily_insert_component hiF hiP hiS) (Finset.mem_insert_self _ _) (by rw [heq]; exact Finset.mem_insert_self _ _) hix hjx
      cases i with | mk p F =>
        cases j with | mk q G =>
          dsimp at hpq heq hix hiF hjF
          subst q
          have hnF := historyGasComponent_not_mem hiF hix
          have hFG := congrArg (fun T => T.erase p) heq
          simp [Finset.erase_insert hnF, Finset.erase_insert (historyGasComponent_not_mem hjF hix)] at hFG
          subst G
          rfl
    · intro F hF
      obtain ⟨hfamily, p, hp, hxp⟩ := Finset.mem_filter.1 hF
      obtain ⟨hFP, _, hs⟩ := mem_historyGasFamilies.1 hfamily
      refine ⟨⟨p, F.erase p⟩, Finset.mem_sigma.2 ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_filter.2 ⟨hFP hp, hxp, hs p hp⟩
      · exact historyGasFamily_erase_component hfamily hp
      · exact Finset.insert_erase hp
    · intro i hi
      obtain ⟨hip, hiF⟩ := Finset.mem_sigma.1 hi
      obtain ⟨_, hix, _⟩ := Finset.mem_filter.1 hip
      rw [Finset.prod_insert (historyGasComponent_not_mem hiF hix)]
  rw [← hsum, Finset.sum_sigma]
  unfold historyGasPartition
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]

/-- The actual signed finite partition sum satisfies the paper's deletion recurrence. -/
theorem historyGasPartition_deletion :
    historyGasPartition P support weight S = historyGasPartition P support weight (S.erase x) +
      ∑ p ∈ historyGasRows P support S x, weight p * historyGasPartition P support weight (S \ support p) := by
  classical
  rw [← historyGas_active_sum, historyGasPartition, historyGasPartition, historyGasFamilies_erase, add_comm]
  exact (Finset.sum_filter_add_sum_filter_not ..).symm

end

/-- Positivity is a theorem about the concrete finite sum, not a recurrence hypothesis. -/
theorem historyGasPartition_positive {P : Finset β} {support : β → Finset α} {weight : β → ℝ}
    (hne : ∀ p ∈ P, (support p).Nonempty)
    (hactivity : ∀ S x, x ∈ S →
      (∑ p ∈ historyGasRows P support S x, |weight p| * 2 ^ ((support p).card - 1)) ≤ 1 / 2) :
    ∀ S, 0 < historyGasPartition P support weight S ∧ ∀ x ∈ S,
      historyGasPartition P support weight (S.erase x) / 2 ≤ historyGasPartition P support weight S ∧
      historyGasPartition P support weight S ≤ 3 / 2 * historyGasPartition P support weight (S.erase x) := by
  apply positive_deletion_recurrence
    (historyGasRows P support) support weight (historyGasPartition_empty P support weight hne)
  · exact fun S x hx p hp => (Finset.mem_filter.mp hp).right
  · solve_by_elim [historyGasPartition_deletion]
  · exact hactivity

end NearlyMinimax
