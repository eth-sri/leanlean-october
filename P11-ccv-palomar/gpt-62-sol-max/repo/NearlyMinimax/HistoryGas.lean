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

def CompatibleHistoryFamily (support : β → Finset α) (F : Finset β) : Prop :=
  ∀ p ∈ F, ∀ q ∈ F, p ≠ q → Disjoint (support p) (support q)

def historyGasFamilies (P : Finset β) (support : β → Finset α) (S : Finset α) : Finset (Finset β) := by
  classical
  exact P.powerset.filter (fun F => CompatibleHistoryFamily support F ∧ ∀ p ∈ F, support p ⊆ S)

def historyGasPartition (P : Finset β) (support : β → Finset α) (weight : β → ℝ) (S : Finset α) : ℝ :=
  ∑ F ∈ historyGasFamilies P support S, ∏ p ∈ F, weight p

def historyGasRows (P : Finset β) (support : β → Finset α) (S : Finset α) (x : α) : Finset β :=
  P.filter (fun p => x ∈ support p ∧ support p ⊆ S)

omit [DecidableEq β] in
theorem mem_historyGasFamilies {P : Finset β} {support : β → Finset α} {S : Finset α} {F : Finset β} :
    F ∈ historyGasFamilies P support S ↔
      F ⊆ P ∧ CompatibleHistoryFamily support F ∧ ∀ p ∈ F, support p ⊆ S := by
  classical
  simp only [historyGasFamilies, Finset.mem_filter, Finset.mem_powerset]

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
variable {P : Finset β} {support : β → Finset α} {S : Finset α}
    {F : Finset β}

theorem historyGasFamily_unique_at (hF : F ∈ historyGasFamilies P support S) {p q : β} {x : α}
    (hp : p ∈ F) (hq : q ∈ F) (hxp : x ∈ support p) (hxq : x ∈ support q) : p = q := by
  by_contra hpq
  exact Finset.disjoint_left.1 ((mem_historyGasFamilies.1 hF).2.1 p hp q hq hpq) hxp hxq

section
variable {p : β}

theorem historyGasFamily_erase_component (hF : F ∈ historyGasFamilies P support S) (hp : p ∈ F) :
    F.erase p ∈ historyGasFamilies P support (S \ support p) := by
  obtain ⟨hFP, hcompat, hsupport⟩ := mem_historyGasFamilies.1 hF
  rw [mem_historyGasFamilies]
  refine ⟨(Finset.erase_subset _ _).trans hFP, ?_, ?_⟩
  · intro q hq r hr hqr
    exact hcompat q (Finset.mem_of_mem_erase hq) r (Finset.mem_of_mem_erase hr) hqr
  · intro q hq x hx
    obtain ⟨hqp, hqF⟩ := Finset.mem_erase.1 hq
    exact Finset.mem_sdiff.2 ⟨hsupport q hqF hx,
      fun hxp => Finset.disjoint_left.1 (hcompat q hqF p hp hqp) hx hxp⟩

theorem historyGasFamily_insert_component (hF : F ∈ historyGasFamilies P support (S \ support p))
    (hp : p ∈ P) (hps : support p ⊆ S) : insert p F ∈ historyGasFamilies P support S := by
  obtain ⟨hFP, hcompat, hsupport⟩ := mem_historyGasFamilies.1 hF
  rw [mem_historyGasFamilies]
  refine ⟨Finset.insert_subset hp hFP, ?_, ?_⟩
  · intro q hq r hr hqr
    by_cases hqp : q = p
    · subst q
      have hrF := Finset.mem_of_mem_insert_of_ne hr (Ne.symm hqr)
      apply Finset.disjoint_left.2
      grind
    · have hqF := Finset.mem_of_mem_insert_of_ne hq hqp
      by_cases hrp : r = p
      · subst r
        apply Finset.disjoint_left.2
        grind
      · exact hcompat q hqF r (Finset.mem_of_mem_insert_of_ne hr hrp) hqr
  grind

end

end

omit [DecidableEq β] in
theorem historyGasComponent_not_mem {P : Finset β} {support : β → Finset α} {S : Finset α}
    {F : Finset β} {p : β} {x : α} (hF : F ∈ historyGasFamilies P support (S \ support p))
    (hxp : x ∈ support p) : p ∉ F := by
  grind [mem_historyGasFamilies]

omit [DecidableEq β] in
theorem historyGasFamilies_erase (P : Finset β) (support : β → Finset α) (S : Finset α) (x : α) :
    historyGasFamilies P support (S.erase x) =
      (historyGasFamilies P support S).filter (fun F => ¬ ∃ p ∈ F, x ∈ support p) := by
  classical
  ext F
  rw [mem_historyGasFamilies, Finset.mem_filter, mem_historyGasFamilies]
  constructor
  · grind
  · grind

def historyGasActiveFamilies (P : Finset β) (support : β → Finset α) (S : Finset α) (x : α) :
    Finset (Finset β) := by
  classical
  exact (historyGasFamilies P support S).filter (fun F => ∃ p ∈ F, x ∈ support p)

section
variable (P : Finset β) (support : β → Finset α) (weight : β → ℝ)

section
variable (S : Finset α) (x : α)

theorem historyGas_active_sum :
    (∑ F ∈ historyGasActiveFamilies P support S x, ∏ p ∈ F, weight p) =
      ∑ p ∈ historyGasRows P support S x, weight p * historyGasPartition P support weight (S \ support p) := by
  classical
  let rows := historyGasRows P support S x
  let families := fun p => historyGasFamilies P support (S \ support p)
  have hsum : (∑ i ∈ rows.sigma families, weight i.1 * ∏ p ∈ i.2, weight p) =
      ∑ F ∈ historyGasActiveFamilies P support S x, ∏ p ∈ F, weight p := by
    apply Finset.sum_bij (fun i _ => insert i.1 i.2)
    · intro i hi
      obtain ⟨hip, hiF⟩ := Finset.mem_sigma.1 hi
      obtain ⟨hiP, hix, hiS⟩ := Finset.mem_filter.1 hip
      apply Finset.mem_filter.2
      refine ⟨historyGasFamily_insert_component hiF hiP hiS, i.1, ?_, hix⟩
      simp
    · intro i hi j hj heq
      obtain ⟨hip, hiF⟩ := Finset.mem_sigma.1 hi
      obtain ⟨hjp, hjF⟩ := Finset.mem_sigma.1 hj
      obtain ⟨hiP, hix, hiS⟩ := Finset.mem_filter.1 hip
      obtain ⟨hjP, hjx, hjS⟩ := Finset.mem_filter.1 hjp
      have hfamily := historyGasFamily_insert_component hiF hiP hiS
      have hji : j.1 ∈ insert i.1 i.2 := by simp_all
      have hpq := historyGasFamily_unique_at hfamily (Finset.mem_insert_self _ _) hji hix hjx
      cases i with | mk p F =>
        cases j with | mk q G =>
          dsimp at hpq heq hix hiF hjF
          subst q
          have hnF := historyGasComponent_not_mem hiF hix
          have hnG := historyGasComponent_not_mem hjF hix
          have hFG := congrArg (fun T : Finset β => T.erase p) heq
          simp only [Finset.erase_insert hnF, Finset.erase_insert hnG] at hFG
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
  rw [← historyGas_active_sum, historyGasPartition, historyGasPartition, historyGasFamilies_erase]
  unfold historyGasActiveFamilies
  rw [add_comm]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

end

/-- Positivity is a theorem about the concrete finite sum, not a recurrence hypothesis. -/
theorem historyGasPartition_positive
    (hne : ∀ p ∈ P, (support p).Nonempty)
    (hactivity : ∀ S x, x ∈ S →
      (∑ p ∈ historyGasRows P support S x, |weight p| * (2 : ℝ) ^ ((support p).card - 1)) ≤ 1 / 2) :
    ∀ S, 0 < historyGasPartition P support weight S ∧ ∀ x ∈ S,
      historyGasPartition P support weight (S.erase x) / 2 ≤ historyGasPartition P support weight S ∧
      historyGasPartition P support weight S ≤ 3 / 2 * historyGasPartition P support weight (S.erase x) := by
  apply positive_deletion_recurrence (historyGasPartition P support weight)
    (historyGasRows P support) support weight (historyGasPartition_empty P support weight hne)
  · intro S x hx p hp
    exact (Finset.mem_filter.1 hp).2
  · solve_by_elim [historyGasPartition_deletion]
  assumption

end

end NearlyMinimax
