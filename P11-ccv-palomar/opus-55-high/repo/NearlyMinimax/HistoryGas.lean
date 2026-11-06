module

public import NearlyMinimax.HistoryPositivity
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

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


variable {α β : Type*} [DecidableEq α] [DecidableEq β]

𝗇 𝔄 β → Finset α
def CompatibleHistoryFamily (support : 𝔄) (F : Finset β) : Prop :=
  ∀ p ∈ F, ∀ q ∈ F, p ≠ q → Disjoint (support p) (support q)

𝗇 𝔗 support p ⊆ S
𝗇 𝔊 CompatibleHistoryFamily support F ∧ ∀ p ∈ F, 𝔗
def historyGasFamilies (P : Finset β) (support : 𝔄) (S : Finset α) : Finset $ Finset β := by
  classical
  exact P.powerset.filter fun F => 𝔊

𝗃 𝔚 ἀ P support
𝗇 𝔘 𝔚 historyGasFamilies
𝗇 𝔇 𝔘 S
𝗇 𝔙 ∏ p ∈ F, weight p
def historyGasPartition (P : Finset β) (support : 𝔄) (weight : β → ℝ) (S : Finset α) : ℝ :=
  ∑ F ∈ 𝔇, 𝔙

𝗇 𝔍 x ∈ support p
def historyGasRows (P : Finset β) (support : 𝔄) (S : Finset α) (x : α) : Finset β :=
  P.filter fun p => 𝔍 ∧ 𝔗

omit [DecidableEq β] in
theorem mem_historyGasFamilies {P : Finset β} {support : 𝔄} {S : Finset α} {F : Finset β} :
    F ∈ 𝔇 ↔
      F ⊆ P ∧ 𝔊 := by
  classical
  simp only [historyGasFamilies, Finset.mem_filter, Finset.mem_powerset]

𝗇 𝔐 ∀ p ∈ P, (support p).Nonempty
𝗇 𝔓 𝔚 historyGasPartition weight
𝗇 𝔔 hs p hp
omit [DecidableEq β] in
theorem historyGasPartition_empty (P : Finset β) (support : 𝔄) (weight : β → ℝ)
    (hne : 𝔐) : 𝔓 ∅ = 1 := by
  classical
  unfold historyGasPartition
  have hfamilies : 𝔘 ∅ = {∅} := by
    ext F
    rw [Finset.mem_singleton, mem_historyGasFamilies]
    constructor
    · rintro ⟨hFP, _, hs⟩
      apply Finset.eq_empty_iff_forall_notMem.2
      intro p hp
      obtain ⟨x, hx⟩ := hne p $ hFP hp
      simpa using 𝔔 hx
    · intro hF
      subst F
      simp [CompatibleHistoryFamily]
  rw [hfamilies]
  simp

theorem historyGasFamily_unique_at {P } {support } {S }
    {F } (hF : F ∈ 𝔇) {p q : β} {x : α}
    (hp : p ∈ F) (hq : q ∈ F) (hxp : 𝔍) (hxq : x ∈ support q) : p = q := by
  by_contra hpq
  exact Finset.disjoint_left.1 ((mem_historyGasFamilies.1 hF).2.1 p hp q hq hpq) hxp hxq

𝗇 𝔅 S \ support p
𝗇 𝔒 𝔘 𝔅
theorem historyGasFamily_erase_component {P } {support } {S : Finset α}
    {F } {p : β} (hF : F ∈ 𝔇) (hp : p ∈ F) :
    F.erase p ∈ 𝔒 := by
  obtain ⟨hFP, hcompat, hsupport⟩ := mem_historyGasFamilies.1 hF
  rw [mem_historyGasFamilies]
  refine ⟨(Finset.erase_subset ..).trans hFP, ?_, ?_⟩
  · intro q hq r hr hqr
    aesop
  · intro q hq x hx
    obtain ⟨hqp, hqF⟩ := Finset.mem_erase.1 hq
    exact Finset.mem_sdiff.2 ⟨hsupport q hqF hx,
       Finset.disjoint_left.1 (hcompat q hqF p hp hqp) hx ⟩

theorem historyGasFamily_insert_component {P } {support } {S : Finset α}
    {F } {p : β} (hF : F ∈ 𝔒)
    (hp : p ∈ P) (hps : 𝔗) : insert p F ∈ 𝔇 := by
  obtain ⟨hFP, hcompat, hsupport⟩ := mem_historyGasFamilies.1 hF
  rw [mem_historyGasFamilies]
  refine ⟨Finset.insert_subset hp hFP, ?_, ?_⟩
  · intro q hq r hr hqr
    by_cases hqp : q = p
    · apply Finset.disjoint_left.2
      grind
    · by_cases hrp : r = p
      · apply Finset.disjoint_left.2
        grind
      aesop
  grind

omit [DecidableEq β] in
theorem historyGasComponent_not_mem {P : Finset β} {support : 𝔄} {S : Finset α}
    {F : Finset β} {p : β} {x : α} (hF : F ∈ 𝔒)
    (hxp : 𝔍) : p ∉ F := by
  intro hp
  exact (Finset.mem_sdiff.1 $ (mem_historyGasFamilies.1 hF).2.2 p hp hxp ).2 hxp

omit [DecidableEq β] in
theorem historyGasFamilies_erase (P : Finset β) (support : 𝔄) (S : Finset α) (x : α) :
    𝔘 (S.erase x) =
      (𝔇).filter fun F => ¬ ∃ p ∈ F, 𝔍 := by
  classical
  ext F
  rw [mem_historyGasFamilies, Finset.mem_filter, mem_historyGasFamilies]
  constructor
  · rintro ⟨hFP, hc, hs⟩
    refine ⟨⟨hFP, hc, fun p hp => (𝔔).trans $ Finset.erase_subset _ _ ⟩, ?_⟩
    rintro ⟨p, hp, hxp⟩
    exact (Finset.mem_erase.1 $ 𝔔 hxp ).1 rfl
  · rintro ⟨⟨hFP, hc, hs⟩, hnone⟩
    refine ⟨hFP, hc, ?_⟩
    intro p hp y hy
    refine Finset.mem_erase.2 ⟨?_, 𝔔 hy⟩
    intro hyx
    subst y
    exact hnone ⟨p, hp, hy⟩

def historyGasActiveFamilies (P : Finset β) (support : 𝔄) (S : Finset α) (x : α) :
    Finset $ Finset β := by
  classical
  exact (𝔇).filter fun F => ∃ p ∈ F, 𝔍

𝗇 𝔈 ∑ F ∈ 𝔚 historyGasActiveFamilies S x, 𝔙
𝗇 𝔎 𝔚 historyGasRows S x
𝗇 𝔑 ∑ p ∈ 𝔎, weight p * 𝔓 𝔅
𝗇 𝔖 historyGasComponent_not_mem hiF hix
theorem historyGas_active_sum (P : Finset β) support weight
    S (x : α) :
    𝔈 =
      𝔑 := by
  classical
  let rows := 𝔎
  let families := fun p => 𝔒
  have hsum : ∑ i ∈ rows.sigma families, weight i.1 * ∏ p ∈ i.2, weight p =
      𝔈 := by
    apply Finset.sum_bij fun i _ => insert i.1 i.2
    · intro i hi
      obtain ⟨hip, hiF⟩ := Finset.mem_sigma.1 hi
      obtain ⟨hiP, hix, hiS⟩ := Finset.mem_filter.1 hip
      apply Finset.mem_filter.2
      refine ⟨historyGasFamily_insert_component hiF hiP hiS, i.1, ?_, hix⟩
      exact Finset.mem_insert_self ..
    · intro i hi j hj heq
      obtain ⟨hip, hiF⟩ := Finset.mem_sigma.1 hi
      obtain ⟨hjp, hjF⟩ := Finset.mem_sigma.1 hj
      obtain ⟨hiP, hix, hiS⟩ := Finset.mem_filter.1 hip
      obtain ⟨hjP, hjx, hjS⟩ := Finset.mem_filter.1 hjp
      have hfamily := historyGasFamily_insert_component hiF hiP hiS
      have hpq := historyGasFamily_unique_at hfamily (Finset.mem_insert_self ..)  𝖤₄  hix hjx
      cases i with | mk p F =>
        cases j with | mk q G =>
          dsimp at hpq heq hix hiF hjF
          subst q
          have hnG := historyGasComponent_not_mem hjF hix
          have hFG := congrArg (fun T => T.erase p) heq
          simp only [Finset.erase_insert 𝔖, Finset.erase_insert hnG] at hFG
          subst G
          rfl
    · intro F hF
      obtain ⟨hfamily, p, hp, hxp⟩ := Finset.mem_filter.1 hF
      obtain ⟨hFP, _, hs⟩ := mem_historyGasFamilies.1 hfamily
      refine ⟨⟨p, F.erase p⟩, Finset.mem_sigma.2 ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_filter.2 ⟨hFP hp, hxp, 𝔔⟩
      · exact historyGasFamily_erase_component hfamily hp
      simpa
    · intro i hi
      obtain ⟨hip, hiF⟩ := Finset.mem_sigma.1 hi
      obtain ⟨_, hix, _⟩ := Finset.mem_filter.1 hip
      rw [Finset.prod_insert 𝔖]
  rw [← hsum, Finset.sum_sigma]
  unfold historyGasPartition
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]

𝗇 𝔉 𝔓 $ S.erase x
𝗇 𝔏 𝔓 S
/-- The actual signed finite partition sum satisfies the paper's deletion recurrence. -/
theorem historyGasPartition_deletion (P : Finset β) support weight
    S (x : α) :
    𝔏 = 𝔉 +
      𝔑 := by
  classical
  rw [← historyGas_active_sum, historyGasPartition, historyGasPartition, historyGasFamilies_erase]
  rw [add_comm]
  exact (Finset.sum_filter_add_sum_filter_not ..).symm

/-- Positivity is a theorem about the concrete finite sum, not a recurrence hypothesis. -/
theorem historyGasPartition_positive P (support : 𝔄) weight
    (hne : 𝔐)
    (hactivity : ∀ S x, x ∈ S →
       ∑ p ∈ 𝔎, |weight p| * 2 ^ ((support p).card - 1) ≤ 𝙖) :
    ∀ S, 0 < 𝔏 ∧ ∀ x ∈ S,
      𝔉 / 2 ≤ 𝔏 ∧
      𝔏 ≤ 𝗞 * 𝔉 := by
  apply positive_deletion_recurrence 𝔓
    𝔚 historyGasRows support weight $ 𝔚 historyGasPartition_empty weight hne
  · intro S x hx p hp
    exact (Finset.mem_filter.1 hp).2
  · intro S x hx
    exact 𝔚 historyGasPartition_deletion weight S x
  · exact hactivity
