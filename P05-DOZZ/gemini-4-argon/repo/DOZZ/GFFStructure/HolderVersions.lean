/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import DOZZ.GFFStructure.HolderLimit

/-!
# Continuous Hölder versions on open exhaustions

Adapted from the limit-modification construction of the Brownian-motion formalization of Rémy
Degenne and collaborators (github.com/RemyDegenne/brownian-motion). Limits are taken along a fixed
countable dense set; agreement with the original process is proved in measure.
-/

@[expose] public section

open MeasureTheory Filter _root_.ProbabilityTheory _root_.Set _root_.Metric
open scoped ENNReal NNReal Topology Asymptotics

namespace DOZZ.Proofs

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}
  {U : Set T}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E]

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [hE : Nonempty E]
variable [IsFiniteMeasure P] [SecondCountableTopology T]

lemma exists_modification_holder'' (hT : HasBoundedCoveringNumber U c d)
    (hU : IsOpen U)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t ∈ U, Y t =ᵐ[P] X t) ∧
      (∀ (β : ℝ≥0), 0 < β → β < (q - d) / p → ∀ ω, ∃ C, HolderOnWith C β (Y · ω) U) ∧
      IsLimitOfIndicator Y X P U := by
  have h_ratio_pos : 0 < (q - d) / p := by
    have := hX.p_pos
    bound
  obtain ⟨β', hβ'_mono, hβ'_mem, hβ'_tendsto⟩ := exists_seq_strictMono_tendsto' h_ratio_pos
  let β : ℕ → ℝ≥0 := fun n ↦ ⟨β' n, (hβ'_mem n).1.le⟩
  have hβ_pos : ∀ n, 0 < β n := fun n ↦ mod_cast (hβ'_mem n).1
  obtain ⟨T', hT'_countable, hT'_dense⟩ := TopologicalSpace.exists_countable_dense T
  classical
  have := fun n ↦ exists_modification_holder_aux' hT hU hX hc hd_pos hdq_lt
    (hβ_pos n) (mod_cast (hβ'_mem n).2)
  choose Z hZ_meas hZ_ae_eq hZ_holder hZ_isLimit using this
  have hZ_ae_eq' n : ∀ᵐ ω ∂P, ∀ t ∈ U, edist (Z n t ω) (Z 0 t ω) = 0 := by
    refine indistinguishable_of_edist_modification_on hU
      (ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_) ?_
    · obtain ⟨_, h⟩ := hZ_holder n ω
      exact h.continuousOn (hβ_pos n)
    · obtain ⟨_, h⟩ := hZ_holder 0 ω
      exact h.continuousOn (hβ_pos 0)
    · intro t htU
      filter_upwards [hZ_ae_eq n t htU, hZ_ae_eq 0 t htU] with ω hω₁ hω₂
      simp [hω₁, hω₂]
  rw [← ae_all_iff] at hZ_ae_eq'
  let A := {ω | ∀ n t, t ∈ U → edist (Z n t ω) (Z 0 t ω) = 0}
  have hA : MeasurableSet A := by
    rw [(show A = ⋂ n, {ω | ∀ t, t ∈ U → edist (Z n t ω) (Z 0 t ω) = 0} by ext; simp [A])]
    refine MeasurableSet.iInter (fun n ↦ ?_)
    refine Measurable.measurableSet_edist_eqOn_zero_of_continuous hU (fun ω ↦ ?_) (fun ω ↦ ?_)
      fun t ↦ ?_
    · obtain ⟨_, h⟩ := hZ_holder n ω
      exact h.continuousOn (hβ_pos n)
    · obtain ⟨_, h⟩ := hZ_holder 0 ω
      exact h.continuousOn (hβ_pos 0)
    · refine IsLimitOfIndicator.measurable_edist hX.measurable hX.measurable
        hX.measurablePair (hZ_isLimit n) (hZ_isLimit 0) t t
  have hA_ae : ∀ᵐ ω ∂P, ω ∈ A := hZ_ae_eq'
  classical
  let Y (t : T) (ω : Ω) : E := indicatorProcess (Z 0) A t ω
  classical
  refine ⟨Y, fun t ↦ Measurable.ite hA (hZ_meas 0 t) (by fun_prop), fun t htU ↦ ?_, ?_, ?_⟩
  · filter_upwards [hA_ae, hZ_ae_eq 0 t htU] with ω hω hω₂
    simpa only [hω, ↓reduceIte, Y, indicatorProcess_apply] using hω₂
  · intro β₀ hβ₀_pos hβ₀_lt ω
    by_cases hω : ω ∈ A
    swap; · simp [hω, Y, HolderOnWith]
    simp only [hω, ↓reduceIte, Y, indicatorProcess_apply]
    obtain ⟨n, hn⟩ : ∃ n, β₀ < β n := by
      obtain ⟨n, hn⟩ : ∃ n, β₀ < β' n := (Tendsto.eventually_const_lt hβ₀_lt hβ'_tendsto).exists
      exact ⟨n, mod_cast hn⟩
    suffices ∃ C, HolderOnWith C (β n) (fun x ↦ Z 0 x ω) U by
      obtain ⟨C, hC⟩ := this
      refine HolderOnWith.mono_right' hC hn.le (C' := (Metric.ediam U).toNNReal) ?_
      rw [ENNReal.coe_toNNReal hT.ediam_lt_top.ne]
      exact fun x hx y hy ↦ Metric.edist_le_ediam_of_mem hx hy
    simp only [Set.mem_ofPred_eq, A] at hω
    obtain ⟨C, hC⟩ := hZ_holder n ω
    refine ⟨C, fun s hs t ht ↦ ?_⟩
    specialize hC s hs t ht
    simp only
    rw [← edist_congr_left (hω n t ht), ← edist_congr_right (hω n s hs)]
    exact hC
  · exact IsLimitOfIndicator.indicatorProcess (hZ_isLimit 0) A hA hA_ae

lemma exists_modification_holder''' {C : ℕ → Set T} {c : ℕ → ℝ≥0∞}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : IsKolmogorovProcess X P p q M) (hc : ∀ n, c n ≠ ∞)
    (hd_pos : 0 < d) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t) ∧
      (∀ ω t, ∃ U ∈ 𝓝 t, ∀ (β : ℝ≥0), 0 < β → β < (q - d) / p → ∃ C, HolderOnWith C β (Y · ω) U) ∧
      IsLimitOfIndicator Y X P Set.univ := by
  have hp_pos := hX.p_pos
  have h_div_pos : 0 < (q - d) / p := by bound
  let ⟨β₀', hβ₀_pos', hβ₀_lt'⟩ := exists_between h_div_pos
  let β₀ : ℝ≥0 := ⟨β₀', hβ₀_pos'.le⟩
  have hβ₀_pos := mod_cast hβ₀_pos'
  have hβ₀_lt := mod_cast hβ₀_lt'
  classical
  choose Z hZ hZ_eq hZ_holder hZ_extend
    using fun n ↦ exists_modification_holder'' (hC.hasBoundedCoveringNumber n) (hC.isOpen n) hX
      (hc n) hd_pos hdq_lt
  have hZ_ae_eq : ∀ᵐ ω ∂P, ∀ n t (ht : t ∈ C n), edist (Z n t ω) (Z (n + 1) t ω) = 0 := by
    rw [ae_all_iff]
    intro n
    refine indistinguishable_of_edist_modification_on (hC.isOpen n)
      (ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_) ?_
    · obtain ⟨_, h⟩ := hZ_holder n β₀ hβ₀_pos hβ₀_lt ω
      exact h.continuousOn hβ₀_pos
    · obtain ⟨_, h⟩ := hZ_holder (n + 1) β₀ hβ₀_pos hβ₀_lt ω
      refine (h.continuousOn hβ₀_pos).mono ?_
      exact hC.mono _ _ (Nat.le_succ _)
    · intro t htCn
      filter_upwards [hZ_eq n t htCn, hZ_eq (n + 1) t (hC.mono _ _ (Nat.le_succ _) htCn)]
        with ω hω₁ hω₂
      simp [hω₁, hω₂]
  let A := {ω | ∀ n t (ht : t ∈ C n), edist (Z n t ω) (Z (n + 1) t ω) = 0}
  have hA_eq_le {ω} (hω : ω ∈ A) {n m} (hnm : n ≤ m) (t : C n) : edist (Z n t ω) (Z m t ω) = 0 := by
    induction m with
    | zero => simp only [nonpos_iff_eq_zero] at hnm; subst hnm; simp
    | succ m hm =>
      by_cases hnm' : n ≤ m
      · specialize hm hnm'
        rw [edist_congr_right hm]
        exact hω m t (hC.mono _ _ hnm' t.2)
      · have : n = m + 1 := by omega
        simp [this]
  have hA : MeasurableSet A := by
    rw [(show A = ⋂ n, {ω | ∀ t ∈ C n, edist (Z n t ω) (Z (n + 1) t ω) = 0} by ext; simp [A])]
    refine MeasurableSet.iInter (fun n ↦ ?_)
    refine Measurable.measurableSet_edist_eqOn_zero_of_continuous (hC.isOpen n)
      (fun ω ↦ ?_) (fun ω ↦ ?_) fun t ↦ ?_
    · obtain ⟨_, h⟩ :=  hZ_holder n β₀ hβ₀_pos hβ₀_lt ω
      exact h.continuousOn hβ₀_pos
    · obtain ⟨_, h⟩ :=  hZ_holder (n + 1) β₀ hβ₀_pos hβ₀_lt ω
      refine (h.continuousOn hβ₀_pos).mono ?_
      exact hC.mono _ _ (Nat.le_succ _)
    · refine IsLimitOfIndicator.measurable_edist ?_ ?_ ?_ (hZ_extend n) (hZ_extend (n + 1)) _ _
      · exact hX.measurable
      · exact hX.measurable
      · intro i j
        exact hX.measurablePair i j
  have hA_ae := hZ_ae_eq
  classical
  -- for each `t`, find `n` such that `t ∈ C n` and call it `nt t`
  have h_mem t : ∃ n, t ∈ C n := by
    simpa using (hC.subset_iUnion (by simp : t ∈ Set.univ))
  let nt t := Nat.find (h_mem t)
  have hnt t : t ∈ C (nt t) := Nat.find_spec (h_mem t)
  choose A' hA'_meas hA'_ae hZ_tendsto hZC_eq hZCc_eq using hZ_extend
  let Y (t : T) (ω : Ω) : E := if ω ∈ (A ∩ ⋂ n, A' n) then Z (nt t) t ω else hE.some
  have hY_eq {ω} (hω : ω ∈ A ∩ ⋂ n, A' n) n (t : T) (ht : t ∈ C n) :
      edist (Y t ω) (Z n t ω) = 0 := by
    simp only [hω, ↓reduceIte, Y]
    exact hA_eq_le hω.1 (Nat.find_le ht) ⟨t, hnt t⟩
  refine ⟨Y, fun t ↦ Measurable.ite (MeasurableSet.inter hA (MeasurableSet.iInter hA'_meas)) (hZ _ _) (by fun_prop), fun t ↦ ?_, ?_, ?_⟩
  · specialize hZ (nt t) t
    filter_upwards [(show ∀ᵐ ω ∂P, ω ∈ A ∩ ⋂ n, A' n by simp only [Set.mem_inter_iff, Set.mem_iInter, eventually_and, ae_all_iff]; exact ⟨hA_ae, hA'_ae⟩), hZ_eq (nt t) t (hnt t)] with ω hω hω₂
    simp only [hω, ↓reduceIte, hω₂, Y, A]
  · intro ω t
    refine ⟨C (nt t), (hC.isOpen (nt t)).mem_nhds (hnt t), ?_⟩
    intro β₀ hβ₀_pos hβ₀_lt
    by_cases hω : ω ∈ A ∩ ⋂ n, A' n
    swap
    · unfold Y
      simp_rw [ite_eq_right hω]
      simp [HolderOnWith]
    obtain ⟨C', hC'⟩ := hZ_holder (nt t) β₀ hβ₀_pos hβ₀_lt ω
    refine ⟨C', ?_⟩
    intro s hs s' hs'
    simp only
    rw [edist_congr_right (hY_eq hω (nt t) s hs), edist_congr_left (hY_eq hω (nt t) s' hs')]
    exact hC' s hs s' hs'
  · refine ⟨A ∩ ⋂ n, A' n, ?_, ?_, ?_, ?_, ?_⟩
    · exact hA.inter (MeasurableSet.iInter hA'_meas)
    · simp only [Set.mem_inter_iff, Set.mem_iInter, eventually_and, ae_all_iff]
      exact ⟨hA_ae, hA'_ae⟩
    · rintro t - ω hω
      simp only [Set.mem_inter_iff, Set.mem_iInter] at hω
      exact hZ_tendsto (nt t) t (hnt t) ω (hω.2 (nt t))
    · intro t _ ω
      classical
      simp only [indicatorProcess_apply]
      by_cases hω : ω ∈ A ∩ ⋂ n, A' n
      swap
      · simp only [hω, ↓reduceIte, Y, Dense.extend, IsDenseInducing.extend]
        have : @NeBot { x // x ∈ denseCountable T } (comap Subtype.val (𝓝 t)) := by
          apply IsDenseInducing.comap_nhds_neBot (Dense.isDenseInducing_val dense_denseCountable)
        rw [edist_comm]
        exact edist_limUnder_const
      simp only [hω, ↓reduceIte, Y]
      specialize hZC_eq _ t (hnt t)
      simp only [Set.mem_inter_iff, Set.mem_iInter] at hω
      simp only [indicatorProcess_apply] at hZC_eq
      convert hZC_eq ω
      rw [ite_eq_left]
      exact hω.2 _
    · simp

lemma exists_modification_holder' {C : ℕ → Set T} {c : ℕ → ℝ≥0∞}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : IsAEKolmogorovProcess X P p q M) (hc : ∀ n, c n ≠ ∞)
    (hd_pos : 0 < d) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω t, ∃ U ∈ 𝓝 t, ∀ (β : ℝ≥0) (_ : 0 < β) (_ : β < (q - d) / p),
        ∃ C, HolderOnWith C β (Y · ω) U := by
  obtain ⟨Y, hY_meas, hY_eq, hY_holder, _⟩ :=
    exists_modification_holder''' hC hX.IsKolmogorovProcess_mk hc hd_pos hdq_lt
  refine ⟨Y, hY_meas, fun t ↦ ?_, hY_holder⟩
  filter_upwards [hX.ae_eq_mk t, hY_eq t] with ω hω1 hω2 using hω2.trans hω1.symm

end PseudoEMetricSpace

section EMetricSpace

variable [PseudoEMetricSpace T] [EMetricSpace E] [hE : Nonempty E]

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

end EMetricSpace

/-- Compatible continuous local modifications glue on a countable open cover. -/
theorem exists_continuous_modification_of_open_cover {T Ω I : Type*}
    [MetricSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    [MeasurableSpace Ω] [Countable I] (P : Measure Ω) (X : T → Ω → ℝ)
    (U : I → Set T) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ t, ∃ i, t ∈ U i)
    (Z : I → T → Ω → ℝ) (hZmeas : ∀ i t, Measurable (Z i t))
    (hZcont : ∀ i ω, Continuous (fun t => Z i t ω))
    (hZeq : ∀ i t, t ∈ U i → Z i t =ᵐ[P] X t) :
    ∃ Y : T → Ω → ℝ, (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ t, Y t =ᵐ[P] X t) ∧
      Measurable (fun p : Ω × T => Y p.2 p.1) := by
  classical
  choose index hindex using hcover
  let A := {ω | ∀ i j t, t ∈ U i ∩ U j → Z i t ω = Z j t ω}
  have hAae : ∀ᵐ ω ∂P, ω ∈ A := by
    have hpair i j : ∀ᵐ ω ∂P, ∀ t ∈ U i ∩ U j, Z i t ω = Z j t ω := by
      have h := indistinguishable_of_edist_modification_on ((hU i).inter (hU j))
        (ae_of_all P (fun ω => (hZcont i ω).continuousOn))
        (ae_of_all P (fun ω => (hZcont j ω).continuousOn)) (fun t ht => ?_)
      · simpa only [edist_eq_zero] using h
      · filter_upwards [hZeq i t ht.1, hZeq j t ht.2] with ω hi hj
        simp only [hi, hj, edist_self]
    simpa only [A, mem_ofPred_eq, ae_all_iff] using hpair
  let Y (t : T) (ω : Ω) := if ω ∈ A then Z (index t) t ω else 0
  have hYmeas t : Measurable (Y t) := Measurable.ite (by rw [(show A = ⋂ i, ⋂ j, {ω | ∀ t ∈ U i ∩ U j, edist (Z i t ω) (Z j t ω) = 0} by ext ω; simp only [A, mem_ofPred_eq, mem_iInter, edist_eq_zero])]; exact MeasurableSet.iInter fun i => MeasurableSet.iInter ((fun i j => by exact DOZZ.Proofs.Measurable.measurableSet_edist_eqOn_zero_of_continuous ((hU i).inter (hU j)) (fun ω => (hZcont i ω).continuousOn) (fun ω => (hZcont j ω).continuousOn) (fun t => (hZmeas i t).edist (hZmeas j t))) i)) (hZmeas (index t) t) measurable_const
  have hYeq i {ω} (hω : ω ∈ A) : EqOn (fun t => Y t ω) (fun t => Z i t ω) (U i) := by
    intro t ht
    simp only [Y, hω, ↓reduceIte]
    exact hω (index t) i t ⟨hindex t, ht⟩
  have hYcont ω : Continuous (fun t => Y t ω) := by
    by_cases hω : ω ∈ A
    · apply continuous_iff_continuousAt.mpr
      intro t
      exact (hZcont (index t) ω).continuousAt.congr_of_eventuallyEq (Filter.eventually_of_mem ((hU (index t)).mem_nhds (hindex t)) (hYeq (index t) hω))
    · simpa only [Y, hω, ↓reduceIte] using (continuous_const : Continuous (fun _ => (0 : ℝ)))
  refine ⟨Y, hYmeas, hYcont, ?_, ?_⟩
  · intro t
    filter_upwards [hAae, hZeq (index t) t (hindex t)] with ω hω ht
    simpa only [Y, hω, ↓reduceIte] using ht
  · exact (measurable_uncurry_of_continuous_of_measurable hYcont hYmeas).comp measurable_swap

end DOZZ.Proofs
