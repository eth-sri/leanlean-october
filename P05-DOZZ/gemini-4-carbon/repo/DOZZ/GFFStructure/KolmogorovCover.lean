/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import DOZZ.GFFStructure.CoveringBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Order.CompleteLattice.Group
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.EMetricSpace.PairReduction

/-!
# Kolmogorov moment bounds along finite metric covers
-/

@[expose] public section

open MeasureTheory _root_.ProbabilityTheory _root_.Metric _root_.Finset
open scoped ENNReal NNReal Finset

namespace DOZZ.Proofs

private lemma finset_iSup_sum_le {α ι : Type*} {β : Sort*} [CompleteLattice α] [AddCommMonoid α]
    [IsOrderedAddMonoid α] {I : Finset ι} (f : ι → β → α) :
    ⨆ b, ∑ i ∈ I, f i b ≤ ∑ i ∈ I, ⨆ b, f i b := by
  classical
  induction I using Finset.induction with
  | empty => simp
  | insert i I hi ih => simpa only [Finset.sum_insert hi] using (iSup_add_le _ _).trans (by gcongr)

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E]
  {p q : ℝ} {M : ℝ≥0} {P : Measure Ω} {X : T → Ω → E}

lemma IsAEKolmogorovProcess.lintegral_sup_rpow_edist_eq_zero' (hX : IsAEKolmogorovProcess X P p q M)
    {J : Set T} (hJ : J.Countable) {δ : ℝ≥0∞}
    (h : ∀ (s : J) (t : { t : J // edist s t ≤ δ }), edist s t = 0) :
    ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P = 0 := by
  have : Countable J := hJ
  refine (lintegral_eq_zero_iff' (AEMeasurable.iSup fun _ => AEMeasurable.iSup fun _ =>
    hX.aemeasurable_edist.pow_const _)).2 ?_
  exact (ae_all_iff.2 fun s => ae_all_iff.2 fun t => hX.edist_eq_zero (h s t)).mono fun ω hω => by
    simp [hω, hX.p_pos]

private lemma lintegral_sup_pair_le (hX : IsAEKolmogorovProcess X P p q M)
    {ε : ℝ≥0∞} (C : Finset (T × T)) (hC : ∀ u ∈ C, edist u.1 u.2 ≤ ε) :
    ∫⁻ ω, ⨆ u : C, edist (X u.1.1 ω) (X u.1.2 ω) ^ p ∂P ≤ #C * M * ε ^ q := by
  calc ∫⁻ ω, ⨆ u : C, edist (X u.1.1 ω) (X u.1.2 ω) ^ p ∂P
    _ = ∫⁻ ω, C.sup (fun u => edist (X u.1 ω) (X u.2 ω) ^ p) ∂P := by
        simp only [iSup_subtype, Finset.sup_eq_iSup]
    _ ≤ ∫⁻ ω, ∑ u ∈ C, edist (X u.1 ω) (X u.2 ω) ^ p ∂P :=
        lintegral_mono fun ω => Finset.sup_le_iff.2 fun _ hb =>
          Finset.single_le_sum (f := fun u : T × T => edist (X u.1 ω) (X u.2 ω) ^ p) (fun _ _ => zero_le) hb
    _ = ∑ u ∈ C, ∫⁻ ω, edist (X u.1 ω) (X u.2 ω) ^ p ∂P :=
        lintegral_finsetSum' _ fun _ _ => hX.aemeasurable_edist.pow_const _
    _ ≤ ∑ u ∈ C, M * ε ^ q := Finset.sum_le_sum fun u hu =>
        (hX.kolmogorovCondition u.1 u.2).trans (by gcongr; exacts [hX.q_pos.le, hC u hu])
    _ = #C * M * ε ^ q := by simp [mul_assoc]

section FirstTerm

variable {J : Set T}

lemma lintegral_sup_rpow_edist_cover_rescale (hX : IsAEKolmogorovProcess X P p q M) (hJ : J.Finite)
    {C : ℕ → Finset T} {ε₀ : ℝ≥0}
    (hC : ∀ i, IsCover (ε₀ * 2⁻¹ ^ i) J (C i)) (hC_subset : ∀ i, (C i : Set T) ⊆ J)
    (hC_card : ∀ i, #(C i) = coveringNumber (ε₀ * 2⁻¹ ^ i) J)
    {δ : ℝ≥0} (_hδ_pos : 0 < δ) (_hδ_le : δ ≤ ε₀ * 4)
    {k m : ℕ} (hm₁ : ε₀ * 2⁻¹ ^ m ≤ δ) (hm₂ : δ ≤ ε₀ * 4 * 2⁻¹ ^ m) (hmk : m ≤ k) :
    ∫⁻ ω, ⨆ (s : C k) (t : { t : C k // edist s t ≤ δ }),
        edist (X (chainingSequence C s k m) ω) (X (chainingSequence C t k m) ω) ^ p ∂P
      ≤ 2 ^ (p + 1) * M
        * (16 * δ * Nat.log2 (coveringNumber (δ/4) J).toNat) ^ q
        * coveringNumber (δ/4) J := by
  rcases Set.eq_empty_or_nonempty J with hJe | hJ'
  · have hCk : C k = ∅ := Finset.coe_eq_empty.mp (Set.subset_empty_iff.mp (hJe ▸ hC_subset k))
    have : IsEmpty (C k) := ⟨fun x => by simpa [hCk] using x.2⟩
    simp
  have hf (pt : (s : C k) × { t : C k // edist s t ≤ δ }) :
      edist (chainingSequence C pt.1 k m) (chainingSequence C pt.2 k m) ≤ ε₀ * 8 * 2⁻¹ ^ m := by
    refine (edist_chainingSequence_pow_two_le hC hC_subset pt.1.2 pt.2.1.2 _ hmk hmk).trans ?_
    rw [show (8 : ℝ≥0∞) = 4 + 4 by norm_num, mul_add, add_mul]
    refine add_le_add_left (pt.2.2.trans ?_) _
    simpa [ENNReal.inv_pow] using (mod_cast hm₂ : (δ : ℝ≥0∞) ≤ ((ε₀ * 4 * 2⁻¹ ^ m : ℝ≥0) : ℝ≥0∞))
  let f : (s : C k) × { t : C k // edist s t ≤ δ } →
      (s : C m) × { t : C m // edist s t ≤ ε₀ * 8 * 2⁻¹ ^ m } :=
    fun pt => ⟨⟨chainingSequence C pt.1 k m, chainingSequence_mem hC hJ' pt.1.2 _ hmk⟩,
      ⟨⟨chainingSequence C pt.2 k m, chainingSequence_mem hC hJ' pt.2.1.2 _ hmk⟩, hf pt⟩⟩
  simp only [iSup_sigma']
  refine (lintegral_mono fun ω => iSup_comp_le (fun st => edist (X st.1 ω) (X st.2 ω) ^ p) f).trans ?_
  simp only [iSup_sigma]
  -- Cover bound on `C m` at scale `c₀ = ε₀ * 8 * 2⁻¹ ^ m`
  let c₀ : ℝ≥0∞ := ε₀ * 8 * 2⁻¹ ^ m
  have hCm_bd : ∫⁻ ω, ⨆ (s : C m) (t : { t : C m // edist s t ≤ c₀ }), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 2 ^ (p + 1) * M * (2 * c₀ * Nat.log2 (coveringNumber (ε₀ * 2⁻¹ ^ m) J).toNat) ^ q
        * coveringNumber (ε₀ * 2⁻¹ ^ m) J := by
    rcases eq_or_ne #(C m) 0 with h0 | h0
    · have hCm : C m = ∅ := Finset.card_eq_zero.mp h0
      have : IsEmpty (C m) := ⟨fun x => by simpa [hCm] using x.2⟩
      simp
    by_cases h1 : #(C m) = 1
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
      simp [ha, iSup_subtype, ENNReal.zero_rpow_of_pos hX.p_pos]
    let rbar := 1 + Nat.log2 #(C m)
    have hcard : (#(C m) : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ rbar :=
      mod_cast (by simpa [rbar, add_comm 1] using Nat.lt_log2_self.le : #(C m) ≤ 2 ^ rbar)
    have hrbar : rbar ≤ 2 * Nat.log2 #(C m) := by
      have : 1 ≤ Nat.log2 #(C m) := by rw [Nat.le_log2] <;> omega
      omega
    obtain ⟨K, -, _, hKeps, hKle⟩ := EMetric.pair_reduction hcard c₀ E
    have hpr : ∫⁻ ω, ⨆ (s : C m) (t : { t : C m // edist s t ≤ c₀ }), edist (X s ω) (X t ω) ^ p ∂P
        ≤ 2 ^ p * 2 * #(C m) * M * (c₀ * rbar) ^ q := by
      calc _ = ∫⁻ ω, (⨆ (s : C m) (t : { t : C m // edist s t ≤ c₀ }), edist (X s ω) (X t ω)) ^ p ∂P := by
            simp only [← (ENNReal.monotone_rpow_of_nonneg hX.p_pos.le).map_iSup_of_continuousAt
              ENNReal.continuous_rpow_const.continuousAt (by simp [hX.p_pos])]
        _ ≤ ∫⁻ ω, (2 * ⨆ u : K, edist (X u.1.1 ω) (X u.1.2 ω)) ^ p ∂P := by
            gcongr with ω; exacts [hX.p_pos.le, hKle (X · ω)]
        _ = 2 ^ p * ∫⁻ ω, ⨆ u : K, edist (X u.1.1 ω) (X u.1.2 ω) ^ p ∂P := by
            simp only [ENNReal.mul_rpow_of_nonneg _ _ hX.p_pos.le,
              (ENNReal.monotone_rpow_of_nonneg hX.p_pos.le).map_iSup_of_continuousAt
                ENNReal.continuous_rpow_const.continuousAt (by simp [hX.p_pos])]
            exact lintegral_const_mul'' _ (AEMeasurable.iSup fun _ => hX.aemeasurable_edist.pow_const _)
        _ ≤ 2 ^ p * (#K * M * (rbar * c₀) ^ q) :=
            mul_le_mul' le_rfl (lintegral_sup_pair_le hX K fun u hu => hKeps u.1 u.2 hu)
        _ ≤ 2 ^ p * 2 * #(C m) * M * (c₀ * rbar) ^ q := by
            simp only [← mul_assoc]; rw [mul_assoc _ 2, mul_comm _ c₀]; gcongr
    refine hpr.trans ?_
    simp only [← hC_card m, ENat.toNat_natCast, ENat.toENNReal_coe]
    rw [show (2 : ℝ≥0∞) ^ (p + 1) = 2 ^ p * 2 by rw [ENNReal.rpow_add _ _ (by norm_num) (by norm_num), ENNReal.rpow_one]]
    calc 2 ^ p * 2 * #(C m) * M * (c₀ * rbar) ^ q
      _ = 2 ^ p * 2 * M * (c₀ * rbar) ^ q * #(C m) := by ring
      _ ≤ 2 ^ p * 2 * M * (2 * c₀ * Nat.log2 #(C m)) ^ q * #(C m) := by
          rw [mul_comm 2 c₀, mul_assoc c₀ 2]; gcongr; exacts [hX.q_pos.le, mod_cast hrbar]
  refine hCm_bd.trans ?_
  have hint : coveringNumber (ε₀ * 2⁻¹ ^ m) J ≤ coveringNumber (δ / 4) J :=
    coveringNumber_anti (by rw [div_le_iff₀ (by simp)]; convert hm₂ using 1; ring)
  gcongr _ * _ * (?_ * ?_) ^ q * ?_
  · exact hX.q_pos.le
  · dsimp [c₀]; rw [mul_comm _ 8, ← mul_assoc, ← mul_assoc, mul_assoc]
    gcongr
    · norm_num
    · simpa [ENNReal.inv_pow] using (mod_cast hm₁ : ((ε₀ * 2⁻¹ ^ m : ℝ≥0) : ℝ≥0∞) ≤ δ)
  · rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact mod_cast Nat.log_mono_right (ENat.toNat_le_toNat hint
      (ne_top_of_le_ne_top (by simpa) (IsCover.coveringNumber_le_encard (subset_rfl : J ⊆ J) (by simp) (ε := δ / 4))))
  · simpa only [ENat.toENNReal_le]

end FirstTerm

section SecondTerm

variable {J : Set T} {C : ℕ → Finset T} {ε : ℕ → ℝ≥0} {j k m : ℕ}

private lemma lintegral_sup_succ (hX : IsAEKolmogorovProcess X P p q M)
    (hC : ∀ n, IsCover (ε n) J (C n)) (hC_subset : ∀ n, (C n : Set T) ⊆ J) (hjk : j < k) :
    ∫⁻ ω, ⨆ t : C k, edist (X (chainingSequence C t k j) ω) (X (chainingSequence C t k (j + 1)) ω) ^ p ∂P
      ≤ #(C (j + 1)) * M * ε j ^ q := by
  rcases Set.eq_empty_or_nonempty J with hJe | hJ
  · have hCk : C k = ∅ := Finset.coe_eq_empty.mp (Set.subset_empty_iff.mp (hJe ▸ hC_subset k))
    have : IsEmpty (C k) := ⟨fun x => by simpa [hCk] using x.2⟩
    simp
  let f₀ : C (j + 1) → T × T := fun x => (chainingSequence C x (j + 1) j, x.1)
  let C' := (C (j + 1)).attach.map ⟨f₀, fun _ _ h => Subtype.ext (congrArg Prod.snd h)⟩
  have hC' : #C' = #(C (j + 1)) := by grind
  let g : C k → C' := fun x => ⟨f₀ ⟨chainingSequence C x k (j + 1),
    chainingSequence_mem hC hJ x.2 (j + 1) (by omega)⟩,
    Finset.mem_map.2 ⟨⟨_, chainingSequence_mem hC hJ x.2 (j + 1) (by omega)⟩, Finset.mem_attach _ _, rfl⟩⟩
  have hle := lintegral_mono (μ := P) fun ω => iSup_comp_le (fun x : C' => edist (X x.1.1 ω) (X x.1.2 ω) ^ p) g
  simp only [g, f₀] at hle
  conv_lhs at hle => right; ext ω; congr; ext x; rw [chainingSequence_chainingSequence (j + 1) (by omega) j (by omega)]
  refine hle.trans (hC' ▸ lintegral_sup_pair_le hX C' ?_)
  rintro _ hu; obtain ⟨u, _, rfl⟩ := Finset.mem_map.1 hu
  exact edist_chainingSequence_add_one_self hC hC_subset u.2

private lemma geom_sum_two_inv_le {α : ℝ} (hα : 0 < α) (N : ℕ) :
    ∑ i ∈ Finset.range N, ((2⁻¹ : ℝ≥0∞) ^ α) ^ i ≤ 2 ^ α * (2 ^ α - 1)⁻¹ := by
  calc ∑ i ∈ Finset.range N, ((2⁻¹ : ℝ≥0∞) ^ α) ^ i
    _ ≤ ∑' i : ℕ, ((2⁻¹ : ℝ≥0∞) ^ α) ^ i := ENNReal.sum_le_tsum _
    _ = (1 - 2⁻¹ ^ α)⁻¹ := ENNReal.tsum_geometric _
    _ = (2⁻¹ ^ α * 2 ^ α - 2⁻¹ ^ α * 1)⁻¹ := by
        rw [mul_one, ← ENNReal.mul_rpow_of_nonneg _ _ hα.le,
          ENNReal.inv_mul_cancel (by simp) (by simp), ENNReal.one_rpow]
    _ = (2⁻¹ ^ α * (2 ^ α - 1))⁻¹ := by rw [← ENNReal.mul_sub (fun _ _ => by finiteness)]
    _ = 2 ^ α * (2 ^ α - 1)⁻¹ := by
        rw [ENNReal.mul_inv (.inr (by finiteness)) (.inl (by simp)), ENNReal.inv_rpow, inv_inv]

noncomputable
def Cp (d p q : ℝ) : ℝ≥0∞ :=
  max (1 / ((2 ^ ((q - d) / p)) - 1) ^ p) (1 / (2 ^ (q - d) - 1))

lemma second_term_bound {C : ℕ → Finset T} {k m : ℕ}
    (hX : IsAEKolmogorovProcess X P p q M) {ε₀ : ℝ≥0} (hε : ε₀ ≤ Metric.ediam J)
    (hC : ∀ n, IsCover (ε₀ * 2⁻¹ ^ n) J (C n)) (hC_subset : ∀ n, (C n : Set T) ⊆ J)
    (hC_card : ∀ n, #(C n) = coveringNumber (ε₀ * 2⁻¹ ^ n) J)
    {c₁ : ℝ≥0∞} {d : ℝ} (hdq : d < q)
    (h_cov : HasBoundedCoveringNumber J c₁ d)
    (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence C t k m) ω) ^ p ∂P
      ≤ 2 ^ d * M * c₁ * (2 * ε₀ * 2⁻¹ ^ m) ^ (q - d) * Cp d p q := by
  let ε (n : ℕ) := ε₀ * 2⁻¹ ^ n
  have hε_le (n : ℕ) : (ε n : ℝ≥0∞) ≤ Metric.ediam J := by
    rw [← mul_one (Metric.ediam J), ENNReal.coe_mul]
    gcongr; norm_cast; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hε' : (ε₀ : ℝ≥0∞) ≠ ∞ := by simp
  have hp_pos := hX.p_pos
  have hqd_pos : 0 < q - d := sub_pos.2 hdq
  rw [Cp, mul_max, mul_one_div, mul_one_div]
  rcases le_total p 1 with hp | hp
  · refine le_trans ?_ (le_max_right _ _)
    have h1 : ∫⁻ ω, ⨆ t : C k, edist (X t ω) (X (chainingSequence C t k m) ω) ^ p ∂P
        ≤ M * c₁ * ∑ j ∈ Finset.range (k - m), (ε (m + j + 1) : ℝ≥0∞) ^ (-d) * (ε (m + j) : ℝ≥0∞) ^ q := by
      calc _ ≤ ∑ i ∈ Finset.range (k - m), ∫⁻ ω, ⨆ t : C k,
              edist (X (chainingSequence C t k (m + i)) ω) (X (chainingSequence C t k (m + i + 1)) ω) ^ p ∂P := by
            rw [← lintegral_finsetSum' _ fun _ _ => .iSup fun _ => hX.aemeasurable_edist.pow_const _]
            refine lintegral_mono fun ω => le_trans ?_ (finset_iSup_sum_le _)
            gcongr with t
            exact (ENNReal.rpow_le_rpow (edist_chainingSequence_le_sum_edist (X · ω) hm) hp_pos.le).trans
              (ENNReal.rpow_finsetSum_le_finsetSum_rpow hp_pos hp)
        _ ≤ ∑ i ∈ Finset.range (k - m), (#(C (m + i + 1)) * M * (ε (m + i) : ℝ≥0∞) ^ q) :=
            Finset.sum_le_sum fun i hi => lintegral_sup_succ hX hC hC_subset (by simp at hi; omega)
        _ ≤ M * c₁ * ∑ i ∈ Finset.range (k - m), (ε (m + i + 1) : ℝ≥0∞) ^ (-d) * (ε (m + i) : ℝ≥0∞) ^ q := by
            simp_rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun i _ => ?_
            have hc : (#(C (m + i + 1)) : ℝ≥0∞) ≤ c₁ * (ε (m + i + 1) : ℝ≥0∞) ^ (-d) := by
              rw [show (#(C (m + i + 1)) : ℝ≥0∞) = coveringNumber (ε (m + i + 1)) J from mod_cast hC_card _,
                ENNReal.rpow_neg, ← ENNReal.inv_rpow]
              exact h_cov.coveringNumber_le _ (hε_le _)
            calc (#(C (m + i + 1)) : ℝ≥0∞) * M * (ε (m + i) : ℝ≥0∞) ^ q
              _ ≤ (c₁ * (ε (m + i + 1) : ℝ≥0∞) ^ (-d)) * M * (ε (m + i) : ℝ≥0∞) ^ q := by gcongr
              _ = M * c₁ * ((ε (m + i + 1) : ℝ≥0∞) ^ (-d) * (ε (m + i) : ℝ≥0∞) ^ q) := by ring
    refine h1.trans ?_
    have hterm (j : ℕ) : (ε (m + j + 1) : ℝ≥0∞) ^ (-d) * (ε (m + j) : ℝ≥0∞) ^ q =
        2 ^ d * ((ε₀ : ℝ≥0∞) * 2⁻¹ ^ m) ^ (q - d) * ((2⁻¹ : ℝ≥0∞) ^ (q - d)) ^ j := by
      dsimp [ε]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_ofNat]
      have hadd := ENNReal.rpow_add_of_add_pos (x := (ε₀ : ℝ≥0∞) * 2⁻¹ ^ (m + j)) (y := -d) (z := q)
        (ENNReal.mul_ne_top hε' (by simp)) (by linarith)
      rw [pow_succ, ← mul_assoc, ENNReal.mul_rpow_of_ne_top (ENNReal.mul_ne_top hε' (by simp)) (by simp),
        ENNReal.inv_rpow, ENNReal.rpow_neg 2, inv_inv, mul_right_comm _ (2 ^ d), ← hadd,
        show -d + q = q - d by ring, pow_add, ← mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ hqd_pos.le,
        ← ENNReal.rpow_natCast_mul, ← ENNReal.rpow_mul_natCast, mul_comm (j : ℝ)]
      ring
    simp_rw [hterm, ← Finset.mul_sum]
    calc (M : ℝ≥0∞) * c₁ * (2 ^ d * ((ε₀ : ℝ≥0∞) * 2⁻¹ ^ m) ^ (q - d) *
            ∑ j ∈ Finset.range (k - m), ((2⁻¹ : ℝ≥0∞) ^ (q - d)) ^ j)
      _ ≤ M * c₁ * (2 ^ d * ((ε₀ : ℝ≥0∞) * 2⁻¹ ^ m) ^ (q - d) * (2 ^ (q - d) * (2 ^ (q - d) - 1)⁻¹)) := by
          gcongr; exact geom_sum_two_inv_le hqd_pos _
      _ = 2 ^ d * M * c₁ * (2 * (ε₀ : ℝ≥0∞) * 2⁻¹ ^ m) ^ (q - d) / (2 ^ (q - d) - 1) := by
          rw [div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg _ _ hqd_pos.le,
            ENNReal.mul_rpow_of_nonneg _ _ hqd_pos.le, ENNReal.mul_rpow_of_nonneg _ _ hqd_pos.le]; ring
  · refine le_trans ?_ (le_max_left _ _)
    have h1 : ∫⁻ ω, ⨆ t : C k, edist (X t ω) (X (chainingSequence C t k m) ω) ^ p ∂P
        ≤ M * c₁ * (∑ j ∈ Finset.range (k - m),
            (ε (m + j + 1) : ℝ≥0∞) ^ (-d / p) * (ε (m + j) : ℝ≥0∞) ^ (q / p)) ^ p := by
      have hlp : ∫⁻ ω, ⨆ t : C k, edist (X t ω) (X (chainingSequence C t k m) ω) ^ p ∂P
          ≤ (∑ i ∈ Finset.range (k - m), (∫⁻ ω, ⨆ t : C k,
              edist (X (chainingSequence C t k (m + i)) ω) (X (chainingSequence C t k (m + i + 1)) ω) ^ p ∂P) ^ (1 / p)) ^ p := by
        simp only [← (ENNReal.monotone_rpow_of_nonneg hp_pos.le).map_iSup_of_continuousAt
          ENNReal.continuous_rpow_const.continuousAt (by simp [hp_pos])]
        refine le_trans ?_ (ENNReal.monotone_rpow_of_nonneg hp_pos.le
          (ENNReal.lintegral_Lp_finsum_le (fun _ _ => AEMeasurable.iSup fun _ => hX.aemeasurable_edist) hp))
        dsimp only; rw [one_div, ENNReal.rpow_inv_rpow hp_pos.ne']
        refine lintegral_mono fun ω => ?_
        gcongr
        simp only [Finset.sum_apply]
        exact (iSup_mono fun t => edist_chainingSequence_le_sum_edist (X · ω) hm).trans (finset_iSup_sum_le _)
      refine hlp.trans ?_
      have hterm_le (i : ℕ) (hi : i ∈ Finset.range (k - m)) :
          (∫⁻ ω, ⨆ t : C k, edist (X (chainingSequence C t k (m + i)) ω)
              (X (chainingSequence C t k (m + i + 1)) ω) ^ p ∂P) ^ (1 / p) ≤
            (M : ℝ≥0∞) ^ (1 / p) * c₁ ^ (1 / p) *
              ((ε (m + i + 1) : ℝ≥0∞) ^ (-d / p) * (ε (m + i) : ℝ≥0∞) ^ (q / p)) := by
        have hs := lintegral_sup_succ hX hC hC_subset (by simp at hi; omega : m + i < k)
        have hc : (#(C (m + i + 1)) : ℝ≥0∞) ≤ c₁ * (ε (m + i + 1) : ℝ≥0∞) ^ (-d) := by
          rw [show (#(C (m + i + 1)) : ℝ≥0∞) = coveringNumber (ε (m + i + 1)) J from mod_cast hC_card _,
            ENNReal.rpow_neg, ← ENNReal.inv_rpow]
          exact h_cov.coveringNumber_le _ (hε_le _)
        refine (ENNReal.rpow_le_rpow (hs.trans (mul_le_mul' (mul_le_mul' hc le_rfl) le_rfl)) (by positivity)).trans_eq ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        rw [show -d * (1 / p) = -d / p by ring, show q * (1 / p) = q / p by ring]; ring
      refine (ENNReal.rpow_le_rpow (Finset.sum_le_sum hterm_le) hp_pos.le).trans_eq ?_
      rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ hp_pos.le,
        ENNReal.mul_rpow_of_nonneg _ _ hp_pos.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        one_div_mul_cancel hp_pos.ne', ENNReal.rpow_one, ENNReal.rpow_one, mul_assoc]
    refine h1.trans ?_
    have hα := div_pos hqd_pos hp_pos
    have hterm (j : ℕ) : (ε (m + j + 1) : ℝ≥0∞) ^ (-d / p) * (ε (m + j) : ℝ≥0∞) ^ (q / p) =
        2 ^ (d / p) * ((ε₀ : ℝ≥0∞) * 2⁻¹ ^ m) ^ ((q - d) / p) * ((2⁻¹ : ℝ≥0∞) ^ ((q - d) / p)) ^ j := by
      dsimp [ε]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_ofNat]
      have hadd := ENNReal.rpow_add_of_add_pos (x := (ε₀ : ℝ≥0∞) * 2⁻¹ ^ (m + j)) (y := -(d / p)) (z := q / p)
        (ENNReal.mul_ne_top hε' (by simp)) (by rw [show -(d / p) + q / p = (q - d) / p by ring]; exact hα)
      rw [pow_succ, ← mul_assoc, ENNReal.mul_rpow_of_ne_top (ENNReal.mul_ne_top hε' (by simp)) (by simp),
        ENNReal.inv_rpow, neg_div, ENNReal.rpow_neg 2, inv_inv, mul_right_comm _ (2 ^ (d / p)), ← hadd,
        show -(d / p) + q / p = (q - d) / p by ring, pow_add, ← mul_assoc,
        ENNReal.mul_rpow_of_nonneg _ _ hα.le,
        ← ENNReal.rpow_natCast_mul, ← ENNReal.rpow_mul_natCast, mul_comm (j : ℝ)]
      ring
    simp_rw [hterm, ← Finset.mul_sum]
    calc (M : ℝ≥0∞) * c₁ * (2 ^ (d / p) * ((ε₀ : ℝ≥0∞) * 2⁻¹ ^ m) ^ ((q - d) / p) *
            ∑ j ∈ Finset.range (k - m), ((2⁻¹ : ℝ≥0∞) ^ ((q - d) / p)) ^ j) ^ p
      _ ≤ M * c₁ * (2 ^ (d / p) * ((ε₀ : ℝ≥0∞) * 2⁻¹ ^ m) ^ ((q - d) / p) *
            (2 ^ ((q - d) / p) * (2 ^ ((q - d) / p) - 1)⁻¹)) ^ p := by
          gcongr; exact geom_sum_two_inv_le hα _
      _ = 2 ^ d * M * c₁ * (2 * (ε₀ : ℝ≥0∞) * 2⁻¹ ^ m) ^ (q - d) / (2 ^ ((q - d) / p) - 1) ^ p := by
          rw [div_eq_mul_inv (2 ^ d * M * c₁ * _),
            ENNReal.mul_rpow_of_nonneg _ _ hp_pos.le, ENNReal.mul_rpow_of_nonneg _ _ hp_pos.le,
            ENNReal.mul_rpow_of_nonneg _ _ hp_pos.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul, div_mul_cancel₀ _ hp_pos.ne', div_mul_cancel₀ _ hp_pos.ne',
            ENNReal.inv_rpow,
            ENNReal.mul_rpow_of_nonneg _ _ hqd_pos.le, ENNReal.mul_rpow_of_nonneg _ _ hqd_pos.le,
            ENNReal.mul_rpow_of_nonneg _ _ hqd_pos.le]
          ring

end SecondTerm

end DOZZ.Proofs
