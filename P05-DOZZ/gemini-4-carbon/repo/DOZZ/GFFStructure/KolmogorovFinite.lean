/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import DOZZ.GFFStructure.KolmogorovCover

/-!
# Finite-set Kolmogorov increment estimates
-/

@[expose] public section

open MeasureTheory _root_.ProbabilityTheory _root_.Metric _root_.Finset Filter
open scoped ENNReal NNReal Finset Topology

namespace DOZZ.Proofs

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E] {P : Measure Ω} {X : T → Ω → E}

section Together

variable {M : ℝ≥0} {d p q : ℝ} {J : Set T} {c : ℝ≥0∞} {δ : ℝ≥0}




theorem finite_set_bound_of_edist_le (hJ : HasBoundedCoveringNumber J c d)
    (hJ_finite : J.Finite) (hX : IsAEKolmogorovProcess X P p q M) (hc : c ≠ ∞)
    (hd_pos : 0 < d) (hdq_lt : d < q) (hδ : δ ≠ 0) :
    ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 2 ^ (2 * p + 4 * q + 1) * M * c * δ ^ (q - d)
        * (4 ^ d * (ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d))) ^ q
            + Cp d p q) := by
  have scale_change_lintegral_iSup {C : ℕ → Finset T} (δ : ℝ≥0∞) (m k : ℕ) : ∫⁻ ω, ⨆ (s : C k) (t : { t : C k // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P
        ≤ 2 ^ p * ∫⁻ ω, ⨆ (s : C k) (t : { t : C k // edist s t ≤ δ }),
            edist (X (chainingSequence C s k m) ω) (X (chainingSequence C t k m) ω) ^ p ∂P
          + 4 ^ p * ∫⁻ ω, ⨆ (s : C k), edist (X s ω) (X (chainingSequence C s k m) ω) ^ p ∂P := by
    rw [← lintegral_const_mul'' _ (AEMeasurable.iSup fun _ => AEMeasurable.iSup fun _ => hX.aemeasurable_edist.pow_const _),
      ← lintegral_const_mul'' _ (AEMeasurable.iSup fun _ => hX.aemeasurable_edist.pow_const _),
      ← lintegral_add_left' ((AEMeasurable.iSup fun _ => AEMeasurable.iSup fun _ => hX.aemeasurable_edist.pow_const _).const_mul _)]
    exact lintegral_mono fun ω => scale_change_rpow m (X · ω) _ _ hX.p_pos.le
  have exists_nat_pow_lt_iInf (hJ : Metric.ediam J < ∞) (hJ_fin : J.Finite) (hJ_ne : J.Nonempty) : ∃ k : ℕ, Metric.ediam J * 2⁻¹ ^ k < ⨅ (s : J) (t : J) (_ : 0 < edist s t), edist s t := by
    have hpos : 0 < ⨅ (s : J) (t : J) (_ : 0 < edist s t), edist s t := by
      rw [iInf_subtype]
      change 0 < ⨅ s ∈ J, ⨅ (t : J) (_ : 0 < edist s t), edist s t
      rw [DOZZ.Proofs.Set.Finite.lt_iInf_iff hJ_ne hJ_fin]
      intro s _
      rw [iInf_subtype]
      change 0 < ⨅ t ∈ J, ⨅ (_ : 0 < edist s t), edist s t
      rw [DOZZ.Proofs.Set.Finite.lt_iInf_iff hJ_ne hJ_fin]
      intro t _; by_cases hst : 0 < edist s t <;> simp [hst]
    have ht : Tendsto (fun n : ℕ => Metric.ediam J * 2⁻¹ ^ n) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_iff.mpr (by simp))
        (Or.inr hJ.ne)
    exact (ht.eventually_lt_const hpos).exists
  have lintegral_sup_cover_eq_of_lt_iInf_dist {C : Set T} {ε : ℝ≥0} (hJ : J.Finite) (hC : IsCover ε J C) (hC_subset : C ⊆ J) (hε_lt : ε < ⨅ (s : J) (t : J) (_ : 0 < edist s t), edist s t) : ∫⁻ ω, ⨆ (s : C) (t : { t : C // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P
        = ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P := by
    have h_le_iff {s t : T} (hs : s ∈ J) (ht : t ∈ J) : edist s t ≤ ε ↔ edist s t = 0 := by
      refine ⟨fun h => ?_, fun h => by simp [h]⟩
      by_contra hne
      have hp : 0 < edist s t := pos_iff_ne_zero.2 hne
      exact lt_irrefl (ε : ℝ≥0∞) (hε_lt.trans_le ((iInf_le _ ⟨s, hs⟩).trans
        ((iInf_le _ ⟨t, ht⟩).trans (by simp [hp, h]))))
    have hC0 : IsCover 0 J C := fun s hs => by
      obtain ⟨t, ht, hst⟩ := hC hs
      simp only [ENNReal.coe_zero, nonpos_iff_eq_zero, Set.mem_ofPred_eq] at hst ⊢
      exact ⟨t, ht, (h_le_iff hs (hC_subset ht)).1 hst⟩
    refine le_antisymm (lintegral_mono fun ω => iSup_le fun s => iSup_le fun t =>
      le_iSup_of_le ⟨s.1, hC_subset s.2⟩ (le_iSup_of_le ⟨⟨t.1, hC_subset t.1.2⟩, t.2⟩ le_rfl)) ?_
    choose f' hf'C hf'_ed using hC0
    simp only [ENNReal.coe_zero, nonpos_iff_eq_zero, Set.mem_ofPred_eq] at hf'_ed
    let f (s : J) : C := ⟨f' s.2, hf'C s.2⟩
    let g (s : J) (t : { t : J // edist s t ≤ δ }) : { t : C // edist (f s) t ≤ δ } :=
      ⟨⟨f' t.1.2, hf'C t.1.2⟩, (edist_triangle4 (f' s.2) s.1 t.1.1 (f' t.1.2)).trans
        (by rw [edist_comm (f' s.2) s.1, hf'_ed s.2, hf'_ed t.1.2, zero_add, add_zero]; exact t.2)⟩
    have h_ed (s : J) (t : { t : J // edist s t ≤ δ }) :
        ∀ᵐ ω ∂P, edist (X s ω) (X t ω) ≤ edist (X (f s) ω) (X (g s t) ω) := by
      filter_upwards [hX.edist_eq_zero (hf'_ed s.2), hX.edist_eq_zero (hf'_ed t.1.2)] with ω h₁ h₂
      refine (edist_triangle4 _ (X (f s) ω) (X (g s t) ω) _).trans ?_
      rw [edist_comm (X (g s t) ω), h₁, h₂]; simp
    have : Countable J := hJ.countable
    have (s : J) : Countable { t : J // edist s t ≤ δ } := Subtype.countable
    simp_rw [← ae_all_iff] at h_ed
    refine (lintegral_mono_ae (h_ed.mono fun ω h => by
      gcongr with s t; exacts [hX.p_pos.le, h s t])).trans
      (lintegral_mono fun ω => iSup_le fun s => iSup_le fun t =>
        le_iSup_of_le (f s) (le_iSup_of_le (g s t) le_rfl))
  have hq_pos : 0 < q := hd_pos.trans hdq_lt
  rcases isEmpty_or_nonempty J with hJ_empty | hJ_ne
  · simp
  have : Nonempty J := hJ_ne
  have hJ_nonempty : J.Nonempty := Set.nonempty_coe_sort.mp hJ_ne
  have hε' := hJ.ediam_lt_top
  let ε₀ := (Metric.ediam J).toNNReal
  rcases eq_zero_or_pos ε₀ with hε₀0 | hε₀_pos
  · simp only [ENNReal.toNNReal_eq_zero_iff, hε'.ne, or_false, ε₀] at hε₀0
    rw [DOZZ.Proofs.IsAEKolmogorovProcess.lintegral_sup_rpow_edist_eq_zero' hX hJ_finite.countable
      fun s t => le_antisymm ((Metric.edist_le_ediam_of_mem s.2 t.1.2).trans_eq hε₀0) zero_le]
    exact zero_le
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (ε₀ : ℝ≥0∞) * 2⁻¹ ^ k <
      ⨅ (s : J) (t : J) (_ : 0 < edist s t), edist s t := by
    simpa [ε₀, ENNReal.coe_toNNReal hε'.ne] using exists_nat_pow_lt_iInf hε' hJ_finite hJ_nonempty
  have hcov_fin (n : ℕ) := DOZZ.Proofs.TotallyBounded.coveringNumber_ne_top hJ_finite.totallyBounded
    (by positivity : 0 < ε₀ * 2⁻¹ ^ n).ne'
  let C (n : ℕ) : Finset T := (finite_minimalCover (ε := ε₀ * 2⁻¹ ^ n) (A := J)).toFinset
  have hC_subset (n : ℕ) : (C n : Set T) ⊆ J := by simpa [C] using minimalCover_subset
  have hC_card (n : ℕ) : #(C n) = coveringNumber (ε₀ * 2⁻¹ ^ n) J := by
    rw [← encard_minimalCover (hcov_fin n)]; simp [C, ← Set.Finite.encard_eq_coe_toFinset_card]
  have hC (n : ℕ) : IsCover (ε₀ * 2⁻¹ ^ n) J (C n) := by simpa [C] using isCover_minimalCover (hcov_fin n)
  rw [← lintegral_sup_cover_eq_of_lt_iInf_dist hJ_finite (hC k) (hC_subset k)
    (by simpa [ENNReal.inv_pow] using hk)]
  have h2pow_le : (4 : ℝ≥0∞) ^ p * 2 ^ q ≤ 2 ^ (2 * p + 4 * q + 1) := by
    rw [show (4 : ℝ≥0∞) = 2 ^ (2 : ℝ) by norm_num, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add _ _ (by norm_num) (by simp)]
    exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hX.p_pos])
  by_cases hδ_le : δ / 4 ≤ Metric.ediam J
  · rcases lt_or_ge δ (ε₀ * 2⁻¹ ^ k) with hδ_lt | hδ_ge
    · rw [DOZZ.Proofs.IsAEKolmogorovProcess.lintegral_sup_rpow_edist_eq_zero' hX
        (hJ_finite.subset (hC_subset k)).countable fun s t => by
          by_contra hne
          have hpos : 0 < edist s t := pos_iff_ne_zero.2 hne
          have hlt : (δ : ℝ≥0∞) < (ε₀ : ℝ≥0∞) * 2⁻¹ ^ k := by
            simpa [ENNReal.inv_pow] using (mod_cast hδ_lt : (δ : ℝ≥0∞) < ((ε₀ * 2⁻¹ ^ k : ℝ≥0) : ℝ≥0∞))
          exact not_le.2 ((hlt.trans hk).trans_le ((iInf_le _ ⟨s, hC_subset k s.2⟩).trans
            ((iInf_le _ ⟨t.1, hC_subset k t.1.2⟩).trans (iInf_le _ hpos)))) t.2]
      exact zero_le
    have hδ_le_mul : δ ≤ ε₀ * 4 := by
      rw [← ENNReal.coe_toNNReal hε'.ne, ENNReal.div_le_iff (by simp) (by simp)] at hδ_le
      exact_mod_cast hδ_le
    let L := Real.logb 2⁻¹ (δ / (ε₀ * 4))
    have hL_nn : 0 ≤ L := Real.logb_nonneg_of_base_lt_one (by simp) (by norm_num) (by positivity)
      (by norm_cast; rw [div_le_one (by positivity)]; exact hδ_le_mul)
    have hδ_eq : δ = ε₀ * 4 * 2⁻¹ ^ L := by
      symm; ext; simp only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_rpow, NNReal.coe_inv]
      rw [mul_assoc, Real.rpow_logb (by simp) (by simp) (by positivity)]; field
    let m := min k ⌊L⌋₊
    have hmk : m ≤ k := min_le_left _ _
    have hmδ : ε₀ * 2⁻¹ ^ m ≤ δ := by
      rcases le_total k ⌊L⌋₊ with hkl | hkl
      · simpa [m, min_eq_left hkl] using hδ_ge
      · rw [show m = ⌊L⌋₊ from min_eq_right hkl]
        calc ε₀ * 2⁻¹ ^ ⌊L⌋₊ = ε₀ * 4 * 2⁻¹ ^ ((⌊L⌋₊ : ℝ) + 2) := by
              rw [mul_assoc]; congr 1; rw [NNReal.rpow_add (by simp), mul_comm 4, mul_assoc]; norm_num
          _ ≤ ε₀ * 4 * 2⁻¹ ^ L := by
              gcongr _ * ?_
              exact NNReal.rpow_le_rpow_of_exponent_ge (by simp) (by simp)
                (by linarith [Nat.lt_floor_add_one L])
          _ = δ := hδ_eq.symm
    have hmδ₂ : δ ≤ ε₀ * 4 * 2⁻¹ ^ m := by
      calc δ = ε₀ * 4 * 2⁻¹ ^ L := hδ_eq
        _ ≤ ε₀ * 4 * 2⁻¹ ^ (⌊L⌋₊ : ℝ) := by
            gcongr _ * ?_; exact NNReal.rpow_le_rpow_of_exponent_ge (by simp) (by simp) (Nat.floor_le hL_nn)
        _ = ε₀ * 4 * 2⁻¹ ^ ⌊L⌋₊ := by simp
        _ ≤ ε₀ * 4 * 2⁻¹ ^ m := by
            gcongr _ * ?_; exact pow_le_pow_right_of_le_one' (by simp) (min_le_right _ _)
    refine (scale_change_lintegral_iSup δ m k).trans ?_
    rw [mul_add]
    refine add_le_add ?_ ?_
    · refine (mul_le_mul' le_rfl (lintegral_sup_rpow_edist_cover_rescale hX hJ_finite hC hC_subset hC_card
        (pos_iff_ne_zero.2 hδ) hδ_le_mul hmδ hmδ₂ hmk)).trans ?_
      have h2eq : (2 : ℝ≥0∞) ^ p * 2 ^ (p + 1) * M * 16 ^ q = 2 ^ (2 * p + 4 * q + 1) * M := by
        rw [show (16 : ℝ≥0∞) = 2 ^ (4 : ℝ) by norm_num, ← ENNReal.rpow_mul,
          mul_right_comm _ (M : ℝ≥0∞), ← ENNReal.rpow_add _ _ (by simp) (by simp),
          ← ENNReal.rpow_add _ _ (by simp) (by simp)]
        congr 2; ring
      have hcov_bd : coveringNumber (δ / 4) J ≤ c * 4 ^ d * (δ : ℝ≥0∞)⁻¹ ^ d := by
        refine (hJ.coveringNumber_le (δ / 4) (by simpa)).trans_eq ?_
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_ofNat]
        rw [ENNReal.inv_div (Or.inr (by simp)) (Or.inr (mod_cast hδ)),
          ENNReal.div_rpow_of_nonneg _ _ hd_pos.le, div_eq_mul_inv, ENNReal.inv_rpow]; ring
      have hlog_bd : (Nat.log2 (coveringNumber (δ / 4) J).toNat : ℝ≥0∞) ≤
          ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d)) := by
        by_cases h0 : Nat.log2 (coveringNumber (δ / 4) J).toNat = 0
        · simp [h0]
        refine (ENNReal.natCast_le_ofReal h0).2 ((Real.log2_le_logb _).trans ?_)
        have hnt : coveringNumber (δ / 4) J ≠ ⊤ := (hJ.coveringNumber_lt_top (by simp [hδ]) hc hd_pos.le).ne
        refine Real.logb_le_logb_of_le (by norm_num) (by
          by_contra hle; simp only [Nat.cast_pos, not_lt, nonpos_iff_eq_zero, ENat.toNat_eq_zero, hnt, or_false] at hle
          simp [hle] at h0) ?_
        have htr : c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d = (c * 4 ^ d * (δ : ℝ≥0∞)⁻¹ ^ d).toReal := by
          simp [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
        rw [htr, ← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (by finiteness)]
        exact (le_of_eq (by norm_cast; simp [hnt])).trans hcov_bd
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq_pos.le, ENNReal.mul_rpow_of_nonneg _ _ hq_pos.le]
      calc 2 ^ p * (2 ^ (p + 1) * (M : ℝ≥0∞) * ((16 ^ q * (δ : ℝ≥0∞) ^ q) *
              (Nat.log2 (coveringNumber (δ / 4) J).toNat : ℝ≥0∞) ^ q) * coveringNumber (δ / 4) J)
        _ = (2 ^ p * 2 ^ (p + 1) * M * 16 ^ q) * (δ : ℝ≥0∞) ^ (q - d) *
            ((δ : ℝ≥0∞) ^ d * (Nat.log2 (coveringNumber (δ / 4) J).toNat : ℝ≥0∞) ^ q * coveringNumber (δ / 4) J) := by
            rw [show (δ : ℝ≥0∞) ^ q = (δ : ℝ≥0∞) ^ (q - d) * (δ : ℝ≥0∞) ^ d by
              rw [← ENNReal.rpow_add _ _ (mod_cast hδ) (by simp)]; ring_nf]; ring
        _ ≤ (2 ^ (2 * p + 4 * q + 1) * M) * (δ : ℝ≥0∞) ^ (q - d) *
            ((δ : ℝ≥0∞) ^ d * (ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d))) ^ q *
              (c * 4 ^ d * (δ : ℝ≥0∞)⁻¹ ^ d)) := by rw [h2eq]; gcongr
        _ = 2 ^ (2 * p + 4 * q + 1) * M * c * (δ : ℝ≥0∞) ^ (q - d) *
            (4 ^ d * (ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d))) ^ q) := by
            have hcancel : (δ : ℝ≥0∞) ^ d * (δ : ℝ≥0∞)⁻¹ ^ d = 1 := by
              rw [← ENNReal.mul_rpow_of_nonneg _ _ hd_pos.le, ENNReal.mul_inv_cancel (mod_cast hδ) (by simp), ENNReal.one_rpow]
            calc _ = 2 ^ (2 * p + 4 * q + 1) * M * c * (δ : ℝ≥0∞) ^ (q - d) *
                  (4 ^ d * (ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d))) ^ q) *
                  ((δ : ℝ≥0∞) ^ d * (δ : ℝ≥0∞)⁻¹ ^ d) := by ring
              _ = _ := by rw [hcancel, mul_one]
    · refine (mul_le_mul' le_rfl (second_term_bound hX (by simp [ε₀, ENNReal.coe_toNNReal hε'.ne])
        hC hC_subset hC_card hdq_lt hJ hmk)).trans ?_
      have : (ε₀ : ℝ≥0∞) * 2⁻¹ ^ m ≤ δ := by
        simpa [ENNReal.inv_pow] using (mod_cast hmδ : ((ε₀ * 2⁻¹ ^ m : ℝ≥0) : ℝ≥0∞) ≤ δ)
      have h2m : (2 * (ε₀ : ℝ≥0∞) * 2⁻¹ ^ m) ^ (q - d) ≤ 2 ^ (q - d) * (δ : ℝ≥0∞) ^ (q - d) := by
        have hqd_nn := sub_nonneg.2 hdq_lt.le
        rw [mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ hqd_nn]; gcongr
      calc (4 : ℝ≥0∞) ^ p * (2 ^ d * M * c * (2 * (ε₀ : ℝ≥0∞) * 2⁻¹ ^ m) ^ (q - d) * Cp d p q)
        _ ≤ 4 ^ p * (2 ^ d * M * c * (2 ^ (q - d) * (δ : ℝ≥0∞) ^ (q - d)) * Cp d p q) := by gcongr
        _ = (4 ^ p * (2 ^ d * 2 ^ (q - d))) * M * c * (δ : ℝ≥0∞) ^ (q - d) * Cp d p q := by ring
        _ = (4 ^ p * 2 ^ q) * M * c * (δ : ℝ≥0∞) ^ (q - d) * Cp d p q := by
            rw [← ENNReal.rpow_add _ _ (by simp) (by simp), add_sub_cancel]
        _ ≤ 2 ^ (2 * p + 4 * q + 1) * M * c * (δ : ℝ≥0∞) ^ (q - d) * Cp d p q := by gcongr
  · have hdiam_le : Metric.ediam J ≤ δ := (not_le.mp hδ_le).le.trans
      (by rw [ENNReal.div_le_iff (by simp) (by simp)]; exact le_mul_of_one_le_right zero_le (by norm_num))
    refine (scale_change_lintegral_iSup δ 0 k).trans ?_
    have hC0 : #(C 0) ≤ 1 := by
      suffices (#(C 0) : ℕ∞) = 1 by norm_cast at this; simp [this]
      simpa [hC_card 0, ε₀] using coveringNumber_eq_one_of_ediam_le hJ_nonempty
        (by rw [ENNReal.coe_toNNReal hε'.ne])
    have hfirst : ∫⁻ ω, ⨆ (s : C k) (t : { t : C k // edist s t ≤ δ }),
        edist (X (chainingSequence C s k 0) ω) (X (chainingSequence C t k 0) ω) ^ p ∂P = 0 :=
      (lintegral_eq_zero_iff' (AEMeasurable.iSup fun _ => AEMeasurable.iSup fun _ =>
        hX.aemeasurable_edist.pow_const _)).2 (ae_of_all _ fun ω => by
          simp only [Pi.zero_apply, ENNReal.iSup_eq_zero, ENNReal.rpow_eq_zero_iff]
          intro s t
          rw [Finset.card_le_one_iff.1 hC0 (chainingSequence_mem hC hJ_nonempty s.2 0 zero_le)
            (chainingSequence_mem hC hJ_nonempty t.1.2 0 zero_le)]
          simp [hX.p_pos])
    rw [hfirst, mul_zero, zero_add]
    refine (mul_le_mul' le_rfl (second_term_bound hX (by simp [ε₀, ENNReal.coe_toNNReal hε'.ne])
      hC hC_subset hC_card hdq_lt hJ zero_le)).trans ?_
    simp only [pow_zero, mul_one, ε₀, ENNReal.coe_toNNReal hε'.ne]
    have h2d : (2 * Metric.ediam J) ^ (q - d) ≤ 2 ^ (q - d) * (δ : ℝ≥0∞) ^ (q - d) := by
      have hqd_nn := sub_nonneg.2 hdq_lt.le
      rw [ENNReal.mul_rpow_of_nonneg _ _ hqd_nn]; gcongr
    calc (4 : ℝ≥0∞) ^ p * (2 ^ d * M * c * (2 * Metric.ediam J) ^ (q - d) * Cp d p q)
      _ ≤ 4 ^ p * (2 ^ d * M * c * (2 ^ (q - d) * (δ : ℝ≥0∞) ^ (q - d)) * Cp d p q) := by gcongr
      _ = (4 ^ p * 2 ^ q) * M * c * (δ : ℝ≥0∞) ^ (q - d) * Cp d p q := by
          rw [show (2 : ℝ≥0∞) ^ q = 2 ^ d * 2 ^ (q - d) by
            rw [← ENNReal.rpow_add _ _ (by simp) (by simp), add_sub_cancel]]; ring
      _ ≤ 2 ^ (2 * p + 4 * q + 1) * M * c * (δ : ℝ≥0∞) ^ (q - d) * Cp d p q := by gcongr
      _ ≤ _ := by rw [mul_add]; exact le_add_self

end Together

end DOZZ.Proofs
