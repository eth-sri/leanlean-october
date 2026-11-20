/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.WeightedCutoffCompact
public import DOZZ.Statements.GMC.CoulombMass
import DOZZ.GMC.SharpMoments.SeibergUniform

/-! Uniform bounds on compact Coulomb configurations. -/

@[expose] public section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace DOZZ.Proofs

private theorem exists_nonneg_bound {α : Type*} [TopologicalSpace α] {S : Set α}
    (hS : IsCompact S) {f : α → ℝ} (hf : ContinuousOn f S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, f p ≤ C := by
  obtain ⟨C, hC⟩ := (hS.image_of_continuousOn hf).bddAbove
  exact ⟨max C 0, le_max_right .., fun p hp => (hC (mem_image_of_mem f hp)).trans (le_max_left ..)⟩

/-- On compact sets both the size of the roots and the absolute Coulomb exponents are bounded. -/
theorem compact_coulomb_bounds {N : ℕ} {S : Set (CoulombParameters N)} (hS : IsCompact S) :
    ∃ Z E : ℝ, 0 ≤ Z ∧ 0 ≤ E ∧ (∀ c ∈ S, ∑ j, ‖c.2.1 j‖ ≤ Z) ∧
      (∀ c ∈ S, ∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2| ≤ E) ∧
      (∀ c ∈ S, ∀ j, |c.1 * c.2.2.1 j| ≤ E) ∧ (∀ c ∈ S, |c.1 * c.2.2.2| ≤ E) := by
  obtain ⟨Z, hZ, hz⟩ := exists_nonneg_bound hS (f := fun c => ∑ j, ‖c.2.1 j‖) (by fun_prop)
  obtain ⟨E, hE, he⟩ := exists_nonneg_bound hS
    (f := fun c => ∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2|) (by fun_prop)
  refine ⟨Z, E, hZ, hE, hz, he, fun c hc j => ?_, fun c hc => ?_⟩
  · exact (Finset.single_le_sum (fun j _ => abs_nonneg (c.1 * c.2.2.1 j)) (Finset.mem_univ j)).trans
      ((le_add_of_nonneg_right (abs_nonneg _)).trans (he c hc))
  · exact (le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => abs_nonneg (c.1 * c.2.2.1 j))).trans (he c hc)

/-- The bounds on couplings, charges and separation common to compact cutoff estimates. -/
abbrev CoulombCutoffConfiguration {N : ℕ} (c : CoulombParameters N) : Prop :=
  0 < c.1 ∧ c.1 < 2 ∧ Function.Injective c.2.1 ∧
  (∀ k, c.2.2.1 k < Q c.1) ∧ c.2.2.2 < Q c.1

/-- Compactness leaves room to increase a moment order above its positive part while preserving
all cutoff bounds. The same neighborhood size can be used for root separation. -/
theorem exists_cutoffUI_slack {N : ℕ} {S : Set (CoulombParameters N)} {s : CoulombParameters N → ℝ}
    (hS : IsCompact S) (hs : ContinuousOn s S) (hc : ∀ c ∈ S, CoulombCutoffConfiguration c)
    (h4 : ∀ c ∈ S, s c < 4 / c.1 ^ 2)
    (hr : ∀ c ∈ S, ∀ k, s c < 2 / c.1 * (Q c.1 - c.2.2.1 k))
    (hi : ∀ c ∈ S, s c < 2 / c.1 * (Q c.1 - c.2.2.2)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      (∀ c ∈ S, ∀ t, 0 < t → t < max (s c) 0 + ε →
        (∀ k, 0 < weightedCutoffSlack (c.1, c.2.2.1 k, t)) ∧
        (∀ k, 0 < weightedCutoffSlack (c.1, max (c.2.2.1 k) 0, t)) ∧
        0 < weightedCutoffSlack (c.1, max c.2.2.2 0, t)) ∧
      ∀ c ∈ S, ∀ j k, j ≠ k → 2 * ε ≤ ‖c.2.1 j - c.2.1 k‖ := by
  have hU (c : CoulombParameters N) (hc' : c ∈ S) : 0 < c.1 := (hc c hc').1
  have hQ (c : CoulombParameters N) (hc' : c ∈ S) : 0 < Q c.1 := by
    have := hU c hc'
    unfold Q
    positivity
  have hslack {f : CoulombParameters N → ℝ} (hf : ContinuousOn f S)
      (hf0 : ∀ c ∈ S, 0 < f c) (hfs : ∀ c ∈ S, s c < f c) :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ c ∈ S, max (s c) 0 + ε ≤ f c := by
    filter_upwards [eventually_le_of_isCompact_of_pos hS (hf.sub (hs.sup continuousOn_const))
      (fun c hc' => sub_pos.mpr (max_lt (hfs c hc') (hf0 c hc')))] with ε hε c hc'
    have h := hε c hc'
    change ε ≤ f c - max (s c) 0 at h
    linarith only [h]
  have efour := hslack (f := fun c => 4 / c.1 ^ 2) (by
    intro c hc'
    have := hU c hc'
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)) (fun c hc' => by have := hU c hc'; positivity) h4
  have echarge (a : CoulombParameters N → ℝ) (ha : Continuous a) (haQ : ∀ c ∈ S, a c < Q c.1)
      (hs' : ∀ c ∈ S, s c < 2 / c.1 * (Q c.1 - a c)) :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ c ∈ S, max (s c) 0 + ε ≤ 2 / c.1 * (Q c.1 - max (a c) 0) := by
    apply hslack
    · intro c hc'
      have := hU c hc'
      apply ContinuousAt.continuousWithinAt
      unfold Q
      fun_prop (disch := positivity)
    · intro c hc'
      exact mul_pos (div_pos two_pos (hU c hc')) (sub_pos.mpr (max_lt (haQ c hc') (hQ c hc')))
    · intro c hc'
      rcases le_total (a c) 0 with h | h
      · rw [max_eq_right h, sub_zero]
        refine (h4 c hc').trans ?_
        have hg := hU c hc'
        unfold Q
        field_simp
        linarith only [sq_pos_of_pos hg]
      · simpa [max_eq_left h] using hs' c hc'
  have eroot := eventually_all.mpr fun k => echarge (fun c => c.2.2.1 k) (by fun_prop)
    (fun c hc' => (hc c hc').2.2.2.1 k) (fun c hc' => hr c hc' k)
  have einf := echarge (fun c => c.2.2.2) (by fun_prop) (fun c hc' => (hc c hc').2.2.2.2) hi
  have eseparate (j k : Fin N) : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ c ∈ S, j ≠ k → 2 * ε ≤ ‖c.2.1 j - c.2.1 k‖ := by
    by_cases hjk : j = k
    · exact Eventually.of_forall fun _ _ _ h => (h hjk).elim
    filter_upwards [eventually_le_of_isCompact_of_pos hS
      (f := fun c => ‖c.2.1 j - c.2.1 k‖ / 2) (by fun_prop)
      (fun c hc' => half_pos (norm_pos_iff.mpr (sub_ne_zero.mpr ((hc c hc').2.2.1.ne hjk))))]
      with ε hε c hc' _
    linarith only [hε c hc']
  obtain ⟨ε, hε4, hεr, hεi, hεs, hε0, hε1⟩ := (efour.and (eroot.and (einf.and
    ((eventually_all.mpr fun j => eventually_all.mpr (eseparate j)).and
      (Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)))))).exists
  refine ⟨ε, hε0, hε1.le, ?_, fun c hc' j k => hεs j k c hc'⟩
  intro c hc' t ht htε
  have hb {a : ℝ} (ha : a < Q c.1) (hle : max (s c) 0 + ε ≤ 2 / c.1 * (Q c.1 - a)) :
      0 < weightedCutoffSlack (c.1, a, t) :=
    (weightedCutoffSlack_pos_iff _).mpr ⟨hU c hc', (hc c hc').2.1, ha, ht,
      lt_min (htε.trans_le (hε4 c hc')) (htε.trans_le hle)⟩
  exact ⟨fun k => hb ((hc c hc').2.2.2.1 k) ((hεr k c hc').trans (mul_le_mul_of_nonneg_left (sub_le_sub_left (le_max_left _ _) _) (by have := hU c hc'; positivity))),
    fun k => hb (max_lt ((hc c hc').2.2.2.1 k) (hQ c hc')) (hεr k c hc'),
    hb (max_lt (hc c hc').2.2.2.2 (hQ c hc')) (hεi c hc')⟩

private theorem cutoff_root_scale_pos {g a t : ℝ} (h : 0 < weightedCutoffSlack (g, a, t)) :
    0 < weightedCutoffMomentScaleExponent g a t := by
  obtain ⟨hg, _, _, ht, hb⟩ := (weightedCutoffSlack_pos_iff _).mp h
  have hi := (lt_min_iff.mp hb).2
  rw [show 2 / g * (Q g - a) = (2 * (Q g - a)) / g by ring, lt_div_iff₀ hg] at hi
  have hpos := mul_pos (mul_pos hg ht) (show 0 < Q g - a - g * t / 2 by linarith)
  unfold weightedCutoffMomentScaleExponent
  convert hpos using 1 <;> ring

/-- The exponent for decay of the weighted exterior moment. -/
noncomputable def cutoffExteriorDecay (g a t : ℝ) : ℝ :=
  2 * t + g ^ 2 * t / 2 - g ^ 2 * t ^ 2 / 2 - max (g * a) 0 * t

private theorem gamma_mul_Q {g : ℝ} (hg : g ≠ 0) : g * Q g = 2 + g ^ 2 / 2 := by
  unfold Q
  field_simp

private theorem cutoff_exterior_decay_pos {g a t : ℝ}
    (h : 0 < weightedCutoffSlack (g, max a 0, t)) : 0 < cutoffExteriorDecay g a t := by
  have hg  := ((weightedCutoffSlack_pos_iff _).mp h).1
  have he := cutoff_root_scale_pos h
  have hmax : max (g * a) 0 = g * max a 0 := by rw [mul_max_of_nonneg _ _ hg.le, mul_zero]
  unfold cutoffExteriorDecay
  rw [hmax]
  have hq := gamma_mul_Q hg.ne'
  unfold weightedCutoffMomentScaleExponent at he
  nlinarith only [he, congrArg (fun x => x * t) hq]

/-- The local decay exponents have a common positive lower bound over the compact set. -/
theorem cutoffUI_eventually_root_decay {N : ℕ} {S : Set (CoulombParameters N)} (hS : IsCompact S)
    (a : CoulombParameters N → ℝ) (ha : ContinuousOn a S) (t : ℝ)
    (h : ∀ c ∈ S, 0 < weightedCutoffSlack (c.1, a c, t)) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∀ c ∈ S, κ ≤ weightedCutoffMomentScaleExponent c.1 (a c) t := by
  apply eventually_le_of_isCompact_of_pos hS _ (fun c hc => cutoff_root_scale_pos (h c hc))
  intro c hc
  have hg := ((weightedCutoffSlack_pos_iff _).mp (h c hc)).1.ne'
  have hQ : ContinuousAt (fun d : CoulombParameters N => Q d.1) c := by
    unfold Q
    fun_prop (disch := exact hg)
  have hf : ContinuousWithinAt (fun d : CoulombParameters N => d.1) S c :=
    continuous_fst.continuousWithinAt
  exact ((hf.mul (hQ.continuousWithinAt.sub (ha c hc))).mul_const t).sub
    (((hf.pow 2).mul_const (t ^ 2)).div_const 2)

/-- The positive exterior decay is uniform, even for a varying continuous moment order. -/
theorem cutoffUI_eventually_exterior_decay {N : ℕ} {S : Set (CoulombParameters N)} (hS : IsCompact S)
    (t : CoulombParameters N → ℝ) (ht : ContinuousOn t S)
    (h : ∀ c ∈ S, 0 < weightedCutoffSlack (c.1, max c.2.2.2 0, t c)) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∀ c ∈ S, κ ≤ cutoffExteriorDecay c.1 c.2.2.2 (t c) := by
  apply eventually_le_of_isCompact_of_pos hS _ (fun c hc => cutoff_exterior_decay_pos (h c hc))
  unfold cutoffExteriorDecay
  fun_prop

/-- Uniform weighted moment bounds at any of the finite roots. The charge `a` can be either the
bare root charge or its positive part. -/
theorem cutoffUI_root_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    {N : ℕ} {S : Set (CoulombParameters N)} (hS : IsCompact S)
    (a t : CoulombParameters N → ℝ) (ha : ContinuousOn a S) (ht : ContinuousOn t S)
    (h : ∀ c ∈ S, 0 < weightedCutoffSlack (c.1, a c, t c)) (j : Fin N) {Z : ℝ}
    (hZ : ∀ c ∈ S, ∑ j, ‖c.2.1 j‖ ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ c ∈ S, ∀ δ R : ℝ, 0 < δ → δ ≤ R → R ≤ 1 →
      (∫⁻ ω, cutoffWeightedGmcBallMass P Xc c.1 (a c) (c.2.1 j) R δ ω ^ (t c) ∂P) ≤
        ENNReal.ofReal (C * R ^ weightedCutoffMomentScaleExponent c.1 (a c) (t c)) := by
  let f  := fun c => (c.1, a c, t c)
  have hf  := continuous_fst.continuousOn.prodMk (ha.prodMk ht)
  obtain ⟨C, hC, hb⟩ := weightedCutoff_bound_uniform_compact P X hX Xc hXc _
    (hS.image_of_continuousOn hf) (by rintro _ ⟨c, hc, rfl⟩; exact h c hc)
    (closedBall 0 Z) (isCompact_closedBall ..) 1 one_pos
  refine ⟨C, hC, fun c hc δ R hδ hδR hR => hb (f c) ⟨c, hc, rfl⟩ _ ?_ δ R hδ hδR hR⟩
  rw [mem_closedBall, dist_zero_right]
  exact (Finset.single_le_sum (fun j _ => norm_nonneg (c.2.1 j)) (Finset.mem_univ j)).trans (hZ c hc)

/-- A cutoff weighted mass with zero charge is a cutoff disk mass. -/
theorem cutoffWeightedGmcBallMass_zero_charge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (γ : ℝ) (z : ℂ) (R r : ℝ) (ω : Ω) :
    cutoffWeightedGmcBallMass P Xc γ 0 z R (Real.exp (-r)) ω =
      regularizedGMC P Xc γ r ω (Metric.ball z R) := by
  have hlog : Real.log (1 / Real.exp (-r)) = r := by
    simp
  rw [cutoffWeightedGmcBallMass, hlog]
  simp

/-- From an admissible nonnegative charge, get the cutoff estimate on every disk about the
origin with radius between 1 and `Rmax`. -/
theorem cutoffUI_disk_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    {N : ℕ} {S : Set (CoulombParameters N)} (hS : IsCompact S)
    (t : CoulombParameters N → ℝ) (ht : ContinuousOn t S)
    (h : ∀ c ∈ S, 0 < weightedCutoffSlack (c.1, max c.2.2.2 0, t c))
    {T Rmax : ℝ} (hT : 0 ≤ T) (hle : ∀ c ∈ S, t c ≤ T) (hRmax : 1 ≤ Rmax) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ c ∈ S, ∀ R : ℝ, 1 ≤ R → R ≤ Rmax → ∀ r : ℝ, 0 ≤ r →
      (∫⁻ ω, regularizedGMC P Xc c.1 r ω (ball 0 R) ^ t c ∂P) ≤ K := by
  let f : CoulombParameters N → ℝ × ℝ × ℝ := fun c => (c.1, 0, t c)
  have hf : ContinuousOn f S := continuous_fst.continuousOn.prodMk (continuousOn_const.prodMk ht)
  have ha : ∀ p ∈ f '' S, 0 < weightedCutoffSlack p := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨hg, hg2, ha, ht0, hb⟩ := (weightedCutoffSlack_pos_iff _).mp (h c hc)
    have h0 := le_max_right c.2.2.2 0
    refine (weightedCutoffSlack_pos_iff _).mpr ⟨hg, hg2, h0.trans_lt ha, ht0, ?_⟩
    exact hb.trans_le (min_le_min le_rfl (mul_le_mul_of_nonneg_left (by linarith) (by positivity)))
  obtain ⟨C, hC, hb⟩ := weightedCutoff_bound_uniform_compact P X hX Xc hXc _
    (hS.image_of_continuousOn hf) ha (closedBall 0 0) (isCompact_closedBall ..) Rmax (by linarith)
  refine ⟨ENNReal.ofReal (C * Rmax ^ (4 * T)), ENNReal.ofReal_lt_top, fun c hc R hR hR' r hr => ?_⟩
  have hi := hb (f c) ⟨c, hc, rfl⟩ 0 (mem_closedBall_self le_rfl) (Real.exp (-r)) R
    (Real.exp_pos _) ((Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)).trans hR) hR'
  change (∫⁻ ω, cutoffWeightedGmcBallMass P Xc c.1 0 0 R (Real.exp (-r)) ω ^ t c ∂P) ≤ _ at hi
  rw [show (fun ω => cutoffWeightedGmcBallMass P Xc c.1 0 0 R (Real.exp (-r)) ω ^ t c) =
    (fun ω => regularizedGMC P Xc c.1 r ω (ball 0 R) ^ t c) by
      funext ω; rw [cutoffWeightedGmcBallMass_zero_charge]] at hi
  obtain ⟨hg, hg2, _, htc, _⟩ := (weightedCutoffSlack_pos_iff _).mp (h c hc)
  have hxp : c.1 * (Q c.1 - 0) * t c - c.1 ^ 2 * t c ^ 2 / 2 ≤ 4 * T := by
    rw [sub_zero, gamma_mul_Q hg.ne']
    have hγsq := pow_lt_pow_left₀ hg2 hg.le two_ne_zero
    nlinarith only [mul_lt_mul_of_pos_right hγsq htc, sq_nonneg (c.1 * t c), hle c hc]
  refine hi.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC.le))
  exact (Real.rpow_le_rpow_of_exponent_le hR hxp).trans
    (Real.rpow_le_rpow (by linarith) hR' (by positivity))

end DOZZ.Proofs
