module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.TruncatedLogarithmicPolynomials
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.EulerIntegrationByParts

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped Classical ContDiff
open MeasureTheory Filter Topology

namespace DedekindZetaZeroFree.LargeSieve.Vendor

section

variable (f : ℝ → ℂ) (P : Polynomial ℂ)

def logMellinRemainder (x : ℝ) : ℂ :=
  f x - truncatedLogPolynomial P x

def logMellinHolomorphicPart (s : ℂ) : ℂ :=
  mellin (logMellinRemainder f P) s

def logMellinContinuation (s : ℂ) : ℂ :=
  logMellinHolomorphicPart f P s + logPrincipalPart P s

end

section Helpers

private lemma continuousOn_eval_log_polynomial (P : Polynomial ℂ) :
    ContinuousOn (fun x : ℝ => Polynomial.eval (Real.log x : ℂ) P) (Set.Ioi 0) := by
  exact (Polynomial.continuous P).comp_continuousOn (Complex.continuous_ofReal.comp_continuousOn
    (Real.continuousOn_log.mono fun x hx => ne_of_gt hx))

private lemma locallyIntegrableOn_truncatedLogPolynomial (P : Polynomial ℂ) :
    LocallyIntegrableOn (truncatedLogPolynomial P) (Set.Ioi 0) := by
  have heq : truncatedLogPolynomial P = Set.indicator (Set.Ioo (0 : ℝ) 1)
      (fun x : ℝ => Polynomial.eval (Real.log x : ℂ) P) := by
    funext x
    simp only [truncatedLogPolynomial, Set.indicator, Set.mem_Ioo]
  rw [heq, locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro k hk hkcomp
  exact (((continuousOn_eval_log_polynomial P).mono hk).integrableOn_compact hkcomp).indicator measurableSet_Ioo

section

variable {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} (h : LogMellinPhysical f δ P)

include h in
private lemma logMellinRemainder_isBigO_origin :
    logMellinRemainder f P =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ δ) := by
  obtain ⟨C, hC0, hC⟩ := h.origin_remainder 0
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))] with x hx0 hx1
  have hx : logMellinRemainder f P x = f x - Polynomial.eval (Real.log x : ℂ) P := by
    simp only [logMellinRemainder, truncatedLogPolynomial, Set.mem_Ioo]
    rw [if_pos ⟨hx0, hx1⟩]
  rw [hx, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le δ)]
  exact hC x hx0 hx1.le

include h in
private lemma logMellinRemainder_isBigO_top (a : ℝ) :
    logMellinRemainder f P =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  obtain ⟨C, hC0, hC⟩ := h.rapid_decay 0 (Nat.ceil a + 1)
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hzero : truncatedLogPolynomial P x = 0 := by
    simp only [truncatedLogPolynomial, Set.mem_Ioo]
    rw [if_neg (by push Not; intro h1; linarith)]
  rw [logMellinRemainder, hzero, sub_zero,
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)]
  refine le_trans (hC x hx) (mul_le_mul_of_nonneg_left ?_ hC0)
  refine Real.rpow_le_rpow_of_exponent_le hx ?_
  push_cast
  have := Nat.le_ceil a
  linarith

end

section

variable {δ : ℝ} (hδ : 0 < δ)

include hδ in
private lemma punctured_halfPlane_preconnected :
    IsPreconnected {s : ℂ | -δ < s.re ∧ s ≠ 0} := by
  let A : Set ℂ := {s | 0 < s.re}
  let B : Set ℂ := {s | -δ < s.re ∧ 0 < s.im}
  let C : Set ℂ := {s | -δ < s.re ∧ s.im < 0}
  let D : Set ℂ := {s | -δ < s.re ∧ s.re < 0}
  have hA := (convex_halfSpace_re_gt 0).isPreconnected
  have hB :=
    ((convex_halfSpace_re_gt (-δ)).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hC :=
    ((convex_halfSpace_re_gt (-δ)).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hD : IsPreconnected D :=
    ((convex_halfSpace_re_gt (-δ)).inter (convex_halfSpace_re_lt 0)).isPreconnected
  have hAB := hA.union (1 + Complex.I) (by simp [A]) (by simp [B]; linarith) hB
  have hABC := hAB.union (1 - Complex.I) (by simp [A, B]) (by simp [C]; linarith) hC
  have hall := hABC.union ((-δ / 2 : ℝ) + Complex.I)
    (by simp [A, B, C]; left; right; linarith)
    (by simp [D]; constructor <;> linarith) hD
  convert hall using 1
  ext z
  simp only [A, B, C, D, Set.mem_setOf_eq, Set.mem_union]
  have hz : z ≠ 0 ↔ z.re ≠ 0 ∨ z.im ≠ 0 := by
    simp only [ne_eq, Complex.ext_iff, Complex.zero_re, Complex.zero_im, not_and_or]
  rw [hz]
  constructor
  · rintro ⟨hr, hne⟩
    rcases lt_trichotomy z.re 0 with hl | he | hg
    · exact Or.inr ⟨hr, hl⟩
    · rcases hne with hn | hn
      · exact (hn he).elim
      · rcases lt_or_gt_of_ne hn with hi | hi
        · exact Or.inl (Or.inr ⟨hr, hi⟩)
        · exact Or.inl (Or.inl (Or.inr ⟨hr, hi⟩))
    · exact Or.inl (Or.inl (Or.inl hg))
  · rintro (((hr | ⟨hr, hi⟩) | ⟨hr, hi⟩) | ⟨hr, hi⟩)
    · exact ⟨by linarith, Or.inl (ne_of_gt hr)⟩
    · exact ⟨hr, Or.inr (ne_of_gt hi)⟩
    · exact ⟨hr, Or.inr (ne_of_lt hi)⟩
    · exact ⟨hr, Or.inl (ne_of_lt hi)⟩

include hδ in
private lemma halfPlane_identity {F G : ℂ → ℂ}
    (hF : ∀ z, -δ < z.re → z ≠ 0 → DifferentiableAt ℂ F z)
    (hG : ∀ z, -δ < z.re → z ≠ 0 → DifferentiableAt ℂ G z)
    (heq : ∀ z, 0 < z.re → F z = G z)
    (s : ℂ) (hs : -δ < s.re) (hs0 : s ≠ 0) : F s = G s := by
  let U : Set ℂ := {z | -δ < z.re ∧ z ≠ 0}
  have hU : IsOpen U := (Complex.isOpen_re_gt (-δ)).inter isOpen_compl_singleton
  refine ((show DifferentiableOn ℂ F U from fun z hz =>
    (hF z hz.1 hz.2).differentiableWithinAt).analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq ((show DifferentiableOn ℂ G U from fun z hz =>
    (hG z hz.1 hz.2).differentiableWithinAt).analyticOnNhd hU)
    (punctured_halfPlane_preconnected hδ)
    (show (1 : ℂ) ∈ U by simp [U]; linarith) ?_ ⟨hs, hs0⟩
  filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds (show 0 < (1 : ℂ).re by norm_num)]
    with z hz
  exact heq z hz

end

private lemma contDiffOn_eulerIter {a : ℝ → ℂ} (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0))
    (j : ℕ) : ContDiffOn ℝ ∞ (EulerIter j a) (Set.Ioi 0) := by apply @LogLocalizedJets.LogLocalizedEulerJets.euler_smooth <;> assumption

private alias eulerIter_add_of_pos := LogMellinPhysical.LogarithmicEndpointIntegrability.eulerIter_add_of_pos

private alias contDiffOn_eval_log := LogMellinPhysical.LogarithmicEndpointIntegrability.contDiffOn_eval_log

private alias eulerIter_sub_originPolynomial_eq := LogMellinPhysical.LogarithmicEndpointIntegrability.eulerIter_sub_originPolynomial_eq

private alias eulerIter_eq_remainder_of_degree_lt := LogMellinPhysical.LogarithmicEndpointIntegrability.eulerIter_eq_remainder_of_degree_lt

private lemma high_euler_mellin_differentiableAt {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}
    (h : LogMellinPhysical f δ P) (n : ℕ) (hn : P.natDegree < n)
    (s : ℂ) (hs : -δ < s.re) : DifferentiableAt ℂ (mellin (EulerIter n f)) s := by
  obtain ⟨N, hN⟩ := exists_nat_gt s.re
  obtain ⟨C₂, hC₂, hbound₂⟩ := h.rapid_decay n N
  obtain ⟨C₁, hC₁, hbound₁⟩ := h.origin_remainder n
  apply mellin_differentiableAt_of_isBigO_rpow
    ((contDiffOn_eulerIter h.contDiffOn n).continuousOn.locallyIntegrableOn measurableSet_Ioi)
  · refine Asymptotics.IsBigO.of_bound C₂ ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)]
    exact hbound₂ x hx
  · exact hN
  · refine Asymptotics.IsBigO.of_bound C₁ ?_
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with x hx
    rw [neg_neg, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.1.le _),
      eulerIter_eq_remainder_of_degree_lt h n hn x hx.1]
    exact hbound₁ x hx.1 hx.2
  · exact hs

end Helpers

variable {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} (h : LogMellinPhysical f δ P)

include h in
theorem logMellinHolomorphicPart_differentiableAt (s : ℂ) (hs : -δ < s.re) :
    DifferentiableAt ℂ (logMellinHolomorphicPart f P) s :=
  mellin_differentiableAt_of_isBigO_rpow (by
    exact (h.contDiffOn.continuousOn.locallyIntegrableOn measurableSet_Ioi).sub (locallyIntegrableOn_truncatedLogPolynomial P))
    (logMellinRemainder_isBigO_top h (s.re + 1)) (by linarith)
    (by simpa using logMellinRemainder_isBigO_origin h) hs

include h in
theorem logMellinContinuation_eq_mellin (s : ℂ) (hs : 0 < s.re) :
    logMellinContinuation f P s = mellin f s := by
  have hfconv : MellinConvergent f s := h.euler_mellinConvergent 0 s hs
  have htconv : MellinConvergent (truncatedLogPolynomial P) s :=
    truncatedLogPolynomial_mellinConvergent P s hs
  have hsub : mellin (logMellinRemainder f P) s =
      mellin f s - mellin (truncatedLogPolynomial P) s :=
    (hasMellin_sub hfconv htconv).2
  simp only [logMellinContinuation, logMellinHolomorphicPart, hsub,
    mellin_truncatedLogPolynomial P s hs]
  ring

include h in
theorem logMellinContinuation_eq_euler (n : ℕ) (hn : P.natDegree < n)
    (s : ℂ) (hs : -δ < s.re) (hs0 : s ≠ 0) :
    logMellinContinuation f P s =
      (-s) ^ (-(n : ℤ)) * mellin (EulerIter n f) s := by
  refine halfPlane_identity h.delta_pos (F := logMellinContinuation f P)
    (G := fun z => (-z) ^ (-(n : ℤ)) * mellin (EulerIter n f) z) ?_ ?_ ?_ s hs hs0
  · intro z hz hz0
    exact (logMellinHolomorphicPart_differentiableAt h z hz).add
      (logPrincipalPart_differentiableAt P z hz0)
  · intro z hz hz0
    exact ((differentiableAt_id.neg).zpow (Or.inl (neg_ne_zero.mpr hz0))).mul
      (high_euler_mellin_differentiableAt h n hn z hz)
  · intro z hz
    have hz0 : z ≠ 0 := by intro he; simpa [he] using hz
    rw [logMellinContinuation_eq_mellin h z hz, h.euler_mellin_eq n z hz,
      zpow_neg, zpow_natCast, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n (neg_ne_zero.mpr hz0)),
      one_mul]

include h in
theorem logMellinContinuation_unique (H₀ : ℂ → ℂ)
    (hM : ∀ s : ℂ, 0 < s.re → H₀ s = mellin f s)
    (hR : ∀ s : ℂ, -δ < s.re → s ≠ 0 → DifferentiableAt ℂ H₀ s)
    (s : ℂ) (hs : -δ < s.re) (hs0 : s ≠ 0) :
    H₀ s = logMellinContinuation f P s := by
  refine halfPlane_identity h.delta_pos hR ?_ ?_ s hs hs0
  · intro z hz hz0
    exact (logMellinHolomorphicPart_differentiableAt h z hz).add
      (logPrincipalPart_differentiableAt P z hz0)
  · intro z hz
    exact (hM z hz).trans (logMellinContinuation_eq_mellin h z hz).symm

end DedekindZetaZeroFree.LargeSieve.Vendor

end
