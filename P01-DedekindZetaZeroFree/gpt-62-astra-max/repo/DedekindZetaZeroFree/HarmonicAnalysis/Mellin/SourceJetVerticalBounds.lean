module

public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.PositiveSideJetSeminorms
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.RegularizedGammaProduct

@[expose] public section

noncomputable section

open scoped NumberField Classical ContDiff
open MeasureTheory

namespace DedekindZetaZeroFree.LargeSieve.Vendor

private lemma iteratedDeriv_eq_zero_of_gt (b : ℝ) (h : ℝ → ℂ)
    (hpos : PositiveSideSupport b h) :
    ∀ (n : ℕ) (x : ℝ), b < x → iteratedDeriv n h x = 0 := by
  intro n
  induction n with
  | zero => intro x hx; exact hpos x hx
  | succ n ih =>
      intro x hx
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv n h =ᶠ[nhds x] (fun _ : ℝ => (0 : ℂ)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact ih y hy
      rw [hev.deriv_eq]
      simp

alias SourceJetVerticalBounds.iteratedDeriv_eq_zero_of_gt := iteratedDeriv_eq_zero_of_gt

private alias S_nonneg_aux := S_nonneg

private lemma jet_le_S (b : ℝ) (hb : 0 < b) (N : ℕ) (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (i : ℕ) (hi : i ≤ N) (x : ℝ) (hx : x ∈ Set.Icc 0 b) :
    ‖iteratedDeriv i h x‖ ≤ S b N h := by
  have h1 := le_csSup ((isCompact_Icc.image (contDiff_iteratedDeriv h hh i).continuous.norm).bddAbove) (⟨x, hx, rfl⟩)
  have hnonneg : ∀ j ∈ Finset.range (N + 1),
      0 ≤ sSup ((fun y : ℝ => ‖iteratedDeriv j h y‖) '' Set.Icc 0 b) := by
    intro j _
    exact le_trans (norm_nonneg _) (le_csSup ((isCompact_Icc.image (contDiff_iteratedDeriv h hh j).continuous.norm).bddAbove) (⟨0, ⟨le_rfl, le_of_lt hb⟩, rfl⟩))
  have h2 : sSup ((fun y : ℝ => ‖iteratedDeriv i h y‖) '' Set.Icc 0 b) ≤ S b N h := by
    unfold S
    exact Finset.single_le_sum hnonneg (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  linarith

private lemma norm_mellin_le (f : ℝ → ℂ) (b a M : ℝ) (hb : 0 < b) (ha : 0 < a)
    (hM : 0 ≤ M) (hf0 : ∀ x : ℝ, b < x → f x = 0)
    (hfM : ∀ x ∈ Set.Icc 0 b, ‖f x‖ ≤ M)
    (w : ℂ) (hw : w.re = a) :
    ‖mellin f w‖ ≤ M * (b ^ a / a) := by
  have hbound : ∀ x : ℝ,
      ‖(Set.Ioi (0 : ℝ)).indicator (fun y : ℝ => (y : ℂ) ^ (w - 1) • f y) x‖ ≤
        (Set.Ioc (0 : ℝ) b).indicator (fun y : ℝ => M * y ^ (a - 1)) x := by
    intro x
    by_cases hx : x ∈ Set.Ioi (0 : ℝ)
    · by_cases hxb : x ∈ Set.Ioc (0 : ℝ) b
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxb]
        have hnorm : ‖(x : ℂ) ^ (w - 1) • f x‖ = x ^ (a - 1) * ‖f x‖ := by
          rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re,
            Complex.one_re, hw]
        rw [hnorm, mul_comm (x ^ (a - 1)) ‖f x‖]
        exact mul_le_mul_of_nonneg_right (hfM x ⟨le_of_lt hxb.1, hxb.2⟩)
          (Real.rpow_nonneg (le_of_lt hx) _)
      · have hbx : b < x := by
          simp only [Set.mem_Ioi] at hx
          simp only [Set.mem_Ioc, not_and, not_le] at hxb
          exact hxb hx
        rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hxb,
          hf0 x hbx, smul_zero, norm_zero]
    · rw [Set.indicator_of_notMem hx]
      by_cases hxb : x ∈ Set.Ioc (0 : ℝ) b
      · rw [Set.indicator_of_mem hxb, norm_zero]
        exact mul_nonneg hM (Real.rpow_nonneg (le_of_lt hxb.1) _)
      · rw [Set.indicator_of_notMem hxb]; simp
  have hmell : mellin f w =
      ∫ x, (Set.Ioi (0 : ℝ)).indicator (fun y : ℝ => (y : ℂ) ^ (w - 1) • f y) x := by
    rw [mellin]
    exact (MeasureTheory.integral_indicator measurableSet_Ioi).symm
  rw [hmell]
  refine le_trans (MeasureTheory.norm_integral_le_of_norm_le (IntegrableOn.integrable_indicator (((intervalIntegral.intervalIntegrable_rpow'
    (by linarith : -1 < a - 1)).1).const_mul M) measurableSet_Ioc)
    (Filter.Eventually.of_forall hbound)) ?_
  rw [MeasureTheory.integral_indicator measurableSet_Ioc, MeasureTheory.integral_const_mul,
    ← intervalIntegral.integral_of_le (le_of_lt hb),
    integral_rpow (Or.inl (by linarith : -1 < a - 1))]
  have ha1 : a - 1 + 1 = a := by ring
  rw [ha1, Real.zero_rpow (ne_of_gt ha), sub_zero]

variable (b : ℝ) (hb : 0 < b)

include hb in
private lemma rpow_le_endpoints {u v σ : ℝ}
    (hσ : σ ∈ Set.Icc u v) : b ^ σ ≤ max (b ^ u) (b ^ v) := by
  rcases le_total 1 b with hb1 | hb1
  · exact le_trans (Real.rpow_le_rpow_of_exponent_le hb1 hσ.2) (le_max_right _ _)
  · exact le_trans (Real.rpow_le_rpow_of_exponent_ge hb hb1 hσ.1) (le_max_left _ _)

include hb in
theorem originMellin_source_vertical_bound (u v : ℝ) (huv : u ≤ v) (k : ℕ) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ (h : ℝ → ℂ), ContDiff ℝ ∞ h → HasCompactSupport h →
        PositiveSideSupport b h →
        ∀ (σ t : ℝ), σ ∈ Set.Icc u v → 1 ≤ |t| →
          (1 + |t|) ^ k *
            ‖Complex.Gammaℂ ((σ : ℂ) + (t : ℂ) * Complex.I) *
              originMellinQ h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * S b N h := by
  set m : ℕ := k + Nat.ceil (-u) + 1 with hmdef
  have hmk : k ≤ m := by omega
  have hceil := Nat.le_ceil (-u)
  have hmcast : (m : ℝ) = (k : ℝ) + (Nat.ceil (-u) : ℝ) + 1 := by
    rw [hmdef]; push_cast; ring
  have hum : 0 < u + (m : ℝ) := by rw [hmcast]; linarith
  set C_D : ℝ := max (b ^ (u + (m : ℝ))) (b ^ (v + (m : ℝ))) / (u + (m : ℝ)) with hCDdef
  have hCDpos : 0 < C_D := by
    rw [hCDdef]
    exact div_pos (lt_of_lt_of_le (Real.rpow_pos_of_pos hb _) (le_max_left _ _)) hum
  refine ⟨m, (2 : ℝ) ^ k * C_D, mul_pos (pow_pos (by norm_num) k) hCDpos, ?_⟩
  intro h hh hc hpos σ t hσ ht
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hs_ne : -(m : ℝ) < s.re := by rw [hsre]; linarith [hσ.1]
  have hsim_ne : s.im ≠ 0 := by
    rw [hsim]
    exact abs_pos.mp (lt_of_lt_of_le zero_lt_one ht)
  have hshift := Gammaℂ_mul_originMellinQ_eq_shift h hh hc m s hs_ne hsim_ne
  have hS := S_nonneg_aux b hb m h hh
  have hnum : ‖mellin (iteratedDeriv m h) (s + (m : ℂ))‖ ≤ S b m h * C_D := by
    have hbase := norm_mellin_le (iteratedDeriv m h) b (σ + (m : ℝ)) (S b m h) hb
      (by linarith [hσ.1]) hS
      (fun x hx => iteratedDeriv_eq_zero_of_gt b h hpos m x hx)
      (fun x hx => jet_le_S b hb m h hh m le_rfl x hx)
      (s + (m : ℂ)) (by simp [hsdef])
    refine le_trans hbase (mul_le_mul_of_nonneg_left ?_ hS)
    rw [hCDdef]
    calc _
        ≤ max (b ^ (u + (m : ℝ))) (b ^ (v + (m : ℝ))) / (σ + (m : ℝ)) :=
          div_le_div_of_nonneg_right (rpow_le_endpoints b hb (⟨by linarith [hσ.1], by linarith [hσ.2]⟩)) (by linarith [hσ.1])
      _ ≤ max (b ^ (u + (m : ℝ))) (b ^ (v + (m : ℝ))) / (u + (m : ℝ)) :=
          div_le_div_of_nonneg_left (le_trans (Real.rpow_nonneg hb.le _) (le_max_left _ _))
            (by linarith [hum]) (by linarith [hσ.1])
  have hden : |t| ^ m ≤ ‖∏ j ∈ Finset.range m, (s + (j : ℂ))‖ := by
    rw [norm_prod]
    calc _ = ∏ _j ∈ Finset.range m, |t| := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ j ∈ Finset.range m, ‖s + (j : ℂ)‖ := by
          refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j _ => ?_)
          have him : (s + (j : ℂ)).im = t := by simp [hsdef]
          calc |t| = |(s + (j : ℂ)).im| := by rw [him]
            _ ≤ ‖s + (j : ℂ)‖ := by exact RCLike.abs_im_le_norm (s + (j : ℂ))
  have hprod : ‖Complex.Gammaℂ s * originMellinQ h s‖ ≤ S b m h * C_D / |t| ^ m := by
    rw [hshift, norm_div, norm_mul]
    have hone : ‖(-1 : ℂ) ^ m‖ = 1 := by simp
    rw [hone, one_mul]
    exact le_trans (div_le_div_of_nonneg_right hnum (norm_nonneg _))
      (div_le_div_of_nonneg_left (mul_nonneg hS hCDpos.le) (by
        rw [← hsim]; exact pow_pos (abs_pos.mpr hsim_ne) m) hden)
  have ht1 := ht
  have hratio : (1 + |t|) ^ k / |t| ^ m ≤ 2 ^ k := by
    rw [div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one ht1) m)]
    calc _ ≤ 2 ^ k * |t| ^ k := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) (by linarith) k
      _ ≤ 2 ^ k * |t| ^ m :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 hmk) (by positivity)
  calc _
      ≤ (1 + |t|) ^ k * (S b m h * C_D / |t| ^ m) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = S b m h * C_D * ((1 + |t|) ^ k / |t| ^ m) := by ring
    _ ≤ S b m h * C_D * 2 ^ k :=
        mul_le_mul_of_nonneg_left hratio (mul_nonneg hS hCDpos.le)
    _ = (2 : ℝ) ^ k * C_D * S b m h := by ring

end DedekindZetaZeroFree.LargeSieve.Vendor

end
