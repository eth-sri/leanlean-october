module

public import GradedNear.Defs

/-!
# Basic identities for the graded near lemma

Logarithmic scale, spectral points, and the integration cutoff.
-/

@[expose] public section

open Complex Filter Topology

noncomputable section

namespace GradedNear

-- The zero and entry coordinates used in the explicit formula and threshold estimates.
scoped notation "zeroOffset " q:max ρ:max => ((1 - Complex.re ρ) * Real.log q)
scoped notation "discGap " γ:max ρ:max => ‖(1 + (γ : ℂ) * I) - ρ‖
scoped notation "heightGap " q:max γ:max ρ:max => (|γ - Complex.im ρ| * Real.log q)
scoped notation "entryAnchor " D:max E:max j:max => (NearData.s D - Entries.δ E j)
scoped notation "diagNumerator " D:max E:max j:max =>
  (NearData.Dδ D (Entries.δ E j) - NearData.d₁ D + pairExcess D E j)
scoped notation "heightTerm " D:max E:max j:max hi:max =>
  Complex.re (laplace (NearData.f D) ((hi - entryAnchor D E j : ℝ) : ℂ))

-- Common statement forms. These expand to the quantifiers and inequalities themselves.
scoped macro "LargeModuli[" q:ident " => " P:term "]" : term =>
  `(∃ q₀ : ℕ, ∀ ($q : ℕ), [NeZero $q] → q₀ ≤ $q → $P)

scoped macro "SeparatedModuli[" M:ident ", " δ:ident ", " q:ident " => " P:term "]" : term =>
  `(Exists fun ($M : ℝ) => 0 < $M ∧ Exists fun ($δ : ℝ) => 0 < $δ ∧ $δ < 1 ∧ LargeModuli[$q => $P])

scoped macro "NearFamily[" D:term ", " q:term "; " ι:ident ", " E:ident " => " P:term "]" : term =>
  `(∀ T : ℝ, 0 ≤ T → T ≤ Real.log $q / 3 → SafeAnchor $q (NearData.s₁ $D) (2 * T + 1) →
    ∀ ($ι : Type) [Fintype $ι] ($E : Entries $q $ι),
      (∀ j, Entries.χ $E j ≠ 1) → (∀ j, |Entries.γ $E j| ≤ T) → (∀ j, Entries.δ $E j ∈ NearData.Δ $D) →
      ((∃ k < NearData.m $D, NearData.h $D k ≠ 0) → Function.Injective (Entries.χ $E)) → $P)

/-- Keep only disc zeros, and bound the number and distance of the unkept zeros right of the anchor. -/
scoped macro "KeptFamily[" D:term ", " q:term "; " ι:term ", " E:term "; " M:term ", " δ:term ", " K:term "; " Sz:ident " => " P:term "]" : term =>
  `(∀ ($Sz : $ι → Finset ℂ),
    (∀ j, ∀ ρ ∈ $Sz j, DirichletCharacter.LFunction (Entries.χ $E j) ρ = 0 ∧ discGap (Entries.γ $E j) ρ ≤ $δ) →
    (∀ j, ∀ ρ : ℂ, DirichletCharacter.LFunction (Entries.χ $E j) ρ = 0 →
      discGap (Entries.γ $E j) ρ ≤ $δ → ρ ∉ $Sz j →
      zeroOffset $q ρ < entryAnchor $D $E j → $M ≤ heightGap $q (Entries.γ $E j) ρ) →
    (∀ j, (∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction (Entries.χ $E j) ρ = 0 ∧
        discGap (Entries.γ $E j) ρ ≤ $δ ∧ ρ ∉ $Sz j ∧ zeroOffset $q ρ < entryAnchor $D $E j},
      zmult (Entries.χ $E j) ρ) ≤ $K) → $P)

lemma tendsto_log_nat_atTop : Tendsto (fun q : ℕ => Real.log q) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_div_log_nat (c : ℝ) : Tendsto (fun q : ℕ => c / Real.log q) atTop (𝓝 0) := 
  tendsto_const_nhds.div_atTop tendsto_log_nat_atTop

lemma eventually_neZero {P : (q : ℕ) → NeZero q → Prop}
    (h : ∀ᶠ q in atTop, ∀ [z : NeZero q], P q z) :
    ∃ q₀, ∀ q [z : NeZero q], q₀ ≤ q → P q z :=
  (eventually_atTop.mp h).imp fun _ h q _ hq => h q hq

def spectralPoint (q : ℕ) (s t : ℝ) : ℂ := ((1 - s / Real.log q : ℝ) : ℂ) + (t : ℂ) * I

@[simp] lemma spectralPoint_re (q : ℕ) (s t : ℝ) :
    (spectralPoint q s t).re = 1 - s / Real.log q := by
  simp [spectralPoint, -natCast_log]

@[simp] lemma spectralPoint_im (q : ℕ) (s t : ℝ) :
    (spectralPoint q s t).im = t := by
  simp [spectralPoint, -natCast_log]

lemma spectralPoint_sub {q : ℕ} (r t : ℝ) (ρ : ℂ) (h : Real.log q ≠ 0) :
    (spectralPoint q r t - ρ) * (Real.log q : ℂ) =
      (((1 - ρ.re) * Real.log q - r : ℝ) : ℂ) + (((t - ρ.im) * Real.log q : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp [mul_re, mul_im, -natCast_log]
  field_simp
  ring

/-- `t_n = log n / log q`. -/
def tn (q n : ℕ) : ℝ := Real.log n / Real.log q

lemma log_q_pos {q : ℕ} (hq : 2 ≤ q) : 0 < Real.log q :=
  Real.log_pos (by simpa)

lemma tendsto_loglog_nat : Tendsto (fun q : ℕ => Real.log (Real.log q)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_log_nat_atTop

lemma eventually_loglog_ge (K : ℝ) :
    ∀ᶠ q : ℕ in atTop, K ≤ Real.sqrt (Real.log (Real.log q)) ∧ 2 ≤ q := by
  filter_upwards [tendsto_loglog_nat.eventually_ge_atTop (K ^ 2), eventually_ge_atTop 2] with q hq hq2
  exact ⟨Real.le_sqrt_of_sq_le hq, hq2⟩

lemma spectralPoint_region {q : ℕ} (hq : 2 ≤ q) {σ γ : ℝ}
    (hσ : |σ| ≤ Real.sqrt (Real.log (Real.log q))) (hγ : |γ| ≤ Real.log q) :
    LemmaRegion q (spectralPoint q σ γ) := by
  refine ⟨?_, by simpa using hγ⟩
  simpa only [spectralPoint_re, sub_sub_cancel_left, abs_neg, abs_div, abs_of_pos (log_q_pos hq)] using
    div_le_div_of_nonneg_right hσ (log_q_pos hq).le

lemma tn_nonneg (q n : ℕ) : 0 ≤ tn q n :=
  div_nonneg (Real.log_natCast_nonneg n) (Real.log_natCast_nonneg q)

lemma le_tn_iff {q n : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n) {X : ℝ} : X ≤ tn q n ↔ (q : ℝ) ^ X ≤ n := by
  rw [tn, le_div_iff₀ (log_q_pos hq), ← Real.log_rpow (by positivity : 0 < (q : ℝ))]
  exact Real.log_le_log_iff (by positivity) (by positivity)

open MeasureTheory in
lemma integral_support_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {X : ℝ} (hX : 0 ≤ X) (hf : ∀ t ≥ X, f t = 0) :
    (∫ t in (0 : ℝ)..X, f t) = ∫ t in Set.Ioi 0, f t := by
  rw [intervalIntegral.integral_of_le hX]
  exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioc_subset_Ioi_self
    fun t ht => hf t (by grind)).symm

open Finset in
lemma sum_Ioc_eq_range {α : Type*} [AddCommMonoid α] (f : ℕ → α) (a b : ℕ) :
    ∑ n ∈ Ioc a b, f n = ∑ n ∈ range (b - a), f (a + 1 + n) := by
  rw [← Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range, Nat.add_sub_add_right]

end GradedNear
