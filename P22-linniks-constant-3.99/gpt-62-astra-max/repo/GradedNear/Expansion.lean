module

public import GradedNear.Basic

/-!
# The responses as one sum over `n`

`Σ_j a_j R_j = -𝓛⁻¹ Σ_{1 ≤ n ≤ q^{x_f}} c_n Re Y_n`, with `c_n = (Λ(n)/n) e^{s t_n} f(t_n)` and
`Y_n = Σ_j a_j e^{-δ_j t_n} χ_j(n) e^{-i γ_j log n}` (paper §8.5).
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

variable {q : ℕ} {ι : Type*}

/-- The height window and admissible offsets of a finite family. The zero-free
anchor and the distinctness condition are imposed separately where needed. -/
structure Window (D : NearData) (E : Entries q ι) where
  T : ℝ
  cap : T ≤ Real.log q / 3
  heights : ∀ j, |E.γ j| ≤ T
  offsets : ∀ j, E.δ j ∈ D.Δ

lemma Window.gap {D : NearData} {E : Entries q ι} (w : Window D E) (j k : ι) :
    |E.γ j-E.γ k| ≤ 2*w.T := by linarith [abs_sub (E.γ j) (E.γ k), w.heights j, w.heights k]

/-- Test point with normalized real displacement `σ` and height `γ`. -/
abbrev point (q : ℕ) (σ γ : ℝ) : ℂ := testPoint q σ γ

@[simp] lemma point_re (q : ℕ) (σ γ : ℝ) : (point q σ γ).re = 1 - σ / Real.log q := by rw [point, ← mk_eq_add_mul_I]
@[simp] lemma point_im (q : ℕ) (σ γ : ℝ) : (point q σ γ).im = γ := by rw [point, ← mk_eq_add_mul_I]

lemma point_arg (σ γ : ℝ) (ρ : ℂ) (hℓ : Real.log q ≠ 0) :
    (point q σ γ - ρ) * (Real.log q : ℂ) =
      xy[λρ[q] ρ - σ, (γ - ρ.im) * Real.log q] := by
  apply Complex.ext <;> simp only [← mk_eq_add_mul_I, re_mul_ofReal, im_mul_ofReal, sub_re, sub_im]; field_simp; ring

/-- The oscillatory part of a twisted character. -/
def twist (χ : DirichletCharacter ℂ q) (γ : ℝ) (n : ℕ) : ℂ :=
  χ n * cexp (-((γ * Real.log n : ℝ) : ℂ) * I)

/-- Character, damping, and oscillation of one entry, before applying its coefficient. -/
def signal (χ : DirichletCharacter ℂ q) (σ γ : ℝ) (n : ℕ) : ℂ :=
  (Real.exp (σ * tn q n) : ℂ) * twist χ γ n

lemma signal_add (χ : DirichletCharacter ℂ q) (s σ γ : ℝ) (n : ℕ) :
    signal χ (s+σ) γ n = Real.exp (s*tn q n) * signal χ σ γ n := by
  simp [signal, add_mul, Real.exp_add, mul_assoc]

/-- Separate `n⁻¹`, damping, and oscillation in the prime sum. -/
lemma shifted_power {n : ℕ} (hn : 1 ≤ n) (χ : DirichletCharacter ℂ q) (σ γ : ℝ) :
    χ n * (n : ℂ) ^ (-point q σ γ) =
      (((n:ℝ)⁻¹ : ℝ) : ℂ) * signal χ σ γ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [natCast_cpow_neg (by omega), show -(1 - σ / Real.log q) * Real.log n = σ * tn q n - Real.log n by unfold tn; ring,
    Real.exp_sub, Real.exp_log hn']
  unfold signal twist; push_cast; ring

lemma primeSum_re {f : ℝ → ℝ} {X : ℝ} (hq : 2 ≤ q) (hf : ∀ t, X ≤ t → f t = 0)
    (χ : DirichletCharacter ℂ q) (σ γ : ℝ) :
    (primeSum χ f (point q σ γ)).re =
      ∑ n ∈ samples q X, primeMass n * f (tn q n) * (signal χ σ γ n).re := by
  rw [primeSum, tsum_eq_sum (s := samples q X) ?_, Complex.re_sum]
  rotate_left
  · intro n hn
    cases n with
    | zero => simp
    | succ n => simp [samples] at hn; exact mul_eq_zero_of_right _ (ofReal_eq_zero.mpr (hf _ (tn_ge_of_gt hq (Nat.lt_succ_of_le hn))))
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [mul_assoc (Λ n : ℂ), shifted_power (Finset.mem_Icc.mp hn).1]
  simp only [primeMass, tn, re_ofReal_mul, re_mul_ofReal]; ring

variable [Fintype ι]

abbrev entrySignal (E : Entries q ι) (j : ι) := signal (E.χ j) (-E.δ j) (E.γ j)

def Yn (E : Entries q ι) (a : ι → ℝ) (n : ℕ) : ℂ := ∑ j, (a j : ℂ) * entrySignal E j n

/-- `Σ_j a_j R_j = -𝓛⁻¹ Σ_{1 ≤ n ≤ q^{x_f}} c_n Re Y_n`. -/
lemma sum_response (D : NearData) (E : Entries q ι) (a : ι → ℝ) (hq : 2 ≤ q)
    (hD : D.Valid) :
    ∑ j, a j * response D E j =
      -(∑ n ∈ samples q D.horizon, primeMass n * amplitude D (tn q n) * (Yn E a n).re) /
        Real.log q := by
  have hf t (ht : D.horizon ≤ t) := hD.f_cond.vanish t ((le_max_left ..).trans ht)
  simp_rw [response, primeSum_re hq hf, Yn, Complex.re_sum,
    ← mul_div_assoc, mul_neg, Finset.mul_sum, ← Finset.sum_div, Finset.sum_neg_distrib]
  congr 2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [sub_eq_add_neg, signal_add, amplitude, re_ofReal_mul, entrySignal]; ring

end GradedNear
