module

public import OAI.NumberTheory.PrimeGaps.LevelMoments
public import Mathlib.Data.Int.Star

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

def divisorMultiplicity (k n : ℕ) : ℕ := (ArithmeticFunction.zeta ^ k) n

theorem divisorMultiplicity_succ (k n : ℕ) :
    divisorMultiplicity (k+1) n = ∑ d ∈ n.divisors, divisorMultiplicity k d := by
  simp only [divisorMultiplicity, pow_succ, ArithmeticFunction.mul_zeta_apply]

theorem reciprocal_divisor_sum_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q : ℝ)) ≤
      (∑ d ∈ Finset.Icc 1 Q, f d / (d : ℝ)) * (harmonic Q : ℝ) := by
  classical
  let s := (Finset.Icc 1 Q).sigma fun q => q.divisors
  let t := (Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)
  let e : (a : ℕ) × ℕ → ℕ × ℕ := fun x => (x.2, x.1/x.2)
  have he_mem : ∀ x ∈ s, e x ∈ t := by
    rintro ⟨q,d⟩ hx
    obtain ⟨hq, hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq1,hqQ⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hdq,hq0⟩ := Nat.mem_divisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq1
    have hdle : d ≤ q := Nat.le_of_dvd hq1 hdq
    have hdivpos : 0 < q/d := Nat.div_pos hdle hd0
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hd0, hdle.trans hqQ⟩,
      Finset.mem_Icc.mpr ⟨hdivpos, (Nat.div_le_self q d).trans hqQ⟩⟩
  have he_inj : Set.InjOn e s := by
    rintro ⟨q,d⟩ hx ⟨q',d'⟩ hy he
    obtain ⟨hq,hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq',hd'⟩ := Finset.mem_sigma.mp hy
    have hed : d = d' := congrArg Prod.fst he
    have heq : q/d = q'/d' := congrArg Prod.snd he
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdq' : d' ∣ q' := (Nat.mem_divisors.mp hd').1
    have hqq : q = q' := by
      rw [← Nat.div_mul_cancel hdq, ← Nat.div_mul_cancel hdq', heq, hed]
    subst d'
    subst q'
    rfl
  have hsum : (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q : ℝ)) =
      ∑ x ∈ s, f (e x).1 / (e x).1 / (e x).2 := by
    dsimp only [s]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hdq := (Nat.mem_divisors.mp hd).1
    dsimp only [e]
    rw [div_div, ← Nat.cast_mul, Nat.mul_div_cancel' hdq]
  rw [hsum]
  calc
    _ = ∑ x ∈ s.image e, f x.1 / (x.1 : ℝ) / (x.2 : ℝ) := by
      rw [Finset.sum_image he_inj]
    _ ≤ ∑ x ∈ t, f x.1 / (x.1 : ℝ) / (x.2 : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr he_mem)
        (fun x _ _ => div_nonneg (div_nonneg (hf _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    _ = _ := by
      simp only [t, Finset.sum_product, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum,
        harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.sum_comm]

theorem sum_divisorMultiplicity_reciprocal_le (k Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (divisorMultiplicity k q : ℝ) / (q : ℝ)) ≤
      (harmonic Q : ℝ) ^ k := by
  induction k with
  | zero =>
    by_cases hQ : Q = 0
    · subst Q; simp
    · have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr hQ
      simp [divisorMultiplicity, ArithmeticFunction.one_apply, ite_div, hQ1]
  | succ k ih =>
    have h := reciprocal_divisor_sum_le (fun n => (divisorMultiplicity k n : ℝ))
      (fun n => Nat.cast_nonneg _) Q
    simp only [divisorMultiplicity_succ, Nat.cast_sum] at ⊢
    apply h.trans
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right ih (by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

noncomputable def residueSlice (f : ℕ → ℝ) (L U q c : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc L U).filter (fun n => n % q = c), f n

noncomputable def residuePrefix (f : ℕ → ℝ) (Y q c : ℕ) : ℝ :=
  residueSlice f 0 Y q c

end LargePrimeGaps

end OAI
