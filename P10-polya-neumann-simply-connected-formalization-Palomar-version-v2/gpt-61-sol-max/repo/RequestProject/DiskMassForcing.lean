module

public import RequestProject.DiskHalfTrace


public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.DiskAreaBessel
public import RequestProject.SobolevMultiplier
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# One full Sobolev derivative from physical disk mass forcing

The nonzero-mode coefficient has multiplier sqrt(1+|n|)/(sqrt(2π)|n|).
The area Bessel estimate bounds the entire H¹ Fourier norm, rather than
only the individual coefficients. Frequency zero is removed explicitly.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate

def diskMassForcingScale m  :=
  Real.sqrt ((m + 2 : ℕ) : ℝ) / (Real.sqrt circlePeriod * ((m + 1 : ℕ) : ℝ))

def diskMassForcingCoeff (v : L2 unitDisk) : ℤ → ℂ
  | Int.ofNat 0 => 0
  | Int.ofNat (m + 1) => (diskMassForcingScale m : ℂ) *
      ∫ z in unitDisk, (v : PlaneMap) z * conj z ^ (m + 1)
  | Int.negSucc m => (diskMassForcingScale m : ℂ) *
      ∫ z in unitDisk, (v : PlaneMap) z * z ^ (m + 1)

private theorem diskMassForcingScale_weight m a :
    (((m + 2 : ℕ) : ℝ) * ‖(diskMassForcingScale m : ℂ) * a‖) ^ 2 ≤
      (4 / circlePeriod) * (((m + 2 : ℕ) : ℝ) * ‖a‖ ^ 2) := by
  have hk : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hweightPos : 0 < ((m + 2 : ℕ) : ℝ) := by positivity
  have hratio : ((m + 2 : ℕ) : ℝ) ^ 2 ≤ 4 * ((m + 1 : ℕ) : ℝ) ^ 2 := by
    have hle : ((m + 2 : ℕ) : ℝ) ≤ 2 * ((m + 1 : ℕ) : ℝ) := by
      push_cast
      nlinarith
    nlinarith
  have hscale : 0 ≤ diskMassForcingScale m := by unfold diskMassForcingScale; positivity
  have hw : (((m + 2 : ℕ) : ℝ) * diskMassForcingScale m) ^ 2 ≤
      (4 / circlePeriod) * ((m + 2 : ℕ) : ℝ) := by
    rw [mul_pow, diskMassForcingScale, div_pow, mul_pow,
      Real.sq_sqrt hweightPos.le, Real.sq_sqrt Real.two_pi_pos.le]
    calc
      _ ≤ (4 * ((m + 1 : ℕ)) ^ 2) *
          (((m + 2 : ℕ)) / (circlePeriod * ((m + 1 : ℕ)) ^ 2)) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = _ := by field_simp
  calc
    _ = (((m + 2 : ℕ)) * diskMassForcingScale m) ^ 2 * ‖a‖ ^ 2 := by
      rw [norm_mul, Complex.norm_of_nonneg hscale]
      ring
    _ ≤ ((4 / circlePeriod) * ((m + 2 : ℕ))) * ‖a‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = _ := by ring

private theorem diskMassForcing_sector (M : ComplexSeq) B
    (hs : Summable (fun m => ((m + 1 : ℕ) : ℝ) * ‖M m‖ ^ 2))
    (hB : (∑' m : ℕ, ((m + 1 : ℕ) : ℝ) * ‖M m‖ ^ 2) ≤ π * B) :
    Summable (fun m => (((m + 2 : ℕ) : ℝ) *
      ‖(diskMassForcingScale m : ℂ) * M (m + 1)‖) ^ 2) ∧
    (∑' m : ℕ, (((m + 2 : ℕ) : ℝ) *
      ‖(diskMassForcingScale m : ℂ) * M (m + 1)‖) ^ 2) ≤ 2 * B := by
  let f  := fun m => ((m + 1 : ℕ)) * ‖M m‖ ^ 2
  let e  := fun m => (((m + 2 : ℕ)) *
    ‖(diskMassForcingScale m) * M (m + 1)‖) ^ 2
  have hi : Function.Injective (fun m : ℕ => m + 1) := by
    simp_all [Function.Injective]
  have ht  := hs.comp_injective hi
  have htail  :=
    (tsum_comp_le_tsum_of_inj hs (fun m => by positivity) hi).trans hB
  have he (m : ℕ) : e m ≤ (4 / circlePeriod) * f (m + 1) := by
    solve_by_elim (maxDepth := 2) [diskMassForcingScale_weight]
  have hse  := Summable.of_nonneg_of_le (fun m => sq_nonneg _) he
    (ht.mul_left (4 / circlePeriod))
  refine ⟨hse, ?_⟩
  calc
    _ ≤ ∑' m : ℕ, (4 / circlePeriod) * f (m + 1) :=
      hse.tsum_le_tsum he (ht.mul_left _)
    _ = (4 / circlePeriod) * ∑' m : ℕ, f (m + 1) := tsum_mul_left
    _ ≤ (4 / circlePeriod) * (π * B) := mul_le_mul_of_nonneg_left htail (by positivity)
    _ = 2 * B := by field_simp; ring

section
variable (v : L2 unitDisk)

include v in
theorem diskMassForcingCoeff_h1 :
    IsSobolevSeq 1 (diskMassForcingCoeff v) ∧
      sobNormSq 1 (diskMassForcingCoeff v) ≤ 4 * ‖v‖ ^ 2 := by
  let Mp  := fun m => ∫ z in ball 0 1, v z * conj z ^ m
  let Mn  := fun m => ∫ z in ball 0 1, v z * z ^ m
  have hp := diskMassForcing_sector Mp (‖v‖ ^ 2)
    (disk_area_holomorphic_bessel v).1 (disk_area_holomorphic_bessel v).2
  have hn := diskMassForcing_sector Mn (‖v‖ ^ 2)
    (disk_area_antiholomorphic_bessel v).1 (disk_area_antiholomorphic_bessel v).2
  let bp  := fun m => (((m + 2 : ℕ)) *
    ‖(diskMassForcingScale m) * Mp (m + 1)‖) ^ 2
  let bn  := fun m => (((m + 2 : ℕ)) *
    ‖(diskMassForcingScale m) * Mn (m + 1)‖) ^ 2
  let b  := Sum.elim bp bn
  let a  := fun n => (sobWeight n * ‖diskMassForcingCoeff v n‖) ^ 2
  have hb  := Summable.sum b hp.1 hn.1
  have hpos (m : ℕ) : a ((m + 1 : ℕ) : ℤ) = b (Sum.inl m) := by
    simp only [a, b, Sum.elim_inl, bp, diskMassForcingCoeff, sobWeight, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (m + 1) :
        (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]
    push_cast
    ring
  have hneg (m : ℕ) : a (-((m + 1 : ℕ) : ℤ)) = b (Sum.inr m) := by
    have hi : -((m + 1 : ℕ) : ℤ) = Int.negSucc m := by omega
    simp only [a, b, Sum.elim_inr, bn, Mn, hi, diskMassForcingCoeff, sobWeight,
      Int.cast_negSucc, abs_neg, abs_of_nonneg (Nat.cast_nonneg (m + 1) :
        (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]
    congr 2
    push_cast
    ring
  obtain ⟨ha, hsum⟩ := common_int_tsum_eq_halves a b hb (by simp [a, diskMassForcingCoeff])
    hpos hneg
  refine ⟨?_, ?_⟩
  · simpa  [IsSobolevSeq] using ha
  · change (∑' n : ℤ, (sobWeight n ^ 1 * ‖diskMassForcingCoeff v n‖) ^ 2) ≤ _
    simp only [Real.rpow_one]
    change (∑' n : ℤ, a n) ≤ _
    rw [hsum, Summable.tsum_sum (f := b) hp.1 hn.1]
    change (∑' m : ℕ, bp m) + (∑' m : ℕ, bn m) ≤ _
    linarith [hp.2, hn.2]

theorem diskMassForcingCoeff_add v w n :
    diskMassForcingCoeff (v + w) n = diskMassForcingCoeff v n + diskMassForcingCoeff w n := by
  cases n with
  | ofNat k =>
      cases k with
      | zero => simp [diskMassForcingCoeff]
      | succ m =>
          simp only [diskMassForcingCoeff]
          rw [← inner_diskHolomorphicArea_eq_integral, ← inner_diskHolomorphicArea_eq_integral,
            ← inner_diskHolomorphicArea_eq_integral, inner_add_right, mul_add]
  | negSucc m =>
      simp only [diskMassForcingCoeff]
      rw [← inner_diskAntiholomorphicArea_eq_integral, ← inner_diskAntiholomorphicArea_eq_integral,
        ← inner_diskAntiholomorphicArea_eq_integral, inner_add_right, mul_add]

theorem diskMassForcingCoeff_smul c v n :
    diskMassForcingCoeff (c • v) n = c * diskMassForcingCoeff v n := by
  cases n with
  | ofNat k =>
      cases k with
      | zero => simp [diskMassForcingCoeff]
      | succ m =>
          simp  [diskMassForcingCoeff]
          rw [← inner_diskHolomorphicArea_eq_integral, ← inner_diskHolomorphicArea_eq_integral,
            inner_smul_right]
          ring
  | negSucc m =>
      simp  [diskMassForcingCoeff]
      rw [← inner_diskAntiholomorphicArea_eq_integral, ← inner_diskAntiholomorphicArea_eq_integral,
        inner_smul_right]
      ring

def diskMassForcingH1Lin : L2 unitDisk →ₗ[ℂ] L2Z where
  toFun v := ⟨fun n => (sobWeight n : ℂ) * diskMassForcingCoeff v n,
    memℓp_two_iff_summable.mpr (by
      simpa only [IsSobolevSeq, Real.rpow_one, norm_mul,
        Complex.norm_of_nonneg (sobWeight_pos _).le] using (diskMassForcingCoeff_h1 v).1)⟩
  map_add' v w := by
    apply lp.ext
    funext n
    simp only [diskMassForcingCoeff_add, lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c v := by
    apply lp.ext
    funext n
    change (sobWeight n) * diskMassForcingCoeff (c • v) n =
      c * ((sobWeight n) * diskMassForcingCoeff v n)
    rw [diskMassForcingCoeff_smul]
    ring

include v in
theorem norm_diskMassForcingH1Lin_le :
    ‖diskMassForcingH1Lin v‖ ≤ 2 * ‖v‖ := by
  have hsq : ‖diskMassForcingH1Lin v‖ ^ 2 ≤ (2 * ‖v‖) ^ 2 := by
    rw [norm_sq_L2Z]
    change (∑' n : ℤ, ‖(sobWeight n) * diskMassForcingCoeff v n‖ ^ 2) ≤ _
    simp only [norm_mul, Complex.norm_of_nonneg (sobWeight_pos _).le]
    have h := (diskMassForcingCoeff_h1 v).2
    simp  [sobNormSq] at h
    nlinarith [h]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

def diskMassForcingH1 : L2 unitDisk →L[ℂ] L2Z :=
  diskMassForcingH1Lin.mkContinuous 2 norm_diskMassForcingH1Lin_le

end


end PolyaNeumann

end
