module

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

def diskMassForcingScale (m : ℕ) : ℝ :=
  Real.sqrt ((m + 2 : ℕ) : ℝ) / (Real.sqrt (2 * π) * ((m + 1 : ℕ) : ℝ))

def diskMassForcingCoeff (v : L2 (ball 0 1)) : ℤ → ℂ
  | Int.ofNat 0 => 0
  | Int.ofNat (m + 1) => (diskMassForcingScale m : ℂ) *
      ∫ z in ball 0 1, (v : ℂ → ℂ) z * conj z ^ (m + 1)
  | Int.negSucc m => (diskMassForcingScale m : ℂ) *
      ∫ z in ball 0 1, (v : ℂ → ℂ) z * z ^ (m + 1)

private theorem diskMassForcingScale_weight m a :
    (((m + 2 : ℕ) : ℝ) * ‖(diskMassForcingScale m : ℂ) * a‖) ^ 2 ≤
      4 / (2 * π) * (((m + 2 : ℕ) : ℝ) * ‖a‖ ^ 2) := by
  have hweightPos : 0 < ((m + 2 : ℕ) : ℝ) := by positivity
  have hw : (((m + 2 : ℕ) : ℝ) * diskMassForcingScale m) ^ 2 ≤
      4 / (2 * π) * ((m + 2 : ℕ) : ℝ) := by
    rw [mul_pow, diskMassForcingScale, div_pow, mul_pow,
      Real.sq_sqrt hweightPos.le, Real.sq_sqrt Real.two_pi_pos.le]
    calc
      _ ≤ _ :=
        mul_le_mul_of_nonneg_right (by
          calc
            ((m + 2 : ℕ) : ℝ) ^ 2 ≤ (2 * (m + 1 : ℕ)) ^ 2 :=
              (sq_le_sq₀ hweightPos.le (by positivity)).mpr (by
                push_cast
                nlinarith)
            _ = 4 * (m + 1 : ℕ) ^ 2 := by ring) (by positivity)
      _ = _ := by field_simp [(show 0 < ((m + 1 : ℕ) : ℝ) by positivity).ne', Real.pi_ne_zero]
  calc
    _ = ((m + 2 : ℕ) * diskMassForcingScale m) ^ 2 * ‖a‖ ^ 2 := by
      rw [norm_mul, Complex.norm_of_nonneg (by unfold diskMassForcingScale; positivity)]
      ring
    _ ≤ _ :=
      mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = _ := by ring

private theorem diskMassForcing_sector (M : ℕ → ℂ) B
    (hs : Summable (fun m => ((m + 1 : ℕ) : ℝ) * ‖M m‖ ^ 2))
    (hB : (∑' m : ℕ, ((m + 1 : ℕ) : ℝ) * ‖M m‖ ^ 2) ≤ π * B) :
    Summable (fun m => (((m + 2 : ℕ) : ℝ) *
      ‖(diskMassForcingScale m : ℂ) * M (m + 1)‖) ^ 2) ∧
    (∑' m : ℕ, (((m + 2 : ℕ) : ℝ) *
      ‖(diskMassForcingScale m : ℂ) * M (m + 1)‖) ^ 2) ≤ 2 * B := by
  let f : ℕ → ℝ := fun m => ((m + 1 : ℕ) : ℝ) * ‖M m‖ ^ 2
  let e : ℕ → ℝ := fun m => ((m + 2 : ℕ) *
    ‖(diskMassForcingScale m) * M (m + 1)‖) ^ 2
  have hi : Function.Injective (fun m => m + 1) := by
    intro m n h
    change m + 1 = n + 1 at h
    exact Nat.add_right_cancel h
  have ht := hs.comp_injective hi
  have htail : (∑' m : ℕ, f (m + 1)) ≤ π * B :=
    (tsum_comp_le_tsum_of_inj hs (fun m => by positivity) hi).trans hB
  have he m : e m ≤ 4 / (2 * π) * f (m + 1) := by
    simpa only [e, f, Nat.add_assoc] using diskMassForcingScale_weight m (M (m + 1))
  have hse : Summable e := Summable.of_nonneg_of_le (fun m => sq_nonneg _) he
    (ht.mul_left (4 / (2 * π)))
  refine ⟨hse, ?_⟩
  calc
    _ ≤ _ :=
      hse.tsum_le_tsum he (ht.mul_left _)
    _ = _ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by field_simp [Real.pi_ne_zero]; ring

private theorem diskMassForcing_int_halves (a : ℤ → ℝ) b
    (hb : Summable b) (hz : a 0 = 0)
    (hp : ∀ m : ℕ, a ((m + 1 : ℕ) : ℤ) = b (Sum.inl m))
    (hn : ∀ m : ℕ, a (-((m + 1 : ℕ) : ℤ)) = b (Sum.inr m)) :
    Summable a ∧ (∑' n : ℤ, a n) = ∑' j : ℕ ⊕ ℕ, b j := by
  have hbl := hb.comp_injective Sum.inl_injective
  have hbr := hb.comp_injective Sum.inr_injective
  have hp0 : Summable (fun m : ℕ => a m) := (summable_nat_add_iff 1).mp (hbl.congr (fun m => (hp m).symm))
  have hn0 : Summable (fun m : ℕ => a (-(m + 1))) := by
    simpa using hbr.congr (fun m => (hn m).symm)
  refine ⟨Summable.of_nat_of_neg_add_one hp0 hn0, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hp0 hn0, hp0.tsum_eq_zero_add]
  simp [hz]
  calc
    _ = _ := by
      congr 1
      · exact tsum_congr hp
      · apply tsum_congr
        intro m
        simpa using hn m
    _ = _ := (hbl.tsum_sum hbr).symm

theorem diskMassForcingCoeff_h1 (v : L2 (ball 0 1)) :
    IsSobolevSeq 1 (diskMassForcingCoeff v) ∧
      sobNormSq 1 (diskMassForcingCoeff v) ≤ 4 * ‖v‖ ^ 2 := by
  let Mp : ℕ → ℂ := fun m => ∫ z in ball 0 1, v z * conj z ^ m
  let Mn : ℕ → ℂ := fun m => ∫ z in ball 0 1, v z * z ^ m
  have hp := diskMassForcing_sector Mp (‖v‖ ^ 2)
    (disk_area_holomorphic_bessel v).1 (disk_area_holomorphic_bessel v).2
  have hn := diskMassForcing_sector Mn (‖v‖ ^ 2)
    (disk_area_antiholomorphic_bessel v).1 (disk_area_antiholomorphic_bessel v).2
  let bp : ℕ → ℝ := fun m => ((m + 2 : ℕ) *
    ‖(diskMassForcingScale m) * Mp (m + 1)‖) ^ 2
  let bn : ℕ → ℝ := fun m => ((m + 2 : ℕ) *
    ‖(diskMassForcingScale m) * Mn (m + 1)‖) ^ 2
  let b : ℕ ⊕ ℕ → ℝ := Sum.elim bp bn
  let a : ℤ → ℝ := fun n => (sobWeight n * ‖diskMassForcingCoeff v n‖) ^ 2
  have hpos m : a ((m + 1 : ℕ) : ℤ) = b (Sum.inl m) := by
    simp only [a, b, Sum.elim_inl, bp, Mp, diskMassForcingCoeff, sobWeight,
      Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (m + 1) :
        0 ≤ ((m + 1 : ℕ) : ℝ))]
    congr 2
    push_cast
    ring
  have hneg m : a (-(m + 1 : ℕ)) = b (Sum.inr m) := by
    simp only [a, b, Sum.elim_inr, bn, Mn, show -((m + 1 : ℕ) : ℤ) = Int.negSucc m by omega, diskMassForcingCoeff, sobWeight,
      Int.cast_negSucc, abs_neg, abs_of_nonneg (Nat.cast_nonneg (m + 1) :
        0 ≤ ((m + 1 : ℕ) : ℝ))]
    congr 2
    push_cast
    ring
  obtain ⟨ha, hsum⟩ := diskMassForcing_int_halves a b (Summable.sum b hp.1 hn.1) (by simp [a, diskMassForcingCoeff])
    hpos hneg
  refine ⟨?_, ?_⟩
  · simpa only [IsSobolevSeq, Real.rpow_one] using ha
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
          simp [diskMassForcingCoeff]
          rw [← inner_diskHolomorphicArea_eq_integral, ← inner_diskHolomorphicArea_eq_integral,
            inner_smul_right]
          ring
  | negSucc m =>
      simp [diskMassForcingCoeff]
      rw [← inner_diskAntiholomorphicArea_eq_integral, ← inner_diskAntiholomorphicArea_eq_integral,
        inner_smul_right]
      ring

def diskMassForcingH1Lin : L2 (ball 0 1) →ₗ[ℂ] L2Z where
  toFun v := ⟨fun n => (sobWeight n : ℂ) * diskMassForcingCoeff v n,
    memℓp_two_iff_summable.mpr (by
      simpa only [IsSobolevSeq, Real.rpow_one, norm_mul,
        Complex.norm_of_nonneg (sobWeight_pos _).le] using (diskMassForcingCoeff_h1 v).1)⟩
  map_add' v w := by
    apply lp.ext
    funext n
    change (sobWeight n : ℂ) * diskMassForcingCoeff (v + w) n = _
    simp only [diskMassForcingCoeff_add, lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c v := by
    apply lp.ext
    funext n
    change (sobWeight n : ℂ) * diskMassForcingCoeff (c • v) n =
      c * ((sobWeight n : ℂ) * diskMassForcingCoeff v n)
    rw [diskMassForcingCoeff_smul]
    ring

theorem norm_diskMassForcingH1Lin_le v :
    ‖diskMassForcingH1Lin v‖ ≤ 2 * ‖v‖ := by
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (by
    rw [norm_sq_L2Z]
    change (∑' n : ℤ, ‖(sobWeight n : ℂ) * diskMassForcingCoeff v n‖ ^ 2) ≤ _
    simp only [norm_mul, Complex.norm_of_nonneg (sobWeight_pos _).le]
    have h := (diskMassForcingCoeff_h1 v).2
    simp only [sobNormSq, Real.rpow_one] at h
    nlinarith [h])

def diskMassForcingH1 : L2 (ball 0 1) →L[ℂ] L2Z :=
  diskMassForcingH1Lin.mkContinuous 2 norm_diskMassForcingH1Lin_le


end PolyaNeumann

end
