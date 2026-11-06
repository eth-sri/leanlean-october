module
public import OAI.NumberTheory.DirichletL.Moments.Unequal
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

open scoped Classical
namespace SevenEighths.CenteredMomentLocal
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentUnequal

section Domain
variable {A : Type*} [CommRing A] [IsDomain A]

theorem fullCorrelation_equal_divided (q k : A) (hq : q ≠ 0)
    [Fintype (Residue q)] (χ : MulChar (Residue q) ℂ) :
    fullModulusCorrelation q q χ χ (q * k) =
      fullCorrelation (fun x : Residue q => x) (fun y : Residue q => y) χ χ
        (Ideal.Quotient.mk _ k) := by
  have hs (x y : Residue q) :
      scaledResidue q q (q * q) rfl x - scaledResidue q q (q * q) (mul_comm _ _) y =
        Ideal.Quotient.mk _ (q * k) ↔ x - y = Ideal.Quotient.mk _ k := by
    pm_2972
    rw [scaledResidue_congruence, ← map_sub, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    rw [show q * x - q * y - q * k = q * (x - y - k) by ring]
    exact mul_dvd_mul_iff_left hq
  unfold fullModulusCorrelation fullCorrelation
  grind

end Domain

open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve
open CenteredMomentSupportedCorrelation CenteredMomentCanonical CompletedGauss
open CenteredMomentFourier
open ConcretePrimeRowBridge hiding O
local notation "O" => ActualEisensteinCubic.O

section
variable (p : O)
include p
theorem powerReduction_multiplicity (_hp : p ≠ 0) {i : ℕ} (hi : 1 ≤ i)
    [Fintype (Residue p)] [Fintype (Residue (p ^ i))] :
    reductionMultiplicity (frequencyReduction p (p ^ i) (dvd_pow_self p (by omega))) =
      Ideal.absNorm (Ideal.span {p}) ^ (i - 1) := by
  have hcard (a : O) [Fintype (Residue a)] :
      Fintype.card (Residue a) = Ideal.absNorm (Ideal.span {a}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  apply reductionMultiplicity_eq_pow _ (Ideal.Quotient.factor_surjective _) (c := i)
  simp_all
  grind
  simp_all
  grind

theorem equal_prime_power_formula [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {i : ℕ} (hi : 1 ≤ i) (k : O) :
    actualCorrelation (p ^ i) (p ^ i) (supported_power p hp i) (supported_power p hp i)
      (p ^ i * k) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (i - 1) *
        (if p ∣ k then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1
         else if 6 ∣ i then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 2 else -1) := by
  pm_2933
  pm_6379 i
  let : Field (Residue p) := Ideal.Quotient.field (Ideal.span {p})
  let π := frequencyReduction p (p ^ i) (dvd_pow_self p (by omega))
  let χ := actualSextic (Ideal.span {p}) hg ^ i
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective _
  have hχ (x : Residue (p ^ i)) :
      supportedModulusCharacter (p ^ i) (supported_power p hp i) x = χ (π x) := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact supported_power_character_mk p hp hg hi x
  have hred := fullCorrelation_reduction_unit_right π hπ
    (1 : (Residue (p ^ i))ˣ) 1 (Ideal.Quotient.mk _ k) χ χ
  simp only [Units.val_one, map_one, one_mul] at hred
  have hpow : χ = 1 ↔ 6 ∣ i := by
    dsimp only [χ]
    rw [← orderOf_dvd_iff_pow_eq_one, actualSextic_order_six (Ideal.span {p}) hg hchar]
  pm_6572 hk k
  pm_1027
  change fullModulusCorrelation _ _ _ _ _ = _
  rw [fullCorrelation_equal_divided _ _ (pow_ne_zero i hp0)]
  have hχfun : (supportedModulusCharacter (p ^ i) (supported_power p hp i) :
      Residue (p ^ i) → ℂ) = (fun x => χ (π x)) := funext hχ
  rw [hχfun, hred]
  have he : fullCorrelation (fun x : Residue p => x) (fun x => x) χ χ
      (π (Ideal.Quotient.mk _ k)) = localCorrelation χ 1 1 (Ideal.Quotient.mk _ k) := by
    simp only [localCorrelation, one_mul, π, frequencyReduction_mk]
  rw [he]
  rw [localCorrelation_units χ one_ne_zero one_ne_zero, div_self one_ne_zero, map_one, one_mul,
    hk, hpow, hcard]
  have hm : (reductionMultiplicity π : ℂ) = (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (i - 1) := by
    rw [powerReduction_multiplicity p hp0 hi, Nat.cast_pow]
  rw [hm]
  split_ifs <;> rfl

theorem equal_prime_power_unit_norm [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {i : ℕ} (hi : 1 ≤ i) (hi6 : ¬ 6 ∣ i) (k : O) (hk : ¬ p ∣ k) :
    ‖actualCorrelation (p ^ i) (p ^ i) (supported_power p hp i) (supported_power p hp i)
      (p ^ i * k)‖ = (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (i - 1) := by
  rw [equal_prime_power_formula p hp hg hchar hi k, ite_eq_right hk, ite_eq_right hi6]
  simp

theorem equal_prime_power_norm_le [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {i : ℕ} (hi : 1 ≤ i) (k : O) :
    ‖actualCorrelation (p ^ i) (p ^ i) (supported_power p hp i) (supported_power p hp i)
      (p ^ i * k)‖ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ i := by
  pm_2933
  pm_1027
  have hN : (2 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast (show 2 ≤ Ideal.absNorm (Ideal.span {p}) from by
      rw [← hcard]
      exact Fintype.one_lt_card)
  have hsub (a : ℝ) (ha : 0 ≤ a) (haN : a ≤ Ideal.absNorm (Ideal.span {p})) :
      ‖(Ideal.absNorm (Ideal.span {p}) : ℂ) - (a : ℂ)‖ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
    have he : (Ideal.absNorm (Ideal.span {p}) : ℂ) - (a : ℂ) =
        ((Ideal.absNorm (Ideal.span {p}) : ℝ) - a : ℝ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr haN)]
    linarith
  rw [equal_prime_power_formula p hp hg hchar hi k, norm_mul, norm_pow]
  have hnorm : ‖(Ideal.absNorm (Ideal.span {p}) : ℂ)‖ = (Ideal.absNorm (Ideal.span {p}) : ℝ) := by simp
  rw [hnorm]
  have hb : ‖(if p ∣ k then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1
      else if 6 ∣ i then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 2 else -1)‖ ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
    split_ifs
    · simpa using hsub 1 (by norm_num) (by linarith)
    · simpa using hsub 2 (by norm_num) hN
    · simpa using (show (1 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}) by linarith)
  calc
    _ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (i - 1) * Ideal.absNorm (Ideal.span {p}) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [← pow_succ, Nat.sub_add_cancel hi]
end

end SevenEighths.CenteredMomentLocal


end OAI
