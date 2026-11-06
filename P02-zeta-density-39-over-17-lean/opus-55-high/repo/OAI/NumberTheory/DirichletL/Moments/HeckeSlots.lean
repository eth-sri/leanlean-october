module
public import OAI.NumberTheory.DirichletL.Moments.HeckeHeight
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeSlots
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentCounting CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

def rowSlot (η : Character) (m A z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t : ℝ) : ℂ :=
  ∑ P ∈ S, β P * (idealCoeff η P * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) P) *
    (Ideal.absNorm P:ℂ)^(Complex.I*t)

section
variable (η : Character) (m A z : O)
include η m A z
theorem row_twisted_coefficient_norm (t : ℝ)
    (P : Ideal O) (hP : P ≠ 0) :
    ‖(idealCoeff η P * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) P) *
      (Ideal.absNorm P:ℂ)^(Complex.I*t)‖ ≤ 1 := by
  have hn : 0 < (Ideal.absNorm P:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP)
  rw [norm_mul, norm_mul, show (Ideal.absNorm P:ℂ)=((Ideal.absNorm P:ℝ):ℂ) by simp,
    norm_real_imaginary_power _ t hn, mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η P)).trans
    (CanonicalRowCompletion.idealRowHom_norm _ _)

theorem rowSlot_bound (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t H M : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hβ : ∀ P ∈ S, ‖β P‖ ≤ M)
    (hN : ∀ P ∈ S, β P ≠ 0 → (Ideal.absNorm P:ℝ) ≤ H) :
    ‖rowSlot η m A z S β t‖ ≤ 128*M*H := by
  let f : Ideal O → ℂ := fun P => if P ∈ S then
    β P * (idealCoeff η P * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) P) *
      (Ideal.absNorm P:ℂ)^(Complex.I*t) else 0
  have hf0 : f 0=0 := by simp only [f, map_zero, zero_mul, mul_zero, ite_self]
  have hf : ∀ P, ‖f P‖ ≤ M := by
    intro P
    by_cases hP : P ∈ S
    · by_cases hP0 : P=0
      · rw [hP0,hf0,norm_zero]; exact hM
      · dsimp only [f]; rw [ite_eq_left hP, mul_assoc, norm_mul]
        exact (mul_le_mul (hβ P hP) (row_twisted_coefficient_norm η m A z t P hP0)
          (norm_nonneg _) hM).trans_eq (mul_one M)
    · simp only [f,ite_eq_right hP,norm_zero]; exact hM
  have hsup : ∀ P, f P ≠ 0 → (Ideal.absNorm P:ℝ) ≤ H := by
    intro P hP
    have hm : P ∈ S := by by_contra hn; exact hP (by simp only [f,ite_eq_right hn])
    exact hN P hm (by intro hz; exact hP (by simp only [f,ite_eq_left hm,hz,zero_mul]))
  have he : (∑' P, f P)=rowSlot η m A z S β t := by
    rw [tsum_eq_sum (s := S) (fun P hP => by simp only [f,ite_eq_right hP])]
    unfold rowSlot
    exact Finset.sum_congr rfl (fun P hP => by simp only [f,ite_eq_left hP])
  rw [← he]
  exact norm_tsum_ideal_ball f H M hH hM hf0 hf hsup
end

variable {ι : Type*} [Fintype ι]

theorem whole_product_normalization (R : ℂ) (q : ι → ℂ) (k p : ι → ℝ)
    (D T L : ℝ) (hD : 0 ≤ D) (hT : 0 < T) (hL : 0 < L)
    (_hk : ∀ i, 0 ≤ k i) (hp : ∀ i, 0 < p i)
    (hq : ∀ i, ‖q i‖ ≤ k i*p i)
    (hR : ‖(Real.sqrt T:ℂ)⁻¹*R‖ ≤ D *(Real.sqrt T/L)) :
    ‖(Real.sqrt (T*∏ i,p i):ℂ)⁻¹*(R*∏ i,q i)‖ ≤
      D *(∏ i,k i)*(Real.sqrt (T*∏ i,p i)/L) := by
  pm_8643 hP p hp
  have hTP : 0 < T*∏ i,p i := mul_pos hT hP
  pm_4891 hsT T hT
  have hsTP : 0 < Real.sqrt (T*∏ i,p i) := Real.sqrt_pos.2 hTP
  have hQ : ‖∏ i,q i‖ ≤ (∏ i,k i)*(∏ i,p i) := by
    rw [norm_prod,← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hq i)
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hsT.le] at hR
  have hR' : ‖R‖ ≤ D *T/L := by
    have h := mul_le_mul_of_nonneg_left hR hsT.le
    rw [← mul_assoc,mul_inv_cancel₀ hsT.ne',one_mul] at h
    have hs := Real.sq_sqrt hT.le
    convert h using 1
    calc
      D *T/L = D *(Real.sqrt T)^2/L := by rw [hs]
      _ = _ := by ring
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hsTP.le,norm_mul]
  calc
    _ ≤ (Real.sqrt (T*∏ i,p i))⁻¹*((D *T/L)*((∏ i,k i)*(∏ i,p i))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hR' hQ (norm_nonneg _) (by positivity)) (inv_nonneg.mpr hsTP.le)
    _ = _ := by
      have hs := Real.sq_sqrt hTP.le
      field_simp
      rw [hs]

def centeredSlotRow (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (p : ι → ℝ) (t X₁ X₂ Y₁ Y₂ T : ℝ) : ℂ :=
  (Real.sqrt (T*∏ i,p i):ℂ)⁻¹ *
    ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
      rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)*
      ∏ i,rowSlot η m A z (S i) (β i) t)

end SevenEighths.CenteredMomentHeckeSlots

end

end OAI
