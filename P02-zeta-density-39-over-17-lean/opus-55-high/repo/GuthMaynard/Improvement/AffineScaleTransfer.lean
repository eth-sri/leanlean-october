module
public import GuthMaynard.Improvement.MixedHeightTheorem
public import GuthMaynard.Improvement.FourierInputClass
import WeylPort.Analytic.RealLaplace

public section
open MeasureTheory
open scoped SchwartzMap
namespace GuthMaynard.Improvement
open GuthMaynard.NativeMoment

theorem fourier_sup_family_mono (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    {T S : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S) {f : 𝓢(ℝ, ℝ)}
    (hf : FourierSupFamily D T f) : FourierSupFamily D S f := by
  intro β hβ n ξ hξ
  have hd := hD β n
  have hS : 0 ≤ S := hT.trans hTS
  exact (hf β hβ n ξ hξ).trans (by gcongr)

set_option maxHeartbeats 600000 in
/-- Real outer scales and arbitrary fixed multiplicative shell/translation
allowances. Only the support convention remains canonical. -/
theorem mixed_affine_real_scales (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    (L : ℝ) (hL : 1 ≤ L) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T R K : ℝ) (f : 𝓢(ℝ, ℝ)) (M₁ M₂ M₃ : ℕ),
      2 ≤ T → 1 ≤ K → K ≤ R → R ≤ T^4 →
      (∀ x, 0 ≤ f x) → GMAffineSourceSupported f → FourierSupFamily D T f →
      0 < M₁ → 0 < M₂ → 0 < M₃ → (M₁:ℝ) ≤ L*R → (M₂:ℝ) ≤ L*K → (M₃:ℝ) ≤ L*R →
      gmAffineTransformIntegral f M₁ M₂ M₃ ≤ C*T^ε*
        (R^2*K^4*(∫ x, f x)^2+R*K^3*(∫ x, f x^2)) := by
  obtain ⟨C,hC,hbound⟩ := mixed_height_affine (massProfile D) (massProfile_nonneg D hD) hε
  let P := L+1
  have hP : 1 ≤ P := by dsimp only [P]; linarith
  have hPp : 0 < P := zero_lt_one.trans_le hP
  refine ⟨C*P^ε*P^6,by positivity,?_⟩
  intro T R K f M₁ M₂ M₃ hT hK hKR hRT hf hs hp h₁ h₂ h₃ h₁R h₂K h₃R
  pm_6304
  have hLp : 0 < L := by linarith
  let RN := ⌈L*R⌉₊
  let KN := ⌈L*K⌉₊
  pm_5322 hRN RN R hR
  pm_5322 hKN KN K hK
  have hKNp : 0 < KN := Nat.ceil_pos.mpr (by positivity)
  have hKNRN : KN ≤ RN := Nat.ceil_mono (by gcongr)
  pm_8800 h₁N M₁ RN h₁R.trans
  pm_8800 h₂N M₂ KN h₂K.trans
  pm_8800 h₃N M₃ RN h₃R.trans
  have hTS : T ≤ P*T := le_mul_of_one_le_left hTp.le hP
  have hS : 2 ≤ P*T := hT.trans hTS
  have hRNT : (RN:ℝ) ≤ (P*T)^4 := by
    calc
      _ ≤ P*R := hRN
      _ ≤ P*T^4 := by gcongr
      _ ≤ P^4*T^4 := by gcongr; simpa only [pow_one] using pow_le_pow_right₀ hP (show 1 ≤ 4 by decide)
      _ = _ := by ring
  have hpS := fourier_sup_family_mono D hD hTp.le hTS hp
  have hh := hbound (P*T) f RN KN M₁ M₂ M₃ hS hf hs
    (fourier_sup_family_to_height_mass D hD (by positivity) f hf hpS)
    hKNp hKNRN hRNT h₁ h₂ h₃ h₁N h₂N h₃N
  pm_4518 hmass x f integral_nonneg hf
  pm_4604
  have hW : (RN:ℝ)^2*(KN:ℝ)^4*(∫ x, f x)^2+(RN:ℝ)*(KN:ℝ)^3*(∫ x, f x^2) ≤
      P^6*(R^2*K^4*(∫ x, f x)^2+R*K^3*(∫ x, f x^2)) := by
    calc
      _ ≤ (P*R)^2*(P*K)^4*(∫ x, f x)^2+(P*R)*(P*K)^3*(∫ x, f x^2) := by gcongr
      _ = P^6*(R^2*K^4*(∫ x, f x)^2)+P^4*(R*K^3*(∫ x, f x^2)) := by ring
      _ ≤ P^6*(R^2*K^4*(∫ x, f x)^2)+P^6*(R*K^3*(∫ x, f x^2)) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hP (show 4 ≤ 6 by decide)) (by positivity))
      _ = _ := by ring
  apply hh.trans
  calc
    _ ≤ C*(P*T)^ε*(P^6*(R^2*K^4*(∫ x, f x)^2+R*K^3*(∫ x, f x^2))) := by gcongr
    _ = _ := by rw [Real.mul_rpow hPp.le hTp.le]; ring

end GuthMaynard.Improvement
