module
public import OAI.NumberTheory.DirichletL.Moments.SecondWholeKernel
public import OAI.NumberTheory.DirichletL.Moments.SectorLocalization
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondTail
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson CompletedGauss
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSupportedCorrelation CenteredMomentSecondWholeKernel
local notation "O" => ActualEisensteinCubic.O

theorem actual_second_kernel_reference (I J : Ideal O) (hI : I≠0) (hJ : J≠0)
    (K X H Tsec : ℝ) (hK : 0<K) (hX : 0<X)
    (hi : (Ideal.absNorm I:ℝ)≤Real.exp H*X) (hj : (Ideal.absNorm J:ℝ)≤Real.exp H*X)
    (hsec : X^2/K≤Tsec) :
    kernelReference Tsec H≤K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
  pm_6453
  pm_268 hNi CenteredMomentFirstScale.norm_pos I hI hNj J hJ
  have hprod : (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)≤Real.exp (2*H)*X^2 := by
    apply (mul_le_mul hi hj hNj.le (by positivity)).trans_eq
    rw [show 2*H=H+H by ring,Real.exp_add]
    ring
  unfold kernelReference
  apply (le_div_iff₀ (mul_pos hNi hNj)).mpr
  calc
    _ ≤ (Real.exp (-2*H)/Tsec)*(Real.exp (2*H)*X^2) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = X^2/Tsec := by
      rw [show -2*H=-(2*H) by ring,Real.exp_neg]
      field_simp
    _ ≤ K := (div_le_iff₀ hT).mpr (by simpa only [mul_comm] using (div_le_iff₀ hK).mp hsec)

def secondDiscardedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
    ∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
      actualCorrelation (primaryGenerator I) (primaryGenerator J)
        ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) (-h)*
      paperRadialFourier W (K*‖eisEmbedding h‖^2/
        ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2)

theorem second_discarded_pair_bound (Adec : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
        (K X H Tsec Z Csec ξ : ℝ),0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp H*X → (Ideal.absNorm J:ℝ)≤Real.exp H*X →
      X^2/K≤Tsec → (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖secondDiscardedPair I J hI hJ W K Tsec Z ξ‖≤
        K*(Real.exp H*X)^2*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z ^(ξ/4))^Adec) := by
  pm_3085 s C hC ht actual_discarded_second_tail Adec
  intro W I J hI hJ K X H Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  pm_6453
  have hb := ht W Tsec Z Csec H ξ (K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))
    hT hZ hCs hthreshold (actual_second_kernel_reference I J hI.1 hJ.1 K X H Tsec hK hX hi hj hsec)
    (primaryGenerator I) (primaryGenerator J)
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ)
  have he (h : O) : K*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2=
      (K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*normValue h := by
    pm_6042
  pm_7884 hu I hI
  pm_7884 hv J hJ
  rw [hu,hv] at hb
  have hNi : (1:ℝ)≤Ideal.absNorm I := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hNj : (1:ℝ)≤Ideal.absNorm J := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ.1)
  have hroot : 1≤Real.sqrt (Ideal.absNorm I:ℝ)*Real.sqrt (Ideal.absNorm J:ℝ) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr hNi) (Real.one_le_sqrt.mpr hNj)
  have hnorm : ‖(K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))‖≤K := by
    rw [norm_div,norm_mul]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hK,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_self hK.le hroot
  unfold secondDiscardedPair
  simp_rw [he]
  pm_8685 hnorm hK.le
  have hprod := mul_le_mul hi hj (Nat.cast_nonneg _) (by positivity : 0≤Real.exp H*X)
  have hfac : 0≤(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
      ((min 1 (kernelReference Tsec H))^2*(1+Z ^(ξ/4))^Adec) := by positivity
  have hb' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod hfac) hK.le
  convert hb' using 1 <;> ring

end SevenEighths.CenteredMomentSecondTail

end

end OAI
