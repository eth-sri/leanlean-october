module
public import OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate
public import OAI.NumberTheory.DirichletL.Moments.FirstEnergy
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstLocalization
open ActualEisensteinCubic EisensteinSchwartzPoisson
open CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion
local notation "O" => ActualEisensteinCubic.O

theorem weighted_fourier_summable (W : 𝓢(ℝ,ℂ)) (k : ℝ) (hk : 0<k)
    (c w : O → ℂ) (B : ℝ) (hc : ∀ h,‖c h‖≤B) (hw : ∀ h,‖w h‖≤1) :
    Summable (fun h : O => w h*c h*paperRadialFourier W (k*normValue h)) := by
  have hs := paperRadialFourier_lattice_summable_norm W k hk
  simp_rw [← normValue_eq_embedding] at hs
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hs.mul_left B)
  intro h
  rw [norm_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right
    ((mul_le_of_le_one_left (norm_nonneg _) (hw h)).trans (hc h)) (norm_nonneg _)

theorem retained_complex_norm (R q : ℝ) : ‖(retainedWeight R q:ℂ)‖≤1 := by
  pm_7640 retainedWeight_nonneg retainedWeight_bounds

theorem discarded_complex_norm (R q : ℝ) : ‖(discardedWeight R q:ℂ)‖≤1 := by
  pm_7640 discardedWeight_nonneg discardedWeight_bounds

theorem lattice_fourier_split (W : 𝓢(ℝ,ℂ)) (k : ℝ) (hk : 0<k)
    (c : O → ℂ) (B : ℝ) (hc : ∀ h,‖c h‖≤B) (R : ℝ) :
    (∑' h : O,c h*paperRadialFourier W (k*normValue h))=
      c 0*paperRadialFourier W 0+
        (∑' h : O,(retainedWeight R (normValue h):ℂ)*c h*paperRadialFourier W (k*normValue h))+
        (∑' h : O,(discardedWeight R (normValue h):ℂ)*c h*paperRadialFourier W (k*normValue h)) := by
  have hs := weighted_fourier_summable W k hk c (fun _ => 1) B hc (by simp)
  simp only [one_mul] at hs
  pm_5561 hr retainedWeight retained_complex_norm
  pm_5561 hd discardedWeight discarded_complex_norm
  rw [hs.tsum_eq_add_tsum_ite 0]
  have hzero : normValue (0:O)=0 := by simp [normValue]
  simp only [hzero,mul_zero]
  rw [add_assoc,← hr.tsum_add hd]
  congr 1
  apply tsum_congr
  intro h
  by_cases hh : h=0
  · subst h
    simp only [ite_true,hzero,
      retainedWeight_zero_nonpos R 0 le_rfl,discardedWeight_zero_nonpos R 0 le_rfl,
      Complex.ofReal_zero,zero_mul,add_zero]
  · rw [ite_eq_right hh]
    have hp : 0<normValue h := norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr hh)
    have he : (retainedWeight R (normValue h):ℂ)+(discardedWeight R (normValue h):ℂ)=1 := by
      exact_mod_cast retained_add_discarded R (normValue h) hp
    grind

def canonicalRetainedTerm (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J=> P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e *
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑' h : O,
      (retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
        paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

def canonicalZeroTerm (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J=> P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e *
    (((k/normValue (a*(b*r)):ℝ):ℂ)*
      (tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
        (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) 0*paperRadialFourier W 0))

def canonicalRetainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalRetainedTerm I J hI hJ E W K Tsec Z ξ

def canonicalZeroPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalZeroTerm I J hI hJ E W K

def retainedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalRetainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

def zeroEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalZeroPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K

end SevenEighths.CenteredMomentFirstLocalization

end

end OAI
