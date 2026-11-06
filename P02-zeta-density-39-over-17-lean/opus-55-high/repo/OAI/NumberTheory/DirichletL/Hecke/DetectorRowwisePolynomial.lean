module
public import OAI.NumberTheory.DirichletL.Hecke.DetectorRowwise
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Set Complex
namespace SevenEighths.HeckeDetectorRowwisePolynomial
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge

def logProfile (W : ℝ→ℂ) (x : ℝ) : ℂ := (Real.log x : ℂ)*W x

section
variable (W : ℝ→ℂ)
include W
theorem logProfile_cover (D : ℝ) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    ∀ J : Ideal O, J≠0 → logProfile W ((J.absNorm : ℝ)/D)≠0 → J∈S := by
  intro J hJ hw
  exact hc J hJ (fun hz => hw (by simp [logProfile,hz]))

theorem logProfile_support :
    Function.support (logProfile W)⊆Function.support W := by
  intro x hx hw
  exact hx (by simp [logProfile,hw])

theorem logProfile_smooth (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (logProfile W) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have he : logProfile W =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds ha] with y hy
      pm_1321 hn hs logProfile
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (Real.contDiffAt_log.mpr hx)).mul hW.contDiffAt
end

section
variable (x σ freq : ℝ) (hx : 0<x)
include x σ freq hx
lemma power_sigma_deriv :
    HasDerivAt (fun u : ℝ => (x : ℂ)^(-HeckeDyadic.shift u freq))
      (-(Real.log x : ℂ)*(x : ℂ)^(-HeckeDyadic.shift σ freq)) σ := by
  have hd := (((hasDerivAt_id (σ : ℂ)).neg).add_const ((freq : ℂ)*I)).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  pm_6708
  · ext u
    congr 1
    pm_3543 HeckeDyadic.shift neg_sub Pi.neg_apply id_eq
  · have he : -HeckeDyadic.shift σ freq= -(σ : ℂ)+(freq : ℂ)*I := by unfold HeckeDyadic.shift; ring
    rw [he]
    simp only [Pi.neg_apply,id_eq]
    ring

lemma power_freq_deriv :
    HasDerivAt (fun u : ℝ => (x : ℂ)^(-HeckeDyadic.shift σ u))
      (I*(Real.log x : ℂ)*(x : ℂ)^(-HeckeDyadic.shift σ freq)) freq := by
  have hd := (((hasDerivAt_id (freq : ℂ)).mul_const I).const_add (-(σ : ℂ))).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  pm_6708
  · ext u
    congr 1
    simp [HeckeDyadic.shift]
    ring
  · have he : -HeckeDyadic.shift σ freq= -(σ : ℂ)+(freq : ℂ)*I := by unfold HeckeDyadic.shift; ring
    rw [he]
    simp only [id_eq]
    ring
end

section
variable (χ : Character) (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D) (S : Finset (Ideal O)) (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S)
include χ inv W D σ freq hD S hc
theorem polynomial_sigma_deriv :
    HasDerivAt (fun u => polynomial χ inv W D u freq)
      (-polynomial χ inv (logProfile W) D σ freq) σ := by
  pm_3141
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun u => coefficient χ inv J*W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift u freq))
      (-coefficient χ inv J*logProfile W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq)) σ := by
    pm_6148 neg_zero σ
    pm_3140
    pm_1348 power_sigma_deriv
  pm_3142
  all_goals simp only [Finset.sum_apply,neg_mul,Finset.sum_neg_distrib,mul_neg]

theorem polynomial_freq_deriv :
    HasDerivAt (fun u => polynomial χ inv W D σ u)
      (I*polynomial χ inv (logProfile W) D σ freq) freq := by
  pm_3141
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun u => coefficient χ inv J*W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ u))
      (I*(coefficient χ inv J*logProfile W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq))) freq := by
    pm_6148 mul_zero freq
    pm_3140
    pm_1348 power_freq_deriv
  pm_3142
  all_goals simp only [Finset.sum_apply,←Finset.mul_sum]
  ring
end

theorem polynomial_continuous (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    Continuous (fun p : ℝ×ℝ => polynomial χ inv W D p.1 p.2) := by
  simp_rw [polynomial_eq_finite χ inv W D _ _ S hc]
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro J hJ
  by_cases hz : J=0
  · subst J
    simp only [coefficient_zero,zero_mul]
    exact continuous_const
  pm_3140
  apply Continuous.const_mul
  apply Continuous.const_cpow _ (Or.inl (Complex.ofReal_ne_zero.mpr hn.ne'))
  unfold HeckeDyadic.shift
  fun_prop

end SevenEighths.HeckeDetectorRowwisePolynomial

end

end OAI
