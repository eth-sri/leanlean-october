module
public import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationEnergy
public import OAI.NumberTheory.DirichletL.Hecke.DetectorRowwisePlain
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge HeckeDetectorRowwise

def scaleProfile (W : ℝ→ℂ) (y : ℝ) : ℂ := -W y/2-(y : ℂ)*deriv W y

def scaleSum (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O)) (l : ℝ) : ℂ :=
  Complex.exp (-(l : ℂ)/2)*∑ J∈S,
    coefficient χ true J*W ((J.absNorm : ℝ)*Real.exp (-l))

theorem scaleProfile_continuous (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    Continuous (scaleProfile W) := by
  have hd := hW.continuous_deriv (by simp)
  unfold scaleProfile
  fun_prop

theorem scaleProfile_support (W : ℝ→ℂ) (a b : ℝ)
    (hs : Function.support W⊆Icc a b) : Function.support (scaleProfile W)⊆Icc a b := by
  intro y hy
  by_contra hn
  have hw : W y=0 := by by_contra hw; simp_all
  have hd : deriv W y=0 := by
    apply deriv_of_notMem_tsupport
    exact fun h => hn ((closure_minimal hs isClosed_Icc) h)
  exact hy (by simp [scaleProfile,hw,hd])

theorem scaleSum_continuous (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Continuous W) : Continuous (scaleSum χ W S) := by
  unfold scaleSum
  fun_prop

theorem scaleSum_deriv (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Differentiable ℝ W) (l : ℝ) :
    HasDerivAt (scaleSum χ W S) (scaleSum χ (scaleProfile W) S l) l := by
  pm_3126
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun t => coefficient χ true J*W ((J.absNorm : ℝ)*Real.exp (-t)))
        (coefficient χ true J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))) l := by
    pm_6697
    convert ((hW _).hasDerivAt.scomp l hy).const_mul (coefficient χ true J) using 1
    · rfl
    · change coefficient χ true J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))=
        coefficient χ true J*(((J.absNorm : ℝ)*(Real.exp (-l)*(-1))) •
          deriv W ((J.absNorm : ℝ)*Real.exp (-l)))
      rw [Complex.real_smul]
      push_cast
      ring
  pm_7491
  · ext t
    simp only [scaleSum,Pi.mul_apply,Finset.sum_apply]
  · dsimp [scaleSum,scaleProfile]
    pm_1547

theorem scale_normalization (l : ℝ) :
    ((Real.exp l : ℝ) : ℂ)^(-(1/2 : ℂ))=Complex.exp (-(l : ℂ)/2) := by
  pm_6378 l
  congr 1
  ring

theorem scaleSum_eq_polynomial (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (l : ℝ) (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    scaleSum χ W S l=polynomial χ true W (Real.exp l) 0 0 := by
  rw [polynomial_eq_finite χ true W (Real.exp l) 0 0 S hc,scale_normalization]
  pm_545 HeckeDyadic.shift ofReal_zero zero_mul sub_self neg_zero Complex.cpow_zero mul_one
  unfold scaleSum
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Real.exp_neg,div_eq_mul_inv]

end SevenEighths.HeckeInverseAmplification

end

end OAI
