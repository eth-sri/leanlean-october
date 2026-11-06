module
public import OAI.NumberTheory.DirichletL.Moments.ReflectedAnnuli
public import OAI.NumberTheory.DirichletL.Moments.ReflectionDeletion
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectedSeries
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli
open CenteredMomentComparisonReflection CenteredMomentReflectionDeletion
open EisensteinSchwartzPoisson
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

def dyadicIdealTerm (η : Character) (F : ℝ→ℂ) (Y : ℝ) (I : NI) (n : ℤ) : ℂ :=
  idealCoeff η I.val*(dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*F ((I.val.absNorm:ℝ)/Y)

section
variable (η : Character) (F : ℝ→ℂ)
include η F
lemma dyadicIdealTerm_norm (Y : ℝ) (I : NI) (n : ℤ) :
    ‖dyadicIdealTerm η F Y I n‖=
      dyadicWeight n ((I.val.absNorm:ℝ)/Y)*‖idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖ := by
  unfold dyadicIdealTerm
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (dyadicWeight_bounds _ _).1,norm_mul]
  ring

lemma dyadic_ideal_absolute (hF : DecayTwo F)
    (Y : ℝ) (hY : 0<Y) :
    Summable (fun p : NI×ℤ=>‖dyadicIdealTerm η F Y p.1 p.2‖) := by
  pm_7792
  simp_rw [dyadicIdealTerm_norm]
  constructor
  · intro I
    exact (dyadicWeight_summable _).mul_right _
  · simp_rw [tsum_mul_right]
    have he (I : NI) : (∑'n : ℤ,dyadicWeight n ((I.val.absNorm:ℝ)/Y))=1 :=
      dyadicWeight_partition _ (div_pos (HeckeDyadic.norm_pos I) hY)
    simp_rw [he,one_mul]
    exact (plain_summable η F hF Y hY).norm
end

end SevenEighths.CenteredMomentReflectedSeries

end

end OAI
