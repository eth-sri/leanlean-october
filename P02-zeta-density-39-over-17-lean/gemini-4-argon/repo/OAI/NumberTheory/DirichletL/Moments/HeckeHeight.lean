module
public import OAI.NumberTheory.DirichletL.Moments.HeckeTwist

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeHeight
open HeckeFamily CenteredMomentHeckeVolume CenteredMomentHeckeCancellation CenteredMomentHeckeTwist CenteredMomentLattice CenteredMomentMask CenteredMomentTwist CenteredMomentHeight QuadraticInitialBound EisensteinSchwartzPoisson

def rowTwistedSum (η : Character) (m A₀ z : O) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  ∑' I : Ideal O, (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A₀*z)) I)*
    (Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)

theorem rowTwistedSum_eq (η χ : Character) (m A₀ z : O)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)
    (W : ℝ → ℂ) (t X : ℝ) :
    rowTwistedSum η m A₀ z W t X=twistedIdealSum χ W t X := by
  apply tsum_congr
  intro I
  have he := HeckeRowClosure.idealCoeff_eq_row η χ m 1 (A₀*z) hrow I
  simp only [one_pow,mul_one] at he
  rw [he]
