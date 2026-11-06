module

public import OAI.NumberTheory.DirichletL.Moments.FirstSecondLossParameters
public import OAI.NumberTheory.DirichletL.Moments.FirstMixedMainError

@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentSuccessorPaidParameters


def edge (epsChild epsRemove delta epsilon delta1 delta2 theta kappa mesh : ℝ) : ℝ :=
  epsChild+epsRemove+2*delta+epsilon+delta2+delta1/6+kappa*mesh+7*theta/3

def exceptional (sigma deltafr epsilon delta B theta : ℝ) : ℝ :=
  3*sigma+5*deltafr/6+2*epsilon+2*delta+2*(5*B+1)*theta

def diagonal (sigma delta reserve epsilon A : ℝ) : ℝ :=
  2*sigma+delta+reserve+epsilon*A

lemma mesh_cost (kappa reserve : ℝ) (hk : 0≤kappa) (hr : 0≤reserve) :
    kappa*(reserve/(kappa+1))≤reserve := by
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0<kappa+1)).mpr
  nlinarith

end SevenEighths.CenteredMomentSuccessorPaidParameters

end

end OAI
