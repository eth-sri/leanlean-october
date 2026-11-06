module
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalWholeSource
public import OAI.NumberTheory.DirichletL.Moments.SourceRectangleEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentExceptionalMaskedSource
open HeckeFamily UniqueFactorizationMonoid CenteredMomentEligibleEnergy CenteredMomentDivisorRowEnergy CenteredMomentActiveAllocation CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell CenteredMomentExceptionalWholeSource CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentSourceRow CenteredMomentRowNorm
local notation "O" => HeckeFamily.O
universe u
variable {ι κ:Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def maskedAmplitude (s:Data ι)(D:Ideal O)(z:O):ℂ:=
  (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    maskedRectangle s.η s.m s.A z s.t s.slots s.coefficient D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂

theorem maskedAmplitude_eq (s:Data ι)(D:Ideal O)(hD:Squarefree D)(z:O):
    maskedAmplitude s D z=∑a∈s.toSource.active D,amplitude s D a z:=by
  unfold maskedAmplitude
  rw [masked_eq_active_allocations s.η s.m s.A z s.t s.slots s.coefficient D hD
    s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos,Finset.mul_sum]
  rfl

theorem paired_masked_le (s:Data ι)(v:Data κ)(D:Ideal O)(hD:Squarefree D)(rows:Finset O):
    (∑z∈rows,‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
      ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖:=by
  calc
    _≤∑z∈rows,(∑a∈s.toSource.active D,‖amplitude s D a z‖)*
        (∑b∈v.toSource.active D,‖amplitude v D b z‖):=by
      apply Finset.sum_le_sum
      intro z hz
      rw [maskedAmplitude_eq s D hD,maskedAmplitude_eq v D hD]
      exact mul_le_mul (norm_sum_le _ _) (norm_sum_le _ _) (norm_nonneg _)
        (Finset.sum_nonneg (fun a _=>norm_nonneg _))
    _=_:=by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s:=rows) (t:=s.toSource.active D)]
      exact Finset.sum_comm

theorem whole_masked_le (s:Data ι)(v:Data κ)(Ds:Finset (Ideal O))(rows:Finset O):
    (∑D∈Ds,‖(moebius D:ℂ)‖*∑z∈rows,‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
      ∑D∈Ds,‖(moebius D:ℂ)‖*∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖:=by
  apply Finset.sum_le_sum
  intro D hD
  by_cases hμ:(moebius D:ℂ)=0
  · simp [hμ]
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply paired_masked_le s v D
    exact CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero D hμ

end SevenEighths.CenteredMomentExceptionalMaskedSource

end

end OAI
