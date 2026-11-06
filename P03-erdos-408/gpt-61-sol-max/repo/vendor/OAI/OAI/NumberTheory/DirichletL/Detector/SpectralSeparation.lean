module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.Row
public import OAI.NumberTheory.DirichletL.Detector.PhysicalCoefficient

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted


def baseRowCoefficient (η : HeckeFamily.Character) (Xi : ActualEisensteinCubic.O →* ℂ)
    (s ) (hs : Supported (Ideal.span {s}))  :=
  targetMonoid η * InitialMeanSquare.conjugateMonoid Xi * reciprocityPhaseMonoid s hs

lemma spectralSummand_mul_fixed_twist  S   D I J 
     φ Ψ   t  :
    spectralSummand S D (φ*Ψ) t I J =
      φ (completedIndex I J) * spectralSummand S D Ψ t I J := by
  have hc (η : ActualEisensteinCubic.O →* ℂ) : cubeWeight η J =
      star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3 *
        η (primaryGenerator J)^3 / (Ideal.absNorm J:ℂ) := rfl
  unfold spectralSummand
  rw [hc, hc]
  simp only [columnWeight, MonoidHom.mul_apply, map_mul, map_pow, mul_pow, completedIndex]
  ring

theorem spectralSummand_row_separation  S   D I J 
     η   Xi   s 
     hs   m   t  :
    spectralSummand S D (rowCoefficient η Xi s hs m) t I J =
      idealRowHom m (Ideal.span {completedIndex I J}) *
        spectralSummand S D (baseRowCoefficient η Xi s hs) t I J := by
  have hr : rowCoefficient η Xi s hs m =
      ((idealRowHom m).toMonoidHom.comp principalIdealHom.toMonoidHom) *
        baseRowCoefficient η Xi s hs := by
    change _ * _ = _ * _
    exact mul_comm _ _
  rw [hr, spectralSummand_mul_fixed_twist]
  rfl

theorem spectralSummand_zero_completedIndex  S   D I J 
     Ψ   t  (hz : completedIndex I J=0) :
    spectralSummand S D Ψ t I J=0 := by
  rcases mul_eq_zero.mp hz with hI | hJ
  · simp_all [squarefreeGaussCoefficient, spectralSummand, columnWeight]
  · have hJ' : primaryGenerator J=0 := (pow_eq_zero_iff (by decide : 3≠0)).mp hJ
    have hc : cubeWeight Ψ J=0 := by
      change star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3 *
        Ψ (primaryGenerator J)^3 / (Ideal.absNorm J:ℂ)=0
      simp [hJ', FiniteGaussPhase.angularFactor]
    simp only [spectralSummand, hc, mul_zero, zero_mul]

end SevenEighths.ProbeRow
end

end OAI
