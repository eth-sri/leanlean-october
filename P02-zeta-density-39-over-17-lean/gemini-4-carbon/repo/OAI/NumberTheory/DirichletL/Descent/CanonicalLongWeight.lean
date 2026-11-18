module
public import OAI.NumberTheory.DirichletL.Descent.CanonicalLongNormalization
public import OAI.NumberTheory.DirichletL.Descent.TripleMass

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers InverseInitialClippedColumns IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem second_label_weight_uniform (K:ℕ)(L eps:ℝ)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀(Z V:ℝ),1≤Z→V≤L→∀I:Ideal O,I≠0→
      (I.absNorm:ℝ)≤Z^V→secondLabelWeight K I≤C*Z^eps := by
  let delta:=eps/(L+1)
  have hd:0<delta:=div_pos heps (by linarith)
  obtain ⟨C,hC,hh⟩:=ideal_divisor_power_small (9+4*K) delta hd
  refine ⟨C,hC,?_⟩
  intro Z V hZ hV I hI hnorm
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hbudget:L*delta≤eps := by
    have he:(L+1)*delta=eps:=by dsimp [delta];field_simp
    nlinarith
  calc
    secondLabelWeight K I≤C*(I.absNorm:ℝ)^delta:=hh I hI
    _≤C*(Z^L)^delta:=by
      gcongr
      exact hnorm.trans (Real.rpow_le_rpow_of_exponent_le hZ hV)
    _=C*Z^(L*delta):=by rw [←Real.rpow_mul hz.le]
    _≤C*Z^eps:=by gcongr

end SevenEighths.InverseMoment

end

end OAI
