module

public import OAI.NumberTheory.DirichletL.Moments.ExceptionalMaskedSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentExceptionalAsymmetricSource
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentDetectorDictionary
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentExceptionalAllocationShell CenteredMomentExceptionalWholeSource
open CenteredMomentExceptionalMaskedSource UniqueFactorizationMonoid CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

lemma reduction_ge_one {α:Type u} [Fintype α] [DecidableEq α]
    (s:Data α)(hP:∀i,1≤s.P i)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2))):1≤formalReductionFactor D a s.P:=by
  have hn (j:Fin 2):(1:ℝ)≤Ideal.absNorm (selectedPlain D a j):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hn 0) (hn 1))
    (Finset.one_le_prod₀ (fun i _=>hP i))

lemma raw_cap_weight {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(hP:∀i,1≤s.P i)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2)))(Z r:ℝ)(hZ:1<Z):
    exceptionalWeight s.toSource v.toSource D a b Z r=
      exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
  have hd:0≤Real.logb Z (formalReductionFactor D a s.P):=
    Real.logb_nonneg hZ (reduction_ge_one s hP D a)
  unfold exceptionalWeight
  congr 2
  by_cases hr:0≤r
  · rw [max_eq_left hr]
  · have h0:r≤0:=le_of_not_ge hr
    rw [max_eq_right h0,max_eq_right (by linarith:r-Real.logb Z (formalReductionFactor D a s.P)≤0),
      max_eq_right (by linarith:0-Real.logb Z (formalReductionFactor D a s.P)≤0)]

end SevenEighths.CenteredMomentExceptionalAsymmetricSource

end

end OAI
