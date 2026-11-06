module

public import OAI.NumberTheory.DirichletL.Hecke.PrimeRay
public import OAI.NumberTheory.DirichletL.Hecke.RowClosure
public import OAI.NumberTheory.DirichletL.Hecke.Conjugation

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate BigOperators
namespace SevenEighths.HeckePrimeRow
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem identityClass_coprime {I : Ideal O} (hI : I∈RayQuotient.identityClass M H) :
    IsCoprime I M := by
  obtain ⟨hI,a,ha,u,hu,huH⟩ := hI
  rw [←ha]
  exact (IdealCharacter.isUnit_mk_iff_isCoprime M a).mp (hu ▸ u.isUnit)

omit [NeZero M] in
theorem identityClass_coprime_larger {I J : Ideal O}
    (hI : I∈RayQuotient.identityClass M H) (hMJ : M≤J) : IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  apply top_unique
  rw [←Ideal.isCoprime_iff_sup_eq.mp (identityClass_coprime M H hI)]
  exact sup_le_sup_left hMJ I

omit [NeZero M] in
theorem identityClass_prime_good (m : O) (hmLam : λ₀∣m) (hMm : M≤Ideal.span {m})
    (P : Ideal O) [P.IsMaximal] (hP : P∈RayQuotient.identityClass M H) : λ₀∉P := by
  have hm : m∉P := (SixthPowerAverage.prime_coprime_span_iff P m).mp
    (identityClass_coprime_larger M H hP hMm)
  intro hLam
  obtain ⟨a,rfl⟩ := hmLam
  exact hm (P.mul_mem_right a hLam)

def canonicalPrimeAmplitude (u : O) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ))*∑ P∈(HeckePrimeAnnular.annulusSet b D).filter
    (fun P => Prime P ∧ P∈RayQuotient.identityClass M H),
    starRingEnd ℂ (idealRowHom u P)*W ((P.absNorm : ℝ)/D)*
      (((P.absNorm : ℝ)/D : ℝ) : ℂ)^(z-1)

end SevenEighths.HeckePrimeRow

end

end OAI
