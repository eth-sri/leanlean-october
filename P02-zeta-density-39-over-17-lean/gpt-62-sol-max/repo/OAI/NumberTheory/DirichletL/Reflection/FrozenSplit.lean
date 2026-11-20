module
public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalIdealFamily
public import OAI.NumberTheory.DirichletL.Reflection.ThreeBlocks

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance frozenSplitFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def frozenArgument [OAI.PrincipalIdealFamily.Maximal p]
    (hg : OAI.PrincipalIdealFamily.Avoids p λ₀) (j : ι → ℕ) (F : Finset ι) : Eis →* ℂ :=
  ∏ i ∈ F, frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i)

def frozenCore [OAI.PrincipalIdealFamily.Maximal p]
    (hp : ∀ i, p i ≠ 0) (hg : OAI.PrincipalIdealFamily.Avoids p λ₀) (c : Eis)
    (j : ι → ℕ) (F : Finset ι) : ℂ :=
  ∏ i ∈ F, frozenPrimeScalar (p i) c (hp i) (hg i) (j i) *
    frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ F.erase i, p k)

theorem frozen_cofactor_split (hp : ∀ i, p i ≠ 0) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (i : ι) (hi : i ∈ F) :
    cofactor p i = (∏ k ∈ F.erase i, p k)*(∏ k ∈ R, p k)*(∏ k ∈ S, p k) := by
  apply mul_left_cancel₀ (hp i)
  rw [prime_mul_cofactor,← hu,Finset.prod_union hF,Finset.prod_union hRS,
    ← Finset.mul_prod_erase F p hi]
  ring

theorem frozenPhase_split [OAI.PrincipalIdealFamily.Maximal p]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : OAI.PrincipalIdealFamily.Avoids p λ₀) (j : ι → ℕ)
    (R S F : Finset ι) (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F)
    (hu : (R ∪ S) ∪ F = Finset.univ) :
    frozenPhase D hp hg j F = frozenCore hp hg c j F *
      frozenArgument hg j F (∏ i ∈ R, p i) * frozenArgument hg j F (∏ i ∈ S, p i) := by
  unfold frozenPhase
  simp_rw [controlled_frozen_phase]
  have he (i : ι) (hi : i ∈ F) :
      frozenPrimeScalar (p i) c (hp i) (hg i) (j i)*
        frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (cofactor p i) =
      (frozenPrimeScalar (p i) c (hp i) (hg i) (j i)*
        frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ F.erase i, p k))*
      frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ R, p k)*
      frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ S, p k) := by
    rw [frozen_cofactor_split hp R S F hRS hF hu i hi,map_mul,map_mul]
    ring
  rw [Finset.prod_congr rfl he]
  simp only [Finset.prod_mul_distrib,frozenCore,frozenArgument,MonoidHom.finsetProd_apply]

omit [Fintype ι] in
theorem frozenArgument_norm_le_one [OAI.PrincipalIdealFamily.Maximal p]
    (hg : OAI.PrincipalIdealFamily.Avoids p λ₀) (j : ι → ℕ) (F : Finset ι) (z : Eis) :
    ‖frozenArgument hg j F z‖ ≤ 1 := by
  simp only [frozenArgument,MonoidHom.finsetProd_apply,norm_prod]
  apply Finset.prod_le_one₀
  · intro i hi; exact norm_nonneg _
  · intro i hi
    unfold frozenCofactorCharacter
    split_ifs
    · exact FiniteRayExpansion.norm_char_le_one (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        (Ideal.Quotient.mk (Ideal.span {p i}) z)
    · exact FiniteRayExpansion.norm_char_le_one ((actualSextic (Ideal.span {p i}) (hg i))^(2*j i+2))
        (Ideal.Quotient.mk (Ideal.span {p i}) z)

end
end SevenEighths.InverseReflectedPhase

end OAI
