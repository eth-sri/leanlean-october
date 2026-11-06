module
public import OAI.NumberTheory.DirichletL.Reflection.Static
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss
open LocalReflectionBrackets FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma scalar_phase_power (a b : ℂ) (ha : a ≠ 0) (j : ℕ) :
    a⁻¹^2*b⁻¹^(j+2) = a^j*(a⁻¹*b⁻¹)^(j+2) := by
  symm
  calc
    _ = (a^j*(a⁻¹)^j)*(a⁻¹)^2*(b⁻¹)^(j+2) := by rw [mul_pow,pow_add]; ring
    _ = _ := by simp_all

section
variable {F : Type*} [Field F] [Fintype F] (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ)
include F χ ψ σ ε
theorem general_local_phase (A B z : F)
    (hsigma : (σ : F) = A*z) (he : B*z*(σ : F)*(ε : F) = -1)
    (j : ℕ) (hj0 : j ≠ 0) (hj4 : j ≠ 4) :
    ((χ⁻¹)^2) σ * phase χ ψ j ε =
      (tau χ (ψ.mulShift (-1)) j*tau χ ψ (j+2)) *
        (χ (-1))⁻¹^(j+2)*(χ A)^j*(χ B)^(j+2)*(χ z)^(2*j+2) := by
  pm_3297
  pm_1412
  simp only [phase,hj4,hj0,↓reduceIte,MulChar.pow_apply_coe,MulChar.inv_apply_eq_inv']
  calc
    _ = (tau χ (ψ.mulShift (-1)) j*tau χ ψ (j+2))*((χ σ)⁻¹^2*(χ ε)⁻¹^(j+2)) := by ring
    _ = _ := by
      rw [scalar_phase_power _ _ hs j,hi,hsig]
      simp only [mul_pow,pow_add,show 2*j=j+j by omega]
      ring

theorem exceptional_local_phase (A z : F)
    (hsigma : (σ : F) = A*z) :
    ((χ⁻¹)^2) σ * phase χ ψ 4 ε =
      (tau χ (ψ.mulShift (-1)) 4*(χ A)⁻¹^2)*(χ z)⁻¹^2 := by
  simp only [phase,↓reduceIte,hsigma,map_mul,
    ]
  simp only [MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv']
  ring
end

noncomputable local instance frozenField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance frozenFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def frozenPrimeScalar (p c : Eis) [(Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : λ₀ ∉ Ideal.span {p}) (j : ℕ) : ℂ :=
  let χ := actualSextic (Ideal.span {p}) hg
  if j=4 then tau χ ((quotientTrace p hp).mulShift (-1)) 4*
      (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c)))⁻¹^2
  else if j=0 then markedPrimeScalar p c hp hg
  else (tau χ ((quotientTrace p hp).mulShift (-1)) j*tau χ (quotientTrace p hp) (j+2)) *
    (χ (-1))⁻¹^(j+2)*(χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c)))^j*
    (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^3*c)))^(j+2)

def frozenCofactorCharacter (P : Ideal Eis) [P.IsMaximal]
    (hg : λ₀ ∉ P) (j : ℕ) : Eis →* ℂ :=
  (if j=4 then ((actualSextic P hg)⁻¹)^2 else (actualSextic P hg)^(2*j+2)).toMonoidHom.comp
    (Ideal.Quotient.mk P).toMonoidHom

variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

theorem controlled_frozen_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (i : ι) (j : ℕ) :
    (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) j (D.epsilon i) =
    frozenPrimeScalar (p i) c (hp i) (hg i) j *
      frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (cofactor p i) := by
  have hs : (D.sigma i : Eis ⧸ Ideal.span {p i}) =
      Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c)*Ideal.Quotient.mk _ (cofactor p i) := by
    simpa only [map_mul] using D.sigma_value i
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c)*
      Ideal.Quotient.mk _ (cofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  by_cases hj4 : j=4
  · subst j
    pm_7909 exceptional_local_phase hs
    simp only [frozenPrimeScalar,frozenCofactorCharacter,↓reduceIte,MonoidHom.comp_apply,
      RingHom.toMonoidHom_eq_coe,MulChar.coe_toMonoidHom,
      MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv']
    rfl
  · by_cases hj0 : j=0
    · subst j
      pm_7909 marked_local_phase he
      simp [frozenPrimeScalar,frozenCofactorCharacter,markedPrimeScalar,
        MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0)]
    · rw [general_local_phase _ _ _ _ _ _ _ hs he j hj0 hj4]
      simp only [frozenPrimeScalar,frozenCofactorCharacter,hj4,hj0,↓reduceIte,
        MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,
        MulChar.coe_toMonoidHom,MulChar.pow_apply' _ (by omega : 2*j+2 ≠ 0)]
      rfl

end
end SevenEighths.InverseReflectedPhase

end OAI
