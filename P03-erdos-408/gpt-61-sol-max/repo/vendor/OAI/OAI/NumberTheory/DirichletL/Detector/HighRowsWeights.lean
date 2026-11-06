module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.LocalWeights

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

section
variable (Q eta a G1 C omega X W V scalar : ℂ) (hQ : Q≠0) (hC : C^2=omega) (ho : omega^2=1) (e l k m : ℕ)

include hC ho in
lemma localCubePhase_step_two      
      : localCubePhase C omega e (l+2) k=localCubePhase C omega e l k := by
  have hchoose : (l+2).choose 2=l.choose 2+2*l+1 := by
    rw [show l+2=(l+1)+1 by omega,Nat.choose_succ_succ,Nat.choose_one_right,
      Nat.choose_succ_succ,Nat.choose_one_right]
    change l+1+(l+l.choose 2)=l.choose 2+2*l+1
    omega
  unfold localCubePhase
  rw [pow_add C l 2,hC,hchoose]
  have he : (e+3*(l+2))*k+e*(l+2)+(l.choose 2+2*l+1)=
      ((e+3*l)*k+e*l+l.choose 2)+(2*(3*k+e+l)+1) := by ring
  have ht : omega^(2*(3*k+e+l)+1)=omega := by
    rw [pow_add,pow_mul omega 2,ho,one_pow,pow_one,one_mul]
  rw [he,pow_add omega _ (2*(3*k+e+l)+1),ht]
  grind

include hQ hC ho in
theorem weightedScalar_step_two  
            :
    weightedScalar Q eta a G1 C omega X W V (Q^6*scalar) e (l+2) k (m+1)=
      evenRatio Q a X V*weightedScalar Q eta a G1 C omega X W V scalar e l k m := by
  grind [weightedScalar, evenRatio, localCubePhase_step_two, localCubePhase]

end

def rowWeightedScalar (Q eta a G1 C omega X W V rho scalar : ℂ) (e l k m : ℕ)  :=
  (rho^k/rho^(e+3*l))*weightedScalar Q eta a G1 C omega X W V scalar e l k m

section
variable (Q eta a G1 C omega X W V rho scalar : ℂ) (hQ : Q≠0) (hC : C^2=omega) (ho : omega^2=1) (hρ : rho^6=1) (e l k m : ℕ)

lemma rowWeightedScalar_zero     :
    rowWeightedScalar Q eta a G1 C omega X W V rho 0 e l k m=0 := by
  rw [rowWeightedScalar,weightedScalar_zero,mul_zero]

theorem rowWeightedScalar_parameters  
      :
    rowWeightedScalar Q eta a G1 C omega X W V rho scalar e l k m=
      weightedScalar Q (eta/rho) (a/rho^3) G1 C omega X (rho*W) V scalar e l k m := by
  unfold rowWeightedScalar weightedScalar
  ring

include hρ in
theorem evenRatio_unit     :
    evenRatio Q (a/rho^3) X V=evenRatio Q a X V := by
  grind [evenRatio]

include hQ hC ho hρ in
theorem rowWeightedScalar_step_two  
              :
    rowWeightedScalar Q eta a G1 C omega X W V rho (Q^6*scalar) e (l+2) k (m+1)=
      evenRatio Q a X V*rowWeightedScalar Q eta a G1 C omega X W V rho scalar e l k m := by
  simp_all [rowWeightedScalar_parameters, weightedScalar_step_two, evenRatio_unit]

end

end SevenEighths.ProbeEuler
end

end OAI
