module

public import OAI.NumberTheory.DirichletL.Reflection.MarkedSource
public import OAI.NumberTheory.DirichletL.Reflection.SlotCoefficients

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section


lemma prime_dvd_cube_mul (P H A : Ideal ActualEisensteinCubic.O) (hP : Prime P) :
    P∣H^3*A ↔ P∣H ∨ P∣A := by
  constructor
  · intro h
    rcases hP.dvd_mul.mp h with h|h
    · exact Or.inl (hP.dvd_of_dvd_pow h)
    · exact Or.inr h
  · rintro (h|h)
    · exact dvd_mul_of_dvd_left (dvd_pow h (by decide : (3:ℕ)≠0)) A
    · exact dvd_mul_of_dvd_right h _

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def cubeActiveSlots (H : Ideal ActualEisensteinCubic.O) (S : PrimeFamily σ)  :=
  Finset.univ.filter (fun i => ¬S.ideal i∣H)

omit [DecidableEq σ] in
lemma cube_shifted_mark (H A : Ideal ActualEisensteinCubic.O) (S : PrimeFamily σ) :
    (∏ i,if S.ideal i∣H^3*A then (1:ℂ) else 0)=
      ∏ i∈cubeActiveSlots H S,if S.ideal i∣A then (1:ℂ) else 0 := by
  rw [cubeActiveSlots,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  have hp : Prime (S.ideal i) := Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  rw [prime_dvd_cube_mul _ H A hp]
  by_cases hh : S.ideal i∣H
  · simp only [hh,true_or,ite_true,not_true_eq_false,ite_false]
  · simp only [hh,false_or,not_false_eq_true,ite_true]

end
end SevenEighths.InverseReflectedPhase

end OAI
