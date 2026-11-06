module

public import OAI.NumberTheory.DirichletL.Reflection.PunctureAbsorption

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open CompletedGauss CanonicalRowCompletion InverseMoment
noncomputable section

lemma markedCompletedT_zero_punctured (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O)
    (P : Ideal ActualEisensteinCubic.O) (hP : Prime P) (hm : m∈P)
    (W : ℝ→ℂ) (X : ℝ) (d : Ideal ActualEisensteinCubic.O→ℂ) (hd : ∀ A,¬P∣A → d A=0) :
    markedCompletedT (rowTwist Ψ m f z) W X d=0 := by
  have hz (I J : Ideal ActualEisensteinCubic.O) : summand (rowTwist Ψ m f z) W X I J*d (I*J^3)=0 := by
    by_cases hdiv : P∣I*J^3
    · rcases hP.dvd_mul.mp hdiv with hI|hJ
      · have hz := CanonicalRowCompletion.columnWeight_zero_of_mask Ψ m f z hP hI hm
        simp only [summand,hz,zero_div,zero_mul]
      · have hz := cubeWeight_zero_of_prime_mask Ψ m f z hP (hP.dvd_of_dvd_pow hJ) hm
        simp only [summand,hz,mul_zero,zero_mul]
    · simp_all
  simp only [markedCompletedT,hz,tsum_zero]

end
end SevenEighths.InverseReflectedPhase

end OAI
