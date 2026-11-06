module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Reflection.PunctureLists
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalPool

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def actualPuncturePrimes (lists : σ→Finset (Ideal ActualEisensteinCubic.O)) (m : ActualEisensteinCubic.O)  :=
  (Finset.univ.biUnion lists).filter (fun P => m∈P)

omit [DecidableEq σ] in
lemma actualPuncturePrimes_mem (lists : σ→Finset (Ideal ActualEisensteinCubic.O))  m 
    (i : σ)  P  (hP : P∈lists i) :
    P∈actualPuncturePrimes lists m ↔ m∈P := by
  grind [actualPuncturePrimes]

lemma puncture_period_coprime (Q : Ideal ActualEisensteinCubic.O) (m : ActualEisensteinCubic.O) (hQ : Q∣Ideal.span {m})
     P  (hP : P.IsMaximal) (hm : m∉P) : IsCoprime Q P := IsCoprime.of_isCoprime_of_dvd_left (IsCoprime.symm (OAI.SevenEighths.InverseReflectedPhase.maximal_coprime_of_not_dvd P (Ideal.span {m}) fun h => hm (Ideal.dvd_iff_le.mp h (Ideal.subset_span (Set.mem_singleton m))))) hQ

theorem original_completed_actual_puncture_lists (lists : σ→Finset (Ideal ActualEisensteinCubic.O))
    (hprime : ∀ i,∀ P∈lists i,Prime P)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    ∑ p : ∀ i,punctureLists lists (actualPuncturePrimes lists m) i,
      (∏ i,w i (punctureListLift lists (actualPuncturePrimes lists m) p i))*markedCompletedT
      (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0) := by
  apply sum_puncture_lists lists (actualPuncturePrimes lists m)
  intro p hp
  obtain ⟨i,hi⟩ := hp
  have hm : m∈(p i).val := (Finset.mem_filter.mp hi).2
  have hz := markedCompletedT_zero_punctured Ψ m f z (p i).val
    (hprime i _ (p i).property) hm W X (fun A => ∏ j,if (p j).val∣A then (1:ℂ) else 0)
    (fun A hA => Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hA))
  exact mul_eq_zero_of_right _ hz
end
end SevenEighths.InverseReflectedPhase

end OAI
