module

public import OAI.NumberTheory.DirichletL.Reflection.SourceSum
public import OAI.NumberTheory.DirichletL.Descent.Quotients

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open CompletedGauss InverseMoment
noncomputable section
variable {φ : Type*} [Fintype φ]

lemma frozenBranchColumn_divisibility (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ) (n b : Ideal ActualEisensteinCubic.O)
    (hn : primaryGenerator n ≠ 0) (hb : primaryGenerator b ≠ 0)
    (hz : frozenBranchColumn F jF e A n b ≠ 0) :
    frozenExtracted F jF e 1 ∣ n ∧ frozenExtracted F jF e 2 ∣ b ∧
      ∀ i, jF i=4 → e i=2 → primaryGenerator n ∉ F.ideal i := by
  have hcp : Pairwise (fun i k => IsCoprime (Ideal.span {F.generator i}) (Ideal.span {F.generator k})) := by
    simpa only [PrimeFamily.generator_span] using hF
  have hh := reflectedBranch_divisibility (fun i => Ideal.span {F.generator i}) F.generator_good hcp
    jF e (primaryGenerator n) (primaryGenerator b) (mul_ne_zero_iff.mp hz).2
  simpa only [frozenExtracted,(primaryGenerator_spec n hn).1,(primaryGenerator_spec b hb).1,
    PrimeFamily.generator_span] using hh

lemma frozenBranchColumn_zero_of_not_dvd (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ) (n b : Ideal ActualEisensteinCubic.O)
    (hn : primaryGenerator n ≠ 0) (hb : primaryGenerator b ≠ 0)
    (hz : ¬ frozenExtracted F jF e 1 ∣ n ∨ ¬ frozenExtracted F jF e 2 ∣ b) :
    frozenBranchColumn F jF e A n b = 0 := by
  by_contra hh
  obtain ⟨hd1,hd2,_⟩ := frozenBranchColumn_divisibility F hF jF e A n b hn hb hh
  simp_all

theorem frozenBranchColumn_dual_reindex (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A W : Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ) (nset bset : Finset (Ideal ActualEisensteinCubic.O))
    (hn : ∀ n ∈ nset, primaryGenerator n ≠ 0) (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0) :
    (∑ n ∈ nset, ∑ b ∈ bset, frozenBranchColumn F jF e A n b*W n b) =
      ∑ n ∈ quotientSupport (frozenExtracted F jF e 1) nset,
        ∑ b ∈ quotientSupport (frozenExtracted F jF e 2) bset,
          frozenBranchColumn F jF e A ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b)*
            W ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b) := by
  classical
  have hfilter :
      (∑ n ∈ nset, ∑ b ∈ bset, frozenBranchColumn F jF e A n b*W n b) =
      ∑ n ∈ nset with frozenExtracted F jF e 1 ∣ n,
        ∑ b ∈ bset with frozenExtracted F jF e 2 ∣ b, frozenBranchColumn F jF e A n b*W n b := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn'
    by_cases hd1 : frozenExtracted F jF e 1 ∣ n
    · rw [ite_eq_left hd1]
      apply Finset.sum_congr rfl
      intro b hb'
      by_cases hd2 : frozenExtracted F jF e 2 ∣ b
      · simp_all
      · rw [ite_eq_right hd2,frozenBranchColumn_zero_of_not_dvd F hF jF e A n b (by grind) (by grind) (Or.inr hd2),zero_mul]
    · rw [ite_eq_right hd1]
      apply Finset.sum_eq_zero
      intro b hb'
      rw [frozenBranchColumn_zero_of_not_dvd F hF jF e A n b (by grind) (by grind) (Or.inl hd1),zero_mul]
  simp [hfilter,sum_quotientSupport]

end
end SevenEighths.InverseReflectedPhase

end OAI
