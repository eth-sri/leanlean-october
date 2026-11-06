module

public import OAI.NumberTheory.DirichletL.Descent.Canonical

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss



variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondChildColumn_label_transfer  Ψ   m a f k 
     H   S  :
    secondChildColumn p hp hcop hg Ψ m (a*f) k H S =
      secondChildColumn p hp hcop hg Ψ m f (a^4*k) H S := by
  simp only [secondChildColumn, finiteSquarefreeRow, map_mul, map_pow,
    Finset.prod_mul_distrib, Finset.prod_pow, mul_pow]
  ring

theorem secondChildColumn_generator_unit (Ψ : ActualEisensteinCubic.O →* ℂ) (u : ActualEisensteinCubic.Oˣ)  m f d k 
     H   S  :
    secondChildColumn p hp hcop hg Ψ m ((u:ActualEisensteinCubic.O)*f) ((u:ActualEisensteinCubic.O)*d*k) H S =
      secondChildColumn p hp hcop hg Ψ m f (d*((u:ActualEisensteinCubic.O)^5*k)) H S := by
  rw [secondChildColumn_label_transfer]
  congr 1
  ring

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_label_transfer  F   Ψ 
     m a f k  (slots : Finset σ) (lists : σ → Finset ι) (coeff : σ → ι → ℂ)
     W   X  :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m (a*f) k slots lists coeff W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m f (a^4*k) slots lists coeff W X := by
  simp only [finiteCanonicalMarkedRow,fixedChildRow,secondChildColumn_label_transfer]

theorem generator_eq_unit_primary  I   e 
    (he : Ideal.span {e} = I) (hI : primaryGenerator I ≠ 0) :
    ∃ u : ActualEisensteinCubic.Oˣ, e = (u:ActualEisensteinCubic.O)*primaryGenerator I := by
  have ha : Associated (primaryGenerator I) e :=
    Ideal.span_singleton_eq_span_singleton.mp ((primaryGenerator_spec I hI).1.trans he.symm)
  obtain ⟨u,hu⟩ := ha
  exact ⟨u,by simpa only [mul_comm] using hu.symm⟩


end SevenEighths.InverseMoment

end OAI
