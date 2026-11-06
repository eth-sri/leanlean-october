module

public import OAI.NumberTheory.DirichletL.Descent.GeneratorTransport
public import OAI.NumberTheory.DirichletL.Descent.SecondFreshAssembly

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
open CompletedGauss
noncomputable section

def secondUnitFrequency (u v : ActualEisensteinCubic.Oˣ) (k : ActualEisensteinCubic.O) : ActualEisensteinCubic.O := ((u^4*v:ActualEisensteinCubic.Oˣ):ActualEisensteinCubic.O)*k

lemma secondUnitFrequency_injective (u v : ActualEisensteinCubic.Oˣ) : Function.Injective (secondUnitFrequency u v) := by
  intro a b hab
  exact mul_left_cancel₀ (by simp) hab

lemma secondUnitFrequency_norm (u v : ActualEisensteinCubic.Oˣ) (k : ActualEisensteinCubic.O) :
    ‖ConcreteTraceCRT.eisEmbedding (secondUnitFrequency u v k)‖ =
      ‖ConcreteTraceCRT.eisEmbedding k‖ :=
  GaussGeneratorTransport.norm_eisEmbedding_unit_mul (u^4*v) k

lemma secondUnitFrequency_neg (u v : ActualEisensteinCubic.Oˣ) (k : ActualEisensteinCubic.O) :
    secondUnitFrequency u v (-k) = -secondUnitFrequency u v k := by
  simp only [secondUnitFrequency,mul_neg]

variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondCanonical_generator_transport
    (F : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m label d e k : ActualEisensteinCubic.O)
    (L D E : Ideal ActualEisensteinCubic.O) (u v : ActualEisensteinCubic.Oˣ)
    (hl : label = (u:ActualEisensteinCubic.O)*primaryGenerator L)
    (hd : d*e = (v:ActualEisensteinCubic.O)*(primaryGenerator D*primaryGenerator E))
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m label (d*e*k) slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m (primaryGenerator L)
        (primaryGenerator D*primaryGenerator E*secondUnitFrequency u v k) slots lists a W X := by
  rw [hl,finiteCanonicalMarkedRow_label_transfer,hd]
  congr 1
  unfold secondUnitFrequency
  change (u:ActualEisensteinCubic.O)^4*((v:ActualEisensteinCubic.O)*(primaryGenerator D*primaryGenerator E)*k) =
    primaryGenerator D*primaryGenerator E*(((u:ActualEisensteinCubic.O)^4*(v:ActualEisensteinCubic.O))*k)
  ring

theorem exists_second_generator_sectors (label d e : ActualEisensteinCubic.O) (L D E : Ideal ActualEisensteinCubic.O)
    (hl : Ideal.span {label} = L) (hd : Ideal.span {d} = D) (he : Ideal.span {e} = E)
    (hL : primaryGenerator L ≠ 0) (hD : primaryGenerator D ≠ 0) (hE : primaryGenerator E ≠ 0) :
    ∃ u v : ActualEisensteinCubic.Oˣ, label = (u:ActualEisensteinCubic.O)*primaryGenerator L ∧
      d*e = (v:ActualEisensteinCubic.O)*(primaryGenerator D*primaryGenerator E) := by
  obtain ⟨u,hu⟩ := generator_eq_unit_primary L label hl hL
  have hspan : Ideal.span {d*e} = D*E := by
    rw [← Ideal.span_singleton_mul_span_singleton,hd,he]
  obtain ⟨v,hv⟩ := generator_eq_unit_primary (D*E) (d*e) hspan
    (by rw [primaryGenerator_mul]; positivity)
  exact ⟨u,v,hu,by simpa only [primaryGenerator_mul] using hv⟩

end
end SevenEighths.InverseMoment

end OAI
