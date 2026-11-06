module

public import OAI.NumberTheory.DirichletL.Detector.CompensatedRows

@[expose] public section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary HeckeInverseAmplification
local notation "Id" => Ideal ActualEisensteinCubic.O
local instance : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : MeasurableSpace FreeRow := ⊤
local instance : MeasurableSingletonClass FreeRow := ⟨fun _=>trivial⟩

def principalFreeRow : FreeRow := ⟨1,one_ne_zero,by
  intro P
  simp [Ideal.span_singleton_one,←Ideal.one_eq_top]⟩

def rowIntegral {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData)
    (p : Fin K→ActualEisensteinCubic.O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (u : FreeRow) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫t,compensatedRowOnLines η S C p W0 W1 X Y Z ⟨u.val,u.property.1⟩ t ∂heightMeasure

def principalRowIntegral {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (p : Fin K→ActualEisensteinCubic.O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    (∏i,(elementNorm (p i):ℂ)^(((2:ℂ)+t.1.2*Complex.I)-1))*
      indexedCompensatedHigh η S p 1 ((3:ℂ)+t.1.1*Complex.I)
        ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I) ∂heightMeasure

lemma rowIntegral_principal {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData)
    (p : Fin K→ActualEisensteinCubic.O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    rowIntegral η S C p W0 W1 X Y Z principalFreeRow=principalRowIntegral η S p W0 W1 X Y Z := by
  simp only [rowIntegral,principalRowIntegral,compensatedRowOnLines,principalFreeRow,
    frequencyWeight,elementNorm_one,map_one,star_one,Complex.ofReal_one,Complex.one_cpow,one_mul]

lemma rowIntegral_summable {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData)
    (p : Fin K→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Summable (rowIntegral η S C p W0 W1 X Y Z) := by
  let e : FreeRow→NonzeroFrequency := fun u=>⟨u.val,u.property.1⟩
  have he : Function.Injective e := fun a b h=>by grind
  have hi := (compensatedRows_counting_product_integrable e he η S C p hp W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).integral_prod_left
  rw [integrable_count_iff] at hi
  exact hi.of_norm.mul_left _

end SevenEighths.ProbePhysical
end

end OAI
