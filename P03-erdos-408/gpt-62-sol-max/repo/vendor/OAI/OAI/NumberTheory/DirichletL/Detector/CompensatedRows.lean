module

public import OAI.NumberTheory.DirichletL.Detector.InitialRows
public import OAI.NumberTheory.DirichletL.Detector.TupleKernel
public import OAI.NumberTheory.DirichletL.Detector.MellinWindows

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : MeasurableSpace FreeRow := ⊤
local instance : MeasurableSingletonClass FreeRow := ⟨fun _=>trivial⟩

def compensatedRowOnLines {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (u : NonzeroFrequency) (t : HeightSpace) : ℂ :=
  sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
    ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
  (∏i,(elementNorm (p i):ℂ)^(((2:ℂ)+t.1.2*Complex.I)-1))*
    (star (C.residueMonoid u.val)*frequencyWeight ((2:ℂ)+t.1.2*Complex.I) u*
      indexedCompensatedHigh η S p u.val ((3:ℂ)+t.1.1*Complex.I)
        ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I))

lemma compensatedRows_counting_product_integrable {ρ : Type*} [Countable ρ]
    [MeasurableSpace ρ] [MeasurableSingletonClass ρ]
    (e : ρ→NonzeroFrequency) (he : Function.Injective e)
    {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData)
    (p : Fin K→O) (hp : ∀i,p i≠0) (mw : MellinWindows)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (fun q : ρ×HeightSpace=>compensatedRowOnLines η S C p mw.left mw.right X Y Z (e q.1) q.2)
      ((Measure.count:Measure ρ).prod heightMeasure) := by
  let F : Finset (Fin K)→ρ×HeightSpace→ℂ := fun J q=>tuplePhysicalScalar η p J*
    (highRowOnLines η S C (Ideal.span {∏i∈Finset.univ\J,p i}) 3 3 2 (e q.1) q.2*
      sourceMellinWeight mw.left mw.right (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
        (Z*elementNorm (∏i∈Finset.univ\J,p i))
        ((3:ℂ)+q.2.1.1*Complex.I) ((3:ℂ)+q.2.2*Complex.I) ((2:ℂ)+q.2.1.2*Complex.I))
  have hF (J : Finset (Fin K)) : Integrable (F J) ((Measure.count:Measure ρ).prod heightMeasure) := by
    apply Integrable.const_mul
    apply highRows_counting_product_integrable e he η S C _ 3 3 2 (by norm_num) (by norm_num) (by norm_num)
      (fun t : HeightSpace=>sourceMellinWeight mw.left mw.right (X/elementNorm (∏i∈J,p i))
        (Y/elementNorm (∏i∈J,p i)) (Z*elementNorm (∏i∈Finset.univ\J,p i))
        ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I))
    · exact sourceMellinWeight_initial_integrable mw
        _ _ _ (div_pos hX (tuple_norm_pos p hp J)) (div_pos hY (tuple_norm_pos p hp J))
        (mul_pos hZ (tuple_norm_pos p hp (Finset.univ\J))) 3 2 3 (by norm_num)
    · exact sourceMellinWeight_initial_continuous mw.left mw.right mw.rightLo mw.rightHi mw.right_pos mw.right_support
        _ _ _ (div_pos hX (tuple_norm_pos p hp J)) (div_pos hY (tuple_norm_pos p hp J))
        (mul_pos hZ (tuple_norm_pos p hp (Finset.univ\J))) 3 2 3 (by norm_num)
  have hi := integrable_finsetSum (Finset.univ:Finset (Fin K)).powerset (fun J _=>hF J)
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro q
  symm
  exact compensatedRow_kernel_subsets η S p hp (e q.1).val
    (star (C.residueMonoid (e q.1).val)*frequencyWeight ((2:ℂ)+q.2.1.2*Complex.I) (e q.1))
    mw.left mw.right X Y Z hX hY hZ _ _ _

lemma counting_product_integral_tsum {ρ : Type*} [Countable ρ]
    [MeasurableSpace ρ] [MeasurableSingletonClass ρ]
    (F : ρ×HeightSpace→ℂ)
    (hF : Integrable F ((Measure.count:Measure ρ).prod heightMeasure)) :
    (∫t,∑'r,F (r,t) ∂heightMeasure)=∑'r,∫t,F (r,t) ∂heightMeasure := by
  calc
    _ = ∫t,∫r,F (r,t) ∂(Measure.count:Measure ρ) ∂heightMeasure := by
      apply integral_congr_ae
      filter_upwards [hF.prod_left_ae] with t ht
      exact (integral_count_eq_tsum _ ht).symm
    _ = ∫q,F q ∂((Measure.count:Measure ρ).prod heightMeasure) := (integral_prod_symm F hF).symm
    _ = _ := by rw [integral_prod F hF,integral_count_eq_tsum _ hF.integral_prod_left]

theorem compensatedRowTripleIntegral_eq_tsum {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (C : CalibrationData) (p : Fin K→O) (hp : ∀i,p i≠0)
    (mw : MellinWindows)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedRowTripleIntegral η S C mw.left mw.right p X Y Z=
      ∑'u : FreeRow,((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫t,compensatedRowOnLines η S C p mw.left mw.right X Y Z ⟨u.val,u.property.1⟩ t ∂heightMeasure := by
  let e : FreeRow→NonzeroFrequency := fun u=>⟨u.val,u.property.1⟩
  have he : Function.Injective e := fun a b h=>Subtype.ext (congrArg (fun u : NonzeroFrequency=>u.val) h)
  have hi := compensatedRows_counting_product_integrable e he η S C p hp mw X Y Z hX hY hZ
  unfold compensatedRowTripleIntegral compensatedRowSeries
  rw [tsum_mul_left]
  congr 1
  rw [←counting_product_integral_tsum _ hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  simp only [compensatedRowOnLines,e,tsum_mul_left,mul_assoc]

end SevenEighths.ProbePhysical
end

end OAI
