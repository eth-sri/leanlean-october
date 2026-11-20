module

public import OAI.NumberTheory.DirichletL.PrimeRows.CentralRectangle
public import OAI.NumberTheory.DirichletL.Detector.MellinWindows

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def centralCubeIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : HeightSpace in {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H},
      continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) p ∂heightMeasure

theorem central_rectangle_z_cutoff_error (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (mw : MellinWindows)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖centralRectangleIntegral S hS hmax P hPS η u mw.left mw.right X Y Z a e H-
        centralCubeIntegral S hS hmax P hPS η u mw.left mw.right X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C,hC,hbound⟩ := uniform_central_cutoff_error (ι:=ι) K e he he' S hS hmax hfirst
    mw.left mw.right mw.leftLo mw.leftHi mw.rightLo mw.rightHi mw.left_pos mw.right_pos mw.left_support mw.right_support N (17/50) le_rfl (by norm_num)
  let n : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨‖n‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  let E : Set HeightSpace := {t | |t.1.1|≤H ∧ |t.2|≤H}
  let T : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  have hE : MeasurableSet E := (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.1|) by fun_prop) measurable_const).inter
    (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.2|) by fun_prop) measurable_const)
  have hT : MeasurableSet T := hE.inter (measurableSet_le (show Measurable (fun t : HeightSpace => |t.1.2|) by fun_prop) measurable_const)
  have hb := hbound η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
    (a+16*e) ⟨le_rfl,by linarith⟩ E T hE hT (fun _ ht => ht.1) (fun _ ht => ht.1)
    (fun t ht => Or.inl (lt_of_not_ge fun ha => ht.2 ⟨ht.1, ha⟩))
  rw [centralRectangleIntegral, centralCubeIntegral, ← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg n)).trans_eq (by dsimp [n]; ring)

theorem uniform_original_row_cube_error (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (mw : MellinWindows)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 1≤Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val) mw.left mw.right X Y Z u-
        centralCubeIntegral S hS hmax P hPS η u mw.left mw.right X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C0,hC0,h0⟩ := uniform_original_row_rectangle_error (ι:=ι) K e he he' S hS hmax hfirst
    mw N
  obtain ⟨C1,hC1,h1⟩ := central_rectangle_z_cutoff_error (ι:=ι) K e he he' S hS hmax hfirst
    mw N
  refine ⟨C0+C1,add_nonneg hC0 hC1,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have h0' := h0 η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have h1' := h1 η u hu P hP hPS ψ X Y Z hX hY (by linarith) a B H i ha haTop hB hH0 hH hbin
  have hcost := contourArithmeticCost_nonneg η u P
  have hz : Z^(a+16*e+(17/50:ℝ)-1)≤Z^(2+(17/50:ℝ)-1) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h1'' : ‖centralRectangleIntegral S hS hmax P hPS η u mw.left mw.right X Y Z a e H-
      centralCubeIntegral S hS hmax P hPS η u mw.left mw.right X Y Z a e H‖≤
      C1*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
    apply h1'.trans
    gcongr
    exact pow_nonneg (height_pos _).le _
  apply (norm_sub_le_norm_sub_add_norm_sub _ (centralRectangleIntegral S hS hmax P hPS η u mw.left mw.right X Y Z a e H) _).trans
  exact (add_le_add h0' h1'').trans_eq (by ring)

end SevenEighths.ProbeHighRowFamily

end

end OAI
