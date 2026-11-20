module

public import OAI.NumberTheory.DirichletL.PrimeRows.BufferedTransport
public import OAI.NumberTheory.DirichletL.PrimeRows.UniformJoins
public import OAI.NumberTheory.DirichletL.PrimeRows.TailIntegral
public import OAI.NumberTheory.DirichletL.PrimeRows.FirstTransport
public import OAI.NumberTheory.DirichletL.Detector.MellinWindows

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma height_slab_partial_integrable (f : HeightSpace→ℂ) (H : ℝ) (hH : 0≤H)
    (hf : IntegrableOn f {t : HeightSpace | |t.1.1|≤H} heightMeasure) :
    Integrable (fun q : ℝ×ℝ=>∫x : ℝ in -H..H,f ((x,q.1),q.2)) (volume.prod volume) := by
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hp := (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ) (volume : Measure ℝ)).symm MeasurableEquiv.prodAssoc
  have hr : Integrable (fun p : ℝ × (ℝ × ℝ)=>(E.indicator f) ((p.1,p.2.1),p.2.2))
      (volume.prod (volume.prod volume)) := hp.integrable_comp_of_integrable ((integrable_indicator_iff hE).mpr hf)
  have heq : (fun q : ℝ×ℝ=>∫x : ℝ,(E.indicator f) ((x,q.1),q.2))=
      (fun q : ℝ×ℝ=>∫x : ℝ in -H..H,f ((x,q.1),q.2)) := by
    funext q
    have hfun : (fun x : ℝ=>(E.indicator f) ((x,q.1),q.2))=
        (Icc (-H) H).indicator (fun x=>f ((x,q.1),q.2)) := by
      funext x
      simp only [Set.indicator_apply,E,Set.mem_ofPred_eq,Set.mem_Icc,abs_le]
    rw [hfun,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by linarith)]
  exact heq ▸ hr.integral_prod_right

lemma height_slab_integral_pair (f : HeightSpace→ℂ) (H : ℝ) (hH : 0≤H)
    (hf : IntegrableOn f {t : HeightSpace | |t.1.1|≤H} heightMeasure) :
    (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H},f p ∂heightMeasure)=
      ∫q : ℝ×ℝ,(∫x : ℝ in -H..H,f ((x,q.1),q.2)) ∂volume.prod volume := by
  rw [height_slab_integral_wzx f H hH hf]
  exact (integral_prod_symm _ (height_slab_partial_integrable f H hH hf)).symm

variable {ι : Type*} [Fintype ι]

theorem rowIntegral_central_decomposition {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH0 : 0≤H) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (mw : MellinWindows)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let k := fun σ p=>continuedRowOnLines S hS hmax P hPS η u mw.left mw.right X Y Z σ (1-a-6*e) (17/50) p
    let E : Set HeightSpace := {t | |t.1.1|≤H}
    IntegrableOn (k (a+16*e)) E heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun j=>CompletedGauss.primaryGenerator (P j).val) mw.left mw.right X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3 *
        ((∫p : HeightSpace in E,k (a+16*e) p ∂heightMeasure)+
          I*((∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((-H,q.1),q.2)) ∂volume.prod volume)-
            (∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((H,q.1),q.2)) ∂volume.prod volume))+
          ∫p : HeightSpace in Eᶜ,k 2 p ∂heightMeasure) := by
  dsimp only
  let k := fun σ p=>continuedRowOnLines S hS hmax P hPS η u mw.left mw.right X Y Z σ (1-a-6*e) (17/50) p
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  obtain ⟨hi,hrow⟩ := rowIntegral_central_start a e ha haTop he he' S hS hmax hfirst P hP hPS η u hu
    mw X Y Z hX hY hZ
  have hleft := continuedPhysicalRowKernel_buffered_integrable e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin mw
    X Y Z hX hY hZ (a+16*e) (17/50) le_rfl (by linarith) le_rfl (by norm_num)
  obtain ⟨_,_,hjoins⟩ := uniform_buffered_horizontal_join_decay (ι:=ι) K e he he' S hS hmax hfirst
    mw 0 (17/50) le_rfl (by norm_num)
  have hJ (tx : ℝ) (htx : |tx|=H) :
      Integrable (fun q : ℝ×ℝ=>∫v : ℝ in (a+16*e)..2,k v ((tx,q.1),q.2)) (volume.prod volume) :=
    (hjoins η u hu P hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH hbin tx htx).1
  have hm := hJ (-H) (by rw [abs_neg,abs_of_nonneg hH0])
  have hp := hJ H (abs_of_nonneg hH0)
  have hc := height_slab_partial_integrable _ H hH0 hleft
  refine ⟨hleft,?_⟩
  rw [hrow,←integral_add_compl hE hi]
  congr 2
  rw [height_slab_integral_pair _ H hH0 hi.integrableOn,
    height_slab_integral_pair _ H hH0 hleft]
  have heq : (fun q : ℝ×ℝ=>∫tx : ℝ in -H..H,k 2 ((tx,q.1),q.2))=
      (fun q : ℝ×ℝ=>(∫tx : ℝ in -H..H,k (a+16*e) ((tx,q.1),q.2))+
        I*((∫v : ℝ in (a+16*e)..2,k v ((-H,q.1),q.2))-(∫v : ℝ in (a+16*e)..2,k v ((H,q.1),q.2)))) := by
    funext q
    have hHT : H≤3*(i+1:ℕ)*B := by
      apply hH.trans
      have hn : (3*i+2:ℕ)≤3*(i+1) := by omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by linarith)
    simpa only [k,continuedRowOnLines,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using
      source_buffered_x_rectangle S hS hmax P hPS η u ψ B a e i he he' ha haTop hfirst hbin mw.left mw.right X Y Z hZ
        ((((1-a-6*e):ℝ):ℂ)+q.2*I) ((17/50:ℂ)+q.1*I) (by simp) (by norm_num) 2 H (by linarith) hH0 hHT
  rw [heq]
  dsimp only [k] at hm hp ⊢
  have hsplit := integral_add hc ((hm.sub hp).const_mul I)
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit,integral_const_mul]
  congr 1
  exact congrArg (fun z : ℂ=>I*z) (integral_sub hm hp)

end SevenEighths.ProbeHighRowFamily

end

end OAI
