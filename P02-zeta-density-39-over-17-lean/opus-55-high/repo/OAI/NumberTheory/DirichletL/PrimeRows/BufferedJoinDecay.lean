module
public import OAI.NumberTheory.DirichletL.PrimeRows.BufferedHeightGrowth
public import OAI.NumberTheory.DirichletL.PrimeRows.BufferedSlices
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

open scoped Classical
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

section
variable {K : ℕ} (e : ℝ) (he : 0<e) (he' : e<1/1000) (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) (hfirst : FirstTail (4*e) S) (P : Fin K→ PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→ Character)
include K e he he' S hS hmax hfirst P hPS η u hu ψ
lemma rowAmplitudeOnLines_buffered_height_uniform
    (r : ℝ) (hr : (17/50:ℝ)≤ r) :
    ∃C : ℝ,0≤C ∧ ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀t : HeightSpace, |t.1.1|≤H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤C*(3+|H|)^2*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_buffered_height_growth e he he' S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu ψ
  pm_3482
  intro a B H i ha haTop hB hH hbin σ hσ t ht
  pm_3475
  have hh := hbound a B H i ha haTop hB hH hbin ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ.1) (by simpa using hσ.2) (by simpa using ht) (by simp) (by simpa using hr)
  pm_3476
  unfold rowAmplitudeOnLines
  pm_3477 hA

theorem buffered_x_slice_arbitrary_decay
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ)
    (r : ℝ) (hr : (17/50:ℝ)≤ r) :
    ∃C : ℝ,0≤C ∧ ∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀tx : ℝ,|tx|=H →
      let F := fun q : ℝ×ℝ=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂ volume.prod volume)≤
          C*(X^(1/2-r)*Z ^(σ+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨A,hA,hrow⟩ := rowAmplitudeOnLines_buffered_height_uniform e he he' S hS hmax hfirst P hPS η u hu ψ r hr
  pm_310 A
  intro X Y Z hX hY hZ a B H i ha haTop hB hH hbin σ hσ tx htx
  let G := fun q : ℝ×ℝ=>rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r ((tx,q.1),q.2)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).comp (by fun_prop)
  have hb (q : ℝ×ℝ) : ‖G q‖≤(9*A*(3+|H|)^2)*jointHeight tx q.1 q.2^2 := by
    pm_649
    apply (hrow a B H i ha haTop hB hH hbin σ hσ ((tx,q.1),q.2) htx.le).trans
    pm_380
  pm_249
  have ht' : Integrable (fun q : ℝ×ℝ=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)‖ ∂ volume.prod volume)≤
        (9*A*(3+|H|)^2)*D *(X^(1/2-r)*Z ^(σ+r-1)*Y^((1-a-6*e)-1))/height tx^(N+2) := by
    simpa only [sliceMap,G,continuedRowOnLines_eq_amplitude] using ht
  pm_137
  calc
    _ ≤ (9*A*(9*(height H)^2))*D *(X^(1/2-r)*Z ^(σ+r-1)*Y^((1-a-6*e)-1))/height H^(N+2) := by
      gcongr
    _ = _ := by rw [pow_add];field_simp;ring
end

end SevenEighths.ProbeHighRowFamily


end OAI
