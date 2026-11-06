module
public import OAI.NumberTheory.DirichletL.PrimeRows.CoarseAmplitude
public import OAI.NumberTheory.DirichletL.PrimeRows.SliceIntegral
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem uniform_buffered_x_slice_decay (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ)
    (r : ℝ) (hr : (17/50:ℝ)≤ r) (hr1 : r≤1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→ Character,∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀tx : ℝ,|tx|=H →
      let F := fun q : ℝ×ℝ=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂ volume.prod volume)≤
          C*contourArithmeticCost η u P*(X^(1/2-r)*Z ^(σ+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨A0,hA0,hrow0⟩ := rowAmplitudeOnLines_buffered_polynomial (ι:=ι) K e he he' S hS hfirst hmax
  pm_310 A0
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH hbin σ hσ tx htx
  let A := A0*contourArithmeticCost η u P
  have hA : 0≤A := mul_nonneg hA0 (contourArithmeticCost_nonneg η u P)
  have hrow := hrow0 η u hu P hP hPS ψ a B H i ha haTop hB hH hbin
  let G := fun q : ℝ×ℝ=>rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r ((tx,q.1),q.2)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).comp (by fun_prop)
  have hb (q : ℝ×ℝ) : ‖G q‖≤(9*A*(3+|H|)^2)*jointHeight tx q.1 q.2^2 := by
    pm_649
    apply (hrow σ hσ r ⟨hr,hr1⟩ ((tx,q.1),q.2) htx.le).trans
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
    _ = _ := by dsimp [A];rw [pow_add];field_simp;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
