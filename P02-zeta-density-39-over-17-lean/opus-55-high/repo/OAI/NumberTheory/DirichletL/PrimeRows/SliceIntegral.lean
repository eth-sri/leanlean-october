module
public import OAI.NumberTheory.DirichletL.PrimeRows.BufferedIntegral
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open ProbePhysical ProbeMellinBoundary

theorem source_profile_arithmetic_slices (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃K : ℝ,0<K ∧ ∀σ∈Icc slo shi,∀ξ∈Icc zlo zhi,∀υ∈Icc wlo whi,
      ∀axis : SliceAxis,∀T A : ℝ,0≤A → ∀X Y Z : ℝ,0<X → 0<Y → 0<Z →
      ∀G : ℝ×ℝ→ℂ,AEStronglyMeasurable G (volume.prod volume) →
      (∀q,‖G q‖≤A*jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J) →
      let F := fun q : ℝ×ℝ=>sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+(sliceMap axis T q).1.1*I) ((υ:ℂ)+(sliceMap axis T q).2*I)
        ((ξ:ℂ)+(sliceMap axis T q).1.2*I)*G q
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂ volume.prod volume)≤
          A*K*(X^(1/2-ξ)*Z ^(σ+ξ-1)*Y^(υ-1))/height T^N := by
  pm_3840 hbound profile_arithmetic_slices
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ axis T A hA X Y Z hX hY hZ G hG hGb
  let E : ℝ := X^(1/2-ξ)*Z ^(σ+ξ-1)*Y^(υ-1)
  pm_3479
  let S := fun q : ℝ×ℝ=>sourceScale X Y Z ((σ:ℂ)+(sliceMap axis T q).1.1*I)
    ((υ:ℂ)+(sliceMap axis T q).2*I) ((ξ:ℂ)+(sliceMap axis T q).1.2*I)
  pm_397
  have hS0 := (sourceScale_continuous X Y Z hX hY hZ).comp (hc.comp (sliceMap_continuous axis T))
  have hS : Continuous S := by simpa only [S,Function.comp_def] using hS0
  have hSn (q : ℝ×ℝ) : ‖S q‖=E := by
    pm_6063
  have hb (q : ℝ×ℝ) : ‖S q*G q‖≤(E*A)*jointHeight
      (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J := by
    pm_5852
  obtain ⟨hi,hb⟩ := hbound σ hσ ξ hξ υ hυ axis T (E*A) (mul_nonneg hE hA)
    (fun q=>S q*G q) (hS.aestronglyMeasurable.mul hG) hb
  have heq : (fun q : ℝ×ℝ=>sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+(sliceMap axis T q).1.1*I) ((υ:ℂ)+(sliceMap axis T q).2*I)
        ((ξ:ℂ)+(sliceMap axis T q).1.2*I)*G q)=
      (fun q=>(S q*G q)*onLines W0 W1 σ ξ υ (sliceMap axis T q)) := by
    pm_7514
  pm_8374
  have hnorm := congrArg (fun f : ℝ×ℝ→ℂ => ∫q : ℝ×ℝ,‖f q‖ ∂ volume.prod volume) heq
  rw [hnorm]
  calc
    _ ≤ (E*A)*K/height T^N := hb
    _ = _ := by dsimp [E];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
