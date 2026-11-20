module

public import OAI.NumberTheory.DirichletL.PrimeRows.BufferedIntegral
public import OAI.NumberTheory.DirichletL.Detector.MellinWindows

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open ProbePhysical ProbeMellinBoundary

theorem source_profile_arithmetic_slices (mw : MellinWindows)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃K : ℝ,0<K ∧ ∀σ∈Icc slo shi,∀ξ∈Icc zlo zhi,∀υ∈Icc wlo whi,
      ∀axis : SliceAxis,∀T A : ℝ,0≤A → ∀X Y Z : ℝ,0<X → 0<Y → 0<Z →
      ∀G : ℝ×ℝ→ℂ,AEStronglyMeasurable G (volume.prod volume) →
      (∀q,‖G q‖≤A*jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J) →
      let F := fun q : ℝ×ℝ=>sourceMellinWeight mw.left mw.right X Y Z
        ((σ:ℂ)+(sliceMap axis T q).1.1*I) ((υ:ℂ)+(sliceMap axis T q).2*I)
        ((ξ:ℂ)+(sliceMap axis T q).1.2*I)*G q
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          A*K*(X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1))/height T^N := by
  obtain ⟨K,hK,hbound⟩ := profile_arithmetic_slices mw
    slo shi zlo zhi wlo whi hzlo J N
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ axis T A hA X Y Z hX hY hZ G hG hGb
  let E : ℝ := X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1)
  have hE : 0≤E := by positivity
  let S := fun q : ℝ×ℝ=>sourceScale X Y Z ((σ:ℂ)+(sliceMap axis T q).1.1*I)
    ((υ:ℂ)+(sliceMap axis T q).2*I) ((ξ:ℂ)+(sliceMap axis T q).1.2*I)
  have hc : Continuous (fun p : HeightSpace => (((σ:ℂ)+p.1.1*I,(υ:ℂ)+p.2*I),(ξ:ℂ)+p.1.2*I)) := by fun_prop
  have hS0 := (sourceScale_continuous X Y Z hX hY hZ).comp (hc.comp (sliceMap_continuous axis T))
  have hS : Continuous S := by assumption
  have hSn (q : ℝ×ℝ) : ‖S q‖=E := by
    dsimp only [S]
    rw [sourceScale_norm X Y Z hX hY hZ]
    simp [E]
  have hb (q : ℝ×ℝ) : ‖S q*G q‖≤(E*A)*jointHeight
      (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J := by
    rw [norm_mul,hSn]
    exact (mul_le_mul_of_nonneg_left (hGb q) hE).trans_eq (by ring)
  obtain ⟨hi,hb⟩ := hbound σ hσ ξ hξ υ hυ axis T (E*A) (mul_nonneg hE hA)
    (fun q=>S q*G q) (hS.aestronglyMeasurable.mul hG) hb
  have heq : (fun q : ℝ×ℝ=>sourceMellinWeight mw.left mw.right X Y Z
        ((σ:ℂ)+(sliceMap axis T q).1.1*I) ((υ:ℂ)+(sliceMap axis T q).2*I)
        ((ξ:ℂ)+(sliceMap axis T q).1.2*I)*G q)=
      (fun q=>(S q*G q)*onLines mw.left mw.right σ ξ υ (sliceMap axis T q)) := by
    funext q
    rw [sourceMellinWeight_eq_scale]
    dsimp [S,onLines]
    ring
  dsimp only
  refine ⟨heq.symm ▸ hi,?_⟩
  have hnorm := congrArg (fun f : ℝ×ℝ→ℂ => ∫q : ℝ×ℝ,‖f q‖ ∂volume.prod volume) heq
  rw [hnorm]
  calc
    _ ≤ (E*A)*K/height T^N := hb
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
