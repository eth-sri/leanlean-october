module

public import OAI.NumberTheory.DirichletL.Reflection.PuncturedMarks
public import OAI.NumberTheory.DirichletL.Reflection.SlotCoefficients
public import OAI.NumberTheory.DirichletL.Reflection.MarkedTuples

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open CanonicalRowCompletion InverseMoment
noncomputable section
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def punctureLists (lists : σ→Finset (Ideal ActualEisensteinCubic.O)) (S : Finset (Ideal ActualEisensteinCubic.O)) : σ→Finset (Ideal ActualEisensteinCubic.O) :=
  fun i => (lists i).filter (fun P => P∉S)

def punctureListLift (lists : σ→Finset (Ideal ActualEisensteinCubic.O)) (S : Finset (Ideal ActualEisensteinCubic.O))
    (p : ∀ i,punctureLists lists S i) : ∀ i,lists i :=
  fun i => ⟨(p i).val,(Finset.mem_filter.mp (p i).property).1⟩

def punctureListEquiv (lists : σ→Finset (Ideal ActualEisensteinCubic.O)) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    (∀ i,punctureLists lists S i) ≃ {p : ∀ i,lists i // ∀ i,(p i).val∉S} where
  toFun p := ⟨punctureListLift lists S p,fun i => (Finset.mem_filter.mp (p i).property).2⟩
  invFun p i := ⟨(p.val i).val,Finset.mem_filter.mpr ⟨(p.val i).property,p.property i⟩⟩
  left_inv _p := rfl
  right_inv _p := rfl

lemma sum_puncture_lists (lists : σ→Finset (Ideal ActualEisensteinCubic.O)) (S : Finset (Ideal ActualEisensteinCubic.O))
    (f : (∀ i,lists i)→ℂ) (hz : ∀ p,(∃ i,(p i).val∈S) → f p=0) :
    (∑ p : ∀ i,lists i,f p)=∑ p : ∀ i,punctureLists lists S i,f (punctureListLift lists S p) := by
  have he := (punctureListEquiv lists S).sum_comp (fun p => f p.val)
  have hs := sum_subtype_dite_decidable (fun p : ∀ i,lists i => ∀ i,(p i).val∉S) (fun p _ => f p)
  calc
    _ = ∑ p : ∀ i,lists i,if h:∀ i,(p i).val∉S then f p else 0 := by
      grind
    _ = ∑ p : {p : ∀ i,lists i // ∀ i,(p i).val∉S},f p.val := hs.symm
    _ = _ := he.symm

theorem original_completed_puncture_lists (lists : σ→Finset (Ideal ActualEisensteinCubic.O))
    (hprime : ∀ i,∀ P∈lists i,Prime P) (S : Finset (Ideal ActualEisensteinCubic.O))
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ (m*excludedGenerator S) f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    ∑ p : ∀ i,punctureLists lists S i,(∏ i,w i (punctureListLift lists S p i))*markedCompletedT
      (rowTwist Ψ (m*excludedGenerator S) f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0) := by
  apply sum_puncture_lists lists S
  intro p hp
  obtain ⟨i,hi⟩ := hp
  have hm := (p i).val.mul_mem_left m (excludedGenerator_mem S hi)
  have hz := markedCompletedT_zero_punctured Ψ (m*excludedGenerator S) f z (p i).val
    (by grind) hm W X (fun A => ∏ j,if (p j).val∣A then (1:ℂ) else 0)
    (fun A hA => Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hA))
  simp_all
end
end SevenEighths.InverseReflectedPhase

end OAI
