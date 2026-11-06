module

public import OAI.NumberTheory.DirichletL.Detector.HighSeries

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted

local notation "Id" => Ideal ActualEisensteinCubic.O

def highIdealMask (S : Finset Id) (D I J K L : Id)  :=
  completedMask S D I J *
    (if ∀ P∈S,¬P∣K then 1 else 0) * (if ∀ P∈S,¬P∣L then 1 else 0)

lemma highIdealMask_norm_le_one  S   D I J K L  :
    ‖highIdealMask S D I J K L‖≤1 := by
  unfold highIdealMask
  split_ifs <;> simp only [mul_one,mul_zero,norm_zero]
  · exact completedMask_norm_le_one S D I J
  all_goals norm_num

def markedIdealHighSummand (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : ActualEisensteinCubic.O) (x w z : ℂ) (I J K L : Id)  :=
  highIdealMask S D I J K L * bareIdealHighSummand η u x w z I J K L

lemma markedIdealHighSummand_norm_le  S   D   η 
     u   x w z   I J K L  :
    ‖markedIdealHighSummand S D η u x w z I J K L‖≤‖bareIdealHighSummand η u x w z I J K L‖ := by
  rw [markedIdealHighSummand,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (highIdealMask_norm_le_one S D I J K L)

theorem markedIdealHighSummand_summable  S   D   η 
     u   x w z  (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun p : (Id×Id)×(Id×Id) =>
      markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (fun p=>markedIdealHighSummand_norm_le S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2)
    (bareIdealHighSummand_summable η u x w z hx hw hz).norm

def markedIdealHighSeries (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : ActualEisensteinCubic.O) (x w z : ℂ)  :=
  ∑' p : (Id×Id)×(Id×Id), markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2

end SevenEighths.ProbePhysical
end

end OAI
