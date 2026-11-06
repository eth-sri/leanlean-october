module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.SourceMass

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.DetectorDictionaryInverseAssignedCount


def assignedTuples {ι } [Fintype ι]
    (L : ι → Finset (Ideal ActualEisensteinCubic.O))  := Fintype.piFinset L

@[simp] theorem mem_assignedTuples {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal ActualEisensteinCubic.O))  q  :
    q ∈ assignedTuples L ↔ ∀ i, q i ∈ L i := by
  simp [assignedTuples]

def assignedConstant (K : ℕ) (b : ℝ)  := (128*b)^K

theorem assignedConstant_pos  K   {b}  (hb : 1 ≤ b) :
    0 < assignedConstant K b := by
  unfold assignedConstant
  positivity

theorem list_card_le (L : Finset (Ideal ActualEisensteinCubic.O))  {H}  (hH : 0 ≤ H)
    (hL : ∀ I ∈ L, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ H) :
    (L.card : ℝ) ≤ 128*H := by
  apply le_trans (Nat.cast_le.mpr (Finset.card_le_card (t :=
    CenteredMomentSourceMass.idealBall H) ?_))
    (CenteredMomentSourceMass.idealBall_card H hH)
  intro I hI
  simp_all

theorem assigned_card_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal ActualEisensteinCubic.O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i)) :
    ((assignedTuples L).card : ℝ) ≤ assignedConstant K b * U^(∑ i, ell i) := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  
  have hbase : 1 ≤ 128*b := by linarith
  simp only [assignedTuples, Fintype.card_piFinset, Nat.cast_prod]
  calc
    (∏ i, ((L i).card : ℝ)) ≤ ∏ i, 128*(b*U^(ell i)) :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => list_card_le (L i) (by positivity) (hL i))
    _ = (128*b)^(Fintype.card ι) * U^(∑ i, ell i) := by
      simp_rw [← mul_assoc]
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hUp]
      simp
    _ ≤ assignedConstant K b * U^(∑ i, ell i) := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase hK)
        (Real.rpow_nonneg hUp.le _)

def assignedCoefficient {ι } [Fintype ι]
    (a : ι → Ideal ActualEisensteinCubic.O → ℂ) (q : ι → Ideal ActualEisensteinCubic.O)  := ∏ i, a i (q i)

theorem assignedCoefficient_norm_le_one {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal ActualEisensteinCubic.O)) (a : ι → Ideal ActualEisensteinCubic.O → ℂ)
    (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
     q  (hq : q ∈ assignedTuples L) :
    ‖assignedCoefficient a q‖ ≤ 1 := by
  rw [assignedCoefficient, norm_prod]
  simpa using Finset.prod_le_prod₀ (fun i _ => norm_nonneg (a i (q i)))
    (fun i _ => ha i (q i) ((mem_assignedTuples L q).mp hq i))

section
variable (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U) {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K) (ell : ι → ℝ) (L : ι → Finset (Ideal ActualEisensteinCubic.O)) (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i)) (a : ι → Ideal ActualEisensteinCubic.O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
include K b U hb hU ι hK ell L hL a ha

section
variable (T : Finset (ι → Ideal ActualEisensteinCubic.O)) (hT : T ⊆ assignedTuples L)
include T hT

theorem restricted_mass_le        
         
       
     
       
        :
    (∑ q ∈ T, ‖assignedCoefficient a q‖) ≤
      assignedConstant K b * U^(∑ i, ell i) := by
  calc
    (∑ q ∈ T, ‖assignedCoefficient a q‖) ≤ ∑ _q ∈ T, (1 : ℝ) :=
      Finset.sum_le_sum (fun q hq => assignedCoefficient_norm_le_one L a ha q (hT hq))
    _ = (T.card : ℝ) := by simp
    _ ≤ ((assignedTuples L).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hT)
    _ ≤ _ := assigned_card_le K hb hU hK ell L hL

theorem restricted_normalized_mass_le        
         
       
     
       
        :
    (∑ q ∈ T, ‖assignedCoefficient a q‖) * U^(-(∑ i, ell i)) ≤
      assignedConstant K b := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  calc
    _ ≤ (assignedConstant K b * U^(∑ i, ell i)) * U^(-(∑ i, ell i)) :=
      mul_le_mul_of_nonneg_right (restricted_mass_le K hb hU hK ell L hL a ha T hT)
        (Real.rpow_nonneg hUp.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hUp]; simp

theorem restricted_sum_normalized_le        
         
       
     
       
        :
    (∑ q ∈ T, ‖assignedCoefficient a q‖ * U^(-(∑ i, ell i))) ≤
      assignedConstant K b := by
  rw [← Finset.sum_mul]
  exact restricted_normalized_mass_le K hb hU hK ell L hL a ha T hT

end

theorem assigned_sum_normalized_le        
         
       
     
        :
    (∑ q ∈ assignedTuples L, ‖assignedCoefficient a q‖ * U^(-(∑ i, ell i))) ≤
      assignedConstant K b :=
  restricted_sum_normalized_le K hb hU hK ell L hL a ha _ (Finset.Subset.refl _)

end

end SevenEighths.DetectorDictionaryInverseAssignedCount

end

end OAI
