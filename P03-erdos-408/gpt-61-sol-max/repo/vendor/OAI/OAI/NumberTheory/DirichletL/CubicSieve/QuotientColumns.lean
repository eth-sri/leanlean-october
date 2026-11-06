module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.CubicSieve.CompactDescent

@[expose] public section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve
noncomputable section


lemma finite_sum_restrict {n A : Type*} [Fintype n] [AddCommMonoid A]
    (p : n → Prop) (f : n → A) (hf : ∀ j, ¬p j → f j = 0) :
    (∑ j, f j) = ∑ j : {j // p j}, f j.val := by
  have h := Fintype.sum_subtype_add_sum_subtype p f
  have hz : (∑ j : {j // ¬p j}, f j.val) = 0 :=
    Finset.sum_eq_zero (fun j hj => hf j.val j.property)
  rw [hz, add_zero] at h
  exact h.symm

lemma cubicSmoothedCoprime_restrict {n : Type*} [Fintype n]
    (cols : n → Ideal ActualEisensteinCubic.O) (a : n → ℂ) (p : n → Prop)
    (ha : ∀ j, ¬p j → a j = 0)  W   M  :
    cubicSmoothedCoprime cols a W M =
      cubicSmoothedCoprime (fun j : {j // p j} => cols j.val) (fun j => a j.val) W M := by
  unfold cubicSmoothedCoprime
  rw [finite_sum_restrict p _ (by
    intro j hj
    simp [ha j hj])]
  apply Finset.sum_congr rfl
  grind [finite_sum_restrict]

def quotientColumn {n : Type*} (D ) (cols : n → Ideal ActualEisensteinCubic.O)
    (j : {j // D ∣ cols j})  := idealQuotient D (cols j.val)

def quotientCoefficient {n } (D ) (cols : n → Ideal ActualEisensteinCubic.O)
    (a : n → ℂ) (d : ActualEisensteinCubic.O) (j : {j // D ∣ cols j})  :=
  cubicRow (quotientColumn D cols j) d * a j.val

section
variable {n : Type*}
include n

section
variable (D : Ideal ActualEisensteinCubic.O) (cols : n → Ideal ActualEisensteinCubic.O)
include D cols

lemma quotientColumn_injective      
    (hc : Function.Injective cols) : Function.Injective (quotientColumn D cols) := by
  intro j k he
  exact Subtype.ext (hc (idealQuotient_injective_on D j.property k.property he))

section
variable (hc : ∀ j, Admissible (cols j))
include hc

lemma quotientColumn_admissible      
      (j : {j // D ∣ cols j}) :
    Admissible (quotientColumn D cols j) := cubic_admissible_quotient (hc j.val) j.property

lemma cubic_quotient_in_shell      
       N 
    (hcols : ∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (j : {j // D ∣ cols j}) :
    (N / (Ideal.absNorm D : ℝ))/2 ≤ (Ideal.absNorm (quotientColumn D cols j) : ℝ) ∧
      (Ideal.absNorm (quotientColumn D cols j) : ℝ) ≤ N / (Ideal.absNorm D : ℝ) := by
  have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero (primaryGenerator_ne_zero_ideal _ (hc j.val).2) j.property
  have hDN : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0)
  have he : (Ideal.absNorm (quotientColumn D cols j) : ℝ) * (Ideal.absNorm D : ℝ) =
      (Ideal.absNorm (cols j.val) : ℝ) := by
    rw [mul_comm, ← Nat.cast_mul, ← map_mul, quotientColumn, idealQuotient_mul j.property]
  refine ⟨?_, idealQuotient_norm_le hD0 j.property N (hcols j.val).2⟩
  have hh : (N/2) / (Ideal.absNorm D : ℝ) ≤ (Ideal.absNorm (quotientColumn D cols j) : ℝ) := by
    apply (div_le_iff₀ hDN).mpr
    rw [he]
    exact (hcols j.val).1
  convert hh using 1; ring

end

end

section
variable [Fintype n] (D : Ideal ActualEisensteinCubic.O) (cols : n → Ideal ActualEisensteinCubic.O) (a : n → ℂ) (d : ActualEisensteinCubic.O)
include D cols a d

lemma compact_descendant_restrict    
           
     W   M  :
    cubicSmoothedCoprime (fun j => totalQuotient D (cols j))
      (descendedCoefficient D cols a d) W M =
    cubicSmoothedCoprime (quotientColumn D cols) (quotientCoefficient D cols a d) W M := by
  rw [cubicSmoothedCoprime_restrict _ _ (fun j => D ∣ cols j) (by
    simp_all [descendedCoefficient])]
  have hc : (fun j : {j // D ∣ cols j} => totalQuotient D (cols j.val)) = quotientColumn D cols := by
    grind [totalQuotient, quotientColumn]
  have ha : (fun j : {j // D ∣ cols j} => descendedCoefficient D cols a d j.val) =
      quotientCoefficient D cols a d := by
    grind [descendedCoefficient, totalQuotient, quotientCoefficient, quotientColumn]
  rw [hc, ha]

lemma quotientCoefficient_energy    
            :
    (∑ j : {j // D ∣ cols j}, ‖quotientCoefficient D cols a d j‖^2) =
      ∑ j, ‖descendedCoefficient D cols a d j‖^2 := by
  rw [finite_sum_restrict (fun j => D ∣ cols j) _ (by
    simp_all [descendedCoefficient])]
  apply Finset.sum_congr rfl
  grind [quotientCoefficient, quotientColumn, descendedCoefficient, totalQuotient]

end

end

end
end SevenEighths.CubicSieve

end OAI
