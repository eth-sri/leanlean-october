module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Hecke.RowClosure

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeExceptionalRows
open HeckeFamily UniqueFactorizationMonoid

def rows (S : Finset (Ideal O))  :=
  {u | u ≠ 0 ∧ ∀ P ∈ normalizedFactors (Ideal.span {u}),
    P ∈ S ∧ (normalizedFactors (Ideal.span {u})).count P < 6}

def bound (S : Finset (Ideal O))  := ((∏ P ∈ S, P)^5).absNorm

section
variable (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) {u : O} (hu : u ∈ rows S)


include hu in
theorem row_ideal_dvd       :
    (Ideal.span {u} : Ideal O) ∣ (∏ P ∈ S, P)^5 := by
  have hI : (Ideal.span {u} : Ideal O) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hu.1
  have hle : normalizedFactors (Ideal.span {u}) ≤ 5 • S.val := by
    apply Multiset.le_iff_count.mpr
    intro P
    by_cases hP : P ∈ normalizedFactors (Ideal.span {u})
    · have hp := hu.2 P hP
      have hc : S.val.count P = 1 := Multiset.count_eq_one_of_mem S.nodup hp.1
      rw [Multiset.count_nsmul, hc]
      omega
    · simp only [Multiset.count_eq_zero.mpr hP]
      exact Nat.zero_le _
  have hd := Multiset.prod_dvd_prod_of_le hle
  rw [Ideal.prod_normalizedFactors_eq_self hI, Multiset.prod_nsmul] at hd
  simp_all

include hS hu in
theorem row_norm_bound    
        : (Ideal.span {u}).absNorm ≤ bound S := by
  have hd := map_dvd Ideal.absNorm (row_ideal_dvd S hu)
  apply Nat.le_of_dvd _ hd
  apply Nat.pos_of_ne_zero
  rw [ne_eq, Ideal.absNorm_eq_zero_iff]
  exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero))

end

end SevenEighths.HeckeExceptionalRows

end

end OAI
