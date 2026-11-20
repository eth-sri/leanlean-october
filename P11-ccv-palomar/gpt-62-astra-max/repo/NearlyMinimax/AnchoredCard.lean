module

public import NearlyMinimax.AnchoredBasis


@[expose] public section

/-! The exact stars-and-bars cardinality of the paper's nonconstant features. -/

noncomputable section
open scoped BigOperators
namespace NearlyMinimax

variable (d ℓ : ℕ)

abbrev TotalDegreeIndex :=
  {γ : PolynomialBox d ℓ // (∑ i, (γ i).val) ≤ ℓ}

def totalDegreeSlackEquiv :
    TotalDegreeIndex d ℓ ≃ {v : Option (Fin d) → ℕ // ∑ i, v i = ℓ} where
  toFun γ := ⟨fun i => i.casesOn (ℓ - ∑ j, (γ.val j).val) (fun j => (γ.val j).val), by
    rw [Fintype.sum_option]
    exact Nat.sub_add_cancel γ.property⟩
  invFun v := ⟨fun i => ⟨v.val (some i), by
    have hi : v.val (some i) ≤ ∑ j, v.val j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ _)
    omega⟩, by
      bound⟩
  left_inv γ := by
    rfl
  right_inv v := by
    apply Subtype.ext
    funext i
    cases i with
    | none =>
      change ℓ - ∑ j, v.val (some j) = v.val none
      have h := v.property
      rw [Fintype.sum_option] at h
      omega
    | some i => rfl

theorem totalDegreeIndex_card :
    Fintype.card (TotalDegreeIndex d ℓ) = (d + ℓ).choose d := by
  let e := (totalDegreeSlackEquiv d ℓ).trans (Sym.equivNatSumOfFintype (Option (Fin d)) ℓ).symm
  rw [Fintype.card_congr e, Sym.card_sym_eq_choose]
  simp
  have h : d + 1 + ℓ - 1 = d + ℓ := by omega
  simpa using (Nat.choose_symm (show ℓ ≤ d + ℓ by omega)).symm

def anchoredNonzeroEquiv : AnchoredIndex d ℓ ≃
    {γ : TotalDegreeIndex d ℓ // ¬ (∑ i, (γ.val i).val) = 0} where
  toFun γ := ⟨⟨γ.val, γ.property.2⟩, ne_of_gt γ.property.1⟩
  invFun γ := ⟨γ.val.val, Nat.pos_of_ne_zero γ.property, γ.val.property⟩
  left_inv γ := rfl
  right_inv γ := rfl

/-- The concrete feature dimension is exactly the manuscript's `q_s - 1`. -/
theorem anchoredIndex_card :
    Fintype.card (AnchoredIndex d ℓ) = (d + ℓ).choose d - 1 := by
  classical
  letI : Unique {γ : TotalDegreeIndex d ℓ // (∑ i, (γ.val i).val) = 0} :=
    { default := ⟨⟨fun _ => 0, by simp⟩, by simp⟩
      uniq := fun γ => by
        apply Subtype.ext
        apply Subtype.ext
        funext i
        grind [Finset.single_le_sum (f := fun j => (γ.val.val j).val) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)] }
  rw [Fintype.card_congr (anchoredNonzeroEquiv d ℓ),
    Fintype.card_subtype_compl, totalDegreeIndex_card]
  grind [Fintype.card_unique]

end NearlyMinimax
