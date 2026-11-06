module

public import NearlyMinimax.AnchoredBasis
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The exact stars-and-bars cardinality of the paper's nonconstant features. -/

𝚪
𝚨

𝗃 𝔊 ∑ i, (ἀ i).val
𝗃 𝔍 ἀ d ℓ
abbrev TotalDegreeIndex (d ℓ : ℕ) :=
  {γ : 𝔍 PolynomialBox // 𝔊 γ ≤ ℓ}

𝗇 𝔅 𝔍 TotalDegreeIndex
𝗇 𝔈 Option $ Fin d
def totalDegreeSlackEquiv (d ℓ : ℕ) :
    𝔅 ≃ {v : 𝔈 → ℕ // ∑ i, v i = ℓ} where
  toFun γ := ⟨fun i => i.casesOn (ℓ - ∑ j, (γ.val j).val) fun j => (γ.val j).val , by
    rw [Fintype.sum_option]
    exact Nat.sub_add_cancel γ.property⟩
  invFun v := ⟨fun i => ⟨v.val $ some i , by
    have hi : v.val (some i) ≤ ∑ j, v.val j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) $ Finset.mem_univ _
    rw [v.property] at hi
    omega⟩, by
      have h := v.property
      rw [Fintype.sum_option] at h
      exact Nat.le.intro $ by simpa [Nat.add_comm] using h ⟩
  left_inv γ := by
    apply Subtype.ext
    funext i
    apply Fin.ext
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

𝗇 𝔉 (d + ℓ).choose d
theorem totalDegreeIndex_card d ℓ :
    Fintype.card 𝔅 = 𝔉 := by
  let e := (𝔍 totalDegreeSlackEquiv).trans (Sym.equivNatSumOfFintype 𝔈 ℓ).symm
  rw [Fintype.card_congr e, Sym.card_sym_eq_choose]
  have hc := Nat.choose_symm $ show ℓ ≤ d + ℓ by omega
  simp_all

𝗇 𝔄 𝔊 γ.val = 0
def anchoredNonzeroEquiv (d ℓ : ℕ) : 𝔍 AnchoredIndex ≃
    {γ : 𝔅 // ¬ 𝔄} where
  toFun γ := ⟨⟨γ.val, γ.property.2⟩, ne_of_gt γ.property.1⟩
  invFun γ := ⟨γ.val.val, Nat.pos_of_ne_zero γ.property, γ.val.property⟩
  left_inv γ := 𝖦₄
  right_inv γ := 𝖦₄

𝗇 𝔇 {γ : 𝔅 // 𝔄}
/-- The concrete feature dimension is exactly the manuscript's `q_s - 1`. -/
theorem anchoredIndex_card d ℓ :
    Fintype.card 𝔍 AnchoredIndex = 𝔉 - 1 := by
  classical
  let z : 𝔇 :=
    ⟨⟨𝖾, 𝖢₄⟩, 𝖢₄⟩
  letI : Unique 𝔇 :=
    { default := z
      uniq := fun γ => by
        aesop }
  rw [Fintype.card_congr 𝔍 anchoredNonzeroEquiv,
    Fintype.card_subtype_compl, totalDegreeIndex_card]
  rw [Fintype.card_unique]
