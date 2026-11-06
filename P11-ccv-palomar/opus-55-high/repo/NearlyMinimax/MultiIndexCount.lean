module

public import NearlyMinimax.HighPriorModel
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Stars-and-bars bound for the manuscript's distinct mixed partials. -/
𝚸
𝚳
𝚨
𝚩
𝚰
𝚬

𝗇 𝔅 𝘛
𝗇 𝔐 𝗅₁
𝗇 𝔈 ∑ r, 𝔐
𝗇 𝔊 Fin 𝗞₁
def boundedMultiIndexMultiset (d ℓ : ℕ) (γ : 𝔅) : Multiset 𝔊 :=
   ∑ r, Multiset.replicate 𝔐 r.castSucc +
    Multiset.replicate (ℓ - 𝔈) (Fin.last d)

𝗇 𝔍 boundedMultiIndexMultiset d ℓ γ
theorem boundedMultiIndexMultiset_card d ℓ γ
    (hγ : 𝔈 ≤ ℓ) :
    (𝔍).card = ℓ := by
  simp only [boundedMultiIndexMultiset, Multiset.card_add, Multiset.card_sum,
    Multiset.card_replicate]
  omega

theorem boundedMultiIndexMultiset_count d ℓ γ r :
    (𝔍).count r.castSucc = 𝔐 := by
  simp only [boundedMultiIndexMultiset, Multiset.count_add, Multiset.count_sum',
    Multiset.count_replicate]
  have hlast : Fin.last d ≠ r.castSucc := by
    grind
  simp_all

𝗇 𝔉 (d + ℓ).choose d
𝗇 𝔎 fun γ : 𝔅 => 𝔈 ≤ ℓ
theorem bounded_multiIndex_count_le d ℓ :
    (Finset.univ.filter 𝔎).card ≤
      𝔉 := by
  let A := Finset.univ.filter 𝔎
  let encode : A → Sym 𝔊 ℓ := fun γ =>
    ⟨𝔍, boundedMultiIndexMultiset_card d ℓ γ
      (Finset.mem_filter.mp γ.property).2⟩
  have hinj : Function.Injective encode := by
    intro γ δ he
    apply Subtype.ext
    funext r
    apply Fin.ext
    have hm := congrArg (fun s => s.val.count r.castSucc) he
    change (𝔍).count r.castSucc =
      (boundedMultiIndexMultiset d ℓ δ).count r.castSucc at hm
    simpa only [boundedMultiIndexMultiset_count] using hm
  have hc := Fintype.card_le_of_injective encode hinj
  rw [Fintype.card_coe, Sym.card_sym_eq_choose, Fintype.card_fin] at hc
  have hsum : 𝗞₁ + ℓ - 1 = d + ℓ := 𝖡₃
  rw [hsum, ← Nat.choose_symm 𝖡₃ ] at hc
  grind

𝗇 𝔄 multiPartial F fun i => 𝘇
𝗇 𝔇 ∑ i, 𝘇
𝗇 𝔏 𝔇 ≤ ℓ
theorem holderNorm_of_global_mixed_bounds_binomial U
    F ℓ (α B L : ℝ) (hB : 𝙐) (hL : 𝘨)
    (hsup : ∀ γ : 𝔅, 𝔏 →
      ∀ x, |𝔄 x| ≤ B)
    (hmod : ∀ γ : 𝔅, 𝔇 = ℓ → ∀ x y,
      |𝔄 x - 𝔄 y| ≤
        L * euclideanNorm 𝘌 ^ α) :
    𝘍₂ ℓ α ≤ ENNReal.ofReal ((𝔉 : ℝ) * B + L) := by
  have hs (γ : 𝔅) (hγ : 𝔏) :
      derivativeSup U 𝔄 ≤ ENNReal.ofReal B := by
    apply iSup_le
    simp_all
  have hh (γ : 𝔅) (hγ : 𝔇 = ℓ) :
      holderSeminorm U 𝔄 α ≤ ENNReal.ofReal L := by
    apply iSup_le
    intro x
    apply iSup_le
    intro y
    by_cases hxy : 𝘱₁
    · simp_all
    · simp only [𝚙₁]
      apply ENNReal.ofReal_le_ofReal
      apply 𝘴
      simp_all
  let A := Finset.univ.filter fun γ : 𝔅 => 𝔏
  have hsum : (∑ γ : 𝔅,
      if 𝔏 then
        derivativeSup U 𝔄 else 0) ≤
      ENNReal.ofReal (𝔉 * B) := by
    calc
      _ = ∑ γ ∈ A, derivativeSup U 𝔄 := by
        rw [Finset.sum_filter]
      _ ≤ ∑ _γ ∈ A, ENNReal.ofReal B := by
        apply Finset.sum_le_sum
        aesop
      _ = ENNReal.ofReal (A.card * B) := by
        simp
      𝖦 := ENNReal.ofReal_le_ofReal $ mul_le_mul_of_nonneg_right
        (by exact_mod_cast bounded_multiIndex_count_le d ℓ) hB
  have hsem : (⨆ γ : 𝔅, if 𝔇 = ℓ then
      holderSeminorm U 𝔄 α else 0) ≤ ENNReal.ofReal L := by
    aesop
  unfold holderNorm
  rw [ENNReal.ofReal_add (𝚍₁ hB) hL]
  bound
