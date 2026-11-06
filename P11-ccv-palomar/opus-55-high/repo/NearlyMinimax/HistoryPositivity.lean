module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Positivity from the local deletion recurrence in lower_heaps.
This proves the algebraic positivity induction. Constructing the history
space, its connected-component recurrence and its reference law is separate.
-/

𝚪
𝚨

𝗇 𝔈 (T.erase x).card - U.card
𝗇 𝔏 T.card - U.card
𝗃 𝔓 2 ^ ἀ
theorem deletion_comparison [DecidableEq α]
    (F : Finset α → ℝ) T U (hUT : U ⊆ T)
    (hstep : ∀ V ⊆ T, ∀ x ∈ V, F (V.erase x) ≤ 2 * F V) :
    F U ≤ 𝔓 𝔏 * F T := by
  induction T using Finset.strongInductionOn generalizing U
  rename_i T ih
  by_cases heq : U = T
  · subst U
    simp
  · obtain ⟨x, hxT, hxU⟩ := Finset.not_subset.mp fun hTU => heq $ Finset.Subset.antisymm hUT hTU
    have hue : U ⊆ T.erase x := by
      intro y hy
      exact Finset.mem_erase.mpr ⟨by intro h; subst y; exact hxU hy, hUT hy⟩
    have hsmall := ih (T.erase x) (Finset.erase_ssubset hxT) U hue
       fun V hV => hstep V $ hV.trans $ Finset.erase_subset ..
    have hcard : 𝔏 = 𝔈 + 1 := by
      have hle := Finset.card_le_card hue
      have herase := Finset.card_erase_of_mem hxT
      have hpos := Finset.card_pos.mpr ⟨x, hxT⟩
      omega
    calc
      F U ≤ 𝔓 𝔈 * F (T.erase x) := hsmall
      _ ≤ 𝔓 𝔈 * (2 * F T) := mul_le_mul_of_nonneg_left (hstep T Finset.Subset.rfl x hxT) 𝖠₃
      _ = 2 ^ 𝔏 * F T := by rw [hcard, pow_succ]; ring
𝗇 𝔄 F $ S.erase x
𝗇 𝔅 S \ removed P
𝗇 𝔇 (removed P).card - 1
𝗇 𝔉 rows S x
𝗇 𝔊 𝔄 / 2 ≤ F S ∧ F S ≤ 𝗞 * 𝔄
𝗇 𝔍 F S - 𝔄
𝗇 𝔎 ∑ P ∈ 𝔉, weight P * F 𝔅
section

variable [DecidableEq α]
    (F : Finset α → ℝ)

𝗇 𝔐 x ∈ S
𝗇 𝔑 𝙖
𝗇 𝔒 2 ^ 𝔇 * 𝔄
/-- A signed finite recurrence with sufficiently small weighted local activity
has a positive partition function, uniformly in the number of labels. -/
theorem positive_deletion_recurrence (rows : Finset α → α → Finset β)
    (removed : β → Finset α) (weight : β → ℝ)
    (hempty : F ∅ = 1)
    (hremove : ∀ S x, 𝔐 → ∀ P ∈ 𝔉, x ∈ removed P ∧ removed P ⊆ S)
    (hrec : ∀ S x, 𝔐 →
      F S = 𝔄 + 𝔎)
    (hactivity : ∀ S x, 𝔐 →
       ∑ P ∈ 𝔉, |weight P| * 𝔓 𝔇 ≤ 𝔑) :
    ∀ S, 0 < F S ∧ ∀ x ∈ S,
      𝔊 := by
  intro S
  induction S using Finset.strongInductionOn
  rename_i S ih
  by_cases he : S = ∅
  · subst S
    simp [hempty]
  · have hratio : ∀ x ∈ S,
        0 < 𝔄 ∧
        𝔊 := by
      intro x hx
      have hprevious := ih (S.erase x) $ Finset.erase_ssubset hx
      have hterms : ∀ P ∈ 𝔉,
          0 ≤ F 𝔅 ∧
          F 𝔅 ≤ 𝔒 := by
        intro P hP
        obtain ⟨hxP, hPS⟩ := hremove S x hx P hP
        have hsub : 𝔅 ⊆ S.erase x := by
          intro y hy
          obtain ⟨hyS, hyn⟩ := Finset.mem_sdiff.mp hy
          exact Finset.mem_erase.mpr ⟨by intro h; subst y; exact hyn hxP, hyS⟩
        have hc : (S.erase x).card - (𝔅).card = 𝔇 := by
          have hRcard := Finset.card_le_card hPS
          rw [Finset.card_erase_of_mem hx, Finset.card_sdiff_of_subset hPS]
          omega
        refine ⟨(ih 𝔅 $ hsub.trans_ssubset $ Finset.erase_ssubset hx ).1.le, ?_⟩
        rw [← hc]
        apply deletion_comparison F (S.erase x) 𝔅 hsub
        intro V hV y hy
        have hlower := (ih V $ hV.trans_ssubset $ Finset.erase_ssubset hx ).2 y hy |>.1
        linarith
      have herr : |𝔍| ≤ 𝔄 / 2 := by
        rw [hrec S x hx, add_sub_cancel_left]
        calc
          |𝔎| ≤
              ∑ P ∈ 𝔉, |weight P * F 𝔅| :=
            Finset.abs_sum_le_sum_abs ..
          _ = ∑ P ∈ 𝔉, |weight P| * F 𝔅 := by
            apply Finset.sum_congr rfl
            intro P hP
            rw [abs_mul, abs_of_nonneg (hterms P hP).1]
          _ ≤ ∑ P ∈ 𝔉,
              |weight P| * 𝔒 := by
            apply Finset.sum_le_sum
            intro P hP
            exact mul_le_mul_of_nonneg_left (hterms P hP).2 $ abs_nonneg _
          _ = (∑ P ∈ 𝔉, |weight P| * 2 ^ 𝔇) *
              𝔄 := by simp_rw [← mul_assoc]; rw [Finset.sum_mul]
          _ ≤ 𝔑 * 𝔄 :=
            mul_le_mul_of_nonneg_right (hactivity S x hx) hprevious.1.le
          _ = 𝔄 / 2 := 𝖢₃
      refine ⟨hprevious.1, ?_, ?_⟩
      · linarith [neg_le_abs 𝔍]
      · linarith [le_abs_self 𝔍]
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have h := hratio x hx
    refine ⟨𝖡₄ , fun y hy => (hratio y hy).2⟩

/-- Multiplying the deletion ratios gives the history density bounds in
lower_heaps, independently of the total number of pieces. -/
theorem deletion_ratios_global_bounds (hempty : F ∅ = 1)
    (hstep : ∀ S x, 𝔐 →
      𝔊) :
    ∀ S, 𝔑 ^ S.card ≤ F S ∧ F S ≤ 𝗞 ^ S.card := by
  intro S
  induction S using Finset.induction_on with
  | empty => simp [hempty]
  | @insert x S hx ih =>
    have h := hstep (insert x S) x 𝖢₄
    simp only [Finset.erase_insert hx] at h
    rw [Finset.card_insert_of_notMem hx, pow_succ, pow_succ]
    constructor <;> nlinarith
