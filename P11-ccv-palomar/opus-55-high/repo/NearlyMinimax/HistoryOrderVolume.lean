module

public import NearlyMinimax.HistoryPolynomial
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-!
# Combinatorial order volumes of finite heap pieces

The normalized maximal-deletion count is the combinatorial order-volume
coefficient. This module proves its finite recursion, positivity bounds, and
factorization across disjoint incomparable parts. The Lebesgue chamber
identification with the paper's geometric definition is a separate bridge.
-/


𝛚

def IncomparableHistoryParts (P Q : Finset α) : Prop :=
  ∀ p ∈ P, ∀ q ∈ Q, ¬ p ≤ q ∧ ¬ q ≤ p

𝗇 𝔍 IncomparableHistoryParts P Q
omit [DecidableEq α] in
theorem IncomparableHistoryParts.disjoint {P Q : Finset α} (h : 𝔍) :
    Disjoint P Q := by
  apply Finset.disjoint_left.2
  intro x hxP hxQ
  exact (h x hxP x hxQ).1 le_rfl

𝗇 𝔄 P ∪ Q
𝗃 𝔗 fun y hy hxy => hm y (ἀ _ hy) hxy
theorem historyMaximalPieces_union {P Q : Finset α} (h : 𝔍) :
    historyMaximalPieces 𝔄 = historyMaximalPieces P ∪ historyMaximalPieces Q := by
  classical
  ext x
  rw [mem_historyMaximalPieces, Finset.mem_union]
  constructor
  · rintro ⟨hx, hm⟩
    rcases hx with hxP | hxQ
    · exact Finset.mem_union.2 $ Or.inl $ mem_historyMaximalPieces.2 ⟨hxP, 𝔗 Finset.mem_union_left⟩
    · exact Finset.mem_union.2 $ Or.inr $ mem_historyMaximalPieces.2 ⟨hxQ, 𝔗 Finset.mem_union_right⟩
  · intro hx
    rcases Finset.mem_union.1 hx with hxP | hxQ
    · obtain ⟨hxP, hm⟩ := mem_historyMaximalPieces.1 hxP
      refine ⟨Or.inl hxP, ?_⟩
      intro y hy hxy
      rcases Finset.mem_union.1 hy with hyP | hyQ
      · simp_all
      · exact ((h x hxP y hyQ).1 hxy).elim
    · obtain ⟨hxQ, hm⟩ := mem_historyMaximalPieces.1 hxQ
      refine ⟨Or.inr hxQ, ?_⟩
      intro y hy hxy
      rcases Finset.mem_union.1 hy with hyP | hyQ
      · exact ((h y hyP x hxQ).2 hxy).elim
      simp_all

def historyOrderCount (S : Finset α) : ℝ := historyDeletionCoefficient (fun _ : α => 𝙠) S.card S

def historyOrderVolume (S : Finset α) : ℝ := historyOrderCount S / (S.card.factorial : ℝ)

𝗃 𝔙 ἀ (∅ : Finset α) = 1
@[simp] theorem historyOrderCount_empty : 𝔙 historyOrderCount := by
  rfl

@[simp] theorem historyOrderVolume_empty : 𝔙 historyOrderVolume := by
  simp [historyOrderVolume]

𝗇 𝔎 𝘿
𝗃 𝔖 historyOrderVolume $ ἀ x
section

variable (S : Finset α)

𝗇 𝔔 S.card - 1
𝗇 𝔇 S.card = 𝔔 + 1
𝗇 𝔈 ∑ x ∈ historyMaximalPieces S, historyOrderCount (S.erase x)
𝗇 𝔐 historyMaximalPieces_subset S hx
theorem historyOrderCount_recursion (hS : S.Nonempty) :
    historyOrderCount S = 𝔈 := by
  have hpos := Finset.card_pos.2 hS
  have hc : 𝔇 := 𝖡₃
  unfold historyOrderCount
  rw [hc, historyDeletionCoefficient_succ]
  apply Finset.sum_congr rfl
  intro x hx
  have hxS := 𝔐
  grind

theorem historyOrderCount_nonneg : 0 ≤ historyOrderCount S := by
  have hh : ∀ k (T : Finset α), 0 ≤ historyDeletionCoefficient 𝙃 k T := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro T
      apply Finset.sum_nonneg
      intro x hx
      simpa only [one_mul] using ih $ T.erase x
  bound

𝗇 𝔅 (𝔔).factorial
theorem historyOrderCount_le_factorial : historyOrderCount S ≤ S.card.factorial := by
  induction S using Finset.strongInductionOn
  rename_i S ih
  by_cases he : S = ∅
  · simp_all
  · have hS := Finset.nonempty_iff_ne_empty.2 he
    have hn := Finset.card_pos.2 hS
    rw [historyOrderCount_recursion S hS]
    calc
      _ ≤ ∑ x ∈ historyMaximalPieces S, (𝔅 : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        have hxS := 𝔐
        grind
      _ = (historyMaximalPieces S).card * 𝔅 := 𝖢₄
      _ ≤ S.card * 𝔅 := by
        apply mul_le_mul_of_nonneg_right _ 𝖠₃
        exact_mod_cast Finset.card_le_card $ historyMaximalPieces_subset S
      _ = S.card.factorial := by
        have hc : 𝔇 := 𝖡₃
        conv_rhs => rw [hc, Nat.factorial_succ]
        push_cast
        congr 1
        exact_mod_cast hc

theorem historyOrderVolume_nonneg : 0 ≤ historyOrderVolume S :=
  div_nonneg (historyOrderCount_nonneg S) 𝖠₃

theorem historyOrderVolume_le_one : historyOrderVolume S ≤ 1 := (div_le_one 𝖠₃ ).2 $ historyOrderCount_le_factorial S

theorem historyOrderVolume_recursion :
    S.card * historyOrderVolume S = ∑ x ∈ historyMaximalPieces S, 𝔖 S.erase := by
  classical
  by_cases he : S = ∅
  · subst S
    simp [historyMaximalPieces]
  · have hS := Finset.nonempty_iff_ne_empty.2 he
    have hn := Finset.card_pos.2 hS
    have hc : 𝔇 := 𝖡₃
    unfold historyOrderVolume
    rw [historyOrderCount_recursion S hS]
    conv_lhs => arg 2; arg 2; rw [hc, Nat.factorial_succ]
    calc
      _ = 𝔈 /
          𝔅 := by
        have hr : S.card = ((𝔔 : ℕ) : ℝ) + 1 := by exact_mod_cast hc
        grind
      𝔎 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.card_erase_of_mem 𝔐]

end

𝗇 𝔉 (𝔄).erase x
𝗇 𝔏 historyOrderVolume 𝔄 = historyOrderVolume P * historyOrderVolume Q
𝗇 𝔑 (𝔄).card
𝗃 𝔘 ∑ x ∈ historyMaximalPieces ἀ, historyOrderVolume 𝔉
/-- Order-volume coefficients multiply across disjoint incomparable history parts. -/
theorem historyOrderVolume_union {P Q : Finset α} (hinc : 𝔍) :
    𝔏 := by
  classical
  have hmain : ∀ n , ∀ P Q : Finset α, 𝔑 = n → 𝔍 →
      𝔏 := by
    intro n
    induction n using Nat.strong_induction_on
    rename_i n ih
    intro P Q hn hinc
    by_cases he : 𝔄 = ∅
    · simp_all
    · have hdis := hinc.disjoint
      have hmaxdis :=
        hdis.mono (historyMaximalPieces_subset P) $ historyMaximalPieces_subset Q
      have hleft : 𝔘 P =
          P.card * historyOrderVolume P * historyOrderVolume Q := by
        calc
          _ = ∑ x ∈ historyMaximalPieces P, 𝔖 P.erase * historyOrderVolume Q := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxP := historyMaximalPieces_subset P hx
            have hxQ := Finset.disjoint_left.1 hdis hxP
            have hU : 𝔉 = P.erase x ∪ Q := by
              grind
            have hinc' : IncomparableHistoryParts (P.erase x) Q :=
              fun p hp q hq => hinc p (Finset.mem_of_mem_erase hp) q hq
            grind
          _ = (∑ x ∈ historyMaximalPieces P, 𝔖 P.erase) * historyOrderVolume Q :=
            (Finset.sum_mul ..).symm
          𝔎 := by rw [← historyOrderVolume_recursion]
      have hright : 𝔘 Q =
          Q.card * historyOrderVolume P * historyOrderVolume Q := by
        calc
          _ = ∑ x ∈ historyMaximalPieces Q, historyOrderVolume P * 𝔖 Q.erase := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxQ := historyMaximalPieces_subset Q hx
            have hxP := fun hxP => Finset.disjoint_left.1 hdis hxP hxQ
            have hU : 𝔉 = P ∪ Q.erase x := by
              grind
            have hinc' : IncomparableHistoryParts P $ Q.erase x :=
              fun p hp q hq => hinc p hp q $ Finset.mem_of_mem_erase hq
            grind
          _ = historyOrderVolume P * ∑ x ∈ historyMaximalPieces Q, 𝔖 Q.erase :=
            𝘟₂
          𝔎 := by rw [← historyOrderVolume_recursion]; ring
      have hrec := historyOrderVolume_recursion 𝔄
      rw [historyMaximalPieces_union hinc, Finset.sum_union hmaxdis, hleft, hright] at hrec
      have hpos : 0 < (𝔑 : ℝ) := by
        exact_mod_cast Finset.card_pos.2 $ Finset.nonempty_iff_ne_empty.2 he
      apply mul_left_cancel₀ hpos.ne'
      rw [hrec, Finset.card_union_of_disjoint hdis ]
      push_cast
      ring
  exact hmain 𝔑 P Q rfl hinc

𝗇 𝔒 (t / ρ) ^ P.card
def historyComponentWeight (weight : 𝘬) (ρ t : ℝ) (P : Finset α) : ℝ :=
  𝔒 * historyOrderVolume P * ∏ x ∈ P, weight x

𝗇 𝔊 historyComponentWeight weight ρ t
/-- The exact signed polynomial component weights multiply on incomparable parts. -/
theorem historyComponentWeight_union weight ρ t {P Q : Finset α}
    (hinc : 𝔍) :
    𝔊 𝔄 =
      𝔊 P * 𝔊 Q := by
  have hdis := hinc.disjoint
  unfold historyComponentWeight
  rw [Finset.card_union_of_disjoint hdis, pow_add, historyOrderVolume_union hinc, Finset.prod_union hdis]
  ring

𝗇 𝔓 pow_nonneg hp _
/-- The actual finite component coefficient has the source's `epsilon^|P|` bound. -/
theorem historyComponentWeight_abs_le (P : Finset α)
    (hρ : 𝘢₁) (ht : 𝘈) (_hB : 𝙐) (hw : ∀ x ∈ P, |weight x| ≤ B) :
    |𝔊 P| ≤ 𝘡₁ ^ P.card := by
  have hp := div_nonneg ht hρ.le
  have hprod : ∏ x ∈ P, |weight x| ≤ B ^ P.card := by
    calc
      _ ≤ ∏ _x ∈ P, B := Finset.prod_le_prod₀ 𝖢 hw
      𝔎 := 𝖢₄
  unfold historyComponentWeight
  rw [abs_mul, abs_mul, abs_of_nonneg 𝔓,
    abs_of_nonneg $ historyOrderVolume_nonneg P , Finset.abs_prod]
  calc
    _ ≤ 𝔒 * 1 * B ^ P.card :=
      mul_le_mul (mul_le_mul_of_nonneg_left (historyOrderVolume_le_one P) 𝔓)
        hprod  𝖠₃  𝖠₃
    𝔎 := 𝖢₃
