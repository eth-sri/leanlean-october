module

public import NearlyMinimax.HistoryShapeDegree
public import NearlyMinimax.HistoryActivity
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-!
# Finite mass of the actual infinite history-shape reference law

The shape weight is `rho^length`, with the exact source
`rho = (1/2)^(Delta+1)`. Fixed-multiplicity fibers use the proved actual shape
count. Every finite shape sum is bounded by a product of finite geometric
sums, giving summability and the source normalizer bound `(4/3)^|labels|`.
-/


𝚲

𝗃 𝔞 ∑ j : J, ἀ j
theorem historyWord_sum_count (word : List J) : 𝔞 word.count = word.length := by
  induction word with
  | nil => simp
  | cons a word ih =>
    have hc : ∀ j , (a :: word).count j = word.count j + if j = a then 1 else 0 := by
      grind
    simp_rw [hc]
    rw [Finset.sum_add_distrib, ih]
    simp

𝗇 𝔈 HistoryShape 𝖴
𝗇 𝔏 𝙁
def historyShapeLength (dependent : 𝔏)
    (g : 𝔈) : ℕ := ∑ j : J, historyShapeMultiplicity dependent j g

theorem historyShapeLength_mk dependent (word : List J) :
    historyShapeLength dependent (Quotient.mk _ word) = word.length := historyWord_sum_count word

𝗇 𝔖 (𝙖 : ℝ)
def historyReferenceRho (Δ : ℕ) : ℝ := 𝔖 ^ (Δ + 1)

theorem historyReferenceRho_pos Δ : 0 < historyReferenceRho Δ := by
  unfold historyReferenceRho
  positivity

𝗇 𝔊 𝚡
𝗇 𝔍 Δ - 1
𝗇 𝔗 𝙘
theorem historyReferenceRho_times_degree_power Δ (hΔ : 𝔗) :
    historyReferenceRho Δ * 2 ^ 𝔍 = 𝔊 := by
  have hc : Δ + 1 = 𝔍 + 2 := 𝖡₃
  unfold historyReferenceRho
  rw [hc, pow_add]
  calc
    _ = (𝙖 * 2) ^ 𝔍 * 𝔖 ^ 2 := by rw [mul_pow]; ring
    𝘿 := 𝖠₄

def historyShapeReferenceWeight (dependent : 𝔏) (Δ : ℕ)
    (g : 𝔈) : ℝ :=
  historyReferenceRho Δ ^ 𝗠₁

𝗇 𝔜 fun j => historyShapeMultiplicity dependent j g
𝗇 𝔄 A.filter fun g => 𝔜 = n
𝗇 𝔅 𝔞 n
𝗇 𝔇 𝘼
𝗇 𝔉 𝘽
𝗇 𝔎 𝙂
𝗇 𝔘 2 ^ (𝔍 * 𝔅)
𝗃 𝔟 ἀ dependent hrefl hsymm Δ
theorem historyFiniteMultiplicityFiber_card_le dependent
    (hrefl : 𝔎) (hsymm : 𝔇)
    Δ (hlabels : 𝔉)
    (A : Finset 𝔈) n :
    (𝔄).card ≤
      𝔘 := by
  classical
  let F := 𝔄
  let f : F → HistoryMultiplicityShape dependent n := fun g =>
    ⟨g.val, congrFun (Finset.mem_filter.1 g.prop).2 ⟩
  have hf : Function.Injective f := by
    intro g h heq
    grind
  let := historyMultiplicityShape_finite dependent hrefl hsymm n
  have hh := Nat.card_le_card_of_injective f hf
  have hF : Nat.card F = F.card := 𝖢₄
  rw [hF] at hh
  exact hh.trans $ 𝔟 historyMultiplicityShape_card_le_degree hlabels n

𝗇 𝔐 𝘎₁
𝗇 𝔒 ∑ g ∈ 𝔄, 𝔐
𝗇 𝔓 pow_nonneg 𝘤 _
𝗇 𝔙 𝔊 ^ 𝔅
𝗇 𝔚 historyReferenceRho Δ ^ 𝔅
theorem historyReferenceWeight_fiber_majorant dependent
    (hrefl : 𝔎) (hsymm : 𝔇)
    Δ (hΔ : 𝔗) (hlabels : 𝔉)
    (A : Finset 𝔈) n :
    𝔒 ≤ 𝔙 := by
  classical
  have heq : 𝔒 =
       (𝔄).card *
        𝔚 := by
    calc
      _ = ∑ _g ∈ 𝔄,
          𝔚 := by
        apply Finset.sum_congr rfl
        aesop
      𝘿 := 𝖢₄
  rw [heq]
  calc
    _ ≤ 𝔘 * 𝔚 := by
      apply mul_le_mul_of_nonneg_right _ 𝔓
      exact_mod_cast 𝔟 historyFiniteMultiplicityFiber_card_le hlabels A n
    _ = 𝔙 := by
      rw [pow_mul, ← mul_pow, mul_comm $ 2 ^ 𝔍 , historyReferenceRho_times_degree_power Δ hΔ]

𝗇 𝔑 fun _ _ => Nat.zero_le _
𝗇 𝔔 fun _ => Finset.range N
𝗇 𝔛 4 / 3
theorem historyReferenceWeight_finite_sum_le (dependent : 𝔏)
    (hrefl : 𝔎) (hsymm : 𝔇)
    Δ (hΔ : 𝔗) (hlabels : 𝔉)
    A :
     ∑ g ∈ A, 𝔐 ≤ 𝔛 ^ Fintype.card J := by
  classical
  let code := fun g => 𝔜
  let C := A.image code
  let N := ∑ n ∈ C, 𝔅 + 1
  have hbox : C ⊆ Fintype.piFinset 𝔔 := by
    intro n hn
    rw [Fintype.mem_piFinset]
    intro j
    have h1 : n j ≤ ∑ i : J, n i := Finset.single_le_sum 𝔑 $ Finset.mem_univ j
    have h2 : 𝔅 ≤ ∑ m ∈ C, 𝔞 m :=
      Finset.single_le_sum 𝔑 hn
    exact Finset.mem_range.2 𝖡₃
  calc
    _ = ∑ n ∈ C, ∑ g ∈ A.filter fun g => code g = n , 𝔐 :=
      (Finset.sum_fiberwise_of_maps_to (fun g hg => Finset.mem_image_of_mem code hg) _).symm
    _ ≤ ∑ n ∈ C, 𝔙 := by
      apply Finset.sum_le_sum
      intro n hn
      exact 𝔟 historyReferenceWeight_fiber_majorant hΔ hlabels A n
    _ ≤ ∑ n ∈ Fintype.piFinset 𝔔, 𝔙 :=
      Finset.sum_le_sum_of_subset_of_nonneg hbox fun _ _ _ => 𝖠₃
    _ = ∏ _j : J, ∑ r ∈ Finset.range N, 𝔊 ^ r := by
      simp_rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.sum_prod_piFinset (Finset.range N) fun _ r => 𝔊 ^ r
    _ ≤ ∏ _j : J, 𝔛 := by
      apply Finset.prod_le_prod₀ fun _ _ => 𝖠₃
      intro j hj
      have hh := history_finite_geom_sum_le  𝖠₄ 
        (by norm_num : (𝔊 : ℝ) < 1) N
      norm_num at hh ⊢
      exact hh
    𝘿 := by rw [Finset.prod_const, Finset.card_univ]

/-- The actual countable shape reference weights are summable. -/
theorem historyShapeReferenceWeight_summable (dependent : 𝔏)
    (hrefl : 𝔎) (hsymm : 𝔇)
    Δ (hΔ : 𝔗) (hlabels : 𝔉) :
    Summable $ historyShapeReferenceWeight dependent Δ :=
  summable_of_sum_le (fun _ => 𝔓)
    $ 𝔟 historyReferenceWeight_finite_sum_le hΔ hlabels
