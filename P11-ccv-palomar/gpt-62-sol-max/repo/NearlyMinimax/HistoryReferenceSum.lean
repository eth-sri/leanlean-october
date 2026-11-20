module

public import NearlyMinimax.HistoryShapeDegree
public import NearlyMinimax.HistoryActivity

@[expose] public section

/-!
# Finite mass of the actual infinite history-shape reference law

The shape weight is `rho^length`, with the exact source
`rho = (1/2)^(Delta+1)`. Fixed-multiplicity fibers use the proved actual shape
count. Every finite shape sum is bounded by a product of finite geometric
sums, giving summability and the source normalizer bound `(4/3)^|labels|`.
-/

noncomputable section
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyWord_sum_count (word : List J) : (∑ j : J, word.count j) = word.length := by
  induction word with
  | nil => simp
  | cons a word ih =>
    have hc : ∀ j : J, (a :: word).count j = word.count j + if j = a then 1 else 0 := by
      grind
    simp_rw [hc]
    rw [Finset.sum_add_distrib, ih]
    simp

def historyShapeLength (dependent : J → J → Prop)
    (g : HistoryShape (fun a b => ¬ dependent a b)) : ℕ := ∑ j : J, historyShapeMultiplicity dependent j g

theorem historyShapeLength_mk (dependent : J → J → Prop) (word : List J) :
    historyShapeLength dependent (Quotient.mk _ word) = word.length := historyWord_sum_count word

def historyReferenceRho (Δ : ℕ) : ℝ := (1 / 2 : ℝ) ^ (Δ + 1)

section
variable (Δ : ℕ)

theorem historyReferenceRho_pos : 0 < historyReferenceRho Δ := by
  unfold historyReferenceRho
  positivity

theorem historyReferenceRho_times_degree_power (hΔ : 1 ≤ Δ) :
    historyReferenceRho Δ * (2 : ℝ) ^ (Δ - 1) = 1 / 4 := by
  have hc : Δ + 1 = (Δ - 1) + 2 := by omega
  unfold historyReferenceRho
  rw [hc, pow_add]
  calc
    _ = ((1 / 2 : ℝ) * 2) ^ (Δ - 1) * (1 / 2 : ℝ) ^ 2 := by rw [mul_pow]; ring
    _ = _ := by norm_num

end

def historyShapeReferenceWeight (dependent : J → J → Prop) (Δ : ℕ)
    (g : HistoryShape (fun a b => ¬ dependent a b)) : ℝ :=
  historyReferenceRho Δ ^ historyShapeLength dependent g

section
variable {dependent : J → J → Prop} {Δ : ℕ}
    (geom : HistoryDegreeBound dependent Δ)
include geom

theorem historyFiniteMultiplicityFiber_card_le
    (A : Finset (HistoryShape (fun a b => ¬ dependent a b))) (n : J → ℕ) :
    (A.filter (fun g => (fun j => historyShapeMultiplicity dependent j g) = n)).card ≤
      2 ^ ((Δ - 1) * ∑ j : J, n j) := by
  classical
  let F := A.filter (fun g => (fun j => historyShapeMultiplicity dependent j g) = n)
  let f : F → HistoryMultiplicityShape dependent n := fun g =>
    ⟨g.val, fun j => congrFun (Finset.mem_filter.1 g.prop).2 j⟩
  have hf : Function.Injective f := by
    intro g h heq <;> grind
  let : Finite (HistoryMultiplicityShape dependent n) := historyMultiplicityShape_finite dependent geom.refl geom.symm n
  have hh := Nat.card_le_card_of_injective f hf
  have hF : Nat.card F = F.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hF] at hh
  exact hh.trans (historyMultiplicityShape_card_le_degree geom n)

section
variable (hΔ : 1 ≤ Δ)
include hΔ

theorem historyReferenceWeight_fiber_majorant
    (A : Finset (HistoryShape (fun a b => ¬ dependent a b))) (n : J → ℕ) :
    (∑ g ∈ A.filter (fun g => (fun j => historyShapeMultiplicity dependent j g) = n),
      historyShapeReferenceWeight dependent Δ g) ≤ (1 / 4 : ℝ) ^ (∑ j : J, n j) := by
  classical
  have heq : (∑ g ∈ A.filter (fun g => (fun j => historyShapeMultiplicity dependent j g) = n),
      historyShapeReferenceWeight dependent Δ g) =
      ((A.filter (fun g => (fun j => historyShapeMultiplicity dependent j g) = n)).card : ℝ) *
        historyReferenceRho Δ ^ (∑ j : J, n j) := by
    calc
      _ = ∑ _g ∈ A.filter (fun g => (fun j => historyShapeMultiplicity dependent j g) = n),
          historyReferenceRho Δ ^ (∑ j : J, n j) := by
        apply Finset.sum_congr rfl
        intro g hg
        have he := (Finset.mem_filter.1 hg).2
        unfold historyShapeReferenceWeight historyShapeLength
        rw [he]
      _ = _ := by simp
  rw [heq]
  calc
    _ ≤ (2 : ℝ) ^ ((Δ - 1) * ∑ j : J, n j) * historyReferenceRho Δ ^ (∑ j : J, n j) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (historyReferenceRho_pos Δ).le _)
      exact_mod_cast historyFiniteMultiplicityFiber_card_le geom A n
    _ = (1 / 4 : ℝ) ^ (∑ j : J, n j) := by
      rw [pow_mul, ← mul_pow, mul_comm ((2 : ℝ) ^ (Δ - 1)), historyReferenceRho_times_degree_power Δ hΔ]

theorem historyReferenceWeight_finite_sum_le
    (A : Finset (HistoryShape (fun a b => ¬ dependent a b))) :
    (∑ g ∈ A, historyShapeReferenceWeight dependent Δ g) ≤ (4 / 3 : ℝ) ^ Fintype.card J := by
  classical
  let code := fun g => (fun j => historyShapeMultiplicity dependent j g)
  let C := A.image code
  let N := (∑ n ∈ C, ∑ j : J, n j) + 1
  have hmap : ∀ g ∈ A, code g ∈ C := fun g hg => Finset.mem_image_of_mem code hg
  have hbox : C ⊆ Fintype.piFinset (fun _ : J => Finset.range N) := by
    intro n hn
    rw [Fintype.mem_piFinset]
    intro j
    have h1 : n j ≤ ∑ i : J, n i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : (∑ j : J, n j) ≤ ∑ m ∈ C, ∑ j : J, m j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hn
    grind
  calc
    _ = ∑ n ∈ C, ∑ g ∈ A.filter (fun g => code g = n), historyShapeReferenceWeight dependent Δ g :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ n ∈ C, (1 / 4 : ℝ) ^ (∑ j : J, n j) := by
      apply Finset.sum_le_sum
      solve_by_elim [historyReferenceWeight_fiber_majorant]
    _ ≤ ∑ n ∈ Fintype.piFinset (fun _ : J => Finset.range N), (1 / 4 : ℝ) ^ (∑ j : J, n j) :=
      Finset.sum_le_sum_of_subset_of_nonneg hbox (fun _ _ _ => by positivity)
    _ = ∏ _j : J, ∑ r ∈ Finset.range N, (1 / 4 : ℝ) ^ r := by
      simp_rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.sum_prod_piFinset
    _ ≤ ∏ _j : J, (4 / 3 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro j hj
      have hh := history_finite_geom_sum_le (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1) N
      norm_num at hh ⊢
      exact hh
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

/-- The actual countable shape reference weights are summable. -/
theorem historyShapeReferenceWeight_summable :
    Summable (historyShapeReferenceWeight dependent Δ) :=
  summable_of_sum_le (fun _ => pow_nonneg (historyReferenceRho_pos Δ).le _)
    (historyReferenceWeight_finite_sum_le geom hΔ)

end

end

end NearlyMinimax
