module
public import ADR11.Clusters

/-! Finite (signed) laws. The cumulative mass on subsets of K turns the
union of independent forests into multiplication: the union is contained
in K exactly when each summand is. -/
@[expose] public section
namespace ADR11
open Finset
abbrev Law (α : Type*) := α → ℝ
namespace Law
variable {α β γ ι : Type*}

noncomputable def push [Fintype α] [DecidableEq β] (r : α → β) (p : Law α) : Law β :=
  fun b => ∑ a, if r a = b then p a else 0
noncomputable def bind [Fintype α] (p : Law α) (P : α → Law β) : Law β := fun b => dotProduct p (P · b)

variable [Fintype α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
@[simp] theorem expect_push (r : α → β) (p : Law α) (f : β → ℝ) : dotProduct (push r p) f = dotProduct p (f ∘ r) := by
  simp only [push,dotProduct,sum_mul,ite_mul,zero_mul]; rw [sum_comm]; simp [sum_ite_eq]
@[simp] theorem push_id [DecidableEq α] (p : Law α) : push id p = p := by funext; simp [push]
@[simp] theorem expect_bind (p : Law α) (P : α → Law β) (f : β → ℝ) : dotProduct (bind p P) f = dotProduct p (fun a => dotProduct (P a) f) := (Matrix.dotProduct_mulVec p P f).symm

theorem expect_congr {p : Law α} {f g : α → ℝ} (h : ∀ a, p a ≠ 0 → f a = g a) : dotProduct p f = dotProduct p g := by
  apply sum_congr rfl; grind

theorem push_bind {p : Law α} {r : α → β} (t : γ → ι) [Fintype ι] [DecidableEq ι]
    {P : α → Law γ} {Q : β → Law ι} (h : ∀ a, p a ≠ 0 → push t (P a) = Q (r a)) :
    push t (bind p P) = bind (push r p) Q := by
  apply dotProduct_eq; intro f; simp only [expect_push,expect_bind]
  apply expect_congr; intro a hz
  exact (expect_push t (P a) f).symm.trans (congrArg (dotProduct · f) (h a hz))

theorem push_push (p : Law α) (f : α → β) (g : β → γ) : push g (push f p) = push (g ∘ f) p := by
  apply dotProduct_eq; simp [Function.comp_def]

variable [DecidableEq α] [DecidableEq ι]

noncomputable def cdf (p : Law (Finset α)) (K : Finset α) := dotProduct p fun F => if F ⊆ K then 1 else 0

theorem cdf_inj {p q : Law (Finset α)} (h : ∀ K, cdf p K = cdf q K) : p = q := by
  funext K; induction K using Finset.strongInduction with | H K ih =>
  have e := sub_eq_zero.mpr (h K)
  rw [cdf,cdf,← sub_dotProduct,dotProduct,sum_eq_single K] at e
  · simpa [sub_eq_zero] using e
  · intro F _ ne; by_cases le : F ⊆ K <;> simp_all [Finset.ssubset_iff_subset_ne]
  · simp

noncomputable def combine (C : Finset ι) (μ : ι → Law (Finset α)) (S : Finset α) : Law (Finset α) :=
  push (fun f : C → Finset α => univ.sup f ∪ S) fun f => ∏ i : C, μ i (f i)

theorem cdf_push_combine (C : Finset ι) (μ : ι → Law (Finset α)) (S : Finset α)
    (r : Finset α → Finset β) (hr : ∀ u v, r (u ∪ v) = r u ∪ r v) (h0 : r ∅ = ∅) (K : Finset β) :
    cdf (push r (combine C μ S)) K = if r S ⊆ K then ∏ i ∈ C, cdf (push r (μ i)) K else 0 := by
  have eqn (f : C → Finset α) : r (univ.sup f ∪ S) ⊆ K ↔ (∀ i, r (f i) ⊆ K) ∧ r S ⊆ K := by
    rw [hr,union_subset_iff,Finset.apply_sup_eq_sup_comp r hr h0]; simp
  simp only [cdf,combine,expect_push]; simp only [dotProduct,Function.comp_apply,mul_ite,mul_one,mul_zero,eqn]
  split_ifs with hs
  · rw [← prod_coe_sort C,Fintype.prod_sum]; simp only [Fintype.prod_ite_zero, hs, and_true]
  · simp [hs]

theorem cdf_combine (C : Finset ι) (μ : ι → Law (Finset α)) (S K : Finset α) :
    cdf (combine C μ S) K = if S ⊆ K then ∏ i ∈ C, cdf (μ i) K else 0 := by
  simpa using cdf_push_combine C μ S id (fun _ _ => rfl) rfl K

@[simp] theorem combine_empty (p : ι → Law (Finset α)) (S : Finset α) : combine ∅ p S = Pi.single S 1 := by
  apply cdf_inj; intro K; rw [cdf_combine]; simp [cdf]

theorem combine_insert (p : ι → Law (Finset α)) (b : ι) (C : Finset ι) (S : Finset α) (hb : b ∉ C) :
    combine (insert b C) p S = bind (p b) (fun B => combine C p (B ∪ S)) := by
  apply cdf_inj; intro K; rw [cdf_combine,prod_insert hb]
  change _ = dotProduct (bind _ _) _
  rw [expect_bind]; change _ = dotProduct _ (fun B => cdf _ K)
  simp_rw [cdf_combine,union_subset_iff]
  by_cases hs : S ⊆ K <;> simp [hs,cdf,dotProduct,sum_mul,mul_ite,ite_mul]

theorem cdf_zero {p : Law (Finset α)} {S K : Finset α} (h : ∀ F, p F ≠ 0 → S ⊆ F) (hn : ¬S ⊆ K) : cdf p K = 0 := by
  apply sum_eq_zero; grind

@[simp] theorem cdf_univ (p : Law (Finset α)) : cdf p univ = dotProduct p 1 := by simp [cdf,Pi.one_def]

end Law
end ADR11
