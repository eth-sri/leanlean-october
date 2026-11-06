module

public import proofs.HordijkSteelThreshold.WordMolecularAnchors

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

/-- Six end edits and a stay-put choice; duplicates only decrease cardinality. -/
def endWordChoices (s : List Bool) : Finset (List Bool) :=
  insert s $ insert s.tail $ insert s.dropLast
    (((Finset.univ : Finset Bool).image (· :: s)) ∪
     ((Finset.univ : Finset Bool).image $ fun b => s ++ [b]))

theorem endWordChoices_card (s : List Bool) : (endWordChoices s).card ≤ 7 := by
  unfold endWordChoices
  grw [Finset.card_insert_le, Finset.card_insert_le, Finset.card_insert_le, Finset.card_union_le,
    Finset.card_image_le, Finset.card_image_le]
  rfl

theorem endWord_adj_mem_choices {u v : List Bool} (h : endWordGraph.Adj u v) :
    v ∈ endWordChoices u := by
  obtain ⟨b, h | h | h | h⟩ := h <;> subst_vars <;> cases b <;> simp [endWordChoices]

def endWordBall : ℕ → List Bool → Finset (List Bool)
  | 0, s => {s}
  | k + 1, s => (endWordChoices s).biUnion $ endWordBall k

variable (k : ℕ) (s : List Bool)

theorem endWordBall_self  : s ∈ endWordBall k s := by
  induction k with
  | zero => tauto
  | succ k ih => exact Finset.mem_biUnion.mpr ⟨s, by simp [endWordChoices], ih⟩

theorem endWordBall_card  : (endWordBall k s).card ≤ 7 ^ k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact Finset.card_biUnion_le.trans ((Finset.sum_le_card_nsmul _ _ _ fun v _ => ih v).trans
      (by simpa [pow_succ'] using Nat.mul_le_mul_right (7 ^ k) $ endWordChoices_card s))


theorem endWord_walk_mem_ball {u v : List Bool} (p : endWordGraph.Walk u v)
    (k : ℕ) (hk : p.length ≤ k) : v ∈ endWordBall k u := by
  induction k generalizing u v with
  | zero => obtain rfl := p.eq_of_length_eq_zero (by omega); tauto
  | succ k ih => cases p with
    | nil => exact endWordBall_self _ u
    | cons ha p => exact Finset.mem_biUnion.mpr ⟨_, endWord_adj_mem_choices ha, ih p $ by simp_all⟩

end HordijkSteelThreshold
