module

public import proofs.HordijkSteelThreshold.WordMolecularAnchors

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

/-- Six end edits and a stay-put choice; duplicates only decrease cardinality. -/
def endWordChoices (s : List Bool) : Finset (List Bool) :=
  insert s (insert s.tail (insert s.dropLast
    (((Finset.univ : Finset Bool).image (fun b => b :: s)) ∪
     ((Finset.univ : Finset Bool).image (fun b => s ++ [b])))))

def endWordBall : ℕ → List Bool → Finset (List Bool)
  | 0, s => {s}
  | k + 1, s => (endWordChoices s).biUnion (endWordBall k)

theorem endWordBall_card (k : ℕ) (s : List Bool) : (endWordBall k s).card ≤ 7 ^ k := by
  induction k generalizing s with
  | zero => simp [endWordBall]
  | succ k ih =>
    let u := (Finset.univ : Finset Bool).image (fun b => b :: s)
    let v := (Finset.univ : Finset Bool).image (fun b => s ++ [b])
    have h1 : u.card ≤ 2 := Finset.card_image_le.trans (by decide)
    have h2 : v.card ≤ 2 := Finset.card_image_le.trans (by decide)
    have := Finset.card_union_le u v
    have := Finset.card_insert_le s.dropLast (u ∪ v)
    have := Finset.card_insert_le s.tail (insert s.dropLast (u ∪ v))
    have := Finset.card_insert_le s (insert s.tail (insert s.dropLast (u ∪ v)))
    have hcard : (endWordChoices s).card ≤ 7 := by
      change (insert s (insert s.tail (insert s.dropLast (u ∪ v)))).card ≤ 7; omega
    refine Finset.card_biUnion_le.trans ((Finset.sum_le_sum fun v _ => ih v).trans ?_)
    simpa [pow_succ'] using Nat.mul_le_mul_right (7 ^ k) hcard

theorem endWord_walk_mem_ball {u v : List Bool} (p : endWordGraph.Walk u v)
    (k : ℕ) (hk : p.length ≤ k) : v ∈ endWordBall k u := by
  have hself (n : ℕ) (s : List Bool) : s ∈ endWordBall n s := by
    induction n with
    | zero => simp [endWordBall]
    | succ n ih => exact Finset.mem_biUnion.mpr ⟨s, by simp [endWordChoices], ih⟩
  induction k generalizing u v with
  | zero => cases p.eq_of_length_eq_zero (by omega); exact hself 0 u
  | succ k ih =>
    cases p with
    | nil => exact hself (k + 1) u
    | @cons u v w ha p =>
      exact Finset.mem_biUnion.mpr ⟨v, by rcases ha with ⟨b, rfl | rfl | rfl | rfl⟩ <;> cases b <;> simp [endWordChoices],
        ih p (by simp at hk; omega)⟩

end HordijkSteelThreshold
