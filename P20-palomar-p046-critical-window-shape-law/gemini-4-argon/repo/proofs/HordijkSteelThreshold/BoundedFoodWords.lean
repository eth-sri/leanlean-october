module

public import proofs.HordijkSteelThreshold.FoodWordParents
public import proofs.HordijkSteelThreshold.BinaryWordCode

@[expose] public section

namespace HordijkSteelThreshold

/-- The actual finite word-graph vertex domain: one food root and only
nonfood words inside the ambient cap. No parity condition above N is needed. -/
def BoundedFoodWord (L N : ℕ) :=
  {s : List Bool // s = [] ∨ (L < s.length ∧ s.length ≤ N)}

theorem boundedFoodWord_length_le {L N : ℕ} (v : BoundedFoodWord L N) :
    v.val.length ≤ N := by
  rcases v.property with h | h
  · simp [h]
  · exact h.2

instance boundedFoodWord_finite (L N : ℕ) : Finite (BoundedFoodWord L N) := by
  let encode : BoundedFoodWord L N → (Σ m : Fin (N + 1), RAF.Polymer.Word m.val) :=
    fun v => ⟨⟨v.val.length, Nat.lt_succ_of_le (boundedFoodWord_length_le v)⟩, listWord v.val⟩
  apply Finite.of_injective encode
  intro u v h
  apply Subtype.ext
  apply binaryWordCode_injective_length
  · exact congrArg (fun z => z.1.val) h
  · exact congrArg (fun z => z.2.val) h

noncomputable instance boundedFoodWord_fintype (L N : ℕ) : Fintype (BoundedFoodWord L N) :=
  Fintype.ofFinite _

def boundedFoodRoot (L N : ℕ) : BoundedFoodWord L N := ⟨[], Or.inl rfl⟩

def boundedFoodLeft {L N : ℕ} (v : BoundedFoodWord L N) : BoundedFoodWord L N :=
  ⟨foodWordLeft L v.val, by
    have hv := boundedFoodWord_length_le v
    by_cases h : v.val.length ≤ L + 1 <;> [left; right] <;> simp [foodWordLeft, h]; omega⟩

def boundedFoodRight {L N : ℕ} (v : BoundedFoodWord L N) : BoundedFoodWord L N :=
  ⟨foodWordRight L v.val, by
    have hv := boundedFoodWord_length_le v
    by_cases h : v.val.length ≤ L + 1 <;> [left; right] <;> simp [foodWordRight, h]; omega⟩

theorem boundedFoodParents_commute {L N : ℕ} (v : BoundedFoodWord L N) :
    boundedFoodLeft (boundedFoodRight v) = boundedFoodRight (boundedFoodLeft v) :=
  Subtype.ext (foodWordParents_commute L v.val)

theorem boundedFood_zero_height {L N : ℕ} (v : BoundedFoodWord L N)
    (h : foodWordHeight L v.val = 0) : v = boundedFoodRoot L N :=
  Subtype.ext (v.2.elim id fun _ => by unfold foodWordHeight at h; omega)

theorem boundedFood_diamond_cut (L N : ℕ)
    (leftEdge rightEdge : BoundedFoodWord L N → Bool)
    (hroot : leftEdge (boundedFoodRoot L N) = false ∧
      rightEdge (boundedFoodRoot L N) = false)
    (hdiamond : ∀ v, (((leftEdge v ^^ rightEdge v) ^^ leftEdge (boundedFoodRight v)) ^^
      rightEdge (boundedFoodLeft v)) = false)
    (v : BoundedFoodWord L N) :
    ((diamondPotential boundedFoodRight rightEdge N v ^^
      diamondPotential boundedFoodRight rightEdge N (boundedFoodLeft v)) = leftEdge v) ∧
    ((diamondPotential boundedFoodRight rightEdge N v ^^
      diamondPotential boundedFoodRight rightEdge N (boundedFoodRight v)) = rightEdge v) :=
  diamondPotential_edges boundedFoodLeft boundedFoodRight
    (fun v : BoundedFoodWord L N => foodWordHeight L v.val) leftEdge rightEdge
    (fun u => foodWordRight_height L u.val) boundedFoodParents_commute
    (fun u hu => boundedFood_zero_height u hu ▸ hroot) hdiamond N v
    (by have := boundedFoodWord_length_le v; unfold foodWordHeight; omega)

end HordijkSteelThreshold
