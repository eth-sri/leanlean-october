import RequestProject.Fox
noncomputable section


namespace FiniteChains
variable {α : Type*} [DecidableEq α]

/-- The group element read by one oriented letter. -/
def foxWordLetter (p : α × Bool) :=
  if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹

/-- The signed contribution of an oriented generator edge to its Fox coordinate. -/
def foxWordIncidence (i : α) (p : α × Bool) :=
  if i = p.1 then (if p.2 then 1 else -grp (FreeGroup.of p.1)⁻¹) else 0

omit [DecidableEq α] in
theorem fox_mk_single_letter (p : α × Bool) :
    FreeGroup.mk [p] = foxWordLetter p := by
  cases' p with a b
  cases b
  · rfl
  · rfl

theorem fox_letter_incidence i (p : α × Bool) :
    fox i (foxWordLetter p) = foxWordIncidence i p := by
  cases' p with a b
  cases b <;> by_cases h : i = a <;>
    simp [foxWordLetter, foxWordIncidence, fox_inv, h]

/-- The actual signed edge sum of a word path, starting at the translate `g`.
Negative letters contribute at the terminal generator coordinate. -/
def foxWordPathBoundary (i : α) (g : FreeGroup α) :
    List (α × Bool) → FreeGroupRing α
  | [] => 0
  | p :: l => grp g * foxWordIncidence i p +
      foxWordPathBoundary i (g * foxWordLetter p) l

/-- The signed edge sum equals the translated Fox derivative of the actual word. -/
theorem foxWordPathBoundary_eq i g (l : List (α × Bool)) :
    foxWordPathBoundary i g l = grp g * fox i (FreeGroup.mk l) := by
  induction l generalizing g with
  | nil => simp [foxWordPathBoundary, ← FreeGroup.one_eq_mk]
  | cons p l ih =>
    have hm : FreeGroup.mk (p :: l) = foxWordLetter p * FreeGroup.mk l := by
      rw [← fox_mk_single_letter, FreeGroup.mul_mk]
      rfl
    rw [foxWordPathBoundary, ih, hm, fox_mul, fox_letter_incidence, grp_mul,
      mul_add, mul_assoc]

/-- At the identity vertex, the word edge sum is exactly the Fox boundary entry. -/
theorem foxWordPathBoundary_one i (l : List (α × Bool)) :
    foxWordPathBoundary i 1 l = fox i (FreeGroup.mk l) := by
  rw [foxWordPathBoundary_eq, grp_one, one_mul]
