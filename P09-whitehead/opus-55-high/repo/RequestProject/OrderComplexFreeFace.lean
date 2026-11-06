import RequestProject.OrderComplexRetraction


/-! The first half of an elementary face-poset collapse: delete the free face while
retaining its unique coface. The resulting monotone retraction reflects homotopies. -/
namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

theorem injIn_delete_free_face {f t : P}
    (ht : C t) (hft : f ≤ t) (hne : t ≠ f)
    (hunique : ∀ x, C x → f ≤ x → x ≠ f → x = t) :
    InjIn C (fun x => C x ∧ x ≠ f) := by
  classical
  let r : {x : P // C x} → P := fun x => if x.1 = f then t else x.1
  have hr : Monotone r := by
    intro x y hxy
    by_cases hx : x.1 = f
    · aesop
    · by_cases hy : y.1 = f
      · have hxf : x.1 ≤ f := hy ▸ hxy
        grind
      aesop
  apply injIn_of_monotone_retraction (by simp_all) r hr
  · grind
  grind

/-- Deleting a maximal cell reflects homotopies when its remaining boundary is connected
and simply connected. The boundary is the actual strict lower face poset in the stage. -/
theorem injIn_delete_maximal {t : P}
    (hmax : ∀ x, C x → t ≤ x → x = t)
    (hne : ∃ x, C x ∧ x < t)
    (hconn : ConnectedIn (fun x => C x ∧ x < t))
    (hsc : SimplyConnectedIn (fun x => C x ∧ x < t)) :
    InjIn C (fun x => C x ∧ x ≠ t) := by
  cases' hne with j hj
  apply injIn_union_of_unmixed
    (B := fun x => C x ∧ x ≤ t) (J := fun x => C x ∧ x < t)
    (j0 := j) (hJconn := hconn) (hJsc := hsc) (hj0 := hj)
  · grind
  · intro x
    constructor
    · grind
    · rintro ⟨⟨hx, hne⟩, ⟨_, hle⟩⟩
      exact ⟨hx, lt_of_le_of_ne hle hne⟩
