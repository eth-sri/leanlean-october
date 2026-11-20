module

public import RequestProject.OrderComplexRetraction

@[expose] public section

/-! The first half of an elementary face-poset collapse: delete the free face while
retaining its unique coface. The resulting monotone retraction reflects homotopies. -/
namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

variable {C : P → Prop}

theorem exists_freeFace_upper_retraction {P : Type*} [PartialOrder P] {C : P → Prop} {s t : P}
    (ht : C t) (hst : s ≤ t) (hne : t ≠ s)
    (hunique : ∀ x, C x → s ≤ x → x ≠ s → x = t) :
    ∃ r : {x : P // C x} → {x : P // C x}, Monotone r ∧
      (∀ x, x ≤ r x) ∧ (∀ x, (r x).1 ≠ s) ∧ (∀ x, x.1 ≠ s → r x = x) := by
  classical
  let r : {x : P // C x} → {x : P // C x} :=
    fun x => if x.1 = s then ⟨t, ht⟩ else x
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x.1 = s
    · by_cases hy : y.1 = s
      · grind
      · have hyt := hunique y.1 y.2 (hx ▸ hxy) hy
        grind
    · by_cases hy : y.1 = s
      · have hxs : x.1 ≤ s := hy ▸ hxy
        change (r x).1 ≤ (r y).1
        grind
      · grind
  · intro x
    by_cases hx : x.1 = s
    · change x.1 ≤ (r x).1
      grind
    · grind
  · grind
  · grind

/-- Deleting a maximal cell reflects homotopies when its remaining boundary is connected
and simply connected. The boundary is the actual strict lower face poset in the stage. -/
theorem injIn_delete_maximal {t : P}
    (hmax : ∀ x, C x → t ≤ x → x = t)
    (hne : ∃ x, C x ∧ x < t)
    (hconn : ConnectedIn (fun x => C x ∧ x < t))
    (hsc : SimplyConnectedIn (fun x => C x ∧ x < t)) :
    InjIn C (fun x => C x ∧ x ≠ t) := by
  obtain ⟨j, hj⟩ := hne
  apply injIn_union_of_unmixed
    (B := fun x => C x ∧ x ≤ t) (hJconn := hconn) (hJsc := hsc) (hj0 := hj)
  · grind
  · intro x
    constructor
    · grind
    · rintro ⟨⟨hx, hne⟩, ⟨_, hle⟩⟩
      exact ⟨hx, lt_of_le_of_ne hle hne⟩

end FiniteChains.Comb
