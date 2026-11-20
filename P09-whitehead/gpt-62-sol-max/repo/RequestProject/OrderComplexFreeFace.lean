module

public import RequestProject.OrderComplexRetraction

@[expose] public section

/-! The first half of an elementary face-poset collapse: delete the free face while
retaining its unique coface. The resulting monotone retraction reflects homotopies. -/
namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

/-- The closure operator that sends a free face to its unique coface. -/
theorem exists_freeFace_upper_retraction {Q : Type*} [PartialOrder Q]
    {C : Q → Prop} {s t : Q} (ht : C t) (hst : s ≤ t) (hne : t ≠ s)
    (hunique : ∀ x, C x → s ≤ x → x ≠ s → x = t) :
    ∃ r : {x : Q // C x} → {x : Q // C x}, Monotone r ∧
      (∀ x, x ≤ r x) ∧ (∀ x, (r x).1 ≠ s) ∧ (∀ x, x.1 ≠ s → r x = x) := by
  classical
  let r : {x : Q // C x} → {x : Q // C x} := fun x => if x.1 = s then ⟨t, ht⟩ else x
  refine ⟨r, ?_, ?_, ?_, fun x hx => ite_eq_right hx⟩
  · intro x y hxy
    change x.1 ≤ y.1 at hxy
    by_cases hx : x.1 = s <;> by_cases hy : y.1 = s <;> simp [r, hx, hy]
    · exact (hunique y.1 y.2 (hx ▸ hxy) hy).ge
    · exact (hy ▸ hxy : x.1 ≤ s).trans hst
    · exact hxy
  · intro x
    change x.1 ≤ (r x).1
    by_cases hx : x.1 = s <;> simp [r, hx, hst]
  · intro x
    by_cases hx : x.1 = s <;> simp [r, hx, hne]

theorem injIn_delete_free_face {C : P → Prop} {f t : P}
    (ht : C t) (hft : f ≤ t) (hne : t ≠ f)
    (hunique : ∀ x, C x → f ≤ x → x ≠ f → x = t) :
    InjIn C (fun x => C x ∧ x ≠ f) := by
  obtain ⟨r, hr, -, hne, hfix⟩ := exists_freeFace_upper_retraction ht hft hne hunique
  exact injIn_of_monotone_retraction (fun _ h => h.1) (Subtype.val ∘ r)
    (monotone_subtypeVal.comp hr) (fun x => ⟨(r x).2, hne x⟩)
    (fun x hx => congrArg Subtype.val (hfix x hx.2))

/-- Deleting a maximal cell reflects homotopies when its remaining boundary is connected
and simply connected. The boundary is the actual strict lower face poset in the stage. -/
theorem injIn_delete_maximal {C : P → Prop} {t : P}
    (hmax : ∀ x, C x → t ≤ x → x = t)
    (hne : ∃ x, C x ∧ x < t)
    (hconn : ConnectedIn (fun x => C x ∧ x < t))
    (hsc : SimplyConnectedIn (fun x => C x ∧ x < t)) :
    InjIn C (fun x => C x ∧ x ≠ t) := by
  obtain ⟨j, hj⟩ := hne
  apply injIn_union_of_unmixed
    (B := fun x => C x ∧ x ≤ t) (J := fun x => C x ∧ x < t)
    (j0 := j) (hJconn := hconn) (hJsc := hsc) (hj0 := hj)
  · grind
  · intro x
    constructor
    · rintro ⟨hx, hxt⟩
      exact ⟨⟨hx, hxt.ne⟩, ⟨hx, hxt.le⟩⟩
    · rintro ⟨⟨hx, hne⟩, ⟨_, hle⟩⟩
      exact ⟨hx, lt_of_le_of_ne hle hne⟩

end FiniteChains.Comb
