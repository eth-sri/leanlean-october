import RequestProject.NerveSupport


/-! Degree projections for the full augmented order-nerve chain complex. -/

namespace FiniteChains.Nerve
open FreeAbelianGroup
universe u
variable {P : Type u}

/-- Retain precisely the basis lists of length `n`. The augmentation has length zero. -/
noncomputable def lengthProjection (n : ℕ) : Ch P →+ Ch P := by
  classical
  exact lift (fun l => if l.length = n then of l else 0)

@[simp] theorem lengthProjection_of n (l : List P) :
    lengthProjection n (of l) = if l.length = n then of l else 0 := by
  classical
  simp [lengthProjection]

theorem lengthProjection_consMap_succ n a (c : Ch P) :
    lengthProjection (n + 1) (consMap a c) = consMap a (lengthProjection n c) := by
  classical
  apply ext_apply (F := (lengthProjection (n + 1)).comp (consMap a))
    (G := (consMap a).comp (lengthProjection n))
  aesop

theorem lengthProjection_consMap_zero a (c : Ch P) :
    lengthProjection 0 (consMap a c) = 0 := by
  classical
  apply ext_apply (F := (lengthProjection 0).comp (consMap a)) (G := 0)
  intro l
  simp

/-- Every face in the boundary of a list has length one less than that list. -/
theorem lengthProjection_bdryOn n (l : List P) :
    lengthProjection n (bdryOn l) = if l.length = n + 1 then bdryOn l else 0 := by
  classical
  induction l generalizing n with
  | nil => rfl
  | cons a l ih =>
    cases n with
    | zero =>
      simp [bdryOn_cons, map_sub, lengthProjection_of, lengthProjection_consMap_zero,
        sub_zero, List.length_cons, Nat.add_right_cancel_iff]
      simp_all
    | succ n =>
      rw [bdryOn_cons, map_sub, lengthProjection_of, lengthProjection_consMap_succ, ih]
      grind

/-- Degree projection commutes with boundary, with the required degree shift. -/
theorem lengthProjection_bdry n (c : Ch P) :
    lengthProjection n (bdry c) = bdry (lengthProjection (n + 1) c) := by
  classical
  apply ext_apply (F := (lengthProjection n).comp bdry)
    (G := bdry.comp (lengthProjection (n + 1)))
  intro l
  simp [AddMonoidHom.coe_comp, Function.comp_apply, bdry_of,
    lengthProjection_bdryOn, lengthProjection_of]
  aesop

@[simp] theorem lengthProjection_idempotent n (c : Ch P) :
    lengthProjection n (lengthProjection n c) = lengthProjection n c := by
  classical
  apply ext_apply (F := (lengthProjection n).comp (lengthProjection n))
    (G := lengthProjection n)
  intro l
  simp [AddMonoidHom.coe_comp, Function.comp_apply, lengthProjection_of]
  split_ifs with h <;> simp [h]

variable [Preorder P]

/-- Projecting a chain to one degree preserves its support in a subposet. -/
theorem lengthProjection_mem_incOn n {A} {c : Ch P}
    (hc : c ∈ IncOn A) : lengthProjection n c ∈ IncOn A := by
  classical
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw [lengthProjection_of]
    split_ifs
    · exact of_mem_incOn hl.1 hl.2
    simp
  | zero => simp
  | add x y _ _ hx hy => aesop
  | neg x _ hx => simp_all

theorem lengthProjection_mem_inc n {c} (hc : c ∈ Inc P) :
    lengthProjection n c ∈ Inc P := by
  classical
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw [lengthProjection_of]
    split_ifs
    · exact of_mem_inc hl
    simp
  | zero => simp
  | add x y _ _ hx hy => aesop
  | neg x _ hx => simp_all
