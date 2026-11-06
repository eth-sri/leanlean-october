module

public import Chazelle.Golf

public import Chazelle.Separator.Maps
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Operations on combinatorial maps (planar separators, part 2)

**Adding an edge inside a face** (`CombMap.addEdge`).  Let `a ≠ b` be two darts of the same face,
`b = fperm^k a` with `k` minimal.  The *arc* `arc a k = {a, fperm a, …, fperm^(k-1) a}` is the
part of the face walk from `a` up to (excluding) `b`.  The new map has darts `D ⊕ Bool`:
the new dart `inr true` is inserted in the rotation just before `a` (at `vert a`), the new dart
`inr false` just before `b` (at `vert b`), and they are opposite to each other.  The face of `a`
splits into the new face `none = arc ∪ {inr false}` and the old face `some (face a)` which keeps
the other darts together with `inr true`; all other faces are unchanged.  Hence
`V' = V`, `E' = E + 1`, `F' = F + 1`, so the Euler characteristic and connectivity are
preserved (`addEdge_planar`).  The face degrees are computed exactly (`addEdge_faceDeg_none`,
`addEdge_faceDeg_some_self`, `addEdge_faceDeg_some_of_ne`).

**Triangulation** (`exists_triangulation`).  Iterating the operation on a face of degree
`≥ 4` with `b = fperm² a` cuts off a triangle; the excess `Σ_g (deg g - 3)` drops by one.  Every
planar map therefore extends (same vertex type, old darts embedded with the same endpoints) to a
planar map all of whose faces have degree `≤ 3`.  Faces of degree `1` and `2` (loops, parallel
edges) are allowed: the separator argument only needs each face to have at most three darts.

Edge deletion (between two distinct faces) and contraction (deletion in the dual) are in
`Delete.lean`; the separator proof itself only adds edges (the Lipton–Tarjan step works on the
triangulation of the whole map, with the BFS levels of the original map, so no contraction of
the levels below `l₀` and no deletion of the levels above `l₂` is needed; see
`LiptonTarjan.lean`).
-/

namespace Chazelle.Separator

universe uF uD

@[expose] public section

open Equiv Finset Sum

namespace CombMap

variable {V F D : Type*} [DecidableEq D] (M : CombMap V F D)

/-! ### The arc of a face between two darts -/

section Arc

/-- The arc `{fperm^j a : j < k}`. -/
def arc (a : D) (k : ℕ) : Finset D := (Finset.range k).image (fun j => (M.fperm ^ j) a)

variable {M} {a b : D} {k : ℕ}

/-- Membership in the arc `{fperm^j a : j < k}`. -/
theorem mem_arc {x : D} : x ∈ M.arc a k ↔ ∃ j < k, (M.fperm ^ j) a = x := by
  Θ arc

omit [DecidableEq D] in
/-- The arc from `a` to `b ≠ a` is nonempty. -/
theorem arc_pos (hab : a ≠ b) (hk : (M.fperm ^ k) a = b) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · simp at hk; exact absurd hk hab
  · exact h

/-- The arc starts at `a`. -/
theorem mem_arc_self (hab : a ≠ b) (hk : (M.fperm ^ k) a = b) : a ∈ M.arc a k :=
  mem_arc.mpr ⟨0, arc_pos hab hk, ✓⟩

/-- The arc stops before `b`. -/
theorem notMem_arc_end (hmin : ∀ j < k, (M.fperm ^ j) a ≠ b) : b ∉ M.arc a k := by
  rintro hb
  obtain ⟨j, hj, hjb⟩ := mem_arc.mp hb
  exact hmin j hj hjb

/-- The arc is closed under `fperm` until it reaches `b`. -/
theorem fperm_mem_arc (hk : (M.fperm ^ k) a = b) {x : D} (hx : x ∈ M.arc a k)
    (hxb : M.fperm x ≠ b) : M.fperm x ∈ M.arc a k := by
  obtain ⟨j, hj, rfl⟩ := mem_arc.mp hx
  refine mem_arc.mpr ⟨j + 1, ?_, by rw [pow_succ', Perm.mul_apply]⟩
  rcases Nat.lt_or_ge (j + 1) k with h | h
  · exact h
  · exfalso; apply hxb
    rw [← Perm.mul_apply, ← pow_succ', show j + 1 = k by omega, hk]

/-- The complement of the arc is closed under `fperm` until it reaches `a`. -/
theorem fperm_notMem_arc {x : D} (hx : x ∉ M.arc a k) (hxa : M.fperm x ≠ a) :
    M.fperm x ∉ M.arc a k := by
  intro h
  obtain ⟨j, hj, hjx⟩ := mem_arc.mp h
  rcases j with _ | j
  · simp at hjx; exact hxa hjx.symm
  · apply hx
    refine mem_arc.mpr ⟨j, ⋄, ?_⟩
    apply M.fperm.injective
    Ξ ← hjx, pow_succ', Perm.mul_apply

/-- The dart before `b` is the last dart of the arc. -/
theorem fperm_symm_end_mem_arc (hab : a ≠ b) (hk : (M.fperm ^ k) a = b) :
    M.fperm.symm b ∈ M.arc a k := by
  have hk0 := arc_pos hab hk
  refine mem_arc.mpr ⟨k - 1, by omega, ?_⟩
  rw [Equiv.eq_symm_apply, ← Perm.mul_apply, ← pow_succ', show k - 1 + 1 = k by omega, hk]

/-- The dart before `a` is not in the arc. -/
theorem fperm_symm_start_notMem_arc (hk : (M.fperm ^ k) a = b)
    (hmin : ∀ j < k, (M.fperm ^ j) a ≠ b) : M.fperm.symm a ∉ M.arc a k := by
  intro h
  obtain ⟨j, hj, hjx⟩ := mem_arc.mp h
  have ha : (M.fperm ^ (j + 1)) a = a := by
    rw [pow_succ', Perm.mul_apply, hjx, Equiv.apply_symm_apply]
  apply hmin (k - (j + 1)) (by omega)
  rw [← hk, show k = (k - (j + 1)) + (j + 1) by omega, pow_add, Perm.mul_apply, ha]
  congr 2; omega

/-- The arc lies in the face of `a`. -/
theorem sameCycle_of_mem_arc {x : D} (hx : x ∈ M.arc a k) : M.fperm.SameCycle a x := by
  obtain ⟨j, -, rfl⟩ := mem_arc.mp hx
  exact ⟨j, ✓⟩

end Arc

/-! ### The new permutations and labels -/

section AddEdge

variable (a b : D) (k : ℕ)

/-- Rotation after adding the edge: `inr true` just before `a`, `inr false` just before `b`. -/
def addRot : Perm (D ⊕ Bool) :=
  swap (inl b) (inr false) * swap (inl a) (inr true) * Perm.sumCongr M.rot 1

/-- The opposite-dart involution after adding the edge `{inr true, inr false}`. -/
def addOpp : Perm (D ⊕ Bool) := Perm.sumCongr M.opp (swap true false)

/-- Vertex labels after adding the edge. -/
def addVert : D ⊕ Bool → V := Sum.elim M.vert (fun t => if t then M.vert a else M.vert b)

/-- Face labels after adding the edge: the arc and `inr false` form the new face `none`. -/
def addFace : D ⊕ Bool → Option F :=
  Sum.elim (fun x => if x ∈ M.arc a k then none else some (M.face x))
    (fun t => if t then some (M.face a) else none)

variable {a b}

/-- The new rotation on an old dart. -/
theorem addRot_inl (hab : a ≠ b) (x : D) : M.addRot a b (inl x) =
    if M.rot x = a then inr true else if M.rot x = b then inr false else inl (M.rot x) := by
  ϴ addRot, Perm.mul_apply, Perm.sumCongr_apply, Sum.map_inl, swap_apply_def
  by_cases h1 : M.rot x = a
  · subst h1; simp
  · by_cases h2 : M.rot x = b
    · subst h2; simp [h1]
    · Θ h1, h2

/-- The new dart `inr true` is followed by `a`. -/
theorem addRot_true (hab : a ≠ b) : M.addRot a b (inr true) = inl a := by
  simp only [addRot, Perm.mul_apply, Perm.sumCongr_apply, Sum.map_inr, Perm.one_apply,
    swap_apply_def]
  Θ hab

/-- The new dart `inr false` is followed by `b`. -/
theorem addRot_false : M.addRot a b (inr false) = inl b := by
  simp only [addRot, Perm.mul_apply, Perm.sumCongr_apply, Sum.map_inr, Perm.one_apply,
    swap_apply_def]
  simp

omit [DecidableEq D] in
/-- The new `opp` on an old dart. -/
theorem addOpp_inl (x : D) : M.addOpp (inl x) = inl (M.opp x) := rfl

omit [DecidableEq D] in
/-- The two new darts are opposite. -/
theorem addOpp_inr (t : Bool) : M.addOpp (inr t) = inr (!t) := by
  cases t <;> simp [addOpp]

/-- The new face permutation on an old dart. -/
theorem addFperm_inl (hab : a ≠ b) (x : D) : (M.addRot a b * M.addOpp) (inl x) =
    if M.fperm x = a then inr true else if M.fperm x = b then inr false else inl (M.fperm x) := by
  rw [Perm.mul_apply, addOpp_inl, addRot_inl M hab]; rfl

/-- The new face permutation at `inr true`. -/
theorem addFperm_true : (M.addRot a b * M.addOpp) (inr true) = inl b := by
  Ξ Perm.mul_apply, addOpp_inr, Bool.not_true, addRot_false

/-- The new face permutation at `inr false`. -/
theorem addFperm_false (hab : a ≠ b) : (M.addRot a b * M.addOpp) (inr false) = inl a := by
  Ξ Perm.mul_apply, addOpp_inr, Bool.not_false, addRot_true M hab

/-- Away from the insertion points the new face permutation is the old one. -/
theorem addFperm_inl_of_ne (hab : a ≠ b) {x : D} (h1 : M.fperm x ≠ a) (h2 : M.fperm x ≠ b) :
    (M.addRot a b * M.addOpp) (inl x) = inl (M.fperm x) := by
  rw [addFperm_inl M hab]; simp [h1, h2]

/-! #### The structure axioms -/

omit [DecidableEq D] in
/-- The new `opp` is an involution. -/
theorem addOpp_addOpp (z : D ⊕ Bool) : M.addOpp (M.addOpp z) = z := by
  rcases z with x | t
  · Θ addOpp_inl, M.opp_opp
  · Θ addOpp_inr

omit [DecidableEq D] in
/-- The new `opp` has no fixed point. -/
theorem addOpp_ne (z : D ⊕ Bool) : M.addOpp z ≠ z := by
  rcases z with x | t
  · Θ addOpp_inl, M.opp_ne
  · cases t <;> simp [addOpp_inr]

/-- The new rotation preserves vertices. -/
theorem addVert_addRot (hab : a ≠ b) (z : D ⊕ Bool) :
    M.addVert a b (M.addRot a b z) = M.addVert a b z := by
  rcases z with x | t
  · Ξ addRot_inl M hab
    split_ifs with h1 h2
    · Θ addVert, ← h1, M.vert_rot
    · Θ addVert, ← h2, M.vert_rot
    · Θ addVert, M.vert_rot
  · cases t
    · Θ addRot_false, addVert
    · Θ addRot_true M hab, addVert

variable [Fintype D]

omit [Fintype D] in
/-- An old dart and its old successor stay in one new rotation cycle. -/
theorem addRot_step (hab : a ≠ b) (x : D) :
    (M.addRot a b).SameCycle (inl x) (inl (M.rot x)) := by
  by_cases h1 : M.rot x = a
  · refine ⟨2, ?_⟩
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, pow_two, Perm.mul_apply,
      addRot_inl M hab, ite_eq_left h1, addRot_true M hab, h1]
  · by_cases h2 : M.rot x = b
    · refine ⟨2, ?_⟩
      rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, pow_two, Perm.mul_apply,
        addRot_inl M hab, ite_eq_right h1, ite_eq_left h2, addRot_false, h2]
    · refine ⟨1, ?_⟩
      rw [zpow_one, addRot_inl M hab, ite_eq_right h1, ite_eq_right h2]

/-- Darts with the same vertex are in one cycle of the new rotation. -/
theorem addVert_sameCycle (hab : a ≠ b) (z w : D ⊕ Bool)
    (h : M.addVert a b z = M.addVert a b w) : (M.addRot a b).SameCycle z w := by
  -- every dart is in the rotation cycle of an old dart with the same vertex
  have hrep : ∀ z : D ⊕ Bool, ∃ x : D, M.vert x = M.addVert a b z ∧
      (M.addRot a b).SameCycle z (inl x) := by
    rintro (x | t)
    · exact ⟨x, rfl, Perm.SameCycle.refl _ _⟩
    · cases t
      · exact ⟨b, rfl, ⟨1, Ρ zpow_one, addRot_false⟩⟩
      · exact ⟨a, rfl, ⟨1, Ρ zpow_one, addRot_true M hab⟩⟩
  obtain ⟨x, hx, hzx⟩ := hrep z
  obtain ⟨y, hy, hwy⟩ := hrep w
  have hxy : M.rot.SameCycle x y := M.sameCycle_of_vert x y (Ρ hx, hy, h)
  exact hzx.trans ((sameCycle_of_step M.rot (M.addRot a b) inl (M.addRot_step hab) hxy).trans
    hwy.symm)

variable {k}

/-- The new face permutation preserves the new face labels. -/
theorem addFace_addFperm (hab : a ≠ b) (hk : (M.fperm ^ k) a = b)
    (hmin : ∀ j < k, (M.fperm ^ j) a ≠ b) (z : D ⊕ Bool) :
    M.addFace a k ((M.addRot a b * M.addOpp) z) = M.addFace a k z := by
  have hfb : M.face b = M.face a := by
    rw [← hk]; exact (eq_of_sameCycle M.fperm M.face M.face_fperm ⟨k, ✓⟩).symm
  rcases z with x | t
  · Ξ addFperm_inl M hab
    split_ifs with h1 h2
    · -- `x = fperm⁻¹ a`
      have hx : x = M.fperm.symm a := Ρ ← h1, Equiv.symm_apply_apply
      have hxn : x ∉ M.arc a k := hx ▸ fperm_symm_start_notMem_arc hk hmin
      ϴ addFace, Sum.elim_inr, Sum.elim_inl, ite_true, ite_eq_right hxn
      Ξ ← h1, M.face_fperm_apply
    · have hx : x = M.fperm.symm b := Ρ ← h2, Equiv.symm_apply_apply
      have hxm : x ∈ M.arc a k := hx ▸ fperm_symm_end_mem_arc hab hk
      Θ addFace, hxm
    · ϴ addFace, Sum.elim_inl, M.face_fperm_apply
      by_cases hx : x ∈ M.arc a k
      · Ξ ite_eq_left (fperm_mem_arc hk hx h2), ite_eq_left hx
      · Ξ ite_eq_right (fperm_notMem_arc hx h1), ite_eq_right hx
  · cases t
    · Ξ addFperm_false M hab
      Θ addFace, mem_arc_self hab hk
    · Ξ addFperm_true
      Θ addFace, notMem_arc_end hmin, hfb

/-- Darts with the same new face label are in one cycle of the new face permutation. -/
theorem addFace_sameCycle (hab : a ≠ b) (hk : (M.fperm ^ k) a = b)
    (hmin : ∀ j < k, (M.fperm ^ j) a ≠ b) (z w : D ⊕ Bool)
    (h : M.addFace a k z = M.addFace a k w) : (M.addRot a b * M.addOpp).SameCycle z w := by
  set ψ := M.addRot a b * M.addOpp with hψ
  have hfb : M.face b = M.face a := by
    rw [← hk]; exact (eq_of_sameCycle M.fperm M.face M.face_fperm ⟨k, ✓⟩).symm
  -- representatives: label `none` ↦ `inr false`, label `some (face a)` ↦ `inr true`
  have hnone : ∀ z, M.addFace a k z = none → ψ.SameCycle z (inr false) := by
    rintro (x | t) hz
    · have hx : x ∈ M.arc a k := by
        by_contra hx; simp [addFace, hx] at hz
      have h1 : ψ.SameCycle (inl x) (inl (M.fperm.symm b)) := by
        refine sameCycle_follow M.fperm ψ inl (fun y => y ∈ M.arc a k)
          (t := M.fperm.symm b) hx ?_ ?_
        · have hab' : M.fperm.SameCycle a b := ⟨(k : ℤ), Ρ zpow_natCast, hk⟩
          have hbb : M.fperm.SameCycle b (M.fperm.symm b) := ⟨-1, by rw [zpow_neg_one]; rfl⟩
          exact ((sameCycle_of_mem_arc hx).symm.trans hab').trans hbb
        · intro y hy hyb
          have hya : M.fperm y ≠ a := by
            rintro h; apply fperm_symm_start_notMem_arc hk hmin
            have hy' : M.fperm.symm a = y := Ρ ← h, Equiv.symm_apply_apply
            rw [hy']; exact hy
          have hyb' : M.fperm y ≠ b := by
            rintro h; apply hyb; rw [← h, Equiv.symm_apply_apply]
          exact ⟨addFperm_inl_of_ne M hab hya hyb', fperm_mem_arc hk hy hyb'⟩
      refine h1.trans ⟨1, ?_⟩
      rw [zpow_one, hψ, addFperm_inl M hab, Equiv.apply_symm_apply, ite_eq_right (Ne.symm hab),
        ite_eq_left rfl]
    · cases t
      · exact Perm.SameCycle.refl _ _
      · simp [addFace] at hz
  have hsome : ∀ z, M.addFace a k z = some (M.face a) → ψ.SameCycle z (inr true) := by
    rintro (x | t) hz
    · have hx : x ∉ M.arc a k := by
        intro hx; simp [addFace, hx] at hz
      have hfx : M.face x = M.face a := by simpa [addFace, hx] using hz
      have h1 : ψ.SameCycle (inl x) (inl (M.fperm.symm a)) := by
        refine sameCycle_follow M.fperm ψ inl
          (fun y => y ∉ M.arc a k ∧ M.face y = M.face a) (t := M.fperm.symm a) ⟨hx, hfx⟩ ?_ ?_
        · have haa : M.fperm.SameCycle a (M.fperm.symm a) := ⟨-1, by rw [zpow_neg_one]; rfl⟩
          exact (M.sameCycle_of_face x a hfx).trans haa
        · rintro y ⟨hy, hfy⟩ hya
          have hya' : M.fperm y ≠ a := by
            rintro h; apply hya; rw [← h, Equiv.symm_apply_apply]
          have hyb : M.fperm y ≠ b := by
            rintro h; apply hy
            have : y = M.fperm.symm b := Ρ ← h, Equiv.symm_apply_apply
            rw [this]; exact fperm_symm_end_mem_arc hab hk
          exact ⟨addFperm_inl_of_ne M hab hya' hyb,
            fperm_notMem_arc hy hya', Ρ M.face_fperm_apply, hfy⟩
      refine h1.trans ⟨1, ?_⟩
      Ξ zpow_one, hψ, addFperm_inl M hab, Equiv.apply_symm_apply, ite_eq_left rfl
    · cases t
      · simp [addFace] at hz
      · exact Perm.SameCycle.refl _ _
  -- the other faces are untouched
  have hother : ∀ x y : D, M.face x = M.face y → M.face x ≠ M.face a →
      ψ.SameCycle (inl x) (inl y) := by
    intro x y hxy hxa
    refine sameCycle_follow M.fperm ψ inl (fun w => M.face w = M.face x) rfl
      (M.sameCycle_of_face x y hxy) ?_
    intro w hw _
    have h1 : M.fperm w ≠ a := by
      rintro h; apply hxa; rw [← hw, ← M.face_fperm_apply, h]
    have h2 : M.fperm w ≠ b := by
      rintro h; apply hxa; rw [← hw, ← M.face_fperm_apply, h, hfb]
    exact ⟨addFperm_inl_of_ne M hab h1 h2, Ρ M.face_fperm_apply, hw⟩
  -- conclude
  rcases hz : M.addFace a k z with _ | g
  · rw [hz] at h
    exact (hnone z hz).trans (hnone w h.symm).symm
  · by_cases hg : g = M.face a
    · subst hg
      rw [hz] at h
      exact (hsome z hz).trans (hsome w h.symm).symm
    · rw [hz] at h
      rcases z with x | t
      · rcases w with y | s
        · have hx : x ∉ M.arc a k := by intro hx; simp [addFace, hx] at hz
          have hy : y ∉ M.arc a k := by intro hy; simp [addFace, hy] at h
          have hfx : M.face x = g := by
            have : some (M.face x) = some g := by rw [← hz]; simp [addFace, hx]
            exact Option.some.inj this
          have hfy : M.face y = g := by
            have : some g = some (M.face y) := by rw [h]; simp [addFace, hy]
            exact (Option.some.inj this).symm
          exact hother x y (hfx.trans hfy.symm) (hfx ▸ hg)
        · cases s
          · simp [addFace] at h
          · have : some g = some (M.face a) := by rw [h]; simp [addFace]
            exact absurd (Option.some.inj this) hg
      · cases t
        · simp [addFace] at hz
        · have : some (M.face a) = some g := by rw [← hz]; simp [addFace]
          exact absurd (Option.some.inj this).symm hg

omit [DecidableEq D] [Fintype D] in
/-- Every vertex keeps a dart. -/
theorem addVert_surj : Function.Surjective (M.addVert a b) := fun v => by
  obtain ⟨x, rfl⟩ := M.vert_surj v
  exact ⟨inl x, rfl⟩

/-- Every new face label is used. -/
theorem addFace_surj :
    Function.Surjective (M.addFace a k) := by
  rintro (_ | g)
  · exact ⟨inr false, rfl⟩
  · obtain ⟨x, rfl⟩ := M.face_surj g
    by_cases hx : x ∈ M.arc a k
    · refine ⟨inr true, ?_⟩
      ϴ addFace, Sum.elim_inr, ite_true
      exact congrArg some (eq_of_sameCycle M.fperm M.face M.face_fperm
        (sameCycle_of_mem_arc hx))
    · exact ⟨inl x, ⊚ addFace, hx⟩

/-- **Adding an edge inside a face.**  `a ≠ b` are darts of one face, `b = fperm^k a` with `k`
minimal. -/
def addEdge (hab : a ≠ b) (hk : (M.fperm ^ k) a = b) (hmin : ∀ j < k, (M.fperm ^ j) a ≠ b) :
    CombMap V (Option F) (D ⊕ Bool) where
  rot := M.addRot a b
  opp := M.addOpp
  vert := M.addVert a b
  face := M.addFace a k
  opp_opp := M.addOpp_addOpp
  opp_ne := M.addOpp_ne
  vert_rot := M.addVert_addRot hab
  sameCycle_of_vert := M.addVert_sameCycle hab
  face_fperm := M.addFace_addFperm hab hk hmin
  sameCycle_of_face := M.addFace_sameCycle hab hk hmin
  vert_surj := M.addVert_surj
  face_surj := M.addFace_surj

variable (hab : a ≠ b) (hk : (M.fperm ^ k) a = b) (hmin : ∀ j < k, (M.fperm ^ j) a ≠ b)

/-- Old darts keep their vertex. -/
@[simp] theorem addEdge_vert_inl (x : D) : (M.addEdge hab hk hmin).vert (inl x) = M.vert x := rfl

/-- Old darts keep their opposite. -/
@[simp] theorem addEdge_opp_inl (x : D) :
    (M.addEdge hab hk hmin).opp (inl x) = inl (M.opp x) := rfl

/-- Old darts keep their head. -/
@[simp] theorem addEdge_head_inl (x : D) :
    (M.addEdge hab hk hmin).head (inl x) = M.head x := rfl

section Euler

variable [Fintype V] [Fintype F]

end Euler

/-! #### Face degrees after adding an edge -/

variable [DecidableEq F]

end AddEdge

/-! ### Triangulation -/

section Triangulation

variable [Fintype D]

variable [Fintype F] [DecidableEq F]

end Triangulation

end CombMap

end

end Chazelle.Separator
