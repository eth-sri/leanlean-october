module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Separator.Clusters

/-!
# WP-I, part 6: the star map (a uniform triangulation)

The separator argument needs a planar map whose faces have at most three darts, extending the
input map on the same real vertices.  Instead of cutting faces into fans (`exists_triangulation`)
we add a *centre* in every face `g` and join it to every corner: the **star map** `star M` has

* vertices `V ⊕ F` (real vertices and face centres),
* darts `D ⊕ D ⊕ D`: `inl d` the old dart, `inr (inl d)` the spoke from the centre of `face d` to
  `vert d`, `inr (inr d)` the reverse spoke,
* faces `D`: the face `d` is the triangle `inl d`, `inr (inr (fperm d))`, `inr (inl d)`.

Every face has exactly three darts (`star_faceDeg`), the Euler characteristic is unchanged
(`star_euler`), connectivity is preserved (`star_connected`), hence `star_planar`.  The formulas
are uniform, so a RAM program writes the star map with three array cells per old dart.

`starTree T a`: a spanning tree of `M` extends to the star map, the centre of `g` hanging at the
corner `vert (a g)` (`a g` any dart of `g`).
-/

namespace Chazelle.Core.Cluster

open Chazelle.Separator Equiv

@[expose] public section

variable {V F D : Type*} (M : CombMap V F D)

/-- The rotation of the star map. -/
def starRot : Perm (D ⊕ D ⊕ D) where
  toFun x := match x with
    | .inl d => .inr (.inr (M.rot d))
    | .inr (.inl d) => .inr (.inl (M.fperm⁻¹ d))
    | .inr (.inr d) => .inl d
  invFun x := match x with
    | .inl d => .inr (.inr d)
    | .inr (.inl d) => .inr (.inl (M.fperm d))
    | .inr (.inr d) => .inl (M.rot⁻¹ d)
  left_inv x := by rcases x with d | d | d <;> simp
  right_inv x := by rcases x with d | d | d <;> simp

/-- The opposite darts of the star map. -/
def starOpp : Perm (D ⊕ D ⊕ D) where
  toFun x := match x with
    | .inl d => .inl (M.opp d)
    | .inr (.inl d) => .inr (.inr d)
    | .inr (.inr d) => .inr (.inl d)
  invFun x := match x with
    | .inl d => .inl (M.opp d)
    | .inr (.inl d) => .inr (.inr d)
    | .inr (.inr d) => .inr (.inl d)
  left_inv x := by rcases x with d | d | d <;> Θ M.opp_opp
  right_inv x := by rcases x with d | d | d <;> Θ M.opp_opp

@[simp] theorem starRot_inl (d : D) : starRot M (.inl d) = .inr (.inr (M.rot d)) := rfl
@[simp] theorem starRot_inl_inr (d : D) : starRot M (.inr (.inl d)) = .inr (.inl (M.fperm⁻¹ d)) :=
  rfl
@[simp] theorem starRot_inr_inr (d : D) : starRot M (.inr (.inr d)) = .inl d := rfl
@[simp] theorem starOpp_inl (d : D) : starOpp M (.inl d) = .inl (M.opp d) := rfl
@[simp] theorem starOpp_inl_inr (d : D) : starOpp M (.inr (.inl d)) = .inr (.inr d) := rfl
@[simp] theorem starOpp_inr_inr (d : D) : starOpp M (.inr (.inr d)) = .inr (.inl d) := rfl

/-- The tail vertex in the star map. -/
def starVert : D ⊕ D ⊕ D → V ⊕ F
  | .inl d => .inl (M.vert d)
  | .inr (.inl d) => .inr (M.face d)
  | .inr (.inr d) => .inl (M.vert d)

/-- The face in the star map. -/
def starFace : D ⊕ D ⊕ D → D
  | .inl d => d
  | .inr (.inl d) => d
  | .inr (.inr d) => M.fperm⁻¹ d

@[simp] theorem starVert_inl (d : D) : starVert M (.inl d) = .inl (M.vert d) := rfl
@[simp] theorem starVert_inl_inr (d : D) : starVert M (.inr (.inl d)) = .inr (M.face d) := rfl
@[simp] theorem starVert_inr_inr (d : D) : starVert M (.inr (.inr d)) = .inl (M.vert d) := rfl
@[simp] theorem starFace_inl (d : D) : starFace M (.inl d) = d := rfl
@[simp] theorem starFace_inl_inr (d : D) : starFace M (.inr (.inl d)) = d := rfl
@[simp] theorem starFace_inr_inr (d : D) : starFace M (.inr (.inr d)) = M.fperm⁻¹ d := rfl

/-- The face permutation of the star map, explicitly. -/
theorem starFperm_inl (d : D) : (starRot M * starOpp M) (.inl d) = .inr (.inr (M.fperm d)) := by
  Θ Perm.mul_apply, M.fperm_apply

theorem starFperm_inr_inr (d : D) :
    (starRot M * starOpp M) (.inr (.inr d)) = .inr (.inl (M.fperm⁻¹ d)) := by
  Θ Perm.mul_apply

theorem starFperm_inl_inr (d : D) : (starRot M * starOpp M) (.inr (.inl d)) = .inl d := by
  Θ Perm.mul_apply

variable [Finite D]

/-- **The star map** of a combinatorial map. -/
def star : CombMap (V ⊕ F) D (D ⊕ D ⊕ D) where
  rot := starRot M
  opp := starOpp M
  vert := starVert M
  face := starFace M
  opp_opp x := by rcases x with d | d | d <;> simp [M.opp_opp]
  opp_ne x := by
    rcases x with d | d | d <;> simp [M.opp_ne]
  vert_rot x := by
    rcases x with d | d | d
    · simp [M.vert_rot]
    · simp only [starRot_inl_inr, starVert_inl_inr, Sum.inr.injEq]
      have := M.face_fperm_apply (M.fperm⁻¹ d)
      rw [show M.fperm (M.fperm⁻¹ d) = d by simp] at this
      exact this.symm
    · simp
  sameCycle_of_vert x y hxy := by
    -- real vertices: old darts along `rot`, reverse spokes one step before their old dart
    have hold : ∀ d e : D, M.vert d = M.vert e →
        (starRot M).SameCycle (.inl d) (.inl e) := by
      intro d e hde
      refine sameCycle_of_step M.rot (starRot M) Sum.inl (fun z => ?_) (M.sameCycle_of_vert d e hde)
      exact ⟨2, by simp [pow_two, Perm.mul_apply]⟩
    have hspoke : ∀ d : D, (starRot M).SameCycle (.inr (.inr d)) (.inl d) := fun d => ⟨1, by simp⟩
    have hctr : ∀ d e : D, M.face d = M.face e →
        (starRot M).SameCycle (.inr (.inl d)) (.inr (.inl e)) := by
      intro d e hde
      have h1 : M.fperm⁻¹.SameCycle d e := (M.sameCycle_of_face d e hde).inv
      exact sameCycle_of_step M.fperm⁻¹ (starRot M) (fun z => Sum.inr (Sum.inl z))
        (fun z => ⟨1, by simp⟩) h1
    rcases x with d | d | d <;> rcases y with e | e | e <;>
      simp only [starVert_inl, starVert_inl_inr, starVert_inr_inr, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq] at hxy
    · exact hold d e hxy
    · exact (hold d e hxy).trans (hspoke e).symm
    · exact hctr d e hxy
    · exact (hspoke d).trans (hold d e hxy)
    · exact (hspoke d).trans ((hold d e hxy).trans (hspoke e).symm)
  face_fperm x := by
    rcases x with d | d | d
    · show starFace M ((starRot M * starOpp M) (.inl d)) = _
      rw [starFperm_inl]; simp
    · show starFace M ((starRot M * starOpp M) (.inr (.inl d))) = _
      rw [starFperm_inl_inr]; simp
    · show starFace M ((starRot M * starOpp M) (.inr (.inr d))) = _
      rw [starFperm_inr_inr]; simp
  sameCycle_of_face x y hxy := by
    -- every dart is in the face cycle of its old dart
    have key : ∀ z : D ⊕ D ⊕ D, (starRot M * starOpp M).SameCycle (.inl (starFace M z)) z := by
      intro z
      rcases z with d | d | d
      · exact Perm.SameCycle.refl _ _
      · refine ⟨2, ?_⟩
        simp only [starFace_inl_inr, zpow_ofNat, pow_two, Perm.mul_apply]
        rw [show (starOpp M) (Sum.inl d) = Sum.inl (M.opp d) from rfl]
        simp only [starRot_inl, starOpp_inr_inr, starRot_inl_inr, Sum.inr.injEq, Sum.inl.injEq]
        rw [← M.fperm_apply]; simp
      · refine ⟨1, ?_⟩
        simp only [starFace_inr_inr, zpow_one]
        rw [starFperm_inl]; simp
    have h1 := key x
    have h2 := key y
    rw [show starFace M x = starFace M y from hxy] at h1
    exact h1.symm.trans h2
  vert_surj v := by
    rcases v with v | g
    · obtain ⟨d, rfl⟩ := M.vert_surj v; exact ⟨.inl d, rfl⟩
    · obtain ⟨d, rfl⟩ := M.face_surj g; exact ⟨.inr (.inl d), rfl⟩
  face_surj d := ⟨.inl d, rfl⟩

/-! ## The star map: basic facts -/

@[simp] theorem star_rot : (star M).rot = starRot M := rfl
@[simp] theorem star_opp : (star M).opp = starOpp M := rfl
@[simp] theorem star_vert : (star M).vert = starVert M := rfl
@[simp] theorem star_face : (star M).face = starFace M := rfl

theorem star_fperm_inl (d : D) : (star M).fperm (.inl d) = .inr (.inr (M.fperm d)) :=
  starFperm_inl M d
theorem star_fperm_inr_inr (d : D) : (star M).fperm (.inr (.inr d)) = .inr (.inl (M.fperm⁻¹ d)) :=
  starFperm_inr_inr M d
theorem star_fperm_inl_inr (d : D) : (star M).fperm (.inr (.inl d)) = .inl d :=
  starFperm_inl_inr M d

/-- **Every face of the star map is a triangle.** -/
theorem star_faceDeg [Fintype D] [DecidableEq D] (g : D) : (star M).faceDeg g = 3 := by
  classical
  unfold CombMap.faceDeg
  have : Finset.univ.filter (fun x => (star M).face x = g) =
      {.inl g, .inr (.inl g), .inr (.inr (M.fperm g))} := by
    ext x
    rcases x with d | d | d
    · Θ eq_comm
    · Θ eq_comm
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      show M.fperm⁻¹ d = g ↔ _
      Ξ Perm.inv_eq_iff_eq
      simp
  Ξ this
  rw [Finset.card_insert_of_notMem (✓), Finset.card_insert_of_notMem (✓),
    Finset.card_singleton]

/-- **Connectivity is preserved.** -/
theorem star_connected (hM : M.Connected) : (star M).Connected := by
  intro S hrot hopp x hx y
  -- the old darts in `S` form a nonempty rotation- and opposite-closed set
  have hinv : ∀ z ∈ S, (starRot M)⁻¹ z ∈ S := fun z hz => mem_of_inv_mem (starRot M) S hrot hz
  set S0 : Set D := {d | Sum.inl d ∈ S}
  have h0rot : ∀ d ∈ S0, M.rot d ∈ S0 := by
    intro d hd
    exact hrot _ (hrot _ hd)
  have h0opp : ∀ d ∈ S0, M.opp d ∈ S0 := fun d hd => hopp _ hd
  have hS0 : ∃ d, d ∈ S0 := by
    rcases x with d | d | d
    · exact ⟨d, hx⟩
    · exact ⟨d, hrot _ (hopp _ hx)⟩
    · exact ⟨d, hrot _ hx⟩
  obtain ⟨d0, hd0⟩ := hS0
  have hall : ∀ d, Sum.inl d ∈ S := fun d => hM S0 h0rot h0opp d0 hd0 d
  rcases y with d | d | d
  · exact hall d
  · exact hopp _ (hinv _ (hall d))
  · exact hinv _ (hall d)

/-- **The Euler characteristic is preserved.** -/
theorem star_euler [Fintype V] [Fintype F] [Fintype D] [DecidableEq D] :
    (star M).euler = M.euler := by
  have h1 := (star M).two_mul_euler
  have h2 := M.two_mul_euler
  ϴ' Fintype.card_sum at h1
  push_cast at h1
  omega

/-- **The star map of a planar map is planar.** -/
theorem star_planar [Fintype V] [Fintype F] [Fintype D] [DecidableEq D] (hM : M.Planar) :
    (star M).Planar :=
  ⟨star_connected M hM.1, by rw [star_euler]; exact hM.2⟩

/-! ## The spanning tree of the star map -/

/-- **The spanning tree of the star map**: the tree `T` of `M` on the real vertices, and the
centre of `g` hanging at the corner `vert (a g)` by the spoke `inr (inl (a g))`. -/
def starTree {M : CombMap V F D} (T : CombMap.SpanTree M) (a : F → D)
    (ha : ∀ g, M.face (a g) = g) : CombMap.SpanTree (star M) where
  root := .inl T.root
  level x := match x with
    | .inl v => T.level v
    | .inr g => T.level (M.vert (a g)) + 1
  par x := match x with
    | .inl v => .inl (T.par v)
    | .inr g => .inr (.inl (a g))
  level_root := T.level_root
  vert_par x hx := by
    rcases x with v | g
    · have : v ≠ T.root := fun h => hx (Ρ h)
      Θ T.vert_par v this
    · Θ ha g
  level_head_par x hx := by
    rcases x with v | g
    · have : v ≠ T.root := fun h => hx (Ρ h)
      show T.level (M.head (T.par v)) + 1 = T.level v
      exact T.level_head_par v this
    · rfl

@[simp] theorem starTree_level_inl {M : CombMap V F D} (T : CombMap.SpanTree M) (a : F → D)
    (ha : ∀ g, M.face (a g) = g) (v : V) : (starTree T a ha).level (.inl v) = T.level v := rfl

@[simp] theorem starTree_root {M : CombMap V F D} (T : CombMap.SpanTree M) (a : F → D)
    (ha : ∀ g, M.face (a g) = g) : (starTree T a ha).root = .inl T.root := rfl

end

end Chazelle.Core.Cluster
