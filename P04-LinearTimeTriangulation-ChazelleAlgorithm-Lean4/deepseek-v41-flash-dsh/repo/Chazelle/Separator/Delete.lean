module

public import Chazelle.Golf

public import Chazelle.Separator.Cotree

/-!
# Deleting and contracting an edge (planar separators, part 2b)

**Deletion** (`CombMap.deleteEdge`).  Let `n` be a dart whose two sides are distinct faces
(`face n ≠ face (opp n)`), excluding the lone loop (`rot n = opp n` and `rot (opp n) = n`, whose
vertex would disappear).  The new map has the darts `D₀ = {x // x ≠ n ∧ x ≠ opp n}`, the
rotation is the first-return map of `rot` to `D₀`, the vertices are unchanged, and the two faces
of `n` merge: faces `{g // g ≠ face (opp n)}`.  So `V' = V`, `E' = E - 1`, `F' = F - 1`;
connectivity and hence planarity are preserved (`deleteEdge_planar`).  The face permutation of
the new map is the first-return map of `fperm * swap n (opp n)` (`deleteEdge_fperm_eq`), whose
cycles are the old faces with the two faces of `n` merged (`sameCycle_mul_swap_iff`).

**Contraction** (`CombMap.contractEdge`) of a non-loop edge is deletion in the dual map:
`M / e = (M.dual − e).dual`; it merges the two endpoints (`V' = V - 1`, `E' = E - 1`, `F' = F`)
and preserves planarity (`contractEdge_planar`).

These operations are not used by the separator proof (which only adds edges); they complete the
toolkit of `Operations.lean`.
-/

namespace Chazelle.Separator

@[expose] public section

open Equiv Finset

namespace CombMap

variable {V F D : Type*} [Fintype D] [DecidableEq D] [DecidableEq F] (M : CombMap V F D)

section Delete

variable (n : D)

/-- The darts other than those of the edge of `n`. -/
abbrev Keep (x : D) : Prop := x ≠ n ∧ x ≠ M.opp n

omit [Fintype D] [DecidableEq D] [DecidableEq F] in
/-- The remaining darts are closed under `opp`. -/
theorem keep_opp_iff (x : D) : M.Keep n (M.opp x) ↔ M.Keep n x := by
  ϴ Keep
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h2 (Ρ h), fun h => h1 (by rw [h, M.opp_opp])⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h2 (Ρ ← h, M.opp_opp), fun h => h1 (M.opp_injective h)⟩

/-- The face permutation with the two faces of `n` merged. -/
def mergePerm : Perm D := M.fperm * swap n (M.opp n)

/-- Rotation after deleting the edge of `n`: the first-return map of `rot`. -/
noncomputable def delRot : Perm {x // M.Keep n x} := firstReturn M.rot (M.Keep n)

/-- The opposite-dart involution restricted to the remaining darts. -/
def delOpp : Perm {x // M.Keep n x} := M.opp.subtypePerm (M.keep_opp_iff n)

omit [Fintype D] [DecidableEq D] [DecidableEq F] in
/-- The restricted `opp`. -/
theorem delOpp_apply (x : {x // M.Keep n x}) : (M.delOpp n x).1 = M.opp x.1 := rfl

omit [Fintype D] [DecidableEq F] in
/-- On the darts of the deleted edge, the merged face permutation acts like the rotation. -/
theorem mergePerm_bad {z : D} (hz : ¬ M.Keep n z) : M.mergePerm n z = M.rot z := by
  simp only [Keep, not_and_or, not_not] at hz
  rcases hz with rfl | rfl
  · Θ mergePerm, fperm_apply, M.opp_opp
  · Θ mergePerm, fperm_apply

omit [Fintype D] [DecidableEq F] in
/-- On the remaining darts, the merged face permutation is the face permutation. -/
theorem mergePerm_good {z : D} (hz : M.Keep n z) : M.mergePerm n z = M.fperm z := by
  Θ mergePerm, swap_apply_of_ne_of_ne hz.1 hz.2

omit [DecidableEq F] in
/-- **The new face permutation is the first-return map of the merged face permutation.** -/
theorem deleteEdge_fperm_eq : M.delRot n * M.delOpp n = firstReturn (M.mergePerm n) (M.Keep n) := by
  ext x
  set y : {x // M.Keep n x} := M.delOpp n x
  -- iterates of `mergePerm` from `x` follow the rotation from `opp x` while outside `Keep`
  have key : ∀ j, 0 < j → (∀ i, 0 < i → i < j → ¬ M.Keep n ((M.rot ^ i) y.1)) →
      ((M.mergePerm n) ^ j) x.1 = (M.rot ^ j) y.1 := by
    intro j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro _ hbad
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        ϴ zero_add, pow_one
        Ξ M.mergePerm_good n x.2, fperm_apply, delOpp_apply
      · rw [pow_succ', Perm.mul_apply, ih hpos (fun i hi0 hi => hbad i hi0 (⋄)),
          M.mergePerm_bad n (hbad j hpos (⋄)), pow_succ', Perm.mul_apply]
  have hm := returnTime_pos M.rot (M.Keep n) y
  have hkey := key _ hm (fun i hi0 hi => not_pow_of_lt_returnTime _ _ y hi0 hi)
  show ((firstReturn M.rot (M.Keep n)) y).1 = ((firstReturn (M.mergePerm n) (M.Keep n)) x).1
  Ξ firstReturn_apply, firstReturn_eq (M.mergePerm n) (M.Keep n) x hm, hkey
  · Ξ hkey
    exact pow_returnTime _ _ y
  · intro i hi0 hi
    rw [key i hi0 (fun i' hi0' hi' => not_pow_of_lt_returnTime _ _ y hi0' (⋄))]
    exact not_pow_of_lt_returnTime _ _ y hi0 hi

variable {n}

/-- The merged face labels. -/
def delFace (hn : M.face n ≠ M.face (M.opp n)) (x : {x // M.Keep n x}) :
    {g : F // g ≠ M.face (M.opp n)} :=
  if h : M.face x.1 = M.face (M.opp n) then ⟨M.face n, hn⟩ else ⟨M.face x.1, h⟩

omit [DecidableEq D] [DecidableEq F] in
/-- The two darts of the deleted edge lie in different faces. -/
theorem not_sameCycle_n (hn : M.face n ≠ M.face (M.opp n)) :
    ¬ M.fperm.SameCycle n (M.opp n) := fun h =>
  hn (eq_of_sameCycle M.fperm M.face M.face_fperm h)

omit [DecidableEq F] in
/-- The merged cycles: two remaining darts are in the same merged face iff they were in the same
face or both in the faces of `n`. -/
theorem sameCycle_mergePerm_iff (hn : M.face n ≠ M.face (M.opp n)) (x y : D) :
    (M.mergePerm n).SameCycle x y ↔
    M.face x = M.face y ∨ ((M.face x = M.face n ∨ M.face x = M.face (M.opp n)) ∧
      (M.face y = M.face n ∨ M.face y = M.face (M.opp n))) := by
  rw [mergePerm, sameCycle_mul_swap_iff M.fperm (M.not_sameCycle_n hn), ← M.face_eq_iff_sameCycle,
    ← M.face_eq_iff_sameCycle, ← M.face_eq_iff_sameCycle, ← M.face_eq_iff_sameCycle,
    ← M.face_eq_iff_sameCycle]

/-- Equal merged face labels iff the same cycle of the merged face permutation. -/
theorem delFace_eq_iff (hn : M.face n ≠ M.face (M.opp n)) (x y : {x // M.Keep n x}) :
    M.delFace hn x = M.delFace hn y ↔
    (M.mergePerm n).SameCycle x.1 y.1 := by
  Ξ M.sameCycle_mergePerm_iff hn
  unfold delFace
  by_cases hx : M.face x.1 = M.face (M.opp n) <;> by_cases hy : M.face y.1 = M.face (M.opp n)
  · ϴ dite_eq_left_of_eq_true (eq_true hx), dite_eq_left_of_eq_true (eq_true hy)
    Θ hx, hy
  · simp only [dite_eq_left_of_eq_true (eq_true hx), dite_eq_right_of_eq_false (eq_false hy),
      Subtype.mk.injEq]
    constructor
    · intro h; exact Or.inr ⟨Or.inr hx, Or.inl h.symm⟩
    · rintro (h | ⟨-, h | h⟩)
      · exact absurd (h ▸ hx) hy
      · exact h.symm
      · exact absurd h hy
  · simp only [dite_eq_right_of_eq_false (eq_false hx), dite_eq_left_of_eq_true (eq_true hy),
      Subtype.mk.injEq]
    constructor
    · intro h; exact Or.inr ⟨Or.inl h, Or.inr hy⟩
    · rintro (h | ⟨h | h, -⟩)
      · exact absurd (h ▸ hy) hx
      · exact h
      · exact absurd h hx
  · simp only [dite_eq_right_of_eq_false (eq_false hx), dite_eq_right_of_eq_false (eq_false hy),
      Subtype.mk.injEq]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨h1 | h1, h2 | h2⟩)
      · exact h
      · Ξ h1, h2
      · exact absurd h2 hy
      · exact absurd h1 hx
      · exact absurd h1 hx

omit [Fintype D] [DecidableEq D] [DecidableEq F] in
/-- The tail of the deleted edge has another dart. -/
theorem rot_ne_self (hn : M.face n ≠ M.face (M.opp n)) : M.rot n ≠ n := fun h => hn (by
  rw [← M.face_fperm_apply (M.opp n), fperm_apply, M.opp_opp, h])

omit [Fintype D] [DecidableEq D] [DecidableEq F] in
/-- The head of the deleted edge has another dart. -/
theorem rot_opp_ne_self (hn : M.face n ≠ M.face (M.opp n)) :
    M.rot (M.opp n) ≠ M.opp n := fun h => hn (by
  rw [← M.face_fperm_apply n, fperm_apply, h])

omit [Fintype D] [DecidableEq F] in
/-- Every vertex keeps a dart. -/
theorem exists_keep_vert (hn : M.face n ≠ M.face (M.opp n))
    (hloop : ¬ (M.rot n = M.opp n ∧ M.rot (M.opp n) = n)) (v : V) :
    ∃ x, M.Keep n x ∧ M.vert x = v := by
  obtain ⟨d, rfl⟩ := M.vert_surj v
  by_cases hd : M.Keep n d
  · exact ⟨d, hd, rfl⟩
  simp only [Keep, not_and_or, not_not] at hd
  have hr1 := M.rot_ne_self hn
  have hr2 := M.rot_opp_ne_self hn
  rcases hd with rfl | rfl
  · by_cases h : M.rot d = M.opp d
    · have h' : M.rot (M.opp d) ≠ d := fun h' => hloop ⟨h, h'⟩
      refine ⟨M.rot (M.opp d), ⟨h', hr2⟩, ?_⟩
      Ξ M.vert_rot, ← h, M.vert_rot
    · exact ⟨M.rot d, ⟨hr1, h⟩, M.vert_rot d⟩
  · by_cases h : M.rot (M.opp n) = n
    · have h' : M.rot n ≠ M.opp n := fun h' => hloop ⟨h', h⟩
      refine ⟨M.rot n, ⟨hr1, h'⟩, ?_⟩
      calc M.vert (M.rot n) = M.vert n := M.vert_rot n
        _ = M.vert (M.rot (M.opp n)) := Ρ h
        _ = M.vert (M.opp n) := M.vert_rot _
    · exact ⟨M.rot (M.opp n), ⟨h, hr2⟩, M.vert_rot _⟩

omit [Fintype D] [DecidableEq F] in
/-- The merged face keeps a dart. -/
theorem exists_keep_merged (hn : M.face n ≠ M.face (M.opp n))
    (hloop : ¬ (M.rot n = M.opp n ∧ M.rot (M.opp n) = n)) : ∃ x, M.Keep n x ∧
    (M.face x = M.face n ∨ M.face x = M.face (M.opp n)) := by
  have hf1 : M.fperm n ≠ M.opp n := fun h => hn (Ρ ← h, M.face_fperm_apply)
  have hf2 : M.fperm (M.opp n) ≠ n := fun h => hn (Ρ ← M.face_fperm_apply (M.opp n), h)
  by_cases h1 : M.fperm n = n
  · have h2 : M.fperm (M.opp n) ≠ M.opp n := by
      intro h2
      apply hloop
      rw [fperm_apply] at h1 h2
      rw [M.opp_opp] at h2
      exact ⟨h2, h1⟩
    exact ⟨M.fperm (M.opp n), ⟨hf2, h2⟩, Or.inr (M.face_fperm_apply _)⟩
  · exact ⟨M.fperm n, ⟨h1, hf1⟩, Or.inl (M.face_fperm_apply _)⟩

/-- **Deleting an edge between two distinct faces.** -/
noncomputable def deleteEdge (hn : M.face n ≠ M.face (M.opp n))
    (hloop : ¬ (M.rot n = M.opp n ∧ M.rot (M.opp n) = n)) :
    CombMap V {g : F // g ≠ M.face (M.opp n)} {x // M.Keep n x} where
  rot := M.delRot n
  opp := M.delOpp n
  vert x := M.vert x.1
  face := M.delFace hn
  opp_opp x := Subtype.ext (M.opp_opp x.1)
  opp_ne x h := M.opp_ne x.1 (congrArg Subtype.val h)
  vert_rot x := by
    show M.vert ((M.delRot n x).1) = M.vert x.1
    Ξ delRot, firstReturn_apply
    exact (eq_of_sameCycle M.rot M.vert M.vert_rot ⟨(returnTime M.rot (M.Keep n) x : ℤ),
      Ρ zpow_natCast⟩).symm
  sameCycle_of_vert x y h := by
    Ξ delRot, sameCycle_firstReturn_iff
    exact M.sameCycle_of_vert _ _ h
  face_fperm x := by
    show M.delFace hn ((M.delRot n * M.delOpp n) x) = M.delFace hn x
    Ξ M.deleteEdge_fperm_eq n, M.delFace_eq_iff hn, ← sameCycle_firstReturn_iff
    exact (Perm.SameCycle.refl _ _).symm.trans ⟨1, Ρ zpow_one⟩ |>.symm
  sameCycle_of_face x y h := by
    Ξ M.deleteEdge_fperm_eq n, sameCycle_firstReturn_iff
    exact (M.delFace_eq_iff hn x y).mp h
  vert_surj v := by
    obtain ⟨x, hx, hv⟩ := M.exists_keep_vert hn hloop v
    exact ⟨⟨x, hx⟩, hv⟩
  face_surj g := by
    by_cases hg : g.1 = M.face n
    · obtain ⟨x, hx, hxf⟩ := M.exists_keep_merged hn hloop
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      unfold delFace
      split_ifs with h
      · exact hg.symm
      · rcases hxf with hxf | hxf
        · exact hxf.trans hg.symm
        · exact absurd hxf h
    · obtain ⟨d, hd⟩ := M.face_surj g.1
      have hk : M.Keep n d := ⟨fun h => hg (Ρ ← hd, h), fun h => g.2 (by rw [← hd, h])⟩
      refine ⟨⟨d, hk⟩, Subtype.ext ?_⟩
      unfold delFace
      Ξ dite_eq_right_of_eq_false (eq_false (by rw [hd]; exact g.2))
      exact hd

/-- Deletion keeps the vertices of the remaining darts. -/
@[simp] theorem deleteEdge_vert (hn : M.face n ≠ M.face (M.opp n))
    (hloop : ¬ (M.rot n = M.opp n ∧ M.rot (M.opp n) = n))
    (x : {x // M.Keep n x}) :
    (M.deleteEdge hn hloop).vert x = M.vert x.1 := rfl

/-- Deletion keeps the heads of the remaining darts. -/
@[simp] theorem deleteEdge_head (hn : M.face n ≠ M.face (M.opp n))
    (hloop : ¬ (M.rot n = M.opp n ∧ M.rot (M.opp n) = n))
    (x : {x // M.Keep n x}) :
    (M.deleteEdge hn hloop).head x = M.head x.1 := rfl

variable [Fintype V] [Fintype F]

end Delete

/-! ### Contraction as deletion in the dual -/

section Contract

variable [DecidableEq V] {n : D} (hn : M.vert n ≠ M.vert (M.opp n))
  (hiso : ¬ (M.fperm n = M.opp n ∧ M.fperm (M.opp n) = n))

end Contract

end CombMap

end

end Chazelle.Separator
