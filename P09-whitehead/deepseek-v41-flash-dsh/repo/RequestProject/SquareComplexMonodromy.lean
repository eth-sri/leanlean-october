module

public import RequestProject.SquareComplexPi1

@[expose] public section

/-!
# Monodromy of a covering of square complexes

For a covering `p : T → B` of square complexes, lifting a walk of the base which starts at
`p x₀` gives a walk of `T` starting at `x₀`; its end point depends only on the homotopy class of
the walk.  This defines the **monodromy map**

`FiniteChains.SquareComplex.IsCovering.monodromy : B.Pi1 (p x₀) → Vt`,

which takes values in the fibre over `p x₀`.  The main theorem,
`FiniteChains.SquareComplex.IsCovering.monodromy_bijective`, says that for a connected and simply
connected covering complex the monodromy map is a bijection from the fundamental group of the
base onto the fibre — the combinatorial form of the classical identification
`π₁(B) ≅ p⁻¹(b₀)` for the universal covering.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

namespace SquareComplex


variable {Vt : Type u} {Vb : Type v} {T : SquareComplex Vt} {B : SquareComplex Vb} {p : Vt → Vb}

namespace IsCovering

/-- The image of an elementary move is an elementary move. -/
theorem map_move (hp : IsCovering T B p) {l l' : List Vt} (h : T.Move l l') :
    B.Move (l.map p) (l'.map p) := by
  induction h with
  | backtrack x y q => exact Move.backtrack (p x) (p y) (q.map p)
  | square hsq q => exact Move.square (hp.map_sq hsq) (q.map p)
  | cons x _ ih => exact Move.cons (p x) ih

theorem map_walkMove (hp : IsCovering T B p) {l l' : List Vt} (h : T.WalkMove l l') :
    B.WalkMove (l.map p) (l'.map p) := by
  rcases h with ⟨hm, hw⟩ | ⟨hm, hw⟩
  · exact Or.inl ⟨hp.map_move hm, hp.map_isWalk hw⟩
  · exact Or.inr ⟨hp.map_move hm, hp.map_isWalk hw⟩

/-- The image of a homotopy through walks is a homotopy through walks. -/
theorem map_walkHomotopic (hp : IsCovering T B p) {l l' : List Vt} (h : T.WalkHomotopic l l') :
    B.WalkHomotopic (l.map p) (l'.map p) := by
  induction h with
  | refl => exact WalkHomotopic.refl _
  | tail _ hstep ih => exact ih.trans (WalkHomotopic.of_walkMove (hp.map_walkMove hstep))

open Classical in
/-- The end point of the unique lift, issuing from `x`, of the edge from `p x` to `w`
(junk value `x` when `p x` and `w` are not joined by an edge). -/
noncomputable def edgeLift (hp : IsCovering T B p) (x : Vt) (w : Vb) : Vt :=
  if h : B.adj (p x) w then (hp.lift_adj x h).exists.choose else x

theorem edgeLift_spec (hp : IsCovering T B p) {x : Vt} {w : Vb} (h : B.adj (p x) w) :
    T.adj x (hp.edgeLift x w) ∧ p (hp.edgeLift x w) = w := by
  classical
  rw [edgeLift, dif_pos h]
  exact (hp.lift_adj x h).exists.choose_spec

/-- The end point of the lift, issuing from `x`, of a walk of the base. -/
noncomputable def liftEnd (hp : IsCovering T B p) :
    ∀ {b c : Vb}, (toSimpleGraph B).Walk b c → Vt → Vt
  | _, _, SimpleGraph.Walk.nil => fun x => x
  | _, _, @SimpleGraph.Walk.cons _ _ _ v _ _ q => fun x => hp.liftEnd q (hp.edgeLift x v)

@[simp] theorem liftEnd_nil (hp : IsCovering T B p) (b : Vb) (x : Vt) :
    hp.liftEnd (SimpleGraph.Walk.nil (u := b)) x = x := rfl

@[simp] theorem liftEnd_cons (hp : IsCovering T B p) {b v c : Vb}
    (h : (toSimpleGraph B).Adj b v) (q : (toSimpleGraph B).Walk v c) (x : Vt) :
    hp.liftEnd (SimpleGraph.Walk.cons h q) x = hp.liftEnd q (hp.edgeLift x v) := rfl

/-- **The lift exists**: over any walk of the base issuing from `p x` there is a walk of `T`
issuing from `x` and ending at `liftEnd`. -/
theorem liftEnd_spec (hp : IsCovering T B p) : ∀ {b c : Vb} (w : (toSimpleGraph B).Walk b c)
    (x : Vt), p x = b →
    ∃ lt : List Vt, T.IsWalk lt ∧ lt.head? = some x ∧ lt.getLast? = some (hp.liftEnd w x) ∧
      lt.map p = w.support := by
  intro b c w
  induction w with
  | nil =>
      intro x hx
      exact ⟨[x], by simp [IsWalk], by simp, by simp, by simp [hx]⟩
  | @cons b' v c' hadj q ih =>
      intro x hx
      have hadj' : B.adj (p x) v := by rw [hx]; exact hadj
      obtain ⟨hxy, hpy⟩ := hp.edgeLift_spec hadj'
      obtain ⟨lt, hw, hh, hlast, hmap⟩ := ih (hp.edgeLift x v) hpy
      have hne : lt ≠ [] := by
        intro hnil; rw [hnil] at hh; simp at hh
      refine ⟨x :: lt, isWalk_cons hw ?_, by simp, ?_, ?_⟩
      · intro y hy
        rw [hh] at hy
        simp at hy
        subst hy
        exact hxy
      · cases hlt : lt with
        | nil => exact absurd hlt hne
        | cons a t =>
            rw [hlt] at hlast
            rw [List.getLast?_cons_cons]
            exact hlast
      · rw [List.map_cons, hmap, hx, SimpleGraph.Walk.support_cons]

/-- **Uniqueness of the lift**: any walk of `T` lying over `w` and issuing from `x` ends at
`liftEnd`. -/
theorem liftEnd_eq_of_lift (hp : IsCovering T B p) {b c : Vb} (w : (toSimpleGraph B).Walk b c)
    {x : Vt} {lt : List Vt} (hw : T.IsWalk lt) (hh : lt.head? = some x)
    (hmap : lt.map p = w.support) : lt.getLast? = some (hp.liftEnd w x) := by
  have hx : p x = b := by
    have h1 : (lt.map p).head? = some (p x) := by rw [List.head?_map, hh]; rfl
    rw [hmap, SimpleGraph.Walk.support_eq_cons] at h1
    cases w <;> simpa using h1.symm
  obtain ⟨lt', hw', hh', hlast', hmap'⟩ := hp.liftEnd_spec w x hx
  have : lt = lt' := hp.lift_unique hw hw' (by rw [hh, hh']) (by rw [hmap, hmap'])
  rw [this]
  exact hlast'

/-- **Homotopy invariance**: homotopic walks of the base have lifts with the same end point. -/
theorem liftEnd_congr (hp : IsCovering T B p) {b c : Vb} {w w' : (toSimpleGraph B).Walk b c}
    (h : B.WalkHtpy w w') {x : Vt} (hx : p x = b) : hp.liftEnd w x = hp.liftEnd w' x := by
  obtain ⟨lt, hw, hh, hlast, hmap⟩ := hp.liftEnd_spec w x hx
  obtain ⟨lt', hw', hh', hmap', hhom⟩ := hp.lift_walkHomotopic h hw hmap
  have h1 : lt'.getLast? = some (hp.liftEnd w' x) :=
    hp.liftEnd_eq_of_lift w' hw' (by rw [hh', hh]) hmap'
  have h2 : lt.getLast? = lt'.getLast? := hhom.getLast?_eq
  rw [hlast, h1] at h2
  simpa using h2

/-! ### The monodromy map -/

/-- **The monodromy map**: the class of a closed walk of the base at `p x₀` goes to the end point
of its lift issuing from `x₀`. -/
noncomputable def monodromy (hp : IsCovering T B p) (x₀ : Vt) : B.Pi1 (p x₀) → Vt :=
  Quotient.lift (fun w => hp.liftEnd w x₀) (fun _ _ h => hp.liftEnd_congr h rfl)

@[simp] theorem monodromy_mk (hp : IsCovering T B p) (x₀ : Vt)
    (w : (toSimpleGraph B).Walk (p x₀) (p x₀)) :
    hp.monodromy x₀ (Pi1.mk w) = hp.liftEnd w x₀ := rfl

@[simp] theorem monodromy_one (hp : IsCovering T B p) (x₀ : Vt) :
    hp.monodromy x₀ 1 = x₀ := rfl

/-! ### The map induced on fundamental groups -/

/-- The image of a walk of the covering complex. -/
def mapWalk (hp : IsCovering T B p) :
    ∀ {x y : Vt}, (toSimpleGraph T).Walk x y → (toSimpleGraph B).Walk (p x) (p y)
  | _, _, SimpleGraph.Walk.nil => SimpleGraph.Walk.nil
  | _, _, SimpleGraph.Walk.cons h q => SimpleGraph.Walk.cons (hp.map_adj h) (hp.mapWalk q)

@[simp] theorem mapWalk_nil (hp : IsCovering T B p) (x : Vt) :
    hp.mapWalk (SimpleGraph.Walk.nil (u := x)) = SimpleGraph.Walk.nil := rfl

@[simp] theorem mapWalk_cons (hp : IsCovering T B p) {x y z : Vt}
    (h : (toSimpleGraph T).Adj x y) (q : (toSimpleGraph T).Walk y z) :
    hp.mapWalk (SimpleGraph.Walk.cons h q)
      = SimpleGraph.Walk.cons (hp.map_adj h) (hp.mapWalk q) := rfl

theorem support_mapWalk (hp : IsCovering T B p) :
    ∀ {x y : Vt} (w : (toSimpleGraph T).Walk x y), (hp.mapWalk w).support = w.support.map p := by
  intro x y w
  induction w with
  | nil => simp
  | cons h q ih => simp [ih]

theorem mapWalk_append (hp : IsCovering T B p) :
    ∀ {x y z : Vt} (w : (toSimpleGraph T).Walk x y) (v : (toSimpleGraph T).Walk y z),
      hp.mapWalk (w.append v) = (hp.mapWalk w).append (hp.mapWalk v) := by
  intro x y z w v
  induction w with
  | nil => rfl
  | cons h q ih => simp [SimpleGraph.Walk.cons_append, ih]

/-- **The homomorphism induced by a covering on fundamental groups.** -/
def pi1Map (hp : IsCovering T B p) (x₀ : Vt) : T.Pi1 x₀ →* B.Pi1 (p x₀) where
  toFun := Quotient.lift (fun w => Pi1.mk (hp.mapWalk w))
    (by
      intro w w' h
      refine Pi1.mk_eq_mk.2 ?_
      show B.WalkHomotopic (hp.mapWalk w).support (hp.mapWalk w').support
      rw [support_mapWalk, support_mapWalk]
      exact hp.map_walkHomotopic h)
  map_one' := rfl
  map_mul' := by
    refine Quotient.ind fun w => Quotient.ind fun v => ?_
    show Pi1.mk (hp.mapWalk (w.append v)) = Pi1.mk (hp.mapWalk w) * Pi1.mk (hp.mapWalk v)
    rw [Pi1.mul_mk, hp.mapWalk_append]

@[simp] theorem pi1Map_mk (hp : IsCovering T B p) (x₀ : Vt)
    (w : (toSimpleGraph T).Walk x₀ x₀) : hp.pi1Map x₀ (Pi1.mk w) = Pi1.mk (hp.mapWalk w) := rfl

end IsCovering

end SquareComplex

end FiniteChains
