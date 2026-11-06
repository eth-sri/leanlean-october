module

public import Chazelle.Golf

public import Chazelle.Separator.Tree
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# The cotree of a spanning tree and the Jordan property of fundamental cycles
(planar separators, part 3b)

Let `T` be a rooted spanning tree of a map `M`.  The non-tree darts (`coDarts`) join faces:
`faceRel S f g` says that some dart `e ∈ S` has `face e = f` and `face (opp e) = g`.

* **Cotree connectivity** (`eqvGen_faceRel_coDarts`): for any spanning tree of a connected map,
  the faces are connected through non-tree edges.  Proof: a proper union `K` of faces closed
  under crossing non-tree edges has a boundary made of tree darts, and every boundary dart has
  a successor boundary dart at its head which is not its reverse; the potential
  `L + level` (upward darts) / `L - level` (downward darts) strictly decreases along
  successors, which is impossible (a tree has no infinite non-backtracking walk).
* **Counting** (`two_mul_numComp_le`): adding an edge merges at most two classes, so
  `2·#classes(S) ≤ 2·#classes(S') + |S' \ S|`.
* **The cotree is a tree** (`not_eqvGen_faceRel`, *acyclicity*): in a *planar* map the
  non-tree edges are `F − 1` (Euler), connect the `F` faces, hence no set of non-tree edges
  already connects the two sides of another non-tree edge.
* For a non-tree dart `d`, removing its edge from the cotree leaves exactly two classes:
  `cross d` (the side entered when crossing `d`) and `cross (opp d)`
  (`mem_cross_or`, `notMem_cross_opp`); `cross_subset`: crossing on from the face entered
  through `d` along another non-tree dart leads into a subset of `cross d`.
* **Jordan property of fundamental cycles** (`face_par_eqvGen`, the parity argument, and
  `eqvGen_face_of_vert`): if a vertex `v` is not on the tree paths from the endpoints of `d` to
  the root, all faces around `v` lie on the same side of the fundamental cycle of `d`; hence two
  adjacent such vertices lie on the same side.  The parity argument: the face walks of one side
  cross the cut of a subtree as often outwards as inwards, while the only unmatched crossing
  would be the tree edge above the subtree.
* **Euler's inequality** (`euler_le_two`): every connected map has `χ ≤ 2`, so `Planar` means
  "connected with maximal Euler characteristic" (`planar_iff`).
-/

namespace Chazelle.Separator

@[expose] public section

open Equiv Finset Relation

namespace CombMap

variable {V F D : Type*} (M : CombMap V F D)

/-! ### Faces joined through a set of darts -/

/-- `faceRel S f g`: some dart `e ∈ S` has `f` on its side and `g` on the other side. -/
def faceRel (S : Finset D) (f g : F) : Prop := ∃ e ∈ S, M.face e = f ∧ M.face (M.opp e) = g

/-- A dart set closed under `opp` (a set of edges). -/
def OppClosed (S : Finset D) : Prop := ∀ e ∈ S, M.opp e ∈ S

/-- The number of classes of faces joined through `S`. -/
noncomputable def numComp (S : Finset D) : ℕ := Nat.card (Quot (M.faceRel S))

variable {M}

/-- Face adjacency is monotone in the dart set. -/
theorem faceRel_mono {S S' : Finset D} (h : S ⊆ S') {f g : F} (hfg : M.faceRel S f g) :
    M.faceRel S' f g := by
  obtain ⟨e, he, h1, h2⟩ := hfg
  exact ⟨e, h he, h1, h2⟩

/-- Face connectivity is monotone in the dart set. -/
theorem eqvGen_faceRel_mono {S S' : Finset D} (h : S ⊆ S') {f g : F}
    (hfg : EqvGen (M.faceRel S) f g) : EqvGen (M.faceRel S') f g :=
  EqvGen.mono (fun _ _ => faceRel_mono h) _ _ hfg

/-- For an edge set (closed under `opp`), face adjacency is symmetric. -/
theorem faceRel_opp {S : Finset D} (hS : M.OppClosed S) {f g : F} (h : M.faceRel S f g) :
    M.faceRel S g f := by
  obtain ⟨e, he, rfl, rfl⟩ := h
  exact ⟨M.opp e, hS e he, rfl, Ρ M.opp_opp⟩

variable [DecidableEq D]

/-- Adding the edge of `e` to `S` adds the pair `(face e, face (opp e))` to face adjacency. -/
theorem eqvGen_faceRel_insert (S : Finset D) (e : D) {x y : F} :
    EqvGen (M.faceRel (insert e (insert (M.opp e) S))) x y ↔
      EqvGen (fun a b => M.faceRel S a b ∨ (a = M.face e ∧ b = M.face (M.opp e))) x y := by
  apply eqvGen_iff_of_le
  · rintro a b ⟨e', he', rfl, rfl⟩
    simp only [Finset.mem_insert] at he'
    rcases he' with rfl | rfl | he'
    · exact EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩)
    · exact EqvGen.symm _ _ (EqvGen.rel _ _ (Or.inr ⟨by rw [M.opp_opp], rfl⟩))
    · exact EqvGen.rel _ _ (Or.inl ⟨e', he', rfl, rfl⟩)
  · rintro a b (h | ⟨rfl, rfl⟩)
    · exact EqvGen.rel _ _ (faceRel_mono (by intro x hx; simp [hx]) h)
    · exact EqvGen.rel _ _ ⟨e, by simp, rfl, rfl⟩

variable [Finite F]

/-- Adding an edge lowers the number of face classes by at most one. -/
theorem numComp_le_insert (S : Finset D) (e : D) :
    M.numComp S ≤ M.numComp (insert e (insert (M.opp e) S)) + 1 := by
  unfold numComp
  Ξ card_quot_eq_of_eqvGen_iff _ _ (fun x y => M.eqvGen_faceRel_insert S e (x := x) (y := y))
  exact card_quot_le_or_pair_add_one _ _ _

/-- Adding an edge whose sides are already joined does not change the face classes. -/
theorem numComp_insert_eq (S : Finset D) (e : D)
    (h : EqvGen (M.faceRel S) (M.face e) (M.face (M.opp e))) :
    M.numComp (insert e (insert (M.opp e) S)) = M.numComp S := by
  unfold numComp
  Ξ card_quot_eq_of_eqvGen_iff _ _ (fun x y => M.eqvGen_faceRel_insert S e (x := x) (y := y))
  exact card_quot_or_pair_eq _ _ _ h

omit [Finite F] in
/-- Adding an edge to an edge set gives an edge set. -/
theorem OppClosed.insert_pair {S : Finset D} (hS : M.OppClosed S) (e : D) :
    M.OppClosed (insert e (insert (M.opp e) S)) := by
  intro x hx
  ϴ' Finset.mem_insert at hx ⊢
  rcases hx with rfl | rfl | hx
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (M.opp_opp _)
  · exact Or.inr (Or.inr (hS x hx))

/-- **Counting.**  `2·#classes(S) ≤ 2·#classes(S') + |S' \ S|` for edge sets `S ⊆ S'`. -/
theorem two_mul_numComp_le {S' : Finset D} (hS' : M.OppClosed S') :
    ∀ (n : ℕ) (S : Finset D), M.OppClosed S → S ⊆ S' → (S' \ S).card = n →
      2 * M.numComp S ≤ 2 * M.numComp S' + n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS hSS' hn
  by_cases hcase : (S' \ S).Nonempty
  · obtain ⟨e, he⟩ := hcase
    Ξ' Finset.mem_sdiff at he
    have hoe : M.opp e ∉ S := fun h => he.2 (by simpa [M.opp_opp] using hS _ h)
    have hoe' : M.opp e ∈ S' := hS' e he.1
    have hne : M.opp e ≠ e := M.opp_ne e
    have hS1S' : insert e (insert (M.opp e) S) ⊆ S' := by
      intro x hx
      ϴ' Finset.mem_insert at hx
      rcases hx with rfl | rfl | hx
      · exact he.1
      · exact hoe'
      · exact hSS' hx
    have hcard : (S' \ insert e (insert (M.opp e) S)).card + 2 = (S' \ S).card := by
      have h1 : S' \ insert e (insert (M.opp e) S) = ((S' \ S).erase e).erase (M.opp e) := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
      have h2 : M.opp e ∈ (S' \ S).erase e := by
        Θ Finset.mem_erase, hne, hoe', hoe
      Ξ h1, Finset.card_erase_of_mem h2, Finset.card_erase_of_mem (⊚ he.1, he.2)
      have : 2 ≤ (S' \ S).card := by
        have hsub : ({e, M.opp e} : Finset D) ⊆ S' \ S := by
          intro x hx; ϴ' Finset.mem_insert, Finset.mem_singleton at hx
          rcases hx with rfl | rfl
          · Θ he.1, he.2
          · Θ hoe', hoe
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair hne.symm] at this
      omega
    have h1 := ih _ (⋄) _ (hS.insert_pair e) hS1S' rfl
    have h2 := M.numComp_le_insert S e
    omega
  · have hempty : S' \ S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcase
    have hSS : S' = S := (Finset.sdiff_eq_empty_iff_subset.mp hempty).antisymm hSS'
    subst hSS; omega

omit [DecidableEq D] [Finite F] in
/-- With no edges, every face is its own class. -/
theorem numComp_empty : M.numComp ∅ = Nat.card F :=
  card_quot_bot _ (fun _ _ ⟨e, he, _⟩ => absurd he (Finset.notMem_empty e))

end CombMap

/-! ### The cotree of a spanning tree -/

namespace CombMap.SpanTree

variable {V F D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
variable {M : CombMap V F D} (T : SpanTree M)

/-- The non-tree darts. -/
def coDarts : Finset D := Finset.univ \ T.treeDarts

/-- A dart is a non-tree dart iff it is not a tree dart. -/
theorem mem_coDarts {d : D} : d ∈ T.coDarts ↔ ¬ T.IsTreeDart d := by
  Θ coDarts, T.mem_treeDarts

/-- The opposite of a non-tree dart is a non-tree dart. -/
theorem opp_mem_coDarts {d : D} (hd : d ∈ T.coDarts) : M.opp d ∈ T.coDarts := by
  Ξ' mem_coDarts at hd ⊢
  intro h
  apply hd
  have := T.opp_mem_treeDarts ((T.mem_treeDarts).mpr h)
  Ξ' M.opp_opp at this
  exact (T.mem_treeDarts).mp this

/-- The non-tree darts form an edge set. -/
theorem coDarts_oppClosed : M.OppClosed T.coDarts := fun _ he => T.opp_mem_coDarts he

/-! #### Cotree connectivity -/

/-- The descending potential of a tree dart. -/
noncomputable def potential (L : ℕ) (d : D) : ℕ :=
  if ∃ u, u ≠ T.root ∧ d = T.par u then L + T.level (M.vert d) else L - T.level (M.head d)

omit [Fintype D] in
/-- The potential of an upward tree dart `par u`. -/
theorem potential_up (L : ℕ) {u : V} (hu : u ≠ T.root) :
    T.potential L (T.par u) = L + T.level u := by
  Ξ potential, ite_eq_left ⟨u, hu, rfl⟩, T.vert_par u hu

omit [Fintype D] in
/-- The potential of a downward tree dart `opp (par u)`. -/
theorem potential_down (L : ℕ) {u : V} (hu : u ≠ T.root) :
    T.potential L (M.opp (T.par u)) = L - T.level u := by
  Ξ potential, ite_eq_right
  · Ξ M.head_opp, T.vert_par u hu
  · rintro ⟨w, hw, h⟩
    exact T.par_ne_opp_par hw hu h.symm

/-! #### The two sides of a non-tree edge -/

/-- The non-tree darts other than `d` and `opp d`. -/
def Sd (d : D) : Finset D := T.coDarts.filter (fun e => e ≠ d ∧ e ≠ M.opp d)

/-- Membership in the cotree minus the edge of `d`. -/
theorem mem_Sd {d e : D} : e ∈ T.Sd d ↔ e ∈ T.coDarts ∧ e ≠ d ∧ e ≠ M.opp d := by
  Θ Sd

/-- The cotree minus an edge is part of the cotree. -/
theorem Sd_subset (d : D) : T.Sd d ⊆ T.coDarts := Finset.filter_subset _ _

/-- The dart `d` itself is removed. -/
theorem notMem_Sd_self (d : D) : d ∉ T.Sd d := ⊚ Sd

/-- The cotree minus an edge is an edge set. -/
theorem Sd_oppClosed (d : D) : M.OppClosed (T.Sd d) := by
  intro e he
  Ξ' mem_Sd at he ⊢
  refine ⟨T.opp_mem_coDarts he.1, fun h => he.2.2 ?_, fun h => he.2.1 (M.opp_injective h)⟩
  Ξ ← h, M.opp_opp

/-- Removing the edge of `d` or of `opp d` is the same. -/
theorem Sd_opp (d : D) : T.Sd (M.opp d) = T.Sd d := by
  ext e; simp only [mem_Sd, M.opp_opp]; tauto

/-- The cotree is the cotree minus the edge of `d` plus that edge. -/
theorem coDarts_eq_insert {d : D} (hd : d ∈ T.coDarts) :
    T.coDarts = insert d (insert (M.opp d) (T.Sd d)) := by
  ext e
  ϴ Finset.mem_insert, mem_Sd
  constructor
  · intro he
    by_cases h1 : e = d
    · exact Or.inl h1
    by_cases h2 : e = M.opp d
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr ⟨he, h1, h2⟩)
  · rintro (rfl | rfl | ⟨he, -, -⟩)
    · exact hd
    · exact T.opp_mem_coDarts hd
    · exact he

/-! #### The Jordan property of fundamental cycles -/

/-- **Parity argument.**  Let `y` be a non-root vertex and `d` a non-tree dart whose endpoints
are both inside or both outside the subtree of `y`.  Then the two faces of the tree edge above
`y` are joined by non-tree edges other than the edge of `d`. -/
theorem face_par_eqvGen {y : V} (hy : y ≠ T.root) {d : D} (hd : d ∈ T.coDarts)
    (hiff : T.IsAnc y (M.vert d) ↔ T.IsAnc y (M.head d)) :
    EqvGen (M.faceRel (T.Sd d)) (M.face (T.par y)) (M.face (M.opp (T.par y))) := by
  classical
  by_contra hK
  set R := M.faceRel (T.Sd d)
  set A := Finset.univ.filter
    (fun e => EqvGen R (M.face (T.par y)) (M.face e) ∧ T.IsAnc y (M.vert e))
  set Bh := Finset.univ.filter
    (fun e => EqvGen R (M.face (T.par y)) (M.face e) ∧ T.IsAnc y (M.head e))
  -- `fperm` maps `Bh` onto `A`
  have hAB : A.card = Bh.card := by
    symm
    apply Finset.card_nbij' (fun e => M.fperm e) (fun e => M.fperm.symm e)
    · intro e he
      ϴ' Bh, A, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq at he ⊢
      rw [M.face_fperm_apply, M.vert_fperm]; exact he
    · intro e he
      ϴ' Bh, A, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq at he ⊢
      have h1 : M.face (M.fperm.symm e) = M.face e := by
        Ξ ← M.face_fperm_apply (M.fperm.symm e), Equiv.apply_symm_apply
      have h2 : M.head (M.fperm.symm e) = M.vert e := by
        Ξ ← M.vert_fperm, Equiv.apply_symm_apply
      rw [h1, h2]; exact he
    · intro e _; simp
    · intro e _; simp
  have hLE : (A \ Bh).card = (Bh \ A).card := by
    have h1 := Finset.card_sdiff_add_card_inter A Bh
    have h2 := Finset.card_sdiff_add_card_inter Bh A
    Ξ' Finset.inter_comm at h2
    omega
  -- the tree dart `par y` leaves the subtree
  have hpar : T.par y ∈ A \ Bh := by
    ϴ A, Bh, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_and
    refine ⟨⟨EqvGen.refl _, by rw [T.vert_par y hy]; exact T.isAnc_refl y⟩, fun _ => ?_⟩
    Ξ ← T.parent_of_ne hy
    exact T.not_isAnc_parent hy
  -- `opp` maps `Bh \ A` into `(A \ Bh).erase (par y)`
  have hmaps : Set.MapsTo M.opp (Bh \ A : Finset D) ((A \ Bh).erase (T.par y) : Finset D) := by
    intro e he
    simp only [A, Bh, Finset.coe_sdiff, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_sdiff, Set.mem_ofPred_eq, not_and] at he
    obtain ⟨⟨hKe, hin⟩, hout⟩ := he
    have hout' : ¬ T.IsAnc y (M.vert e) := hout hKe
    -- `e` is a non-tree dart different from `d`, `opp d`
    have heS : e ∈ T.Sd d := by
      Ξ mem_Sd, mem_coDarts
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨x, hx, rfl | rfl⟩
        · apply hout'
          Ξ T.vert_par x hx
          have : M.head (T.par x) = T.parent x := (T.parent_of_ne hx).symm
          Ξ' this at hin
          exact hin.of_parent
        · have h1 : M.head (M.opp (T.par x)) = x := Ρ M.head_opp, T.vert_par x hx
          have h2 : M.vert (M.opp (T.par x)) = T.parent x := (T.parent_of_ne hx).symm
          Ξ' h1 at hin; Ξ' h2 at hout'
          have hxy := T.eq_of_isAnc_of_not_parent hin hout'
          subst hxy
          exact hK hKe
      · rintro rfl
        exact hout' (hiff.mpr hin)
      · rintro rfl
        Ξ' M.head_opp at hin
        exact hout' (by rw [show M.vert (M.opp d) = M.head d from rfl]; exact hiff.mp hin)
    have hKo : EqvGen R (M.face (T.par y)) (M.face (M.opp e)) :=
      EqvGen.trans _ _ _ hKe (EqvGen.rel _ _ ⟨e, heS, rfl, rfl⟩)
    simp only [A, Bh, Finset.coe_erase, Finset.coe_sdiff, Finset.coe_filter, Finset.mem_univ,
      true_and, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, not_and]
    refine ⟨⟨⟨hKo, hin⟩, fun _ => ?_⟩, ?_⟩
    · rw [M.head_opp]; exact hout'
    · intro h
      have : e = M.opp (T.par y) := Ρ ← h, M.opp_opp
      Ξ' this at hKe
      exact hK hKe
  have hle := Finset.card_le_card_of_injOn M.opp hmaps (M.opp_injective.injOn)
  Ξ' Finset.card_erase_of_mem hpar at hle
  have hpos : 0 < (A \ Bh).card := Finset.card_pos.mpr ⟨_, hpar⟩
  omega

/-- Around a vertex off the root paths of the endpoints of a non-tree dart `d`, consecutive
faces are on the same side of the fundamental cycle of `d`. -/
theorem eqvGen_face_rot {d : D} (hd : d ∈ T.coDarts) {v : V}
    (hv1 : ¬ T.IsAnc v (M.vert d)) (hv2 : ¬ T.IsAnc v (M.head d)) {e : D}
    (he : M.vert e = v) : EqvGen (M.faceRel (T.Sd d)) (M.face e) (M.face (M.rot e)) := by
  have hrot : M.face (M.rot e) = M.face (M.opp e) := by
    Ξ ← M.face_fperm_apply (M.opp e), fperm_apply, M.opp_opp
  Ξ hrot
  by_cases hco : e ∈ T.coDarts
  · refine EqvGen.rel _ _ ⟨e, T.mem_Sd.mpr ⟨hco, ?_, ?_⟩, rfl, rfl⟩
    · rintro rfl; exact hv1 (he ▸ T.isAnc_refl _)
    · rintro rfl; exact hv2 (by rw [← he]; exact T.isAnc_refl _)
  · Ξ' mem_coDarts, not_not at hco
    obtain ⟨x, hx, rfl | rfl⟩ := hco
    · Ξ' T.vert_par x hx at he
      subst he
      exact T.face_par_eqvGen hx hd (iff_of_false hv1 hv2)
    · have hxv : T.parent x = v := by
        rw [T.parent_of_ne hx]; exact he
      have hiff : T.IsAnc x (M.vert d) ↔ T.IsAnc x (M.head d) := by
        refine iff_of_false (fun h => hv1 ?_) (fun h => hv2 ?_)
        · rw [← hxv]; exact (T.isAnc_parent_self x).trans T h
        · rw [← hxv]; exact (T.isAnc_parent_self x).trans T h
      Ξ M.opp_opp
      exact EqvGen.symm _ _ (T.face_par_eqvGen hx hd hiff)

/-- **Jordan property, vertex form.**  All faces around a vertex `v` off the root paths of the
endpoints of a non-tree dart `d` lie on the same side of the fundamental cycle of `d`. -/
theorem eqvGen_face_of_vert {d : D} (hd : d ∈ T.coDarts) {v : V}
    (hv1 : ¬ T.IsAnc v (M.vert d)) (hv2 : ¬ T.IsAnc v (M.head d)) {e e' : D}
    (he : M.vert e = v) (he' : M.vert e' = v) :
    EqvGen (M.faceRel (T.Sd d)) (M.face e) (M.face e') := by
  have hsc : M.rot.SameCycle e e' := M.sameCycle_of_vert e e' (he.trans he'.symm)
  refine (mem_of_sameCycle M.rot
    {x | M.vert x = v ∧ EqvGen (M.faceRel (T.Sd d)) (M.face e) (M.face x)} ?_ hsc
    ⟨he, EqvGen.refl _⟩).2
  rintro x ⟨hx, hex⟩
  exact ⟨by rw [M.vert_rot, hx], EqvGen.trans _ _ _ hex (T.eqvGen_face_rot hd hv1 hv2 hx)⟩

/-- **Jordan property, edge form.**  The two endpoints of a dart `e`, both off the root paths of
the endpoints of the non-tree dart `d`, have their faces on the same side of the fundamental
cycle of `d`. -/
theorem eqvGen_face_of_dart {d : D} (hd : d ∈ T.coDarts) (e : D)
    (h1 : ¬ T.IsAnc (M.vert e) (M.vert d)) (h2 : ¬ T.IsAnc (M.vert e) (M.head d))
    (h3 : ¬ T.IsAnc (M.head e) (M.vert d)) (h4 : ¬ T.IsAnc (M.head e) (M.head d))
    {x x' : D} (hx : M.vert x = M.vert e) (hx' : M.vert x' = M.head e) :
    EqvGen (M.faceRel (T.Sd d)) (M.face x) (M.face x') := by
  have hrot : M.face (M.rot e) = M.face (M.opp e) := by
    Ξ ← M.face_fperm_apply (M.opp e), fperm_apply, M.opp_opp
  have k1 := T.eqvGen_face_of_vert hd h1 h2 hx (M.vert_rot e)
  have k2 := T.eqvGen_face_of_vert hd h3 h4 (e := M.opp e) rfl hx'
  Ξ' hrot at k1
  exact EqvGen.trans _ _ _ k1 k2

section FiniteFaces

variable [Fintype F]

omit [Fintype F] in
/-- **Cotree connectivity.**  In a connected map, the faces are connected through the non-tree
edges of any spanning tree. -/
theorem eqvGen_faceRel_coDarts (hM : M.Connected) (f g : F) :
    EqvGen (M.faceRel T.coDarts) f g := by
  classical
  by_contra hfg
  set K : Set F := {x | EqvGen (M.faceRel T.coDarts) f x} with hK
  -- boundary darts
  set B : Finset D := Finset.univ.filter (fun d => M.face d ∈ K ∧ M.face (M.opp d) ∉ K)
  have hKclosed : ∀ e ∈ T.coDarts, M.face e ∈ K → M.face (M.opp e) ∈ K := fun e he hx =>
    EqvGen.trans _ _ _ hx (EqvGen.rel _ _ ⟨e, he, rfl, rfl⟩)
  have hBnonempty : B.Nonempty := by
    by_contra hB
    rw [Finset.not_nonempty_iff_eq_empty] at hB
    have hopp : ∀ d, M.face d ∈ K → M.face (M.opp d) ∈ K := by
      intro d hd
      by_contra h
      have : d ∈ B := by simp [B, hd, h]
      rw [hB] at this; simp at this
    obtain ⟨d0, hd0⟩ := M.face_surj f
    obtain ⟨dg, hdg⟩ := M.face_surj g
    have := hM.of_face {d | M.face d ∈ K}
      (fun d e hde hd => by rw [Set.mem_ofPred_eq, ← hde]; exact hd)
      (fun d hd => hopp d hd) (d := d0) (by simp [hK, hd0, EqvGen.refl]) dg
    exact hfg (by simpa [hK, hdg] using this)
  have hBtree : ∀ d ∈ B, T.IsTreeDart d := by
    intro d hd
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hd
    by_contra h
    exact hd.2 (hKclosed d ((T.mem_coDarts).mpr h) hd.1)
  -- successor boundary dart
  have hsucc : ∀ d ∈ B, ∃ d' ∈ B, M.vert d' = M.head d ∧ d' ≠ M.opp d := by
    intro d hd
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hd
    by_contra hno
    push Not at hno
    have hclosed : ∀ y ∈ {x | M.vert x = M.head d ∧ M.face x ∈ K},
        M.rot y ∈ {x | M.vert x = M.head d ∧ M.face x ∈ K} := by
      rintro y ⟨hy1, hy2⟩
      refine ⟨by rw [M.vert_rot, hy1], ?_⟩
      by_contra hy3
      have hyB : y ∈ B := by
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hy2, ?_⟩
        rwa [← M.face_fperm_apply (M.opp y), fperm_apply, M.opp_opp]
      have := hno y hyB hy1
      subst this
      exact hd.2 hy2
    have hstart : M.fperm d ∈ {x | M.vert x = M.head d ∧ M.face x ∈ K} :=
      ⟨M.vert_fperm d, by rw [M.face_fperm_apply]; exact hd.1⟩
    have hsc : M.rot.SameCycle (M.fperm d) (M.opp d) :=
      M.sameCycle_of_vert _ _ (by rw [M.vert_fperm]; rfl)
    exact hd.2 (mem_of_sameCycle M.rot _ hclosed hsc hstart).2
  -- the potential decreases along successors
  set L : ℕ := Finset.univ.sup T.level
  have hL : ∀ v, T.level v ≤ L := fun v => Finset.le_sup (Finset.mem_univ v)
  have hdec : ∀ d ∈ B, ∀ d' ∈ B, M.vert d' = M.head d → d' ≠ M.opp d →
      T.potential L d' < T.potential L d := by
    intro d hd d' hd' hv hne
    obtain ⟨u, hu, rfl | rfl⟩ := hBtree d hd <;> obtain ⟨u', hu', rfl | rfl⟩ := hBtree d' hd'
    · -- up, up
      rw [T.potential_up L hu, T.potential_up L hu']
      rw [T.vert_par u' hu'] at hv
      have := T.level_head_par u hu
      rw [← hv] at this; omega
    · -- up, down
      rw [T.potential_up L hu, T.potential_down L hu']
      have := T.level_pos hu; omega
    · -- down, up: impossible
      exfalso
      rw [T.vert_par u' hu', M.head_opp, T.vert_par u hu] at hv
      subst hv
      exact hne (M.opp_opp _).symm
    · -- down, down
      rw [T.potential_down L hu, T.potential_down L hu']
      have h1 := T.level_head_par u' hu'
      have hv' : M.head (T.par u') = u := by
        have : M.vert (M.opp (T.par u')) = M.head (M.opp (T.par u)) := hv
        rw [M.head_opp, T.vert_par u hu] at this
        exact this
      rw [hv'] at h1
      have := hL u'
      omega
  obtain ⟨d, hd, hmin⟩ := B.exists_min_image (T.potential L) hBnonempty
  obtain ⟨d', hd', hv, hne⟩ := hsucc d hd
  exact absurd (hmin d' hd') (not_le.mpr (hdec d hd d' hd' hv hne))

/-! #### Acyclicity of the cotree in a planar map -/

omit [DecidableEq V] [DecidableEq D] in
/-- A planar map has at least one vertex. -/
theorem card_vert_pos (hM : M.Planar) : 0 < Fintype.card V := by
  by_contra h
  have hV : Fintype.card V = 0 := ⋄
  have hVe : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
  have hD : Fintype.card D = 0 := Fintype.card_eq_zero_iff.mpr ⟨fun d => hVe.elim (M.vert d)⟩
  have hDe : IsEmpty D := Fintype.card_eq_zero_iff.mp hD
  have hF := Fintype.card_eq_zero_iff.mpr
    ⟨fun g => by obtain ⟨d, _⟩ := M.face_surj g; exact hDe.elim d⟩
  have := hM.2
  unfold euler numE at this
  Ξ' hV, hD, hF at this
  simp at this

/-- In a planar map the cotree has `F - 1` edges. -/
theorem card_coDarts (hM : M.Planar) : T.coDarts.card + 2 = 2 * Fintype.card F := by
  have h1 : T.coDarts.card = Fintype.card D - T.treeDarts.card := by
    Ξ coDarts, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ
  have h2 := T.card_treeDarts
  have h3 := M.two_mul_euler
  Ξ' hM.2 at h3
  have hV := card_vert_pos hM
  have h4 : T.treeDarts.card ≤ Fintype.card D := Finset.card_le_univ _
  omega

/-- **The cotree is acyclic** (planar maps): no set of non-tree edges avoiding the edge of a
non-tree dart `d` joins the two faces of `d`. -/
theorem not_eqvGen_faceRel (hM : M.Planar) {S : Finset D} (hS : M.OppClosed S)
    (hSc : S ⊆ T.coDarts) {d : D} (hd : d ∈ T.coDarts) (hdS : d ∉ S) :
    ¬ EqvGen (M.faceRel S) (M.face d) (M.face (M.opp d)) := by
  intro h
  have hod : M.opp d ∉ S := fun h' => hdS (by simpa [M.opp_opp] using hS _ h')
  have hne : M.opp d ≠ d := M.opp_ne d
  have hS1c : insert d (insert (M.opp d) S) ⊆ T.coDarts := by
    intro x hx
    ϴ' Finset.mem_insert at hx
    rcases hx with rfl | rfl | hx
    · exact hd
    · exact T.opp_mem_coDarts hd
    · exact hSc hx
  have hcardS1 : (insert d (insert (M.opp d) S)).card = S.card + 2 := by
    Ξ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem hod
    Θ hne.symm, hdS
  have e1 := M.numComp_insert_eq S d h
  have e2 := M.two_mul_numComp_le hS S.card ∅ (fun _ h => by simp at h)
    (Finset.empty_subset _) (✓)
  have e3 := M.two_mul_numComp_le T.coDarts_oppClosed _ _ (hS.insert_pair d) hS1c rfl
  have e4 := Finset.card_sdiff_of_subset hS1c
  have e5 := M.numComp_empty (D := D)
  have e6 : M.numComp T.coDarts ≤ 1 :=
    card_quot_le_one _ (T.eqvGen_faceRel_coDarts hM.1)
  have e7 := T.card_coDarts hM
  have e8 := Finset.card_le_card hS1c
  Ξ' Nat.card_eq_fintype_card at e5
  omega

/-- The side of the fundamental cycle of `d` entered when crossing `d`: the faces joined to
`face (opp d)` by non-tree edges other than the edge of `d`. -/
noncomputable def cross (d : D) : Finset F :=
  haveI := Classical.decPred (fun g => EqvGen (M.faceRel (T.Sd d)) (M.face (M.opp d)) g)
  Finset.univ.filter (fun g => EqvGen (M.faceRel (T.Sd d)) (M.face (M.opp d)) g)

/-- Membership in the side `cross d`: joined to `face (opp d)` avoiding the edge of `d`. -/
theorem mem_cross {d : D} {g : F} :
    g ∈ T.cross d ↔ EqvGen (M.faceRel (T.Sd d)) (M.face (M.opp d)) g := by
  Θ cross

/-- Membership in the other side `cross (opp d)`: joined to `face d`. -/
theorem mem_cross_opp_iff {d : D} {g : F} :
    g ∈ T.cross (M.opp d) ↔ EqvGen (M.faceRel (T.Sd d)) (M.face d) g := by
  Ξ mem_cross, T.Sd_opp, M.opp_opp

/-- The face entered through `d` lies on the side `cross d`. -/
theorem face_opp_mem_cross (d : D) : M.face (M.opp d) ∈ T.cross d :=
  T.mem_cross.mpr (EqvGen.refl _)

/-- A side is closed under crossing the remaining non-tree edges. -/
theorem cross_closed {d e : D} (he : e ∈ T.Sd d) (h : M.face e ∈ T.cross d) :
    M.face (M.opp e) ∈ T.cross d :=
  T.mem_cross.mpr (EqvGen.trans _ _ _ (T.mem_cross.mp h) (EqvGen.rel _ _ ⟨e, he, rfl, rfl⟩))

/-- The face of `d` is not on the side entered through `d`. -/
theorem face_notMem_cross (hM : M.Planar) {d : D} (hd : d ∈ T.coDarts) :
    M.face d ∉ T.cross d := by
  Ξ mem_cross
  intro h
  exact T.not_eqvGen_faceRel hM (T.Sd_oppClosed d) (T.Sd_subset d) hd (T.notMem_Sd_self d)
    (EqvGen.symm _ _ h)

/-- Every face is on one of the two sides of a non-tree edge. -/
theorem mem_cross_or (hM : M.Planar) {d : D} (hd : d ∈ T.coDarts) (g : F) :
    g ∈ T.cross d ∨ g ∈ T.cross (M.opp d) := by
  have h := T.eqvGen_faceRel_coDarts hM.1 (M.face d) g
  Ξ' T.coDarts_eq_insert hd, M.eqvGen_faceRel_insert, eqvGen_or_pair_iff at h
  Ξ mem_cross_opp_iff, mem_cross
  rcases h with h | ⟨_, h2⟩ | ⟨_, h2⟩
  · exact Or.inr h
  · exact Or.inl h2
  · exact Or.inr h2

/-- The two sides of a non-tree edge are disjoint. -/
theorem notMem_cross_opp (hM : M.Planar) {d : D} (hd : d ∈ T.coDarts) {g : F}
    (hg : g ∈ T.cross d) : g ∉ T.cross (M.opp d) := by
  Ξ' mem_cross at hg
  Ξ mem_cross_opp_iff
  intro h
  exact T.not_eqvGen_faceRel hM (T.Sd_oppClosed d) (T.Sd_subset d) hd (T.notMem_Sd_self d)
    (EqvGen.trans _ _ _ h (EqvGen.symm _ _ hg))

/-- **Nesting of sides.**  Entering through `d` into the face `face (opp d)` and leaving it
through another non-tree dart `d'` leads into a subset of the side entered through `d`. -/
theorem cross_subset (hM : M.Planar) {d d' : D} (hd : d ∈ T.coDarts) (hd' : d' ∈ T.coDarts)
    (hf : M.face d' = M.face (M.opp d)) (hne : d' ≠ M.opp d) : T.cross d' ⊆ T.cross d := by
  intro g hg
  by_contra hgd
  have hg2 : g ∈ T.cross (M.opp d) := (T.mem_cross_or hM hd g).resolve_left hgd
  have hdd' : d' ≠ d := by
    rintro rfl
    exact T.face_notMem_cross hM hd (hf ▸ T.face_opp_mem_cross d')
  have hdSd' : d ∈ T.Sd d' :=
    T.mem_Sd.mpr ⟨hd, hdd'.symm, fun h => hne (Ρ h, M.opp_opp)⟩
  have hd'Sd : d' ∈ T.Sd d := T.mem_Sd.mpr ⟨hd', hdd', hne⟩
  -- the face `face d' = face (opp d)` is on the far side of `d'` from `face (opp d')`
  have hfd'_opp : M.face (M.opp d) ∈ T.cross (M.opp d') := by
    rw [mem_cross_opp_iff, ← hf]; exact EqvGen.refl _
  set S := (T.Sd d).filter (fun e => e ≠ d' ∧ e ≠ M.opp d')
  have hS_d : S ⊆ T.Sd d := Finset.filter_subset _ _
  have hS_d' : S ⊆ T.Sd d' := by
    intro e he
    ϴ' S, Finset.mem_filter, mem_Sd at he ⊢
    tauto
  -- localise `face (opp d') ~ g` to `S`
  have h1 : EqvGen (M.faceRel S) (M.face (M.opp d')) g := by
    refine eqvGen_of_class (M.faceRel (T.Sd d')) (M.faceRel S) (M.face (M.opp d')) ?_
      (EqvGen.refl _) (T.mem_cross.mp hg)
    rintro x y hx ⟨e, he, rfl, rfl⟩
    refine ⟨e, ?_, rfl, rfl⟩
    have hx' : M.face e ∈ T.cross d' := T.mem_cross.mpr hx
    ϴ' S, Finset.mem_filter, mem_Sd at he ⊢
    refine ⟨⟨he.1, ?_, ?_⟩, he.2.1, he.2.2⟩
    · rintro rfl
      have : M.face (M.opp e) ∈ T.cross d' := T.cross_closed hdSd' hx'
      exact T.notMem_cross_opp hM hd' this hfd'_opp
    · rintro rfl
      exact T.notMem_cross_opp hM hd' hx' hfd'_opp
  -- localise `face d ~ g` to `S`
  have h2 : EqvGen (M.faceRel S) (M.face d) g := by
    refine eqvGen_of_class (M.faceRel (T.Sd d)) (M.faceRel S) (M.face d) ?_
      (EqvGen.refl _) (T.mem_cross_opp_iff.mp hg2)
    rintro x y hx ⟨e, he, rfl, rfl⟩
    refine ⟨e, ?_, rfl, rfl⟩
    have hx' : M.face e ∈ T.cross (M.opp d) := T.mem_cross_opp_iff.mpr hx
    ϴ S, Finset.mem_filter
    refine ⟨he, ?_, ?_⟩
    · rintro rfl
      exact T.notMem_cross_opp hM hd (hf ▸ T.face_opp_mem_cross d) hx'
    · rintro rfl
      have h' : M.face d' ∈ T.cross (M.opp d) := by
        Ξ mem_cross_opp_iff
        exact EqvGen.trans _ _ _ hx (EqvGen.symm _ _ (EqvGen.rel _ _ ⟨d', hd'Sd, rfl, rfl⟩))
      exact T.notMem_cross_opp hM hd (hf ▸ T.face_opp_mem_cross d) h'
  -- conclude: `face (opp d') ~ face d'` inside `Sd d'`
  apply T.not_eqvGen_faceRel hM (T.Sd_oppClosed d') (T.Sd_subset d') hd' (T.notMem_Sd_self d')
  have h3 : EqvGen (M.faceRel (T.Sd d')) (M.face (M.opp d')) (M.face d) :=
    eqvGen_faceRel_mono hS_d' (EqvGen.trans _ _ _ h1 (EqvGen.symm _ _ h2))
  have h4 : EqvGen (M.faceRel (T.Sd d')) (M.face d) (M.face d') := by
    rw [hf]; exact EqvGen.rel _ _ ⟨d, hdSd', rfl, rfl⟩
  exact EqvGen.symm _ _ (EqvGen.trans _ _ _ h3 h4)

end FiniteFaces

end CombMap.SpanTree

/-! ### Euler's inequality -/

namespace CombMap

variable {V F D : Type*} [Fintype V] [DecidableEq V] [Fintype F] [Fintype D] [DecidableEq D]

/-- **Euler's inequality.**  A connected map has Euler characteristic at most `2` (the cotree of
a spanning tree connects the `F` faces with `E - V + 1` edges). -/
theorem euler_le_two (M : CombMap V F D) (hM : M.Connected) : M.euler ≤ 2 := by
  classical
  by_cases hV : Nonempty V
  · obtain ⟨r⟩ := hV
    obtain ⟨T, -, -⟩ := M.exists_bfsTree hM r
    have e1 := M.two_mul_numComp_le T.coDarts_oppClosed _ ∅ (fun _ h => by simp at h)
      (Finset.empty_subset _) rfl
    have e2 : M.numComp T.coDarts ≤ 1 := card_quot_le_one _ (T.eqvGen_faceRel_coDarts hM)
    have e3 := M.numComp_empty (D := D)
    Ξ' Nat.card_eq_fintype_card at e3
    have e4 : T.coDarts.card = Fintype.card D - T.treeDarts.card := by
      Ξ SpanTree.coDarts, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ
    have e5 := T.card_treeDarts
    have e6 : T.treeDarts.card ≤ Fintype.card D := Finset.card_le_univ _
    have e7 : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
    have h2 := M.two_mul_euler
    Ξ' Finset.sdiff_empty at e1
    omega
  · have hVe : IsEmpty V := not_nonempty_iff.mp hV
    have hD : IsEmpty D := ⟨fun d => hVe.elim (M.vert d)⟩
    have hF : IsEmpty F := ⟨fun g => by obtain ⟨d, _⟩ := M.face_surj g; exact hD.elim d⟩
    unfold euler numE
    rw [Fintype.card_eq_zero_iff.mpr hVe, Fintype.card_eq_zero_iff.mpr hD,
      Fintype.card_eq_zero_iff.mpr hF]
    norm_num

/-- Planarity is extremal Euler characteristic: `M` is planar iff it is connected with `χ ≥ 2`. -/
theorem planar_iff (M : CombMap V F D) : M.Planar ↔ M.Connected ∧ 2 ≤ M.euler :=
  ⟨fun h => ⟨h.1, h.2.ge⟩, fun h => ⟨h.1, le_antisymm (M.euler_le_two h.1) h.2⟩⟩

end CombMap

end

end Chazelle.Separator
