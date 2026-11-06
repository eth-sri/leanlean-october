import Mathlib.Tactic

import RequestProject.OrderComplexHtpyIn

/-!
# A retraction on path classes across one gluing step

Let a subposet `U` of an ambient poset be covered by two subposets `A` and `B` such that no
comparability inside `U` is mixed, and let `J = A ∩ B` be nonempty, connected and simply
connected.  Then the inclusion of `A` into `U` is injective on path classes: a loop inside `A`
which is null-homotopic inside `U` is already null-homotopic inside `A`.

Nothing is assumed about the fundamental group of `B`.  The proof is the explicit van Kampen
retraction, written directly on edge paths:

* choose a vertex `j0` of `J` and, for every vertex `v` of `J`, a path `γ v : j0 → v` inside
  `J` (`γ v = []` for the vertices that are not in `J`);
* `FiniteChains.Comb.retrVert` sends a vertex to itself if it lies in `A` and to `j0`
  otherwise;
* `FiniteChains.Comb.retrGerm` sends an oriented edge of `A` to itself and any other oriented
  edge `u → v` to `γ u ⁻¹ γ v`;
* `FiniteChains.Comb.retrPath` applies this edgewise.

The two formulas agree, up to homotopy inside `A`, on the edges of `J`: this is exactly where
the simple connectedness of `J` is used (`FiniteChains.Comb.htpyIn_retrGerm_of_pathIn_B`).  The
elementary cancellations are then preserved (`FiniteChains.Comb.htpyIn_retrPath_of_stepIn`):
backtracks cancel, a two-cell of `A` is unchanged, and for a two-cell of `B` the chosen paths
telescope around its boundary.  Since a path inside `A` is returned unchanged, the assignment is
a retraction on path classes, which is the statement
`FiniteChains.Comb.injIn_union_of_unmixed`.

The initial step of a chamber filtration is handled by
`FiniteChains.Comb.injIn_of_monotone_retraction`: a monotone retraction of a subposet onto a
smaller one is also injective on path classes.

Finally, `FiniteChains.Comb.injIn_of_directed` passes from the members of an increasing
exhaustion to the whole complex: a null-homotopy is a finite derivation, so it only involves
finitely many cells and therefore stays inside one member of the exhaustion.
-/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb



variable {P Q : Type u} [Preorder P] [Preorder Q]

/-! ### Injectivity on path classes -/

/-- **`B` is injective on path classes inside `U`**: a loop inside `B` that is null-homotopic
inside `U` is null-homotopic inside `B`. -/
def InjIn (U B : P → Prop)  :=
  ∀ (v : P) (l : List ((orderCx P).E × Bool)), B v →
    IsPath (orderCx P).src (orderCx P).tgt l v v → PathIn B l →
    HtpyIn U v v l [] → HtpyIn B v v l []

/-- Every loop inside `J` is null-homotopic inside `J`. -/
def SimplyConnectedIn (J : P → Prop)  :=
  ∀ (v : P) (l : List ((orderCx P).E × Bool)), J v →
    IsPath (orderCx P).src (orderCx P).tgt l v v → PathIn J l → HtpyIn J v v l []



/-- Both endpoints of an oriented edge with endpoints in `C` lie in `C`. -/
theorem germ_ends {C : P → Prop} {eb : (orderCx P).E × Bool} (h : C eb.1.1.1 ∧ C eb.1.1.2) :
    C (germSrc (orderCx P).src (orderCx P).tgt eb) ∧
      C (germTgt (orderCx P).src (orderCx P).tgt eb) := by
  obtain ⟨e, tag⟩ := eb
  cases tag
  · exact ⟨h.2, h.1⟩
  · exact ⟨h.1, h.2⟩

/-- Injectivity on path classes only depends on the ambient subposet up to equivalence. -/
abbrev injIn_congr_left {U U' B : P → Prop} (h : ∀ x, U x ↔ U' x) (hinj : InjIn U B)  :=
  fun v l hv hp hl hh => hinj v l hv hp hl (HtpyIn.mono (fun x hx => (h x).2 hx) hh)

/-- Injectivity on path classes composes. -/
theorem injIn_trans {U A B : P → Prop} (hBA : ∀ x, B x → A x)
    (hUA : InjIn U A) (hAB : InjIn A B) : InjIn U B := by
  classical grind [FiniteChains.Comb.InjIn, pathIn_mono]

/-- Simple connectedness of a subposet, in the form produced by the order-complex results of the
project. -/
theorem simplyConnectedIn_of_simplyConnected {J : P → Prop}
    (hJ : SimplyConnected (orderCx {x : P // J x})) : SimplyConnectedIn J := by
  intro v l hv hp hl
  have hlift := isPath_liftPathIn l hl hv hv hp
  have hnull := hJ ⟨v, hv⟩ (liftPathIn l hl) hlift
  have h := htpyIn_mapPath (C := J) (fun x : {x : P // J x} => (x : P)) monotone_subtypeVal
    (fun x => x.2) hnull
  rw [show mapPath (orderCxMap (fun x : {x : P // J x} => (x : P)) monotone_subtypeVal)
      (liftPathIn l hl) = l from mapPath_liftPathIn l hl] at h
  simpa [mapPath] using h

/-! ### The retraction on paths -/

section

variable (A : P → Prop) (j0 : P) (γ : P → List ((orderCx P).E × Bool))

open Classical in
/-- The retraction on vertices: a vertex of `A` stays where it is, any other vertex goes to the
base vertex `j0` of the intersection. -/
noncomputable def retrVert (u : P)  := if A u then u else j0

variable (eb : (orderCx P).E × Bool)
open Classical in
/-- The retraction on oriented edges: an edge of `A` is unchanged, any other edge `u → v` is
replaced by `γ u ⁻¹ γ v`. -/
noncomputable def retrGerm   :=
  if A eb.1.1.1 ∧ A eb.1.1.2 then [eb]
  else revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++
    γ (germTgt (orderCx P).src (orderCx P).tgt eb)

/-- The retraction on edge paths. -/
noncomputable def retrPath : List ((orderCx P).E × Bool) → List ((orderCx P).E × Bool)
  | [] => []
  | eb :: t => retrGerm A γ eb ++ retrPath t

variable {A j0 γ}

@[simp] theorem retrPath_nil : retrPath A γ [] = [] := rfl

@[simp] theorem retrPath_cons  (t : List ((orderCx P).E × Bool)) :
    retrPath A γ (eb :: t) = retrGerm A γ eb ++ retrPath A γ t := rfl

theorem retrPath_append (l l' : List ((orderCx P).E × Bool)) :
    retrPath A γ (l ++ l') = retrPath A γ l ++ retrPath A γ l' := by
  induction l <;> simp_all 

section
omit [Preorder P]
theorem retrVert_of_mem {u : P} (hu : A u) : retrVert A j0 u = u := by
  simp [retrVert, hu]

theorem retrVert_of_not_mem {u : P} (hu : ¬ A u) : retrVert A j0 u = j0 := by
  simp [retrVert, hu]
end

variable {eb : (orderCx P).E × Bool}
theorem retrGerm_of_mem  (h : A eb.1.1.1 ∧ A eb.1.1.2) :
    retrGerm A γ eb = [eb] := by
  simp [retrGerm, h]

theorem retrGerm_of_not_mem  (h : ¬ (A eb.1.1.1 ∧ A eb.1.1.2)) :
    retrGerm A γ eb = revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++
      γ (germTgt (orderCx P).src (orderCx P).tgt eb) := by
  simp [retrGerm, h]

/-- Reversing an edge reverses its retracted path. -/
theorem retrGerm_revGerm  :
    retrGerm A γ (revGerm eb) = revPath (retrGerm A γ eb) := by
  classical
  rcases eb with ⟨e, b⟩
  cases b <;> by_cases h : A e.1.1 ∧ A e.1.2 <;>
    simp [retrGerm, revGerm, germSrc, germTgt, h, revPath_append]

/-- A path inside `A` is returned unchanged. -/
theorem retrPath_eq_self {l : List ((orderCx P).E × Bool)} (hl : PathIn A l) :
    retrPath A γ l = l := by
  induction l with
  | nil => rfl
  | cons eb t ih =>
      classical grind [FiniteChains.Comb.pathIn_of_cons, FiniteChains.Comb.retrPath_cons, FiniteChains.Comb.retrGerm_of_mem, List.singleton_append]

/-- The retraction lands inside `A`. -/
theorem pathIn_retrPath (hγA : ∀ u : P, PathIn A (γ u)) (l : List ((orderCx P).E × Bool)) :
    PathIn A (retrPath A γ l) := by
  classical
  induction l with
  | nil => exact pathIn_nil A
  | cons eb t ih =>
      refine pathIn_append ?_ ih
      by_cases h : A eb.1.1.1 ∧ A eb.1.1.2
      · classical simp_all [FiniteChains.Comb.retrGerm_of_mem, FiniteChains.Comb.pathIn_cons, FiniteChains.Comb.pathIn_nil]
      · classical simp_all [FiniteChains.Comb.retrGerm_of_not_mem, FiniteChains.Comb.pathIn_append, FiniteChains.Comb.pathIn_revPath]

end

/-! ### The gluing step -/

section

variable {A B U J : P → Prop} {j0 : P} {γ : P → List ((orderCx P).E × Bool)}

variable (hJA : ∀ x, J x → A x) (hJmk : ∀ x, A x → B x → J x)
  (hγpath : ∀ u : P, J u → IsPath (orderCx P).src (orderCx P).tgt (γ u) j0 u)
  (hγin : ∀ u : P, PathIn J (γ u)) (hγnil : ∀ u : P, ¬ J u → γ u = [])

include hJA hγin in
abbrev pathIn_gamma_of_subset (u : P)  :=
  FiniteChains.Comb.pathIn_mono hJA (hγin u)

include hJA hJmk hγpath hγnil in
/-- The chosen path from the base vertex to the image of a vertex of `B`. -/
theorem isPath_gamma {u : P} (hu : B u) :
    IsPath (orderCx P).src (orderCx P).tgt (γ u) j0 (retrVert A j0 u) := by
  by_cases hA : A u
  · simp_all [retrVert_of_mem]
  · rw [retrVert_of_not_mem hA, hγnil u (fun h => hA (hJA u h))]
    rfl

variable (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
include hmix in
include hJA hJmk hγpath hγnil in
/-- The image of an oriented edge is a path between the images of its endpoints. -/
theorem isPath_retrGerm 
    {eb : (orderCx P).E × Bool} (h1 : U eb.1.1.1) (h2 : U eb.1.1.2) :
    IsPath (orderCx P).src (orderCx P).tgt (retrGerm A γ eb)
      (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
      (retrVert A j0 (germTgt (orderCx P).src (orderCx P).tgt eb)) := by
  by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
  · rw [retrGerm_of_mem hA]
    have hAs := germ_ends hA
    rw [retrVert_of_mem hAs.1, retrVert_of_mem hAs.2]
    exact isPath_single _
  · rw [retrGerm_of_not_mem hA]
    have hB : B eb.1.1.1 ∧ B eb.1.1.2 := by
      grind
    have hBs := germ_ends hB
    refine isPath_append_iff.mpr ⟨j0, ?_, isPath_gamma hJA hJmk hγpath hγnil hBs.2⟩
    exact isPath_revPath (isPath_gamma hJA hJmk hγpath hγnil hBs.1)

include hmix in
include hJA hJmk hγpath hγnil in
/-- The image of a path is a path between the images of its endpoints. -/
theorem isPath_retrPath  :
    ∀ (l : List ((orderCx P).E × Bool)) {a b : P},
      IsPath (orderCx P).src (orderCx P).tgt l a b → PathIn U l →
      IsPath (orderCx P).src (orderCx P).tgt (retrPath A γ l) (retrVert A j0 a)
        (retrVert A j0 b) := by
  intro l
  induction l with
  | nil =>
      intro a b hp _
      have  := hp
      subst this
      rfl
  | cons eb t ih =>
      intro a b hp hU
      obtain ⟨ha, hrest⟩ := hp
      subst ha
      obtain ⟨hUe, hUt⟩ := pathIn_of_cons hU
      refine isPath_append_iff.mpr
        ⟨retrVert A j0 (germTgt (orderCx P).src (orderCx P).tgt eb), ?_, ih hrest hUt⟩
      exact isPath_retrGerm hJA hJmk hγpath hγnil hmix hUe.1 hUe.2

variable (hJsc : SimplyConnectedIn J)
include hJsc in
include hJA hJmk hγpath hγin in
/-- **On the edges of `J` the two formulas agree.**  This is the only place where the simple
connectedness of the intersection is used. -/
theorem htpyIn_retrGerm_of_pathIn_B  (hj0 : J j0)
    {eb : (orderCx P).E × Bool} (hB : B eb.1.1.1 ∧ B eb.1.1.2) :
    HtpyIn A (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
      (retrVert A j0 (germTgt (orderCx P).src (orderCx P).tgt eb))
      (retrGerm A γ eb)
      (revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++
        γ (germTgt (orderCx P).src (orderCx P).tgt eb)) := by
  classical
  by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
  · -- the edge lies in `J`
    set s : P := germSrc (orderCx P).src (orderCx P).tgt eb with hs
    set t : P := germTgt (orderCx P).src (orderCx P).tgt eb with ht
    have hAs  := germ_ends hA
    have hBs  := germ_ends hB
    have hJs  := hJmk s hAs.1 hBs.1
    have hJt  := hJmk t hAs.2 hBs.2
    have hγs  := hγpath s hJs
    have hγt  := hγpath t hJt
    have hγsA  := pathIn_gamma_of_subset hJA hγin s
    have hγtA  := pathIn_gamma_of_subset hJA hγin t
    have hebPath : IsPath (orderCx P).src (orderCx P).tgt [eb] s t := isPath_single eb
    have hebA  := pathIn_cons hA (pathIn_nil A)
    -- the loop `γ s · eb · γ t ⁻¹` lies in `J` and is therefore null-homotopic inside `J`
    have hloopPath : IsPath (orderCx P).src (orderCx P).tgt
        (γ s ++ ([eb] ++ revPath (γ t))) j0 j0 :=
      isPath_append_iff.mpr ⟨s, hγs,
        isPath_append_iff.mpr ⟨t, hebPath, isPath_revPath hγt⟩⟩
    have hebJ : J eb.1.1.1 ∧ J eb.1.1.2 :=
      ⟨hJmk _ hA.1 hB.1, hJmk _ hA.2 hB.2⟩
    have hloopIn  :=
      pathIn_append (hγin s)
        (pathIn_append (pathIn_cons hebJ (pathIn_nil J)) (pathIn_revPath (hγin t)))
    have hnull  :=
      HtpyIn.mono hJA (hJsc j0 _ hj0 hloopPath hloopIn)
    -- conjugate the null-homotopy by `γ s ⁻¹` and `γ t`
    have hconj  :=
      hnull.congr_append (isPath_revPath hγs) hγt (pathIn_revPath hγsA) hγtA
    -- the left-hand side is homotopic to `eb`
    have hcancel1  := htpyIn_revPath_append hγs hγsA
    have hcancel2  := htpyIn_revPath_append hγt hγtA
    have hstep1  :=
      HtpyIn.append_congr hebPath
        (isPath_append_iff.mpr ⟨j0, isPath_revPath hγt, hγt⟩) hebA
        (pathIn_append (pathIn_revPath hγtA) hγtA) (HtpyIn.refl _) hcancel2
    have hstep2  :=
      HtpyIn.append_congr (isPath_append_iff.mpr ⟨j0, isPath_revPath hγs, hγs⟩)
        (isPath_append_iff.mpr ⟨t, hebPath, isPath_append_iff.mpr ⟨j0, isPath_revPath hγt, hγt⟩⟩)
        (pathIn_append (pathIn_revPath hγsA) hγsA)
        (pathIn_append hebA (pathIn_append (pathIn_revPath hγtA) hγtA))
        hcancel1 (HtpyIn.refl _)
    have hmain : HtpyIn A s t [eb] (revPath (γ s) ++ γ t) := by
      grind [FiniteChains.Comb.HtpyIn.trans, FiniteChains.Comb.HtpyIn.symm]
    rw [retrGerm_of_mem hA, retrVert_of_mem hAs.1, retrVert_of_mem hAs.2]
    exact hmain
  · classical simp_all [FiniteChains.Comb.retrGerm_of_not_mem, FiniteChains.Comb.HtpyIn.refl]

include hJsc in
include hJA hJmk hγpath hγin hγnil in
/-- **Telescoping along a path of `B`.**  The image of a path of `B` from `u` to `v` is
homotopic, inside `A`, to `γ u ⁻¹ γ v`. -/
theorem htpyIn_retrPath_of_pathIn_B  (hj0 : J j0) :
    ∀ (l : List ((orderCx P).E × Bool)) {u v : P},
      IsPath (orderCx P).src (orderCx P).tgt l u v → PathIn B l → B u → B v →
      HtpyIn A (retrVert A j0 u) (retrVert A j0 v) (retrPath A γ l)
        (revPath (γ u) ++ γ v) := by
  intro l
  induction l with
  | nil =>
      intro u v hp _ hu _
      have huv  := hp
      subst huv
      have hγu  :=
        isPath_gamma hJA hJmk hγpath hγnil hu
      have hγuA  := pathIn_gamma_of_subset hJA hγin u
      exact (htpyIn_revPath_append hγu hγuA).symm
  | cons eb t ih =>
      intro u v hp hBl hu hv
      obtain ⟨ha, hrest⟩ := hp
      subst ha
      obtain ⟨hBe, hBt⟩ := pathIn_of_cons hBl
      set m : P := germTgt (orderCx P).src (orderCx P).tgt eb with hm
      have hBm  := (germ_ends hBe).2
      have hγu  :=
        isPath_gamma hJA hJmk hγpath hγnil hu
      have hγm  :=
        isPath_gamma hJA hJmk hγpath hγnil hBm
      have hγv  :=
        isPath_gamma hJA hJmk hγpath hγnil hv
      have hγuA : PathIn A (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) :=
        pathIn_gamma_of_subset hJA hγin _
      have hγmA  := pathIn_gamma_of_subset hJA hγin m
      have hγvA  := pathIn_gamma_of_subset hJA hγin v
      have hgerm := htpyIn_retrGerm_of_pathIn_B (A := A) (γ := γ) hJA hJmk hγpath hγin hJsc hj0 hBe
      have hih := ih hrest hBt hBm hv
      have hfirst : IsPath (orderCx P).src (orderCx P).tgt (retrGerm A γ eb)
          (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb)) (retrVert A j0 m) := by
        refine HtpyIn.isPath hgerm.symm ?_
        exact isPath_append_iff.mpr ⟨j0, isPath_revPath hγu, hγm⟩
      have hsecond  :=
        HtpyIn.isPath hih.symm (isPath_append_iff.mpr ⟨j0, isPath_revPath hγm, hγv⟩)
      have hfirstA : PathIn A (retrGerm A γ eb) := by
        classical
        by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
        · classical grind [FiniteChains.Comb.retrGerm_of_mem, FiniteChains.Comb.pathIn_cons, FiniteChains.Comb.pathIn_nil]
        · classical simp_all [FiniteChains.Comb.retrGerm_of_not_mem, FiniteChains.Comb.pathIn_append, FiniteChains.Comb.pathIn_revPath]
      have hsecondA  :=
        pathIn_retrPath (fun x => pathIn_gamma_of_subset hJA hγin x) t
      have hcomb  :=
        HtpyIn.append_congr hfirst hsecond hfirstA hsecondA hgerm hih
      refine hcomb.trans ?_
      -- cancel `γ m ⁻¹ γ m` in the middle
      have hcancel  :=
        htpyIn_append_revPath hγm hγmA
      have hmid  :=
        hcancel.congr_append (isPath_revPath hγu) hγv (pathIn_revPath hγuA) hγvA
      simp_all

include hJsc in
include hmix in
include hJA hJmk hγpath hγin hγnil in
/-- **The retraction respects one elementary cancellation.** -/
theorem htpyIn_retrPath_of_stepIn
    
     (hj0 : J j0) {a b : P}
    {l l' : List ((orderCx P).E × Bool)} (h : StepIn U a b l l') :
    HtpyIn A (retrVert A j0 a) (retrVert A j0 b) (retrPath A γ l) (retrPath A γ l') := by
  classical
  obtain ⟨⟨hpl, hpl', hc⟩, hUl, hUl'⟩ := h
  have hγA  := fun x => pathIn_gamma_of_subset hJA hγin x
  rcases hc with ⟨p', q', eb, hlEq, hl'Eq⟩ | ⟨p', q', t, hlEq, hl'Eq⟩
  · -- a backtrack
    subst hlEq
    subst hl'Eq
    have hUp'  := pathIn_of_append_left hUl
    have hUrest  := pathIn_of_append_right hUl
    obtain ⟨hUe, hUrest'⟩ := pathIn_of_cons hUrest
    have hUq'  := (pathIn_of_cons hUrest').2
    -- endpoints of the pieces
    obtain ⟨c, hpc, hrest⟩ := isPath_append_iff.mp hpl
    obtain ⟨hcs, hrest2⟩ := hrest
    obtain ⟨hmid, hq'⟩ := hrest2
    have hPp'  :=
      isPath_retrPath hJA hJmk hγpath hγnil hmix p' hpc hUp'
    have hcq  := hq'
    have hPq'  :=
      isPath_retrPath hJA hJmk hγpath hγnil hmix q' hcq hUq'
    have hrevTgt  := germTgt_revGerm (X := orderCx P) eb
    -- the two images cancel
    have hkey : HtpyIn A (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
        (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
        (retrGerm A γ eb ++ retrGerm A γ (revGerm eb)) [] := by
      rw [retrGerm_revGerm]
      exact htpyIn_append_revPath
        (isPath_retrGerm hJA hJmk hγpath hγnil hmix hUe.1 hUe.2)
        (by simpa [retrPath] using pathIn_retrPath hγA [eb])
    have hcs'  := hcs
    subst hcs'
    have hglue : HtpyIn A (retrVert A j0 a) (retrVert A j0 b)
        (retrPath A γ p' ++ (retrGerm A γ eb ++ retrGerm A γ (revGerm eb)) ++ retrPath A γ q')
        (retrPath A γ p' ++ [] ++ retrPath A γ q') := by
      refine hkey.congr_append hPp' ?_ (pathIn_retrPath hγA p') (pathIn_retrPath hγA q')
      rw [hrevTgt] at hPq'
      exact hPq'
    simp_all [retrPath_append]
  · -- a two-cell
    subst hlEq
    subst hl'Eq
    have hfront  := pathIn_of_append_left hUl
    have hUp'  := pathIn_of_append_left hfront
    have hUatt  := pathIn_of_append_right hfront
    have hUq'  := pathIn_of_append_right hUl
    obtain ⟨c, hfrontPath, hq'⟩ := isPath_append_iff.mp hpl
    obtain ⟨d, hpc, hatt⟩ := isPath_append_iff.mp hfrontPath
    have hbase  := hatt.1
    have hbase' : c = t.1.1 := by
      obtain ⟨-, h2⟩ := hatt
      obtain ⟨-, h2'⟩ := h2
      obtain ⟨-, h3⟩ := h2'
      exact h3.symm
    subst hbase
    subst hbase'
    have hPp'  :=
      isPath_retrPath hJA hJmk hγpath hγnil hmix p' hpc hUp'
    have hPq'  :=
      isPath_retrPath hJA hJmk hγpath hγnil hmix q' hq' hUq'
    have hv1 := hUatt ((⟨(t.1.1, t.1.2.1), t.2.1⟩ : OrdEdge P), true) (by simp [orderCx])
    have hv2 := hUatt ((⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : OrdEdge P), true) (by simp [orderCx])
    have hUx  := hv1.1
    have hUy  := hv1.2
    have hUz  := hv2.2
    have hkey : HtpyIn A (retrVert A j0 t.1.1) (retrVert A j0 t.1.1)
        (retrPath A γ ((orderCx P).att t)) [] := by
      by_cases hallA : A t.1.1 ∧ A t.1.2.1 ∧ A t.1.2.2
      · -- the two-cell lies in `A`
        have hattA : PathIn A ((orderCx P).att t) := by
          grind [FiniteChains.Comb.PathIn, orderCx]
        rw [retrPath_eq_self hattA, retrVert_of_mem hallA.1]
        refine HtpyIn.of_step ⟨⟨(orderCx P).att_isLoop t, rfl,
          Or.inr ⟨[], [], t, by simp, rfl⟩⟩, hattA, pathIn_nil A⟩
      · -- the two-cell lies in `B`
        have hallB : B t.1.1 ∧ B t.1.2.1 ∧ B t.1.2.2 := by
          grind
        have hattB : PathIn B ((orderCx P).att t) := by
          grind [PathIn, orderCx]
        have htel := htpyIn_retrPath_of_pathIn_B (A := A) (γ := γ) hJA hJmk hγpath hγin hγnil hJsc hj0 ((orderCx P).att t) ((orderCx P).att_isLoop t) hattB hallB.1 hallB.1
        refine htel.trans ?_
        have hγx  := isPath_gamma hJA hJmk hγpath hγnil hallB.1
        exact htpyIn_revPath_append hγx (hγA t.1.1)
    have hglue  :=
      hkey.congr_append hPp' hPq' (pathIn_retrPath hγA p') (pathIn_retrPath hγA q')
    rw [retrPath_append, retrPath_append, retrPath_append]
    simpa using hglue

include hJsc in
include hmix in
include hJA hJmk hγpath hγin hγnil in
/-- The retraction respects homotopies inside `U`. -/
theorem htpyIn_retrPath_of_htpyIn
    
     (hj0 : J j0) {a b : P}
    {p q : List ((orderCx P).E × Bool)} (h : HtpyIn U a b p q) :
    HtpyIn A (retrVert A j0 a) (retrVert A j0 b) (retrPath A γ p) (retrPath A γ q) := by
  induction h with
  | refl => exact HtpyIn.refl _
  | tail _ hstep ih =>
      refine ih.trans ?_
      rcases hstep with hs | hs
      · exact htpyIn_retrPath_of_stepIn hJA hJmk hγpath hγin hγnil hmix hJsc hj0 hs
      · exact (htpyIn_retrPath_of_stepIn hJA hJmk hγpath hγin hγnil hmix hJsc hj0 hs).symm

end

/-- **The gluing step for injectivity on path classes.**  If `U = A ∪ B`, no comparability inside
`U` is mixed, and the intersection `J = A ∩ B` is nonempty, connected and simply connected, then
a loop inside `A` which is null-homotopic inside `U` is null-homotopic inside `A`.  Nothing is
assumed about `B`. -/
theorem injIn_union_of_unmixed {A B U J : P → Prop}
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hJdef : ∀ x, J x ↔ (A x ∧ B x))
    (hJconn : ConnectedIn J) (hJsc : SimplyConnectedIn J)
    {j0 : P} (hj0 : J j0) :
    InjIn U A := by
  classical
  have hJA  := fun x h => ((hJdef x).1 h).1
  have hJmk  := fun x h h' => (hJdef x).2 ⟨h, h'⟩
  -- choose the paths `γ`
  have hex : ∀ u : P, ∃ g : List ((orderCx P).E × Bool),
      (J u → IsPath (orderCx P).src (orderCx P).tgt g j0 u) ∧ PathIn J g ∧ (¬ J u → g = []) := by
    intro u
    by_cases hu : J u
    · aesop
    · classical aesop (add unsafe apply [FiniteChains.Comb.pathIn_nil, rfl])
  choose γ hγpath hγin hγnil using hex
  intro v l hv hp hl hnull
  have h := htpyIn_retrPath_of_htpyIn (A := A) (B := B) (J := J) (γ := γ) hJA hJmk
    hγpath hγin hγnil hmix hJsc hj0 hnull
  rw [retrPath_eq_self hl, retrVert_of_mem hv] at h
  simpa only [retrPath_nil (P := P)] using h

/-! ### The initial step: a monotone retraction -/

/-- A monotone map that fixes the vertices of `B` returns a path of `B` unchanged. -/
theorem mapPath_liftPathIn_of_fix {C B : P → Prop} (f : {x : P // C x} → P) (hf : Monotone f)
    (hfix : ∀ z : {x : P // C x}, B z.1 → f z = z.1) :
    ∀ (l : List ((orderCx P).E × Bool)) (hl : PathIn C l), PathIn B l →
      mapPath (orderCxMap f hf) (liftPathIn l hl) = l
  | [], _, _ => rfl
  | e :: t, hl, hB => by
      have hrest  :=
        mapPath_liftPathIn_of_fix f hf hfix t (pathIn_of_cons hl).2 (pathIn_of_cons hB).2
      obtain ⟨he1, he2⟩ := (pathIn_of_cons hB).1
      obtain ⟨hc1, hc2⟩ := (pathIn_of_cons hl).1
      simp only [liftPathIn, mapPath, List.map_cons, List.cons.injEq]
      constructor
      · classical apply_rules [Prod.ext, rfl, Subtype.ext]
      · exact hrest

/-- **A monotone retraction is injective on path classes.**  If the subposet `C` retracts
monotonically onto a smaller subposet `B`, fixing `B` pointwise, then a loop inside `B` that is
null-homotopic inside `C` is null-homotopic inside `B`. -/
theorem injIn_of_monotone_retraction {C B : P → Prop} (hBC : ∀ x, B x → C x)
    (f : {x : P // C x} → P) (hf : Monotone f) (hfB : ∀ z, B (f z))
    (hfix : ∀ z : {x : P // C x}, B z.1 → f z = z.1) :
    InjIn C B := by
  intro v l hv hp hl hnull
  have hvC  := hBC v hv
  have hlC  := pathIn_mono hBC hl
  have hlift  :=
    htpy_lift_of_htpyIn hnull hvC hvC hlC (pathIn_nil C)
  have hpush := htpyIn_mapPath (C := B) f hf hfB hlift
  grind [mapPath_liftPathIn_of_fix, mapPath, liftPathIn]

/-! ### Passing to an increasing exhaustion -/

/-- **Finiteness of null-homotopies.**  A homotopy of the ambient complex only uses finitely many
cells, so it takes place inside one member of an increasing exhaustion. -/
theorem exists_htpyIn_of_htpy {D : ℕ → P → Prop} (hmono : ∀ m n, m ≤ n → ∀ x, D m x → D n x)
    (hcov : ∀ x : P, ∃ n, D n x) {a b : P} {p q : List ((orderCx P).E × Bool)}
    (h : Htpy (orderCx P) a b p q) : ∃ n, HtpyIn (D n) a b p q := by
  have hpath : ∀ l : List ((orderCx P).E × Bool), ∃ n, PathIn (D n) l := by
    intro l
    induction l with
    | nil => exact ⟨0, pathIn_nil _⟩
    | cons e t ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨n1, hn1⟩ := hcov e.1.1.1
        obtain ⟨n2, hn2⟩ := hcov e.1.1.2
        refine ⟨max n (max n1 n2), pathIn_cons ⟨?_, ?_⟩ ?_⟩
        · aesop
        · aesop
        · grind [FiniteChains.Comb.PathIn]
  induction h with
  | refl => exact ⟨0, Relation.ReflTransGen.refl⟩
  | @tail u v _ hstep ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m1, hm1⟩ := hpath u
      obtain ⟨m2, hm2⟩ := hpath v
      refine ⟨max n (max m1 m2), ?_⟩
      refine (HtpyIn.mono (hmono n _ (le_max_left _ _)) hn).trans ?_
      have hu  :=
        pathIn_mono (hmono m1 _ (le_trans (le_max_left m1 m2) (le_max_right n _))) hm1
      have hv  :=
        pathIn_mono (hmono m2 _ (le_trans (le_max_right m1 m2) (le_max_right n _))) hm2
      rcases hstep with hs | hs
      · exact HtpyIn.of_step ⟨hs, hu, hv⟩
      · exact (HtpyIn.of_step ⟨hs, hv, hu⟩).symm

end FiniteChains.Comb

