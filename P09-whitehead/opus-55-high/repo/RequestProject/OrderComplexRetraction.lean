import RequestProject.OrderComplexHtpyIn
noncomputable section


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
def InjIn (U B : P → Prop) :=
  ∀ v l, B v →
    IsPath (orderCx P).src (orderCx P).tgt l v v → PathIn B l →
    HtpyIn U v v l [] → HtpyIn B v v l []

/-- Every loop inside `J` is null-homotopic inside `J`. -/
def SimplyConnectedIn (J : P → Prop) :=
  ∀ v l, J v →
    IsPath (orderCx P).src (orderCx P).tgt l v v → PathIn J l → HtpyIn J v v l []

theorem injIn_self (U : P → Prop) : InjIn U U := by tauto

/-- Both endpoints of an oriented edge with endpoints in `C` lie in `C`. -/
theorem germ_ends {C : P → Prop} {eb} (h : C eb.1.1.1 ∧ C eb.1.1.2) :
    C (germSrc (orderCx P).src (orderCx P).tgt eb) ∧
      C (germTgt (orderCx P).src (orderCx P).tgt eb) := by
  cases' eb with e tag
  cases tag
  · tauto
  tauto

/-- Injectivity on path classes only depends on the ambient subposet up to equivalence. -/
theorem injIn_congr_left {U U' B : P → Prop} (h : ∀ x, U x ↔ U' x) (hinj : InjIn U B) :
    InjIn U' B :=
  fun v l hv hp hl hh => hinj v l hv hp hl (HtpyIn.mono (by simp_all) hh)

/-- Injectivity on path classes composes. -/
theorem injIn_trans {U A B : P → Prop} (hBA : ∀ x, B x → A x)
    (hUA : InjIn U A) (hAB : InjIn A B) : InjIn U B := by
  intro v l hv hp hl h
  exact hAB v l hv hp hl (hUA v l (hBA v hv) hp (pathIn_mono hBA hl) h)

/-- Simple connectedness of a subposet, in the form produced by the order-complex results of the
project. -/
theorem simplyConnectedIn_of_simplyConnected
    (hJ : SimplyConnected (orderCx {x : P // J x})) : SimplyConnectedIn J := by
  intro v l hv hp hl
  have hlift := isPath_liftPathIn l hl hv hv hp
  have hnull := hJ _ _ hlift
  have h := htpyIn_mapPath (C := J) _ monotone_subtypeVal
    (by simp) hnull
  simp_all [show mapPath (orderCxMap _ monotone_subtypeVal)
      (liftPathIn l hl) = l from mapPath_liftPathIn l hl]

/-! ### The retraction on paths -/

section Retr

variable (A : P → Prop) (j0 : P) (γ : P → List ((orderCx P).E × Bool))

open Classical
/-- The retraction on vertices: a vertex of `A` stays where it is, any other vertex goes to the
base vertex `j0` of the intersection. -/
def retrVert (u : P) := if A u then u else j0

open Classical
/-- The retraction on oriented edges: an edge of `A` is unchanged, any other edge `u → v` is
replaced by `γ u ⁻¹ γ v`. -/
def retrGerm (eb : (orderCx P).E × Bool) :=
  if A eb.1.1.1 ∧ A eb.1.1.2 then [eb]
  else revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++
    γ (germTgt (orderCx P).src (orderCx P).tgt eb)

/-- The retraction on edge paths. -/
def retrPath : List ((orderCx P).E × Bool) → List ((orderCx P).E × Bool)
  | [] => []
  | eb :: t => retrGerm A γ eb ++ retrPath t

variable {A j0 γ}

@[simp] theorem retrPath_nil : retrPath A γ [] = [] := rfl

@[simp] theorem retrPath_cons eb t :
    retrPath A γ (eb :: t) = retrGerm A γ eb ++ retrPath A γ t := rfl

theorem retrPath_append l l' :
    retrPath A γ (l ++ l') = retrPath A γ l ++ retrPath A γ l' := by
  induction l <;> simp_all

omit [Preorder P] in
theorem retrVert_of_mem {u : P} (hu : A u) : retrVert A j0 u = u := by
  classical
  simp [retrVert, hu]

omit [Preorder P] in
theorem retrVert_of_not_mem {u : P} (hu : ¬ A u) : retrVert A j0 u = j0 := by
  classical
  simp [retrVert, hu]

theorem retrGerm_of_mem (h : A eb.1.1.1 ∧ A eb.1.1.2) :
    retrGerm A γ eb = [eb] := by
  classical
  simp [retrGerm, h]

theorem retrGerm_of_not_mem (h : ¬ (A eb.1.1.1 ∧ A eb.1.1.2)) :
    retrGerm A γ eb = revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++
      γ (germTgt (orderCx P).src (orderCx P).tgt eb) := by
  classical
  simp [retrGerm, h]

/-- A path inside `A` is returned unchanged. -/
theorem retrPath_eq_self (hl : PathIn A l) :
    retrPath A γ l = l := by
  induction l with
  | nil => rfl
  | cons eb t ih =>
      cases' pathIn_of_cons hl with heb ht
      rw [retrPath_cons, retrGerm_of_mem heb, ih ht, List.singleton_append]

/-- The retraction lands inside `A`. -/
theorem pathIn_retrPath (hγA : ∀ u, PathIn A (γ u)) l :
    PathIn A (retrPath A γ l) := by
  classical
  induction l with
  | nil => exact pathIn_nil A
  | cons eb t ih =>
      refine pathIn_append ?_ ih
      by_cases h : A eb.1.1.1 ∧ A eb.1.1.2
      · rw [retrGerm_of_mem h]
        exact pathIn_cons h (pathIn_nil A)
      · rw [retrGerm_of_not_mem h]
        exact pathIn_append (pathIn_revPath (hγA _)) (hγA _)

end Retr

/-! ### The gluing step -/

section Gluing

variable {A B U J : P → Prop} {j0 : P} {γ : P → List ((orderCx P).E × Bool)}

variable (hJA : ∀ x, J x → A x) (hJmk : ∀ x, A x → B x → J x)
  (hγpath : ∀ u : P, J u → IsPath (orderCx P).src (orderCx P).tgt (γ u) j0 u)
  (hγin : ∀ u : P, PathIn J (γ u)) (hγnil : ∀ u : P, ¬ J u → γ u = [])

include hJA hγin in
theorem pathIn_gamma_of_subset (u : P) : PathIn A (γ u) :=
  pathIn_mono hJA (hγin u)

include hJA hJmk hγpath hγnil in
/-- The chosen path from the base vertex to the image of a vertex of `B`. -/
theorem isPath_gamma {u : P} (hu : B u) :
    IsPath (orderCx P).src (orderCx P).tgt (γ u) j0 (retrVert A j0 u) := by
  by_cases hA : A u
  · rw [retrVert_of_mem hA]
    simp_all
  · rw [retrVert_of_not_mem hA, hγnil u (by grind)]
    rfl

include hJA hJmk hγpath hγnil in
/-- The image of an oriented edge is a path between the images of its endpoints. -/
theorem isPath_retrGerm (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    {eb : (orderCx P).E × Bool} (h1 : U eb.1.1.1) (h2 : U eb.1.1.2) :
    IsPath (orderCx P).src (orderCx P).tgt (retrGerm A γ eb)
      (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
      (retrVert A j0 (germTgt (orderCx P).src (orderCx P).tgt eb)) := by
  classical
  by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
  · rw [retrGerm_of_mem hA]
    have hAs := germ_ends hA
    simp [retrVert_of_mem hAs.1, retrVert_of_mem hAs.2]
  · rw [retrGerm_of_not_mem hA]
    have hB : B eb.1.1.1 ∧ B eb.1.1.2 := by
      grind
    have hBs := germ_ends hB
    refine isPath_append_iff.mpr ⟨j0, ?_, isPath_gamma hJA hJmk hγpath hγnil hBs.2⟩
    exact isPath_revPath (isPath_gamma hJA hJmk hγpath hγnil hBs.1)

include hJA hJmk hγpath hγnil in
/-- The image of a path is a path between the images of its endpoints. -/
theorem isPath_retrPath (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b)) :
    ∀ (l : List ((orderCx P).E × Bool)) {a b : P},
      IsPath (orderCx P).src (orderCx P).tgt l a b → PathIn U l →
      IsPath (orderCx P).src (orderCx P).tgt (retrPath A γ l) (retrVert A j0 a)
        (retrVert A j0 b) := by
  intro l
  induction l with
  | nil =>
      simp
  | cons eb t ih =>
      intro a b hp hU
      cases' hp with ha hrest
      subst ha
      cases' pathIn_of_cons hU with hUe hUt
      refine isPath_append_iff.mpr
        ⟨retrVert A j0 (germTgt (orderCx P).src (orderCx P).tgt eb), ?_, ih hrest hUt⟩
      exact isPath_retrGerm hJA hJmk hγpath hγnil hmix hUe.1 hUe.2

include hJA hJmk hγpath hγin in
/-- **On the edges of `J` the two formulas agree.**  This is the only place where the simple
connectedness of the intersection is used. -/
theorem htpyIn_retrGerm_of_pathIn_B (hJsc : SimplyConnectedIn J) (hj0 : J j0)
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
    have hAs := germ_ends hA
    have hBs := germ_ends hB
    have hJs := hJmk s hAs.1 hBs.1
    have hJt := hJmk t hAs.2 hBs.2
    have hγs := hγpath s hJs
    have hγt := hγpath t hJt
    have hγsA := pathIn_gamma_of_subset hJA hγin s
    have hγtA := pathIn_gamma_of_subset hJA hγin t
    have hebPath := isPath_single eb
    have hebA := pathIn_cons hA (pathIn_nil A)
    -- the loop `γ s · eb · γ t ⁻¹` lies in `J` and is therefore null-homotopic inside `J`
    have hloopPath : IsPath (orderCx P).src (orderCx P).tgt
        (γ s ++ ([eb] ++ revPath (γ t))) j0 j0 :=
      isPath_append_iff.mpr ⟨s, hγs,
        isPath_append_iff.mpr ⟨t, hebPath, isPath_revPath hγt⟩⟩
    have hebJ : J eb.1.1.1 ∧ J eb.1.1.2 :=
      by simp_all
    have hloopIn :=
      pathIn_append (hγin s)
        (pathIn_append (pathIn_cons hebJ (pathIn_nil J)) (pathIn_revPath (hγin t)))
    have hnull :=
      HtpyIn.mono hJA (hJsc j0 _ hj0 hloopPath hloopIn)
    -- conjugate the null-homotopy by `γ s ⁻¹` and `γ t`
    have hconj :=
      hnull.congr_append (isPath_revPath hγs) hγt (pathIn_revPath hγsA) hγtA
    -- the left-hand side is homotopic to `eb`
    have hcancel1 := htpyIn_revPath_append hγs hγsA
    have hcancel2 := htpyIn_revPath_append hγt hγtA
    have hstep1 :=
      HtpyIn.append_congr hebPath
        (isPath_append_iff.mpr ⟨j0, isPath_revPath hγt, hγt⟩) hebA
        (pathIn_append (pathIn_revPath hγtA) hγtA) (HtpyIn.refl _) hcancel2
    have hstep2 :=
      HtpyIn.append_congr (isPath_append_iff.mpr ⟨j0, isPath_revPath hγs, hγs⟩)
        (isPath_append_iff.mpr ⟨t, hebPath, isPath_append_iff.mpr ⟨j0, isPath_revPath hγt, hγt⟩⟩)
        (pathIn_append (pathIn_revPath hγsA) hγsA)
        (pathIn_append hebA (pathIn_append (pathIn_revPath hγtA) hγtA))
        hcancel1 (HtpyIn.refl _)
    have hmain : HtpyIn A s t [eb] (revPath (γ s) ++ γ t) := by
      have h1 : HtpyIn A s t [eb] ((revPath (γ s) ++ γ s) ++ ([eb] ++ (revPath (γ t) ++ γ t))) := by
        refine (HtpyIn.trans ?_ hstep2.symm)
        simpa using hstep1.symm
      refine h1.trans ?_
      simp_all
    grind [retrGerm_of_mem hA, retrVert_of_mem hAs.1, retrVert_of_mem hAs.2]
  · rw [retrGerm_of_not_mem hA]
    exact HtpyIn.refl _

include hJA hJmk hγpath hγin hγnil in
/-- **Telescoping along a path of `B`.**  The image of a path of `B` from `u` to `v` is
homotopic, inside `A`, to `γ u ⁻¹ γ v`. -/
theorem htpyIn_retrPath_of_pathIn_B (hJsc : SimplyConnectedIn J) (hj0 : J j0) :
    ∀ (l : List ((orderCx P).E × Bool)) {u v : P},
      IsPath (orderCx P).src (orderCx P).tgt l u v → PathIn B l → B u → B v →
      HtpyIn A (retrVert A j0 u) (retrVert A j0 v) (retrPath A γ l)
        (revPath (γ u) ++ γ v) := by
  intro l
  induction l with
  | nil =>
      intro u v hp _ hu _
      have huv := hp
      subst huv
      have hγu :=
        isPath_gamma hJA hJmk hγpath hγnil hu
      have hγuA := pathIn_gamma_of_subset hJA hγin u
      exact (htpyIn_revPath_append hγu hγuA).symm
  | cons eb t ih =>
      intro u v hp hBl hu hv
      cases' hp with ha hrest
      subst ha
      cases' pathIn_of_cons hBl with hBe hBt
      set m : P := germTgt (orderCx P).src (orderCx P).tgt eb with hm
      have hBm := (germ_ends hBe).2
      have hγu :=
        isPath_gamma hJA hJmk hγpath hγnil hu
      have hγm :=
        isPath_gamma hJA hJmk hγpath hγnil hBm
      have hγv :=
        isPath_gamma hJA hJmk hγpath hγnil hv
      have hγuA : PathIn A (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) :=
        pathIn_gamma_of_subset hJA hγin _
      have hγmA := pathIn_gamma_of_subset hJA hγin m
      have hγvA := pathIn_gamma_of_subset hJA hγin v
      have hgerm := htpyIn_retrGerm_of_pathIn_B (A := A) (γ := γ) hJA hJmk hγpath hγin hJsc hj0 hBe
      have hih := ih hrest hBt hBm hv
      have hfirst : IsPath (orderCx P).src (orderCx P).tgt (retrGerm A γ eb)
          (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb)) (retrVert A j0 m) := by
        refine HtpyIn.isPath hgerm.symm ?_
        exact isPath_append_iff.mpr ⟨j0, isPath_revPath hγu, hγm⟩
      have hsecond :=
        HtpyIn.isPath hih.symm (isPath_append_iff.mpr ⟨j0, isPath_revPath hγm, hγv⟩)
      have hfirstA : PathIn A (retrGerm A γ eb) := by
        classical
        by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
        · rw [retrGerm_of_mem hA]; exact pathIn_cons hA (pathIn_nil A)
        · rw [retrGerm_of_not_mem hA]
          exact pathIn_append (pathIn_revPath hγuA) hγmA
      have hsecondA :=
        pathIn_retrPath (pathIn_gamma_of_subset hJA hγin) t
      have hcomb :=
        HtpyIn.append_congr hfirst hsecond hfirstA hsecondA hgerm hih
      refine hcomb.trans ?_
      -- cancel `γ m ⁻¹ γ m` in the middle
      have hcancel :=
        htpyIn_append_revPath hγm hγmA
      have hmid :=
        hcancel.congr_append (isPath_revPath hγu) hγv (pathIn_revPath hγuA) hγvA
      simp_all

include hJA hJmk hγpath hγin hγnil in
/-- **The retraction respects one elementary cancellation.** -/
theorem htpyIn_retrPath_of_stepIn
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hJsc : SimplyConnectedIn J) (hj0 : J j0) {a b : P}
    {l l' : List ((orderCx P).E × Bool)} (h : StepIn U a b l l') :
    HtpyIn A (retrVert A j0 a) (retrVert A j0 b) (retrPath A γ l) (retrPath A γ l') := by
  classical
  obtain ⟨⟨hpl, hpl', hc⟩, hUl, hUl'⟩ := h
  have hγA := (pathIn_gamma_of_subset hJA hγin)
  rcases hc with ⟨p', q', eb, hlEq, hl'Eq⟩ | ⟨p', q', t, hlEq, hl'Eq⟩
  · -- a backtrack
    subst hlEq
    subst hl'Eq
    have hUp' := pathIn_of_append_left hUl
    have hUrest := pathIn_of_append_right hUl
    cases' pathIn_of_cons hUrest with hUe hUrest'
    have hUq' := (pathIn_of_cons hUrest').2
    -- endpoints of the pieces
    obtain ⟨c, hpc, hrest⟩ := isPath_append_iff.mp hpl
    cases' hrest with hcs hrest2
    cases' hrest2 with hmid hq'
    have hPp' :=
      isPath_retrPath hJA hJmk hγpath hγnil hmix p' hpc hUp'
    have hcq := hq'
    have hPq' :=
      isPath_retrPath hJA hJmk hγpath hγnil hmix q' hcq hUq'
    have hrevTgt : germTgt (orderCx P).src (orderCx P).tgt (revGerm eb) =
        germSrc (orderCx P).src (orderCx P).tgt eb := by simp
    -- the two images cancel
    have hkey : HtpyIn A (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
        (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
        (retrGerm A γ eb ++ retrGerm A γ (revGerm eb)) [] := by
      by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
      · have hA' : A (revGerm eb).1.1.1 ∧ A (revGerm eb).1.1.2 := hA
        rw [retrGerm_of_mem hA, retrGerm_of_mem hA']
        have hsrc := (germ_ends hA).1
        refine HtpyIn.of_step ⟨⟨?_, rfl, Or.inl ⟨[], [], eb, rfl, rfl⟩⟩, ?_, pathIn_nil A⟩
        · refine ⟨?_, ?_, ?_⟩
          · rw [retrVert_of_mem hsrc]
          · omega
          · rw [retrVert_of_mem hsrc]; simp
        · exact pathIn_cons hA (pathIn_cons hA (pathIn_nil A))
      · have hA' : ¬ (A (revGerm eb).1.1.1 ∧ A (revGerm eb).1.1.2) := hA
        rw [retrGerm_of_not_mem hA, retrGerm_of_not_mem hA']
        have hB : B eb.1.1.1 ∧ B eb.1.1.2 := by
          grind
        have hBs := germ_ends hB
        set s : P := germSrc (orderCx P).src (orderCx P).tgt eb with hs
        set t : P := germTgt (orderCx P).src (orderCx P).tgt eb with ht
        have hγs :=
          isPath_gamma hJA hJmk hγpath hγnil hBs.1
        have hγt :=
          isPath_gamma hJA hJmk hγpath hγnil hBs.2
        have hsimp : germSrc (orderCx P).src (orderCx P).tgt (revGerm eb) = t := by
          simp_all
        have hsimp' : germTgt (orderCx P).src (orderCx P).tgt (revGerm eb) = s := by
          omega
        rw [hsimp, hsimp']
        -- `(γ s ⁻¹ γ t)(γ t ⁻¹ γ s) ≃ []`
        have hcancelt :=
          htpyIn_append_revPath hγt (hγA t)
        have hmid :=
          hcancelt.congr_append (isPath_revPath hγs) hγs (pathIn_revPath (hγA s)) (hγA s)
        have hrw : (revPath (γ s) ++ γ t) ++ (revPath (γ t) ++ γ s) =
            revPath (γ s) ++ (γ t ++ revPath (γ t)) ++ γ s := by
          simp
        rw [hrw]
        refine hmid.trans ?_
        simpa using htpyIn_revPath_append hγs (hγA s)
    have hcs' := hcs
    subst hcs'
    have hglue : HtpyIn A (retrVert A j0 a) (retrVert A j0 b)
        (retrPath A γ p' ++ (retrGerm A γ eb ++ retrGerm A γ (revGerm eb)) ++ retrPath A γ q')
        (retrPath A γ p' ++ [] ++ retrPath A γ q') := by
      refine hkey.congr_append hPp' ?_ (pathIn_retrPath hγA p') (pathIn_retrPath hγA q')
      simp_all
    have hrwl : retrPath A γ (p' ++ eb :: revGerm eb :: q') =
        retrPath A γ p' ++ (retrGerm A γ eb ++ retrGerm A γ (revGerm eb)) ++ retrPath A γ q' := by
      rw [retrPath_append]
      simp
    simp_all [hrwl, retrPath_append]
  · -- a two-cell
    subst hlEq
    subst hl'Eq
    have hfront := pathIn_of_append_left hUl
    have hUp' := pathIn_of_append_left hfront
    have hUatt := pathIn_of_append_right hfront
    have hUq' := pathIn_of_append_right hUl
    obtain ⟨c, hfrontPath, hq'⟩ := isPath_append_iff.mp hpl
    obtain ⟨d, hpc, hatt⟩ := isPath_append_iff.mp hfrontPath
    have hbase := hatt.1
    have hbase' : c = t.1.1 := by
      obtain ⟨-, h2⟩ := hatt
      aesop
    subst hbase
    subst hbase'
    have hPp' :=
      isPath_retrPath hJA hJmk hγpath hγnil hmix p' hpc hUp'
    have hPq' :=
      isPath_retrPath hJA hJmk hγpath hγnil hmix q' hq' hUq'
    have hv1 := hUatt _ (by tauto)
    have hv2 := hUatt ((⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : OrdEdge P), true) (by tauto)
    have hkey : HtpyIn A (retrVert A j0 t.1.1) (retrVert A j0 t.1.1)
        (retrPath A γ ((orderCx P).att t)) [] := by
      by_cases hallA : A t.1.1 ∧ A t.1.2.1 ∧ A t.1.2.2
      · -- the two-cell lies in `A`
        have hattA : PathIn A ((orderCx P).att t) := by
          intro e he
          have hmem : e = ((⟨(t.1.1, t.1.2.1), t.2.1⟩ : OrdEdge P), true) ∨
              e = ((⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : OrdEdge P), true) ∨
              e = ((⟨(t.1.1, t.1.2.2), le_trans t.2.1 t.2.2⟩ : OrdEdge P), false) := by
            simpa [orderCx, or_assoc] using he
          grind
        rw [retrPath_eq_self hattA, retrVert_of_mem hallA.1]
        refine HtpyIn.of_step ⟨⟨(orderCx P).att_isLoop t, rfl,
          Or.inr ⟨[], [], t, by simp, rfl⟩⟩, hattA, pathIn_nil A⟩
      · -- the two-cell lies in `B`
        have hallB : B t.1.1 ∧ B t.1.2.1 ∧ B t.1.2.2 := by
          grind
        have hattB : PathIn B ((orderCx P).att t) := by
          intro e he
          have hmem : e = ((⟨(t.1.1, t.1.2.1), t.2.1⟩ : OrdEdge P), true) ∨
              e = ((⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : OrdEdge P), true) ∨
              e = ((⟨(t.1.1, t.1.2.2), le_trans t.2.1 t.2.2⟩ : OrdEdge P), false) := by
            simpa [orderCx, or_assoc] using he
          grind
        have htel := htpyIn_retrPath_of_pathIn_B (A := A) (γ := γ) hJA hJmk hγpath hγin hγnil hJsc hj0 _ ((orderCx P).att_isLoop t) hattB hallB.1 hallB.1
        refine htel.trans ?_
        have hγx := isPath_gamma hJA hJmk hγpath hγnil hallB.1
        exact htpyIn_revPath_append hγx (hγA t.1.1)
    have hglue :=
      hkey.congr_append hPp' hPq' (pathIn_retrPath hγA p') (pathIn_retrPath hγA q')
    simp_all [retrPath_append]

include hJA hJmk hγpath hγin hγnil in
/-- The retraction respects homotopies inside `U`. -/
theorem htpyIn_retrPath_of_htpyIn
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hJsc : SimplyConnectedIn J) (hj0 : J j0) {a b : P}
    {p q : List ((orderCx P).E × Bool)} (h : HtpyIn U a b p q) :
    HtpyIn A (retrVert A j0 a) (retrVert A j0 b) (retrPath A γ p) (retrPath A γ q) := by
  induction h with
  | refl => exact HtpyIn.refl _
  | tail _ hstep ih =>
      refine ih.trans ?_
      rcases hstep with hs | hs
      · exact htpyIn_retrPath_of_stepIn hJA hJmk hγpath hγin hγnil hmix hJsc hj0 hs
      · exact (htpyIn_retrPath_of_stepIn hJA hJmk hγpath hγin hγnil hmix hJsc hj0 hs).symm

end Gluing

/-- **The gluing step for injectivity on path classes.**  If `U = A ∪ B`, no comparability inside
`U` is mixed, and the intersection `J = A ∩ B` is nonempty, connected and simply connected, then
a loop inside `A` which is null-homotopic inside `U` is null-homotopic inside `A`.  Nothing is
assumed about `B`. -/
theorem injIn_union_of_unmixed {A B U J : P → Prop}
    (hmix : ∀ a b, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hJdef : ∀ x, J x ↔ (A x ∧ B x))
    (hJconn : ConnectedIn J) (hJsc : SimplyConnectedIn J)
    {j0} (hj0 : J j0) :
    InjIn U A := by
  classical
  have hJA : ∀ x, J x → A x := by simp_all
  have hJmk : ∀ x, A x → B x → J x := by simp_all
  -- choose the paths `γ`
  have hex : ∀ u, ∃ g : List ((orderCx P).E × Bool),
      (J u → IsPath (orderCx P).src (orderCx P).tgt g j0 u) ∧ PathIn J g ∧ (¬ J u → g = []) := by
    intro u
    by_cases hu : J u
    · aesop
    · exact ⟨[], by simp_all, pathIn_nil J, fun _ => rfl⟩
  choose γ hγpath hγin hγnil using hex
  intro v l hv hp hl hnull
  have h := htpyIn_retrPath_of_htpyIn (A := A) (B := B) (J := J) (γ := γ) hJA hJmk
    hγpath hγin hγnil hmix hJsc hj0 hnull
  simp_all [retrPath_eq_self hl, retrVert_of_mem hv]

/-! ### The initial step: a monotone retraction -/

/-- A monotone map that fixes the vertices of `B` returns a path of `B` unchanged. -/
theorem mapPath_liftPathIn_of_fix {C B : P → Prop} (f : {x : P // C x} → P) (hf : Monotone f)
    (hfix : ∀ z : {x : P // C x}, B z.1 → f z = z.1) :
    ∀ (l : List ((orderCx P).E × Bool)) (hl : PathIn C l), PathIn B l →
      mapPath (orderCxMap f hf) (liftPathIn l hl) = l
  | [], _, _ => rfl
  | e :: t, hl, hB => by
      have hrest :=
        mapPath_liftPathIn_of_fix f hf hfix t (pathIn_of_cons hl).2 (pathIn_of_cons hB).2
      cases' (pathIn_of_cons hB).1 with he1 he2
      simp [liftPathIn, mapPath, List.map_cons, List.cons.injEq]
      constructor
      · refine Prod.ext ?_ rfl
        refine Subtype.ext ?_
        aesop
      · exact hrest

/-- **A monotone retraction is injective on path classes.**  If the subposet `C` retracts
monotonically onto a smaller subposet `B`, fixing `B` pointwise, then a loop inside `B` that is
null-homotopic inside `C` is null-homotopic inside `B`. -/
theorem injIn_of_monotone_retraction {C B} (hBC : ∀ x, B x → C x)
    f (hf : Monotone f) (hfB : ∀ z, B (f z))
    (hfix : ∀ z : {x : P // C x}, B z.1 → f z = z.1) :
    InjIn C B := by
  intro v l hv hp hl hnull
  have hvC := hBC v hv
  have hlC := pathIn_mono hBC hl
  have hlift :=
    htpy_lift_of_htpyIn hnull hvC hvC hlC (pathIn_nil C)
  have hpush := htpyIn_mapPath (C := B) f hf hfB hlift
  rw [mapPath_liftPathIn_of_fix f hf hfix l hlC hl, hfix _ hv] at hpush
  tauto

/-! ### Passing to an increasing exhaustion -/

/-- **Finiteness of null-homotopies.**  A homotopy of the ambient complex only uses finitely many
cells, so it takes place inside one member of an increasing exhaustion. -/
theorem exists_htpyIn_of_htpy {D : ℕ → P → Prop} (hmono : ∀ m n, m ≤ n → ∀ x, D m x → D n x)
    (hcov : ∀ x, ∃ n, D n x) {a b : P} {p q}
    (h : Htpy (orderCx P) a b p q) : ∃ n, HtpyIn (D n) a b p q := by
  have hpath : ∀ l, ∃ n, PathIn (D n) l := by
    intro l
    induction l with
    | nil => exact ⟨0, pathIn_nil _⟩
    | cons e t ih =>
        cases' ih with n hn
        cases' hcov e.1.1.1 with n1 hn1
        cases' hcov e.1.1.2 with n2 hn2
        refine ⟨max n (max n1 n2), pathIn_cons ⟨?_, ?_⟩ ?_⟩
        · grind
        · grind
        · exact pathIn_mono (by grind) hn
  induction h with
  | refl => tauto
  | @tail u v _ hstep ih =>
      cases' ih with n hn
      cases' hpath u with m1 hm1
      cases' hpath v with m2 hm2
      refine ⟨max n (max m1 m2), ?_⟩
      refine (HtpyIn.mono (by grind) hn).trans ?_
      have hu : PathIn (D (max n (max m1 m2))) u :=
        pathIn_mono (by grind) hm1
      have hv : PathIn (D (max n (max m1 m2))) v :=
        pathIn_mono (by grind) hm2
      rcases hstep with hs | hs
      · exact HtpyIn.of_step (by tauto)
      · exact (HtpyIn.of_step (by tauto)).symm
