module

public import RequestProject.OrderComplexHtpyIn

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains.Comb

universe u

variable {P : Type u}

open Classical in
def retrVert (A : P → Prop) (j0 u : P) : P := if A u then u else j0

theorem retrVert_of_mem {A : P → Prop} {j0 u : P} (hu : A u) : retrVert A j0 u = u := by
  classical simp [retrVert, hu]

theorem retrVert_of_not_mem {A : P → Prop} {j0 u : P} (hu : ¬ A u) : retrVert A j0 u = j0 := by
  classical simp [retrVert, hu]

variable [Preorder P]

def InjIn (U B : P → Prop) : Prop :=
  ∀ (v : P) (l : List ((orderCx P).E × Bool)), B v →
    IsPath (orderCx P).src (orderCx P).tgt l v v → PathIn B l →
    HtpyIn U v v l [] → HtpyIn B v v l []

def SimplyConnectedIn (J : P → Prop) : Prop :=
  ∀ (v : P) (l : List ((orderCx P).E × Bool)), J v →
    IsPath (orderCx P).src (orderCx P).tgt l v v → PathIn J l → HtpyIn J v v l []

theorem injIn_self (U : P → Prop) : InjIn U U := fun _ _ _ _ _ h => h

theorem germ_ends {C : P → Prop} {eb : (orderCx P).E × Bool} (h : C eb.1.1.1 ∧ C eb.1.1.2) :
    C (germSrc (orderCx P).src (orderCx P).tgt eb) ∧
      C (germTgt (orderCx P).src (orderCx P).tgt eb) := by
  rcases eb with ⟨e, _ | _⟩ <;> exact ⟨by tauto, by tauto⟩

theorem injIn_congr_left {U U' B : P → Prop} (h : ∀ x, U x ↔ U' x) (hinj : InjIn U B) :
    InjIn U' B :=
  fun v l hv hp hl hh => hinj v l hv hp hl (HtpyIn.mono (fun x hx => (h x).2 hx) hh)

theorem injIn_trans {U A B : P → Prop} (hBA : ∀ x, B x → A x)
    (hUA : InjIn U A) (hAB : InjIn A B) : InjIn U B :=
  fun v l hv hp hl h => hAB v l hv hp hl (hUA v l (hBA v hv) hp (pathIn_mono hBA hl) h)

theorem simplyConnectedIn_of_simplyConnected {J : P → Prop}
    (hJ : SimplyConnected (orderCx {x : P // J x})) : SimplyConnectedIn J := by
  intro v l hv hp hl
  have h := htpyIn_mapPath (C := J) Subtype.val monotone_subtypeVal Subtype.prop
    (hJ ⟨v, hv⟩ (liftPathIn l hl) (isPath_liftPathIn l hl hv hv hp))
  erw [mapPath_liftPathIn l hl] at h
  exact h

section

variable (A : P → Prop) (γ : P → List ((orderCx P).E × Bool))

open Classical in
def retrGerm (eb : (orderCx P).E × Bool) : List ((orderCx P).E × Bool) :=
  if A eb.1.1.1 ∧ A eb.1.1.2 then [eb]
  else revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++
    γ (germTgt (orderCx P).src (orderCx P).tgt eb)

def retrPath : List ((orderCx P).E × Bool) → List ((orderCx P).E × Bool)
  | [] => []
  | eb :: t => retrGerm A γ eb ++ retrPath t

variable {A γ}

@[simp] theorem retrPath_nil : retrPath A γ [] = [] := rfl
@[simp] theorem retrPath_cons (eb : (orderCx P).E × Bool) (t : List ((orderCx P).E × Bool)) :
    retrPath A γ (eb :: t) = retrGerm A γ eb ++ retrPath A γ t := rfl

theorem retrPath_append (l l' : List ((orderCx P).E × Bool)) :
    retrPath A γ (l ++ l') = retrPath A γ l ++ retrPath A γ l' := by
  induction l <;> simp [retrPath, *, List.append_assoc]

theorem retrGerm_of_mem {eb : (orderCx P).E × Bool} (h : A eb.1.1.1 ∧ A eb.1.1.2) :
    retrGerm A γ eb = [eb] := by classical simp [retrGerm, h]

theorem retrGerm_of_not_mem {eb : (orderCx P).E × Bool} (h : ¬ (A eb.1.1.1 ∧ A eb.1.1.2)) :
    retrGerm A γ eb = revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++
      γ (germTgt (orderCx P).src (orderCx P).tgt eb) := by classical simp [retrGerm, h]

theorem retrPath_eq_self : ∀ {l : List ((orderCx P).E × Bool)}, PathIn A l → retrPath A γ l = l
  | [], _ => rfl
  | eb :: t, hl => by
      obtain ⟨heb, ht⟩ := pathIn_of_cons hl
      rw [retrPath_cons, retrGerm_of_mem heb, retrPath_eq_self ht, List.singleton_append]

theorem pathIn_retrPath (hγA : ∀ u : P, PathIn A (γ u)) :
    ∀ l : List ((orderCx P).E × Bool), PathIn A (retrPath A γ l)
  | [] => pathIn_nil A
  | eb :: t => by
      classical
      refine pathIn_append ?_ (pathIn_retrPath hγA t)
      by_cases h : A eb.1.1.1 ∧ A eb.1.1.2
      · rw [retrGerm_of_mem h]; exact pathIn_cons h (pathIn_nil A)
      · rw [retrGerm_of_not_mem h]; exact pathIn_append (pathIn_revPath (hγA _)) (hγA _)

end

section

variable {A B U J : P → Prop} {j0 : P} {γ : P → List ((orderCx P).E × Bool)}
  (hJA : ∀ x, J x → A x) (hJmk : ∀ x, A x → B x → J x)
  (hγpath : ∀ u : P, J u → IsPath (orderCx P).src (orderCx P).tgt (γ u) j0 u)
  (hγin : ∀ u : P, PathIn J (γ u)) (hγnil : ∀ u : P, ¬ J u → γ u = [])

include hJA hJmk hγpath hγnil in
theorem isPath_gamma {u : P} (hu : B u) :
    IsPath (orderCx P).src (orderCx P).tgt (γ u) j0 (retrVert A j0 u) := by
  by_cases hA : A u
  · rw [retrVert_of_mem hA]; exact hγpath u (hJmk u hA hu)
  · rw [retrVert_of_not_mem hA, hγnil u (fun h => hA (hJA u h))]; rfl

include hJA hJmk hγpath hγin hγnil in
theorem htpyIn_mid_cancel {u m v : P} (hu : B u) (hm : B m) (hv : B v) :
    HtpyIn A (retrVert A j0 u) (retrVert A j0 v)
      ((revPath (γ u) ++ γ m) ++ (revPath (γ m) ++ γ v)) (revPath (γ u) ++ γ v) := by
  simpa [List.append_assoc] using
    (htpyIn_append_revPath (isPath_gamma hJA hJmk hγpath hγnil hm)
      (pathIn_mono hJA (hγin m))).congr_append
      (isPath_revPath (isPath_gamma hJA hJmk hγpath hγnil hu))
      (isPath_gamma hJA hJmk hγpath hγnil hv)
      (pathIn_revPath (pathIn_mono hJA (hγin u))) (pathIn_mono hJA (hγin v))

include hJA hJmk hγpath hγnil in
theorem isPath_retrPath (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b)) :
    ∀ (l : List ((orderCx P).E × Bool)) {a b : P},
      IsPath (orderCx P).src (orderCx P).tgt l a b → PathIn U l →
      IsPath (orderCx P).src (orderCx P).tgt (retrPath A γ l) (retrVert A j0 a) (retrVert A j0 b)
  | [], _, _, rfl, _ => rfl
  | eb :: t, _, _, ⟨rfl, hrest⟩, hU => by
      classical
      obtain ⟨hUe, hUt⟩ := pathIn_of_cons hU
      refine IsPath.append ?_ (isPath_retrPath hmix t hrest hUt)
      by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
      · have hAs := germ_ends hA
        rw [retrGerm_of_mem hA, retrVert_of_mem hAs.1, retrVert_of_mem hAs.2]
        exact isPath_single _
      · rw [retrGerm_of_not_mem hA]
        have hBs := germ_ends ((hmix _ _ eb.1.2 hUe.1 hUe.2).resolve_left hA)
        exact (isPath_revPath (isPath_gamma hJA hJmk hγpath hγnil hBs.1)).append
          (isPath_gamma hJA hJmk hγpath hγnil hBs.2)

include hJA hJmk hγpath hγin hγnil in
theorem htpyIn_retrPath_of_pathIn_B (hJsc : SimplyConnectedIn J) (hj0 : J j0) :
    ∀ (l : List ((orderCx P).E × Bool)) {u v : P},
      IsPath (orderCx P).src (orderCx P).tgt l u v → PathIn B l → B u → B v →
      HtpyIn A (retrVert A j0 u) (retrVert A j0 v) (retrPath A γ l) (revPath (γ u) ++ γ v)
  | [], u, _, rfl, _, hu, _ =>
      (htpyIn_revPath_append (isPath_gamma hJA hJmk hγpath hγnil hu) (pathIn_mono hJA (hγin u))).symm
  | eb :: t, _, v, ⟨rfl, hrest⟩, hBl, hu, hv => by
      classical
      set u : P := germSrc (orderCx P).src (orderCx P).tgt eb
      obtain ⟨hBe, hBt⟩ := pathIn_of_cons hBl
      have hBm : B (germTgt (orderCx P).src (orderCx P).tgt eb) := (germ_ends hBe).2
      have hγA (x) := pathIn_mono hJA (hγin x)
      have hgerm : HtpyIn A (retrVert A j0 u) (retrVert A j0 (germTgt (orderCx P).src (orderCx P).tgt eb))
          (retrGerm A γ eb) (revPath (γ u) ++ γ (germTgt (orderCx P).src (orderCx P).tgt eb)) := by
        by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
        · set s : P := germSrc (orderCx P).src (orderCx P).tgt eb
          set w : P := germTgt (orderCx P).src (orderCx P).tgt eb
          have hAs := germ_ends hA; have hBs := germ_ends hBe
          have hγs := hγpath s (hJmk s hAs.1 hBs.1); have hγw := hγpath w (hJmk w hAs.2 hBs.2)
          have hebPath : IsPath (orderCx P).src (orderCx P).tgt [eb] s w := isPath_single eb
          have hebA : PathIn A [eb] := pathIn_cons hA (pathIn_nil A)
          have hnull : HtpyIn A j0 j0 (γ s ++ ([eb] ++ revPath (γ w))) [] :=
            HtpyIn.mono hJA (hJsc j0 _ hj0 (hγs.append (hebPath.append (isPath_revPath hγw)))
              (pathIn_append (hγin s) (pathIn_append
                (pathIn_cons ⟨hJmk _ hA.1 hBe.1, hJmk _ hA.2 hBe.2⟩ (pathIn_nil J))
                (pathIn_revPath (hγin w)))))
          have hstep1 := (htpyIn_revPath_append hγw (hγA w)).congr_append hebPath (isPath_nil' w) hebA (pathIn_nil A)
          have hstep2 := (htpyIn_revPath_append hγs (hγA s)).congr_append (isPath_nil' s)
            (hebPath.append ((isPath_revPath hγw).append hγw)) (pathIn_nil A)
            (pathIn_append hebA (pathIn_append (pathIn_revPath (hγA w)) (hγA w)))
          rw [retrGerm_of_mem hA, retrVert_of_mem hAs.1, retrVert_of_mem hAs.2]
          exact (HtpyIn.trans (by simpa using hstep1.symm) (by simpa using hstep2.symm)).trans
            (by simpa [List.append_assoc] using hnull.congr_append (isPath_revPath hγs) hγw (pathIn_revPath (hγA s)) (hγA w))
        · rw [retrGerm_of_not_mem hA]
      have hih := htpyIn_retrPath_of_pathIn_B hJsc hj0 t hrest hBt hBm hv
      have hγu := isPath_gamma hJA hJmk hγpath hγnil hu
      have hγm := isPath_gamma hJA hJmk hγpath hγnil hBm
      have hγv := isPath_gamma hJA hJmk hγpath hγnil hv
      exact (HtpyIn.append_congr (hgerm.symm.isPath ((isPath_revPath hγu).append hγm))
        (hih.symm.isPath ((isPath_revPath hγm).append hγv))
        (by simpa [retrPath] using pathIn_retrPath hγA [eb]) (pathIn_retrPath hγA t) hgerm hih).trans
        (htpyIn_mid_cancel hJA hJmk hγpath hγin hγnil hu hBm hv)

include hJA hJmk hγpath hγin hγnil in
theorem htpyIn_retrPath_of_stepIn
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hJsc : SimplyConnectedIn J) (hj0 : J j0) {a b : P}
    {l l' : List ((orderCx P).E × Bool)} (h : StepIn U a b l l') :
    HtpyIn A (retrVert A j0 a) (retrVert A j0 b) (retrPath A γ l) (retrPath A γ l') := by
  classical
  obtain ⟨⟨hpl, hpl', hc⟩, hUl, hUl'⟩ := h
  have hγA (x) := pathIn_mono hJA (hγin x)
  rcases hc with ⟨p', q', eb, rfl, rfl⟩ | ⟨p', q', t, rfl, rfl⟩
  · obtain ⟨hUe, hUrest'⟩ := pathIn_of_cons (pathIn_of_append_right hUl)
    obtain ⟨c, hpc, rfl, _, hq'⟩ := isPath_append_iff.mp hpl
    have hPp' := isPath_retrPath hJA hJmk hγpath hγnil hmix p' hpc (pathIn_of_append_left hUl)
    have hPq' := isPath_retrPath hJA hJmk hγpath hγnil hmix q' hq' (pathIn_of_cons hUrest').2
    rw [germTgt_revGerm (X := orderCx P) eb] at hPq'
    have hkey : HtpyIn A (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
        (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
        (retrGerm A γ eb ++ retrGerm A γ (revGerm eb)) [] := by
      by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
      · rw [retrGerm_of_mem hA, retrGerm_of_mem (show A (revGerm eb).1.1.1 ∧ A (revGerm eb).1.1.2 from hA)]
        have hsrc : A (germSrc (orderCx P).src (orderCx P).tgt eb) := (germ_ends hA).1
        exact HtpyIn.of_step ⟨⟨⟨by rw [retrVert_of_mem hsrc], (germSrc_revGerm (X := orderCx P) eb).symm,
          by rw [retrVert_of_mem hsrc]; exact germTgt_revGerm (X := orderCx P) eb⟩,
          rfl, Or.inl ⟨[], [], eb, rfl, rfl⟩⟩, pathIn_cons hA (pathIn_cons hA (pathIn_nil A)), pathIn_nil A⟩
      · rw [retrGerm_of_not_mem hA, retrGerm_of_not_mem (show ¬(A (revGerm eb).1.1.1 ∧ A (revGerm eb).1.1.2) from hA),
          germSrc_revGerm (X := orderCx P) eb, germTgt_revGerm (X := orderCx P) eb]
        have hBs := germ_ends ((hmix _ _ eb.1.2 hUe.1 hUe.2).resolve_left hA)
        exact (htpyIn_mid_cancel hJA hJmk hγpath hγin hγnil hBs.1 hBs.2 hBs.1).trans
          (htpyIn_revPath_append (isPath_gamma hJA hJmk hγpath hγnil hBs.1) (hγA _))
    simpa [retrPath_append, retrPath, List.append_assoc] using
      hkey.congr_append hPp' hPq' (pathIn_retrPath hγA p') (pathIn_retrPath hγA q')
  · have hfront : PathIn U (p' ++ (orderCx P).att t) := pathIn_of_append_left hUl
    have hUatt : PathIn U ((orderCx P).att t) := pathIn_of_append_right hfront
    obtain ⟨c, hfrontPath, hq'⟩ := isPath_append_iff.mp hpl
    obtain ⟨d, hpc, rfl, -, -, rfl⟩ := isPath_append_iff.mp hfrontPath
    have hPp' := isPath_retrPath hJA hJmk hγpath hγnil hmix p' hpc (pathIn_of_append_left hfront)
    have hPq' := isPath_retrPath hJA hJmk hγpath hγnil hmix q' hq' (pathIn_of_append_right hUl)
    have hv1 := hUatt ((⟨(t.1.1, t.1.2.1), t.2.1⟩ : OrdEdge P), true) (by simp [orderCx])
    have hv2 := hUatt ((⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : OrdEdge P), true) (by simp [orderCx])
    have hatt_in {C : P → Prop} (hC : C t.1.1 ∧ C t.1.2.1 ∧ C t.1.2.2) : PathIn C ((orderCx P).att t) := by
      intro e he
      rcases show e = ((⟨(t.1.1, t.1.2.1), t.2.1⟩ : OrdEdge P), true) ∨
          e = ((⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : OrdEdge P), true) ∨
          e = ((⟨(t.1.1, t.1.2.2), le_trans t.2.1 t.2.2⟩ : OrdEdge P), false) by
        simpa [orderCx, or_assoc] using he with rfl | rfl | rfl <;> exact ⟨by tauto, by tauto⟩
    have hkey : HtpyIn A (retrVert A j0 t.1.1) (retrVert A j0 t.1.1)
        (retrPath A γ ((orderCx P).att t)) [] := by
      by_cases hallA : A t.1.1 ∧ A t.1.2.1 ∧ A t.1.2.2
      · rw [retrPath_eq_self (hatt_in hallA), retrVert_of_mem hallA.1]
        exact HtpyIn.of_step ⟨⟨(orderCx P).att_isLoop t, rfl,
          Or.inr ⟨[], [], t, by simp, rfl⟩⟩, hatt_in hallA, pathIn_nil A⟩
      · have hallB : B t.1.1 ∧ B t.1.2.1 ∧ B t.1.2.2 := by
          have := hmix _ _ t.2.1 hv1.1 hv1.2
          have := hmix _ _ t.2.2 hv1.2 hv2.2
          have := hmix _ _ (le_trans t.2.1 t.2.2) hv1.1 hv2.2
          tauto
        exact (htpyIn_retrPath_of_pathIn_B hJA hJmk hγpath hγin hγnil hJsc hj0
          ((orderCx P).att t) ((orderCx P).att_isLoop t) (hatt_in hallB) hallB.1 hallB.1).trans
          (htpyIn_revPath_append (isPath_gamma hJA hJmk hγpath hγnil hallB.1) (hγA t.1.1))
    simpa [retrPath_append] using
      hkey.congr_append hPp' hPq' (pathIn_retrPath hγA p') (pathIn_retrPath hγA q')

end

theorem injIn_union_of_unmixed {A B U J : P → Prop}
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hJdef : ∀ x, J x ↔ (A x ∧ B x))
    (hJconn : ConnectedIn J) (hJsc : SimplyConnectedIn J)
    {j0 : P} (hj0 : J j0) :
    InjIn U A := by
  classical
  have hJA : ∀ x, J x → A x := fun x h => ((hJdef x).1 h).1
  have hJmk : ∀ x, A x → B x → J x := fun x h h' => (hJdef x).2 ⟨h, h'⟩
  have hex (u : P) : ∃ g : List ((orderCx P).E × Bool),
      (J u → IsPath (orderCx P).src (orderCx P).tgt g j0 u) ∧ PathIn J g ∧ (¬ J u → g = []) := by
    by_cases hu : J u
    · obtain ⟨g, hg, hgin⟩ := hJconn j0 u hj0 hu
      exact ⟨g, fun _ => hg, hgin, fun h => absurd hu h⟩
    · exact ⟨[], fun h => absurd h hu, pathIn_nil J, fun _ => rfl⟩
  choose γ hγpath hγin hγnil using hex
  intro v l hv hp hl hnull
  have hhtpy {p q} (h : HtpyIn U v v p q) :
      HtpyIn A (retrVert A j0 v) (retrVert A j0 v) (retrPath A γ p) (retrPath A γ q) := by
    induction h with
    | refl => exact HtpyIn.refl _
    | tail _ hstep ih =>
        exact ih.trans (hstep.elim
          (htpyIn_retrPath_of_stepIn hJA hJmk hγpath hγin hγnil hmix hJsc hj0)
          fun hs => (htpyIn_retrPath_of_stepIn hJA hJmk hγpath hγin hγnil hmix hJsc hj0 hs).symm)
  have h := hhtpy hnull
  rwa [retrPath_eq_self hl, retrVert_of_mem hv, retrPath_nil] at h

theorem mapPath_liftPathIn_of_fix {C B : P → Prop} (f : {x : P // C x} → P) (hf : Monotone f)
    (hfix : ∀ z : {x : P // C x}, B z.1 → f z = z.1) :
    ∀ (l : List ((orderCx P).E × Bool)) (hl : PathIn C l), PathIn B l →
      mapPath (orderCxMap f hf) (liftPathIn l hl) = l
  | [], _, _ => rfl
  | e :: t, hl, hB => by
      obtain ⟨he1, he2⟩ := (pathIn_of_cons hB).1
      obtain ⟨hc1, hc2⟩ := (pathIn_of_cons hl).1
      simp only [liftPathIn, mapPath, List.map_cons, List.cons.injEq]
      exact ⟨Prod.ext (Subtype.ext (Prod.ext (hfix ⟨_, hc1⟩ he1) (hfix ⟨_, hc2⟩ he2))) rfl,
        mapPath_liftPathIn_of_fix f hf hfix t (pathIn_of_cons hl).2 (pathIn_of_cons hB).2⟩

theorem injIn_of_monotone_retraction {C B : P → Prop} (hBC : ∀ x, B x → C x)
    (f : {x : P // C x} → P) (hf : Monotone f) (hfB : ∀ z, B (f z))
    (hfix : ∀ z : {x : P // C x}, B z.1 → f z = z.1) :
    InjIn C B := by
  intro v l hv hp hl hnull
  have hvC := hBC v hv
  have hlC := pathIn_mono hBC hl
  have hpush := htpyIn_mapPath (C := B) f hf hfB
    (htpy_lift_of_htpyIn hnull hvC hvC hlC (pathIn_nil C))
  rw [mapPath_liftPathIn_of_fix f hf hfix l hlC hl, hfix ⟨v, hvC⟩ hv] at hpush
  simpa [mapPath, liftPathIn] using hpush

theorem exists_htpyIn_of_htpy {D : ℕ → P → Prop} (hmono : ∀ m n, m ≤ n → ∀ x, D m x → D n x)
    (hcov : ∀ x : P, ∃ n, D n x) {a b : P} {p q : List ((orderCx P).E × Bool)}
    (h : Htpy (orderCx P) a b p q) : ∃ n, HtpyIn (D n) a b p q := by
  have hpath (l : List ((orderCx P).E × Bool)) : ∃ n, PathIn (D n) l := by
    induction l with
    | nil => exact ⟨0, pathIn_nil _⟩
    | cons e t ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨n1, hn1⟩ := hcov e.1.1.1
        obtain ⟨n2, hn2⟩ := hcov e.1.1.2
        exact ⟨max n (max n1 n2), pathIn_cons
          ⟨hmono n1 _ (le_trans (le_max_left n1 n2) (le_max_right n _)) _ hn1,
           hmono n2 _ (le_trans (le_max_right n1 n2) (le_max_right n _)) _ hn2⟩
          (pathIn_mono (hmono n _ (le_max_left _ _)) hn)⟩
  induction h with
  | refl => exact ⟨0, Relation.ReflTransGen.refl⟩
  | @tail u v _ hstep ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m1, hm1⟩ := hpath u
      obtain ⟨m2, hm2⟩ := hpath v
      have hu := pathIn_mono (hmono m1 _ (le_trans (le_max_left m1 m2) (le_max_right n _))) hm1
      have hv := pathIn_mono (hmono m2 _ (le_trans (le_max_right m1 m2) (le_max_right n _))) hm2
      exact ⟨max n (max m1 m2), (HtpyIn.mono (hmono n _ (le_max_left _ _)) hn).trans
        (hstep.elim (fun hs => HtpyIn.of_step ⟨hs, hu, hv⟩) fun hs => (HtpyIn.of_step ⟨hs, hv, hu⟩).symm)⟩
