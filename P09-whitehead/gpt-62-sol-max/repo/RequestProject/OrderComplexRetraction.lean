module

public import RequestProject.OrderComplexHtpyIn

@[expose] public section

/-! Retracting a gluing along a simply connected intersection on edge-path classes. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

universe u

variable {P Q : Type u} [Preorder P] [Preorder Q]

/-! ### Injectivity on path classes -/

/-- **`B` is injective on path classes inside `U`**: a loop inside `B` that is null-homotopic
inside `U` is null-homotopic inside `B`. -/
def InjIn (U B : P → Prop) : Prop :=
  ∀ (v : P) (l : List ((orderCx P).E × Bool)), B v →
    IsPath (orderCx P).src (orderCx P).tgt l v v → PathIn B l →
    HtpyIn U v v l [] → HtpyIn B v v l []

/-- Every loop inside `J` is null-homotopic inside `J`. -/
def SimplyConnectedIn (J : P → Prop) : Prop :=
  ∀ (v : P) (l : List ((orderCx P).E × Bool)), J v →
    IsPath (orderCx P).src (orderCx P).tgt l v v → PathIn J l → HtpyIn J v v l []

theorem injIn_self (U : P → Prop) : InjIn U U := fun _ _ _ _ _ h => h


/-- Injectivity on path classes composes. -/
theorem injIn_trans {U A B : P → Prop} (hBA : ∀ x, B x → A x)
    (hUA : InjIn U A) (hAB : InjIn A B) : InjIn U B := by
  intro v l hv hp hl h
  exact hAB v l hv hp hl (hUA v l (hBA v hv) hp (pathIn_mono hBA hl) h)

/-- Simple connectedness of a subposet, in the form produced by the order-complex results of the
project. -/
theorem simplyConnectedIn_of_simplyConnected {J : P → Prop}
    (hJ : SimplyConnected (orderCx {x : P // J x})) : SimplyConnectedIn J := by
  intro v l hv hp hl
  have hh := htpyIn_mapPath (C := J) Subtype.val monotone_subtypeVal Subtype.property
    (hJ ⟨v, hv⟩ _ (isPath_liftPathIn l hl hv hv hp))
  change HtpyIn J v v (mapPath (subposetHom J) (liftPathIn l hl)) [] at hh
  rwa [mapPath_liftPathIn] at hh

/-! ### The retraction on paths -/

private abbrev subCx (A : P → Prop) := orderCx (Subtype A)

private theorem subposet_mapPath_injective (A : P → Prop) :
    Function.Injective (mapPath (subposetHom A)) :=
  mapPath_injective_of_onE fun _ _ h =>
    Subtype.ext (Prod.ext (Subtype.ext (congrArg (·.1.1) h))
      (Subtype.ext (congrArg (·.1.2) h)))

/-- A homotopy in `A ∪ B` retracts to `A`: edges of `A` stay as they are, and edges of `B`
are replaced by paths through a fixed vertex of the intersection. Simple connectivity makes
the two descriptions agree on the intersection. -/
theorem injIn_union_of_unmixed {A B U J : P → Prop}
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hJdef : ∀ x, J x ↔ (A x ∧ B x))
    (hJconn : ConnectedIn J) (hJsc : SimplyConnectedIn J)
    {j0 : P} (hj0 : J j0) : InjIn U A := by
  classical
  have hJA (v) (h : J v) := ((hJdef v).mp h).1
  let o : Subtype A := ⟨j0, hJA j0 hj0⟩
  let r (v : P)  := if h : A v then ⟨v,h⟩ else o
  have hr (v : P) (h : A v) : r v = ⟨v,h⟩ := dite_eq_left h
  have hex (v : P) : ∃ p : List ((orderCx P).E × Bool), PathIn J p ∧
      (J v → IsPath (orderCx P).src (orderCx P).tgt p j0 v) ∧ (¬ J v → p = []) := by
    by_cases hv : J v
    · obtain ⟨p, hp, hsp⟩ := hJconn _ _ hj0 hv
      exact ⟨p, hsp, fun _ => hp, fun h => (h hv).elim⟩
    · exact ⟨[], pathIn_nil _, fun h => (hv h).elim, fun _ => rfl⟩
  choose γ hγ hγpath hγnil using hex
  have hγA v := pathIn_mono hJA (hγ v)
  let γA v := liftPathIn (γ v) (hγA v)
  have hγr (v : P) (hv : B v) :
      IsPath (orderCx P).src (orderCx P).tgt (γ v) j0 (r v).val := by
    by_cases ha : A v
    · exact (hr v ha).symm ▸ hγpath v ((hJdef v).mpr ⟨ha, hv⟩)
    · simp [r, o, ha, hγnil v (fun h => ha (hJA v h))]
  have hγAr (v : P) (hv : B v)  :=
    isPath_liftPathIn _ (hγA v) o.2 (r v).2 (hγr v hv)
  let E (e : (subCx U).E × Bool) := ((subposetHom U).onE e.1, e.2)
  let s (e : (subCx U).E × Bool) := (germSrc (subCx U).src (subCx U).tgt e).val
  let t (e : (subCx U).E × Bool) := (germTgt (subCx U).src (subCx U).tgt e).val
  have ends {C : P → Prop} (e : (subCx U).E × Bool) :
      (C e.1.1.1.1 ∧ C e.1.1.2.1) ↔ C (s e) ∧ C (t e) :=
    germ_ends_iff (B := fun x : Subtype U => C x.val) e
  have hsingle e : IsPath (orderCx P).src (orderCx P).tgt [E e] (s e) (t e) :=
    isPath_mapPath (subposetHom U) (isPath_single e)
  let g (e : (subCx U).E × Bool) :=
    if h : A e.1.1.1.1 ∧ A e.1.1.2.1 then [liftGermIn (E e) h] else
      revPath (γA (s e)) ++ γA (t e)
  have hGA (e : (subCx U).E × Bool) (h : A e.1.1.1.1 ∧ A e.1.1.2.1) :
      g e = [liftGermIn (E e) h] := dite_eq_left h
  have hvalid e : IsPath (subCx A).src (subCx A).tgt (g e) (r (s e)) (r (t e)) := by
    by_cases ha : A e.1.1.1.1 ∧ A e.1.1.2.1
    · have hn := (ends e).mp ha
      rw [hGA e ha, hr _ hn.1, hr _ hn.2]
      exact isPath_liftPathIn [E e] (pathIn_cons ha (pathIn_nil _)) _ _ (hsingle e)
    · have hB := (ends e).mp ((hmix _ _ e.1.2 e.1.1.1.2 e.1.1.2.2).resolve_left ha)
      simpa only [g, dite_eq_right ha] using (isPath_revPath (hγAr _ hB.1)).append (hγAr _ hB.2)
  have hrev (e : (subCx U).E × Bool) : g (revGerm e) = revPath (g e) := by
    by_cases he : A e.1.1.1.1 ∧ A e.1.1.2.1
    · simp [g, he, E, liftGermIn, revGerm, revPath]
    · have he' : ¬ (A (revGerm e).1.1.1.1 ∧ A (revGerm e).1.1.2.1) := he
      simp only [g, dite_eq_right he, dite_eq_right he', s, t, germSrc_revGerm,
        germTgt_revGerm, revPath_append, revPath_revPath]
  have hBedge (e : (subCx U).E × Bool) (hb : B (s e)) (hc : B (t e)) :
      Htpy (subCx A) (r (s e)) (r (t e)) (g e) (revPath (γA (s e)) ++ γA (t e)) := by
    by_cases ha : A e.1.1.1.1 ∧ A e.1.1.2.1
    · have hA := (ends e).mp ha
      have hjs := (hJdef _).mpr ⟨hA.1, hb⟩
      have hjt := (hJdef _).mpr ⟨hA.2, hc⟩
      have hpath : IsPath (orderCx P).src (orderCx P).tgt
          (γ (s e) ++ [E e] ++ revPath (γ (t e))) j0 j0 :=
        ((hγpath _ hjs).append (hsingle e)).append (isPath_revPath (hγpath _ hjt))
      have hJedge : PathIn J [E e] := pathIn_cons ((ends e).mpr ⟨hjs, hjt⟩) (pathIn_nil _)
      have hin := pathIn_append (pathIn_append (hγ (s e)) hJedge) (pathIn_revPath (hγ (t e)))
      have h := (hJsc _ _ hj0 hpath hin).mono hJA
      have hl := htpy_lift_of_htpyIn h o.2 o.2 (pathIn_mono hJA hin) (pathIn_nil _)
      apply htpy_of_rooted_null (hγAr _ hb) (hvalid e) (hγAr _ hc)
      convert hl using 1 <;> try rfl
      apply subposet_mapPath_injective A
      simp only [mapPath_append, mapPath_revPath, hGA e ha, mapPath_liftPathIn]
      rfl
    · simpa only [g, dite_eq_right ha] using Htpy.refl (revPath (γA (s e)) ++ γA (t e))
  let F : PathSubstitution (subCx U) (subCx A) :=
    { onV := fun v => r v.val
      onGerm := g
      valid := hvalid
      reverse := hrev
      faces := fun f => by
        obtain ⟨⟨x, y, z⟩, hxy, hyz⟩ := f
        have h₁ := hmix x.val y.val hxy x.2 y.2
        have h₂ := hmix y.val z.val hyz y.2 z.2
        have h₃ := hmix x.val z.val (le_trans hxy hyz) x.2 z.2
        have hAB : (A x.val ∧ A y.val ∧ A z.val) ∨ (B x.val ∧ B y.val ∧ B z.val) := by tauto
        rcases hAB with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
        · let f' : OrdTri (Subtype A) := ⟨(⟨x.val,hx⟩, ⟨y.val,hy⟩, ⟨z.val,hz⟩), hxy, hyz⟩
          have hf : ((subCx U).att ⟨(x,y,z), hxy,hyz⟩).flatMap g = (subCx A).att f' := by
            change g (⟨(x,y),hxy⟩, true) ++ (g (⟨(y,z),hyz⟩, true) ++
              (g (⟨(x,z),le_trans hxy hyz⟩, false) ++ [])) = _
            rw [hGA _ ⟨hx,hy⟩, hGA _ ⟨hy,hz⟩, hGA _ ⟨hx,hz⟩]
            rfl
          change Htpy (subCx A) (r x.val) (r x.val) _ []
          rw [hf, hr _ hx]
          exact Htpy.of_step ⟨(subCx A).att_isLoop f', rfl, Or.inr ⟨[], [], f', by simp, rfl⟩⟩
        · let f : OrdTri (Subtype U) := ⟨(x,y,z), hxy,hyz⟩
          have hS : PathIn (fun v : Subtype U => B v.val) ((subCx U).att f) :=
            (pathIn_att_iff f).2 ⟨hx, hy, hz⟩
          change Htpy (subCx A) (r x.val) (r x.val) (((subCx U).att f).flatMap g) []
          exact (htpy_telescope (X := subCx U) (Y := subCx A)
            (S := fun v  => B v.val) (f := fun v  => r v.val)
            (γ := fun v  => γA v.val) (g := g)
            (fun v => hγAr v.val) hBedge ((subCx U).att_isLoop f) hx hx
            (fun e he => germ_ends (C := fun v : Subtype U => B v.val) (e := e) (hS e he))).trans
            (htpy_revPath_append (hγAr x.val hx)) }
  intro v l hv hp hl hnull
  cases l with
  | nil => exact HtpyIn.refl _
  | cons e l =>
    have hlU := hnull.symm.pathIn (pathIn_nil U)
    have hvU  := hp.1.symm ▸ (germ_ends (hlU e List.mem_cons_self)).1
    have h := F.htpy (htpy_lift_of_htpyIn hnull hvU hvU hlU (pathIn_nil U))
    have h' := htpyIn_mapPath (C := A) Subtype.val monotone_subtypeVal Subtype.property h
    change HtpyIn A (r v).val (r v).val
      (mapPath (subposetHom A) ((liftPathIn (e :: l) hlU).flatMap g)) [] at h'
    have hfix (p : List ((orderCx P).E × Bool)) (hU : PathIn U p) (hA : PathIn A p) :
        mapPath (subposetHom A) ((liftPathIn p hU).flatMap g) = p := by
      induction p with
      | nil => rfl
      | cons x p ih =>
        have he := (pathIn_of_cons hA).1
        have he' := hGA (liftGermIn x (pathIn_of_cons hU).1) he
        change mapPath (subposetHom A) (g _ ++ (liftPathIn p _).flatMap g) = _
        rw [mapPath_append, he', ih (pathIn_of_cons hU).2 (pathIn_of_cons hA).2]
        rfl
    rwa [hr v hv, hfix _ hlU hl] at h'

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
      · refine Prod.ext ?_ rfl
        refine Subtype.ext ?_
        refine Prod.ext ?_ ?_
        · tauto
        · tauto
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
  rw [mapPath_liftPathIn_of_fix f hf hfix l hlC hl, hfix ⟨v, hvC⟩ hv] at hpush
  assumption

/-! ### Passing to an increasing exhaustion -/

open scoped Filter

/-- **Finiteness of null-homotopies.**  A homotopy of the ambient complex only uses finitely many
cells, so it takes place inside one member of an increasing exhaustion. -/
theorem exists_htpyIn_of_htpy {D : ℕ → P → Prop} (hmono : ∀ m n, m ≤ n → ∀ x, D m x → D n x)
    (hcov : ∀ x : P, ∃ n, D n x) {a b : P} {p q : List ((orderCx P).E × Bool)}
    (h : Htpy (orderCx P) a b p q) : ∃ n, HtpyIn (D n) a b p q := by
  have hv (v : P) : ∀ᶠ n in Filter.atTop, D n v := by
    obtain ⟨n, hn⟩ := hcov v
    exact Filter.eventually_atTop.mpr ⟨n, fun m hm => hmono n m hm v hn⟩
  have hp (l : List ((orderCx P).E × Bool)) : ∀ᶠ n in Filter.atTop, PathIn (D n) l := by
    induction l with
    | nil => exact Filter.Eventually.of_forall fun _ => pathIn_nil _
    | cons e l ih =>
      filter_upwards [hv e.1.1.1, hv e.1.1.2, ih] with _ ha hb hl using pathIn_cons ⟨ha, hb⟩ hl
  suffices ∀ᶠ n in Filter.atTop, HtpyIn (D n) a b p q from this.exists
  induction h with
  | refl => exact Filter.Eventually.of_forall fun _ => HtpyIn.refl _
  | @tail u v _ hstep ih =>
    filter_upwards [ih, hp u, hp v] with _ hh hu hv
    rcases hstep with hs | hs
    · exact hh.trans (HtpyIn.of_step ⟨hs, hu, hv⟩)
    · exact hh.trans (HtpyIn.of_step ⟨hs, hv, hu⟩).symm

end Comb
end FiniteChains
