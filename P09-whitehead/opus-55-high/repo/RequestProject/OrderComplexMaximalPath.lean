import RequestProject.OrderComplexBoundaryDetour
import RequestProject.StrictOrderComplex
import RequestProject.Tac


set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

theorem germ_into_maximal_lt {C : P → Prop} {t}
    (hmax : ∀ x, C x → t ≤ x → x = t) e
    (he : C e.1.1.1 ∧ C e.1.1.2)
    (ht : germTgt (orderCx P).src (orderCx P).tgt e = t)
    (hne : germSrc (orderCx P).src (orderCx P).tgt e ≠ t) :
    (germSrc (orderCx P).src (orderCx P).tgt e : P) < t := by
  cases' e with e b
  cases b with
  | true =>
    exact lt_of_le_of_ne (ht ▸ e.2) hne
  | false =>
    change e.1.1 = t at ht
    change e.1.2 ≠ t at hne
    grind

 theorem maximal_detour_germs {t u v : P}
    (hmax : ∀ x, C x → t ≤ x → x = t)
    (hconn : ConnectedIn (fun x => C x ∧ x < t))
    e f
    (he : IsPath (orderCx P).src (orderCx P).tgt [e] u t)
    (hf : IsPath (orderCx P).src (orderCx P).tgt [f] t v)
    (hC : PathIn C [e, f]) (hu : u ≠ t) (hv : v ≠ t) :
    ∃ l, IsPath (orderCx P).src (orderCx P).tgt l u v ∧
      PathIn (fun x => C x ∧ x ≠ t) l ∧ Htpy (orderCx P) u v [e, f] l := by
  have heC := (pathIn_of_cons hC).1
  have hfC := (pathIn_of_cons (pathIn_of_cons hC).2).1
  have heends := germ_ends heC
  have hfends := germ_ends hfC
  have hes := he.1.symm
  have het := he.2
  have hfs := hf.1.symm
  have hft := hf.2
  have hut : u < t := by
    simpa [hes] using germ_into_maximal_lt hmax e heC het (hes ▸ hu)
  have hvt : v < t := by
    have hrC := hfC
    have hr := germ_into_maximal_lt hmax (revGerm f) hrC
      (by simpa using hfs) (by simp_all)
    rwa [germSrc_revGerm, hft] at hr
  obtain ⟨l, hl, hB⟩ := hconn u v (by simp_all) (by simp_all)
  have hp := he.append hf
  have hT : PathIn (· ≤ t) [e, f] := by
    apply pathIn_cons
    · cases' e with e b
      cases b with
      | false =>
        change e.1.2 = u at hes
        grind
      | true =>
        change e.1.2 = t at het
        grind
    · apply pathIn_cons
      · cases' f with f b
        cases b with
        | false =>
          change f.1.2 = t at hfs
          grind
        | true =>
          change f.1.1 = t at hfs
          grind
      tauto
  refine ⟨l, hl, pathIn_mono (by grind) hB, ?_⟩
  apply Davis.htpy_of_loop_nil hp hl
  exact htpy_nil_of_pathIn_le_top (A := fun x => x ≤ t) (le_refl t)
    (by simp) hut.le (hp.append (isPath_revPath hl))
    (pathIn_append hT (pathIn_revPath (pathIn_mono (by grind) hB)))

theorem germ_ends_iff {B : P → Prop} e :
    (B e.1.1.1 ∧ B e.1.1.2) ↔
      (B (germSrc (orderCx P).src (orderCx P).tgt e) ∧
        B (germTgt (orderCx P).src (orderCx P).tgt e)) := by
  cases' e with e b
  cases b <;> simp only [germSrc, germTgt, Bool.false_eq_true, if_false, if_true]
  · exact and_comm
  · rfl

/-- A nondegenerate path with endpoints away from a maximal cell has a homotopic
representative avoiding that cell. -/
theorem maximal_path_representative_nondegenerate
    (hmax : ∀ x, C x → t ≤ x → x = t)
    (hconn : ConnectedIn (fun x => C x ∧ x < t))
    p {a b : P}
    (ha : C a ∧ a ≠ t) (hb : C b ∧ b ≠ t)
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) (hC : PathIn C p)
    (hnd : ∀ e ∈ p, germSrc (orderCx P).src (orderCx P).tgt e ≠
      germTgt (orderCx P).src (orderCx P).tgt e) :
    ∃ l, IsPath (orderCx P).src (orderCx P).tgt l a b ∧
      PathIn (fun x => C x ∧ x ≠ t) l ∧ Htpy (orderCx P) a b p l := by
  induction p using List.twoStepInduction generalizing a with
  | nil => exact ⟨[], hp, pathIn_nil _, Htpy.refl _⟩
  | singleton e =>
    refine ⟨[e], hp, pathIn_cons ?_ (pathIn_nil _), Htpy.refl _⟩
    apply (germ_ends_iff (B := fun x => C x ∧ x ≠ t) e).mpr
    simp_all
  | cons_cons e f p ih ihTail =>
    have heC := (pathIn_of_cons hC).1
    have htail := (pathIn_of_cons hC).2
    have hfC := (pathIn_of_cons htail).1
    have hrest := (pathIn_of_cons htail).2
    have he : IsPath (orderCx P).src (orderCx P).tgt [e] a
        (germTgt (orderCx P).src (orderCx P).tgt e) := ⟨hp.1, rfl⟩
    have hwC := (germ_ends heC).2
    by_cases hw : germTgt (orderCx P).src (orderCx P).tgt e = t
    · have hf : IsPath (orderCx P).src (orderCx P).tgt [f] t
          (germTgt (orderCx P).src (orderCx P).tgt f) := ⟨hw ▸ hp.2.1, rfl⟩
      have hv : germTgt (orderCx P).src (orderCx P).tgt f ≠ t := by
        intro hvt
        aesop
      have hpair := pathIn_cons heC (pathIn_cons hfC (pathIn_nil _))
      obtain ⟨l, hl, hB, hh⟩ := maximal_detour_germs hmax hconn e f
        (hw ▸ he) hf hpair ha.2 hv
      obtain ⟨r, hr, hrB, hhr⟩ := ih ⟨(germ_ends hfC).2, hv⟩ hp.2.2 hrest
        (by grind)
      exact ⟨l ++ r, hl.append hr, pathIn_append hB hrB,
        Htpy.append_congr (he.append (by grind)) hp.2.2 hh hhr⟩
    · obtain ⟨r, hr, hrB, hh⟩ := ihTail f ⟨hwC, hw⟩ hp.2 htail
        (by grind)
      have heB : PathIn (fun x => C x ∧ x ≠ t) [e] := by
        apply pathIn_cons
        · exact (germ_ends_iff (B := fun x => C x ∧ x ≠ t) e).mpr ⟨hp.1 ▸ ha, ⟨hwC, hw⟩⟩
        tauto
      exact ⟨[e] ++ r, he.append hr, pathIn_append heB hrB,
        Htpy.append_congr he hp.2 (Htpy.refl _) hh⟩

theorem normalizeOrdGerm_properties e
    (hC : C e.1.1.1 ∧ C e.1.1.2) :
    PathIn C (mapPath (strictOrderIncl P) (normalizeOrdGerm e)) ∧
      ∀ g ∈ mapPath (strictOrderIncl P) (normalizeOrdGerm e),
        germSrc (orderCx P).src (orderCx P).tgt g ≠
          germTgt (orderCx P).src (orderCx P).tgt g := by
  classical
  unfold normalizeOrdGerm
  split_ifs with h
  · tauto
  · constructor
    · exact pathIn_cons hC (pathIn_nil _)
    · intro g hg
      have hg' : g = (⟨e.1.1, e.1.2⟩, e.2) := by simpa [mapPath, strictOrderIncl] using hg
      subst g
      cases' e with e b
      cases b with
      | false => exact Ne.symm h
      | true => exact h

theorem normalizeOrdPath_properties
    p (hC : PathIn C p) :
    PathIn C (mapPath (strictOrderIncl P) (normalizeOrdPath p)) ∧
      ∀ g ∈ mapPath (strictOrderIncl P) (normalizeOrdPath p),
        germSrc (orderCx P).src (orderCx P).tgt g ≠
          germTgt (orderCx P).src (orderCx P).tgt g := by
  induction p with
  | nil => tauto
  | cons e p ih =>
    have he := normalizeOrdGerm_properties e (pathIn_of_cons hC).1
    have hp := ih (pathIn_of_cons hC).2
    change PathIn C (mapPath (strictOrderIncl P) (normalizeOrdGerm e ++ normalizeOrdPath p)) ∧ _
    rwd [mapPath_append]
    refine ⟨pathIn_append he.1 hp.1, ?_⟩
    grind

/-- Complete maximal-cell path replacement, with no nondegeneracy assumption. -/
theorem maximal_path_representative
    (hmax : ∀ x, C x → t ≤ x → x = t)
    (hconn : ConnectedIn (fun x => C x ∧ x < t))
    p {a b : P}
    (ha : C a ∧ a ≠ t) (hb : C b ∧ b ≠ t)
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) (hC : PathIn C p) :
    ∃ l, IsPath (orderCx P).src (orderCx P).tgt l a b ∧
      PathIn (fun x => C x ∧ x ≠ t) l ∧ Htpy (orderCx P) a b p l := by
  have hn := normalizeOrdPath_properties p hC
  have hpath := isPath_mapPath (strictOrderIncl P) (normalizeOrdPath_isPath hp)
  obtain ⟨l, hl, hB, hh⟩ := maximal_path_representative_nondegenerate hmax hconn
    _ ha hb hpath hn.1 hn.2
  exact ⟨l, hl, hB, (normalizeOrdPath_htpy hp).symm.trans hh⟩
