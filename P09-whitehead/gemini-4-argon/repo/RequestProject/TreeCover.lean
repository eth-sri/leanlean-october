module

public import RequestProject.TreePresentation
public import RequestProject.CoverComplex

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.SpanningTree

universe u

variable {K : Complex2.{u}} (T : SpanningTree K)
variable (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]

abbrev CovQ : Type u := FreeGroup (NonTree T) ⧸ N

noncomputable def germQ (g : K.E × Bool) : CovQ T N := QuotientGroup.mk (germWord T g)

noncomputable def wordQ (p : List (K.E × Bool)) : CovQ T N :=
  QuotientGroup.mk (pathWord T p)

variable {T N}

@[simp] theorem wordQ_nil : wordQ T N ([] : List (K.E × Bool)) = 1 := rfl

theorem wordQ_cons (g : K.E × Bool) (p : List (K.E × Bool)) :
    wordQ T N (g :: p) = germQ T N g * wordQ T N p := by
  unfold wordQ germQ; rw [pathWord_cons, QuotientGroup.mk_mul]

theorem wordQ_append (p p' : List (K.E × Bool)) :
    wordQ T N (p ++ p') = wordQ T N p * wordQ T N p' := by
  unfold wordQ; rw [pathWord_append, QuotientGroup.mk_mul]

theorem germQ_false_eq_inv (e : K.E) :
    germQ T N (e, false) = (germQ T N (e, true))⁻¹ := by
  unfold germQ
  simpa [revGerm] using (by rw [germWord_revGerm, QuotientGroup.mk_inv] :
    (QuotientGroup.mk (germWord T (revGerm (e, true))) : CovQ T N) =
      (QuotientGroup.mk (germWord T (e, true)))⁻¹)

@[simp] theorem wordQ_treePath (a : K.V) : wordQ T N (T.treePath a) = 1 := by
  unfold wordQ; rw [pathWord_treePath]; rfl

variable (T N)

def covSrc (x : CovQ T N × K.E) : CovQ T N × K.V := (x.1, K.src x.2)

noncomputable def covTgt (x : CovQ T N × K.E) : CovQ T N × K.V :=
  (x.1 * germQ T N (x.2, true), K.tgt x.2)

noncomputable def liftGerm (q : CovQ T N) (g : K.E × Bool) : (CovQ T N × K.E) × Bool :=
  if g.2 then ((q, g.1), true) else ((q * germQ T N g, g.1), false)

noncomputable def liftK : List (K.E × Bool) → CovQ T N → List ((CovQ T N × K.E) × Bool)
  | [], _ => []
  | g :: L, q => liftGerm T N q g :: liftK L (q * germQ T N g)

variable {T N}

@[simp] theorem liftK_nil (q : CovQ T N) : liftK T N [] q = [] := rfl

@[simp] theorem liftK_cons (g : K.E × Bool) (L : List (K.E × Bool)) (q : CovQ T N) :
    liftK T N (g :: L) q = liftGerm T N q g :: liftK T N L (q * germQ T N g) := rfl

@[simp] theorem liftGerm_fst_snd (q : CovQ T N) (g : K.E × Bool) :
    ((liftGerm T N q g).1.2, (liftGerm T N q g).2) = g := by
  rcases g with ⟨_, _ | _⟩ <;> simp [liftGerm]

theorem germSrc_liftGerm (q : CovQ T N) (g : K.E × Bool) :
    germSrc (covSrc T N) (covTgt T N) (liftGerm T N q g) = (q, germSrc K.src K.tgt g) := by
  rcases g with ⟨e, _ | _⟩
  · show (q * germQ T N (e, false) * germQ T N (e, true), K.tgt e) = (q, K.tgt e)
    rw [germQ_false_eq_inv, inv_mul_cancel_right]
  · rfl

theorem germTgt_liftGerm (q : CovQ T N) (g : K.E × Bool) :
    germTgt (covSrc T N) (covTgt T N) (liftGerm T N q g) =
      (q * germQ T N g, germTgt K.src K.tgt g) := by
  rcases g with ⟨_, _ | _⟩ <;> rfl

theorem liftK_isPath {L : List (K.E × Bool)} {a b : K.V} (hL : IsPath K.src K.tgt L a b)
    (q : CovQ T N) :
    IsPath (covSrc T N) (covTgt T N) (liftK T N L q) (q, a) (q * wordQ T N L, b) := by
  induction L generalizing a q with
  | nil => cases hL; simp [wordQ, liftK]
  | cons g L ih =>
      rcases hL with ⟨rfl, hrest⟩
      refine ⟨by rw [germSrc_liftGerm], ?_⟩
      rw [germTgt_liftGerm, wordQ_cons, ← mul_assoc]
      exact ih hrest (q * germQ T N g)

variable (T N)

noncomputable def treeCover (hN : ∀ f, treeRel T f ∈ N) : Complex2.{u} where
  V := CovQ T N × K.V
  E := CovQ T N × K.E
  F := CovQ T N × K.F
  src := covSrc T N
  tgt := covTgt T N
  base f := (f.1, K.base f.2)
  att f := liftK T N (K.att f.2) f.1
  att_isLoop f := by
    have h := liftK_isPath (T := T) (N := N) (K.att_isLoop f.2) f.1
    rwa [show wordQ T N (K.att f.2) = 1 from (QuotientGroup.eq_one_iff _).2 (hN f.2), mul_one] at h

variable {T N}

@[simp] theorem treeCover_src (hN : ∀ f, treeRel T f ∈ N) (x : CovQ T N × K.E) :
    (treeCover T N hN).src x = covSrc T N x := rfl

@[simp] theorem treeCover_tgt (hN : ∀ f, treeRel T f ∈ N) (x : CovQ T N × K.E) :
    (treeCover T N hN).tgt x = covTgt T N x := rfl

variable (T N)

noncomputable def treeCoverProj (hN : ∀ f, treeRel T f ∈ N) : Hom (treeCover T N hN) K where
  onV x := x.2
  onE x := x.2
  onF x := x.2
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := by
    have hmap : ∀ (L : List (K.E × Bool)) (q : CovQ T N),
        (liftK T N L q).map (fun eb => (eb.1.2, eb.2)) = L := by
      intro L; induction L with
      | nil => intro _; rfl
      | cons _ _ ih => intro _; simp [ih]
    exact (hmap (K.att f.2) f.1).symm

theorem exists_loop_spelling (w : FreeGroup (NonTree T)) :
    ∃ p : List (K.E × Bool), IsPath K.src K.tgt p T.root T.root ∧ pathWord T p = w := by
  classical
  induction w using FreeGroup.induction_on with
  | one => exact ⟨[], rfl, rfl⟩
  | of e =>
      refine ⟨conjPath T [((e : K.E), true)] (K.src (e : K.E)) (K.tgt (e : K.E)),
        conjPath_isLoop T (isPath_single _), ?_⟩
      rw [conjPath, pathWord_append, pathWord_append, pathWord_treePath, pathWord_revPath,
        pathWord_treePath]
      simp [pathWord, germWord, dif_neg e.2]
  | inv_of _ ih =>
      obtain ⟨p, hp, hw⟩ := ih
      exact ⟨revPath p, isPath_revPath hp, by rw [pathWord_revPath, hw]⟩
  | mul _ _ hx hy =>
      obtain ⟨p, hp, hpw⟩ := hx; obtain ⟨p', hp', hpw'⟩ := hy
      exact ⟨p ++ p', hp.append hp', by rw [pathWord_append, hpw, hpw']⟩

end FiniteChains.Comb.SpanningTree
