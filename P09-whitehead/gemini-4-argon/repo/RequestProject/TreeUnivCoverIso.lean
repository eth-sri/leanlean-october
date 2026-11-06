module

public import RequestProject.TreeCoverAcyclic
public import RequestProject.CombPi2
public import RequestProject.UniversalCoverPi2

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains.Comb

universe u

theorem htpy_of_congr_append {X : Complex2.{u}} {a b c d : X.V}
    {r s p q : List (X.E × Bool)}
    (hr : IsPath X.src X.tgt r c a) (hs : IsPath X.src X.tgt s b d)
    (hp : IsPath X.src X.tgt p a b) (hq : IsPath X.src X.tgt q a b)
    (h : Htpy X c d (r ++ p ++ s) (r ++ q ++ s)) : Htpy X a b p q := by
  have key (l : List (X.E × Bool)) (hl : IsPath X.src X.tgt l a b) :
      Htpy X a b (revPath r ++ (r ++ l ++ s) ++ revPath s) l := by
    have hss := hs.append (isPath_revPath hs)
    rw [show revPath r ++ (r ++ l ++ s) ++ revPath s = (revPath r ++ r) ++ (l ++ (s ++ revPath s)) by
      simp [List.append_assoc]]
    exact (Htpy.append_congr ((isPath_revPath hr).append hr) (hl.append hss)
      (htpy_revPath_append hr) (Htpy.refl _)).trans
      (by simpa using Htpy.append_congr hl hss (Htpy.refl _) (htpy_append_revPath hs))
  exact ((key p hp).symm.trans (h.congr_append (isPath_revPath hr) (isPath_revPath hs))).trans (key q hq)

namespace SpanningTree

variable {K : Complex2.{u}} (T : SpanningTree K)

abbrev relTree : Subgroup (FreeGroup (NonTree T)) := relSub (treeRel T)

abbrev treeUniv : Complex2.{u} :=
  treeCover T (relTree T) (rel_mem_relSub (treeRel T))

variable {T}

def uvQ {x₀ : K.V} : UV K x₀ → CovQ T (relTree T) :=
  Quotient.lift (fun p : PathFrom K x₀ => wordQ T (relTree T) p.1)
    (fun _ _ h => wordClass_htpy T h)

@[simp] theorem uvQ_mk {x₀ : K.V} (p : PathFrom K x₀) :
    uvQ (T := T) (UV.mk p) = wordQ T (relTree T) p.1 := rfl

theorem uvQ_extend {x₀ : K.V} {c : UV K x₀} {eb : K.E × Bool}
    (h : endV c = germSrc K.src K.tgt eb) :
    uvQ (T := T) (extend eb c) = uvQ (T := T) c * germQ T (relTree T) eb := by
  induction c using UV.ind with | h p =>
  rw [extend_mk, uvQ_mk, extendP_pos h, uvQ_mk, wordQ_append]; congr 1
  rw [wordQ_cons, wordQ_nil, mul_one]

theorem uvQ_conjPath {x₀ b : K.V} {l : List (K.E × Bool)} (hl : IsPath K.src K.tgt l x₀ b) :
    pi1ToPres T (loopOf T hl) = wordQ T (relTree T) l := by
  show wordClass T (conjPath T l x₀ b) = _
  rw [conjPath, wordClass_append, wordClass_append,
    show wordClass T (T.treePath x₀) = 1 by
      show QuotientGroup.mk (pathWord T (T.treePath x₀)) = 1; rw [pathWord_treePath]; rfl,
    show wordClass T (revPath (T.treePath b)) = 1 by
      show QuotientGroup.mk (pathWord T (revPath (T.treePath b))) = 1
      rw [pathWord_revPath, pathWord_treePath]; simp,
    one_mul, mul_one]; rfl

theorem uvQ_injective {x₀ : K.V} {c d : UV K x₀} (hq : uvQ (T := T) c = uvQ (T := T) d)
    (he : endV c = endV d) : c = d := by
  induction c using UV.ind with | h p =>
  induction d using UV.ind with | h q =>
  have hp : IsPath K.src K.tgt p.1 x₀ (endpt K x₀ p.1) := p.2
  have hq' : IsPath K.src K.tgt q.1 x₀ (endpt K x₀ p.1) := by
    rw [show endpt K x₀ p.1 = endpt K x₀ q.1 from he]; exact q.2
  have hloop : loopOf T hp = loopOf T hq' := (pi1EquivPres T).injective <| by
    show pi1ToPres T (loopOf T hp) = pi1ToPres T (loopOf T hq')
    rw [uvQ_conjPath hp, uvQ_conjPath hq']; exact hq
  exact Quotient.sound (htpy_of_congr_append (T.treePath_isPath x₀)
    (isPath_revPath (T.treePath_isPath (endpt K x₀ p.1))) hp hq' (Quotient.exact hloop))

variable (T)

def uvEdge {x₀ : K.V} (E : UE K x₀) : (treeUniv T).E := (uvQ (T := T) E.1.1, E.1.2)
def uvFace {x₀ : K.V} (F : UF K x₀) : (treeUniv T).F := (uvQ (T := T) F.1.1, F.1.2)

theorem map_uLiftPath_tree {x₀ : K.V} : ∀ (L : List (K.E × Bool)) (c : UV K x₀) (w : K.V),
    IsPath K.src K.tgt L (endV c) w →
      (uLiftPath L c).map (fun Eb => (uvEdge T Eb.1, Eb.2))
        = liftK T (relTree T) L (uvQ (T := T) c)
  | [], _, _, _ => rfl
  | (e, b) :: t, c, w, ⟨hc, h2⟩ => by
      rw [uLiftPath_cons hc, List.map_cons, liftK_cons,
        map_uLiftPath_tree t (extend (e, b) c) w (by rw [endV_extend hc]; exact h2), uvQ_extend hc]
      cases b <;> simp [uvEdge, uvQ_extend hc, SpanningTree.liftGerm]

def treeUnivHom (x₀ : K.V) : Hom (uCover K x₀) (treeUniv T) where
  onV c := (uvQ (T := T) c, endV c)
  onE := uvEdge T
  onF := uvFace T
  src_onE E := Prod.ext rfl E.2.symm
  tgt_onE E := by
    show covTgt T (relTree T) (uvQ (T := T) E.1.1, E.1.2)
      = (uvQ (T := T) (extend (E.1.2, true) E.1.1), endV (extend (E.1.2, true) E.1.1))
    rw [uvQ_extend (eb := (E.1.2, true)) E.2, endV_extend (eb := (E.1.2, true)) E.2]; rfl
  base_onF F := Prod.ext rfl F.2.symm
  att_onF F := (map_uLiftPath_tree T (K.att F.1.2) F.1.1 (K.base F.1.2)
    (F.2.symm ▸ K.att_isLoop F.1.2)).symm

theorem uvFace_injective {x₀ : K.V} : Function.Injective (uvFace T (x₀ := x₀)) := by
  rintro ⟨⟨c, _⟩, hc⟩ ⟨⟨d, _⟩, hd⟩ hEq
  cases congrArg Prod.snd hEq
  exact Subtype.ext (Prod.ext (uvQ_injective (congrArg Prod.fst hEq) (hc.trans hd.symm)) rfl)

variable [DecidableEq (NonTree T)] in
theorem mem_pi2_iff_bdry2_univCover {x₀ : K.V} (u : (uCover K x₀).F →₀ ℤ) :
    u ∈ Pi2 K x₀ ↔
      bdry2 (univCover (treeRel T)) (chain2 (treeUnivHom T x₀) u) = 0 := by
  have hkey : bdry2 (univCover (treeRel T)) (chain2 (treeUnivHom T x₀) u)
      = piE T (relTree T) (chain1 (treeUnivHom T x₀) (bdry2 (uCover K x₀) u)) := by
    rw [← bdry2_chain2 (treeUnivHom T x₀) u]
    exact (piE_bdry2 (T := T) (N := relTree T) (hN := rel_mem_relSub (treeRel T))
      (chain2 (treeUnivHom T x₀) u)).symm
  refine ⟨fun (hu : bdry2 _ u = 0) => by rw [hkey, hu, map_zero, map_zero], fun hu => ?_⟩
  set z := chain1 (treeUnivHom T x₀) (bdry2 (uCover K x₀) u) with hz
  have hzero : z = 0 :=
    treeChain_eq_zero (T := T) (N := relTree T) (hN := rel_mem_relSub (treeRel T))
      (support_isTree_of_piE_eq_zero (T := T) (N := relTree T) (by rwa [hz, ← hkey]))
      (by rw [hz, ← bdry2_chain2 (treeUnivHom T x₀) u]; exact bdry1_bdry2 _)
  have hinj : Function.Injective (chain1 (treeUnivHom T x₀)) :=
    Finsupp.mapDomain_injective fun ⟨⟨c, _⟩, hc⟩ ⟨⟨d, _⟩, hd⟩ hEq => by
      cases congrArg Prod.snd hEq
      exact Subtype.ext (Prod.ext (uvQ_injective (congrArg Prod.fst hEq) (hc.trans hd.symm)) rfl)
  exact hinj (by rw [← hz, hzero, map_zero])

theorem chain2_treeUnivHom_surjective {x₀ : K.V} :
    Function.Surjective (chain2 (treeUnivHom T x₀)) := by
  refine Finsupp.mapDomain_surjective ?_
  rintro ⟨g, f⟩
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective (s := relTree T) g
  obtain ⟨L, hL, hLw⟩ := exists_loop_spelling T w
  let l := revPath (T.treePath x₀) ++ L ++ T.treePath (K.base f)
  have hl : IsPath K.src K.tgt l x₀ (K.base f) :=
    ((isPath_revPath (T.treePath_isPath x₀)).append hL).append (T.treePath_isPath (K.base f))
  have hend : endpt K x₀ l = K.base f := endpt_eq_of_isPath hl
  refine ⟨⟨(UV.mk ⟨l, hend.symm ▸ hl⟩, f), hend⟩, Prod.ext ?_ rfl⟩
  show wordQ T (relTree T) l = _
  rw [wordQ_append, wordQ_append, wordQ_treePath,
    show wordQ T (relTree T) (revPath (T.treePath x₀)) = 1 by
      show QuotientGroup.mk (pathWord T (revPath (T.treePath x₀))) = 1
      rw [pathWord_revPath, pathWord_treePath]; simp,
    one_mul, mul_one]
  exact congrArg QuotientGroup.mk hLw
