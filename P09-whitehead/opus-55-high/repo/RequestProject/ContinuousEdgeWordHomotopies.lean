import RequestProject.ContinuousEdgeWords
import RequestProject.CombPi1
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Data.List.OfFn
import RequestProject.Tac


/-! Endpoint-preserving reversal and naturality for actual finite edge-word
paths. These statements concern continuous paths, not only their fundamental
group classes. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology

bwd

namespace FiniteChains.ContinuousEdgeWords

theorem realize_congr_list {V E X} [TopologicalSpace X]
    src tgt (v : V → X) edge
    {l m : List (E × Bool)} {a b}
    hl (hm : Comb.IsPath src tgt m a b) (he : l = m) :
    realize src tgt v edge l hl = realize src tgt v edge m hm := by
  subst m
  rfl

variable {K : Comb.Complex2} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (v : K.V → X) (edge : ∀ e, Path (v (K.src e)) (v (K.tgt e)))

theorem reversed_single g :
    (germPath K.src K.tgt v edge g).symm.Homotopic
      (realize K.src K.tgt v edge [Comb.revGerm (X := K) g]
        (by simp)) := by
  cases' g with e b
  cases b
  · simpa [Comb.germSrc, Comb.germTgt, germPath, Comb.revGerm, Bool.not, Bool.not_false, realize, Path.cast_rfl_rfl,
      Path.symm_symm] using (Path.Homotopic.trans_refl _).symm
  · simpa [Comb.germSrc, Comb.germTgt, germPath, Comb.revGerm, Bool.not, Bool.not_true, realize, Path.cast_rfl_rfl]
      using (Path.Homotopic.trans_refl _).symm

theorem realize_revPath l {a b}
    (hl : Comb.IsPath K.src K.tgt l a b) :
    (realize K.src K.tgt v edge l hl).symm.Homotopic
      (realize K.src K.tgt v edge (Comb.revPath (X := K) l) (Comb.isPath_revPath hl)) := by
  induction l generalizing a with
  | nil =>
    cases hl
    rfl
  | cons g l ih =>
    obtain ⟨rfl, ht⟩ := hl
    rw [realize_congr_list K.src K.tgt v edge
      _
      ((Comb.isPath_revPath ht).append (by simp)) (Comb.revPath_cons g l)]
    change ((germPath K.src K.tgt v edge g).trans
      (realize K.src K.tgt v edge l ht)).symm.Homotopic _
    rw [Path.trans_symm]
    exact ((ih ht).hcomp (reversed_single v edge g)).trans
      (realize_append K.src K.tgt v edge _ _
        _ _)

end FiniteChains.ContinuousEdgeWords

namespace FiniteChains.Comb

theorem isPath_ofFn {V E : Type} src tgt n
    (a : Fin (n + 1) → V) (g : Fin n → E × Bool)
    (hs : ∀ i, a i.castSucc = germSrc src tgt (g i))
    (ht : ∀ i, germTgt src tgt (g i) = a i.succ) :
    IsPath src tgt (List.ofFn g) (a 0) (a (Fin.last n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append]
    exact (ih (a ∘ Fin.castSucc) _
      (by simp_all) (by simp_all)).append
      (by simp_all)

end FiniteChains.Comb

namespace FiniteChains.ContinuousEdgeWords

variable {V E X : Type} [TopologicalSpace X]
  (src tgt : E → V) (v : V → X) (edge : ∀ e, Path (v (src e)) (v (tgt e)))

theorem concat_homotopic_realize_ofFn n
    a g
    hs
    ht
    (F : ∀ i : Fin n, Path (v (a i.castSucc)) (v (a i.succ)))
    (hF : ∀ i, (F i).Homotopic
      (realize src tgt v edge [g i] ⟨hs i, ht i⟩)) :
    (Path.concat (v ∘ a) F).Homotopic
      (realize src tgt v edge (List.ofFn g) (Comb.isPath_ofFn src tgt n a g hs ht)) := by
  induction n with
  | zero =>
    aesop
  | succ n ih =>
    rw [Path.concat_succ]
    have he : List.ofFn g = List.ofFn (g ·.castSucc) ++ [g (Fin.last n)] := by
      rw [List.ofFn_succ', List.concat_eq_append]
    rw [realize_congr_list src tgt v edge (Comb.isPath_ofFn src tgt _ a g hs ht)
      ((Comb.isPath_ofFn src tgt n (a ∘ Fin.castSucc) (g ·.castSucc)
        (by simp_all) (by simp_all)).append
          (by simp_all)) he]
    exact ((ih (a ∘ Fin.castSucc) (g ·.castSucc)
      (by simp_all) (by simp_all)
      (F ·.castSucc) (by simp_all)).hcomp (by simp_all)).trans
      (realize_append src tgt v edge
        _ _
        _
        (by simp_all))
