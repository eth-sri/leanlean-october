import Mathlib.Tactic

import RequestProject.CellComplex
import RequestProject.OpenCoverPathReplacement

/-! Actual continuous realizations of finite oriented edge words. The open
cover criterion retains a finite word, not merely a replacement continuous
path. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval


namespace FiniteChains.ContinuousEdgeWords

variable {V E X : Type} [TopologicalSpace X]
  (src tgt : E → V) (v : V → X) (edge : ∀ e, Path (v (src e)) (v (tgt e)))

def germPath (g : E × Bool) : Path (v (Comb.germSrc src tgt g))
    (v (Comb.germTgt src tgt g)) :=
  match g with
  | (e, true) => edge e
  | (e, false) => (edge e).symm

/-- Read a genuinely composable finite list as a continuous path. -/
def realize : (l : List (E × Bool)) → {a b : V} →
    Comb.IsPath src tgt l a b → Path (v a) (v b)
  | [], a, _, h => (Path.refl (v a)).cast rfl (congrArg v h.symm)
  | g :: l, _, _, h =>
      ((germPath src tgt v edge g).cast (congrArg v h.1) rfl).trans
        (realize l h.2)



theorem realize_append (l m : List (E × Bool)) {a b c : V}
    (hl : Comb.IsPath src tgt l a b) (hm : Comb.IsPath src tgt m b c) :
    Path.Homotopic
      ((realize src tgt v edge l hl).trans (realize src tgt v edge m hm))
      (realize src tgt v edge (l ++ m) (hl.append hm)) := by
  induction l generalizing a with
  | nil =>
    
    subst b
    exact Path.Homotopic.refl_trans _
  | cons g l ih =>
    
    exact (Path.Homotopic.trans_assoc _ _ _).trans
      ((Path.Homotopic.refl _).hcomp (ih hl.2))

def IsWord {a b : V} (p : Path (v a) (v b))  :=
  ∃ l : List (E × Bool), ∃ hl : Comb.IsPath src tgt l a b,
    Path.Homotopic p (realize src tgt v edge l hl)

theorem isWord_refl (a : V) : IsWord src tgt v edge (Path.refl (v a)) :=
  ⟨[], rfl, Path.Homotopic.refl _⟩

variable {src tgt v edge} in
theorem IsWord.trans {a b c : V} {p : Path (v a) (v b)} {q : Path (v b) (v c)}
    (hp : IsWord src tgt v edge p) (hq : IsWord src tgt v edge q) :
    IsWord src tgt v edge (p.trans q) := by
  obtain ⟨l, hl, hpl⟩ := hp
  obtain ⟨m, hm, hqm⟩ := hq
  exact ⟨l ++ m, hl.append hm,
    (hpl.hcomp hqm).trans (realize_append src tgt v edge l m hl hm)⟩

variable {src tgt v edge} in
theorem IsWord.of_homotopic {a b : V} {p q : Path (v a) (v b)}
    (hq : IsWord src tgt v edge q) (hpq : Path.Homotopic p q) :
    IsWord src tgt v edge p := by
  obtain ⟨l, hl, hq⟩ := hq
  exact ⟨l, hl, hpq.trans hq⟩





/-- An open-cover subdivision yields a finite edge word. Local connectors
may move subdivision points to vertices; no finiteness of the graph is used. -/
theorem isWord_of_open_cover {ι : Type} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)
    (a : X → V) (C : ∀ x, Path x (v (a x)))
    (hlocal : ∀ i {x y : X} (p : Path x y), Set.range p ⊆ U i →
      IsWord src tgt v edge (((C x).symm.trans p).trans (C y)))
    {x y : X} (p : Path x y) :
    IsWord src tgt v edge (((C x).symm.trans p).trans (C y)) := PathReplacement.of_open_cover v (IsWord src tgt v edge) U hU hcover a C
    (fun x => isWord_refl src tgt v edge (a x))
    (fun hp hq => hp.trans hq) (fun h hp => hp.of_homotopic h) hlocal p

end FiniteChains.ContinuousEdgeWords
