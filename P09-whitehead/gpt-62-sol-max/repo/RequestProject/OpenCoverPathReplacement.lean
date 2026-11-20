module

public import RequestProject.TopologyPaths.OpenCoverPaths
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

@[expose] public section

/-! A finite open-cover argument for replacing a path after moving its
vertices along specified connector paths. The result is an actual path and
an actual path homotopy; no fundamental-group surjectivity is assumed.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PathReplacement

variable {X : Type} [TopologicalSpace X]

/-- A homotopy-invariant path property that is closed under concatenation
can be checked on subpaths lying in the members of an open cover. -/
theorem property_of_open_cover {ι V : Type} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)
    {v : V → X} (R : ∀ a b, Path (v a) (v b) → Prop)
    (hrefl : ∀ a, R a a (Path.refl (v a)))
    (htrans : ∀ {a b c} {p : Path (v a) (v b)} {q : Path (v b) (v c)},
      R a b p → R b c q → R a c (p.trans q))
    (hhom : ∀ {a b} {p q : Path (v a) (v b)}, Path.Homotopic p q → R a b q → R a b p)
    (a : X → V) (C : ∀ x, Path x (v (a x)))
    (hlocal : ∀ i {x y : X} (p : Path x y), Set.range p ⊆ U i →
      R (a x) (a y) (((C x).symm.trans p).trans (C y)))
    {x y : X} (p : Path x y) : R (a x) (a y) (((C x).symm.trans p).trans (C y)) := by
  let P {x y : X} (q : Path x y) := R (a x) (a y) (((C x).symm.trans q).trans (C y))
  refine OpenCoverPaths.path_induction U hU (fun x => mem_iUnion.mp (hcover (mem_univ x)))
    (@P) ?_ ?_ ?_ (fun q ⟨i, hi⟩ => hlocal i q hi) p
  · intro x
    apply hhom ?_ (hrefl (a x))
    exact ((Path.Homotopic.trans_refl (C x).symm).hcomp (Path.Homotopic.refl _)).trans
      (Path.Homotopic.symm_trans (C x))
  · intro x y z q r hq hr
    apply hhom ?_ (htrans hq hr)
    open Path.Homotopic.Quotient in
    exact eq.mp (by simp [mk_trans, mk_symm, ← trans_assoc (mk (C y))])
  · intro x y q r h hq
    exact hhom (((Path.Homotopic.refl _).hcomp h.symm).hcomp (Path.Homotopic.refl _)) hq

/-- Local replacements on an open cover concatenate to a replacement of
the entire path. Connectors are allowed to move subdivision vertices. -/
theorem replace_of_open_cover {ι : Type} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)
    (A : Set X) (a : X → X) (ha : ∀ x, a x ∈ A) (C : ∀ x, Path x (a x))
    (hlocal : ∀ i {x y : X} (p : Path x y), Set.range p ⊆ U i →
      ∃ q : Path (a x) (a y), Set.range q ⊆ A ∧
        Path.Homotopic (((C x).symm.trans p).trans (C y)) q)
    {x y : X} (p : Path x y) :
    ∃ q : Path (a x) (a y), Set.range q ⊆ A ∧
      Path.Homotopic (((C x).symm.trans p).trans (C y)) q := by
  refine property_of_open_cover U hU hcover (v := a)
    (fun x y p => ∃ q : Path (a x) (a y), Set.range q ⊆ A ∧ Path.Homotopic p q) ?_ ?_ ?_ id C hlocal p
  · exact fun x => ⟨_, by simpa [Path.refl_range] using ha x, Path.Homotopic.refl _⟩
  · rintro x y z p q ⟨p', hp', hp⟩ ⟨q', hq', hq⟩
    exact ⟨p'.trans q', by simpa only [Path.trans_range] using Set.union_subset hp' hq', hp.hcomp hq⟩
  · rintro x y p q h ⟨r, hr, hq⟩
    exact ⟨r, hr, h.trans hq⟩

end FiniteChains.PathReplacement
