import Mathlib.Topology.Subpath
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import RequestProject.Tac


/-! A finite open-cover argument for replacing a path after moving its
vertices along specified connector paths. The result is an actual path and
an actual path homotopy; no fundamental-group surjectivity is assumed.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set

bwd

namespace FiniteChains.PathReplacement

variable {X : Type} [TopologicalSpace X]

theorem concat_conjugate (p a : Fin (n + 1) → X)
    (C : ∀ i, Path (p i) (a i))
    (F : ∀ i, Path (p i.castSucc) (p i.succ))
    (G : ∀ i : Fin n, Path (a i.castSucc) (a i.succ))
    (h : ∀ i, Path.Homotopic (((C i.castSucc).symm.trans (F i)).trans (C i.succ)) (G i)) :
    Path.Homotopic (((C 0).symm.trans (Path.concat p F)).trans (C (Fin.last n)))
      (Path.concat a G) := by
  induction n with
  | zero =>
    apply Path.Homotopic.Quotient.eq.mp
    simp
  | succ n ih =>
    have hi := Path.Homotopic.Quotient.eq.mpr
      (ih (p ∘ Fin.castSucc) (a ∘ Fin.castSucc) (C ·.castSucc)
        (F ·.castSucc) (G ·.castSucc) (by simp_all))
    have hj := Path.Homotopic.Quotient.eq.mpr (h (Fin.last n))
    apply Path.Homotopic.Quotient.eq.mp
    rw [Path.concat_succ, Path.concat_succ]
    grind

theorem concat_range_subset p
    (F : ∀ i : Fin n, Path (p i.castSucc) (p i.succ)) (A : Set X)
    (hp : p 0 ∈ A) (hF : ∀ i, Set.range (F i) ⊆ A) : Set.range (Path.concat p F) ⊆ A := by
  induction n with
  | zero =>
    simp_all
  | succ n ih =>
    simp [Path.concat_succ, Path.trans_range]
    simp_all

/-- Local replacements on an open cover concatenate to a replacement of
the entire path. Connectors are allowed to move subdivision vertices. -/
theorem replace_of_open_cover {ι : Type} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)
    A (a : X → X) (ha : ∀ x, a x ∈ A) (C : ∀ x, Path x (a x))
    (hlocal : ∀ i {x y} (p : Path x y), Set.range p ⊆ U i →
      ∃ q : Path (a x) (a y), Set.range q ⊆ A ∧
        Path.Homotopic (((C x).symm.trans p).trans (C y)) q)
    {x y} p :
    ∃ q : Path (a x) (a y), Set.range q ⊆ A ∧
      Path.Homotopic (((C x).symm.trans p).trans (C y)) q := by
  obtain ⟨t, ht0, htm, ⟨n, htn⟩, htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun i => p ⁻¹' U i) (fun i => (hU i).preimage p.continuous)
      (by intro s _; obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ _))
          aesop)
  let ts : Fin (n + 1) → I := fun i => t i.val
  let points : Fin (n + 1) → X := p ∘ ts
  let F : ∀ i : Fin n, Path (points i.castSucc) (points i.succ) :=
    fun i => p.subpath _ _
  have hloc (i : Fin n) : ∃ q : Path (a (points i.castSucc)) (a (points i.succ)),
      Set.range q ⊆ A ∧
      Path.Homotopic (((C _).symm.trans (F i)).trans (C _)) q := by
    obtain ⟨j, hj⟩ := htU i.val
    apply hlocal j _
    rw [show Set.range (F i) = p '' Set.Icc (t i.val) (t (i.val + 1)) from
      p.range_subpath_of_le _ _ (by aesop)]
    simp_all
  choose G hGA hG using hloc
  have hcat := concat_conjugate points _ (fun i => C _) F G hG
  have hsub := Path.Homotopic.concat_subpath p ts
  have hcat' :=
    ((Path.Homotopic.refl _).hcomp hsub.symm).hcomp (Path.Homotopic.refl _) |>.trans hcat
  have hp0 : points 0 = x := by grind
  have hp1 : points (Fin.last n) = y := by
    grind
  let q := (Path.concat (a ∘ points) G).cast (congrArg a hp0.symm) (congrArg a hp1.symm)
  refine ⟨q, ?_, ?_⟩
  · exact concat_range_subset (a ∘ points) G A (ha _) hGA
  · have ht0' : ts 0 = 0 := ht0
    have ht1' : ts (Fin.last n) = 1 := htn n le_rfl
    have hc0 : (C _).cast hp0.symm (congrArg a hp0.symm) = C x := by
      apply Path.ext
      funext s
      change C (points 0) s = C x s
      rw [hp0]
    have hc1 : (C _).cast hp1.symm (congrArg a hp1.symm) = C y := by
      apply Path.ext
      funext s
      change C (points (Fin.last n)) s = C y s
      rw [hp1]
    have hps : (p.subpath _ _).cast hp0.symm hp1.symm = p := by
      apply Path.ext
      funext s
      change p (Set.Icc.convexComb (ts 0) (ts (Fin.last n)) s) = p s
      simp_all
    have hc := hcat'.pathCast (congrArg a hp0.symm) (congrArg a hp1.symm)
    aesop
