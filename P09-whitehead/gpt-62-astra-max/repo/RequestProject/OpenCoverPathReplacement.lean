module

public import Mathlib.Topology.Subpath
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

variable {n : ℕ}

theorem concat_conjugate (p a : Fin (n + 1) → X)
    (C : ∀ i, Path (p i) (a i))
    (F : ∀ i : Fin n, Path (p i.castSucc) (p i.succ))
    (G : ∀ i : Fin n, Path (a i.castSucc) (a i.succ))
    (h : ∀ i, Path.Homotopic (((C i.castSucc).symm.trans (F i)).trans (C i.succ)) (G i)) :
    Path.Homotopic (((C 0).symm.trans (Path.concat p F)).trans (C (Fin.last n)))
      (Path.concat a G) := by
  induction n with
  | zero =>
    rw [Path.concat_zero, Path.concat_zero]
    change Path.Homotopic (((C 0).symm.trans (Path.refl (p 0))).trans (C 0))
      (Path.refl (a 0))
    apply Path.Homotopic.Quotient.eq.mp <;> simp_all
  | succ n ih =>
    have hi := Path.Homotopic.Quotient.eq.mpr
      (ih (p ∘ Fin.castSucc) (a ∘ Fin.castSucc) (fun i => C i.castSucc)
        (fun i => F i.castSucc) (fun i => G i.castSucc) (fun i => h i.castSucc))
    have hj := Path.Homotopic.Quotient.eq.mpr (h (Fin.last n))
    apply Path.Homotopic.Quotient.eq.mp
    rw [Path.concat_succ, Path.concat_succ]
    calc
      _ = Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk (((C 0).symm.trans
            (Path.concat (p ∘ Fin.castSucc) (fun i => F i.castSucc))).trans
              (C (Fin.castSucc (Fin.last n)))))
          (Path.Homotopic.Quotient.mk (((C (Fin.castSucc (Fin.last n))).symm.trans
            (F (Fin.last n))).trans (C (Fin.last (n + 1))))) := by
        simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
          Path.Homotopic.Quotient.trans_assoc]
        rw [← Path.Homotopic.Quotient.trans_assoc
            (Path.Homotopic.Quotient.mk (C (Fin.castSucc (Fin.last n))))
            (Path.Homotopic.Quotient.mk (C (Fin.castSucc (Fin.last n)))).symm
            ((Path.Homotopic.Quotient.mk (F (Fin.last n))).trans
              (Path.Homotopic.Quotient.mk (C (Fin.last (n + 1))))),
          Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]
      _ = Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk (Path.concat (a ∘ Fin.castSucc) (fun i => G i.castSucc)))
          (Path.Homotopic.Quotient.mk (G (Fin.last n))) := by
        congr 1
      _ = _ := rfl

/-- Patch local paths whose endpoints have been moved by connectors. Only closure
under the constant path and concatenation is required of the local representatives. -/
theorem assemble_of_open_cover {ι : Type} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)
    (a : X → X) (C : ∀ x, Path x (a x))
    (R : ∀ x y, Path (a x) (a y) → Prop)
    (hrefl : ∀ x, R x x (Path.refl _))
    (htrans : ∀ {x y z p q}, R x y p → R y z q → R x z (p.trans q))
    (hlocal : ∀ i {x y : X} (p : Path x y), Set.range p ⊆ U i →
      ∃ q : Path (a x) (a y), R x y q ∧
        Path.Homotopic (((C x).symm.trans p).trans (C y)) q)
    {x y : X} (p : Path x y) :
    ∃ q : Path (a x) (a y), R x y q ∧
      Path.Homotopic (((C x).symm.trans p).trans (C y)) q := by
  obtain ⟨t, ht0, htm, ⟨n, htn⟩, htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun i => p ⁻¹' U i) (fun i => (hU i).preimage p.continuous)
      (by intro s _; obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ (p s)))
          exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  let ts : Fin (n + 1) → I := fun i => t i.val
  let points := p ∘ ts
  let F : ∀ i : Fin n, Path (points i.castSucc) (points i.succ) :=
    fun i => p.subpath (ts i.castSucc) (ts i.succ)
  have hloc (i : Fin n) : ∃ q : Path (a (points i.castSucc)) (a (points i.succ)),
      R _ _ q ∧
      Path.Homotopic (((C (points i.castSucc)).symm.trans (F i)).trans (C (points i.succ))) q := by
    obtain ⟨j, hj⟩ := htU i.val
    apply hlocal j (F i)
    rw [show Set.range (F i) = p '' Set.Icc (t i.val) (t (i.val + 1)) from
      p.range_subpath_of_le _ _ (htm (Nat.le_succ i.val))] <;> grind
  choose G hGA hG using hloc
  have hcat := concat_conjugate points (a ∘ points) (fun i => C (points i)) F G hG
  have hsub := Path.Homotopic.concat_subpath p ts
  have hcat' :=
    ((Path.Homotopic.refl _).hcomp hsub.symm).hcomp (Path.Homotopic.refl _) |>.trans hcat
  have hp0 : points 0 = x := by change p (t 0) = x; simp_all
  have hp1 : points (Fin.last n) = y := by
    change p (t n) = y
    simp [htn, p.target]
  have assembled {m : ℕ} (pts : Fin (m + 1) → X)
      (segs : ∀ i : Fin m, Path (a (pts i.castSucc)) (a (pts i.succ)))
      (ok : ∀ i, R _ _ (segs i)) : R _ _ (Path.concat (a ∘ pts) segs) := by
    induction m with
    | zero => simpa using hrefl (pts 0)
    | succ m ih =>
      rw [Path.concat_succ]
      exact htrans (ih (pts ∘ Fin.castSucc) (fun i => segs i.castSucc) (fun i => ok i.castSucc)) (ok _)
  have transport {u v x y : X} {q : Path (a u) (a v)} (h : R u v q)
      (hx : x = u) (hy : y = v) : R x y (q.cast (congrArg a hx) (congrArg a hy)) := by
    subst_vars; exact h
  refine ⟨_, transport (assembled points G hGA) hp0.symm hp1.symm, ?_⟩
  have ht0' : ts 0 = 0 := ht0
  have ht1' : ts (Fin.last n) = 1 := htn n le_rfl
  have castC {x y : X} (h : x = y) : (C y).cast h (congrArg a h) = C x := by
    subst_vars; rfl
  have hps : (p.subpath (ts 0) (ts (Fin.last n))).cast hp0.symm hp1.symm = p := by
    apply Path.ext
    funext s
    change p (Set.Icc.convexComb (ts 0) (ts (Fin.last n)) s) = p s
    simp [ht0', ht1', Set.Icc.convexComb]
  have hc := hcat'.pathCast (congrArg a hp0.symm) (congrArg a hp1.symm)
  rw [Path.cast_trans _ _ (congrArg a hp0.symm) hp1.symm (congrArg a hp1.symm),
    Path.cast_trans _ _ (congrArg a hp0.symm) hp0.symm hp1.symm,
    Path.cast_symm, castC, hps, castC] at hc <;> assumption

theorem replace_of_open_cover {ι : Type} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)
    (A : Set X) (a : X → X) (ha : ∀ x, a x ∈ A) (C : ∀ x, Path x (a x))
    (hlocal : ∀ i {x y : X} (p : Path x y), Set.range p ⊆ U i →
      ∃ q : Path (a x) (a y), Set.range q ⊆ A ∧
        Path.Homotopic (((C x).symm.trans p).trans (C y)) q)
    {x y : X} (p : Path x y) :
    ∃ q : Path (a x) (a y), Set.range q ⊆ A ∧
      Path.Homotopic (((C x).symm.trans p).trans (C y)) q :=
  assemble_of_open_cover U hU hcover a C (fun _ _ q => Set.range q ⊆ A)
    (fun x => by simp [ha]) (fun hp hq => by simpa [Path.trans_range] using Set.union_subset hp hq)
    hlocal p

end FiniteChains.PathReplacement
