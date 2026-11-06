import Mathlib.Tactic

import Mathlib.Topology.Subpath
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! A finite open-cover argument for replacing a path after moving its
vertices along specified connector paths. The result is an actual path and
an actual path homotopy; no fundamental-group surjectivity is assumed.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PathReplacement

variable {X : Type} [TopologicalSpace X]

theorem concat_conjugate {n : ℕ} (p a : Fin (n + 1) → X)
    (C : ∀ i, Path (p i) (a i))
    (F : ∀ i : Fin n, Path (p i.castSucc) (p i.succ))
    (G : ∀ i : Fin n, Path (a i.castSucc) (a i.succ))
    (h : ∀ i, Path.Homotopic (((C i.castSucc).symm.trans (F i)).trans (C i.succ)) (G i)) :
    Path.Homotopic (((C 0).symm.trans (Path.concat p F)).trans (C (Fin.last n)))
      (Path.concat a G) := by
  induction n with
  | zero =>
    rw [Path.concat_zero, Path.concat_zero]
    apply Path.Homotopic.Quotient.eq.mp
    simp_all
  | succ n ih =>
    have hi := Path.Homotopic.Quotient.eq.mpr
      (ih (p ∘ Fin.castSucc) (a ∘ Fin.castSucc) (fun i => C i.castSucc)
        (fun i => F i.castSucc) (fun i => G i.castSucc) (fun i => h i.castSucc))
    have hj := Path.Homotopic.Quotient.eq.mpr (h (Fin.last n))
    apply Path.Homotopic.Quotient.eq.mp
    rw [Path.concat_succ, Path.concat_succ]
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm] at hi hj ⊢
    rw [← hi, ← hj]
    simp only [Path.Homotopic.Quotient.trans_assoc]
    rw [← Path.Homotopic.Quotient.trans_assoc
      (Path.Homotopic.Quotient.mk (C (Fin.castSucc (Fin.last n))))
      (Path.Homotopic.Quotient.mk (C (Fin.castSucc (Fin.last n)))).symm]
    simp



/-- Properties of vertex-based paths closed under homotopy and concatenation
can be checked on an open cover, after moving vertices along connectors. -/
theorem of_open_cover {V ι : Type} (v : V → X)
    (P : ∀ {a b : V}, Path (v a) (v b) → Prop)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : Set.univ ⊆ ⋃ i, U i) (a : X → V) (C : ∀ x, Path x (v (a x)))
    (hrefl : ∀ x, P (Path.refl (v (a x))))
    (htrans : ∀ {a b c} {p : Path (v a) (v b)} {q : Path (v b) (v c)},
      P p → P q → P (p.trans q))
    (hhom : ∀ {a b} {p q : Path (v a) (v b)}, Path.Homotopic p q → P q → P p)
    (hlocal : ∀ i {x y : X} (p : Path x y), Set.range p ⊆ U i →
      P (((C x).symm.trans p).trans (C y))) {x y : X} (p : Path x y) :
    P (((C x).symm.trans p).trans (C y)) := by
  obtain ⟨t, ht0, htm, ⟨n, htn⟩, htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun i => p ⁻¹' U i) (fun i => (hU i).preimage p.continuous)
      (by intro s _; obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ (p s)))
          exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  let ts : Fin (n + 1) → I := fun i => t i.val
  let points : Fin (n + 1) → X := p ∘ ts
  let F : ∀ i : Fin n, Path (points i.castSucc) (points i.succ) :=
    fun i => p.subpath (ts i.castSucc) (ts i.succ)
  let G : ∀ i : Fin n, Path (v (a (points i.castSucc))) (v (a (points i.succ))) :=
    fun i => ((C (points i.castSucc)).symm.trans (F i)).trans (C (points i.succ))
  have hG (i : Fin n) : P (G i) := by
    obtain ⟨j, hj⟩ := htU i.val
    apply hlocal j (F i)
    rw [show Set.range (F i) = p '' Set.Icc (t i.val) (t (i.val + 1)) from
      p.range_subpath_of_le _ _ (htm (Nat.le_succ i.val))]
    rintro _ ⟨s, hs, rfl⟩
    exact hj hs
  have cat {n : ℕ} (z : Fin (n + 1) → X)
      (g : ∀ i : Fin n, Path (v (a (z i.castSucc))) (v (a (z i.succ))))
      (hg : ∀ i, P (g i)) : P (Path.concat (v ∘ a ∘ z) g) := by
    induction n with
    | zero => rw [Path.concat_zero]; exact hrefl (z 0)
    | succ n ih =>
      rw [Path.concat_succ]
      exact htrans (ih (z ∘ Fin.castSucc) (fun i => g i.castSucc)
        (fun i => hg i.castSucc)) (hg (Fin.last n))
  have castP {a b a' b'} {q : Path (v a) (v b)} (hq : P q) (ha : a' = a) (hb : b' = b) :
      P (q.cast (congrArg v ha) (congrArg v hb)) := by subst a'; subst b'; exact hq
  have hcat := concat_conjugate points (v ∘ a ∘ points)
    (fun i => C (points i)) F G (fun _ => Path.Homotopic.refl _)
  have hsub := Path.Homotopic.concat_subpath p ts
  have hcat' := (((Path.Homotopic.refl _).hcomp hsub.symm).hcomp
    (Path.Homotopic.refl _)).trans hcat
  have hp0 : points 0 = x := by change p (t 0) = x; rw [ht0, p.source]
  have hp1 : points (Fin.last n) = y := by change p (t n) = y; rw [htn n le_rfl, p.target]
  have castC {x y : X} (h : x = y) :
      (C x).cast h.symm (congrArg (v ∘ a) h.symm) = C y := by subst y; rfl
  have hps : (p.subpath (ts 0) (ts (Fin.last n))).cast hp0.symm hp1.symm = p := by
    ext s
    change p (Path.subpathAux (ts 0) (ts (Fin.last n)) s) = p s
    have ht0' : ts 0 = 0 := ht0
    have ht1' : ts (Fin.last n) = 1 := htn n le_rfl
    rw [ht0', ht1']
    congr 1
    apply Subtype.ext
    simp [Path.subpathAux]
  have hc := hcat'.pathCast (congrArg (v ∘ a) hp0.symm) (congrArg (v ∘ a) hp1.symm)
  rw [Path.cast_trans _ _ (congrArg (v ∘ a) hp0.symm) hp1.symm (congrArg (v ∘ a) hp1.symm),
    Path.cast_trans _ _ (congrArg (v ∘ a) hp0.symm) hp0.symm hp1.symm,
    Path.cast_symm, castC hp0, hps, castC hp1] at hc
  exact hhom hc (castP (cat points G hG) (congrArg a hp0.symm) (congrArg a hp1.symm))

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
      Path.Homotopic (((C x).symm.trans p).trans (C y)) q := of_open_cover id
    (fun {x y} p => ∃ q : Path x y, Set.range q ⊆ A ∧ Path.Homotopic p q)
    U hU hcover a C
    (fun x => ⟨Path.refl _, by simpa using ha x, Path.Homotopic.refl _⟩)
    (by rintro _ _ _ _ _ ⟨p, hp, h⟩ ⟨q, hq, h'⟩
        exact ⟨p.trans q, by simpa only [Path.trans_range, Set.union_subset_iff] using ⟨hp, hq⟩,
          h.hcomp h'⟩)
    (by rintro _ _ _ _ h ⟨q, hq, h'⟩; exact ⟨q, hq, h.trans h'⟩)
    hlocal p

end FiniteChains.PathReplacement
