module

public import RequestProject.CellComplex
public import RequestProject.OpenCoverPathReplacement

@[expose] public section

noncomputable section
open scoped Classical unitInterval
open Set

namespace FiniteChains.ContinuousEdgeWords

variable {V E X : Type} [TopologicalSpace X]
  (src tgt : E → V) (v : V → X) (edge : ∀ e, Path (v (src e)) (v (tgt e)))

def germPath : (g : E × Bool) → Path (v (Comb.germSrc src tgt g)) (v (Comb.germTgt src tgt g))
  | (e, true) => edge e
  | (e, false) => (edge e).symm

def realize : (l : List (E × Bool)) → {a b : V} →
    Comb.IsPath src tgt l a b → Path (v a) (v b)
  | [], a, _, h => (Path.refl (v a)).cast rfl (congrArg v h.symm)
  | g :: l, _, _, h =>
      ((germPath src tgt v edge g).cast (congrArg v h.1) rfl).trans (realize l h.2)

theorem realize_append (l m : List (E × Bool)) {a b c : V}
    (hl : Comb.IsPath src tgt l a b) (hm : Comb.IsPath src tgt m b c) :
    Path.Homotopic
      ((realize src tgt v edge l hl).trans (realize src tgt v edge m hm))
      (realize src tgt v edge (l ++ m) (hl.append hm)) := by
  induction l generalizing a with
  | nil => cases hl; exact Path.Homotopic.refl_trans _
  | cons g l ih =>
    exact (Path.Homotopic.trans_assoc _ _ _).trans ((Path.Homotopic.refl _).hcomp (ih hl.2))

def IsWord {a b : V} (p : Path (v a) (v b)) : Prop :=
  ∃ l : List (E × Bool), ∃ hl : Comb.IsPath src tgt l a b,
    Path.Homotopic p (realize src tgt v edge l hl)

variable {src tgt v edge} in
theorem IsWord.trans {a b c : V} {p : Path (v a) (v b)} {q : Path (v b) (v c)}
    (hp : IsWord src tgt v edge p) (hq : IsWord src tgt v edge q) :
    IsWord src tgt v edge (p.trans q) := by
  obtain ⟨l, hl, hpl⟩ := hp; obtain ⟨m, hm, hqm⟩ := hq
  exact ⟨l ++ m, hl.append hm, (hpl.hcomp hqm).trans (realize_append src tgt v edge l m hl hm)⟩

variable {src tgt v edge} in
theorem IsWord.of_homotopic {a b : V} {p q : Path (v a) (v b)}
    (hq : IsWord src tgt v edge q) (hpq : Path.Homotopic p q) :
    IsWord src tgt v edge p := by
  obtain ⟨l, hl, hq⟩ := hq; exact ⟨l, hl, hpq.trans hq⟩

variable {src tgt v edge} in
theorem IsWord.pathCast {a b a' b' : V} {p : Path (v a) (v b)}
    (hp : IsWord src tgt v edge p) (ha : a' = a) (hb : b' = b) :
    IsWord src tgt v edge (p.cast (congrArg v ha) (congrArg v hb)) := by
  subst a' b'; exact hp

theorem isWord_of_open_cover {ι : Type} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)
    (a : X → V) (C : ∀ x, Path x (v (a x)))
    (hlocal : ∀ i {x y : X} (p : Path x y), Set.range p ⊆ U i →
      IsWord src tgt v edge (((C x).symm.trans p).trans (C y)))
    {x y : X} (p : Path x y) :
    IsWord src tgt v edge (((C x).symm.trans p).trans (C y)) := by
  have hconcat {n : ℕ} (a : Fin (n + 1) → V)
      (G : ∀ i : Fin n, Path (v (a i.castSucc)) (v (a i.succ)))
      (hG : ∀ i, IsWord src tgt v edge (G i)) :
      IsWord src tgt v edge (Path.concat (v ∘ a) G) := by
    induction n with
    | zero => rw [Path.concat_zero]; exact ⟨[], rfl, Path.Homotopic.refl _⟩
    | succ n ih =>
      rw [Path.concat_succ]
      exact (ih (a ∘ Fin.castSucc) (fun i => G i.castSucc)
        (fun i => hG i.castSucc)).trans (hG (Fin.last n))
  obtain ⟨t, ht0, htm, ⟨n, htn⟩, htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun i => p ⁻¹' U i) (fun i => (hU i).preimage p.continuous)
      (fun s _ => by
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ (p s)))
        exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  let ts : Fin (n + 1) → I := fun i => t i.val
  let points : Fin (n + 1) → X := p ∘ ts
  let F (i : Fin n) : Path (points i.castSucc) (points i.succ) := p.subpath (ts i.castSucc) (ts i.succ)
  let G (i : Fin n) : Path (v (a (points i.castSucc))) (v (a (points i.succ))) :=
    ((C (points i.castSucc)).symm.trans (F i)).trans (C (points i.succ))
  have hG (i : Fin n) : IsWord src tgt v edge (G i) := by
    obtain ⟨j, hj⟩ := htU i.val
    refine hlocal j (F i) ?_
    rw [show Set.range (F i) = p '' Set.Icc (t i.val) (t (i.val + 1)) from
      p.range_subpath_of_le _ _ (htm (Nat.le_succ i.val))]
    rintro _ ⟨s, hs, rfl⟩; exact hj hs
  have hcat' : Path.Homotopic
      (((C (points 0)).symm.trans (p.subpath (ts 0) (ts (Fin.last n)))).trans
        (C (points (Fin.last n)))) (Path.concat (v ∘ a ∘ points) G) :=
    (((Path.Homotopic.refl _).hcomp (Path.Homotopic.concat_subpath p ts).symm).hcomp
      (Path.Homotopic.refl _)).trans
      (PathReplacement.concat_conjugate points (v ∘ a ∘ points)
        (fun i => C (points i)) F G fun _ => Path.Homotopic.refl _)
  have hp0 : points 0 = x := by change p (t 0) = x; rw [ht0, p.source]
  have hp1 : points (Fin.last n) = y := by change p (t n) = y; rw [htn n le_rfl, p.target]
  have hc := hcat'.pathCast (congrArg (v ∘ a) hp0.symm) (congrArg (v ∘ a) hp1.symm)
  rw [Path.cast_trans _ _ (congrArg (v ∘ a) hp0.symm) hp1.symm (congrArg (v ∘ a) hp1.symm),
    Path.cast_trans _ _ (congrArg (v ∘ a) hp0.symm) hp0.symm hp1.symm, Path.cast_symm,
    show (C (points 0)).cast hp0.symm (congrArg (v ∘ a) hp0.symm) = C x from
      Path.ext (funext fun s => by change C (points 0) s = C x s; rw [hp0]),
    show (p.subpath (ts 0) (ts (Fin.last n))).cast hp0.symm hp1.symm = p from
      Path.ext (funext fun s => by
        change p (Path.subpathAux (ts 0) (ts (Fin.last n)) s) = p s
        have ht0' : ts 0 = 0 := ht0
        have ht1' : ts (Fin.last n) = 1 := htn n le_rfl
        rw [ht0', ht1']
        exact congrArg p (Subtype.ext (by simp [Path.subpathAux]))),
    show (C (points (Fin.last n))).cast hp1.symm (congrArg (v ∘ a) hp1.symm) = C y from
      Path.ext (funext fun s => by change C (points (Fin.last n)) s = C y s; rw [hp1])] at hc
  exact ((hconcat (a ∘ points) G hG).pathCast
    (congrArg a hp0.symm) (congrArg a hp1.symm)).of_homotopic hc

end FiniteChains.ContinuousEdgeWords
