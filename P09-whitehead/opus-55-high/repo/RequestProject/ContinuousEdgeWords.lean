import RequestProject.CellComplex
import RequestProject.OpenCoverPathReplacement


/-! Actual continuous realizations of finite oriented edge words. The open
cover criterion retains a finite word, not merely a replacement continuous
path. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set

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


theorem realize_append l m {a b c}
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

def IsWord {a b : V} (p : Path (v a) (v b)) :=
  ∃ l : List (E × Bool), ∃ hl : Comb.IsPath src tgt l a b,
    p.Homotopic (realize src tgt v edge l hl)

theorem isWord_refl a : IsWord src tgt v edge (Path.refl (v a)) :=
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

variable {src tgt v edge} in
theorem IsWord.pathCast {a b a' b' : V} {p : Path (v a) (v b)}
    (hp : IsWord src tgt v edge p) (ha : a' = a) (hb : b' = b) :
    IsWord src tgt v edge (p.cast (congrArg v ha) (congrArg v hb)) := by
  aesop

theorem isWord_concat a
    (G : ∀ i : Fin n, Path (v (a i.castSucc)) (v (a i.succ)))
    (hG : ∀ i, IsWord src tgt v edge (G i)) :
    IsWord src tgt v edge (Path.concat (v ∘ a) G) := by
  induction n with
  | zero =>
    rw [Path.concat_zero]
    exact isWord_refl src tgt v edge _
  | succ n ih =>
    rw [Path.concat_succ]
    exact (ih _ _
      (by simp_all)).trans (by simp_all)

/-- An open-cover subdivision yields a finite edge word. Local connectors
may move subdivision points to vertices; no finiteness of the graph is used. -/
theorem isWord_of_open_cover {ι : Type} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)
    (a : X → V) (C : ∀ x, Path x (v (a x)))
    (hlocal : ∀ i {x y} (p : Path x y), Set.range p ⊆ U i →
      IsWord src tgt v edge (((C x).symm.trans p).trans (C y)))
    {x y} p :
    IsWord src tgt v edge (((C x).symm.trans p).trans (C y)) := by
  obtain ⟨t, ht0, htm, ⟨n, htn⟩, htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun i => p ⁻¹' U i) (fun i => (hU i).preimage p.continuous)
      (by intro s _; cases' Set.mem_iUnion.mp (hcover (Set.mem_univ _)) with i hi
          aesop)
  let ts : Fin (n + 1) → I := fun i => t i.val
  let points := p ∘ ts
  let F : ∀ i : Fin n, Path (points i.castSucc) (points i.succ) :=
    fun i => p.subpath _ _
  let G :=
    fun i => ((C _).symm.trans (F i)).trans (C _)
  have hG (i : Fin n) : IsWord src tgt v edge (G i) := by
    cases' htU i.val with j hj
    apply hlocal j _
    rw [show Set.range (F i) = p '' Set.Icc (t i.val) (t (i.val + 1)) from
      p.range_subpath_of_le _ _ (htm (Nat.le_succ i.val))]
    simp_all
  have hcat := PathReplacement.concat_conjugate points _
    (fun i => C _) F G (fun _ => Path.Homotopic.refl _)
  have hsub := Path.Homotopic.concat_subpath p ts
  have hcat' :=
    (((Path.Homotopic.refl _).hcomp hsub.symm).hcomp (Path.Homotopic.refl _)).trans hcat
  have hp0 : points 0 = x := by grind
  have hp1 : points (Fin.last n) = y := by
    grind
  have hw := (isWord_concat src tgt v edge (a ∘ points) G hG).pathCast
    (congrArg a hp0.symm) (congrArg a hp1.symm)
  have hc := hcat'.pathCast (congrArg (v ∘ a) hp0.symm) (congrArg (v ∘ a) hp1.symm)
  have hc0 : (C _).cast hp0.symm (by simp_all) = C x := by
    apply Path.ext
    funext s
    change C (points 0) s = C x s
    rw [hp0]
  have hc1 : (C _).cast hp1.symm (by simp_all) = C y := by
    apply Path.ext
    funext s
    change C (points (Fin.last n)) s = C y s
    rw [hp1]
  have hps : (p.subpath _ _).cast hp0.symm hp1.symm = p := by
    apply Path.ext
    funext s
    change p (Path.subpathAux (ts 0) (ts (Fin.last n)) s) = p s
    have ht0' : ts 0 = 0 := ht0
    have ht1' : ts (Fin.last n) = 1 := htn n le_rfl
    simp [ht0', ht1', Path.subpathAux]
  rw [Path.cast_trans _ _ _ hp1.symm _,
    Path.cast_trans _ _ _ hp0.symm hp1.symm,
    Path.cast_symm, hc0, hps, hc1] at hc
  exact hw.of_homotopic hc
