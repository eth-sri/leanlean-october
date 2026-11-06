module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ClusterDriver

/-!
# WP-I, part 36: one split step preserves the driver invariant

* `sel_iff`: the selections of the three class passes on the memory after the marks and the
  copy are the classes of `ClusterCentroid.lean` at the items of the segment;
-/

namespace Chazelle.Core.Cluster

open Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

section step

variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face (a g) = g}
  {C : CoTree (starTree T a ha)} {R : BTree} {first : Fin μ → Fin N} {preE slot upT : ℕ → ℕ} {k c W : ℕ}

/-- The class predicate of the star dart `t` of `f` at the vertex `v`, read from memory. -/
def QC (m : ℕ → ℕ) (S : SS) (T : SpanTree M) (a : F → Fin N) (f : Fin N) (t v : ℕ) : Prop :=
  ¬ markN T a f v ∧ inClass (fun x => m (S.bSO + x)) (fun x => m (S.bSF + x))
    (fun x => m (S.bFPAR + x)) (fun x => m (S.bFPRE + x)) (fun x => m (S.bFSZ + x)) 0
    (enc N (starDarts (M := M) f t)) f (m (S.bFPRE + m (S.bFIRST + v)))

set_option maxHeartbeats 1000000 in
open Classical in
/-- **The selections of the passes are the classes.** -/
theorem sel_iff {S : SS} {A0 U : ℕ} {m : ℕ → ℕ} {lo hi : ℕ} {rest : List (ℕ × ℕ)}
    {fin : Finset (ℕ × ℕ)} {D : Finset ℕ} {nsp : ℕ}
    (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W m)
    (hD : DInv M T k c S m ((lo, hi) :: rest) fin D nsp) {lbot ltop : ℕ}
    (hwin : ∀ x : Fin μ, (x : ℕ) ∈ items (fun i => m (S.bACT + i)) (lo, hi) →
      lbot ≤ T.level x ∧ T.level x ≤ ltop) (f : Fin N) :
    let m2 := copyF (marksF m S lo hi lbot ltop upT f) S lo hi
    (∀ i, lo ≤ i → i < hi → (SelI m2 S f f i ↔ QC m S T a f 0 (m (S.bACT + i)))) ∧
    (∀ i, lo ≤ i → i < hi → (SelI m2 S (2 * S.N + m2 (S.bFP + f)) f i ↔
      QC m S T a f 1 (m (S.bACT + i)))) ∧
    (∀ i, lo ≤ i → i < hi → (SelI m2 S (S.N + f) f i ↔ QC m S T a f 2 (m (S.bACT + i)))) := by
  intro m2
  have hL := hSF.lay
  have := hL.hFIRST; have := hL.hLEV; have := hL.hFP; have := hL.hATT; have := hL.hSO
  have := hL.hSF; have := hL.hFPAR; have := hL.hFSZ; have := hL.hFPRE; have := hL.hACT
  have := hL.hPOS; have := hL.hTMP; have := hL.hDF; have := hL.hμU; have := hL.hNU
  have hN := hSF.hN; have hμ := hSF.hμ
  have hlv : Lv ((lo, hi) :: rest) fin (lo, hi) := Or.inl List.mem_cons_self
  have hhi : hi ≤ μ := hD.rng _ hlv
  have hmk := fun (y : ℕ) (hy : y < μ) => marksF_df (m0 := m) (S := S) (lo := lo) (hi := hi)
    (lbot := lbot) (ltop := ltop) T hSF.upT_eq (fun x hx => by rw [hμ] at hx ⊢; exact hSF.upT_lt x hx)
    hμ (fun x hx => hD.pos_iff hlv hx) hwin hSF.lev hSF.vert hSF.opp hSF.att
    (fun y hy => ⟨by omega, by omega⟩) f ⟨y, hy⟩
  have hmo : ∀ x, ¬ (S.bDF ≤ x ∧ x < S.bDF + S.μ) → marksF m S lo hi lbot ltop upT f x = m x := by
    intro x hx
    have hup : ∀ x, x < S.μ → upT x < S.μ := fun x hx => by
      rw [hμ] at hx ⊢; exact hSF.upT_lt x hx
    have hvl : ∀ u : Fin μ, (u : ℕ) < S.μ := fun u => by omega
    unfold marksF
    rw [markStep_other hup (by rw [hSF.att, hSF.vert]; exact hvl _) hx,
      markStep_other hup (by rw [hSF.opp, hSF.vert]; exact hvl _) hx,
      markStep_other hup (by rw [hSF.vert]; exact hvl _) hx]
  have hm2 : ∀ x, ¬ (S.bDF ≤ x ∧ x < S.bDF + S.μ) → ¬ (S.bTMP + lo ≤ x ∧ x < S.bTMP + hi) →
      m2 x = m x := by
    grind [copyF]
  have htmp : ∀ i, lo ≤ i → i < hi → m2 (S.bTMP + i) = m (S.bACT + i) := by
    intro i h1 h2
    show copyF _ S lo hi _ = _
    unfold copyF
    grind
  have hm2d : ∀ x, ¬ (S.bTMP + lo ≤ x ∧ x < S.bTMP + hi) →
      m2 x = marksF m S lo hi lbot ltop upT f x := by
    grind [copyF]
  clear_value m2
  have hcp := hSF.cpMem
  -- the class reads
  have hcls : ∀ X, X < 3 * N → ∀ κ, (inClass (fun x => m2 (S.bSO + x)) (fun x => m2 (S.bSF + x))
      (fun x => m2 (S.bFPAR + x)) (fun x => m2 (S.bFPRE + x)) (fun x => m2 (S.bFSZ + x)) 0 X f κ ↔
      inClass (fun x => m (S.bSO + x)) (fun x => m (S.bSF + x))
      (fun x => m (S.bFPAR + x)) (fun x => m (S.bFPRE + x)) (fun x => m (S.bFSZ + x)) 0 X f κ) := by
    intro X hX κ
    have h1 := hcp.so_lt X (by omega)
    have h2 := hcp.sf_lt _ h1
    have h6 := hcp.fp_lt f (by omega)
    have hf : (f : ℕ) < N := f.2
    have hfU : (f : ℕ) + 1 ≤ U := by omega
    set y := m (S.bSO + X) with hy
    set z := m (S.bSF + y) with hz
    have e1 : m2 (S.bSO + X) = m (S.bSO + X) := hm2 _ (by omega) (by omega)
    have e2 : m2 (S.bSF + y) = m (S.bSF + y) := hm2 _ (by omega) (by omega)
    have e3 : m2 (S.bFPAR + z) = m (S.bFPAR + z) := hm2 _ (by omega) (by omega)
    have e4 : m2 (S.bFPRE + z) = m (S.bFPRE + z) := hm2 _ (by omega) (by omega)
    have e5 : m2 (S.bFSZ + z) = m (S.bFSZ + z) := hm2 _ (by omega) (by omega)
    set w := m (S.bFPAR + f) with hw
    generalize hfv : (f : ℕ) = fv at hfU hw
    have e6 : m2 (S.bFPAR + fv) = m (S.bFPAR + fv) := hm2 _ (by omega) (by omega)
    have e7 : m2 (S.bSO + w) = m (S.bSO + w) := hm2 _ (by omega) (by omega)
    have e8 : m2 (S.bFPRE + fv) = m (S.bFPRE + fv) := hm2 _ (by omega) (by omega)
    have e9 : m2 (S.bFSZ + fv) = m (S.bFSZ + fv) := hm2 _ (by omega) (by omega)
    subst hfv
    exact inClass_congr (sO := fun x => m (S.bSO + x)) (sF := fun x => m (S.bSF + x))
      (fp := fun x => m (S.bFPAR + x)) (pr := fun x => m (S.bFPRE + x))
      (sz := fun x => m (S.bFSZ + x)) (sO' := fun x => m2 (S.bSO + x))
      (sF' := fun x => m2 (S.bSF + x)) (fp' := fun x => m2 (S.bFPAR + x))
      (pr' := fun x => m2 (S.bFPRE + x)) (sz' := fun x => m2 (S.bFSZ + x)) e1 e2 e3 e4 e5 e6 e7 e8 e9
  have hsel : ∀ X, X < 3 * N → ∀ i, lo ≤ i → i < hi → (SelI m2 S X f i ↔
      (¬ markN T a f (m (S.bACT + i)) ∧ inClass (fun x => m (S.bSO + x)) (fun x => m (S.bSF + x))
      (fun x => m (S.bFPAR + x)) (fun x => m (S.bFPRE + x)) (fun x => m (S.bFSZ + x)) 0 X f
      (m (S.bFPRE + m (S.bFIRST + m (S.bACT + i)))))) := by
    intro X hX i h1 h2
    have hvi : m (S.bACT + i) ∈ items (fun i => m (S.bACT + i)) (lo, hi) :=
      mem_items.mpr ⟨i, h1, h2, rfl⟩
    have hv : m (S.bACT + i) < μ := hD.sinv.lt _ hlv _ hvi
    have hnD : m (S.bACT + i) ∉ D := (hD.sinv.off _ hlv _ hvi).1
    unfold SelI
    rw [htmp i h1 h2, hm2d (S.bDF + _) (by omega), hmk _ hv,
      hm2 (S.bFIRST + _) (by omega) (by omega)]
    have hfi : m (S.bFIRST + m (S.bACT + i)) < N := by
      have := hSF.first ⟨_, hv⟩; grind
    rw [hm2 (S.bFPRE + _) (by omega) (by omega), hcls X hX]
    constructor
    · rintro ⟨hne, hc⟩
      exact ⟨fun hmN => hne (by rw [ite_eq_left ⟨hvi, hmN⟩]), hc⟩
    · rintro ⟨hne, hc⟩
      refine ⟨?_, hc⟩
      rw [ite_eq_right (fun h => hne h.2)]
      intro h
      exact hnD ((hD.df _ hv).mp h)
  have hfp : m2 (S.bFP + f) = M.fperm f := by
    rw [hm2 _ (by omega) (by omega)]; exact hSF.fp f
  have hf : (f : ℕ) < N := f.2
  refine ⟨fun i h1 h2 => hsel f (by omega) i h1 h2, fun i h1 h2 => ?_,
    fun i h1 h2 => ?_⟩
  · 
    rw [hfp, hN]; exact hsel _ (by omega) i h1 h2
  · rw [hN]; exact hsel _ (by omega) i h1 h2

/-- The preorder interval test in memory. -/
theorem SFacts.hint {S : SS} {A0 U : ℕ} {m : ℕ → ℕ}
    (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W m) (g h : Fin N) :
    C.IsDesc h g ↔ m (S.bFPRE + g) ≤ m (S.bFPRE + h) ∧
      m (S.bFPRE + h) < m (S.bFPRE + g) + m (S.bFSZ + g) := by
  rw [hSF.pre g g.2, hSF.pre h h.2, hSF.sz g g.2]
  exact desc_interval hSF.R_ok hSF.R_n hSF.R_up hSF.R_pre g h

open Classical in
/-- **The classes of the split**, in terms of `QC`: they cover the unmarked items, are unique,
hold at most half of the items each and are not joined by an edge. -/
theorem cls_facts {S : SS} {A0 U : ℕ} {m : ℕ → ℕ} {lo hi : ℕ} {rest : List (ℕ × ℕ)}
    {fin : Finset (ℕ × ℕ)} {D : Finset ℕ} {nsp : ℕ}
    (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W m)
    (hD : DInv M T k c S m ((lo, hi) :: rest) fin D nsp) {f : Fin N}
    (hgood : Good C (delta first a)
      (liftP (μ := μ) (F := F) (items (fun i => m (S.bACT + i)) (lo, hi))) f)
    (hch : ∀ g, g ≠ C.r0 → C.parent g = f → ¬ Good C (delta first a)
      (liftP (μ := μ) (F := F) (items (fun i => m (S.bACT + i)) (lo, hi))) g) :
    (∀ i, lo ≤ i → i < hi → ¬ markN T a f (m (S.bACT + i)) →
      ∃ t, t < 3 ∧ QC m S T a f t (m (S.bACT + i))) ∧
    (∀ i, lo ≤ i → i < hi → ∀ t t', t < 3 → t' < 3 → QC m S T a f t (m (S.bACT + i)) →
      QC m S T a f t' (m (S.bACT + i)) → t = t') ∧
    (∀ t, t < 3 → 2 * cntS (fun i => QC m S T a f t (m (S.bACT + i))) lo hi ≤ hi - lo) ∧
    (∀ (d : Fin N) t t', t < 3 → t' < 3 →
      ((M.vert d : ℕ) ∈ items (fun i => m (S.bACT + i)) (lo, hi) ∧ QC m S T a f t (M.vert d)) →
      ((M.head d : ℕ) ∈ items (fun i => m (S.bACT + i)) (lo, hi) ∧ QC m S T a f t' (M.head d)) →
      t = t') := by
  have hlv : Lv ((lo, hi) :: rest) fin (lo, hi) := Or.inl List.mem_cons_self
  have hinj := hD.sinv.inj _ hlv
  have hlt := hD.sinv.lt _ hlv
  obtain ⟨h1, h2, h3, h4⟩ := split_math (T := T) (C := C) hSF.planar hSF.vert_first
    (firstN := fun v => m (S.bFIRST + v)) hSF.first
    (sopp := fun x => m (S.bSO + x)) (sface := fun x => m (S.bSF + x))
    (fparN := fun x => m (S.bFPAR + x)) (pre := fun x => m (S.bFPRE + x))
    (sz := fun x => m (S.bFSZ + x)) (r0 := 0) hSF.so hSF.sf hSF.r0.symm hSF.fpar hSF.hint
    hinj hlt hgood hch
  have hmem : ∀ i, lo ≤ i → i < hi → m (S.bACT + i) ∈ items (fun i => m (S.bACT + i)) (lo, hi) :=
    fun i a b => mem_items.mpr ⟨i, a, b, rfl⟩
  refine ⟨fun i a b hm => ?_, fun i a b t t' ht ht' q q' => ?_, fun t ht => ?_,
    fun d t t' ht ht' ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ => h4 d t t' ht ht' ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩⟩
  · obtain ⟨t, ht, hc⟩ := h1 _ (hmem i a b) hm
    exact ⟨t, ht, hm, hc⟩
  · exact h2 _ (hmem i a b) q.1 t t' ht ht' q.2 q'.2
  · have := h3 t ht
    rw [card_items_filter hinj] at this
    unfold cntS QC
    ram_grind

end step

end

end Chazelle.Core.Cluster
