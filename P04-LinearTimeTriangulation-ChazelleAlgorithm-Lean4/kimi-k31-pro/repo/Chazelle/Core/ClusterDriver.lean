module

public import Chazelle.Core.ClusterSplitTail
public import Chazelle.Core.ClusterSplitCorrect
public import Chazelle.Core.ClusterStack
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# WP-I, part 35: the split driver

* `centroid_typed`: the face found by the climb is a centroid of the piece in the sense of
  `ClusterCentroid.lean` (good, no good child);
-/

namespace Chazelle.Core.Cluster

open Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

section centroid

variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face (a g) = g} {C : CoTree (starTree T a ha)}
  {R : BTree}

/-- Descendants are preorder intervals. -/
theorem desc_interval (hR : R.OK) (hRn : R.n = N) (hup : ∀ g : Fin N, R.up g = C.parent g)
    {pre slot : ℕ → ℕ} (hP : R.PreInv pre slot R.n) (g h : Fin N) :
    C.IsDesc h g ↔ pre g ≤ pre h ∧ pre h < pre g + (R.sub g).card := by
  rw [isDesc_iff_anc hup, hP.anc_iff hR (by rw [hRn]; exact g.2) (by rw [hRn]; exact h.2)]

/-- **The climb finds a centroid.** -/
theorem centroid_typed (hR : R.OK) (hRn : R.n = N) (hup : ∀ g : Fin N, R.up g = C.parent g)
    (hroot : R.root = (C.r0 : ℕ)) {pre slot : ℕ → ℕ} (hP : R.PreInv pre slot R.n)
    {first : Fin μ → Fin N} {firstN : ℕ → ℕ} (hfN : ∀ v : Fin μ, firstN v = first v)
    {act : ℕ → ℕ} {lo hi : ℕ} (hinj : Set.InjOn act (Finset.Ico lo hi))
    (hlt : ∀ v ∈ items act (lo, hi), v < μ)
    (hs : Sorted (fun i => pre (firstN (act i))) lo hi) {f : ℕ} (hf : f < N)
    (hres : (BTree.GdN pre (fun g => (R.sub g).card) (fun i => pre (firstN (act i))) lo hi
        (firstN (act (lo + (hi - lo) / 2))) ∧ f = firstN (act (lo + (hi - lo) / 2))) ∨
      ∃ x n, R.up^[n] (firstN (act (lo + (hi - lo) / 2))) = x ∧
        ¬ BTree.GdN pre (fun g => (R.sub g).card) (fun i => pre (firstN (act i))) lo hi x ∧
        BTree.GdN pre (fun g => (R.sub g).card) (fun i => pre (firstN (act i))) lo hi (R.up x) ∧
        f = R.up x)
    (hlh : lo < hi) :
    Good C (delta first a) (liftP (μ := μ) (F := F) (items act (lo, hi))) ⟨f, hf⟩ ∧
      ∀ g, g ≠ C.r0 → C.parent g = ⟨f, hf⟩ →
        ¬ Good C (delta first a) (liftP (μ := μ) (F := F) (items act (lo, hi))) g := by
  have hint := desc_interval hR hRn hup hP
  have hphi : ∀ i, lo ≤ i → i < hi → firstN (act i) < R.n ∧
      (fun i => pre (firstN (act i))) i = pre (firstN (act i)) := by
    intro i h1 h2
    have hv := hlt (act i) (mem_items.mpr ⟨i, h1, h2, rfl⟩)
    refine ⟨?_, rfl⟩
    rw [hfN ⟨act i, hv⟩, hRn]; exact Fin.isLt _
  have hmed : lo ≤ lo + (hi - lo) / 2 ∧ lo + (hi - lo) / 2 < hi := by omega
  have hy : firstN (act (lo + (hi - lo) / 2)) < R.n := (hphi _ hmed.1 hmed.2).1
  have hanc : ∀ z, z < R.n → BTree.GdN pre (fun g => (R.sub g).card)
      (fun i => pre (firstN (act i))) lo hi z → R.Anc z (firstN (act (lo + (hi - lo) / 2))) :=
    fun z hz hg => BTree.good_anc_median hR hP hs hphi hz hg
  obtain ⟨hgf, hch⟩ := BTree.centroid_of_climb hR hy hanc hres
  have hgood : ∀ z : Fin N, Good C (delta first a) (liftP (μ := μ) (F := F) (items act (lo, hi)))
      z ↔ BTree.GdN pre (fun g => (R.sub g).card) (fun i => pre (firstN (act i))) lo hi z :=
    fun z => good_iff hfN hint hinj hlt z
  refine ⟨(hgood _).mpr hgf, fun g hg hpar hgg => ?_⟩
  have hgr : (g : ℕ) ≠ R.root := by rw [hroot]; exact fun h => hg (Fin.ext h)
  have hpar' : R.par g = f := by
    have := hup g
    unfold BTree.up at this
    rw [ite_eq_right hgr, hpar] at this
    exact this
  exact hch g (by rw [hRn]; exact g.2) hgr hpar' ((hgood g).mp hgg)

end centroid

section marks

variable {μ N : ℕ} {F : Type} {M : CombMap (Fin μ) F (Fin N)} (T : SpanTree M)

open Classical in
/-- **One corner's marks** are its ancestors among the items of the segment. -/
theorem markStep_df {m : ℕ → ℕ} {S : SS} {lo hi lbot ltop : ℕ} {upT : ℕ → ℕ}
    (hup : ∀ v : Fin μ, upT v = T.parent v) {act : ℕ → ℕ}
    (hpos : ∀ x, x < μ → ((lo ≤ m (S.bPOS + x) ∧ m (S.bPOS + x) < hi) ↔ x ∈ items act (lo, hi)))
    (hwin : ∀ x : Fin μ, (x : ℕ) ∈ items act (lo, hi) → lbot ≤ T.level x ∧ T.level x ≤ ltop)
    (u : Fin μ) (hlev : m (S.bLEV + u) = T.level u) (x : Fin μ) :
    markStep m S lo hi lbot ltop upT u (S.bDF + x) =
      if (x : ℕ) ∈ items act (lo, hi) ∧ T.IsAnc x u then 1 else m (S.bDF + x) := by
  unfold markStep
  rw [hlev]
  by_cases hin : (x : ℕ) ∈ items act (lo, hi)
  · have hw := anc_window T hup x u (hwin x hin)
    by_cases hbt : lbot ≤ min (T.level u) ltop
    · rw [ite_eq_left hbt]
      unfold markMem
      have e : (∃ x', S.bDF + (x : ℕ) = S.bDF + x' ∧ lo ≤ m (S.bPOS + x') ∧
          m (S.bPOS + x') < hi ∧ ∃ i', i' < min (T.level u) ltop + 1 - lbot ∧
            x' = upT^[i'] (upT^[T.level u - min (T.level u) ltop] u)) ↔ T.IsAnc x u := by
        rw [← hw]
        constructor
        · rintro ⟨x', hx', -, -, i', hi', rfl⟩
          refine ⟨hbt, i', hi', ?_⟩
          have : (x : ℕ) = upT^[i'] (upT^[T.level u - min (T.level u) ltop] u) := by omega
          rw [this, ← Function.iterate_add_apply, Nat.add_comm]
        · rintro ⟨-, i', hi', h⟩
          refine ⟨x, rfl, (hpos x x.2).mpr hin |>.1, (hpos x x.2).mpr hin |>.2, i', hi', ?_⟩
          rw [h, ← Function.iterate_add_apply, Nat.add_comm]
      by_cases ha : T.IsAnc x u
      · rw [ite_eq_left (e.mpr ha), ite_eq_left ⟨hin, ha⟩]
      · rw [ite_eq_right (fun h => ha (e.mp h)), ite_eq_right (fun h => ha h.2)]
    · rw [ite_eq_right hbt, ite_eq_right]
      rintro ⟨-, ha⟩
      exact hbt (hw.mpr ha).1
  · have hno : ¬ ((x : ℕ) ∈ items act (lo, hi) ∧ T.IsAnc x u) := fun h => hin h.1
    rw [ite_eq_right hno]
    split_ifs
    · unfold markMem
      rw [ite_eq_right]
      rintro ⟨x', hx', h1, h2, -⟩
      have : x' = x := by omega
      subst this
      exact hin ((hpos x x.2).mp ⟨h1, h2⟩)
    · rfl

open Classical in
/-- **The marks of the three corners** are the separator `markN` among the items. -/
theorem marksF_df {a : F → Fin N} {m0 : ℕ → ℕ} {S : SS} {lo hi lbot ltop : ℕ}
    {upT : ℕ → ℕ} (hup : ∀ v : Fin μ, upT v = T.parent v) (hupl : ∀ x, x < S.μ → upT x < S.μ)
    (hSμ : S.μ = μ) {act : ℕ → ℕ}
    (hpos : ∀ x, x < μ → ((lo ≤ m0 (S.bPOS + x) ∧ m0 (S.bPOS + x) < hi) ↔
      x ∈ items act (lo, hi)))
    (hwin : ∀ x : Fin μ, (x : ℕ) ∈ items act (lo, hi) → lbot ≤ T.level x ∧ T.level x ≤ ltop)
    (hlev : ∀ v : Fin μ, m0 (S.bLEV + v) = T.level v)
    (hvert : ∀ d : Fin N, m0 (S.bVERT + d) = M.vert d)
    (hopp : ∀ d : Fin N, m0 (S.bOPP + d) = M.opp d)
    (hatt : ∀ d : Fin N, m0 (S.bATT + d) = a (M.face d))
    (hDF : ∀ y, y < μ → ¬ (S.bDF ≤ S.bPOS + y ∧ S.bPOS + y < S.bDF + S.μ) ∧
      ¬ (S.bDF ≤ S.bLEV + y ∧ S.bLEV + y < S.bDF + S.μ))
    (f : Fin N) (x : Fin μ) :
    marksF m0 S lo hi lbot ltop upT f (S.bDF + x) =
      if (x : ℕ) ∈ items act (lo, hi) ∧ markN T a f x then 1 else m0 (S.bDF + x) := by
  -- the memories of the marks agree with `m0` on `POS` and `LEV`
  have keep : ∀ (m : ℕ → ℕ) (u : ℕ), u < S.μ → (∀ y, y < μ → m (S.bPOS + y) = m0 (S.bPOS + y) ∧
      m (S.bLEV + y) = m0 (S.bLEV + y)) → ∀ y, y < μ →
      markStep m S lo hi lbot ltop upT u (S.bPOS + y) = m0 (S.bPOS + y) ∧
      markStep m S lo hi lbot ltop upT u (S.bLEV + y) = m0 (S.bLEV + y) := by
    intro m u hu hm y hy
    rw [markStep_other hupl hu (hDF y hy).1, markStep_other hupl hu (hDF y hy).2]
    exact hm y hy
  have hv0  := hvert f
  have hv1 : m0 (S.bVERT + m0 (S.bOPP + f)) = M.head f := by
    rwr [hopp f, hvert]
  have hv2 : m0 (S.bVERT + m0 (S.bATT + f)) = M.vert (a (M.face f)) := by rw [hatt f, hvert]
  unfold marksF
  rw [hv0, hv1, hv2]
  have k1 := keep m0 (M.vert f) (by rw [hSμ]; exact Fin.isLt _) (fun y _ => ⟨rfl, rfl⟩)
  have k2 := keep (markStep m0 S lo hi lbot ltop upT (M.vert f)) (M.head f)
    (by rw [hSμ]; exact Fin.isLt _) k1
  have hpos1 := fun y hy => (k1 y hy).1 ▸ hpos y hy
  have hpos2 := fun y hy => (k2 y hy).1 ▸ hpos y hy
  rw [markStep_df T hup hpos2 hwin _ (by rw [(k2 _ (Fin.isLt _)).2]; exact hlev _) x,
    markStep_df T hup hpos1 hwin _ (by rw [(k1 _ (Fin.isLt _)).2]; exact hlev _) x,
    markStep_df T hup hpos hwin _ (hlev _) x]
  have hmk : markN T a f x ↔ T.IsAnc x (M.vert f) ∨ T.IsAnc x (M.head f) ∨
      T.IsAnc x (M.vert (a (M.face f))) := by
    unfold markN
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩
  by_cases h1 : (x : ℕ) ∈ items act (lo, hi) ∧ T.IsAnc x (M.vert (a (M.face f)))
  · rw [ite_eq_left h1, ite_eq_left ⟨h1.1, hmk.mpr (Or.inr (Or.inr h1.2))⟩]
  · rw [ite_eq_right h1]
    by_cases h2 : (x : ℕ) ∈ items act (lo, hi) ∧ T.IsAnc x (M.head f)
    · rw [ite_eq_left h2, ite_eq_left ⟨h2.1, hmk.mpr (Or.inr (Or.inl h2.2))⟩]
    · rw [ite_eq_right h2]
      by_cases h3 : (x : ℕ) ∈ items act (lo, hi) ∧ T.IsAnc x (M.vert f)
      · rw [ite_eq_left h3, ite_eq_left ⟨h3.1, hmk.mpr (Or.inl h3.2)⟩]
      · rw [ite_eq_right h3, ite_eq_right]
        rintro ⟨hin, hm⟩
        rcases hmk.mp hm with h | h | h
        · exact h3 ⟨hin, h⟩
        · exact h2 ⟨hin, h⟩
        · exact h1 ⟨hin, h⟩

end marks

/-- `inClass` reads its arrays at a few points only. -/
theorem inClass_congr {sO sF fp pr sz sO' sF' fp' pr' sz' : ℕ → ℕ} {r0 X f κ : ℕ}
    (h1 : sO' X = sO X) (h2 : sF' (sO X) = sF (sO X))
    (h3 : fp' (sF (sO X)) = fp (sF (sO X))) (h4 : pr' (sF (sO X)) = pr (sF (sO X)))
    (h5 : sz' (sF (sO X)) = sz (sF (sO X))) (h6 : fp' f = fp f) (h7 : sO' (fp f) = sO (fp f))
    (h8 : pr' f = pr f) (h9 : sz' f = sz f) :
    inClass sO' sF' fp' pr' sz' r0 X f κ ↔ inClass sO sF fp pr sz r0 X f κ := by
  unfold inClass
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-! ## The static facts and the invariant of the driver -/

/-- The stack stored at `b`: entries `n - 1, …, 0` (top first). -/
def stkList (m : ℕ → ℕ) (b : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | n + 1 => (m (b + 2 * n), m (b + 2 * n + 1)) :: stkList m b n

section defs

variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  (T : SpanTree M)

/-- The slab of a vertex (a block of `k` levels shifted by `c`). -/
def slabN (c k x : ℕ) : ℕ := if h : x < μ then (T.level ⟨x, h⟩ + c) / k else 0

open Classical in
/-- The light levels. -/
noncomputable def Hset (c k : ℕ) : Finset ℕ :=
  (Finset.range μ).filter (fun x => ∃ h : x < μ, (T.level ⟨x, h⟩ + c) % k = k - 1)

/-- Adjacency along a dart. -/
def AdjN (M : CombMap (Fin μ) F (Fin N)) (x y : ℕ) : Prop := ∃ d : Fin N, (M.vert d : ℕ) = x ∧ (M.head d : ℕ) = y

end defs

section facts

variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] (M : CombMap (Fin μ) F (Fin N))
  (T : SpanTree M) (a : F → Fin N) (ha : ∀ g, M.face (a g) = g)
  (C : CoTree (starTree T a ha)) (R : BTree) (first : Fin μ → Fin N) (preE slot : ℕ → ℕ)
  (upT : ℕ → ℕ) (k c : ℕ)

/-- **The static facts** of the split driver: the arrays in memory hold the map, the trees and
the tables. -/
structure SFacts (S : SS) (A0 U W : ℕ) (m : ℕ → ℕ) : Prop where
  lay : S.Lay A0 U W
  hN : S.N = N
  hμ : S.μ = μ
  planar : M.Planar
  vert_first : ∀ v, M.vert (first v) = v
  vert : ∀ d : Fin N, m (S.bVERT + d) = M.vert d
  opp : ∀ d : Fin N, m (S.bOPP + d) = M.opp d
  first : ∀ v : Fin μ, m (S.bFIRST + v) = first v
  lev : ∀ v : Fin μ, m (S.bLEV + v) = T.level v
  lev_lt : ∀ v : Fin μ, T.level v < μ
  att : ∀ d : Fin N, m (S.bATT + d) = a (M.face d)
  fp : ∀ d : Fin N, m (S.bFP + d) = M.fperm d
  so : ∀ x, m (S.bSO + enc N x) = enc N ((star M).opp x)
  sf : ∀ x, m (S.bSF + enc N x) = ((star M).face x : ℕ)
  fpar : ∀ g : Fin N, g ≠ C.r0 → m (S.bFPAR + g) = enc N (C.fpar g)
  fpar_lt : ∀ g, g < N → m (S.bFPAR + g) < 3 * N
  r0 : (C.r0 : ℕ) = 0
  pre : ∀ g, g < N → m (S.bFPRE + g) = preE g
  sz : ∀ g, g < N → m (S.bFSZ + g) = (R.sub g).card
  R_ok : R.OK
  R_n : R.n = N
  R_up : ∀ g : Fin N, R.up g = C.parent g
  R_root : R.root = 0
  R_pre : R.PreInv preE slot R.n
  up_tab : ∀ j, j < S.L → ∀ g, g < N → m (S.bUP + j * N + g) = R.up^[2 ^ j] g
  upT_eq : ∀ v : Fin μ, upT v = T.parent v
  upT_lt : ∀ x, x < μ → upT x < μ
  pv : ∀ x, x < μ → m (S.bPV + x) = upT x
  upt_tab : ∀ j, j < S.L → ∀ x, x < μ → m (S.bUPT + j * μ + x) = upT^[2 ^ j] x
  pow : ∀ j, j < S.L → m (S.bPOW + j) = 2 ^ j
  pow_big : N + μ < 2 ^ S.L
  pow_U : 2 ^ S.L ≤ U
  L_pos : 0 < S.L
  half : ∀ w, w ≤ μ → m (S.bHALF + w) = w / 2
  win : ∀ v x : Fin μ, slabN T c k x = slabN T c k v →
    m (S.bLBOT + T.level v) ≤ T.level x ∧ T.level x ≤ m (S.bLTOP + T.level v)
  win_k : ∀ v : Fin μ, m (S.bLTOP + T.level v) + 1 - m (S.bLBOT + T.level v) ≤ k

end facts

section derived

variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face (a g) = g}
  {C : CoTree (starTree T a ha)} {R : BTree} {first : Fin μ → Fin N} {preE slot : ℕ → ℕ}
  {upT : ℕ → ℕ} {k c : ℕ} {W : ℕ}

theorem enc_surj {x : ℕ} (hx : x < 3 * N) : ∃ y, enc N y = x := by
  by_cases h1 : x < N
  · exact ⟨.inl ⟨x, h1⟩, rfl⟩
  · by_cases h2 : x < 2 * N
    · exact ⟨.inr (.inl ⟨x - N, by omega⟩), by sio only [enc]⟩
    · exact ⟨.inr (.inr ⟨x - 2 * N, by omega⟩), by sio only [enc]⟩

/-- The class-test memory facts. -/
theorem SFacts.cpMem {S : SS} {A0 U : ℕ} {m : ℕ → ℕ}
    (h : SFacts M T a ha C R first preE slot upT k c S A0 U W m) :
    CpMem m W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N := by
  have hL := h.lay
  have := hL.hSO; have := hL.hSF; have := hL.hFPAR; have := hL.hFPRE; have := hL.hFSZ
  have := hL.hNU; have := hL.hW; have := h.hN
  have hLU0 : 0 ≤ S.L * U := Nat.zero_le _
  refine ⟨by omega, by omega, by omega, by omega, by omega, fun x hx => ?_, fun x hx => ?_,
    fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨y, rfl⟩ := enc_surj (N := N) (x := x) (by omega)
    rw [h.so, h.hN]; exact enc_lt _
  · obtain ⟨y, rfl⟩ := enc_surj (N := N) (x := x) (by omega)
    rw [h.sf, h.hN]; exact Fin.isLt _
  · rw [h.hN]; exact h.fpar_lt g (by omega)
  · rw [h.pre g (by omega), h.sz g (by omega)]
    obtain ⟨hp1, hp2⟩ := h.R_ok.pos_spec (show g < R.n by rwo [h.R_n])
    have hb := h.R_pre.bound (R.pos g) hp1
    rw [hp2, h.R_n] at hb
    omega

/-- The marking memory facts. -/
theorem SFacts.markMem {S : SS} {A0 U : ℕ} {m : ℕ → ℕ}
    (h : SFacts M T a ha C R first preE slot upT k c S A0 U W m) :
    MarkMem m W S.bLEV S.bUPT S.bPOW S.L S.bPV S.bPOS S.bDF S.μ upT := by
  have hL := h.lay
  have := hL.hLEV; have := hL.hUPT; have := hL.hPOW; have := hL.hPV; have := hL.hPOS
  have := hL.hDF; have := hL.hμU; have := hL.hW; have := hL.hLU; have := h.hμ
  have := h.pow_big
  have hLU0 : S.L * S.μ ≤ S.L * U := Nat.mul_le_mul_left _ (by omega)
  have hSμ : S.μ = μ := h.hμ
  refine ⟨fun x hx => by rw [hSμ]; exact h.upT_lt x (by omega), fun x hx => h.pv x (by omega),
    fun j hj x hx => by rw [hSμ]; exact h.upt_tab j hj x (by omega), h.pow, fun x hx => ?_,
    fun x hx => ?_,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega⟩
  · have := h.lev ⟨x, by omega⟩; simp at this; rw [this]
    have := h.lev_lt ⟨x, by omega⟩; omega
  · have := h.lev ⟨x, by omega⟩; simp at this; rw [this]
    have := h.lev_lt ⟨x, by omega⟩; omega

end derived

section inv

variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] (M : CombMap (Fin μ) F (Fin N))
  (T : SpanTree M) (k c : ℕ)

/-- **The invariant of the split driver.** -/
structure DInv (S : SS) (m : ℕ → ℕ) (stk : List (ℕ × ℕ)) (fin : Finset (ℕ × ℕ))
    (D : Finset ℕ) (nsp : ℕ) : Prop where
  sinv : SInv μ k S.s (Hset T c k) (slabN T c k) (AdjN M) (fun i => m (S.bACT + i)) stk fin D nsp
  df : ∀ v, v < μ → (m (S.bDF + v) = 1 ↔ v ∈ D)
  Dlt : ∀ v ∈ D, v < μ
  pos_in : ∀ p, Lv stk fin p → ∀ i, p.1 ≤ i → i < p.2 → m (S.bPOS + m (S.bACT + i)) = i
  pos_out : ∀ w, w < μ → m (S.bPOS + w) = μ ∨ ∃ p, Lv stk fin p ∧ p.1 ≤ m (S.bPOS + w) ∧
    m (S.bPOS + w) < p.2 ∧ m (S.bACT + m (S.bPOS + w)) = w
  sorted : ∀ p ∈ stk, Sorted (keyOf m S.bACT S.bFIRST S.bFPRE) p.1 p.2
  stack : stk = stkList m S.bSTK stk.length
  rng : ∀ p, Lv stk fin p → p.2 ≤ μ

variable {M T k c}

omit [Fintype F] [DecidableEq F] in
/-- **The position test**: a vertex has its position in the live segment `p` iff it is an item
of `p`. -/
theorem DInv.pos_iff {S : SS} {m : ℕ → ℕ} {stk : List (ℕ × ℕ)} {fin : Finset (ℕ × ℕ)}
    {D : Finset ℕ} {nsp : ℕ} (hI : DInv M T k c S m stk fin D nsp) {p : ℕ × ℕ}
    (hp : Lv stk fin p) {x : ℕ} (hx : x < μ) :
    (p.1 ≤ m (S.bPOS + x) ∧ m (S.bPOS + x) < p.2) ↔ x ∈ items (fun i => m (S.bACT + i)) p := by
  constructor
  · rintro ⟨h1, h2⟩
    have hle := hI.rng p hp
    rcases hI.pos_out x hx with h | ⟨q, hq, h3, h4, h5⟩
    · omega
    · by_cases hqp : q = p
      · subst hqp; exact mem_items.mpr ⟨_, h3, h4, h5⟩
      · rcases hI.sinv.rdisj q p hq hp hqp with h | h | h | h <;> omega
  · intro h
    obtain ⟨i, h1, h2, rfl⟩ := mem_items.mp h
    rw [hI.pos_in p hp i h1 h2]
    exact ⟨h1, h2⟩

end inv

end

end Chazelle.Core.Cluster
