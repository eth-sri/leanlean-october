module

public import Chazelle.MacT
public import Chazelle.Core.NFDecompFinal2
public import Chazelle.Core.FactsAttach
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Logic.Relation
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Order.Interval.Finset.Nat
public import Chazelle.Core.SpecNF
public import Chazelle.Core.Lemma41Cover
public import Chazelle.Chain.Submap
public import Chazelle.Core.Facts2Trap

namespace Chazelle.Core.Dec
@[expose] public section
open Relation Finset

/-- The state of the search. -/
structure BS where
  /-- Visited regions (`1`). -/
  vis : ℕ → ℕ
  /-- The queue (the search order). -/
  ord : ℕ → ℕ
  /-- Parent regions. -/
  prg : ℕ → ℕ
  /-- Parent chords. -/
  pch : ℕ → ℕ
  /-- `1` iff the region is the `dn` endpoint of its parent chord. -/
  isdn : ℕ → ℕ
  /-- The child endpoint of each chord. -/
  chOf : ℕ → ℕ
  /-- The tail of the queue. -/
  tl : ℕ

/-- Scan chord `i` from region `r`: discover its other endpoint if it is new. -/
def bstep (up dn : ℕ → ℕ) (r : ℕ) (st : BS) (i : ℕ) : BS :=
  if st.vis ztnh = 1 then st
  else
    { vis := Function.update st.vis ztnh 1
      ord := Function.update st.ord st.tl ztnh
      prg := Function.update st.prg ztnh r
      pch := Function.update st.pch ztnh i
      isdn := Function.update st.isdn ztnh (if up i = r then 1 else 0)
      chOf := Function.update st.chOf i ztnh
      tl := st.tl + 1 }

/-- Dequeue the region at the head `q` and scan its exit chords. -/
def bouter (up dn : ℕ → ℕ) (lst : ℕ → List ℕ) (st : BS) (q : ℕ) : BS :=
  (lst ztbsx).foldl (bstep up dn ztbsx) st

/-- The facts on a discovered (non-root) region. -/
def Disc (K : ℕ) (up dn : ℕ → ℕ) (st : BS) (q : ℕ) : Prop :=
  st.ord q ≠ 0 ∧ st.pch ztbsx < K ∧ (∃ q', q' < q ∧ st.prg ztbsx = st.ord q') ∧
    ((up ztxos = st.prg ztbsx ∧ dn ztxos = st.ord q) ∨
      (up ztxos = st.ord q ∧ dn ztxos = st.prg ztbsx)) ∧
    (st.isdn ztbsx = 1 ↔ dn ztxos = st.ord q) ∧
    st.chOf ztxos = st.ord q

/-- **The search invariant** with head `h`; `done` lists the chords already scanned from the
region at the head. -/
structure BInv (R K : ℕ) (up dn : ℕ → ℕ) (lst : ℕ → List ℕ) (h : ℕ) (done : List ℕ) (st : BS) :
    Prop where
  tl_pos : 1 ≤ st.tl
  tl_le : st.tl ≤ R
  h_lt : h < st.tl ∨ (h = st.tl ∧ done = [])
  ord_lt : ∀ q, q < st.tl → st.ord q < R ∧ st.vis ztbsx = 1
  ord_inj : ∀ q q', q < st.tl → q' < st.tl → st.ord q = st.ord q' → q = q'
  vis_ord : ∀ r, r < R → st.vis r = 1 → ∃ q, q < st.tl ∧ st.ord q = r
  root : st.ord 0 = 0
  disc : ∀ q, 0 < q → q < st.tl → Disc K up dn st q
  closed : ∀ q, q < h → ∀ i ∈ lst ztbsx, st.vis ztwha = 1 ∧ st.vis ztvpf = 1
  closed_cur : ∀ i ∈ done, st.vis ztwha = 1 ∧ st.vis ztvpf = 1
section bfs
variable {R K : ℕ} {up dn : ℕ → ℕ} {lst : ℕ → List ℕ}
variable (hends : ∀ i, i < K → up i < R ∧ dn i < R ∧ up i ≠ dn i)
variable (hlists : ∀ r, r < R → ∀ i, i ∈ lst r ↔ i < K ∧ (up i = r ∨ dn i = r))
include hends hlists

/-- The invariant at the start, for any state with only the root visited and queued. -/
theorem binv_start (hR : 1 ≤ R) {st : BS} (hv : ∀ r, r < R → st.vis r = if r = 0 then 1 else 0)
    (ho : st.ord 0 = 0) (ht : st.tl = 1) : BInv R K up dn lst 0 [] st where
  tl_pos := by_omega
  tl_le := by_omega
  h_lt := by_omega
  ord_lt q hq := by
    grind
  ord_inj q q' hq hq' _ := by_omega
  vis_ord r hr hvr := by
    simp_all
  root := ho
  disc q hq hq' := by_omega
  closed q hq := by_omega
  closed_cur i hi := by_simp_all
variable {h : ℕ} {st : BS}
/-- One scan step preserves the invariant (the scanned chord is added to `done`). -/
theorem bstep_inv {done : List ℕ} {st : BS} (hI : BInv R K up dn lst h done st)
    (hh : h < st.tl) {i : ℕ} (hi : i ∈ lst ztddm) :
    BInv R K up dn lst h (i :: done) (bstep up dn ztddm st i) := by
  obtain ⟨hrR, hrv⟩ := hI.ord_lt h hh
  zujnb
  obtain ⟨hiK, hir⟩ := (hlists r hrR i).1 hi
  obtain ⟨hu, hd, hne⟩ := hends i hiK
  zuend

  -- the two endpoints are `r` and `s`
  have hpair : (up i = r ∧ dn i = s) ∨ (up i = s ∧ dn i = r) := by
    grind
  unfold bstep
  rw [← hsdef]
  by_cases hvs : st.vis s = 1
  · rw [ite_eq_left hvs]
    refine { hI with h_lt := Or.inl hh, closed_cur := ?_ }
    intro i' hi'
    zujco
    · grind
    · exact hI.closed_cur i' hi'
  · rw [ite_eq_right hvs]
    -- `s` is new
    have hsnew : ∀ q, q < st.tl → st.ord q ≠ s := fun q hq e => hvs (e ▸ (hI.ord_lt q hq).2)
    have hsr := by_omega
    have hs0 : ztppw := fun e => hsnew 0 hI.tl_pos (hI.root.trans e.symm)
    have htlR : st.tl < R := by
      -- the queue holds `tl` distinct regions other than `s`
      have himg : ((range st.tl).image st.ord) ⊆ (range R).erase s := by
        zucdk
        rw [Finset.mem_image] at hw
        obtain ⟨q, hq, rfl⟩ := hw
        rw [Finset.mem_range] at hq
        exact Finset.mem_erase.2 ⟨by_simp_all, Finset.mem_range.2 (hI.ord_lt q hq).1⟩
      zulju
      rw [Finset.card_image_of_injOn (fun a ha b hb e => hI.ord_inj a b
        ztpyu ztpyv e), Finset.card_range,
        Finset.card_erase_of_mem (Finset.mem_range.2 hsR), Finset.card_range] at hc
      grind
    -- the chord `i` is no parent chord yet
    have hinew : ∀ q, 0 < q → q < st.tl → st.pch ztbsx ≠ i := by
      intro q hq0 hq e
      obtain ⟨-, -, ⟨q', hq', hpq⟩, hends', -, -⟩ := hI.disc q hq0 hq
      grind
    have hord_old : ∀ q, q < st.tl → Function.update st.ord st.tl s q = st.ord q :=
      by grind
    constructor
    · simp
    · grind
    · grind
    · zuco
      dsimp only at hq ⊢
      zujtt
      · grind
      · zuiab
        rw [hord_old q hq']
        refine ⟨(hI.ord_lt q hq').1, ?_⟩
        rw [Function.update_of_ne by_grind]
        exact (hI.ord_lt q hq').2
    · zukjs
      dsimp only at hq hq' e
      by_cases h1 : q = st.tl <;> by_cases h2 : q' = st.tl
      · omega
      · grind
      · grind
      · rw [hord_old q by_omega, hord_old q' by_omega] at e
        exact hI.ord_inj q q' by_omega by_omega e
    · intro v hv hvv
      dsimp only at hvv ⊢
      by_cases hvs' : v = s
      · exact ⟨st.tl, by_omega, by_grind⟩
      · rw [Function.update_of_ne hvs'] at hvv
        obtain ⟨q, hq, e⟩ := hI.vis_ord v hv hvv
        grind
    · zubvt
      rw [hord_old 0 hI.tl_pos]; exact hI.root
    · intro q hq0 hq
      dsimp only at hq
      zujtt
      · subst hqt
        unfold Disc
        zubvt
        simp only [Function.update_self]
        grind
      · zuiab
        obtain ⟨d1, d2, ⟨q', hq'', d3⟩, d4, d5, d6⟩ := hI.disc q hq0 hq'
        have hne' := hsnew q hq'
        unfold Disc
        zubvt
        rw [hord_old q hq', Function.update_of_ne hne', Function.update_of_ne hne',
          Function.update_of_ne hne', Function.update_of_ne by_grind]
        grind
    · intro q hq i' hi'
      dsimp only at hi' ⊢
      rw [hord_old q by_omega] at hi'
      obtain ⟨c1, c2⟩ := hI.closed q hq i' hi'
      grind
    · intro i' hi'
      zubvt
      have hvis : ∀ v, st.vis v = 1 → Function.update st.vis s 1 v = 1 := by
        grind
      zujco
      · grind
      · obtain ⟨c1, c2⟩ := hI.closed_cur i' hi'
        grind

/-- A scan never changes the queue up to the old tail, nor the tail downwards. -/
theorem bstep_mono (r : ℕ) (st : BS) (i : ℕ) :
    st.tl ≤ (bstep up dn r st i).tl ∧
      ∀ q, q < st.tl → (bstep up dn r st i).ord q = st.ord q := by
  unfold bstep
  by_cases hv : st.vis ztnh = 1
  · simp_all
  · zulql
    grind
theorem fold_mono (r : ℕ) (l : List ℕ) (st : BS) :
    st.tl ≤ (l.foldl ztlgj st).tl ∧
      ∀ q, q < st.tl → (l.foldl ztlgj st).ord q = st.ord q := by
  induction l generalizing st with
  | nil => exact by_simp_all
  | cons i l ih =>
    zumlj
    obtain ⟨a1, a2⟩ := bstep_mono hends hlists r st i
    obtain ⟨b1, b2⟩ := ih _
    exact ⟨a1.trans b1, by_grind⟩

/-- Scanning a prefix of the list of the head region. -/
theorem fold_inv (hh : h < st.tl) :
    ∀ (l done : List ℕ), (∀ i ∈ l, i ∈ lst ztddm) → BInv R K up dn lst h done st →
      BInv R K up dn lst h (l.reverse ++ done) (l.foldl ztzkq st) := by
  intro l
  induction l generalizing st with
  | nil => intro done _ hI; simpa using hI
  | cons i l ih =>
    intro done hl hI
    zumlj
    have h1 := bstep_inv hends hlists hI hh (hl i (List.mem_cons_self))
    obtain ⟨m1, m2⟩ := bstep_mono hends hlists _ st i
    have hord : (bstep up dn ztddm st i).ord h = st.ord h := m2 h hh
    have := ih by_omega _
      by_simp_all h1
    rw [hord] at this
    simpa [List.reverse_cons, List.append_assoc] using this

/-- **Dequeuing one region** preserves the invariant (with the next head). -/
theorem bouter_inv (hI : BInv R K up dn lst h [] st) (hh : h < st.tl) :
    BInv R K up dn lst ztgn [] ztoze := by
  have hI' := fold_inv hends hlists hh _ [] (fun _ hi => hi) hI
  rw [List.append_nil] at hI'
  obtain ⟨m1, m2⟩ := fold_mono hends hlists ztddm (lst ztddm) st
  unfold bouter
  set st' := (lst ztddm).foldl ztzkq st with hst'
  have hord : st'.ord h = st.ord h := by_simp_all
  refine { hI' with h_lt := ?_, closed := ?_, closed_cur := by_simp_all }
  · grind
  · intro q hq i hi
    by_cases e : q = h
    · zugig
      rw [hord] at hi
      exact hI'.closed_cur i (List.mem_reverse.2 hi)
    · exact hI'.closed q by_omega i hi
variable (hcount : R = K + 1)
variable (hconn : ∀ r, r < R → ReflTransGen (fun a b => ∃ i, i < K ∧
    (up i = a ∧ dn i = b ∨ up i = b ∧ dn i = a)) 0 r)
include hcount hconn

/-- **The end of the search**: with the queue exhausted, every region is queued. -/
theorem bfs_all (hI : BInv R K up dn lst st.tl [] st) : st.tl = R := by
  -- every region is visited
  have hvis : ztlbz := by
    zuz
    have := hconn r hr
    induction this with
    | refl => have := hI.ord_lt 0 hI.tl_pos; rw [hI.root] at this; exact this.2
    | tail hab hbc ih =>
      zurd

      have hmem : ztbacz := by
        grind
      zubtx

      · simp_all
      · simp_all
  -- so the queue holds all regions
  have himg : range R ⊆ (range st.tl).image st.ord := by
    zuz
    zudtk
    obtain ⟨q, hq, e⟩ := hI.vis_ord r hr (hvis r hr)
    grind
  zulju
  rw [Finset.card_range, Finset.card_image_of_injOn (fun a ha b hb e => hI.ord_inj a b
    ztpyu ztpyv e), Finset.card_range] at hc
  have := hI.tl_le
  omega

/-- With the queue exhausted, every region is in the queue. -/
theorem bfs_cover (hI : BInv R K up dn lst st.tl [] st) :
    ∀ r, r < R → ∃ q, q < st.tl ∧ st.ord q = r := by
  have hvis : ztlbz := by
    zuz
    have := hconn r hr
    induction this with
    | refl => have := hI.ord_lt 0 hI.tl_pos; rw [hI.root] at this; exact this.2
    | tail hab hbc ih =>
      zurd

      have hmem : ztbacz := by
        grind
      zubtx

      · simp_all
      · simp_all
  exact fun r hr => hI.vis_ord r hr by_simp_all
open Classical in
/-- The position of a region in the search order. -/
noncomputable def bpos (st : BS) (r : ℕ) : ℕ :=
  if h : ∃ q, q < st.tl ∧ st.ord q = r then Nat.find h else 0

/-- **The search establishes the rooted tree**, the child endpoints and the side bits. -/
theorem bfs_rooted (hI : BInv R K up dn lst st.tl [] st) :
    Rooted R K up dn st.ord (bpos st) st.prg st.pch ∧
      (∀ e, e < K → st.chOf e < R ∧ st.chOf e ≠ 0 ∧ st.pch (st.chOf e) = e) ∧
      (∀ s, s < R → s ≠ 0 → ztyfs) := by
  classical
  have htl := bfs_all hends hlists hcount hconn hI
  have hcov := bfs_cover hends hlists hcount hconn hI
  -- positions
  have hposs : ∀ r, r < R → bpos st r < st.tl ∧ st.ord (bpos st r) = r := by
    zuz
    have hex : ∃ q, q < st.tl ∧ st.ord q = r := by_simp_all
    unfold bpos
    grind
  have hpos_ord : ∀ q, q < R → bpos st ztbsx = q := by
    zuco
    have h1 := hposs _ (hI.ord_lt q by_omega).1
    exact hI.ord_inj _ _ h1.1 by_omega h1.2
  -- a non-root region and its discovery facts
  have hdisc : ∀ s, s < R → s ≠ 0 → Disc K up dn st zttgy := by
    zujbm
    obtain ⟨p1, p2⟩ := hposs s hs
    have hp0 : 0 < bpos st s := by
      rcases Nat.eq_zero_or_pos zttgy with e | e
      · rw [e, hI.root] at p2; omega
      omega
    exact hI.disc _ hp0 p1
  have hprg : ∀ s, s < R → s ≠ 0 → st.prg s < R ∧ bpos st (st.prg s) < bpos st s := by
    zujbm
    obtain ⟨-, -, ⟨q', hq', hpq⟩, -, -, -⟩ := hdisc s hs hs0
    rw [(hposs s hs).2] at hpq
    have hq'R : q' < R := by_grind
    refine ⟨by rw [hpq]; exact (hI.ord_lt q' by_omega).1, ?_⟩
    grind
  have hdisc' : ∀ s, s < R → s ≠ 0 → st.pch s < K ∧
      ((up ztgme = st.prg s ∧ dn ztgme = s) ∨ (up ztgme = s ∧ dn ztgme = st.prg s)) ∧
      ztyfs ∧ st.chOf ztgme = s := by
    zujbm
    obtain ⟨-, d2, -, d4, d5, d6⟩ := hdisc s hs hs0
    rw [(hposs s hs).2] at d2 d4 d5 d6
    omega
  -- parent chords are injective
  have hinj : ∀ s s', s < R → s' < R → s ≠ 0 → s' ≠ 0 → st.pch s = st.pch s' → s = s' := by
    grind
  -- so they are onto the chords
  have hsurj : ∀ i, i < K → ∃ s, s < R ∧ s ≠ 0 ∧ st.pch s = i := by
    have himg : ((range R).erase 0).image st.pch = range K := by
      apply Finset.eq_of_subset_of_card_le
      · zug
        zugby
        obtain ⟨s, hs, rfl⟩ := hi
        grind
      · rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem by_grind,
          Finset.card_range, Finset.card_range]
        · omega
        · zukiz
          simp only [Finset.coe_erase, Finset.coe_range, Set.mem_sdiff, Set.mem_Iio,
            Set.mem_singleton_iff] at ha hb
          grind
    zug
    have : i ∈ ((range R).erase 0).image st.pch := by_grind
    rw [Finset.mem_image] at this
    obtain ⟨s, hs, e⟩ := this
    rw [Finset.mem_erase, Finset.mem_range] at hs
    grind
  refine ⟨⟨hcount, fun q hq => (hI.ord_lt q by_omega).1, fun r hr => by
      grind, by_grind, hpos_ord, hI.root,
      by grind, by_grind,
      by grind, fun s hs h0 => (hdisc' s hs h0).2.1, hsurj,
      by grind⟩, ?_, by_grind⟩
  zubre
  obtain ⟨s, hs, h0, rfl⟩ := hsurj e he
  rw [(hdisc' s hs h0).2.2.2]
  zulyc
end bfs
end
end Chazelle.Core.Dec
namespace Chazelle.Separator
@[expose] public section
open Equiv Relation
section PermLemmas
variable {X Y Z : Type*}

/-- **Following an orbit.**  Let `P` be a region and `t` a target in the `π`-cycle of `z ∈ P`.
If, at every point `y ∈ P` other than `t`, the permutation `ψ` acts (through `ι`) like `π` and
`π y` stays in `P`, then `ι z` and `ι t` lie in the same `ψ`-cycle. -/
theorem sameCycle_follow [Finite X] (π : Perm X) (ψ : Perm Y) (ι : X → Y) (P : X → Prop)
    {z t : X} (hz : P z) (hzt : π.SameCycle z t)
    (h : ∀ y, P y → y ≠ t → ψ ztwif = ι ztwij ∧ P ztwij) : ψ.SameCycle ztwig (ι t) := by
  classical
  have hex : ∃ k, ztkhy z = t := hzt.exists_nat_pow_eq
  have hmin : ∀ j < Nat.find hex, ztkhx z ≠ t := by_simp_all
  have key : ∀ j ≤ Nat.find hex, P ztbaiw ∧ (ψ ^ j) ztwig = ι ztbaiw := by
    zujbf
    induction j with
    | zero => intro _; simp [hz]
    | succ j ih =>
      intro hj
      obtain ⟨hP, hψ⟩ := ih by_omega
      obtain ⟨h1, h2⟩ := h _ hP by_simp_all
      zujx
      · zunaz; exact h2
      · rw [pow_succ', Perm.mul_apply, hψ, h1, pow_succ', Perm.mul_apply]
  refine ⟨(Nat.find hex : ℤ), ?_⟩
  rw [zpow_natCast, (key _ le_rfl).2, Nat.find_spec hex]

/-- **Stepwise transfer.**  If each point `ι x` is in the same `ψ`-cycle as `ι (π x)`, then
`π`-cycles map into `ψ`-cycles. -/
theorem sameCycle_of_step [Finite X] (π : Perm X) (ψ : Perm Y) (ι : X → Y)
    (h : ∀ x, ψ.SameCycle ztwie (ι ztwii)) {x y : X} (hxy : π.SameCycle x y) :
    ψ.SameCycle ztwie ztwif := by
  obtain ⟨k, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction k with
  | zero => simpa using Perm.SameCycle.refl ψ _
  | succ k ih => zunaz; exact ih.trans (h _)

/-- A function invariant under `π` is constant on `π`-cycles. -/
theorem eq_of_sameCycle [Finite X] (π : Perm X) (f : X → Z) (hf : ∀ x, f ztwii = f x)
    {x y : X} (h : π.SameCycle x y) : f x = f y := by
  zubpg

  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Perm.mul_apply, hf, ih]

/-- A set closed under `π` is closed under `π.SameCycle`. -/
theorem mem_of_sameCycle [Finite X] (π : Perm X) (S : Set X) (hS : ∀ x ∈ S, π x ∈ S)
    {x y : X} (h : π.SameCycle x y) (hx : x ∈ S) : y ∈ S := by
  zubpg

  induction k with
  | zero => simpa using hx
  | succ k ih => zunaz; exact hS _ ih

/-- A set closed under `π` is closed under `π⁻¹` (finite case). -/
theorem mem_of_inv_mem [Finite X] (π : Perm X) (S : Set X) (hS : ∀ x ∈ S, π x ∈ S)
    {x : X} (hx : x ∈ S) : π⁻¹ x ∈ S :=
  mem_of_sameCycle π S hS ztluz hx
end PermLemmas
section Merge
variable {X : Type*} [Finite X] [DecidableEq X]

/-- **Merging two cycles.**  If `a` and `b` lie in different cycles of `π`, the cycles of
`π * swap a b` are those of `π`, except that the cycles of `a` and `b` are merged. -/
theorem sameCycle_mul_swap_iff (π : Perm X) {a b : X} (hab : ¬ π.SameCycle a b) (x y : X) :
    (π * swap a b).SameCycle x y ↔ π.SameCycle x y ∨
      ((π.SameCycle x a ∨ π.SameCycle x b) ∧ (π.SameCycle y a ∨ π.SameCycle y b)) := by
  set ψ := π * swap a b with hψ
  have hne : a ≠ b := fun h => hab (h ▸ Perm.SameCycle.refl π a)
  have hψa : ψ a = π b := by_simp_all
  have hψb : ψ b = π a := by_simp_all
  have hψz : ∀ z, z ≠ a → z ≠ b → ψ z = π z := by
    intro z h1 h2; simp [hψ, swap_apply_of_ne_of_ne h1 h2]
  set U : X → Prop := fun z => π.SameCycle z a ∨ π.SameCycle z b
  -- `U` is `ψ`-invariant
  have hU : ∀ z, U z → U ztwin := by
    zugh
    by_cases h1 : z = a
    · subst h1; rw [hψa]; exact Or.inr ztiho
    · by_cases h2 : z = b
      · subst h2; rw [hψb]; exact Or.inl ztiho
      · zujkc
        zukms
        · exact Or.inl ztvcs
        · exact Or.inr ztvcs
  have hUc : ∀ z, ¬ U z → ¬ U ztwin ∧ ψ z = π z := by
    zugh
    have h1 : z ≠ a := fun h => hz (Or.inl ztqot)
    have h2 : z ≠ b := fun h => hz (Or.inr ztqot)
    zujkc
    refine ⟨fun h => hz ?_, rfl⟩
    zuy
    · exact Or.inl ztvcr
    · exact Or.inr ztvcr
  -- all of `U` is one `ψ`-cycle
  have hcycA : ∀ z, π.SameCycle z a → ψ.SameCycle z a := by
    zugh
    refine sameCycle_follow π ψ id (fun w => π.SameCycle w a) hz hz ?_
    intro w hw hwa
    have hwb : w ≠ b := fun h => hab (h ▸ hw).symm
    simp_all
  have hcycB : ∀ z, π.SameCycle z b → ψ.SameCycle z b := by
    zugh
    refine sameCycle_follow π ψ id (fun w => π.SameCycle w b) hz hz ?_
    intro w hw hwb
    have hwa : w ≠ a := by_grind
    simp_all
  have hAB : ψ.SameCycle a b := by
    have : ψ.SameCycle _ b := hcycB _ ztiho
    rw [← hψa] at this
    exact (Perm.sameCycle_apply_left.mp this)
  have hUall : ∀ z, U z → ψ.SameCycle z a := by
    zugh
    zukms
    · simp_all
    · exact (hcycB z hz).trans hAB.symm
  constructor
  · zuq
    zuldo
    · have hy := mem_of_sameCycle ψ {z | U z} hU h hx
      exact Or.inr ⟨hx, hy⟩
    · left
      zubpg

      have key : ∀ k, ¬ U (ztufm x) ∧ ztufm x = ztkhy x := by
        zugoi
        induction k with
        | zero => exact by_simp_all
        | succ k ih =>
          obtain ⟨h1, h2⟩ := hUc _ ih.1
          refine ⟨by zunaz; exact h1, ?_⟩
          rw [pow_succ', Perm.mul_apply, h2, ih.2, pow_succ', Perm.mul_apply]
      rw [(key k).2]
      tauto
  · rintro (h | ⟨hx, hy⟩)
    · zuldo
      · have hy : U y := by
          zuky
          · exact Or.inl ztvsa
          · exact Or.inr ztvsa
        zueos
      · refine sameCycle_follow π ψ id (fun w => ¬ U w) hx h ?_
        grind
    · zueos
end Merge
section FirstReturn
variable {X : Type*} [Finite X] (π : Perm X) (p : X → Prop)

/-- The orbit of a point of `{p}` returns to `{p}`. -/
theorem exists_return {x : X} (hx : p x) : ∃ m, 0 < m ∧ p (ztkhz x) :=
  ⟨orderOf π, orderOf_pos π, by_simp_all⟩
open Classical in
/-- The first time the `π`-orbit of `x` returns to `{p}`. -/
noncomputable def returnTime (x : {x // p x}) : ℕ := Nat.find ztlnq
variable (x : {x // p x}) {m : ℕ}
/-- The return time is positive. -/
theorem returnTime_pos : 0 < returnTime π p x := by
  classical exact (Nat.find_spec ztlnq).1

/-- At the return time the orbit is back in `{p}`. -/
theorem pow_returnTime : p (ztdwq x.1) := by
  classical exact (Nat.find_spec ztlnq).2

/-- Before the return time the orbit avoids `{p}`. -/
theorem not_pow_of_lt_returnTime {j : ℕ} (hj0 : 0 < j)
    (hj : j < returnTime π p x) : ¬ p ztbwq := by
  classical
  zuq
  exact Nat.find_min _ hj by_simp_all

/-- Characterisation of the return time. -/
theorem returnTime_eq (hm0 : 0 < m) (hm : p ztbaix)
    (hmin : ∀ j, 0 < j → j < m → ¬ p ztbwq) : returnTime π p x = m := by
  classical
  refine le_antisymm (Nat.find_min' _ by_simp_all) ?_
  zubq

  exact hmin _ (returnTime_pos π p x) h (pow_returnTime π p x)

/-- The first-return map to `{p}`. -/
noncomputable def returnFun (x : {x // p x}) : {x // p x} :=
  ⟨ztdwq x.1, pow_returnTime π p x⟩

/-- The first-return map is injective. -/
theorem returnFun_injective : Function.Injective zttyu := by
  zujbt
  have h : ztdwq x.1 = ztpes y.1 := congrArg Subtype.val hxy
  -- the smaller return time forces equality
  have key : ∀ (x y : {x // p x}), returnTime π p x ≤ returnTime π p y →
      ztdwq x.1 = ztpes y.1 → x = y := by
    intro x y hle h
    have h' : x.1 = (π ^ (returnTime π p y - returnTime π p x)) y.1 := by
      apply (π ^ returnTime π p x).injective
      rw [h, ← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hle]
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · apply Subtype.ext
      simp_all
    · have := returnTime_pos π p x
      exact absurd (h' ▸ x.2) (not_pow_of_lt_returnTime π p y by_omega by_omega)
  grind

/-- **The first-return permutation** of `π` on the subtype `{x // p x}`. -/
noncomputable def firstReturn : Perm {x // p x} :=
  Equiv.ofBijective zttyu (Finite.injective_iff_bijective.mp (returnFun_injective π p))

/-- The first-return permutation. -/
theorem firstReturn_apply :
    (firstReturn π p x).1 = ztdwq x.1 := rfl

/-- If the first `m - 1` iterates after `x` avoid `{p}` and the `m`-th is in it, the first return
of `x` is the `m`-th iterate. -/
theorem firstReturn_eq (hm0 : 0 < m) (hm : p ztbaix)
    (hmin : ∀ j, 0 < j → j < m → ¬ p ztbwq) :
    (firstReturn π p x).1 = ztkhz x.1 := by
  rw [firstReturn_apply, returnTime_eq π p x hm0 hm hmin]

/-- The cycles of the first-return map are the traces of the cycles of `π`. -/
theorem sameCycle_firstReturn_iff (x y : {x // p x}) :
    (firstReturn π p).SameCycle x y ↔ π.SameCycle x.1 y.1 := by
  classical
  constructor
  · zuq
    zubpg

    induction k with
    | zero => exact Perm.SameCycle.refl _ _
    | succ k ih =>
      rw [pow_succ', Perm.mul_apply, firstReturn_apply]
      zufeo
  · zuq
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    have key : ∀ k (hk : p _),
        (firstReturn π p).SameCycle x ⟨ztkhy x.1, hk⟩ := by
      zugoi
      induction k using Nat.strong_induction_on with
      | _ k ih =>
      zuibt
      zujcz
      · zubvi
        rfl
      · set j := Nat.findGreatest (fun j => p ztbwq) ztie
        have hj : p ztbwq := Nat.findGreatest_spec (P := fun j => p ztbwq)
          ztbg (by simpa using x.2)
        have hjk : j < k := by
          have := Nat.findGreatest_le (P := fun j => p ztbwq) ztie
          omega
        have hret : (firstReturn π p ⟨ztkhx x.1, hj⟩).1 = ztkhy x.1 := by
          rw [firstReturn_eq π p _ (m := k - j) by_omega]
          · zunrc
          · zunrc; exact hk
          · zumgx
            rw [← Perm.mul_apply, ← pow_add]
            exact Nat.findGreatest_is_greatest (P := fun j => p ztbwq) (n := k - 1)
              by_omega by_omega
        refine (ih j hjk hj).trans ztfvv
        rw [zpow_one]
        grind
    grind
end FirstReturn
section EqvGenLemmas
variable {X : Type*}
variable (R : X → X → Prop)
/-- The equivalence closure of `R` with one extra pair `(u, w)`. -/
theorem eqvGen_or_pair_iff (u w x y : X) :
    EqvGen ztxeb x y ↔
      EqvGen R x y ∨ (EqvGen R x u ∧ EqvGen R w y) ∨ (EqvGen R x w ∧ EqvGen R u y) := by
  constructor
  · zuq
    induction h with
    | rel a b hab =>
      rcases hab with hab | ⟨rfl, rfl⟩
      · tauto
      · exact Or.inr (Or.inl ⟨EqvGen.refl _, EqvGen.refl _⟩)
    | refl a => exact Or.inl ztmav
    | symm a b _ ih =>
      rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ztrja
      · exact Or.inr (Or.inr ztlvd)
      · exact Or.inr (Or.inl ztlvd)
    | trans a b c _ _ ih1 ih2 =>
      rcases ih1 with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases ih2 with k | ⟨k1, k2⟩ | ⟨k1, k2⟩
      · exact Or.inl (EqvGen.trans _ _ _ h k)
      · exact Or.inr (Or.inl ztmqa)
      · exact Or.inr (Or.inr ztmqa)
      · exact Or.inr (Or.inl ztmql)
      · simp_all
      · exact Or.inl ztowr
      · exact Or.inr (Or.inr ztmql)
      · exact Or.inl ztowr
      · simp_all
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact EqvGen.mono zthgs _ _ h
    · have hm := fun a b (h : EqvGen R a b) =>
        EqvGen.mono (p := fun a b => R a b ∨ ztbzg)
          zthgs a b h
      exact EqvGen.trans _ _ _ by_simp_all
        (EqvGen.trans _ _ _ ztbapu by_simp_all)
    · have hm := fun a b (h : EqvGen R a b) =>
        EqvGen.mono (p := fun a b => R a b ∨ ztbzg)
          zthgs a b h
      exact EqvGen.trans _ _ _ by_simp_all
        (EqvGen.trans _ _ _ (EqvGen.symm _ _ ztbapu) by_simp_all)

/-- Two relations with the same equivalence closure. -/
theorem eqvGen_iff_of_le (R R' : X → X → Prop) (h1 : ∀ a b, R a b → EqvGen R' a b)
    (h2 : ∀ a b, R' a b → EqvGen R a b) {x y : X} : EqvGen R x y ↔ EqvGen R' x y := by
  have key : ∀ (S S' : X → X → Prop), (∀ a b, S a b → EqvGen S' a b) →
      ∀ x y, EqvGen S x y → EqvGen S' x y := by
    intro S S' h x y hxy
    induction hxy with
    | rel a b hab => exact h a b hab
    | refl a => exact EqvGen.refl _
    | symm a b _ ih => exact EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact EqvGen.trans _ _ _ ih1 ih2
  grind

/-- Classes of the empty relation: `Quot` by an empty relation has the cardinality of the type. -/
theorem card_quot_bot (hR : ∀ a b, ¬ R a b) :
    Nat.card ztjll = Nat.card X := by
  symm
  refine Nat.card_eq_of_bijective _ ⟨fun a b hab => ?_, Quot.mk_surjective⟩
  have h := Quot.eqvGen_exact hab
  clear hab
  induction h with
  | rel a b hab => exact by_simp_all
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

/-- Adding one pair to a relation merges at most two classes: the number of classes drops by
at most one. -/
theorem card_quot_le_or_pair_add_one [Finite X] (R : X → X → Prop) (u w : X) :
    Nat.card ztjll ≤ Nat.card ztbasj + 1 := by
  classical
  zudgh
  let g : Quot R → Quot R' := Quot.lift _ ztyqk
  let G : Quot R → Option _ := fun q => if q = Quot.mk R w then none else some (g q)
  have hG : Function.Injective G := by
    intro q q' hqq
    induction q using Quot.ind with
    | mk a =>
    induction q' using Quot.ind with
    | mk b =>
    by_cases ha : Quot.mk R a = Quot.mk R w <;> by_cases hb : Quot.mk R b = Quot.mk R w
    · simp_all
    · grind
    · grind
    · simp only [G, ha, hb, ite_false, Option.some.injEq] at hqq
      zufta

      rcases h with h | ⟨_, h2⟩ | ⟨h1, _⟩
      · exact Quot.eqvGen_sound h
      · exact absurd (Quot.eqvGen_sound ztrjb) hb
      · exact absurd (Quot.eqvGen_sound h1) ha
  have := Nat.card_le_card_of_injective G hG
  rwa [Finite.card_option] at this

/-- Adding a pair that is already related does not change the classes. -/
theorem card_quot_or_pair_eq [Finite X] (R : X → X → Prop) (u w : X) (huw : EqvGen R u w) :
    Nat.card ztbasj = Nat.card ztjll := by
  zudgh
  let g : Quot R → Quot R' := Quot.lift ztvcw ztyqk
  symm
  refine Nat.card_eq_of_bijective g ⟨fun q q' hqq => ?_, ?_⟩
  · induction q using Quot.ind with
    | mk a =>
    induction q' using Quot.ind with
    | mk b =>
    zufta

    apply Quot.eqvGen_sound
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · zubh
    · exact EqvGen.trans _ _ _ h1 (EqvGen.trans _ _ _ huw h2)
    · exact EqvGen.trans _ _ _ h1 (EqvGen.trans _ _ _ (EqvGen.symm _ _ huw) h2)
  · intro q
    induction q using Quot.ind with
    | mk a => exact ⟨Quot.mk R a, rfl⟩

/-- **Localisation.**  Inside a class of `EqvGen R` all of whose outgoing `R`-edges are
`R'`-edges, `EqvGen R` implies `EqvGen R'`. -/
theorem eqvGen_of_class (R R' : X → X → Prop) (a : X)
    (h : ∀ x y, EqvGen R a x → R x y → R' x y) {x y : X} (hx : EqvGen R a x)
    (hxy : EqvGen R x y) : EqvGen R' x y := by
  induction hxy with
  | rel x y hr => exact EqvGen.rel _ _ by_simp_all
  | refl x => exact EqvGen.refl _
  | symm x y hyx ih =>
    exact EqvGen.symm _ _ (ih (EqvGen.trans _ _ _ hx (EqvGen.symm _ _ hyx)))
  | trans x z y hxz _ ih1 ih2 =>
    exact EqvGen.trans _ _ _ (ih1 hx) (ih2 (EqvGen.trans _ _ _ hx hxz))

/-- Relations with the same equivalence closure have the same number of classes. -/
theorem card_quot_eq_of_eqvGen_iff (R R' : X → X → Prop)
    (h : ∀ x y, EqvGen R x y ↔ EqvGen R' x y) : Nat.card ztjll = Nat.card (Quot R') := by
  let g : Quot R → Quot R' := Quot.lift ztvcw
    (fun a b hab => Quot.eqvGen_sound ((h a b).mp (EqvGen.rel _ _ hab)))
  refine Nat.card_eq_of_bijective g ⟨fun q q' hqq => ?_, fun q => ?_⟩
  · induction q using Quot.ind with
    | mk a =>
    induction q' using Quot.ind with
    | mk b => exact Quot.eqvGen_sound ((h a b).mpr (Quot.eqvGen_exact hqq))
  · induction q using Quot.ind with
    | mk a => exact ⟨Quot.mk R a, rfl⟩

/-- A set closed under a relation in both directions is closed under its equivalence closure. -/
theorem mem_of_eqvGen (U : Set X) (h1 : ∀ x y, R x y → x ∈ U → y ∈ U)
    (h2 : ∀ x y, R x y → y ∈ U → x ∈ U) {x y : X} (hxy : EqvGen R x y) (hx : x ∈ U) : y ∈ U := by
  have key : ∀ x y, EqvGen R x y → (x ∈ U ↔ y ∈ U) := by
    zujbt
    induction hxy with
    | rel a b hab => exact by_grind
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  grind

/-- A relation all of whose elements are related has at most one class. -/
theorem card_quot_le_one [Finite X] (R : X → X → Prop) (h : ∀ x y, EqvGen R x y) :
    Nat.card ztjll ≤ 1 := by
  rw [Finite.card_le_one_iff_subsingleton]
  refine ⟨fun q q' => ?_⟩
  induction q using Quot.ind with
  | mk a =>
  induction q' using Quot.ind with
  | mk b => exact Quot.eqvGen_sound by_simp_all
end EqvGenLemmas
open Finset
structure CombMap (V F D : Type*) where
  /-- rotation of the darts around their vertex -/
  rot : Perm D
  /-- the opposite dart of the same edge -/
  opp : Perm D
  /-- the vertex (tail) of a dart -/
  vert : D → V
  /-- the face to the left of a dart (the face cycle of `rot * opp` through it) -/
  face : D → F
  opp_opp : ∀ d, opp ztwba = d
  opp_ne : ∀ d, opp d ≠ d
  vert_rot : ∀ d, vert (rot d) = vert d
  sameCycle_of_vert : ∀ d e, vert d = vert e → rot.SameCycle d e
  face_fperm : ∀ d, face (rot ztwba) = face d
  sameCycle_of_face : ∀ d e, face d = face e → (rot * opp).SameCycle d e
  vert_surj : Function.Surjective vert
  face_surj : Function.Surjective face
namespace CombMap
variable {V F D : Type*} (M : CombMap V F D)

/-- The face permutation `fperm d = rot (opp d)`. -/
def fperm : Perm D := M.rot * M.opp

/-- The head of a dart: the vertex of the opposite dart. -/
def head (d : D) : V := M.vert ztxa
variable (d : D)
/-- The face permutation: `fperm d = rot (opp d)`. -/
theorem fperm_apply : M.fperm d = M.rot ztxa := rfl

/-- The face permutation preserves faces. -/
theorem face_fperm_apply : M.face ztjju = M.face d := M.face_fperm d

/-- The next dart along the face starts at the head of `d`. -/
theorem vert_fperm : M.vert ztjju = M.head d := M.vert_rot _

/-- The head of the opposite dart is the tail. -/
theorem head_opp : M.head ztxa = M.vert d := by
  simp [head, M.opp_opp]

/-- `opp` is injective. -/
theorem opp_injective : Function.Injective M.opp := M.opp.injective

/-- The rotation in terms of the face permutation. -/
theorem rot_eq_fperm_opp : M.rot d = M.fperm ztxa := by
  rw [fperm_apply, M.opp_opp]
section Finite
variable [Finite D]

/-- Faces are the cycles of the face permutation. -/
theorem face_eq_iff_sameCycle {d e : D} : M.face d = M.face e ↔ M.fperm.SameCycle d e :=
  ⟨M.sameCycle_of_face d e, fun h => eq_of_sameCycle M.fperm M.face M.face_fperm h⟩
end Finite

/-! ### Maps from bare permutations -/

/-! ### Counting -/
section Counting
variable [Fintype V] [Fintype F] [Fintype D]

/-- The number of edges. -/
def numE (_M : CombMap V F D) : ℕ := Fintype.card D / 2

/-- The Euler characteristic `V - E + F`. -/
def euler (M : CombMap V F D) : ℤ := (Fintype.card V : ℤ) - M.numE + Fintype.card F
omit [Fintype V] [Fintype F] in
/-- The number of darts is even. -/
theorem card_darts_even (M : CombMap V F D) : 2 ∣ Fintype.card D := by
  classical
  have h2 : M.opp ^ 2 = 1 := by
    ext d; simp [pow_two, M.opp_opp]
  have hs : M.opp.support = Finset.univ := by
    ext d; simp [Perm.mem_support, M.opp_ne]
  have := Perm.two_dvd_card_support h2
  rwa [hs, Finset.card_univ] at this
omit [Fintype V] [Fintype F] in
/-- Every edge has two darts: `|D| = 2E`. -/
theorem two_mul_numE : 2 * M.numE = Fintype.card D := by
  have := M.card_darts_even
  unfold numE; omega

/-- The Euler characteristic in dart form: `2χ = 2V - |D| + 2F`. -/
theorem two_mul_euler : 2 * M.euler =
    2 * (Fintype.card V : ℤ) - Fintype.card D + 2 * Fintype.card F := by
  have := M.two_mul_numE
  unfold euler; omega
variable [DecidableEq F]

/-- The degree of a face: its number of darts. -/
def faceDeg (g : F) : ℕ := (Finset.univ.filter (fun d => M.face d = g)).card
end Counting

/-! ### Connectivity and planarity -/

/-- A map is connected when the only nonempty dart set closed under `rot` and `opp` is
everything (the group generated by `rot` and `opp` acts transitively). -/
def Connected : Prop :=
  ∀ S : Set D, (∀ d ∈ S, M.rot d ∈ S) → (∀ d ∈ S, M.opp d ∈ S) → ∀ d ∈ S, ∀ e, e ∈ S

/-- A planar map: connected with Euler characteristic `2`. -/
def Planar [Fintype V] [Fintype F] [Fintype D] : Prop := M.Connected ∧ M.euler = 2

/-- Connectivity through faces: a nonempty dart set closed under `fperm` and `opp` is
everything. -/
theorem Connected.of_fperm {M : CombMap V F D} (hM : M.Connected) (S : Set D)
    (hf : ∀ d ∈ S, M.fperm d ∈ S)
    (ho : ∀ d ∈ S, M.opp d ∈ S) {d : D} (hd : d ∈ S) (e : D) : e ∈ S :=
  hM S (fun x hx => by rw [M.rot_eq_fperm_opp]; simp_all) ho d hd e

/-- Connectivity through face labels. -/
theorem Connected.of_face {M : CombMap V F D} (hM : M.Connected) (S : Set D)
    (hv : ∀ d e, M.face d = M.face e → d ∈ S → e ∈ S)
    (ho : ∀ d ∈ S, M.opp d ∈ S) {d : D} (hd : d ∈ S) (e : D) : e ∈ S :=
  hM.of_fperm S (fun x hx => hv x _ (M.face_fperm_apply x).symm hx) ho hd e

/-! ### The underlying simple graph -/

/-- The underlying simple graph: distinct vertices joined by some dart. -/
def graph : SimpleGraph V where
  Adj u w := u ≠ w ∧ ∃ d, M.vert d = u ∧ M.head d = w
  symm := ⟨by
    rintro u w ⟨hne, d, rfl, rfl⟩
    exact ⟨hne.symm, M.opp d, rfl, M.head_opp d⟩⟩
  loopless := ztpfk

/-! ### The dual map -/

/-- `fperm * opp = rot`. -/
theorem fperm_mul_opp : M.fperm * M.opp = M.rot := by
  ext d; simp [fperm, M.opp_opp]

/-- The **dual map**: vertices and faces exchanged, the rotation of the dual is the face
permutation `fperm` and the edges are the same (`opp`). -/
def dual : CombMap F V D where
  rot := M.fperm
  opp := M.opp
  vert := M.face
  face := M.vert
  opp_opp := M.opp_opp
  opp_ne := M.opp_ne
  vert_rot := M.face_fperm_apply
  sameCycle_of_vert := M.sameCycle_of_face
  face_fperm d := by
    show M.vert (M.fperm ztxa) = M.vert d
    rw [fperm_apply, M.opp_opp, M.vert_rot]
  sameCycle_of_face d e h := by rw [M.fperm_mul_opp]; exact M.sameCycle_of_vert d e h
  vert_surj := M.face_surj
  face_surj := M.vert_surj

/-! ### Edge bounds -/
section Bounds
variable [Fintype V] [Fintype F] [Fintype D] [DecidableEq F]
end Bounds
end CombMap
end
universe uF uD
@[expose] public section
open Equiv Finset Sum
namespace CombMap
variable {V F D : Type*} [DecidableEq D] (M : CombMap V F D)

/-! ### The arc of a face between two darts -/
section Arc
def arc (a : D) (k : ℕ) : Finset D := (Finset.range k).image (fun j => ztenc a)
variable {M} {a b : D} {k : ℕ}
variable {x : D}
/-- Membership in the arc `{fperm^j a : j < k}`. -/
theorem mem_arc : x ∈ M.arc a k ↔ ∃ j < k, ztenc a = x := by
  simp [arc]
omit [DecidableEq D] in
/-- The arc from `a` to `b ≠ a` is nonempty. -/
theorem arc_pos (hab : a ≠ b) (hk : ztdtj a = b) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · simp_all
  omega

/-- The arc starts at `a`. -/
theorem mem_arc_self (hab : a ≠ b) (hk : ztdtj a = b) : a ∈ M.arc a k :=
  mem_arc.mpr ⟨0, arc_pos hab hk, by_simp⟩

/-- The arc stops before `b`. -/
theorem notMem_arc_end (hmin : ∀ j < k, ztenc a ≠ b) : b ∉ M.arc a k := by
  rintro hb
  obtain ⟨j, hj, hjb⟩ := mem_arc.mp hb
  simp_all

/-- The arc is closed under `fperm` until it reaches `b`. -/
theorem fperm_mem_arc (hk : ztdtj a = b) {x : D} (hx : x ∈ M.arc a k)
    (hxb : M.fperm x ≠ b) : M.fperm x ∈ M.arc a k := by
  obtain ⟨j, hj, rfl⟩ := mem_arc.mp hx
  refine mem_arc.mpr ⟨j + 1, ?_, by zunaz⟩
  rcases Nat.lt_or_ge ztl k with h | h
  · zubh
  · exfalso; apply hxb
    rw [← Perm.mul_apply, ← pow_succ', show j + 1 = k by omega, hk]

/-- The complement of the arc is closed under `fperm` until it reaches `a`. -/
theorem fperm_notMem_arc (hx : x ∉ M.arc a k) (hxa : M.fperm x ≠ a) :
    M.fperm x ∉ M.arc a k := by
  zuq
  zufym
  rcases j with _ | j
  · simp_all
  · apply hx
    refine mem_arc.mpr ztrdp
    apply M.fperm.injective
    rw [← hjx, pow_succ', Perm.mul_apply]

/-- The dart before `b` is the last dart of the arc. -/
theorem fperm_symm_end_mem_arc (hab : a ≠ b) (hk : ztdtj a = b) :
    M.fperm.symm b ∈ M.arc a k := by
  have hk0 := arc_pos hab hk
  refine mem_arc.mpr ⟨k - 1, by_omega, ?_⟩
  rw [Equiv.eq_symm_apply, ← Perm.mul_apply, ← pow_succ', show k - 1 + 1 = k by omega, hk]

/-- The dart before `a` is not in the arc. -/
theorem fperm_symm_start_notMem_arc (hk : ztdtj a = b)
    (hmin : ∀ j < k, ztenc a ≠ b) : M.fperm.symm a ∉ M.arc a k := by
  zuq
  zufym
  have ha : (M.fperm ^ ztl) a = a := by
    rw [pow_succ', Perm.mul_apply, hjx, Equiv.apply_symm_apply]
  apply hmin ztzwk by_omega
  rw [← hk, show k = ztzwk + ztl by omega, pow_add, Perm.mul_apply, ha]
  simp

/-- The arc lies in the face of `a`. -/
theorem sameCycle_of_mem_arc (hx : x ∈ M.arc a k) : M.fperm.SameCycle a x := by
  obtain ⟨j, -, rfl⟩ := mem_arc.mp hx
  tauto
end Arc

/-! ### The new permutations and labels -/
section AddEdge
variable (a b : D) (k : ℕ)

/-- Rotation after adding the edge: `inr true` just before `a`, `inr false` just before `b`. -/
def addRot : Perm ztnkj :=
  swap (inl b) ztmlt * swap (inl a) ztmlu * Perm.sumCongr M.rot 1

/-- The opposite-dart involution after adding the edge `{inr true, inr false}`. -/
def addOpp : Perm ztnkj := Perm.sumCongr M.opp (swap true false)

/-- Vertex labels after adding the edge. -/
def addVert : D ⊕ Bool → V := Sum.elim M.vert (fun t => if t then M.vert a else M.vert b)

/-- Face labels after adding the edge: the arc and `inr false` form the new face `none`. -/
def addFace : D ⊕ Bool → Option F :=
  Sum.elim (fun x => if x ∈ M.arc a k then none else some ztpzx)
    (fun t => if t then some ztmbn else none)
variable {a b}

/-- The new rotation on an old dart. -/
theorem addRot_inl (hab : a ≠ b) (x : D) : M.addRot a b ztetq =
    if M.rot x = a then inr true else if M.rot x = b then inr false else inl ztvaa := by
  simp only [addRot, Perm.mul_apply, Perm.sumCongr_apply, Sum.map_inl, swap_apply_def]
  grind

/-- The new dart `inr true` is followed by `a`. -/
theorem addRot_true (hab : a ≠ b) : M.addRot a b ztmlu = inl a := by
  simp only [addRot, Perm.mul_apply, Perm.sumCongr_apply, Sum.map_inr, Perm.one_apply,
    swap_apply_def]
  simp_all

/-- The new dart `inr false` is followed by `b`. -/
theorem addRot_false : M.addRot a b ztmlt = inl b := by
  rfl
omit [DecidableEq D] in
/-- The new `opp` on an old dart. -/
theorem addOpp_inl (x : D) : M.addOpp ztetq = inl ztpzz := rfl
omit [DecidableEq D] in
/-- The two new darts are opposite. -/
theorem addOpp_inr (t : Bool) : M.addOpp (inr t) = inr (!t) := by
  cases t <;> simp [addOpp]

/-- The new face permutation on an old dart. -/
theorem addFperm_inl (hab : a ≠ b) (x : D) : ztenb ztetq =
    if M.fperm x = a then inr true else if M.fperm x = b then inr false else inl ztuzu := by
  rw [Perm.mul_apply, addOpp_inl, addRot_inl M hab]; rfl

/-- The new face permutation at `inr true`. -/
theorem addFperm_true : ztenb ztmlu = inl b := by
  rfl

/-- The new face permutation at `inr false`. -/
theorem addFperm_false (hab : a ≠ b) : ztenb ztmlt = inl a := by
  rw [Perm.mul_apply, addOpp_inr, Bool.not_false, addRot_true M hab]

/-- Away from the insertion points the new face permutation is the old one. -/
theorem addFperm_inl_of_ne (hab : a ≠ b) {x : D} (h1 : M.fperm x ≠ a) (h2 : M.fperm x ≠ b) :
    ztenb ztetq = inl ztuzu := by
  zuoqn; simp_all

/-! #### The structure axioms -/
omit [DecidableEq D] in
/-- The new `opp` is an involution. -/
theorem addOpp_addOpp (z : D ⊕ Bool) : M.addOpp (M.addOpp z) = z := by
  zucoz
  · simp [addOpp_inl, M.opp_opp]
  · zupem
omit [DecidableEq D] in
/-- The new `opp` has no fixed point. -/
theorem addOpp_ne (z : D ⊕ Bool) : M.addOpp z ≠ z := by
  zucoz
  · simp [addOpp_inl, M.opp_ne]
  · cases t <;> zupem

/-- The new rotation preserves vertices. -/
theorem addVert_addRot (hab : a ≠ b) (z : D ⊕ Bool) :
    M.addVert a b (M.addRot a b z) = M.addVert a b z := by
  zucoz
  · rw [addRot_inl M hab]
    zupi
    · simp [addVert, ← h1, M.vert_rot]
    · simp [addVert, ← h2, M.vert_rot]
    · simp [addVert, M.vert_rot]
  · cases t
    · rfl
    · simp [addRot_true M hab, addVert]
variable [Fintype D]
omit [Fintype D] in
/-- An old dart and its old successor stay in one new rotation cycle. -/
theorem addRot_step (hab : a ≠ b) (x : D) :
    (M.addRot a b).SameCycle ztetq (inl ztvaa) := by
  by_cases h1 : M.rot x = a
  · refine ztolp
    rw [show ztprh = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, pow_two, Perm.mul_apply,
      addRot_inl M hab, ite_eq_left h1, addRot_true M hab, h1]
  · by_cases h2 : M.rot x = b
    · refine ztolp
      rw [show ztprh = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, pow_two, Perm.mul_apply,
        addRot_inl M hab, ite_eq_right h1, ite_eq_left h2, addRot_false, h2]
    · refine ztfvv
      rw [zpow_one, addRot_inl M hab, ite_eq_right h1, ite_eq_right h2]

/-- Darts with the same vertex are in one cycle of the new rotation. -/
theorem addVert_sameCycle (hab : a ≠ b) (z w : D ⊕ Bool)
    (h : M.addVert a b z = M.addVert a b w) : (M.addRot a b).SameCycle z w := by
  -- every dart is in the rotation cycle of an old dart with the same vertex
  have hrep : ∀ z : D ⊕ Bool, ∃ x : D, M.vert x = M.addVert a b z ∧
      (M.addRot a b).SameCycle z ztetq := by
    rintro (x | t)
    · tauto
    · cases t
      · exact ⟨b, rfl, ⟨1, by_rfl⟩⟩
      · exact ⟨a, rfl, ⟨1, by rw [zpow_one, addRot_true M hab]⟩⟩
  obtain ⟨x, hx, hzx⟩ := hrep z
  obtain ⟨y, hy, hwy⟩ := hrep w
  have hxy := M.sameCycle_of_vert x y by_simp_all
  exact hzx.trans ((sameCycle_of_step M.rot _ inl (M.addRot_step hab) hxy).trans
    hwy.symm)
variable {k}

/-- The new face permutation preserves the new face labels. -/
theorem addFace_addFperm (hab : a ≠ b) (hk : ztdtj a = b)
    (hmin : ∀ j < k, ztenc a ≠ b) (z : D ⊕ Bool) :
    M.addFace a k (ztenb z) = M.addFace a k z := by
  have hfb : ztscc := by
    zueed
  zucoz
  · zuoqn
    zupi
    · -- `x = fperm⁻¹ a`
      have hx : x = M.fperm.symm a := by_grind
      have hxn := hx ▸ fperm_symm_start_notMem_arc hk hmin
      simp only [addFace, Sum.elim_inr, Sum.elim_inl, ite_true, ite_eq_right hxn]
      rw [← h1, M.face_fperm_apply]
    · have hx : x = M.fperm.symm b := by_grind
      have hxm := hx ▸ fperm_symm_end_mem_arc hab hk
      simp [addFace, hxm]
    · simp only [addFace, Sum.elim_inl, M.face_fperm_apply]
      zuhtl
      · rw [ite_eq_left (fperm_mem_arc hk hx h2), ite_eq_left hx]
      · rw [ite_eq_right (fperm_notMem_arc hx h1), ite_eq_right hx]
  · cases t
    · rw [addFperm_false M hab]
      simp [addFace, mem_arc_self hab hk]
    · rw [addFperm_true]
      simp [addFace, notMem_arc_end hmin, hfb]

/-- Darts with the same new face label are in one cycle of the new face permutation. -/
theorem addFace_sameCycle (hab : a ≠ b) (hk : ztdtj a = b)
    (hmin : ∀ j < k, ztenc a ≠ b) (z w : D ⊕ Bool)
    (h : M.addFace a k z = M.addFace a k w) : (M.addRot a b * M.addOpp).SameCycle z w := by
  set ψ := M.addRot a b * M.addOpp with hψ
  have hfb : ztscc := by
    zueed
  -- representatives: label `none` ↦ `inr false`, label `some (face a)` ↦ `inr true`
  have hnone : ∀ z, M.addFace a k z = none → ψ.SameCycle z ztmlt := by
    zujgb
    · have hx : x ∈ M.arc a k := by
        by_contra hx; simp [addFace, hx] at hz
      have h1 : ψ.SameCycle ztetq (inl ztuzw) := by
        refine sameCycle_follow M.fperm ψ inl (fun y => y ∈ M.arc a k) hx ?_ ?_
        · have hab' : M.fperm.SameCycle a b := ⟨(k : ℤ), by_simp_all⟩
          have hbb : M.fperm.SameCycle b ztuzw := ztluz
          exact ((sameCycle_of_mem_arc hx).symm.trans hab').trans hbb
        · intro y hy hyb
          have hya : ztulo := by
            rintro h; apply fperm_symm_start_notMem_arc hk hmin
            grind
          have hyb' : ztulp := by
            grind
          exact ⟨addFperm_inl_of_ne M hab hya hyb', fperm_mem_arc hk hy hyb'⟩
      refine h1.trans ztfvv
      rw [zpow_one, hψ, addFperm_inl M hab, Equiv.apply_symm_apply, ite_eq_right ztmbt,
        ite_eq_left rfl]
    · cases t
      · rfl
      tauto
  have hsome : ∀ z, M.addFace a k z = some ztmbn → ψ.SameCycle z ztmlu := by
    zujgb
    · have hx : ztsmz := by
        intro hx; simp [addFace, hx] at hz
      have hfx : M.face x = M.face a := by simpa [addFace, hx] using hz
      have h1 : ψ.SameCycle ztetq (inl ztuzv) := by
        refine sameCycle_follow M.fperm ψ inl
          (fun y => y ∉ M.arc a k ∧ M.face y = M.face a) by_simp_all ?_ ?_
        · have haa : M.fperm.SameCycle a ztuzv := ztluz
          exact (M.sameCycle_of_face x a hfx).trans haa
        · rintro y ⟨hy, hfy⟩ hya
          have hya' : ztulo := by
            grind
          have hyb : ztulp := by
            rintro h; apply hy
            have : y = M.fperm.symm b := by_grind
            zvmwk; exact fperm_symm_end_mem_arc hab hk
          exact ⟨addFperm_inl_of_ne M hab hya' hyb,
            fperm_notMem_arc hy hya', by rw [M.face_fperm_apply, hfy]⟩
      refine h1.trans ztfvv
      rw [zpow_one, hψ, addFperm_inl M hab, Equiv.apply_symm_apply, ite_eq_left rfl]
    · cases t
      · tauto
      rfl
  -- the other faces are untouched
  have hother : ∀ x y : D, M.face x = M.face y → M.face x ≠ M.face a →
      ψ.SameCycle ztetq (inl y) := by
    intro x y hxy hxa
    refine sameCycle_follow M.fperm ψ inl (fun w => M.face w = M.face x) rfl
      (M.sameCycle_of_face x y hxy) ?_
    intro w hw _
    have h1 : M.fperm w ≠ a := by
      rintro h; apply hxa; rw [← hw, ← M.face_fperm_apply, h]
    have h2 : M.fperm w ≠ b := by
      rintro h; apply hxa; rw [← hw, ← M.face_fperm_apply, h, hfb]
    exact ⟨addFperm_inl_of_ne M hab h1 h2, by rw [M.face_fperm_apply, hw]⟩
  -- conclude
  rcases hz : M.addFace a k z with _ | g
  · zugep
    exact (hnone z hz).trans (hnone w h.symm).symm
  · by_cases hg : g = M.face a
    · subst hg
      zugep
      exact (hsome z hz).trans (hsome w h.symm).symm
    · zugep
      zucoz
      · rcases w with y | s
        · have hx : ztsmz := by intro hx; simp [addFace, hx] at hz
          have hy : y ∉ M.arc a k := by intro hy; simp [addFace, hy] at h
          have hfx : M.face x = g := by
            have : some ztpzx = some g := by rw [← hz]; simp [addFace, hx]
            grind
          have hfy : M.face y = g := by
            have : some g = some (M.face y) := by zvmwc; simp [addFace, hy]
            grind
          simp_all
        · cases s
          · tauto
          · have : some g = some ztmbn := by_tauto
            simp_all
      · cases t
        · tauto
        · have : some ztmbn = some g := by_tauto
          grind
omit [DecidableEq D] [Fintype D] in
/-- Every vertex keeps a dart. -/
theorem addVert_surj : Function.Surjective (M.addVert a b) := fun v => by
  obtain ⟨x, rfl⟩ := M.vert_surj v
  tauto

/-- Every new face label is used. -/
theorem addFace_surj :
    Function.Surjective (M.addFace a k) := by
  rintro (_ | g)
  · exact ⟨inr false, rfl⟩
  · obtain ⟨x, rfl⟩ := M.face_surj g
    zuhtl
    · refine ⟨inr true, ?_⟩
      simp only [addFace, Sum.elim_inr, ite_true]
      exact congrArg some (eq_of_sameCycle M.fperm M.face M.face_fperm
        (sameCycle_of_mem_arc hx))
    · exact ⟨inl x, by simp [addFace, hx]⟩

/-- **Adding an edge inside a face.**  `a ≠ b` are darts of one face, `b = fperm^k a` with `k`
minimal. -/
def addEdge (hab : a ≠ b) (hk : ztdtj a = b) (hmin : ∀ j < k, ztenc a ≠ b) :
    CombMap V (Option F) ztnkj where
  rot := M.addRot a b
  opp := M.addOpp
  vert := M.addVert a b
  face := M.addFace a k
  opp_opp := M.addOpp_addOpp
  opp_ne := M.addOpp_ne
  vert_rot := M.addVert_addRot hab
  sameCycle_of_vert := M.addVert_sameCycle hab
  face_fperm := M.addFace_addFperm hab hk hmin
  sameCycle_of_face := M.addFace_sameCycle hab hk hmin
  vert_surj := M.addVert_surj
  face_surj := M.addFace_surj
variable (hab : a ≠ b) (hk : (M.fperm ^ k) a = b) (hmin : ∀ j < k, (M.fperm ^ j) a ≠ b)
section Euler
variable [Fintype V] [Fintype F]
end Euler

/-! #### Face degrees after adding an edge -/
variable [DecidableEq F]
end AddEdge

/-! ### Triangulation -/
section Triangulation
variable [Fintype D]
variable [Fintype F] [DecidableEq F]
end Triangulation
end CombMap
namespace CombMap
variable {V F D : Type*}

/-- A rooted spanning tree of a map, given by parent darts and levels. -/
structure SpanTree (M : CombMap V F D) where
  /-- the root -/
  root : V
  /-- the depth of a vertex -/
  level : V → ℕ
  /-- the dart from a non-root vertex to its parent -/
  par : V → D
  level_root : level root = 0
  vert_par : ∀ v, v ≠ root → M.vert zthzd = v
  level_head_par : ∀ v, v ≠ root → level (M.head zthzd) + 1 = level v
namespace SpanTree
variable {M : CombMap V F D} (T : SpanTree M)
section Basic
variable [DecidableEq V]

/-- The parent of a vertex (the root is its own parent). -/
def parent (v : V) : V := if v = T.root then T.root else M.head zteoj

/-- `IsAnc v u`: `v` lies on the tree path from `u` to the root (reflexive). -/
def IsAnc (v u : V) : Prop := ∃ n : ℕ, T.parent^[n] u = v

/-- The root is its own parent. -/
theorem parent_root : T.parent T.root = T.root := by zuocs
variable {v : V} (u : V)
/-- The parent of a non-root vertex is the head of its parent dart. -/
theorem parent_of_ne (hv : v ≠ T.root) : T.parent v = M.head zteoj := by
  simp [parent, hv]
omit [DecidableEq V] in
/-- Non-root vertices have positive level. -/
theorem level_pos (hv : v ≠ T.root) : 0 < T.level v := by
  have := T.level_head_par v hv; omega

/-- The root is the only vertex of level `0`. -/
theorem eq_root_of_level_eq_zero (hv : T.level v = 0) : v = T.root := by
  by_contra h; have := T.level_pos h; omega

/-- The parent is one level up. -/
theorem level_parent (v : V) : T.level ztqda = T.level v - 1 := by
  zufro
  · subst hv; simp [parent_root, T.level_root]
  · rw [T.parent_of_ne hv]; have := T.level_head_par v hv; omega

/-- The `n`-th ancestor is `n` levels up (truncated). -/
theorem level_iterate_parent (n : ℕ) (u : V) :
    T.level (T.parent^[n] u) = T.level u - n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', T.level_parent, ih]; omega

/-- Enough steps up reach the root. -/
theorem iterate_parent_eq_root {n : ℕ} {u : V} (hn : T.level u ≤ n) :
    T.parent^[n] u = T.root :=
  T.eq_root_of_level_eq_zero (by zupen; omega)

/-- Every vertex is its own ancestor. -/
theorem isAnc_refl : T.IsAnc u u := ztkil

/-- The parent is an ancestor. -/
theorem isAnc_parent_self : T.IsAnc ztqcz u := ztufq

/-- The ancestor relation is transitive. -/
theorem IsAnc.trans {w v u : V} (h1 : T.IsAnc w v) (h2 : T.IsAnc v u) : T.IsAnc w u := by
  obtain ⟨m, rfl⟩ := h1
  obtain ⟨n, rfl⟩ := h2
  exact ⟨m + n, by zunri⟩

/-- Ancestors have smaller levels. -/
theorem IsAnc.level_le {v u : V} (h : T.IsAnc v u) : T.level v ≤ T.level u := by
  zuida
  zupen; omega

/-- An ancestor of the parent is an ancestor. -/
theorem IsAnc.of_parent {v u : V} (h : T.IsAnc v ztqcz) : T.IsAnc v u :=
  h.trans T (T.isAnc_parent_self u)

/-- If `v` is an ancestor of `u` but not of its parent, then `u = v`. -/
theorem eq_of_isAnc_of_not_parent {v u : V} (h : T.IsAnc v u) (hp : ¬ T.IsAnc v ztqcz) :
    u = v := by
  obtain ⟨n, hn⟩ := h
  zugai
  · exact hn
  tauto

/-- A non-root vertex is not an ancestor of its parent. -/
theorem not_isAnc_parent (hv : v ≠ T.root) : ¬ T.IsAnc v ztqda := by
  zuq
  have h1 := h.level_le
  rw [T.level_parent] at h1
  have := T.level_pos hv
  omega

/-- A root path has at most one vertex on each level. -/
theorem eq_of_isAnc_of_level_eq {v v' u : V} (h : T.IsAnc v u) (h' : T.IsAnc v' u)
    (hl : T.level v = T.level v') : v = v' := by
  zuida
  obtain ⟨n', rfl⟩ := h'
  rw [T.level_iterate_parent, T.level_iterate_parent] at hl
  by_cases hn : T.level u ≤ n
  · rw [T.iterate_parent_eq_root hn, T.iterate_parent_eq_root by_omega]
  grind
end Basic

/-! ### Tree darts -/
section TreeDarts

/-- A tree dart: `par v` or its opposite, for a non-root vertex `v`. -/
def IsTreeDart (d : D) : Prop := ∃ v, v ≠ T.root ∧ (d = T.par v ∨ d = M.opp zteoj)
variable {v w : V} {d : D}
/-- A parent dart is never the opposite of a parent dart. -/
theorem par_ne_opp_par (hv : v ≠ T.root) (hw : w ≠ T.root) :
    T.par v ≠ M.opp ztqcy := by
  zuq
  have h1 : T.level (M.head ztqcy) + 1 = T.level w := T.level_head_par w hw
  have h2 : T.level ztbaeh + 1 = T.level v := T.level_head_par v hv
  have e1 : M.head ztqcy = v := by
    rw [← T.vert_par v hv, h]; rfl
  have e2 : M.head zteoj = w := by
    rw [← T.vert_par w hw, h, head, M.opp_opp]
  grind

/-- Parent darts of distinct vertices are distinct. -/
theorem par_injective (hv : v ≠ T.root) (hw : w ≠ T.root) (h : T.par v = T.par w) :
    v = w := by
  rw [← T.vert_par v hv, ← T.vert_par w hw, h]
variable [Fintype V] [DecidableEq V] [DecidableEq D]

/-- The finite set of tree darts. -/
def treeDarts : Finset D :=
  ((Finset.univ.filter ztokr).image T.par) ∪
    ((Finset.univ.filter ztokr).image (fun v => M.opp zteoj))

/-- Membership in the tree darts. -/
theorem mem_treeDarts : d ∈ T.treeDarts ↔ T.IsTreeDart d := by
  simp only [treeDarts, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, IsTreeDart]
  grind

/-- The tree darts form an edge set. -/
theorem opp_mem_treeDarts (hd : d ∈ T.treeDarts) : M.opp d ∈ T.treeDarts := by
  rw [mem_treeDarts] at hd ⊢
  obtain ⟨v, hv, rfl | rfl⟩ := hd
  · exact ⟨v, hv, Or.inr rfl⟩
  · exact ⟨v, hv, Or.inl ztuzz⟩

/-- A spanning tree has `V - 1` edges: `|treeDarts| = 2 (V - 1)`. -/
theorem card_treeDarts : T.treeDarts.card = 2 * ztlen := by
  unfold treeDarts
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injOn, Finset.card_image_of_injOn]
    · have : (Finset.univ.filter ztokr).card = Fintype.card V - 1 := by
        rw [Finset.filter_ne' Finset.univ T.root, Finset.card_erase_of_mem ztuyq,
          Finset.card_univ]
      omega
    · zucsd

      exact T.par_injective hv hw ztqaa
    · zucsd

      exact T.par_injective hv hw h
  · zuzt
    intro d hd hd'
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hd hd'
    obtain ⟨v, hv, rfl⟩ := hd
    obtain ⟨w, hw, h⟩ := hd'
    exact T.par_ne_opp_par hv hw h.symm
end TreeDarts
end SpanTree

/-! ### Breadth-first trees -/
section BFS
variable (M : CombMap V F D)

/-- A connected map has a connected underlying graph: every vertex is reachable from `r`. -/
theorem reachable_of_connected (hM : M.Connected) (r u : V) : M.graph.Reachable r u := by
  obtain ⟨d0, hd0⟩ := M.vert_surj r
  obtain ⟨d, rfl⟩ := M.vert_surj u
  refine hM {x | M.graph.Reachable r (M.vert x)} ?_ ?_ d0 by_simp_all d
  · intro x hx; simpa [M.vert_rot] using hx
  · zuh
    simp only [Set.mem_ofPred_eq] at hx ⊢
    by_cases h : M.vert x = M.vert ztpzz
    · simp_all
    · exact hx.trans (SimpleGraph.Adj.reachable ⟨h, x, rfl, rfl⟩)

/-- Every non-root vertex has a neighbour one step closer to `r`. -/
theorem exists_dart_toward (hM : M.Connected) (r v : V) (hv : v ≠ r) :
    ∃ d, M.vert d = v ∧ M.graph.dist r ztbyq + 1 = M.graph.dist r v := by
  obtain ⟨p, hp⟩ := (M.reachable_of_connected hM v r).exists_walk_length_eq_dist
  cases p with
  | nil => exact absurd rfl hv
  | cons hadj q =>
    rename_i w
    obtain ⟨_, d, hd, hdw⟩ := id hadj
    refine ztkkr
    rw [hdw]
    rw [SimpleGraph.Walk.length_cons] at hp
    have h1 := SimpleGraph.dist_le q
    obtain ⟨q', hq'⟩ := (M.reachable_of_connected hM w r).exists_walk_length_eq_dist
    have h2 := SimpleGraph.dist_le (SimpleGraph.Walk.cons hadj q')
    rw [SimpleGraph.Walk.length_cons] at h2
    rw [SimpleGraph.dist_comm (u := r), SimpleGraph.dist_comm (u := r)]
    omega
variable [DecidableEq V]

/-- **BFS tree.**  A connected map has a spanning tree rooted at any vertex `r` whose levels are
the graph distances from `r`; in particular every dart joins levels differing by at most one. -/
theorem exists_bfsTree (hM : M.Connected) (r : V) :
    ∃ T : SpanTree M, T.root = r ∧ (∀ v, T.level v = M.graph.dist r v) := by
  classical
  obtain ⟨d0, -⟩ := M.vert_surj r
  let par : V → D := fun v =>
    if hv : v = r then d0 else Classical.choose (M.exists_dart_toward hM r v hv)
  refine ⟨⟨r, fun v => M.graph.dist r v, par, by_simp, ?_, ?_⟩, rfl, fun v => rfl⟩
  · grind
  · grind
end BFS
end CombMap
end
end Chazelle.Separator
section
set_option hygiene false
local macro "zqbgs" : tactic => `(tactic| (rintro x y hx ⟨e, he, rfl, rfl⟩
                                           refine ⟨e, ?_, rfl, rfl⟩))
local macro "zqbgt" : tactic => `(tactic| (intro e he
                                           simp only [Bh, A, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at he ⊢))
set_option hygiene true

/-!
# The cotree of a spanning tree and the Jordan property of fundamental cycles
(planar separators, part 3b)

Let `T` be a rooted spanning tree of a map `M`.  The non-tree darts (`coDarts`) join faces:
`faceRel S f g` says that some dart `e ∈ S` has `face e = f` and `face (opp e) = g`.

* **Cotree connectivity** (`eqvGen_faceRel_coDarts`): for any spanning tree of a connected map,
  the faces are connected through non-tree edges.  Proof: a proper union `K` of faces closed
  under crossing non-tree edges has a boundary made of tree darts, and every boundary dart has
  a successor boundary dart at its head which is not its reverse; the potential
  `L + level` (upward darts) / `L - level` (downward darts) strictly decreases along
  successors, which is impossible (a tree has no infinite non-backtracking walk).
* **Counting** (`two_mul_numComp_le`): adding an edge merges at most two classes, so
  `2·#classes(S) ≤ 2·#classes(S') + |S' \ S|`.
* **The cotree is a tree** (`not_eqvGen_faceRel`, *acyclicity*): in a *planar* map the
  non-tree edges are `F − 1` (Euler), connect the `F` faces, hence no set of non-tree edges
  already connects the two sides of another non-tree edge.
* For a non-tree dart `d`, removing its edge from the cotree leaves exactly two classes:
  `cross d` (the side entered when crossing `d`) and `cross (opp d)`
  (`mem_cross_or`, `notMem_cross_opp`); `cross_subset`: crossing on from the face entered
  through `d` along another non-tree dart leads into a subset of `cross d`.
* **Jordan property of fundamental cycles** (`face_par_eqvGen`, the parity argument, and
  `eqvGen_face_of_vert`): if a vertex `v` is not on the tree paths from the endpoints of `d` to
  the root, all faces around `v` lie on the same side of the fundamental cycle of `d`; hence two
  adjacent such vertices lie on the same side.  The parity argument: the face walks of one side
  cross the cut of a subtree as often outwards as inwards, while the only unmatched crossing
  would be the tree edge above the subtree.
* **Euler's inequality** (`euler_le_two`): every connected map has `χ ≤ 2`, so `Planar` means
  "connected with maximal Euler characteristic" (`planar_iff`).
-/
namespace Chazelle.Separator
@[expose] public section
open Equiv Finset Relation
namespace CombMap
variable {V F D : Type*} (M : CombMap V F D)

/-! ### Faces joined through a set of darts -/

/-- `faceRel S f g`: some dart `e ∈ S` has `f` on its side and `g` on the other side. -/
def faceRel (S : Finset D) (f g : F) : Prop := ∃ e ∈ S, M.face e = f ∧ M.face ztcpj = g

/-- A dart set closed under `opp` (a set of edges). -/
def OppClosed (S : Finset D) : Prop := ∀ e ∈ S, M.opp e ∈ S

/-- The number of classes of faces joined through `S`. -/
noncomputable def numComp (S : Finset D) : ℕ := Nat.card (Quot zthrh)
variable {M}
variable {S S' : Finset D}
/-- Face adjacency is monotone in the dart set. -/
theorem faceRel_mono (h : S ⊆ S') {f g : F} (hfg : M.faceRel S f g) :
    M.faceRel S' f g := by
  obtain ⟨e, he, h1, h2⟩ := hfg
  exact ⟨e, h he, h1, h2⟩

/-- Face connectivity is monotone in the dart set. -/
theorem eqvGen_faceRel_mono (h : S ⊆ S') {f g : F}
    (hfg : EqvGen zthrh f g) : EqvGen (M.faceRel S') f g :=
  EqvGen.mono (fun _ _ => faceRel_mono h) _ _ hfg

/-- For an edge set (closed under `opp`), face adjacency is symmetric. -/
theorem faceRel_opp {S : Finset D} (hS : M.OppClosed S) {f g : F} (h : M.faceRel S f g) :
    M.faceRel S g f := by
  obtain ⟨e, he, rfl, rfl⟩ := h
  exact ⟨M.opp e, hS e he, rfl, by rw [M.opp_opp]⟩
variable [DecidableEq D]

/-- Adding the edge of `e` to `S` adds the pair `(face e, face (opp e))` to face adjacency. -/
theorem eqvGen_faceRel_insert (S : Finset D) (e : D) {x y : F} :
    EqvGen (M.faceRel ztxab) x y ↔
      EqvGen (fun a b => M.faceRel S a b ∨ (a = M.face e ∧ b = M.face ztcpj)) x y := by
  apply eqvGen_iff_of_le
  · rintro a b ⟨e', he', rfl, rfl⟩
    simp only [Finset.mem_insert] at he'
    rcases he' with rfl | rfl | he'
    · exact EqvGen.rel _ _ by_simp_all
    · exact EqvGen.symm _ _ (EqvGen.rel _ _ (Or.inr ⟨by rw [M.opp_opp], rfl⟩))
    · exact EqvGen.rel _ _ (Or.inl ⟨e', he', rfl, rfl⟩)
  · rintro a b (h | ⟨rfl, rfl⟩)
    · exact EqvGen.rel _ _ (faceRel_mono by_grind h)
    · exact EqvGen.rel _ _ ⟨e, by_simp, rfl, rfl⟩
variable [Finite F]

/-- Adding an edge lowers the number of face classes by at most one. -/
theorem numComp_le_insert (S : Finset D) (e : D) :
    M.numComp S ≤ M.numComp ztxab + 1 := by
  zuhqw

  exact card_quot_le_or_pair_add_one _ _ _

/-- Adding an edge whose sides are already joined does not change the face classes. -/
theorem numComp_insert_eq (S : Finset D) (e : D)
    (h : EqvGen zthrh ztjjt (M.face ztcpj)) :
    M.numComp ztxab = M.numComp S := by
  zuhqw

  exact card_quot_or_pair_eq _ _ _ h
omit [Finite F] in
/-- Adding an edge to an edge set gives an edge set. -/
theorem OppClosed.insert_pair {S : Finset D} (hS : M.OppClosed S) (e : D) :
    M.OppClosed ztxab := by
  zuh
  simp only [Finset.mem_insert] at hx ⊢
  zuief
  · simp
  · exact Or.inl ztuzz
  tauto

/-- **Counting.**  `2·#classes(S) ≤ 2·#classes(S') + |S' \ S|` for edge sets `S ⊆ S'`. -/
theorem two_mul_numComp_le {S' : Finset D} (hS' : M.OppClosed S') :
    ∀ (n : ℕ) (S : Finset D), M.OppClosed S → S ⊆ S' → (S' \ S).card = n →
      2 * M.numComp S ≤ 2 * M.numComp S' + n := by
  zugok
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS hSS' hn
  by_cases hcase : (S' \ S).Nonempty
  · obtain ⟨e, he⟩ := hcase
    rw [Finset.mem_sdiff] at he
    have hoe : M.opp e ∉ S := fun h => he.2 (by simpa [M.opp_opp] using hS _ h)
    have hoe' := hS' e he.1
    have hne := M.opp_ne e
    have hS1S' : insert e ztzwf ⊆ S' := by
      zuh
      grind
    have hcard : (S' \ insert e ztzwf).card + 2 = (S' \ S).card := by
      grind
    have h1 := ih _ by_omega _ (hS.insert_pair e) hS1S' rfl
    have h2 := M.numComp_le_insert S e
    omega
  · grind
omit [DecidableEq D] [Finite F] in
/-- With no edges, every face is its own class. -/
theorem numComp_empty : M.numComp ∅ = Nat.card F :=
  card_quot_bot _ (fun _ _ ⟨e, he, _⟩ => by_simp_all)
end CombMap

/-! ### The cotree of a spanning tree -/
namespace CombMap.SpanTree
variable {V F D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
variable {M : CombMap V F D} (T : SpanTree M)

/-- The non-tree darts. -/
def coDarts : Finset D := Finset.univ \ T.treeDarts
variable {d : D} (L : ℕ) {u : V}
/-- A dart is a non-tree dart iff it is not a tree dart. -/
theorem mem_coDarts : d ∈ T.coDarts ↔ ¬ T.IsTreeDart d := by
  simp [coDarts, T.mem_treeDarts]

/-- The opposite of a non-tree dart is a non-tree dart. -/
theorem opp_mem_coDarts (hd : d ∈ T.coDarts) : M.opp d ∈ T.coDarts := by
  rw [mem_coDarts] at hd ⊢
  zuq
  apply hd
  have := T.opp_mem_treeDarts ((T.mem_treeDarts).mpr h)
  rw [M.opp_opp] at this
  exact (T.mem_treeDarts).mp this

/-- The non-tree darts form an edge set. -/
theorem coDarts_oppClosed : M.OppClosed T.coDarts := fun _ he => T.opp_mem_coDarts he

/-! #### Cotree connectivity -/

/-- The descending potential of a tree dart. -/
noncomputable def potential (L : ℕ) (d : D) : ℕ :=
  if ∃ u, u ≠ T.root ∧ d = T.par u then L + T.level ztbmc else L - T.level ztbyq
omit [Fintype D] in
/-- The potential of an upward tree dart `par u`. -/
theorem potential_up (hu : u ≠ T.root) :
    T.potential L ztvdy = L + T.level u := by
  rw [potential, ite_eq_left by_grind, T.vert_par u hu]
omit [Fintype D] in
/-- The potential of a downward tree dart `opp (par u)`. -/
theorem potential_down (hu : u ≠ T.root) :
    T.potential L (M.opp ztvdy) = L - T.level u := by
  rw [potential, ite_eq_right]
  · rw [M.head_opp, T.vert_par u hu]
  · rintro ⟨w, hw, h⟩
    exact T.par_ne_opp_par hw hu h.symm

/-! #### The two sides of a non-tree edge -/

/-- The non-tree darts other than `d` and `opp d`. -/
def Sd (d : D) : Finset D := T.coDarts.filter (fun e => e ≠ d ∧ e ≠ M.opp d)

/-- Membership in the cotree minus the edge of `d`. -/
theorem mem_Sd {d e : D} : e ∈ T.Sd d ↔ e ∈ T.coDarts ∧ e ≠ d ∧ e ≠ M.opp d := by
  zupek

/-- The cotree minus an edge is part of the cotree. -/
theorem Sd_subset (d : D) : T.Sd d ⊆ T.coDarts := Finset.filter_subset _ _

/-- The dart `d` itself is removed. -/
theorem notMem_Sd_self (d : D) : d ∉ T.Sd d := by zupek

/-- The cotree minus an edge is an edge set. -/
theorem Sd_oppClosed (d : D) : M.OppClosed ztvdu := by
  zubre
  rw [mem_Sd] at he ⊢
  refine ⟨T.opp_mem_coDarts he.1, fun h => he.2.2 ?_, by_simp_all⟩
  zunll

/-- Removing the edge of `d` or of `opp d` is the same. -/
theorem Sd_opp (d : D) : T.Sd ztxa = T.Sd d := by
  ext e; simp only [mem_Sd, M.opp_opp]; tauto

/-- The cotree is the cotree minus the edge of `d` plus that edge. -/
theorem coDarts_eq_insert (hd : d ∈ T.coDarts) :
    T.coDarts = insert d (insert ztxa ztvdu) := by
  ext e
  simp only [Finset.mem_insert, mem_Sd]
  constructor
  · grind
  · rintro (rfl | rfl | ⟨he, -, -⟩)
    · exact hd
    · exact T.opp_mem_coDarts hd
    omega

/-! #### The Jordan property of fundamental cycles -/

/-- **Parity argument.**  Let `y` be a non-root vertex and `d` a non-tree dart whose endpoints
are both inside or both outside the subtree of `y`.  Then the two faces of the tree edge above
`y` are joined by non-tree edges other than the edge of `d`. -/
theorem face_par_eqvGen {y : V} (hy : y ≠ T.root) {d : D} (hd : d ∈ T.coDarts)
    (hiff : T.IsAnc y ztbmc ↔ T.IsAnc y ztbyq) :
    EqvGen ztcgs (M.face ztmck) (M.face (M.opp ztmck)) := by
  classical
  by_contra hK
  set R := M.faceRel _
  set A := Finset.univ.filter
    (fun e => EqvGen R _ ztjjt ∧ T.IsAnc y ztenh)
  set Bh := Finset.univ.filter
    (fun e => EqvGen R _ _ ∧ T.IsAnc y ztjjv)
  -- `fperm` maps `Bh` onto `A`
  have hAB : A.card = Bh.card := by
    symm
    apply Finset.card_nbij' (fun e => M.fperm e) (fun e => M.fperm.symm e)
    · zqbgt
      rw [M.face_fperm_apply, M.vert_fperm]; exact he
    · zqbgt
      have h1 : M.face ztuzx = M.face e := by
        rw [← M.face_fperm_apply _, Equiv.apply_symm_apply]
      have h2 : M.head ztuzx = M.vert e := by
        rw [← M.vert_fperm, Equiv.apply_symm_apply]
      grind
    · zulmo
    · zulmo
  have hLE : (A \ Bh).card = (Bh \ A).card := by
    grind
  -- the tree dart `par y` leaves the subtree
  have hpar : T.par y ∈ A \ Bh := by
    simp only [A, Bh, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    refine ⟨⟨EqvGen.refl _, by rw [T.vert_par y hy]; tauto⟩, fun _ => ?_⟩
    rw [← T.parent_of_ne hy]
    exact T.not_isAnc_parent hy
  -- `opp` maps `Bh \ A` into `(A \ Bh).erase (par y)`
  have hmaps : Set.MapsTo M.opp (Bh \ A : Finset D) ((A \ Bh).erase ztmck : Finset D) := by
    zubre
    simp only [A, Bh, Finset.coe_sdiff, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_sdiff, Set.mem_ofPred_eq, not_and] at he
    obtain ⟨⟨hKe, hin⟩, hout⟩ := he
    have hout' : ¬ T.IsAnc y _ := hout hKe
    -- `e` is a non-tree dart different from `d`, `opp d`
    have heS : e ∈ T.Sd d := by
      rw [mem_Sd, mem_coDarts]
      zusk
      · rintro ⟨x, hx, rfl | rfl⟩
        · apply hout'
          rw [T.vert_par x hx]
          have : M.head _ = T.parent x := (T.parent_of_ne hx).symm
          zvmwk at hin
          exact hin.of_parent
        · have h1 : M.head (M.opp (T.par x)) = x := by rw [M.head_opp, T.vert_par x hx]
          have h2 : M.vert _ = T.parent x := (T.parent_of_ne hx).symm
          zvmwp at hin; zvmxx at hout'
          have hxy := T.eq_of_isAnc_of_not_parent hin hout'
          simp_all
      · grind
      · zunq
        rw [M.head_opp] at hin
        tauto
    have hKo : EqvGen R _ _ :=
      EqvGen.trans _ _ _ hKe (EqvGen.rel _ _ ⟨e, heS, rfl, rfl⟩)
    simp only [A, Bh, Finset.coe_erase, Finset.coe_sdiff, Finset.coe_filter, Finset.mem_univ,
      true_and, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, not_and]
    refine ⟨⟨⟨hKo, hin⟩, fun _ => ?_⟩, ?_⟩
    · rw [M.head_opp]; omega
    · zuq
      have : e = M.opp ztmck := by zunll
      simp_all
  have hle := Finset.card_le_card_of_injOn M.opp hmaps (M.opp_injective.injOn)
  rw [Finset.card_erase_of_mem hpar] at hle
  have hpos : 0 < (A \ Bh).card := by_grind
  omega

/-- Around a vertex off the root paths of the endpoints of a non-tree dart `d`, consecutive
faces are on the same side of the fundamental cycle of `d`. -/
theorem eqvGen_face_rot (hd : d ∈ T.coDarts) {v : V}
    (hv1 : ¬ T.IsAnc v ztbmc) (hv2 : ¬ T.IsAnc v ztbyq) {e : D}
    (he : M.vert e = v) : EqvGen ztcgs ztjjt (M.face ztqab) := by
  have hrot : ztzou := by
    zugxm
  rw [hrot]
  by_cases hco : e ∈ T.coDarts
  · refine EqvGen.rel _ _ ⟨e, T.mem_Sd.mpr ⟨hco, ?_, ?_⟩, rfl, rfl⟩
    · zudsz
    · zudsz
  · rw [mem_coDarts, not_not] at hco
    obtain ⟨x, hx, rfl | rfl⟩ := hco
    · rw [T.vert_par x hx] at he
      zulsz
      exact T.face_par_eqvGen hx hd by_simp_all
    · have hxv : T.parent x = v := by
        rw [T.parent_of_ne hx]; exact he
      have hiff : T.IsAnc x ztbmc ↔ T.IsAnc x ztbyq := by
        refine iff_of_false (fun h => hv1 ?_) (fun h => hv2 ?_)
        · zuemv
        · zuemv
      zumlq
      exact EqvGen.symm _ _ (T.face_par_eqvGen hx hd hiff)

/-- **Jordan property, vertex form.**  All faces around a vertex `v` off the root paths of the
endpoints of a non-tree dart `d` lie on the same side of the fundamental cycle of `d`. -/
theorem eqvGen_face_of_vert (hd : d ∈ T.coDarts) {v : V}
    (hv1 : ¬ T.IsAnc v ztbmc) (hv2 : ¬ T.IsAnc v ztbyq) {e e' : D}
    (he : M.vert e = v) (he' : M.vert e' = v) :
    EqvGen ztcgs ztjjt (M.face e') := by
  have hsc := M.sameCycle_of_vert e e' (he.trans he'.symm)
  refine (mem_of_sameCycle M.rot
    {x | M.vert x = v ∧ EqvGen _ ztjjt _} ?_ hsc
    ⟨he, EqvGen.refl _⟩).2
  rintro x ⟨hx, hex⟩
  exact ⟨by rw [M.vert_rot, hx], EqvGen.trans _ _ _ hex (T.eqvGen_face_rot hd hv1 hv2 hx)⟩

/-- **Jordan property, edge form.**  The two endpoints of a dart `e`, both off the root paths of
the endpoints of the non-tree dart `d`, have their faces on the same side of the fundamental
cycle of `d`. -/
theorem eqvGen_face_of_dart (hd : d ∈ T.coDarts) (e : D)
    (h1 : ¬ T.IsAnc ztenh ztbmc) (h2 : ¬ T.IsAnc ztenh ztbyq)
    (h3 : ¬ T.IsAnc ztjjv ztbmc) (h4 : ¬ T.IsAnc ztjjv ztbyq)
    {x x' : D} (hx : M.vert x = M.vert e) (hx' : M.vert x' = M.head e) :
    EqvGen ztcgs ztpzx (M.face x') := by
  have hrot : ztzou := by
    zugxm
  have k1 := T.eqvGen_face_of_vert hd h1 h2 hx (M.vert_rot e)
  have k2 := T.eqvGen_face_of_vert hd h3 h4 rfl hx'
  rw [hrot] at k1
  exact EqvGen.trans _ _ _ k1 k2
section FiniteFaces
variable [Fintype F]
omit [Fintype F] in
/-- **Cotree connectivity.**  In a connected map, the faces are connected through the non-tree
edges of any spanning tree. -/
theorem eqvGen_faceRel_coDarts (hM : M.Connected) (f g : F) :
    EqvGen ztpzy f g := by
  classical
  by_contra hfg
  set K : Set F := {x | EqvGen ztpzy f x} with hK
  -- boundary darts
  set B : Finset D := Finset.univ.filter (fun d => M.face d ∈ K ∧ M.face ztxa ∉ K)
  have hKclosed : ∀ e ∈ T.coDarts, M.face e ∈ K → M.face _ ∈ K := fun e he hx =>
    EqvGen.trans _ _ _ hx ztipz
  have hBnonempty : B.Nonempty := by
    by_contra hB
    rw [Finset.not_nonempty_iff_eq_empty] at hB
    have hopp : ∀ d, M.face d ∈ K → M.face ztxa ∈ K := by
      zuip
      zumv
      have : d ∈ B := by_grind
      simp_all
    obtain ⟨d0, hd0⟩ := M.face_surj f
    obtain ⟨dg, hdg⟩ := M.face_surj g
    have := hM.of_face {d | M.face d ∈ K}
      by_simp_all
      by_simp_all (d := d0) (by simp [hK, hd0, EqvGen.refl]) dg
    simp_all
  have hBtree : ∀ d ∈ B, T.IsTreeDart d := by
    zuip
    zufao
    zumv
    exact hd.2 (hKclosed d ((T.mem_coDarts).mpr h) hd.1)
  -- successor boundary dart
  have hsucc : ∀ d ∈ B, ∃ d' ∈ B, M.vert d' = M.head d ∧ d' ≠ M.opp d := by
    zuip
    zufao
    zubaj

    have hclosed : ∀ y ∈ {x | M.vert x = M.head d ∧ M.face x ∈ K},
        M.rot y ∈ {x | M.vert x = M.head d ∧ M.face x ∈ K} := by
      rintro y ⟨hy1, hy2⟩
      refine ⟨by rw [M.vert_rot, hy1], ?_⟩
      by_contra hy3
      have hyB : y ∈ B := by
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hy2, ?_⟩
        rwa [← M.face_fperm_apply _, fperm_apply, M.opp_opp]
      grind
    have hstart : M.fperm d ∈ {x | M.vert x = M.head d ∧ M.face x ∈ K} :=
      ⟨M.vert_fperm d, by zupel; simp_all⟩
    have hsc : M.rot.SameCycle _ ztxa :=
      M.sameCycle_of_vert _ _ (by rw [M.vert_fperm]; rfl)
    exact hd.2 (mem_of_sameCycle M.rot _ hclosed hsc hstart).2
  -- the potential decreases along successors
  set L : ℕ := Finset.univ.sup T.level
  have hL : ∀ v, T.level v ≤ L := fun v => Finset.le_sup (Finset.mem_univ v)
  have hdec : ∀ d ∈ B, ∀ d' ∈ B, M.vert d' = M.head d → d' ≠ M.opp d →
      T.potential L d' < T.potential L d := by
    intro d hd d' hd' hv hne
    obtain ⟨u, hu, rfl | rfl⟩ := hBtree d hd <;> obtain ⟨u', hu', rfl | rfl⟩ := hBtree d' hd'
    · -- up, up
      rw [T.potential_up L hu, T.potential_up L hu']
      rw [T.vert_par u' hu'] at hv
      have := T.level_head_par u hu
      grind
    · -- up, down
      rw [T.potential_up L hu, T.potential_down L hu']
      have := T.level_pos hu; omega
    · -- down, up: impossible
      exfalso
      rw [T.vert_par u' hu', M.head_opp, T.vert_par u hu] at hv
      grind
    · -- down, down
      rw [T.potential_down L hu, T.potential_down L hu']
      have h1 := T.level_head_par u' hu'
      have hv' : M.head (T.par u') = u := by
        have : M.vert _ = M.head _ := hv
        rw [M.head_opp, T.vert_par u hu] at this
        tauto
      grind
  obtain ⟨d, hd, hmin⟩ := B.exists_min_image (T.potential L) hBnonempty
  obtain ⟨d', hd', hv, hne⟩ := hsucc d hd
  zubfo

/-! #### Acyclicity of the cotree in a planar map -/
omit [DecidableEq V] [DecidableEq D] in
/-- A planar map has at least one vertex. -/
theorem card_vert_pos (hM : M.Planar) : 0 < Fintype.card V := by
  zumv
  have hV : Fintype.card V = 0 := by_omega
  have hVe := Fintype.card_eq_zero_iff.mp hV
  have hD := Fintype.card_eq_zero_iff.mpr ztzik
  have hDe := Fintype.card_eq_zero_iff.mp hD
  have hF := Fintype.card_eq_zero_iff.mpr
    ⟨fun g => by obtain ⟨d, _⟩ := M.face_surj g; exact hDe.elim d⟩
  have := hM.2
  unfold euler numE at this
  omega

/-- In a planar map the cotree has `F - 1` edges. -/
theorem card_coDarts (hM : M.Planar) : T.coDarts.card + 2 = 2 * Fintype.card F := by
  have h1 : ztrfw := by
    rw [coDarts, Finset.card_sdiff_of_subset ztuyr, Finset.card_univ]
  have h2 := T.card_treeDarts
  have h3 := M.two_mul_euler
  rw [hM.2] at h3
  have hV := card_vert_pos hM
  have h4 : ztumj := Finset.card_le_univ _
  omega

/-- **The cotree is acyclic** (planar maps): no set of non-tree edges avoiding the edge of a
non-tree dart `d` joins the two faces of `d`. -/
theorem not_eqvGen_faceRel (hM : M.Planar) {S : Finset D} (hS : M.OppClosed S)
    (hSc : S ⊆ T.coDarts) {d : D} (hd : d ∈ T.coDarts) (hdS : d ∉ S) :
    ¬ EqvGen zthrh ztcci ztbaeg := by
  zuq
  have hod : M.opp d ∉ S := fun h' => hdS (by simpa [M.opp_opp] using hS _ h')
  have hne := M.opp_ne d
  have hS1c : insert d ztzwg ⊆ T.coDarts := by
    zuh
    simp only [Finset.mem_insert] at hx
    zuief
    · exact hd
    · exact T.opp_mem_coDarts hd
    grind
  have hcardS1 : (insert d ztzwg).card = S.card + 2 := by
    grind
  have e1 := M.numComp_insert_eq S d h
  have e2 := M.two_mul_numComp_le hS S.card ∅ ztqnf
    ztuyl by_simp
  have e3 := M.two_mul_numComp_le T.coDarts_oppClosed _ _ (hS.insert_pair d) hS1c rfl
  have e4 := Finset.card_sdiff_of_subset hS1c
  have e5 := M.numComp_empty
  have e6 : ztulq :=
    card_quot_le_one _ (T.eqvGen_faceRel_coDarts hM.1)
  have e7 := T.card_coDarts hM
  have e8 := Finset.card_le_card hS1c
  rw [Nat.card_eq_fintype_card] at e5
  omega

/-- The side of the fundamental cycle of `d` entered when crossing `d`: the faces joined to
`face (opp d)` by non-tree edges other than the edge of `d`. -/
noncomputable def cross (d : D) : Finset F :=
  haveI := Classical.decPred ztyaw
  Finset.univ.filter ztyaw
variable {d : D} {g : F}
/-- Membership in the side `cross d`: joined to `face (opp d)` avoiding the edge of `d`. -/
theorem mem_cross :
    g ∈ T.cross d ↔ EqvGen ztcgs ztbaeg g := by
  simp [cross]

/-- Membership in the other side `cross (opp d)`: joined to `face d`. -/
theorem mem_cross_opp_iff :
    g ∈ T.cross ztxa ↔ EqvGen ztcgs ztcci g := by
  rw [mem_cross, T.Sd_opp, M.opp_opp]

/-- The face entered through `d` lies on the side `cross d`. -/
theorem face_opp_mem_cross (d : D) : M.face ztxa ∈ T.cross d :=
  T.mem_cross.mpr ztmav

/-- A side is closed under crossing the remaining non-tree edges. -/
theorem cross_closed {d e : D} (he : e ∈ T.Sd d) (h : M.face e ∈ T.cross d) :
    M.face ztcpj ∈ T.cross d :=
  T.mem_cross.mpr (EqvGen.trans _ _ _ (T.mem_cross.mp h) ztipz)

/-- The face of `d` is not on the side entered through `d`. -/
theorem face_notMem_cross (hM : M.Planar) {d : D} (hd : d ∈ T.coDarts) :
    M.face d ∉ T.cross d := by
  rw [mem_cross]
  zuq
  exact T.not_eqvGen_faceRel hM ztvdv ztvdw hd ztvdx
    ztrja

/-- Every face is on one of the two sides of a non-tree edge. -/
theorem mem_cross_or (hM : M.Planar) {d : D} (hd : d ∈ T.coDarts) (g : F) :
    g ∈ T.cross d ∨ g ∈ T.cross ztxa := by
  have h := T.eqvGen_faceRel_coDarts hM.1 ztcci g
  rw [T.coDarts_eq_insert hd, M.eqvGen_faceRel_insert, eqvGen_or_pair_iff] at h
  rw [mem_cross_opp_iff, mem_cross]
  grind

/-- The two sides of a non-tree edge are disjoint. -/
theorem notMem_cross_opp (hM : M.Planar) {d : D} (hd : d ∈ T.coDarts) {g : F}
    (hg : g ∈ T.cross d) : g ∉ T.cross ztxa := by
  rw [mem_cross] at hg
  zumor
  zuq
  exact T.not_eqvGen_faceRel hM ztvdv ztvdw hd ztvdx
    (EqvGen.trans _ _ _ h (EqvGen.symm _ _ hg))

/-- **Nesting of sides.**  Entering through `d` into the face `face (opp d)` and leaving it
through another non-tree dart `d'` leads into a subset of the side entered through `d`. -/
theorem cross_subset (hM : M.Planar) {d d' : D} (hd : d ∈ T.coDarts) (hd' : d' ∈ T.coDarts)
    (hf : M.face d' = M.face ztxa) (hne : d' ≠ M.opp d) : T.cross d' ⊆ T.cross d := by
  zubrf
  by_contra hgd
  have hg2 : g ∈ T.cross _ := (T.mem_cross_or hM hd g).resolve_left hgd
  have hdd' : d' ≠ d := by
    grind
  have hdSd' :=
    T.mem_Sd.mpr ⟨hd, hdd'.symm, fun h => hne ztntk⟩
  have hd'Sd : d' ∈ T.Sd d := T.mem_Sd.mpr by_simp_all
  -- the face `face d' = face (opp d)` is on the far side of `d'` from `face (opp d')`
  have hfd'_opp : M.face ztxa ∈ T.cross ztuzy := by
    rw [mem_cross_opp_iff, ← hf]; exact EqvGen.refl _
  set S := (T.Sd d).filter (fun e => e ≠ d' ∧ e ≠ M.opp d')
  have hS_d : S ⊆ T.Sd d := by_grind
  have hS_d' : S ⊆ T.Sd d' := by
    zubre
    zufpn
    tauto
  -- localise `face (opp d') ~ g` to `S`
  have h1 : EqvGen zthrh (M.face ztuzy) g := by
    refine eqvGen_of_class _ _ _ ?_
      ztmav (T.mem_cross.mp hg)
    zqbgs
    have hx' := T.mem_cross.mpr hx
    zufpn
    refine ⟨⟨he.1, ?_, ?_⟩, he.2.1, he.2.2⟩
    · zunq
      have : M.face _ ∈ T.cross d' := T.cross_closed hdSd' hx'
      exact T.notMem_cross_opp hM hd' this hfd'_opp
    · zunq
      exact T.notMem_cross_opp hM hd' hx' hfd'_opp
  -- localise `face d ~ g` to `S`
  have h2 : EqvGen zthrh ztcci g := by
    refine eqvGen_of_class _ _ _ ?_
      ztmav (T.mem_cross_opp_iff.mp hg2)
    zqbgs
    have hx' : M.face e ∈ T.cross _ := T.mem_cross_opp_iff.mpr hx
    simp only [S, Finset.mem_filter]
    refine ⟨he, ?_, ?_⟩
    · zunq
      exact T.notMem_cross_opp hM hd ztrrt hx'
    · zunq
      have h' : M.face d' ∈ T.cross ztxa := by
        zumor
        exact EqvGen.trans _ _ _ hx (EqvGen.symm _ _ (EqvGen.rel _ _ ⟨d', hd'Sd, rfl, rfl⟩))
      exact T.notMem_cross_opp hM hd ztrrt h'
  -- conclude: `face (opp d') ~ face d'` inside `Sd d'`
  apply T.not_eqvGen_faceRel hM (T.Sd_oppClosed d') (T.Sd_subset d') hd' (T.notMem_Sd_self d')
  have h3 : EqvGen _ _ _ :=
    eqvGen_faceRel_mono hS_d' (EqvGen.trans _ _ _ h1 ztrjb)
  have h4 : EqvGen (M.faceRel (T.Sd d')) ztcci (M.face d') := by
    rw [hf]; exact EqvGen.rel _ _ ⟨d, hdSd', rfl, rfl⟩
  exact EqvGen.symm _ _ (EqvGen.trans _ _ _ h3 h4)
end FiniteFaces
end CombMap.SpanTree

/-! ### Euler's inequality -/
namespace CombMap
variable {V F D : Type*} [Fintype V] [DecidableEq V] [Fintype F] [Fintype D] [DecidableEq D]

/-- **Euler's inequality.**  A connected map has Euler characteristic at most `2` (the cotree of
a spanning tree connects the `F` faces with `E - V + 1` edges). -/
theorem euler_le_two (M : CombMap V F D) (hM : M.Connected) : M.euler ≤ 2 := by
  classical
  by_cases hV : Nonempty V
  · obtain ⟨r⟩ := hV
    obtain ⟨T, -, -⟩ := M.exists_bfsTree hM r
    have e1 := M.two_mul_numComp_le T.coDarts_oppClosed _ ∅ ztqnf
      ztuyl rfl
    have e2 : ztulq := card_quot_le_one _ (T.eqvGen_faceRel_coDarts hM)
    have e3 := M.numComp_empty
    rw [Nat.card_eq_fintype_card] at e3
    have e4 : ztrfw := by
      rw [SpanTree.coDarts, Finset.card_sdiff_of_subset ztuyr, Finset.card_univ]
    have e5 := T.card_treeDarts
    have e6 : ztumj := Finset.card_le_univ _
    have e7 := Fintype.card_pos_iff.mpr ⟨r⟩
    zumbf
    grind
  · have hVe := not_nonempty_iff.mp hV
    have hD : IsEmpty D := ztzik
    have hF : IsEmpty F := ⟨fun g => by obtain ⟨d, _⟩ := M.face_surj g; exact hD.elim d⟩
    unfold euler numE
    simp

/-- Planarity is extremal Euler characteristic: `M` is planar iff it is connected with `χ ≥ 2`. -/
theorem planar_iff (M : CombMap V F D) : M.Planar ↔ M.Connected ∧ 2 ≤ M.euler :=
  ⟨fun h => ⟨h.1, h.2.ge⟩, fun h => ⟨h.1, le_antisymm (M.euler_le_two h.1) h.2⟩⟩
end CombMap
end
end Chazelle.Separator
end
namespace Chazelle.Separator
@[expose] public section
open Equiv Finset Relation

/-! ### Packing groups into two parts -/
section Packing
variable {ι : Type*}
end Packing
namespace CombMap
variable {V F D : Type*} (M : CombMap V F D)

/-- A chosen dart at each vertex. -/
noncomputable def vdart (v : V) : D := Classical.choose (M.vert_surj v)

/-- The face receiving the weight of a vertex. -/
noncomputable def fv (v : V) : F := M.face (M.vdart v)
namespace SpanTree
variable [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F]
variable {M} (T : SpanTree M)

/-! ### Weights of sides and the centroid face -/

/-! ### The separator of a face and the labelling -/

/-- The vertices on the tree paths from the corners of the face `f` to the root. -/
noncomputable def sepSet (f : F) : Finset V :=
  haveI := Classical.decPred (fun v : V => ∃ e, M.face e = f ∧ T.IsAnc v ztenh)
  Finset.univ.filter (fun v => ∃ e, M.face e = f ∧ T.IsAnc v ztenh)
omit [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F] in
/-- Membership in the separator of a face: an ancestor of a corner of the face. -/
theorem mem_sepSet {f : F} {v : V} : v ∈ T.sepSet f ↔ ∃ e, M.face e = f ∧ T.IsAnc v ztenh := by
  simp [sepSet]
omit [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F] in
/-- A vertex off `sepSet f` is not on the root path of any corner of `f`. -/
theorem not_isAnc_of_notMem_sepSet {f : F} {v : V} (hv : v ∉ T.sepSet f) {e : D}
    (he : M.face e = f) : ¬ T.IsAnc v ztenh := fun h => hv (T.mem_sepSet.mpr ⟨e, he, h⟩)
omit [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F] in
/-- A vertex off `sepSet f` is not on the root path of the head of a dart of `f`. -/
theorem not_isAnc_head_of_notMem_sepSet {f : F} {v : V} (hv : v ∉ T.sepSet f) {e : D}
    (he : M.face e = f) : ¬ T.IsAnc v ztjjv := by
  rw [← M.vert_fperm]
  exact T.not_isAnc_of_notMem_sepSet hv (by zupel; exact he)
omit [DecidableEq F] in
/-- The far sides of distinct non-tree darts of one face are disjoint. -/
theorem label_unique (hM : M.Planar) {d d' : D} (hd : d ∈ T.coDarts) (hd' : d' ∈ T.coDarts)
    (hf : M.face d' = M.face d) {g : F} (hg : g ∈ T.cross d) (hg' : g ∈ T.cross d') :
    d = d' := by
  zuct
  have hsub := T.cross_subset hM (T.opp_mem_coDarts hd) hd' (by rw [M.opp_opp]; exact hf)
    (by rw [M.opp_opp]; grind)
  exact T.notMem_cross_opp hM hd hg (hsub hg')
omit [DecidableEq D] [Fintype F] in
/-- The separator of a face has at most `deg f` vertices on each level (levels shifted by
`c`). -/
theorem card_sepSet_filter_shift_le (f : F) (c : ℕ) (I : Finset ℕ) :
    ((T.sepSet f).filter ztlow).card ≤ M.faceDeg f * I.card := by
  classical
  set E := Finset.univ.filter (fun e => M.face e = f)
  have hsub : (T.sepSet f).filter ztlow ⊆
      E.biUnion (fun e => Finset.univ.filter
        (fun v => T.IsAnc v ztenh ∧ T.level v + c ∈ I)) := by
    zuml
    simp only [Finset.mem_filter, mem_sepSet] at hv
    obtain ⟨⟨e, he, hanc⟩, hl⟩ := hv
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, E]
    grind
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  rw [faceDeg, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum (fun e _ => ?_)
  refine Finset.card_le_card_of_injOn (fun v => T.level v + c) ?_ ?_
  · zuml
    simp_all
  · intro v hv v' hv' hl
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv hv'
    exact T.eq_of_isAnc_of_level_eq hv.1 hv'.1 by_simp_all
end SpanTree
variable {V F D : Type*} [Fintype D] [DecidableEq D] [DecidableEq F] (M : CombMap V F D)
section Delete
variable (n : D)

/-- The darts other than those of the edge of `n`. -/
abbrev Keep (x : D) : Prop := x ≠ n ∧ x ≠ M.opp n
omit [Fintype D] [DecidableEq D] [DecidableEq F] in
/-- The remaining darts are closed under `opp`. -/
theorem keep_opp_iff (x : D) : M.Keep n ztpzz ↔ M.Keep n x := by
  simp only [Keep]
  constructor
  · zubf
    exact ⟨fun h => h2 ztbzk, fun h => h1 ztntk⟩
  · zubf
    exact ⟨fun h => h2 (by zunll), fun h => h1 ztqaa⟩

/-- The face permutation with the two faces of `n` merged. -/
def mergePerm : Perm D := M.fperm * swap n ztxb

/-- Rotation after deleting the edge of `n`: the first-return map of `rot`. -/
noncomputable def delRot : Perm {x // M.Keep n x} := firstReturn M.rot ztgeb

/-- The opposite-dart involution restricted to the remaining darts. -/
def delOpp : Perm {x // M.Keep n x} := M.opp.subtypePerm (M.keep_opp_iff n)
omit [Fintype D] [DecidableEq D] [DecidableEq F] in
/-- The restricted `opp`. -/
theorem delOpp_apply (x : {x // M.Keep n x}) : (M.delOpp n x).1 = M.opp x.1 := rfl
omit [Fintype D] [DecidableEq F] in
/-- On the darts of the deleted edge, the merged face permutation acts like the rotation. -/
theorem mergePerm_bad {z : D} (hz : ¬ M.Keep n z) : M.mergePerm n z = M.rot z := by
  simp only [Keep, not_and_or, not_not] at hz
  rcases hz with rfl | rfl
  · simp [mergePerm, fperm_apply, M.opp_opp]
  · simp [mergePerm, fperm_apply]
omit [Fintype D] [DecidableEq F] in
/-- On the remaining darts, the merged face permutation is the face permutation. -/
theorem mergePerm_good {z : D} (hz : M.Keep n z) : M.mergePerm n z = M.fperm z := by
  simp [mergePerm, swap_apply_of_ne_of_ne hz.1 hz.2]
omit [DecidableEq F] in
/-- **The new face permutation is the first-return map of the merged face permutation.** -/
theorem deleteEdge_fperm_eq : M.delRot n * M.delOpp n = firstReturn ztmbo ztgeb := by
  zumx
  set y : {x // M.Keep n x} := M.delOpp n x
  -- iterates of `mergePerm` from `x` follow the rotation from `opp x` while outside `Keep`
  have key : ∀ j, 0 < j → (∀ i, 0 < i → i < j → ¬ M.Keep n ((M.rot ^ i) y.1)) →
      (ztmbo ^ j) x.1 = (M.rot ^ j) y.1 := by
    zujbf
    induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro _ hbad
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · zubvi
        simp only [zero_add, pow_one]
        rw [M.mergePerm_good n x.2, fperm_apply, delOpp_apply]
      · rw [pow_succ', Perm.mul_apply, ih hpos (fun i hi0 hi => hbad i hi0 by_omega),
          M.mergePerm_bad n (hbad j hpos by_omega), pow_succ', Perm.mul_apply]
  have hm := returnTime_pos M.rot ztgeb y
  have hkey := key _ hm (fun i hi0 hi => not_pow_of_lt_returnTime _ _ y hi0 hi)
  show ((firstReturn M.rot ztgeb) y).1 = ((firstReturn ztmbo ztgeb) x).1
  rw [firstReturn_apply, firstReturn_eq ztmbo ztgeb x hm, hkey]
  · rw [hkey]
    exact pow_returnTime _ _ y
  · zumgx
    rw [key i hi0 (fun i' hi0' hi' => not_pow_of_lt_returnTime _ _ y hi0' by_omega)]
    exact not_pow_of_lt_returnTime _ _ y hi0 hi
variable {n}

/-- The merged face labels. -/
def delFace (hn : M.face n ≠ M.face ztxb) (x : {x // M.Keep n x}) :
    {g : F // g ≠ M.face ztxb} :=
  if h : M.face x.1 = M.face ztxb then ⟨M.face n, hn⟩ else ⟨M.face x.1, h⟩
omit [DecidableEq D] [DecidableEq F] in
/-- The two darts of the deleted edge lie in different faces. -/
theorem not_sameCycle_n (hn : M.face n ≠ M.face ztxb) :
    ¬ M.fperm.SameCycle n ztxb := fun h =>
  hn (eq_of_sameCycle M.fperm M.face M.face_fperm h)
omit [DecidableEq F] in
/-- The merged cycles: two remaining darts are in the same merged face iff they were in the same
face or both in the faces of `n`. -/
theorem sameCycle_mergePerm_iff (hn : M.face n ≠ M.face ztxb) (x y : D) :
    (M.mergePerm n).SameCycle x y ↔
    M.face x = M.face y ∨ (ztxvh ∧
      (M.face y = M.face n ∨ M.face y = M.face ztxb)) := by
  rw [mergePerm, sameCycle_mul_swap_iff M.fperm (M.not_sameCycle_n hn), ← M.face_eq_iff_sameCycle,
    ← M.face_eq_iff_sameCycle, ← M.face_eq_iff_sameCycle, ← M.face_eq_iff_sameCycle,
    ← M.face_eq_iff_sameCycle]

/-- Equal merged face labels iff the same cycle of the merged face permutation. -/
theorem delFace_eq_iff (hn : M.face n ≠ M.face ztxb) (x y : {x // M.Keep n x}) :
    M.delFace hn x = M.delFace hn y ↔
    (M.mergePerm n).SameCycle x.1 y.1 := by
  rw [M.sameCycle_mergePerm_iff hn]
  zulul
omit [Fintype D] [DecidableEq D] [DecidableEq F] in
/-- The tail of the deleted edge has another dart. -/
theorem rot_ne_self (hn : M.face n ≠ M.face ztxb) : M.rot n ≠ n := fun h => hn (by
  rw [← M.face_fperm_apply ztxb, fperm_apply, M.opp_opp, h])
omit [Fintype D] [DecidableEq D] [DecidableEq F] in
/-- The head of the deleted edge has another dart. -/
theorem rot_opp_ne_self (hn : M.face n ≠ M.face ztxb) :
    M.rot ztxb ≠ M.opp n := fun h => hn (by
  rw [← M.face_fperm_apply n, fperm_apply, h])
omit [Fintype D] [DecidableEq F] in
/-- Every vertex keeps a dart. -/
theorem exists_keep_vert (hn : M.face n ≠ M.face ztxb)
    (hloop : ¬ ztxbe) (v : V) :
    ∃ x, M.Keep n x ∧ M.vert x = v := by
  obtain ⟨d, rfl⟩ := M.vert_surj v
  by_cases hd : M.Keep n d
  · tauto
  simp only [Keep, not_and_or, not_not] at hd
  have hr1 := M.rot_ne_self hn
  have hr2 := M.rot_opp_ne_self hn
  rcases hd with rfl | rfl
  · by_cases h : M.rot d = M.opp d
    · have h' : M.rot ztxa ≠ d := fun h' => hloop ztfwk
      refine ⟨M.rot ztxa, ⟨h', hr2⟩, ?_⟩
      rw [M.vert_rot, ← h, M.vert_rot]
    · exact ⟨M.rot d, ⟨hr1, h⟩, M.vert_rot d⟩
  · by_cases h : M.rot ztxb = n
    · have h' : M.rot n ≠ M.opp n := fun h' => hloop ⟨h', h⟩
      refine ⟨M.rot n, ⟨hr1, h'⟩, ?_⟩
      calc M.vert (M.rot n) = M.vert n := M.vert_rot n
        _ = M.vert (M.rot ztxb) := by zvmwc
        _ = M.vert ztxb := M.vert_rot _
    · exact ⟨M.rot ztxb, ⟨h, hr2⟩, M.vert_rot _⟩
omit [Fintype D] [DecidableEq F] in
/-- The merged face keeps a dart. -/
theorem exists_keep_merged (hn : M.face n ≠ M.face ztxb)
    (hloop : ¬ ztxbe) : ∃ x, M.Keep n x ∧
    ztxvh := by
  have hf1 : M.fperm n ≠ M.opp n := fun h => hn (by rw [← h, M.face_fperm_apply])
  have hf2 : M.fperm ztxb ≠ n := fun h => hn (by rw [← M.face_fperm_apply ztxb, h])
  by_cases h1 : M.fperm n = n
  · have h2 : M.fperm ztxb ≠ M.opp n := by
      zukji
      apply hloop
      rw [fperm_apply] at h1 h2
      rw [M.opp_opp] at h2
      simp_all
    exact ⟨M.fperm ztxb, ⟨hf2, h2⟩, Or.inr ztuzt⟩
  · exact ⟨M.fperm n, ⟨h1, hf1⟩, Or.inl ztuzt⟩

/-- **Deleting an edge between two distinct faces.** -/
noncomputable def deleteEdge (hn : M.face n ≠ M.face ztxb)
    (hloop : ¬ ztxbe) :
    CombMap V {g : F // g ≠ M.face ztxb} {x // M.Keep n x} where
  rot := M.delRot n
  opp := M.delOpp n
  vert x := M.vert x.1
  face := M.delFace hn
  opp_opp x := Subtype.ext (M.opp_opp x.1)
  opp_ne x h := M.opp_ne x.1 (congrArg Subtype.val h)
  vert_rot x := by
    show M.vert ((M.delRot n x).1) = M.vert x.1
    rw [delRot, firstReturn_apply]
    exact (eq_of_sameCycle M.rot M.vert M.vert_rot ⟨(returnTime M.rot ztgeb x : ℤ),
      by simp⟩).symm
  sameCycle_of_vert x y h := by
    rw [delRot, sameCycle_firstReturn_iff]
    exact M.sameCycle_of_vert _ _ h
  face_fperm x := by
    show M.delFace hn ((M.delRot n * M.delOpp n) x) = M.delFace hn x
    rw [M.deleteEdge_fperm_eq n, M.delFace_eq_iff hn, ← sameCycle_firstReturn_iff]
    exact (Perm.SameCycle.refl _ _).symm.trans ⟨1, by_simp⟩ |>.symm
  sameCycle_of_face x y h := by
    rw [M.deleteEdge_fperm_eq n, sameCycle_firstReturn_iff]
    exact (M.delFace_eq_iff hn x y).mp h
  vert_surj v := by
    obtain ⟨x, hx, hv⟩ := M.exists_keep_vert hn hloop v
    exact ⟨ztfxa, hv⟩
  face_surj g := by
    by_cases hg : g.1 = M.face n
    · obtain ⟨x, hx, hxf⟩ := M.exists_keep_merged hn hloop
      refine ⟨ztfxa, Subtype.ext ?_⟩
      zulul

    · obtain ⟨d, hd⟩ := M.face_surj g.1
      have hk : M.Keep n d := ⟨fun h => hg by_simp_all, fun h => g.2 by_simp_all⟩
      refine ⟨⟨d, hk⟩, Subtype.ext ?_⟩
      zulul
variable [Fintype V] [Fintype F]
end Delete

/-! ### Contraction as deletion in the dual -/
section Contract
variable [DecidableEq V] {n : D} (hn : M.vert n ≠ M.vert (M.opp n))
  (hiso : ¬ (M.fperm n = M.opp n ∧ M.fperm ztxb = n))
end Contract
end CombMap
end
end Chazelle.Separator
namespace Chazelle.Separator
@[expose] public section
open Finset

/-- The numerical heart of the recursion: pieces of size at most `M/2` with total at most `M`,
`M > s`, satisfy `s + Σ (2 m_d − s) ≤ 2M − s` (truncated subtraction). -/
theorem sum_split_bound {ι : Type*} [DecidableEq ι] (L : Finset ι) (m : ι → ℕ) (M s : ℕ)
    (hsum : ∑ d ∈ L, m d ≤ M) (hhalf : ∀ d ∈ L, 2 * m d ≤ M) (hMs : s < M) :
    s + ∑ d ∈ L, ztfff ≤ 2 * M - s := by
  set J := L.filter (fun d => s < 2 * m d)
  have hJ : ∑ d ∈ L, ztfff = ∑ d ∈ J, ztfff := by
    rw [Finset.sum_filter]
    grind
  have hkey : ∑ d ∈ J, ztfff + J.card * s = 2 * ∑ d ∈ J, m d := by
    rw [Finset.mul_sum, ← smul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ztbzy
    grind
  have hJsum : ∑ d ∈ J, m d ≤ M :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      ztnyk) hsum
  rw [hJ]
  rcases Nat.lt_or_ge J.card 2 with h | h
  · rcases (show J.card = 0 ∨ J.card = 1 by omega) with h0 | h1
    · rw [Finset.card_eq_zero.mp h0, Finset.sum_empty]; omega
    · obtain ⟨d, hd⟩ := Finset.card_eq_one.mp h1
      grind
  · have : 2 * s ≤ J.card * s := Nat.mul_le_mul_right s h
    omega
namespace CombMap
variable {V F D : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F] [Fintype D]
  [DecidableEq D]
namespace SpanTree
variable {M : CombMap V F D} (T : SpanTree M)
end SpanTree

/-! ### Slabs of levels -/
section Slabs
end Slabs
end CombMap
end
end Chazelle.Separator
namespace Chazelle.Core
@[expose] public section
open Chazelle.Machine (Stmt)
open Chazelle.Chain (sideInArc)

/-! ## Bands -/

/-- Band of the sign kernel (WP-A). -/
def bSign : ℕ := 1
/-- Band of sorting (WP-C). -/
def bSort : ℕ := 3
/-- Band of normal-form construction (WP-C). -/
def bBuild : ℕ := 4
/-- Band of double identification (WP-C). -/
def bLocate : ℕ := 5
/-- Band of the tree decomposition (WP-C). -/
def bDecomp : ℕ := 6
/-- Band of the fusion (WP-D). -/
def bFuse : ℕ := 7
/-- Band of conformality restoration (WP-E). -/
def bRestore : ℕ := 8
/-- Band of granularity enforcement (WP-F). -/
def bGran : ℕ := 9
/-- Band of the merge driver (WP-F). -/
def bMerge : ℕ := 10
/-- Band of oracle preprocessing (WP-H). -/
def bOPrep : ℕ := 11
/-- Band of oracle queries (WP-H). -/
def bOQuery : ℕ := 12
/-- Band of the cluster algorithm (WP-I). -/
def bCluster : ℕ := 13
/-- Band of the ray-shooter for merges (WP-G). -/
def bShoot : ℕ := 14
/-- Band of the arc-cutter (WP-G). -/
def bCut : ℕ := 15
/-- Band of Lemma 4.1 (WP-J). -/
def bL41 : ℕ := 16
/-- Band of the up-phase driver (WP-J). -/
def bUp : ℕ := 17
/-- Band of brute-force maps (WP-K). -/
def bBrute : ℕ := 18
/-- Band of the transition to the interior model (WP-M). -/
def bTrans : ℕ := 19
/-- Band of the down step (WP-M). -/
def bDown : ℕ := 20
/-- Band of the down-phase driver (WP-M). -/
def bDownDrv : ℕ := 21
/-- Band of the core driver (WP-L). -/
def bCore : ℕ := 23
/-- Band of the sweep of the fusion (WP-D; added in the consolidated revision, design doc §10). -/
def bSweep : ℕ := 24

/-- The leaf toolkit (sign kernel, sorting, normal-form construction, double identification,
tree decomposition): scratch bands that any call may clobber; no caller keeps state in them.
(Review finding F6: every package now writes a fixed band set, so callers know what survives.) -/
def kernelBands : Finset ℕ := {bSign, bSort, bBuild, bLocate, bDecomp}

/-- The bands an oracle (ray-shooter, arc-cutter, Lemma 3.6 query) may write. -/
def oracleBands : Finset ℕ := kernelBands ∪ {bOQuery, bShoot, bCut, bCluster}

/-- The bands of granularity enforcement. -/
def granBands : Finset ℕ := kernelBands ∪ {bGran}

/-- The bands of the sweep itself (without its oracle). -/
def sweepBands : Finset ℕ := kernelBands ∪ {bSweep}

/-- The bands of the fusion itself (the fusion driver and its sweeps, without their oracle). -/
def fuseBands : Finset ℕ := kernelBands ∪ {bFuse, bSweep}

/-- The bands of conformality restoration itself (without its oracles). -/
def restoreBands : Finset ℕ := kernelBands ∪ {bRestore}

/-- The bands of a merge itself (without its oracles). -/
def mergeBands : Finset ℕ := kernelBands ∪ {bFuse, bRestore, bGran, bMerge, bSweep}

/-- Register `i` of band `b` in the configuration `c`. -/
def rd (c : Config) (b i : ℕ) : ℕ := c.nreg zttgm

/-- The geometric environment of every procedure: a simple input with a good shear, so that
`Qof P` is the (simple, distinct-heights) geometry polygon. -/
def GoodEnv (P : Polygon) : Prop := P.Simple ∧ ∃ ε, GoodShear P ε

/-! ## WP-A: the sign kernel -/

/-- A symbolic point held in three registers from `r` on: kind (`0` vertex, `1` edge point) and
its indices. -/
def SymPtIn (c : Config) (r : ℕ) : SymPt → Prop
  | .vtx i => c.nreg r = 0 ∧ c.nreg ztgu = i
  | .onEdge e h => c.nreg r = 1 ∧ c.nreg ztgu = e ∧ c.nreg ztbcu = h

/-- The four sign tests: `0` abscissa order, `1` ordinate order, `2` positive orientation,
`3` collinearity. -/
def SignTest (op : ℕ) (a b d : Point) : Prop :=
  match op with
  | 0 => a.1 < b.1
  | 1 => a.2 < b.2
  | 2 => 0 < det a b d
  | _ => det a b d = 0

/-! ## WP-C: the normal-form toolkit -/

/-- A list of chord triples `(h, lp, rp)` at `A`, three words each. -/
def ChordListAt (m : ℕ → ℕ) (A : ℕ) (L : List zte) : Prop :=
  ∀ i, i < L.length →
    m (A + 3 * i) = (L.getD i ztt).1 ∧ m ztnif = (L.getD i ztt).2.1 ∧
      m ztnig = (L.getD i ztt).2.2

/-- The chord record of a triple (regions unknown). -/
def recOf (x : ℕ × ℕ × ℕ) : CRec := ⟨x.1, x.2.1, x.2.2, 0, 0⟩

/-- The triples describe distinct, admissible, correctly attached chords of `M`. -/
def ChordTriplesOK (M : Model) (Q : Polygon) (L : List zte) : Prop :=
  M.ChordFamily Q {c | ∃ x ∈ L, c = (recOf x).toSet M Q} ∧
    (L.map fun x => (recOf x).toSet M Q).Nodup ∧ (∀ x ∈ L, (recOf x).Attached M Q) ∧
    ∀ x ∈ L, x.1 < Q.n

/-- **WP-C: normal form from a chord list.**  Inputs: model descriptor (register `0`), chord
list base (`1`) and length (`2`).  Output (`3`): a fresh normal-form handle whose chords are the
given ones in the given order (no decomposition).  Cost `κ (K (⌈log₂ K⌉ + 1) + 1)`.
(Consolidated revision: the descriptor is well formed and the descriptor and the chord list lie
below the allocator, findings C7/C8; the output's arc records are proper positions, part of
`IsNF`, finding C6; the side regions of each chord are fixed by `UpSideSpec`, finding C10.) -/
def BuildNFSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s {bBuild, bSort, bSign}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      ModelDescWF P ztm c.nmem ztue ∧
      ∃ M L, ModelDescAt c.nmem ztue zta M ∧
      GoodModel M ∧ rd c bBuild 2 = L.length ∧ rd c bBuild 1 + 3 * L.length ≤ c.nreg ALLOC ∧
      ChordListAt c.nmem ztbis L ∧ ChordTriplesOK M zta L)
    (fun P c c' => ∀ M L, ModelDescAt c.nmem ztue zta M →
      rd c bBuild 2 = L.length → ChordListAt c.nmem ztbis L →
        ∃ N, c.nreg ALLOC ≤ rd c' bBuild 3 ∧ NFWithin c'.nmem ztdph ztdo N ∧
          IsNF M zta N ∧ N.chords.map ztwma = L ∧ N.dec = [])
    ztzj

/-- **WP-C: tree decomposition** (§2.3).  Inputs: model descriptor (`0`), normal form (`1`),
degree cap `D` (`2`).  Output (`3`): a fresh copy with a decomposition of depth
`decDepth D K`.  Cost `κ (D + 1) (K (⌈log₂ K⌉ + 1) + 1)`.  (Consolidated revision: well-formed
descriptor and input below the allocator, findings C7/C8.) -/
def DecompSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s {bDecomp}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      ModelDescWF P ztm c.nmem ztefq ∧
      ∃ M N, ModelDescAt c.nmem ztefq zta M ∧
      GoodModel M ∧ NFWithin c.nmem ztczz ztm N ∧ IsNF M zta N ∧
      M.DegLe ztwiv zthzw)
    (fun P c c' => ∀ M N, ModelDescAt c.nmem ztefq zta M →
      NFAt c.nmem ztczz N → IsNF M zta N →
        ∃ N', c.nreg ALLOC ≤ rd c' bDecomp 3 ∧
          NFWithin c'.nmem ztrvn ztdo N' ∧
          N'.chords = N.chords ∧ N'.arcs = N.arcs ∧ N'.regions = N.regions ∧ N'.seq = N.seq ∧
          IsDecomp N' ztzvn)
    (fun _ c => κ * ztpdd *
      ztxkr)

/-! ## Oracle interfaces for the merges -/

/-- A **memory context**: a property of the memory below a bound, found through a handle (the
up-phase data: canonical submaps and oracle structures of all processed chains, reached through
the grade table), insensitive to the memory above the bound, together with the largest weight
bound `cap` it supports. -/
structure MemCtx where
  /-- `holds P m g A`: the memory `m` holds the context at handle `g`, below address `A`. -/
  holds : Polygon → ztjx → ℕ → ℕ → Prop
  /-- The largest arc weight the oracles built on the context support. -/
  cap : Polygon → ztjx → ℕ → ℕ
  /-- Locality. -/
  local_ : ∀ P m m' g A, (∀ a, a < A → m a = m' a) → holds P m g A → holds P m' g A
  /-- Monotonicity in the bound. -/
  mono : ∀ P m g A A', A ≤ A' → holds P m g A → holds P m g A'

/-- **Capacity locality** (review finding E4): the capacity read at a handle does not change when
the memory changes at or above a bound below which the context holds.  Procedures that allocate
before calling an oracle (restore, fusion, sweep, merge) need it to re-establish the oracles'
precondition `γ ≤ cap`; the contexts of the project (`gradeCtx`) have it (`gradeCtx_capLocal`). -/
def MemCtx.CapLocal (X : MemCtx) : Prop :=
  ∀ P m m' g A, ztwv → X.holds P m g A → X.cap P m' g = X.cap P m g

/-- **A halving table** (review finding R-D3): the context stores `⌊x / 2⌋` for `x ≤ n` at the
address read at `g + 3`.  The RAM has no division, and the search of Lemma 3.2 halves the codes of
a tree decomposition at every node of its descent; with the table this costs `O(1)`.  The
contexts of the project (`gradeCtx`) have it (`gradeCtx_halves`). -/
def MemCtx.Halves (X : MemCtx) : Prop :=
  ∀ P m g A, X.holds P m g A → g + 3 < A ∧
    ∀ x, x ≤ P.n → m ztnzs + x < A ∧ m (m ztnzs + x) = x / 2

/-- The points of the walk with keys in the closed cyclic interval `[a, b]`. -/
def Model.arcSet (M : Model) (a b : ℝ) : Set Point :=
  {x | ∃ p : ℕ, ∃ t : ℝ, p < M.W.n ∧ 0 ≤ t ∧ t ≤ 1 ∧
    (sideInArc a b ztk ∨ (p : ℝ) + t = a ∨ (p : ℝ) + t = b) ∧
      x = Geometry.lerp ztpr ztoa t}

/-- The first hit of the horizontal ray from `p` in direction `σ` on the set `A` is at
parameter `t`. -/
def FirstHit (A : Set Point) (p : Point) (σ t : ℝ) : Prop :=
  0 < t ∧ Visibility.rayPt p σ t ∈ A ∧ ∀ t', 0 < t' → t' < t → Visibility.rayPt p σ t' ∉ A

/-- The horizontal ray from `p` in direction `σ` misses `A`. -/
def NoHit (A : Set Point) (p : Point) (σ : ℝ) : Prop :=
  ∀ t, 0 < t → Visibility.rayPt p σ t ∉ A

/-- The direction coded by a register value (`1` right, otherwise left). -/
def dirOf (v : ℕ) : ℝ := if v = 1 then 1 else -1

/-- **A ray origin** of a merge (review finding F5): the fusion shoots from chord endpoints, which
are symbolic points of `Q` or points of the model's walk (box and slit edges included). -/
inductive Origin where
  /-- A symbolic point of `Q`. -/
  | sym (p : SymPt)
  /-- A walk position of the model. -/
  | walk (x : WPos)
  deriving DecidableEq

/-- An origin held in three registers from `r` on: kinds `0, 1` as `SymPtIn`, kind `2` a walk
position (edge, height code). -/
def OriginIn (c : Config) (r : ℕ) : Origin → Prop
  | .sym p => SymPtIn c r p
  | .walk x => c.nreg r = 2 ∧ c.nreg ztgu = x.edge ∧ c.nreg ztbcu = x.hgt

/-- The indices of an origin are in range. -/
def Origin.Lt (n : ℕ) (M : Model) : Origin → Prop
  | .sym p => p.Lt n
  | .walk x => x.edge < M.W.n ∧ x.hgt ≤ n

/-- The Euclidean point of an origin. -/
noncomputable def Origin.eval (M : Model) (Q : Polygon) : Origin → Point
  | .sym p => p.eval Q
  | .walk x => M.pos Q x

/-- **An inner point** of a model (review finding G2): strictly between the heights of two walk
vertices and between the abscissae of two walk vertices (for a chain model: inside the box
height band).  Shots from other points, or at subarcs ending at other non-vertex points, may
depend on the box radius, a sum over all host vertices, which the shooter cannot afford to read. -/
def Model.InnerPt (M : Model) (z : Point) : Prop :=
  (∃ p q, p < M.W.n ∧ q < M.W.n ∧ (M.W.vtx p).2 < z.2 ∧ z.2 < (M.W.vtx q).2) ∧
    (∃ p q, p < M.W.n ∧ q < M.W.n ∧ (M.W.vtx p).1 ≤ z.1 ∧ z.1 ≤ (M.W.vtx q).1)

/-- **The ray-shooter interface** (p. 501 (i)).  `sh` answers, for a model `M` accepted by `Ok`
(registers `0`: model descriptor; `1, 2` and `3, 4`: the ends of a subarc; `5 … 7`: the query
point (an `Origin`); `8`: the direction; `9`: a bound `γ ≤ cap` on the counted edges of the subarc; `13`: the
context handle), the first point of the subarc hit by the ray (register `10`: hit flag; `11, 12`:
its walk position), in at most `F γ` steps, provided the context `X` (the up-phase data) is in
memory below the allocator.  (Consolidated revision: the model descriptor is well formed and
below the allocator, the subarc ends are proper positions, findings C6–C8; the origin is a walk
vertex or an inner point, and non-vertex subarc ends are inner points, finding G2.) -/
def ShooterOK (sh : Stmt) (B : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) : Prop :=
  Meets sh B
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      X.holds P c.nmem ztefx ztm ∧
      rd c bShoot 9 ≤ X.cap P c.nmem ztefx ∧
      ModelDescWF P ztm c.nmem ztbrn ∧
      (c.nmem ztbrn = 0 → ∀ H C, ChainDescAt c.nmem ztfih zta H C →
        HostRegular (Qof P).n H) ∧
      ∃ M, ModelDescAt c.nmem ztbrn zta M ∧ Ok P M ∧
        ProperPos M zta P.n ztnp ∧
        ProperPos M zta P.n ztnq ∧
        rd c bShoot 1 < M.W.n ∧ rd c bShoot 3 < M.W.n ∧
        ztwwl ∧
        ztwwm ∧
        M.arcWt ztwwa
          ztwwb ≤ rd c bShoot 9 ∧
        ∃ o : Origin, o.Lt P.n M ∧ OriginIn c ztbpu o ∧
          (ztbnv ∨ (M.InnerPt ztwle ∧
            ∀ x, o = .walk x → ProperPos M zta P.n x)) ∧
          o.eval M zta ∉ M.arcSet ztwwa
            ztwwb)
    (fun P c c' => ∀ M (o : Origin), ModelDescAt c.nmem ztbrn zta M →
      OriginIn c ztbpu o →
        let A := M.arcSet ztwwa
          ztwwb
        (rd c' bShoot 10 = 1 → ∃ t, FirstHit A ztwle ztbqc t ∧
          ProperPos M zta P.n ztdqv ∧ rd c' bShoot 11 < M.W.n ∧
          M.pos zta ztdqv =
            Visibility.rayPt ztwle ztbqc t) ∧
        ztbamj)
    ztyvx

/-- The walks `W` and `W'` **agree** on the stretch of length `L` starting at their vertices `g`
and `g'` (indices modulo the lengths); the same as `WalkEmbed.Agree`, stated here to keep the
specification files free of implementation imports. -/
def WalkAgree (W W' : Polygon) (g g' L : ℕ) : Prop :=
  ∀ d, d ≤ L → W.vtx ztwnv = W'.vtx ztwtx

/-- **The walk of a kind-1 piece** (review finding E5).  The piece of the walk of `M` from the
walk vertex `s` to the walk vertex `e` traverses the chain `Cα` on one side, as `Cα.m`
consecutive walk edges.  It agrees with the walk of `chainModel Cα` either along one stretch, or
along two stretches that meet at the top of `Cα`, where the walk of `chainModel Cα` leaves up
the slit (walk vertex `2 m + 6`) and comes back down (walk vertex `6`). -/
def PieceWalk (M : Model) (Cα : Chain) (s e : WPos) : Prop :=
  s.hgt = 0 ∧ e.hgt = 0 ∧ s.edge < M.W.n ∧ e.edge = (s.edge + Cα.m) % M.W.n ∧
    ∃ g' : ℕ, g' < (chainModel Cα).W.n ∧
      (WalkAgree M.W (chainModel Cα).W s.edge g' Cα.m ∨
        ∃ L₁, 0 < L₁ ∧ L₁ < Cα.m ∧ g' + L₁ = 2 * Cα.m + 6 ∧
          WalkAgree M.W (chainModel Cα).W s.edge g' L₁ ∧
          WalkAgree M.W (chainModel Cα).W ((s.edge + L₁) % M.W.n) 6 (Cα.m - L₁))

/-- **The arc-cutter interface** (p. 501 (ii)).  Inputs as for the shooter (registers `0 … 4`,
bound `γ ≤ cap` in `9`, context handle in `13`).  Output (`10`): a fresh piece list — its length `q ≤ G γ`, then seven words
per piece: the two ends (walk positions), a kind (`0` a single-edge end piece, `1` a
vertex-to-vertex piece), a chain descriptor and a normal-form handle.  The pieces tile the subarc
in order; a piece of kind `1` covers the point set of its chain once (no double-backing) and
carries a `γ'`-canonical normal form of it (degree cap `4`) for some `γ' ≤ H γ` (review finding
F2: the paper, p. 517, bounds the granularity of the pieces, it does not fix it); its chain is a
chain of `Qof P` and its walk visits the vertices of the chain upward or downward (finding R-D2:
the search descends the normal form in the chain's own model, which must satisfy the walk axioms,
and converts positions between the two walks).  The piece list
lies below the new allocator (finding F8), and so do the pieces' descriptors (well formed) and
normal forms (consolidated revision, findings C7/C8).  A kind-`1` piece's walk agrees with its
chain's model walk (`PieceWalk`, finding E5). -/
def CutterOK (cu : Stmt) (B : Finset ℕ) (G H : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) : Prop :=
  Meets cu B
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ X.holds P c.nmem zthzu ztm ∧
      rd c bCut 9 ≤ X.cap P c.nmem zthzu ∧
      ModelDescWF P ztm c.nmem ztfub ∧
      ∃ M, ModelDescAt c.nmem ztfub zta M ∧ Ok P M ∧
        ProperPos M zta P.n ztbgi ∧
        ProperPos M zta P.n ztxu ∧
        rd c bCut 1 < M.W.n ∧ rd c bCut 3 < M.W.n ∧
        ztxrd ∧
        ztxre ∧
        M.arcWt ztzua
          ztzub ≤ rd c bCut 9)
    (fun P c c' => ∀ M, ModelDescAt c.nmem ztfub zta M →
      let L := rd c' bCut 10
      let q := c'.nmem L
      let pc := fun (i j : ℕ) => c'.nmem ztlfb
      let key := fun (e h : ℕ) => M.key zta ztcq
      c.nreg ALLOC ≤ L ∧ L + 1 + 7 * q ≤ c'.nreg ALLOC ∧ q ≤ G ztbit ∧ 1 ≤ q ∧
      key zttvw zttvx = key zthzt zthzv ∧
      key ztzxp ztzxq = key ztcog ztefp ∧
      ztwyi ∧
      (∀ i, i + 1 < q → sideInArc ztzn (key ztcog ztefp)
        ztzo) ∧
      (∀ i, i < q → pc i 4 = 0 → M.arcWt ztzn ztzo ≤ 1) ∧
      (∀ i, i < q → pc i 4 = 1 → ChainWF P ztdo c'.nmem ztkcg ∧
        ∃ Hs Cα N, ChainDescAt c'.nmem ztkcg zta Hs Cα ∧
        NFWithin c'.nmem zttwa ztdo N ∧
        (∃ γ', γ' ≤ H ztbit ∧ IsCanonicalNF ztbdc zta N γ' 4) ∧
        M.arcSet ztzn ztzo = Cα.set ∧
        M.arcWt ztzn ztzo = Cα.m ∧
        PieceWalk M Cα zteyu zteyv ∧ Cα.P = Qof P ∧
        ((∀ d, d ≤ Cα.m → M.W.vtx ztbaac = Cα.vertex d) ∨
          (∀ d, d ≤ Cα.m → M.W.vtx ztbaac = Cα.vertex ztclf))) ∧
      (∀ i, i < q → ProperPos M zta P.n zteyu ∧
        ProperPos M zta P.n zteyv ∧ pc i 0 < M.W.n ∧ pc i 2 < M.W.n) ∧
      ztiup)
    (fun _ c => G ztbit)

/-! ## WP-H: the oracle of Lemma 3.6 -/

/-- **An oracle implementation** (Lemma 3.6): a predicate `At P m O` ("the memory holds at `O` a
structure for the chain and normal form recorded at `O`, `O + 1`, with granularity at `O + 2`"),
a preprocessing and a query statement. -/
structure OracleIface where
  /-- The structure predicate. -/
  At : Polygon → ztjx → ℕ → Prop
  /-- Preprocessing. -/
  prep : Stmt
  /-- Query. -/
  query : Stmt
  /-- The bands written. -/
  bands : Finset ℕ
  /-- The cost constant. -/
  κ : ℕ

/-- **A query origin** of the Lemma 3.6 structure: a symbolic point of `Q`, or the point of the
box of the structure's chain at the height of vertex `h` on the side the ray comes from (rays
from box, slit or far points reduce to this: review finding F5). -/
inductive QOrigin where
  /-- A symbolic point of `Q`. -/
  | sym (p : SymPt)
  /-- The box point at the height of vertex `h`, on the side opposite to the ray direction. -/
  | box (h : ℕ)
  deriving DecidableEq

/-- A query origin in registers from `r` on: kinds `0, 1` as `SymPtIn`, kind `2` a box point. -/
def QOriginIn (c : Config) (r : ℕ) : QOrigin → Prop
  | .sym p => SymPtIn c r p
  | .box h => c.nreg r = 2 ∧ c.nreg ztgu = h

/-- The indices of a query origin are in range. -/
def QOrigin.Lt (n : ℕ) : QOrigin → Prop
  | .sym p => p.Lt n
  | .box h => h < n

/-- The point of a query origin for the chain `C` and the ray direction `σ`. -/
noncomputable def QOrigin.eval (Q : Polygon) (C : Chain) (σ : ℝ) : QOrigin → Point
  | .sym p => p.eval Q
  | .box h => (-σ * C.radius, (Q.vtx h).2)

/-- **Validity of an oracle implementation.**
* Preprocessing (band `bOPrep`): from a well-formed chain descriptor (`0`) of a chain of the
  geometry polygon and a `γ`-canonical normal form (`1`) of it, both below the allocator (`γ` in `2`, degree cap `4`), builds a fresh
  structure (`3`) in at most `κ (K (⌈log₂ m⌉ + 1) + 1)` steps (`K` chords, `m` edges); the
  structure lies below the new allocator.
* Bands: at most `oracleBands ∪ {bOPrep}` for the preprocessing (review finding F6), and
  `kernelBands ∪ {bOQuery}` for the query (findings G3, G5: the shooter calls queries inside its
  own frame and keeps its state in the bands `bShoot`, `bCut` across them).
* Query (band `bOQuery`): from a structure (`0`), a query origin (`1 … 3`) and a direction
  (`4`), reports the first hit of the ray on the chain (`5`: flag; `6`: the hit edge of `Q`) in
  at most `κ (γ^{1/3} (m + 1)^{2/3} + 1)` steps. -/
def OracleIface.Valid (O : OracleIface) : Prop :=
  O.bands ⊆ oracleBands ∪ {bOPrep} ∧
  Meets O.prep O.bands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ ChainWF P ztm c.nmem zthzz ∧
      ∃ H C N, ChainDescAt c.nmem zthzz zta H C ∧
      C.P = Qof P ∧ NFWithin c.nmem ztiaa ztm N ∧
      IsCanonicalNF ztc zta N ztrvm 4)
    (fun P c c' => c.nreg ALLOC ≤ rd c' bOPrep 3 ∧ rd c' bOPrep 3 + 3 ≤ c'.nreg ALLOC ∧
      c'.nmem ztiaf = rd c bOPrep 0 ∧ c'.nmem ztpdh = rd c bOPrep 1 ∧
      c'.nmem ztpdi = rd c bOPrep 2 ∧
      ∀ m', ztdwr → O.At P m' ztiaf)
    (fun _ c => O.κ * (c.nmem ztiaa *
      zthbp + 1)) ∧
  Meets O.query (kernelBands ∪ {bOQuery})
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ O.At P c.nmem ztdpg ∧
      ∃ o : QOrigin, o.Lt P.n ∧ QOriginIn c ztdtv o)
    (fun P c c' => ∀ H C (o : QOrigin),
      ChainDescAt c.nmem ztbaga zta H C →
      QOriginIn c ztdtv o →
        let z := o.eval zta C ztbqb
        (rd c' bOQuery 5 = 1 → ∃ t, FirstHit C.set z ztbqb t ∧
          rd c' bOQuery 6 < P.n ∧
          Visibility.rayPt z ztbqb t ∈ (Qof P).edge ztrvp) ∧
        ztxxw)
    (fun _ c => ⌈(O.κ : ℝ) * ((c.nmem ztpde : ℝ) ^ ztby *
      ztxqe ^ ztcd + 1)⌉₊)

/-! ## WP-I: clusters of a planar map in memory -/

/-- A combinatorial map with `μ` vertices and `2 E` darts stored at `B`: the bases of the
`opp`, `rot`, `vert` arrays at `B`, `B + 1`, `B + 2`; it is planar. -/
def PlanarMapAt (m : ℕ → ℕ) (B μ E : ℕ) : Prop :=
  ∃ (F : Type) (_ : Fintype F) (_ : DecidableEq F)
    (M : Separator.CombMap ztemr F ztzbw), M.Planar ∧
      ∀ d : Fin ztdsj, m ztlrc = M.opp d ∧ m (m ztvf + d) = M.rot d ∧
        m ztzmw = M.vert d

/-- A dart of the map stored at `B` goes from `u` to `v`. -/
def MemDart (m : ℕ → ℕ) (B E : ℕ) (u v : ℕ) : Prop :=
  ∃ d, d < 2 * E ∧ m ztzmw = u ∧ m (m zthb + m ztlrc) = v

/-- The (simple) graph of the map stored at `B`, on the vertices `Fin μ`. -/
def memGraph (m : ℕ → ℕ) (B μ E : ℕ) : SimpleGraph ztemr where
  Adj u v := u ≠ v ∧ (MemDart m B E u v ∨ MemDart m B E v u)
  symm := ⟨by
    grind⟩
  loopless := ⟨by_omega⟩
open Set Filter Topology
open Chazelle.Chain (IsHChordIn)
open Chazelle.Visibility (hseg chords chordSet rayPt)
open Chazelle.Geometry (lerp point_ext)
namespace DownBase
def wStart (li : Bool) (n p : ℕ) : ℕ := if li then p else n - 1 - p

/-- The input vertex at the end of interior walk edge `p`. -/
def wEnd (li : Bool) (n p : ℕ) : ℕ := wStart li n ztxlu

/-- **A kept triple**: one of its walk edges starts at the height vertex. -/
def keepX (li : Bool) (n : ℕ) (x : ℕ × ℕ × ℕ) : Bool :=
  decide (x.1 = wStart li n x.2.1) || decide (x.1 = wStart li n x.2.2)
theorem keepX_iff (li : Bool) (n : ℕ) (x : ℕ × ℕ × ℕ) :
    keepX li n x = true ↔ x.1 = wStart li n x.2.1 ∨ x.1 = wStart li n x.2.2 := by
  simp [keepX]
variable {Q : Polygon} {li : Bool}
theorem interiorWalk_n (Q : Polygon) : (interiorWalk Q).n = Q.n := by
  zugiq

  · rfl
  · zufan
theorem rev_vtx (Q : Polygon) {p : ℕ} (hp : p < Q.n) :
    Polygon.vtx ⟨Q.vertices.reverse⟩ p = Q.vtx ztqbp := by
  zuioz
  rw [List.getElem?_reverse hp]
  rfl
theorem walk_vtx (hli : li = true ↔ Mountain.LeftInside Q) {p : ℕ} (hp : p < Q.n) :
    (interiorWalk Q).vtx p = Q.vtx ztryh := by
  unfold interiorWalk wStart
  by_cases h : Mountain.LeftInside Q
  · simp_all
  · have : ztppd := by
      simp_all
    rw [ite_eq_right h, this]
    exact rev_vtx Q hp
theorem mod_lt' {p n : ℕ} (hp : p < n) : ztr % n < n := Nat.mod_lt _ by_omega
theorem walk_vtx_succ (hli : li = true ↔ Mountain.LeftInside Q) {p : ℕ} (hp : p < Q.n) :
    (interiorWalk Q).vtx ztxlt = Q.vtx ztryg := by
  zuouj
  exact walk_vtx hli ztvzg
variable {n p : ℕ}
theorem wStart_lt (hp : p < n) : wStart li n p < n := by
  unfold wStart; grind
theorem wEnd_lt (hp : p < n) : wEnd li n p < n := wStart_lt ztvzg
theorem wStart_ne_wEnd (hn : 2 ≤ n) (hp : p < n) : wStart li n p ≠ wEnd li n p := by
  unfold wEnd wStart
  have : ztr % n = if p + 1 < n then p + 1 else 0 := by
    zus
    · zubql
    · zubyy
  grind

/-! ## Positions on the interior walk -/
variable (hQ : Q.Simple) (hDH : DistinctHeights Q) (hli : li = true ↔ Mountain.LeftInside Q)
include hQ hDH hli
omit hQ hDH hli in
theorem wa_eq (_hQ : Q.Simple) (_hDH : DistinctHeights Q) (hli : li = true ↔ Mountain.LeftInside Q)
    {p : ℕ} (hp : p < Q.n) : (interiorModel Q).wa p = Q.vtx ztryh :=
  walk_vtx hli hp
omit hQ hDH hli in
theorem wb_eq (_hQ : Q.Simple) (_hDH : DistinctHeights Q) (hli : li = true ↔ Mountain.LeftInside Q)
    {p : ℕ} (hp : p < Q.n) : (interiorModel Q).wb p = Q.vtx ztryg :=
  walk_vtx_succ hli hp
theorem wa_wb_snd_ne {p : ℕ} (hp : p < Q.n) :
    ((interiorModel Q).wa p).2 ≠ ((interiorModel Q).wb p).2 := by
  zunim
  exact hDH _ _ (wStart_lt hp) (wEnd_lt hp) (wStart_ne_wEnd (by have := hQ.1; omega) hp)
theorem param_eq {p h : ℕ} (hp : p < Q.n) :
    (interiorModel Q).param Q ztdw =
      ztgvo /
        ztfln := by
  zulrt
  simp_all

/-- The point of a position lies at the height of its vertex. -/
theorem pos_snd {p h : ℕ} (hp : p < Q.n) :
    ((interiorModel Q).pos Q ztdw).2 = (Q.vtx h).2 := by
  have hne := wa_wb_snd_ne hQ hDH hli hp
  zuhes
  simp only [Model.pos, Geometry.lerp_snd]
  rw [param_eq hQ hDH hli hp]
  simp_all

/-- A position whose edge starts at its vertex is that vertex. -/
theorem pos_start {p h : ℕ} (hp : p < Q.n) (hh : h = wStart li Q.n p) :
    (interiorModel Q).pos Q ztdw = Q.vtx h := by
  have hpar : ztykz := by
    rw [param_eq hQ hDH hli hp, wa_eq hQ hDH hli hp, ← hh, sub_self, zero_div]
  zulru
  rw [hpar, Geometry.lerp_zero, wa_eq hQ hDH hli hp, ← hh]

/-- **A position at a vertex, with parameter in `[0, 1)`, is on an edge starting there.** -/
theorem start_of_pos {p h : ℕ} (hp : p < Q.n) (hh : h < Q.n)
    (ht0 : 0 ≤ (interiorModel Q).param Q ztdw)
    (ht1 : (interiorModel Q).param Q ztdw < 1)
    (hpos : (interiorModel Q).pos Q ztdw = Q.vtx h) : h = wStart li Q.n p := by
  set t := (interiorModel Q).param Q ztdw with ht
  set j := wStart li Q.n p with hj
  set j' := wEnd li Q.n p with hj'
  have hjn : ztsjp := wStart_lt hp
  have hj'n : j' < Q.n := wEnd_lt hp
  have hjj' : j ≠ j' := wStart_ne_wEnd (by have := hQ.1; omega) hp
  have hpos' : lerp zthrw (Q.vtx j') t = Q.vtx h := by
    zuora; zunuw; zunim
  zuct
  have inj := hQ.2.1
  -- `t ≠ 0`
  have ht0' : ztmwx := by
    zuchf
    rw [e, Geometry.lerp_zero] at hpos'
    grind
  -- `h ≠ j'`
  have hj'h : h ≠ j' := by
    zuchf
    have hy := congrArg Prod.snd hpos'
    zugcs
    zufav
    have hne' := hDH _ _ hjn hj'n hjj'
    grind
  -- the `Q` edge carrying the position
  obtain ⟨e, hen, hee, hmem⟩ : ∃ e, e < Q.n ∧ (e = j ∧ (e + 1) % Q.n = j' ∨
      e = j' ∧ ztda % Q.n = j) ∧ Q.vtx h ∈ Q.edge e := by
    have hmod : ∀ q, q < Q.n → ztfo % Q.n = if q + 1 < Q.n then q + 1 else 0 := fun q hq => by
      zudlu
      · exact Nat.mod_eq_of_lt h1
      · rw [show q + 1 = Q.n by omega, Nat.mod_self]
    cases hb : li
    · -- reversed walk: edge `j'` runs from `j'` to `j`
      have hj1 : j = Q.n - 1 - p := by rw [hj]; zuoik
      have hj'1 : j' = Q.n - 1 - ztr % Q.n := by zuocw; zunxt
      refine ⟨j', hj'n, Or.inr ztmw, ?_⟩
      · zuelz
        zuwd
      · have hjs : ztdhr % Q.n = j := by
          zuelz
          zuwd
        refine ztlva
        rw [hjs, ← hpos']
        zuorb
        grind
    · have hj1 : j = p := by rw [hj]; zuoik
      have hj'1 : j' = ztr % Q.n := by zuocw; zunxt
      refine ⟨j, hjn, by_grind, ?_⟩
      refine ⟨t, ht0, ht1.le, ?_⟩
      have hs : ztl % Q.n = j' := by_grind
      rw [hs, ← hpos']
      rfl
  have heh : e ≠ h := by
    omega
  have hmh : Q.vtx h ∈ Q.edge h := ztolk
  have hcap := hQ.2.2 h e hh hen heh.symm
  have hin : Q.vtx h ∈ Q.edge h ∩ Q.edge e := ⟨hmh, hmem⟩
  rw [hcap] at hin
  obtain ⟨-, h2 | h2⟩ := hin
  · grind
  · have := inj _ _ hh by_omega h2
    omega
omit hQ hDH hli in
theorem vtx_not_mem_dom {h : ℕ} (hh : h < Q.n) : Q.vtx h ∉ Q.filled \ Q.boundary := fun hm =>
  hm.2 ⟨h, hh, 0, le_rfl, zero_le_one, by_simp⟩

/-! ## Vertex chords among the records -/

/-- **A record of the interior model is a vertex chord iff its triple is kept.** -/
theorem mem_full_iff {x : ℕ × ℕ × ℕ} (hx : (recOf x).Attached ztd Q)
    (hadm : (recOf x).toSet ztd Q ∈ (interiorModel Q).Adm) (hh : x.1 < Q.n) :
    (recOf x).toSet ztd Q ∈ (interiorModel Q).Full ↔ keepX li Q.n x = true := by
  obtain ⟨h, lp, rp⟩ := x
  simp only at hh
  zuhm
  set y := (Q.vtx h).2 with hy
  set a := (I.pos Q ztrdt).1 with ha
  set b := (I.pos Q ztrek).1 with hb
  have hset : (recOf ztcvt).toSet I Q = hseg y a b := rfl
  rw [hset] at hadm ⊢
  rw [keepX_iff]
  zubi
  obtain ⟨hA1, hA2⟩ := hx
  obtain ⟨hlp, hl0, hl1, -⟩ := hA1
  obtain ⟨hrp, hr0, hr1, -⟩ := hA2
  have hWn : ztpkh := interiorWalk_n Q
  zvnux at hlp hrp
  -- the chord of the domain
  obtain ⟨y', a', b', hch, heq⟩ := hadm
  have hab : a ≤ b := by
    have : (ztdtr : Point) ∈ hseg y a b := heq ▸ (⟨rfl, le_rfl, hch.lt.le⟩ :
      (ztdtr : Point) ∈ hseg y' a' b')
    exact this.2.1.trans this.2.2
  obtain ⟨rfl, rfl, rfl⟩ := Merge.hseg_inj hab heq
  have hL : I.pos Q ztrdt = ztdv := point_ext rfl (pos_snd hQ hDH hli hlp)
  have hR : I.pos Q ztrek = ztdy := point_ext rfl (pos_snd hQ hDH hli hrp)
  have hHC : FullDegInt.HC Q _ := ztlws
  constructor
  · -- a vertex chord: the vertex is an end
    zuhgp
    obtain ⟨i, σ, hi, hσ, hdir, hcs, -⟩ := Visibility.chords_spec hQ hmem
    have hvi : Q.vtx i ∈ hseg y a b := by
      rw [hcs, Visibility.chordSet_eq_openChordSet_union hQ hi hdir]
      simp
    have hih : i = h := by
      zuct
      exact hDH _ _ hi hh hne hvi.1
    subst hih
    have hvD := vtx_not_mem_dom hi
    obtain ⟨-, h1, h2⟩ := hvi
    zuff
    · zudt
      · exact absurd (by
          have := hch.open_mem _ h1 h2
          omega) hvD
      · right
        exact start_of_pos hQ hDH hli hrp hi hr0 hr1 by_grind
    · left
      exact start_of_pos hQ hDH hli hlp hi hl0 hl1 by_grind
  · -- a kept triple: the chord is the vertex chord of `h`
    have key : ∀ σ : ℝ, ztdd →
        (∀ t, 0 < t → t < b - a → rayPt ztqbr σ t ∈ Q.filled \ Q.boundary) →
        (∀ t, 0 < t → t < b - a → rayPt ztqbr σ t ∈ hseg y a b) →
        hseg y a b ∈ chords Q := by
      intro σ hσ hin hon
      have hba := sub_pos.2 hch.lt
      have e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 _ := Ioo_mem_nhdsGT hba
      have hdir : Visibility.DirInterior Q h σ := e1.mono by_grind
      have hmem : chordSet Q h σ ∈ chords Q := ⟨h, σ, hh, hσ, hdir, rfl⟩
      have hpar := Visibility.chordParam_pos hQ hh hdir
      set s := min (Visibility.chordParam Q h σ / 2) ztwsh with hs
      zucmn
      have hs1 : s < Visibility.chordParam Q h σ := by_grind
      have hs2 : s < b - a := by_grind
      have hzC : rayPt ztqbr σ s ∈ chordSet Q h σ := by
        rw [Visibility.chordSet_eq_openChordSet_union hQ hh hdir]
        exact Or.inl ⟨s, by_grind, rfl⟩
      have heq := FullDegInt.eq_of_common (FullDegInt.hc_full hQ hmem) hHC hzC
        by_grind by_grind
      grind
    rintro (e | e)
    · -- left end at the vertex
      have hv : Q.vtx h = ztdv := by rw [← hL]; exact (pos_start hQ hDH hli hlp e).symm
      refine key 1 ztp ztfhm ztfhm
      · have := hch.open_mem ztne by_linarith by_linarith
        convert this using 1
        zvmyq; zvmxf
      · zuemh
    · -- right end at the vertex
      have hv : Q.vtx h = ztdy := by rw [← hR]; exact (pos_start hQ hDH hli hrp e).symm
      refine key _ ztbt ztfhm ztfhm
      · have := hch.open_mem (b - t) by_linarith by_linarith
        convert this using 1
        zvmyq; zunob
      · zuemh
end DownBase
open Chazelle.Chain (SideAttach)
namespace Model
variable (M : Model)

/-- More chords, more cuts. -/
theorem isCut_mono {F F' : Set ztf} (h : F ⊆ F') {x : ℝ} (hx : M.IsCut F x) :
    M.IsCut F' x := by
  obtain ⟨c, hc, p, t, ha, rfl⟩ := hx
  exact ⟨c, h hc, p, t, ha, rfl⟩

/-- The set of counted walk edges met by the open key interval `(a, b)`. -/
def arcEdges (a b : ℝ) : Set ℕ :=
  {p : ℕ | p < M.W.n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b ztk}
variable (a b : ℝ)
theorem arcWt_eq : M.arcWt a b = (M.arcEdges a b).ncard := rfl
theorem arcEdges_finite : (M.arcEdges a b).Finite :=
  (Set.finite_lt_nat M.W.n).subset fun _ hp => hp.1

/-- A smaller key interval meets fewer counted edges. -/
theorem arcWt_mono {a b a' b' : ℝ} (h : ∀ x, sideInArc a' b' x → sideInArc a b x) :
    M.arcWt a' b' ≤ M.arcWt a b := by
  rw [arcWt_eq, arcWt_eq]
  refine Set.ncard_le_ncard ?_ (M.arcEdges_finite a b)
  zutp
  exact ⟨hp, hc, t, ht0, ht1, by_simp_all⟩
end Model

/-- **Splitting a cyclic interval at an inner key** `g`: a key of `(a, b)` lies in `(a, g)`, is
`g`, or lies in `(g, b)`. -/
theorem sideInArc_split {a b g x : ℝ} (hx : sideInArc a b x) (hg : sideInArc a b g) :
    sideInArc a g x ∨ x = g ∨ sideInArc g b x := by
  unfold sideInArc at *
  grind
namespace Model
variable (M : Model)

/-- The walk edges whose open part contains the key `g` (at most one). -/
def keyEdges (g : ℝ) : Set ℕ := {p : ℕ | ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (p : ℝ) + t = g}

/-- A natural key is the open part of no walk edge. -/
theorem keyEdges_natCast (k : ℕ) : keyEdges (k : ℝ) = ∅ := by
  zufj
  simp only [keyEdges, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  intro t ht0 ht1 hp
  have h1 : ztixl := by_linarith
  zujyk
  have h1' : p < k := by_simp_all
  zucgf
  omega
theorem arcEdges_subset_split {a b g : ℝ} (hg : sideInArc a b g) :
    M.arcEdges a b ⊆ M.arcEdges a g ∪ M.arcEdges g b ∪ keyEdges g := by
  zutp
  rcases sideInArc_split hx hg with h | h | h
  · exact Or.inl (Or.inl ztklp)
  · exact Or.inr ⟨t, ht0, ht1, h⟩
  · exact Or.inl (Or.inr ztklp)

/-- **Cutting at a vertex key loses nothing**: for a natural key `k` inside `(a, b)`,
`arcWt a b ≤ arcWt a k + arcWt k b`. -/
theorem arcWt_le_split_vertex {a b : ℝ} {k : ℕ} (hg : sideInArc a b k) :
    M.arcWt a b ≤ M.arcWt a k + M.arcWt k b := by
  rw [arcWt_eq, arcWt_eq, arcWt_eq]
  have hsub := M.arcEdges_subset_split hg
  rw [keyEdges_natCast, Set.union_empty] at hsub
  calc (M.arcEdges a b).ncard ≤ (M.arcEdges a k ∪ M.arcEdges k b).ncard :=
        Set.ncard_le_ncard hsub ((M.arcEdges_finite a k).union (M.arcEdges_finite k b))
    _ ≤ (M.arcEdges a k).ncard + (M.arcEdges k b).ncard := Set.ncard_union_le _ _
end Model

/-! ## The glue chords of a junction -/
section Glue
variable (J : Merge.Junction)

/-- The shared vertex `v = C₁ ∩ C₂` (vertex `m₁` of `C`). -/
noncomputable def sharedV : Point := J.whole.vertex J.m₁

/-- The neighbour of the shared vertex on `C₁` (vertex `m₁ - 1` of `C`). -/
noncomputable def sharedU : Point := J.whole.vertex (J.m₁ - 1)

/-- The neighbour of the shared vertex on `C₂` (vertex `m₁ + 1` of `C`). -/
noncomputable def sharedW : Point := J.whole.vertex ztnlv

/-- **Genericity at the shared vertex**: the shared vertex and its two neighbours have pairwise
distinct heights.  Automatic for chains of the geometry polygon (distinct heights); an
obligation of the down phase for the junctions of region boundaries `R*`. -/
def SharedGeneric : Prop :=
  (sharedU J).2 ≠ (sharedV J).2 ∧ (sharedW J).2 ≠ (sharedV J).2 ∧ (sharedU J).2 ≠ (sharedW J).2

/-- The shared vertex is a local extremum of `C` (both neighbours strictly above, or both
strictly below): then one of its two companions on the walk of `C` (the *inner* one, where the
paper puts a null-length chord) has no horizontal direction in its sector. -/
def SharedExtremum : Prop :=
  0 < ztbll * ztblm

/-- The neighbour of the shared vertex nearer in height ("lower arm" of the extremum). -/
noncomputable def capNear : Point :=
  if |(sharedU J).2 - (sharedV J).2| < |(sharedW J).2 - (sharedV J).2| then sharedU J
  else sharedW J

/-- The other neighbour ("higher arm"). -/
noncomputable def capFar : Point :=
  if |(sharedU J).2 - (sharedV J).2| < |(sharedW J).2 - (sharedV J).2| then sharedW J
  else sharedU J

/-- **The origin of the cap chord**: the point of the higher arm `[v, far]` at the height of the
nearer neighbour (an interior point of that edge under `SharedGeneric`, and a symbolic point
`onEdge` of the host). -/
noncomputable def capOrigin : Point :=
  Geometry.lerp ztiar (capFar J)
    ztzzb

/-- The direction of the cap chord: horizontally from the higher arm towards the nearer
neighbour, i.e. into the inner sector of the extremum. -/
noncomputable def capDir : ℝ := if (capNear J).1 < (capOrigin J).1 then -1 else 1

/-- **The cap chord** (at most one): when the shared vertex is a local extremum of `C`, the chord
of `C` shot from `capOrigin` in direction `capDir`.  It is attached on the walk edge adjacent to
the inner companion of the shared vertex, which bounds the arc through that companion by one
edge on that side (design doc `design-merge-v2.md` §2). -/
def capChords : Set ztf :=
  {d | SharedExtremum J ∧ Merge.FreeAt J.whole ztchm ztchl ∧
    d = Merge.shoot J.whole ztchm ztchl}

/-- The indices (in `C`) of the tops of `C₁` and `C₂`: where their slits were. -/
noncomputable def topIdxs : Finset ℕ := {J.left.topIdx, J.m₁ + J.right.topIdx}

/-- **The top chords**: the vertex chords of `C` at the tops of `C₁` and `C₂` (at most four).  The
copy of a top vertex that carried the slit of `C₁` (resp. `C₂`) is a single walk position of
`C` whose sector contains a free horizontal direction, so these chords make it a cut. -/
def topChords : Set ztf :=
  {d | ∃ k ∈ topIdxs J, ∃ σ : ℝ, ztdd ∧ J.whole.DirFree k σ ∧
    d = J.whole.chordSet k σ}

/-- **The glue chords** added by the revised fusion. -/
def glueChords : Set ztf := topChords J ∪ capChords J
theorem capChords_subsingleton : (capChords J).Subsingleton := by
  rintro d ⟨-, -, rfl⟩ e ⟨-, -, rfl⟩
  rfl
theorem topChords_subset_chords : topChords J ⊆ J.whole.chords := by
  rintro d ⟨k, hk, σ, hσ, hf, rfl⟩
  refine ⟨k, σ, ?_, hσ, hf, rfl⟩
  zugia
  zuvk
  · have := J.left.topIdx_le
    simp only [Merge.Junction.whole_m, Merge.Junction.left_m] at this ⊢
    omega
  · have := J.right.topIdx_le
    simp_all
theorem topChords_finite : (topChords J).Finite :=
  J.whole.chords_finite.subset (topChords_subset_chords J)
theorem glueChords_finite : (glueChords J).Finite :=
  (topChords_finite J).union (capChords_subsingleton J).finite
end Glue

/-! ## The revised mathematical obligations of WP-D -/

/-- The additive granularity loss of one fusion (`c₀` of design doc §9.6, option 2). -/
def fuseLoss : ℕ := 1

/-- **WP-D (math), the weight bound of the revised fusion.**  The fusion of a γ-semigranular
submap of `C₁` and one of `C₂`, together with the glue chords, is `(γ + 1)`-semigranular.
Paper proof in `docs/design-merge-v2.md` §2: every arc of the result avoiding the inner companion
of the shared vertex lies, cut for cut, inside an arc of `S₁` or of `S₂`; the arc through the
inner companion is that plus the part of one walk edge up to the cap chord
(`Model.arcWt_le_split_vertex`).  The missing library lemma is a *walk embedding* (design
`design-merge-v2.md` §8, O1).  (Review m1: the former hypothesis `HeightsIn Q J.whole` is not used
by the argument and was dropped.) -/
def FusionWeightSpec : Prop :=
  ∀ (J : Merge.Junction) (Q : Polygon) (S₁ S₂ : Set ztf) (γ : ℕ),
    J.P.Simple → SharedGeneric J →
    (chainModel J.left).ChordFamily Q S₁ → (chainModel J.right).ChordFamily Q S₂ →
    (chainModel J.left).Semigranular S₁ γ → (chainModel J.right).Semigranular S₂ γ →
    (chainModel J.whole).Semigranular ztqu ztcbh

/-- **WP-D (math), the degree bound (finding D4).**  The degree of the revised fusion is bounded
by a function of the degree bound of the inputs.  The paper (p. 508) gives two runs of at most
four exit chords each; `docs/design-merge-v2.md` §4 sketches `capF D = 2 D + 13` in the formal
model.  Stated existentially: only `RestoreSpec`'s cost constant `κ d₀ D` depends on it.  (Review m1:
`HeightsIn` dropped; review m3: the sketch covers shared, top and cap chords with both ends on
one side.) -/
def FusionDegSpec : Prop :=
  ∃ capF : ℕ → ℕ, ∀ (J : Merge.Junction) (Q : Polygon) (S₁ S₂ : Set ztf) (D : ℕ),
    J.P.Simple → SharedGeneric J →
    (chainModel J.left).ChordFamily Q S₁ → (chainModel J.right).ChordFamily Q S₂ →
    (chainModel J.left).DegLe S₁ D → (chainModel J.right).DegLe S₂ D →
    (chainModel J.whole).DegLe ztqu zthvn

/-! ## RAM contracts -/

/-- Three chain descriptors describe the left, right and whole chains of a junction. -/
def JunctionAt (m : ℕ → ℕ) (bl br bw : ℕ) (Q : Polygon) (H : Host) (J : Merge.Junction) : Prop :=
  ChainDescAt m bl Q H J.left ∧ ChainDescAt m br Q H J.right ∧ ChainDescAt m bw Q H J.whole

/-- **Well-formed junction descriptors** below `E` (review M1, findings C7/C8): the three chain
descriptors are well formed (`ChainWF`: at most `64` host items, items in range, start in range)
and stored below `E`.  With in-range host items every host point has a vertex height of `Q`, so
the cap chord (at the height of a host neighbour of the shared vertex) has a normal-form record
(M1's counterexample: an item `.pt (.onEdge e h)` with `h ≥ n`). -/
def JunctionWF (P : Polygon) (E : ℕ) (m : ℕ → ℕ) (bl br bw : ℕ) : Prop :=
  ChainWF P E m bl ∧ ChainWF P E m br ∧ ChainWF P E m bw ∧
    ∀ H : Host, HostAt m (m bw) H → HostRegular P.n H

/-- A list of result quadruples `(flag, h, lp, rp)` at `A`, four words each. -/
def ResultListAt (m : ℕ → ℕ) (A : ℕ) (R : List ztpl) : Prop :=
  ∀ i, i < R.length →
    m (A + 4 * i) = (R.getD i ztlt).1 ∧ m (A + 4 * i + 1) = (R.getD i ztlt).2.1 ∧
      m (A + 4 * i + 2) = (R.getD i ztlt).2.2.1 ∧
      m (A + 4 * i + 3) = (R.getD i ztlt).2.2.2

/-- The chain on side `i` of a junction (`0`: `C₁`, otherwise `C₂`). -/
def sideChain (J : Merge.Junction) (i : ℕ) : Chain := if i = 0 then J.left else J.right

/-- A sweep query `(edge, height code, direction code)`: a walk position of the chain model of
side `i`, with a height code `≥ 1` and a parameter in `[0, 1)` (review finding C2), at a height
not above the top of that chain (so that the chord it sees is an augmented chord of `C`), whose
direction points into the left sector of the walk at the position, i.e. into the query's own
side of the chain (review of the merge redesign, m2: otherwise the local shooting would have to
use the companion walk edge). -/
def QueryOK (J : Merge.Junction) (Q : Polygon) (i : ℕ) (q : ℕ × ℕ × ℕ) : Prop :=
  let M := chainModel ztgi
  let z := M.pos Q ztpo
  q.1 < M.W.n ∧ 1 ≤ q.2.1 ∧ q.2.1 ≤ Q.n ∧ 0 ≤ M.param Q ztpo ∧
    M.param Q ztpo < 1 ∧ z.2 ≤ (sideChain J i).top.2 ∧
    Chazelle.Chain.sideLeft M.W q.1 (M.param Q ztpo) (z.1 + dirOf q.2.2, z.2)

/-- **The endpoint queries of a chord list** (finding S-1): two queries per record, from its left
end to the east (`(lp, h + 1, 1)`) and from its right end to the west (`(rp, h + 1, 0)`). -/
def sweepEndQ (cs : List CRec) : List zte :=
  (List.range ztssj).map fun j =>
    let r := cs.getD ztwm ztrp
    if j % 2 = 0 then ztdic else ztdid

/-- **What a query point sees in `C`**: the result flag is `1` iff the direction is free for `C`
at the point, and then the triple is a correctly attached record of the chord of `C` seen from
the point (`Merge.shoot`). -/
def SeesInWhole (J : Merge.Junction) (Q : Polygon) (i : ℕ) (q : ℕ × ℕ × ℕ)
    (r : ℕ × ℕ × ℕ × ℕ) : Prop :=
  let z := (chainModel ztgi).pos Q ztpo
  (r.1 = 1 ↔ Merge.FreeAt J.whole z zthwj) ∧
    (r.1 = 1 → (recOf r.2).toSet ztbm Q = Merge.shoot J.whole z zthwj ∧
      (recOf r.2).Attached ztbm Q)

/-- **WP-D: the fusion** (Lemma 3.1 with glue chords).  Registers of band `bFuse`: `0, 1, 2`
junction descriptors, `3, 4` normal forms of `S₁`, `S₂`, `5` a bound `γ` on their weights, `6` a
bound `D` on their degrees, `8` the oracle context handle; output `7`: the normal form of
`J.fusion S₁ S₂ ∪ glueChords J`.  Findings D1–D4:
* the output is `(γ + fuseLoss)`-semigranular (D1), with at most `2 (K₁ + K₂) + 7` chords;
* the degree cap is `capF D` for a fixed function `capF` (D4; `FusionDegSpec`);
* `Ok` for the whole chain and `SharedGeneric J` are assumed (D3; the sweeps only shoot in the
  models of `C₁`, `C₂`);
* the cost uses `⌈log₂ (K₁ + K₂ + 1)⌉` (the sort of `BuildNF`) and a constant `κ D` (D2). -/
def FuseSpec : Prop :=
  ∃ (mk : Stmt → Stmt) (κ capF : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ)
    (X : MemCtx) (Ok : Polygon → Model → Prop), X.CapLocal → Bs ⊆ oracleBands →
    ShooterOK sh Bs F X Ok →
    Meets ztkbc (fuseBands ∪ oracleBands)
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        X.holds P c.nmem ztrvh ztm ∧
        rd c bFuse 5 ≤ X.cap P c.nmem ztrvh ∧
        JunctionWF P ztm c.nmem ztlsj ztlsk ztlsl ∧
        ∃ H J N₁ N₂, JunctionAt c.nmem ztlsj ztlsk ztlsl zta H J ∧
          J.P.Simple ∧ SharedGeneric J ∧ Ok P ztbw ∧ Ok P ztj ∧
          Ok P ztbm ∧
          NFWithin c.nmem ztfue ztm N₁ ∧
          NFWithin c.nmem ztfuf ztm N₂ ∧
          IsNF ztbw zta N₁ ∧ IsNF ztj zta N₂ ∧
          (chainModel J.left).DegLe ztwjx zthzy ∧
          (chainModel J.right).DegLe ztwis zthzy ∧
          (chainModel J.left).Semigranular ztwjx ztlsm ∧
          (chainModel J.right).Semigranular ztwis ztlsm)
      (fun P c c' => ∀ H J N₁ N₂,
        JunctionAt c.nmem ztlsj ztlsk ztlsl zta H J →
        NFAt c.nmem ztfue N₁ → NFAt c.nmem ztfuf N₂ →
        ∃ N, c.nreg ALLOC ≤ rd c' bFuse 7 ∧ NFWithin c'.nmem (rd c' bFuse 7) ztdo N ∧
          IsNF ztbm zta N ∧
          N.F ztbm zta =
            J.fusion ztwjx ztwis ∪
              glueChords J ∧
          N.nChords ≤ 2 * zttbf + 7 ∧
          (chainModel J.whole).DegLe ztzui (capF zthzy) ∧
          (chainModel J.whole).Semigranular ztzui
            (rd c bFuse 5 + fuseLoss))
      (fun _ c => κ zthzy * ztyqf *
        (F ztlsm + Nat.clog 2 ztyqf + 1))

/-- The host curves on which the merges run: the geometry polygon itself (up phase) or a region
boundary `R*` of the down phase, described by at most `64` items (arcs of a region of degree
`≤ 4` plus the chord edges tilted into the curve, p. 519). -/
def HostOk (H : Host) : Prop := H.length ≤ 64

/-- The models the oracles serve: chain models of chains of simple, regular host curves
(`HostRegular`, review finding G1: a non-regular host edge carries origins that are neither
symbolic nor box points, from which no oracle query can be issued). -/
def OkModel (P : Polygon) (M : Model) : Prop :=
  ∃ (H : Host) (C : Chain), HostOk H ∧ HostRegular (Qof P).n H ∧ C.P = H.poly zta ∧
    C.P.Simple ∧ M = chainModel C

/-- **WP-E: restoring conformality** (Lemmas 2.4, 3.2, 3.3, 3.4).  Registers of band `bRestore`:
`0` model descriptor (a chain model or the interior model of `Qof P`), `1` normal form, `2` its
degree bound `d₀`, `3` the target cap `D ≥ 4` (the full augmented map of the model has degree
`≤ D`), `4` its semigranularity `γ`, `6` the context handle; output `5`: a normal form of a finer
submap with degree `≤ D`, still γ-semigranular (restoration only adds chords, so the `γ + 1`
loss of the fusion is not increased), with at most `cR d₀ D (K + 1)` chords (finding F-G3: the
merge's granularity step pays for them).  Cost `κ d₀ D (K + 1) F γ · G γ · (H γ + ⌈log₂ γ⌉ + 1)`. -/
def RestoreSpec : Prop :=
  ∃ (mk : Stmt → Stmt → Stmt) (κ cR : ℕ → ℕ → ℕ), ∀ (sh cu : Stmt)
    (Bs Bc : Finset ℕ) (F G H : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop),
    X.CapLocal → X.Halves → ztcxi →
    Bs ⊆ oracleBands → Bc ⊆ oracleBands → ShooterOK sh Bs F X Ok → CutterOK cu Bc G H X Ok →
    Meets ztdvk zttyt
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        X.holds P c.nmem ztiab ztm ∧
        rd c bRestore 4 ≤ X.cap P c.nmem ztiab ∧ 4 ≤ rd c bRestore 3 ∧
        ModelDescWF P ztm c.nmem ztcdq ∧
        (c.nmem ztcdq = 0 → ∀ H C,
          ChainDescAt c.nmem ztfig zta H C → HostRegular (Qof P).n H) ∧
        (c.nmem ztcdq = 0 → ∀ H C,
          ChainDescAt c.nmem ztfig zta H C → C.P.Simple) ∧
        ∃ M N, ModelDescAt c.nmem ztcdq zta M ∧ GoodModel M ∧ Ok P M ∧
          M.FullDegLe zta ztdad ∧
          NFWithin c.nmem ztdac ztm N ∧ IsNF M zta N ∧
          M.DegLe ztwiv ztefw ∧
          M.Semigranular ztwiv ztbrm)
      (fun P c c' => ∀ M N, ModelDescAt c.nmem ztcdq zta M →
        NFAt c.nmem ztdac N →
        ∃ N', c.nreg ALLOC ≤ rd c' bRestore 5 ∧
          NFWithin c'.nmem ztrvq ztdo N' ∧ IsNF M zta N' ∧
          N.F M zta ⊆ N'.F M zta ∧ M.DegLe ztxvm ztdad ∧
          M.Semigranular ztxvm ztbrm ∧
          N'.nChords ≤ cR ztefw ztdad * zthbn)
      (fun _ c => κ ztefw ztdad * ztxnh *
        F ztbrm * G ztbrm *
        (H ztbrm + Nat.clog 2 ztbrm +
          Nat.clog 2 ztxnh + 1))

/-- **WP-F: enforcing granularity** (§3.3; a worklist version, since removing a leaf can lower a
neighbour's degree below `3`: design doc §7) and computing the tree decomposition.  Registers of
band `bGran`: `0` model descriptor, `1` normal form, `2` degree cap `D`, `3` target `γ`; output
`4`: a γ-canonical normal form of a coarser submap.  Cost `κ D (K (⌈log₂ K⌉ + 1) + 1)`. -/
def GranularizeSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ → ℕ), Meets s granBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bGran 2 ∧
      ModelDescWF P ztm c.nmem ztqa ∧
      ∃ M N, ModelDescAt c.nmem ztqa zta M ∧ GoodModel M ∧
        NFWithin c.nmem ztbdi ztm N ∧ IsNF M zta N ∧
        M.DegLe ztwiv ztqb ∧
        M.Semigranular ztwiv ztbdj)
    (fun P c c' => ∀ M N, ModelDescAt c.nmem ztqa zta M → NFAt c.nmem ztbdi N →
      ∃ N', c.nreg ALLOC ≤ rd c' bGran 4 ∧ NFWithin c'.nmem ztcoh ztdo N' ∧
        N'.F M zta ⊆ N.F M zta ∧
        IsCanonicalNF M zta N' ztbdj ztqb)
    (fun _ c => κ ztqb *
      ztin)

/-- **WP-F: the merge** (Lemma 3.5).  Registers of band `bMerge`: `0, 1, 2` junction descriptors,
`3, 4` γ₁- and γ₂-canonical normal forms of the two chains, `5` a bound `γ₀ ≥ γ₁, γ₂` (review
finding F9: Lemma 3.5 is symmetric), `6` the target `γ ≥ γ₀ + fuseLoss` (the fusion loses
`fuseLoss`, and granularity enforcement only removes chords), `7` the degree cap `D ≥ 4` (the full
augmented map of the union has degree `≤ D`), `9` the oracle context handle; output `8`: a
γ-canonical normal form of the union.  The oracles must serve arcs of weight `γ₀ + fuseLoss`
(restoration runs on the fused map), and the junction is generic at the shared vertex.  Cost
`κ D (K₁ + K₂ + 1) F(γ₀+1) · G(γ₀+1) · (H(γ₀+1) + ⌈log₂ (m + 1)⌉ + 1)` (the inputs are canonical,
so Lemma 2.3 bounds `K₁ + K₂` by `c(D)(m + 1)` and `log K` by `log m + O_D(1)`). -/
def MergeSpec : Prop :=
  ∃ (mk : Stmt → Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh cu : Stmt)
    (Bs Bc : Finset ℕ) (F G H : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop),
    X.CapLocal → X.Halves → ztcxi → Monotone F → Monotone G →
    Monotone H →
    Bs ⊆ oracleBands → Bc ⊆ oracleBands → ShooterOK sh Bs F X Ok → CutterOK cu Bc G H X Ok →
    Meets ztdvk ztodk
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        X.holds P c.nmem ztdab ztm ∧
        rd c bMerge 5 + fuseLoss ≤ X.cap P c.nmem ztdab ∧ 4 ≤ rd c bMerge 7 ∧
        rd c bMerge 5 + fuseLoss ≤ rd c bMerge 6 ∧
        JunctionWF P ztm c.nmem ztefr ztefs zteft ∧
        ∃ Hs J N₁ N₂, JunctionAt c.nmem ztefr ztefs zteft zta Hs J ∧
          J.P.Simple ∧ SharedGeneric J ∧ Ok P ztbw ∧ Ok P ztj ∧
          Ok P ztbm ∧ (chainModel J.whole).FullDegLe zta ztbnk ∧
          NFWithin c.nmem ztefu ztm N₁ ∧
          NFWithin c.nmem ztefv ztm N₂ ∧
          (∃ γ₁, γ₁ ≤ rd c bMerge 5 ∧
            IsCanonicalNF ztbw zta N₁ γ₁ ztbnk) ∧
          (∃ γ₂, γ₂ ≤ rd c bMerge 5 ∧
            IsCanonicalNF ztj zta N₂ γ₂ ztbnk))
      (fun P c c' => ∀ Hs J N₁ N₂,
        JunctionAt c.nmem ztefr ztefs zteft zta Hs J →
        NFAt c.nmem ztefu N₁ → NFAt c.nmem ztefv N₂ →
        ∃ N, c.nreg ALLOC ≤ rd c' bMerge 8 ∧ NFWithin c'.nmem ztrvo ztdo N ∧
          IsCanonicalNF ztbm zta N ztrvl ztbnk)
      (fun _ c => κ ztbnk * ztyqe *
        F ztdaa * G ztdaa *
        ztxqq)
open Chazelle.Machine (Exec)
def coreReg (i : ℕ) : ℕ := bandReg bCore i

/-- The bands a phase may write: every procedure band (`1 … 24`, including the sweep band
`bSweep = 24` of the consolidated revision) and the core band, not the final stage's band `0`. -/
def phaseBands : Finset ℕ := Finset.Icc 1 24

/-- The bands the output phase may write (it also sets the hand-off registers of band `0`). -/
def outBands : Finset ℕ := Finset.range 25

/-- The core registers listed in `S` are unchanged. -/
def KeepsCore (S : Finset ℕ) (c c' : Config) : Prop :=
  ∀ i ∈ S, c'.nreg ztfgz = c.nreg ztfgz

/-! ## WP-L: setup -/

/-- The top grade: the least `p` with `n - 1 ≤ 2^p`. -/
def topGrade (n : ℕ) : ℕ := Nat.clog 2 ztkl

/-- **The canonical granularity of grade `g`** (consolidated revision, design doc §10;
formerly `gradeGranV2`): `γ'_g = 2^⌈βg⌉ + fuseLoss · g (⌈log₂ g⌉ + 2)`.  The paper's `2^⌈βg⌉`
plus a lower-order term absorbing the additive loss `fuseLoss` of the at most `1 + ⌈log₂ g⌉`
merge levels of Lemma 4.1 (`gradeGran_step`); within a factor `1201` of the paper's
(`gradeGran_le_real`). -/
noncomputable def gradeGran (g : ℕ) : ℕ :=
  2 ^ Cost.ceilBeta g + fuseLoss * ztzvt

/-- The granularity of the canonical submap of the top chain, `γ'_p` (`gradeGran`). -/
noncomputable def topGran (n : ℕ) : ℕ := gradeGran ztcea

/-- **The setup record** at `S`: `n`, the top grade `p`, the table of `2^i` (`i ≤ p + 1`) at
`S + 2`, the table of `⌈i/5⌉` (`i ≤ p + 1`) at `S + p + 4`; all of it below `E`. -/
def SetupAt (m : ℕ → ℕ) (S n E : ℕ) : Prop :=
  m S = n ∧ m ztbgu = topGrade n ∧
    (∀ i, i ≤ topGrade n + 1 → m ztjmb = 2 ^ i ∧
      m (S + topGrade n + 4 + i) = Cost.ceilBeta i) ∧
    S + 2 * topGrade n + 6 ≤ E

/-- **WP-L: setup.**  From the initial state (with a good environment), writes a fresh setup
record and puts its handle in `coreReg 0`, in `κ (n + 1)` steps. -/
def SetupSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s phaseBands
    (fun P W _ => GoodEnv P ∧ P.n + 3 ≤ W)
    (fun P _ c' => Robust ztdo c'.nmem
      fun m => SetupAt m (c'.nreg ztcpu) P.n ztdo)
    ztwqk

/-! ## The phases -/

/-- The top chain of the geometry polygon: all edges but the last (`v₀ … v_{n-1}`). -/
def TopChain (P : Polygon) (C : Chain) : Prop := C.P = Qof P ∧ C.s = 0 ∧ C.m + 1 = P.n

/-- **WP-J: the up phase** (§4.1) with up-phase data `X`.  Reads the setup handle in
`coreReg 0` (kept); writes the handle of `X` in `coreReg 1` (holding below the allocator, with
all grades processed: its oracles serve arcs of up to `n - 1` edges, review finding F4) and the
handle of a `γ'_p`-canonical normal form (`topGran`, degree cap `4`) of the
top chain in `coreReg 2`, in `κ (n + 1)` steps. -/
def UpPhaseSpec (X : MemCtx) : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s phaseBands
    (fun P W c => GoodEnv P ∧ P.n + 3 ≤ W ∧ Robust ztm c.nmem
      fun m => SetupAt m (c.nreg ztcpu) P.n ztm)
    (fun P c c' => KeepsCore {0} c c' ∧
      X.holds P c'.nmem ztbafx ztdo ∧
      P.n - 1 ≤ X.cap P c'.nmem ztbafx ∧
      ∃ C N, TopChain P C ∧ Robust ztdo c'.nmem (fun m => NFAt m (c'.nreg ztvlu) N) ∧
        IsCanonicalNF ztc zta N ztmow 4)
    ztwqk

/-! ## The composition (proved) -/

/-! ## Package-level specifications -/

/-! ### The grade table (paper p. 516) -/

/-- The first edge of chain `i` of grade `g`. -/
def gradeStart (g i : ℕ) : ℕ := i * 2 ^ g

/-- The number of edges of chain `i` of grade `g` of the curve `v₀ … v_{n-1}` (`n - 1` edges):
`2^g`, except for a short last chain (the input is not padded). -/
def gradeLen (n g i : ℕ) : ℕ := min ztgyk (n - 1 - i * 2 ^ g)

/-- The number of chains of grade `g`: `⌈(n - 1) / 2^g⌉`. -/
def gradeCount (n g : ℕ) : ℕ := zteud / 2 ^ g + 1

/-- **The raw grade table** at handle `h`: `m h = Λ`, the number of processed grades
(`Λ ≤ p + 1`); `m (h + 1)` the setup handle; `m (h + 2)` the base `T` of the row table; for every
grade `g < Λ` and chain `i < gradeCount n g`, the entry at `m (T + g) + 3 i` holds a chain
descriptor of chain `i` of grade `g` of `Q = Qof P`, the handle of a `γ'_g`-canonical normal
form (`gradeGran`) (degree cap `4`) of it, and the handle of an oracle structure (`O.At`) for them;
the hosts are well formed (consolidated revision, finding C8; the descriptors lie below the bound
of the context because the context is robust).  The descriptors are well formed and the normal
forms robust below the bound `A` of the context (review finding G4: a robust existential does not
give the single robust normal form a cutter piece needs). -/
def GradeRaw (O : OracleIface) (P : Polygon) (m : ℕ → ℕ) (h A : ℕ) : Prop :=
  m h ≤ topGrade P.n + 1 ∧ SetupAt m ztzgl P.n ztyfh ∧
    ztxez ∧
    ∀ g i, g < m h → i < gradeCount P.n g →
      ∃ (H : Host) (C : Chain) (N : NF),
        ChainDescAt m (m ztbalr) zta H C ∧
        ChainWF P A m (m ztbalr) ∧ C.P = Qof P ∧
        H.length ≤ 64 ∧ HostWF P.n H ∧
        C.s = gradeStart g i ∧ C.m = gradeLen P.n g i ∧
        NFWithin m (m ztbanh) A N ∧
        IsCanonicalNF ztc zta N ztcvr 4 ∧
        O.At P m (m ztbajn) ∧
        m (m ztbajn) = m ztbalr ∧
        m (m ztbajn + 1) = m ztbanh ∧
        m (m ztbajn + 2) = gradeGran g

/-- The grade table is monotone in its bound. -/
theorem GradeRaw.mono {O : OracleIface} {P : Polygon} {m : ℕ → ℕ} {h A A' : ℕ}
    (hr : GradeRaw O P m h A) (hA : A ≤ A') : GradeRaw O P m h A' := by
  obtain ⟨h1, h2, h3, h4⟩ := hr
  refine ztioi
  obtain ⟨H, C, N, hd, hwf, hP, hl, hH, hs, hm, hN, rest⟩ := h4 g i hg hi
  exact ⟨H, C, N, hd, hwf.mono hA, hP, hl, hH, hs, hm, hN.mono hA, rest⟩

/-- **The up-phase data** as a memory context.  Once grades `< Λ` are processed, arcs of weight
at most `2^(Λ-1)` can be shot at and cut (a subarc of `w` edges splits into `O(log w)` grade
chains of grade `≤ ⌈log₂ w⌉`, `Cost.dyadic_cover`). -/
noncomputable def gradeCtx (O : OracleIface) : MemCtx where
  holds P m h A := Robust A m fun m' => GradeRaw O P m' h A
  cap _ m h := 2 ^ ztlrg
  local_ _P _m _m' _g _A hmm' h := h.transport by_simp_all
  mono _P _m _g _A _A' hA h := fun m' hm' =>
    (h m' by_grind).mono hA

/-! ### WP-H: Lemma 3.6 -/

/-- **WP-H.**  An implementation of the ray-shooting structure of Lemma 3.6. -/
def OracleSpec : Prop := ∃ O : OracleIface, O.Valid

/-! ### WP-G: the oracles of the merges -/

/-- `⌈x^a⌉` for a natural `x` and a real exponent. -/
noncomputable def rpowCeil (x : ℕ) (a : ℝ) : ℕ := ⌈(x : ℝ) ^ a⌉₊

/-- The granularity of the pieces produced by the arc-cutter for arcs of weight `≤ γ`:
`h(γ) = γ'_{⌈log₂ γ⌉} ≤ 1201 · 2^⌈β⌈log₂ γ⌉⌉` (p. 517, with the revised schedule). -/
noncomputable def cutGran (γ : ℕ) : ℕ := gradeGran (Nat.clog 2 γ)

/-- **WP-G: the ray-shooter and the arc-cutter** (p. 501, built as on p. 517): for the up-phase
data `gradeCtx O`, a shooter with `F(γ) = κ (⌈log₂ γ⌉ + 1) ⌈h(γ)^{1/3} (γ + 1)^{2/3}⌉ + κ`
(`O(λ)` subarcs, each a Lemma 3.6 query) and a cutter with `G(γ) = κ (⌈log₂ γ⌉ + 1)` pieces of
granularity `h(γ)`. -/
def ShootCutSpec (O : OracleIface) : Prop :=
  ∃ (sh cu : Stmt) (κ : ℕ),
    ShooterOK sh oracleBands
      ztbalu
      ztsy OkModel ∧
    CutterOK cu oracleBands ztywh cutGran ztsy OkModel

/-! ### WP-J: Lemma 4.1 -/

/-- The bands of Lemma 4.1 (merges with their oracles and sweeps, and its own band). -/
def l41Bands : Finset ℕ := mergeBands ∪ oracleBands ∪ {bL41}

/-- Lemma 4.1's bound `λ² (⌈log₂ λ⌉ + 1) 2^(74λ/75)` (with the `+1` of the logarithm kept). -/
noncomputable def lemma41Nat (g : ℕ) : ℕ :=
  ⌈(g : ℝ) ^ 2 * zttu * (2 : ℝ) ^ ztme⌉₊

/-- The first grade at which Lemma 4.1 is used (`gradeGran_cap`: from grade `7` on, the oracles
of the grades `< λ` serve every weight a merge of Lemma 4.1 needs; below it, `BruteSpec`). -/
def lemma41Start : ℕ := 7

/-- **WP-J: Lemma 4.1** (p. 517).  Band `bL41`: `0` the handle of the up-phase data (with at
least `λ` grades processed), `1` the start `a`, `2` the length `b - a`, `3` the grade
`λ ≥ lemma41Start = 7` (`2^(λ-1) < b - a ≤ 2^λ`); output `4`: a `γ'_λ`-canonical normal form
(`gradeGran`, degree cap `4`) of the chain `v_a … v_b` of `Q`, robust below the new allocator.
Cost `κ (lemma41Nat λ + 1)`.  (Consolidated revision: the revised schedule, `λ ≥ 7` so that the
merge targets `γ₀ + 1 ≤ γ'_λ < 2^(λ-1)` are served by the oracles (`gradeGran_cap`), and the
word bound `hostWords`.) -/
def Lemma41Spec (O : OracleIface) : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s l41Bands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      (gradeCtx O).holds P c.nmem ztbdk ztm ∧
      rd c bL41 3 ≤ c.nmem ztbdk ∧ lemma41Start ≤ rd c bL41 3 ∧
      rd c bL41 1 + rd c bL41 2 + 1 ≤ P.n ∧
      2 ^ ztbwz < rd c bL41 2 ∧ rd c bL41 2 ≤ 2 ^ rd c bL41 3)
    (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bL41 1 ∧ C.m = rd c bL41 2 ∧
      Robust ztdo c'.nmem ztwr ∧
      IsCanonicalNF ztc zta N ztbqg 4)
    ztgit

/-! ### WP-K: brute force -/

/-- The bands of the brute-force procedure (granularity enforcement and its own band). -/
def bruteBands : Finset ℕ := granBands ∪ {bBrute}

/-- **WP-K: brute-force canonical submaps** (the early grades, p. 516: "this work can be done
naively").  Band `bBrute`: `0` start `a`, `1` number of edges `m ≥ 1` (`a + m + 1 ≤ n`), `2` a
granularity `γ ≥ 1` with `m = 1` or `γ ≥ 2` (review finding K1: an interior top vertex of a chain of `≥ 2` edges always leaves an arc of weight `≥ 2`, so `γ = 1` is impossible there); output `3`: a `γ`-canonical normal form (degree cap `4`) of the chain
`v_a … v_{a+m}` of `Q`.  Cost `κ (m + 1)³`. -/
def BruteSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s bruteBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bBrute 1 ∧
      rd c bBrute 0 + rd c bBrute 1 + 1 ≤ P.n ∧ 1 ≤ rd c bBrute 2 ∧
      ztuu)
    (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bBrute 0 ∧ C.m = rd c bBrute 1 ∧
      Robust ztdo c'.nmem ztwq ∧
      IsCanonicalNF ztc zta N ztczy 4)
    ztgrj

/-! ### Arithmetic of the schedule (formerly `SpecMergeV2`) -/
variable {g g' : ℕ}
theorem ceilBeta_mono (h : g ≤ g') : Cost.ceilBeta g ≤ Cost.ceilBeta g' := by
  zumqp
  apply Nat.ceil_mono
  have hb : (0 : ℝ) ≤ Cost.beta := by rw [Cost.beta_eq]; norm_num
  exact mul_le_mul_of_nonneg_left by_simp_all hb
theorem ceilBeta_succ_le (g : ℕ) : Cost.ceilBeta ztbs ≤ Cost.ceilBeta g + 1 := by
  zumqp
  zumlu
  have h1 := Nat.le_ceil ztnkh
  rw [Cost.beta_eq] at h1 ⊢
  grind
theorem clog_succ_le {g : ℕ} (hg : 1 ≤ g) : Nat.clog 2 ztbs ≤ Nat.clog 2 g + 1 := by
  zudwq
  have := Nat.le_pow_clog (b := 2) by_norm_num g
  omega

/-- **The recurrence of the revised schedule**:
`γ'_g + fuseLoss (⌈log₂ (g + 1)⌉ + 1) ≤ γ'_{g+1}`. -/
theorem gradeGran_step (g : ℕ) :
    gradeGran g + fuseLoss * ztzcg ≤ gradeGran ztbs := by
  zuhqt
  have h1 : 2 ^ Cost.ceilBeta g ≤ 2 ^ Cost.ceilBeta ztbs :=
    Nat.pow_le_pow_right by_norm_num (ceilBeta_mono ztvah)
  have h2 := Nat.clog_mono_right 2 ztvah
  have h3 : g * ztcgu + ztzcg ≤
      ztbs * ztxvo := by
    have := Nat.mul_le_mul_left g h2
    nlinarith
  omega

/-- The revised schedule is monotone. -/
theorem gradeGran_mono (h : g ≤ g') : gradeGran g ≤ gradeGran g' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (le_trans by_omega (gradeGran_step _))

/-- The revised schedule dominates the paper's: `2^⌈βg⌉ ≤ γ'_g` (fewer chords). -/
theorem two_pow_ceilBeta_le_gradeGran (g : ℕ) : 2 ^ Cost.ceilBeta g ≤ gradeGran g :=
  Nat.le_add_right _ _

/-- `γ'_{g+1} ≤ 2 γ'_g` for `g ≥ 2`. -/
theorem gradeGran_succ_le_two_mul {g : ℕ} (hg : 2 ≤ g) :
    gradeGran ztbs ≤ 2 * gradeGran g := by
  zuhqt
  have h1 : 2 ^ Cost.ceilBeta ztbs ≤ 2 * 2 ^ Cost.ceilBeta g := by
    calc 2 ^ Cost.ceilBeta _ ≤ 2 ^ (Cost.ceilBeta g + 1) :=
          Nat.pow_le_pow_right by_norm_num (ceilBeta_succ_le g)
      _ = 2 * 2 ^ Cost.ceilBeta g := by_omega
  have h2 := clog_succ_le (g := g) by_omega
  have hc : ztrzx := Nat.clog_pos by_norm_num by_omega
  have h3 : ztbs * ztxvo ≤ 2 * ztzvt := by
    have := Nat.mul_le_mul_left ztbs (Nat.add_le_add_right h2 2)
    nlinarith
  omega

/-- **The cap condition**: from grade `7` on, `γ'_λ + 1 ≤ 2^(λ-1)`, so the oracles of the grades
`< λ` (which serve arcs of weight up to `2^(λ-1)`) serve every merge of Lemma 4.1 at grade `λ`
(inputs `≤ γ'_λ - 1`, fused weights `≤ γ'_λ`). -/
theorem gradeGran_cap {g : ℕ} (hg : lemma41Start ≤ g) : gradeGran g + 1 ≤ 2 ^ ztfe := by
  unfold lemma41Start at hg
  induction g, hg using Nat.le_induction with
  | base =>
    have hb : Cost.ceilBeta 7 ≤ 2 := by
      zumqp
      rw [Nat.ceil_le, Cost.beta_eq]
      norm_num
    have hc : Nat.clog 2 7 ≤ 3 := Nat.clog_le_of_le_pow by_norm_num
    have hp : 2 ^ Cost.ceilBeta 7 ≤ 2 ^ 2 := Nat.pow_le_pow_right by_norm_num hb
    zuhqt
    have : 7 * (Nat.clog 2 7 + 2) ≤ 7 * (3 + 2) := by_omega
    norm_num at hp this ⊢
    omega
  | succ g hg ih =>
    have h2 := gradeGran_succ_le_two_mul (g := g) by_omega
    have e : g + 1 - 1 = ztfe + 1 := by_omega
    rw [e, pow_succ]
    omega

/-- **The revised schedule is within a constant factor of the paper's**:
`γ'_g ≤ 1201 · 2^⌈βg⌉`.  All oracle costs `f`, `g`, `h` of the paper are nondecreasing and at
most polynomial in `γ`, so they change by constant factors only. -/
theorem gradeGran_le_real (g : ℕ) :
    (gradeGran g : ℝ) ≤ 1201 * (2 : ℝ) ^ Cost.ceilBeta g := by
  zuhqt
  have hc := Cost.clog_two_le_self g
  have hpoly : g * ztcgu ≤ 3 * g ^ 2 := by
    rcases Nat.eq_zero_or_pos g with h0 | hpos
    · simp_all
    · have := Nat.mul_le_mul_left g by_omega
      nlinarith
  have hsq := Cost.natPow_le_two_rpow 2 5 by_norm_num g
  have hexp : (2 : ℝ) ^ ((g : ℝ) / (5 : ℕ)) ≤ (2 : ℝ) ^ Cost.ceilBeta g := by
    rw [← Real.rpow_natCast (2 : ℝ) _]
    zuldb
    have := Cost.beta_mul_le_ceilBeta g
    zukoz
    grind
  have hpolyR : ((g * ztcgu : ℕ) : ℝ) ≤ 3 * (g : ℝ) ^ 2 := by exact_mod_cast hpoly
  grind

/-- The oracle grade of a merge at grade `λ`: `⌈log₂ (γ'_λ + 1)⌉ ≤ ⌈βλ⌉ + 11`. -/
theorem clog_gradeGran_le (g : ℕ) :
    Nat.clog 2 ztlpj ≤ Cost.ceilBeta g + 11 := by
  zudwq
  zulhg
  have hN : gradeGran g ≤ 1201 * 2 ^ Cost.ceilBeta g := by exact_mod_cast h
  grind
open Metric
open Chazelle.Chain (freeIn regionsIn TouchesIn box)
theorem vtx_mem_vertices {P : Polygon} {i : ℕ} (hi : i < P.n) : P.vtx i ∈ P.vertices := by
  zulrw
  zucpl
  grind
namespace ChainObs
open SegObs HSegObs
theorem ord_le (u w : Point) : (ord u w).1.2 ≤ (ord u w).2.2 := by
  zulus
variable {C : Chain}

/-- **The segment obstacles of a chain model are `GoodH`** (simple host; `t` bounds the number of
host vertices at one height). -/
theorem goodH (hP : C.P.Simple) {t : ℕ}
    (ht : ∀ y : ℝ, {p | p ∈ C.P.vertices ∧ p.2 = y}.ncard ≤ t) :
    GoodH C.radius ztfim t := by
  zubo
  zubnz
  zugnf

  · refine Set.Finite.union (((Set.finite_Iio C.m).image
      fun k => ord ztib ztwkj).subset ?_) (Set.toFinite _)
    zugth

  · zugg
    zubcw
    · exact ord_le _ _
    · zubeu

      · exact htop.le
      · zujox
      · zujoy
  · zuza

    · have := C.abs_le_coordBound_of_mem_set h
      exact ztres
    · zukoq
      refine ⟨by zuoum; exact abs_top_fst_lt.le, abs_le.2 ⟨by_grind, h.2.2⟩⟩
    · grind
    grind
  · zuhgv
    have hslit : ztxic := by
      zubok
      zugbo

      have : ztpph := point_ext h2.1 (le_antisymm hle h2.2.1)
      exact ztmqt
    have hsetL : ztgvc := by
      zubok
      have := abs_fst_lt_of_set h1
      grind
    have hsetR : zthpw := by
      zubok
      have := abs_fst_lt_of_set h1
      grind
    have hslitL : ztgvd := by
      zubok
      zudtg
      have := abs_top_fst_lt (C := C)
      grind
    have hslitR : zthpx := by
      zubok
      zudtg
      have := abs_top_fst_lt (C := C)
      grind
    rcases seg_cases hs hp with ⟨h1, k, hk, rfl⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1, -⟩ | ⟨rfl, h1, -⟩ <;>
      zubbf
    · -- two chain edges
      zukcz
      have hidx : C.edgeIdx k ≠ C.edgeIdx j := fun h => hkj ztrir
      have hmem : ztyyz := by
        zujx
        · have := hp; rw [seg_ord, ← C.chainEdge_eq] at this; tauto
        · have := hp'; rw [seg_ord, ← C.chainEdge_eq] at this; tauto
      zucpt

      · zujio
      · zuocz; exact ⟨_, Or.inl ztrds, (ord_ends _ _).2⟩
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    grind
  · zusy
    have hsub : {v | IsVert ztfim v ∧ v.2 = y} ⊆ {p | p ∈ C.P.vertices ∧ p.2 = y} := by
      rintro v ⟨hv, hvy⟩
      obtain ⟨j, -, rfl⟩ := vert_eq_vertex hv by_simp_all
      exact ⟨vtx_mem_vertices ztdyj, hvy⟩
    exact (ncard_le_ncard hsub ztdbo).trans (ht y)
end ChainObs

/-- **The chain half of `HostFullDegSpec`**: for a chain of a simple polygon with at most `t`
vertices at any height, the full augmented map of the chain model has degree at most
`2 (t + 1)`. -/
theorem fullDegLe_host {C : Chain} (hP : C.P.Simple) {t : ℕ}
    (ht : ∀ y : ℝ, {p | p ∈ C.P.vertices ∧ p.2 = y}.ncard ≤ t) (Q : Polygon) :
    (chainModel C).FullDegLe Q (2 * ztbx) := by
  zuhgd
  zudho
  show {c | c ∈ C.chords ∪ F ∧ TouchesIn C.dom c U}.ncard ≤ 2 * ztbx
  zulra
  refine HSegObs.deg_leH (ChainObs.goodH hP ht) (G := C.chords ∪ F) ?_
    ztuxa ztuxk ztmdp
  zubyh
  · zucnz

  · zucyd

/-! ## Host vertices at one height -/
variable (Q : Polygon)
/-- Two vertices of `Q` (indices reduced modulo `n`) at one height coincide (distinct heights). -/
theorem vtx_mod_eq (hDH : DistinctHeights Q) {i j : ℕ}
    (h : (Q.vtx zttoy).2 = (Q.vtx zttpv).2) : Q.vtx zttoy = Q.vtx zttpv := by
  rcases Nat.eq_zero_or_pos Q.n with h0 | h0
  · have hnil : Q.vertices = [] := List.eq_nil_of_length_eq_zero h0
    simp [Polygon.vtx, hnil]
  · zuct
    exact hDH _ _ zthbr zthbr (fun e => hne ztdlt) h

/-- The points of one host item at one height: at most one. -/
theorem item_ncard_le (hDH : DistinctHeights Q) (it : HostItem) (y : ℝ) :
    {p | p ∈ (it.pts Q.n).map ztbzb ∧ p.2 = y}.ncard ≤ 1 := by
  rw [Set.ncard_le_one ztdbo]
  rintro p ⟨hp, hpy⟩ p' ⟨hp', hp'y⟩
  cases it with
  | run a ℓ =>
    simp only [HostItem.pts, List.map_map, List.mem_map, List.mem_range,
      Function.comp_apply] at hp hp'
    obtain ⟨k, -, rfl⟩ := hp
    obtain ⟨k', -, rfl⟩ := hp'
    simp only [SymPt.eval] at hpy hp'y ⊢
    exact vtx_mod_eq Q hDH (hpy.trans hp'y.symm)
  | pt x =>
    simp only [HostItem.pts, List.map_cons, List.map_nil, List.mem_singleton] at hp hp'
    rw [hp, hp']

/-- **A host has at most `H.length` vertices at one height.** -/
theorem host_ncard_le (hDH : DistinctHeights Q) (H : Host) (y : ℝ) :
    {p | p ∈ (Host.poly Q H).vertices ∧ p.2 = y}.ncard ≤ H.length := by
  show {p | p ∈ (Host.pts Q.n H).map ztbzb ∧ p.2 = y}.ncard ≤ H.length
  induction H with
  | nil => zuoun
  | cons it H ih =>
    have hsub : {p | p ∈ (Host.pts Q.n (it :: H)).map ztbzb ∧ p.2 = y} ⊆
        {p | p ∈ (it.pts Q.n).map ztbzb ∧ p.2 = y} ∪
          {p | p ∈ (Host.pts Q.n H).map ztbzb ∧ p.2 = y} := by
      rintro p ⟨hp, hpy⟩
      simp only [Host.pts, List.flatMap_cons, List.map_append, List.mem_append] at hp
      tauto
    have h1 := item_ncard_le Q hDH it y
    calc _ ≤ _ := ncard_le_ncard hsub
          ((ztdbo).union
            ztdbo)
      _ ≤ _ := ncard_union_le _ _
      _ ≤ (it :: H).length := by_grind
theorem gradeRaw_handle_lt {O : OracleIface} {P : Polygon} {m : ℕ → ℕ} {h A : ℕ}
    (hR : Robust A m fun m' => GradeRaw O P m' h A) : h < A := by
  zuhbt
  zubhq
  have := (hR (Function.update m h ztegi) fun a ha => by
    grind).1
  simp_all

/-- **The grade context has local capacity.** -/
theorem gradeCtx_capLocal (O : OracleIface) : (gradeCtx O).CapLocal := by
  intro P m m' g A hmm' hh
  have hlt := gradeRaw_handle_lt (O := O) hh
  show 2 ^ (m' g - 1) = 2 ^ ztlrf
  simp_all
