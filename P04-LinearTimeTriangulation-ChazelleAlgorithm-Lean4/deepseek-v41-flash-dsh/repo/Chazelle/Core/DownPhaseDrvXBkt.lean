module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvXCtx

/-!
# Down phase, extraction (D6): the buckets of the kept ends

The splice bucket `DrvR.keyBkt Q N x` of a position `x` on the closure of arc `j` of
`N = buildNF I Q L E` (`OnArcKey`) is computed from three comparisons with the ends of arc `j`
(`keyBkt_eq`, formula `bktF`):

* at the start of arc `j`: `2 j + 1`;
* at its end (the start of arc `j + 1 mod A`): `2 ((j + 1) mod A) + 1`;
* strictly inside, after the start: `2 j + 2`; strictly inside, before the start (the last arc,
  wrapping): `0`.

This uses that the arcs of `buildNF` are the gaps of the sorted event list in order (S-M1): their
start keys increase strictly (`key_s_strict`), each ends where the next one starts (`key_e_next`),
and no arc start lies inside an arc (arcs are cut-free).  The comparisons of keys of interior walk
positions are those of their edges and of the heights of their vertices (`key_lt_iff`,
`key_eq_iff`: `PosLt`, `PosEq`).
-/

namespace Chazelle.Core

namespace DrvX

@[expose] public section

open Set
open Chazelle.Chain (sideInArc sidePt)
open BuildNF (codeLe wposOf buildNF gapStarts evs evOf)
open DrvR (keyBkt OnArcKey ivB)

variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-! ## The gaps of the event list -/

/-- The key of the event at index `i`. -/
noncomputable def kE (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (i : ℕ) : ℝ :=
  M.key Q (wposOf L (E.getD i 0))

theorem kap_evs' {m : ℕ} (hm : m < E.length) :
    BuildSort.kap (evs M Q L E) m = kE M Q L E m := by
  have hm' : m < (evs M Q L E).length := ⊚ evs, hm
  Ξ BuildSort.kap_eq hm'
  ϴ evs, List.getElem_map
  unfold kE evOf wposOf
  Ξ List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some
  split_ifs <;> rfl

theorem kE_mono' (hsort : E.Pairwise (codeLe M Q L)) {i i' : ℕ} (hii : i ≤ i')
    (hi' : i' < E.length) : kE M Q L E i ≤ kE M Q L E i' := by
  rcases Nat.eq_or_lt_of_le hii with rfl | hlt
  · exact le_rfl
  · have h := List.pairwise_iff_getElem.1 hsort i i' (⋄) hi' hlt
    unfold kE
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (⋄), Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    rcases h with h | ⟨h, -⟩
    · exact h.le
    · exact h.le

/-- The start index of gap `j`. -/
noncomputable def gsX (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (j : ℕ) : ℕ :=
  (gapStarts M Q L E).getD j 0

theorem mem_gapStarts' {m : ℕ} : m ∈ gapStarts M Q L E ↔ m < E.length ∧
    (m + 1 = E.length ∨ BuildSort.kap (evs M Q L E) m < BuildSort.kap (evs M Q L E) (m + 1)) := by
  unfold gapStarts; simp

theorem gsX_eq {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    gsX M Q L E j = (gapStarts M Q L E)[j] := by
  unfold gsX; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

theorem gsX_mem {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    gsX M Q L E j ∈ gapStarts M Q L E := by
  rw [gsX_eq hj]; exact List.getElem_mem hj

theorem gsX_lt_len {j : ℕ} (hj : j < (gapStarts M Q L E).length) : gsX M Q L E j < E.length :=
  (mem_gapStarts'.1 (gsX_mem hj)).1

theorem gsX_lt {j j' : ℕ} (hjj : j < j') (hj' : j' < (gapStarts M Q L E).length) :
    gsX M Q L E j < gsX M Q L E j' := by
  have hj : j < (gapStarts M Q L E).length := ⋄
  Ξ gsX_eq hj, gsX_eq hj'
  exact List.pairwise_iff_getElem.1 (List.Pairwise.filter _ List.pairwise_lt_range) j j' hj
    hj' hjj

/-- Every gap start is some `gsX k`. -/
theorem gsX_of_mem {m : ℕ} (hm : m ∈ gapStarts M Q L E) :
    ∃ k, k < (gapStarts M Q L E).length ∧ gsX M Q L E k = m := by
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.1 hm
  exact ⟨k, hk, by rw [gsX_eq hk]; exact hke⟩

/-- **The keys are constant between consecutive gap starts.** -/
theorem kE_const (hsort : E.Pairwise (codeLe M Q L)) {a b : ℕ} (hab : a ≤ b) (hb : b < E.length)
    (hno : ∀ m, a ≤ m → m < b → m ∉ gapStarts M Q L E) : kE M Q L E a = kE M Q L E b := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    rw [ih (⋄) (fun m h1 h2 => hno m h1 (by omega))]
    have hnm := hno b hab (⋄)
    rw [mem_gapStarts'] at hnm
    push Not at hnm
    obtain ⟨-, hk⟩ := hnm (⋄)
    rw [kap_evs' (m := b + 1) hb, kap_evs' (m := b) (⋄)] at hk
    exact le_antisymm (kE_mono' hsort (⋄) hb) hk

theorem gsX_last (hE : 0 < E.length) :
    0 < (gapStarts M Q L E).length ∧
      gsX M Q L E ((gapStarts M Q L E).length - 1) = E.length - 1 := by
  have hmem : E.length - 1 ∈ gapStarts M Q L E := mem_gapStarts'.2 ⟨by omega, Or.inl (by omega)⟩
  obtain ⟨j₀, hj₀, hj₀e⟩ := gsX_of_mem hmem
  have hA : 0 < (gapStarts M Q L E).length := by omega
  refine ⟨hA, ?_⟩
  by_contra hne
  have hlt : j₀ < (gapStarts M Q L E).length - 1 := by
    rcases Nat.lt_or_ge j₀ ((gapStarts M Q L E).length - 1) with h | h
    · exact h
    · exact absurd (by rw [show (gapStarts M Q L E).length - 1 = j₀ by omega]; exact hj₀e) hne
  have h1 := gsX_lt (M := M) (Q := Q) (L := L) (E := E) hlt (by omega)
  have h2 := gsX_lt_len (M := M) (Q := Q) (L := L) (E := E)
    (j := (gapStarts M Q L E).length - 1) (by omega)
  omega

/-! ## The arcs of `buildNF` -/

section arcs

variable (hK : 0 < L.length) (hsort : E.Pairwise (codeLe M Q L))
  (hE : E.length = 2 * L.length)
include hK hsort hE

omit hK hsort hE in
theorem arcsLen (hK : 0 < L.length) (_hsort : E.Pairwise (codeLe M Q L))
    (_hE : E.length = 2 * L.length) : (buildNF M Q L E).arcs.length = (gapStarts M Q L E).length := by
  Ξ DownDrv.buildNF_arcs hK, List.length_map

omit hK hsort hE in
theorem keyS (hK : 0 < L.length) (_hsort : E.Pairwise (codeLe M Q L))
    (_hE : E.length = 2 * L.length) {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    M.key Q ((buildNF M Q L E).arc j).s = kE M Q L E (gsX M Q L E j) := by
  have h := DownDrv.buildNF_arc (M := M) (Q := Q) (L := L) (E := E) hK hj
  unfold NF.arc; rw [h]; rfl

omit hK hsort hE in
theorem keyE (hK : 0 < L.length) (_hsort : E.Pairwise (codeLe M Q L))
    (_hE : E.length = 2 * L.length) {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    M.key Q ((buildNF M Q L E).arc j).e = kE M Q L E ((gsX M Q L E j + 1) % E.length) := by
  have h := DownDrv.buildNF_arc (M := M) (Q := Q) (L := L) (E := E) hK hj
  unfold NF.arc; rw [h]; rfl

/-- **The start keys of the arcs increase strictly.** -/
theorem key_s_strict {j j' : ℕ} (hjj : j < j') (hj' : j' < (buildNF M Q L E).arcs.length) :
    M.key Q ((buildNF M Q L E).arc j).s < M.key Q ((buildNF M Q L E).arc j').s := by
  rw [arcsLen hK hsort hE] at hj'
  have hE0 : 0 < E.length := by omega
  rw [keyS hK hsort hE (by omega), keyS hK hsort hE hj']
  have hlt := gsX_lt (M := M) (Q := Q) (L := L) (E := E) hjj hj'
  have hj'len := gsX_lt_len (M := M) (Q := Q) (L := L) (E := E) hj'
  rcases (mem_gapStarts'.1 (gsX_mem (M := M) (Q := Q) (L := L) (E := E)
    (show j < (gapStarts M Q L E).length by omega))).2 with h | h
  · omega
  · rw [kap_evs' (by omega), kap_evs' (by omega)] at h
    exact lt_of_lt_of_le h (kE_mono' hsort (by omega) hj'len)

/-- **Each arc ends where the next one starts.** -/
theorem key_e_next {j : ℕ} (hj : j < (buildNF M Q L E).arcs.length) :
    M.key Q ((buildNF M Q L E).arc j).e =
      M.key Q ((buildNF M Q L E).arc ((j + 1) % (buildNF M Q L E).arcs.length)).s := by
  rw [arcsLen hK hsort hE] at hj ⊢
  have hE0 : 0 < E.length := by omega
  obtain ⟨hA, hlast⟩ := gsX_last (M := M) (Q := Q) (L := L) hE0
  rw [keyE hK hsort hE hj, keyS hK hsort hE (Nat.mod_lt _ hA)]
  by_cases hj1 : j + 1 < (gapStarts M Q L E).length
  · rw [Nat.mod_eq_of_lt hj1]
    have h1 := gsX_lt (M := M) (Q := Q) (L := L) (E := E) (show j < j + 1 by omega) hj1
    have h2 := gsX_lt_len (M := M) (Q := Q) (L := L) (E := E) hj1
    rw [Nat.mod_eq_of_lt (by omega)]
    refine kE_const hsort (by omega) h2 fun m hm1 hm2 hmem => ?_
    obtain ⟨k, hk, hke⟩ := gsX_of_mem hmem
    rcases Nat.lt_or_ge k (j + 1) with hk' | hk'
    · rcases Nat.lt_or_ge k j with hk'' | hk''
      · have := gsX_lt (M := M) (Q := Q) (L := L) (E := E) hk'' hj; omega
      · have : k = j := by omega
        subst this; omega
    · rcases Nat.lt_or_ge (j + 1) k with hk'' | hk''
      · have := gsX_lt (M := M) (Q := Q) (L := L) (E := E) hk'' hk; omega
      · have : k = j + 1 := by omega
        subst this; omega
  · have hjl : j = (gapStarts M Q L E).length - 1 := by omega
    rw [show j + 1 = (gapStarts M Q L E).length by omega, Nat.mod_self, hjl, hlast,
      Nat.sub_add_cancel hE0, Nat.mod_self]
    have h0 := gsX_lt_len (M := M) (Q := Q) (L := L) (E := E) hA
    refine kE_const hsort (Nat.zero_le _) h0 fun m hm1 hm2 hmem => ?_
    obtain ⟨k, hk, hke⟩ := gsX_of_mem hmem
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · omega
    · have := gsX_lt (M := M) (Q := Q) (L := L) (E := E) hk0 hk; omega

end arcs

/-! ## Counting the arc starts below a key -/

theorem filter_range_length {A c : ℕ} {p : ℕ → Bool} (hc : c ≤ A)
    (hp : ∀ j, j < A → (p j = true ↔ j < c)) : ((List.range A).filter p).length = c := by
  induction A generalizing c with
  | zero => simp; omega
  | succ A ih =>
    Ξ List.range_succ, List.filter_append, List.length_append
    rcases Nat.lt_or_ge A c with h | h
    · have hc' : c = A + 1 := ⋄
      have hA := (hp A (⋄)).2 h
      have h1 := ih (c := A) le_rfl fun j hj => ⟨fun _ => hj, fun _ => (hp j (⋄)).2 (⋄)⟩
      Θ hA, h1, hc'
    · have hA : p A = false := by
        cases h' : p A
        · rfl
        · exact absurd ((hp A (⋄)).1 h') (by omega)
      have h1 := ih (c := c) h fun j hj => hp j (⋄)
      Θ hA, h1

open Classical in
/-- **The bucket of a position on the closure of an arc** of `N`. -/
theorem keyBkt_eq {N : NF} {A : ℕ} (hA : N.arcs.length = A)
    (hinc : ∀ j j', j < j' → j' < A →
      (interiorModel Q).key Q (N.arc j).s < (interiorModel Q).key Q (N.arc j').s)
    (hnext : ∀ j, j < A →
      (interiorModel Q).key Q (N.arc j).e = (interiorModel Q).key Q (N.arc ((j + 1) % A)).s)
    (hfree : ∀ j j', j < A → j' < A → ¬ sideInArc ((interiorModel Q).key Q (N.arc j).s)
      ((interiorModel Q).key Q (N.arc j).e) ((interiorModel Q).key Q (N.arc j').s))
    {x : WPos} {j : ℕ} (hj : j < A) (hon : OnArcKey Q N j x) :
    keyBkt Q N x = bktF A j
      ((interiorModel Q).key Q x = (interiorModel Q).key Q (N.arc j).s)
      ((interiorModel Q).key Q x = (interiorModel Q).key Q (N.arc j).e)
      ((interiorModel Q).key Q (N.arc j).s < (interiorModel Q).key Q x) := by
  set ks : ℕ → ℝ := fun j => (interiorModel Q).key Q (N.arc j).s with hks
  set ke : ℕ → ℝ := fun j => (interiorModel Q).key Q (N.arc j).e with hke
  set kx := (interiorModel Q).key Q x with hkx
  have hinj : ∀ j j', j < A → j' < A → ks j = ks j' → j = j' := by
    intro j j' hj hj' he
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd he (hinc j j' h hj').ne
    · exact absurd he.symm (hinc j' j h hj).ne
  -- the count of starts below `ks c`, for a start index `c`
  have hcount : ∀ c, c ≤ A → (∀ j', j' < A → (ks j' < kx ↔ j' < c)) →
      ((List.range N.arcs.length).filter fun j' =>
        decide ((interiorModel Q).key Q (N.arc j').s < kx)).length = c := by
    intro c hc h
    Ξ hA
    exact filter_range_length hc fun j' hj' => by simp only [decide_eq_true_eq]; exact h j' hj'
  have hbelow : ∀ c, c < A → ∀ j', j' < A → (ks j' < ks c ↔ j' < c) := by
    intro c hc j' hj'
    constructor
    · intro h; by_contra h'
      rcases (Nat.le_of_not_lt h').lt_or_eq with h'' | rfl
      · exact absurd (hinc c j' h'' hj') (not_lt.2 h.le)
      · exact lt_irrefl _ h
    · intro h; exact hinc j' c h hc
  unfold keyBkt bktF
  by_cases hS : kx = ks j
  · rw [ite_eq_left hS, hcount j hj.le (fun j' hj' => by rw [hS]; exact hbelow j hj j' hj'),
      ite_eq_left ⟨j, by rw [hA]; exact hj, hS.symm⟩]
  · Ξ ite_eq_right hS
    by_cases hE : kx = ke j
    · have hj2 : (j + 1) % A < A := Nat.mod_lt _ (⋄)
      have hE' : kx = ks ((j + 1) % A) := hE.trans (hnext j hj)
      rw [ite_eq_left hE, hcount _ hj2.le (fun j' hj' => by rw [hE']; exact hbelow _ hj2 j' hj'),
        ite_eq_left ⟨_, by rw [hA]; exact hj2, hE'.symm⟩]
    · Ξ ite_eq_right hE
      have hin : sideInArc (ks j) (ke j) kx := by
        rcases hon with h | h | h
        · exact absurd h hS
        · exact absurd h hE
        · exact h
      have hnoeq : ¬ ∃ j', j' < N.arcs.length ∧ (interiorModel Q).key Q (N.arc j').s = kx := by
        rintro ⟨j', hj', he⟩
        rw [hA] at hj'
        exact hfree j j' hj hj' (by rw [show (interiorModel Q).key Q (N.arc j').s = kx from he]; exact hin)
      Ξ ite_eq_right hnoeq
      by_cases hG : ks j < kx
      · rw [ite_eq_left hG, hcount (j + 1) (⋄) fun j' hj' => ?_]
        · ring
        · constructor
          · intro h; by_contra h'
            have hjj : j < j' := ⋄
            refine hfree j j' hj hj' ?_
            have h1 := hinc j j' hjj hj'
            unfold sideInArc at hin ⊢
            split_ifs at hin ⊢ with hse
            · exact ⟨h1, lt_trans h hin.2⟩
            · exact Or.inl h1
          · intro h
            rcases (Nat.lt_succ_iff.1 h).lt_or_eq with h' | rfl
            · exact lt_trans (hinc j' j h' hj) hG
            · exact hG
      · have hlt : kx < ks j := lt_of_le_of_ne (not_lt.1 hG) (fun e => hS e)
        Ξ ite_eq_right hG, hcount 0 (Nat.zero_le _) fun j' hj' => ?_
        constructor
        · intro h
          exfalso
          refine hfree j j' hj hj' ?_
          unfold sideInArc at hin ⊢
          split_ifs at hin ⊢ with hse
          · linarith [hin.1]
          · rcases hin with h1 | h1
            · linarith
            · exact Or.inr (lt_trans h h1)
        · intro h; omega

/-! ## Comparing keys of interior positions -/

section keys

variable {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) (hdh : DistinctHeights Q)
  (hn : 2 ≤ Q.n)
include hli hdh hn

/-- The parameter of an interior position at a vertex height. -/
theorem param_eq {x : WPos} (hx1 : 1 ≤ x.hgt) (hq : x.edge < Q.n) :
    (interiorModel Q).param Q x = ((Q.vtx (x.hgt - 1)).2 - (Q.vtx (ivB li Q.n x.edge)).2) /
      ((Q.vtx (ivB li Q.n ((x.edge + 1) % Q.n))).2 - (Q.vtx (ivB li Q.n x.edge)).2) := by
  have hq1 : (x.edge + 1) % Q.n < Q.n := Nat.mod_lt _ (by omega)
  have hd : (Q.vtx (ivB li Q.n x.edge)).2 ≠ (Q.vtx (ivB li Q.n ((x.edge + 1) % Q.n))).2 := by
    refine hdh _ _ (DownMath.ivB_lt li hq) (DownMath.ivB_lt li hq1) fun h' => ?_
    have := DownMath.ivB_inj li hq hq1 h'
    by_cases h1 : x.edge + 1 < Q.n
    · rw [Nat.mod_eq_of_lt h1] at this; omega
    · rw [show x.edge + 1 = Q.n by omega, Nat.mod_self] at this; omega
  have hW : (interiorModel Q).W = interiorWalk Q := rfl
  have ha : (interiorModel Q).wa x.edge = Q.vtx (ivB li Q.n x.edge) := by
    unfold Model.wa; rw [hW, DownMath.walk_vtx hli hq]
  have hb : (interiorModel Q).wb x.edge = Q.vtx (ivB li Q.n ((x.edge + 1) % Q.n)) := by
    unfold Model.wb; rw [hW, DownMath.walk_n, DownMath.walk_vtx hli hq1]
  obtain ⟨e, h⟩ := x
  cases h with
  | zero => simp at hx1
  | succ h =>
    show (if ((interiorModel Q).wa e).2 = ((interiorModel Q).wb e).2 then 0
      else ((Q.vtx h).2 - ((interiorModel Q).wa e).2) /
        (((interiorModel Q).wb e).2 - ((interiorModel Q).wa e).2)) = _
    simp only at ha hb hd ⊢
    rw [ha, hb, ite_eq_right hd, Nat.add_sub_cancel]

/-- On one walk edge, the parameter order is the height order (reversed on a descending edge). -/
theorem param_lt_iff {x y : WPos} (hx1 : 1 ≤ x.hgt) (hy1 : 1 ≤ y.hgt) (hxy : x.edge = y.edge)
    (hq : x.edge < Q.n) (ha : x.hgt - 1 < Q.n) (hb : y.hgt - 1 < Q.n) (hab : x.hgt ≠ y.hgt) :
    (interiorModel Q).param Q x < (interiorModel Q).param Q y ↔
      (EdgeUp Q li x.edge ↔ (Q.vtx (x.hgt - 1)).2 < (Q.vtx (y.hgt - 1)).2) := by
  have hq1 : (x.edge + 1) % Q.n < Q.n := Nat.mod_lt _ (by omega)
  rw [param_eq hli hdh hn hx1 hq, param_eq hli hdh hn hy1 (hxy ▸ hq), ← hxy]
  have hd : (Q.vtx (ivB li Q.n x.edge)).2 ≠ (Q.vtx (ivB li Q.n ((x.edge + 1) % Q.n))).2 := by
    refine hdh _ _ (DownMath.ivB_lt li hq) (DownMath.ivB_lt li hq1) fun h' => ?_
    have := DownMath.ivB_inj li hq hq1 h'
    by_cases h1 : x.edge + 1 < Q.n
    · rw [Nat.mod_eq_of_lt h1] at this; omega
    · rw [show x.edge + 1 = Q.n by omega, Nat.mod_self] at this; omega
  have hab' := hdh _ _ ha hb (by omega)
  unfold EdgeUp
  rcases lt_or_gt_of_ne hd with hup | hdown
  · have hpos : 0 < (Q.vtx (ivB li Q.n ((x.edge + 1) % Q.n))).2 - (Q.vtx (ivB li Q.n x.edge)).2 := by
      linarith
    rw [div_lt_div_iff_of_pos_right hpos]
    constructor
    · intro h; exact ⟨fun _ => by linarith, fun _ => hup⟩
    · intro h; have := h.1 hup; linarith
  · have hneg : (Q.vtx (ivB li Q.n ((x.edge + 1) % Q.n))).2 - (Q.vtx (ivB li Q.n x.edge)).2 < 0 := by
      linarith
    rw [div_lt_div_right_of_neg hneg]
    constructor
    · intro h; exact ⟨fun h' => absurd h' (not_lt.2 hdown.le), fun h' => absurd h' (by linarith)⟩
    · intro h
      rcases lt_or_gt_of_ne hab' with h' | h'
      · exact absurd (h.2 h') (not_lt.2 hdown.le)
      · linarith

/-- **Key order of interior positions** by edges and heights. -/
theorem key_lt_iff {x y : WPos} (hx : ProperPos (interiorModel Q) Q Q.n x)
    (hy : ProperPos (interiorModel Q) Q Q.n y) (hx1 : 1 ≤ x.hgt) (hy1 : 1 ≤ y.hgt)
    (hxe : x.edge < Q.n) :
    (interiorModel Q).key Q x < (interiorModel Q).key Q y ↔ PosLt Q li x y := by
  have hxn : x.hgt - 1 < Q.n := by have := hx.2.2; omega
  have hyn : y.hgt - 1 < Q.n := by have := hy.2.2; omega
  have hpx := hx.1
  have hpx1 := hx.2.1
  have hpy := hy.1
  have hpy1 := hy.2.1
  have hkx : (interiorModel Q).key Q x = x.edge + (interiorModel Q).param Q x := rfl
  have hky : (interiorModel Q).key Q y = y.edge + (interiorModel Q).param Q y := rfl
  Ξ hkx, hky
  unfold PosLt
  constructor
  · intro h
    rcases Nat.lt_or_ge x.edge y.edge with h1 | h1
    · exact Or.inl h1
    · rcases h1.lt_or_eq with h2 | h2
      · exfalso
        have : (y.edge : ℝ) + 1 ≤ x.edge := by exact_mod_cast h2
        linarith
      · right
        have he := h2.symm
        have hne : x.hgt ≠ y.hgt := by
          intro hh
          have : x = y := by cases x; cases y; simp_all
          rw [this] at h; exact lt_irrefl _ h
        refine ⟨he, hne, ?_⟩
        rw [he] at h
        exact (param_lt_iff hli hdh hn hx1 hy1 he hxe hxn hyn hne).1 (⟡)
  · rintro (h | ⟨h1, h2, h3⟩)
    · have : (x.edge : ℝ) + 1 ≤ y.edge := by exact_mod_cast h
      linarith
    · have := (param_lt_iff hli hdh hn hx1 hy1 h1 hxe hxn hyn h2).2 h3
      rw [h1]; linarith

/-- **Key equality of interior positions**: equal edges and heights. -/
theorem key_eq_iff {x y : WPos} (hx : ProperPos (interiorModel Q) Q Q.n x)
    (hy : ProperPos (interiorModel Q) Q Q.n y) (hx1 : 1 ≤ x.hgt) (hy1 : 1 ≤ y.hgt)
    (hxe : x.edge < Q.n) (hye : y.edge < Q.n) :
    (interiorModel Q).key Q x = (interiorModel Q).key Q y ↔ PosEq x y := by
  constructor
  · intro h
    have h1 : ¬ PosLt Q li x y := fun h' =>
      absurd h ((key_lt_iff hli hdh hn hx hy hx1 hy1 hxe).2 h').ne
    have h2 : ¬ PosLt Q li y x := fun h' =>
      absurd h.symm ((key_lt_iff hli hdh hn hy hx hy1 hx1 hye).2 h').ne
    unfold PosLt at h1 h2
    have he : x.edge = y.edge := by
      rcases Nat.lt_trichotomy x.edge y.edge with h' | h' | h'
      · exact absurd (Or.inl h') h1
      · exact h'
      · exact absurd (Or.inl h') h2
    refine ⟨he, ?_⟩
    by_contra hh
    have hxn : x.hgt - 1 < Q.n := by have := hx.2.2; omega
    have hyn : y.hgt - 1 < Q.n := by have := hy.2.2; omega
    have hd := hdh _ _ hxn hyn (⋄)
    rw [← he] at h2
    by_cases hup : EdgeUp Q li x.edge
    · rcases lt_or_gt_of_ne hd with h' | h'
      · exact h1 (Or.inr ⟨he, hh, ⟨fun _ => h', fun _ => hup⟩⟩)
      · exact h2 (Or.inr ⟨rfl, Ne.symm hh, ⟨fun _ => h', fun _ => hup⟩⟩)
    · rcases lt_or_gt_of_ne hd with h' | h'
      · exact h2 (Or.inr ⟨rfl, Ne.symm hh,
          ⟨fun h'' => absurd h'' hup, fun h'' => absurd h'' (not_lt.2 h'.le)⟩⟩)
      · exact h1 (Or.inr ⟨he, hh,
          ⟨fun h'' => absurd h'' hup, fun h'' => absurd h'' (not_lt.2 h'.le)⟩⟩)
  · rintro ⟨he, hh⟩
    have : x = y := by cases x; cases y; simp_all
    Ξ this

end keys

end

end DrvX

end Chazelle.Core
