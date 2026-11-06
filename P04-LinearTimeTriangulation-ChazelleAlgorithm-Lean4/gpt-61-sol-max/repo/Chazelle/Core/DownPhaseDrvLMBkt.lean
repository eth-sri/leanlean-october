module

public import Chazelle.Core.DownPhaseDrvLMHost

/-!
# Down-phase level math (D7), part 2: the buckets of the extracted chord ends

`DrvR.keyBkt Q N x` is `2 · #{arc starts below key x} + [key x is an arc start]`.

* `keyBkt_le`: at most `2 · #arcs + 1`;
* `key_lt_of_keyBkt_lt`: a smaller bucket means a smaller key;
* for `N = buildNF I Q L E` (`K > 0`): the arc starts increase strictly (`st_lt`), every arc
  other than the last ends at the next start (`key_e_eq`), the last one at the first start
  (`key_e_last_eq`);
* **`arc_of_bkt`**: a position on the closure of arc `j` has a bucket `b` with
  `j = arcA A b ∨ j = arcB A b` — every bucket meets at most two arcs.
-/

namespace Chazelle.Core

namespace DrvLM

@[expose] public section

open DrvR (keyBkt OnArcKey)
open BuildNF (codeLe wposOf gapStarts)
open Chazelle.Chain (sideInArc)

/-! ## Buckets and keys -/

theorem keyBkt_le (Q : Polygon) (N : NF) (x : WPos) : keyBkt Q N x ≤ 2 * N.arcs.length + 1 := by
  unfold keyBkt
  have := List.length_filter_le (fun j => decide ((interiorModel Q).key Q (N.arc j).s <
    (interiorModel Q).key Q x)) (List.range N.arcs.length)
  rw [List.length_range] at this
  split_ifs <;> omega

/-- Filtering a range by a stronger predicate, with a witness, is shorter. -/
theorem filter_range_lt {p p' : ℕ → Bool} (hpp : ∀ i, p i = true → p' i = true) {A j : ℕ}
    (hj : j < A) (hj1 : p' j = true) (hj0 : p j = false) :
    ((List.range A).filter p).length < ((List.range A).filter p').length := by
  induction A with
  | zero => omega
  | succ A ih =>
    rw [List.range_succ, List.filter_append, List.filter_append, List.length_append,
      List.length_append]
    have hle : ((List.range A).filter p).length ≤ ((List.range A).filter p').length :=
      (List.monotone_filter_right _ (fun {i} h => hpp i h)).length_le
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · have := ih h
      have : ([A].filter p).length ≤ ([A].filter p').length := by
        simp only [List.filter_cons, List.filter_nil]
        cases h1 : p A
        · simp
        · simp [hpp A h1]
      omega
    · subst h
      simp [hj1, hj0, hle]

theorem keyBkt_mono (Q : Polygon) (N : NF) {x y : WPos}
    (h : (interiorModel Q).key Q y ≤ (interiorModel Q).key Q x) :
    keyBkt Q N y ≤ keyBkt Q N x := by
  classical
  rcases lt_or_eq_of_le h with h | h
  · unfold keyBkt
    have hle : ((List.range N.arcs.length).filter fun j =>
          decide ((interiorModel Q).key Q (N.arc j).s < (interiorModel Q).key Q y)).length ≤
        ((List.range N.arcs.length).filter fun j =>
          decide ((interiorModel Q).key Q (N.arc j).s < (interiorModel Q).key Q x)).length :=
      (List.monotone_filter_right _ (fun {i} hi => by
        simp only [decide_eq_true_eq] at hi ⊢; linarith)).length_le
    by_cases hex : ∃ j, j < N.arcs.length ∧
        (interiorModel Q).key Q (N.arc j).s = (interiorModel Q).key Q y
    · obtain ⟨j, hj, hjy⟩ := hex
      have hlt := filter_range_lt (A := N.arcs.length) (j := j)
        (p := fun j => decide ((interiorModel Q).key Q (N.arc j).s < (interiorModel Q).key Q y))
        (p' := fun j => decide ((interiorModel Q).key Q (N.arc j).s < (interiorModel Q).key Q x))
        (fun i hi => by simp only [decide_eq_true_eq] at hi ⊢; linarith) hj
        (by simp only [decide_eq_true_eq]; linarith) (by simp [hjy])
      rw [ite_eq_left ⟨j, hj, hjy⟩]
      split_ifs <;> omega
    · rw [ite_eq_right hex]
      split_ifs <;> omega
  · unfold keyBkt; rw [h]

/-- **A smaller bucket means a smaller key.** -/
theorem key_lt_of_keyBkt_lt (Q : Polygon) (N : NF) {x y : WPos}
    (h : keyBkt Q N x < keyBkt Q N y) :
    (interiorModel Q).key Q x < (interiorModel Q).key Q y := by
  by_contra hc
  push Not at hc
  have := keyBkt_mono Q N hc
  omega

/-! ## Counting the ends of a bucket -/

section count

open DrvR (bcnt bfilt)

theorem bcnt_congr {bk bk' : ℕ → ℕ} {n b : ℕ} (h : ∀ q, q < n → bk q = bk' q) :
    bcnt bk n b = bcnt bk' n b := by
  unfold bcnt bfilt
  congr 1
  refine List.filter_congr fun q hq => ?_
  rw [List.mem_range] at hq
  rw [h q hq]

theorem bcnt_le (bk : ℕ → ℕ) (n b : ℕ) : bcnt bk n b ≤ n := by
  unfold bcnt bfilt
  have := List.length_filter_le (fun q => decide (bk q = b)) (List.range n)
  rwa [List.length_range] at this

theorem bcnt_add (bk : ℕ → ℕ) (a c b : ℕ) :
    bcnt bk (a + c) b = bcnt bk a b + bcnt (fun q => bk (a + q)) c b := by
  induction c with
  | zero => simp [bcnt, bfilt]
  | succ c ih =>
    rw [← Nat.add_assoc, DrvR.bcnt_succ, ih, DrvR.bcnt_succ (bk := fun q => bk (a + q))]
    split_ifs <;> omega

/-- The number of ends of `l` in bucket `b`. -/
noncomputable def cntB (Q : Polygon) (N : NF) (l : List (ℕ × ℕ × ℕ)) (b : ℕ) : ℕ :=
  bcnt (fun q => keyBkt Q N (DrvR.endPos l q)) (2 * l.length) b

theorem endPos_append_left {l₁ l₂ : List (ℕ × ℕ × ℕ)} {q : ℕ} (hq : q < 2 * l₁.length) :
    DrvR.endPos (l₁ ++ l₂) q = DrvR.endPos l₁ q := by
  unfold DrvR.endPos
  rw [List.getD_append _ _ _ _ (by omega)]

theorem endPos_append_right (l₁ l₂ : List (ℕ × ℕ × ℕ)) (q : ℕ) :
    DrvR.endPos (l₁ ++ l₂) (2 * l₁.length + q) = DrvR.endPos l₂ q := by
  have e2 : (2 * l₁.length + q) / 2 = l₁.length + q / 2 := by omega
  have e3 : (2 * l₁.length + q) % 2 = q % 2 := by omega
  unfold DrvR.endPos
  rw [e2, e3, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

variable {Q : Polygon} {N : NF}

theorem cntB_nil (b : ℕ) : cntB Q N [] b = 0 := by simp [cntB, bcnt, bfilt]

theorem cntB_append (l₁ l₂ : List (ℕ × ℕ × ℕ)) (b : ℕ) :
    cntB Q N (l₁ ++ l₂) b = cntB Q N l₁ b + cntB Q N l₂ b := by
  unfold cntB
  rw [List.length_append, Nat.mul_add, bcnt_add]
  congr 1
  · exact bcnt_congr fun q hq => by simp only [endPos_append_left hq]
  · exact bcnt_congr fun q _ => by simp only [endPos_append_right]

theorem cntB_flatMap (Lx : ℕ → List (ℕ × ℕ × ℕ)) (R b : ℕ) :
    cntB Q N ((List.range R).flatMap Lx) b = ∑ r ∈ Finset.range R, cntB Q N (Lx r) b := by
  induction R with
  | zero => simp [cntB_nil]
  | succ R ih =>
    rw [List.range_succ, List.flatMap_append, cntB_append, ih, Finset.sum_range_succ]
    simp

theorem length_flatMap_range (Lx : ℕ → List (ℕ × ℕ × ℕ)) (R : ℕ) :
    ((List.range R).flatMap Lx).length = ∑ r ∈ Finset.range R, (Lx r).length := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, Finset.sum_range_succ]
    simp

/-- **A bucket fed by two regions** holds at most `4 M` ends. -/
theorem cntB_flat_le {Lx : ℕ → List (ℕ × ℕ × ℕ)} {R M b : ℕ} (rA rB : ℕ)
    (hM : ∀ r, r < R → (Lx r).length ≤ M)
    (hreg : ∀ r, r < R → ∀ q, q < 2 * (Lx r).length →
      keyBkt Q N (DrvR.endPos (Lx r) q) = b → r = rA ∨ r = rB) :
    cntB Q N ((List.range R).flatMap Lx) b ≤ 4 * M := by
  classical
  rw [cntB_flatMap]
  have hper : ∀ r ∈ Finset.range R, cntB Q N (Lx r) b ≤
      (if r = rA then 2 * M else 0) + (if r = rB then 2 * M else 0) := by
    intro r hr
    rw [Finset.mem_range] at hr
    by_cases hab : r = rA ∨ r = rB
    · have h1 : cntB Q N (Lx r) b ≤ 2 * M := (bcnt_le _ _ _).trans (by have := hM r hr; omega)
      rcases hab with h | h <;> split_ifs <;> omega
    · have h0 : cntB Q N (Lx r) b = 0 := by
        unfold cntB bcnt bfilt
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro q hq hqb
        rw [List.mem_range] at hq
        exact hab (hreg r hr q hq (of_decide_eq_true hqb))
      rw [h0]; exact Nat.zero_le _
  refine (Finset.sum_le_sum hper).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  split_ifs <;> omega

end count

/-! ## The order of the new codes -/

/-- The positions of the new event codes. -/
theorem wposOf_new' {L L₂ : List (ℕ × ℕ × ℕ)} {q : ℕ} (_hq : q < 2 * L₂.length) :
    wposOf (L ++ L₂) (2 * L.length + q) = DrvR.endPos L₂ q := by
  have e2 : (2 * L.length + q) / 2 = L.length + q / 2 := by omega
  have e3 : (2 * L.length + q) % 2 = q % 2 := by omega
  have hg : (L ++ L₂).getD (L.length + q / 2) (0, 0, 0) = L₂.getD (q / 2) (0, 0, 0) := by
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  unfold wposOf DrvR.endPos
  rw [e3, e2]
  simp only [BuildRegions.crec, hg]

/-- **Bucket order gives code order.** -/
theorem codeLe_of_keyBkt (Q : Polygon) (N : NF) {L L₂ : List (ℕ × ℕ × ℕ)} {q q' : ℕ}
    (hq : q < 2 * L₂.length) (hq' : q' < 2 * L₂.length)
    (h : keyBkt Q N (DrvR.endPos L₂ q) < keyBkt Q N (DrvR.endPos L₂ q')) :
    codeLe (interiorModel Q) Q (L ++ L₂) (2 * L.length + q) (2 * L.length + q') := by
  left
  rw [wposOf_new' hq, wposOf_new' hq']
  exact key_lt_of_keyBkt_lt Q N h

/-! ## The arcs of `buildNF` -/

section arcs

variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-- The key of the start of arc `i`. -/
noncomputable def st (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (i : ℕ) : ℝ :=
  (interiorModel Q).key Q ((BuildNF.buildNF (interiorModel Q) Q L E).arc i).s

/-- Equal keys between gap starts. -/
theorem kE_const (hsort : E.Pairwise (codeLe (interiorModel Q) Q L)) {a b : ℕ} (hab : a ≤ b)
    (hb : b < E.length)
    (hgap : ∀ m, a ≤ m → m < b → m ∉ gapStarts (interiorModel Q) Q L E) :
    DrvD.kE (interiorModel Q) Q L E a = DrvD.kE (interiorModel Q) Q L E b := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    have h1 := ih (by omega) (fun m h1 h2 => hgap m h1 (by omega))
    have hm := hgap b hab (by omega)
    rw [DrvD.mem_gapStarts] at hm
    push Not at hm
    have h2 := (hm (by omega)).2
    rw [DrvD.kap_evs (by omega), DrvD.kap_evs (by omega)] at h2
    have h3 := DrvD.kE_mono hsort (show b ≤ b + 1 by omega) hb
    linarith

/-- A gap start index is some `gs k`. -/
theorem gs_of_mem {m : ℕ} (hm : m ∈ gapStarts (interiorModel Q) Q L E) :
    ∃ k, k < (gapStarts (interiorModel Q) Q L E).length ∧ DrvD.gs (interiorModel Q) Q L E k = m := by
  obtain ⟨k, hk, hkm⟩ := List.mem_iff_getElem.1 hm
  exact ⟨k, hk, by rw [DrvD.gs_eq hk]; exact hkm⟩

theorem gs_strict {k k' : ℕ} (hk : k < (gapStarts (interiorModel Q) Q L E).length)
    (_hk' : k' < (gapStarts (interiorModel Q) Q L E).length)
    (h : DrvD.gs (interiorModel Q) Q L E k < DrvD.gs (interiorModel Q) Q L E k') : k < k' := by
  by_contra hc
  push Not at hc
  rcases lt_or_eq_of_le hc with hc | hc
  · have := DrvD.gs_lt_gs (M := interiorModel Q) (Q := Q) (L := L) (E := E) hc
      (by omega)
    omega
  · subst hc; omega

/-! ## The bucket of a key -/

theorem len_filter_lt (c A : ℕ) :
    ((List.range A).filter fun i => decide (i < c)).length = min A c := by
  induction A with
  | zero => simp
  | succ A ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : A < c
    · simp [h]; omega
    · simp [h]; omega

/-- The bucket of a key, from the number `c` of arc starts below it. -/
theorem keyBkt_eq {x : WPos} {A c : ℕ}
    (hA : (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length = A) (hc : c ≤ A)
    (h : ∀ i, i < A → (st Q L E i < (interiorModel Q).key Q x ↔ i < c)) :
    ((∃ i, i < A ∧ st Q L E i = (interiorModel Q).key Q x) →
      keyBkt Q (BuildNF.buildNF (interiorModel Q) Q L E) x = 2 * c + 1) ∧
    ((¬ ∃ i, i < A ∧ st Q L E i = (interiorModel Q).key Q x) →
      keyBkt Q (BuildNF.buildNF (interiorModel Q) Q L E) x = 2 * c) := by
  classical
  subst hA
  have hf : ((List.range (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length).filter fun j =>
      decide ((interiorModel Q).key Q ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).s <
        (interiorModel Q).key Q x)) =
      (List.range (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length).filter
        fun i => decide (i < c) := by
    refine List.filter_congr fun i hi => ?_
    rw [List.mem_range] at hi
    exact decide_eq_decide.2 (h i hi)
  have hm : min (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length c = c := Nat.min_eq_right hc
  constructor
  · intro hex
    unfold st at hex
    unfold keyBkt
    rw [hf, len_filter_lt, hm, ite_eq_left hex]
  · intro hex
    unfold st at hex
    unfold keyBkt
    rw [hf, len_filter_lt, hm, ite_eq_right hex, Nat.add_zero]

/-- The first arc of bucket `b` (`A` arcs). -/
def arcA (A b : ℕ) : ℕ := if b = 0 then A - 1 else (b - 1) / 2

/-- The second arc of bucket `b`. -/
def arcB (A b : ℕ) : ℕ := if b ≤ 1 then A - 1 else (b - 1) / 2 - 1

variable (hK : 0 < L.length) (hperm : E.Perm (List.range (2 * L.length)))
  (hsort : E.Pairwise (codeLe (interiorModel Q) Q L))
include hK hperm hsort

omit hK hperm hsort in
theorem hElen (hK : 0 < L.length) (hperm : E.Perm (List.range (2 * L.length)))
    (_hsort : E.Pairwise (codeLe (interiorModel Q) Q L)) : 0 < E.length := by rw [hperm.length_eq, List.length_range]; omega

/-- **The arc starts increase strictly.** -/
theorem st_lt {i i' : ℕ} (hii : i < i') (hi' : i' < (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length) :
    st Q L E i < st Q L E i' := by
  have hE := hElen hK hperm hsort
  have hA := DrvD.arcs_length (M := interiorModel Q) (Q := Q) (E := E) hK
  rw [hA] at hi'
  unfold st
  rw [DrvD.key_s hK (by omega), DrvD.key_s hK hi']
  have h1 := DrvD.gs_succ (M := interiorModel Q) (Q := Q) (L := L) hE (j := i) (by omega)
  have h2 := DrvD.gs_lt_gs (M := interiorModel Q) (Q := Q) (L := L) (E := E) hii hi'
  have h3 := DrvD.kE_mono hsort (show DrvD.gs (interiorModel Q) Q L E i + 1 ≤
    DrvD.gs (interiorModel Q) Q L E i' by omega) (DrvD.gs_lt_len hi')
  linarith [h1.2]

theorem st_le {i i' : ℕ} (hii : i ≤ i')
    (hi' : i' < (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length) :
    st Q L E i ≤ st Q L E i' := by
  rcases lt_or_eq_of_le hii with h | h
  · exact (st_lt hK hperm hsort h hi').le
  · rw [h]

/-- **An arc other than the last ends at the next start.** -/
theorem key_e_eq {j : ℕ} (hj : j + 1 < (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length) :
    (interiorModel Q).key Q ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).e = st Q L E (j + 1) := by
  have hE := hElen hK hperm hsort
  have hA := DrvD.arcs_length (M := interiorModel Q) (Q := Q) (E := E) hK
  rw [hA] at hj
  unfold st
  rw [DrvD.key_e hK hE hj, DrvD.key_s hK hj]
  have h1 := DrvD.gs_succ (M := interiorModel Q) (Q := Q) (L := L) hE (j := j) hj
  have h2 := DrvD.gs_lt_gs (M := interiorModel Q) (Q := Q) (L := L) (E := E)
    (show j < j + 1 by omega) hj
  refine kE_const hsort (by omega) (DrvD.gs_lt_len hj) fun m hm1 hm2 hm => ?_
  obtain ⟨k, hk, rfl⟩ := gs_of_mem hm
  have := gs_strict (L := L) (E := E) (by omega) hk (k := j) (by omega)
  have := gs_strict (L := L) (E := E) hk hj (k := k) hm2
  omega

/-- **The last arc ends at the first start.** -/
theorem key_e_last_eq :
    (interiorModel Q).key Q ((BuildNF.buildNF (interiorModel Q) Q L E).arc
      ((BuildNF.buildNF (interiorModel Q) Q L E).arcs.length - 1)).e = st Q L E 0 := by
  have hE := hElen hK hperm hsort
  have hA := DrvD.arcs_length (M := interiorModel Q) (Q := Q) (E := E) hK
  obtain ⟨hA0, -⟩ := DrvD.gs_last (M := interiorModel Q) (Q := Q) (L := L) hE
  rw [hA, DrvD.key_e_last hK hE]
  unfold st
  rw [DrvD.key_s hK hA0]
  refine kE_const hsort (Nat.zero_le _) (DrvD.gs_lt_len hA0) fun m _ hm2 hm => ?_
  obtain ⟨k, hk, rfl⟩ := gs_of_mem hm
  have := gs_strict (L := L) (E := E) hk hA0 (k := k) hm2
  omega

/-- **Every bucket meets at most two arcs**: a position on the closure of arc `j` has a bucket
`b` with `j = arcA A b ∨ j = arcB A b`. -/
theorem arc_of_bkt {j : ℕ} {x : WPos}
    (hj : j < (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length)
    (hx : OnArcKey Q (BuildNF.buildNF (interiorModel Q) Q L E) j x) :
    j = arcA (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length
        (keyBkt Q (BuildNF.buildNF (interiorModel Q) Q L E) x) ∨
      j = arcB (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length
        (keyBkt Q (BuildNF.buildNF (interiorModel Q) Q L E) x) := by
  have hlt : ∀ i i', i < i' → i' < (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length →
      st Q L E i < st Q L E i' := fun i i' h1 h2 => st_lt hK hperm hsort h1 h2
  have hle : ∀ i i', i ≤ i' → i' < (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length →
      st Q L E i ≤ st Q L E i' := fun i i' h1 h2 => st_le hK hperm hsort h1 h2
  have hks : (interiorModel Q).key Q ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).s =
      st Q L E j := rfl
  -- the end of arc `j`
  have hke : (j + 1 < (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length →
      (interiorModel Q).key Q ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).e =
        st Q L E (j + 1)) ∧
      (j + 1 = (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length →
      (interiorModel Q).key Q ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).e =
        st Q L E 0) := by
    refine ⟨fun h => key_e_eq hK hperm hsort h, fun h => ?_⟩
    have : j = (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length - 1 := by omega
    rw [this]; exact key_e_last_eq hK hperm hsort
  unfold OnArcKey at hx
  rw [hks] at hx
  generalize hA : (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length = A at hlt hle hke hj ⊢
  have hkb := fun c (hc : c ≤ A) h => keyBkt_eq (Q := Q) (L := L) (E := E) (x := x) (c := c) hA hc h
  rcases hx with hx | hx | hx
  · -- the start of arc `j`
    have := (hkb j hj.le (fun i hi => ⟨fun h => by
        by_contra h'; have := hle j i (by omega) hi; linarith,
      fun h => by rw [hx]; exact hlt i j h hj⟩)).1 ⟨j, hj, hx.symm⟩
    left; rw [this]; unfold arcA; rw [ite_eq_right (by omega)]; omega
  · rcases Nat.lt_or_ge (j + 1) A with hj1 | hj1
    · rw [hke.1 hj1] at hx
      have := (hkb (j + 1) hj1.le (fun i hi => ⟨fun h => by
          by_contra h'; have := hle (j + 1) i (by omega) hi; linarith,
        fun h => by rw [hx]; exact hlt i (j + 1) h hj1⟩)).1 ⟨j + 1, hj1, hx.symm⟩
      right; rw [this]; unfold arcB; rw [ite_eq_right (by omega)]; omega
    · rw [hke.2 (by omega)] at hx
      have := (hkb 0 (Nat.zero_le _) (fun i hi => ⟨fun h => by
          have := hle 0 i (by omega) hi; linarith, fun h => by omega⟩)).1 ⟨0, by omega, hx.symm⟩
      right; rw [this]; unfold arcB; rw [ite_eq_left (by omega)]; omega
  · rcases Nat.lt_or_ge (j + 1) A with hj1 | hj1
    · rw [hke.1 hj1] at hx
      unfold sideInArc at hx
      rw [ite_eq_left (hlt j (j + 1) (by omega) hj1)] at hx
      have := (hkb (j + 1) hj1.le (fun i hi => ⟨fun h => by
          by_contra h'; have := hle (j + 1) i (by omega) hi; linarith,
        fun h => by have := hle i j (by omega) hj; linarith⟩)).2 (by
          rintro ⟨i, hi, hie⟩
          rcases Nat.lt_or_ge j i with hji | hji
          · have := hle (j + 1) i (by omega) hi; linarith
          · have := hle i j hji hj; linarith)
      left; rw [this]; unfold arcA; rw [ite_eq_right (by omega)]; omega
    · rw [hke.2 (by omega)] at hx
      unfold sideInArc at hx
      rw [ite_eq_right (by have := hle 0 j (by omega) hj; linarith)] at hx
      rcases hx with hx | hx
      · have := (hkb A le_rfl (fun i hi => ⟨fun _ => hi,
          fun _ => by have := hle i j (by omega) hj; linarith⟩)).2 (by
            rintro ⟨i, hi, hie⟩
            have := hle i j (by omega) hj; linarith)
        left; rw [this]; unfold arcA; rw [ite_eq_right (by omega)]; omega
      · have := (hkb 0 (Nat.zero_le _) (fun i hi => ⟨fun h => by
            have := hle 0 i (by omega) hi; linarith, fun h => by omega⟩)).2 (by
            rintro ⟨i, hi, hie⟩
            have := hle 0 i (by omega) hi; linarith)
        left; rw [this]; unfold arcA; rw [ite_eq_left rfl]; omega

/-- **At most `4 M` ends per bucket.** -/
theorem bcnt_le_four {reg : ℕ → Set Point}
    (hregs : Restore.NFRegs (interiorModel Q) Q (BuildNF.buildNF (interiorModel Q) Q L E) reg)
    {Lx : ℕ → List (ℕ × ℕ × ℕ)} {M : ℕ}
    (hM : ∀ r, r < (BuildNF.buildNF (interiorModel Q) Q L E).nRegions → (Lx r).length ≤ M)
    (hon : ∀ r, r < (BuildNF.buildNF (interiorModel Q) Q L E).nRegions →
      ∀ q, q < 2 * (Lx r).length →
        ∃ j ∈ ((BuildNF.buildNF (interiorModel Q) Q L E).region r).arcs,
          OnArcKey Q (BuildNF.buildNF (interiorModel Q) Q L E) j (DrvR.endPos (Lx r) q))
    (b : ℕ) :
    DrvR.bcnt (fun q => keyBkt Q (BuildNF.buildNF (interiorModel Q) Q L E)
        (DrvR.endPos ((List.range (BuildNF.buildNF (interiorModel Q) Q L E).nRegions).flatMap
          Lx) q))
      (2 * ((List.range (BuildNF.buildNF (interiorModel Q) Q L E).nRegions).flatMap Lx).length)
      b ≤ 4 * M := by
  refine cntB_flat_le (Q := Q) (N := BuildNF.buildNF (interiorModel Q) Q L E)
    ((BuildNF.buildNF (interiorModel Q) Q L E).arc
      (arcA (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length b)).reg
    ((BuildNF.buildNF (interiorModel Q) Q L E).arc
      (arcB (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length b)).reg hM ?_
  intro r hr q hq hqb
  obtain ⟨j, hj, hjx⟩ := hon r hr q hq
  obtain ⟨hjA, hjr⟩ := (hregs.2.2.1.2.2.2 r hr j).1 hj
  rcases arc_of_bkt hK hperm hsort hjA hjx with h | h
  · left; rw [← hjr, h, hqb]
  · right; rw [← hjr, h, hqb]

end arcs


end

end DrvLM

end Chazelle.Core
