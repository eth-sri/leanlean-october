module

public import Chazelle.Golf

public import Chazelle.Core.SweepIoS0CandInitMath

/-!
# The sweep RAM (WP-D), answers: the slot table of the side-0 candidates (mathematics, 2)

`OD`: the outputs of stages 2 and 3 (stops, log, table) in a memory `m` at fixed bases, local
below a bound (`OD.congr`).  The steps of the initialisation:

* `OD.logW`, `OD.stopW`, `OD.tabW`, `OD.down`: the preconditions of the search;
* `stop_step`: a stop record, its origin position (`stopPos`) and the answer of the search give a
  good slot at a log record with its key;
* `valid_test`: the regular endpoint queries by an index test on the normalised end position;
* `tab_step`: the same for a regular table entry with flag `1`;
* `SInv`: the invariant of the slot table (`SInv.congr`, `SInv.store`).
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Set
open Chazelle.Chain (sidePt SideAttach)
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep SweepEv

@[expose] public section

/-- **The outputs of stages 2 and 3** in the memory `m`: `S` stop records at `AS`, `E` log
records at `AL`, the endpoint table at `AT`. -/
structure OD (P : Polygon) (J : Merge.Junction) (N : NF) (m : ℕ → ℕ) (AS S AL E AT : ℕ)
    (rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) : Prop where
  rl : rs.length = S
  rr : StopRecsAt m AS rs
  rok : StopsOK J (N.F (chainModel J.right) (Qof P)) (stopsOf J (Qof P) N rs)
  rw : ∀ r ∈ rs, PosW P J r.1 r.2.1 ∧ r.2.2.1 ≤ 2 ∧ r.2.2.2.2 ≤ 1 ∧
      (r.2.2.1 = 1 → r.2.2.2.1 < N.nChords)
  ll : ls.length = E
  lr : LogRecsAt m AL ls
  lok : LogOK J (N.F (chainModel J.right) (Qof P)) (logOf J (Qof P) N ls)
  lw : ∀ r ∈ ls, PosW P J r.1 r.2.1
  tok : TabOK J (Qof P) N (tabOf J (Qof P) m AT)
  tw : ∀ j, j < 2 * N.nChords → m (AT + 3 * j) ≤ 1 ∧
      (m (AT + 3 * j) = 1 → PosW P J (m (AT + 3 * j + 1)) (m (AT + 3 * j + 2)))

/-- `OD` from `SweepEv.Out`. -/
theorem OD.of_out {P : Polygon} {J : Merge.Junction} {N : NF} {c : Config}
    (h : SweepEv.Out P J N c) : ∃ rs ls, OD P J N c.nmem (rd c bSweep 200) (rd c bSweep 201)
      (rd c bSweep 300) (rd c bSweep 301) (rd c bSweep 302) rs ls := by
  obtain ⟨rs, ls, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨rs, ls, h1, h2, h3, h4, h5, h6, h7, fun r hr => (h8 r hr).1, h9, h10⟩

theorem stopRecs_congr {m m' : ℕ → ℕ} {A : ℕ} {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    (h : StopRecsAt m A rs) (hm : ∀ a, a < A + 5 * rs.length → m' a = m a) :
    StopRecsAt m' A rs := by
  intro i hi
  obtain ⟨a1, a2, a3, a4, a5⟩ := h i hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hm _ (⋄)]; exact a1
  · rw [hm _ (⋄)]; exact a2
  · rw [hm _ (⋄)]; exact a3
  · rw [hm _ (⋄)]; exact a4
  · rw [hm _ (⋄)]; exact a5

theorem logRecs_congr {m m' : ℕ → ℕ} {A : ℕ} {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}
    (h : LogRecsAt m A ls) (hm : ∀ a, a < A + 7 * ls.length → m' a = m a) :
    LogRecsAt m' A ls := by
  intro i hi
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h i hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm _ (⋄)]; exact a1
  · rw [hm _ (⋄)]; exact a2
  · rw [hm _ (⋄)]; exact a3
  · rw [hm _ (⋄)]; exact a4
  · rw [hm _ (⋄)]; exact a5
  · rw [hm _ (⋄)]; exact a6
  · rw [hm _ (⋄)]; exact a7

/-- **`OD` is local.** -/
theorem OD.congr {P : Polygon} {J : Merge.Junction} {N : NF} {m m' : ℕ → ℕ}
    {AS S AL E AT : ℕ} {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)} {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}
    (h : OD P J N m AS S AL E AT rs ls) {A₀ : ℕ} (hm : ∀ a, a < A₀ → m' a = m a)
    (hS : AS + 5 * S ≤ A₀) (hE : AL + 7 * E ≤ A₀) (hT : AT + 3 * (2 * N.nChords) ≤ A₀) :
    OD P J N m' AS S AL E AT rs ls := by
  have ht : ∀ j, j < 2 * N.nChords → tabOf J (Qof P) m' AT j = tabOf J (Qof P) m AT j := by
    intro j hj
    unfold tabOf
    rw [hm _ (⋄), hm (AT + 3 * j + 1) (by omega), hm (AT + 3 * j + 2) (by omega)]
  refine ⟨h.rl, stopRecs_congr h.rr (fun a ha => hm a (by rw [h.rl] at ha; omega)), h.rok, h.rw,
    h.ll, logRecs_congr h.lr (fun a ha => hm a (by rw [h.ll] at ha; omega)), h.lok, h.lw,
    fun j hj => ?_, fun j hj => ?_⟩
  · rw [ht j hj]; exact h.tok j hj
  · rw [hm _ (⋄), hm (AT + 3 * j + 1) (by omega), hm (AT + 3 * j + 2) (by omega)]
    exact h.tw j hj

section steps

variable {P : Polygon} {J : Merge.Junction} {N : NF} {m : ℕ → ℕ} {AS S AL E AT : ℕ}
  {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)} {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}

theorem OD.logW (h : OD P J N m AS S AL E AT rs ls) {j : ℕ} (hj : j < E) :
    PosW P J (m (AL + 7 * j)) (m (AL + 7 * j + 1)) := by
  have hj' : j < ls.length := by rw [h.ll]; exact hj
  obtain ⟨a1, a2, -⟩ := h.lr j hj'
  Ξ a1, a2, List.getD_eq_getElem _ _ hj'
  exact h.lw _ (List.getElem_mem _)

theorem OD.stopR (h : OD P J N m AS S AL E AT rs ls) {x : ℕ} (hx : x < S) :
    PosW P J (m (AS + 5 * x)) (m (AS + 5 * x + 1)) ∧ m (AS + 5 * x + 2) ≤ 2 ∧
      m (AS + 5 * x + 4) ≤ 1 ∧ (m (AS + 5 * x + 2) = 1 → m (AS + 5 * x + 3) < N.nChords) := by
  have hx' : x < rs.length := by rw [h.rl]; exact hx
  obtain ⟨a1, a2, a3, a4, a5⟩ := h.rr x hx'
  Ξ a1, a2, a3, a4, a5, List.getD_eq_getElem _ _ hx'
  exact h.rw _ (List.getElem_mem _)

theorem OD.down (h : OD P J N m AS S AL E AT rs ls) {G : ℕ} (hG : G = gW J) (x : WPos) :
    ∀ a b, a ≤ b → b < E → lsPr P J m AL G x b → lsPr P J m AL G x a := by
  rw [← h.ll]; exact (search_exact hG h.lr h.lok x).1

/-- **A stop record**: the answer `t` of the search for its key is a log record with that key,
and its origin position is a good slot content for it. -/
theorem stop_step (h : OD P J N m AS S AL E AT rs ls) (hP : J.P.Simple)
    (hN : IsNF (chainModel J.right) (Qof P) N) {G : ℕ} (hG : G = gW J) {x : ℕ} (hx : x < S)
    {t : ℕ} (h1 : ∀ j, j < t → lsPr P J m AL G ⟨m (AS + 5 * x), m (AS + 5 * x + 1)⟩ j)
    (h2 : ∀ j, t ≤ j → j < E → ¬ lsPr P J m AL G ⟨m (AS + 5 * x), m (AS + 5 * x + 1)⟩ j) :
    t < E ∧ m (AL + 7 * t) = m (AS + 5 * x) ∧
      (chainModel J.whole).param (Qof P) (logPos m AL t) =
        (chainModel J.whole).param (Qof P) ⟨m (AS + 5 * x), m (AS + 5 * x + 1)⟩ ∧
      SlotVal P J (stopPos P J N (m (AS + 5 * x + 2)) (m (AS + 5 * x + 3)) (m (AS + 5 * x + 4)))
        (sOf (m (AS + 5 * x + 4))) (logPt P J m AL t) := by
  have hx' : x < rs.length := by rw [h.rl]; exact hx
  set r := rs[x] with hr
  have hmem : r ∈ rs := List.getElem_mem _
  obtain ⟨a1, a2, a3, a4, a5⟩ := h.rr x hx'
  rw [List.getD_eq_getElem _ _ hx'] at a1 a2 a3 a4 a5
  obtain ⟨-, hkind, -, hk⟩ := h.rw r hmem
  obtain ⟨hc, hF, hA, hL⟩ := stop_cand J hN h.rok hmem hkind hk
  obtain ⟨i, hi, e1, e2⟩ := attach_idx (x := ⟨r.1, r.2.1⟩) h.lr h.lok hF hA hL
  rw [← a1, ← a2] at e1 e2
  have hti : t = i := (search_exact hG h.lr h.lok _).2 i hi e1 e2 t h1 (by rw [h.ll]; exact h2)
  subst hti
  rw [h.ll] at hi
  refine ⟨hi, e1, e2, ?_⟩
  Ξ a3, a4, a5
  obtain ⟨s1, s2, s3⟩ := stopPos_facts (b := r.2.2.2.2) hP hN hkind hk
  refine ⟨s1, s2, ?_⟩
  Ξ s3, ini_dS_sOf
  have hpt : logPt P J m AL t = sidePt (chainModel J.whole).W r.1
      ((chainModel J.whole).param (Qof P) ⟨r.1, r.2.1⟩) := by
    unfold logPt
    Ξ e2, ← a1, ← a2
    show sidePt _ (m (AL + 7 * t)) _ = _
    Ξ e1
  Ξ hpt
  exact hc

/-- **The regular endpoint queries** by an index test on the normalised end position. -/
theorem valid_test (hP : J.P.Simple) (hN : IsNF (chainModel J.right) (Qof P) N) {k s : ℕ}
    (hk : k < N.nChords) (hs : s ≤ 1) :
    ValidO J (Qof P) N (2 * k + s) ↔
      (6 ≤ (endPos N k s).edge ∧ (endPos N k s).edge ≤ 2 * J.right.m + 5 ∧
        (nhgt (chainModel J.right) (Qof P) (endPos N k s) ≠ 0 ∨
          ((endPos N k s).edge ≠ 6 ∧ (endPos N k s).edge ≠ cstR J 1 ∧
            (endPos N k s).edge ≠ 6 + midT J.right))) := by
  obtain ⟨f1, f2, f3, f4⟩ := endPos_facts hN hk hs
  have hv := valid_iff J hP (Qof P)
    (x := ⟨(endPos N k s).edge, nhgt (chainModel J.right) (Qof P) (endPos N k s)⟩) f1 f2.1 f2.2.1 f4
  unfold ValidO
  Ξ ← f3
  exact hv

/-- **A regular table entry with flag `1`**: the answer `t` of the search for its position is a
log record with that key, and the normalised end position is a good slot content for it. -/
theorem tab_step (h : OD P J N m AS S AL E AT rs ls) (hN : IsNF (chainModel J.right) (Qof P) N)
    {G : ℕ} (hG : G = gW J) {k s : ℕ} (hk : k < N.nChords) (hs : s ≤ 1)
    (hv : ValidO J (Qof P) N (2 * k + s)) (hf : m (AT + 3 * (2 * k + s)) = 1) {t : ℕ}
    (h1 : ∀ j, j < t → lsPr P J m AL G
      ⟨m (AT + 3 * (2 * k + s) + 1), m (AT + 3 * (2 * k + s) + 2)⟩ j)
    (h2 : ∀ j, t ≤ j → j < E → ¬ lsPr P J m AL G
      ⟨m (AT + 3 * (2 * k + s) + 1), m (AT + 3 * (2 * k + s) + 2)⟩ j) :
    t < E ∧ m (AL + 7 * t) = m (AT + 3 * (2 * k + s) + 1) ∧
      (chainModel J.whole).param (Qof P) (logPos m AL t) =
        (chainModel J.whole).param (Qof P)
          ⟨m (AT + 3 * (2 * k + s) + 1), m (AT + 3 * (2 * k + s) + 2)⟩ ∧
      SlotVal P J ⟨(endPos N k s).edge, nhgt (chainModel J.right) (Qof P) (endPos N k s)⟩ s
        (logPt P J m AL t) := by
  set j := 2 * k + s with hjdef
  have hj : j < 2 * N.nChords := ⋄
  obtain ⟨hon, hsh, htop⟩ := hv
  have hTj : tabOf J (Qof P) m AT j =
      some (m (AT + 3 * j + 1), (chainModel J.whole).param (Qof P)
        ⟨m (AT + 3 * j + 1), m (AT + 3 * j + 2)⟩) := by
    unfold tabOf; rw [ite_eq_left hf]
  obtain ⟨hc, hF, hA, hL⟩ := tab_cand J h.tok hj hon hsh htop hTj
  obtain ⟨i, hi, e1, e2⟩ := attach_idx (x := ⟨m (AT + 3 * j + 1), m (AT + 3 * j + 2)⟩)
    h.lr h.lok hF hA hL
  have hti : t = i := (search_exact hG h.lr h.lok _).2 i hi e1 e2 t h1 (by rw [h.ll]; exact h2)
  subst hti
  rw [h.ll] at hi
  refine ⟨hi, e1, e2, ?_⟩
  obtain ⟨f1, f2, f3, -⟩ := endPos_facts hN hk hs
  refine ⟨f1, f2, ?_⟩
  Ξ f3
  have hd : dS s = endDir j := by
    unfold dS endDir
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hs with rfl | rfl
    · Θ hjdef
    · have : (2 * k + 1) % 2 = 1 := ⋄
      Θ hjdef, this
  Ξ hd
  have hpt : logPt P J m AL t = sidePt (chainModel J.whole).W (m (AT + 3 * j + 1))
      ((chainModel J.whole).param (Qof P) ⟨m (AT + 3 * j + 1), m (AT + 3 * j + 2)⟩) := by
    unfold logPt
    Ξ e2
    show sidePt _ (m (AL + 7 * t)) _ = _
    Ξ e1
  Ξ hpt
  exact hc

end steps

/-! ## The invariant of the slot table -/

/-- **The slot table after `x` stop records and the table entries of the first `kk` chords.** -/
def SInv (P : Polygon) (J : Merge.Junction) (N : NF) (AS AL E AT B : ℕ) (m : ℕ → ℕ)
    (x kk : ℕ) : Prop :=
  (∀ i, i < E → ∀ s, s ≤ 1 → SlotOK P J m B AL i s) ∧
  (∀ y, y < x → ∃ i, i < E ∧ m (AL + 7 * i) = m (AS + 5 * y) ∧
    (chainModel J.whole).param (Qof P) (logPos m AL i) =
      (chainModel J.whole).param (Qof P) ⟨m (AS + 5 * y), m (AS + 5 * y + 1)⟩ ∧
    m (slotA B i (sOf (m (AS + 5 * y + 4)))) = 1) ∧
  (∀ j, j < kk → ValidO J (Qof P) N j → m (AT + 3 * j) = 1 →
    ∃ i, i < E ∧ m (AL + 7 * i) = m (AT + 3 * j + 1) ∧
    (chainModel J.whole).param (Qof P) (logPos m AL i) =
      (chainModel J.whole).param (Qof P) ⟨m (AT + 3 * j + 1), m (AT + 3 * j + 2)⟩ ∧
    m (slotA B i (j % 2)) = 1)

/-- The invariant at the start: a zeroed slot table. -/
theorem SInv.zero {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ} {m : ℕ → ℕ}
    (hz : ∀ a, B ≤ a → a < B + 6 * E → m a = 0) : SInv P J N AS AL E AT B m 0 0 := by
  refine ⟨fun i hi s hs => ?_, fun y hy => absurd hy (Nat.not_lt_zero _),
    fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  have h0 : m (slotA B i s) = 0 := hz _ (by unfold slotA; omega) (by unfold slotA; omega)
  unfold SlotOK
  Ξ h0
  exact ⟨Nat.zero_le _, fun h => absurd h (⊛)⟩

/-- **The invariant is local** below the end of the slot table. -/
theorem SInv.congr {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ}
    {m m' : ℕ → ℕ} {x kk : ℕ} (h : SInv P J N AS AL E AT B m x kk)
    (hm : ∀ a, a < B + 6 * E → m' a = m a) (hS : AS + 5 * x ≤ B) (hE : AL + 7 * E ≤ B)
    (hT : AT + 3 * kk ≤ B) : SInv P J N AS AL E AT B m' x kk := by
  obtain ⟨h1, h2, h3⟩ := h
  have hL : ∀ i, i < E → logPos m' AL i = logPos m AL i := fun i hi => by
    unfold logPos; rw [hm _ (⋄), hm (AL + 7 * i + 1) (by omega)]
  have hL0 : ∀ i, i < E → m' (AL + 7 * i) = m (AL + 7 * i) := fun i hi => hm _ (⋄)
  have hB : ∀ i, i < E → ∀ s, s ≤ 1 → ∀ d, d < 3 → m' (slotA B i s + d) = m (slotA B i s + d) :=
    fun i hi s hs d hd => hm _ (by unfold slotA; omega)
  have hB0 : ∀ i, i < E → ∀ s, s ≤ 1 → m' (slotA B i s) = m (slotA B i s) :=
    fun i hi s hs => by simpa using hB i hi s hs 0 (⊛)
  refine ⟨fun i hi s hs => ?_, fun y hy => ?_, fun j hj hv hf => ?_⟩
  · unfold SlotOK logPt
    rw [hB0 i hi s hs, hB i hi s hs 1 (⊛), hB i hi s hs 2 (by norm_num), hL i hi]
    exact h1 i hi s hs
  · obtain ⟨i, hi, e1, e2, e3⟩ := h2 y hy
    refine ⟨i, hi, ?_, ?_, ?_⟩
    · rw [hL0 i hi, hm (AS + 5 * y) (⋄), e1]
    · rw [hL i hi, hm (AS + 5 * y) (⋄), hm (AS + 5 * y + 1) (by omega), e2]
    · rw [hm (AS + 5 * y + 4) (⋄), hB0 i hi _ (ini_sOf_le _), e3]
  · have hf' : m (AT + 3 * j) = 1 := by rw [← hm _ (⋄)]; exact hf
    obtain ⟨i, hi, e1, e2, e3⟩ := h3 j hj hv hf'
    refine ⟨i, hi, ?_, ?_, ?_⟩
    · rw [hL0 i hi, hm (AT + 3 * j + 1) (⋄), e1]
    · rw [hL i hi, hm (AT + 3 * j + 1) (⋄), hm (AT + 3 * j + 2) (by omega), e2]
    · rw [hB0 i hi _ (⋄), e3]

/-- **Writing a good slot keeps the invariant** (the records lie below the slot table). -/
theorem SInv.store {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ}
    {m : ℕ → ℕ} {x kk t s e h : ℕ} (hI : SInv P J N AS AL E AT B m x kk)
    (hS : AS + 5 * x ≤ B) (hE : AL + 7 * E ≤ B) (hT : AT + 3 * kk ≤ B) (ht : t < E)
    (hs : s ≤ 1) (hv : SlotVal P J ⟨e, h⟩ s (logPt P J m AL t)) :
    SInv P J N AS AL E AT B (slotW m B t s e h) x kk ∧ slotW m B t s e h (slotA B t s) = 1 := by
  obtain ⟨h1, h2, h3⟩ := hI
  have hlow : ∀ a, a < B → slotW m B t s e h a = m a :=
    fun a ha => slotW_other (Or.inl (by unfold slotA; omega))
  have hfl : ∀ i, i < E → ∀ s', s' ≤ 1 → m (slotA B i s') = 1 →
      slotW m B t s e h (slotA B i s') = 1 := by
    intro i hi s' hs' hf
    by_cases hit : i = t ∧ s' = s
    · obtain ⟨rfl, rfl⟩ := hit; exact slotW_flag
    · rw [slotW_other (by simpa using slot_sep (d := 0) hs' hs (⊛) hit)]; exact hf
  have hL : ∀ i, i < E → logPos (slotW m B t s e h) AL i = logPos m AL i := fun i hi => by
    unfold logPos; rw [hlow _ (⋄), hlow (AL + 7 * i + 1) (by omega)]
  have hL0 : ∀ i, i < E → slotW m B t s e h (AL + 7 * i) = m (AL + 7 * i) :=
    fun i hi => hlow _ (⋄)
  refine ⟨⟨slotOK_store hE ht hs h1 hv, fun y hy => ?_, fun j hj hv' hf => ?_⟩, slotW_flag⟩
  · obtain ⟨i, hi, e1, e2, e3⟩ := h2 y hy
    refine ⟨i, hi, ?_, ?_, ?_⟩
    · rw [hL0 i hi, hlow (AS + 5 * y) (⋄), e1]
    · rw [hL i hi, hlow (AS + 5 * y) (⋄), hlow (AS + 5 * y + 1) (by omega), e2]
    · rw [hlow (AS + 5 * y + 4) (⋄)]; exact hfl i hi _ (ini_sOf_le _) e3
  · have hf' : m (AT + 3 * j) = 1 := by rw [← hlow _ (⋄)]; exact hf
    obtain ⟨i, hi, e1, e2, e3⟩ := h3 j hj hv' hf'
    refine ⟨i, hi, ?_, ?_, ?_⟩
    · rw [hL0 i hi, hlow (AT + 3 * j + 1) (⋄), e1]
    · rw [hL i hi, hlow (AT + 3 * j + 1) (⋄), hlow (AT + 3 * j + 2) (by omega), e2]
    · exact hfl i hi _ (⋄) e3

/-- One more stop record. -/
theorem SInv.extS {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ}
    {m : ℕ → ℕ} {x kk : ℕ} (h : SInv P J N AS AL E AT B m x kk)
    (hx : ∃ i, i < E ∧ m (AL + 7 * i) = m (AS + 5 * x) ∧
      (chainModel J.whole).param (Qof P) (logPos m AL i) =
        (chainModel J.whole).param (Qof P) ⟨m (AS + 5 * x), m (AS + 5 * x + 1)⟩ ∧
      m (slotA B i (sOf (m (AS + 5 * x + 4)))) = 1) :
    SInv P J N AS AL E AT B m (x + 1) kk := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun y hy => ?_, h3⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy | rfl
  · exact h2 y hy
  · exact hx

/-- One more table entry. -/
theorem SInv.extT {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ}
    {m : ℕ → ℕ} {x kk : ℕ} (h : SInv P J N AS AL E AT B m x kk)
    (hx : ValidO J (Qof P) N kk → m (AT + 3 * kk) = 1 →
      ∃ i, i < E ∧ m (AL + 7 * i) = m (AT + 3 * kk + 1) ∧
      (chainModel J.whole).param (Qof P) (logPos m AL i) =
        (chainModel J.whole).param (Qof P) ⟨m (AT + 3 * kk + 1), m (AT + 3 * kk + 2)⟩ ∧
      m (slotA B i (kk % 2)) = 1) :
    SInv P J N AS AL E AT B m x (kk + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · exact h3 j hj
  · exact hx

theorem logPt_congr {P : Polygon} {J : Merge.Junction} {m m' : ℕ → ℕ} {AL t B : ℕ}
    (hm : ∀ a, a < B → m' a = m a) (ht : AL + 7 * t + 1 < B) :
    logPt P J m' AL t = logPt P J m AL t := by
  unfold logPt logPos; rw [hm _ (⋄), hm (AL + 7 * t + 1) ht]

/-- **The step of a stop record**: a good slot written at the answer of the search. -/
theorem SInv.stopStep {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ}
    {m m₂ : ℕ → ℕ} {x kk t eV hV : ℕ} (hI : SInv P J N AS AL E AT B m x kk)
    (hm : ∀ a, a < B → m₂ a = m a) (hS : AS + 5 * (x + 1) ≤ B) (hE : AL + 7 * E ≤ B)
    (hT : AT + 3 * kk ≤ B) (ht : t < E) (e1 : m₂ (AL + 7 * t) = m₂ (AS + 5 * x))
    (e2 : (chainModel J.whole).param (Qof P) (logPos m₂ AL t) =
      (chainModel J.whole).param (Qof P) ⟨m₂ (AS + 5 * x), m₂ (AS + 5 * x + 1)⟩)
    (hv : SlotVal P J ⟨eV, hV⟩ (sOf (m₂ (AS + 5 * x + 4))) (logPt P J m₂ AL t)) :
    SInv P J N AS AL E AT B (slotW m B t (sOf (m (AS + 5 * x + 4))) eV hV) (x + 1) kk := by
  rw [hm _ (⋄)] at hv
  rw [logPt_congr hm (⋄)] at hv
  obtain ⟨h1, h2⟩ := hI.store (⋄) hE hT ht (ini_sOf_le _) hv
  refine h1.extS ⟨t, ht, ?_, ?_, ?_⟩
  · rw [slotW_other (Or.inl (by unfold slotA; omega)),
      slotW_other (Or.inl (by unfold slotA; omega)), ← hm _ (⋄), ← hm (AS + 5 * x) (by omega)]
    exact e1
  · have hp : logPos (slotW m B t (sOf (m (AS + 5 * x + 4))) eV hV) AL t = logPos m₂ AL t := by
      unfold logPos
      rw [slotW_other (Or.inl (by unfold slotA; omega)),
        slotW_other (Or.inl (by unfold slotA; omega)), hm _ (⋄), hm (AL + 7 * t + 1) (by omega)]
    rw [hp, e2, slotW_other (Or.inl (by unfold slotA; omega)),
      slotW_other (Or.inl (by unfold slotA; omega)), hm _ (⋄), hm (AS + 5 * x + 1) (by omega)]
  · have h4 : slotW m B t (sOf (m (AS + 5 * x + 4))) eV hV (AS + 5 * x + 4) = m (AS + 5 * x + 4) :=
      slotW_other (Or.inl (by unfold slotA; omega))
    rw [h4]; exact h2

/-- **The step of a regular table entry with flag `1`.** -/
theorem SInv.tabStep {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ}
    {m m₂ : ℕ → ℕ} {x kk t eV hV : ℕ} (hI : SInv P J N AS AL E AT B m x kk)
    (hm : ∀ a, a < B → m₂ a = m a) (hS : AS + 5 * x ≤ B) (hE : AL + 7 * E ≤ B)
    (hT : AT + 3 * (kk + 1) ≤ B) (ht : t < E) (e1 : m₂ (AL + 7 * t) = m₂ (AT + 3 * kk + 1))
    (e2 : (chainModel J.whole).param (Qof P) (logPos m₂ AL t) =
      (chainModel J.whole).param (Qof P) ⟨m₂ (AT + 3 * kk + 1), m₂ (AT + 3 * kk + 2)⟩)
    (hv : SlotVal P J ⟨eV, hV⟩ (kk % 2) (logPt P J m₂ AL t)) :
    SInv P J N AS AL E AT B (slotW m B t (kk % 2) eV hV) x (kk + 1) := by
  rw [logPt_congr hm (⋄)] at hv
  obtain ⟨h1, h2⟩ := hI.store hS hE (⋄) ht (by omega) hv
  refine h1.extT (fun _ _ => ⟨t, ht, ?_, ?_, h2⟩)
  · rw [slotW_other (Or.inl (by unfold slotA; omega)),
      slotW_other (Or.inl (by unfold slotA; omega)), ← hm _ (⋄),
      ← hm (AT + 3 * kk + 1) (⋄)]
    exact e1
  · have hp : logPos (slotW m B t (kk % 2) eV hV) AL t = logPos m₂ AL t := by
      unfold logPos
      rw [slotW_other (Or.inl (by unfold slotA; omega)),
        slotW_other (Or.inl (by unfold slotA; omega)), hm _ (⋄), hm (AL + 7 * t + 1) (by omega)]
    rw [hp, e2, slotW_other (Or.inl (by unfold slotA; omega)),
      slotW_other (Or.inl (by unfold slotA; omega)), hm (AT + 3 * kk + 1) (⋄),
      hm (AT + 3 * kk + 2) (⋄)]

/-- **A table entry without a slot**: not regular, or flag `0`. -/
theorem SInv.tabSkip {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ}
    {m : ℕ → ℕ} {x kk : ℕ} (hI : SInv P J N AS AL E AT B m x kk)
    (h : ¬ (ValidO J (Qof P) N kk ∧ m (AT + 3 * kk) = 1)) :
    SInv P J N AS AL E AT B m x (kk + 1) :=
  hI.extT (fun hv hf => absurd ⟨hv, hf⟩ h)

end

end S0C

end SweepIo

end Chazelle.Core
