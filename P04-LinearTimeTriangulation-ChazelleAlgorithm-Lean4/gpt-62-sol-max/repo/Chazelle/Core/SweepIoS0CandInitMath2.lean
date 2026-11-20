module

meta import Chazelle.Programs.RegisterGuard

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
  rok : StopsOK J (N.F J.rightModel (Qof P)) (stopsOf J (Qof P) N rs)
  rw : ∀ r ∈ rs, PosW P J r.1 r.2.1 ∧ r.2.2.1 ≤ 2 ∧ r.2.2.2.2 ≤ 1 ∧
      (r.2.2.1 = 1 → r.2.2.2.1 < N.nChords)
  ll : ls.length = E
  lr : LogRecsAt m AL ls
  lok : LogOK J (N.F J.rightModel (Qof P)) (logOf J (Qof P) N ls)
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

/-- **`OD` is local.** -/
theorem OD.congr {P : Polygon} {J : Merge.Junction} {N : NF} {m m' : ℕ → ℕ}
    {AS S AL E AT : ℕ} {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)} {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}
    (h : OD P J N m AS S AL E AT rs ls) {A₀ : ℕ} (hm : MemEqBelow A₀ m' m)
    (hS : AS + 5 * S ≤ A₀) (hE : AL + 7 * E ≤ A₀) (hT : AT + 3 * (2 * N.nChords) ≤ A₀) :
    OD P J N m' AS S AL E AT rs ls := by
  have ht : ∀ j, j < 2 * N.nChords → tabOf J (Qof P) m' AT j = tabOf J (Qof P) m AT j := by
    intro j hj
    unfold tabOf
    ram_rw [hm, hm (AT + 3 * j + 1), hm (AT + 3 * j + 2)]
  refine ⟨h.rl, h.rr.congr (fun a _ ha => hm a (by rw [h.rl] at ha; omega)), h.rok, h.rw,
    h.ll, h.lr.below (by rw [h.ll]; exact hE) hm, h.lok, h.lw,
    fun j hj => ?_, fun j hj => ?_⟩
  · rw [ht j hj]; exact h.tok j hj
  · ram_rw [hm, hm (AT + 3 * j + 1), hm (AT + 3 * j + 2)]
    exact h.tw j hj

section steps

variable {P : Polygon} {J : Merge.Junction} {N : NF} {m : ℕ → ℕ} {AS S AL E AT : ℕ}
  {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)} {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}

section

variable (h : OD P J N m AS S AL E AT rs ls)

include h in
theorem OD.logW {j : ℕ} (hj : j < E) :
    PosW P J (m (AL + 7 * j)) (m (AL + 7 * j + 1)) := by
  have hj' : j < ls.length := by rwa [h.ll]
  obtain ⟨a1, a2, -⟩ := h.lr j hj'
  rw [a1, a2, List.getD_eq_getElem _ _ hj']
  exact h.lw _ (List.getElem_mem _)

include h in
theorem OD.stopR {x : ℕ} (hx : x < S) :
    PosW P J (m (AS + 5 * x)) (m (AS + 5 * x + 1)) ∧ m (AS + 5 * x + 2) ≤ 2 ∧
      m (AS + 5 * x + 4) ≤ 1 ∧ (m (AS + 5 * x + 2) = 1 → m (AS + 5 * x + 3) < N.nChords) := by
  have hx' : x < rs.length := by rwa [h.rl]
  obtain ⟨a1, a2, a3, a4, a5⟩ := h.rr x hx'
  rw [a1, a2, a3, a4, a5, List.getD_eq_getElem _ _ hx']
  exact h.rw _ (List.getElem_mem _)

include h in
theorem OD.down {G : ℕ} (hG : G = gW J) (x : WPos) :
    ∀ a b, a ≤ b → b < E → lsPr P J m AL G x b → lsPr P J m AL G x a := by
  rw [← h.ll]; exact (search_exact hG h.lr h.lok x).1

include h in
/-- **A stop record**: the answer `t` of the search for its key is a log record with that key,
and its origin position is a good slot content for it. -/
theorem stop_step (hP : J.P.Simple)
    (hN : IsNF J.rightModel (Qof P) N) {G : ℕ} (hG : G = gW J) {x : ℕ} (hx : x < S)
    {t : ℕ} (h1 : ∀ j, j < t → lsPr P J m AL G ⟨m (AS + 5 * x), m (AS + 5 * x + 1)⟩ j)
    (h2 : ∀ j, t ≤ j → j < E → ¬ lsPr P J m AL G ⟨m (AS + 5 * x), m (AS + 5 * x + 1)⟩ j) :
    t < E ∧ m (AL + 7 * t) = m (AS + 5 * x) ∧
      J.wholeModel.param (Qof P) (logPos m AL t) =
        J.wholeModel.param (Qof P) ⟨m (AS + 5 * x), m (AS + 5 * x + 1)⟩ ∧
      SlotVal P J (stopPos P J N (m (AS + 5 * x + 2)) (m (AS + 5 * x + 3)) (m (AS + 5 * x + 4)))
        (sOf (m (AS + 5 * x + 4))) (logPt P J m AL t) := by
  have hx' : x < rs.length := by rwa [h.rl]
  set r := rs[x] with hr
  have hmem : r ∈ rs := List.getElem_mem _
  obtain ⟨a1, a2, a3, a4, a5⟩ := h.rr x hx'
  rw [List.getD_eq_getElem _ _ hx'] at a1 a2 a3 a4 a5
  obtain ⟨-, hkind, -, hk⟩ := h.rw r hmem
  obtain ⟨hc, hF, hA, hL⟩ := stop_cand J hN h.rok hmem hkind hk
  obtain ⟨i, hi, e1, e2⟩ := attach_idx (x := ⟨r.1, r.2.1⟩) h.lr h.lok hF hA hL
  rw [← a1, ← a2] at e1 e2
  have hti := (search_exact hG h.lr h.lok _).2 i hi e1 e2 t h1 (by rw [h.ll]; exact h2)
  subst hti
  rw [h.ll] at hi
  refine ⟨hi, e1, e2, ?_⟩
  rw [a3, a4, a5]
  obtain ⟨s1, s2, s3⟩ := stopPos_facts (b := r.2.2.2.2) hP hN hkind hk
  refine ⟨s1, s2, ?_⟩
  rw [s3, ini_dS_sOf]
  have hpt : logPt P J m AL t = sidePt J.wholeModel.W r.1
      (J.wholeModel.param (Qof P) ⟨r.1, r.2.1⟩) := by
    unfold logPt
    rw [e2, ← a1, ← a2]
    show sidePt _ (m (AL + 7 * t)) _ = _
    rw [e1]
  rwa [hpt]

/-- **The regular endpoint queries** by an index test on the normalised end position. -/
theorem valid_test (hP : J.P.Simple) (hN : IsNF J.rightModel (Qof P) N) {k s : ℕ}
    (hk : k < N.nChords) (hs : s ≤ 1) :
    ValidO J (Qof P) N (2 * k + s) ↔
      (6 ≤ (endPos N k s).edge ∧ (endPos N k s).edge ≤ 2 * J.right.m + 5 ∧
        (nhgt J.rightModel (Qof P) (endPos N k s) ≠ 0 ∨
          ((endPos N k s).edge ≠ 6 ∧ (endPos N k s).edge ≠ cstR J 1 ∧
            (endPos N k s).edge ≠ 6 + midT J.right))) := by
  obtain ⟨f1, f2, f3, f4⟩ := endPos_facts hN hk hs
  have hv := valid_iff J hP (Qof P)
    (x := ⟨(endPos N k s).edge, nhgt J.rightModel (Qof P) (endPos N k s)⟩) f1 f2.1 f2.2.1 f4
  unfold ValidO
  rwa [← f3]

include h in
/-- **A regular table entry with flag `1`**: the answer `t` of the search for its position is a
log record with that key, and the normalised end position is a good slot content for it. -/
theorem tab_step (hN : IsNF J.rightModel (Qof P) N)
    {G : ℕ} (hG : G = gW J) {k s : ℕ} (hk : k < N.nChords) (hs : s ≤ 1)
    (hv : ValidO J (Qof P) N (2 * k + s)) (hf : m (AT + 3 * (2 * k + s)) = 1) {t : ℕ}
    (h1 : ∀ j, j < t → lsPr P J m AL G
      ⟨m (AT + 3 * (2 * k + s) + 1), m (AT + 3 * (2 * k + s) + 2)⟩ j)
    (h2 : ∀ j, t ≤ j → j < E → ¬ lsPr P J m AL G
      ⟨m (AT + 3 * (2 * k + s) + 1), m (AT + 3 * (2 * k + s) + 2)⟩ j) :
    t < E ∧ m (AL + 7 * t) = m (AT + 3 * (2 * k + s) + 1) ∧
      J.wholeModel.param (Qof P) (logPos m AL t) =
        J.wholeModel.param (Qof P)
          ⟨m (AT + 3 * (2 * k + s) + 1), m (AT + 3 * (2 * k + s) + 2)⟩ ∧
      SlotVal P J ⟨(endPos N k s).edge, nhgt J.rightModel (Qof P) (endPos N k s)⟩ s
        (logPt P J m AL t) := by
  set j := 2 * k + s with hjdef
  have hj : j < 2 * N.nChords := by omega
  obtain ⟨hon, hsh, htop⟩ := hv
  have hTj : tabOf J (Qof P) m AT j =
      some (m (AT + 3 * j + 1), J.wholeModel.param (Qof P)
        ⟨m (AT + 3 * j + 1), m (AT + 3 * j + 2)⟩) := by
    unfold tabOf; rw [ite_eq_left hf]
  obtain ⟨hc, hF, hA, hL⟩ := tab_cand J h.tok hj hon hsh htop hTj
  obtain ⟨i, hi, e1, e2⟩ := attach_idx (x := ⟨m (AT + 3 * j + 1), m (AT + 3 * j + 2)⟩)
    h.lr h.lok hF hA hL
  have hti := (search_exact hG h.lr h.lok _).2 i hi e1 e2 t h1 (by rw [h.ll]; exact h2)
  subst hti
  rw [h.ll] at hi
  refine ⟨hi, e1, e2, ?_⟩
  obtain ⟨f1, f2, f3, -⟩ := endPos_facts hN hk hs
  refine ⟨f1, f2, ?_⟩
  rw [f3]
  have hd : dS s = endDir j := by
    unfold dS endDir
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hs with rfl | rfl
    · simp [hjdef]
    simp_all 
  rw [hd]
  have hpt : logPt P J m AL t = sidePt J.wholeModel.W (m (AT + 3 * j + 1))
      (J.wholeModel.param (Qof P) ⟨m (AT + 3 * j + 1), m (AT + 3 * j + 2)⟩) := by
    unfold logPt
    rw [e2]
    show sidePt _ (m (AL + 7 * t)) _ = _
    rw [e1]
  rwa [hpt]

end

end steps

/-! ## The invariant of the slot table -/

/-- **The slot table after `x` stop records and the table entries of the first `kk` chords.** -/
def SInv (P : Polygon) (J : Merge.Junction) (N : NF) (AS AL E AT B : ℕ) (m : ℕ → ℕ)
    (x kk : ℕ) : Prop :=
  (∀ i, i < E → ∀ s, s ≤ 1 → SlotOK P J m B AL i s) ∧
  (∀ y, y < x → ∃ i, i < E ∧ m (AL + 7 * i) = m (AS + 5 * y) ∧
    J.wholeModel.param (Qof P) (logPos m AL i) =
      J.wholeModel.param (Qof P) ⟨m (AS + 5 * y), m (AS + 5 * y + 1)⟩ ∧
    m (slotA B i (sOf (m (AS + 5 * y + 4)))) = 1) ∧
  (∀ j, j < kk → ValidO J (Qof P) N j → m (AT + 3 * j) = 1 →
    ∃ i, i < E ∧ m (AL + 7 * i) = m (AT + 3 * j + 1) ∧
    J.wholeModel.param (Qof P) (logPos m AL i) =
      J.wholeModel.param (Qof P) ⟨m (AT + 3 * j + 1), m (AT + 3 * j + 2)⟩ ∧
    m (slotA B i (j % 2)) = 1)

section

variable {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ}

include P J N AS AL E AT B in
/-- The invariant at the start: a zeroed slot table. -/
theorem SInv.zero {m : ℕ → ℕ}
    (hz : ∀ a, B ≤ a → a < B + 6 * E → m a = 0) : SInv P J N AS AL E AT B m 0 0 := by
  refine ⟨fun i hi s hs => ?_, fun y hy => absurd hy (Nat.not_lt_zero _),
    fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  have h0 : m (slotA B i s) = 0 := hz _ (by register_guard) (by register_guard)
  simp [SlotOK, h0]

include P J N AS AL E AT B in
/-- **The invariant is local** below the end of the slot table. -/
theorem SInv.congr
    {m m' : ℕ → ℕ} {x kk : ℕ} (h : SInv P J N AS AL E AT B m x kk)
    (hm : MemEqBelow (B + 6 * E) m' m) (hS : AS + 5 * x ≤ B) (hE : AL + 7 * E ≤ B)
    (hT : AT + 3 * kk ≤ B) : SInv P J N AS AL E AT B m' x kk := by
  obtain ⟨h1, h2, h3⟩ := h
  have hL : ∀ i, i < E → logPos m' AL i = logPos m AL i := fun i hi => by
    ram_finish [logPos, hm]
  have hL0 : ∀ i, i < E → m' (AL + 7 * i) = m (AL + 7 * i) := fun i hi => hm _ (by omega)
  have hB : ∀ i, i < E → ∀ s, s ≤ 1 → ∀ d, d < 3 → m' (slotA B i s + d) = m (slotA B i s + d) :=
    fun i hi s hs d hd => hm _ (by register_guard)
  have hB0 := fun i hi s hs => by simpa using hB i hi s hs 0 (by norm_num)
  refine ⟨fun i hi s hs => ?_, fun y hy => ?_, fun j hj hv hf => ?_⟩
  · unfold SlotOK logPt
    ram_rw [hB0 i hi s hs, hB i hi s hs 1, hB i hi s hs 2, hL i hi]
    exact h1 i hi s hs
  · obtain ⟨i, hi, e1, e2, e3⟩ := h2 y hy
    refine ⟨i, hi, ?_, ?_, ?_⟩
    · ram_simp [hL0 i hi, hm, e1]
    · ram_simp [hL i hi, hm, e2]
    · ram_rw [hm (AS + 5 * y + 4), hB0 i hi _ (ini_sOf_le _), e3]
  · have hf' : m (AT + 3 * j) = 1 := by ram_simp [← hm] <;> omega
    obtain ⟨i, hi, e1, e2, e3⟩ := h3 j hj hv hf'
    refine ⟨i, hi, ?_, ?_, ?_⟩
    · ram_simp [hL0 i hi, hm, e1]
    · ram_simp [hL i hi, hm, e2]
    ram_simp [hB0, e3]

include P J N AS AL E AT B in
/-- **Writing a good slot keeps the invariant** (the records lie below the slot table). -/
theorem SInv.store
    {m : ℕ → ℕ} {x kk t s e h : ℕ} (hI : SInv P J N AS AL E AT B m x kk)
    (hS : AS + 5 * x ≤ B) (hE : AL + 7 * E ≤ B) (hT : AT + 3 * kk ≤ B) (ht : t < E)
    (hs : s ≤ 1) (hv : SlotVal P J ⟨e, h⟩ s (logPt P J m AL t)) :
    SInv P J N AS AL E AT B (slotW m B t s e h) x kk ∧ slotW m B t s e h (slotA B t s) = 1 := by
  obtain ⟨h1, h2, h3⟩ := hI
  have hlow : ∀ a, a < B → slotW m B t s e h a = m a :=
    fun a ha => slotW_other (Or.inl (by register_guard))
  have hfl : ∀ i, i < E → ∀ s', s' ≤ 1 → m (slotA B i s') = 1 →
      slotW m B t s e h (slotA B i s') = 1 := by
    intro i hi s' hs' hf
    by_cases hit : i = t ∧ s' = s
    · obtain ⟨rfl, rfl⟩ := hit; exact slotW_flag
    · rwa [slotW_other (by simpa using slot_sep (d := 0) hs' hs (by norm_num) hit)]
  have hL : ∀ i, i < E → logPos (slotW m B t s e h) AL i = logPos m AL i := fun i hi => by
    ram_simp [logPos, hlow] 
  have hL0 : ∀ i, i < E → slotW m B t s e h (AL + 7 * i) = m (AL + 7 * i) :=
    fun i hi => hlow _ (by omega)
  refine ⟨⟨slotOK_store hE ht hs h1 hv, fun y hy => ?_, fun j hj hv' hf => ?_⟩, slotW_flag⟩
  · obtain ⟨i, hi, e1, e2, e3⟩ := h2 y hy
    refine ⟨i, hi, ?_, ?_, ?_⟩
    · ram_simp [hL0 i hi, hlow, e1]
    · ram_simp [hL i hi, hlow, e2]
    · ram_rw [hlow (AS + 5 * y + 4)]; exact hfl i hi _ (ini_sOf_le _) e3
  · have hf' : m (AT + 3 * j) = 1 := by ram_simp [← hlow] <;> omega
    obtain ⟨i, hi, e1, e2, e3⟩ := h3 j hj hv' hf'
    refine ⟨i, hi, ?_, ?_, ?_⟩
    · ram_simp [hL0 i hi, hlow, e1]
    · ram_simp [hL i hi, hlow, e2]
    · exact hfl i hi _ (by omega) e3

include P J N AS AL E AT B in
/-- One more stop record. -/
theorem SInv.extS
    {m : ℕ → ℕ} {x kk : ℕ} (h : SInv P J N AS AL E AT B m x kk)
    (hx : ∃ i, i < E ∧ m (AL + 7 * i) = m (AS + 5 * x) ∧
      J.wholeModel.param (Qof P) (logPos m AL i) =
        J.wholeModel.param (Qof P) ⟨m (AS + 5 * x), m (AS + 5 * x + 1)⟩ ∧
      m (slotA B i (sOf (m (AS + 5 * x + 4)))) = 1) :
    SInv P J N AS AL E AT B m (x + 1) kk := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun y hy => ?_, h3⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy | rfl
  · exact h2 y hy
  · exact hx

include P J N AS AL E AT B in
/-- One more table entry. -/
theorem SInv.extT
    {m : ℕ → ℕ} {x kk : ℕ} (h : SInv P J N AS AL E AT B m x kk)
    (hx : ValidO J (Qof P) N kk → m (AT + 3 * kk) = 1 →
      ∃ i, i < E ∧ m (AL + 7 * i) = m (AT + 3 * kk + 1) ∧
      J.wholeModel.param (Qof P) (logPos m AL i) =
        J.wholeModel.param (Qof P) ⟨m (AT + 3 * kk + 1), m (AT + 3 * kk + 2)⟩ ∧
      m (slotA B i (kk % 2)) = 1) :
    SInv P J N AS AL E AT B m x (kk + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · exact h3 j hj
  · exact hx

theorem logPt_congr {P : Polygon} {J : Merge.Junction} {m m' : ℕ → ℕ} {AL t B : ℕ}
    (hm : MemEqBelow B m' m) (ht : AL + 7 * t + 1 < B) :
    logPt P J m' AL t = logPt P J m AL t := by
  ram_finish [logPt, logPos, hm, hm (AL + 7 * t + 1) ht]

include P J N AS AL E AT B in
/-- **The step of a stop record**: a good slot written at the answer of the search. -/
theorem SInv.stopStep
    {m m₂ : ℕ → ℕ} {x kk t eV hV : ℕ} (hI : SInv P J N AS AL E AT B m x kk)
    (hm : MemEqBelow B m₂ m) (hS : AS + 5 * (x + 1) ≤ B) (hE : AL + 7 * E ≤ B)
    (hT : AT + 3 * kk ≤ B) (ht : t < E) (e1 : m₂ (AL + 7 * t) = m₂ (AS + 5 * x))
    (e2 : J.wholeModel.param (Qof P) (logPos m₂ AL t) =
      J.wholeModel.param (Qof P) ⟨m₂ (AS + 5 * x), m₂ (AS + 5 * x + 1)⟩)
    (hv : SlotVal P J ⟨eV, hV⟩ (sOf (m₂ (AS + 5 * x + 4))) (logPt P J m₂ AL t)) :
    SInv P J N AS AL E AT B (slotW m B t (sOf (m (AS + 5 * x + 4))) eV hV) (x + 1) kk := by
  ram_rw [hm] at hv
  ram_rw [logPt_congr hm] at hv
  obtain ⟨h1, h2⟩ := hI.store (by omega) hE hT ht (ini_sOf_le _) hv
  refine h1.extS ⟨t, ht, ?_, ?_, ?_⟩
  · ram_rw assumption [slotW_other (Or.inl (by register_guard)),
      slotW_other (Or.inl (by register_guard)), ← hm, ← hm (AS + 5 * x) (by omega)]
  · have hp : logPos (slotW m B t (sOf (m (AS + 5 * x + 4))) eV hV) AL t = logPos m₂ AL t := by
      unfold logPos
      ram_rw [slotW_other (Or.inl (by register_guard)),
        slotW_other (Or.inl (by register_guard)), hm, hm (AL + 7 * t + 1) (by omega)]
    ram_rw [hp, e2, slotW_other (Or.inl (by register_guard)),
      slotW_other (Or.inl (by register_guard)), hm, hm (AS + 5 * x + 1) (by omega)]
  · have h4 : slotW m B t (sOf (m (AS + 5 * x + 4))) eV hV (AS + 5 * x + 4) = m (AS + 5 * x + 4) :=
      slotW_other (Or.inl (by register_guard))
    rwa [h4]

include P J N AS AL E AT B in
/-- **The step of a regular table entry with flag `1`.** -/
theorem SInv.tabStep
    {m m₂ : ℕ → ℕ} {x kk t eV hV : ℕ} (hI : SInv P J N AS AL E AT B m x kk)
    (hm : MemEqBelow B m₂ m) (hS : AS + 5 * x ≤ B) (hE : AL + 7 * E ≤ B)
    (hT : AT + 3 * (kk + 1) ≤ B) (ht : t < E) (e1 : m₂ (AL + 7 * t) = m₂ (AT + 3 * kk + 1))
    (e2 : J.wholeModel.param (Qof P) (logPos m₂ AL t) =
      J.wholeModel.param (Qof P) ⟨m₂ (AT + 3 * kk + 1), m₂ (AT + 3 * kk + 2)⟩)
    (hv : SlotVal P J ⟨eV, hV⟩ (kk % 2) (logPt P J m₂ AL t)) :
    SInv P J N AS AL E AT B (slotW m B t (kk % 2) eV hV) x (kk + 1) := by
  ram_rw [logPt_congr hm] at hv
  obtain ⟨h1, h2⟩ := hI.store hS hE (by omega) ht (by omega) hv
  refine h1.extT (fun _ _ => ⟨t, ht, ?_, ?_, h2⟩)
  · ram_rw assumption [slotW_other (Or.inl (by register_guard)),
      slotW_other (Or.inl (by register_guard)), ← hm,
      ← hm (AT + 3 * kk + 1) (by omega)]
  · have hp : logPos (slotW m B t (kk % 2) eV hV) AL t = logPos m₂ AL t := by
      unfold logPos
      ram_rw [slotW_other (Or.inl (by register_guard)),
        slotW_other (Or.inl (by register_guard)), hm, hm (AL + 7 * t + 1) (by omega)]
    rw [hp, e2, slotW_other (Or.inl (by register_guard)),
      slotW_other (Or.inl (by register_guard)), hm (AT + 3 * kk + 1) (by omega),
      hm (AT + 3 * kk + 2) (by omega)]

include P J N AS AL E AT B in
/-- **A table entry without a slot**: not regular, or flag `0`. -/
theorem SInv.tabSkip
    {m : ℕ → ℕ} {x kk : ℕ} (hI : SInv P J N AS AL E AT B m x kk)
    (h : ¬ (ValidO J (Qof P) N kk ∧ m (AT + 3 * kk) = 1)) :
    SInv P J N AS AL E AT B m x (kk + 1) :=
  hI.extT (fun hv hf => absurd ⟨hv, hf⟩ h)

end

end

end S0C

end SweepIo

end Chazelle.Core
