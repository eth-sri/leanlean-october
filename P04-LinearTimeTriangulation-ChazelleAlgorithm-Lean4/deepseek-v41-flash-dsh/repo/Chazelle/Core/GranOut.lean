module

public import Chazelle.Core.GranInit

/-!
# WP-F, part 16: the chord list of the result

After the worklist, the chord triples `(h, lp, rp)` of the live chord records, in the order of
the records, are written to the list area (`outStmt`, `out_exec`): the list `outList N live K`.
Its chords are the current submap and satisfy `ChordTriplesOK` (`outList_ok`), the input of
normal-form construction (`BuildNFSpec`).
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-! ## The list -/

/-- The triple of a chord record. -/
def trip (N : NF) (u : ℕ) : ℕ × ℕ × ℕ := ((N.chord u).h, (N.chord u).lp, (N.chord u).rp)

/-- The live record indices below `i`. -/
def liveList (live : ℕ → ℕ) (i : ℕ) : List ℕ := (List.range i).filter fun u => live u == 1

/-- The triples of the live records below `i`. -/
def outList (N : NF) (live : ℕ → ℕ) (i : ℕ) : List (ℕ × ℕ × ℕ) := (liveList live i).map (trip N)

theorem liveList_succ (live : ℕ → ℕ) (i : ℕ) :
    liveList live (i + 1) = liveList live i ++ (if live i = 1 then [i] else []) := by
  unfold liveList
  rw [List.range_succ, List.filter_append]
  congr 1
  by_cases h : live i = 1 <;> simp [h]

theorem mem_liveList {live : ℕ → ℕ} {i u : ℕ} : u ∈ liveList live i ↔ u < i ∧ live u = 1 := by
  unfold liveList; simp

theorem liveList_nodup (live : ℕ → ℕ) (i : ℕ) : (liveList live i).Nodup :=
  (List.nodup_range).filter _

/-- **The list describes the current submap and is a valid input of the construction.** -/
theorem outList_ok {E : Env} {st : St} (hE : E.Good) :
    {c | ∃ x ∈ outList E.N st.live E.K, c = (recOf x).toSet E.M E.Q} = st.F E ∧
      ChordTriplesOK E.M E.Q (outList E.N st.live E.K) := by
  have hF : {c | ∃ x ∈ outList E.N st.live E.K, c = (recOf x).toSet E.M E.Q} = st.F E := by
    ext c
    simp only [outList, List.mem_map, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      obtain ⟨h1, h2⟩ := mem_liveList.1 hu
      exact ⟨u, ⟨h1, h2⟩, h1, rfl⟩
    · rintro ⟨u, ⟨h1, h2⟩, -, rfl⟩
      exact ⟨trip E.N u, ⟨u, mem_liveList.2 ⟨h1, h2⟩, rfl⟩, rfl⟩
  refine ⟨hF, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hF]; exact fam_chordFamily hE.hNF _
  · rw [outList, List.map_map]
    refine (liveList_nodup st.live E.K).map_on fun u hu v hv h => ?_
    exact cs_inj hE.hNF (mem_liveList.1 hu).1 (mem_liveList.1 hv).1 h
  · simp only [outList, List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact hE.hNF.2.2.1 u (mem_liveList.1 hu).1
  · simp only [outList, List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨-, -, -, -, -, -, -, -, -, hh, -⟩ := hE.hNF
    exact hh u (mem_liveList.1 hu).1

/-! ## The program -/

/-- Write the triple of record `r71` at `r96` (advanced by three) and count it in `r95`. -/
def writeT : Stmt := block [.loadN 90074 90071, .storeN 90096 90074, .addN 90096 90096 90019,
  .addN 90075 90071 90019, .loadN 90074 90075, .storeN 90096 90074, .addN 90096 90096 90019,
  .addN 90075 90071 90021, .loadN 90074 90075, .storeN 90096 90074, .addN 90096 90096 90019,
  .addN 90095 90095 90019]

/-- One record. -/
def outBody : Stmt :=
  .seq (block [.addN 90072 90030 90070, .loadN 90073 90072])
    (.seq (.ifLtN 90073 90019 .skip writeT) (block [.addN 90071 90071 90076, .addN 90070 90070 90019]))

/-- **The output of the chord list** at `r28`, its length in `r95`. -/
def outStmt : Stmt := .seq (block [.constN 90070 0, .copyN 90071 90013, .constN 90095 0,
  .copyN 90096 90028, .constN 90076 5]) (.whileLtN 90070 90010 outBody)

theorem wrS_outStmt : wrS Binit outStmt = true := by decide

set_option maxHeartbeats 2000000 in
theorem writeT_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {p q L : ℕ}
    (h71 : c.nreg 90071 = p) (h96 : c.nreg 90096 = q) (h95 : c.nreg 90095 = L)
    (h19 : c.nreg 90019 = 1) (h21 : c.nreg 90021 = 2) (hpq : p + 2 < q) (hq : q + 3 ≤ W)
    (hL : L + 1 ≤ W) :
    ∃ c' k, Exec P W writeT c c' k ∧ k = 12 ∧ c'.nreg 90096 = q + 3 ∧ c'.nreg 90095 = L + 1 ∧
      c'.nmem = upd (upd (upd c.nmem q (c.nmem p)) (q + 1) (c.nmem (p + 1))) (q + 2)
        (c.nmem (p + 2)) ∧
      (∀ r, r ≠ 90074 → r ≠ 90075 → r ≠ 90095 → r ≠ 90096 → c'.nreg r = c.nreg r) := by
  unfold writeT
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same, Machine.upd_other,
    h71, h96, h95, h19, h21]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r a1 a2 a3 a4 => ?_⟩ <;>
    simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, h71, h96, h95, h19, h21]

/-! ## Lists -/

theorem liveList_length_le (live : ℕ → ℕ) (i : ℕ) : (liveList live i).length ≤ i := by
  unfold liveList
  exact (List.length_filter_le _ _).trans (by simp)

theorem outList_length_le (N : NF) (live : ℕ → ℕ) (i : ℕ) : (outList N live i).length ≤ i := by
  unfold outList; rw [List.length_map]; exact liveList_length_le live i

theorem outList_succ (N : NF) (live : ℕ → ℕ) (i : ℕ) :
    outList N live (i + 1) = outList N live i ++ (if live i = 1 then [trip N i] else []) := by
  unfold outList; rw [liveList_succ, List.map_append]; split_ifs <;> simp

theorem ChordListAt.congr {m m' : ℕ → ℕ} {A : ℕ} {L : List (ℕ × ℕ × ℕ)} (h : ChordListAt m A L)
    (hm : ∀ a, A ≤ a → a < A + 3 * L.length → m' a = m a) : ChordListAt m' A L := by
  intro i hi
  obtain ⟨h0, h1, h2⟩ := h i hi
  exact ⟨(hm _ (by omega) (by omega)).trans h0, (hm _ (by omega) (by omega)).trans h1,
    (hm _ (by omega) (by omega)).trans h2⟩

theorem ChordListAt.snoc {m m' : ℕ → ℕ} {A : ℕ} {L : List (ℕ × ℕ × ℕ)} {x : ℕ × ℕ × ℕ}
    (h : ChordListAt m A L) (hm : ∀ a, A ≤ a → a < A + 3 * L.length → m' a = m a)
    (h0 : m' (A + 3 * L.length) = x.1) (h1 : m' (A + 3 * L.length + 1) = x.2.1)
    (h2 : m' (A + 3 * L.length + 2) = x.2.2) : ChordListAt m' A (L ++ [x]) := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i L.length with hl | hl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hl, ← List.getD_eq_getElem?_getD]
    exact (ChordListAt.congr h hm) i hl
  · have : i = L.length := by omega
    subst this
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self]
    exact ⟨h0, h1, h2⟩

/-! ## The loop -/

/-- The output-loop invariant. -/
structure OutI (W K CB LB0 : ℕ) (N : NF) (live : ℕ → ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  i_le : c.nreg 90070 ≤ K
  ptr : c.nreg 90071 = CB + 5 * c.nreg 90070
  c76 : c.nreg 90076 = 5
  cnt : c.nreg 90095 = (outList N live (c.nreg 90070)).length
  dst : c.nreg 90096 = LB0 + 3 * (outList N live (c.nreg 90070)).length
  regs : ∀ r, Binit r = false → c.nreg r = c₀.nreg r
  list : ChordListAt c.nmem LB0 (outList N live (c.nreg 90070))
  mem : ∀ a, (a < LB0 ∨ LB0 + 3 * K ≤ a) → c.nmem a = c₀.nmem a

theorem outHead_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (ha : c.nreg 90030 + c.nreg 90070 ≤ W) :
    ∃ c' k, Exec P W (block [.addN 90072 90030 90070, .loadN 90073 90072]) c c' k ∧ k = 2 ∧
      c'.nreg 90073 = c.nmem (c.nreg 90030 + c.nreg 90070) ∧ c'.nmem = c.nmem ∧
      (∀ r, r ≠ 90072 → r ≠ 90073 → c'.nreg r = c.nreg r) := by
  exec_block
  · exact ha
  · refine ⟨rfl, ?_, rfl, fun r a1 a2 => ?_⟩ <;> config_simp
    simp (disch := omega) only [Machine.upd_other]

theorem outTail_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (ha : c.nreg 90071 + c.nreg 90076 ≤ W) (hb : c.nreg 90070 + c.nreg 90019 ≤ W) :
    ∃ c' k, Exec P W (block [.addN 90071 90071 90076, .addN 90070 90070 90019]) c c' k ∧
      k = 2 ∧ c'.nreg 90071 = c.nreg 90071 + c.nreg 90076 ∧
      c'.nreg 90070 = c.nreg 90070 + c.nreg 90019 ∧ c'.nmem = c.nmem ∧
      (∀ r, r ≠ 90070 → r ≠ 90071 → c'.nreg r = c.nreg r) := by
  exec_block
  · exact ha
  · config_simp; exact hb
  · refine ⟨rfl, ?_, ?_, rfl, fun r a1 a2 => ?_⟩ <;> config_simp
    simp (disch := omega) only [Machine.upd_other]

/-- The fixed data of the output loop. -/
structure OutEnv (W K CB LB0 b0 : ℕ) (N : NF) (live : ℕ → ℕ) (c₀ : Config) : Prop where
  r30 : c₀.nreg 90030 = b0
  r19 : c₀.nreg 90019 = 1
  r21 : c₀.nreg 90021 = 2
  r10 : c₀.nreg 90010 = K
  hlive : ∀ u, u < K → c₀.nmem (b0 + u) = live u
  hl01 : ∀ u, u < K → live u ≤ 1
  hrec : ∀ u, u < K → c₀.nmem (CB + 5 * u) = (N.chord u).h ∧
    c₀.nmem (CB + 5 * u + 1) = (N.chord u).lp ∧ c₀.nmem (CB + 5 * u + 2) = (N.chord u).rp
  hCB : CB + 5 * K ≤ LB0
  hb0 : b0 + K ≤ LB0
  hW : LB0 + 3 * K ≤ W

set_option maxHeartbeats 1000000 in
theorem outBody_exec {P : Polygon} {W K CB LB0 b0 : ℕ} {N : NF} {live : ℕ → ℕ} {c₀ c : Config}
    (hE : OutEnv W K CB LB0 b0 N live c₀) (hI : OutI W K CB LB0 N live c₀ c)
    (ht : c.nreg 90070 < K) :
    ∃ c' k, Exec P W outBody c c' k ∧ OutI W K CB LB0 N live c₀ c' ∧ k ≤ 19 ∧
      c'.nreg 90070 = c.nreg 90070 + 1 := by
  obtain ⟨hw, hi, hp, h76, hcnt, hdst, hr, hlist, hm⟩ := hI
  have c30 : c.nreg 90030 = b0 := by rw [hr _ (by decide), hE.r30]
  have c19 : c.nreg 90019 = 1 := by rw [hr _ (by decide), hE.r19]
  have c21 : c.nreg 90021 = 2 := by rw [hr _ (by decide), hE.r21]
  have hW := hE.hW
  have hCB := hE.hCB
  have hb0 := hE.hb0
  set i := c.nreg 90070 with hi_def
  set L := outList N live i with hL_def
  have hLi : L.length ≤ i := outList_length_le N live i
  have mlive : c.nmem (b0 + i) = live i := by rw [hm _ (by left; omega), hE.hlive i ht]
  obtain ⟨c₁, k₁, e₁, hk₁, r73, m₁, R₁⟩ := outHead_exec (P := P) c hw (by rw [c30]; omega)
  rw [c30, mlive] at r73
  have w₁ := e₁.wb_right
  -- the conditional write
  obtain ⟨c₂, k₂, e₂, hk₂, w₂, r95, r96, lst, mm, R₂⟩ : ∃ c₂ k₂, Exec P W
      (.ifLtN 90073 90019 .skip writeT) c₁ c₂ k₂ ∧ k₂ ≤ 14 ∧ WordsBounded W c₂ ∧
      c₂.nreg 90095 = (outList N live (i + 1)).length ∧
      c₂.nreg 90096 = LB0 + 3 * (outList N live (i + 1)).length ∧
      ChordListAt c₂.nmem LB0 (outList N live (i + 1)) ∧
      (∀ a, (a < LB0 ∨ LB0 + 3 * K ≤ a) → c₂.nmem a = c₀.nmem a) ∧
      (∀ r, r ≠ 90072 → r ≠ 90073 → r ≠ 90074 → r ≠ 90075 → r ≠ 90095 → r ≠ 90096 →
        c₂.nreg r = c.nreg r) := by
    rw [outList_succ, ← hL_def]
    have h1 : c₁.nreg 90019 = 1 := by rw [R₁ _ (by decide) (by decide), c19]
    by_cases hl : live i = 1
    · simp only [hl, ite_true]
      have hrec := hE.hrec i ht
      obtain ⟨c₂, k₂, e₂, hk₂, r96', r95', m₂, R₂'⟩ := writeT_exec (P := P) c₁ w₁ (p := CB + 5 * i)
        (q := LB0 + 3 * L.length) (L := L.length)
        (by rw [R₁ _ (by decide) (by decide), hp]) (by rw [R₁ _ (by decide) (by decide), hdst])
        (by rw [R₁ _ (by decide) (by decide), hcnt]) h1
        (by rw [R₁ _ (by decide) (by decide), c21]) (by omega) (by omega) (by omega)
      have e₂' : Exec P W (.ifLtN 90073 90019 .skip writeT) c₁ c₂ (k₂ + 2) :=
        .ifLtN_false (by rw [r73, h1, hl]; omega) e₂
      have v0 : c₁.nmem (CB + 5 * i) = (N.chord i).h := by rw [m₁, hm _ (by left; omega), hrec.1]
      have v1 : c₁.nmem (CB + 5 * i + 1) = (N.chord i).lp := by
        rw [m₁, hm _ (by left; omega), hrec.2.1]
      have v2 : c₁.nmem (CB + 5 * i + 2) = (N.chord i).rp := by
        rw [m₁, hm _ (by left; omega), hrec.2.2]
      refine ⟨c₂, _, e₂', by omega, e₂.wb_right, by rw [r95']; simp, by rw [r96']; simp; omega,
        ?_, fun a ha => ?_, fun r a1 a2 a3 a4 a5 a6 => ?_⟩
      · refine ChordListAt.snoc hlist (fun a a1 a2 => ?_) ?_ ?_ ?_
        · rw [m₂, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
            Machine.upd_other _ _ _ (by omega), m₁]
        · rw [m₂, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
            Machine.upd_same, v0]; rfl
        · rw [m₂, Machine.upd_other _ _ _ (by omega), Machine.upd_same, v1]; rfl
        · rw [m₂, Machine.upd_same, v2]; rfl
      · have hL : L.length < K := by omega
        rw [m₂, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
          Machine.upd_other _ _ _ (by omega), m₁, hm a ha]
      · rw [R₂' r a3 a4 a5 a6, R₁ r a1 a2]
    · have h0 : live i = 0 := by have := hE.hl01 i ht; omega
      simp only [hl, ite_false, List.append_nil]
      refine ⟨c₁, _, .ifLtN_true (by rw [r73, h1, h0]; omega) (.skip w₁), by omega, w₁,
        by rw [R₁ _ (by decide) (by decide), hcnt], by rw [R₁ _ (by decide) (by decide), hdst],
        by rw [m₁]; exact hlist, fun a ha => by rw [m₁, hm a ha],
        fun r a1 a2 _ _ _ _ => R₁ r a1 a2⟩
  have c71 : c₂.nreg 90071 = CB + 5 * i := by rw [R₂ _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide), hp]
  have c76 : c₂.nreg 90076 = 5 := by rw [R₂ _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide), h76]
  have c70 : c₂.nreg 90070 = i := R₂ _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have d19 : c₂.nreg 90019 = 1 := by rw [R₂ _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide), c19]
  obtain ⟨c₃, k₃, e₃, hk₃, r71, r70, m₃, R₃⟩ := outTail_exec (P := P) c₂ w₂
    (by rw [c71, c76]; omega) (by rw [c70, d19]; omega)
  rw [c71, c76] at r71
  rw [c70, d19] at r70
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), ⟨e₃.wb_right, by omega, by rw [r71, r70]; ring, by
    rw [R₃ _ (by decide) (by decide), c76], by rw [R₃ _ (by decide) (by decide), r95, r70],
    by rw [R₃ _ (by decide) (by decide), r96, r70], fun r hr' => ?_, by rw [m₃, r70]; exact lst,
    fun a ha => by rw [m₃, mm a ha]⟩, by omega, r70⟩
  have hb : ¬ (90070 ≤ r ∧ r < 90100) := by simpa [Binit] using hr'
  rw [R₃ r (by omega) (by omega), R₂ r (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega), hr r hr']

/-- **The output loop** writes the triples of the live records to the list area. -/
theorem out_exec {P : Polygon} {W K CB LB0 b0 : ℕ} {N : NF} {live : ℕ → ℕ} {c₀ : Config}
    (hw : WordsBounded W c₀) (hE : OutEnv W K CB LB0 b0 N live c₀) (h13 : c₀.nreg 90013 = CB)
    (h28 : c₀.nreg 90028 = LB0) (hW5 : 5 ≤ W) :
    ∃ c' k, Exec P W outStmt c₀ c' k ∧ k ≤ 21 * K + 7 ∧
      c'.nreg 90095 = (outList N live K).length ∧ ChordListAt c'.nmem LB0 (outList N live K) ∧
      (∀ a, (a < LB0 ∨ LB0 + 3 * K ≤ a) → c'.nmem a = c₀.nmem a) ∧
      FrameS Binit c₀ c' := by
  suffices hh : ∃ c' k, Exec P W outStmt c₀ c' k ∧ k ≤ 21 * K + 7 ∧
      c'.nreg 90095 = (outList N live K).length ∧ ChordListAt c'.nmem LB0 (outList N live K) ∧
      (∀ a, (a < LB0 ∨ LB0 + 3 * K ≤ a) → c'.nmem a = c₀.nmem a) by
    obtain ⟨c', k, e, h1, h2, h3, h4⟩ := hh
    exact ⟨c', k, e, h1, h2, h3, h4, exec_frameS e wrS_outStmt⟩
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.constN 90070 0, .copyN 90071 90013,
      .constN 90095 0, .copyN 90096 90028, .constN 90076 5]) c₀ c₁ k₁ ∧ k₁ = 5 ∧
      OutI W K CB LB0 N live c₀ c₁ ∧ c₁.nreg 90070 = 0 := by
    exec_block
    · omega
    · omega
    · omega
    · refine ⟨rfl, ⟨by assumption, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, fun a _ => rfl⟩, ?_⟩
      · config_simp; omega
      · config_simp; rw [h13]; omega
      · config_simp
      · config_simp; rfl
      · config_simp; rw [h28]; rfl
      · simp only [Binit, decide_eq_false_iff_not] at hr
        config_simp; simp only [upd]; split_ifs <;> first | rfl | omega
      · config_simp; intro i hi; simp [outList, liveList] at hi
      · config_simp
  obtain ⟨q, q0⟩ := q
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90070) (b := 90010)
    (body := outBody) (OutI W K CB LB0 N live c₀) (fun c => K - c.nreg 90070) 19
    (fun _ h => h.wb)
    (fun c I ht => by
      have t : c.nreg 90070 < K := by rw [I.regs 90010 (by decide), hE.r10] at ht; exact ht
      obtain ⟨c', k, e, I', hk, hi⟩ := outBody_exec (P := P) hE I t
      exact ⟨c', k, e, I', hk, by omega⟩) q
  have hK' : c'.nreg 90070 = K := by
    rw [I'.regs 90010 (by decide), hE.r10] at hx; have := I'.i_le; omega
  refine ⟨c', _, .seq e₁ e, ?_, by rw [I'.cnt, hK'], by rw [← hK']; exact I'.list, I'.mem⟩
  rw [q0] at hk
  omega

end

end Gran

end Chazelle.Core
