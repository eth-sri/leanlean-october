module

public import Chazelle.Core.OraclePrepDedupMath

/-!
# Lemma 3.6 (WP-H), preprocessing part 16: sorting and deduplicating the raw pairs

`dS`: the handles are saved in band `bDecomp` (`60001 …`), an item array `0 … nZ - 1` is built,
sorted by the lexicographic order of the raw pairs (`SortR.sortStmt lexCmp`), and the pairs are
appended, without repetitions, to the chord arrays after the star chords (`dS_exec`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ

@[expose] public section

/-- The dedup body: the pair at sorted position `t`, kept iff first or new. -/
def dBody : Stmt :=
  .seq (block [.addN 60015 60007 60010, .loadN 60015 60015, .addN 60016 60004 60015,
      .loadN 60012 60016, .addN 60016 60005 60015, .loadN 60013 60016])
    (.ifLtN 120012 60010
      (.seq (block [.subN 60015 60010 120011, .addN 60015 60007 60015, .loadN 60015 60015,
          .addN 60016 60004 60015, .loadN 60018 60016, .addN 60016 60005 60015,
          .loadN 60019 60016])
        (ifEq 60012 60018 (ifEq 60013 60019 (.instr (.constN 60011 0)) (.instr (.constN 60011 1)))
          (.instr (.constN 60011 1))))
      (.instr (.constN 60011 1)))

/-- The registers written by `dBody`. -/
def BDB (r : ℕ) : Bool := decide (60011 ≤ r ∧ r ≤ 60019 ∧ r ≠ 60014 ∧ r ≠ 60017)

/-- The memory read by the dedup body. -/
structure DMem (m : ℕ → ℕ) (Sb Z1 Z2 n : ℕ) (s P1 P2 : ℕ → ℕ) : Prop where
  s_eq : ∀ t, t < n → m (Sb + t) = s t
  s_lt : ∀ t, t < n → s t < n
  p1 : ∀ i, i < n → m (Z1 + i) = P1 i
  p2 : ∀ i, i < n → m (Z2 + i) = P2 i

theorem dBody_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {Sb Z1 Z2 n t : ℕ}
    {s P1 P2 : ℕ → ℕ} (hM : DMem c.nmem Sb Z1 Z2 n s P1 P2) (h7 : c.nreg 60007 = Sb)
    (h4 : c.nreg 60004 = Z1) (h5 : c.nreg 60005 = Z2) (h1 : c.nreg 120011 = 1)
    (h0 : c.nreg 120012 = 0) (ht : c.nreg 60010 = t) (htn : t < n) (hSW : Sb + n ≤ W)
    (hZW : Z1 + n ≤ W) (hZW' : Z2 + n ≤ W) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W dBody c c' k ∧ k ≤ 30 ∧ FrameB BDB c c' ∧
      (dedupF n (fun i => (P1 i, P2 i)) s t = none → c'.nreg 60011 = 0) ∧
      ∀ x, dedupF n (fun i => (P1 i, P2 i)) s t = some x →
        c'.nreg 60011 = 1 ∧ c'.nreg 60012 = x.1 ∧ c'.nreg 60013 = x.2 := by
  have hwr : wr BDB dBody = true := by decide
  have hs := hM.s_lt t htn
  obtain ⟨c₁, k₁, e₁, hk₁, n₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 60015 60007 60010,
      .loadN 60015 60015, .addN 60016 60004 60015, .loadN 60012 60016, .addN 60016 60005 60015,
      .loadN 60013 60016]) c c₁ k₁ ∧ k₁ = 6 ∧
      c₁.nreg = upd (upd (upd (upd c.nreg 60015 (s t)) 60016 (Z2 + s t)) 60012 (P1 (s t))) 60013
        (P2 (s t)) := by
    exec_block
    · rw [h7, ht]; omega
    · config_simp; rw [h7, ht, h4, hM.s_eq t htn]; omega
    · config_simp; rw [h7, ht, h5, hM.s_eq t htn]; omega
    · refine ⟨rfl, ?_⟩
      config_simp; rw [h7, ht, h4, h5, hM.s_eq t htn, hM.p1 _ hs, hM.p2 _ hs]
      funext r; simp only [upd]; split_ifs <;> first | omega
  have w₁ := e₁.wb_right
  have R₁ : ∀ r, r ≠ 60015 → r ≠ 60016 → r ≠ 60012 → r ≠ 60013 → c₁.nreg r = c.nreg r :=
    fun r a b c' d => by rw [n₁]; simp only [upd]; split_ifs <;> first | omega
  have x12 : c₁.nreg 60012 = P1 (s t) := by rw [n₁]; config_simp
  have x13 : c₁.nreg 60013 = P2 (s t) := by rw [n₁]; config_simp
  suffices H : ∃ c₂ k₂, Exec P W (.ifLtN 120012 60010
      (.seq (block [.subN 60015 60010 120011, .addN 60015 60007 60015, .loadN 60015 60015,
          .addN 60016 60004 60015, .loadN 60018 60016, .addN 60016 60005 60015,
          .loadN 60019 60016])
        (ifEq 60012 60018 (ifEq 60013 60019 (.instr (.constN 60011 0)) (.instr (.constN 60011 1)))
          (.instr (.constN 60011 1))))
      (.instr (.constN 60011 1))) c₁ c₂ k₂ ∧ k₂ ≤ 24 ∧
      c₂.nreg 60012 = P1 (s t) ∧ c₂.nreg 60013 = P2 (s t) ∧
      c₂.nreg 60011 = (if t = 0 ∨ (P1 (s t), P2 (s t)) ≠ (P1 (s (t - 1)), P2 (s (t - 1)))
        then 1 else 0) by
    obtain ⟨c₂, k₂, e₂, hk₂, a, b, f⟩ := H
    have ex : Exec P W dBody c c₂ _ := .seq e₁ e₂
    refine ⟨c₂, _, ex, by omega, exec_frameB ex hwr, fun hn => ?_, fun x hx => ?_⟩
    · unfold dedupF at hn
      split_ifs at hn with hc
      rw [f, ite_eq_right (fun h' => hc ⟨htn, h'⟩)]
    · unfold dedupF at hx
      split_ifs at hx with hc
      cases hx
      exact ⟨by rw [f, ite_eq_left hc.2], a, b⟩
  by_cases hz : t = 0
  · have ht' : ¬ c₁.nreg 120012 < c₁.nreg 60010 := by
      rw [R₁ _ (by decide) (by decide) (by decide) (by decide), R₁ _ (by decide) (by decide)
        (by decide) (by decide), h0, ht, hz]; exact Nat.lt_irrefl 0
    exact ⟨_, _, .ifLtN_false ht' (Exec.constN w₁ 60011 1 hW), by omega, by config_simp; exact x12,
      by config_simp; exact x13, by config_simp; rw [ite_eq_left (Or.inl hz)]⟩
  · have ht' : c₁.nreg 120012 < c₁.nreg 60010 := by
      rw [R₁ _ (by decide) (by decide) (by decide) (by decide), R₁ _ (by decide) (by decide)
        (by decide) (by decide), h0, ht]; omega
    have hs' := hM.s_lt (t - 1) (by omega)
    obtain ⟨c₂, k₂, e₂, hk₂, n₂⟩ : ∃ c₂ k₂, Exec P W (block [.subN 60015 60010 120011,
        .addN 60015 60007 60015, .loadN 60015 60015, .addN 60016 60004 60015, .loadN 60018 60016,
        .addN 60016 60005 60015, .loadN 60019 60016]) c₁ c₂ k₂ ∧ k₂ = 7 ∧
        c₂.nreg = upd (upd (upd (upd c₁.nreg 60015 (s (t - 1))) 60016 (Z2 + s (t - 1))) 60018
          (P1 (s (t - 1)))) 60019 (P2 (s (t - 1))) := by
      have a7 : c₁.nreg 60007 = Sb := by rw [R₁ _ (by decide) (by decide) (by decide) (by decide), h7]
      have a4 : c₁.nreg 60004 = Z1 := by rw [R₁ _ (by decide) (by decide) (by decide) (by decide), h4]
      have a5 : c₁.nreg 60005 = Z2 := by rw [R₁ _ (by decide) (by decide) (by decide) (by decide), h5]
      have a10 : c₁.nreg 60010 = t := by
        rw [R₁ _ (by decide) (by decide) (by decide) (by decide), ht]
      have a11 : c₁.nreg 120011 = 1 := by
        rw [R₁ _ (by decide) (by decide) (by decide) (by decide), h1]
      have hmem : c₁.nmem = c.nmem :=
        (exec_frameB e₁ (B := BDB) (by decide)).2.2.1
      exec_block
      · config_simp; rw [a7, a10, a11]; omega
      · config_simp; rw [a7, a10, a11, a4, hmem, hM.s_eq _ (by omega)]; omega
      · config_simp; rw [a7, a10, a11, a5, hmem, hM.s_eq _ (by omega)]; omega
      · refine ⟨rfl, ?_⟩
        config_simp; rw [a7, a10, a11, a4, a5, hmem, hM.s_eq _ (by omega), hM.p1 _ hs', hM.p2 _ hs']
        funext r; simp only [upd]; split_ifs <;> first | omega
    have w₂ := e₂.wb_right
    have y12 : c₂.nreg 60012 = P1 (s t) := by rw [n₂]; config_simp; exact x12
    have y13 : c₂.nreg 60013 = P2 (s t) := by rw [n₂]; config_simp; exact x13
    have y18 : c₂.nreg 60018 = P1 (s (t - 1)) := by rw [n₂]; config_simp
    have y19 : c₂.nreg 60019 = P2 (s (t - 1)) := by rw [n₂]; config_simp
    by_cases e1 : P1 (s t) = P1 (s (t - 1))
    · have q1 : c₂.nreg 60012 = c₂.nreg 60018 := by rw [y12, y18, e1]
      by_cases e2 : P2 (s t) = P2 (s (t - 1))
      · have q2 : c₂.nreg 60013 = c₂.nreg 60019 := by rw [y13, y19, e2]
        exact ⟨_, _, .ifLtN_true ht' (.seq e₂ (ifEq_eq_exec q1 (ifEq_eq_exec q2
          (Exec.constN w₂ 60011 0 (Nat.zero_le _))))), by omega, by config_simp; exact y12,
          by config_simp; exact y13, by
            config_simp; rw [ite_eq_right (by rw [e1, e2]; simp [hz])]⟩
      · have q2 : c₂.nreg 60013 ≠ c₂.nreg 60019 := by rwa [y13, y19]
        obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (P := P) (W := W) (S := .instr (.constN 60011 0)) q2
          (Exec.constN w₂ 60011 1 hW)
        exact ⟨_, _, .ifLtN_true ht' (.seq e₂ (ifEq_eq_exec q1 e')), by omega,
          by config_simp; exact y12, by config_simp; exact y13, by
            config_simp; rw [ite_eq_left (Or.inr (fun h' => e2 (Prod.mk.inj h').2))]⟩
    · have q1 : c₂.nreg 60012 ≠ c₂.nreg 60018 := by rwa [y12, y18]
      obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (P := P) (W := W)
        (S := ifEq 60013 60019 (.instr (.constN 60011 0)) (.instr (.constN 60011 1))) q1
        (Exec.constN w₂ 60011 1 hW)
      exact ⟨_, _, .ifLtN_true ht' (.seq e₂ e'), by omega, by config_simp; exact y12,
        by config_simp; exact y13, by
          config_simp; rw [ite_eq_left (Or.inr (fun h' => e1 (Prod.mk.inj h').1))]⟩

/-! ## Saving the handles, the items, the sort -/

/-- Save the handles into band `bDecomp`. -/
def dSave : Stmt :=
  block [.copyN 60001 110072, .copyN 60002 110073, .copyN 60003 110074, .copyN 60004 110293,
    .copyN 60005 110294, .copyN 60006 110295]

/-- The item array `0 … n - 1` at the allocator (`30003`). -/
def itemS : Stmt :=
  .seq (block [.copyN 30003 9999, .addN 9999 9999 60006])
    (scatS 60020 60006 120011 60016 60017 (block [.addN 60016 30003 60020, .copyN 60017 60020]))

/-- The inputs of the sort and of the comparator. -/
def sortSet : Stmt :=
  block [.copyN 30004 60006, .copyN 115000 60004, .copyN 115001 60005, .copyN 115005 60006]

/-- **Save, build the items, sort them by their raw pairs.** -/
def dSort : Stmt :=
  .seq dSave (.seq itemS (.seq sortSet (.seq (SortR.sortStmt lexCmp)
    (.instr (.copyN 60007 30005)))))

/-- The bands written by `dSort` (besides the allocator). -/
def dBands : Finset ℕ := {bSort, bDecomp, bOPrep}

theorem dSort_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {CH1 CH2 nI Z1 Z2 n A₀ : ℕ} (h72 : c.nreg 110072 = CH1) (h73 : c.nreg 110073 = CH2)
    (h74 : c.nreg 110074 = nI) (h93 : c.nreg 110293 = Z1) (h94 : c.nreg 110294 = Z2)
    (h95 : c.nreg 110295 = n) (h1 : c.nreg 120011 = 1) (hAl : c.nreg 9999 = A₀)
    (hZ1 : Z1 + n ≤ A₀) (hZ2 : Z2 + n ≤ A₀)
    (hroom : A₀ + n + SortR.sortCost 20 n ≤ W) :
    ∃ c' k, Exec P W dSort c c' k ∧ k ≤ 7 * n + SortR.sortCost 20 n + 20 ∧
      FrameN dBands c c' ∧ A₀ + n ≤ c'.nreg ALLOC ∧
      c'.nreg ALLOC ≤ A₀ + n + SortR.sortCost 20 n ∧
      c'.nreg 60001 = CH1 ∧ c'.nreg 60002 = CH2 ∧ c'.nreg 60003 = nI ∧ c'.nreg 60004 = Z1 ∧
      c'.nreg 60005 = Z2 ∧ c'.nreg 60006 = n ∧
      A₀ + n ≤ c'.nreg 60007 ∧ c'.nreg 60007 + n ≤ c'.nreg 9999 ∧
      SortedSeq (fun i => (c.nmem (Z1 + i), c.nmem (Z2 + i))) (fun t => c'.nmem (c'.nreg 60007 + t)) n ∧
      (∀ i, i < n → ∃ t, t < n ∧ c'.nmem (c'.nreg 60007 + t) = i) ∧
      (∀ t, t < n → c'.nmem (c'.nreg 60007 + t) < n) := by
  -- 1. save
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W dSave c c₁ k₁ ∧ k₁ = 6 ∧
      c₁.nreg = upd (upd (upd (upd (upd (upd c.nreg 60001 CH1) 60002 CH2) 60003 nI) 60004 Z1)
        60005 Z2) 60006 n ∧ c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧
      c₁.output = c.output := by
    unfold dSave
    exec_block
    exact ⟨rfl, by config_simp; rw [h72, h73, h74, h93, h94, h95], rfl, rfl, rfl, rfl⟩
  -- 2. the items
  obtain ⟨c₂, k₂, e₂, hk₂, n₂, m₂, rr₂, rm₂, o₂⟩ : ∃ c₂ k₂, Exec P W
      (block [.copyN 30003 9999, .addN 9999 9999 60006]) c₁ c₂ k₂ ∧ k₂ = 2 ∧
      c₂.nreg = upd (upd c₁.nreg 30003 A₀) 9999 (A₀ + n) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    have w₁ := e₁.wb_right
    have a9 : c₁.nreg 9999 = A₀ := by rw [n₁]; config_simp; exact hAl
    have a6 : c₁.nreg 60006 = n := by rw [n₁]; config_simp
    exec_block
    · config_simp; rw [a9, a6]; omega
    · exact ⟨rfl, by config_simp; rw [a9, a6], rfl, rfl, rfl, rfl⟩
  have a30 : c₂.nreg 30003 = A₀ := by rw [n₂]; config_simp
  have a6 : c₂.nreg 60006 = n := by rw [n₂]; config_simp; rw [n₁]; config_simp
  have a11 : c₂.nreg 120011 = 1 := by rw [n₂]; config_simp; rw [n₁]; config_simp; exact h1
  obtain ⟨c₃, k₃, e₃, hk₃, r₃, rr₃, mm₃, rm₃, o₃, -⟩ := scatS_exec (P := P) (W := W)
    (ri := 60020) (rn := 60006) (r1 := 120011) (ra := 60016) (rv := 60017)
    (body := block [.addN 60016 30003 60020, .copyN 60017 60020])
    (B := fun r => decide (r = 60016 ∨ r = 60017)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (JK c₂ (fun r => decide (r = 30003)) A₀) A₀
    (fun d d' hJ hr hm => JK.stable (rs := [60020]) (fun r hr' => by
      simp only [decide_eq_true_eq] at hr'; subst hr'; decide) hJ
      (fun r a b => hr r a (by simpa using b)) hm)
    (n := n) (κ := 2) (fun i => A₀ + i) (fun i => i) (fun i _ => by omega)
    (fun i d hi hJ hwd hri => by
      have g30 : d.nreg 30003 = A₀ := by rw [hJ.1 _ (by decide), a30]
      obtain ⟨d', k, e, hk, v1, v2⟩ : ∃ d' k, Exec P W (block [.addN 60016 30003 60020,
          .copyN 60017 60020]) d d' k ∧ k = 2 ∧ d'.nreg 60016 = A₀ + i ∧ d'.nreg 60017 = i := by
        exec_block
        · rw [g30, hri]; omega
        · exact ⟨rfl, by config_simp; rw [g30, hri], by config_simp; exact hri⟩
      exact ⟨d', k, e, by omega, exec_frameB e (by decide), v1, v2⟩)
    e₂.wb_right (JK.refl _ _ _) a6 a11 (by omega)
  have R₃ : ∀ r, r ≠ 60016 → r ≠ 60017 → r ≠ 60020 → c₃.nreg r = c₂.nreg r := fun r a b c' =>
    r₃ r (by simp; omega) c'
  -- 3. the inputs of the sort
  obtain ⟨c₄, k₄, e₄, hk₄, n₄⟩ : ∃ c₄ k₄, Exec P W sortSet c₃ c₄ k₄ ∧ k₄ = 4 ∧
      c₄.nreg = upd (upd (upd (upd c₃.nreg 30004 n) 115000 Z1) 115001 Z2) 115005 n := by
    have w₃ := e₃.wb_right
    have b6 : c₃.nreg 60006 = n := by rw [R₃ _ (by decide) (by decide) (by decide), a6]
    have b4 : c₃.nreg 60004 = Z1 := by
      rw [R₃ _ (by decide) (by decide) (by decide), n₂]; config_simp; rw [n₁]; config_simp
    have b5 : c₃.nreg 60005 = Z2 := by
      rw [R₃ _ (by decide) (by decide) (by decide), n₂]; config_simp; rw [n₁]; config_simp
    unfold sortSet
    exec_block
    exact ⟨rfl, by config_simp; rw [b6, b4, b5]⟩
  have hm₄ : c₄.nmem = c₃.nmem :=
    (exec_frameB e₄ (B := fun r => decide (r = 30004 ∨ 115000 ≤ r ∧ r ≤ 115005)) (by decide)).2.2.1
  have R₄ : ∀ r, r ≠ 30004 → (r < 115000 ∨ 115005 < r) → c₄.nreg r = c₃.nreg r := fun r a b => by
    rw [n₄]; simp only [upd]; split_ifs <;> first | omega
  have g9 : c₄.nreg 9999 = A₀ + n := by
    rw [R₄ _ (by decide) (by decide), R₃ _ (by decide) (by decide) (by decide), n₂]; config_simp
  have g30 : c₄.nreg 30003 = A₀ := by
    rw [R₄ _ (by decide) (by decide), R₃ _ (by decide) (by decide) (by decide), a30]
  -- the items in memory
  have hitems : SortL.seg c₄.nmem (c₄.nreg 30003) (List.range n).length = List.range n := by
    rw [g30, List.length_range, hm₄, mm₃]
    unfold SortL.seg
    apply List.ext_getElem (by simp)
    intro t h1 h2
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at h1
    exact scat_at (g := fun i => A₀ + i) (f := fun i => i) h1 (fun j _ hj => by omega)
  -- 4. the sort
  have hW' : A₀ + n ≤ W := by have := SortR.sortCost_ge 20 n; omega
  have hmem₄ : ∀ a, a < A₀ → c₄.nmem a = c.nmem a := fun a ha => by
    rw [hm₄, mm₃, scat_below (fun i _ => by omega) ha, m₂, m₁]
  obtain ⟨c₅, k₅, e₅, hk₅, J₅, F₅, s₁, s₂, L', hseg, hperm, hpw⟩ := SortR.sortStmt_exec (P := P)
    (W := W) (lexCmp_ok (m₀ := c₄.nmem) (A₀ := A₀ + n) (B1 := Z1) (B2 := Z2) (K := n)
      (by omega) (by omega) (by have := SortR.sortCost_ge 20 n; omega) hW') (by decide)
    (fun a b d h h' => lexLe_trans _ _ _ _ _ _ _ h h') (lexLe_total _ _ _ _)
    e₄.wb_right ⟨by rw [n₄]; config_simp, by rw [n₄]; config_simp, by rw [n₄]; config_simp,
      fun _ _ => rfl⟩ (by rw [show ALLOC = 9999 from rfl, g9]; exact lexJ_stable _ _ _ _ _) (List.range n) hitems
    (by rw [n₄]; simp [upd]) (by rw [g30, show ALLOC = 9999 from rfl, g9, List.length_range]) (by rw [show ALLOC = 9999 from rfl, g9, List.length_range]; omega)
  rw [List.length_range] at hseg s₂ hk₅
  rw [show ALLOC = 9999 from rfl, g9] at s₁
  -- 5. the base of the sorted items
  have e₆ := Exec.copyN (P := P) e₅.wb_right 60007 30005
  set c₆ : Config := { c₅ with nreg := upd c₅.nreg 60007 (c₅.nreg 30005) } with hc₆
  have ex : Exec P W dSort c c₆ _ := .seq e₁ (.seq (.seq e₂ e₃) (.seq e₄ (.seq e₅ e₆)))
  have hF5 : ∀ r, bandOf r = 6 → c₅.nreg r = c₄.nreg r := fun r hr =>
    F₅.1 r (by simp [hr, bSort]) (by unfold ALLOC; intro h; rw [h] at hr; simp [bandOf] at hr)
  have v : ∀ r, 60001 ≤ r → r ≤ 60006 → c₆.nreg r = c₁.nreg r := fun r a b => by
    rw [hc₆]; config_simp; rw [upd_other _ _ _ (by omega), hF5 r (by unfold bandOf; omega),
      R₄ r (by omega) (by omega), R₃ r (by omega) (by omega) (by omega), n₂]
    rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
  have v7 : c₆.nreg 60007 = c₅.nreg 30005 := by rw [hc₆]; config_simp
  have hm₆ : c₆.nmem = c₅.nmem := rfl
  -- the sorted sequence
  have hsd : ∀ t, t < n → c₆.nmem (c₆.nreg 60007 + t) = L'.getD t 0 := fun t ht => by
    rw [hm₆, v7, ← hseg, SortL.seg_getD t ht]
  have hL'len : L'.length = n := by rw [← hseg, SortL.seg_length]
  have hmemL : ∀ t, t < n → L'.getD t 0 < n := fun t ht => by
    have : L'.getD t 0 ∈ L' := by rw [NFLoc.getD_of_lt 0 (by omega)]; exact List.getElem_mem _
    exact List.mem_range.1 (hperm.subset this)
  have g9' : c₄.nreg ALLOC = A₀ + n := g9
  have hAl' : c.nreg ALLOC = A₀ := hAl
  refine ⟨c₆, _, ex, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := SortR.sortCost_ge 20 n; omega
  · -- the frame
    have F14 : FrameN dBands c c₄ := by
      refine PF.frameN (B := fun r => decide (r = 9999) || decide (60001 ≤ r ∧ r ≤ 60020) ||
        decide (30003 ≤ r ∧ r ≤ 30004) || decide (115000 ≤ r ∧ r ≤ 115005))
        ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_⟩ (fun r hr => ?_) ?_
      · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
        rw [R₄ r (by omega) (by omega), R₃ r (by omega) (by omega) (by omega), n₂, n₁]
        simp only [upd]; split_ifs <;> first | omega
      · have := (exec_frameB e₄ (B := fun r => decide (r = 30004 ∨ 115000 ≤ r ∧ r ≤ 115005))
          (by decide)).2.1 r (by simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega)
        rw [this, rr₃ r (by simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega),
          rr₂, rr₁]
      · rw [hmem₄ a (by rwa [hAl'] at ha)]
      · rw [(exec_frameB e₄ (B := fun r => decide (r = 30004 ∨ 115000 ≤ r ∧ r ≤ 115005))
          (by decide)).2.2.2.1, rm₃, rm₂, rm₁]
      · rw [(exec_frameB e₄ (B := fun r => decide (r = 30004 ∨ 115000 ≤ r ∧ r ≤ 115005))
          (by decide)).2.2.2.2, o₃, o₂, o₁]
      · simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
        rcases hr with ((h | h) | h) | h
        · exact Or.inr h
        · left; simp [dBands, bDecomp, bandOf]; omega
        · left; simp [dBands, bSort, bandOf]; omega
        · left; simp [dBands, bOPrep, bandOf]; omega
      · have := (exec_frameB e₄ (B := fun r => decide (r = 30004 ∨ 115000 ≤ r ∧ r ≤ 115005))
          (by decide)).2.1 ALLOC (by decide)
        rw [this, rr₃ _ (by decide), rr₂, rr₁]
    have F56 : FrameN dBands c₅ c₆ :=
      Frame.toN (NFLoc.frame_of_frameB (exec_frameB e₆ (B := fun r => decide (r = 60007))
        (by decide)) (fun r hr => by
          simp at hr; subst hr; exact ⟨by simp [dBands, bDecomp, bandOf], by decide⟩) 1)
    exact (F14.trans (FrameN.mono (Frame.toN F₅) (by decide))
      (by rw [hAl', g9']; omega)).trans F56
      (by rw [hAl']; have := F₅.2.2.2.2.2.1; rw [g9'] at this; omega)
  · have := F₅.2.2.2.2.2.1; rw [g9'] at this
    rw [hc₆]; exact this
  · have := F₅.2.2.2.2.2.2; rw [g9'] at this
    rw [hc₆]; show c₅.nreg ALLOC ≤ _; omega
  · rw [v _ (by norm_num) (by norm_num), n₁]; config_simp
  · rw [v _ (by norm_num) (by norm_num), n₁]; config_simp
  · rw [v _ (by norm_num) (by norm_num), n₁]; config_simp
  · rw [v _ (by norm_num) (by norm_num), n₁]; config_simp
  · rw [v _ (by norm_num) (by norm_num), n₁]; config_simp
  · rw [v _ (by norm_num) (by norm_num), n₁]; config_simp
  · rwa [v7]
  · rw [v7, hc₆]; config_simp; exact s₂
  · -- sorted
    intro t t' htt ht'
    beta_reduce
    rw [hsd t (by omega), hsd t' ht']
    have hA := hmemL t (by omega)
    have hB := hmemL t' ht'
    have hc4 : ∀ i, i < n → c₄.nmem (Z1 + i) = c.nmem (Z1 + i) ∧ c₄.nmem (Z2 + i) = c.nmem (Z2 + i) :=
      fun i hi => ⟨hmem₄ _ (by omega), hmem₄ _ (by omega)⟩
    rcases eq_or_lt_of_le htt with h | h
    · subst h; right; exact ⟨rfl, le_rfl⟩
    · have := List.pairwise_iff_getElem.1 hpw t t' (by omega) (by omega) h
      rw [← NFLoc.getD_of_lt 0 (by omega), ← NFLoc.getD_of_lt 0 (by omega)] at this
      unfold lexLe at this
      rw [ite_eq_left hA, ite_eq_left hB] at this
      simp only [decide_eq_true_eq] at this
      rwa [(hc4 _ hA).1, (hc4 _ hB).1, (hc4 _ hA).2, (hc4 _ hB).2] at this
  · intro i hi
    have : i ∈ L' := hperm.symm.subset (List.mem_range.2 hi)
    obtain ⟨t, ht, e⟩ := List.getElem_of_mem this
    exact ⟨t, by omega, by rw [hsd t (by omega), NFLoc.getD_of_lt 0 ht, e]⟩
  · intro t ht; rw [hsd t ht]; exact hmemL t ht

/-- **The dedup emission** into the chord arrays. -/
def dEmit : Stmt := emitS 60010 60006 120011 60011 60012 60013 60001 60002 60003 60014 dBody

/-- The environment of the dedup emission. -/
def DEnv (Sb Z1 Z2 n : ℕ) (s P1 P2 : ℕ → ℕ) (d : Config) : Prop :=
  d.nreg 60004 = Z1 ∧ d.nreg 60005 = Z2 ∧ d.nreg 60007 = Sb ∧ d.nreg 120011 = 1 ∧
    d.nreg 120012 = 0 ∧ DMem d.nmem Sb Z1 Z2 n s P1 P2

theorem dEmit_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {CH1 CH2 nI Sb Z1 Z2 n : ℕ} {s P1 P2 : ℕ → ℕ} (hE : DEnv Sb Z1 Z2 n s P1 P2 c)
    (h1 : c.nreg 60001 = CH1) (h2 : c.nreg 60002 = CH2) (h3 : c.nreg 60003 = nI)
    (h6 : c.nreg 60006 = n) (hC : CH1 + nI + n ≤ CH2) (hZ : CH2 + nI + n ≤ Z1)
    (hZ12 : Z1 ≤ Z2) (hZS : Z2 ≤ Sb) (hSW : Sb + n ≤ W) :
    ∃ c' k, Exec P W dEmit c c' k ∧ k ≤ n * 40 + 3 ∧
      (∀ r, BDB r = false → r ≠ 60010 → r ≠ 60003 → r ≠ 60014 → c'.nreg r = c.nreg r) ∧
      (∀ r, BDB r = false → c'.rreg r = c.rreg r) ∧
      c'.nreg 60003 = nI + (emitted (dedupF n (fun i => (P1 i, P2 i)) s) n).length ∧
      PairsAt c'.nmem (CH1 + nI) (CH2 + nI) (emitted (dedupF n (fun i => (P1 i, P2 i)) s) n) ∧
      (∀ a, (a < CH1 + nI ∨ (CH1 + nI + (emitted (dedupF n (fun i => (P1 i, P2 i)) s) n).length ≤ a ∧
        a < CH2 + nI) ∨ CH2 + nI + (emitted (dedupF n (fun i => (P1 i, P2 i)) s) n).length ≤ a) →
        c'.nmem a = c.nmem a) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', k, ex, hk, r', rr', cnt, pr, mm, rm, o, -⟩ := emitS_exec (P := P) (W := W)
    (ri := 60010) (rn := 60006) (r1 := 120011) (rf := 60011) (rv1 := 60012) (rv2 := 60013)
    (rR1 := 60001) (rR2 := 60002) (rc := 60003) (rt := 60014) (body := dBody) (B := BDB)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (R1 := CH1) (R2 := CH2) (c₀ := nI) (n := n) (κ := 30) (DEnv Sb Z1 Z2 n s P1 P2)
    (fun d d' hJ hr hm => by
      obtain ⟨a4, a5, a7, a11, a12, hM⟩ := hJ
      refine ⟨by rw [hr _ (by decide) (by decide) (by decide) (by decide), a4],
        by rw [hr _ (by decide) (by decide) (by decide) (by decide), a5],
        by rw [hr _ (by decide) (by decide) (by decide) (by decide), a7],
        by rw [hr _ (by decide) (by decide) (by decide) (by decide), a11],
        by rw [hr _ (by decide) (by decide) (by decide) (by decide), a12], ⟨fun t ht => ?_,
        hM.s_lt, fun i hi => ?_, fun i hi => ?_⟩⟩
      · rw [hm _ (Or.inr (Or.inr (by omega)))]; exact hM.s_eq t ht
      · rw [hm _ (Or.inr (Or.inr (by omega)))]; exact hM.p1 i hi
      · rw [hm _ (Or.inr (Or.inr (by omega)))]; exact hM.p2 i hi)
    (dedupF n (fun i => (P1 i, P2 i)) s)
    (fun i d hi hJ hwd hri => by
      obtain ⟨a4, a5, a7, a11, a12, hM⟩ := hJ
      exact dBody_exec hwd hM a7 a4 a5 a11 a12 hri hi hSW (by omega) (by omega) (by omega))
    hw hE h6 hE.2.2.2.1 h1 h2 h3 hC (by omega)
  exact ⟨c', k, ex, by nlinarith, r', rr', cnt, pr, mm, rm, o⟩

end

end OracleR

end Chazelle.Core
