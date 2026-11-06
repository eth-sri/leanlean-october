module

public import Chazelle.Core.SortRam
public import Chazelle.Core.FuseAsmColl
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 4000000

/-!
# WP-F fusion assembly, part 5: a comparator of stored triples

`cmp3` compares the items `a, b < K` by the stored triples `(m (T + 3a), m (T + 3a + 1),
m (T + 3a + 2))` lexicographically (base `T` in `70216`, bound `K` in `70217`); items `≥ K` come
after, in their natural order (`le3`).  `cmp3_ok`: its contract `SortR.CmpOK` (band `bFuse`,
registers `70210 … 70215`).
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- The stored triple of item `a`. -/
def trip (m : ℕ → ℕ) (T a : ℕ) : ℕ × ℕ × ℕ := (m (T + 3 * a), m (T + 3 * a + 1), m (T + 3 * a + 2))

/-- The lexicographic order of triples. -/
def tle (x y : ℕ × ℕ × ℕ) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ (x.2.1 < y.2.1 ∨ (x.2.1 = y.2.1 ∧ x.2.2 ≤ y.2.2)))

instance (x y : ℕ × ℕ × ℕ) : Decidable (tle x y) := by unfold tle; infer_instance

theorem tle_antisymm {x y : ℕ × ℕ × ℕ} (h1 : tle x y) (h2 : tle y x) : x = y := by
  obtain ⟨a, b, c⟩ := x; obtain ⟨d, e, f⟩ := y
  unfold tle at h1 h2; simp only at h1 h2
  have : a = d ∧ b = e ∧ c = f := by omega
  obtain ⟨rfl, rfl, rfl⟩ := this; rfl

/-- The order of the items. -/
def le3 (m : ℕ → ℕ) (T K a b : ℕ) : Bool :=
  if a < K then (if b < K then decide (tle (trip m T a) (trip m T b)) else true)
  else (if b < K then false else decide (a ≤ b))

theorem le3_total (m : ℕ → ℕ) (T K a b : ℕ) : (le3 m T K a b || le3 m T K b a) = true := by
  unfold le3 tle
  split_ifs <;> simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.or_true,
    Bool.or_false] <;> omega

theorem le3_trans (m : ℕ → ℕ) (T K a b c : ℕ) (h1 : le3 m T K a b = true)
    (h2 : le3 m T K b c = true) : le3 m T K a c = true := by
  unfold le3 tle at *
  split_ifs at h1 h2 ⊢ <;> simp only [decide_eq_true_eq] at h1 h2 ⊢ <;> omega

/-- Load the triples of the two items into `70210 … 70215`. -/
def ld3 : Stmt := block [.addN 70210 30000 30000, .addN 70210 70210 30000,
  .addN 70210 70210 70216, .loadN 70211 70210, .constN 70215 1, .addN 70210 70210 70215,
  .loadN 70212 70210, .addN 70210 70210 70215, .loadN 70213 70210,
  .addN 70210 30001 30001, .addN 70210 70210 30001, .addN 70210 70210 70216,
  .loadN 70214 70210, .addN 70210 70210 70215, .loadN 70215 70210]

/-- The comparison of two loaded triples: `(70211, 70212, 70213)` against `(70214, 70215, ·)`,
the third component of `b` loaded on demand. -/
def cmpT : Stmt :=
  .ifLtN 70211 70214 (.instr (.constN 30002 1))
    (.ifLtN 70214 70211 (.instr (.constN 30002 0))
      (.ifLtN 70212 70215 (.instr (.constN 30002 1))
        (.ifLtN 70215 70212 (.instr (.constN 30002 0))
          (.seq (block [.addN 70210 30001 30001, .addN 70210 70210 30001,
              .addN 70210 70210 70216, .constN 70214 2, .addN 70210 70210 70214,
              .loadN 70214 70210])
            (.ifLtN 70214 70213 (.instr (.constN 30002 0)) (.instr (.constN 30002 1)))))))

/-- **The comparator.** -/
def cmp3 : Stmt :=
  .ifLtN 30000 70217
    (.ifLtN 30001 70217 (.seq ld3 cmpT) (.instr (.constN 30002 1)))
    (.ifLtN 30001 70217 (.instr (.constN 30002 0))
      (.ifLtN 30001 30000 (.instr (.constN 30002 0)) (.instr (.constN 30002 1))))

/-- The invariant of the comparator: the base, the bound and the memory below `A₀`. -/
def Cmp3J (m₀ : ℕ → ℕ) (A₀ T K : ℕ) (g : ℕ → ℕ) (c : Config) : Prop :=
  c.nreg 70216 = T ∧ c.nreg 70217 = K ∧ (∀ a, a < A₀ → c.nmem a = m₀ a) ∧
    ∀ r, 70000 ≤ r → r < 70105 → c.nreg r = g r

theorem cmp3J_stable (m₀ : ℕ → ℕ) (A₀ T K : ℕ) (g : ℕ → ℕ) :
    SortR.JStable (Cmp3J m₀ A₀ T K g) A₀ := by
  intro c c' ⟨h1, h2, h3, h4⟩ hr _ hm _ _
  have hb : ∀ r, 70000 ≤ r → r < 80000 → c'.nreg r = c.nreg r := fun r a b =>
    hr r (by ufo bandOf bSort) (by ufo ALLOC)
  exact ⟨by rwx [hb _ (by norm_num) (by norm_num)],
    by rwx [hb _ (by norm_num) (by norm_num)], fun a ha => (hm a ha).trans (h3 a ha),
    fun r a b => by rw [hb r a (by omega)]; exact h4 r a b⟩

theorem ld3_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {T a b : ℕ}
    (hT : c.nreg 70216 = T) (ha : c.nreg 30000 = a) (hb : c.nreg 30001 = b)
    (haW : T + 3 * a + 2 ≤ W) (hbW : T + 3 * b + 2 ≤ W) :
    ∃ c' k, Exec P W ld3 c c' k ∧ k = 15 ∧
      c'.nreg 70211 = c.nmem (T + 3 * a) ∧ c'.nreg 70212 = c.nmem (T + 3 * a + 1) ∧
      c'.nreg 70213 = c.nmem (T + 3 * a + 2) ∧ c'.nreg 70214 = c.nmem (T + 3 * b) ∧
      c'.nreg 70215 = c.nmem (T + 3 * b + 1) ∧
      (∀ r, (r < 70210 ∨ 70215 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ld3
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hT, ha, hb]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hT, ha, hb]
  all_goals first | rfl | (congr 1; ring)

theorem cmpT_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W)
    {T b x0 x1 x2 y0 y1 : ℕ} (hT : c.nreg 70216 = T) (hb : c.nreg 30001 = b)
    (hbW : T + 3 * b + 2 ≤ W) (h11 : c.nreg 70211 = x0) (h12 : c.nreg 70212 = x1)
    (h13 : c.nreg 70213 = x2) (h14 : c.nreg 70214 = y0) (h15 : c.nreg 70215 = y1) :
    ∃ c' k, Exec P W cmpT c c' k ∧ k ≤ 18 ∧
      c'.nreg 30002 = (if tle (x0, x1, x2) (y0, y1, c.nmem (T + 3 * b + 2)) then 1 else 0) ∧
      (∀ r, r ≠ 30002 → (r < 70210 ∨ 70215 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cmpT tle
  by_cases c1 : x0 < y0
  · refine spec_ifLtN_true (by rwx [h11, h14]) (spec_instr (Exec.constN hw _ _ hW)
      fun _ => ⟨by omega, by simp [c1], fun r hr _ => by simp [hr], rfl, rfl, rfl, rfl⟩)
  refine spec_ifLtN_false (by rwx [h11, h14]) ?_
  by_cases c2 : y0 < x0
  · refine spec_ifLtN_true (by rwx [h11, h14]) (spec_instr (Exec.constN hw _ _
      (Nat.zero_le _)) fun _ => ⟨by omega, ?_, fun r hr _ => by simp [hr], rfl, rfl, rfl, rfl⟩)
    simp only [upd_same]; rwo [ite_eq_right]
  refine spec_ifLtN_false (by rwx [h11, h14]) ?_
  by_cases c3 : x1 < y1
  · refine spec_ifLtN_true (by rwx [h12, h15]) (spec_instr (Exec.constN hw _ _ hW)
      fun _ => ⟨by omega, ?_, fun r hr _ => by simp [hr], rfl, rfl, rfl, rfl⟩)
    simp only [upd_same]; rwo [ite_eq_left]
  refine spec_ifLtN_false (by rwx [h12, h15]) ?_
  by_cases c4 : y1 < x1
  · refine spec_ifLtN_true (by rwx [h12, h15]) (spec_instr (Exec.constN hw _ _
      (Nat.zero_le _)) fun _ => ⟨by omega, ?_, fun r hr _ => by simp [hr], rfl, rfl, rfl, rfl⟩)
    simp only [upd_same]; rwo [ite_eq_right]
  refine spec_ifLtN_false (by rwx [h12, h15]) ?_
  obtain ⟨c₁, k₁, e₁, hk₁, v14, v13, r₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 70210 30001 30001, .addN 70210 70210 30001, .addN 70210 70210 70216,
        .constN 70214 2, .addN 70210 70210 70214, .loadN 70214 70210]) c c₁ k₁ ∧ k₁ = 6 ∧
      c₁.nreg 70214 = c.nmem (T + 3 * b + 2) ∧ c₁.nreg 70213 = x2 ∧
      (∀ r, (r < 70210 ∨ 70215 < r) → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hT, hb]; omega)
    refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hT, hb, h13]
    congr 1; ring
  have w₁ := e₁.wb_right
  refine spec_seq ⟨c₁, k₁, e₁, ?_⟩
  by_cases c5 : c.nmem (T + 3 * b + 2) < x2
  · refine spec_ifLtN_true (by rwx [v14, v13]) (spec_instr (Exec.constN w₁ _ _
      (Nat.zero_le _)) fun _ => ⟨by omega, ?_, fun r hr hr' => ?_, by rw [m₁], by rw [rr₁],
        by rw [rm₁], by rw [o₁]⟩)
    · simp only [upd_same]; rwo [ite_eq_right]
    · simp only [upd_other _ _ _ hr]; exact r₁ r hr'
  · refine spec_ifLtN_false (by rwx [v14, v13]) (spec_instr (Exec.constN w₁ _ _ hW)
      fun _ => ⟨by omega, ?_, fun r hr hr' => ?_, by rw [m₁], by rw [rr₁], by rw [rm₁],
        by rw [o₁]⟩)
    · simp only [upd_same]; rwo [ite_eq_left]
    · simp only [upd_other _ _ _ hr]; exact r₁ r hr'

/-- **The contract of the comparator.** -/
theorem cmp3_ok {P : Polygon} {W : ℕ} {m₀ : ℕ → ℕ} {A₀ T K : ℕ} {g : ℕ → ℕ} (hTK : T + 3 * K ≤ A₀)
    (hW : 1 ≤ W) (hAW : A₀ ≤ W) :
    SortR.CmpOK P W cmp3 {bFuse} (Cmp3J m₀ A₀ T K g) (le3 m₀ T K) 40 := by
  intro c hw ⟨j1, j2, j3, j4⟩
  have hwr : wr (fun r => decide (r = 30002) || decide (70210 ≤ r ∧ r ≤ 70215)) cmp3 = true := by
    decide
  suffices H : ∃ c' k, Exec P W cmp3 c c' k ∧ k ≤ 40 ∧
      c'.nreg 30002 = (if le3 m₀ T K (c.nreg 30000) (c.nreg 30001) then 1 else 0) by
    obtain ⟨c', k, ex, hk, hbit⟩ := H
    have f := exec_frameB ex hwr
    have fr := WalkKey.exec_rframe ex (B := fun _ => false) (by decide)
    refine ⟨c', k, ex, hk, ⟨?_, ?_, fun a ha => by rw [f.2.2.1]; exact j3 a ha,
      fun r a b => by rw [f.1 r (by sio only [Bool.or_eq_false_iff, decide_eq_false_iff_not])]
                      exact j4 r a b⟩, hbit,
      fun r h0 h1 h2 hb => f.1 r ?_, fun r _ => fr r rfl, f.2.2.1, f.2.2.2.1, f.2.2.2.2⟩
    · rwx [f.1 _ (by decide)]
    · rwx [f.1 _ (by decide)]
    · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      refine ⟨h2, fun h => ?_⟩
      rcases hb with hb | hb
      · exact hb (by ruo [Finset.mem_singleton] bandOf bFuse)
      · ufo ALLOC at hb
  have h1  := j2
  unfold cmp3 le3
  by_cases ha : c.nreg 30000 < K
  · refine spec_ifLtN_true (by rwx [h1]) ?_
    by_cases hb : c.nreg 30001 < K
    · refine spec_ifLtN_true (by rwx [h1]) ?_
      obtain ⟨a, ha'⟩ : ∃ a, c.nreg 30000 = a := ⟨_, rfl⟩
      obtain ⟨b, hb'⟩ : ∃ b, c.nreg 30001 = b := ⟨_, rfl⟩
      have haK  := ha' ▸ ha
      have hbK  := hb' ▸ hb
      obtain ⟨c₁, k₁, e₁, hk₁, v11, v12, v13, v14, v15, r₁, m₁, -, -, -⟩ :=
        ld3_exec (P := P) c hw j1 ha' hb' (by omega) (by omega)
      obtain ⟨c₂, k₂, e₂, hk₂, v2, -⟩ := cmpT_exec (P := P) (T := T) (b := b) c₁ e₁.wb_right hW
        ((r₁ _ (by omega)).trans j1) ((r₁ _ (by omega)).trans hb') (by omega)
        v11 v12 v13 v14 v15
      refine ⟨c₂, _, .seq e₁ e₂, by omega, ?_⟩
      rw [v2, m₁, j3 _ (by omega), j3 _ (by omega), j3 _ (by omega), j3 _ (by omega),
        j3 _ (by omega), j3 _ (by omega), ha', hb']
      by_cases ht : tle (m₀ (T + 3 * a), m₀ (T + 3 * a + 1), m₀ (T + 3 * a + 2))
          (m₀ (T + 3 * b), m₀ (T + 3 * b + 1), m₀ (T + 3 * b + 2))
      · have ht' : tle (trip m₀ T a) (trip m₀ T b) := ht
        simp [haK, hbK, ht, ht']
      · have ht' : ¬ tle (trip m₀ T a) (trip m₀ T b) := ht
        simp [haK, hbK, ht, ht']
    · refine spec_ifLtN_false (by rwx [h1]) (spec_instr (Exec.constN hw _ _ hW)
        fun _ => ⟨by omega, ?_⟩)
      simp [ha, hb]
  · refine spec_ifLtN_false (by rwx [h1]) ?_
    by_cases hb : c.nreg 30001 < K
    · refine spec_ifLtN_true (by rwx [h1]) (spec_instr (Exec.constN hw _ _ (by omega))
        fun _ => ⟨by omega, ?_⟩)
      simp [ha, hb]
    · refine spec_ifLtN_false (by rwx [h1]) ?_
      by_cases hc : c.nreg 30001 < c.nreg 30000
      · refine spec_ifLtN_true hc (spec_instr (Exec.constN hw _ _ (by omega)) fun _ =>
          ⟨by omega, ?_⟩)
        sio [ha, hb]
      · refine spec_ifLtN_false hc (spec_instr (Exec.constN hw _ _ hW) fun _ => ⟨by omega, ?_⟩)
        sio [ha, hb]

end

end FuseAsm

end Chazelle.Core
