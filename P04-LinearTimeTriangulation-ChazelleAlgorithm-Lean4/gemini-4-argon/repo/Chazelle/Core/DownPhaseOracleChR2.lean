module

public import Chazelle.Core.DownPhaseOracleChR

/-!
# WP-M (E7-B, RAM part 6): the orientation bit of the chain of a stretch

`betaI` computes the orientation bit `sideBeta` of the chain of a stretch into `170075`: `0`
if the top is its first vertex, else, with `A`, `v`, `B` the vertices of `Q` before, at and after
the top (`nbrI`, indices modulo `n`), six sign tests (`testsI`) and a decision tree (`logI`)
following `BetaF` (`sideBeta_ch`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey Brute SweepPrim

@[expose] public section

/-! ## The programs -/

/-- The neighbours of the top: `170080 := (v + n - 1) mod n`, `170081 := (v + 1) mod n`. -/
def nbrI : Stmt :=
  .seq (block [.addN 170080 170079 170019, .addN 170081 170079 170011])
    (.seq (.ifLtN 170080 170010 .skip (block [.subN 170080 170080 170010]))
      (.ifLtN 170081 170010 .skip (block [.constN 170081 0])))

/-- The six sign tests. -/
def testsI : Stmt :=
  .seq (testS 2 (.v 170080) (.v 170079) (.v 170081) 170082)
  (.seq (testS 3 (.v 170080) (.v 170079) (.v 170081) 170083)
  (.seq (testS 0 (.v 170079) (.v 170081) (.v 170079) 170085)
  (.seq (testS 0 (.v 170080) (.v 170079) (.v 170080) 170086)
  (.seq (testS 1 (.v 170079) (.v 170081) (.v 170079) 170087)
  (testS 1 (.v 170081) (.v 170079) (.v 170081) 170088)))))

/-- `170075 := v`. -/
def setB (v : ℕ) : Stmt := block [.constN 170075 v]

/-- The decision tree of `BetaF`. -/
def logI : Stmt :=
  .ifLtN 170012 170083
    (.ifLtN 170012 170088 (setB 1)
      (.ifLtN 170012 170087 (.ifLtN 170012 170085 (setB 1) (setB 0)) (setB 0)))
    (.ifLtN 170012 170082
      (.ifLtN 170012 170085 (.ifLtN 170012 170086 (setB 1) (setB 0)) (setB 0))
      (.ifLtN 170012 170085 (setB 1) (.ifLtN 170012 170086 (setB 1) (setB 0))))

/-- **The orientation bit.** -/
def betaI : Stmt := .ifLtN 170012 170074 (.seq nbrI (.seq testsI logI)) (setB 0)

/-- The registers `betaI` writes. -/
def Bbeta (r : ℕ) : Bool := decide (r = 170075) || decide (170080 ≤ r ∧ r < 170089) || Bk r

theorem wr_betaI : wr Bbeta betaI = true := by
  have hsp : wr Bbeta signProg = true :=
    SweepPrim.wr_mono SweepPrim.wr_signProg (fun r hr => by simp [Bbeta, hr])
  have ht : ∀ op x y z d, 170080 ≤ d → d < 170089 → wr Bbeta (testS op x y z d) = true := by
    intro op x y z d h1 h2
    cases x <;> cases y <;> cases z <;>
      simp only [testS, Src.load, wr, block, wrOK, hsp, Bool.and_true, Bool.true_and] <;>
      simp [Bbeta, Bk] <;> omega
  simp only [betaI, nbrI, testsI, logI, setB, wr, block, wrOK, ht _ _ _ _ 170082 (by norm_num)
    (by norm_num), ht _ _ _ _ 170083 (by norm_num) (by norm_num), ht _ _ _ _ 170085 (by norm_num)
    (by norm_num), ht _ _ _ _ 170086 (by norm_num) (by norm_num), ht _ _ _ _ 170087 (by norm_num)
    (by norm_num), ht _ _ _ _ 170088 (by norm_num) (by norm_num), Bool.and_true, Bool.true_and]
  decide

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

theorem setB_exec (c : Config) (hw : WordsBounded W c) (v : ℕ) (hv : v ≤ 1) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W (setB v) c c' k ∧ k = 1 ∧
      c' = { c with nreg := upd c.nreg 170075 v } := by
  unfold setB
  exec_block
  · omega
  exact ⟨rfl, rfl⟩

/-- **The decision tree** of `BetaF` on six bits. -/
theorem logI_exec (c : Config) (hw : WordsBounded W c) (h12 : c.nreg 170012 = 0) (hW : 1 ≤ W)
    {pp p0 bx ax by' by'' : Prop} (hpp : BitIs c 170082 pp) (hp0 : BitIs c 170083 p0)
    (hbx : BitIs c 170085 bx) (hax : BitIs c 170086 ax) (hby : BitIs c 170087 by')
    (hby' : BitIs c 170088 by'') (hcons : p0 → ¬ pp) :
    ∃ c' k, Exec P W logI c c' k ∧ k ≤ 12 ∧ ∃ b, b ≤ 1 ∧
      c' = { c with nreg := upd c.nreg 170075 b } ∧
      (b = 1 ↔ (pp ∧ bx ∧ ax) ∨ (¬ pp ∧ ¬ p0 ∧ (bx ∨ ax)) ∨ (p0 ∧ by' ∧ bx) ∨
        (p0 ∧ by'')) := by
  obtain ⟨hpp1, hpp2⟩ := hpp
  obtain ⟨hp01, hp02⟩ := hp0
  obtain ⟨hbx1, hbx2⟩ := hbx
  obtain ⟨hax1, hax2⟩ := hax
  obtain ⟨hby1, hby2⟩ := hby
  obtain ⟨hby'1, hby'2⟩ := hby'
  have t : ∀ r, c.nreg r ≤ 1 → (c.nreg 170012 < c.nreg r ↔ c.nreg r = 1) := fun r hr => by
    rw [h12]; omega
  have one : ∀ {Φ : Prop}, Φ → ((1 : ℕ) = 1 ↔ Φ) := fun h => iff_of_true rfl h
  have zero : ∀ {Φ : Prop}, ¬ Φ → ((0 : ℕ) = 1 ↔ Φ) := fun h => iff_of_false (by norm_num) h
  unfold logI
  by_cases g0 : c.nreg 170012 < c.nreg 170083
  · have q0 : p0 := hp02.1 ((t _ hp01).1 g0)
    have q0' : ¬ pp := hcons q0
    refine spec_ifLtN_true g0 ?_
    by_cases g1 : c.nreg 170012 < c.nreg 170088
    · have q1 : by'' := hby'2.1 ((t _ hby'1).1 g1)
      refine spec_ifLtN_true g1 ?_
      obtain ⟨c', k, e, hk, rfl⟩ := setB_exec (P := P) c hw 1 le_rfl hW
      exact ⟨_, _, e, by omega, 1, le_rfl, rfl, one (Or.inr (Or.inr (Or.inr ⟨q0, q1⟩)))⟩
    · have q1 : ¬ by'' := fun h => g1 ((t _ hby'1).2 (hby'2.2 h))
      refine spec_ifLtN_false g1 ?_
      by_cases g2 : c.nreg 170012 < c.nreg 170087
      · have q2 : by' := hby2.1 ((t _ hby1).1 g2)
        refine spec_ifLtN_true g2 ?_
        by_cases g3 : c.nreg 170012 < c.nreg 170085
        · have q3 : bx := hbx2.1 ((t _ hbx1).1 g3)
          refine spec_ifLtN_true g3 ?_
          obtain ⟨c', k, e, hk, rfl⟩ := setB_exec (P := P) c hw 1 le_rfl hW
          exact ⟨_, _, e, by omega, 1, le_rfl, rfl, one (Or.inr (Or.inr (Or.inl ⟨q0, q2, q3⟩)))⟩
        · have q3 : ¬ bx := fun h => g3 ((t _ hbx1).2 (hbx2.2 h))
          refine spec_ifLtN_false g3 ?_
          obtain ⟨c', k, e, hk, rfl⟩ := setB_exec (P := P) c hw 0 (by norm_num) hW
          refine ⟨_, _, e, by omega, 0, by norm_num, rfl, zero ?_⟩
          rintro (⟨a1, -, -⟩ | ⟨-, a2, -⟩ | ⟨-, -, a3⟩ | ⟨-, a4⟩)
          exacts [q0' a1, a2 q0, q3 a3, q1 a4]
      · have q2 : ¬ by' := fun h => g2 ((t _ hby1).2 (hby2.2 h))
        refine spec_ifLtN_false g2 ?_
        obtain ⟨c', k, e, hk, rfl⟩ := setB_exec (P := P) c hw 0 (by norm_num) hW
        refine ⟨_, _, e, by omega, 0, by norm_num, rfl, zero ?_⟩
        rintro (⟨a1, -, -⟩ | ⟨-, a2, -⟩ | ⟨-, a3, -⟩ | ⟨-, a4⟩)
        exacts [q0' a1, a2 q0, q2 a3, q1 a4]
  · have q0 : ¬ p0 := fun h => g0 ((t _ hp01).2 (hp02.2 h))
    refine spec_ifLtN_false g0 ?_
    by_cases g1 : c.nreg 170012 < c.nreg 170082
    · have q1 : pp := hpp2.1 ((t _ hpp1).1 g1)
      refine spec_ifLtN_true g1 ?_
      by_cases g2 : c.nreg 170012 < c.nreg 170085
      · have q2 : bx := hbx2.1 ((t _ hbx1).1 g2)
        refine spec_ifLtN_true g2 ?_
        by_cases g3 : c.nreg 170012 < c.nreg 170086
        · have q3 : ax := hax2.1 ((t _ hax1).1 g3)
          refine spec_ifLtN_true g3 ?_
          obtain ⟨c', k, e, hk, rfl⟩ := setB_exec (P := P) c hw 1 le_rfl hW
          exact ⟨_, _, e, by omega, 1, le_rfl, rfl, one (Or.inl ⟨q1, q2, q3⟩)⟩
        · have q3 : ¬ ax := fun h => g3 ((t _ hax1).2 (hax2.2 h))
          refine spec_ifLtN_false g3 ?_
          obtain ⟨c', k, e, hk, rfl⟩ := setB_exec (P := P) c hw 0 (by norm_num) hW
          refine ⟨_, _, e, by omega, 0, by norm_num, rfl, zero ?_⟩
          rintro (⟨-, -, a1⟩ | ⟨a2, -, -⟩ | ⟨a3, -, -⟩ | ⟨a4, -⟩)
          exacts [q3 a1, a2 q1, q0 a3, q0 a4]
      · have q2 : ¬ bx := fun h => g2 ((t _ hbx1).2 (hbx2.2 h))
        refine spec_ifLtN_false g2 ?_
        obtain ⟨c', k, e, hk, rfl⟩ := setB_exec (P := P) c hw 0 (by norm_num) hW
        refine ⟨_, _, e, by omega, 0, by norm_num, rfl, zero ?_⟩
        rintro (⟨-, a1, -⟩ | ⟨a2, -, -⟩ | ⟨a3, -, -⟩ | ⟨a4, -⟩)
        exacts [q2 a1, a2 q1, q0 a3, q0 a4]
    · have q1 : ¬ pp := fun h => g1 ((t _ hpp1).2 (hpp2.2 h))
      refine spec_ifLtN_false g1 ?_
      by_cases g2 : c.nreg 170012 < c.nreg 170085
      · have q2 : bx := hbx2.1 ((t _ hbx1).1 g2)
        refine spec_ifLtN_true g2 ?_
        obtain ⟨c', k, e, hk, rfl⟩ := setB_exec (P := P) c hw 1 le_rfl hW
        exact ⟨_, _, e, by omega, 1, le_rfl, rfl, one (Or.inr (Or.inl ⟨q1, q0, Or.inl q2⟩))⟩
      · have q2 : ¬ bx := fun h => g2 ((t _ hbx1).2 (hbx2.2 h))
        refine spec_ifLtN_false g2 ?_
        by_cases g3 : c.nreg 170012 < c.nreg 170086
        · have q3 : ax := hax2.1 ((t _ hax1).1 g3)
          refine spec_ifLtN_true g3 ?_
          obtain ⟨c', k, e, hk, rfl⟩ := setB_exec (P := P) c hw 1 le_rfl hW
          exact ⟨_, _, e, by omega, 1, le_rfl, rfl, one (Or.inr (Or.inl ⟨q1, q0, Or.inr q3⟩))⟩
        · have q3 : ¬ ax := fun h => g3 ((t _ hax1).2 (hax2.2 h))
          refine spec_ifLtN_false g3 ?_
          obtain ⟨c', k, e, hk, rfl⟩ := setB_exec (P := P) c hw 0 (by norm_num) hW
          refine ⟨_, _, e, by omega, 0, by norm_num, rfl, zero ?_⟩
          rintro (⟨a1, -, -⟩ | ⟨-, -, a2⟩ | ⟨a3, -, -⟩ | ⟨a4, -⟩)
          exacts [q1 a1, a2.elim q2 q3, q0 a3, q0 a4]

/-- **The neighbours of the top.** -/
theorem nbrI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {v : ℕ}
    (hv : c.nreg 170079 = v) (hvn : v < P.n) :
    ∃ c' k, Exec P W nbrI c c' k ∧ k ≤ 8 ∧ c'.nreg 170080 = (v + P.n - 1) % P.n ∧
      c'.nreg 170081 = (v + 1) % P.n ∧ c'.nmem = c.nmem ∧
      (∀ r, r ≠ 170080 → r ≠ 170081 → c'.nreg r = c.nreg r) := by
  have hW := hS.hW
  unfold hostWords at hW
  have hn := hS.n3
  unfold nbrI
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hv, hS.r19]; omega
  · config_simp; rw [hv, hS.r11]; omega
  refine spec_seq ?_
  have hA : (v + (P.n - 1)) % P.n = (v + P.n - 1) % P.n := by congr 1; omega
  by_cases h1 : v + (P.n - 1) < P.n
  · refine spec_ifLtN_true (by config_simp; rwa [hv, hS.r19, hS.r10]) ?_
    refine spec_skip ‹_› ?_
    by_cases h2 : v + 1 < P.n
    · refine spec_ifLtN_true (by config_simp; rwa [hv, hS.r11, hS.r10]) ?_
      refine spec_skip ‹_› ⟨by omega, ?_, ?_, rfl, fun r h1 h2 => ?_⟩
      · config_simp; rw [hv, hS.r19, ← hA, Nat.mod_eq_of_lt h1]
      · config_simp; rw [hv, hS.r11, Nat.mod_eq_of_lt h2]
      · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
    · refine spec_ifLtN_false (by config_simp; rwa [hv, hS.r11, hS.r10]) ?_
      exec_block
      · omega
      refine ⟨by omega, ?_, ?_, rfl, fun r h1 h2 => ?_⟩
      · config_simp; rw [hv, hS.r19, ← hA, Nat.mod_eq_of_lt h1]
      · config_simp; rw [show v + 1 = P.n by omega, Nat.mod_self]
      · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
  · refine spec_ifLtN_false (by config_simp; rwa [hv, hS.r19, hS.r10]) ?_
    exec_block
    by_cases h2 : v + 1 < P.n
    · refine spec_ifLtN_true (by config_simp; rwa [hv, hS.r11, hS.r10]) ?_
      refine spec_skip ‹_› ⟨by omega, ?_, ?_, rfl, fun r h1 h2 => ?_⟩
      · config_simp; rw [hv, hS.r19, hS.r10, ← hA, Nat.mod_eq_sub_mod (by omega),
          Nat.mod_eq_of_lt (by omega)]
      · config_simp; rw [hv, hS.r11, Nat.mod_eq_of_lt h2]
      · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
    · refine spec_ifLtN_false (by config_simp; rwa [hv, hS.r11, hS.r10]) ?_
      exec_block
      · omega
      refine ⟨by omega, ?_, ?_, rfl, fun r h1 h2 => ?_⟩
      · config_simp; rw [hv, hS.r19, hS.r10, ← hA, Nat.mod_eq_sub_mod (by omega),
          Nat.mod_eq_of_lt (by omega)]
      · config_simp; rw [show v + 1 = P.n by omega, Nat.mod_self]
      · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega

/-- One test of `testsI`: the bit, and the other registers outside the kernel. -/
theorem test1 {op : ℕ} (hop : op ≤ 3) (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {a b d dst : ℕ}
    (ha : 10500 ≤ a) (hb : 10500 ≤ b) (hd : 10500 ≤ d) (hdst : 10500 ≤ dst) (c : Config)
    (hw : WordsBounded W c) (hla : c.nreg a < P.n) (hlb : c.nreg b < P.n) (hld : c.nreg d < P.n) :
    ∃ c' k, Exec P W (testS op (.v a) (.v b) (.v d) dst) c c' k ∧ k ≤ 245 ∧
      BitIs c' dst (SignTest op ((Qof P).vtx (c.nreg a)) ((Qof P).vtx (c.nreg b))
        ((Qof P).vtx (c.nreg d))) ∧
      (∀ r, r ≠ dst → (r < 10000 ∨ 10500 ≤ r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, F, b1, b2⟩ := testS_exec hG hW hop (x := .v a) (y := .v b) (z := .v d)
    (d := dst) (by simp only [Src.Out]; omega) (by simp only [Src.Out]; omega)
    (by simp only [Src.Out]; omega) c hw hla hlb hld
  refine ⟨c', k, e, hk, ⟨b1, b2⟩, fun r h1 h2 => F.1 r ?_, F.2.2.1⟩
  unfold Bt Bk; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega

/-- **The six sign tests.** -/
theorem testsI_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W)
    {A v B : ℕ} (hA : c.nreg 170080 = A) (hv : c.nreg 170079 = v) (hB : c.nreg 170081 = B)
    (hAn : A < P.n) (hvn : v < P.n) (hBn : B < P.n) :
    ∃ c' k, Exec P W testsI c c' k ∧ k ≤ 1470 ∧
      BitIs c' 170082 (0 < det ((Qof P).vtx A) ((Qof P).vtx v) ((Qof P).vtx B)) ∧
      BitIs c' 170083 (det ((Qof P).vtx A) ((Qof P).vtx v) ((Qof P).vtx B) = 0) ∧
      BitIs c' 170085 (((Qof P).vtx v).1 < ((Qof P).vtx B).1) ∧
      BitIs c' 170086 (((Qof P).vtx A).1 < ((Qof P).vtx v).1) ∧
      BitIs c' 170087 (((Qof P).vtx v).2 < ((Qof P).vtx B).2) ∧
      BitIs c' 170088 (((Qof P).vtx B).2 < ((Qof P).vtx v).2) ∧
      (∀ r, (r < 170082 ∨ 170089 ≤ r) → (r < 10000 ∨ 10500 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem := by
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, r₁, m₁⟩ := test1 (op := 2) (by norm_num) hG hW (a := 170080)
    (b := 170079) (d := 170081) (dst := 170082) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) c hw (by rwa [hA]) (by rwa [hv]) (by rwa [hB])
  rw [hA, hv, hB] at b₁
  have f₁ : ∀ r, (r < 170082 ∨ 170082 < r) → (r < 10000 ∨ 10500 ≤ r) → c₁.nreg r = c.nreg r :=
    fun r h1 h2 => r₁ r (by omega) h2
  obtain ⟨c₂, k₂, e₂, hk₂, b₂, r₂, m₂⟩ := test1 (op := 3) (by norm_num) hG hW (a := 170080)
    (b := 170079) (d := 170081) (dst := 170083) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) c₁ e₁.wb_right (by rwa [f₁ _ (by omega) (by omega), hA])
    (by rwa [f₁ _ (by omega) (by omega), hv])
    (by rwa [f₁ _ (by omega) (by omega), hB])
  rw [f₁ _ (by omega) (by omega), f₁ _ (by omega) (by omega), f₁ _ (by omega) (by omega), hA, hv,
    hB] at b₂
  have f₂ : ∀ r, (r < 170082 ∨ 170083 < r) → (r < 10000 ∨ 10500 ≤ r) → c₂.nreg r = c.nreg r :=
    fun r h1 h2 => by rw [r₂ r (by omega) h2, f₁ r (by omega) h2]
  obtain ⟨c₃, k₃, e₃, hk₃, b₃, r₃, m₃⟩ := test1 (op := 0) (by norm_num) hG hW (a := 170079)
    (b := 170081) (d := 170079) (dst := 170085) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) c₂ e₂.wb_right (by rwa [f₂ _ (by omega) (by omega), hv])
    (by rwa [f₂ _ (by omega) (by omega), hB])
    (by rwa [f₂ _ (by omega) (by omega), hv])
  rw [f₂ _ (by omega) (by omega), f₂ _ (by omega) (by omega), hv, hB] at b₃
  have f₃ : ∀ r, (r < 170082 ∨ 170085 < r) → (r < 10000 ∨ 10500 ≤ r) → c₃.nreg r = c.nreg r :=
    fun r h1 h2 => by rw [r₃ r (by omega) h2, f₂ r (by omega) h2]
  obtain ⟨c₄, k₄, e₄, hk₄, b₄, r₄, m₄⟩ := test1 (op := 0) (by norm_num) hG hW (a := 170080)
    (b := 170079) (d := 170080) (dst := 170086) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) c₃ e₃.wb_right (by rwa [f₃ _ (by omega) (by omega), hA])
    (by rwa [f₃ _ (by omega) (by omega), hv])
    (by rwa [f₃ _ (by omega) (by omega), hA])
  rw [f₃ _ (by omega) (by omega), f₃ _ (by omega) (by omega), hv, hA] at b₄
  have f₄ : ∀ r, (r < 170082 ∨ 170086 < r) → (r < 10000 ∨ 10500 ≤ r) → c₄.nreg r = c.nreg r :=
    fun r h1 h2 => by rw [r₄ r (by omega) h2, f₃ r (by omega) h2]
  obtain ⟨c₅, k₅, e₅, hk₅, b₅, r₅, m₅⟩ := test1 (op := 1) (by norm_num) hG hW (a := 170079)
    (b := 170081) (d := 170079) (dst := 170087) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) c₄ e₄.wb_right (by rwa [f₄ _ (by omega) (by omega), hv])
    (by rwa [f₄ _ (by omega) (by omega), hB])
    (by rwa [f₄ _ (by omega) (by omega), hv])
  rw [f₄ _ (by omega) (by omega), f₄ _ (by omega) (by omega), hv, hB] at b₅
  have f₅ : ∀ r, (r < 170082 ∨ 170087 < r) → (r < 10000 ∨ 10500 ≤ r) → c₅.nreg r = c.nreg r :=
    fun r h1 h2 => by rw [r₅ r (by omega) h2, f₄ r (by omega) h2]
  obtain ⟨c₆, k₆, e₆, hk₆, b₆, r₆, m₆⟩ := test1 (op := 1) (by norm_num) hG hW (a := 170081)
    (b := 170079) (d := 170081) (dst := 170088) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) c₅ e₅.wb_right (by rwa [f₅ _ (by omega) (by omega), hB])
    (by rwa [f₅ _ (by omega) (by omega), hv])
    (by rwa [f₅ _ (by omega) (by omega), hB])
  rw [f₅ _ (by omega) (by omega), f₅ _ (by omega) (by omega), hv, hB] at b₆
  have ex : Exec P W testsI c c₆ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))))
  have pr : ∀ {c c' : Config} {r : ℕ}, (∀ q, q ≠ r → (q < 10000 ∨ 10500 ≤ q) →
      c'.nreg q = c.nreg q) → ∀ {r' : ℕ} {p : Prop}, BitIs c r' p → r' ≠ r → 10500 ≤ r' →
      BitIs c' r' p := fun h _ _ hb hne h2 => hb.of_eq (h _ hne (Or.inr h2))
  refine ⟨c₆, _, ex, by omega, ?_, ?_, ?_, ?_, ?_, b₆, fun r h1 h2 => ?_, by
    rw [m₆, m₅, m₄, m₃, m₂, m₁]⟩
  · exact pr r₆ (pr r₅ (pr r₄ (pr r₃ (pr r₂ b₁ (by norm_num) (by norm_num)) (by norm_num)
      (by norm_num)) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)) (by norm_num)
      (by norm_num)
  · exact pr r₆ (pr r₅ (pr r₄ (pr r₃ b₂ (by norm_num) (by norm_num)) (by norm_num)
      (by norm_num)) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  · exact pr r₆ (pr r₅ (pr r₄ b₃ (by norm_num) (by norm_num)) (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  · exact pr r₆ (pr r₅ b₄ (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  · exact pr r₆ b₅ (by norm_num) (by norm_num)
  · rw [r₆ r (by omega) h2, f₅ r (by omega) h2]

/-- **The orientation bit of the chain of a stretch.** -/
theorem betaI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {C : Chain}
    (hC : C.P = Qof P) (hT : c.nreg 170074 = C.topIdx) (hv : c.nreg 170079 = (C.s + C.topIdx) % (Qof P).n) :
    ∃ c' k, Exec P W betaI c c' k ∧ k ≤ 1500 ∧ c'.nreg 170075 ≤ 1 ∧
      (c'.nreg 170075 = 1 ↔ C.sideBeta = true) ∧ c'.nmem = c.nmem ∧ FrameB Bbeta c c' := by
  have hQ : (Qof P).n = P.n := qn'
  have hD : DistinctHeights (Qof P) := (goodShear_epsOf hS.good.2).2.1
  have hW := hS.nW
  unfold betaI
  have hwr := wr_betaI
  by_cases h0 : c.nreg 170012 < c.nreg 170074
  · have hT0 : 0 < C.topIdx := by rw [← hT]; rwa [hS.r12] at h0
    set v := (C.s + C.topIdx) % (Qof P).n with hvd
    have hvn : v < P.n := by rw [← hQ]; exact Nat.mod_lt _ (by rw [hQ]; have := hS.n3; omega)
    obtain ⟨c₁, k₁, e₁, hk₁, a80, a81, m₁, r₁⟩ := nbrI_exec c hw hS hv hvn
    obtain ⟨c₂, k₂, e₂, hk₂, b82, b83, b85, b86, b87, b88, r₂, m₂⟩ := testsI_exec c₁ e₁.wb_right
      hS.good hW a80 (by rwa [r₁ _ (by decide) (by decide)]) a81
      (Nat.mod_lt _ (by omega)) hvn (Nat.mod_lt _ (by omega))
    have c12 : c₂.nreg 170012 = 0 := by
      rw [r₂ _ (by decide) (by decide), r₁ _ (by decide) (by decide)]; exact hS.r12
    have hcons : ∀ x : ℝ, x = 0 → ¬ 0 < x := fun x h => by rw [h]; exact lt_irrefl 0
    obtain ⟨c₃, k₃, e₃, hk₃, b, b75, rfl, i75⟩ := logI_exec c₂ e₂.wb_right c12 (by omega) b82 b83
      b85 b86 b87 b88 (hcons _)
    have ex := Exec.ifLtN_true (e := setB 0) h0 (.seq e₁ (.seq e₂ e₃))
    refine ⟨_, _, ex, by omega, by simpa using b75, ?_, by simp [m₂, m₁], exec_frameB ex hwr⟩
    simp only [upd_same]
    rw [i75, sideBeta_ch hC hD hT0 hvd]
    unfold BetaF
    rw [hQ]
  · have hT0 : C.topIdx = 0 := by rw [← hT]; rw [hS.r12] at h0; omega
    obtain ⟨c₁, k₁, e₁, hk₁, rfl⟩ := setB_exec (P := P) c hw 0 (by norm_num) (by omega)
    have ex := Exec.ifLtN_false (t := nbrI.seq (testsI.seq logI)) h0 e₁
    refine ⟨_, _, ex, by omega, by simp, ?_, rfl, exec_frameB ex hwr⟩
    rw [sideBeta_of_top_zero hT0]; simp

end exec

end

end IOrc

end Chazelle.Core
