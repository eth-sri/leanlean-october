module

public import Chazelle.Core.DownPhaseOracleSubM

/-!
# WP-M (E7-B, RAM part 5): the chain of a stretch and its top

For a stretch of the interior walk (its start vertex `u` in `170033`, its number of edges `L` in
`170037`), `topCh` computes:

* `170038`: the start `cs = cStart Q u L` of its chain `ch Q u L` (`csI`);
* `170039 … 170041`: the vertex ranges `[cs, y₁]`, `[x₂, y₂]` of the chain (`rngI`);
* `170046`, `170079`: its highest vertex `v`, by two covers of the grade table (`top1`, `top2`);
* `170074`: its top index `T = (v + n - cs) mod n` (`tI`).

`topCh_exec`: within `1204 log₂ (2 L) + 900` steps, `T = (ch Q u L).topIdx` and
`(cs + T) mod n = v` (`topIdx_ch`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-! ## The programs -/

/-- `170038 := cStart Q u L`. -/
def csI : Stmt :=
  .ifLtN 170014 170011
    (.seq (block [.subN 170038 170019 170033, .subN 170084 170010 170037,
        .addN 170038 170038 170084])
      (.ifLtN 170038 170010 .skip (block [.subN 170038 170038 170010])))
    (block [.copyN 170038 170033])

/-- The vertex ranges `[cs, y₁]` and `[x₂, y₂]` into `170039 … 170041`. -/
def rngI : Stmt :=
  .seq (block [.addN 170084 170038 170037])
    (.ifLtN 170084 170010
      (block [.copyN 170039 170084, .copyN 170040 170038, .copyN 170041 170038])
      (block [.copyN 170039 170019, .constN 170040 0, .subN 170041 170084 170010]))

/-- The cover of the first range (the running maximum starts at its ends). -/
def top1 : Stmt :=
  .seq (block [.copyN 170046 170038, .copyN 170059 170039]) (.seq cmpUpd
    (.seq (block [.copyN 170050 170038, .copyN 170051 170039]) topLoop))

/-- The cover of the second range (the running maximum first takes its ends). -/
def top2 : Stmt :=
  .seq (block [.copyN 170059 170040]) (.seq cmpUpd (.seq (block [.copyN 170059 170041])
    (.seq cmpUpd (.seq (block [.copyN 170050 170040, .copyN 170051 170041]) topLoop))))

/-- `170079 := v`, `170074 := (v + n - cs) mod n`. -/
def tI : Stmt :=
  .seq (block [.copyN 170079 170046, .addN 170074 170046 170010, .subN 170074 170074 170038])
    (.ifLtN 170074 170010 .skip (block [.subN 170074 170074 170010]))

/-- **The chain of a stretch and its top.** -/
def topCh : Stmt := .seq csI (.seq rngI (.seq top1 (.seq top2 tI)))

/-- The registers `topCh` writes. -/
def Bch (r : ℕ) : Bool :=
  decide (170038 ≤ r ∧ r < 170042) || decide (170046 ≤ r ∧ r < 170070) ||
    decide (r = 170074 ∨ r = 170079 ∨ r = 170084) || Bk r

theorem btop_bch {r : ℕ} (h : Btop r = true) : Bch r = true := by
  unfold Btop at h; unfold Bch
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  rcases h with h | h
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inr h

theorem wr_topCh : wr Bch topCh = true := by
  have h1 := SweepPrim.wr_mono wr_cmpUpd (B' := Bch) (fun r hr => btop_bch hr)
  have h2 := SweepPrim.wr_mono wr_topLoop (B' := Bch) (fun r hr => btop_bch hr)
  simp only [topCh, csI, rngI, top1, top2, tI, wr, block, wrOK, h1, h2, Bool.and_true,
    Bool.true_and]
  decide

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

theorem qn' : (Qof P).n = P.n := shear_n _ _

/-- **The start of the chain.** -/
theorem csI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {u L : ℕ}
    (hu : c.nreg 170033 = u) (hL : c.nreg 170037 = L) (hun : u < P.n) (h1 : 1 ≤ L)
    (h2 : L + 1 ≤ P.n) :
    ∃ c' k, Exec P W csI c c' k ∧ k ≤ 7 ∧ c'.nreg 170038 = cStart (Qof P) u L ∧
      c'.nmem = c.nmem ∧ (∀ r, r ≠ 170038 → r ≠ 170084 → c'.nreg r = c.nreg r) := by
  have hW := hS.hW
  unfold hostWords at hW
  have hQ : (Qof P).n = P.n := qn'
  unfold csI
  by_cases hb : c.nreg 170014 < c.nreg 170011
  · have hL' : ¬ Mountain.LeftInside (Qof P) := fun h => by
      have := hS.lb.2 h; rw [hS.r11] at hb; omega
    refine spec_ifLtN_true hb ?_
    refine spec_seq ?_
    exec_block
    · config_simp; rw [hS.r19, hS.r10, hu, hL]; omega
    by_cases hlt : P.n - 1 - u + (P.n - L) < P.n
    · refine spec_ifLtN_true (by config_simp; rwa [hS.r19, hS.r10, hu, hL]) ?_
      refine spec_skip ‹_› ⟨by omega, ?_, rfl, fun r h1 h2 => ?_⟩
      · config_simp; rw [hS.r19, hS.r10, hu, hL]
        unfold cStart; rw [ite_eq_right hL', hQ, Nat.mod_eq_of_lt hlt]
      · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
    · refine spec_ifLtN_false (by config_simp; rwa [hS.r19, hS.r10, hu, hL]) ?_
      exec_block
      refine ⟨by omega, ?_, rfl, fun r h1 h2 => ?_⟩
      · config_simp; rw [hS.r19, hS.r10, hu, hL]
        unfold cStart; rw [ite_eq_right hL', hQ, Nat.mod_eq_sub_mod (by omega),
          Nat.mod_eq_of_lt (by omega)]
      · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
  · have hL' : Mountain.LeftInside (Qof P) := hS.lb.1 (by rw [hS.r11] at hb; have := hS.lb1; omega)
    refine spec_ifLtN_false hb ?_
    exec_block
    refine ⟨by omega, ?_, rfl, fun r h1 h2 => ?_⟩
    · config_simp; rw [hu]; unfold cStart; rw [ite_eq_left hL']
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega

/-- **The vertex ranges of the chain.** -/
theorem rngI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {cs L : ℕ}
    (hcs : c.nreg 170038 = cs) (hL : c.nreg 170037 = L) (hcsn : cs < P.n) (h2 : L + 1 ≤ P.n) :
    ∃ c' k, Exec P W rngI c c' k ∧ k ≤ 6 ∧ c'.nreg 170039 = rY1 P.n cs L ∧
      c'.nreg 170040 = rX2 P.n cs L ∧ c'.nreg 170041 = rY2 P.n cs L ∧ c'.nmem = c.nmem ∧
      (∀ r, r ≠ 170039 → r ≠ 170040 → r ≠ 170041 → r ≠ 170084 → c'.nreg r = c.nreg r) := by
  have hW := hS.hW
  unfold hostWords at hW
  unfold rngI
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hcs, hL]; omega
  by_cases hlt : cs + L < P.n
  · refine spec_ifLtN_true (by config_simp; rwa [hcs, hL, hS.r10]) ?_
    exec_block
    refine ⟨by omega, ?_, ?_, ?_, rfl, fun r h1 h2 h3 h4 => ?_⟩
    · config_simp; rw [hcs, hL]; unfold rY1; rw [ite_eq_left hlt]
    · config_simp; rw [hcs]; unfold rX2; rw [ite_eq_left hlt]
    · config_simp; rw [hcs]; unfold rY2; rw [ite_eq_left hlt]
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
  · refine spec_ifLtN_false (by config_simp; rwa [hcs, hL, hS.r10]) ?_
    exec_block
    · omega
    refine ⟨by omega, ?_, ?_, ?_, rfl, fun r h1 h2 h3 h4 => ?_⟩
    · config_simp; rw [hS.r19]; unfold rY1; rw [ite_eq_right hlt]
    · config_simp; unfold rX2; rw [ite_eq_right hlt]
    · config_simp; rw [hcs, hL, hS.r10]; unfold rY2; rw [ite_eq_right hlt]
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega

/-- Two copies. -/
theorem copy2_exec (c : Config) (hw : WordsBounded W c) (a b a' b' : ℕ) (hab : a ≠ b)
    (hb : a ≠ b') :
    ∃ c' k, Exec P W (block [.copyN a a', .copyN b b']) c c' k ∧ k = 2 ∧
      c'.nreg a = c.nreg a' ∧ c'.nreg b = c.nreg b' ∧
      (∀ r, r ≠ a → r ≠ b → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  exec_block
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl⟩
  · simp [upd, hab, Ne.symm hab]
  · simp [upd, Ne.symm hb]
  · simp [upd, h1, h2]

/-- **The cover of the first range.** -/
theorem top1_exec {G : ℕ → Prop} (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    {x y : ℕ} (hx : c.nreg 170038 = x) (hy : c.nreg 170039 = y) (hxy : x ≤ y) (hyn : y ≤ P.n - 1)
    (hcap : y - x ≤ 2 ^ (s.m₀ s.h - 1)) (hgood : ∀ v, x ≤ v → v ≤ y → G v) :
    ∃ c' k, Exec P W top1 c c' k ∧ k ≤ 602 * Nat.log 2 (2 * (y - x)) + 262 ∧ SEnv P W O s c' ∧
      G (c'.nreg 170046) ∧ c'.nreg 170046 < P.n ∧
      (∀ v, x ≤ v → v ≤ y → Y P v ≤ Y P (c'.nreg 170046)) ∧
      (∀ r, (r < 170046 ∨ 170070 ≤ r) → (r < 10000 ∨ 10500 ≤ r) → c'.nreg r = c.nreg r) := by
  have hn := hS.n3
  obtain ⟨c₁, k₁, e₁, hk₁, a46, a59, r₁, m₁⟩ := copy2_exec (P := P) c hw 170046 170059
    170038 170039 (by norm_num) (by norm_num)
  have S₁ : SEnv P W O s c₁ := hS.keep (fun r h1 h2 => r₁ r (by omega) (by omega))
    (fun a _ => by rw [m₁]) (by rw [r₁ _ (by decide) (by decide)])
  obtain ⟨c₂, k₂, e₂, hk₂, b46, r₂, m₂⟩ := cmpUpd_exec c₁ e₁.wb_right S₁
    (by rw [a46, hx]; omega) (by rw [a59, hy]; omega)
  have S₂ : SEnv P W O s c₂ := S₁.keep (fun r h1 h2 => r₂ r (by omega) (by omega) (by omega))
    (fun a _ => by rw [m₂]) (by rw [r₂ _ (by decide) (by decide) (by decide)])
  obtain ⟨c₃, k₃, e₃, hk₃, d50, d51, r₃, m₃⟩ := copy2_exec (P := P) c₂ e₂.wb_right
    170050 170051 170038 170039 (by norm_num) (by norm_num)
  have S₃ : SEnv P W O s c₃ := S₂.keep (fun r h1 h2 => r₃ r (by omega) (by omega))
    (fun a _ => by rw [m₃]) (by rw [r₃ _ (by decide) (by decide)])
  have k38 : c₂.nreg 170038 = x := by
    rwa [r₂ _ (by decide) (by decide) (by decide), r₁ _ (by decide) (by decide)]
  have k39 : c₂.nreg 170039 = y := by
    rwa [r₂ _ (by decide) (by decide) (by decide), r₁ _ (by decide) (by decide)]
  have v46 : c₃.nreg 170046 = c₂.nreg 170046 := r₃ _ (by decide) (by decide)
  have hmx := Y_max_le (P := P) (a := c₁.nreg 170046) (b := c₁.nreg 170059)
  rw [← b46, a46, a59, hx, hy] at hmx
  have hv : c₂.nreg 170046 = x ∨ c₂.nreg 170046 = y := by
    rw [b46, a46, a59, hx, hy]; split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  obtain ⟨c₄, k₄, e₄, hk₄, S₄, g₄, n₄, cov₄, r₄, -, m₄⟩ := topLoop_exec (G := G) c₃ e₃.wb_right S₃
    (by rw [d50, k38]) (by rw [d51, k39]) hxy hyn hcap
    (by rw [v46]; rcases hv with h | h <;> rw [h] <;> exact hgood _ (by omega) (by omega))
    (by rw [v46]; rcases hv with h | h <;> rw [h] <;> omega)
    (by rw [v46]; exact hmx.1) (by rw [v46]; exact hmx.2) hgood
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, S₄, g₄, n₄, cov₄,
    fun r h1 h2 => ?_⟩
  rw [r₄ r h1 h2, r₃ r (by omega) (by omega), r₂ r (by omega) (by omega) h2,
    r₁ r (by omega) (by omega)]

/-- **The cover of the second range.** -/
theorem top2_exec {G : ℕ → Prop} (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    {x y : ℕ} (hx : c.nreg 170040 = x) (hy : c.nreg 170041 = y) (hxy : x ≤ y) (hyn : y ≤ P.n - 1)
    (hcap : y - x ≤ 2 ^ (s.m₀ s.h - 1)) (hgood : ∀ v, x ≤ v → v ≤ y → G v)
    (hvG : G (c.nreg 170046)) (hvn : c.nreg 170046 < P.n) :
    ∃ c' k, Exec P W top2 c c' k ∧ k ≤ 602 * Nat.log 2 (2 * (y - x)) + 512 ∧ SEnv P W O s c' ∧
      G (c'.nreg 170046) ∧ c'.nreg 170046 < P.n ∧
      (∀ v, x ≤ v → v ≤ y → Y P v ≤ Y P (c'.nreg 170046)) ∧
      Y P (c.nreg 170046) ≤ Y P (c'.nreg 170046) ∧
      (∀ r, (r < 170046 ∨ 170070 ≤ r) → (r < 10000 ∨ 10500 ≤ r) → c'.nreg r = c.nreg r) := by
  have hn := hS.n3
  -- the first end
  obtain ⟨c₁, k₁, e₁, hk₁, a59, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 170059 170040]) c c₁ k₁ ∧
      k₁ = 1 ∧ c₁.nreg 170059 = x ∧ (∀ r, r ≠ 170059 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    exec_block
    refine ⟨rfl, by config_simp; exact hx, fun r hr => ?_, rfl⟩
    simp only [Config.nreg_mk, upd, ite_eq_right hr]
  have S₁ : SEnv P W O s c₁ := hS.keep (fun r h1 h2 => r₁ r (by omega))
    (fun a _ => by rw [m₁]) (by rw [r₁ _ (by decide)])
  obtain ⟨c₂, k₂, e₂, hk₂, b46, r₂, m₂⟩ := cmpUpd_exec c₁ e₁.wb_right S₁
    (by rwa [r₁ _ (by decide)]) (by rw [a59]; omega)
  have S₂ : SEnv P W O s c₂ := S₁.keep (fun r h1 h2 => r₂ r (by omega) (by omega) (by omega))
    (fun a _ => by rw [m₂]) (by rw [r₂ _ (by decide) (by decide) (by decide)])
  have k41 : c₂.nreg 170041 = y := by
    rwa [r₂ _ (by decide) (by decide) (by decide), r₁ _ (by decide)]
  have k40 : c₂.nreg 170040 = x := by
    rwa [r₂ _ (by decide) (by decide) (by decide), r₁ _ (by decide)]
  -- the second end
  obtain ⟨c₃, k₃, e₃, hk₃, a59', r₃, m₃⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 170059 170041]) c₂ c₃ k₃ ∧
      k₃ = 1 ∧ c₃.nreg 170059 = y ∧ (∀ r, r ≠ 170059 → c₃.nreg r = c₂.nreg r) ∧
      c₃.nmem = c₂.nmem := by
    have w₂ := e₂.wb_right
    exec_block
    refine ⟨rfl, by config_simp; exact k41, fun r hr => ?_, rfl⟩
    simp only [Config.nreg_mk, upd, ite_eq_right hr]
  have S₃ : SEnv P W O s c₃ := S₂.keep (fun r h1 h2 => r₃ r (by omega))
    (fun a _ => by rw [m₃]) (by rw [r₃ _ (by decide)])
  have hmx1 := Y_max_le (P := P) (a := c₁.nreg 170046) (b := c₁.nreg 170059)
  rw [← b46, a59, r₁ _ (by decide)] at hmx1
  have hv2 : c₂.nreg 170046 < P.n ∧ G (c₂.nreg 170046) := by
    rw [b46, a59, r₁ _ (by decide)]; split_ifs
    · exact ⟨by omega, hgood x le_rfl hxy⟩
    · exact ⟨hvn, hvG⟩
  obtain ⟨c₄, k₄, e₄, hk₄, b46', r₄, m₄⟩ := cmpUpd_exec c₃ e₃.wb_right S₃
    (by rw [r₃ _ (by decide)]; exact hv2.1) (by rw [a59']; omega)
  have S₄ : SEnv P W O s c₄ := S₃.keep (fun r h1 h2 => r₄ r (by omega) (by omega) (by omega))
    (fun a _ => by rw [m₄]) (by rw [r₄ _ (by decide) (by decide) (by decide)])
  have hmx2 := Y_max_le (P := P) (a := c₃.nreg 170046) (b := c₃.nreg 170059)
  rw [← b46', a59', r₃ _ (by decide)] at hmx2
  have hv4 : c₄.nreg 170046 < P.n ∧ G (c₄.nreg 170046) := by
    rw [b46', a59', r₃ _ (by decide)]; split_ifs
    · exact ⟨by omega, hgood y hxy le_rfl⟩
    · exact hv2
  have k40' : c₄.nreg 170040 = x := by
    rwa [r₄ _ (by decide) (by decide) (by decide), r₃ _ (by decide)]
  have k41' : c₄.nreg 170041 = y := by
    rwa [r₄ _ (by decide) (by decide) (by decide), r₃ _ (by decide)]
  -- the cover
  obtain ⟨c₅, k₅, e₅, hk₅, d50, d51, r₅, m₅⟩ := copy2_exec (P := P) c₄ e₄.wb_right
    170050 170051 170040 170041 (by norm_num) (by norm_num)
  have S₅ : SEnv P W O s c₅ := S₄.keep (fun r h1 h2 => r₅ r (by omega) (by omega))
    (fun a _ => by rw [m₅]) (by rw [r₅ _ (by decide) (by decide)])
  have v46 : c₅.nreg 170046 = c₄.nreg 170046 := r₅ _ (by decide) (by decide)
  obtain ⟨c₆, k₆, e₆, hk₆, S₆, g₆, n₆, cov₆, r₆, y₆, m₆⟩ := topLoop_exec (G := G) c₅ e₅.wb_right S₅
    (by rw [d50, k40']) (by rw [d51, k41']) hxy hyn hcap (by rw [v46]; exact hv4.2)
    (by rw [v46]; exact hv4.1) (by rw [v46]; exact hmx1.2.trans hmx2.1)
    (by rw [v46]; exact hmx2.2) hgood
  refine ⟨c₆, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), by omega, S₆, g₆, n₆, cov₆,
    ?_, fun r h1 h2 => ?_⟩
  · rw [v46] at y₆
    exact le_trans hmx1.1 (hmx2.1.trans y₆)
  · rw [r₆ r h1 h2, r₅ r (by omega) (by omega), r₄ r (by omega) (by omega) h2, r₃ r (by omega),
      r₂ r (by omega) (by omega) h2, r₁ r (by omega)]

/-- **The top index.** -/
theorem tI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {v cs : ℕ}
    (hv : c.nreg 170046 = v) (hcs : c.nreg 170038 = cs) (hvn : v < P.n) (hcsn : cs < P.n) :
    ∃ c' k, Exec P W tI c c' k ∧ k ≤ 6 ∧ c'.nreg 170079 = v ∧
      c'.nreg 170074 = (v + P.n - cs) % P.n ∧ c'.nmem = c.nmem ∧
      (∀ r, r ≠ 170079 → r ≠ 170074 → c'.nreg r = c.nreg r) := by
  have hW := hS.hW
  unfold hostWords at hW
  unfold tI
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hv, hS.r10]; omega
  by_cases hlt : v + P.n - cs < P.n
  · refine spec_ifLtN_true (by config_simp; rwa [hv, hS.r10, hcs]) ?_
    refine spec_skip ‹_› ⟨by omega, by config_simp; exact hv, ?_, rfl, fun r h1 h2 => ?_⟩
    · config_simp; rw [hv, hS.r10, hcs, Nat.mod_eq_of_lt hlt]
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
  · refine spec_ifLtN_false (by config_simp; rwa [hv, hS.r10, hcs]) ?_
    exec_block
    refine ⟨by omega, by config_simp; exact hv, ?_, rfl, fun r h1 h2 => ?_⟩
    · config_simp; rw [hv, hS.r10, hcs, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega

theorem log_two_mono {a b : ℕ} (h : a ≤ b) : Nat.log 2 (2 * a) ≤ Nat.log 2 (2 * b) :=
  Nat.log_mono_right (by omega)

/-- **The chain of a stretch and its top.** -/
theorem topCh_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {u L : ℕ}
    (hu : c.nreg 170033 = u) (hL : c.nreg 170037 = L) (hun : u < P.n) (h1 : 1 ≤ L)
    (h2 : L + 1 ≤ (Qof P).n) (hcap : L ≤ 2 ^ (s.m₀ s.h - 1)) :
    ∃ c' k, Exec P W topCh c c' k ∧ k ≤ 1204 * Nat.log 2 (2 * L) + 900 ∧ SEnv P W O s c' ∧
      c'.nreg 170038 = cStart (Qof P) u L ∧
      c'.nreg 170074 = (ch (Qof P) u L h1 h2).topIdx ∧
      (cStart (Qof P) u L + (ch (Qof P) u L h1 h2).topIdx) % (Qof P).n = c'.nreg 170079 ∧
      FrameB Bch c c' := by
  have hQ : (Qof P).n = P.n := qn'
  have h2' : L + 1 ≤ P.n := by rwa [← hQ]
  have hD : DistinctHeights (Qof P) := (goodShear_epsOf hS.good.2).2.1
  set cs := cStart (Qof P) u L with hcsd
  have hcsn : cs < P.n := by rw [← hQ]; exact cStart_lt (by rwa [hQ])
  have hLn : L < P.n := by omega
  -- the start
  obtain ⟨c₁, k₁, e₁, hk₁, a38, m₁, r₁⟩ := csI_exec c hw hS hu hL hun h1 h2'
  rw [← hcsd] at a38
  have S₁ : SEnv P W O s c₁ := hS.keep (fun r h1 h2 => r₁ r (by omega) (by omega))
    (fun a _ => by rw [m₁]) (by rw [r₁ _ (by decide) (by decide)])
  -- the ranges
  obtain ⟨c₂, k₂, e₂, hk₂, b39, b40, b41, m₂, r₂⟩ := rngI_exec c₁ e₁.wb_right S₁ a38
    (by rwa [r₁ _ (by decide) (by decide)]) hcsn h2'
  have S₂ : SEnv P W O s c₂ := S₁.keep (fun r h1 h2 => r₂ r (by omega) (by omega) (by omega)
    (by omega)) (fun a _ => by rw [m₂]) (by rw [r₂ _ (by decide) (by decide) (by decide)
      (by decide)])
  have b38 : c₂.nreg 170038 = cs := by
    rwa [r₂ _ (by decide) (by decide) (by decide) (by decide)]
  let G : ℕ → Prop := fun v => InCh (Qof P).n cs L v
  have hcap1 : rY1 P.n cs L - cs ≤ 2 ^ (s.m₀ s.h - 1) := le_trans rY1_sub hcap
  have hcap2 : rY2 P.n cs L - rX2 P.n cs L ≤ 2 ^ (s.m₀ s.h - 1) := le_trans (rY2_sub hcsn) hcap
  -- the first cover
  obtain ⟨c₃, k₃, e₃, hk₃, S₃, g₃, n₃, cov₃, r₃⟩ := top1_exec (G := G) c₂ e₂.wb_right S₂ b38 b39
    (cs_le_rY1 hcsn) (by have := rY1_lt (L := L) hcsn; omega) hcap1
    (fun v hv1 hv2 => by
      show InCh (Qof P).n cs L v
      rw [hQ]; exact of_rng1 hcsn hv1 hv2)
  have c40 : c₃.nreg 170040 = rX2 P.n cs L := by
    rwa [r₃ _ (by omega) (by omega)]
  have c41 : c₃.nreg 170041 = rY2 P.n cs L := by
    rwa [r₃ _ (by omega) (by omega)]
  -- the second cover
  obtain ⟨c₄, k₄, e₄, hk₄, S₄, g₄, n₄, cov₄, y₄, r₄⟩ := top2_exec (G := G) c₃ e₃.wb_right S₃
    c40 c41 (rX2_le hcsn hLn) (by have := rY2_lt hcsn hLn (L := L); omega) hcap2
    (fun v hv1 hv2 => by
      show InCh (Qof P).n cs L v
      rw [hQ]; exact of_rng2 hcsn hLn hv1 hv2) g₃ n₃
  have c38 : c₄.nreg 170038 = cs := by
    rwa [r₄ _ (by omega) (by omega), r₃ _ (by omega) (by omega)]
  -- the top index
  obtain ⟨c₅, k₅, e₅, hk₅, d79, d74, m₅, r₅⟩ := tI_exec c₄ e₄.wb_right S₄ rfl c38 n₄ hcsn
  have S₅ : SEnv P W O s c₅ := S₄.keep (fun r h1 h2 => r₅ r (by omega) (by omega))
    (fun a _ => by rw [m₅]) (by rw [r₅ _ (by decide) (by decide)])
  -- the mathematics
  have hmax : ∀ k, k ≤ L → ((Qof P).vtx ((cs + k) % (Qof P).n)).2 ≤ ((Qof P).vtx (c₄.nreg 170046)).2 := by
    intro k hk
    rw [hQ]
    rcases rng_of hcsn hLn hk with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · exact (cov₃ _ k1 k2).trans y₄
    · exact cov₄ _ k1 k2
  obtain ⟨hT, hTv⟩ := topIdx_ch (Q := Qof P) (h1 := h1) (h2 := h2) hD g₄ hmax (by rwa [hQ])
  have ex : Exec P W topCh c c₅ (k₁ + (k₂ + (k₃ + (k₄ + k₅)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  have hlog1 : Nat.log 2 (2 * (rY1 P.n cs L - cs)) ≤ Nat.log 2 (2 * L) := log_two_mono rY1_sub
  have hlog2 : Nat.log 2 (2 * (rY2 P.n cs L - rX2 P.n cs L)) ≤ Nat.log 2 (2 * L) :=
    log_two_mono (rY2_sub hcsn)
  refine ⟨c₅, _, ex, by omega, S₅, by rwa [r₅ _ (by decide) (by decide)], ?_, by rwa [d79], exec_frameB ex wr_topCh⟩
  rw [d74, hT, hQ]

end exec

end

end IOrc

end Chazelle.Core
