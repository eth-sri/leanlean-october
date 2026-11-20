module

public import Chazelle.Core.DownPhaseDrvPTop

/-!
# Down-phase pieces (D4), part 2: the top of a long leaf from the grade table

`gTop` computes, for a leaf `v_a … v_{a+m}` of `Q` (`a` in `218004`, `m` in `218002`, the
handle of the up-phase data in `218008`), the offset `T ≤ m` of a highest vertex
(`218013 := T`), without scanning the leaf: it reads the row and halving tables of the grade
table (`gSetup`), takes the running maximum of `v_a`, `v_mid`, `v_{a+m}` (`mid = a + ⌊m/2⌋`,
two `cmpUpd`) and runs the grade-table cover `IOrc.topLoop` on `[a, mid]` and on
`[mid, a + m]` (each of length `≤ 2^(μ-1)`, within the cap of the table).  `gTop_exec`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace DrvP

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-! ## The program -/

/-- The constants and the row and halving tables of the grade table. -/
def gSetup : Stmt := block [.constN 170011 1, .constN 170012 0, .constN 170067 2,
  .addN 170056 218008 170067, .loadN 170016 170056, .addN 170056 170056 170011,
  .loadN 170017 170056]

/-- `170046 := a`, `170070 := a + m`, `170072 := a + ⌊m/2⌋`. -/
def gEnds : Stmt := block [.copyN 170046 218004, .addN 170070 218004 218002,
  .addN 170056 170017 218002, .loadN 170071 170056, .addN 170072 218004 170071]

/-- **The top of a long leaf** by the grade table. -/
def gTop : Stmt :=
  .seq gSetup (.seq gEnds (.seq (block [.copyN 170059 170072]) (.seq IOrc.cmpUpd
  (.seq (block [.copyN 170059 170070]) (.seq IOrc.cmpUpd
  (.seq (block [.copyN 170050 218004, .copyN 170051 170072]) (.seq IOrc.topLoop
  (.seq (block [.copyN 170050 170072, .copyN 170051 170070]) (.seq IOrc.topLoop
  (block [.subN 218013 170046 218004]))))))))))

/-- The registers `gTop` writes. -/
def Bg (r : ℕ) : Bool := decide (170000 ≤ r ∧ r < 170100) || Bk r || r == 218013

theorem wr_gTop : wr Bg gTop = true := by
  have h1 : wr Bg IOrc.topLoop = true := SweepPrim.wr_mono IOrc.wr_topLoop (fun r hr => by
    simp only [IOrc.Btop, Bool.or_eq_true, decide_eq_true_eq] at hr
    simp only [Bg, Bool.or_eq_true, decide_eq_true_eq]
    rcases hr with hr | hr
    · exact Or.inl (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inl (Or.inr hr))
  have h2 : wr Bg IOrc.cmpUpd = true := SweepPrim.wr_mono IOrc.wr_cmpUpd (fun r hr => by
    simp only [IOrc.Btop, Bool.or_eq_true, decide_eq_true_eq] at hr
    simp only [Bg, Bool.or_eq_true, decide_eq_true_eq]
    rcases hr with hr | hr
    · exact Or.inl (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inl (Or.inr hr))
  simp only [gTop, gSetup, gEnds, wr, block, wrOK, h1, h2, Bool.and_true, Bool.true_and]
  decide

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ} {O : OracleIface}

theorem tenv_upd {s : TSt} {c : Config} (h : TEnv P W O s c) {r₀ : ℕ} (v : ℕ)
    (hr : r₀ < 170000 ∨ 170030 ≤ r₀) (hA : r₀ ≠ ALLOC) :
    TEnv P W O s { c with nreg := upd c.nreg r₀ v } :=
  h.keep (fun r h1 h2 => by simp only [upd]; rw [ite_eq_right (by omega)])
    (fun _ _ => rfl) (by simp only [upd]; rw [ite_eq_right (Ne.symm hA)])

theorem log_le_of_half {d μ : ℕ} (hμ : 1 ≤ μ) (hd : d ≤ 2 ^ (μ - 1)) :
    Nat.log 2 (2 * d) ≤ μ := by
  have h2 : 2 * d ≤ 2 ^ μ := by
    have : 2 ^ μ = 2 * 2 ^ (μ - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  calc Nat.log 2 (2 * d) ≤ Nat.log 2 (2 ^ μ) := Nat.log_mono_right h2
    _ = μ := Nat.log_pow (by norm_num) μ

theorem half_le {m μ : ℕ} (hμ : 1 ≤ μ) (hm : m ≤ 2 ^ μ) : m / 2 ≤ 2 ^ (μ - 1) ∧
    m - m / 2 ≤ 2 ^ (μ - 1) := by
  have : 2 ^ μ = 2 * 2 ^ (μ - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

set_option maxHeartbeats 1000000 in
/-- **The top of a long leaf** `v_a … v_{a+m}` (`1 ≤ μ`, `m ≤ 2^μ`, at least `μ` grades in the
table): `218013 := T ≤ m` with `v_{a+T}` at least as high as every vertex of the leaf. -/
theorem gTop_exec {s : TSt} (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hW : hostWords P.n ≤ W) (hmem : ∀ a, a < s.A₀ → c.nmem a = s.m₀ a)
    (hal : s.A₀ ≤ c.nreg ALLOC) (hgr : Robust s.A₀ s.m₀ (fun m => GradeRaw O P m s.h s.A₀))
    (hh : c.nreg 218008 = s.h) {μ : ℕ} (hμ1 : 1 ≤ μ) (hμ : c.nreg 218002 ≤ 2 ^ μ)
    (hμΛ : μ ≤ s.m₀ s.h) (ham : c.nreg 218004 + c.nreg 218002 + 1 ≤ P.n) :
    ∃ c' k, Exec P W gTop c c' k ∧ k ≤ 1204 * μ + 600 ∧ FrameB Bg c c' ∧
      c'.nreg 218013 ≤ c.nreg 218002 ∧
      ∀ j, j ≤ c.nreg 218002 →
        IOrc.Y P (c.nreg 218004 + j) ≤ IOrc.Y P (c.nreg 218004 + c'.nreg 218013) := by
  have hlow := ShootCut.grade_low hgr
  have hA := hw.1 ALLOC
  have hWh := hW
  unfold hostWords at hWh
  set a := c.nreg 218004 with ha
  set m := c.nreg 218002 with hm
  have hmn : m ≤ P.n := by omega
  have hhalf := (hgr.holds).2.2.1 m hmn
  have e2 : c.nmem (s.h + 2) = s.m₀ (s.h + 2) := hmem _ (by omega)
  have e3 : c.nmem (s.h + 2 + 1) = s.m₀ (s.h + 3) := hmem _ (by omega)
  -- 1. setup
  obtain ⟨c₁, k₁, e₁, hk₁, S₁, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W gSetup c c₁ k₁ ∧ k₁ = 7 ∧
      TEnv P W O s c₁ ∧ (∀ r, (r < 170000 ∨ 170100 ≤ r) → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    unfold gSetup
    exec_block
    all_goals first | omega | skip
    · config_simp; rw [hh]; omega
    · config_simp; rw [hh]; omega
    refine ⟨rfl, ⟨hG, hW, by config_simp, by config_simp, ?_, ?_, fun a ha => ?_, ?_, hgr⟩,
      fun r hr => ?_, rfl⟩
    · config_simp; rw [hh, e2]
    · config_simp; rw [hh, e3]
    · exact hmem a ha
    · config_simp; exact hal
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
  have w₁ := e₁.wb_right
  have a₁ : c₁.nreg 218004 = a := r₁ _ (by norm_num)
  have m₁' : c₁.nreg 218002 = m := r₁ _ (by norm_num)
  have hm2 : c₁.nmem (s.m₀ (s.h + 3) + m) = m / 2 := by
    rw [m₁, hmem _ (hlow.2.2 _ hmn)]; exact hhalf
  -- 2. the ends and the middle
  obtain ⟨c₂, k₂, e₂, hk₂, S₂, v46, v70, v72, r₂, m₂⟩ : ∃ c₂ k₂, Exec P W gEnds c₁ c₂ k₂ ∧
      k₂ = 5 ∧ TEnv P W O s c₂ ∧ c₂.nreg 170046 = a ∧ c₂.nreg 170070 = a + m ∧
      c₂.nreg 170072 = a + m / 2 ∧ (∀ r, (r < 170000 ∨ 170100 ≤ r) → c₂.nreg r = c.nreg r) ∧
      c₂.nmem = c.nmem := by
    unfold gEnds
    exec_block
    all_goals first | omega | skip
    · config_simp; rw [a₁, m₁']; omega
    · config_simp; rw [S₁.r17, m₁']; have := hlow.2.2 _ hmn; omega
    · config_simp; rw [S₁.r17, a₁, m₁', hm2]; omega
    refine ⟨rfl, S₁.keep (fun r h1 h2 => ?_) (fun _ _ => rfl) (by simp [upd, ALLOC]), ?_, ?_, ?_,
      fun r hr => ?_, m₁⟩
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
    · config_simp; exact a₁
    · config_simp; rw [a₁, m₁']
    · config_simp; rw [S₁.r17, a₁, m₁', hm2]
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | (exact r₁ r hr) | omega
  have w₂ := e₂.wb_right
  -- 3. the first comparison (the middle)
  obtain ⟨c₃, k₃, e₃, hk₃, h59, r₃⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 170059 170072]) c₂ c₃ k₃ ∧
      k₃ = 1 ∧ c₃.nreg 170059 = a + m / 2 ∧ c₃ = { c₂ with nreg := upd c₂.nreg 170059 (a + m / 2) } := by
    exec_block
    refine ⟨rfl, by config_simp; exact v72, ?_⟩
    rw [v72]
  have w₃ := e₃.wb_right
  have S₃ : TEnv P W O s c₃ := by rw [r₃]; exact tenv_upd S₂ _ (by norm_num) (by decide)
  have c346 : c₃.nreg 170046 = a := by rw [r₃]; config_simp; exact v46
  obtain ⟨c₄, k₄, e₄, hk₄, u46, f₄, m₄⟩ := cmpUpd_exec c₃ w₃ S₃ (by rw [c346]; omega)
    (by rw [h59]; omega)
  rw [c346, h59] at u46
  have w₄ := e₄.wb_right
  have S₄ : TEnv P W O s c₄ := S₃.keep (fun r h1 h2 => f₄ r (by omega) (by omega) (by omega))
    (fun _ _ => by rw [m₄]) (by rw [f₄ _ (by decide) (by decide) (by decide)])
  have k₄' : ∀ r, (r < 170000 ∨ 170100 ≤ r) → (r < 10000 ∨ 10500 ≤ r) → c₄.nreg r = c.nreg r :=
    fun r h1 h2 => by
      rw [f₄ r (by omega) (by omega) h2, r₃]
      simp only [upd, ite_eq_right (show r ≠ 170059 by omega)]; exact r₂ r h1
  have c470 : c₄.nreg 170070 = a + m := by
    rw [f₄ _ (by decide) (by decide) (by decide), r₃]; simp only [upd]; exact v70
  have c472 : c₄.nreg 170072 = a + m / 2 := by
    rw [f₄ _ (by decide) (by decide) (by decide), r₃]; simp only [upd]; exact v72
  set v₄ := c₄.nreg 170046 with hv₄
  have hv₄G : a ≤ v₄ ∧ v₄ ≤ a + m := by rw [u46]; split_ifs <;> omega
  have hv₄Y := IOrc.Y_max_le (P := P) (a := a) (b := a + m / 2)
  rw [← u46] at hv₄Y
  -- 4. the second comparison (the end)
  have e₅ := IOrc.exec_copyN_upd (P := P) w₄ 170059 170070
  set c₅ : Config := { c₄ with nreg := upd c₄.nreg 170059 (c₄.nreg 170070) } with hc₅
  have w₅ : WordsBounded W c₅ := e₅.wb_right
  have S₅ : TEnv P W O s c₅ := tenv_upd S₄ _ (by norm_num) (by decide)
  have c546 : c₅.nreg 170046 = v₄ := by rw [hc₅]; simp [upd]; rfl
  have c559 : c₅.nreg 170059 = a + m := by rw [hc₅]; simp only [upd_same]; exact c470
  obtain ⟨c₆, k₆, e₆, hk₆, u46', f₆, m₆⟩ := cmpUpd_exec c₅ w₅ S₅ (by rw [c546]; omega)
    (by rw [c559]; omega)
  rw [c546, c559] at u46'
  have w₆ := e₆.wb_right
  have S₆ : TEnv P W O s c₆ := S₅.keep (fun r h1 h2 => f₆ r (by omega) (by omega) (by omega))
    (fun _ _ => by rw [m₆]) (by rw [f₆ _ (by decide) (by decide) (by decide)])
  have k₆' : ∀ r, (r < 170000 ∨ 170100 ≤ r) → (r < 10000 ∨ 10500 ≤ r) → c₆.nreg r = c.nreg r :=
    fun r h1 h2 => by
      rw [f₆ r (by omega) (by omega) h2, hc₅]
      simp only [upd, ite_eq_right (show r ≠ 170059 by omega)]; exact k₄' r h1 h2
  have c670 : c₆.nreg 170070 = a + m := by
    rw [f₆ _ (by decide) (by decide) (by decide), hc₅]; simp only [upd]; exact c470
  have c672 : c₆.nreg 170072 = a + m / 2 := by
    rw [f₆ _ (by decide) (by decide) (by decide), hc₅]; simp only [upd]; exact c472
  set v₆ := c₆.nreg 170046 with hv₆
  have hv₆G : a ≤ v₆ ∧ v₆ ≤ a + m := by rw [u46']; split_ifs <;> omega
  have hv₆Y := IOrc.Y_max_le (P := P) (a := v₄) (b := a + m)
  rw [← u46'] at hv₆Y
  have hm₆ : c₆.nmem = c.nmem := by rw [m₆, hc₅, m₄, r₃, m₂]
  -- 5. the cover of `[a, mid]`
  obtain ⟨c₇, k₇, e₇, hk₇, x₇, y₇, r₇⟩ : ∃ c₇ k₇, Exec P W
      (block [.copyN 170050 218004, .copyN 170051 170072]) c₆ c₇ k₇ ∧ k₇ = 2 ∧
      c₇.nreg 170050 = a ∧ c₇.nreg 170051 = a + m / 2 ∧
      c₇ = { c₆ with nreg := upd (upd c₆.nreg 170050 a) 170051 (a + m / 2) } := by
    exec_block
    refine ⟨rfl, by config_simp; rw [k₆' _ (by norm_num) (by norm_num)], by config_simp; exact c672,
      ?_⟩
    rw [k₆' _ (by norm_num) (by norm_num), c672]
  have w₇ := e₇.wb_right
  have S₇ : TEnv P W O s c₇ := by
    rw [r₇]; exact tenv_upd (tenv_upd S₆ _ (by norm_num) (by decide)) _ (by norm_num) (by decide)
  have c746 : c₇.nreg 170046 = v₆ := by rw [r₇]; simp [upd]; rfl
  have hcap : ∀ d, d ≤ 2 ^ (μ - 1) → d ≤ 2 ^ (s.m₀ s.h - 1) := fun d hd =>
    hd.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hhl := half_le hμ1 hμ
  obtain ⟨c₈, k₈, e₈, hk₈, S₈, g₈, n₈, cov₈, f₈, y₈, m₈⟩ := topLoop_exec
    (G := fun v => a ≤ v ∧ v ≤ a + m) c₇ w₇ S₇ x₇ y₇ (by omega) (by omega)
    (hcap _ (by omega)) (by rw [c746]; exact hv₆G) (by rw [c746]; omega)
    (by rw [c746]; exact hv₄Y.1.trans hv₆Y.1) (by rw [c746]; exact hv₄Y.2.trans hv₆Y.1)
    (fun v h1 h2 => ⟨h1, by omega⟩)
  have w₈ := e₈.wb_right
  have hk₈' : k₈ ≤ 602 * μ + 6 := by
    have := Nat.mul_le_mul_left 602 (log_le_of_half hμ1 (d := a + m / 2 - a) (by omega))
    omega
  have k₈' : ∀ r, (r < 170000 ∨ 170100 ≤ r) → (r < 10000 ∨ 10500 ≤ r) → c₈.nreg r = c.nreg r :=
    fun r h1 h2 => by
      rw [f₈ r (by omega) h2, r₇]
      simp only [upd, ite_eq_right (show r ≠ 170051 by omega), ite_eq_right (show r ≠ 170050 by omega)]
      exact k₆' r h1 h2
  have c870 : c₈.nreg 170070 = a + m := by
    rw [f₈ _ (by decide) (by decide), r₇]; simp only [upd]; exact c670
  have c872 : c₈.nreg 170072 = a + m / 2 := by
    rw [f₈ _ (by decide) (by decide), r₇]; simp only [upd]; exact c672
  set v₈ := c₈.nreg 170046 with hv₈
  -- 6. the cover of `[mid, a + m]`
  obtain ⟨c₉, k₉, e₉, hk₉, x₉, y₉, r₉⟩ : ∃ c₉ k₉, Exec P W
      (block [.copyN 170050 170072, .copyN 170051 170070]) c₈ c₉ k₉ ∧ k₉ = 2 ∧
      c₉.nreg 170050 = a + m / 2 ∧ c₉.nreg 170051 = a + m ∧
      c₉ = { c₈ with nreg := upd (upd c₈.nreg 170050 (a + m / 2)) 170051 (a + m) } := by
    exec_block
    refine ⟨rfl, by config_simp; exact c872, by config_simp; exact c870, ?_⟩
    rw [c872, c870]
  have w₉ := e₉.wb_right
  have S₉ : TEnv P W O s c₉ := by
    rw [r₉]; exact tenv_upd (tenv_upd S₈ _ (by norm_num) (by decide)) _ (by norm_num) (by decide)
  have c946 : c₉.nreg 170046 = v₈ := by rw [r₉]; simp [upd]; rfl
  have yv₆ : IOrc.Y P v₆ ≤ IOrc.Y P v₈ := by rw [← c746]; exact y₈
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, S₁₀, g₁₀, n₁₀, cov₁₀, f₁₀, y₁₀, m₁₀⟩ := topLoop_exec
    (G := fun v => a ≤ v ∧ v ≤ a + m) c₉ w₉ S₉ x₉ y₉ (by omega) (by omega)
    (hcap _ (by omega)) (by rw [c946]; exact g₈) (by rw [c946]; exact n₈)
    (by rw [c946]; exact cov₈ _ (by omega) le_rfl)
    (by rw [c946]; exact hv₆Y.2.trans yv₆)
    (fun v h1 h2 => ⟨by omega, h2⟩)
  have w₁₀ := e₁₀.wb_right
  have hk₁₀' : k₁₀ ≤ 602 * μ + 6 := by
    have := Nat.mul_le_mul_left 602 (log_le_of_half hμ1 (d := a + m - (a + m / 2)) (by omega))
    omega
  have k₁₀' : ∀ r, (r < 170000 ∨ 170100 ≤ r) → (r < 10000 ∨ 10500 ≤ r) →
      c₁₀.nreg r = c.nreg r := fun r h1 h2 => by
    rw [f₁₀ r (by omega) h2, r₉]
    simp only [upd, ite_eq_right (show r ≠ 170051 by omega), ite_eq_right (show r ≠ 170050 by omega)]
    exact k₈' r h1 h2
  set v₁₀ := c₁₀.nreg 170046 with hv₁₀
  have yv₈ : IOrc.Y P v₈ ≤ IOrc.Y P v₁₀ := by rw [← c946]; exact y₁₀
  -- 7. the offset
  obtain ⟨c₁₁, k₁₁, e₁₁, hk₁₁, v13⟩ : ∃ c₁₁ k₁₁, Exec P W (block [.subN 218013 170046 218004])
      c₁₀ c₁₁ k₁₁ ∧ k₁₁ = 1 ∧ c₁₁.nreg 218013 = c₁₀.nreg 170046 - c₁₀.nreg 218004 := by
    exec_block
    exact ⟨rfl, by config_simp⟩
  have ex : Exec P W gTop c c₁₁ (k₁ + (k₂ + (k₃ + (k₄ + (1 + (k₆ + (k₇ + (k₈ + (k₉ + (k₁₀ +
      k₁₁)))))))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉
      (.seq e₁₀ e₁₁)))))))))
  have a₁₀ : c₁₀.nreg 218004 = a := k₁₀' _ (by norm_num) (by norm_num)
  rw [a₁₀] at v13
  refine ⟨_, _, ex, by omega, exec_frameB ex wr_gTop, ?_, fun j hj => ?_⟩
  · rw [v13]; omega
  · rw [v13, show a + (v₁₀ - a) = v₁₀ by omega]
    by_cases hj2 : a + j ≤ a + m / 2
    · exact (cov₈ _ (by omega) hj2).trans yv₈
    · exact cov₁₀ _ (by omega) (by omega)

end exec

end

end DrvP

end Chazelle.Core
