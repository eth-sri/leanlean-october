module

public import Chazelle.MacT
public import Chazelle.Core.GranInitL5
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.SweepPrimKer

section
set_option hygiene false
local macro "zqbgb" : tactic => `(tactic| refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl⟩)
local macro "zqbgc" : tactic => `(tactic| (simp only [upd]; grind))
local macro "zqbgd" : tactic => `(tactic| have m₁' : ztdbm := by_grind)
local macro "zqbge" : tactic => `(tactic| (have w₁ := e₁.wb_right
                                           have fr₁ : zthoe := exec_frameB e₁ by_decide))
set_option hygiene true

/-!
# WP-G, part 16: the downward dyadic sweep on the RAM

`dyDn emit` hands the blocks of a dyadic cover of `[q₀ - L, q₀)`, from the top `q₀` down, to
`emit`, as pieces of the walk from the vertex `c₀` (`dyDn_exec`): at most `2 (log₂ L + 1)`
pieces, chained from `c₀` to `c₀ + L`, each valid by the hypothesis `hblk` on blocks.
-/
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK NFLoc
@[expose] public section
def dnPc (c₀ q₀ g b e : ℕ) : Pc :=
  ⟨⟨c₀ + ztyro, 0⟩, ⟨c₀ + ztyro + 2 ^ g, 0⟩,
    if 0 < g then 1 else 0, e, b * 2 ^ g, 0, 2 ^ g⟩

/-- The validity of the blocks of a downward sweep. -/
def DnBlocks (Pv : Pc → Prop) (m₀ : ℕ → ℕ) (W A₀ Tb c₀ q₀ L : ℕ) : Prop :=
  ∀ g b, q₀ - L ≤ b * 2 ^ g → ztds * 2 ^ g ≤ q₀ →
    ztezp ∧
      ∀ e, ztgqn → Pv (dnPc c₀ q₀ g b e)
variable {P : Polygon} {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop} {I : List Pc → Config → Prop}
/-- **The odd branch**: the block `(g, qq - 1)` below `y` is handed to `emit`. -/
theorem dn_odd
 (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb q₀ L c₀ : ℕ} {ps : List Pc} (hblk : DnBlocks Pv m₀ W A₀ Tb c₀ q₀ L)
    (hW : c₀ + L + 2 ≤ W) (_hW' : 3 * L + 4 ≤ W) (hA : A₀ ≤ W) (hLq : L ≤ q₀) {y g qq : ℕ}
    (d₁ : Config) (w₁ : WordsBounded W d₁) (hm : ∀ a, a < A₀ → d₁.nmem a = m₀ a)
    (h90 : d₁.nreg 150090 = 0) (h91 : d₁.nreg 150091 = 1) (h34 : d₁.nreg 150034 = Tb)
    (h81 : d₁.nreg 150081 = y) (h82 : d₁.nreg 150082 = g) (h83 : d₁.nreg 150083 = qq)
    (h84 : d₁.nreg 150084 = 2 ^ g) (h85 : d₁.nreg 150085 = c₀ + ztdvw)
    (hy : y = qq * 2 ^ g) (hyq : y ≤ q₀) (hxy : q₀ - L + 2 ^ g ≤ y) (hI : I ps d₁) :
    ∃ d₅ k₅ e, Exec P W (dnOdd emit) d₁ d₅ k₅ ∧ k₅ ≤ K + 20 ∧ Pv (dnPc c₀ q₀ g zthjp e) ∧
      I (ps ++ [dnPc c₀ q₀ g zthjp e]) d₅ ∧ d₅.nreg 150081 = y - 2 ^ g ∧
      d₅.nreg 150085 = c₀ + ztdvw + 2 ^ g ∧
      (∀ r, (ztbdq ∨ r = 150080 ∨ r = 150082 ∨ r = 150083 ∨
        r = 150086 ∨ r = 150090 ∨ r = 150091) → d₅.nreg r = d₁.nreg r) ∧
      ztiui := by
  zubdt
  have hq1 : 1 ≤ qq := by
    grind
  have hyb : (qq - 1 + 1) * 2 ^ g = y := by_simp_all
  have hyl : zthjp * 2 ^ g = y - 2 ^ g := by_grind
  obtain ⟨hblk1, hblk2⟩ := hblk g zthjp by_omega by_omega
  obtain ⟨d₂, k₂, e₂, hk₂, n77, n78, g2, nm⟩ : ∃ d₂ k₂, Exec P W
      ztirf d₁ d₂ k₂ ∧ k₂ = 2 ∧
      d₂.nreg 150077 = qq - 1 ∧ d₂.nreg 150078 = y - 2 ^ g ∧
      (∀ r, r ≠ 150077 → r ≠ 150078 → d₂.nreg r = d₁.nreg r) ∧ d₂.nmem = d₁.nmem := by
    exec_block
    zqbgb
    · config_simp; omega
    · config_simp; omega
    · zqbgc
  zue
  obtain ⟨d₃, k₃, e₃, hk₃, v50, v51, v52, v53, v54, v55, v56, v57, v58, r₃, m₃⟩ :=
    pcBlock_exec (P := P) d₂ w₂ 150078 0 ztbh by_omega
      by_grind
      by_grind
      (fun hg => by
        grind)
  rw [g2 _ by_omega by_omega] at v50 v52 v54 v58 v55
  rw [g2 _ by_omega by_omega] at v52
  set pc := dnPc c₀ q₀ g zthjp ztvpj with hpc
  have hpcR : PcRegs d₃ pc := by
    refine ztfaf
    · zuoay; zuonl
    · zuntp; zuonl
    · zugxi
    · rw [v56, n78, hpc]; simp [dnPc, hyl]
    · zuina
  zuiyy
  have fr₃ : ztuku := (exec_frameB e₂ by_decide).trans ztduk
  zubxl
  zucc
  have back : ∀ r, Keep r → r ≠ 150077 → r ≠ 150078 → zteux →
      r ≠ 150075 → r ≠ 150076 → d₄.nreg r = d₁.nreg r := by_grind
  have q81 : d₄.nreg 150081 = y := by rw [back _ ztbh by_omega by_omega
    by_omega by_omega by_omega, h81]
  have q84 : ztrgq := by rw [back _ ztbh by_omega by_omega
    by_omega by_omega by_omega, h84]
  have q85 : d₄.nreg 150085 = c₀ + ztdvw := by rw [back _ ztbh by_omega
    by_omega by_omega by_omega by_omega, h85]
  obtain ⟨d₅, k₅, e₅, hk₅, a81, a85, r₅, m₅⟩ : ∃ d₅ k₅, Exec P W
      ztirg d₄ d₅ k₅ ∧ k₅ = 2 ∧
      d₅.nreg 150081 = y - 2 ^ g ∧ d₅.nreg 150085 = c₀ + ztdvw + 2 ^ g ∧
      (∀ r, r ≠ 150081 → r ≠ 150085 → d₅.nreg r = d₄.nreg r) ∧ d₅.nmem = d₄.nmem := by
    exec_block
    all_goals first | (config_simp; rw [q85, q84]; omega) | skip
    zqbgb
    · config_simp; grind
    · config_simp; omega
    · zqbgc
  refine ⟨d₅, k₂ + ztlg, d₃.nreg 150055, .seq e₂ ztbpd,
    by omega, hpv, hE.stable _ _ _ hI₄ zttjx, a81, a85, ?_, ?_⟩
  · zuz
    rw [r₅ r by_omega by_omega, back r ztii by_omega by_omega
      by_omega by_omega by_omega]
  grind

/-! ## The ascending sweep of the downward cover -/

/-- The invariant of the ascending sweep of the downward cover. -/
def DnA (W : ℕ) (Pv : Pc → Prop) (I : List Pc → Config → Prop) (ps₀ : List Pc)
    (m₀ : ℕ → ℕ) (A₀ Tb Hb Pb tg q₀ L c₀ : ℕ) (cc d : Config) : Prop :=
  WordsBounded W d ∧ SwRegs Tb Hb Pb m₀ A₀ cc d ∧
    ∃ y g ps', d.nreg 150080 = q₀ - L ∧ d.nreg 150081 = y ∧ d.nreg 150082 = g ∧
      y = d.nreg 150083 * 2 ^ g ∧ d.nreg 150084 = 2 ^ g ∧ d.nreg 150085 = c₀ + ztdvw ∧
      d.nreg 150087 = q₀ - L + 2 ^ g ∧ d.nreg 150088 = y + 1 ∧ q₀ - L ≤ y ∧ y ≤ q₀ ∧
      I ztcdl d ∧ Chained ztcxt ps' ztzih ∧ ztbqq ∧
      ps'.length ≤ g ∧ ztyfa ∧ g ≤ tg + 1

/-- The tail block of a step of the ascending sweep of the downward cover. -/
def dnATail : Stmt := block [.addN 150082 150082 150091, .addN 150075 150036 150082,
  .loadN 150084 150075, .copyN 150083 150086, .addN 150087 150080 150084,
  .addN 150088 150081 150091]
theorem dnABody_eq (emit : Stmt) : dnABody emit =
    .seq ztbus
      (.seq ztlzw dnATail) := rfl
theorem dnATail_exec {W A₀ Pb g x y : ℕ} {m₀ : ℕ → ℕ} (d : Config)
    (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a) (h36 : d.nreg 150036 = Pb)
    (h82 : d.nreg 150082 = g) (h80 : d.nreg 150080 = x) (h81 : d.nreg 150081 = y)
    (h91 : d.nreg 150091 = 1)
    (hpow : m₀ ztzuq = 2 ^ ztbs ∧ Pb + ztbs < A₀) (hA : A₀ ≤ W)
    (hxW : x + 2 ^ ztbs ≤ W) (hyW : y + 1 ≤ W) :
    ∃ d' k, Exec P W dnATail d d' k ∧ k = 6 ∧ d'.nreg 150082 = g + 1 ∧
      d'.nreg 150084 = 2 ^ ztbs ∧ d'.nreg 150083 = d.nreg 150086 ∧
      d'.nreg 150087 = x + 2 ^ ztbs ∧ d'.nreg 150088 = y + 1 ∧
      (∀ r, r ≠ 150075 → r ≠ 150082 → r ≠ 150083 → r ≠ 150084 → r ≠ 150087 → r ≠ 150088 →
        d'.nreg r = d.nreg r) ∧ d'.nmem = d.nmem := by
  zulla
  unfold dnATail
  exec_block
  all_goals first | (config_simp; rw [h82, h91]; omega) | (config_simp; rw [h82, h91, h36]; omega) |
    (config_simp; rw [h82, h91, h80, h36, hm _ hpow.2, hpow.1]; omega) |
    (config_simp; rw [h81, h91]; omega) | skip
  simp_all

/-- **After the optional block** of the ascending sweep of the downward cover. -/
theorem dnA_after
 (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb Hb Pb tg q₀ L c₀ : ℕ} {ps₀ : List Pc} {cc : Config}
    (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 2 * P.n + 4 ≤ W)
    (hq : q₀ ≤ P.n) (d₅ : Config) (w₅ : WordsBounded W d₅) (y' h' g : ℕ) (ps'' : List Pc)
    (hgt : g ≤ tg) (hgL : 2 ^ g ≤ L)
    (m₅ : ∀ a, a < A₀ → d₅.nmem a = m₀ a) (s₅ : ∀ r, 150000 ≤ r → r < 150044 → d₅.nreg r = cc.nreg r)
    (a90 : d₅.nreg 150090 = 0) (a91 : d₅.nreg 150091 = 1) (a34 : d₅.nreg 150034 = Tb)
    (a35 : d₅.nreg 150035 = Hb) (a36 : d₅.nreg 150036 = Pb) (a82 : d₅.nreg 150082 = g)
    (a80 : d₅.nreg 150080 = q₀ - L) (a81 : d₅.nreg 150081 = y')
    (a85 : d₅.nreg 150085 = c₀ + zttxg)
    (hy' : y' = h' * 2 ^ ztbs) (a86 : d₅.nreg 150086 = h') (hq' : q₀ - L ≤ y') (hy'q : y' ≤ q₀)
    (hI₅ : I ztlru d₅) (hch₅ : Chained ztcxt ps'' ⟨c₀ + zttxg, 0⟩)
    (hv₅ : ∀ pc ∈ ps'', Pv pc) (hl₅ : ps''.length ≤ g + 1) :
    ∃ d₆ k₆, Exec P W dnATail d₅ d₆ k₆ ∧ k₆ = 6 ∧
      DnA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d₆ ∧ d₆.nreg 150082 = g + 1 := by
  zudzl

  obtain ⟨d₆, k₆, e₆, hk₆, b82, b84, b83, b87, b88, r₆, m₆⟩ := dnATail_exec (P := P)
    (x := q₀ - L) (y := y') d₅ w₅ m₅ a36 a82 a80 a81 a91 ztuhz env.aW
    by_omega by_omega
  zuffo

  refine ⟨d₆, k₆, e₆, hk₆, ⟨e₆.wb_right, ⟨fun a ha => by_grind,
    by grind,
    by grind,
    by grind,
    by grind,
    by grind,
    by grind⟩,
    y', g + 1, ps'',
    by grind,
    by grind,
    b82, by_grind, b84,
    by grind,
    b87, b88, hq', hy'q, hE.stable _ _ _ hI₅ fr₆, hch₅, hv₅, hl₅, by_grind,
    by omega⟩, b82⟩

/-- **One step of the ascending sweep of the downward cover.** -/
theorem dnABody_exec
 (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb Hb Pb tg q₀ L c₀ : ℕ} {ps₀ : List Pc} {cc d : Config}
    (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) (hblk : DnBlocks Pv m₀ W A₀ Tb c₀ q₀ L)
    (hq : q₀ ≤ P.n) (hLq : L ≤ q₀) (hLtg : L ≤ 2 ^ tg) (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 2 * P.n + 4 ≤ W)
    (hI : DnA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d)
    (ht : d.nreg 150087 < d.nreg 150088) :
    ∃ d' k, Exec P W (dnABody emit) d d' k ∧ DnA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d' ∧
      k ≤ K + 40 ∧ Nat.log 2 L + 1 - d'.nreg 150082 < Nat.log 2 L + 1 - d.nreg 150082 := by
  obtain ⟨hw, ⟨hm, hk0, h90, h91, h34, h35, h36⟩, y, g, ps', h80, h81, h82, hy, h84, h85, h87,
    h88, hqy, hyq, hI', hch, hv, hlen, hg1, hgtg⟩ := hI
  zuiim
  zubdt
  zudde

  have hqqy : d.nreg 150083 ≤ y := by rw [hy]; exact Nat.le_mul_of_pos_right _ hp
  zuegn

  obtain ⟨d₁, k₁, e₁, hk₁, o75, o86, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W (block [.addN 150075 150035 150083,
      .loadN 150086 150075, .addN 150075 150086 150086]) d d₁ k₁ ∧ k₁ = 3 ∧
      d₁.nreg 150075 = d.nreg 150083 / 2 + d.nreg 150083 / 2 ∧
      d₁.nreg 150086 = d.nreg 150083 / 2 ∧
      ztgsj ∧ d₁.nmem = d.nmem := by
    exec_block
    all_goals first | (config_simp; rw [h35, hm _ by_omega, hh1]; omega) |
      (config_simp; rw [h35]; omega) | skip
    zqbgb
    · config_simp; grind
    · config_simp; grind
    · zqbgc
  zqbge
  zugnr
  zqbgd
  rw [dnABody_eq]
  zudwz
  · obtain ⟨d₅, k₅, e, e₅, hk₅, hpv, hI₅, a81, a85, r₅, m₅⟩ := dn_odd hE
      hblk by_omega by_omega hA hLq d₁ w₁ m₁'
      by_grind by_grind
      by_grind by_grind
      by_grind by_grind
      by_grind by_grind
      hy hyq by_omega ztcij
    have kk : ∀ r, (ztbdq ∨ r = 150080 ∨ r = 150082 ∨
        r = 150090 ∨ r = 150091) → d₅.nreg r = d.nreg r := fun r hr => by
      zugfh
    zuef
    obtain ⟨d₆, k₆, e₆, hk₆, hU, b82⟩ := dnA_after hE env hW hW' hq d₅ w₅ _
      _ g _ hgt hgL
      ztxl
      ztgjp
      by_grind by_grind
      by_grind by_grind
      by_grind by_grind
      by_grind a81 ztheo
      (by zuonm; have : ztyuq := by_omega
          nth_rewrite 1 [this]; rw [Nat.add_mul, one_mul, Nat.add_sub_cancel]; ring)
      by_grind by_omega by_omega
      ztljc
      (by
        have hq1 : 1 ≤ d.nreg 150083 := by
          omega
        have h2 := hch.append (dnPc c₀ q₀ g ztroj e) (by
          simp [dnPc, Nat.sub_add_cancel hq1, ← hy])
        have he : (dnPc c₀ q₀ g ztroj e).e = ⟨c₀ + (q₀ - (y - 2 ^ g)), 0⟩ := by
          simp only [dnPc, Nat.sub_add_cancel hq1, ← hy, WPos.mk.injEq, and_true]; omega
        grind)
      (fun p hp => by
        zutk
        · grind
        · zvnns at hp; grind)
      ztbaw
    exact ⟨d₆, k₁ + ztzzq, .seq e₁ (.seq (.ifLtN_true (by
        grind) e₅) e₆), hU, by_omega,
      by omega⟩
  · obtain ⟨d₆, k₆, e₆, hk₆, hU, b82⟩ := dnA_after hE env hW hW' hq d₁ w₁ y
      _ g ps' hgt hgL m₁'
      ztfyg
      by_grind by_grind
      by_grind by_grind
      by_grind by_grind
      by_grind by_grind
      by_grind
      (by zuonm; have : ztzjh := by_omega
          grind)
      o86 hqy hyq ztcij hch hv by_omega
    exact ⟨d₆, k₁ + ztzzd, .seq e₁ (.seq (.ifLtN_false (by
        grind) (.skip w₁)) e₆), hU, by_omega,
      by omega⟩

/-! ## The descending sweep of the downward cover -/

/-- The invariant of the descending sweep of the downward cover. -/
def DnB (W : ℕ) (Pv : Pc → Prop) (I : List Pc → Config → Prop) (ps₀ : List Pc)
    (m₀ : ℕ → ℕ) (A₀ Tb Hb Pb tg q₀ L c₀ : ℕ) (cc d : Config) : Prop :=
  WordsBounded W d ∧ SwRegs Tb Hb Pb m₀ A₀ cc d ∧
    ∃ y g ps', d.nreg 150080 = q₀ - L ∧ d.nreg 150081 = y ∧ d.nreg 150082 = g ∧
      y = d.nreg 150083 * 2 ^ g ∧ d.nreg 150085 = c₀ + ztdvw ∧
      q₀ - L ≤ y ∧ y ≤ q₀ ∧ y < q₀ - L + 2 ^ g ∧
      I ztcdl d ∧ Chained ztcxt ps' ztzih ∧ ztbqq ∧
      ps'.length + g ≤ 2 * ztbdz ∧ g ≤ tg + 1 ∧ 2 ^ g ≤ 2 * L + 1
theorem dnBBody_eq (emit : Stmt) : dnBBody emit =
    .seq (block [.subN 150082 150082 150091, .addN 150075 150036 150082, .loadN 150084 150075,
      .addN 150083 150083 150083, .addN 150087 150080 150084, .addN 150088 150081 150091])
    ztfei :=
  rfl

/-- **One step of the descending sweep of the downward cover.** -/
theorem dnBBody_exec
 (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb Hb Pb tg q₀ L c₀ : ℕ} {ps₀ : List Pc} {cc d : Config}
    (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) (hblk : DnBlocks Pv m₀ W A₀ Tb c₀ q₀ L)
    (hq : q₀ ≤ P.n) (hLq : L ≤ q₀) (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 2 * P.n + 4 ≤ W)
    (hI : DnB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d)
    (ht : d.nreg 150090 < d.nreg 150082) :
    ∃ d' k, Exec P W (dnBBody emit) d d' k ∧ DnB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d' ∧
      k ≤ K + 40 ∧ d'.nreg 150082 < d.nreg 150082 := by
  obtain ⟨hw, ⟨hm, hk0, h90, h91, h34, h35, h36⟩, y, g, ps', h80, h81, h82, hy, h85,
    hxy, hyq, hyx, hI', hch, hv, hlen, hgt, hgb⟩ := hI
  zusm

  have hy2 : y = zthjo * 2 ^ g' := by_grind
  have hqqy : qq + qq ≤ y := by rw [hy2]; exact Nat.le_mul_of_pos_right _ hp
  zukce
  have hyx' : y < q₀ - L + 2 * 2 ^ g' := by_omega
  obtain ⟨d₁, k₁, e₁, hk₁, o82, o84, o83, o87, o88, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W
      (block [.subN 150082 150082 150091, .addN 150075 150036 150082, .loadN 150084 150075,
        .addN 150083 150083 150083, .addN 150087 150080 150084, .addN 150088 150081 150091])
      d d₁ k₁ ∧ k₁ = 6 ∧ d₁.nreg 150082 = g' ∧ d₁.nreg 150084 = 2 ^ g' ∧
      d₁.nreg 150083 = qq + qq ∧ d₁.nreg 150087 = q₀ - L + 2 ^ g' ∧ d₁.nreg 150088 = y + 1 ∧
      (∀ r, r ≠ 150075 → r ≠ 150082 → r ≠ 150083 → r ≠ 150084 → r ≠ 150087 → r ≠ 150088 →
        d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem := by
    exec_block
    all_goals first | (config_simp; rw [h82, h91, Nat.add_sub_cancel, h36]; omega) |
      (config_simp; omega) | (config_simp; rw [h81, h91]; omega) |
      (config_simp; rw [h82, h91, Nat.add_sub_cancel, h36, h80, hm _ by_omega, hp1]; omega) | skip
    refine zteha
    · config_simp; omega
    · config_simp; grind
    · rfl
    · config_simp; grind
    · config_simp; omega
    · zqbgc
  zqbge
  have k : ∀ r, (ztbdq ∨ r = 150080 ∨ r = 150081 ∨ r = 150085 ∨
      r = 150090 ∨ r = 150091) → d₁.nreg r = d.nreg r := by_grind
  zqbgd
  rw [dnBBody_eq]
  zuhth
  · zufgz

    obtain ⟨d₅, k₅, e, e₅, hk₅, hpv, hI₅, a81, a85, r₅, m₅⟩ := dn_odd hE
      hblk by_omega by_omega hA hLq d₁ w₁ m₁'
      by_grind by_grind
      by_grind by_grind o82 o83 o84
      by_grind hy2 hyq by_omega ztcij
    zuef
    have e₆ := Exec.subN (P := P) w₅ 150083 150083 150091
    set d₆ := ({ d₅ with nreg := upd d₅.nreg 150083 _ } :
      Config) with hd₆
    zudcu
    have b83 : d₆.nreg 150083 = qq + qq - 1 := by
      zuntq
      rw [r₅ _ by_omega, r₅ _ by_omega, o83, k _ by_omega, h91]
    have kk : ∀ r, (ztbdq ∨ r = 150080 ∨ r = 150090 ∨ r = 150091) →
        d₆.nreg r = d.nreg r := fun r hr => by
      rw [g6 r by_omega, r₅ r by_omega, k r by_omega]
    have hq1 : 1 ≤ qq + qq := by
      grind
    have hyl : ztglj * 2 ^ g' = y - 2 ^ g' := by rw [Nat.sub_mul, one_mul, hy2]
    refine ⟨d₆, k₁ + (ztett + 1), .seq e₁ (.ifLtN_true hodd ztcsd), ⟨e₆.wb_right,
      ⟨fun a ha => by zuonn; grind,
        fun r h1 h2 => (kk r by_omega).trans by_grind,
        by zumxu; omega, by zumxu; omega,
        by zumxu; omega, by zumxu; omega,
        by zumxu; omega⟩,
      y - 2 ^ g', g', ps' ++ [dnPc c₀ q₀ g' ztglj e],
      by zumxu; omega, by zunfs; omega,
      by rw [g6 _ by_omega, r₅ _ by_omega]; omega,
      by grind, by rw [g6 _ by_omega, a85]; omega, by_omega, by_omega, by_omega,
      hE.stable _ _ _ by_grind ztnyb,
      ?_, ?_, by simp; omega, by_omega, by_omega⟩, by_omega, ?_⟩
    · have h2 := hch.append (dnPc c₀ q₀ g' ztglj e) (by
        simp [dnPc, Nat.sub_add_cancel hq1, ← hy2])
      have he : (dnPc c₀ q₀ g' ztglj e).e = ⟨c₀ + (q₀ - (y - 2 ^ g')), 0⟩ := by
        simp only [dnPc, Nat.sub_add_cancel hq1, ← hy2, WPos.mk.injEq, and_true]; omega
      grind
    · zuda
      zutk
      · grind
      · zvnns at hp; grind
    · rw [g6 _ by_omega, r₅ _ by_omega, o82, h82]; omega
  · zufgz

    refine ⟨d₁, k₁ + ztdeu, .seq e₁ ztzrt, ⟨w₁,
      ⟨m₁', by_grind,
        by grind, by_grind,
        by grind, by_grind,
        by grind⟩,
      y, g', ps', by_grind, by_grind, o82,
      by grind, by_grind, hxy, hyq, by_omega,
      hE.stable _ _ _ hI' fr₁, hch, hv, by_omega, by_omega, by_omega⟩, by_omega,
      by omega⟩

/-! ## The downward cover -/
theorem dyDn_eq (emit : Stmt) : dyDn emit =
    .seq (block [.copyN 150081 150070, .subN 150080 150070 150071, .addN 150088 150081 150091,
      .constN 150082 0, .copyN 150083 150070, .constN 150084 1, .copyN 150085 150040,
      .addN 150087 150080 150084])
    (.seq ztncx
      ztzsh) := rfl

/-- **The downward dyadic cover** of `[q₀ - L, q₀)` from the walk vertex `c₀`. -/
theorem dyDn_exec
 (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb Hb Pb tg q₀ L c₀ : ℕ} {ps₀ : List Pc} (c : Config)
    (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) (hblk : DnBlocks Pv m₀ W A₀ Tb c₀ q₀ L)
    (hq : q₀ ≤ P.n) (hLq : L ≤ q₀) (hLtg : L ≤ 2 ^ tg) (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 2 * P.n + 4 ≤ W)
    (hw : WordsBounded W c) (hm : ∀ a, a < A₀ → c.nmem a = m₀ a)
    (h90 : c.nreg 150090 = 0) (h91 : c.nreg 150091 = 1) (h34 : c.nreg 150034 = Tb)
    (h35 : c.nreg 150035 = Hb) (h36 : c.nreg 150036 = Pb) (h70 : c.nreg 150070 = q₀)
    (h71 : c.nreg 150071 = L) (h40 : c.nreg 150040 = c₀) (hI : I ps₀ c) :
    ∃ c' k ps', Exec P W ztvpg c c' k ∧ k ≤ ztlu * ztbdz + 20 ∧
      I ztcdl c' ∧ Chained ztcxt ps' ztrbq ∧ ztbqq ∧
      ps'.length ≤ 2 * ztbdz ∧ c'.nreg 150040 = c₀ + L ∧
      ztfjj ∧
      c'.nreg 150090 = 0 ∧ c'.nreg 150091 = 1 ∧ ztiud := by
  zumbh
  obtain ⟨c₁, k₁, e₁, hk₁, o81, o80, o88, o82, o83, o84, o85, o87, r₁, m₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 150081 150070, .subN 150080 150070 150071,
        .addN 150088 150081 150091, .constN 150082 0, .copyN 150083 150070, .constN 150084 1,
        .copyN 150085 150040, .addN 150087 150080 150084]) c c₁ k₁ ∧ k₁ = 8 ∧
      c₁.nreg 150081 = q₀ ∧ c₁.nreg 150080 = q₀ - L ∧ c₁.nreg 150088 = q₀ + 1 ∧
      c₁.nreg 150082 = 0 ∧ c₁.nreg 150083 = q₀ ∧ c₁.nreg 150084 = 1 ∧ c₁.nreg 150085 = c₀ ∧
      c₁.nreg 150087 = q₀ - L + 1 ∧
      ztgsf ∧ c₁.nmem = c.nmem := by
    exec_block
    all_goals first | (config_simp; rw [h70, h71]; omega) | (config_simp; rw [h70, h91]; omega) |
      (config_simp; rw [h70]; omega) | omega | skip
    refine ztedw
    all_goals first | (config_simp; rw [h70, h71]) | (config_simp; rw [h70, h91]) |
      (config_simp; rw [h70]) | (config_simp; rw [h40]) | config_simp | skip
    zqbgc
  zud
  have hA0 : DnA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ c c₁ :=
    ⟨w₁, ⟨by_simp_all, by_grind,
      by simp_all, by_simp_all,
      by simp_all, by_simp_all,
      by simp_all⟩, q₀, 0, [], o80, o81, o82, by_omega,
      by omega, by_omega, by_omega, o88, by_omega, le_rfl,
      by rw [List.append_nil]; exact hE.stable _ _ _ hI ztduj,
      by zupbe, by_simp, by_simp, Or.inl rfl, by_omega⟩
  -- phase A
  obtain ⟨c₂, k₂, e₂, hA2, hx₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (a := 150087) (b := 150088)
    (body := dnABody emit) (DnA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ c)
    ztjvs ztjje ztoe (fun d hd ht => by
      obtain ⟨d', k, ex, hU, hk, hμ⟩ := dnABody_exec hE env hblk hq hLq hLtg hW hW' hd ht
      grind) hA0
  obtain ⟨w₂, ⟨m₂, s₂, a90, a91, a34, a35, a36⟩, y, g, ps', a80, a81, a82, ay, a84, a85, a87, a88,
    aqy, ayq, aI, ach, av, alen, ag1, agt⟩ := hA2
  zuigw
  have hglog : ztpou := by
    zudrx
    · omega
    · zujct
      · grind
      · have := Nat.le_log_of_pow_le by_norm_num h; omega
  have hB0 : DnB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ c c₂ :=
    ⟨w₂, ⟨m₂, s₂, a90, a91, a34, a35, a36⟩, y, g, ps', a80, a81, a82, ay, a85, aqy, ayq,
      by omega, aI, ach, av, by_omega, agt, by
        zueva
        · grind
        · zudrx
          · omega
          · zufeu
            omega⟩
  -- phase B
  obtain ⟨c₃, k₃, e₃, hB3, hx₃, hk₃⟩ := Exec.whileLtN_bounded (P := P) (a := 150090) (b := 150082)
    (body := dnBBody emit) (DnB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ c)
    ztqnn ztjje ztoe (fun d hd ht => by
      obtain ⟨d', k, ex, hU, hk, hμ⟩ := dnBBody_exec hE env hblk hq hLq hW hW' hd ht
      grind) hB0
  obtain ⟨w₃, ⟨m₃, s₃, b90, b91, b34, b35, b36⟩, y₃, g₃, ps₃, b80, b81, b82, by₃, b85,
    bqy, byq, byx, bI, bch, bv, blen, bgt, bgb⟩ := hB3
  zucek

  have hyL : q₀ - y₃ = L := by_grind
  zuffl
  refine ⟨_, k₁ + ztdhs, ps₃, ?_, ?_,
    hE.stable _ _ _ bI ztjuw, by rw [hyL] at bch; omega, bv,
    by omega, by config_simp; omega, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
  · rw [dyDn_eq]; exact .seq e₁ ztcb
  · zucax

    have hk2' : ztyyv :=
      le_trans hk₂ by_simp
    have hk3' : ztyyw :=
      le_trans hk₃ (by zupbf; have := Nat.mul_le_mul_left ztfnt hglog; omega)
    grind
  · config_simp
    rw [upd_other _ _ _ h3, s₃ r h1 h2]
  · config_simp; omega
  · config_simp; omega
  omega
end
end ShootCut
end Chazelle.Core
end
namespace Chazelle.Core
@[expose] public section
open Set
open Chazelle.Chain (sideE sideInArc)
namespace ShootCut
def VPc (P : Polygon) (C : Chain) (m : ℕ → ℕ) (h γ : ℕ) (pc : Pc) : Prop :=
  PcOK P C m h γ pc ∧ pc.s.hgt = 0 ∧ pc.e.hgt = 0 ∧ pc.s.edge < pc.e.edge
theorem EmitOK.mono {P : Polygon} {W : ℕ} {emit : Machine.Stmt} {A₀ : ℕ} {Pv Pv' : Pc → Prop}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ Pv I K)
    (h : ∀ pc, Pv' pc → Pv pc) : EmitOK P W emit A₀ Pv' I K :=
  ⟨hE.stable, fun ps pc c hw hI hR hv => hE.run ps pc c hw hI hR (h pc hv)⟩
section Run
variable (C : Chain) {Q : Polygon} {H : Host}

/-- **The host point along a climbing stretch.** -/
theorem uOf_up (hP : C.P = H.poly Q) {i d : ℕ} (hJ : tJ C i + d ≤ C.m) {r a ℓ t : ℕ}
    (hr : r < H.length) (hrun : H[r] = .run a ℓ)
    (hu : zttx % C.P.n = NFLoc.preLen Q.n H r + t) (ht : t + d ≤ ℓ) :
    ztbfu % C.P.n = NFLoc.preLen Q.n H r + zthkq := by
  zubn

  zudvi
  zuey
  omega

/-- **The host point along a descending stretch.** -/
theorem uOf_down (hP : C.P = H.poly Q) {i d : ℕ} (hm : C.m ≤ tJ C i) (hJ : tJ C i + d ≤ 2 * C.m)
    {r a ℓ t : ℕ} (hr : r < H.length) (hrun : H[r] = .run a ℓ)
    (hu : zttx % C.P.n = NFLoc.preLen Q.n H r + t) (ht : t ≤ ℓ)
    (hdt : d ≤ t) :
    ztbfu % C.P.n = NFLoc.preLen Q.n H r + ztdwh := by
  zubn

  have hkd : ztzqb := by
    have := sideE_down C (d := d) hm hJ
    zucgr
    unfold sideE at *
    grind
  zubsn

  have e2 : C.s + ztzha =
      C.P.n * ztbaaz + ztyvh := by
    omega
  zuhld

/-- The tour position `i` is a **breakpoint**: a turn of the tour or a break host point. -/
def Brk (n : ℕ) (H : Host) (i : ℕ) : Prop :=
  tJ C i = 0 ∨ tJ C i = C.m ∨ HostBreak n H ztdim
variable {n : ℕ}
/-- **A break in a run.** -/
theorem brk_run {i r a ℓ t : ℕ} (hr : r < H.length) (hrun : H[r] = .run a ℓ)
    (hu : uOf C i = NFLoc.preLen n H r + t) (ht : t ≤ ℓ)
    (hc : t = 0 ∨ t = ℓ ∨ ztne % n = 0 ∨ ztne % n = n - 1) : Brk C n H i := by
  zulw
  zuizj
  rw [hrun] at hsucc
  zubiq
  refine ⟨r, hr, by_omega, by_omega, ?_⟩
  simp_all

/-- **A point item is a break.** -/
theorem brk_pt {i r : ℕ} {x : SymPt} (hr : r < H.length) (hpt : H[r] = .pt x)
    (hu1 : NFLoc.preLen n H r ≤ uOf C i) (hu2 : uOf C i < NFLoc.preLen n H ztgu) :
    Brk C n H i := by
  zulw
  refine ⟨r, hr, hu1, hu2, ?_⟩
  simp_all
end Run

/-! ## The blocks of a stretch -/
theorem lt_gradeCount {n g b : ℕ} (h : b * 2 ^ g + 2 ^ g ≤ n - 1) : b < gradeCount n g := by
  zubdt
  zulbt
  have : b * 2 ^ g ≤ n - 2 := by_omega
  have := (Nat.le_div_iff_mul_le hp).2 this
  omega
variable {O : OracleIface} {P : Polygon} {C : Chain} {m₀ : ℕ → ℕ} {h γ A₀ W : ℕ}

/-- The words of the entry of a processed block lie below `A₀`. -/
theorem entry_low (hR : Robust A₀ m₀ fun m' => GradeRaw O P m' h A₀) {γ g b : ℕ} (hg : 0 < g)
    (hγ : 2 ^ g ≤ γ) (hcap : γ ≤ 2 ^ ztczu) (hb : b * 2 ^ g + 2 ^ g ≤ P.n - 1) :
    m₀ zteu + g < A₀ ∧ m₀ (m₀ zteu + g) + 3 * b + 2 < A₀ := by
  obtain ⟨hΛ, -⟩ := block_grade (γ := γ) hg hγ hcap
  obtain ⟨-, h1, h2⟩ := grade_entry hR hΛ (lt_gradeCount hb)
  tauto

/-- **The blocks of a climbing stretch** are valid pieces for the upward sweep. -/
theorem upBlocks_of (hR : Robust A₀ m₀ fun m' => GradeRaw O P m' h A₀) (hAW : A₀ ≤ W)
    {c₀ q₀ L : ℕ} (hwalk : ∀ d, d ≤ L → (chainModel C).W.vtx zttiq = (Qof P).vtx (q₀ + d))
    (h6 : 6 ≤ c₀) (hcL : c₀ + L ≤ 2 * C.m + 6) (hqL : q₀ + L < P.n) (hLγ : L ≤ γ)
    (hcap : γ ≤ 2 ^ ztczu) :
    UpBlocks ztwp m₀ W A₀ ztzgo c₀ q₀ L := by
  zulmp
  zubdt
  zudmw
  refine ztkym
  · zucbj

  · refine ⟨blockUp_ok hwalk h6 hcL hqL hLγ hcap hlo hhi fun hg => he by_omega, rfl, rfl,
      by simp only [upPc]; omega⟩

/-- **The blocks of a descending stretch** are valid pieces for the downward sweep. -/
theorem dnBlocks_of (hR : Robust A₀ m₀ fun m' => GradeRaw O P m' h A₀) (hAW : A₀ ≤ W)
    {c₀ q₀ L : ℕ} (hwalk : ∀ d, d ≤ L → (chainModel C).W.vtx zttiq = (Qof P).vtx (q₀ - d))
    (h6 : 6 ≤ c₀) (hcL : c₀ + L ≤ 2 * C.m + 6) (hq : q₀ < P.n) (hLq : L ≤ q₀) (hLγ : L ≤ γ)
    (hcap : γ ≤ 2 ^ ztczu) :
    DnBlocks ztwp m₀ W A₀ ztzgo c₀ q₀ L := by
  zulmp
  zubdt
  zudmw
  refine ztkym
  · zucbj

  · refine ⟨blockDn_ok hwalk h6 hcL hq hLq hLγ hcap hlo hhi fun hg => he by_omega, rfl, rfl,
      by simp only [dnPc]; omega⟩
end ShootCut
open Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sidePrev sideNext sideLeft TouchesIn freeIn regionsIn)
open Chazelle.Geometry (lerp)
open WalkEmbed FuseMath
namespace FuseDeg
variable (J : Merge.Junction)

/-- A point of the domain of `C` off the slit of a side chain is in the domain of that chain. -/
theorem mem_side_dom {C' : Chain} (hC'P : C'.P = J.P) (hset : C'.set ⊆ J.whole.set) {x : Point}
    (hx : x ∈ J.whole.dom) (hxs : x ∉ C'.slit) : x ∈ C'.dom := by
  rw [Chain.mem_dom_iff] at hx ⊢
  refine ⟨?_, by_grind, hxs⟩
  rw [radius_of_P J hC'P]; simp_all

/-- **Half-balls transfer to a side chain**: a half-ball of the domain of `C` on the side `τ` of a
point gives a half-ball of the free set of `Sᵢ`, away from the slit of `Cᵢ`. -/
theorem halfIn_side (hP : J.P.Simple) {C' : Chain} (hC'P : C'.P = J.P)
    (hset : C'.set ⊆ J.whole.set) {Si : Set ztf} (hSiA : Si ⊆ (chainModel C').Adm)
    (hSifin : Si.Finite) {τ x h : ℝ} (hgood : HalfIn J.whole.dom τ (ztcon : Point))
    (hcol : h < C'.top.2 ∨ (τ = -1 ∧ h ≤ C'.top.2) ∨ x ≠ C'.top.1) :
    HalfIn ztjvg τ (ztcon : Point) := by
  zuftt
  obtain ⟨r, hr, hsub⟩ := hgood
  obtain ⟨r₂, hr₂, hch⟩ := chords_off_line (walkAx_chainModel hP') hSiA hSifin (ztcon : Point)
  obtain ⟨r₃, hr₃, hsl⟩ : ∃ r₃ > 0, ∀ y ∈ ball ((x, h) : Point) r₃,
      0 < τ * (y.2 - h) → y ∉ C'.slit := by
    rcases hcol with hc | ⟨hτ1, hc⟩ | hc
    · refine ⟨C'.top.2 - h, by_linarith, fun y hy _ hys => ?_⟩
      zuhvz
      zuedp

    · refine ⟨1, one_pos, fun y _ hy hys => ?_⟩
      zuhvz
      rw [hτ1] at hy
      linarith
    · refine ⟨|x - C'.top.1|, by_grind, fun y hy _ hys => ?_⟩
      have h1 := (C'.mem_slit_iff.1 hys).1
      zuedp

  refine ⟨min r (min r₂ r₃), by_grind, fun y hy hpos => ?_⟩
  have hy1 := ball_subset_ball ztff hy
  have hy2 := ball_subset_ball ztxju hy
  have hy3 := ball_subset_ball ztxjv hy
  have hyD := hsub y hy1 hpos
  refine ⟨mem_side_dom J hC'P hset hyD by_grind, fun hyS => hch y hy2 ?_ hyS⟩
  grind
variable {M : Model}
/-- The points of the domain between two points of the domain on an admissible chord. -/
theorem between_open (hM : WalkAx M) {f : Set Point} (hf : f ∈ M.Adm) {z z' : Point}
    (hz : z ∈ f) (hzD : z ∈ M.D) (hz' : z' ∈ f) (hz'D : z' ∈ M.D) {x : ℝ}
    (hx1 : min z.1 z'.1 ≤ x) (hx2 : x ≤ max z.1 z'.1) :
    (ztewp : Point) ∈ M.D := by
  obtain ⟨w, q, hce, hqy, hqw, hop, hwe, hqD⟩ := sigma_end hM hf ztp
  have hwD : w ∉ M.D := by
    obtain ⟨⟨p, t, hA, rfl⟩, -⟩ := hwe
    exact hM.trace p hA.1 t hA.2.1 hA.2.2.1.le
  simp only [one_mul] at hqw
  have hstrict : ∀ {y : Point}, y ∈ f → y ∈ M.D → y.2 = w.2 ∧ q.1 < y.1 ∧ y.1 < w.1 := by
    intro y hy hyD
    zvnme at hy
    obtain ⟨h1, h2, h3⟩ := mem_seg_sigma hqy ztp by_simp_all hy
    grind
  obtain ⟨hz2, hzq, hzw⟩ := hstrict hz hzD
  obtain ⟨-, hz'q, hz'w⟩ := hstrict hz' hz'D
  rw [hz2]
  refine (open_pt hqy ztp hop ?_ ?_).2
  · grind
  grind

/-! ## The region of `Sᵢ` on the side of `R` of a chord -/
open Classical in
/-- The side (`1` above, `-1` below) of the chord `f` on which the region `R` lies. -/
noncomputable def sideOf (M : Model) (R f : Set Point) : ℝ := if SideIn M R f 1 then 1 else -1
open Classical in
/-- A point of the chord `f` in the domain. -/
noncomputable def midOf (M : Model) (f : Set Point) : Point :=
  if h : ∃ z ∈ f, z ∈ M.D then Classical.choose h else 0
open Classical in
/-- **The region of `Sᵢ` on the side of `R` of the chord `f`** (in the side model `M'`): the
region containing the points just on that side of a point of `f` (`∅` if there is none). -/
noncomputable def Phi (M M' : Model) (Si : Set ztf) (R f : Set Point) : Set Point :=
  if h : ∃ U ∈ M'.regions Si, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (ztfeg : Point) ∈ U then
    Classical.choose h
  else ∅
theorem phi_mem_or_empty (M M' : Model) (Si : Set ztf) (R f : Set Point) :
    Phi M M' Si R f ∈ M'.regions Si ∨ Phi M M' Si R f = ∅ := by
  unfold Phi
  zus
  · grind
  simp

/-- The points of an admissible chord have its height. -/
theorem snd_eq_of_mem (hM : WalkAx M) {f : Set Point} (hf : f ∈ M.Adm) {z z' : Point}
    (hz : z ∈ f) (hz' : z' ∈ f) : z'.2 = z.2 := by
  obtain ⟨w, q, hce, hqy, hqw, -, -, -⟩ := sigma_end hM hf ztp
  zvnme at hz hz'
  exact (mem_seg_sigma hqy ztp hqw hz').1.trans (mem_seg_sigma hqy ztp hqw hz).1.symm

/-- **`Phi` is the region of `Sᵢ` just on the side of `R` of any point of `f`** (below the top of
`Cᵢ`). -/
theorem phi_eq (hP : J.P.Simple) {C' : Chain} (hC'P : C'.P = J.P) (hset : C'.set ⊆ J.whole.set)
    {Si : Set ztf} (hSiA : Si ⊆ (chainModel C').Adm) (hSifin : Si.Finite)
    {F : Set ztf} (hF : F ⊆ (chainModel J.whole).Adm) (hfin : F.Finite) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions F) {f : Set Point} (hf : f ∈ F) {τ : ℝ}
    (hτ : τ = 1 ∨ τ = -1) (hside : SideIn ztbm R f τ) {z₁ : Point} (hz₁ : z₁ ∈ f)
    (hz₁D : z₁ ∈ J.whole.dom) (hh : z₁.2 ≤ C'.top.2) {V : Set Point}
    (hV : V ∈ (chainModel C').regions Si)
    (hzV : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztokp : Point) ∈ V) :
    Phi ztbm ztbmo Si R f = V := by
  zuvv

  have hso : sideOf M R f = τ := by
    unfold sideOf
    zujj
    · simp_all
    · zucjw
      zudqd
      have := side_unique hM hF hfin hf hR hz₁ hz₁D ztp ztbt (h1 z₁ hz₁ hz₁D)
        (hside z₁ hz₁ hz₁D)
      grind
  have hex : ∃ z ∈ f, z ∈ M.D := ⟨z₁, hz₁, hz₁D⟩
  have hm : midOf M f ∈ f ∧ midOf M f ∈ M.D := by
    unfold midOf; grind
  set m := midOf M f with hmdef
  have hm2 := snd_eq_of_mem hM ztjxh hz₁ hm.1
  have hgood : ∀ x ∈ Icc (min z₁.1 m.1) (max z₁.1 m.1),
      HalfIn ztjvg τ (ztuec : Point) := by
    zuh
    have hxD := between_open hM ztjxh hz₁ hz₁D hm.1 hm.2 hx.1 hx.2
    refine halfIn_side J hP hC'P hset hSiA hSifin (halfIn_of_mem J.whole.isOpen_dom τ hxD) ?_
    rcases hh.lt_or_eq with hlt | heq
    · simp_all
    · zulw
      intro hx1
      apply (J.whole.mem_dom_iff.1 hxD).2.1
      have : (ztuec : Point) = C'.top := by_simp_all
      zvmwk; exact hset C'.top_mem_set
  obtain ⟨w, hw, h1, h2⟩ := strip_const hτ min_le_max hgood
  set W₀ := connectedComponentIn ztjvg w with hW₀
  have hW₀r : W₀ ∈ M'.regions Si := ztgps
  have hz₁W : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztokp : Point) ∈ W₀ := by
    zuiep
    · grind
    · rw [max_eq_left h] at h2; exact h2
  have hmW : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztode : Point) ∈ W₀ := by
    zumnp
    zuiep
    · rw [max_eq_right h] at h2; exact h2
    · rw [min_eq_right h] at h1; exact h1
  have hmeet : ∀ {X Y : Set Point}, X ∈ M'.regions Si → Y ∈ M'.regions Si → ∀ {p : Point},
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztoee : Point) ∈ X) →
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztoee : Point) ∈ Y) → X = Y := by
    intro X Y hX hY p hX' hY'
    obtain ⟨δ, h3, h4⟩ := (hX'.and hY').exists
    exact (Chazelle.Chain.regionsIn_eq_or_disjoint hX hY).resolve_right
      by_grind
  have hWV := hmeet hW₀r hV hz₁W hzV
  have hPhi : ∃ U ∈ M'.regions Si, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (ztfeg : Point) ∈ U := by
    zuoyc; exact ⟨W₀, hW₀r, hmW⟩
  unfold Phi
  rw [dite_eq_left hPhi]
  obtain ⟨hU, hUm⟩ := Classical.choose_spec hPhi
  have hUm' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztode : Point) ∈ Classical.choose hPhi :=
    hUm.mono by_grind
  rw [← hWV]
  exact hmeet hU hW₀r hUm' hmW

/-- **The parent of an exit chord of `R` in `Sᵢ` is an exit chord of `Phi f`** for an exit chord
`f` of `R` faced next to an attachment (the end of the chain of wedges of `R`). -/
theorem parent_touch (hP : J.P.Simple) {C' : Chain} (hC'P : C'.P = J.P)
    (hset : C'.set ⊆ J.whole.set) {Q : Polygon} {Si : Set ztf}
    (hSi : (chainModel C').ChordFamily Q Si) {F : Set ztf}
    (hF : F ⊆ (chainModel J.whole).Adm) (hfin : F.Finite)
    (hends : ∀ c ∈ Si, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions F) {e : Set Point} (he : e ∈ F)
    (hRe : TouchesIn J.whole.dom e R) {c : Set Point} (hc : c ∈ Si) (hec : e ⊆ c) :
    ∃ f ∈ F, TouchesIn J.whole.dom f R ∧
      (∃ (p : ℕ) (t : ℝ), SideAttach (chainModel J.whole).W f p t ∧
        Adj ztbm F R p t) ∧
      c ∈ exits ztbmo Si (Phi ztbm ztbmo Si R f) := by
  zuvv

  zuftt
  obtain ⟨y, a, b, hH, hy, hceq, hl, hr⟩ := Merge.augChords_spec ztqpq
  -- the side of `R`
  obtain ⟨τ, hτ, hsideE⟩ : ∃ τ : ℝ, (τ = 1 ∨ τ = -1) ∧ SideIn M R e τ := by
    obtain ⟨Up, Dn, hUp, hDn, -, hside, hiff⟩ := chordSides_of_system ztbip he
    rcases (hiff R hR).1 hRe with rfl | rfl
    · refine ⟨1, Or.inl rfl, fun z hz hzD => ?_⟩
      simp_all
    · refine ⟨-1, Or.inr rfl, fun z hz hzD => ?_⟩
      zugkn
      grind
  -- points of `e` in the domain are open points of `c`
  have hopen : ∀ z ∈ e, z ∈ M.D → z.2 = y ∧ a < z.1 ∧ z.1 < b := by
    zumht
    have hzc := hec hz
    rw [hceq] at hzc
    obtain ⟨hz2, hza, hzb⟩ := hzc
    refine ⟨hz2, lt_of_le_of_ne hza fun h => ?_, lt_of_le_of_ne hzb fun h => ?_⟩
    · have : z = Merge.lend c := by_grind
      exact (hends c hc).1 ztubz
    · have : z = Merge.rend c := by_grind
      exact (hends c hc).2 ztubz
  -- a direction away from the slit of `Cᵢ`
  obtain ⟨σ, hσ, hcol⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ z ∈ e, z ∈ M.D → ∀ x : ℝ,
      σ * z.1 ≤ σ * x → (y < C'.top.2 ∨ (τ = -1 ∧ y ≤ C'.top.2) ∨ x ≠ C'.top.1) := by
    by_cases hcase : y < C'.top.2 ∨ τ = -1
    · refine ⟨1, Or.inl rfl, fun z _ _ x _ => ?_⟩
      grind
    · push Not at hcase
      have hyt : y = C'.top.2 := by_grind
      have htop : C'.top.1 ≤ a ∨ b ≤ C'.top.1 := by
        zubq

        have hmem := hH.open_mem C'.top.1 h.1 h.2
        rw [hyt] at hmem
        exact C'.not_mem_set_of_mem_dom hmem C'.top_mem_set
      rcases htop with ht | ht
      · refine ⟨1, Or.inl rfl, fun z hz hzD x hx => Or.inr ztgej⟩
        grind
      · refine ⟨-1, Or.inr rfl, fun z hz hzD x hx => Or.inr ztgej⟩
        grind
  obtain ⟨f, hf, hRf, hadjf, hsidef, z₀, hz₀e, hz₀D, z₁, hz₁f, hz₁D, hz₁y, hσ01, hgood⟩ :=
    chain_end hM hF hfin hR hτ hσ _ e he hRe hsideE le_rfl
  obtain ⟨hz₀y, hz₀a, hz₀b⟩ := hopen z₀ hz₀e hz₀D
  -- the strip between `z₀` and `z₁`
  have hgood' : ∀ x : ℝ, σ * z₀.1 ≤ σ * x → σ * x ≤ σ * z₁.1 →
      HalfIn ztjvg τ (ztueb : Point) := by
    zuchi
    refine halfIn_side J hP hC'P hset hSi.2.1 hSi.1 (hgood x h1 h2) ?_
    grind
  obtain ⟨V, hV, hV₀, hV₁⟩ : ∃ V ∈ M'.regions Si,
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), (zthll : Point) ∈ V) ∧
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z₁.1, z₀.2 + τ * δ) : Point) ∈ V) := by
    zur
    · simp only [one_mul] at hσ01 hgood'
      obtain ⟨w, hw, h1, h2⟩ := strip_const hτ hσ01 fun x hx => hgood' x hx.1 hx.2
      exact ⟨_, ztgps, h1, h2⟩
    · simp only [neg_mul, one_mul, neg_le_neg_iff] at hσ01 hgood'
      obtain ⟨w, hw, h1, h2⟩ := strip_const hτ hσ01 fun x hx => hgood' x hx.2 hx.1
      exact ⟨_, ztgps, h2, h1⟩
  have hPhi : Phi M M' Si R f = V := by
    refine phi_eq J hP hC'P hset hSi.2.1 hSi.1 hF hfin hR hf hτ hsidef hz₁f hz₁D
      by_grind hV ?_
    rw [hz₁y]; omega
  refine ⟨f, hf, hRf, hadjf, hc, z₀, ⟨hec hz₀e, ?_⟩, ?_⟩
  · show z₀ ∈ C'.dom
    have : z₀ = (ztkhp : Point) := by_grind
    zvmwk; exact hH.open_mem z₀.1 hz₀a hz₀b
  · rw [hPhi]
    have htend : Tendsto (fun δ : ℝ => ((z₀.1, z₀.2 + τ * δ) : Point)) (𝓝[>] (0 : ℝ)) (𝓝 z₀) := by
      have : Tendsto (fun δ : ℝ => (zthll : Point)) _
          (𝓝 ((z₀.1, z₀.2 + τ * 0) : Point)) :=
        ((continuous_const.prodMk (continuous_const.add
          ztqjx)).tendsto 0)
      rw [mul_zero, add_zero] at this
      zuhv
    exact mem_closure_of_tendsto htend hV₀

/-- The exit chords of `R` next to one of whose attachments `R` is faced. -/
def adjExits (M : Model) (F : Set ztf) (R : Set Point) : Set ztf :=
  {f | f ∈ exits M F R ∧ ∃ (p : ℕ) (t : ℝ), SideAttach M.W f p t ∧ Adj M F R p t}

/-- **The parents in `Sᵢ` of the exit chords of `R`** are at most `D` times as many as the exit
chords of `R` faced next to an attachment. -/
theorem parents_ncard_le (hP : J.P.Simple) {C' : Chain} (hC'P : C'.P = J.P)
    (hset : C'.set ⊆ J.whole.set) {Q : Polygon} {Si : Set ztf}
    (hSi : (chainModel C').ChordFamily Q Si) {F : Set ztf}
    (hF : F ⊆ (chainModel J.whole).Adm) (hfin : F.Finite)
    (hends : ∀ c ∈ Si, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions F) {D : ℕ} (hdeg : (chainModel C').DegLe Si D) :
    {c | c ∈ Si ∧ ∃ e ∈ exits ztbm F R, e ⊆ c}.ncard ≤
      D * (adjExits ztbm F R).ncard := by
  zudbi
  set M' := chainModel C' with hM'def
  have hsub : {c | c ∈ Si ∧ ∃ e ∈ exits M F R, e ⊆ c} ⊆
      ⋃ f ∈ adjExits M F R, exits M' Si ztoxn := by
    rintro c ⟨hc, e, ⟨he, hRe⟩, hec⟩
    obtain ⟨f, hf, hRf, hadj, hcf⟩ :=
      parent_touch J hP hC'P hset hSi hF hfin hends hR he hRe hc hec
    zucqw
    exact ⟨f, ⟨⟨hf, hRf⟩, hadj⟩, hcf⟩
  refine (Set.ncard_le_ncard hsub (hSi.1.subset ?_)).trans ?_
  · zung
    simp only [Set.mem_iUnion] at hc
    obtain ⟨f, -, hc, -⟩ := hc
    exact hc
  · refine ncard_biUnion_le_mul (hfin.subset fun f hf => hf.1.1) _ fun f _ => ?_
    rcases phi_mem_or_empty M M' Si R f with h | h
    · tauto
    · have : exits M' Si ztoxn = ∅ := by
        zuzx
        zubcj
        simp only [exits, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        rintro - ⟨z, -, hz⟩
        simp_all
      simp_all
theorem counted_mem_set (C : Chain) {p : ℕ} (hp : p < (chainModel C).W.n)
    (hc : (chainModel C).counted p) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sidePt (chainModel C).W p t ∈ C.set := by
  obtain ⟨h6, h2m⟩ : 6 ≤ p ∧ p < 2 * C.m + 6 := hc
  zuii
  zukcl
  zugue
  zucky
  rw [C.sideWalk_next_tour _ hi, C.sideWalk_vtx_tour _ hi.le, C.sideWalk_vtx_tour _ by_omega]
  zueev
  zuidg
  · exact C.sideLerp_mem_set zteg ztswa ztbdw ht0 ht1
  · exact C.sideLerp_mem_set ztbho ztswa ztbdw ht0 ht1

/-- **A chord containing an attached chord from its point is attached there too.** -/
theorem attach_sup {W : Polygon} {f c : Set Point} {p : ℕ} {t : ℝ} (hA : SideAttach W f p t)
    {e b : Point} (hfe : f = Chazelle.segment ztia e) (he : e ≠ sidePt W p t)
    (hcb : c = Chazelle.segment ztia b) (hec : e ∈ c) : SideAttach W c p t := by
  obtain ⟨hp, ht, ht1, -, r, hr, hl⟩ := hA
  set q := sidePt W p t with hq
  have hd := dist_pos.2 he
  refine ⟨hp, ht, ht1, by rw [hcb]; exact Geometry.left_mem_segment _ _, min r _,
    lt_min hr hd, fun x hx hxq hxd => hl x ?_ hxq by_simp_all⟩
  have hxd' : dist x q < dist e q := by_simp_all
  have hdist : ∀ u : ℝ, 0 ≤ u → dist (lerp q b u) q = u * dist b q := by
    zubgt
    zuecv
    have : q - lerp q b u = u • (q - b) := by
      zuhbe
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu, norm_sub_rev]
  rw [hcb] at hx hec
  zufr
  obtain ⟨se, hse0, hse1, hese⟩ := Geometry.mem_segment_iff_lerp.1 hec
  rw [hese] at hxd' hd
  rw [hdist s hs0, hdist se hse0] at hxd'
  rw [hdist se hse0] at hd
  have hbq : 0 < dist b q := by
    rcases (dist_nonneg : 0 ≤ dist b q).lt_or_eq with h | h
    · zubh
    grind
  have hsse := lt_of_mul_lt_mul_right hxd' hbq.le
  have hse : 0 < se := by_grind
  rw [hfe, hese]
  refine Geometry.mem_segment_iff_lerp.2 ⟨s / se, div_nonneg hs0 hse.le,
    (div_le_one hse).2 hsse.le, ?_⟩
  apply Geometry.point_ext <;> simp only [Geometry.lerp_fst, Geometry.lerp_snd] <;>
    zufsp

/-- An agreement with a side walk, with the lengths in range, is a piece. -/
theorem pieceAt_of_agree {C' : Chain} (hC'P : C'.P = J.P) {g g' L : ℕ}
    (hg : g < (chainModel J.whole).W.n) (hg' : g' < (chainModel C').W.n)
    (hL : L < (chainModel J.whole).W.n) (hL' : L ≤ (chainModel C').W.n)
    (hA : Agree (chainModel J.whole).W (chainModel C').W g g' L) : PieceAt J C' g g' L := by
  zudnw
  refine ⟨hg, hg', hL, hL', hA, fun d hd hc => ?_⟩
  zucpo

  rw [hA d hd.le, hA ztet hd] at hc
  simp_all

/-- The offset from a later base of a stretch. -/
theorem dOf_shift {n g s p : ℕ} (hg : g < n) (hp : p < n) (hs : s ≤ dOf n g p) :
    dOf n (zthhj % n) p = dOf n g p - s := by
  have h1 := off_shift hg hp hs le_rfl one_pos
  have h2 := off_key' (g := zthhj % n) ztcv hp le_rfl one_pos
  rw [h1, add_zero, add_zero] at h2
  exact_mod_cast h2.symm

/-- **Two pieces along one side**: the stretch of the walk of `C` read from the copy of the shared
vertex left towards a side chain `C'` is covered by two pieces (equal, unless only the box of
`C'` lies inside the stretch), each starting at a copy of the shared vertex or of the top of
`C'`. -/
theorem side_two_pieces (_hP : J.P.Simple) {C' : Chain} (hC'P : C'.P = J.P)
    {J₀ J₀' ℓ : ℕ} (hT : ∀ e, e ≤ ℓ → tourV J.whole J₀ e = tourV C' J₀' e)
    (hv0 : tourV J.whole J₀ 0 = sharedV J) (hℓ' : ℓ ≤ 2 * C'.m) (hℓ : ℓ < 2 * J.whole.m)
    (hbox : 2 * J.whole.m - tpos J.whole J₀ < ℓ →
      2 * C'.m - tpos C' J₀' = 2 * J.whole.m - tpos J.whole J₀) :
    ∃ gA gA' LA gB gB' LB : ℕ, PieceAt J C' gA gA' LA ∧ PieceAt J C' gB gB' LB ∧
      ((chainModel J.whole).W.vtx gA = J.shared ∨ (chainModel J.whole).W.vtx gA = C'.top) ∧
      ((chainModel J.whole).W.vtx gB = J.shared ∨ (chainModel J.whole).W.vtx gB = C'.top) ∧
      ∀ p : ℕ, p < (chainModel J.whole).W.n →
        dOf (chainModel J.whole).W.n ztpux p <
          ztgrr →
        dOf (chainModel J.whole).W.n gA p < LA ∨ dOf (chainModel J.whole).W.n gB p < LB := by
  zugft
  zubqe
  zugyl
  zudnw
  zukk
  zuhfj
  zudvu

  zuig

  have hstart : W.vtx g = J.shared := by
    have := walk_tour C J₀ 0 by_omega
    zuhkp
    rw [this, hv0]; rfl
  zudmg
  · -- case Sh
    zukfv
    zubno
    zufha

  zucyg

  · -- case N
    zucvr
    zufha

  -- case G
  zuzm

  have hpc1 := pieceAt_of_agree J hC'P hg hg' by_grind by_omega hA1
  have hpc2 := pieceAt_of_agree J hC'P (Nat.mod_lt _ by_grind)
    ztcv
    by_grind by_omega hA2
  have hpt : W.vtx (zttkq % W.n) = C'.top := by
    zugda
    have := walk_box C' J₀' 0 by_omega
    tauto
  refine ⟨g, g', s', _, _, ℓ - s', hpc1, hpc2, Or.inl hstart, Or.inr hpt, fun p hp hin => ?_⟩
  rw [ite_eq_right (not_lt.2 hsl)] at hin
  zuhbn
  · omega
  · zumif
    right
    rw [dOf_shift hg hp hD]
    omega

/-- **The glue chords are augmented chords of `C`.** -/
theorem glue_subset_aug (hgen : SharedGeneric J) : glueChords J ⊆ Merge.augChords J.whole := by
  rintro d (hd | ⟨hext, hfree, rfl⟩)
  · exact Merge.chords_subset_augChords _ (topChords_subset_chords J hd)
  · zuebf
    have hm₁ := J.one_le_m₁
    have hm₂ := J.one_le_m₂
    zudpo
    have hmem : capOrigin J ∈ J.whole.set := by
      unfold capOrigin
      generalize ztzzb = τ
        at hτ0 hτ1 ⊢
      rcases hnf with ⟨-, hf⟩ | ⟨-, hf⟩
      · zujix
        exact J.whole.sideLerp_mem_set ztp by_omega
          by_omega hτ0.le hτ1.le
      · zujix
        exact J.whole.sideLerp_mem_set by_omega
          by_omega by_omega hτ0.le hτ1.le
    have hy : (capOrigin J).2 ≤ J.whole.top.2 := by
      have : (capOrigin J).2 = (capNear J).2 := by
        tauto
      zubk
      rcases hnf with ⟨hn, -⟩ | ⟨hn, -⟩
      · zuikf
      · zuikf
    have hdir : ztlxv := by
      zumsc
    exact Merge.shoot_mem_augChords J.whole hy (fun h => J.whole.not_mem_set_of_mem_dom h hmem) hdir hfree

/-- **Classification of the exit chords faced inside a piece**: a chord of the fusion with a
parent chord `c` in `Sᵢ ∪ Sⱼ` (containing it and one of whose ends it contains), with all its
attachments on counted edges and not through the shared vertex, attached at an offset in
`(0, L)` of a piece of side `i` next to which `R` is faced, is of type (I) or crossing. -/
theorem classify (hP : J.P.Simple) {C' : Chain} {Q : Polygon} {Si Sj S' : Set ztf}
    (hS : SideOK J C' Q Si S') {g g' L : ℕ} (hpc : PieceAt J C' g g' L)
    (hjend : ∀ c ∈ Sj, ∀ q : Point, ztcoc → q ∈ C'.set →
      q = J.shared)
    (hjnd : ∀ c ∈ Sj, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom)
    {R : Set Point} {f : Set Point} (hf : f ∈ exits ztbm S' R)
    (hpar : ∃ c ∈ Si ∪ Sj, f ⊆ c ∧ ztcls)
    (hcnt : ∀ (pb : ℕ) (tb : ℝ), SideAttach (chainModel J.whole).W f pb tb →
      (chainModel J.whole).counted pb)
    (hsh : J.shared ∉ f) {d : ℕ} {t : ℝ} (hd : d < L) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hdt : 0 < (d : ℝ) + t)
    (hA : SideAttach (chainModel J.whole).W f ztwmx t)
    (hadj : Adj ztbm S' R ztwmx t) :
    f ∈ TypeI J C' Si S' R g g' L ∨ f ∈ CrossX ztbm S' R g L := by
  obtain ⟨c, hc, hfc, hnear⟩ := hpar
  zumen
  obtain ⟨hg, hg', hLn, hLn', hAg, hcntP⟩ := hpc
  zuvv

  zuhek
  zuiy
  zukea
  have hdt' : ztgaz := fun h => by
    zucpr
  have hq' : sidePt M.W _ t = sidePt M'.W _ t :=
    hAg.sidePt_eq hd t
  have hAf' : SideAttach M'.W f _ t :=
    (hAg.sideAttach_iff hn hn' hd hdt' f).1 hA
  have hfA := hS.adm hf.1
  rcases hc with hci | hcj
  · left
    refine ⟨hf.1, d, t, hd, ht0, ht1, hdt, hA, hadj, c, hci, ?_⟩
    set q := sidePt M'.W _ t with hq
    have hqf := hAf'.2.2.2.1
    have hqD : q ∉ M.D := by rw [← hq']; exact hM.trace _ hA.1 t ht0 ht1.le
    have hqD' : ztslh := hM'.trace _ hAf'.1 t ht0 ht1.le
    obtain ⟨e, hfe, he, -, -, -⟩ := chord_through hM hfA hqf hqD
    obtain ⟨y, a, b, hH, -, hceq, -, -⟩ := Merge.augChords_spec (hS.fam.2.1 hci)
    have hqc := hfc hqf
    rw [hceq] at hqc
    obtain ⟨hq2, hqa, hqb⟩ := hqc
    have hseg := FactsChain.hseg_eq_segment (y := y) hH.lt.le
    have hec := hfc (by rw [hfe]; exact Geometry.right_mem_segment _ _)
    zugab
    · zubui
      · exact absurd ztwl
          hqD'
      · have hqe : q = (ztdy : Point) := by_grind
        refine attach_sup hAf' hfe he (b := (ztdv : Point)) ?_ hec
        rw [hceq, hseg, Geometry.segment_comm, ← hqe]
    · have hqe : q = (ztdv : Point) := by_grind
      refine attach_sup hAf' hfe he (b := (ztdy : Point)) ?_ hec
      grind
  · obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach hfA hA
    by_cases hX : off M.W.n g ztbd = 0 ∨ (L : ℝ) ≤ off M.W.n g ztbd
    · exact Or.inr ⟨hf, d, t, hd, ht0, ht1, hdt, hA, hadj, pb, tb, hB, hBne, hX⟩
    exfalso
    push Not at hX
    set dB := dOf M.W.n g pb with hdB
    have hpb := add_dOf hg hB.1
    have hoB : off M.W.n g _ = dB + tb := off_key' hg hB.1 hB.2.1 hB.2.2.1
    have hdBL : dB < L := by
      have : (dB : ℝ) < L := by rw [hoB] at hX; linarith [hX.2, hB.2.1]
      zufc
    have hB' : SideAttach M.W f ((g + dB) % M.W.n) tb := by_grind
    -- the two attachment points of `f` are on `C'`
    have hmemB : sidePt M.W pb tb ∈ C'.set := by
      rw [← hpb, hAg.sidePt_eq hdBL tb]
      exact counted_mem_set C' ztdtl (hcntP dB hdBL by_grind)
        hB.2.1 hB.2.2.1.le
    have hmemA : sidePt M.W ztwje t ∈ C'.set := by
      zumob
      exact counted_mem_set C' ztdtl (hcntP d hd by_grind) ht0 ht1.le
    -- the near end of `f` is one of them
    obtain ⟨u, w, -, hends⟩ := seg_end hM hfA
    have hA0 := hends _ hA.2.2.2.1 (hM.trace _ hA.1 t ht0 ht1.le)
    have hB0 := hends _ hB.2.2.2.1 (hM.trace _ hB.1 tb hB.2.1 hB.2.2.1.le)
    obtain ⟨q₀, hq₀, hq₀f⟩ : ∃ q₀, (q₀ = Merge.lend c ∨ q₀ = Merge.rend c) ∧ q₀ ∈ f := by
      grind
    have hq₀D : q₀ ∉ M.D := by
      rcases hq₀ with rfl | rfl
      · exact (hjnd c hcj).1
      · exact (hjnd c hcj).2
    have hq0 := hends _ hq₀f hq₀D
    have hq₀C : q₀ ∈ C'.set := by
      rcases hA0 with h1 | h1 <;> rcases hB0 with h2 | h2 <;> rcases hq0 with h3 | h3
      all_goals first
        | (rw [h3, ← h1]; exact hmemA)
        | (rw [h3, ← h2]; exact hmemB)
        | (exfalso; exact by_grind)
    grind
theorem fuse_adm (hgen : SharedGeneric J) {S₁ S₂ : Set ztf}
    (h₁ : S₁ ⊆ Merge.augChords J.left) (h₂ : S₂ ⊆ Merge.augChords J.right) :
    J.fusion S₁ S₂ ∪ glueChords J ⊆ (chainModel J.whole).Adm :=
  union_subset (J.fusion_subset_augChords h₁ h₂) (glue_subset_aug J hgen)
variable {S₁ S₂ : Set (Set Point)}
theorem fuse_fin (h₁ : S₁.Finite) (h₂ : S₂.Finite) :
    (J.fusion S₁ S₂ ∪ glueChords J).Finite :=
  (J.fusion_finite h₁ h₂).union (glueChords_finite J)
theorem fuse_endm (hP : J.P.Simple) {S₁ S₂ : Set ztf} (h₁ : S₁ ⊆ Merge.augChords J.left)
    (h₂ : S₂ ⊆ Merge.augChords J.right) {c : Set Point} (hc : c ∈ S₁ ∪ S₂) :
    (Merge.lend c ≠ J.shared → ∃ e ∈ J.fusion S₁ S₂ ∪ glueChords J, Merge.lend c ∈ e ∧ e ⊆ c) ∧
      (Merge.rend c ≠ J.shared →
        ∃ e ∈ J.fusion S₁ S₂ ∪ glueChords J, Merge.rend c ∈ e ∧ e ⊆ c) := by
  obtain ⟨hl, hr⟩ := Merge.Junction.end_mem_fusion J hP h₁ h₂ hc
  grind
theorem sideOK_left (hP : J.P.Simple) (hgen : SharedGeneric J) {Q : Polygon}
    {S₁ S₂ : Set ztf} (hS₁ : (chainModel J.left).ChordFamily Q S₁)
    (hS₂ : (chainModel J.right).ChordFamily Q S₂) :
    SideOK J J.left Q S₁ ztqu where
  simple := hP
  fam := hS₁
  endm := fun _c hc => fuse_endm J hP hS₁.2.1 hS₂.2.1 ztjkr
  ends := fun _c hc => ⟨(J.ends_left zthxu).2.1, (J.ends_left zthxu).2.2.2⟩
  shared := fun _ hc => Or.inl ztdlf
  adm := fuse_adm J hgen hS₁.2.1 hS₂.2.1
  fin := fuse_fin J hS₁.1 hS₂.1
theorem sideOK_right (hP : J.P.Simple) (hgen : SharedGeneric J) {Q : Polygon}
    {S₁ S₂ : Set ztf} (hS₁ : (chainModel J.left).ChordFamily Q S₁)
    (hS₂ : (chainModel J.right).ChordFamily Q S₂) :
    SideOK J J.right Q S₂ ztqu where
  simple := hP
  fam := hS₂
  endm := fun _c hc => fuse_endm J hP hS₁.2.1 hS₂.2.1 ztdlf
  ends := fun _c hc => ⟨(J.ends_right ztgkd).2.1, (J.ends_right ztgkd).2.2.2⟩
  shared := fun _ hc => Or.inl ztdlf
  adm := fuse_adm J hgen hS₁.2.1 hS₂.2.1
  fin := fuse_fin J hS₁.1 hS₂.1

/-- An end of a chord of the other side lying on this side chain is the shared vertex. -/
theorem jend (_hP : J.P.Simple) {C' C'' : Chain} (hR : C'.radius = C''.radius)
    (hinter : C'.set ∩ C''.set ⊆ {J.shared}) {Sj : Set ztf}
    (hj : Sj ⊆ Merge.augChords C'') :
    ∀ c ∈ Sj, ∀ q : Point, ztcoc → q ∈ C'.set → q = J.shared := by
  intro c hc q hq hqC
  obtain ⟨y, a, b, hH, hy, -, hl, hr⟩ := Merge.augChords_spec (hj hc)
  have hnd : q ∉ C''.dom ∧ q.2 ≤ C''.top.2 := by
    rcases hq with rfl | rfl
    · zvnen; exact ⟨hH.left_not, hy⟩
    · zvnel; exact ⟨hH.right_not, hy⟩
  rcases (Merge.not_mem_dom_iff C'' hnd.2).1 hnd.1 with h | h
  · exact absurd (hR ▸ C'.set_subset_box hqC) h
  tauto
theorem jend_left (hP : J.P.Simple) {S₂ : Set ztf} (hj : S₂ ⊆ Merge.augChords J.right) :
    ∀ c ∈ S₂, ∀ q : Point, ztcoc → q ∈ J.left.set →
      q = J.shared :=
  jend J hP (C' := J.left) (C'' := J.right) rfl (by rw [J.left_inter_right hP]) hj
theorem jend_right (hP : J.P.Simple) {S₁ : Set ztf} (hj : S₁ ⊆ Merge.augChords J.left) :
    ∀ c ∈ S₁, ∀ q : Point, ztcoc → q ∈ J.right.set →
      q = J.shared :=
  jend J hP (C' := J.right) (C'' := J.left) rfl
    (by rw [Set.inter_comm, J.left_inter_right hP]) hj

/-! ## The exceptional exit chords -/

/-- The chord passes through the shared vertex or through the top of `C₁` or of `C₂`. -/
def Thr (f : Set Point) : Prop := J.shared ∈ f ∨ J.left.top ∈ f ∨ J.right.top ∈ f
theorem thr_ncard (hP : J.P.Simple) {F : Set ztf} (hFA : F ⊆ (chainModel J.whole).Adm)
    (hfin : F.Finite) : {f | f ∈ F ∧ Thr J f}.ncard ≤ 6 := by
  have hM : ztxzt := walkAx_chainModel hP
  have hv : ∀ v ∈ J.whole.set, v ∉ (chainModel J.whole).D := fun v hv h =>
    J.whole.not_mem_set_of_mem_dom h hv
  have h1 := ncard_through_le hM hFA (hv _ ztffl)
  have h2 := ncard_through_le hM hFA (hv _ (J.left_set_subset J.left.top_mem_set))
  have h3 := ncard_through_le hM hFA (hv _ ztuzd)
  have hsub : {f | f ∈ F ∧ Thr J f} ⊆ ({c | c ∈ F ∧ J.shared ∈ c} ∪
      {c | c ∈ F ∧ J.left.top ∈ c}) ∪ {c | c ∈ F ∧ J.right.top ∈ c} := by
    rintro f ⟨hf, h | h | h⟩
    · simp_all
    · simp_all
    simp_all
  calc {f | f ∈ F ∧ Thr J f}.ncard
      ≤ (({c | c ∈ F ∧ J.shared ∈ c} ∪ {c | c ∈ F ∧ J.left.top ∈ c}) ∪
          {c | c ∈ F ∧ J.right.top ∈ c}).ncard :=
        Set.ncard_le_ncard hsub (hfin.subset (by
          simp))
    _ ≤ 6 := by
        zuieu
        have := Set.ncard_union_le {c | c ∈ F ∧ J.shared ∈ c} {c | c ∈ F ∧ J.left.top ∈ c}
        omega

/-- **The exit chords attached on the box block**: at most `42`. -/
theorem nc_ncard (hP : J.P.Simple) {F : Set ztf} (hFA : F ⊆ (chainModel J.whole).Adm)
    (hfin : F.Finite) {R : Set Point} (hR : R ∈ (chainModel J.whole).regions F) :
    {f | f ∈ exits ztbm F R ∧ ∃ (p : ℕ) (t : ℝ),
      SideAttach (chainModel J.whole).W f p t ∧ ¬ (chainModel J.whole).counted p}.ncard ≤ 42 := by
  classical
  zudbi
  zuiwn
  zumh
  set P0 : Finset ℕ := Finset.range 6 ∪ {2 * J.whole.m + 6} with hP0
  have hP0c : P0.card ≤ 7 := by_simp_all
  set X : ℕ → Set _ := fun p =>
    {f | f ∈ exits M F R ∧ ∃ t : ℝ, SideAttach M.W f p t} with hX
  have hXp : ∀ p, (X p).ncard ≤ 6 := by
    zukjq
    set T := {t : ℝ | 0 < t ∧ ∃ c ∈ exits M F R, SideAttach M.W c p t} with hT
    have hT2 : T.ncard ≤ 2 := edge_two hM hFA hfin hR p
    have hTfin : T.Finite := by
      refine (Set.Finite.image (fun x : ℝ => x - (p : ℝ)) (hM.finite_cuts hFA hfin)).subset ?_
      rintro t ⟨-, c, hc, hA⟩
      exact ⟨p + t, ⟨c, hc.1, p, t, hA, rfl⟩, by_ring⟩
    have hsub : X p ⊆ ⋃ t ∈ insert 0 T, {f | f ∈ F ∧ SideAttach M.W f p t} := by
      rintro f ⟨hf, t, hA⟩
      zucqw
      rcases hA.2.1.lt_or_eq with h | h
      · exact ⟨t, by_grind, hf.1, hA⟩
      · exact ⟨t, Or.inl h.symm, hf.1, hA⟩
    calc (X p).ncard ≤ (⋃ t ∈ insert 0 T, {f | f ∈ F ∧ SideAttach M.W f p t}).ncard :=
          Set.ncard_le_ncard hsub (hfin.subset (by
            simp))
      _ ≤ 2 * (insert 0 T).ncard :=
          ncard_biUnion_le_mul (hTfin.insert 0) _ fun t _ => ncard_at_le hM hFA hfin p t
      _ ≤ 6 := by have := Set.ncard_insert_le (0 : ℝ) T; omega
  have hsub : {f | f ∈ exits M F R ∧ ∃ (p : ℕ) (t : ℝ), SideAttach M.W f p t ∧ ¬ M.counted p} ⊆
      ⋃ p ∈ (P0 : Set ℕ), X p := by
    rintro f ⟨hf, p, t, hA, hc⟩
    zucqw
    refine ⟨p, ?_, hf, t, hA⟩
    zuerz
    zugei
    have : ¬ (6 ≤ p ∧ p < 2 * J.whole.m + 6) := hc
    grind
  calc _ ≤ (⋃ p ∈ (P0 : Set ℕ), X p).ncard :=
        Set.ncard_le_ncard hsub (hfin.subset (by
          intro f hf; simp only [Set.mem_iUnion] at hf; obtain ⟨p, -, hf, -⟩ := hf; exact hf.1))
    _ ≤ 6 * (P0 : Set ℕ).ncard := ncard_biUnion_le_mul P0.finite_toSet _ fun p _ => hXp p
    _ ≤ 42 := by rw [Set.ncard_coe_finset]; omega

/-- **Glue and shared chords pass through the shared vertex or a top, or are the cap chord.** -/
theorem glue_thr {f : Set Point}
    (hf : f ∈ glueChords J ∨ f ∈ J.sharedChords) : Thr J f ∨ f ∈ capChords J := by
  rcases hf with (⟨k, hk, σ, -, -, rfl⟩ | hcap) | ⟨σ, -, -, rfl⟩
  · left
    zugia
    have hmem : J.whole.vertex k ∈ J.whole.chordSet k σ := Geometry.left_mem_segment _ _
    zuvk
    · tauto
    · zulw
      rw [Merge.Junction.whole_vertex_add] at hmem
      tauto
  · simp_all
  · left; left
    zucvg

/-- **A fused chord other than a shared chord is shot from an end of its parent.** -/
theorem fused_parent (h₁ : S₁ ⊆ Merge.augChords J.left)
    (h₂ : S₂ ⊆ Merge.augChords J.right) {f : Set Point} (hf : f ∈ J.fusion S₁ S₂)
    (hsh : f ∉ J.sharedChords) :
    ∃ c ∈ S₁ ∪ S₂, (f = Merge.shoot J.whole ztffp 1 ∨
      f = Merge.shoot J.whole ztffq (-1)) ∧ f ⊆ c ∧
      ztcls := by
  have hc' : ∀ c ∈ S₁ ∪ S₂, c ∈ Merge.augChords J.left ∪ Merge.augChords J.right := by
    grind
  rcases hf with (⟨c, hc, -, rfl⟩ | ⟨c, hc, -, rfl⟩) | hd
  · exact ⟨c, hc, Or.inl rfl, J.shoot_lend_subset by_simp_all,
      Or.inl ztdte⟩
  · exact ⟨c, hc, Or.inr rfl, J.shoot_rend_subset by_simp_all,
      Or.inr ztdte⟩
  simp_all

/-! ## The four pieces -/

/-- **The walk of `C` is covered by four pieces** (two along each side chain), each starting at a
copy of the shared vertex or of the top of its side chain. -/
theorem four_pieces (hP : J.P.Simple) :
    ∃ gA gA' LA gB gB' LB gC gC' LC gD gD' LD : ℕ,
      PieceAt J J.left gA gA' LA ∧ PieceAt J J.left gB gB' LB ∧
      PieceAt J J.right gC gC' LC ∧ PieceAt J J.right gD gD' LD ∧
      ((chainModel J.whole).W.vtx gA = J.shared ∨ (chainModel J.whole).W.vtx gA = J.left.top) ∧
      ((chainModel J.whole).W.vtx gB = J.shared ∨ (chainModel J.whole).W.vtx gB = J.left.top) ∧
      ((chainModel J.whole).W.vtx gC = J.shared ∨ (chainModel J.whole).W.vtx gC = J.right.top) ∧
      ((chainModel J.whole).W.vtx gD = J.shared ∨ (chainModel J.whole).W.vtx gD = J.right.top) ∧
      ∀ p : ℕ, p < (chainModel J.whole).W.n → (chainModel J.whole).counted p →
        dOf (chainModel J.whole).W.n gA p < LA ∨ dOf (chainModel J.whole).W.n gB p < LB ∨
          dOf (chainModel J.whole).W.n gC p < LC ∨ dOf (chainModel J.whole).W.n gD p < LD := by
  zufz

  zumh
  zudpo
  obtain ⟨gA, gA', LA, gB, gB', LB, hA, hB, hsA, hsB, hcovL⟩ :=
    side_two_pieces J hP (C' := J.left) rfl (J₀ := J.m₁ + 2 * J.m₂) (J₀' := J.m₁)
      (ℓ := 2 * J.m₁) ztnyt
      (by zunyw; rfl) by_simp by_omega
      ztvyd
  obtain ⟨gC, gC', LC, gD, gD', LD, hC, hD, hsC, hsD, hcovR⟩ :=
    side_two_pieces J hP (C' := J.right) rfl (J₀ := J.m₁) (J₀' := 0)
      (ℓ := 2 * J.m₂) ztnyu
      (by zunyx; rfl) by_simp by_omega
      ztwcu
  refine ⟨gA, gA', LA, gB, gB', LB, gC, gC', LC, gD, gD', LD, hA, hB, hC, hD, hsA, hsB, hsC, hsD,
    fun p hp hc => ?_⟩
  zucsu

  zubcq

  · rcases hcovL _ hp ztlhy with h | h
    · omega
    omega
  · rcases hcovR _ hp ztlhy with h | h
    · omega
    omega

/-- An exit chord faced next to an attachment inside a piece is of type (I) or crossing. -/
theorem in_piece (hP : J.P.Simple) {C' : Chain} {Q : Polygon} {Si Sj S' : Set ztf}
    (hS : SideOK J C' Q Si S') {g g' L : ℕ} (hpc : PieceAt J C' g g' L)
    (hstart : (chainModel J.whole).W.vtx g = J.shared ∨ (chainModel J.whole).W.vtx g = C'.top)
    (hjend : ∀ c ∈ Sj, ∀ q : Point, ztcoc → q ∈ C'.set →
      q = J.shared)
    (hjnd : ∀ c ∈ Sj, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom)
    {R f : Set Point} (hf : f ∈ exits ztbm S' R)
    (hpar : ∃ c ∈ Si ∪ Sj, f ⊆ c ∧ ztcls)
    (hcnt : ∀ (pb : ℕ) (tb : ℝ), SideAttach (chainModel J.whole).W f pb tb →
      (chainModel J.whole).counted pb)
    (hsh : J.shared ∉ f) (htop : C'.top ∉ f) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W f p t) (hadj : Adj ztbm S' R p t)
    (hdp : dOf (chainModel J.whole).W.n g p < L) :
    f ∈ TypeI J C' Si S' R g g' L ∨ f ∈ CrossX ztbm S' R g L := by
  have hpd :=
    add_dOf hpc.1 hA.1
  rw [← hpd] at hA hadj
  by_cases h0 : 0 < (dOf (chainModel J.whole).W.n g p : ℝ) + t
  · exact classify J hP hS hpc hjend hjnd hf hpar hcnt hsh hdp hA.2.1 hA.2.2.1 h0 hA hadj
  · exfalso
    have ht := le_antisymm (by
      grind)
      hA.2.1
    have hd : dOf (chainModel J.whole).W.n g p = 0 := by
      simp_all
    rw [hd, ht, add_zero, Nat.mod_eq_of_lt hpc.1] at hA
    have hmem := hA.2.2.2.1
    rw [Chazelle.Chain.sidePt_zero] at hmem
    grind
theorem cap_ncard : (capChords J).ncard ≤ 1 :=
  (Set.ncard_le_one (capChords_subsingleton J).finite).2
    fun _ ha _ hb => capChords_subsingleton J ha hb

/-- **At most `16 D + 65` exit chords of `R` are faced next to an attachment.** -/
theorem adj_ncard (hP : J.P.Simple) (hgen : SharedGeneric J) {Q : Polygon}
    {S₁ S₂ : Set ztf} (hS₁ : (chainModel J.left).ChordFamily Q S₁)
    (hS₂ : (chainModel J.right).ChordFamily Q S₂) {D : ℕ}
    (hD₁ : (chainModel J.left).DegLe S₁ D) (hD₂ : (chainModel J.right).DegLe S₂ D)
    {R : Set Point} (hR : R ∈ (chainModel J.whole).regions ztqu) :
    (adjExits ztbm ztqu R).ncard ≤ 16 * D + 65 := by
  zudbi
  zugfu
  zuiwn
  zudyg

  have SL := sideOK_left J hP hgen hS₁ hS₂
  have SR := sideOK_right J hP hgen hS₁ hS₂
  obtain ⟨gA, gA', LA, gB, gB', LB, gC, gC', LC, gD, gD', LD, hA, hB, hC, hD, hsA, hsB, hsC, hsD,
    hcov⟩ := four_pieces J hP
  have hjL := jend_left J hP hS₂.2.1
  have hjR := jend_right J hP hS₁.2.1
  have hndL : ztiox := fun c hc =>
    ⟨(J.ends_right ztgkd).2.1, (J.ends_right ztgkd).2.2.2⟩
  have hndR : ztiow := fun c hc =>
    ⟨(J.ends_left zthxu).2.1, (J.ends_left zthxu).2.2.2⟩
  set NC := {f | f ∈ exits M F R ∧ ∃ (p : ℕ) (t : ℝ), SideAttach M.W f p t ∧ ¬ M.counted p}
    with hNC
  set E₀ := ({f | f ∈ F ∧ Thr J f} ∪ capChords J) ∪ NC with hE₀
  set PA := TypeI J J.left S₁ F R gA gA' LA ∪ CrossX M F R gA LA
  set PB := TypeI J J.left S₁ F R gB gB' LB ∪ CrossX M F R gB LB
  set PC := TypeI J J.right S₂ F R gC gC' LC ∪ CrossX M F R gC LC
  set PD := TypeI J J.right S₂ F R gD gD' LD ∪ CrossX M F R gD LD
  have hsub : adjExits M F R ⊆ E₀ ∪ zteit := by
    rintro f ⟨hf, p, t, hAt, hadj⟩
    zujty
    · exact Or.inl (Or.inl ztoxj)
    zuirn
    · grind
    by_cases hnc : ∃ (p : ℕ) (t : ℝ), SideAttach M.W f p t ∧ ¬ M.counted p
    · grind
    push Not at hnc
    right
    have hfus : ztmvr := by
      zukli
      · zugta

        · grind
        grind
      · zuidx
        · grind
        grind
    obtain ⟨c, hc, -, hfc, hnear⟩ := fused_parent J hS₁.2.1 hS₂.2.1 hfus.1 hfus.2
    have hsh := fun h => hthr zteg
    have hlt := fun h => hthr ztwkb
    have hrt := fun h => hthr ztwxb
    have hparL : ∃ c ∈ S₁ ∪ S₂, f ⊆ c ∧ ztcls :=
      by grind
    have hparR : ∃ c ∈ S₂ ∪ S₁, f ⊆ c ∧ ztcls :=
      by grind
    rcases hcov p hAt.1 (hnc p t hAt) with h | h | h | h
    · exact Or.inl (Or.inl (in_piece J hP SL hA hsA hjL hndL hf hparL hnc hsh hlt hAt hadj h))
    · exact Or.inl (Or.inr (in_piece J hP SL hB hsB hjL hndL hf hparL hnc hsh hlt hAt hadj h))
    · exact Or.inr (Or.inl (in_piece J hP SR hC hsC hjR hndR hf hparR hnc hsh hrt hAt hadj h))
    · exact Or.inr (Or.inr (in_piece J hP SR hD hsD hjR hndR hf hparR hnc hsh hrt hAt hadj h))
  have hEfin : (E₀ ∪ zteit).Finite := by
    refine hfin.subset ?_
    rintro f (((⟨hf, -⟩ | hf) | ⟨hf, -⟩) | ((hf | hf) | (hf | hf)))
    · exact hf
    · exact Or.inr (Or.inr hf)
    · exact hf.1
    all_goals rcases hf with hf | hf
    all_goals first | exact hf.1 | exact hf.1.1
  have hPiece : ∀ {C' : Chain} {Si : Set _} {g g' L : ℕ},
      SideOK J C' Q Si F → PieceAt J C' g g' L → (chainModel C').DegLe Si D →
      (TypeI J C' Si F R g g' L ∪ CrossX M F R g L).ncard ≤ 4 * D + 4 := by
    intro C' Si g g' L hS hpc hdeg
    have h1 := typeI_ncard_le J hP hS hpc hR hdeg
    have h2 : (CrossX M F R g L).ncard ≤ 4 := crossX_ncard_le hM hFA hfin hpc.1 hpc.2.2.1 hR
    have h3 := Set.ncard_union_le (TypeI J C' Si F R g g' L) (CrossX M F R g L)
    omega
  have hA' : PA.ncard ≤ 4 * D + 4 := by_grind
  have hB' : PB.ncard ≤ 4 * D + 4 := by_grind
  have hC' : PC.ncard ≤ 4 * D + 4 := by_grind
  have hD' : PD.ncard ≤ 4 * D + 4 := by_grind
  have hThr : {f | f ∈ F ∧ Thr J f}.ncard ≤ 6 := thr_ncard J hP hFA hfin
  zulht
  have hNCn : NC.ncard ≤ 42 := nc_ncard J hP hFA hfin hR
  have u1 := Set.ncard_union_le ({f | f ∈ F ∧ Thr J f}) (capChords J)
  have u2 : E₀.ncard ≤ ({f | f ∈ F ∧ Thr J f} ∪ capChords J).ncard + NC.ncard :=
    Set.ncard_union_le _ _
  have u3 := Set.ncard_union_le PA PB
  have u4 := Set.ncard_union_le PC PD
  have u5 := Set.ncard_union_le (PA ∪ PB) (PC ∪ PD)
  have u6 := Set.ncard_union_le E₀ zteit
  have := Set.ncard_le_ncard hsub hEfin
  omega

/-! ## The degree bound -/

/-- **WP-D (math): the degree bound of the revised fusion** (`FusionDegSpec`, finding D4): the
fusion of two submaps of degree `≤ D` plus the glue chords has degree
`≤ 7 + 4 D (16 D + 65)`. -/
theorem fusionDegSpec : FusionDegSpec := by
  refine ⟨fun D => 7 + 4 * D * ztpsx, ?_⟩
  intro J Q S₁ S₂ D hP hgen hS₁ hS₂ hD₁ hD₂ R hR
  zudbi
  zugfu
  zudyg

  have hA := adj_ncard J hP hgen hS₁ hS₂ hD₁ hD₂ hR
  have hendsL : ztiow := fun c hc =>
    ⟨(J.ends_left zthxu).2.1, (J.ends_left zthxu).2.2.2⟩
  have hendsR : ztiox := fun c hc =>
    ⟨(J.ends_right ztgkd).2.1, (J.ends_right ztgkd).2.2.2⟩
  set P₁ := {c | c ∈ S₁ ∧ ∃ e ∈ exits M F R, e ⊆ c} with hP₁
  set P₂ := {c | c ∈ S₂ ∧ ∃ e ∈ exits M F R, e ⊆ c} with hP₂
  have h₁ :=
    parents_ncard_le J hP rfl J.left_set_subset hS₁ hFA hfin hendsL hR hD₁
  have h₂ :=
    parents_ncard_le J hP rfl J.right_set_subset hS₂ hFA hfin hendsR hR hD₂
  set P := P₁ ∪ P₂ with hPdef
  have hPfin : P.Finite := (hS₁.1.union hS₂.1).subset (by
    grind)
  set I₁ := (fun c => Merge.shoot J.whole ztffp 1) '' P
  set I₂ := (fun c => Merge.shoot J.whole ztffq (-1)) '' P
  set E₀ := {f | f ∈ F ∧ Thr J f} ∪ capChords J
  have hsub : exits M F R ⊆ E₀ ∪ ztnls := by
    zuhgh
    zujty
    · exact Or.inl ztoxj
    zuirn
    · grind
    right
    have hfus : ztmvr := by
      zukli
      · zugta

        · simp_all
        simp_all
      · zuidx
        · simp_all
        simp_all
    obtain ⟨c, hc, hshoot, hfc, -⟩ := fused_parent J hS₁.2.1 hS₂.2.1 hfus.1 hfus.2
    have hcP : c ∈ P := by
      grind
    grind
  have hfin' : (E₀ ∪ ztnls).Finite :=
    ((hfin.subset (by rintro f (⟨hf, -⟩ | hf); exacts [hf, Or.inr (Or.inr hf)])).union
      ((hPfin.image _).union (hPfin.image _)))
  have hThr := thr_ncard J hP hFA hfin
  zulht
  have u1 : E₀.ncard ≤ {f | f ∈ F ∧ Thr J f}.ncard + (capChords J).ncard := Set.ncard_union_le _ _
  have u2 := Set.ncard_union_le I₁ I₂
  have u3 := Set.ncard_union_le E₀ ztnls
  have i1 : I₁.ncard ≤ P.ncard := Set.ncard_image_le hPfin
  have i2 : I₂.ncard ≤ P.ncard := Set.ncard_image_le hPfin
  have hPu : P.ncard ≤ P₁.ncard + P₂.ncard := Set.ncard_union_le _ _
  have hsubn := Set.ncard_le_ncard hsub hfin'
  have hDA := Nat.mul_le_mul_left D hA
  show (exits M F R).ncard ≤ 7 + 4 * D * ztpsx
  grind
end FuseDeg
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open OracleQ OracleR
namespace OracleQ
variable (Q : Polygon) (s hz : ℕ) (σ : ℝ) (z : Point)
open Classical in
/-- The parameter of the point of chain edge `ci` at the height of the ray (`-1`, never a hit
parameter, if the edge does not span that height: so a recorded best edge is spanning). -/
noncomputable def vOf (ci : ℕ) : ℝ :=
  if Spans Q ztcda hz then σ * ztyxf else -1

/-- The parameter of a best chain edge. -/
noncomputable def bestVal (best : Option ℕ) : Option ℝ := best.map (vOf Q s hz σ z)
variable {Q s hz σ z}
variable {ci : ℕ} {C : Chain}
theorem vOf_of_spans (h : Spans Q ztcda hz) :
    vOf Q s hz σ z ci = σ * ztyxf := by
  classical
  unfold vOf; zvnbq
theorem spans_of_vOf_pos (h : 0 < vOf Q s hz σ z ci) : Spans Q ztcda hz := by
  classical
  zuhbw
  unfold vOf at h; rw [ite_eq_right hn] at h; norm_num at h

/-- **The origin data of the scan**: a symbolic origin `z` (`some z`), or a box origin on the
side the ray comes from (`none`). -/
def ZoOK (C : Chain) (σ : ℝ) (z : Point) (zo : Option Point) : Prop :=
  zo = some z ∨ (zo = none ∧ z.1 = -σ * C.radius)
open Classical in
/-- **The answer for one chain edge.** -/
theorem hit_chainEdge (hCQ : C.P = Q) (hs : C.s = s) (hD : DistinctHeights Q)
    {ci : ℕ} (hci : ci < C.m) (hzy : z.2 = (Q.vtx hz).2) (hσ : σ = 1 ∨ σ = -1)
    {zo : Option Point} (hzo : ZoOK C σ z zo) :
    Sweep.FirstHitOpt (C.chainEdge ci) z σ
      (if HitC Q s hz σ zo ci then some ztewh else none) := by
  classical
  have hn2 : ztsag := by rw [← hCQ]; have := C.add_one_le; grind
  have he : C.chainEdge ci = Q.edge ztcda := by
    unfold Chain.chainEdge Chain.edgeIdx eIdx; simp_all
  set e := eIdx Q.n s ci with he_def
  have hen : ztsic := Nat.mod_lt _ by_omega
  have hne : ztbamn := by
    refine hD _ _ hen ztcv ?_
    zuq
    rcases Nat.lt_or_ge ztda Q.n with h' | h'
    · zupe
    · rw [show e + 1 = Q.n by omega, Nat.mod_self] at h; omega
  have hspec := edgeHit_spec Q hne hzy hσ
  zucjo
  suffices hiff : (Spans Q e hz ∧ 0 < σ * (xe Q e hz - z.1)) ↔ HitC Q s hz σ zo ci by
    unfold edgeHit at hspec
    by_cases h : HitC Q s hz σ zo ci
    · rw [ite_eq_left h, vOf_of_spans h.1]; simp_all
    · grind
  unfold HitC
  rw [← he_def]
  rcases hzo with rfl | ⟨rfl, hz1⟩
  · simp only [Ahead]
    rw [ahead_iff hσ]
  · simp only [Ahead, and_true]
    constructor
    · simp_all
    · intro hsp
      refine ztooq
      -- the point is on the chain, hence in the box
      have hmem : (ztkxz : Point) ∈ C.chainEdge ci := by
        zucjo
        have := (rayPt_mem_edge_iff Q hne (z := (ztkxz : Point)) rfl
          ztp 0).2 ⟨hsp, by_simp⟩
        simp_all
      have hbox := C.set_subset_box ⟨ci, hci, hmem⟩
      have hx := (abs_lt.1 hbox.1)
      simp only at hx
      zuntc
      zur
      · grind
      simp_all
open Classical in
/-- **One step of the scan.** -/
theorem fold_step (hCQ : C.P = Q) (hs : C.s = s) (hD : DistinctHeights Q)
    {ci : ℕ} (hci : ci < C.m) (hzy : z.2 = (Q.vtx hz).2) (hσ : σ = 1 ∨ σ = -1)
    {zo : Option Point} (hzo : ZoOK C σ z zo) {S : Set Point} {best : Option ℕ}
    (hS : Sweep.FirstHitOpt S z σ (bestVal Q s hz σ z best)) :
    Sweep.FirstHitOpt (S ∪ C.chainEdge ci) z σ
      (bestVal Q s hz σ z (upd1 Q s hz σ zo best ci)) := by
  classical
  have hu := Sweep.firstHitOpt_union hS (hit_chainEdge hCQ hs hD hci hzy hσ hzo)
  convert hu using 1
  unfold upd1
  by_cases hh : HitC Q s hz σ zo ci
  · zulpx
    by_cases hall : ∀ cb, best = some cb → BetterC Q s hz σ ci cb
    · rw [ite_eq_left ⟨hh, hall⟩]
      rcases best with _ | cb
      · rfl
      · have hb := hall cb rfl
        zudyw
        have hlt : vOf Q s hz σ z ci < vOf Q s hz σ z cb := by
          rw [vOf_of_spans hh.1, vOf_of_spans hcb, better_iff hσ]; exact hb
        show some ztewh = some ztzxe
        grind
    · rw [ite_eq_right (fun h => hall h.2)]
      zugrg
      obtain ⟨cb, rfl, hnb⟩ := hall
      zudyw
      have hle : vOf Q s hz σ z cb ≤ vOf Q s hz σ z ci := by
        zux

        rw [vOf_of_spans hh.1, vOf_of_spans hcb] at hc
        exact hnb (by rwa [better_iff hσ] at hc)
      show some ztdip = some ztzxe
      simp_all
  · rw [ite_eq_right hh, ite_eq_right (fun h => hh h.1)]
    rcases best with _ | cb <;> rfl
end OracleQ
end
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
@[expose] public section
structure QV where
  /-- The chain descriptor. -/
  D : ℕ
  /-- The normal-form handle. -/
  NB : ℕ
  /-- Start of the chain. -/
  s : ℕ
  /-- Number of edges. -/
  m : ℕ
  /-- Top index. -/
  tIdx : ℕ
  /-- Orientation bit. -/
  β : ℕ
  /-- `sideS`. -/
  sS : ℕ
  /-- Index in `Q` of the top vertex. -/
  tv : ℕ
  /-- Height vertex of the ray. -/
  hz : ℕ
  /-- Direction bit. -/
  σb : ℕ
  /-- The origin (`none`: box). -/
  zo : Option Point
  /-- Number of arcs. -/
  A : ℕ
  /-- Base of the inverse sequence table. -/
  POS : ℕ
  /-- Base of the `D*` flags. -/
  FL : ℕ
  /-- Base of the labels. -/
  LAB : ℕ
  /-- Base of the `D*` list. -/
  DL : ℕ
  /-- Length of the `D*` list. -/
  nD : ℕ
  /-- Base of the nodes sorted by label. -/
  ORD : ℕ
  /-- Base of the ranks. -/
  RK : ℕ
  /-- Base of the sorted chords. -/
  CH : ℕ
  /-- Number of chords. -/
  K : ℕ
  /-- Model descriptor. -/
  MD : ℕ
  /-- Table of powers. -/
  TB : ℕ
  /-- Its length. -/
  L : ℕ
  /-- Chord area. -/
  CB : ℕ
  /-- Arc area. -/
  AB : ℕ
  /-- Region area. -/
  RB : ℕ
  /-- Sequence table. -/
  SB : ℕ
  /-- List area. -/
  LB : ℕ
  /-- Number of nodes of the book. -/
  μ : ℕ

/-- **The constants of the query in the registers `120010 … 120049`.** -/
structure QConst (P : Polygon) (V : QV) (c : Config) : Prop where
  n : c.nreg 120010 = P.n
  one : c.nreg 120011 = 1
  zero : c.nreg 120012 = 0
  D : c.nreg 120013 = V.D
  NB : c.nreg 120014 = V.NB
  s : c.nreg 120015 = V.s
  m : c.nreg 120016 = V.m
  tIdx : c.nreg 120017 = V.tIdx
  β : c.nreg 120018 = V.β
  twoM : c.nreg 120019 = 2 * V.m
  nW : c.nreg 120020 = 2 * V.m + 7
  sS : c.nreg 120021 = V.sS
  tv : c.nreg 120022 = V.tv
  hz : c.nreg 120023 = V.hz
  σb : c.nreg 120024 = V.σb
  org : OriginOK P c V.zo
  six : c.nreg 120028 = 6
  tEnd : c.nreg 120029 = 2 * V.m + 6
  A : c.nreg 120030 = V.A
  POS : c.nreg 120031 = V.POS
  FL : c.nreg 120032 = V.FL
  LAB : c.nreg 120033 = V.LAB
  DL : c.nreg 120034 = V.DL
  nD : c.nreg 120035 = V.nD
  ORD : c.nreg 120036 = V.ORD
  RK : c.nreg 120037 = V.RK
  CH : c.nreg 120038 = V.CH
  K : c.nreg 120039 = V.K
  MD : c.nreg 120040 = V.MD
  TB : c.nreg 120041 = V.TB
  L : c.nreg 120042 = V.L
  CB : c.nreg 120043 = V.CB
  AB : c.nreg 120044 = V.AB
  RB : c.nreg 120045 = V.RB
  SB : c.nreg 120046 = V.SB
  LB : c.nreg 120047 = V.LB
  two : c.nreg 120048 = 2
  μ : c.nreg 120049 = V.μ
variable {P : Polygon} {V : QV} {c c' : Config} {C : Chain}
/-- The constants survive a statement that does not write the registers `120010 … 120049`. -/
theorem QConst.congr (h : QConst P V c)
    (hr : ∀ r, 120010 ≤ r → r ≤ 120049 → c'.nreg r = c.nreg r) : QConst P V c' := by
  have g : ∀ r, 120010 ≤ r → r ≤ 120049 → ∀ v, c.nreg r = v → c'.nreg r = v :=
    by simp_all
  exact ⟨g _ by_norm_num by_norm_num _ h.n, g _ by_norm_num by_norm_num _ h.one,
    g _ by_norm_num by_norm_num _ h.zero, g _ by_norm_num by_norm_num _ h.D,
    g _ by_norm_num by_norm_num _ h.NB, g _ by_norm_num by_norm_num _ h.s,
    g _ by_norm_num by_norm_num _ h.m, g _ by_norm_num by_norm_num _ h.tIdx,
    g _ by_norm_num by_norm_num _ h.β, g _ by_norm_num by_norm_num _ h.twoM,
    g _ by_norm_num by_norm_num _ h.nW, g _ by_norm_num by_norm_num _ h.sS,
    g _ by_norm_num by_norm_num _ h.tv, g _ by_norm_num by_norm_num _ h.hz,
    g _ by_norm_num by_norm_num _ h.σb,
    originOK_congr by_grind h.org,
    g _ by_norm_num by_norm_num _ h.six, g _ by_norm_num by_norm_num _ h.tEnd,
    g _ by_norm_num by_norm_num _ h.A, g _ by_norm_num by_norm_num _ h.POS,
    g _ by_norm_num by_norm_num _ h.FL, g _ by_norm_num by_norm_num _ h.LAB,
    g _ by_norm_num by_norm_num _ h.DL, g _ by_norm_num by_norm_num _ h.nD,
    g _ by_norm_num by_norm_num _ h.ORD, g _ by_norm_num by_norm_num _ h.RK,
    g _ by_norm_num by_norm_num _ h.CH, g _ by_norm_num by_norm_num _ h.K,
    g _ by_norm_num by_norm_num _ h.MD, g _ by_norm_num by_norm_num _ h.TB,
    g _ by_norm_num by_norm_num _ h.L, g _ by_norm_num by_norm_num _ h.CB,
    g _ by_norm_num by_norm_num _ h.AB, g _ by_norm_num by_norm_num _ h.RB,
    g _ by_norm_num by_norm_num _ h.SB, g _ by_norm_num by_norm_num _ h.LB,
    g _ by_norm_num by_norm_num _ h.two, g _ by_norm_num by_norm_num _ h.μ⟩

/-- A statement whose written registers (natural and real) lie outside `120010 … 120049`. -/
theorem QConst.frame {B : ℕ → Bool} (h : QConst P V c)
    (hf : FrameB B c c') (hB : ∀ r, 120010 ≤ r → r ≤ 120049 → B r = false) : QConst P V c' :=
  h.congr fun r h1 h2 => hf.1 r by_simp_all

/-- **The facts about the values** used by the scan. -/
structure QVOK (P : Polygon) (C : Chain) (V : QV) : Prop where
  CQ : C.P = Qof P
  s : V.s = C.s
  m : V.m = C.m
  sS : V.sS = C.sideS C.sideBeta
  hz_lt : V.hz < P.n
  σb_le : V.σb ≤ 1
  s_lt : V.s < P.n

/-- The edge test's constants from the query's. -/
theorem QConst.econst {V : QV} {c : Config} (h : QConst P V c)
    (hv : QVOK P C V) : EConst P V.s V.hz V.σb V.zo c :=
  ⟨h.n, h.one, h.two, h.s, h.hz, h.σb, hv.σb_le, h.org, hv.s_lt, hv.hz_lt⟩

/-! ## One walk edge -/

/-- **The scan of walk edge `w`** (register `120070`). -/
def wstep : Stmt :=
  .ifLtN 120070 120028 .skip
    (.ifLtN 120070 120029
      (.seq ztiqw
        (.seq (modSub 120071 120019)
          (.seq (.ifLtN 120071 120016 ztouv
                  zteby)
            edgeT)))
      .skip)

/-- The registers written by `wstep`. -/
def BW (r : ℕ) : Bool := BE r || decide (r = 120071) || decide (r = 120060)
theorem wr_wstep : wr BW wstep = true := by_decide
theorem BW_const (r : ℕ) (h1 : 120010 ≤ r) (h2 : r ≤ 120049) : BW r = false := by
  simp only [BW, BE, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
open Classical in
/-- **The new best after walk edge `w`.** -/
noncomputable def wupd (Q : Polygon) (C : Chain) (s hz : ℕ) (σ : ℝ) (zo : Option Point)
    (best : Option ℕ) (w : ℕ) : Option ℕ :=
  if 6 ≤ w ∧ w < 2 * C.m + 6 then upd1 Q s hz σ zo best ztyrz else best
theorem wstep_exec {W : ℕ} (hG : GoodEnv P) (hW : 4 * P.n + 8 ≤ W)
    (hD : DistinctHeights zta) {C : Chain} {V : QV} (hv : QVOK P C V) (c : Config)
    (hw : WordsBounded W c) (hq : QConst P V c) (hb : BestOK P.n V.s V.m c) :
    ∃ c' k, Exec P W wstep c c' k ∧ k ≤ 1120 ∧ FrameB BW c c' ∧ BestOK P.n V.s V.m c' ∧
      bestOf c' = wupd zta C V.s V.hz zthx V.zo ztchc (c.nreg 120070) := by
  have hmn : ztgaj := by
    have := C.m_lt; zvmxw at this; omega
  zubb
  suffices H : ∃ c' k, Exec P W wstep c c' k ∧ k ≤ 1120 ∧ BestOK P.n V.s V.m c' ∧
      bestOf c' = wupd _ C V.s V.hz _ V.zo _ _ by
    obtain ⟨c', k, ex, hk, hb', hv'⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex wr_wstep, hb', hv'⟩
  set w := c.nreg 120070 with hw_def
  zufqv
  · refine ⟨c, _, .ifLtN_true ztgfw ztjd, by_omega, hb, ?_⟩
    zumvl
  by_cases hE : w < 2 * C.m + 6
  swap
  · refine ⟨c, _, .ifLtN_false ztgfw
      (.ifLtN_false ztkts ztjd), by_omega, hb, ?_⟩
    zumvl
  -- the tour edge `i = w - 6`
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁⟩ : ∃ c₁ k₁, Exec P W
      ztiqw c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 120071 = w - 6 + V.sS ∧ (∀ r, r ≠ 120071 → c₁.nreg r = c.nreg r) := by
    exec_block
    · config_simp; rw [hq.six, hq.sS, hv.sS]
      have := C.sideS_lt C.sideBeta; omega
    · zuhjd
      · config_simp; rw [hq.six, hq.sS]
      simp_all
  zubqz
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, r₂, -⟩ := modSub_exec (P := P) (r := 120071) (nr := 120019)
    by_decide c₁ e₁.wb_right (by rw [v₁, r₁ _ by_decide, hq.twoM, hv.m]; omega)
  zubsp
  have htj : c₂.nreg 120071 = tj C ztvu := by
    zubmg
  zufwp
  have R₂ : ∀ r, r ≠ 120071 → c₂.nreg r = c.nreg r := by_simp_all
  -- the chain edge
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃⟩ : ∃ c₃ k₃, Exec P W
      (.ifLtN 120071 120016 ztouv
        zteby) c₂ c₃ k₃ ∧ k₃ ≤ 4 ∧
      c₃.nreg 120060 = tci C ztvu ∧ ztiux := by
    zupn

    · refine ⟨_, _, .ifLtN_true by_omega ztlei,
        by omega, ?_, fun r hr => ?_⟩
      · config_simp; rw [htj]; unfold tci; simp_all
      simp_all
    · zue
      obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃⟩ : ∃ c₃ k₃, Exec P W
          zteby c₂ c₃ k₃ ∧ k₃ = 2 ∧
          c₃.nreg 120060 = 2 * C.m - 1 - tj C _ ∧
          ztiux := by
        exec_block
        zuhjd
        · config_simp
          rw [R₂ _ by_decide, R₂ _ by_decide, hq.twoM, hq.one, htj, hv.m]
        · config_simp; upd_solve
      refine ztiof
      zudkr
  have R₃ : ∀ r, r ≠ 120071 → r ≠ 120060 → c₃.nreg r = c.nreg r := by_simp_all
  have hq₃ : ztgan := hq.congr by_grind
  have hb₃ : ztsao := by
    zucku
    rw [R₃ 120050 by_decide by_decide, R₃ 120051 by_decide by_decide,
      R₃ 120052 by_decide by_decide]
    zulfi
  obtain ⟨c₄, k₄, e₄, hk₄, -, hb₄, v₄⟩ := edgeT_exec (P := P) hG by_omega hD c₃ e₃.wb_right
    (hq₃.econst hv) (by rw [v₃]; have := tci_lt C ztvu; omega) (mb := V.m)
    (by rw [v₃, hv.m]; exact tci_lt C _) hb₃
  have hbo₃ : ztmuf := by
    zulbi
    simp_all
  rw [v₃, hbo₃] at v₄
  refine ⟨c₄, _, .ifLtN_false ztgfw
    (.ifLtN_true ztkts ztwri),
    by omega, hb₄, ?_⟩
  zuntf; unfold wupd; simp_all

/-! ## The semantic context -/

/-- **The geometric context of the scan**: the ray from `z` at the height of vertex `hz`, in
direction `σ = sgnOf σb`, the origin data `zo` of the registers. -/
structure SemOK (P : Polygon) (C : Chain) (V : QV) (z : Point) : Prop where
  hv : QVOK P C V
  hD : DistinctHeights zta
  zy : z.2 = ((Qof P).vtx V.hz).2
  σ : sgnOf V.σb = 1 ∨ sgnOf V.σb = -1
  zo : ZoOK C zthx z V.zo
theorem sgnOf_cases (b : ℕ) : sgnOf b = 1 ∨ sgnOf b = -1 := by
  unfold sgnOf; grind

/-- **One walk edge, semantically.** -/
theorem wupd_step {V : QV} {z : Point} (hs : SemOK P C V z)
    {S : Set Point} {best : Option ℕ}
    (hS : Sweep.FirstHitOpt S z zthx ztyqb)
    (w : ℕ) :
    Sweep.FirstHitOpt (S ∪ wseg C w) z zthx
      (bestVal zta V.s V.hz zthx z
        (wupd zta C V.s V.hz zthx V.zo best w)) := by
  unfold wupd wseg
  by_cases h : 6 ≤ w ∧ w < 2 * C.m + 6
  · rw [ite_eq_left h, ite_eq_left h]
    exact fold_step hs.hv.CQ hs.hv.s.symm hs.hD (tci_lt C _) hs.zy hs.σ hs.zo hS
  · rw [ite_eq_right h, ite_eq_right h, Set.union_empty]; exact hS
def arcHead : Stmt := block [.addN 120086 120080 120080, .addN 120086 120086 120086,
  .addN 120086 120086 120080, .addN 120086 120086 120044, .addN 120087 120086 120011,
  .loadN 120081 120087, .addN 120087 120087 120048, .loadN 120082 120087,
  .addN 120087 120031 120080, .loadN 120083 120087, .addN 120087 120083 120011]

/-- The number of scanned walk edges, minus three. -/
def arcLen : Stmt :=
  .ifLtN 120087 120030 (.instr (.subN 120084 120082 120081))
    ztiqd

/-- The first walk edge and the loop bound. -/
def arcInit : Stmt :=
  .seq ztgfi
    (.seq (modSub 120070 120020) ztjpb)

/-- One walk edge, then the next. -/
def arcBody : Stmt :=
  .seq wstep (.seq ztiqe
    ztipj)

/-- **The scan of arc record `j`.** -/
def arcScan : Stmt := .seq arcHead (.seq arcLen (.seq arcInit (.whileLtN 120085 120088 arcBody)))

/-- The registers written by `arcScan`. -/
def BA (r : ℕ) : Bool := BW r || decide zttxl || decide ztnec
theorem BA_const (r : ℕ) (h1 : 120010 ≤ r) (h2 : r ≤ 120049) : BA r = false := by
  simp only [BA, BW, BE, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega

/-- The walk edges scanned for an arc starting on edge `se`. -/
def scanW (nW se k : ℕ) : ℕ := (se + nW - 1 + k) % nW

/-- The points scanned before step `t`. -/
def scanned (C : Chain) (nW se t : ℕ) : Set Point := {x | ∃ k, k < t ∧ x ∈ wseg C (scanW nW se k)}
theorem scanned_succ (C : Chain) (nW se t : ℕ) :
    scanned C nW se ztbx = scanned C nW se t ∪ wseg C (scanW nW se t) := by
  zumx
  simp only [scanned, Set.mem_ofPred_eq, Set.mem_union]
  grind

/-- **The invariant of the loop of `arcScan`.** -/
structure AInv (P : Polygon) (W : ℕ) (C : Chain) (V : QV) (z : Point) (c₀ : Config) (S : Set Point)
    (se len : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  q : QConst P V c
  b : BestOK P.n V.s V.m c
  t_le : c.nreg 120085 ≤ len + 1
  lim : c.nreg 120088 = len + 1
  w : c.nreg 120070 = scanW zthn se ztvhj
  hit : Sweep.FirstHitOpt (S ∪ scanned C zthn se ztvhj) z zthx
    ztwmd
  fr : FrameB BA c₀ c
variable {P : Polygon} {W : ℕ}
theorem arcBody_inv (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {V : QV} {z : Point} (hs : SemOK P C V z) {c₀ : Config} {S : Set Point} {se len : ℕ}
    (_hse : se < 2 * V.m + 7) {c : Config} (h : AInv P W C V z c₀ S se len c)
    (ht : c.nreg 120085 < c.nreg 120088) :
    ∃ c' k, Exec P W arcBody c c' k ∧ AInv P W C V z c₀ S se len c' ∧ k ≤ 1130 ∧
      len + 1 - c'.nreg 120085 < len + 1 - c.nreg 120085 := by
  zuesm
  have hmn : ztgaj := by
    have := C.m_lt; zvmxw at this; omega
  set t := c.nreg 120085 with ht_def
  have htl : t < len + 1 := by rw [h.lim] at ht; exact ht
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, hb₁, v₁⟩ := wstep_exec (P := P) hG by_omega hs.hD hv c h.wb h.q h.b
  have R₁ := f₁.1
  have x85 : c₁.nreg 120085 = t := R₁ _ by_decide
  have x70 : c₁.nreg 120070 = scanW _ se t := (R₁ _ by_decide).trans h.w
  have hq₁ := h.q.frame f₁ BW_const
  have hwn : scanW _ se t < 2 * V.m + 7 := Nat.mod_lt _ by_omega
  obtain ⟨c₂, k₂, e₂, hk₂, v₂⟩ : ∃ c₂ k₂, Exec P W
      ztiqe c₁ c₂ k₂ ∧ k₂ = 2 ∧
      (c₂.nreg 120085 = t + 1 ∧ c₂.nreg 120070 = scanW zthn se t + 1 ∧
        (∀ r, r ≠ 120085 → r ≠ 120070 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
        c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output) := by
    zud
    have hb1 : ztmwv := by have := h.wb.1 120088; omega
    have hb2 : scanW zthn se t + 1 ≤ W := by
      have := h.wb.1 120020; rw [h.q.nW] at this; omega
    exec_block
    · zuomp; omega
    · config_simp; zuomq; omega
    · refine ztfkb
      · config_simp; zuomp
      · config_simp; zuomq
      simp_all
  obtain ⟨v85, v70, r₂, m₂, rr₂, rm₂, o₂⟩ := v₂
  zuesc
  -- wrap around
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃, m₃, rr₃, rm₃, o₃⟩ : ∃ c₃ k₃, Exec P W
      ztipj c₂ c₃ k₃ ∧ k₃ ≤ 3 ∧
      c₃.nreg 120070 = scanW zthn se ztbx ∧
      (∀ r, r ≠ 120070 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have hsucc : scanW zthn se ztbx =
        (scanW zthn se t + 1) % zthn := by
      unfold scanW
      grind
    by_cases hlt : scanW zthn se t + 1 < 2 * V.m + 7
    · refine ⟨c₂, _, .ifLtN_true ztliy ztdyc, by_omega,
        ?_, by_omega, rfl, rfl, rfl, rfl⟩
      rw [v70, hsucc, Nat.mod_eq_of_lt hlt]
    · refine ⟨_, _, .ifLtN_false ztliy
        (Exec.constN e₂.wb_right 120070 0 by_omega), by_omega, ?_, fun r hr => ?_, rfl, rfl,
        rfl, rfl⟩
      · config_simp
        rw [hsucc, show scanW _ se t + 1 = 2 * V.m + 7 by omega, Nat.mod_self]
      simp_all
  have R₂₃ : ∀ r, r ≠ 120085 → r ≠ 120070 → c₃.nreg r = c₁.nreg r := by_simp_all
  have fb₂₃ : FrameB BA c₁ c₃ := by
    refine ⟨fun r hr => R₂₃ r ?_ ?_, by_simp_all, by_simp_all, by_simp_all,
      by simp_all⟩
    · zueta
    · zueta
  have fb₁ : FrameB BA c c₁ := by
    refine ⟨fun r hr => f₁.1 r ?_, fun r hr => f₁.2.1 r ?_, f₁.2.2.1, f₁.2.2.2.1, f₁.2.2.2.2⟩ <;>
      · simp only [BA, Bool.or_eq_false_iff] at hr; simp_all
  refine ⟨c₃, _, .seq e₁ ztcr, ⟨e₃.wb_right, hq₂.congr by_grind,
    ?_, ?_, ?_, ?_, ?_, h.fr.trans (fb₁.trans fb₂₃)⟩, by_omega, ?_⟩
  · zucku
    rw [R₂₃ 120050 by_decide by_decide, R₂₃ 120051 by_decide by_decide,
      R₂₃ 120052 by_decide by_decide]
    tauto
  · simp_all
  · rw [R₂₃ _ by_decide by_decide, R₁ _ by_decide]; exact h.lim
  · simp_all
  · have hbo : bestOf c₃ = bestOf c₁ := by
      zulbi
      simp_all
    rw [hbo, v₁, r₃ _ by_decide, v85, scanned_succ, ← Set.union_assoc, h.w]
    exact wupd_step hs h.hit _
  grind

/-- The number of scanned walk edges of an arc, minus one, as the program computes it. -/
def lenOf (A nW se ee p : ℕ) : ℕ := (if p + 1 < A then ee - se else ee + nW - se) + 2

/-- **The scan of arc record `j`.** -/
theorem arcScan_exec (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W)
    {C : Chain} {V : QV} {z : Point} (hs : SemOK P C V z) (c : Config) (hw : WordsBounded W c)
    (hq : QConst P V c) (hb : BestOK P.n V.s V.m c) {se ee p : ℕ}
    (hse : c.nmem (V.AB + 5 * c.nreg 120080 + 1) = se)
    (hee : c.nmem (V.AB + 5 * c.nreg 120080 + 3) = ee)
    (hp : c.nmem (V.POS + c.nreg 120080) = p) (hsen : se < 2 * V.m + 7)
    (heen : ee < 2 * V.m + 7) (hpA : p < V.A) (haddr : V.AB + 5 * c.nreg 120080 + 3 ≤ W)
    (hpos : V.POS + c.nreg 120080 ≤ W)
    {S : Set Point}
    (hS : Sweep.FirstHitOpt S z zthx ztwmd) :
    ∃ c' k, Exec P W arcScan c c' k ∧ k ≤ 1132 * ztyjk + 30 ∧
      FrameB BA c c' ∧ BestOK P.n V.s V.m c' ∧
      Sweep.FirstHitOpt (S ∪ scanned C zthn se ztyjk) z
        zthx ztwot := by
  zuesm
  have hmn : ztgaj := by
    have := C.m_lt; zvmxw at this; omega
  have hVm := hv.m
  have hAW : V.A ≤ W := by have := hw.1 120030; rw [hq.A] at this; omega
  -- 1. the head
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W arcHead c c₁ k₁ ∧ k₁ = 11 ∧
      (c₁.nreg 120081 = se ∧ c₁.nreg 120082 = ee ∧ c₁.nreg 120083 = p ∧
        c₁.nreg 120087 = p + 1 ∧
        (∀ r, r ≠ 120081 → r ≠ 120082 → r ≠ 120083 → r ≠ 120086 → r ≠ 120087 →
          c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧
        c₁.output = c.output) := by
    unfold arcHead
    exec_block
    · omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; rw [hq.AB]; omega
    · config_simp; rw [hq.AB, hq.one]; omega
    · config_simp; zunzw; omega
    · config_simp; zupab; omega
    · config_simp; rw [hq.POS, hq.one]
      omega
    · refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [hq.AB, hq.one, ← hse]; grind
      · config_simp; zunzw
        grind
      · config_simp; zupab; exact hp
      · config_simp; rw [hq.POS, hq.one, hp]
      simp_all
  obtain ⟨x81, x82, x83, x87, r₁, m₁, rr₁, rm₁, o₁⟩ := v₁
  zubwn
  zud
  -- 2. the length
  set L0 := (if p + 1 < V.A then ee - se else ee + zthn - se) with hL0
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, r₂⟩ : ∃ c₂ k₂, Exec P W arcLen c₁ c₂ k₂ ∧ k₂ ≤ 4 ∧
      c₂.nreg 120084 = L0 ∧ (∀ r, r ≠ 120084 → c₂.nreg r = c₁.nreg r) := by
    unfold arcLen
    by_cases hlt : p + 1 < V.A
    · refine ⟨_, _, .ifLtN_true ztljb ztbly, by_omega,
        ?_, fun r hr => ?_⟩
      · simp_all
      simp_all
    · obtain ⟨c₂, k₂, e₂, hk₂, v₂⟩ : ∃ c₂ k₂, Exec P W
          ztiqd c₁ c₂ k₂ ∧ k₂ = 2 ∧
          (c₂.nreg 120084 = ee + zthn - se ∧
            ∀ r, r ≠ 120084 → c₂.nreg r = c₁.nreg r) := by
        exec_block
        · rw [x82, hq₁.nW]; omega
        · zuhjd
          · config_simp; rw [x82, hq₁.nW, x81]
          · config_simp; upd_solve
      exact ⟨c₂, _, .ifLtN_false ztljb e₂, by_omega,
        by grind, v₂.2⟩
  zue
  zuesc
  have hL0le : L0 ≤ 2 * zthn := by_grind
  -- 3. the initialisation
  obtain ⟨c₃, k₃, e₃, hk₃, v₃⟩ : ∃ c₃ k₃, Exec P W
      ztgfi
      c₂ c₃ k₃ ∧ k₃ = 3 ∧ (c₃.nreg 120084 = L0 + 2 ∧ c₃.nreg 120070 = se + zthn - 1 ∧
        ∀ r, r ≠ 120084 → r ≠ 120070 → c₃.nreg r = c₂.nreg r) := by
    exec_block
    · zunpz; omega
    · config_simp; rw [r₂ _ by_decide, x81, hq₂.nW]; omega
    · refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_⟩
      · config_simp; zunpz
      · config_simp; rw [r₂ _ by_decide, x81, hq₂.nW, hq₂.one]
      · config_simp; upd_solve
  obtain ⟨v84, v70, r₃⟩ := v₃
  zuiyz
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, r₄, -⟩ := modSub_exec (P := P) (r := 120070) (nr := 120020)
    by_decide c₃ e₃.wb_right (by rw [v70, hq₃.nW]; omega)
  rw [v70, hq₃.nW] at v₄
  have hq₄ := hq₃.congr fun r h1 h2 => r₄ r by_omega
  obtain ⟨c₅, k₅, e₅, hk₅, v₅⟩ : ∃ c₅ k₅, Exec P W
      ztjpb c₄ c₅ k₅ ∧ k₅ = 2 ∧
      (c₅.nreg 120085 = 0 ∧ c₅.nreg 120088 = L0 + 2 + 1 ∧
        (∀ r, r ≠ 120085 → r ≠ 120088 → c₅.nreg r = c₄.nreg r) ∧ c₅.nmem = c₄.nmem ∧
        c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output) := by
    zucc
    exec_block
    · omega
    · config_simp; zuntg; omega
    · refine ⟨rfl, by config_simp, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; zuntg
      · config_simp; upd_solve
  obtain ⟨v85, v88, r₅, m₅, rr₅, rm₅, o₅⟩ := v₅
  have hlen : lenOf V.A _ se ee p = L0 + 2 := rfl
  -- frames of the preparation
  have ex₀ : Exec P W (.seq arcHead (.seq arcLen arcInit)) c c₅ _ :=
    .seq e₁ ztbq
  have f₀' := exec_frameB ex₀ (B := fun r => decide zttxl ||
    decide ztnec) by_decide
  have f₀ : FrameB BA c c₅ := FrameB.mono f₀' fun r hr => by
    simp only [BA, Bool.or_eq_true, decide_eq_true_eq] at hr ⊢; tauto
  have I₀ : AInv P W C V z c S se ztszf c₅ := by
    refine ⟨e₅.wb_right, hq₄.congr fun r h1 h2 => r₅ r by_omega by_omega, ?_, by_omega, v88,
      ?_, ?_, f₀⟩
    · zucku
      rw [f₀'.1 120050 by_decide, f₀'.1 120051 by_decide, f₀'.1 120052 by_decide]
      zulfi
    · rw [r₅ _ by_decide by_decide, v₄, v85]; rfl
    · have hbo : ztmuh := by
        unfold bestOf; rw [f₀'.1 120050 by_decide, f₀'.1 120052 by_decide]
      rw [hbo, v85]
      have : scanned C zthn se 0 = ∅ := by
        ext x; simp [scanned]
      zuhnm
  -- 4. the loop
  obtain ⟨c₆, k₆, e₆, I₆, hex, hk₆⟩ := Exec.whileLtN_bounded (a := 120085) (b := 120088)
    (AInv P W C V z c S se ztszf) (fun d => L0 + 2 + 1 - d.nreg 120085) 1130
    ztpf
    (fun d hd ht => by
      obtain ⟨d', k, e, I, hk, hi⟩ := arcBody_inv (P := P) hG hW hs hsen hd ht
      exact ztkkp) I₀
  have ht6 : c₆.nreg 120085 = L0 + 2 + 1 := by
    have := I₆.t_le; rw [I₆.lim] at hex; omega
  refine ⟨c₆, _, .seq e₁ (.seq e₂ (.seq ztbpd e₆)), ?_, I₆.fr, I₆.b, ?_⟩
  · omega
  · have := I₆.hit
    grind
section Mem
variable (m : ℕ → ℕ) (V : QV)

/-- The start edge of arc record `j`. -/
def arcSe (j : ℕ) : ℕ := m (V.AB + 5 * j + 1)
/-- The end edge of arc record `j`. -/
def arcEe (j : ℕ) : ℕ := m (V.AB + 5 * j + 3)
/-- The spine position of arc record `j`. -/
def arcPos (j : ℕ) : ℕ := m ztfou
/-- The number of scanned walk edges of arc record `j`, minus one. -/
def arcLenM (j : ℕ) : ℕ := lenOf V.A zthn ztlfy (arcEe m V j) ztdlm
/-- The arc record of node `v`. -/
def nodeArc0 (v : ℕ) : ℕ := m (V.SB + v)
/-- The region of node `v`. -/
def nodeReg (v : ℕ) : ℕ := m (V.AB + 5 * nodeArc0 m V v)
/-- The number of arcs of the region of node `v`. -/
def nodeNa (v : ℕ) : ℕ := m (V.RB + 5 * nodeReg m V v)
/-- The start of the arc list of the region of node `v`. -/
def nodeLs (v : ℕ) : ℕ := m (V.RB + 5 * nodeReg m V v + 1)
/-- The `t`-th arc record of the region of node `v`. -/
def nodeArc (v t : ℕ) : ℕ := m (V.LB + nodeLs m V v + t)

/-- The points scanned for arc record `j`. -/
def arcPts (C : Chain) (j : ℕ) : Set Point :=
  scanned C zthn ztlfy (arcLenM m V j + 1)

/-- **The points scanned for node `v`.** -/
def nodePts (C : Chain) (v : ℕ) : Set Point :=
  {x | v < V.A ∧ ∃ t, t < nodeNa m V v ∧ x ∈ arcPts m V C ztqub}

/-- The cost of the arcs of node `v` from the `t`-th on. -/
def nodeCostFrom (v t : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico t (nodeNa m V v), (1132 * (arcLenM m V (nodeArc m V v i) + 1) + 40)

/-- **The cost of the scan of node `v`.** -/
def nodeCost (v : ℕ) : ℕ := if v < V.A then nodeCostFrom m V v 0 + 40 else 40
end Mem

/-- **The memory facts** that keep the scans in range (word bound `W`). -/
structure QMem (V : QV) (m : ℕ → ℕ) (W : ℕ) : Prop where
  A_le : V.A ≤ W
  arc : ∀ j, j < V.A → arcSe m V j < 2 * V.m + 7 ∧ arcEe m V j < 2 * V.m + 7 ∧
    arcPos m V j < V.A ∧ V.AB + 5 * j + 3 ≤ W ∧ V.POS + j ≤ W
  node : ∀ v, v < V.A → V.SB + v ≤ W ∧ nodeArc0 m V v < V.A ∧
    V.RB + 5 * nodeReg m V v + 1 ≤ W ∧ V.LB + nodeLs m V v ≤ W ∧
    ∀ t, t < nodeNa m V v → nodeArc m V v t < V.A ∧ V.LB + nodeLs m V v + t ≤ W

/-! ## The program -/

/-- `rd := rb + 5 · rs`. -/
def t5 (rd rs rb : ℕ) : Stmt := block [.addN rd rs rs, .addN rd rd rd, .addN rd rd rs, .addN rd rd rb]

/-- Read the region of node `v` and its arc list. -/
def nodeHead : Stmt :=
  .seq (block [.addN 120091 120046 120090, .loadN 120092 120091])
    (.seq (t5 120093 120092 120044) (.seq (.instr (.loadN 120094 120093))
      (.seq (t5 120095 120094 120045) (block [.loadN 120096 120095, .addN 120095 120095 120011,
        .loadN 120097 120095, .addN 120097 120097 120047, .constN 120098 0]))))

/-- One arc of the region. -/
def nodeBody : Stmt :=
  .seq ztjom
    (.seq arcScan (.instr (.addN 120098 120098 120011)))

/-- **The scan of node `v`** (register `120090`). -/
def nodeScanS : Stmt :=
  .ifLtN 120090 120030 (.seq nodeHead (.whileLtN 120098 120096 nodeBody)) .skip

/-- The registers written by `nodeScanS`. -/
def BN (r : ℕ) : Bool := BA r || decide (r = 120080) || decide (120091 ≤ r ∧ r ≤ 120099)
theorem BN_const (r : ℕ) (h1 : 120010 ≤ r) (h2 : r ≤ 120049) : BN r = false := by
  simp only [BN, BA, BW, BE, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega

/-! ## Execution -/
variable {P : Polygon} {W : ℕ}
theorem t5_exec {rd rs rb : ℕ} (h1 : rd ≠ rs) (h2 : rd ≠ rb) (c : Config)
    (hw : WordsBounded W c) (h : c.nreg rb + 5 * c.nreg rs ≤ W) :
    ∃ c', Exec P W (t5 rd rs rb) c c' 4 ∧ c'.nreg rd = c.nreg rb + 5 * c.nreg rs ∧
      ztcqi ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold t5
  obtain ⟨c', k, ex, hk, hq⟩ : ∃ c' k, Exec P W (block [.addN rd rs rs, .addN rd rd rd,
      .addN rd rd rs, .addN rd rd rb]) c c' k ∧ k = 4 ∧ (c'.nreg rd = c.nreg rb + 5 * c.nreg rs ∧
        ztcqi ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
    exec_block
    · omega
    · config_simp; omega
    · config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;> omega)
    · config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;> omega)
    · refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;>
          first | omega)
      simp_all
  grind

/-- **The invariant of the loop of `nodeScanS`.** -/
structure NInv (P : Polygon) (W : ℕ) (C : Chain) (V : QV) (z : Point) (c₀ : Config)
    (S : Set Point) (v : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  q : QConst P V c
  b : BestOK P.n V.s V.m c
  rv : c.nreg 120090 = v
  na : c.nreg 120096 = nodeNa c₀.nmem V v
  ls : c.nreg 120097 = V.LB + nodeLs c₀.nmem V v
  t_le : c.nreg 120098 ≤ nodeNa c₀.nmem V v
  hit : Sweep.FirstHitOpt (S ∪ {x | ∃ t, t < c.nreg 120098 ∧
      x ∈ arcPts c₀.nmem V C ztqua}) z (sgnOf V.σb)
    ztwmd
  fr : FrameB BN c₀ c
theorem nodeCostFrom_succ (m : ℕ → ℕ) (V : QV) {v t : ℕ} (ht : t < nodeNa m V v) :
    nodeCostFrom m V v t = (1132 * (arcLenM m V ztqub + 1) + 40) +
      nodeCostFrom m V v ztbx := by
  unfold nodeCostFrom
  rw [Finset.sum_eq_sum_Ico_succ_bot ht]
theorem nodeBody_inv (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {V : QV} {z : Point} (hs : SemOK P C V z) {c₀ : Config} {S : Set Point} {v : ℕ}
    (hvA : v < V.A) (hm : QMem V c₀.nmem W) {c : Config} (h : NInv P W C V z c₀ S v c)
    (ht : c.nreg 120098 < c.nreg 120096) :
    ∃ c' k, Exec P W nodeBody c c' k ∧ NInv P W C V z c₀ S v c' ∧
      nodeCostFrom c₀.nmem V v (c'.nreg 120098) + k + 2 ≤
        nodeCostFrom c₀.nmem V v (c.nreg 120098) := by
  set t := c.nreg 120098 with ht_def
  have htn : t < nodeNa c₀.nmem V v := by rw [h.na] at ht; exact ht
  have hmem := h.fr.2.2.1
  zudri
  obtain ⟨hjA, hLBt⟩ := hlist t htn
  set j := nodeArc c₀.nmem V v t with hj_def
  obtain ⟨hsen, heen, hpA, haddr, hpos⟩ := hm.arc j hjA
  -- 1. read the arc
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W
      ztjom c c₁ k₁ ∧ k₁ = 2 ∧
      (c₁.nreg 120080 = j ∧ (∀ r, r ≠ 120099 → r ≠ 120080 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    zuesn
    exec_block
    · rw [h.ls]; omega
    · refine ztcqz
      · config_simp; rw [h.ls, hmem]; rfl
      simp_all
  obtain ⟨x80, r₁, m₁, rr₁, rm₁, o₁⟩ := v₁
  have hq₁ : ztehw := h.q.congr by_grind
  have hb₁ : ztiyc := by
    zucku
    rw [r₁ 120050 by_decide by_decide, r₁ 120051 by_decide by_decide,
      r₁ 120052 by_decide by_decide]
    exact h.b
  have hbo₁ : ztguc := by
    zubqh
  have hm₁ := m₁.trans hmem
  -- 2. scan it
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hb₂, hit₂⟩ := arcScan_exec (P := P) hG hW hs c₁ e₁.wb_right hq₁ hb₁
    (se := arcSe c₀.nmem V j) (ee := arcEe c₀.nmem V j) (p := arcPos c₀.nmem V j)
    ztfpw ztfpw ztfpw hsen heen hpA
    by_omega by_omega
    (S := S ∪ {x | ∃ t', t' < t ∧ x ∈ arcPts c₀.nmem V C ztkbm})
    ztgfu
  zumaq
  have hq₂ := hq₁.frame f₂ BA_const
  -- 3. next
  have x98 : c₂.nreg 120098 = t := (R₂ _ by_decide).trans by_simp_all
  have hW98 : ztmwv := by
    have := h.wb.1 120096; omega
  obtain ⟨c₃, e₃, v₃, r₃, m₃⟩ := add_exec (P := P) e₂.wb_right 120098 120098 120011
    (by rw [x98, hq₂.one]; omega)
  rw [x98, hq₂.one] at v₃
  have R₃ : ∀ r, BA r = false → r ≠ 120099 → r ≠ 120080 → r ≠ 120098 → c₃.nreg r = c.nreg r :=
    by simp_all
  have ex : Exec P W nodeBody c c₃ _ := .seq e₁ ztcr
  have fb := exec_frameB ex (B := BN) by_decide
  refine ⟨c₃, _, ex, ⟨e₃.wb_right, hq₂.congr by_grind, ?_, ?_, ?_, ?_,
    ?_, ?_, h.fr.trans fb⟩, ?_⟩
  · zucku
    zudvg

  · zunfk; exact h.rv
  · zunfk; exact h.na
  · zunfk; exact h.ls
  · omega
  · have hbo : ztmug := by
      zubqh
    zugdo
    have e : {x | ∃ t', t' < t + 1 ∧ x ∈ arcPts c₀.nmem V C ztkbm} =
        {x | ∃ t', t' < t ∧ x ∈ arcPts c₀.nmem V C ztkbm} ∪
          arcPts c₀.nmem V C j := by
      zumx
      zujny
      grind
    rw [e, ← Set.union_assoc]
    exact hit₂
  · rw [v₃, nodeCostFrom_succ c₀.nmem V htn]
    have e : arcLenM c₀.nmem V ztqua = lenOf V.A _
        (arcSe c₀.nmem V j) (arcEe c₀.nmem V j) (arcPos c₀.nmem V j) := rfl
    omega

/-- **The scan of node `v`** (register `120090`). -/
theorem nodeScan_exec (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W)
    {C : Chain} {V : QV} {z : Point} (hs : SemOK P C V z) (c : Config) (hw : WordsBounded W c)
    (hq : QConst P V c) (hb : BestOK P.n V.s V.m c) (hm : QMem V c.nmem W) {S : Set Point}
    (hS : Sweep.FirstHitOpt S z zthx ztwmd) :
    ∃ c' k, Exec P W nodeScanS c c' k ∧ k ≤ nodeCost c.nmem V ztvhk ∧
      FrameB BN c c' ∧ BestOK P.n V.s V.m c' ∧
      Sweep.FirstHitOpt (S ∪ nodePts c.nmem V C ztvhk) z zthx
        ztwot := by
  set v := c.nreg 120090 with hv_def
  by_cases hvA : v < V.A
  swap
  · refine ⟨c, _, .ifLtN_false ztnty ztjd, by
      unfold nodeCost; grind,
      FrameB.refl _ _, hb, ?_⟩
    have e : nodePts c.nmem V C v = ∅ := by
      ext x; simp only [nodePts, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      omega
    simp_all
  zudri
  obtain ⟨-, -, -, haddr0, -⟩ := hm.arc _ hj0
  -- 1. the head
  have m0 := hm
  obtain ⟨c₁, e₁, v₁⟩ : ∃ c₁, Exec P W (block [.addN 120091 120046 120090, .loadN 120092 120091])
      c c₁ 2 ∧ (c₁.nreg 120092 = nodeArc0 c.nmem V v ∧
        ztgsh ∧ c₁.nmem = c.nmem ∧
        c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    obtain ⟨c₁, k, e, hk, hq'⟩ : ∃ c₁ k, Exec P W (block [.addN 120091 120046 120090,
        .loadN 120092 120091]) c c₁ k ∧ k = 2 ∧ (c₁.nreg 120092 = nodeArc0 c.nmem V v ∧
        ztgsh ∧ c₁.nmem = c.nmem ∧
        c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
      exec_block
      · zupad; omega
      · refine ztcqz
        · config_simp; zupad; rfl
        simp_all
    grind
  obtain ⟨x92, r₁, m₁, rr₁, rm₁, o₁⟩ := v₁
  obtain ⟨c₂, e₂, v₂, r₂, m₂, rr₂, rm₂, o₂⟩ := t5_exec (P := P) (rd := 120093) (rs := 120092)
    (rb := 120044) by_decide by_decide c₁ e₁.wb_right (by
      rw [x92, r₁ _ by_decide by_decide, hq.AB]; omega)
  rw [x92, r₁ _ by_decide by_decide, hq.AB] at v₂
  have e₃ := Exec.loadN e₂.wb_right 120094 120093 (P := P)
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 120094 _ } with hc₃
  have x94 : c₃.nreg 120094 = nodeReg c.nmem V v := by
    zumwr; config_simp; rw [v₂, m₂, m₁]; rfl
  have r₃ : ∀ r, r ≠ 120094 → c₃.nreg r = c₂.nreg r := by_simp_all
  obtain ⟨c₄, e₄, v₄, r₄, m₄, rr₄, rm₄, o₄⟩ := t5_exec (P := P) (rd := 120095) (rs := 120094)
    (rb := 120045) by_decide by_decide c₃ e₃.wb_right (by
      rw [x94, r₃ _ by_decide, r₂ _ by_decide, r₁ _ by_decide by_decide, hq.RB]; omega)
  rw [x94, r₃ _ by_decide, r₂ _ by_decide, r₁ _ by_decide by_decide, hq.RB] at v₄
  have m₄' : zteid := by_simp_all
  obtain ⟨c₅, k₅, e₅, hk₅, v₅⟩ : ∃ c₅ k₅, Exec P W (block [.loadN 120096 120095,
      .addN 120095 120095 120011, .loadN 120097 120095, .addN 120097 120097 120047,
      .constN 120098 0]) c₄ c₅ k₅ ∧ k₅ = 5 ∧
      (c₅.nreg 120096 = nodeNa c.nmem V v ∧ c₅.nreg 120097 = V.LB + nodeLs c.nmem V v ∧
        c₅.nreg 120098 = 0 ∧
        (∀ r, r ≠ 120095 → r ≠ 120096 → r ≠ 120097 → r ≠ 120098 → c₅.nreg r = c₄.nreg r) ∧
        c₅.nmem = c₄.nmem ∧ c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output) := by
    have hq4 : ztpnq := by
      rw [r₄ _ by_decide, r₃ _ by_decide, r₂ _ by_decide, r₁ _ by_decide by_decide,
        hq.one]
    have hq47 : c₄.nreg 120047 = V.LB := by
      rw [r₄ _ by_decide, r₃ _ by_decide, r₂ _ by_decide, r₁ _ by_decide by_decide,
        hq.LB]
    zucc
    exec_block
    · simp_all
    · config_simp; rw [v₄, hq4, hq47, m₄']
      have : nodeLs c.nmem V v = c.nmem _ := rfl
      omega
    · omega
    · refine ⟨rfl, ?_, ?_, by config_simp, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [v₄, m₄']; rfl
      · config_simp; rw [v₄, hq4, hq47, m₄', Nat.add_comm]; rfl
      · config_simp; upd_solve
  obtain ⟨x96, x97, x98, r₅, m₅, rr₅, rm₅, o₅⟩ := v₅
  -- the frame of the head
  have exh : Exec P W nodeHead c c₅ _ :=
    .seq e₁ ztbq
  have fh := exec_frameB exh (B := fun r => decide (120091 ≤ r ∧ r ≤ 120098)) by_decide
  have hmh := fh.2.2.1
  have R₅ : ∀ r, (r < 120091 ∨ 120098 < r) → c₅.nreg r = c.nreg r := by_grind
  have I₀ : NInv P W C V z c S v c₅ := by
    refine ⟨e₅.wb_right, hq.congr by_grind, ?_, by_grind, x96, x97,
      by omega, ?_, FrameB.mono fh fun r hr => ?_⟩
    · zucku
      rw [R₅ 120050 by_omega, R₅ 120051 by_omega, R₅ 120052 by_omega]; exact hb
    · have hbo : ztmuh := by
        zujqh
      rw [hbo, x98]
      have : {x | ∃ t, t < 0 ∧ x ∈ arcPts c.nmem V C ztqtz} = ∅ := by
        simp
      zuhnm
    · zucy
      simp only [BN, Bool.or_eq_true, decide_eq_true_eq]; omega
  -- 2. the loop
  obtain ⟨c₆, k₆, e₆, I₆, hex, hk₆⟩ := Exec.whileLtN_potential (a := 120098) (b := 120096)
    (NInv P W C V z c S v) (fun d => nodeCostFrom c.nmem V v (d.nreg 120098)) ztpf
    (fun d hd ht => nodeBody_inv (P := P) hG hW hs hvA hm hd ht) I₀
  have ht6 : c₆.nreg 120098 = nodeNa c.nmem V v := by
    have := I₆.t_le; rw [I₆.na] at hex; omega
  refine ⟨c₆, _, .ifLtN_true ztnty (.seq exh e₆), ?_, I₆.fr, I₆.b, ?_⟩
  · rw [x98] at hk₆
    unfold nodeCost; grind
  · have e : nodePts c.nmem V C v =
        {x | ∃ t, t < c₆.nreg 120098 ∧ x ∈ arcPts c.nmem V C ztqtz} := by
      zumx
      simp only [nodePts, Set.mem_ofPred_eq, ht6]
      grind
    zvmwe; exact I₆.hit
def dstarBody : Stmt :=
  .seq ztjon
    (.seq nodeScanS (.instr (.addN 120100 120100 120011)))

/-- **The scan of the nodes of `D*`.** -/
def dstarS : Stmt := .seq (.instr (.constN 120100 0)) (.whileLtN 120100 120035 dstarBody)

/-- The registers written by `dstarS`. -/
def BD (r : ℕ) : Bool := BN r || decide ztogh || decide (120100 ≤ r ∧ r ≤ 120101)
theorem BD_const (r : ℕ) (h1 : 120010 ≤ r) (h2 : r ≤ 120049) : BD r = false := by
  simp only [BD, BN, BA, BW, BE, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega

/-- The cost of the listed nodes from the `i`-th on. -/
def dstarCostFrom (m : ℕ → ℕ) (V : QV) (i : ℕ) : ℕ :=
  ∑ t ∈ Finset.Ico i V.nD, (nodeCost m V ztilm + 6)

/-- **The cost of the scan of `D*`.** -/
def dstarCost (m : ℕ → ℕ) (V : QV) : ℕ := dstarCostFrom m V 0 + 4

/-- The points of the listed nodes before the `i`-th. -/
def dstarPts (m : ℕ → ℕ) (V : QV) (C : Chain) (i : ℕ) : Set Point :=
  {x | ∃ t, t < i ∧ x ∈ nodePts m V C ztilm}

/-- **The invariant of the loop of `dstarS`.** -/
structure DInv (P : Polygon) (W : ℕ) (C : Chain) (V : QV) (z : Point) (c₀ : Config)
    (S : Set Point) (c : Config) : Prop where
  wb : WordsBounded W c
  q : QConst P V c
  b : BestOK P.n V.s V.m c
  i_le : c.nreg 120100 ≤ V.nD
  hit : Sweep.FirstHitOpt (S ∪ dstarPts c₀.nmem V C ztvhl) z zthx
    ztwmd
  fr : FrameB BD c₀ c
variable {P : Polygon} {W : ℕ}
theorem dstarBody_inv (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {V : QV} {z : Point} (hs : SemOK P C V z) {c₀ : Config} {S : Set Point}
    (hm : QMem V c₀.nmem W) (hDL : V.DL + V.nD ≤ W) {c : Config} (h : DInv P W C V z c₀ S c)
    (ht : c.nreg 120100 < c.nreg 120035) :
    ∃ c' k, Exec P W dstarBody c c' k ∧ DInv P W C V z c₀ S c' ∧
      dstarCostFrom c₀.nmem V (c'.nreg 120100) + k + 2 ≤ dstarCostFrom c₀.nmem V ztvhl := by
  set i := c.nreg 120100 with hi_def
  have hin : i < V.nD := by rw [h.q.nD] at ht; exact ht
  have hmem : c.nmem = c₀.nmem := h.fr.2.2.1
  -- 1. read the node
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W
      ztjon c c₁ k₁ ∧ k₁ = 2 ∧
      (c₁.nreg 120090 = c₀.nmem ztdgi ∧ (∀ r, r ≠ 120101 → r ≠ 120090 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    zuesn
    exec_block
    · rw [h.q.DL]; omega
    · refine ztcqz
      · config_simp; rw [h.q.DL, hmem]
      simp_all
  obtain ⟨x90, r₁, m₁, rr₁, rm₁, o₁⟩ := v₁
  have hq₁ : ztehw := h.q.congr fun r h1 h2 => r₁ r by_omega by_omega
  have hb₁ : ztiyc := by
    zucku
    rw [r₁ 120050 by_decide by_decide, r₁ 120051 by_decide by_decide,
      r₁ 120052 by_decide by_decide]
    exact h.b
  have hbo₁ : ztguc := by
    zubqh
  have hm₁ : c₁.nmem = c₀.nmem := m₁.trans hmem
  -- 2. scan it
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hb₂, hit₂⟩ := nodeScan_exec (P := P) hG hW hs c₁ e₁.wb_right hq₁ hb₁
    by_simp_all (S := S ∪ dstarPts c₀.nmem V C i) ztgfu
  rw [x90, hm₁] at hk₂ hit₂
  have R₂ : ∀ r, BN r = false → c₂.nreg r = c₁.nreg r := f₂.1
  have hq₂ : ztehx := hq₁.frame f₂ BN_const
  -- 3. next
  have x100 : c₂.nreg 120100 = i := (R₂ _ by_decide).trans (r₁ _ by_decide by_decide)
  have hW1 : ztsiz := by_omega
  obtain ⟨c₃, e₃, v₃, r₃, m₃⟩ := add_exec (P := P) e₂.wb_right 120100 120100 120011
    (by rw [x100, hq₂.one]; omega)
  rw [x100, hq₂.one] at v₃
  have ex : Exec P W dstarBody c c₃ ztyrf := .seq e₁ ztcr
  have fb := exec_frameB ex (B := BD) by_decide
  refine ⟨c₃, _, ex, ⟨e₃.wb_right, hq₂.congr fun r h1 h2 => r₃ r by_omega, ?_, by_omega, ?_,
    h.fr.trans fb⟩, ?_⟩
  · zucku
    zudvg

  · have hbo : ztmug := by
      zubqh
    zugdo
    have e : dstarPts c₀.nmem V C ztg =
        dstarPts c₀.nmem V C i ∪ nodePts c₀.nmem V C (c₀.nmem ztdgi) := by
      zumx
      simp only [dstarPts, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · grind
      · rintro (⟨t, ht, hx⟩ | hx)
        · grind
        · exact ⟨i, by_omega, hx⟩
    grind
  · rw [v₃]
    unfold dstarCostFrom
    rw [Finset.sum_eq_sum_Ico_succ_bot hin]
    omega

/-- **The scan of the nodes of `D*`.** -/
theorem dstarS_exec (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W)
    {C : Chain} {V : QV} {z : Point} (hs : SemOK P C V z) (c : Config) (hw : WordsBounded W c)
    (hq : QConst P V c) (hb : BestOK P.n V.s V.m c) (hm : QMem V c.nmem W) (hDL : V.DL + V.nD ≤ W)
    {S : Set Point}
    (hS : Sweep.FirstHitOpt S z zthx ztwmd) :
    ∃ c' k, Exec P W dstarS c c' k ∧ k ≤ dstarCost c.nmem V ∧ FrameB BD c c' ∧
      BestOK P.n V.s V.m c' ∧
      Sweep.FirstHitOpt (S ∪ dstarPts c.nmem V C V.nD) z zthx
        ztwot := by
  obtain ⟨c₁, e₁, v₁, r₁⟩ := const_exec (P := P) hw 120100 0 by_omega
  have I₀ : DInv P W C V z c S c₁ := by
    refine ⟨e₁.wb_right, hq.congr fun r h1 h2 => r₁ r by_omega, ?_, by_omega, ?_, ?_⟩
    · zucku
      zuniv; exact hb
    · have hbo : ztguc := by
        zubqh
      rw [hbo, v₁]
      have : dstarPts c.nmem V C 0 = ∅ := by ext x; simp [dstarPts]
      simp_all
    · exact FrameB.mono (exec_frameB e₁ (B := fun r => decide (r = 120100)) by_decide)
        fun r hr => by
          zucy
          simp only [BD, Bool.or_eq_true, decide_eq_true_eq]; omega
  obtain ⟨c₂, k₂, e₂, I₂, hex, hk₂⟩ := Exec.whileLtN_potential (a := 120100) (b := 120035)
    (DInv P W C V z c S) (fun d => dstarCostFrom c.nmem V (d.nreg 120100)) ztpf
    (fun d hd ht => dstarBody_inv (P := P) hG hW hs hm hDL hd ht) I₀
  have hi2 : c₂.nreg 120100 = V.nD := by
    have := I₂.i_le; rw [I₂.q.nD] at hex; omega
  refine ⟨c₂, _, .seq e₁ e₂, ?_, I₂.fr, I₂.b, by rw [← hi2]; exact I₂.hit⟩
  rw [v₁] at hk₂
  unfold dstarCost; omega
