module

public import Chazelle.Core.ShootCutCore

/-!
# WP-G, part 15: the upward dyadic sweep on the RAM

`dyUp emit` hands the blocks of a dyadic cover of `[q₀, q₀ + L)` to `emit`, as pieces of the walk
from the vertex `c₀` (`dyUp_exec`): at most `2 (log₂ L + 1)` pieces, chained from `c₀` to
`c₀ + L`, each valid by the hypothesis `hblk` on blocks.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc

@[expose] public section

/-- **A block piece** in the registers. -/
theorem pcBlock_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (x dir : ℕ)
    (hx : x < 150050 ∨ 150059 ≤ x) (hdir : dir ≤ W)
    (h90 : c.nreg 150090 = 0)
    (hwW : c.nreg 150085 + c.nreg 150084 ≤ W)
    (hent : 0 < c.nreg 150082 → c.nreg 150034 + c.nreg 150082 ≤ W ∧
      c.nmem (c.nreg 150034 + c.nreg 150082) + 3 * c.nreg 150077 ≤ W) :
    ∃ c' k, Exec P W (pcBlock x dir) c c' k ∧ k ≤ 15 ∧
      c'.nreg 150050 = c.nreg 150085 ∧ c'.nreg 150051 = 0 ∧
      c'.nreg 150052 = c.nreg 150085 + c.nreg 150084 ∧ c'.nreg 150053 = 0 ∧
      c'.nreg 150054 = (if 0 < c.nreg 150082 then 1 else 0) ∧
      (0 < c.nreg 150082 → c'.nreg 150055 =
        c.nmem (c.nreg 150034 + c.nreg 150082) + 3 * c.nreg 150077) ∧
      c'.nreg 150056 = c.nreg x ∧ c'.nreg 150057 = dir ∧ c'.nreg 150058 = c.nreg 150084 ∧
      (∀ r, (r < 150050 ∨ 150059 ≤ r) → r ≠ 150075 → r ≠ 150076 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem := by
  obtain ⟨c₁, k₁, e₁, hk₁, v50, v51, v52, v53, v56, v57, v58, r₁, m₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 150050 150085, .constN 150051 0, .addN 150052 150085 150084,
        .constN 150053 0, .copyN 150056 x, .constN 150057 dir, .copyN 150058 150084]) c c₁ k₁ ∧
      k₁ = 7 ∧ c₁.nreg 150050 = c.nreg 150085 ∧ c₁.nreg 150051 = 0 ∧
      c₁.nreg 150052 = c.nreg 150085 + c.nreg 150084 ∧ c₁.nreg 150053 = 0 ∧
      c₁.nreg 150056 = c.nreg x ∧ c₁.nreg 150057 = dir ∧ c₁.nreg 150058 = c.nreg 150084 ∧
      (∀ r, (r < 150050 ∨ 150059 ≤ r) → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    exec_block
    all_goals first | (config_simp; omega) | exact hdir | skip
    · refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, ?_, by config_simp,
        by config_simp, fun r hr => ?_, rfl⟩
      · config_simp
        rcases hx with hx | hx
        · simp [upd, show x ≠ 150050 by omega, show x ≠ 150051 by omega, show x ≠ 150052 by omega,
            show x ≠ 150053 by omega]
        · simp [upd, show x ≠ 150050 by omega, show x ≠ 150051 by omega, show x ≠ 150052 by omega,
            show x ≠ 150053 by omega]
      · simp only [upd]; split_ifs <;> first | rfl | omega
  have w₁ := e₁.wb_right
  have a90 : c₁.nreg 150090 = 0 := by rw [r₁ _ (by omega), h90]
  have a82 : c₁.nreg 150082 = c.nreg 150082 := r₁ _ (by omega)
  have a34 : c₁.nreg 150034 = c.nreg 150034 := r₁ _ (by omega)
  have a77 : c₁.nreg 150077 = c.nreg 150077 := r₁ _ (by omega)
  by_cases hg : 0 < c.nreg 150082
  · obtain ⟨hA1, hA2⟩ := hent hg
    obtain ⟨c₂, k₂, e₂, hk₂, v54, v55, r₂, m₂⟩ : ∃ c₂ k₂, Exec P W (block [.constN 150054 1,
        .addN 150075 150034 150082, .loadN 150076 150075, .addN 150055 150076 150077,
        .addN 150055 150055 150077, .addN 150055 150055 150077]) c₁ c₂ k₂ ∧ k₂ = 6 ∧
        c₂.nreg 150054 = 1 ∧
        c₂.nreg 150055 = c.nmem (c.nreg 150034 + c.nreg 150082) + 3 * c.nreg 150077 ∧
        (∀ r, r ≠ 150054 → r ≠ 150055 → r ≠ 150075 → r ≠ 150076 → c₂.nreg r = c₁.nreg r) ∧
        c₂.nmem = c₁.nmem := by
      exec_block
      all_goals first | (config_simp; omega) | (config_simp; rw [a34, a82, m₁, a77]; omega) | skip
      · refine ⟨rfl, by config_simp, ?_, fun r h1 h2 h3 h4 => ?_, rfl⟩
        · config_simp; rw [a34, a82, m₁, a77]; ring
        · simp only [upd]; split_ifs <;> first | rfl | omega
    refine ⟨c₂, k₁ + (k₂ + 1), .seq e₁ (.ifLtN_true (by rwa [a90, a82]) e₂), by omega,
      ?_, ?_, ?_, ?_, ?_, fun _ => v55, ?_, ?_, ?_, fun r hr h1 h2 => ?_, by rw [m₂, m₁]⟩
    · rw [r₂ _ (by omega) (by omega) (by omega) (by omega), v50]
    · rw [r₂ _ (by omega) (by omega) (by omega) (by omega), v51]
    · rw [r₂ _ (by omega) (by omega) (by omega) (by omega), v52]
    · rw [r₂ _ (by omega) (by omega) (by omega) (by omega), v53]
    · rw [v54, ite_eq_left hg]
    · rw [r₂ _ (by omega) (by omega) (by omega) (by omega), v56]
    · rw [r₂ _ (by omega) (by omega) (by omega) (by omega), v57]
    · rw [r₂ _ (by omega) (by omega) (by omega) (by omega), v58]
    · rw [r₂ _ (by omega) (by omega) h1 h2, r₁ r hr]
  · refine ⟨_, k₁ + (1 + 2), .seq e₁ (.ifLtN_false (by rwa [a90, a82])
      (Exec.constN w₁ 150054 0 (by omega))), by omega, ?_, ?_, ?_, ?_, ?_, fun h => absurd h hg,
      ?_, ?_, ?_, fun r hr h1 h2 => ?_, by config_simp; exact m₁⟩
    all_goals config_simp
    · exact v50
    · exact v51
    · exact v52
    · exact v53
    · rw [ite_eq_right hg]
    · exact v56
    · exact v57
    · exact v58
    · rw [upd_other _ _ _ (by omega)]; exact r₁ r hr

/-! ## The static context of a sweep -/

/-- The tables and bounds a sweep reads: the halving table at `Hb`, the powers of two at `Pb`
(up to `2^(tg + 1)`), all below `A₀ ≤ W`; the registers `34 … 36`, `90`, `91`. -/
structure SwEnv (n W A₀ Tb Hb Pb tg : ℕ) (m₀ : ℕ → ℕ) : Prop where
  half : ∀ x, x ≤ n → m₀ (Hb + x) = x / 2 ∧ Hb + x < A₀
  pow : ∀ j, j ≤ tg + 1 → m₀ (Pb + j) = 2 ^ j ∧ Pb + j < A₀
  aW : A₀ ≤ W

/-- The registers of the sweep that stay fixed. -/
def SwRegs (Tb Hb Pb : ℕ) (m₀ : ℕ → ℕ) (A₀ : ℕ) (c₀c : Config) (d : Config) : Prop :=
  (∀ a, a < A₀ → d.nmem a = m₀ a) ∧ (∀ r, 150000 ≤ r → r < 150044 → d.nreg r = c₀c.nreg r) ∧
    d.nreg 150090 = 0 ∧ d.nreg 150091 = 1 ∧ d.nreg 150034 = Tb ∧ d.nreg 150035 = Hb ∧
    d.nreg 150036 = Pb

/-- The piece of the block `(g, b)` of an upward sweep from `q₀` at the walk vertex `c₀`. -/
def upPc (c₀ q₀ g b e : ℕ) : Pc :=
  ⟨⟨c₀ + (b * 2 ^ g - q₀), 0⟩, ⟨c₀ + (b * 2 ^ g - q₀) + 2 ^ g, 0⟩, if 0 < g then 1 else 0, e,
    b * 2 ^ g, 1, 2 ^ g⟩

/-- The validity of the blocks, as the sweep needs it. -/
def UpBlocks (Pv : Pc → Prop) (m₀ : ℕ → ℕ) (W A₀ Tb c₀ q₀ L : ℕ) : Prop :=
  ∀ g b, q₀ ≤ b * 2 ^ g → (b + 1) * 2 ^ g ≤ q₀ + L →
    (0 < g → Tb + g < A₀ ∧ m₀ (Tb + g) + 3 * b ≤ W) ∧
      ∀ e, (0 < g → e = m₀ (Tb + g) + 3 * b) → Pv (upPc c₀ q₀ g b e)

/-- The invariant of the ascending sweep. -/
def UpA (W : ℕ) (Pv : Pc → Prop) (I : List Pc → Config → Prop) (ps₀ : List Pc)
    (m₀ : ℕ → ℕ) (A₀ Tb Hb Pb tg q₀ L c₀ : ℕ) (cc d : Config) : Prop :=
  WordsBounded W d ∧ SwRegs Tb Hb Pb m₀ A₀ cc d ∧
    ∃ x g ps', d.nreg 150080 = x ∧ d.nreg 150081 = q₀ + L ∧ d.nreg 150082 = g ∧
      x = d.nreg 150083 * 2 ^ g ∧ d.nreg 150084 = 2 ^ g ∧ d.nreg 150085 = c₀ + (x - q₀) ∧
      d.nreg 150087 = x + 2 ^ g ∧ d.nreg 150088 = q₀ + L + 1 ∧ q₀ ≤ x ∧ x ≤ q₀ + L ∧
      I (ps₀ ++ ps') d ∧ Chained ⟨c₀, 0⟩ ps' ⟨c₀ + (x - q₀), 0⟩ ∧ (∀ pc ∈ ps', Pv pc) ∧
      ps'.length ≤ g ∧ (g = 0 ∨ 2 ^ (g - 1) ≤ L) ∧ g ≤ tg + 1

theorem pow_le_of_le {g L tg : ℕ} (h : 2 ^ g ≤ L) (hL : L ≤ 2 ^ tg) : g ≤ tg :=
  (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (h.trans hL)

/-- The end of a step of the ascending sweep: double the block size. -/
theorem upATail_exec {P : Polygon} {W A₀ Pb g x : ℕ} {m₀ : ℕ → ℕ} (d : Config)
    (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a) (h36 : d.nreg 150036 = Pb)
    (h82 : d.nreg 150082 = g) (h80 : d.nreg 150080 = x) (h91 : d.nreg 150091 = 1)
    (hpow : m₀ (Pb + (g + 1)) = 2 ^ (g + 1) ∧ Pb + (g + 1) < A₀) (hA : A₀ ≤ W)
    (hxW : x + 2 ^ (g + 1) ≤ W) :
    ∃ d' k, Exec P W (block [.addN 150082 150082 150091, .addN 150075 150036 150082,
        .loadN 150084 150075, .copyN 150083 150086, .addN 150087 150080 150084]) d d' k ∧
      k = 5 ∧ d'.nreg 150082 = g + 1 ∧ d'.nreg 150084 = 2 ^ (g + 1) ∧
      d'.nreg 150083 = d.nreg 150086 ∧ d'.nreg 150087 = x + 2 ^ (g + 1) ∧
      (∀ r, r ≠ 150075 → r ≠ 150082 → r ≠ 150083 → r ≠ 150084 → r ≠ 150087 →
        d'.nreg r = d.nreg r) ∧ d'.nmem = d.nmem := by
  exec_block
  all_goals first | (config_simp; rw [h82, h91]; omega) | (config_simp; rw [h82, h91, h36]; omega) |
    (config_simp; rw [h82, h91, h80, h36, hm _ hpow.2, hpow.1]; omega) | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, rfl⟩
  · config_simp; rw [h82, h91]
  · config_simp; rw [h82, h91, h36, hm _ hpow.2, hpow.1]
  · config_simp
  · config_simp; rw [h82, h91, h80, h36, hm _ hpow.2, hpow.1]
  · simp only [upd]; split_ifs <;> first | rfl | omega


/-- Building the invariant of the ascending sweep. -/
theorem mkUpA {W : ℕ} {Pv : Pc → Prop} {I : List Pc → Config → Prop} {ps₀ : List Pc}
    {m₀ : ℕ → ℕ} {A₀ Tb Hb Pb tg q₀ L c₀ : ℕ} {cc d : Config} (x g : ℕ) (ps' : List Pc)
    (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (hk : ∀ r, 150000 ≤ r → r < 150044 → d.nreg r = cc.nreg r) (h90 : d.nreg 150090 = 0)
    (h91 : d.nreg 150091 = 1) (h34 : d.nreg 150034 = Tb) (h35 : d.nreg 150035 = Hb)
    (h36 : d.nreg 150036 = Pb) (h80 : d.nreg 150080 = x) (h81 : d.nreg 150081 = q₀ + L)
    (h82 : d.nreg 150082 = g) (hx : x = d.nreg 150083 * 2 ^ g) (h84 : d.nreg 150084 = 2 ^ g)
    (h85 : d.nreg 150085 = c₀ + (x - q₀)) (h87 : d.nreg 150087 = x + 2 ^ g)
    (h88 : d.nreg 150088 = q₀ + L + 1) (hqx : q₀ ≤ x) (hxy : x ≤ q₀ + L)
    (hI : I (ps₀ ++ ps') d) (hch : Chained ⟨c₀, 0⟩ ps' ⟨c₀ + (x - q₀), 0⟩)
    (hv : ∀ pc ∈ ps', Pv pc) (hlen : ps'.length ≤ g) (hg : g = 0 ∨ 2 ^ (g - 1) ≤ L)
    (hgt : g ≤ tg + 1) : UpA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d :=
  ⟨hw, ⟨hm, hk, h90, h91, h34, h35, h36⟩, x, g, ps', h80, h81, h82, hx, h84, h85, h87, h88, hqx,
    hxy, hI, hch, hv, hlen, hg, hgt⟩

/-- The tail block of a step of the ascending sweep. -/
def upATail : Stmt := block [.addN 150082 150082 150091, .addN 150075 150036 150082,
  .loadN 150084 150075, .copyN 150083 150086, .addN 150087 150080 150084]

/-- The odd branch of a step of the ascending sweep. -/
def upAOdd (emit : Stmt) : Stmt :=
  .seq (.instr (.copyN 150077 150083))
    (.seq (pcBlock 150080 1)
      (.seq emit (block [.addN 150080 150080 150084, .addN 150085 150085 150084,
        .addN 150086 150086 150091])))

theorem upABody_eq (emit : Stmt) : upABody emit =
    .seq (block [.addN 150075 150035 150083, .loadN 150086 150075, .addN 150075 150086 150086])
      (.seq (.ifLtN 150075 150083 (upAOdd emit) .skip) upATail) := rfl

/-- **After the optional block**: the tail re-establishes the invariant with `g + 1`. -/
theorem upA_after {P : Polygon} {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop}
    {I : List Pc → Config → Prop} (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb Hb Pb tg q₀ L c₀ : ℕ} {ps₀ : List Pc} {cc : Config}
    (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 2 * P.n + 4 ≤ W)
    (hqL : q₀ + L ≤ P.n) (d₅ : Config) (w₅ : WordsBounded W d₅) (x' h' g : ℕ) (ps'' : List Pc)
    (hgt : g ≤ tg) (hgL : 2 ^ g ≤ L)
    (m₅ : ∀ a, a < A₀ → d₅.nmem a = m₀ a) (s₅ : ∀ r, 150000 ≤ r → r < 150044 → d₅.nreg r = cc.nreg r)
    (a90 : d₅.nreg 150090 = 0) (a91 : d₅.nreg 150091 = 1) (a34 : d₅.nreg 150034 = Tb)
    (a35 : d₅.nreg 150035 = Hb) (a36 : d₅.nreg 150036 = Pb) (a82 : d₅.nreg 150082 = g)
    (a80 : d₅.nreg 150080 = x') (a81 : d₅.nreg 150081 = q₀ + L)
    (a85 : d₅.nreg 150085 = c₀ + (x' - q₀)) (a88 : d₅.nreg 150088 = q₀ + L + 1)
    (hx' : x' = h' * 2 ^ (g + 1)) (a86 : d₅.nreg 150086 = h') (hq' : q₀ ≤ x') (hx'L : x' ≤ q₀ + L)
    (hI₅ : I (ps₀ ++ ps'') d₅) (hch₅ : Chained ⟨c₀, 0⟩ ps'' ⟨c₀ + (x' - q₀), 0⟩)
    (hv₅ : ∀ pc ∈ ps'', Pv pc) (hl₅ : ps''.length ≤ g + 1) :
    ∃ d₆ k₆, Exec P W upATail d₅ d₆ k₆ ∧ k₆ = 5 ∧
      UpA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d₆ ∧ d₆.nreg 150082 = g + 1 := by
  obtain ⟨hp1, hp2⟩ := env.pow (g + 1) (by omega)
  obtain ⟨d₆, k₆, e₆, hk₆, b82, b84, b83, b87, r₆, m₆⟩ := upATail_exec (P := P) (x := x') d₅ w₅
    m₅ a36 a82 a80 a91 ⟨hp1, hp2⟩ env.aW (by rw [pow_succ]; omega)
  have fr₆ : FrameB Scr d₅ d₆ := exec_frameB e₆ (by decide)
  have k : ∀ r, r ≠ 150075 → r ≠ 150082 → r ≠ 150083 → r ≠ 150084 → r ≠ 150087 →
      d₆.nreg r = d₅.nreg r := r₆
  refine ⟨d₆, k₆, e₆, hk₆, mkUpA x' (g + 1) ps'' e₆.wb_right
    (fun a ha => by rw [m₆]; exact m₅ a ha)
    (fun r h1 h2 => (k r (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (s₅ r h1 h2))
    (by rwa [k _ (by omega) (by omega) (by omega) (by omega) (by omega)])
    (by rwa [k _ (by omega) (by omega) (by omega) (by omega) (by omega)])
    (by rwa [k _ (by omega) (by omega) (by omega) (by omega) (by omega)])
    (by rwa [k _ (by omega) (by omega) (by omega) (by omega) (by omega)])
    (by rwa [k _ (by omega) (by omega) (by omega) (by omega) (by omega)])
    (by rwa [k _ (by omega) (by omega) (by omega) (by omega) (by omega)])
    (by rwa [k _ (by omega) (by omega) (by omega) (by omega) (by omega)])
    b82 (by rwa [b83, a86]) b84
    (by rwa [k _ (by omega) (by omega) (by omega) (by omega) (by omega)]) b87
    (by rwa [k _ (by omega) (by omega) (by omega) (by omega) (by omega)]) hq' hx'L
    (hE.stable _ _ _ hI₅ fr₆) hch₅ hv₅ hl₅ (Or.inr (by simpa using hgL)) (by omega), b82⟩

/-- **The odd branch**: the block `(g, qq)` is handed to `emit`. -/
theorem upA_odd {P : Polygon} {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop}
    {I : List Pc → Config → Prop} (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb q₀ L c₀ : ℕ} {ps : List Pc} (hblk : UpBlocks Pv m₀ W A₀ Tb c₀ q₀ L)
    (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 4 ≤ W) (hA : A₀ ≤ W) (hqW : q₀ + L ≤ W) {x g qq : ℕ}
    (d₁ : Config) (w₁ : WordsBounded W d₁) (hm : ∀ a, a < A₀ → d₁.nmem a = m₀ a)
    (h90 : d₁.nreg 150090 = 0) (h91 : d₁.nreg 150091 = 1) (h34 : d₁.nreg 150034 = Tb)
    (h80 : d₁.nreg 150080 = x) (h82 : d₁.nreg 150082 = g) (h83 : d₁.nreg 150083 = qq)
    (h84 : d₁.nreg 150084 = 2 ^ g) (h85 : d₁.nreg 150085 = c₀ + (x - q₀))
    (hx : x = qq * 2 ^ g) (hqx : q₀ ≤ x) (hxy : x + 2 ^ g ≤ q₀ + L) (hI : I ps d₁)
    (h86 : d₁.nreg 150086 + 1 ≤ W) :
    ∃ d₅ k₅ e, Exec P W (upAOdd emit) d₁ d₅ k₅ ∧ k₅ ≤ K + 20 ∧ Pv (upPc c₀ q₀ g qq e) ∧
      I (ps ++ [upPc c₀ q₀ g qq e]) d₅ ∧ d₅.nreg 150080 = x + 2 ^ g ∧
      d₅.nreg 150085 = c₀ + (x - q₀) + 2 ^ g ∧ d₅.nreg 150086 = d₁.nreg 150086 + 1 ∧
      (∀ r, ((150000 ≤ r ∧ r < 150044) ∨ r = 150081 ∨ r = 150082 ∨ r = 150088 ∨
        r = 150090 ∨ r = 150091 ∨ r = 150083) → d₅.nreg r = d₁.nreg r) ∧
      (∀ a, a < A₀ → d₅.nmem a = d₁.nmem a) := by
  obtain ⟨hblk1, hblk2⟩ := hblk g qq (by rwa [← hx]) (by
    rwa [Nat.add_mul, one_mul, ← hx])
  have ex₂ := Exec.copyN (P := P) w₁ 150077 150083
  set d₂ := ({ d₁ with nreg := upd d₁.nreg 150077 (d₁.nreg 150083) } : Config) with hd₂
  have w₂ := ex₂.wb_right
  have g2 : ∀ r, r ≠ 150077 → d₂.nreg r = d₁.nreg r := fun r hr => by simp [hd₂, upd, hr]
  have n77 : d₂.nreg 150077 = qq := by simp [hd₂, h83]
  have nm : d₂.nmem = d₁.nmem := rfl
  obtain ⟨d₃, k₃, e₃, hk₃, v50, v51, v52, v53, v54, v55, v56, v57, v58, r₃, m₃⟩ :=
    pcBlock_exec (P := P) d₂ w₂ 150080 1 (Or.inr (by omega)) (by omega)
      (by rw [g2 _ (by omega), h90])
      (by rw [g2 _ (by omega), g2 _ (by omega), h85, h84]; omega) (fun hg => by
        have hg' : 0 < g := by rwa [g2 _ (by omega), h82] at hg
        rw [g2 _ (by omega), g2 _ (by omega), n77, nm, h34, h82, hm _ (hblk1 hg').1]
        exact ⟨by have := (hblk1 hg').1; omega, (hblk1 hg').2⟩)
  rw [g2 _ (by omega)] at v50 v52 v54 v56 v58 v55
  rw [g2 _ (by omega)] at v52
  set pc := upPc c₀ q₀ g qq (d₃.nreg 150055) with hpc
  have hpcR : PcRegs d₃ pc := by
    refine ⟨?_, v51, ?_, v53, ?_, fun _ => ⟨rfl, ?_, v57, ?_⟩⟩
    · rw [v50, h85, hpc]; simp [upPc, ← hx]
    · rw [v52, h85, h84, hpc]; simp [upPc, ← hx]
    · rw [v54, h82, hpc]; rfl
    · rw [v56, h80, hpc]; simp [upPc, ← hx]
    · rw [v58, h84]; rfl
  have hpv : Pv pc := hblk2 _ (fun hg => by
    rw [v55 (by rwa [h82]), g2 _ (by omega), n77, h82, h34, hm _ (hblk1 hg).1])
  have fr₃ : FrameB Scr d₁ d₃ := (exec_frameB ex₂ (by decide)).trans (exec_frameB e₃ (by decide))
  obtain ⟨d₄, k₄, e₄, hk₄, hI₄, kp, mem₄⟩ := hE.run _ pc d₃ e₃.wb_right (hE.stable _ _ _ hI fr₃) hpcR hpv
  have w₄ := e₄.wb_right
  have back : ∀ r, Keep r → r ≠ 150077 → (r < 150050 ∨ 150059 ≤ r) → r ≠ 150075 → r ≠ 150076 →
      d₄.nreg r = d₁.nreg r := fun r hk h1 h2 h3 h4 => by
    rw [kp r hk, r₃ r h2 h3 h4, g2 r h1]
  have q80 : d₄.nreg 150080 = x := by rw [back _ (Or.inr (by omega)) (by omega) (by omega)
    (by omega) (by omega), h80]
  have q84 : d₄.nreg 150084 = 2 ^ g := by rw [back _ (Or.inr (by omega)) (by omega) (by omega)
    (by omega) (by omega), h84]
  have q85 : d₄.nreg 150085 = c₀ + (x - q₀) := by rw [back _ (Or.inr (by omega)) (by omega)
    (by omega) (by omega) (by omega), h85]
  have q91 : d₄.nreg 150091 = 1 := by rw [back _ (Or.inr (by omega)) (by omega) (by omega)
    (by omega) (by omega), h91]
  have q86 : d₄.nreg 150086 = d₁.nreg 150086 := by
    rw [back _ (Or.inr (by omega)) (by omega) (by omega) (by omega) (by omega)]
  obtain ⟨d₅, k₅, e₅, hk₅, a80, a85, a86, r₅, m₅⟩ : ∃ d₅ k₅, Exec P W
      (block [.addN 150080 150080 150084, .addN 150085 150085 150084,
        .addN 150086 150086 150091]) d₄ d₅ k₅ ∧ k₅ = 3 ∧ d₅.nreg 150080 = x + 2 ^ g ∧
      d₅.nreg 150085 = c₀ + (x - q₀) + 2 ^ g ∧ d₅.nreg 150086 = d₄.nreg 150086 + 1 ∧
      (∀ r, r ≠ 150080 → r ≠ 150085 → r ≠ 150086 → d₅.nreg r = d₄.nreg r) ∧
      d₅.nmem = d₄.nmem := by
    exec_block
    all_goals first | (config_simp; rw [q80, q84]; omega) | (config_simp; rw [q85, q84]; omega) |
      (config_simp; rw [q86, q91]; omega) | skip
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl⟩
    · config_simp; rw [q80, q84]
    · config_simp; rw [q85, q84]
    · config_simp; rw [q91]
    · simp only [upd]; split_ifs <;> first | rfl | omega
  refine ⟨d₅, 1 + (k₃ + (k₄ + k₅)), d₃.nreg 150055, .seq ex₂ (.seq e₃ (.seq e₄ e₅)), by omega,
    hpv, hE.stable _ _ _ hI₄ (exec_frameB e₅ (by decide)), a80, a85, by rw [a86, q86], ?_, ?_⟩
  · intro r hr
    rw [r₅ r (by omega) (by omega) (by omega), back r (by unfold Keep; omega) (by omega) (by omega)
      (by omega) (by omega)]
  · intro a ha
    rw [m₅, mem₄ a ha, m₃]

/-- **One step of the ascending sweep.** -/
theorem upABody_exec {P : Polygon} {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop}
    {I : List Pc → Config → Prop} (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb Hb Pb tg q₀ L c₀ : ℕ} {ps₀ : List Pc} {cc d : Config}
    (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) (hblk : UpBlocks Pv m₀ W A₀ Tb c₀ q₀ L)
    (hqL : q₀ + L ≤ P.n) (hLtg : L ≤ 2 ^ tg) (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 2 * P.n + 4 ≤ W)
    (hI : UpA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d)
    (ht : d.nreg 150087 < d.nreg 150088) :
    ∃ d' k, Exec P W (upABody emit) d d' k ∧ UpA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d' ∧
      k ≤ K + 40 ∧ Nat.log 2 L + 1 - d'.nreg 150082 < Nat.log 2 L + 1 - d.nreg 150082 := by
  obtain ⟨hw, ⟨hm, hk0, h90, h91, h34, h35, h36⟩, x, g, ps', h80, h81, h82, hx, h84, h85, h87,
    h88, hqx, hxy, hI', hch, hv, hlen, hg1, hgtg⟩ := hI
  rw [h87, h88] at ht
  have hp := Nat.two_pow_pos g
  have hgL : 2 ^ g ≤ L := by omega
  have hgt : g ≤ tg := pow_le_of_le hgL hLtg
  have hgl : g ≤ Nat.log 2 L := Nat.le_log_of_pow_le (by norm_num) hgL
  have hqqx : d.nreg 150083 ≤ x := by rw [hx]; exact Nat.le_mul_of_pos_right _ hp
  have hA := env.aW
  obtain ⟨hh1, hh2⟩ := env.half (d.nreg 150083) (by omega)
  -- the half of `qq`
  obtain ⟨d₁, k₁, e₁, hk₁, o75, o86, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W (block [.addN 150075 150035 150083,
      .loadN 150086 150075, .addN 150075 150086 150086]) d d₁ k₁ ∧ k₁ = 3 ∧
      d₁.nreg 150075 = d.nreg 150083 / 2 + d.nreg 150083 / 2 ∧
      d₁.nreg 150086 = d.nreg 150083 / 2 ∧
      (∀ r, r ≠ 150075 → r ≠ 150086 → d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem := by
    exec_block
    all_goals first | (config_simp; rw [h35, hm _ (by omega), hh1]; omega) |
      (config_simp; rw [h35]; omega) | skip
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl⟩
    · config_simp; rw [h35, hm _ (by omega), hh1]
    · config_simp; rw [h35, hm _ (by omega), hh1]
    · simp only [upd]; split_ifs <;> first | rfl | omega
  have w₁ := e₁.wb_right
  have fr₁ : FrameB Scr d d₁ := exec_frameB e₁ (by decide)
  have k₁' : ∀ r, r ≠ 150075 → r ≠ 150086 → d₁.nreg r = d.nreg r := r₁
  have m₁' : ∀ a, a < A₀ → d₁.nmem a = m₀ a := fun a ha => by rw [m₁]; exact hm a ha
  rw [upABody_eq]
  by_cases hodd : d.nreg 150083 / 2 + d.nreg 150083 / 2 < d.nreg 150083
  · obtain ⟨d₅, k₅, e, e₅, hk₅, hpv, hI₅, a80, a85, a86, r₅, m₅⟩ := upA_odd hE (ps := ps₀ ++ ps')
      hblk (by omega) (by omega) hA (by omega) (x := x) (g := g) (qq := d.nreg 150083) d₁ w₁ m₁'
      (by rw [k₁' _ (by omega) (by omega), h90]) (by rw [k₁' _ (by omega) (by omega), h91])
      (by rw [k₁' _ (by omega) (by omega), h34]) (by rw [k₁' _ (by omega) (by omega), h80])
      (by rw [k₁' _ (by omega) (by omega), h82]) (by rw [k₁' _ (by omega) (by omega)])
      (by rw [k₁' _ (by omega) (by omega), h84]) (by rw [k₁' _ (by omega) (by omega), h85])
      hx hqx (by omega) (hE.stable _ _ _ hI' fr₁) (by rw [o86]; omega)
    have kk : ∀ r, ((150000 ≤ r ∧ r < 150044) ∨ r = 150081 ∨ r = 150082 ∨ r = 150088 ∨
        r = 150090 ∨ r = 150091) → d₅.nreg r = d.nreg r := fun r hr => by
      rw [r₅ r (by omega), k₁' r (by omega) (by omega)]
    have w₅ := e₅.wb_right
    obtain ⟨d₆, k₆, e₆, hk₆, hU, b82⟩ := upA_after hE env hW hW' hqL d₅ w₅ (x + 2 ^ g)
      (d.nreg 150083 / 2 + 1) g (ps' ++ [upPc c₀ q₀ g (d.nreg 150083) e]) hgt hgL
      (fun a ha => by rw [m₅ a ha]; exact m₁' a ha)
      (fun r h1 h2 => (kk r (Or.inl ⟨h1, h2⟩)).trans (hk0 r h1 h2))
      (by rwa [kk _ (by omega)]) (by rwa [kk _ (by omega)])
      (by rwa [kk _ (by omega)]) (by rwa [kk _ (by omega)])
      (by rwa [kk _ (by omega)]) (by rw [kk _ (by omega)]; exact h82) a80
      (by rw [kk _ (by omega)]; exact h81) (by rw [a85]; omega)
      (by rw [kk _ (by omega)]; exact h88)
      (by rw [hx, pow_succ]; have : d.nreg 150083 = 2 * (d.nreg 150083 / 2) + 1 := by omega
          nth_rewrite 1 [this]; ring)
      (by rw [a86, o86]) (by omega) (by omega) (by rwa [← List.append_assoc])
      (by
        have h2 := hch.append (upPc c₀ q₀ g (d.nreg 150083) e) (by simp [upPc, ← hx])
        have he : (upPc c₀ q₀ g (d.nreg 150083) e).e = ⟨c₀ + (x + 2 ^ g - q₀), 0⟩ := by
          simp only [upPc, ← hx, WPos.mk.injEq, and_true]; omega
        rwa [he] at h2)
      (fun p hp => by
        rcases List.mem_append.1 hp with hp | hp
        · exact hv p hp
        · simp only [List.mem_singleton] at hp; rwa [hp])
      (by simp; omega)
    exact ⟨d₆, k₁ + ((k₅ + 1) + k₆), .seq e₁ (.seq (.ifLtN_true (by
        rwa [o75, k₁' _ (by omega) (by omega)]) e₅) e₆), hU, by omega,
      by rw [b82, h82]; omega⟩
  · obtain ⟨d₆, k₆, e₆, hk₆, hU, b82⟩ := upA_after hE env hW hW' hqL d₁ w₁ x
      (d.nreg 150083 / 2) g ps' hgt hgL m₁'
      (fun r h1 h2 => (k₁' r (by omega) (by omega)).trans (hk0 r h1 h2))
      (by rwa [k₁' _ (by omega) (by omega)]) (by rwa [k₁' _ (by omega) (by omega)])
      (by rwa [k₁' _ (by omega) (by omega)]) (by rwa [k₁' _ (by omega) (by omega)])
      (by rwa [k₁' _ (by omega) (by omega)]) (by rw [k₁' _ (by omega) (by omega)]; exact h82)
      (by rw [k₁' _ (by omega) (by omega)]; exact h80) (by rw [k₁' _ (by omega) (by omega)]; exact h81)
      (by rw [k₁' _ (by omega) (by omega)]; exact h85) (by rw [k₁' _ (by omega) (by omega)]; exact h88)
      (by rw [hx, pow_succ]; have : d.nreg 150083 = 2 * (d.nreg 150083 / 2) := by omega
          nth_rewrite 1 [this]; ring)
      o86 hqx hxy (hE.stable _ _ _ hI' fr₁) hch hv (by omega)
    exact ⟨d₆, k₁ + ((0 + 2) + k₆), .seq e₁ (.seq (.ifLtN_false (by
        rwa [o75, k₁' _ (by omega) (by omega)]) (.skip w₁)) e₆), hU, by omega,
      by rw [b82, h82]; omega⟩

/-! ## The descending sweep of the upward cover -/

/-- The invariant of the descending sweep. -/
def UpB (W : ℕ) (Pv : Pc → Prop) (I : List Pc → Config → Prop) (ps₀ : List Pc)
    (m₀ : ℕ → ℕ) (A₀ Tb Hb Pb tg q₀ L c₀ : ℕ) (cc d : Config) : Prop :=
  WordsBounded W d ∧ SwRegs Tb Hb Pb m₀ A₀ cc d ∧
    ∃ x g ps', d.nreg 150080 = x ∧ d.nreg 150081 = q₀ + L ∧ d.nreg 150082 = g ∧
      x = d.nreg 150083 * 2 ^ g ∧ d.nreg 150085 = c₀ + (x - q₀) ∧
      d.nreg 150088 = q₀ + L + 1 ∧ q₀ ≤ x ∧ x ≤ q₀ + L ∧ q₀ + L < x + 2 ^ g ∧
      I (ps₀ ++ ps') d ∧ Chained ⟨c₀, 0⟩ ps' ⟨c₀ + (x - q₀), 0⟩ ∧ (∀ pc ∈ ps', Pv pc) ∧
      ps'.length + g ≤ 2 * (Nat.log 2 L + 1) ∧ g ≤ tg + 1 ∧ 2 ^ g ≤ 2 * L + 1

theorem upBBody_eq (emit : Stmt) : upBBody emit =
    .seq (block [.subN 150082 150082 150091, .addN 150075 150036 150082, .loadN 150084 150075,
      .addN 150083 150083 150083, .copyN 150086 150083, .addN 150087 150080 150084])
    (.seq (.ifLtN 150087 150088 (upAOdd emit) .skip) (.instr (.copyN 150083 150086))) := rfl

/-- **One step of the descending sweep.** -/
theorem upBBody_exec {P : Polygon} {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop}
    {I : List Pc → Config → Prop} (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb Hb Pb tg q₀ L c₀ : ℕ} {ps₀ : List Pc} {cc d : Config}
    (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) (hblk : UpBlocks Pv m₀ W A₀ Tb c₀ q₀ L)
    (hqL : q₀ + L ≤ P.n) (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 2 * P.n + 4 ≤ W)
    (hI : UpB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d)
    (ht : d.nreg 150090 < d.nreg 150082) :
    ∃ d' k, Exec P W (upBBody emit) d d' k ∧ UpB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d' ∧
      k ≤ K + 40 ∧ d'.nreg 150082 < d.nreg 150082 := by
  obtain ⟨hw, ⟨hm, hk0, h90, h91, h34, h35, h36⟩, x, g, ps', h80, h81, h82, hx, h85,
    h88, hqx, hxy, hyx, hI', hch, hv, hlen, hgt, hgb⟩ := hI
  rw [h90, h82] at ht
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  have hp := Nat.two_pow_pos g'
  have hA := env.aW
  obtain ⟨hp1, hp2⟩ := env.pow g' (by omega)
  set qq := d.nreg 150083 with hqq
  have hx2 : x = (qq + qq) * 2 ^ g' := by rw [hx, pow_succ]; ring
  have hqqx : qq + qq ≤ x := by rw [hx2]; exact Nat.le_mul_of_pos_right _ hp
  have hxn : x ≤ P.n := by omega
  obtain ⟨d₁, k₁, e₁, hk₁, o82, o84, o83, o86, o87, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W
      (block [.subN 150082 150082 150091, .addN 150075 150036 150082, .loadN 150084 150075,
        .addN 150083 150083 150083, .copyN 150086 150083, .addN 150087 150080 150084])
      d d₁ k₁ ∧ k₁ = 6 ∧ d₁.nreg 150082 = g' ∧ d₁.nreg 150084 = 2 ^ g' ∧
      d₁.nreg 150083 = qq + qq ∧ d₁.nreg 150086 = qq + qq ∧ d₁.nreg 150087 = x + 2 ^ g' ∧
      (∀ r, r ≠ 150075 → r ≠ 150082 → r ≠ 150083 → r ≠ 150084 → r ≠ 150086 → r ≠ 150087 →
        d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem := by
    exec_block
    all_goals first | (config_simp; rw [h82, h91, Nat.add_sub_cancel, h36]; omega) |
      (config_simp; omega) |
      (config_simp; rw [h82, h91, Nat.add_sub_cancel, h36, h80, hm _ (by omega), hp1]; omega) | skip
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 => ?_, rfl⟩
    · config_simp; rw [h82, h91, Nat.add_sub_cancel]
    · config_simp; rw [h82, h91, Nat.add_sub_cancel, h36, hm _ (by omega), hp1]
    · config_simp; rw [← hqq]
    · config_simp; rw [← hqq]
    · config_simp; rw [h82, h91, Nat.add_sub_cancel, h36, h80, hm _ (by omega), hp1]
    · simp only [upd]; split_ifs <;> first | rfl | omega
  have w₁ := e₁.wb_right
  have fr₁ : FrameB Scr d d₁ := exec_frameB e₁ (by decide)
  have k : ∀ r, ((150000 ≤ r ∧ r < 150044) ∨ r = 150080 ∨ r = 150081 ∨ r = 150085 ∨ r = 150088 ∨
      r = 150090 ∨ r = 150091) → d₁.nreg r = d.nreg r := fun r hr =>
    r₁ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have m₁' : ∀ a, a < A₀ → d₁.nmem a = m₀ a := fun a ha => by rw [m₁]; exact hm a ha
  rw [upBBody_eq]
  -- the final copy
  have fin : ∀ (d₅ : Config) (k₅ x' : ℕ) (ps'' : List Pc),
      Exec P W (.ifLtN 150087 150088 (upAOdd emit) .skip) d₁ d₅ k₅ → k₅ ≤ K + 22 →
      (∀ a, a < A₀ → d₅.nmem a = m₀ a) →
      (∀ r, ((150000 ≤ r ∧ r < 150044) ∨ r = 150081 ∨ r = 150082 ∨ r = 150088 ∨ r = 150090 ∨
        r = 150091) → d₅.nreg r = d₁.nreg r) →
      d₅.nreg 150080 = x' → d₅.nreg 150085 = c₀ + (x' - q₀) → x' = d₅.nreg 150086 * 2 ^ g' →
      q₀ ≤ x' → x' ≤ q₀ + L → q₀ + L < x' + 2 ^ g' → I (ps₀ ++ ps'') d₅ →
      Chained ⟨c₀, 0⟩ ps'' ⟨c₀ + (x' - q₀), 0⟩ → (∀ pc ∈ ps'', Pv pc) →
      ps''.length ≤ ps'.length + 1 →
      ∃ d' k, Exec P W (.seq (block [.subN 150082 150082 150091, .addN 150075 150036 150082,
        .loadN 150084 150075, .addN 150083 150083 150083, .copyN 150086 150083,
        .addN 150087 150080 150084])
        (.seq (.ifLtN 150087 150088 (upAOdd emit) .skip) (.instr (.copyN 150083 150086))))
        d d' k ∧ UpB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d' ∧ k ≤ K + 40 ∧
        d'.nreg 150082 < g' + 1 := by
    intro d₅ k₅ x' ps'' e₅ hk₅ m₅ k₅' a80 a85 hx' hq' hx'L hy' hI₅ hch₅ hv₅ hl₅
    have w₅ := e₅.wb_right
    have e₆ := Exec.copyN (P := P) w₅ 150083 150086
    set d₆ := ({ d₅ with nreg := upd d₅.nreg 150083 (d₅.nreg 150086) } : Config) with hd₆
    have g6 : ∀ r, r ≠ 150083 → d₆.nreg r = d₅.nreg r := fun r hr => by simp [hd₆, upd, hr]
    have kk : ∀ r, ((150000 ≤ r ∧ r < 150044) ∨ r = 150081 ∨ r = 150088 ∨
        r = 150090 ∨ r = 150091) → d₆.nreg r = d.nreg r := fun r hr => by
      rw [g6 r (by omega), k₅' r (by omega), k r (by omega)]
    refine ⟨d₆, k₁ + (k₅ + 1), .seq e₁ (.seq e₅ e₆), ⟨e₆.wb_right,
      ⟨fun a ha => m₅ a ha, fun r h1 h2 => (kk r (Or.inl ⟨h1, h2⟩)).trans (hk0 r h1 h2),
        by rwa [kk _ (by omega)], by rwa [kk _ (by omega)],
        by rwa [kk _ (by omega)], by rwa [kk _ (by omega)],
        by rwa [kk _ (by omega)]⟩,
      x', g', ps'', by rwa [g6 _ (by omega)], by rw [kk _ (by omega)]; exact h81,
      by rwa [g6 _ (by omega), k₅' _ (by omega)],
      by simp [hd₆]; exact hx', by rwa [g6 _ (by omega)],
      by rw [kk _ (by omega)]; exact h88, hq', hx'L, hy',
      hE.stable _ _ _ hI₅ (exec_frameB e₆ (by decide)), hch₅, hv₅, by omega, by omega, by rw [pow_succ] at hgb; omega⟩,
      by omega, by rw [g6 _ (by omega), k₅' _ (by omega), o82]; omega⟩
  by_cases hodd : d₁.nreg 150087 < d₁.nreg 150088
  · rw [o87, k _ (by omega), h88] at hodd
    obtain ⟨d₅, k₅, e, e₅, hk₅, hpv, hI₅, a80, a85, a86, r₅, m₅⟩ := upA_odd hE
      (ps := ps₀ ++ ps') hblk (by omega) (by omega) hA (by omega) (x := x) (g := g') (qq := qq + qq) d₁ w₁ m₁'
      (by rw [k _ (by omega), h90]) (by rw [k _ (by omega), h91])
      (by rw [k _ (by omega), h34]) (by rw [k _ (by omega), h80]) o82 o83 o84
      (by rw [k _ (by omega), h85]) hx2 hqx (by omega) (hE.stable _ _ _ hI' fr₁)
      (by rw [o86]; omega)
    obtain ⟨d', k', ex, hU, hk', hg'⟩ := fin d₅ (k₅ + 1) (x + 2 ^ g')
      (ps' ++ [upPc c₀ q₀ g' (qq + qq) e])
      (.ifLtN_true (by rw [o87, k _ (by omega), h88]; omega) e₅) (by omega)
      (fun a ha => by rw [m₅ a ha]; exact m₁' a ha) (fun r hr => r₅ r (by omega)) a80
      (by rw [a85]; omega) (by rw [a86, o86, hx2]; ring) (by omega) (by omega)
      (by rw [pow_succ] at hyx; omega) (by rwa [← List.append_assoc])
      (by
        have h2 := hch.append (upPc c₀ q₀ g' (qq + qq) e) (by simp [upPc, ← hx2])
        have he : (upPc c₀ q₀ g' (qq + qq) e).e = ⟨c₀ + (x + 2 ^ g' - q₀), 0⟩ := by
          simp only [upPc, ← hx2, WPos.mk.injEq, and_true]; omega
        rwa [he] at h2)
      (fun p hp => by
        rcases List.mem_append.1 hp with hp | hp
        · exact hv p hp
        · simp only [List.mem_singleton] at hp; rwa [hp])
      (by simp)
    exact ⟨d', k', ex, hU, hk', by rwa [h82]⟩
  · have hodd' := hodd
    rw [o87, k _ (by omega), h88] at hodd'
    obtain ⟨d', k', ex, hU, hk', hg'⟩ := fin d₁ 2 x ps' (.ifLtN_false hodd (.skip w₁)) (by omega)
      m₁' (fun r hr => rfl) (by rw [k _ (by omega), h80]) (by rw [k _ (by omega), h85])
      (by rw [o86, hx2]) hqx hxy (by omega) (hE.stable _ _ _ hI' fr₁) hch hv (by omega)
    exact ⟨d', k', ex, hU, hk', by rwa [h82]⟩

/-! ## The upward cover -/

theorem dyUp_eq (emit : Stmt) : dyUp emit =
    .seq (block [.copyN 150080 150070, .addN 150081 150070 150071, .addN 150088 150081 150091,
      .constN 150082 0, .copyN 150083 150070, .constN 150084 1, .copyN 150085 150040,
      .addN 150087 150080 150084])
    (.seq (.whileLtN 150087 150088 (upABody emit))
      (.seq (.whileLtN 150090 150082 (upBBody emit)) (.instr (.copyN 150040 150085)))) := rfl

/-- **The upward dyadic cover** of `[q₀, q₀ + L)` from the walk vertex `c₀`. -/
theorem dyUp_exec {P : Polygon} {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop}
    {I : List Pc → Config → Prop} (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb Hb Pb tg q₀ L c₀ : ℕ} {ps₀ : List Pc} (c : Config)
    (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) (hblk : UpBlocks Pv m₀ W A₀ Tb c₀ q₀ L)
    (hqL : q₀ + L ≤ P.n) (hLtg : L ≤ 2 ^ tg) (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 2 * P.n + 4 ≤ W)
    (hw : WordsBounded W c) (hm : ∀ a, a < A₀ → c.nmem a = m₀ a)
    (h90 : c.nreg 150090 = 0) (h91 : c.nreg 150091 = 1) (h34 : c.nreg 150034 = Tb)
    (h35 : c.nreg 150035 = Hb) (h36 : c.nreg 150036 = Pb) (h70 : c.nreg 150070 = q₀)
    (h71 : c.nreg 150071 = L) (h40 : c.nreg 150040 = c₀) (hI : I ps₀ c) :
    ∃ c' k ps', Exec P W (dyUp emit) c c' k ∧ k ≤ (2 * K + 90) * (Nat.log 2 L + 1) + 20 ∧
      I (ps₀ ++ ps') c' ∧ Chained ⟨c₀, 0⟩ ps' ⟨c₀ + L, 0⟩ ∧ (∀ pc ∈ ps', Pv pc) ∧
      ps'.length ≤ 2 * (Nat.log 2 L + 1) ∧ c'.nreg 150040 = c₀ + L ∧
      (∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → c'.nreg r = c.nreg r) ∧ (∀ a, a < A₀ → c'.nmem a = m₀ a) := by
  obtain ⟨c₁, k₁, e₁, hk₁, o80, o81, o88, o82, o83, o84, o85, o87, r₁, m₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 150080 150070, .addN 150081 150070 150071,
        .addN 150088 150081 150091, .constN 150082 0, .copyN 150083 150070, .constN 150084 1,
        .copyN 150085 150040, .addN 150087 150080 150084]) c c₁ k₁ ∧ k₁ = 8 ∧
      c₁.nreg 150080 = q₀ ∧ c₁.nreg 150081 = q₀ + L ∧ c₁.nreg 150088 = q₀ + L + 1 ∧
      c₁.nreg 150082 = 0 ∧ c₁.nreg 150083 = q₀ ∧ c₁.nreg 150084 = 1 ∧ c₁.nreg 150085 = c₀ ∧
      c₁.nreg 150087 = q₀ + 1 ∧
      (∀ r, r < 150080 ∨ 150089 ≤ r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    exec_block
    all_goals first | (config_simp; rw [h70, h71]; omega) | (config_simp; rw [h70, h71, h91]; omega) |
      (config_simp; rw [h70]; omega) | omega | skip
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl⟩
    all_goals first | (config_simp; rw [h70, h71, h91]) | (config_simp; rw [h70, h71]) |
      (config_simp; rw [h70]) | (config_simp; rw [h40]) | config_simp | skip
    simp only [upd]; split_ifs <;> first | rfl | omega
  have w₁ := e₁.wb_right
  have hA0 : UpA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ c c₁ :=
    mkUpA q₀ 0 [] w₁ (fun a ha => by rw [m₁]; exact hm a ha)
      (fun r h1 h2 => r₁ r (by omega)) (by rwa [r₁ _ (by omega)])
      (by rwa [r₁ _ (by omega)]) (by rwa [r₁ _ (by omega)])
      (by rwa [r₁ _ (by omega)]) (by rwa [r₁ _ (by omega)]) o80 o81 o82
      (by rw [o83]; simp) (by rw [o84]; simp) (by rw [o85]; simp) (by rw [o87]; simp) o88 le_rfl
      (by omega) (by rw [List.append_nil]; exact hE.stable _ _ _ hI (exec_frameB e₁ (by decide)))
      (by simp [Chained]) (by simp) (by simp) (Or.inl rfl) (by omega)
  -- phase A
  obtain ⟨c₂, k₂, e₂, hA2, hx₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (a := 150087) (b := 150088)
    (body := upABody emit) (UpA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ c)
    (fun d => Nat.log 2 L + 1 - d.nreg 150082) (K + 40) (fun d hd => hd.1) (fun d hd ht => by
      obtain ⟨d', k, ex, hU, hk, hμ⟩ := upABody_exec hE env hblk hqL hLtg hW hW' hd ht
      exact ⟨d', k, ex, hU, hk, hμ⟩) hA0
  obtain ⟨w₂, ⟨m₂, s₂, a90, a91, a34, a35, a36⟩, x, g, ps', a80, a81, a82, ax, a84, a85, a87, a88,
    aqx, axy, aI, ach, av, alen, ag1, agt⟩ := hA2
  rw [a87, a88] at hx₂
  have hglog : g ≤ Nat.log 2 L + 1 := by
    rcases ag1 with h | h
    · omega
    · rcases Nat.eq_zero_or_pos L with hL | hL
      · rw [hL] at h; have := Nat.one_le_two_pow (n := g - 1); omega
      · have := Nat.le_log_of_pow_le (by norm_num) h; omega
  have hB0 : UpB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ c c₂ :=
    ⟨w₂, ⟨m₂, s₂, a90, a91, a34, a35, a36⟩, x, g, ps', a80, a81, a82, ax, a85, a88, aqx, axy,
      by omega, aI, ach, av, by omega, agt, by
        rcases Nat.eq_zero_or_pos g with h0 | h0
        · rw [h0]; omega
        · rcases ag1 with h | h
          · omega
          · have : 2 ^ g = 2 * 2 ^ (g - 1) := by rw [← pow_succ']; congr 1; omega
            omega⟩
  -- phase B
  obtain ⟨c₃, k₃, e₃, hB3, hx₃, hk₃⟩ := Exec.whileLtN_bounded (P := P) (a := 150090) (b := 150082)
    (body := upBBody emit) (UpB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ c)
    (fun d => d.nreg 150082) (K + 40) (fun d hd => hd.1) (fun d hd ht => by
      obtain ⟨d', k, ex, hU, hk, hμ⟩ := upBBody_exec hE env hblk hqL hW hW' hd ht
      exact ⟨d', k, ex, hU, hk, hμ⟩) hB0
  obtain ⟨w₃, ⟨m₃, s₃, b90, b91, b34, b35, b36⟩, x₃, g₃, ps₃, b80, b81, b82, bx, b85, b88,
    bqx, bxy, byx, bI, bch, bv, blen, bgt, bgb⟩ := hB3
  rw [b90, b82] at hx₃
  have hg0 : g₃ = 0 := by omega
  rw [hg0] at byx blen
  have hxL : x₃ = q₀ + L := by simp at byx; omega
  have e₄ := Exec.copyN (P := P) w₃ 150040 150085
  refine ⟨_, k₁ + (k₂ + (k₃ + 1)), ps₃, ?_, ?_,
    hE.stable _ _ _ bI (exec_frameB e₄ (by decide)), by rw [hxL] at bch; simpa using bch, bv,
    by omega, by config_simp; rw [b85, hxL]; omega, fun r h1 h2 h3 => ?_, ?_⟩
  · rw [dyUp_eq]; exact .seq e₁ (.seq e₂ (.seq e₃ e₄))
  · have l1 : Nat.log 2 L + 1 - c₁.nreg 150082 ≤ Nat.log 2 L + 1 := by omega
    rw [show K + 40 + 2 = K + 42 by ring] at hk₂ hk₃
    have hk2' : k₂ ≤ (K + 42) * (Nat.log 2 L + 1) + 2 :=
      le_trans hk₂ (by have := Nat.mul_le_mul_left (K + 42) l1; omega)
    have hk3' : k₃ ≤ (K + 42) * (Nat.log 2 L + 1) + 2 :=
      le_trans hk₃ (by rw [a82]; have := Nat.mul_le_mul_left (K + 42) hglog; omega)
    have e : (2 * K + 90) * (Nat.log 2 L + 1) =
        2 * ((K + 42) * (Nat.log 2 L + 1)) + 6 * (Nat.log 2 L + 1) := by ring
    omega
  · config_simp
    rw [upd_other _ _ _ h3, s₃ r h1 h2]
  · intro a ha; config_simp; exact m₃ a ha

end

end ShootCut

end Chazelle.Core
