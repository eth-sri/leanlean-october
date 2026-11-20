module

meta import Chazelle.Programs.RamEval

public import Chazelle.Core.ShootCutDyUp

/-!
# WP-G, part 16: the downward dyadic sweep on the RAM

`dyDn emit` hands the blocks of a dyadic cover of `[q₀ - L, q₀)`, from the top `q₀` down, to
`emit`, as pieces of the walk from the vertex `c₀` (`dyDn_exec`): at most `2 (log₂ L + 1)`
pieces, chained from `c₀` to `c₀ + L`, each valid by the hypothesis `hblk` on blocks.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc

@[expose] public section

/-- The piece of the block `(g, b)` of a downward sweep from the top `q₀` at the walk vertex
`c₀`. -/
def dnPc (c₀ q₀ g b e : ℕ) : Pc :=
  ⟨⟨c₀ + (q₀ - (b + 1) * 2 ^ g), 0⟩, ⟨c₀ + (q₀ - (b + 1) * 2 ^ g) + 2 ^ g, 0⟩,
    if 0 < g then 1 else 0, e, b * 2 ^ g, 0, 2 ^ g⟩

/-- The validity of the blocks of a downward sweep. -/
def DnBlocks (Pv : Pc → Prop) (m₀ : ℕ → ℕ) (W A₀ Tb c₀ q₀ L : ℕ) : Prop :=
  ∀ g b, q₀ - L ≤ b * 2 ^ g → (b + 1) * 2 ^ g ≤ q₀ →
    (0 < g → Tb + g < A₀ ∧ m₀ (Tb + g) + 3 * b ≤ W) ∧
      ∀ e, (0 < g → e = m₀ (Tb + g) + 3 * b) → Pv (dnPc c₀ q₀ g b e)

section

variable {P : Polygon} {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop}
    {I : List Pc → Config → Prop} (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}

include hE m₀ in
/-- **The odd branch**: the block `(g, qq - 1)` below `y` is handed to `emit`. -/
theorem dn_odd
    {Tb q₀ L c₀ : ℕ} {ps : List Pc} (hblk : DnBlocks Pv m₀ W A₀ Tb c₀ q₀ L)
    (hW : c₀ + L + 2 ≤ W) (_hW' : 3 * L + 4 ≤ W) (hA : A₀ ≤ W) (hLq : L ≤ q₀) {y g qq : ℕ}
    (d₁ : Config) (w₁ : WordsBounded W d₁) (hm : MemEqBelow A₀ d₁.nmem m₀)
    (h90 : d₁.nreg 150090 = 0) (h91 : d₁.nreg 150091 = 1) (h34 : d₁.nreg 150034 = Tb)
    (h81 : d₁.nreg 150081 = y) (h82 : d₁.nreg 150082 = g) (h83 : d₁.nreg 150083 = qq)
    (h84 : d₁.nreg 150084 = 2 ^ g) (h85 : d₁.nreg 150085 = c₀ + (q₀ - y))
    (hy : y = qq * 2 ^ g) (hyq : y ≤ q₀) (hxy : q₀ - L + 2 ^ g ≤ y) (hI : I ps d₁) :
    ∃ d₅ k₅ e, Exec P W (dnOdd emit) d₁ d₅ k₅ ∧ k₅ ≤ K + 20 ∧ Pv (dnPc c₀ q₀ g (qq - 1) e) ∧
      I (ps ++ [dnPc c₀ q₀ g (qq - 1) e]) d₅ ∧ d₅.nreg 150081 = y - 2 ^ g ∧
      d₅.nreg 150085 = c₀ + (q₀ - y) + 2 ^ g ∧
      (∀ r, ((150000 ≤ r ∧ r < 150044) ∨ r = 150080 ∨ r = 150082 ∨ r = 150083 ∨
        r = 150086 ∨ r = 150090 ∨ r = 150091) → d₅.nreg r = d₁.nreg r) ∧
      (MemEqBelow A₀ d₅.nmem d₁.nmem) := by
  have hp := Nat.two_pow_pos g
  have hq1 : 1 ≤ qq := by
    rcases Nat.eq_zero_or_pos qq with h | h
    · simp_all
    · exact h
  have hyb : (qq - 1 + 1) * 2 ^ g = y := by simp_all
  have hyl : (qq - 1) * 2 ^ g = y - 2 ^ g := by rw [Nat.sub_mul, one_mul, hy]
  obtain ⟨hblk1, hblk2⟩ := hblk g (qq - 1) (by rw [hyl]; omega) (by rwa [hyb])
  obtain ⟨d₂, k₂, e₂, hk₂, n77, n78, g2, nm⟩ : ∃ d₂ k₂, Exec P W
      (block [.subN 150077 150083 150091, .subN 150078 150081 150084]) d₁ d₂ k₂ ∧ k₂ = 2 ∧
      d₂.nreg 150077 = qq - 1 ∧ d₂.nreg 150078 = y - 2 ^ g ∧
      (∀ r, r ≠ 150077 → r ≠ 150078 → d₂.nreg r = d₁.nreg r) ∧ d₂.nmem = d₁.nmem := by
    exec_block
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl⟩
    · config_simp; rw [h83, h91]
    · config_simp; rw [h81, h84]
    · simp only [upd]; split_ifs <;> first | rfl | omega
  have w₂ := e₂.wb_right
  obtain ⟨d₃, k₃, e₃, hk₃, v50, v51, v52, v53, v54, v55, v56, v57, v58, r₃, m₃⟩ :=
    pcBlock_exec (P := P) d₂ w₂ 150078 0 (Or.inr (by omega)) (by omega)
      (by simp [g2, h90])
      (by ram_simp [g2, h85, h84] <;> omega)
      (fun hg => by
        have hg' : 0 < g := by ram_rw assumption [g2, h82] at hg
        ram_rw [g2, g2, n77, nm, h34, h82,
          hm _ (hblk1 hg').1]
        exact ⟨by have := (hblk1 hg').1; omega, (hblk1 hg').2⟩)
  ram_rw [g2] at v50 v52 v54 v58 v55
  ram_rw [g2] at v52
  set pc := dnPc c₀ q₀ g (qq - 1) (d₃.nreg 150055) with hpc
  have hpcR : PcRegs d₃ pc := by
    refine ⟨?_, v51, ?_, v53, ?_, fun _ => ⟨rfl, ?_, v57, ?_⟩⟩
    · rw [v50, h85, hpc]; simp [dnPc, hyb]
    · rw [v52, h85, h84, hpc]; simp [dnPc, hyb]
    · rw [v54, h82, hpc]; rfl
    · rw [v56, n78, hpc]; simp [dnPc, hyl]
    · rw [v58, h84]; rfl
  have hpv : Pv pc := hblk2 _ (fun hg => by
    ram_rw [v55 (by rwa [h82]), g2, n77, h82, h34, nm,
      hm _ (hblk1 hg).1])
  have fr₃ : FrameB Scr d₁ d₃ := (by ram_frame)
  obtain ⟨d₄, k₄, e₄, hk₄, hI₄, kp, mem₄⟩ := hE.run _ pc d₃ e₃.wb_right (hE.stable _ _ _ hI fr₃) hpcR hpv
  have w₄ := e₄.wb_right
  have back : ∀ r, Keep r → r ≠ 150077 → r ≠ 150078 → (r < 150050 ∨ 150059 ≤ r) →
      r ≠ 150075 → r ≠ 150076 → d₄.nreg r = d₁.nreg r := fun r hk h1 h1' h2 h3 h4 => by
    frame_finish
  have q81 : d₄.nreg 150081 = y := by rw [back _ (Or.inr (by omega)) (by omega) (by omega)
    (by omega) (by omega) (by omega), h81]
  have q84 : d₄.nreg 150084 = 2 ^ g := by rw [back _ (Or.inr (by omega)) (by omega) (by omega)
    (by omega) (by omega) (by omega), h84]
  have q85 : d₄.nreg 150085 = c₀ + (q₀ - y) := by rw [back _ (Or.inr (by omega)) (by omega)
    (by omega) (by omega) (by omega) (by omega), h85]
  obtain ⟨d₅, k₅, e₅, hk₅, a81, a85, r₅, m₅⟩ : ∃ d₅ k₅, Exec P W
      (block [.subN 150081 150081 150084, .addN 150085 150085 150084]) d₄ d₅ k₅ ∧ k₅ = 2 ∧
      d₅.nreg 150081 = y - 2 ^ g ∧ d₅.nreg 150085 = c₀ + (q₀ - y) + 2 ^ g ∧
      (∀ r, r ≠ 150081 → r ≠ 150085 → d₅.nreg r = d₄.nreg r) ∧ d₅.nmem = d₄.nmem := by
    exec_block
    all_goals first | (config_simp; rw [q85, q84]; omega) | skip
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl⟩
    · config_simp; rw [q81, q84]
    · config_simp; rw [q85, q84]
    · simp only [upd]; split_ifs <;> first | rfl | omega
  refine ⟨d₅, k₂ + (k₃ + (k₄ + k₅)), d₃.nreg 150055, (by ram_path),
    by omega, hpv, hE.stable _ _ _ hI₄ (exec_frameB e₅ (by decide)), a81, a85, ?_, ?_⟩
  · intro r hr
    ram_rw [r₅ r, back r (by unfold Keep; omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)]
  · intro a ha
    rw [m₅, mem₄ a ha, m₃, nm]

/-! ## The ascending sweep of the downward cover -/

/-- The invariant of the ascending sweep of the downward cover. -/
def DnA (W : ℕ) (Pv : Pc → Prop) (I : List Pc → Config → Prop) (ps₀ : List Pc)
    (m₀ : ℕ → ℕ) (A₀ Tb Hb Pb tg q₀ L c₀ : ℕ) (cc d : Config) : Prop :=
  WordsBounded W d ∧ SwRegs Tb Hb Pb m₀ A₀ cc d ∧
    ∃ y g ps', d.nreg 150080 = q₀ - L ∧ d.nreg 150081 = y ∧ d.nreg 150082 = g ∧
      y = d.nreg 150083 * 2 ^ g ∧ d.nreg 150084 = 2 ^ g ∧ d.nreg 150085 = c₀ + (q₀ - y) ∧
      d.nreg 150087 = q₀ - L + 2 ^ g ∧ d.nreg 150088 = y + 1 ∧ q₀ - L ≤ y ∧ y ≤ q₀ ∧
      I (ps₀ ++ ps') d ∧ Chained ⟨c₀, 0⟩ ps' ⟨c₀ + (q₀ - y), 0⟩ ∧ (∀ pc ∈ ps', Pv pc) ∧
      ps'.length ≤ g ∧ (g = 0 ∨ 2 ^ (g - 1) ≤ L) ∧ g ≤ tg + 1

/-- The tail block of a step of the ascending sweep of the downward cover. -/
def dnATail : Stmt := block [.addN 150082 150082 150091, .addN 150075 150036 150082,
  .loadN 150084 150075, .copyN 150083 150086, .addN 150087 150080 150084,
  .addN 150088 150081 150091]

theorem dnABody_eq (emit : Stmt) : dnABody emit =
    .seq sweepHalf
      (.seq (.ifLtN 150075 150083 (dnOdd emit) .skip) dnATail) := rfl

theorem dnATail_exec {P : Polygon} {W A₀ Pb g x y : ℕ} {m₀ : ℕ → ℕ} (d : Config)
    (hw : WordsBounded W d) (hm : MemEqBelow A₀ d.nmem m₀) (h36 : d.nreg 150036 = Pb)
    (h82 : d.nreg 150082 = g) (h80 : d.nreg 150080 = x) (h81 : d.nreg 150081 = y)
    (h91 : d.nreg 150091 = 1)
    (hpow : m₀ (Pb + (g + 1)) = 2 ^ (g + 1) ∧ Pb + (g + 1) < A₀) (hA : A₀ ≤ W)
    (hxW : x + 2 ^ (g + 1) ≤ W) (hyW : y + 1 ≤ W) :
    ∃ d' k, Exec P W dnATail d d' k ∧ k = 6 ∧ d'.nreg 150082 = g + 1 ∧
      d'.nreg 150084 = 2 ^ (g + 1) ∧ d'.nreg 150083 = d.nreg 150086 ∧
      d'.nreg 150087 = x + 2 ^ (g + 1) ∧ d'.nreg 150088 = y + 1 ∧
      (∀ r, r ≠ 150075 → r ≠ 150082 → r ≠ 150083 → r ≠ 150084 → r ≠ 150087 → r ≠ 150088 →
        d'.nreg r = d.nreg r) ∧ d'.nmem = d.nmem := by
  
  unfold dnATail
  exec_block
  all_goals first | (config_simp; rw [h82, h91]; omega) | (config_simp; rw [h82, h91, h36]; omega) |
    (config_simp; rw [h82, h91, h80, h36, hm _ hpow.2, hpow.1]; omega) |
    (config_simp; rw [h81, h91]; omega) | skip
  simp_all <;> omega

include hE m₀ in
/-- **After the optional block** of the ascending sweep of the downward cover. -/
theorem dnA_after
    {Tb Hb Pb tg q₀ L c₀ : ℕ} {ps₀ : List Pc} {cc : Config}
    (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 2 * P.n + 4 ≤ W)
    (hq : q₀ ≤ P.n) (d₅ : Config) (w₅ : WordsBounded W d₅) (y' h' g : ℕ) (ps'' : List Pc)
    (hgt : g ≤ tg) (hgL : 2 ^ g ≤ L)
    (hs : SwRegs Tb Hb Pb m₀ A₀ cc d₅) (a82 : d₅.nreg 150082 = g)
    (a80 : d₅.nreg 150080 = q₀ - L) (a81 : d₅.nreg 150081 = y')
    (a85 : d₅.nreg 150085 = c₀ + (q₀ - y'))
    (hy' : y' = h' * 2 ^ (g + 1)) (a86 : d₅.nreg 150086 = h') (hq' : q₀ - L ≤ y') (hy'q : y' ≤ q₀)
    (hI₅ : I (ps₀ ++ ps'') d₅) (hch₅ : Chained ⟨c₀, 0⟩ ps'' ⟨c₀ + (q₀ - y'), 0⟩)
    (hv₅ : ∀ pc ∈ ps'', Pv pc) (hl₅ : ps''.length ≤ g + 1) :
    ∃ d₆ k₆, Exec P W dnATail d₅ d₆ k₆ ∧ k₆ = 6 ∧
      DnA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d₆ ∧ d₆.nreg 150082 = g + 1 := by
  obtain ⟨hp1, hp2⟩ := env.pow (g + 1) (by omega)
  obtain ⟨d₆, k₆, e₆, hk₆, b82, b84, b83, b87, b88, r₆, m₆⟩ := dnATail_exec (P := P)
    (x := q₀ - L) (y := y') d₅ w₅ hs.1 hs.2.2.2.2.2.2 a82 a80 a81 hs.2.2.2.1 ⟨hp1, hp2⟩ env.aW
    (by rw [pow_succ]; omega) (by omega)
  have fr₆ : FrameB Scr d₅ d₆ := exec_frameB e₆ (by decide)
  have k : ∀ r, r ≠ 150075 → r ≠ 150082 → r ≠ 150083 → r ≠ 150084 → r ≠ 150087 →
      r ≠ 150088 → d₆.nreg r = d₅.nreg r := r₆
  refine ⟨d₆, k₆, e₆, hk₆, ⟨e₆.wb_right, hs.keep (fun a _ => congrFun m₆ a) (fun r hr => r₆ r ?_ ?_ ?_ ?_ ?_ ?_),
    y', g + 1, ps'',
    by ram_simp [k] <;> omega,
    by ram_simp [k] <;> omega,
    b82, by rwa [b83, a86], b84,
    by ram_simp [k] <;> omega,
    b87, b88, hq', hy'q, hE.stable _ _ _ hI₅ fr₆, hch₅, hv₅, hl₅, Or.inr (by simpa using hgL),
    by omega⟩, b82⟩ <;> omega

include hE m₀ in
/-- **One step of the ascending sweep of the downward cover.** -/
theorem dnABody_exec
    {Tb Hb Pb tg q₀ L c₀ : ℕ} {ps₀ : List Pc} {cc d : Config}
    (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) (hblk : DnBlocks Pv m₀ W A₀ Tb c₀ q₀ L)
    (hq : q₀ ≤ P.n) (hLq : L ≤ q₀) (hLtg : L ≤ 2 ^ tg) (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 2 * P.n + 4 ≤ W)
    (hI : DnA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d)
    (ht : d.nreg 150087 < d.nreg 150088) :
    ∃ d' k, Exec P W (dnABody emit) d d' k ∧ DnA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d' ∧
      k ≤ K + 40 ∧ Nat.log 2 L + 1 - d'.nreg 150082 < Nat.log 2 L + 1 - d.nreg 150082 := by
  have hs := hI.2.1
  obtain ⟨hw, ⟨hm, -, h90, h91, h34, h35, -⟩, y, g, ps', h80, h81, h82, hy, h84, h85, h87,
    h88, hqy, hyq, hI', hch, hv, hlen, hg1, hgtg⟩ := hI
  rw [h87, h88] at ht
  have hp := Nat.two_pow_pos g
  have hgL : 2 ^ g ≤ L := by omega
  have hgt := pow_le_of_le hgL hLtg
  have hgl := Nat.le_log_of_pow_le (by norm_num) hgL
  have hqqy : d.nreg 150083 ≤ y := by rw [hy]; exact Nat.le_mul_of_pos_right _ hp
  have hA := env.aW
  obtain ⟨hh1, hh2⟩ := env.half (d.nreg 150083) (by omega)
  obtain ⟨d₁, k₁, e₁, hk₁, o75, o86, k₁', m₁⟩ :=
    sweepHalf_exec (P := P) hw hm h35 hh1 hh2 hA (hw.1 150083)
  have w₁ := e₁.wb_right
  have fr₁ : FrameB Scr d d₁ := exec_frameB e₁ (by decide)
  have hs₁ := hs.keep (fun a _ => congrFun m₁ a) (fun r hr => k₁' r (by omega) (by omega))
  rw [dnABody_eq]
  by_cases hodd : d.nreg 150083 / 2 + d.nreg 150083 / 2 < d.nreg 150083
  · obtain ⟨d₅, k₅, e, e₅, hk₅, hpv, hI₅, a81, a85, r₅, m₅⟩ := dn_odd hE (ps := ps₀ ++ ps')
      hblk (by omega) (by omega) hA hLq (y := y) (g := g) (qq := d.nreg 150083) d₁ w₁ hs₁.1
      (by ram_rw [k₁', h90]) (by ram_rw [k₁', h91])
      (by ram_rw [k₁', h34]) (by ram_rw [k₁', h81])
      (by ram_rw [k₁', h82]) (by ram_rw [k₁'])
      (by ram_rw [k₁', h84]) (by ram_rw [k₁', h85])
      hy hyq (by omega) (hE.stable _ _ _ hI' fr₁)
    have kk : ∀ r, ((150000 ≤ r ∧ r < 150044) ∨ r = 150080 ∨ r = 150082 ∨
        r = 150090 ∨ r = 150091) → d₅.nreg r = d.nreg r := fun r hr => by
      ram_rw [r₅ r, k₁' r]
    have w₅ := e₅.wb_right
    obtain ⟨d₆, k₆, e₆, hk₆, hU, b82⟩ := dnA_after hE env hW hW' hq d₅ w₅ (y - 2 ^ g)
      (d.nreg 150083 / 2) g (ps' ++ [dnPc c₀ q₀ g (d.nreg 150083 - 1) e]) hgt hgL
      (hs₁.keep m₅ (fun r hr => r₅ r (by omega))) (by ram_rw assumption [kk])
      (by ram_rw assumption [kk]) a81 (by rw [a85]; omega)
      (by rw [hy, pow_succ]; have : d.nreg 150083 = 2 * (d.nreg 150083 / 2) + 1 := by omega
          nth_rewrite 1 [this]; rw [Nat.add_mul, one_mul, Nat.add_sub_cancel]; ring)
      (by ram_rw [r₅, o86]) (by omega) (by omega)
      (by rwa [← List.append_assoc])
      (by
        have hq1 : 1 ≤ d.nreg 150083 := by
          rcases Nat.eq_zero_or_pos (d.nreg 150083) with h | h
          · omega
          · exact h
        have h2 := hch.append (dnPc c₀ q₀ g (d.nreg 150083 - 1) e) (by
          simp [dnPc, Nat.sub_add_cancel hq1, ← hy])
        have he : (dnPc c₀ q₀ g (d.nreg 150083 - 1) e).e = ⟨c₀ + (q₀ - (y - 2 ^ g)), 0⟩ := by
          simp only [dnPc, Nat.sub_add_cancel hq1, ← hy, WPos.mk.injEq, and_true]; omega
        rwa [he] at h2)
      (by simpa only [List.forall_mem_append, List.forall_mem_singleton] using And.intro hv hpv)
      (by simp; omega)
    exact ⟨d₆, k₁ + ((k₅ + 1) + k₆), .seq e₁ (.seq (.ifLtN_true (by
        ram_post) e₅) e₆), hU, by omega,
      by rw [b82, h82]; omega⟩
  · obtain ⟨d₆, k₆, e₆, hk₆, hU, b82⟩ := dnA_after hE env hW hW' hq d₁ w₁ y
      (d.nreg 150083 / 2) g ps' hgt hgL hs₁
      (by ram_rw assumption [k₁'])
      (by ram_rw assumption [k₁'])
      (by ram_rw assumption [k₁'])
      (by ram_rw assumption [k₁'])
      (by rw [hy, pow_succ]; have : d.nreg 150083 = 2 * (d.nreg 150083 / 2) := by omega
          nth_rewrite 1 [this]; ring)
      o86 hqy hyq (hE.stable _ _ _ hI' fr₁) hch hv (by omega)
    exact ⟨d₆, k₁ + ((0 + 2) + k₆), .seq e₁ (.seq (.ifLtN_false (by
        ram_simp [o75, k₁'] <;> reg_omega) (.skip w₁)) e₆), hU, by omega,
      by rw [b82, h82]; omega⟩


/-! ## The descending sweep of the downward cover -/

/-- The invariant of the descending sweep of the downward cover. -/
def DnB (W : ℕ) (Pv : Pc → Prop) (I : List Pc → Config → Prop) (ps₀ : List Pc)
    (m₀ : ℕ → ℕ) (A₀ Tb Hb Pb tg q₀ L c₀ : ℕ) (cc d : Config) : Prop :=
  WordsBounded W d ∧ SwRegs Tb Hb Pb m₀ A₀ cc d ∧
    ∃ y g ps', d.nreg 150080 = q₀ - L ∧ d.nreg 150081 = y ∧ d.nreg 150082 = g ∧
      y = d.nreg 150083 * 2 ^ g ∧ d.nreg 150085 = c₀ + (q₀ - y) ∧
      q₀ - L ≤ y ∧ y ≤ q₀ ∧ y < q₀ - L + 2 ^ g ∧
      I (ps₀ ++ ps') d ∧ Chained ⟨c₀, 0⟩ ps' ⟨c₀ + (q₀ - y), 0⟩ ∧ (∀ pc ∈ ps', Pv pc) ∧
      ps'.length + g ≤ 2 * (Nat.log 2 L + 1) ∧ g ≤ tg + 1 ∧ 2 ^ g ≤ 2 * L + 1

theorem dnBBody_eq (emit : Stmt) : dnBBody emit =
    .seq (block [.subN 150082 150082 150091, .addN 150075 150036 150082, .loadN 150084 150075,
      .addN 150083 150083 150083, .addN 150087 150080 150084, .addN 150088 150081 150091])
    (.ifLtN 150087 150088 (.seq (dnOdd emit) (.instr (.subN 150083 150083 150091))) .skip) :=
  rfl

include hE m₀ in
/-- **One step of the descending sweep of the downward cover.** -/
theorem dnBBody_exec
    {Tb Hb Pb tg q₀ L c₀ : ℕ} {ps₀ : List Pc} {cc d : Config}
    (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) (hblk : DnBlocks Pv m₀ W A₀ Tb c₀ q₀ L)
    (hq : q₀ ≤ P.n) (hLq : L ≤ q₀) (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 2 * P.n + 4 ≤ W)
    (hI : DnB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d)
    (ht : d.nreg 150090 < d.nreg 150082) :
    ∃ d' k, Exec P W (dnBBody emit) d d' k ∧ DnB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d' ∧
      k ≤ K + 40 ∧ d'.nreg 150082 < d.nreg 150082 := by
  have hs := hI.2.1
  obtain ⟨hw, ⟨hm, -, h90, h91, h34, -, h36⟩, y, g, ps', h80, h81, h82, hy, h85,
    hxy, hyq, hyx, hI', hch, hv, hlen, hgt, hgb⟩ := hI
  rw [h90, h82] at ht
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  have hp := Nat.two_pow_pos g'
  have hA := env.aW
  obtain ⟨hp1, hp2⟩ := env.pow g' (by omega)
  set qq := d.nreg 150083 with hqq
  have hy2 : y = (qq + qq) * 2 ^ g' := by rw [hy, pow_succ]; ring
  have hqqy : qq + qq ≤ y := by rw [hy2]; exact Nat.le_mul_of_pos_right _ hp
  
  
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
      (config_simp; ram_rw [h82, h91, Nat.add_sub_cancel, h36, h80, hm, hp1]; omega) | skip
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 => ?_, rfl⟩
    · config_simp; rw [h82, h91, Nat.add_sub_cancel]
    · ram_simp [h82, h91, Nat.add_sub_cancel, h36, hm, hp1] <;> reg_omega
    · config_simp; rw [← hqq]
    · ram_simp [h82, h91, Nat.add_sub_cancel, h36, h80, hm, hp1] <;> reg_omega
    · config_simp; rw [h81, h91]
    · simp only [upd]; split_ifs <;> first | rfl | omega
  have w₁ := e₁.wb_right
  have fr₁ : FrameB Scr d d₁ := exec_frameB e₁ (by decide)
  have k : ∀ r, ((150000 ≤ r ∧ r < 150044) ∨ r = 150080 ∨ r = 150081 ∨ r = 150085 ∨
      r = 150090 ∨ r = 150091) → d₁.nreg r = d.nreg r := fun r hr =>
    r₁ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have m₁' : MemEqBelow A₀ d₁.nmem m₀ := fun a ha => by rw [m₁]; exact hm a ha
  rw [dnBBody_eq]
  by_cases hodd : d₁.nreg 150087 < d₁.nreg 150088
  · have hodd' := hodd
    rw [o87, o88] at hodd'
    obtain ⟨d₅, k₅, e, e₅, hk₅, hpv, hI₅, a81, a85, r₅, m₅⟩ := dn_odd hE (ps := ps₀ ++ ps')
      hblk (by omega) (by omega) hA hLq (y := y) (g := g') (qq := qq + qq) d₁ w₁ m₁'
      (by ram_rw [k, h90]) (by ram_rw [k, h91])
      (by ram_rw [k, h34]) (by ram_rw [k, h81]) o82 o83 o84
      (by ram_rw [k, h85]) hy2 hyq (by omega) (hE.stable _ _ _ hI' fr₁)
    have w₅ := e₅.wb_right
    have e₆ := Exec.subN (P := P) w₅ 150083 150083 150091
    set d₆ := ({ d₅ with nreg := upd d₅.nreg 150083 (d₅.nreg 150083 - d₅.nreg 150091) } :
      Config) with hd₆
    have g6 : ∀ r, r ≠ 150083 → d₆.nreg r = d₅.nreg r := fun r hr => by simp [hd₆, upd, hr]
    have b83 : d₆.nreg 150083 = qq + qq - 1 := by
      frame_finish [hd₆, ↓reduceIte, r₅, o83, k, h91]
    have kk : ∀ r, ((150000 ≤ r ∧ r < 150044) ∨ r = 150080 ∨ r = 150090 ∨ r = 150091) →
        d₆.nreg r = d.nreg r := fun r hr => by
      ram_rw [g6 r, r₅ r, k r]
    have hq1 : 1 ≤ qq + qq := by
      rcases Nat.eq_zero_or_pos (qq + qq) with h | h
      · rw [h] at hy2; simp at hy2; omega
      · exact h
    have hyl : (qq + qq - 1) * 2 ^ g' = y - 2 ^ g' := by rw [Nat.sub_mul, one_mul, hy2]
    refine ⟨d₆, k₁ + ((k₅ + 1) + 1), (by ram_path), ⟨e₆.wb_right,
      hs.keep (fun a ha => (m₅ a ha).trans (congrFun m₁ a)) (fun r hr => kk r (by omega)),
      y - 2 ^ g', g', ps' ++ [dnPc c₀ q₀ g' (qq + qq - 1) e],
      by ram_rw assumption [kk], by assumption,
      by frame_finish,
      by rw [b83, hyl], by ram_rw [g6, a85]; omega, by omega, by omega, by omega,
      hE.stable _ _ _ (by rwa [← List.append_assoc]) (exec_frameB e₆ (by decide)),
      ?_, ?_, by simp; omega, by omega, by omega⟩, by omega, ?_⟩
    · have h2 := hch.append (dnPc c₀ q₀ g' (qq + qq - 1) e) (by
        simp [dnPc, Nat.sub_add_cancel hq1, ← hy2])
      have he : (dnPc c₀ q₀ g' (qq + qq - 1) e).e = ⟨c₀ + (q₀ - (y - 2 ^ g')), 0⟩ := by
        simp only [dnPc, Nat.sub_add_cancel hq1, ← hy2, WPos.mk.injEq, and_true]; omega
      rwa [he] at h2
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hv p hp
      · simp only [List.mem_singleton] at hp; rwa [hp]
    · simp [g6, r₅, o82, h82]
  · have hodd' := hodd
    rw [o87, o88] at hodd'
    refine ⟨d₁, k₁ + (0 + 2), .seq e₁ (.ifLtN_false hodd (.skip w₁)), ⟨w₁,
      hs.keep (fun a _ => congrFun m₁ a) (fun r hr => k r (by omega)),
      y, g', ps', by ram_rw assumption [k], by ram_rw assumption [k], o82,
      by rwa [o83], by ram_rw assumption [k], hxy, hyq, by omega,
      hE.stable _ _ _ hI' fr₁, hch, hv, by omega, by omega, by omega⟩, by omega,
      by rw [o82, h82]; omega⟩

/-! ## The downward cover -/

theorem dyDn_eq (emit : Stmt) : dyDn emit =
    .seq (sweepInit false)
    (.seq (.whileLtN 150087 150088 (dnABody emit))
      (.seq (.whileLtN 150090 150082 (dnBBody emit)) (.instr (.copyN 150040 150085)))) := rfl

include hE m₀ in
/-- **The downward dyadic cover** of `[q₀ - L, q₀)` from the walk vertex `c₀`. -/
theorem dyDn_exec
    {Tb Hb Pb tg q₀ L c₀ : ℕ} {ps₀ : List Pc} (c : Config)
    (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) (hblk : DnBlocks Pv m₀ W A₀ Tb c₀ q₀ L)
    (hq : q₀ ≤ P.n) (hLq : L ≤ q₀) (hLtg : L ≤ 2 ^ tg) (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 2 * P.n + 4 ≤ W)
    (hw : WordsBounded W c) (hm : MemEqBelow A₀ c.nmem m₀)
    (h90 : c.nreg 150090 = 0) (h91 : c.nreg 150091 = 1) (h34 : c.nreg 150034 = Tb)
    (h35 : c.nreg 150035 = Hb) (h36 : c.nreg 150036 = Pb) (h70 : c.nreg 150070 = q₀)
    (h71 : c.nreg 150071 = L) (h40 : c.nreg 150040 = c₀) (hI : I ps₀ c) :
    ∃ c' k ps', Exec P W (dyDn emit) c c' k ∧ k ≤ (2 * K + 90) * (Nat.log 2 L + 1) + 20 ∧
      I (ps₀ ++ ps') c' ∧ Chained ⟨c₀, 0⟩ ps' ⟨c₀ + L, 0⟩ ∧ (∀ pc ∈ ps', Pv pc) ∧
      ps'.length ≤ 2 * (Nat.log 2 L + 1) ∧ c'.nreg 150040 = c₀ + L ∧
      (∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → c'.nreg r = c.nreg r) ∧
      c'.nreg 150090 = 0 ∧ c'.nreg 150091 = 1 ∧ (MemEqBelow A₀ c'.nmem m₀) := by
  have hA := env.aW
  obtain ⟨c₁, k₁, e₁, hk₁, o80, o81, o88, o82, o83, o84, o85, o87, r₁, m₁⟩ :=
    sweepInit_exec (P := P) false hw (by change q₀ + 1 ≤ W; omega) (by omega) h70 h71 h91 h40
  have w₁ := e₁.wb_right
  have hs : SwRegs Tb Hb Pb m₀ A₀ c c := ⟨hm, fun _ _ _ => rfl, h90, h91, h34, h35, h36⟩
  have hs₁ := hs.keep (fun a _ => congrFun m₁ a) (fun r hr => r₁ r (by omega))
  have hA0 : DnA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ c c₁ :=
    ⟨w₁, hs₁, q₀, 0, [], o80, o81, o82, by rw [o83]; simp,
      by rw [o84]; simp, by rw [o85]; simp, by rw [o87]; simp, o88, by omega, le_rfl,
      by rw [List.append_nil]; exact hE.stable _ _ _ hI (exec_frameB e₁ (by decide)),
      by simp [Chained], by simp, by simp, Or.inl rfl, by omega⟩
  -- phase A
  obtain ⟨c₂, k₂, e₂, hA2, hx₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (a := 150087) (b := 150088)
    (body := dnABody emit) (DnA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ c)
    (fun d => Nat.log 2 L + 1 - d.nreg 150082) (K + 40) (fun d hd => hd.1) (fun d hd ht => by
      exact dnABody_exec hE env hblk hq hLq hLtg hW hW' hd ht) hA0
  obtain ⟨w₂, regs₂, y, g, ps', a80, a81, a82, ay, a84, a85, a87, a88,
    aqy, ayq, aI, ach, av, alen, ag1, agt⟩ := hA2
  rw [a87, a88] at hx₂
  obtain ⟨hglog, hpow⟩ := ascend_limits ag1
  have hB0 : DnB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ c c₂ :=
    ⟨w₂, regs₂, y, g, ps', a80, a81, a82, ay, a85, aqy, ayq,
      by omega, aI, ach, av, by omega, agt, hpow⟩
  -- phase B
  obtain ⟨c₃, k₃, e₃, hB3, hx₃, hk₃⟩ := Exec.whileLtN_bounded (P := P) (a := 150090) (b := 150082)
    (body := dnBBody emit) (DnB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ c)
    (fun d => d.nreg 150082) (K + 40) (fun d hd => hd.1) (fun d hd ht => by
      exact dnBBody_exec hE env hblk hq hLq hW hW' hd ht) hB0
  obtain ⟨w₃, ⟨m₃, s₃, b90, b91, b34, b35, b36⟩, y₃, g₃, ps₃, b80, b81, b82, by₃, b85,
    bqy, byq, byx, bI, bch, bv, blen, bgt, bgb⟩ := hB3
  rw [b90, b82] at hx₃
  have hg0 : g₃ = 0 := by omega
  rw [hg0] at byx blen
  have hyL : q₀ - y₃ = L := by simp at byx; omega
  have e₄ := Exec.copyN (P := P) w₃ 150040 150085
  refine ⟨_, k₁ + (k₂ + (k₃ + 1)), ps₃, ?_, ?_,
    hE.stable _ _ _ bI (exec_frameB e₄ (by decide)), by rw [hyL] at bch; exact bch, bv,
    by omega, by config_simp; rw [b85, hyL], fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
  · rw [dyDn_eq]; exact .seq e₁ (.seq e₂ (.seq e₃ e₄))
  · rw [show K + 40 + 2 = K + 42 by omega] at hk₂ hk₃
    rw [a82] at hk₃
    have h := sweepCost (Nat.sub_le (Nat.log 2 L + 1) (c₁.nreg 150082)) hglog hk₂ hk₃
    omega
  · config_simp
    rw [upd_other _ _ _ h3, s₃ r h1 h2]
  · config_simp; exact b90
  · config_simp; exact b91
  · intro a ha; config_simp; exact m₃ a ha

end

end

end ShootCut

end Chazelle.Core
