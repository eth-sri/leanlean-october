module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ShootCutRun

/-!
# WP-G, part 18: the pieces of one step of the main loop on the RAM

* `single_exec`: the single walk edge `[c, c + 1]` handed to `emit`;
* `minTo_exec`: `150071 := min 150071 r`;
* `upStretch_exec`, `dnStretch_exec`: a climbing (descending) stretch of length
  `L = min (m - J) (ℓ - t) (n - 1 - q) lim` (`L = min (2m - J) t q lim`) and its dyadic cover.
-/


namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc

@[expose] public section

/-- The single-edge piece from the walk vertex `c`. -/
def sgPc (c : ℕ) : Pc := ⟨⟨c, 0⟩, ⟨c + 1, 0⟩, 0, 0, 0, 0, 0⟩

/-- **A single edge** handed to `emit`. -/
theorem single_exec {P : Polygon} {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop}
    {I : List Pc → Config → Prop} (hE : EmitOK P W emit A₀ Pv I K) {ps : List Pc}
    (d : Config) (hw : WordsBounded W d) {c : ℕ} (h40 : d.nreg 150040 = c)
    (h91 : d.nreg 150091 = 1) (hcW : c + 1 ≤ W) (hI : I ps d) (hpv : Pv (sgPc c)) :
    ∃ d' k, Exec P W (single emit) d d' k ∧ k ≤ K + 7 ∧ I (ps ++ [sgPc c]) d' ∧
      d'.nreg 150040 = c + 1 ∧ (∀ r, Keep r → r ≠ 150040 → d'.nreg r = d.nreg r) ∧
      (∀ a, a < A₀ → d'.nmem a = d.nmem a) := by
  obtain ⟨d₁, k₁, e₁, hk₁, v50, v51, v52, v53, v54, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W pcSingle d d₁ k₁ ∧
      k₁ = 5 ∧ d₁.nreg 150050 = c ∧ d₁.nreg 150051 = 0 ∧ d₁.nreg 150052 = c + 1 ∧
      d₁.nreg 150053 = 0 ∧ d₁.nreg 150054 = 0 ∧
      (∀ r, (r < 150050 ∨ 150055 ≤ r) → d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem := by
    unfold pcSingle
    exec_block
    all_goals (grind [upd])
  have fr₁ : FrameB Scr d d₁ := exec_frameB e₁ (by decide)
  have hR : PcRegs d₁ (sgPc c) := ⟨v50, v51, v52, v53, v54, fun h => by grind [sgPc]⟩
  obtain ⟨d₂, k₂, e₂, hk₂, hI₂, kp, mem₂⟩ := hE.run _ (sgPc c) d₁ e₁.wb_right (hE.stable _ _ _ hI fr₁) hR hpv
  have q40 : d₂.nreg 150040 = c := by
    ram_grind
  have q91 : d₂.nreg 150091 = 1 := by
    ram_grind
  have e₃ := Exec.addN (P := P) e₂.wb_right 150040 150040 150091 (by omega)
  refine ⟨_, k₁ + (k₂ + 1), .seq e₁ (.seq e₂ e₃), by omega,
    hE.stable _ _ _ hI₂ (exec_frameB e₃ (by decide)), by ram_simp,
    fun r hr h1 => ?_, fun a ha => ?_⟩
  · ram_simp
  simp_all

section
variable {P : Polygon} {W : ℕ} (d : Config) (hw : WordsBounded W d)
include hw
/-- **`150071 := min 150071 r`.** -/
theorem minTo_exec (r : ℕ) :
    ∃ d' k, Exec P W (minTo r) d d' k ∧ k ≤ 2 ∧
      d'.nreg 150071 = min (d.nreg 150071) (d.nreg r) ∧
      (∀ x, x ≠ 150071 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem := by
  unfold minTo
  by_cases h : d.nreg r < d.nreg 150071
  · refine spec_ifLtN_true h (spec_instr (Exec.copyN hw _ _) fun _ => ⟨by omega, ?_,
      fun x hx => by simp [hx], rfl⟩)
    config_simp; omega
  · refine spec_ifLtN_false h (spec_skip hw ⟨by omega, by omega, fun _ _ => rfl, rfl⟩)

/-- The straight part of a climbing stretch: `L` into `150071`. -/
theorem upLen_exec {mC J ℓ t n q lim : ℕ}
    (h23 : d.nreg 150023 = mC) (h61 : d.nreg 150061 = J) (h69 : d.nreg 150069 = ℓ)
    (h66 : d.nreg 150066 = t) (h27 : d.nreg 150027 = n) (h70 : d.nreg 150070 = q)
    (h72 : d.nreg 150072 = lim) (h91 : d.nreg 150091 = 1) :
    ∃ d' k, Exec P W upLen d d' k ∧ k ≤ 10 ∧
      d'.nreg 150071 = min (min (min (mC - J) (ℓ - t)) (n - q - 1)) lim ∧
      (∀ x, x ≠ 150071 → x ≠ 150075 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem := by
  obtain ⟨d₁, k₁, e₁, hk₁, o71, o75, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W
      (block [.subN 150071 150023 150061, .subN 150075 150069 150066]) d d₁ k₁ ∧ k₁ = 2 ∧
      d₁.nreg 150071 = mC - J ∧ d₁.nreg 150075 = ℓ - t ∧
      (∀ x, x ≠ 150071 → x ≠ 150075 → d₁.nreg x = d.nreg x) ∧ d₁.nmem = d.nmem := by
    exec_block
    simp_all
  obtain ⟨d₂, k₂, e₂, hk₂, o71', r₂, m₂⟩ := minTo_exec (P := P) d₁ e₁.wb_right 150075
  obtain ⟨d₃, k₃, e₃, hk₃, o75', r₃, m₃⟩ : ∃ d₃ k₃, Exec P W
      (block [.subN 150075 150027 150070, .subN 150075 150075 150091]) d₂ d₃ k₃ ∧ k₃ = 2 ∧
      d₃.nreg 150075 = n - q - 1 ∧ (∀ x, x ≠ 150075 → d₃.nreg x = d₂.nreg x) ∧
      d₃.nmem = d₂.nmem := by
    have a27 : d₂.nreg 150027 = n := by grind
    have a70 : d₂.nreg 150070 = q := by grind
    have a91 : d₂.nreg 150091 = 1 := by grind
    have w₂ := e₂.wb_right
    exec_block
    grind [upd]
  obtain ⟨d₄, k₄, e₄, hk₄, o71'', r₄, m₄⟩ := minTo_exec (P := P) d₃ e₃.wb_right 150075
  obtain ⟨d₅, k₅, e₅, hk₅, o71''', r₅, m₅⟩ := minTo_exec (P := P) d₄ e₄.wb_right 150072
  refine ⟨d₅, k₁ + (k₂ + (k₃ + (k₄ + k₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega,
    ?_, fun x h1 h2 => ?_, by grind⟩
  all_goals grind

/-- The straight part of a descending stretch: `L` into `150071`. -/
theorem dnLen_exec {m2 J t q lim : ℕ}
    (h29 : d.nreg 150029 = m2) (h61 : d.nreg 150061 = J) (h66 : d.nreg 150066 = t)
    (h70 : d.nreg 150070 = q) (h72 : d.nreg 150072 = lim) :
    ∃ d' k, Exec P W dnLen d d' k ∧ k ≤ 7 ∧
      d'.nreg 150071 = min (min (min (m2 - J) t) q) lim ∧
      (∀ x, x ≠ 150071 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem := by
  have e₁ := Exec.subN (P := P) hw 150071 150029 150061
  set d₁ := ({ d with nreg := upd d.nreg 150071 (d.nreg 150029 - d.nreg 150061) } : Config)
    with hd₁
  have r₁ : ∀ x, x ≠ 150071 → d₁.nreg x = d.nreg x := fun x hx => by ram_simp
  have o71 : d₁.nreg 150071 = m2 - J := by simp_all
  obtain ⟨d₂, k₂, e₂, hk₂, o₂, r₂, m₂⟩ := minTo_exec (P := P) d₁ e₁.wb_right 150066
  obtain ⟨d₃, k₃, e₃, hk₃, o₃, r₃, m₃⟩ := minTo_exec (P := P) d₂ e₂.wb_right 150070
  obtain ⟨d₄, k₄, e₄, hk₄, o₄, r₄, m₄⟩ := minTo_exec (P := P) d₃ e₃.wb_right 150072
  refine ⟨d₄, 1 + (k₂ + (k₃ + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, ?_,
    fun x hx => by grind, by grind⟩
  grind


/-- **The constants.** -/
theorem cInit_exec (hW : 6 ≤ W) :
    ∃ d' k, Exec P W cInit d d' k ∧ k = 5 ∧ d'.nreg 150090 = 0 ∧ d'.nreg 150091 = 1 ∧
      d'.nreg 150092 = 2 ∧ d'.nreg 150093 = 3 ∧ d'.nreg 150096 = 6 ∧
      (∀ r, r ≠ 150090 → r ≠ 150091 → r ≠ 150092 → r ≠ 150093 → r ≠ 150096 →
        d'.nreg r = d.nreg r) ∧ d'.nmem = d.nmem := by
  unfold cInit
  exec_block
  all_goals first | omega | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, rfl⟩
  all_goals first | (config_simp; done) | skip
  simp only [upd]; split_ifs <;> first | rfl | omega


end

section
variable {P : Polygon} {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop} {I : List Pc → Config → Prop} (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ} {Tb Hb Pb tg : ℕ} (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) {ps₀ : List Pc} (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
include hE env hw hm
/-- **A climbing stretch** on the RAM: its length `L` and its upward cover. -/
theorem upStretch_exec
    {mC J ℓ t q lim c : ℕ} (h90 : d.nreg 150090 = 0) (h91 : d.nreg 150091 = 1)
    (h34 : d.nreg 150034 = Tb) (h35 : d.nreg 150035 = Hb) (h36 : d.nreg 150036 = Pb)
    (h23 : d.nreg 150023 = mC) (h61 : d.nreg 150061 = J) (h69 : d.nreg 150069 = ℓ)
    (h66 : d.nreg 150066 = t) (h27 : d.nreg 150027 = P.n) (h70 : d.nreg 150070 = q)
    (h72 : d.nreg 150072 = lim) (h40 : d.nreg 150040 = c) (hI : I ps₀ d)
    (hqn : q + 1 < P.n) (hJ : J < mC) (ht : t < ℓ) (htg : P.n - 1 ≤ 2 ^ tg)
    (hW : c + lim + 2 ≤ W) (hW' : 5 * P.n + 6 ≤ W)
    (hblk : UpBlocks Pv m₀ W A₀ Tb c q (min (min (min (mC - J) (ℓ - t)) (P.n - q - 1)) lim)) :
    ∃ d' k ps', Exec P W (upStretch emit) d d' k ∧
      k ≤ (2 * K + 90) * (Nat.log 2 (min (min (min (mC - J) (ℓ - t)) (P.n - q - 1)) lim) + 1)
        + 40 ∧
      I (ps₀ ++ ps') d' ∧
      Chained ⟨c, 0⟩ ps' ⟨c + min (min (min (mC - J) (ℓ - t)) (P.n - q - 1)) lim, 0⟩ ∧
      (∀ pc ∈ ps', Pv pc) ∧
      ps'.length ≤ 2 * (Nat.log 2 (min (min (min (mC - J) (ℓ - t)) (P.n - q - 1)) lim) + 1) ∧
      d'.nreg 150040 = c + min (min (min (mC - J) (ℓ - t)) (P.n - q - 1)) lim ∧
      (∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → d'.nreg r = d.nreg r) ∧
      d'.nreg 150090 = 0 ∧ d'.nreg 150091 = 1 ∧ d'.nreg 150092 = 2 ∧ d'.nreg 150093 = 3 ∧
      d'.nreg 150096 = 6 ∧ WordsBounded W d' ∧ (∀ a, a < A₀ → d'.nmem a = m₀ a) := by
  set L := min (min (min (mC - J) (ℓ - t)) (P.n - q - 1)) lim with hL
  obtain ⟨d₁, k₁, e₁, hk₁, o71, r₁, m₁⟩ := upLen_exec (P := P) d hw h23 h61 h69 h66 h27 h70 h72 h91
  have fr₁ : FrameB Scr d d₁ := exec_frameB e₁ (by decide)
  have k₁' : ∀ r, r ≠ 150071 → r ≠ 150075 → d₁.nreg r = d.nreg r := r₁
  obtain ⟨d₂, k₂, ps', e₂, hk₂, hI₂, hch, hv, hlen, o40, r₂, a90, a91, m₂⟩ :=
    dyUp_exec hE (ps₀ := ps₀) (q₀ := q) (L := L) (c₀ := c) d₁ env hblk (by omega)
      (by grind) (by omega) (by omega) e₁.wb_right
      (fun a ha => by grind)
      (by grind) (by grind)
      (by grind) (by grind)
      (by grind) (by grind)
      o71 (by grind) (hE.stable _ _ _ hI fr₁)
  obtain ⟨d₃, k₃, e₃, hk₃, b90, b91, b92, b93, b96, r₃, m₃⟩ :=
    cInit_exec (P := P) d₂ e₂.wb_right (by omega)
  refine ⟨d₃, k₁ + (k₂ + k₃), ps', .seq e₁ (.seq e₂ e₃), by omega,
    hE.stable _ _ _ hI₂ (exec_frameB e₃ (by decide)), hch, hv, hlen,
    by grind,
    fun r h1 h2 h3 => ?_, b90, b91, b92, b93, b96, e₃.wb_right,
    fun a ha => by grind⟩
  rw [r₃ _ (by omega) (by omega) (by omega) (by omega) (by omega), r₂ r h1 h2 h3,
    k₁' r (by omega) (by omega)]

/-- **A descending stretch** on the RAM: its length `L` and its downward cover. -/
theorem dnStretch_exec
    {m2 J t q lim c : ℕ} (h90 : d.nreg 150090 = 0) (h91 : d.nreg 150091 = 1)
    (h34 : d.nreg 150034 = Tb) (h35 : d.nreg 150035 = Hb) (h36 : d.nreg 150036 = Pb)
    (h29 : d.nreg 150029 = m2) (h61 : d.nreg 150061 = J)
    (h66 : d.nreg 150066 = t) (h70 : d.nreg 150070 = q)
    (h72 : d.nreg 150072 = lim) (h40 : d.nreg 150040 = c) (hI : I ps₀ d)
    (hq : q < P.n) (htg : P.n - 1 ≤ 2 ^ tg)
    (hW : c + lim + 2 ≤ W) (hW' : 5 * P.n + 6 ≤ W)
    (hblk : DnBlocks Pv m₀ W A₀ Tb c q (min (min (min (m2 - J) t) q) lim)) :
    ∃ d' k ps', Exec P W (dnStretch emit) d d' k ∧
      k ≤ (2 * K + 90) * (Nat.log 2 (min (min (min (m2 - J) t) q) lim) + 1) + 40 ∧
      I (ps₀ ++ ps') d' ∧
      Chained ⟨c, 0⟩ ps' ⟨c + min (min (min (m2 - J) t) q) lim, 0⟩ ∧
      (∀ pc ∈ ps', Pv pc) ∧
      ps'.length ≤ 2 * (Nat.log 2 (min (min (min (m2 - J) t) q) lim) + 1) ∧
      d'.nreg 150040 = c + min (min (min (m2 - J) t) q) lim ∧
      (∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → d'.nreg r = d.nreg r) ∧
      d'.nreg 150090 = 0 ∧ d'.nreg 150091 = 1 ∧ d'.nreg 150092 = 2 ∧ d'.nreg 150093 = 3 ∧
      d'.nreg 150096 = 6 ∧ WordsBounded W d' ∧ (∀ a, a < A₀ → d'.nmem a = m₀ a) := by
  set L := min (min (min (m2 - J) t) q) lim with hL
  obtain ⟨d₁, k₁, e₁, hk₁, o71, r₁, m₁⟩ := dnLen_exec (P := P) d hw h29 h61 h66 h70 h72
  have fr₁ : FrameB Scr d d₁ := exec_frameB e₁ (by decide)
  have k₁' : ∀ r, r ≠ 150071 → d₁.nreg r = d.nreg r := r₁
  obtain ⟨d₂, k₂, ps', e₂, hk₂, hI₂, hch, hv, hlen, o40, r₂, a90, a91, m₂⟩ :=
    dyDn_exec hE (ps₀ := ps₀) (q₀ := q) (L := L) (c₀ := c) d₁ env hblk (by omega)
      (by omega) (by omega) (by omega) (by omega) e₁.wb_right
      (fun a ha => by grind)
      (by grind) (by grind)
      (by grind) (by grind)
      (by grind) (by grind)
      o71 (by grind) (hE.stable _ _ _ hI fr₁)
  obtain ⟨d₃, k₃, e₃, hk₃, b90, b91, b92, b93, b96, r₃, m₃⟩ :=
    cInit_exec (P := P) d₂ e₂.wb_right (by omega)
  refine ⟨d₃, k₁ + (k₂ + k₃), ps', .seq e₁ (.seq e₂ e₃), by omega,
    hE.stable _ _ _ hI₂ (exec_frameB e₃ (by decide)), hch, hv, hlen,
    by grind,
    fun r h1 h2 h3 => ?_, b90, b91, b92, b93, b96, e₃.wb_right,
    fun a ha => by grind⟩
  rw [r₃ _ (by omega) (by omega) (by omega) (by omega) (by omega), r₂ r h1 h2 h3,
    k₁' r (by omega)]


end

end

end ShootCut

end Chazelle.Core
