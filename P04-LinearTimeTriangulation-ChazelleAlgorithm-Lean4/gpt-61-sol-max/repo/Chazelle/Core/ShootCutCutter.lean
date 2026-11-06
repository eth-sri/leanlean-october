module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ShootCutCore2

/-!
# WP-G, part 34: the arc-cutter's `emit`

The arc-cutter runs the core with `cutEmit`, which writes the record of each piece (seven words:
the two ends, the kind, the descriptor and normal-form handles of the grade chain of a kind-`1`
piece) at the pointer `140000` (band `bShoot`, which the cutter may write and the core does not),
from the list base `A₀ + 1` on.  A guard `ptr < LIM` keeps the pointer below the word bound;
`LIM` leaves room for more pieces than the core ever hands.

* `RecOK`: the records in memory;
* `CutI`: the invariant of `cutEmit`; `cutEmit_ok`: its contract (`EmitOK`).
-/


namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc

@[expose] public section

/-! ## The programs -/

/-- The five words of the ends and the kind. -/
def cutStore : Stmt := block [.storeN 140000 150050, .addN 140000 140000 140003,
  .storeN 140000 150051, .addN 140000 140000 140003, .storeN 140000 150052,
  .addN 140000 140000 140003, .storeN 140000 150053, .addN 140000 140000 140003,
  .storeN 140000 150054, .addN 140000 140000 140003]

/-- Kind `0`: two zero words. -/
def cutK0 : Stmt := block [.storeN 140000 140006, .addN 140000 140000 140003,
  .storeN 140000 140006, .addN 140000 140000 140003]

/-- Kind `1`: the descriptor and normal-form handles of the grade-table entry `150055`. -/
def cutK1 : Stmt := block [.loadN 140004 150055, .storeN 140000 140004,
  .addN 140000 140000 140003, .addN 140005 150055 140003, .loadN 140004 140005,
  .storeN 140000 140004, .addN 140000 140000 140003]

/-- **The arc-cutter's `emit`**: the record of the piece, if there is room. -/
def cutEmit : Stmt :=
  .ifLtN 140000 140007
    (.seq cutStore (.seq (.ifLtN 150054 140003 cutK0 cutK1) (.instr (.addN 140002 140002 140003))))
    .skip

/-! ## The records -/

/-- The records of the pieces `ps` from the list base `L + 1` on. -/
def RecOK (m₀ mem : ℕ → ℕ) (L : ℕ) (ps : List Pc) : Prop :=
  ∀ i (hi : i < ps.length),
    mem (L + 1 + 7 * i) = (ps[i]'hi).s.edge ∧ mem (L + 1 + 7 * i + 1) = (ps[i]'hi).s.hgt ∧
    mem (L + 1 + 7 * i + 2) = (ps[i]'hi).e.edge ∧ mem (L + 1 + 7 * i + 3) = (ps[i]'hi).e.hgt ∧
    mem (L + 1 + 7 * i + 4) = (ps[i]'hi).kind ∧
    ((ps[i]'hi).kind = 1 → mem (L + 1 + 7 * i + 5) = m₀ (ps[i]'hi).entry ∧
      mem (L + 1 + 7 * i + 6) = m₀ ((ps[i]'hi).entry + 1))

/-- **The invariant of `cutEmit`** (`Nmax` records fit below `LIM = A₀ + 1 + 7 Nmax`). -/
structure CutI (W A₀ Nmax : ℕ) (m₀ : ℕ → ℕ) (ps : List Pc) (c : Config) : Prop where
  alloc : c.nreg ALLOC = A₀
  base : c.nreg 140001 = A₀
  one : c.nreg 140003 = 1
  zero : c.nreg 140006 = 0
  lim : c.nreg 140007 = A₀ + 1 + 7 * Nmax
  limW : A₀ + 1 + 7 * Nmax + 7 ≤ W
  mem : ∀ a, a < A₀ → c.nmem a = m₀ a
  ptr : c.nreg 140000 = A₀ + 1 + 7 * min ps.length Nmax
  cnt : c.nreg 140002 = min ps.length Nmax
  recs : RecOK m₀ c.nmem A₀ (ps.take Nmax)

/-! ## The pieces of `cutEmit` -/

section
variable {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
include hw
section
variable {p : ℕ} (h00 : c.nreg 140000 = p) (h03 : c.nreg 140003 = 1)
include p h00 h03
theorem cutStore_exec (hp : p + 5 ≤ W) :
    ∃ c' k, Exec P W cutStore c c' k ∧ k = 10 ∧ c'.nreg 140000 = p + 5 ∧
      c'.nmem p = c.nreg 150050 ∧ c'.nmem (p + 1) = c.nreg 150051 ∧
      c'.nmem (p + 2) = c.nreg 150052 ∧ c'.nmem (p + 3) = c.nreg 150053 ∧
      c'.nmem (p + 4) = c.nreg 150054 ∧ (∀ a, a < p → c'.nmem a = c.nmem a) ∧
      (∀ x, x ≠ 140000 → c'.nreg x = c.nreg x) := by
  unfold cutStore
  exec_block
  all_goals first | (config_simp; rw [h00, h03]; omega) | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun x hx => ?_⟩
  all_goals ram_simp
  all_goals ram_simp

theorem cutK0_exec (h06 : c.nreg 140006 = 0)
    (hp : p + 2 ≤ W) :
    ∃ c' k, Exec P W cutK0 c c' k ∧ k = 4 ∧ c'.nreg 140000 = p + 2 ∧ c'.nmem p = 0 ∧
      c'.nmem (p + 1) = 0 ∧ (∀ a, a < p → c'.nmem a = c.nmem a) ∧
      (∀ x, x ≠ 140000 → c'.nreg x = c.nreg x) := by
  unfold cutK0
  exec_block
  all_goals first | (config_simp; rw [h00, h03]; omega) | skip
  refine ⟨rfl, ?_, ?_, ?_, fun a ha => ?_, fun x hx => ?_⟩
  all_goals ram_simp
  all_goals omega_nf


end

theorem cutK1_exec {p en : ℕ}
    (h00 : c.nreg 140000 = p) (h03 : c.nreg 140003 = 1) (h55 : c.nreg 150055 = en)
    (hen : en + 1 < p) (hp : p + 2 ≤ W) :
    ∃ c' k, Exec P W cutK1 c c' k ∧ k = 7 ∧ c'.nreg 140000 = p + 2 ∧
      c'.nmem p = c.nmem en ∧ c'.nmem (p + 1) = c.nmem (en + 1) ∧
      (∀ a, a < p → c'.nmem a = c.nmem a) ∧
      (∀ x, x ≠ 140000 → x ≠ 140004 → x ≠ 140005 → c'.nreg x = c.nreg x) := by
  unfold cutK1
  exec_block
  all_goals first | (config_simp; rw [h00, h03]; omega) | (config_simp; rw [h55, h03]; omega) |
    skip
  refine ⟨rfl, ?_, ?_, ?_, fun a ha => ?_, fun x h1 h2 h3 => ?_⟩
  all_goals ram_simp
  all_goals omega_nf

/-! ## The contract of `cutEmit` -/


end

variable {O : OracleIface} {P : Polygon} {C : Chain} {H : Host} {Hh h γ : ℕ} {m₀ : ℕ → ℕ}
  {A₀ W : ℕ}

/-- The grade-table entry of a kind-`1` piece lies below `A₀`. -/
theorem entry_lt (S : SEnv O P C H Hh h γ m₀ A₀ W) {pc : Pc} (hp : PcOK P C m₀ h γ pc)
    (hk : pc.kind = 1) : pc.entry + 2 < A₀ := by
  obtain ⟨g, b, -, hg, hb, hE, -⟩ := hp.2.2.2.2.2.2 hk
  rw [hE]
  exact (grade_entry S.hR hg hb).2.2

theorem recOK_append {m₀ mem mem' : ℕ → ℕ} {L : ℕ} {ps : List Pc} {pc : Pc}
    (hold : RecOK m₀ mem L ps) (hsame : ∀ a, a < L + 1 + 7 * ps.length → mem' a = mem a)
    (h0 : mem' (L + 1 + 7 * ps.length) = pc.s.edge)
    (h1 : mem' (L + 1 + 7 * ps.length + 1) = pc.s.hgt)
    (h2 : mem' (L + 1 + 7 * ps.length + 2) = pc.e.edge)
    (h3 : mem' (L + 1 + 7 * ps.length + 3) = pc.e.hgt)
    (h4 : mem' (L + 1 + 7 * ps.length + 4) = pc.kind)
    (h56 : pc.kind = 1 → mem' (L + 1 + 7 * ps.length + 5) = m₀ pc.entry ∧
      mem' (L + 1 + 7 * ps.length + 6) = m₀ (pc.entry + 1)) :
    RecOK m₀ mem' L (ps ++ [pc]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  rcases (show i < ps.length ∨ i = ps.length by omega) with hlt | rfl
  · rw [List.getElem_append_left hlt]
    obtain ⟨a0, a1, a2, a3, a4, a56⟩ := hold i hlt
    grind
  grind

/-- **The contract of the arc-cutter's `emit`.** -/
theorem cutEmit_ok (S : SEnv O P C H Hh h γ m₀ A₀ W) (Nmax : ℕ) :
    EmitOK P W cutEmit A₀ (PcOK P C m₀ h γ) (CutI W A₀ Nmax m₀) 30 := by
  refine ⟨fun ps c c' hI fr => ?_, fun ps pc c hw hI hR hv => ?_⟩
  · have k : ∀ r, Scr r = false → c'.nreg r = c.nreg r := fr.1
    have hmm : c'.nmem = c.nmem := fr.2.2.1
    exact ⟨by ram_grind, by ram_grind,
      by ram_grind, by ram_grind,
      by ram_grind, hI.limW, fun a ha => by ram_grind,
      by ram_grind, by ram_grind,
      by ram_grind⟩
  · obtain ⟨hA, hB, h1, h0, hL, hLW, hm, hp, hc, hrec⟩ := hI
    obtain ⟨r50, r51, r52, r53, r54, r55⟩ := hR
    have hkind := hv.2.2.2.2.1
    by_cases hlt : ps.length < Nmax
    · have hmin : min ps.length Nmax = ps.length := min_eq_left hlt.le
      rw [hmin] at hp hc
      have htake : ps.take Nmax = ps := List.take_of_length_le hlt.le
      rw [htake] at hrec
      set p := A₀ + 1 + 7 * ps.length with hpdef
      have t₀ : c.nreg 140000 < c.nreg 140007 := by omega
      obtain ⟨c₁, k₁, e₁, hk₁, q00, q0, q1, q2, q3, q4, qm, qr⟩ := cutStore_exec (P := P) c hw hp h1
        (by omega)
      have w₁ := e₁.wb_right
      have b03 : c₁.nreg 140003 = 1 := by grind
      -- the handles
      obtain ⟨c₂, k₂, e₂, hk₂, q20, q5, q6, qm₂, qr₂⟩ : ∃ c₂ k₂, Exec P W
          (.ifLtN 150054 140003 cutK0 cutK1) c₁ c₂ k₂ ∧ k₂ ≤ 9 ∧ c₂.nreg 140000 = p + 7 ∧
          (pc.kind = 1 → c₂.nmem (p + 5) = m₀ pc.entry ∧ c₂.nmem (p + 6) = m₀ (pc.entry + 1)) ∧
          True ∧ (∀ a, a < p + 5 → c₂.nmem a = c₁.nmem a) ∧
          (∀ x, x ≠ 140000 → x ≠ 140004 → x ≠ 140005 → c₂.nreg x = c₁.nreg x) := by
        rcases hkind with hk0 | hk1
        · have t : c₁.nreg 150054 < c₁.nreg 140003 := by
            grind
          obtain ⟨c₂, k₂, e₂, hk₂, a0, -, -, am, ar⟩ := cutK0_exec (P := P) c₁ w₁ q00 b03
            (by grind) (by omega)
          exact ⟨c₂, _, .ifLtN_true t e₂, by omega, by rw [a0],
            fun h => absurd (hk0.symm.trans h) (by decide), trivial, am, fun x h1 _ _ => ar x h1⟩
        · have t : ¬ c₁.nreg 150054 < c₁.nreg 140003 := by
            grind
          have he := entry_lt S hv hk1
          obtain ⟨c₂, k₂, e₂, hk₂, a0, a5, a6, am, ar⟩ := cutK1_exec (P := P)
            (en := pc.entry) c₁ w₁ q00 b03
            (by grind) (by omega) (by omega)
          refine ⟨c₂, _, .ifLtN_false t e₂, by omega, by rw [a0], fun _ => ⟨?_, ?_⟩, trivial,
            am, ar⟩
          · grind
          grind
      have w₂ := e₂.wb_right
      have b02 : c₂.nreg 140002 = ps.length := by
        grind
      have b03' : c₂.nreg 140003 = 1 := by grind
      have e₃ := Exec.addN (P := P) w₂ 140002 140002 140003 (by grind)
      set c₃ := ({ c₂ with nreg := upd c₂.nreg 140002 (c₂.nreg 140002 + c₂.nreg 140003) } :
        Config) with hc₃
      have g₃ : ∀ x, x ≠ 140000 → x ≠ 140002 → x ≠ 140004 → x ≠ 140005 →
          c₃.nreg x = c.nreg x := fun x h1 h2 h3 h4 => by
        ram_simp
      have mem3 : ∀ a, a < p → c₃.nmem a = c.nmem a := fun a ha => by
        grind
      refine ⟨c₃, _, .ifLtN_true t₀ (.seq e₁ (.seq e₂ e₃)), by omega, ⟨?_, ?_, ?_, ?_, ?_, hLW,
        fun a ha => by grind, ?_, ?_, ?_⟩, fun r hr => ?_,
        fun a ha => mem3 a (by omega)⟩
      · rw [g₃ _ (by decide) (by decide) (by decide) (by decide)]; exact hA
      · grind
      · grind
      · grind
      · grind
      · grind [upd, List.length_append, List.length_singleton]
      · ram_simp <;> omega_nf
      · rw [List.take_of_length_le (by simp; omega)]
        refine recOK_append hrec (fun a ha => mem3 a ha) ?_ ?_ ?_ ?_ ?_ ?_
        · grind
        · ram_simp
        · ram_simp
        · ram_simp
        all_goals grind
      · unfold Keep at hr
        exact g₃ r (by omega) (by omega) (by omega) (by omega)
    · have hmin : min ps.length Nmax = Nmax := min_eq_right (by omega)
      rw [hmin] at hp hc
      have t₀ : ¬ c.nreg 140000 < c.nreg 140007 := by omega
      refine ⟨c, _, .ifLtN_false t₀ (.skip hw), by omega, ⟨hA, hB, h1, h0, hL, hLW, hm, ?_, ?_, ?_⟩,
        fun _ _ => rfl, fun _ _ => rfl⟩
      all_goals grind

end

end ShootCut

end Chazelle.Core
