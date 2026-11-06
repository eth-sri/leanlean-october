module

public import Chazelle.Golf

public import Chazelle.Core.ShootCutShOrg
public import Chazelle.Core.ShootCutCutter2

/-!
# WP-G, part 56: the ray-shooter's piece records

The ray-shooter runs the core of the arc-cutter with `shEmit`, which writes the record of each
piece (nine words: the two ends, the kind, the grade-table entry, the first edge, the direction,
the length) at the pointer `140100`, from the list base `A₀ + 1` on; the pieces are shot at
afterwards, when the core is done (a query of a Lemma 3.6 structure may write the registers of
the core).  A guard `ptr < LIM` keeps the pointer below the word bound.

* `Rec9`: the records in memory; `ShI`: the invariant of `shEmit`; `shEmit_ok`: its contract;
* `shInit_exec`: the set-up (`LIM = A₀ + 1 + 18900 (t + 1)`, `2^t ≥ γ`);
* `shFin_exec`: the allocator raised to the end of the records.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc

@[expose] public section

/-! ## The programs -/

/-- The first five words of a piece. -/
def shStoreA : Stmt := block [.storeN 140100 150050, .addN 140100 140100 140103,
  .storeN 140100 150051, .addN 140100 140100 140103, .storeN 140100 150052,
  .addN 140100 140100 140103, .storeN 140100 150053, .addN 140100 140100 140103,
  .storeN 140100 150054, .addN 140100 140100 140103]

/-- The last four words of a piece. -/
def shStoreB : Stmt := block [.storeN 140100 150055,
  .addN 140100 140100 140103, .storeN 140100 150056, .addN 140100 140100 140103,
  .storeN 140100 150057, .addN 140100 140100 140103, .storeN 140100 150058,
  .addN 140100 140100 140103]

/-- The nine words of a piece. -/
def shStore : Stmt := .seq shStoreA shStoreB

/-- **The ray-shooter's `emit`**: the record of the piece, if there is room. -/
def shEmit : Stmt := .ifLtN 140100 140107 shStore .skip

/-- The doubling loop of the limit. -/
def shLimBody : Stmt := block [.addN 140109 140109 140109, .addN 140107 140107 140108]

/-- The constants of the set-up. -/
def shInitA : Stmt := block [.constN 140103 1, .constN 140108 18900, .constN 140109 1]

/-- The pointers of the set-up. -/
def shInitB : Stmt := block [.copyN 140101 ALLOC, .addN 140100 ALLOC 140103]

/-- The set-up of the records. -/
def shInit : Stmt :=
  .seq shInitA (.seq shInitB (.seq (.instr (.addN 140107 140100 140108))
    (.whileLtN 140109 150009 shLimBody)))

/-- Raise the allocator one by one to the end of the records. -/
def shFin : Stmt := .whileLtN ALLOC 140100 (.instr (.addN ALLOC ALLOC 140103))

/-! ## The records -/

/-- The records of the pieces `ps` from the list base `L + 1` on. -/
def Rec9 (mem : ℕ → ℕ) (L : ℕ) (ps : List Pc) : Prop :=
  ∀ i (hi : i < ps.length),
    mem (L + 1 + 9 * i) = (ps[i]'hi).s.edge ∧ mem (L + 1 + 9 * i + 1) = (ps[i]'hi).s.hgt ∧
    mem (L + 1 + 9 * i + 2) = (ps[i]'hi).e.edge ∧ mem (L + 1 + 9 * i + 3) = (ps[i]'hi).e.hgt ∧
    mem (L + 1 + 9 * i + 4) = (ps[i]'hi).kind ∧
    ((ps[i]'hi).kind = 1 → mem (L + 1 + 9 * i + 5) = (ps[i]'hi).entry ∧
      mem (L + 1 + 9 * i + 6) = (ps[i]'hi).x0 ∧ mem (L + 1 + 9 * i + 7) = (ps[i]'hi).dir ∧
      mem (L + 1 + 9 * i + 8) = (ps[i]'hi).pw)

/-- **The invariant of `shEmit`** (`Nmax` records fit below `LIM = A₀ + 1 + 9 Nmax`); the
registers `140000 … 140099` keep their values in `c₀`. -/
structure ShI (W A₀ Nmax : ℕ) (m₀ : ℕ → ℕ) (c₀ : Config) (ps : List Pc) (c : Config) : Prop where
  alloc : c.nreg ALLOC = A₀
  base : c.nreg 140101 = A₀
  one : c.nreg 140103 = 1
  lim : c.nreg 140107 = A₀ + 1 + 9 * Nmax
  limW : A₀ + 1 + 9 * Nmax + 9 ≤ W
  mem : ∀ a, a < A₀ → c.nmem a = m₀ a
  ptr : c.nreg 140100 = A₀ + 1 + 9 * min ps.length Nmax
  recs : Rec9 c.nmem A₀ (ps.take Nmax)
  keep : ∀ r, 140000 ≤ r → r < 140100 → c.nreg r = c₀.nreg r

theorem rec9_append {mem mem' : ℕ → ℕ} {L : ℕ} {ps : List Pc} {pc : Pc}
    (hold : Rec9 mem L ps) (hsame : ∀ a, a < L + 1 + 9 * ps.length → mem' a = mem a)
    (h0 : mem' (L + 1 + 9 * ps.length) = pc.s.edge)
    (h1 : mem' (L + 1 + 9 * ps.length + 1) = pc.s.hgt)
    (h2 : mem' (L + 1 + 9 * ps.length + 2) = pc.e.edge)
    (h3 : mem' (L + 1 + 9 * ps.length + 3) = pc.e.hgt)
    (h4 : mem' (L + 1 + 9 * ps.length + 4) = pc.kind)
    (h58 : pc.kind = 1 → mem' (L + 1 + 9 * ps.length + 5) = pc.entry ∧
      mem' (L + 1 + 9 * ps.length + 6) = pc.x0 ∧ mem' (L + 1 + 9 * ps.length + 7) = pc.dir ∧
      mem' (L + 1 + 9 * ps.length + 8) = pc.pw) :
    Rec9 mem' L (ps ++ [pc]) := by
  intro i hi
  ϴ' List.length_append, List.length_singleton at hi
  rcases (show i < ps.length ∨ i = ps.length by omega) with hlt | rfl
  · Ξ List.getElem_append_left hlt
    obtain ⟨a0, a1, a2, a3, a4, a58⟩ := hold i hlt
    refine ⟨by rw [hsame _ (⋄)]; exact a0, by rw [hsame _ (⋄)]; exact a1,
      by rw [hsame _ (⋄)]; exact a2, by rw [hsame _ (⋄)]; exact a3,
      by rw [hsame _ (⋄)]; exact a4, fun hk => ?_⟩
    obtain ⟨b5, b6, b7, b8⟩ := a58 hk
    exact ⟨by rw [hsame _ (⋄)]; exact b5, by rw [hsame _ (⋄)]; exact b6,
      by rw [hsame _ (⋄)]; exact b7, by rw [hsame _ (⋄)]; exact b8⟩
  · Ξ List.getElem_append_right (le_refl _)
    ϴ Nat.sub_self, List.getElem_cons_zero
    exact ⟨h0, h1, h2, h3, h4, h58⟩

/-! ## The contract of `shEmit` -/

theorem shStoreA_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {p : ℕ}
    (h00 : c.nreg 140100 = p) (h03 : c.nreg 140103 = 1) (hp : p + 9 ≤ W) :
    ∃ c' k, Exec P W shStoreA c c' k ∧ k = 10 ∧ c'.nreg 140100 = p + 5 ∧
      c'.nmem p = c.nreg 150050 ∧ c'.nmem (p + 1) = c.nreg 150051 ∧
      c'.nmem (p + 2) = c.nreg 150052 ∧ c'.nmem (p + 3) = c.nreg 150053 ∧
      c'.nmem (p + 4) = c.nreg 150054 ∧ (∀ a, a < p → c'.nmem a = c.nmem a) ∧
      (∀ x, x ≠ 140100 → c'.nreg x = c.nreg x) := by
  unfold shStoreA
  exec_block
  all_goals first | (config_simp; rw [h00, h03]; omega) | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun x hx => ?_⟩
  all_goals simp only [upd, Config.nreg_mk, Config.nmem_mk, h00, h03]
  all_goals first | (split_ifs <;> first | rfl | omega) | skip

theorem shStoreB_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {p : ℕ}
    (h00 : c.nreg 140100 = p) (h03 : c.nreg 140103 = 1) (hp : p + 4 ≤ W) :
    ∃ c' k, Exec P W shStoreB c c' k ∧ k = 8 ∧ c'.nreg 140100 = p + 4 ∧
      c'.nmem p = c.nreg 150055 ∧ c'.nmem (p + 1) = c.nreg 150056 ∧
      c'.nmem (p + 2) = c.nreg 150057 ∧ c'.nmem (p + 3) = c.nreg 150058 ∧
      (∀ a, a < p → c'.nmem a = c.nmem a) ∧
      (∀ x, x ≠ 140100 → c'.nreg x = c.nreg x) := by
  unfold shStoreB
  exec_block
  all_goals first | (config_simp; rw [h00, h03]; omega) | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun x hx => ?_⟩
  all_goals simp only [upd, Config.nreg_mk, Config.nmem_mk, h00, h03]
  all_goals first | (split_ifs <;> first | rfl | omega) | skip

theorem shStore_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {p : ℕ}
    (h00 : c.nreg 140100 = p) (h03 : c.nreg 140103 = 1) (hp : p + 9 ≤ W) :
    ∃ c' k, Exec P W shStore c c' k ∧ k = 18 ∧ c'.nreg 140100 = p + 9 ∧
      c'.nmem p = c.nreg 150050 ∧ c'.nmem (p + 1) = c.nreg 150051 ∧
      c'.nmem (p + 2) = c.nreg 150052 ∧ c'.nmem (p + 3) = c.nreg 150053 ∧
      c'.nmem (p + 4) = c.nreg 150054 ∧ c'.nmem (p + 5) = c.nreg 150055 ∧
      c'.nmem (p + 6) = c.nreg 150056 ∧ c'.nmem (p + 7) = c.nreg 150057 ∧
      c'.nmem (p + 8) = c.nreg 150058 ∧ (∀ a, a < p → c'.nmem a = c.nmem a) ∧
      (∀ x, x ≠ 140100 → c'.nreg x = c.nreg x) := by
  obtain ⟨c₁, k₁, e₁, hk₁, q00, q0, q1, q2, q3, q4, qm, qr⟩ := shStoreA_exec (P := P) c hw h00 h03 hp
  obtain ⟨c₂, k₂, e₂, hk₂, u00, u5, u6, u7, u8, um, ur⟩ := shStoreB_exec (P := P) c₁ e₁.wb_right
    q00 (by rw [qr _ (by omega), h03]) (by omega)
  refine ⟨c₂, _, .seq e₁ e₂, by omega, by rw [u00], by rw [um _ (by omega), q0],
    by rw [um _ (by omega), q1], by rw [um _ (by omega), q2], by rw [um _ (by omega), q3],
    by rw [um _ (by omega), q4], by rw [u5, qr _ (by omega)], ?_, ?_, ?_,
    fun a ha => by rw [um _ (by omega), qm _ ha], fun x hx => by rw [ur x hx, qr x hx]⟩
  · rw [show p + 6 = p + 5 + 1 by omega, u6, qr _ (by omega)]
  · rw [show p + 7 = p + 5 + 2 by omega, u7, qr _ (by omega)]
  · rw [show p + 8 = p + 5 + 3 by omega, u8, qr _ (by omega)]

/-- **The contract of the ray-shooter's `emit`.** -/
theorem shEmit_ok {P : Polygon} {W A₀ : ℕ} {m₀ : ℕ → ℕ} {c₀ : Config} (Pv : Pc → Prop)
    (Nmax : ℕ) : EmitOK P W shEmit A₀ Pv (ShI W A₀ Nmax m₀ c₀) 30 := by
  refine ⟨fun ps c c' hI fr => ?_, fun ps pc c hw hI hR hv => ?_⟩
  · have k : ∀ r, Scr r = false → c'.nreg r = c.nreg r := fr.1
    have hmm : c'.nmem = c.nmem := fr.2.2.1
    exact ⟨by rw [k ALLOC (by decide)]; exact hI.alloc, by rw [k _ (by decide)]; exact hI.base,
      by rw [k _ (by decide)]; exact hI.one, by rw [k _ (by decide)]; exact hI.lim, hI.limW,
      fun a ha => by rw [hmm]; exact hI.mem a ha, by rw [k _ (by decide)]; exact hI.ptr,
      by rw [hmm]; exact hI.recs,
      fun r h1 h2 => by rw [k r (by unfold Scr; simp; omega)]; exact hI.keep r h1 h2⟩
  · obtain ⟨hA, hB, h1, hL, hLW, hm, hp, hrec, hkeep⟩ := hI
    obtain ⟨r50, r51, r52, r53, r54, r55⟩ := hR
    by_cases hlt : ps.length < Nmax
    · have hmin : min ps.length Nmax = ps.length := min_eq_left hlt.le
      rw [hmin] at hp
      have htake : ps.take Nmax = ps := List.take_of_length_le hlt.le
      rw [htake] at hrec
      set p := A₀ + 1 + 9 * ps.length with hpdef
      have t₀ : c.nreg 140100 < c.nreg 140107 := by rw [hp, hL]; omega
      obtain ⟨c₁, k₁, e₁, hk₁, q00, q0, q1, q2, q3, q4, q5, q6, q7, q8, qm, qr⟩ :=
        shStore_exec (P := P) c hw hp h1 (by omega)
      have ex : Exec P W shEmit c c₁ (k₁ + 1) := .ifLtN_true t₀ e₁
      refine ⟨c₁, _, ex, by omega, ⟨?_, ?_, ?_, ?_, hLW,
        fun a ha => by rw [qm a (by omega)]; exact hm a ha, ?_, ?_,
        fun r a b => by rw [qr r (by omega)]; exact hkeep r a b⟩, fun r hr => ?_,
        fun a ha => qm a (by omega)⟩
      · rw [qr _ (by decide)]; exact hA
      · rw [qr _ (by omega)]; exact hB
      · rw [qr _ (by omega)]; exact h1
      · rw [qr _ (by omega)]; exact hL
      · rw [q00, List.length_append, List.length_singleton, min_eq_left (by omega)]
        omega
      · rw [List.take_of_length_le (by simp; omega)]
        refine rec9_append hrec (fun a ha => qm a ha) ?_ ?_ ?_ ?_ ?_ ?_
        · rw [q0, r50]
        · rw [q1, r51]
        · rw [q2, r52]
        · rw [q3, r53]
        · rw [q4, r54]
        · intro hk
          obtain ⟨b5, b6, b7, b8⟩ := r55 hk
          exact ⟨by rw [q5, b5], by rw [q6, b6], by rw [q7, b7], by rw [q8, b8]⟩
      · unfold Keep at hr
        exact qr r (by omega)
    · have hmin : min ps.length Nmax = Nmax := min_eq_right (by omega)
      rw [hmin] at hp
      have t₀ : ¬ c.nreg 140100 < c.nreg 140107 := by rw [hp, hL]; omega
      refine ⟨c, _, .ifLtN_false t₀ (.skip hw), by omega, ⟨hA, hB, h1, hL, hLW, hm, ?_, ?_,
        hkeep⟩, fun _ _ => rfl, fun _ _ => rfl⟩
      · rw [hp, List.length_append, List.length_singleton, min_eq_right (by omega)]
      · rw [List.take_append_of_le_length (by omega)]; exact hrec

/-! ## The set-up and the finish -/

/-- **The set-up of the records.** -/
theorem shInit_exec {P : Polygon} {W : ℕ} (d : Config) (hw : WordsBounded W d) {γ A₀ : ℕ}
    {m₀ : ℕ → ℕ} (hm : ∀ a, a < A₀ → d.nmem a = m₀ a) (h09 : d.nreg 150009 = γ)
    (hA : d.nreg ALLOC = A₀) (hγW : 2 * γ ≤ W)
    (hroom : A₀ + 18900 * Nat.clog 2 γ + 18910 ≤ W) :
    ∃ d' k Nmax, Exec P W shInit d d' k ∧ k ≤ 5 * Nat.clog 2 γ + 20 ∧
      ShI W A₀ Nmax m₀ d [] d' ∧ 2100 * Nat.log 2 γ + 2100 ≤ Nmax ∧
      (∀ x, ¬ (140100 ≤ x ∧ x < 140110) → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  have hAl : ALLOC = 9999 := rfl
  have hW1 : A₀ + 18910 ≤ W := by omega
  obtain ⟨da, ka, ea, hka, a03, a08, a09, ra, ma⟩ : ∃ d₁ k₁, Exec P W shInitA d d₁ k₁ ∧
      k₁ = 3 ∧ d₁.nreg 140103 = 1 ∧ d₁.nreg 140108 = 18900 ∧ d₁.nreg 140109 = 1 ∧
      (∀ x, ¬ (140100 ≤ x ∧ x < 140110) → d₁.nreg x = d.nreg x) ∧ d₁ = { d with nreg := d₁.nreg } := by
    clear hroom hγW hm hA h09
    unfold shInitA
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl⟩
    all_goals first | (config_simp; done) | skip
    simp only [upd]; split_ifs <;> first | rfl | omega
  have hAa : da.nreg 9999 = A₀ := by rw [ra _ (by omega)]; exact hA
  obtain ⟨db, kb, eb, hkb, b01, b00, rb, mb⟩ : ∃ d₁ k₁, Exec P W shInitB da d₁ k₁ ∧
      k₁ = 2 ∧ d₁.nreg 140101 = A₀ ∧ d₁.nreg 140100 = A₀ + 1 ∧
      (∀ x, x ≠ 140101 → x ≠ 140100 → d₁.nreg x = da.nreg x) ∧ d₁ = { da with nreg := d₁.nreg } := by
    have ew := ea.wb_right
    clear hroom hγW hm hA h09 ea ra
    unfold shInitB
    rw [hAl]
    exec_block
    all_goals first | (config_simp; rw [hAa, a03]; omega) | skip
    refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl⟩
    · config_simp; exact hAa
    · config_simp; rw [hAa, a03]
    · simp only [upd]; split_ifs <;> first | rfl | omega
  have b03 : db.nreg 140103 = 1 := by rw [rb _ (by omega) (by omega), a03]
  have b08 : db.nreg 140108 = 18900 := by rw [rb _ (by omega) (by omega), a08]
  have ec := Exec.addN (P := P) eb.wb_right 140107 140100 140108 (by rw [b00, b08]; omega)
  set d₁ := ({ db with nreg := upd db.nreg 140107 (db.nreg 140100 + db.nreg 140108) } : Config)
    with hd₁
  have r₁ : ∀ x, ¬ (140100 ≤ x ∧ x < 140110) → d₁.nreg x = d.nreg x := fun x hx => by
    simp only [hd₁, upd]
    rw [ite_eq_right (by omega), rb x (by omega) (by omega), ra x hx]
  have g₁ : ∀ x, x ≠ 140107 → d₁.nreg x = db.nreg x := fun x hx => by
    simp only [hd₁, upd]; rw [ite_eq_right hx]
  have o03 : d₁.nreg 140103 = 1 := by rw [g₁ _ (by omega)]; exact b03
  have o08 : d₁.nreg 140108 = 18900 := by rw [g₁ _ (by omega)]; exact b08
  have o01 : d₁.nreg 140101 = A₀ := by rw [g₁ _ (by omega)]; exact b01
  have o00 : d₁.nreg 140100 = A₀ + 1 := by rw [g₁ _ (by omega)]; exact b00
  have o09 : d₁.nreg 140109 = 1 := by rw [g₁ _ (by omega), rb _ (by omega) (by omega)]; exact a09
  have o07 : d₁.nreg 140107 = A₀ + 1 + 18900 := by
    simp only [hd₁, upd, ↓reduceIte]; rw [b00, b08]
  have m₁ : d₁ = { d with nreg := d₁.nreg } := by
    show ({ db with nreg := _ } : Config) = _
    rw [mb, ma]
  -- the doubling loop
  obtain ⟨T, hT⟩ : ∃ T, Nat.clog 2 γ = T := ⟨_, rfl⟩
  rw [hT] at hroom
  let Inv : Config → Prop := fun c => WordsBounded W c ∧ c = { d with nreg := c.nreg } ∧
    (∀ x, ¬ (140100 ≤ x ∧ x < 140110) → c.nreg x = d.nreg x) ∧ c.nreg 140103 = 1 ∧
    c.nreg 140108 = 18900 ∧ c.nreg 140101 = A₀ ∧ c.nreg 140100 = A₀ + 1 ∧
    ∃ t, c.nreg 140109 = 2 ^ t ∧ c.nreg 140107 = A₀ + 1 + (18900 * t + 18900) ∧ t ≤ T
  have I₁ : Inv d₁ := ⟨ec.wb_right, m₁, r₁, o03, o08, o01, o00, 0, by rw [o09, pow_zero],
    by rw [o07], Nat.zero_le _⟩
  obtain ⟨d₂, k₂, e₂, I₂, hx₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (a := 140109) (b := 150009)
    (body := shLimBody) Inv
    (fun c => T + 1 - (Nat.log 2 (c.nreg 140109))) 2 (fun c hc => hc.1)
    (fun c ⟨hw', hm', hr', h3, h8, h1, h0, t, h9, h7, ht⟩ hlt => by
      have g9 : c.nreg 150009 = γ := by rw [hr' _ (by omega), h09]
      rw [h9, g9] at hlt
      have htc : t < T := by rw [← hT]; exact (Nat.lt_clog_iff_pow_lt (by norm_num)).2 hlt
      have hmul := Nat.mul_le_mul_left 18900 (show t + 1 ≤ T from htc)
      have hW7 : A₀ + 1 + (18900 * t + 18900) + 18900 ≤ W := by
        rw [Nat.mul_succ] at hmul; omega
      unfold shLimBody
      obtain ⟨c', k, e, hk, o9, o7, r', m'⟩ : ∃ c' k, Exec P W (block [.addN 140109 140109 140109,
          .addN 140107 140107 140108]) c c' k ∧ k = 2 ∧ c'.nreg 140109 = 2 ^ (t + 1) ∧
          c'.nreg 140107 = A₀ + 1 + (18900 * t + 18900) + 18900 ∧
          (∀ x, x ≠ 140109 → x ≠ 140107 → c'.nreg x = c.nreg x) ∧
          c' = { c with nreg := c'.nreg } := by
        have h2W : 2 ^ t + 2 ^ t ≤ W := by omega
        clear hroom hγW hm hmul hlt
        exec_block
        all_goals first | (config_simp; rw [h9]; omega) | (config_simp; rw [h7, h8]; omega) |
          skip
        refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl⟩
        · config_simp; rw [h9, pow_succ]; ring
        · config_simp; rw [h7, h8]
        · simp only [upd]; split_ifs <;> first | rfl | omega
      refine ⟨c', k, e, ⟨e.wb_right, by rw [m', hm'], fun x hx => by
        rw [r' x (by omega) (by omega), hr' x hx], by rw [r' _ (by omega) (by omega), h3],
        by rw [r' _ (by omega) (by omega), h8], by rw [r' _ (by omega) (by omega), h1],
        by rw [r' _ (by omega) (by omega), h0], t + 1, o9, by rw [o7]; ring, by omega⟩,
        by omega, ?_⟩
      rw [o9, h9, Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)]
      omega) I₁
  obtain ⟨hw₂, hm₂, hr₂, h3, h8, h1, h0, t, h9, h7, ht⟩ := I₂
  have g9 : d₂.nreg 150009 = γ := by rw [hr₂ _ (by omega), h09]
  rw [h9, g9] at hx₂
  have hlog : Nat.log 2 γ ≤ t := by
    rcases Nat.eq_zero_or_pos γ with h0' | hpos
    · rw [h0']; simp
    · have := Nat.log_lt_of_lt_pow (b := 2) (x := t + 1) (y := γ) (by omega)
        (by rw [pow_succ]; omega)
      omega
  have hmul := Nat.mul_le_mul_left 18900 ht
  have hlog' := Nat.mul_le_mul_left 2100 hlog
  have hmem : d₂.nmem = d.nmem := by rw [hm₂]
  refine ⟨d₂, ka + (kb + (1 + k₂)), 2100 * t + 2100, .seq ea (.seq eb (.seq ec e₂)), ?_,
    ⟨by rw [hr₂ _ (by rw [hAl]; omega)]; exact hA, h1, h3, by rw [h7]; ring, by linarith,
    fun a ha => by rw [hmem]; exact hm a ha,
    by rw [h0, List.length_nil, Nat.zero_min, Nat.mul_zero, Nat.add_zero],
    fun i hi => by simp at hi, fun r h1 h2 => hr₂ r (by omega)⟩, by omega, hr₂, hmem,
    by rw [hm₂], by rw [hm₂], by rw [hm₂]⟩
  have hl1 : Nat.log 2 (d₁.nreg 140109) = 0 := by rw [o09]; exact Nat.log_one_right 2
  rw [hl1] at hk₂
  rw [hT]
  omega

/-- **The finish**: the allocator raised to the end of the records. -/
theorem shFin_exec {P : Polygon} {W A₀ Nmax : ℕ} {m₀ : ℕ → ℕ} {c₀ : Config} {ps : List Pc}
    (d : Config) (hw : WordsBounded W d) (hI : ShI W A₀ Nmax m₀ c₀ ps d)
    (hq : ps.length ≤ Nmax) :
    ∃ d' k, Exec P W shFin d d' k ∧ k ≤ 3 * (1 + 9 * ps.length) + 2 ∧
      d'.nreg ALLOC = A₀ + 1 + 9 * ps.length ∧ d'.nreg ALLOC ≤ d.nreg ALLOC + k ∧
      (∀ x, x ≠ ALLOC → d'.nreg x = d.nreg x) ∧ d' = { d with nreg := d'.nreg } := by
  have hAl : ALLOC = 9999 := rfl
  obtain ⟨hA, -, h1, -, hLW, -, hp, -, -⟩ := hI
  Ξ' min_eq_left hq at hp
  set E := A₀ + 1 + 9 * ps.length with hE
  let Inv : Config → Prop := fun c => WordsBounded W c ∧ c.nreg ALLOC ≤ E ∧
    (∀ x, x ≠ ALLOC → c.nreg x = d.nreg x) ∧ c = { d with nreg := c.nreg }
  obtain ⟨d₂, k₂, e₂, ⟨hw₂, hA₂, hr₂, hm₂⟩, hx₂, hk₂, hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := ALLOC) (b := 140100)
    (body := .instr (.addN ALLOC ALLOC 140103)) Inv (fun c => 3 * (E - c.nreg ALLOC))
    (fun c => c.nreg ALLOC) (fun c h => h.1)
    (fun c ⟨hw', hA', hr', hm'⟩ ht => by
      have e3 : c.nreg 140103 = 1 := Ρ hr' _ (by rw [hAl]; omega), h1
      have e0 : c.nreg 140100 = E := Ρ hr' _ (by rw [hAl]; omega), hp
      Ξ' e0 at ht
      have ex := Exec.addN (P := P) hw' ALLOC ALLOC 140103 (by rw [e3]; omega)
      refine ⟨_, 1, ex, ⟨ex.wb_right, ?_, fun x hx => ?_, ?_⟩, ?_, ?_⟩
      · simp only [Config.nreg_mk, Machine.upd_same]; rw [e3]; omega
      · simp only [Config.nreg_mk]; rw [Machine.upd_other _ _ _ hx]; exact hr' x hx
      · Ξ hm'
      · simp only [Config.nreg_mk, Machine.upd_same]; rw [e3]; omega
      · simp only [Config.nreg_mk, Machine.upd_same]; rw [e3])
    ⟨hw, by rw [hA]; omega, fun _ _ => rfl, rfl⟩
  have e0 : d₂.nreg 140100 = E := Ρ hr₂ _ (by rw [hAl]; omega), hp
  Ξ' e0 at hx₂
  refine ⟨d₂, k₂, e₂, ?_, ⋄, ⋄, hr₂, hm₂⟩
  Ξ' hA at hk₂; omega

end

end ShootCut

end Chazelle.Core
