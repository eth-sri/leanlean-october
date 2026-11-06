module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvRPlB

/-!
# Down-phase driver (RAM side): the leaf planner, part 3 (the item loop)

**`plS`**: for the host `H` at the handle `r219000` (`HostAt`) and the chunk size `C = r219002`,
the table of the leaves `hostLeaves n C 0 H` (three words each) at the entry allocator (handle
`r219003`, count `r219004`); the allocator ends past the table (`plS_exec`).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs BuildRam

@[expose] public section

/-- One host item at the address `r219008`. -/
def plItem : Stmt :=
  .seq (block [.loadN 219009 219008, .addN 219021 219008 219018, .loadN 219010 219021,
      .addN 219021 219021 219018, .loadN 219011 219021])
    (.seq (.ifLtN 219009 219018
        (.seq plRun (block [.addN 219007 219007 219011, .addN 219007 219007 219018]))
        (block [.addN 219007 219007 219018]))
      (block [.addN 219008 219008 219020, .addN 219005 219005 219018]))

/-- The constants and the loop state. -/
def plInit : Stmt :=
  block [.inputSize 219001, .constN 219017 0, .constN 219018 1, .constN 219019 2,
    .constN 219020 3, .subN 219026 219001 219018, .constN 219004 0, .copyN 219003 9999,
    .copyN 219016 9999, .constN 219005 0, .loadN 219006 219000, .addN 219008 219000 219018,
    .constN 219007 0]

/-- **The leaf planner.** -/
def plS : Stmt := .seq plInit (.seq (.whileLtN 219005 219006 plItem) (.instr (.copyN 9999 219016)))

/-- The registers `plItem` writes. -/
def Bitem (r : ℕ) : Bool := Brun r || decide (r = 219005) || decide (219007 ≤ r ∧ r ≤ 219011)

/-- The words of a host item at `addr` (`HostAt`'s encoding). -/
def ItemWords (m : ℕ → ℕ) (addr : ℕ) : HostItem → Prop
  | .run a ℓ => m addr = 0 ∧ m (addr + 1) = a ∧ m (addr + 2) = ℓ
  | .pt (.vtx _) => m addr = 1
  | .pt (.onEdge _ _) => m addr = 2

/-- The run items are in range. -/
def ItemOK (n : ℕ) : HostItem → Prop
  | .run a ℓ => a < n ∧ ℓ < n
  | .pt _ => True

/-- The registers `plS` writes. -/
def Bpl (r : ℕ) : Bool := decide (219001 ≤ r ∧ r ≤ 219029) || decide (r = 9999)

theorem wrM2_plS : wrM2 Bpl (fun _ => false) plS = true := by decide

theorem hostLeaves_take_succ (n C : ℕ) (H : Host) {i : ℕ} (hi : i < H.length) :
    hostLeaves n C 0 (H.take (i + 1)) = hostLeaves n C 0 (H.take i) ++
      itemLeaves n C (Host.pts n (H.take i)).length (H.getD i (.run 0 0)) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, hostLeaves_append,
    hostLeaves_single, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]

theorem pts_take_succ (n : ℕ) (H : Host) {i : ℕ} (hi : i < H.length) :
    (Host.pts n (H.take (i + 1))).length = (Host.pts n (H.take i)).length +
      ((H.getD i (.run 0 0)).pts n).length := by
  grind [List.take_add_one, Option.toList_some, DownMath.pts_append, List.length_append, List.getD_eq_getElem?_getD, Option.getD_some, Host.pts]

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **One host item.** -/
theorem plItem_exec {n C : ℕ} (hC : 1 ≤ C) (hn : 2 ≤ n) (d : Config) (hw : WordsBounded W d)
    (hK : PlConst n C d) {it : HostItem} {i p k ptr addr : ℕ} (h05 : d.nreg 219005 = i)
    (h08 : d.nreg 219008 = addr) (h07 : d.nreg 219007 = p) (h16 : d.nreg 219016 = ptr)
    (h04 : d.nreg 219004 = k)
    (hit : ItemWords d.nmem addr it) (hwf : ItemOK n it)
    (hWa : addr + 3 ≤ W) (hWi : i + 1 ≤ W) (hWp : p + n + n + 1 ≤ W)
    (hWt : ptr + 3 * (itemLeaves n C p it).length ≤ W)
    (hWk : k + (itemLeaves n C p it).length ≤ W) :
    ∃ d' j, Exec P W plItem d d' j ∧ j ≤ 15 * (itemLeaves n C p it).length + 60 ∧
      d'.nreg 219005 = i + 1 ∧ d'.nreg 219008 = addr + 3 ∧
      d'.nreg 219007 = p + (it.pts n).length ∧
      d'.nreg 219016 = ptr + 3 * (itemLeaves n C p it).length ∧
      d'.nreg 219004 = k + (itemLeaves n C p it).length ∧
      ChordListAt d'.nmem ptr (itemLeaves n C p it) ∧
      (∀ x, (x < ptr ∨ ptr + 3 * (itemLeaves n C p it).length ≤ x) → d'.nmem x = d.nmem x) ∧
      FrameM Bitem d d' := by
  -- the item's words
  obtain ⟨d₁, j₁, e₁, hj₁, v09, v10, v11, m₁⟩ : ∃ d₁ j₁, Exec P W
      (block [.loadN 219009 219008, .addN 219021 219008 219018, .loadN 219010 219021,
        .addN 219021 219021 219018, .loadN 219011 219021]) d d₁ j₁ ∧ j₁ = 5 ∧
      d₁.nreg 219009 = d.nmem addr ∧ d₁.nreg 219010 = d.nmem (addr + 1) ∧
      d₁.nreg 219011 = d.nmem (addr + 2) ∧ d₁.nmem = d.nmem := by
    have q18 := hK.r18
    exec_block
    all_goals try (config_simp; (try simp only [h08, q18]); omega)
    refine ⟨rfl, ?_, ?_, ?_, rfl⟩ <;> config_simp <;> (try simp only [h08, q18])
  have fr₁ := exec_frameM e₁ (by decide : wrM (fun r => decide (219009 ≤ r ∧ r ≤ 219011) ||
    decide (r = 219021)) (block [.loadN 219009 219008, .addN 219021 219008 219018,
      .loadN 219010 219021, .addN 219021 219021 219018, .loadN 219011 219021]) = true)
  have g₁ : ∀ r, ¬ (219009 ≤ r ∧ r ≤ 219011) → r ≠ 219021 → d₁.nreg r = d.nreg r :=
    fun r h1 h2 => fr₁.1 r (by simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  have w₁ := e₁.wb_right
  have kK : PlConst n C d₁ := hK.keep fun r hr => g₁ r (by omega) (by omega)
  have k07 : d₁.nreg 219007 = p := by rw [g₁ _ (by omega) (by omega), h07]
  have k16 : d₁.nreg 219016 = ptr := by rw [g₁ _ (by omega) (by omega), h16]
  have k04 : d₁.nreg 219004 = k := by rw [g₁ _ (by omega) (by omega), h04]
  have k05 : d₁.nreg 219005 = i := by rw [g₁ _ (by omega) (by omega), h05]
  have k08 : d₁.nreg 219008 = addr := by rw [g₁ _ (by omega) (by omega), h08]
  have hf₁ : FrameM Bitem d d₁ := exec_frameM e₁ (by decide)
  -- the tail: next address and index
  have tail : ∀ (d₂ : Config) (j₂ : ℕ), Exec P W
      (.ifLtN 219009 219018
        (.seq plRun (block [.addN 219007 219007 219011, .addN 219007 219007 219018]))
        (block [.addN 219007 219007 219018])) d₁ d₂ j₂ →
      d₂.nreg 219005 = i → d₂.nreg 219008 = addr → d₂.nreg 219018 = 1 → d₂.nreg 219020 = 3 →
      ∃ d₃, Exec P W (block [.addN 219008 219008 219020, .addN 219005 219005 219018]) d₂ d₃ 2 ∧
        d₃.nreg 219005 = i + 1 ∧ d₃.nreg 219008 = addr + 3 ∧
        (∀ r, r ≠ 219005 → r ≠ 219008 → d₃.nreg r = d₂.nreg r) ∧ d₃.nmem = d₂.nmem ∧
        FrameM Bitem d₂ d₃ := by
    intro d₂ j₂ e₂ a05 a08 a18 a20
    have w₂ := e₂.wb_right
    obtain ⟨d₃, j₃, e₃, hj₃, b05, b08, gb, mb⟩ : ∃ d₃ j₃, Exec P W
        (block [.addN 219008 219008 219020, .addN 219005 219005 219018]) d₂ d₃ j₃ ∧ j₃ = 2 ∧
        d₃.nreg 219005 = i + 1 ∧ d₃.nreg 219008 = addr + 3 ∧
        (∀ r, r ≠ 219005 → r ≠ 219008 → d₃.nreg r = d₂.nreg r) ∧ d₃.nmem = d₂.nmem := by
      exec_block
      all_goals try (config_simp; (try simp only [a05, a08, a18, a20]); omega)
      refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl⟩ <;> config_simp <;>
        (try simp only [a05, a08, a18, a20])
      first | rfl | (simp only [Machine.upd_apply]; split_ifs <;> first | rfl | omega)
    subst hj₃
    exact ⟨d₃, e₃, b05, b08, gb, mb, exec_frameM e₃ (by decide)⟩
  cases it with
  | run a ℓ =>
    obtain ⟨hk0, ha, hl⟩ := hit
    obtain ⟨han, hln⟩ := hwf
    simp only [itemLeaves] at hWt hWk ⊢
    have kK10 : d₁.nreg 219010 = a := by rw [v10, ha]
    have kK11 : d₁.nreg 219011 = ℓ := by rw [v11, hl]
    obtain ⟨d₂, j₂, e₂, hj₂, c16, c04, cL, cm, cf⟩ := plRun_exec (P := P) hC hn d₁ w₁ kK kK10
      kK11 k07 k16 k04 han hln (by omega) hWt hWk
    have g₂ : ∀ r, Brun r = false → d₂.nreg r = d₁.nreg r := cf.1
    have kK₂ : PlConst n C d₂ := kK.keep fun r hr => g₂ r (brun_const hr)
    have t07 : d₂.nreg 219007 = p := by rw [g₂ _ (by decide), k07]
    have t11 : d₂.nreg 219011 = ℓ := by rw [g₂ _ (by decide), kK11]
    -- `p := p + ℓ + 1`
    obtain ⟨d₃, j₃, e₃, hj₃, s07, gs, ms⟩ : ∃ d₃ j₃, Exec P W
        (block [.addN 219007 219007 219011, .addN 219007 219007 219018]) d₂ d₃ j₃ ∧ j₃ = 2 ∧
        d₃.nreg 219007 = p + (ℓ + 1) ∧ (∀ r, r ≠ 219007 → d₃.nreg r = d₂.nreg r) ∧
        d₃.nmem = d₂.nmem := by
      have q18 := kK₂.r18
      have e := e₂.wb_right
      exec_block
      all_goals try (config_simp; omega)
      refine ⟨rfl, ?_, fun r h1 => ?_, rfl⟩ <;> config_simp <;> (try simp only [t07, t11, q18])
      · omega
      · first | rfl | (simp only [Machine.upd_apply]; split_ifs <;> first | rfl | omega)
    have ex₂ : Exec P W (.ifLtN 219009 219018
        (.seq plRun (block [.addN 219007 219007 219011, .addN 219007 219007 219018]))
        (block [.addN 219007 219007 219018])) d₁ d₃ (j₂ + j₃ + 1) :=
      .ifLtN_true (by rw [v09, hk0, kK.r18]; omega) (.seq e₂ e₃)
    obtain ⟨d₄, e₄, b05, b08, gb, mb, fb⟩ := tail d₃ _ ex₂
      (by rw [gs _ (by decide), g₂ _ (by decide), k05])
      (by rw [gs _ (by decide), g₂ _ (by decide), k08])
      (by rw [gs _ (by decide), kK₂.r18]) (by rw [gs _ (by decide), kK₂.r20])
    refine ⟨d₄, j₁ + ((j₂ + j₃ + 1) + 2), .seq e₁ (.seq ex₂ e₄), by omega, b05, b08, ?_, ?_, ?_, ?_,
      fun x hx => ?_, ?_⟩
    · rw [gb _ (by decide) (by decide), s07, DownMath.run_pts_length]
    · rw [gb _ (by decide) (by decide), gs _ (by decide), c16]
    · rw [gb _ (by decide) (by decide), gs _ (by decide), c04]
    · rw [mb, ms]; exact cL
    · rw [mb, ms, cm x hx, m₁]
    · have f₃ : FrameM Bitem d₂ d₃ := exec_frameM e₃ (by decide)
      have up : FrameM Bitem d₁ d₂ :=
        ⟨fun r hr => cf.1 r (by simp only [Bitem, Bool.or_eq_false_iff] at hr; exact hr.1.1),
          fun r hr => cf.2.1 r (by simp only [Bitem, Bool.or_eq_false_iff] at hr; exact hr.1.1),
          cf.2.2.1, cf.2.2.2⟩
      exact hf₁.trans (up.trans (f₃.trans fb))
  | pt x =>
    have hk1 : ¬ d₁.nreg 219009 < d₁.nreg 219018 := by
      rw [v09, kK.r18]
      cases x with
      | vtx j => have h1 : d.nmem addr = 1 := hit; omega
      | onEdge e h => have h1 : d.nmem addr = 2 := hit; omega
    simp only [itemLeaves, List.length_nil, Nat.mul_zero, Nat.add_zero] at hWt hWk ⊢
    obtain ⟨d₂, j₂, e₂, hj₂, s07, gs, ms⟩ : ∃ d₂ j₂, Exec P W
        (block [.addN 219007 219007 219018]) d₁ d₂ j₂ ∧ j₂ = 1 ∧
        d₂.nreg 219007 = p + 1 ∧ (∀ r, r ≠ 219007 → d₂.nreg r = d₁.nreg r) ∧
        d₂.nmem = d₁.nmem := by
      have q18 := kK.r18
      exec_block
      all_goals try (config_simp; (try simp only [k07, q18]); omega)
      refine ⟨rfl, ?_, fun r h1 => ?_, rfl⟩ <;> config_simp <;> (try simp only [k07, q18])
      first | rfl | (simp only [Machine.upd_apply]; split_ifs <;> first | rfl | omega)
    have ex₂ : Exec P W (.ifLtN 219009 219018
        (.seq plRun (block [.addN 219007 219007 219011, .addN 219007 219007 219018]))
        (block [.addN 219007 219007 219018])) d₁ d₂ (j₂ + 2) := .ifLtN_false hk1 e₂
    obtain ⟨d₄, e₄, b05, b08, gb, mb, fb⟩ := tail d₂ _ ex₂
      (by rw [gs _ (by decide), k05]) (by rw [gs _ (by decide), k08])
      (by rw [gs _ (by decide), kK.r18]) (by rw [gs _ (by decide), kK.r20])
    refine ⟨d₄, j₁ + ((j₂ + 2) + 2), .seq e₁ (.seq ex₂ e₄), by omega, b05, b08, ?_, ?_, ?_,
      fun i hi => by simp at hi, fun y _ => by rw [mb, ms, m₁], ?_⟩
    · rw [gb _ (by decide) (by decide), s07]; rfl
    · rw [gb _ (by decide) (by decide), gs _ (by decide), k16]
    · rw [gb _ (by decide) (by decide), gs _ (by decide), k04]
    · exact hf₁.trans ((exec_frameM e₂ (by decide)).trans fb)

end exec

end

end DrvR

end Chazelle.Core
