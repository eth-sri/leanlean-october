module

public import Chazelle.MacT
public import Chazelle.Core.NFBuildRegFill
public import Mathlib.Data.List.GetD
public import Chazelle.Core.NFBuildArcs
public import Chazelle.Core.DownPhaseDrvRExtSpec
public import Chazelle.Core.Lemma41Cover
public import Chazelle.Core.DownPhaseDrvBCtx
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.SpecNF
public import Chazelle.Core.DownPhaseTransWt
public import Chazelle.Core.BruteRam3
public import Chazelle.Core.DownPhaseDrvBFar1

namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs BuildRam
@[expose] public section
def itemLeaves (n C p : ℕ) : HostItem → List zte
  | .run a ℓ => runLeaves n C p a ℓ
  | .pt _ => []
theorem hostLeaves_append (n C : ℕ) : ∀ (H₁ H₂ : Host) (p : ℕ),
    hostLeaves n C p (H₁ ++ H₂) = hostLeaves n C p H₁ ++ hostLeaves n C ztoeb H₂
  | [], H₂, p => by_rfl
  | .run a ℓ :: H₁, H₂, p => by
    simp only [List.cons_append, hostLeaves, hostLeaves_append n C H₁ H₂, List.append_assoc]
    congr 3
    zunhn; ring
  | .pt x :: H₁, H₂, p => by
    simp only [List.cons_append, hostLeaves, hostLeaves_append n C H₁ H₂]
    zugjz
    zuojm; zunjr; omega
theorem hostLeaves_single (n C p : ℕ) (it : HostItem) :
    hostLeaves n C p [it] = itemLeaves n C p it := by
  cases it <;> simp [hostLeaves, itemLeaves]

/-- A chord list written in two parts. -/
theorem clAt_append {m : ℕ → ℕ} {A : ℕ} {L L₂ : List zte}
    (h₁ : ChordListAt m A L) (h₂ : ChordListAt m ztgcw L₂) :
    ChordListAt m A ztfi := by
  zug
  zuelb

  · zuela
  · zuets

/-- A chord list survives memory changes outside its words. -/
theorem clAt_congr {m m' : ℕ → ℕ} {A : ℕ} {L : List zte} (h : ChordListAt m A L)
    (hm : ∀ x, A ≤ x → x < A + 3 * L.length → m' x = m x) : ChordListAt m' A L := by
  zug
  zurw
  grind

/-- The wrap-around case: two chunk loops around the edge `v_{n-1} v_0`. -/
def plRunW : Stmt :=
  .seq (block [.subN 219014 219026 219022])
    (.seq plCh
      (.seq (block [.subN 219025 219001 219022, .addN 219012 219007 219018,
          .addN 219012 219012 219025, .copyN 219013 219017, .subN 219014 219023 219025])
        plCh))

/-- `u = (a + 1) mod n`, `L = ℓ - 2`, `u + L`, `s = p + 1`, `a := u`. -/
def plRunPre : Stmt :=
  .seq (block [.addN 219022 219010 219018])
    (.seq (.ifLtN 219022 219001 .skip (.instr (.constN 219022 0)))
      (block [.subN 219023 219011 219019, .addN 219024 219022 219023,
        .addN 219012 219007 219018, .copyN 219013 219022]))

/-- **The leaves of a run item.** -/
def plRun : Stmt :=
  .ifLtN 219011 219020 .skip
    (.seq plRunPre (.ifLtN 219024 219001 (.seq (.instr (.copyN 219014 219023)) plCh) plRunW))

/-- The registers `plRun` writes. -/
def Brun (r : ℕ) : Bool := Bch r || decide (219022 ≤ r ∧ r ≤ 219025)
section exec
variable {P : Polygon} {W : ℕ}

/-- The common hypotheses of the planner steps: constants and the chunk size. -/
structure PlConst (n C : ℕ) (d : Config) : Prop where
  r01 : d.nreg 219001 = n
  r02 : d.nreg 219002 = C
  r17 : d.nreg 219017 = 0
  r18 : d.nreg 219018 = 1
  r19 : d.nreg 219019 = 2
  r20 : d.nreg 219020 = 3
  r26 : d.nreg 219026 = n - 1
variable {n C : ℕ}
theorem PlConst.keep {d d' : Config} (h : PlConst n C d)
    (hk : ∀ r, (r = 219001 ∨ r = 219002 ∨ ztnfx ∨ r = 219026) →
      d'.nreg r = d.nreg r) : PlConst n C d' :=
  ⟨by zumzq; exact h.r01, by zumzq; exact h.r02,
    by zumzq; exact h.r17, by zumzq; exact h.r18,
    by zumzq; exact h.r19, by zumzq; exact h.r20,
    by zumzq; exact h.r26⟩
theorem brun_const {r : ℕ} (h : r = 219001 ∨ r = 219002 ∨ ztnfx ∨ r = 219026) :
    Brun r = false := by
  simp only [Brun, Bch, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
set_option maxHeartbeats 4000000 in
/-- **The leaves of a run item** are written at the pointer. -/
theorem plRun_exec (hC : 1 ≤ C) (hn : 2 ≤ n) (d : Config) (hw : WordsBounded W d)
    (hK : PlConst n C d) {a ℓ p k ptr : ℕ} (h10 : d.nreg 219010 = a) (h11 : d.nreg 219011 = ℓ)
    (h07 : d.nreg 219007 = p) (h16 : d.nreg 219016 = ptr) (h04 : d.nreg 219004 = k)
    (ha : a < n) (hℓ : ℓ < n) (hWp : p + ℓ + n + 1 ≤ W)
    (hWt : ptr + 3 * (runLeaves n C p a ℓ).length ≤ W)
    (hWk : k + (runLeaves n C p a ℓ).length ≤ W) :
    ∃ d' j, Exec P W plRun d d' j ∧ j ≤ 15 * (runLeaves n C p a ℓ).length + 40 ∧
      d'.nreg 219016 = ptr + 3 * (runLeaves n C p a ℓ).length ∧
      d'.nreg 219004 = k + (runLeaves n C p a ℓ).length ∧
      ChordListAt d'.nmem ptr (runLeaves n C p a ℓ) ∧
      (∀ x, (x < ptr ∨ ptr + 3 * (runLeaves n C p a ℓ).length ≤ x) → d'.nmem x = d.nmem x) ∧
      FrameM Brun d d' := by
  by_cases h3 : ℓ < 3
  · have hrl : runLeaves n C p a ℓ = [] := by unfold runLeaves; simp_all
    rw [hrl]
    refine ⟨d, 0 + 1, .ifLtN_true (by rw [h11, hK.r20]; exact h3) (.skip hw), by simp,
      by omega, by omega, fun i hi => by simp_all, by omega, FrameM.refl _ _⟩
  -- `u = (a + 1) % n`, `L = ℓ - 2`
  have hu : (a + 1) % n = if a + 1 < n then a + 1 else 0 := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [show a + 1 = n by omega, Nat.mod_self]
  set u := (a + 1) % n with hud
  have hun : u < n := by grind
  obtain ⟨d₁, j₁, e₁, hj₁, v22, v23, v24, v12, v13, g₁, m₁⟩ : ∃ d₁ j₁, Exec P W
      plRunPre d d₁ j₁ ∧ j₁ ≤ 8 ∧
      d₁.nreg 219022 = u ∧ d₁.nreg 219023 = ℓ - 2 ∧ d₁.nreg 219024 = u + (ℓ - 2) ∧
      d₁.nreg 219012 = p + 1 ∧ d₁.nreg 219013 = u ∧
      (∀ r, ¬ (219012 ≤ r ∧ r ≤ 219013) → ¬ (219022 ≤ r ∧ r ≤ 219024) → d₁.nreg r = d.nreg r) ∧
      d₁.nmem = d.nmem := by
    have e₁ := Exec.addN (P := P) hw 219022 219010 219018 (by rw [h10, hK.r18]; omega)
    set c₁ : Config := { d with nreg := upd d.nreg 219022 _ } with hc₁
    have q22 : c₁.nreg 219022 = a + 1 := by rw [hc₁]; config_simp; rw [h10, hK.r18]
    have q : ∀ r, r ≠ 219022 → c₁.nreg r = d.nreg r := by simp_all
    unfold plRunPre
    obtain ⟨c₂, j₂, e₂, hj₂, q22', q', qm⟩ : ∃ c₂ j₂, Exec P W
        (.ifLtN 219022 219001 .skip (.instr (.constN 219022 0))) c₁ c₂ j₂ ∧ j₂ ≤ 3 ∧
        c₂.nreg 219022 = u ∧ (∀ r, r ≠ 219022 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem := by
      by_cases hlt : a + 1 < n
      · refine ⟨c₁, 0 + 1, .ifLtN_true (by rw [q22, q _ (by decide), hK.r01]; omega)
          (.skip e₁.wb_right), by omega, by simp_all, by omega, rfl⟩
      · refine ⟨_, 1 + 2, .ifLtN_false (by rw [q22, q _ (by decide), hK.r01]; omega)
          (Exec.constN e₁.wb_right 219022 0 (by omega)), by omega, ?_,
          by simp_all, rfl⟩
        simp_all
    have w₂ := e₂.wb_right
    have b11 : c₂.nreg 219011 = ℓ := by simp_all
    have b19 : c₂.nreg 219019 = 2 := by rw [q' _ (by decide), q _ (by decide), hK.r19]
    have b07 : c₂.nreg 219007 = p := by simp_all
    have b18 : c₂.nreg 219018 = 1 := by simp_all
    obtain ⟨c₃, j₃, e₃, hj₃, w23, w24, w12, w13, g₃, m₃⟩ : ∃ c₃ j₃, Exec P W
        (block [.subN 219023 219011 219019, .addN 219024 219022 219023,
          .addN 219012 219007 219018, .copyN 219013 219022]) c₂ c₃ j₃ ∧ j₃ = 4 ∧
        c₃.nreg 219023 = ℓ - 2 ∧ c₃.nreg 219024 = u + (ℓ - 2) ∧ c₃.nreg 219012 = p + 1 ∧
        c₃.nreg 219013 = u ∧
        (∀ r, ¬ (219012 ≤ r ∧ r ≤ 219013) → r ≠ 219023 → r ≠ 219024 → c₃.nreg r = c₂.nreg r) ∧
        c₃.nmem = c₂.nmem := by
      exec_block
      all_goals try (config_simp; (try simp only [b11, b19, q22', b07, b18]); omega)
      refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl⟩ <;> config_simp <;>
        (try simp only [b11, b19, q22', b07, b18])
      try simp only [Config.nreg_mk]
      rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ h3, Machine.upd_other _ _ _ h2]
    refine ⟨c₃, (1 + 0) + (j₂ + j₃), .seq (.seq e₁ (.skip e₁.wb_right)) (.seq e₂ e₃), by omega, ?_,
      w23, w24, w12, w13, ?_, ?_⟩
    · grind
    · intro r h1 h2
      rw [g₃ r h1 (by omega) (by omega), q' r (by omega), q r (by omega)]
    simp_all
  have w₁ := e₁.wb_right
  have kK : PlConst n C d₁ := hK.keep (by grind)
  have k07 : d₁.nreg 219007 = p := by simp_all
  have k16 : d₁.nreg 219016 = ptr := by simp_all
  have k04 : d₁.nreg 219004 = k := by simp_all
  have hf₁ : FrameM Brun d d₁ := ⟨fun r hr => g₁ r (by
      simp only [Brun, Bch, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr; omega) (by
      simp only [Brun, Bch, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr; omega),
    (exec_frameM e₁ (by decide : wrM Brun plRunPre = true)).2.1,
    (exec_frameM e₁ (by decide : wrM Brun plRunPre = true)).2.2.1,
    (exec_frameM e₁ (by decide : wrM Brun plRunPre = true)).2.2.2⟩
  by_cases hnw : u + (ℓ - 2) < n
  · -- no wrap-around: one chunk loop
    have hrl : runLeaves n C p a ℓ = chunks C (p + 1) u (ℓ - 2) := by
      unfold runLeaves; grind
    rw [hrl] at hWt hWk ⊢
    have e₂ := Exec.copyN (P := P) w₁ 219014 219023
    set d₂ : Config := { d₁ with nreg := upd d₁.nreg 219014 _ } with hd₂
    have g₂ : ∀ r, r ≠ 219014 → d₂.nreg r = d₁.nreg r := fun r hr => by rw [hd₂]; simp [hr]
    have kK₂ := kK.keep fun r hr => g₂ r (by omega)
    obtain ⟨d', j₃, e₃, hj₃, c16, c04, cL, cm, cf⟩ := plCh_exec hC _ d₂ _ u k
      ptr e₂.wb_right kK₂.r02 (by rw [hd₂]; simp [v23]) (by grind)
      (by grind) (by grind)
      (by grind) kK₂.r17 kK₂.r18 kK₂.r20 (by omega) (by omega) hWt hWk
    have ex : Exec P W plRun d d' _ :=
      .ifLtN_false (by rw [h11, hK.r20]; exact h3)
        (.seq e₁ (.ifLtN_true (by rw [v24, kK.r01]; omega) (.seq e₂ e₃)))
    refine ⟨d', _, ex, by omega, c16, c04,
      cL, by grind, ?_⟩
    exact hf₁.trans ((exec_frameM e₂ (by decide : wrM Brun _ = true)).trans
      ⟨fun r hr => cf.1 r (by simp only [Brun, Bool.or_eq_false_iff] at hr; grind),
        fun r hr => cf.2.1 r (by simp only [Brun, Bool.or_eq_false_iff] at hr; grind),
        cf.2.2.1, cf.2.2.2⟩)
  · -- wrap-around: two chunk loops
    have hL1 : n - 1 - u + 1 + (ℓ - 2 - (n - u)) = ℓ - 2 := by omega
    have hrl : runLeaves n C p a ℓ = chunks C (p + 1) u (n - 1 - u) ++
        chunks C (p + 1 + (n - u)) 0 (ℓ - 2 - (n - u)) := by
      unfold runLeaves; grind
    set ch₁ := chunks C _ u _ with hch₁
    set ch₂ := chunks C _ 0 _ with hch₂
    rw [hrl, List.length_append] at hWt hWk ⊢
    -- the first segment
    have e₂ := Exec.subN (P := P) w₁ 219014 219026 219022
    set d₂ : Config := { d₁ with nreg := upd d₁.nreg 219014 _ }
      with hd₂
    have g₂ : ∀ r, r ≠ 219014 → d₂.nreg r = d₁.nreg r := fun r hr => by rw [hd₂]; simp [hr]
    have kK₂ := kK.keep fun r hr => g₂ r (by omega)
    obtain ⟨d₃, j₃, e₃, hj₃, c16, c04, cL, cm, cf⟩ := plCh_exec (P := P) hC (n - 1 - u) d₂
      _ u k ptr e₂.wb_right kK₂.r02 (by rw [hd₂]; simp [kK.r26, v22])
      (by rw [g₂ _ (by decide), v12]) (by rw [g₂ _ (by decide), v13])
      (by rw [g₂ _ (by decide), k16]) (by rw [g₂ _ (by decide), k04]) kK₂.r17 kK₂.r18 kK₂.r20
      (by omega) (by omega) (by grind) (by grind)
    rw [← hch₁] at c16 c04 cL cm hj₃
    have g₃ := cf.1
    have kK₃ := kK₂.keep fun r hr => g₃ r (by
      simp only [Bch, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
    have t07 : d₃.nreg 219007 = p := by
      rw [g₃ _ (by decide), g₂ _ (by decide), k07]
    have t22 : d₃.nreg 219022 = u := by rw [g₃ _ (by decide), g₂ _ (by decide), v22]
    have t23 : d₃.nreg 219023 = ℓ - 2 := by rw [g₃ _ (by decide), g₂ _ (by decide), v23]
    -- the arguments of the second segment
    obtain ⟨d₄, j₄, e₄, hj₄, s12, s13, s14, s16, s04, gs, ms⟩ : ∃ d₄ j₄, Exec P W
        (block [.subN 219025 219001 219022, .addN 219012 219007 219018,
          .addN 219012 219012 219025, .copyN 219013 219017, .subN 219014 219023 219025])
        d₃ d₄ j₄ ∧ j₄ = 5 ∧ d₄.nreg 219012 = p + 1 + (n - u) ∧ d₄.nreg 219013 = 0 ∧
        d₄.nreg 219014 = ℓ - 2 - (n - u) ∧ d₄.nreg 219016 = ptr + 3 * ch₁.length ∧
        d₄.nreg 219004 = k + ch₁.length ∧
        (∀ r, ¬ (219012 ≤ r ∧ r ≤ 219014) → r ≠ 219025 → d₄.nreg r = d₃.nreg r) ∧
        d₄.nmem = d₃.nmem := by
      have q01 := kK₃.r01; have q18 := kK₃.r18; have q17 := kK₃.r17
      have e := e₃.wb_right
      exec_block
      all_goals try (config_simp; (try simp only [q01, t22, t07, q18, q17, t23]); omega)
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl⟩ <;> config_simp <;>
        (try simp only [q01, t22, t07, q18, q17, t23, c16, c04])
      first | rfl | (simp only [Machine.upd_apply]; split_ifs <;> first | rfl | omega)
    have kK₄ := kK₃.keep fun r hr => gs r (by omega) (by omega)
    obtain ⟨d', j₅, e₅, hj₅, c16', c04', cL', cm', cf'⟩ := plCh_exec hC
      _ d₄ _ 0 _ _
      e₄.wb_right kK₄.r02 s14 s12 s13 s16 s04 kK₄.r17 kK₄.r18 kK₄.r20 (by omega) (by omega)
      (by grind) (by grind)
    rw [← hch₂] at c16' c04' cL' cm' hj₅
    have exW : Exec P W plRunW d₁ d' _ :=
      .seq (.seq e₂ (.skip e₂.wb_right)) (.seq e₃ (.seq e₄ e₅))
    have ex : Exec P W plRun d d' _ :=
      .ifLtN_false (by rw [h11, hK.r20]; exact h3)
        (.seq e₁ (.ifLtN_false (by rw [v24, kK.r01]; omega) exW))
    refine ⟨d', _, ex, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · refine clAt_append (clAt_congr cL fun x h1 h2 => ?_) ?_
      · rw [cm' x (Or.inl h2), ms]
      omega
    · intro x hx
      rw [cm' x (by omega), ms, cm x (by omega)]
      grind
    · have f₂ := exec_frameM e₂ (by decide : wrM Brun _ = true)
      have f₄ := exec_frameM e₄ (by decide : wrM Brun
        _ = true)
      have up : ∀ {x y : Config}, FrameM Bch x y → FrameM Brun x y := fun h =>
        ⟨fun r hr => h.1 r (by simp only [Brun, Bool.or_eq_false_iff] at hr; grind),
          fun r hr => h.2.1 r (by simp only [Brun, Bool.or_eq_false_iff] at hr; grind),
          h.2.2.1, h.2.2.2⟩
      exact hf₁.trans (f₂.trans ((up cf).trans (f₄.trans (up cf'))))
end exec
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs BuildRam
@[expose] public section
def plItem : Stmt :=
  .seq (block [.loadN 219009 219008, .addN 219021 219008 219018, .loadN 219010 219021,
      .addN 219021 219021 219018, .loadN 219011 219021])
    (.seq (.ifLtN 219009 219018
        ztxuh
        ztdgq)
      ztebw)

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
  | .run a ℓ => m addr = 0 ∧ m zttfa = a ∧ m zttfb = ℓ
  | .pt (.vtx _) => m addr = 1
  | .pt (.onEdge _ _) => m addr = 2

/-- The run items are in range. -/
def ItemOK (n : ℕ) : HostItem → Prop
  | .run a ℓ => a < n ∧ ℓ < n
  | .pt _ => True

/-- The registers `plS` writes. -/
def Bpl (r : ℕ) : Bool := decide (219001 ≤ r ∧ r ≤ 219029) || decide ztyc
theorem wrM2_plS : wrM2 Bpl ztczi plS = true := by_decide
theorem hostLeaves_take_succ (n C : ℕ) (H : Host) {i : ℕ} (hi : i < H.length) :
    hostLeaves n C 0 ztbaeb = hostLeaves n C 0 ztdbw ++
      itemLeaves n C (Host.pts n ztdbw).length ztwzh := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, hostLeaves_append,
    hostLeaves_single, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]
theorem pts_take_succ (n : ℕ) (H : Host) {i : ℕ} (hi : i < H.length) :
    (Host.pts n ztbaeb).length = (Host.pts n ztdbw).length +
      ((H.getD i ztmn).pts n).length := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, DownMath.pts_append,
    List.length_append, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]
  zujnh
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
      d₁.nreg 219009 = d.nmem addr ∧ d₁.nreg 219010 = d.nmem zttfa ∧
      d₁.nreg 219011 = d.nmem zttfb ∧ d₁.nmem = d.nmem := by
    have q18 := hK.r18
    exec_block
    all_goals try (config_simp; (try simp only [h08, q18]); omega)
    simp_all
  have fr₁ := exec_frameM e₁ (by decide : wrM (fun r => decide ztnfv ||
    decide zttxs) (block [.loadN 219009 219008, .addN 219021 219008 219018,
      .loadN 219010 219021, .addN 219021 219021 219018, .loadN 219011 219021]) = true)
  have g₁ : ∀ r, ¬ ztnfv → r ≠ 219021 → d₁.nreg r = d.nreg r :=
    fun r h1 h2 => fr₁.1 r by_simp_all
  zud
  have kK : PlConst n C d₁ := hK.keep fun r hr => g₁ r by_omega by_omega
  have k07 : ztuts := by_simp_all
  have k16 : ztpof := by_simp_all
  have k04 : ztpoe := by_simp_all

  have k05 : d₁.nreg 219005 = i := by_simp_all
  have k08 : d₁.nreg 219008 = addr := by_simp_all
  have hf₁ : FrameM Bitem d d₁ := exec_frameM e₁ by_decide
  -- the tail: next address and index
  have tail : ∀ (d₂ : Config) (j₂ : ℕ), Exec P W
      (.ifLtN 219009 219018
        ztxuh
        ztdgq) d₁ d₂ j₂ →
      d₂.nreg 219005 = i → d₂.nreg 219008 = addr → d₂.nreg 219018 = 1 → d₂.nreg 219020 = 3 →
      ∃ d₃, Exec P W ztebw d₂ d₃ 2 ∧
        d₃.nreg 219005 = i + 1 ∧ d₃.nreg 219008 = addr + 3 ∧
        ztgsl ∧ d₃.nmem = d₂.nmem ∧
        FrameM Bitem d₂ d₃ := by
    intro d₂ j₂ e₂ a05 a08 a18 a20
    zue
    obtain ⟨d₃, j₃, e₃, hj₃, b05, b08, gb, mb⟩ : ∃ d₃ j₃, Exec P W
        ztebw d₂ d₃ j₃ ∧ j₃ = 2 ∧
        d₃.nreg 219005 = i + 1 ∧ d₃.nreg 219008 = addr + 3 ∧
        ztgsl ∧ d₃.nmem = d₂.nmem := by
      exec_block
      all_goals try (config_simp; (try simp only [a05, a08, a18, a20]); omega)
      simp_all
    subst hj₃
    exact ⟨d₃, e₃, b05, b08, gb, mb, exec_frameM e₃ by_decide⟩
  cases it with
  | run a ℓ =>
    obtain ⟨hk0, ha, hl⟩ := hit
    obtain ⟨han, hln⟩ := hwf
    simp only [itemLeaves] at hWt hWk ⊢
    have kK10 : d₁.nreg 219010 = a := by_omega
    have kK11 : d₁.nreg 219011 = ℓ := by_omega
    obtain ⟨d₂, j₂, e₂, hj₂, c16, c04, cL, cm, cf⟩ := plRun_exec (P := P) hC hn d₁ w₁ kK kK10
      kK11 k07 k16 k04 han hln by_omega hWt hWk
    have g₂ : ∀ r, Brun r = false → d₂.nreg r = d₁.nreg r := cf.1
    have kK₂ : PlConst n C d₂ := kK.keep fun r hr => g₂ r (brun_const hr)
    have t07 : d₂.nreg 219007 = p := by rw [g₂ _ by_decide, k07]
    have t11 : d₂.nreg 219011 = ℓ := by rw [g₂ _ by_decide, kK11]
    -- `p := p + ℓ + 1`
    obtain ⟨d₃, j₃, e₃, hj₃, s07, gs, ms⟩ : ∃ d₃ j₃, Exec P W
        ztbtv d₂ d₃ j₃ ∧ j₃ = 2 ∧
        d₃.nreg 219007 = p + ztmv ∧ (∀ r, r ≠ 219007 → d₃.nreg r = d₂.nreg r) ∧
        d₃.nmem = d₂.nmem := by
      have q18 := kK₂.r18
      have e := e₂.wb_right
      exec_block
      all_goals try (config_simp; (try simp only [t07, t11, q18]); omega)
      refine ⟨rfl, ?_, fun r h1 => ?_, rfl⟩ <;> config_simp <;> (try simp only [t07, t11, q18])
      · omega
      · zuym
    have ex₂ : Exec P W (.ifLtN 219009 219018
        ztxuh
        ztdgq) d₁ d₃ (j₂ + j₃ + 1) :=
      .ifLtN_true (by rw [v09, hk0, kK.r18]; omega) ztcr
    obtain ⟨d₄, e₄, b05, b08, gb, mb, fb⟩ := tail d₃ _ ex₂
      (by rw [gs _ by_decide, g₂ _ by_decide, k05])
      (by rw [gs _ by_decide, g₂ _ by_decide, k08])
      (by rw [gs _ by_decide, kK₂.r18]) (by rw [gs _ by_decide, kK₂.r20])
    refine ⟨d₄, j₁ + ((j₂ + j₃ + 1) + 2), .seq e₁ ztsqb, by_omega, b05, b08, ?_, ?_, ?_, ?_,
      fun x hx => ?_, ?_⟩
    · rw [gb _ by_decide by_decide, s07, DownMath.run_pts_length]
    · grind
    · grind
    · grind
    · grind
    · have f₃ : FrameM Bitem d₂ d₃ := exec_frameM e₃ by_decide
      have up : FrameM Bitem d₁ d₂ :=
        ⟨fun r hr => cf.1 r ztirz,
          fun r hr => cf.2.1 r ztirz,
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
        ztdgq d₁ d₂ j₂ ∧ j₂ = 1 ∧
        d₂.nreg 219007 = p + 1 ∧ (∀ r, r ≠ 219007 → d₂.nreg r = d₁.nreg r) ∧
        d₂.nmem = d₁.nmem := by
      have q18 := kK.r18
      exec_block
      all_goals try (config_simp; (try simp only [k07, q18]); omega)
      refine ⟨rfl, ?_, fun r h1 => ?_, rfl⟩ <;> config_simp <;> (try simp only [k07, q18])
      zuym
    have ex₂ : Exec P W (.ifLtN 219009 219018
        ztxuh
        ztdgq) d₁ d₂ (j₂ + 2) := .ifLtN_false hk1 e₂
    obtain ⟨d₄, e₄, b05, b08, gb, mb, fb⟩ := tail d₂ _ ex₂
      by_grind by_grind
      (by rw [gs _ by_decide, kK.r18]) (by rw [gs _ by_decide, kK.r20])
    refine ⟨d₄, j₁ + ((j₂ + 2) + 2), .seq e₁ ztsqb, by_omega, b05, b08, ?_, ?_, ?_,
      fun i hi => by_grind, fun y _ => by_grind, ?_⟩
    · rw [gb _ by_decide by_decide, s07]; rfl
    · grind
    · grind
    · exact hf₁.trans ((exec_frameM e₂ by_decide).trans fb)
end exec
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs BuildRam
@[expose] public section
variable (n C : ℕ) (H : Host) (i : ℕ)
theorem hostLeaves_take_drop :
    hostLeaves n C 0 H = hostLeaves n C 0 ztdbw ++
      hostLeaves n C (Host.pts n ztdbw).length (H.drop i) := by
  conv_lhs => rw [← List.take_append_drop i H]
  rw [hostLeaves_append, Nat.zero_add]
theorem hostLeaves_take_le :
    (hostLeaves n C 0 ztdbw).length ≤ (hostLeaves n C 0 H).length := by
  rw [hostLeaves_take_drop n C H i, List.length_append]; omega
theorem pts_take_le (n : ℕ) (H : Host) (i : ℕ) :
    (Host.pts n ztdbw).length ≤ (Host.pts n H).length := by
  conv_rhs => rw [← List.take_append_drop i H]
  rw [DownMath.pts_append, List.length_append]; omega

/-- The loop invariant of the planner after `i` items. -/
structure PlI (W n C HB T len K : ℕ) (H : Host) (c₀ : Config) (i : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  kc : PlConst n C c
  r05 : c.nreg 219005 = i
  r06 : c.nreg 219006 = len
  r08 : c.nreg 219008 = HB + 1 + 3 * i
  r07 : c.nreg 219007 = (Host.pts n ztdbw).length
  r16 : c.nreg 219016 = T + 3 * (hostLeaves n C 0 ztdbw).length
  r04 : c.nreg 219004 = (hostLeaves n C 0 ztdbw).length
  r03 : c.nreg 219003 = T
  rA : c.nreg ALLOC = T
  il : i ≤ len
  tab : ChordListAt c.nmem T (hostLeaves n C 0 ztdbw)
  low : ∀ a, a < T → c.nmem a = c₀.nmem a
  fr : FrameM Bpl c₀ c
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **The leaf planner.** -/
theorem plS_exec {C : ℕ} (hC : 1 ≤ C) (hn3 : 3 ≤ P.n) (c : Config) (hw : WordsBounded W c)
    {H : Host} {HB : ℕ} (h00 : c.nreg 219000 = HB) (h02 : c.nreg 219002 = C)
    (hH : HostAt c.nmem HB H) (hwf : HostWF P.n H)
    (hHB : HB + 3 * H.length + 1 ≤ c.nreg ALLOC)
    (hW1 : c.nreg ALLOC + 3 * (hostLeaves P.n C 0 H).length + 1 ≤ W)
    (hW2 : (Host.pts P.n H).length + 2 * P.n + 1 ≤ W) :
    ∃ c' k, Exec P W plS c c' k ∧
      k ≤ 15 * (hostLeaves P.n C 0 H).length + 70 * H.length + 20 ∧ WordsBounded W c' ∧
      c'.nreg 219003 = c.nreg ALLOC ∧ c'.nreg 219004 = (hostLeaves P.n C 0 H).length ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * (hostLeaves P.n C 0 H).length ∧
      ChordListAt c'.nmem (c.nreg ALLOC) (hostLeaves P.n C 0 H) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧ PlConst P.n C c' ∧
      (∀ r, Bpl r = false → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  set T := c.nreg ALLOC with hT
  set K := (hostLeaves P.n C 0 H).length with hK
  set len := H.length with hlen
  have hTW : T ≤ W := by omega
  -- initialization
  obtain ⟨c₁, k₁, e₁, hk₁, w₁, x01, x02, x17, x18, x19, x20, x26, x05, x06, x08, x07, x16, x04,
      x03, xA, xm⟩ : ∃ c₁ k₁, Exec P W plInit c c₁ k₁ ∧ k₁ = 13 ∧ WordsBounded W c₁ ∧
      c₁.nreg 219001 = P.n ∧ c₁.nreg 219002 = C ∧ c₁.nreg 219017 = 0 ∧ c₁.nreg 219018 = 1 ∧
      c₁.nreg 219019 = 2 ∧ c₁.nreg 219020 = 3 ∧ c₁.nreg 219026 = P.n - 1 ∧
      c₁.nreg 219005 = 0 ∧ c₁.nreg 219006 = len ∧ c₁.nreg 219008 = HB + 1 ∧
      c₁.nreg 219007 = 0 ∧ c₁.nreg 219016 = T ∧ c₁.nreg 219004 = 0 ∧ c₁.nreg 219003 = T ∧
      c₁.nreg ALLOC = T ∧ c₁.nmem = c.nmem := by
    have hl : c.nmem HB = len := hH.1
    have hT9 : c.nreg 9999 = T := rfl
    unfold plInit
    exec_block
    all_goals try (config_simp; (try simp only [h00, hl, h02, hT9]); omega)
    refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
      (try simp only [show ALLOC = 9999 from rfl]) <;> config_simp <;>
      (try simp only [h00, hl, h02, hT9])
  have fr₁ : FrameM Bpl c c₁ := exec_frameM e₁ (by decide)
  have h0 : hostLeaves P.n C 0 (H.take 0) = [] := by rfl
  have h0p : (Host.pts P.n (H.take 0)).length = 0 := by rfl
  have I₁ : PlI W P.n C HB T len K H c 0 c₁ :=
    { wb := w₁, kc := ⟨x01, x02, x17, x18, x19, x20, x26⟩, r05 := x05, r06 := x06,
      r08 := by rw [x08], r07 := by omega, r16 := by simp_all,
      r04 := by simp_all, r03 := x03, rA := xA, il := Nat.zero_le _,
      tab := fun i hi => by simp_all, low := fun a _ => by rw [xm],
      fr := fr₁ }
  -- the item loop
  have hstep : ∀ c₂, (∃ i, PlI W P.n C HB T len K H c i c₂) → c₂.nreg 219005 < c₂.nreg 219006 →
      ∃ c₃ k₃, Exec P W plItem c₂ c₃ k₃ ∧ (∃ i, PlI W P.n C HB T len K H c i c₃) ∧
        (70 * (len - c₃.nreg 219005) + 15 * (K - c₃.nreg 219004)) + k₃ + 2 ≤
          70 * (len - c₂.nreg 219005) + 15 * (K - c₂.nreg 219004) := by
    rintro c₂ ⟨i, I⟩ hlt
    rw [I.r05, I.r06] at hlt
    obtain ⟨it, hitd⟩ : ∃ it, it = H.getD i (.run 0 0) := ⟨_, rfl⟩
    have hmem : it ∈ H := by
      simp_all
    have hwfi := hwf it hmem
    have hHi := hH.2 i hlt
    rw [← hitd] at hHi
    have haddr : HB + 1 + 3 * i + 3 ≤ T := by omega
    have l0 := I.low (HB + 1 + 3 * i) (by omega)
    have l1 := I.low (HB + 1 + 3 * i + 1) (by omega)
    have l2 := I.low (HB + 1 + 3 * i + 2) (by omega)
    have hit : ItemWords c₂.nmem (HB + 1 + 3 * i) it := by
      cases it with
      | run a ℓ =>
        obtain ⟨x1, x2, x3⟩ := hHi
        exact ⟨by omega,
          by grind,
          by grind⟩
      | pt x =>
        cases x with
        | vtx j => show c₂.nmem _ = 1; rw [l0]; exact hHi.1
        | onEdge e h => show c₂.nmem _ = 2; rw [l0]; exact hHi.1
    have hwfi' : ItemOK P.n it := by
      cases it with
      | run a ℓ => exact hwfi
      | pt x => trivial
    have hsucc := hostLeaves_take_succ P.n C H hlt
    rw [← hitd] at hsucc
    have hpsucc := pts_take_succ P.n H hlt
    rw [← hitd] at hpsucc
    have hle1 := hostLeaves_take_le P.n C H (i + 1)
    rw [hsucc, List.length_append] at hle1
    have hpt := pts_take_le P.n H i
    obtain ⟨c₃, k₃, e₃, hk₃, b05, b08, b07, b16, b04, bL, bm, bf⟩ := plItem_exec (P := P) hC
      (by omega) c₂ I.wb I.kc (it := it) I.r05 I.r08 I.r07 I.r16 I.r04 hit hwfi' (by omega)
      (by omega) (by omega) (by omega) (by omega)
    have gI : ∀ r, Bitem r = false → c₃.nreg r = c₂.nreg r := bf.1
    refine ⟨c₃, k₃, e₃, ⟨i + 1, ?_⟩, ?_⟩
    · refine ⟨e₃.wb_right, I.kc.keep fun r hr => gI r (by
          simp only [Bitem, Brun, Bch, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega),
        b05, by rw [gI _ (by decide), I.r06], by omega, ?_, ?_, ?_,
        by rw [gI _ (by decide), I.r03], by rw [gI _ (by decide), I.rA], by omega, ?_, ?_, ?_⟩
      · omega
      · grind
      · simp_all
      · rw [hsucc]
        exact clAt_append (clAt_congr I.tab fun x _ hx => bm x (Or.inl hx)) bL
      · intro a ha
        rw [bm a (Or.inl (by omega)), I.low a ha]
      · exact I.fr.trans ⟨fun r hr => gI r (by
            simp only [Bpl, Bitem, Brun, Bch, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢
            omega), fun r hr => bf.2.1 r (by
            simp only [Bpl, Bitem, Brun, Bch, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢
            omega), bf.2.2.1, bf.2.2.2⟩
    · rw [b05, b04, I.r04, I.r05]
      omega
  obtain ⟨c₂, k₂, e₂, ⟨i, I₂⟩, hend, hk₂⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 219005) (b := 219006) (body := plItem)
    (fun c₂ => ∃ i, PlI W P.n C HB T len K H c i c₂)
    (fun c₂ => 70 * (len - c₂.nreg 219005) + 15 * (K - c₂.nreg 219004))
    (fun c₂ ⟨i, I⟩ => I.wb) hstep ⟨0, I₁⟩
  have hi : i = len := by rw [I₂.r05, I₂.r06] at hend; have := I₂.il; omega
  subst hi
  have htk : H.take len = H := by grind
  have tab₂ := I₂.tab
  have r16₂ := I₂.r16
  have r04₂ := I₂.r04
  rw [htk] at tab₂ r16₂ r04₂
  have e₃ := Exec.copyN (P := P) e₂.wb_right 9999 219016
  have ex : Exec P W plS c _ (k₁ + (k₂ + 1)) := .seq e₁ (.seq e₂ e₃)
  have h0 : (hostLeaves P.n C 0 (H.take 0)).length = 0 := by rfl
  refine ⟨_, k₁ + (k₂ + 1), ex, ?_, e₃.wb_right, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · simp only; rw [Machine.upd_other _ _ _ (by decide)]; exact I₂.r03
  · simp only; rw [Machine.upd_other _ _ _ (by decide)]; omega
  · show upd c₂.nreg 9999 (c₂.nreg 219016) 9999 = T + 3 * K
    rw [Machine.upd_same, r16₂]
  · omega
  · exact I₂.low
  · exact I₂.kc.keep fun r hr => by
      simp only; rw [Machine.upd_other _ _ _ (by omega)]
  · intro r hr
    simp only
    rw [Machine.upd_other _ _ _ (by
      intro h; subst h; simp [Bpl] at hr)]
    exact I₂.fr.1 r hr
  · funext r; exact exec_frameM2 ex wrM2_plS r rfl
  · exact I₂.fr.2.2.1
  · exact I₂.fr.2.2.2
end exec
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
@[expose] public section
open Machine

/-- The degree cap of the region maps (`hostFullDegSpec`: `2 (64 + 1)`). -/
def regCap : ℕ := 130

/-- **The contract of the region procedure (D5).** -/
def RegionSpec (O : OracleIface) : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s drvBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      (gradeCtx O).holds P c.nmem ztdzl ztm ∧
      7 ≤ c.nreg 219202 ∧ c.nreg 219202 ≤ c.nmem ztdzl ∧
      c.nreg 219203 = 2 ^ c.nreg 219202 ∧
      2 * gradeGran ztdzk ≤ c.nreg 219204 ∧ 128 ≤ c.nreg 219204 ∧
      c.nreg 219204 ≤ 4096 * 2 ^ Cost.ceilBeta ztdzk ∧
      c.nreg 219204 + 129 ≤ (gradeCtx O).cap P c.nmem ztdzl ∧
      ∃ H : Host, Robust ztm c.nmem ztfbx ∧
        c.nreg 219200 + 3 * H.length + 1 ≤ c.nreg ALLOC ∧
        H.length ≤ 20 ∧ HostWF (Qof P).n H ∧ HostRegular (Qof P).n H ∧
        (H.poly zta).Simple ∧
        c.nreg 219201 = (H.pts (Qof P).n).length ∧ 3 ≤ c.nreg 219201 ∧
        ∀ a ℓ, HostItem.run a ℓ ∈ H → ℓ ≤ 2 * c.nreg 219203)
    (fun P c c' =>
      ztbfg ∧
      c.nreg ALLOC ≤ c'.nreg 219210 ∧ c.nreg ALLOC ≤ c'.nreg 219211 ∧
      c.nreg 219204 ≤ c'.nreg 219212 ∧ c'.nreg 219212 ≤ c.nreg 219204 + 128 ∧
      ModelDescWF P ztdo c'.nmem ztfgh ∧
      ∀ (H : Host) (C : Chain), HostAt c.nmem ztqhv H → C.P = H.poly zta →
        C.s = 0 → C.m + 1 = C.P.n →
        Robust ztdo c'.nmem
          (fun m => m ztfgh = 0 ∧
            ChainDescAt m ztcyy zta H C ∧
            m ztcyy = c.nreg 219200) ∧
        ∃ N, NFWithin c'.nmem ztmfg ztdo N ∧
          IsCanonicalNF ztc zta N ztmfh regCap)
    ztbanw
noncomputable def lvNch (μ : ℕ) : ℕ :=
  140 * ztevh * ztdey / ztwtk

/-- The weight bound `γ_r = 2^(⌈βμ⌉+12)` of `Inv(μ)` (the rounds' semigranularity). -/
noncomputable def lvGr (μ : ℕ) : ℕ := 2 ^ ztfni

/-- **The cost arithmetic of one level (D11).** -/
def LvCostSpec : Prop :=
  (∃ n₀ : ℕ, ∀ n, n₀ ≤ n → 2 ^ ztydt + 200 ≤ n) ∧
  ∀ κo : ℕ, ∃ κ : ℕ, ∀ μ, 15 ≤ μ →
    lvNch μ ≤ κ * ztud ∧
    zthyt * (Nat.clog 2 (4 * lvNch μ + 4) + 1) ≤ κ * ztud ∧
    zthyt * shCost κo ztmmh * cuCost κo ztmmh *
        (cutGran ztmmh + Nat.clog 2 ztmmh + 1) ≤ κ * ztud
open BuildNF (codeLe)

/-- **The math of one level (D7).** -/
noncomputable def LevelMathSpec : Prop :=
  open Classical in
  ∀ (P : Polygon) (L : List zte) (E : List ℕ) (reg : ℕ → Set Point) (lam : ℕ),
    GoodEnv P → L ≠ [] →
    ChordTriplesOK ztwiq zta L → E.Perm ztct →
    E.Pairwise ztbajl →
    (interiorModel zta).DegLe
      ztbajd 4 →
    (interiorModel zta).Semigranular
      ztbajd
      ztxuo →
    Restore.NFRegs ztwiq zta
      ztbaja reg →
    -- 1. the hosts
    (∀ r, r < (BuildNF.buildNF ztwiq zta L E).nRegions →
      (regHost ztwkl (Qof P).n
          ztbaja r).length ≤ 20 ∧
      (∀ a ℓ, HostItem.run a ℓ ∈ regHost ztwkl (Qof P).n
          ztbaja r → ℓ ≤ 2 * 2 ^ nextLvl lam) ∧
      3 ≤ ((regHost ztwkl (Qof P).n
          ztbaja r).pts (Qof P).n).length ∧
      ((regHost ztwkl (Qof P).n
          ztbaja r).pts (Qof P).n).length ≤
        10 * 2 ^ nextLvl lam + 8) ∧
    -- the region data
    ∀ (γ₀ M : ℕ) (C : ℕ → Chain) (NR : ℕ → NF) (γR : ℕ → ℕ) (Lx : ℕ → List zte),
      γ₀ + 128 ≤ 2 ^ ztwnz →
      (∀ r, r < (BuildNF.buildNF ztwiq zta L E).nRegions →
        (C r).P = (regHost ztwkl (Qof P).n
          ztbaja r).poly (Qof P) ∧
        (C r).s = 0 ∧ (C r).m + 1 = (C r).P.n ∧
        IsCanonicalNF ztzee zta ztvab ztwid regCap ∧
        γ₀ ≤ γR r ∧ γR r ≤ γ₀ + 128 ∧
        {x | ∃ y ∈ Lx r, x = (recOf y).toSet ztwiq zta} =
          Extract.kept ztcz ((NR r).F ztzee zta) ∧
        ((Lx r).map fun y => (recOf y).toSet ztwiq zta).Nodup ∧
        (∀ y ∈ Lx r, (recOf y).Attached ztwiq zta ∧ y.1 < (Qof P).n) ∧
        (∀ q, q < 2 * (Lx r).length →
          ∃ j ∈ ((BuildNF.buildNF ztwiq zta L E).region r).arcs,
            OnArcKey zta ztbaja j
              (endPos ztdyq q)) ∧
        (Lx r).length ≤ M) →
      -- 3. the size of the kept lists
      (∀ r, r < (BuildNF.buildNF ztwiq zta L E).nRegions →
        (Lx r).length * ztbfd ≤ 140 * ztevh * (20 * 2 ^ nextLvl lam + 17)) ∧
      -- 2. the splice precondition
      ChordTriplesOK ztwiq zta
        (L ++ (List.range (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap
          Lx) ∧
      (∀ q, q < 2 * ((List.range
          (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap Lx).length →
        keyBkt zta ztbaja
            (endPos ((List.range
              (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap Lx) q) ≤
          2 * (BuildNF.buildNF ztwiq zta L E).arcs.length + 1) ∧
      (∀ q q', q < 2 * ((List.range
            (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap Lx).length →
          q' < 2 * ((List.range
            (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap Lx).length →
          keyBkt zta ztbaja
              (endPos ((List.range
                (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap Lx) q) <
            keyBkt zta ztbaja
              (endPos ((List.range
                (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap Lx) q') →
          codeLe ztwiq zta
            (L ++ (List.range
              (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap Lx)
            ztbhj ztekx) ∧
      (∀ b, bcnt (fun q => keyBkt zta ztbaja
            (endPos ((List.range
              (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap Lx) q))
          (2 * ((List.range
            (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap Lx).length)
          b ≤ 4 * M) ∧
      -- 4. the family after the splice
      ∀ E' : List ℕ,
        E'.Perm (List.range (2 * (L ++ (List.range
          (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap Lx).length)) →
        E'.Pairwise (codeLe ztwiq zta (L ++ (List.range
          (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap Lx)) →
        (BuildNF.buildNF ztwiq zta L E).F ztwiq zta ⊆
          (BuildNF.buildNF ztwiq zta (L ++ (List.range
            (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap Lx) E').F
            ztwiq zta ∧
        (interiorModel zta).DegLe
          ((BuildNF.buildNF ztwiq zta (L ++ (List.range
            (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap Lx) E').F
            ztwiq zta) (regCap + 4) ∧
        (interiorModel zta).Semigranular
          ((BuildNF.buildNF ztwiq zta (L ++ (List.range
            (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap Lx) E').F
            ztwiq zta) (2 ^ (Cost.ceilBeta (nextLvl lam) + 12)) ∧
        (L ++ (List.range
            (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap Lx).length *
            ztbfd ≤
          L.length * ztbfd + 1120 * ztevh * ((Qof P).n + 4 * L.length)
open Machine.Stmt Programs SignK
def lvParA : Stmt := block [
  .copyN 211000 230000, .constN 211014 1, .constN 211015 3, .constN 211016 0, .constN 211017 2,
  .addN 211021 211000 211014, .loadN 211001 211021,
  .constN 211022 4, .addN 211023 211000 211001, .addN 211023 211023 211022,
  .addN 211021 211023 210000, .loadN 211002 211021, .constN 211022 11,
  .addN 211002 211002 211022,
  .addN 211021 211023 211002, .loadN 211003 211021,
  .addN 211024 211000 211017,
  .addN 211021 211024 211002, .loadN 211004 211021,
  .constN 211022 10, .addN 211021 211024 211003, .addN 211021 211021 211022,
  .loadN 211005 211021,
  .addN 211006 211005 211005, .addN 211006 211006 211005,
  .addN 211021 211021 211017, .loadN 211007 211021,
  .addN 211021 210001 211014, .loadN 211025 211021, .constN 211008 0]
section exec
variable {P : Polygon} {W : ℕ}

/-- The registers `lvParA` writes. -/
def Bpar (r : ℕ) : Bool := decide (211000 ≤ r ∧ r < 211030)
theorem wr_lvParA : SignK.wr Bpar lvParA = true := by_decide
set_option maxHeartbeats 4000000 in
theorem lvParA_exec (c : Config) (hw : WordsBounded W c) {S n lam MD : ℕ}
    (h0 : c.nreg 230000 = S) (hl : c.nreg 210000 = lam) (h1 : c.nreg 210001 = MD)
    (hS : SetupAt c.nmem S n ztm) (h16 : 16 ≤ lam) (hlp : lam ≤ topGrade n)
    (hMD : MD + 6 ≤ c.nreg ALLOC) (hAW : c.nreg ALLOC ≤ W) (hW : 11 ≤ W) :
    ∃ c' k, Exec P W lvParA c c' k ∧ k = 30 ∧
      c'.nreg 211000 = S ∧ c'.nreg 211001 = topGrade n ∧ c'.nreg 211002 = nextLvl lam ∧
      c'.nreg 211003 = Cost.ceilBeta ztmc ∧ c'.nreg 211004 = 2 ^ nextLvl lam ∧
      c'.nreg 211005 = 2 ^ ztwqe ∧
      c'.nreg 211006 = 3 * 2 ^ ztwqe ∧
      c'.nreg 211007 = 2 ^ ztwnz ∧
      c'.nreg 211025 = c.nmem ztki ∧ c'.nreg 211008 = 0 ∧
      c'.nreg 211014 = 1 ∧ c'.nreg 211015 = 3 ∧ c'.nreg 211016 = 0 ∧ c'.nreg 211017 = 2 ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hS0, hS1, hT, hSE⟩ := hS
  zufak
  have hμl := nextLvl_lt h16
  have hcb := Setup.ceilBeta_eq
  have hμ : nextLvl lam = zttru / 5 + 11 := by unfold nextLvl; rw [hcb]
  have hb12 : Cost.ceilBeta ztmc + 12 ≤ nextLvl lam := by_grind
  have t1 : c.nmem _ = Cost.ceilBeta lam := (hT lam by_omega).2
  have t2 : c.nmem _ = Cost.ceilBeta ztmc :=
    (hT _ by_omega).2
  have t3 : c.nmem _ = 2 ^ nextLvl lam := (hT _ by_omega).1
  have t4 : c.nmem _ =
      2 ^ ztwqe := (hT _ by_omega).1
  have t5 : c.nmem _ =
      2 ^ ztwnz := (hT _ by_omega).1
  have hpW : p + 1 ≤ W := by_omega
  have w5 := hw.2 (S + 2 + ztwnz)
  rw [t5] at w5
  have hpow : 2 ^ ztwnz = 4 * 2 ^ ztwqe := by
    grind
  have hμ' : Cost.ceilBeta lam + 11 = nextLvl lam := rfl
  have w3 := hw.2 (S + 2 + nextLvl lam)
  rw [t3] at w3
  have wm := hw.2 ztki
  have cb1 := Cost.ceilBeta_le lam
  have cb2 := Cost.ceilBeta_le ztmc
  have hAW' := hAW
  have t4' : c.nmem (S + 2 + Cost.ceilBeta ztmc + 10) =
      2 ^ ztwqe := by
    omega
  have t5' : c.nmem (S + 2 + Cost.ceilBeta ztmc + 10 + 2) =
      2 ^ ztwnz := by
    omega
  unfold lvParA
  exec_block
  all_goals try (config_simp; (try simp only [h0, hl, h1, hS1, t1, hμ', t2, t3, t4', t5']); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    config_simp <;> (try simp only [h0, hl, h1, hS1, t1, hμ', t2, t3, t4', t5']); grind

/-- The `LeftInside` bit, normalized: `1` iff the word is `1`. -/
def lvParB : Stmt :=
  .ifLtN 211025 211017 (.ifLtN 211016 211025 (.instr (.constN 211008 1)) .skip) .skip

/-- The table of the regions (three words per region) and the loop registers. -/
def lvParC : Stmt :=
  block [.copyN 211009 9999, .addN 211011 210003 211014, .addN 211026 211011 211011,
    .addN 211026 211026 211011, .addN 9999 9999 211026, .constN 211010 0, .constN 211012 0,
    .constN 211013 0]
theorem lvParB_exec (c : Config) (hw : WordsBounded W c) (h16 : c.nreg 211016 = 0)
    (h17 : c.nreg 211017 = 2) (h08 : c.nreg 211008 = 0) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W lvParB c c' k ∧ k ≤ 4 ∧ c'.nreg 211008 ≤ 1 ∧
      (c'.nreg 211008 = 1 ↔ c.nreg 211025 = 1) ∧
      (∀ r, r ≠ 211008 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lvParB
  by_cases ha : c.nreg 211025 < c.nreg 211017
  · by_cases hb : c.nreg 211016 < c.nreg 211025
    · have e := Exec.constN (P := P) hw 211008 1 hW
      refine ⟨_, _, .ifLtN_true ha (.ifLtN_true hb e), by_omega, by_simp, ?_, by_simp_all, rfl, rfl, rfl, rfl⟩
      zuoco; omega
    · refine ⟨_, _, .ifLtN_true ha (.ifLtN_false hb ztjd), by_omega, by_omega, ?_,
        by omega, rfl, rfl, rfl, rfl⟩
      omega
  · refine ⟨_, _, .ifLtN_false ha ztjd, by_omega, by_omega, ?_, by_omega, rfl, rfl,
      rfl, rfl⟩
    omega

/-- The registers `lvParC` writes. -/
def BparC (r : ℕ) : Bool :=
  decide (211009 ≤ r ∧ r ≤ 211013) || decide (r = 211026) || decide ztyc
theorem wr_lvParC : SignK.wr BparC lvParC = true := by_decide
theorem lvParC_exec (c : Config) (hw : WordsBounded W c) {K : ℕ} (h03 : c.nreg 210003 = K)
    (h14 : c.nreg 211014 = 1) (hW : c.nreg ALLOC + 3 * ztbr ≤ W) :
    ∃ c' k, Exec P W lvParC c c' k ∧ k = 8 ∧ c'.nreg 211009 = c.nreg 9999 ∧
      c'.nreg 211011 = K + 1 ∧ c'.nreg 9999 = c.nreg 9999 + 3 * ztbr ∧
      c'.nreg 211010 = 0 ∧ c'.nreg 211012 = 0 ∧ c'.nreg 211013 = 0 ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hA : ztyue := hW
  unfold lvParC
  exec_block
  all_goals try (config_simp; (try simp only [h03, h14]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> (try simp only [h03, h14]);
    grind

/-- **The parameters of the level** and the region table. -/
def lvPar : Stmt := .seq lvParA (.seq lvParB (.seq lvParC (padS 211009)))
theorem lvPar_exec (c : Config) (hw : WordsBounded W c) {S n lam MD K : ℕ}
    (h0 : c.nreg 230000 = S) (hl : c.nreg 210000 = lam) (h1 : c.nreg 210001 = MD)
    (h03 : c.nreg 210003 = K)
    (hS : SetupAt c.nmem S n ztm) (h16 : 16 ≤ lam) (hlp : lam ≤ topGrade n)
    (hMD : MD + 6 ≤ c.nreg ALLOC) (hAW : c.nreg ALLOC + 3 * ztbr ≤ W) (hW : 11 ≤ W) :
    ∃ c' k, Exec P W lvPar c c' k ∧ k ≤ 9 * ztbr + 46 ∧
      c'.nreg 211000 = S ∧ c'.nreg 211001 = topGrade n ∧ c'.nreg 211002 = nextLvl lam ∧
      c'.nreg 211003 = Cost.ceilBeta ztmc ∧ c'.nreg 211004 = 2 ^ nextLvl lam ∧
      c'.nreg 211006 = 3 * 2 ^ ztwqe ∧
      c'.nreg 211007 = 2 ^ ztwnz ∧
      c'.nreg 211008 ≤ 1 ∧ (c'.nreg 211008 = 1 ↔ c.nmem ztki = 1) ∧
      c'.nreg 211014 = 1 ∧ c'.nreg 211015 = 3 ∧ c'.nreg 211016 = 0 ∧ c'.nreg 211017 = 2 ∧
      c'.nreg 211009 = c.nreg ALLOC ∧ c'.nreg 211011 = K + 1 ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * ztbr ∧
      c'.nreg 211010 = 0 ∧ c'.nreg 211012 = 0 ∧ c'.nreg 211013 = 0 ∧ WordsBounded W c' ∧
      (∀ q, ztoew → q ≠ 210068 → q ≠ 210069 → q ≠ ALLOC →
        c'.nreg q = c.nreg q) ∧
      c'.nmem = c.nmem ∧ Frame {bDownDrv} c c' k := by
  obtain ⟨c₁, k₁, e₁, hk₁, a00, a01, a02, a03, a04, a05, a06, a07, a25, a08, a14, a15, a16, a17,
    m₁, rr₁, rm₁, o₁⟩ :=
    lvParA_exec (P := P) c hw h0 hl h1 hS h16 hlp hMD by_omega hW
  have g₁ := exec_frameB e₁ wr_lvParA
  obtain ⟨c₂, k₂, e₂, hk₂, b08, b08', g₂, m₂, rr₂, rm₂, o₂⟩ :=
    lvParB_exec (P := P) c₁ e₁.wb_right a16 a17 a08 by_omega
  have u₂ := fun r h h' =>
    (g₂ r h).trans (g₁.1 r h')
  have q03 : c₂.nreg 210003 = K := by rw [u₂ _ by_decide by_decide, h03]
  have q14 : c₂.nreg 211014 = 1 := by_simp_all
  have qA : c₂.nreg 9999 = c.nreg 9999 := u₂ _ by_decide by_decide
  have hA9 : ztyue := hAW
  obtain ⟨c₃, k₃, e₃, hk₃, d09, d11, d99, d10, d12, d13, m₃, rr₃, rm₃, o₃⟩ :=
    lvParC_exec (P := P) c₂ e₂.wb_right q03 q14 (by show c₂.nreg 9999 + 3 * ztbr ≤ W; omega)
  have g₃ := exec_frameB e₃ wr_lvParC
  obtain ⟨c₄, e₄, g₄, rr₄, m₄, rm₄, o₄, w₄⟩ :=
    padS_exec (P := P) (src := 211009) e₃.wb_right by_simp_all
      by_omega
  have v : ∀ r, Bpar r = false → BparC r = false → r ≠ 211008 → r ≠ 210068 → r ≠ 210069 →
      c₄.nreg r = c.nreg r := fun r h1 h2 h3 h4 h5 =>
    (g₄ r h4 h5).trans ((g₃.1 r h2).trans by_grind)
  have k4 : 3 * (c₃.nreg 9999 - c₃.nreg 211009) + 4 = 9 * ztbr + 4 := by
    omega
  rw [k4] at e₄
  have ex : Exec P W lvPar c c₄ _ :=
    .seq e₁ ztcb
  have w₃ := g₃.1
  have v32 : ∀ r, BparC r = false → r ≠ 210068 → r ≠ 210069 → c₄.nreg r = c₂.nreg r :=
    by grind
  have hmm : zteid := by_grind
  have hA4 : c₄.nreg 9999 = c.nreg 9999 + 3 * ztbr := by
    grind
  have hreg : ∀ q, ztoew → q ≠ 210068 → q ≠ 210069 → q ≠ ALLOC →
      c₄.nreg q = c.nreg q := fun q hq h68 h69 hA => v q
    (by simp only [Bpar, decide_eq_false_iff_not]; omega)
    (by simp only [BparC, Bool.or_eq_false_iff, decide_eq_false_iff_not]; unfold ALLOC at hA; omega)
    by_omega h68 h69
  refine ⟨c₄, _, ex, by_omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hA4, ?_, ?_, ?_, w₄, hreg, hmm, ?_⟩
  · zubr
  · zubr
  · zubr
  · zubr
  · zubr
  · zubr
  · zubr
  · rw [v32 _ by_decide by_decide by_decide]; omega
  · rw [v32 _ by_decide by_decide by_decide, b08', a25]
  · zubr
  · zubr
  · zubr
  · zubr
  · rw [g₄ _ by_decide by_decide, d09, qA]; rfl
  · grind
  · grind
  · grind
  · grind
  · refine ⟨fun r hr hrA => hreg r ?_ ?_ ?_ hrA, by_grind,
      by grind, by_grind, by_grind,
      by show c.nreg 9999 ≤ c₄.nreg 9999; omega,
      by show c₄.nreg 9999 ≤ c.nreg 9999 + _; omega⟩
    all_goals (simp only [Finset.mem_singleton, bandOf, bDownDrv] at hr; omega)
end exec
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine
open BuildNF (codeLe)
open SortL (seg)
@[expose] public section
def StateAt (P : Polygon) (c : Config) (L : List zte) (E : List ℕ) : Prop :=
  rd c bDownDrv 1 + 6 ≤ c.nreg ALLOC ∧
    Robust ztm c.nmem
      ztbang ∧
    rd c bDownDrv 3 = L.length ∧
    rd c bDownDrv 2 + 3 * L.length ≤ c.nreg ALLOC ∧
    Robust ztm c.nmem ztyqo ∧
    rd c bDownDrv 4 + 2 * L.length ≤ c.nreg ALLOC ∧
    Robust ztm c.nmem ztyew ∧
    ChordTriplesOK ztwiq zta L ∧
    E.Perm ztct ∧
    E.Pairwise ztbajl ∧
    NFWithin c.nmem ztrvg ztm
      ztbaja

/-- **The contract of the restoration rounds (D8)**, for interior oracles of costs `F`, `G`, `H`
on the context `X`. -/
def RoundsSpec (X : MemCtx) (F G H : ℕ → ℕ) : Prop :=
  ∃ (s : Stmt) (κ : ℕ → ℕ), Meets s drvBands
    (fun P W c => EnvD X P W c ∧ 4 ≤ c.nreg 216000 ∧ 1 ≤ c.nreg 216001 ∧
      c.nreg 216001 ≤ P.n - 1 ∧
      ∃ (L : List zte) (E : List ℕ), StateAt P c L E ∧
        (interiorModel zta).DegLe
          ((BuildNF.buildNF ztwiq zta L E).F ztwiq
            zta) (c.nreg 216000) ∧
        (interiorModel zta).Semigranular
          ((BuildNF.buildNF ztwiq zta L E).F ztwiq
            zta) (c.nreg 216001))
    (fun P c c' =>
      (∀ r, (r = 210000 ∨ r = 210001 ∨ 211000 ≤ r ∧ r < 216000 ∨ 217000 ≤ r ∧ r < 220000) →
        c'.nreg r = c.nreg r) ∧
      ∀ (L : List zte) (E : List ℕ), StateAt P c L E →
        ∃ (L' : List zte) (E' : List ℕ), StateAt P c' L' E' ∧
          (BuildNF.buildNF ztwiq zta L E).F ztwiq zta ⊆
            (BuildNF.buildNF ztwiq zta L' E').F ztwiq
              zta ∧
          (interiorModel zta).DegLe
            ((BuildNF.buildNF ztwiq zta L' E').F ztwiq
              zta) 4 ∧
          (interiorModel zta).Semigranular
            ((BuildNF.buildNF ztwiq zta L' E').F ztwiq
              zta) (c.nreg 216001) ∧
          L'.length + 1 ≤ 2 ^ c.nreg 216000 * ztkr)
    (fun _ c => κ zteqw * ztcix * F ztbuu *
      G ztbuu * ztwxa)
end
end DrvR
namespace DownBase
open Machine Machine.Stmt Programs SortL
open BuildNF (codeLe)
@[expose] public section
theorem tw_eq (L' : List zte) (i q : ℕ) (hq : q < 3) :
    tw L' ztgcm = if q = 0 then (L'.getD i ztt).1
      else if q = 1 then (L'.getD i ztt).2.1 else (L'.getD i ztt).2.2 := by
  unfold tw
  rw [show ztgcm % 3 = q by omega, show ztgcm / 3 = i by omega]
theorem mem1_zero (m₀ : ℕ → ℕ) (li : Bool) (n : ℕ) (L : List zte) (B' X a : ℕ) :
    mem1 m₀ li n L B' X 0 a = m₀ a := by
  zulby
  have h0 : rankF ztse L 0 = 0 := by_rfl
  grind
variable {m₀ : ℕ → ℕ} {li : Bool} {n : ℕ} {L : List (ℕ × ℕ × ℕ)} {B' X i a : ℕ} {m₁ : ℕ → ℕ}
theorem mem1_low
    (h1 : a < B') (h2 : a < X) : mem1 m₀ li n L B' X i a = m₀ a := by
  zulby
  grind
theorem mem1_list
    (h1 : B' ≤ a) (h2 : a < B' + 3 * rankF ztse L i) :
    mem1 m₀ li n L B' X i a = tw ztdou ztjnv := by
  zulby
  simp_all
theorem mem2_low {li : Bool} {n : ℕ} {L : List zte} {E : List ℕ}
    {SE' t a : ℕ} (h : a < SE') : mem2 m₁ li n L E SE' t a = m₁ a := by
  zulbz
  simp_all
theorem mem2_in {li : Bool} {n : ℕ} {L : List zte} {E : List ℕ}
    {SE' t a : ℕ} (h1 : SE' ≤ a) (h2 : a < SE' + (dropE li n L ztffi).length) :
    mem2 m₁ li n L E SE' t a = (dropE li n L ztffi).getD zttek 0 := by
  zulbz
  simp_all
set_option maxHeartbeats 16000000 in
/-- **A1: `DropAugSpec`.** -/
theorem dropAug : DropAugSpec := by
  refine ⟨dropStmt, 80, ?_⟩
  zulq
  obtain ⟨hG, hWn, hDA, hli, L, hlen, hBL, hCL, hok, hSEL, hperm, hsort⟩ := hpre
  zvnhj at hDA hli hlen hBL hCL hSEL hperm hsort hcost ⊢
  zukzj
  set D := c.nreg 200000 with hD
  set B := c.nreg 200001 with hB
  set SE := c.nreg 200003 with hSE
  zuce
  zubfv
  set li := liBit c.nmem D with hlidef
  set E := seg c.nmem SE ztbds with hEdef
  have hEl : ztgtw := seg_length
  set X := A₀ + 3 * K with hX
  set SE' := A₀ + 5 * K with hSE'
  have hcost' : A₀ + 80 * ztbr ≤ W := by
    omega
  have hnW : ztfku := by unfold hostWords at hWn; omega
  zuc
  -- setup
  obtain ⟨c₁, k₁, e₁, hk₁, s100, s101, s105, s104, s106, s103, s136, s004, s121, s122, s9999,
      s006, s110, s111, s117, s118, s119, sfr, sin, sm, srr, srm, so⟩ :=
    dSetup_exec (P := P) c hw rfl rfl hlen hA by_omega by_omega hnW
  -- the bit
  obtain ⟨c₂, k₂, e₂, hk₂, b103, bfr, bm, brr, brm, bo⟩ :=
    dBit_exec (P := P) c₁ e₁.wb_right by_omega s106 s105 s101 s103
  have g21 : ∀ r, r ≠ 200103 → c₂.nreg r = c₁.nreg r := bfr
  -- the chord pass
  have hI₁ : Inv1 c.nmem li P.n L B A₀ X c₂ c₂ :=
    { i_le := by_grind
      rK := by_grind
      r111 := by_grind
      r117 := by_grind
      r118 := by
        rw [g21 _ by_norm_num, g21 _ by_norm_num, s118, s110]; rfl
      r119 := by
        rw [g21 _ by_norm_num, g21 _ by_norm_num, s119, s110]; rfl
      r100 := by_grind
      r101 := by_grind
      r103 := by rw [b103]; simp [hlidef, liBit]; rfl
      r104 := by_grind
      fr := fun _ _ => rfl
      rr := rfl
      rm := rfl
      out := rfl
      mem := fun a => by
        rw [bm, sm, g21 _ by_norm_num, s110]
        exact (mem1_zero c.nmem li P.n L A₀ X a).symm }
  obtain ⟨c₃, k₃, e₃, hw₃, hI₃, h3i, hk₃, hk₃'⟩ := dLoop1_exec (P := P) hCL by_omega rfl
    by_omega e₂.wb_right hI₁ by_grind
  -- between the passes
  obtain ⟨c₄, k₄, e₄, hk₄, m005, m130, m131, m134, mfr, mm, mrr, mrm, mo⟩ :=
    dMid_exec (P := P) c₃ hw₃
  -- registers of `c₃` outside the chord-pass scratch
  have g3 : ∀ r, zthjs → r ≠ 200103 → c₃.nreg r = c₁.nreg r :=
    fun r hr h103 => by rw [hI₃.fr r hr, g21 r h103]
  set m₁ := mem1 c.nmem li P.n L A₀ X K with hm₁
  have hI₂ : Inv2 m₁ li P.n L E SE X SE' c₄ c₄ :=
    { t_le := by_omega
      r136 := by
        grind
      r131 := by
        grind
      r134 := by
        rw [m134, m130, g3 _ by_norm_num by_norm_num, s122]
        rfl
      r121 := by
        grind
      r100 := by_grind
      r101 := by_grind
      fr := fun _ _ => rfl
      rr := rfl
      rm := rfl
      out := rfl
      mem := fun a => by
        rw [mm, hI₃.mem, h3i, m130]
        zulbz
        simp only [dropE, List.take_zero, List.filter_nil, List.map_nil, List.length_nil,
          Nat.add_zero]
        zvmyd }
  have hrk : rankF zttqr L K ≤ K := rankF_le _ _ _
  obtain ⟨c₅, k₅, e₅, hw₅, hI₅, h5t, hk₅, hk₅'⟩ := dLoop2_exec (P := P) (m₁ := m₁)
    (fun t ht => by
      zujjl
      zvmyn
      exact BuildRam.seg_getD rfl by_omega)
    by_omega
    (fun c' hc' => by
      zujjl
      rw [ite_eq_right by_omega, ite_eq_left by_omega, Nat.add_sub_cancel_left])
    by_omega hEl hperm by_omega e₄.wb_right hI₂ m130
  -- the final configuration
  have g5 : ∀ r, zthjt → c₅.nreg r = c₄.nreg r := hI₅.fr
  have g51 : ∀ r, (r < 200110 ∨ 200135 < r) → r ≠ 200005 → r ≠ 200103 →
      c₅.nreg r = c₁.nreg r := fun r hr h5 h3 => by
    rw [g5 r by_omega, mfr r h5 by_omega by_omega by_omega, g3 r by_omega h3]
  have f004 : c₅.nreg 200004 = A₀ := by
    rw [g51 _ by_norm_num by_norm_num by_norm_num, s004]
  have f006 : c₅.nreg 200006 = SE' := by
    rw [g51 _ by_norm_num by_norm_num by_norm_num, s006]
  have f9999 : c₅.nreg 9999 = A₀ + 7 * K := by
    rw [g51 _ by_norm_num by_norm_num by_norm_num, s9999]
  set L' := keepL li P.n L with hL'
  have hL'len : L'.length = rankF zttqr L K := (rankF_length _ _).symm
  have f005 : c₅.nreg 200005 = L'.length := by
    rw [g5 _ by_norm_num, m005, hI₃.r118, h3i, hL'len]
  have hK' : L'.length ≤ K := by_omega
  have hK2 : (keepL li P.n L).length ≤ K := hK'
  have hmem5 : ∀ a, c₅.nmem a = mem2 m₁ li P.n L E SE' E.length a := fun a => by
    rw [hI₅.mem, h5t]
  have hEt : E.take E.length = E := List.take_length
  have hdlen : (dropE li P.n L E).length = 2 * L'.length := by
    have := (dropE_perm (li := li) (n := P.n) hperm).length_eq
    grind
  have hCL' : ChordListAt c₅.nmem A₀ L' := by
    zug
    have hm : ∀ q, q < 3 → c₅.nmem (A₀ + 3 * i + q) = tw L' ztgcm := fun q hq => by
      rw [hmem5, mem2_low by_omega, hm₁, mem1_list by_omega by_omega,
        show A₀ + 3 * i + q - A₀ = 3 * i + q by omega]
    zusk
    · have := hm 0 by_norm_num
      rw [Nat.add_zero, Nat.add_zero] at this
      rw [this, show 3 * i = 3 * i + 0 from rfl, tw_eq L' i 0 by_norm_num]
      rfl
    · rw [hm 1 by_norm_num, tw_eq L' i 1 by_norm_num]
      rfl
    · rw [hm 2 by_norm_num, tw_eq L' i 2 by_norm_num]
      rfl
  have hseg : seg c₅.nmem SE' (2 * L'.length) = dropE li P.n L E := by
    zuhrr
    · rw [seg_length, hdlen]
    · intro u h1 h2
      simp only [seg, List.getElem_map, List.getElem_range]
      rw [hmem5, mem2_in by_omega by_grind, hEt, List.getD_eq_getElem?_getD,
        Nat.add_sub_cancel_left, List.getElem?_eq_getElem h2, Option.getD_some]
  -- the math
  zucm
  zuyq
  have hli' : ztzjk := by
    rw [hlidef]
    simp only [liBit, decide_eq_true_eq]
    omega
  have hfam := family_keepL hQ hDH hli' hok
  zvmxg at hfam
  have X' : Exec P W dropStmt c c₅ ztbamf :=
    .seq e₁ ztbq
  refine ⟨c₅, _, X', ?_, fun L₂ hlen₂ hL₂ => ?_, ?_⟩
  · omega
  · obtain rfl := BuildNF.chordListAt_unique hCL hL₂ (hlen.symm.trans hlen₂)
    zujih
    refine ⟨by_grind, ?_, by_grind, f005, ?_, ?_, by_grind,
      hfam, chordTriplesOK_keepL hok, dropE_perm hperm, dropE_pairwise _ _ hperm hsort⟩
    · rw [f004]; show _ ≤ c₅.nreg 9999; grind
    · grind
    · rw [f006]; show _ ≤ c₅.nreg 9999; grind
  · zuife
    · have hr' : r < 200000 ∨ 210000 ≤ r := by
        simp only [Finset.mem_singleton, bandOf] at hr
        omega
      rw [g51 r by_omega by_omega by_omega, sfr r hr' hra]
    · rw [hI₅.rr, mrr, hI₃.rr, brr, srr]
    · zufuh
      rw [hmem5, mem2_low by_omega, hm₁, mem1_low by_omega by_omega]
    · rw [hI₅.rm, mrm, hI₃.rm, brm, srm]
    · rw [hI₅.out, mo, hI₃.out, bo, so]
    · show A₀ ≤ c₅.nreg 9999
      grind
    · show c₅.nreg 9999 ≤ A₀ + _
      grind
end
end DownBase
end Chazelle.Core
namespace Chazelle.Core
namespace DrvG
open DrvR
@[expose] public section
def GapsLe (B : ℕ) : List zte → ℕ → ℕ → Prop
  | [], e, M => e ≤ M ∧ M ≤ e + B
  | x :: L, e, M => e ≤ x.1 ∧ x.1 ≤ e + B ∧ GapsLe B L ztbui M

/-- The end of the last leaf (`e` if none). -/
def lastEnd : List zte → ℕ → ℕ
  | [], e => e
  | x :: L, _ => lastEnd L ztbui
theorem gapsLe_append {B : ℕ} : ∀ (L₁ L₂ : List zte) (e M M₁ : ℕ),
    GapsLe B L₁ e M₁ → GapsLe B L₂ zttrv M → GapsLe B zthrg e M
  | [], _L₂, _e, _M, _M₁, _, h₂ => h₂
  | x :: L₁, L₂, _e, M, M₁, ⟨h1, h2, h3⟩, h₂ =>
    ⟨h1, h2, gapsLe_append L₁ L₂ ztbui M M₁ h3 h₂⟩
theorem gapsLe_mono {B B' : ℕ} (hB : B ≤ B') : ∀ (L : List zte) (e M : ℕ),
    GapsLe B L e M → GapsLe B' L e M
  | [], e, M, ⟨h1, h2⟩ => ⟨h1, by_omega⟩
  | x :: L, e, M, ⟨h1, h2, h3⟩ => ⟨h1, by_omega, gapsLe_mono hB L _ M h3⟩
theorem lastEnd_append : ∀ (L₁ L₂ : List zte) (e : ℕ),
    lastEnd zthrg e = lastEnd L₂ zttrv
  | [], _, _ => rfl
  | x :: L₁, L₂, _ => lastEnd_append L₁ L₂ ztbui

/-- **The pieces of a segment** from `s`, contiguous, ending at `s + L`, seen from any `e ≤ s`
at most `B` edges before `s`. -/
theorem chunks_gaps {C : ℕ} (hC : 1 ≤ C) : ∀ (L s a e B : ℕ), 1 ≤ L → e ≤ s → s ≤ e + B →
    GapsLe B ztjsu e ztny ∧ lastEnd ztjsu e = s + L := by
  zumgg
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro s a e B hL he hB
    rw [chunks_cons hC hL]
    zujsb
    · rw [min_eq_right h, Nat.sub_self, chunks_zero]
      refine ⟨⟨he, hB, ?_, ?_⟩, rfl⟩ <;> simp only <;> omega
    · zulqn
      obtain ⟨h1, h2⟩ := ih zthbe by_omega _ ztjnt ztkee B by_omega ztbhw
        by_omega
      rw [show s + C + zthbe = s + L by omega] at h1 h2
      tauto

/-- A run is **degenerate** when its only interior edge is the wrap-around edge
`v_{n-1} v_0`. -/
def Degen (n a ℓ : ℕ) : Prop := ℓ = 3 ∧ ztdf % n = n - 1
instance (n a ℓ : ℕ) : Decidable (Degen n a ℓ) := by unfold Degen; infer_instance
variable {n C p a ℓ : ℕ}
/-- **The leaves of a run**: none if the run is short or degenerate; otherwise they start at
most two points after the first point of the run, are separated by at most one edge, and end at
most two points before its last point. -/
theorem runLeaves_gaps (hC : 1 ≤ C) (hn : 2 ≤ n) (hℓ : ℓ < n) :
    (runLeaves n C p a ℓ = [] ∧ (ℓ < 3 ∨ Degen n a ℓ)) ∨
      (3 ≤ ℓ ∧ ¬ Degen n a ℓ ∧ ∀ e, e ≤ p + 1 →
        GapsLe zteuj ztdvz e (lastEnd ztdvz e) ∧
        p + ℓ - 2 ≤ lastEnd ztdvz e ∧
        lastEnd ztdvz e ≤ p + ℓ - 1) := by
  zuiao
  by_cases h3 : ℓ < 3
  · left; exact ⟨by unfold runLeaves; simp_all, Or.inl h3⟩
  by_cases hdg : Degen n a ℓ
  · left
    refine ⟨?_, Or.inr hdg⟩
    obtain ⟨hl, hm⟩ := hdg
    unfold runLeaves
    rw [ite_eq_right h3, ite_eq_right by_omega, hm, show n - 1 - ztkl = 0 by omega, chunks_zero,
      show ℓ - 2 - (n - ztkl) = 0 by omega, chunks_zero]
    rfl
  right
  refine ⟨by_omega, hdg, fun e he => ?_⟩
  have hDg : ¬ (ℓ = 3 ∧ ztdf % n = n - 1) := hdg
  unfold runLeaves
  rw [ite_eq_right h3]
  split_ifs with hw
  · obtain ⟨g1, g2⟩ := chunks_gaps hC ztdit _ ztwwo e zteuj by_omega he
      by_omega
    grind
  · by_cases h1 : n - 1 - ztdf % n = 0
    · have h2 : 1 ≤ ℓ - 2 - ztwkq := by_omega
      rw [h1, chunks_zero, List.nil_append]
      obtain ⟨g1, g2⟩ := chunks_gaps hC _ ztbajv 0
        e zteuj h2 by_omega by_omega
      grind
    · obtain ⟨g1, g2⟩ := chunks_gaps hC ztwqo _ _ e zteuj
        by_omega he by_omega
      by_cases h2 : ℓ - 2 - ztwkq = 0
      · rw [h2, chunks_zero, List.append_nil, g2]
        grind
      · obtain ⟨k1, k2⟩ := chunks_gaps hC ztbajw ztbajv 0
          (p + 1 + ztwqo) zteuj by_omega by_omega by_omega
        have hl : lastEnd (chunks C ztr ztwwo ztwqo ++
            chunks C ztbajv 0 ztbajw) e =
            p + 1 + ztwkq + ztbajw := by
          rw [lastEnd_append, g2, k2]
        zudug
        refine ⟨gapsLe_append _ _ e _ _ g1 ?_, by_omega, by_omega⟩
        grind

/-! ## The gaps of a host -/

/-- The number of degenerate runs of a host. -/
def degCount (n : ℕ) : Host → ℕ
  | [] => 0
  | .run a ℓ :: H => ztlpy + degCount n H
  | .pt _ :: H => degCount n H
theorem hostLeaves_gapsG {n C : ℕ} (hC : 1 ≤ C) (hn : 2 ≤ n) : ∀ (H : Host) (p e k d : ℕ),
    HostWF n H → e ≤ p → p ≤ e + 3 * k + d + 3 → k + H.length ≤ 20 → d + degCount n H ≤ 1 →
    e + 1 ≤ p + (H.pts n).length →
    GapsLe 64 (hostLeaves n C p H) e (p + (H.pts n).length - 1)
  | [], p, e, k, d, _, h1, h2, h3, h4, h5 => by
    simp only [hostLeaves, Host.pts, List.flatMap_nil, List.length_nil, Nat.add_zero] at h5 ⊢
    simp only [List.length_nil] at h3
    exact ztgy
  | .pt x :: H, p, e, k, d, hwf, h1, h2, h3, h4, h5 => by
    zufhf
    have hl : (Host.pts n (HostItem.pt x :: H)).length = (Host.pts n H).length + 1 := by
      rfl
    zucpw

    rw [hostLeaves, show p + ((Host.pts n H).length + 1) - 1 = p + 1 + (Host.pts n H).length - 1 by
      omega]
    exact hostLeaves_gapsG hC hn H _ e zts d hwf' by_omega by_omega by_omega h4
      by_omega
  | .run a ℓ :: H, p, e, k, d, hwf, h1, h2, h3, h4, h5 => by
    zufhf
    have hit := hwf _ (List.mem_cons_self ..)
    zujpe
    have hl : (Host.pts n (HostItem.run a ℓ :: H)).length = (Host.pts n H).length + ℓ + 1 := by
      zunhn; omega
    zucpw

    rw [hostLeaves, show p + ((Host.pts n H).length + ℓ + 1) - 1 =
      p + ℓ + 1 + (Host.pts n H).length - 1 by omega]
    rcases runLeaves_gaps (p := p) hC hn hit.2 with ⟨he, hsh⟩ | ⟨h3l, hdg, hg⟩
    · rw [he, List.nil_append]
      have hd : ℓ + 1 ≤ 3 + ztlpy := by
        rcases hsh with h | hdg'
        · omega
        · rw [ite_eq_left hdg']; have := hdg'.1; omega
      exact hostLeaves_gapsG hC hn H _ e zts (d + if Degen n a ℓ then 1 else 0)
        hwf' by_omega by_omega by_omega by_omega by_omega
    · obtain ⟨g1, g2, g3⟩ := hg e by_omega
      rw [ite_eq_right hdg] at h4
      refine gapsLe_append _ _ e _ _ (gapsLe_mono by_omega _ _ _ g1) ?_
      exact hostLeaves_gapsG hC hn H _ _ 0 d hwf' by_omega by_omega by_omega
        by_omega by_omega

/-- **The gaps of a host** of at most `20` items with at most one degenerate run are at most `64`
edges. -/
theorem hostLeaves_gaps {n C : ℕ} (hC : 1 ≤ C) (hn : 2 ≤ n) {H : Host} (hwf : HostWF n H)
    (hl : H.length ≤ 20) (hd : degCount n H ≤ 1) (hp : 1 ≤ (H.pts n).length) :
    GapsLe 64 (hostLeaves n C 0 H) 0 ((H.pts n).length - 1) := by
  have := hostLeaves_gapsG hC hn H 0 0 0 0 hwf ztbhw by_omega by_omega by_omega
    by_omega
  simp_all

/-! ## At most one degenerate run -/
theorem degCount_first (n : ℕ) : ∀ H : Host, 1 ≤ degCount n H →
    ∃ H₁ a ℓ H₂, H = H₁ ++ HostItem.run a ℓ :: H₂ ∧ Degen n a ℓ ∧
      degCount n H₂ + 1 = degCount n H
  | [], h => by_tauto
  | .pt x :: H, h => by
    simp only [degCount] at h
    obtain ⟨H₁, a, ℓ, H₂, e, hd, hc⟩ := degCount_first n H h
    exact ⟨.pt x :: H₁, a, ℓ, H₂, by_simp_all, hd, by_tauto⟩
  | .run a ℓ :: H, h => by
    simp only [degCount] at h ⊢
    by_cases hd : Degen n a ℓ
    · exact ⟨[], a, ℓ, H, rfl, hd, by_grind⟩
    · rw [ite_eq_right hd] at h
      obtain ⟨H₁, a', ℓ', H₂, e, hd', hc⟩ := degCount_first n H by_omega
      grind

/-- **A simple host polygon has at most one degenerate run** (two would both contain the vertex
`v_{n-1}`). -/
theorem degCount_le_one {Q : Polygon} {H : Host} (hS : (H.poly Q).Simple) :
    degCount Q.n H ≤ 1 := by
  zukr
  obtain ⟨H₁, a, ℓ, H₂, e₁, hd, hc₁⟩ := degCount_first Q.n H by_omega
  have h₂ : 1 ≤ degCount Q.n H₂ := by_omega
  subst e₁
  obtain ⟨H₃, a', ℓ', H₄, rfl, hd', -⟩ := degCount_first Q.n H₂ h₂
  obtain ⟨hl, hm⟩ := hd
  obtain ⟨hl', hm'⟩ := hd'
  subst hl hl'
  set G := H₁ ++ HostItem.run a 3 :: (H₃ ++ HostItem.run a' 3 :: H₄) with hG
  have hG' : G = (H₁ ++ HostItem.run a 3 :: H₃) ++ HostItem.run a' 3 :: H₄ := by
    simp_all
  have p1 := DownMath.pts_append_run Q.n H₁ (H₃ ++ HostItem.run a' 3 :: H₄) a 3
    (k := 1) by_omega
  have p2 := DownMath.pts_append_run Q.n (H₁ ++ HostItem.run a 3 :: H₃) H₄ a' 3
    (k := 1) by_omega
  rw [← hG] at p1; rw [← hG'] at p2
  have l1 := DownMath.pts_append_run_length Q.n H₁ (H₃ ++ HostItem.run a' 3 :: H₄) a 3
  have l2 := DownMath.pts_append_run_length Q.n (H₁ ++ HostItem.run a 3 :: H₃) H₄ a' 3
  rw [← hG] at l1; rw [← hG'] at l2
  have l3 : (H₁.pts Q.n).length + 4 ≤ ((H₁ ++ HostItem.run a 3 :: H₃).pts Q.n).length := by
    rw [DownMath.pts_append, DownMath.pts_cons, List.length_append, List.length_append,
      DownMath.run_pts_length]; omega
  have v1 := DownMath.host_poly_vtx Q G (i := (H₁.pts Q.n).length + 1) by_omega
  have v2 := DownMath.host_poly_vtx Q G
    (i := ((H₁ ++ HostItem.run a 3 :: H₃).pts Q.n).length + 1) by_omega
  rw [p1, hm] at v1
  rw [p2, hm'] at v2
  have := hS.2.1 _ _ ztnsv ztnsv
    (v1.trans v2.symm)
  omega

/-! ## The number of leaves -/
theorem runLeaves_length_le (hC : 1 ≤ C) (hℓ : ℓ ≤ 2 * C) :
    (runLeaves n C p a ℓ).length ≤ 3 := by
  unfold runLeaves
  split_ifs with h3 hw
  · simp
  · have := chunks_length hC ztdit ztr ztwwo
    have h : (chunks C ztr ztwwo ztdit).length * C < 4 * C := by_omega
    have := Nat.lt_of_mul_lt_mul_right h
    omega
  · zujgr
    have h1 := chunks_length hC ztwqo ztr ztwwo
    have h2 := chunks_length hC ztbajw ztbajv 0
    have h : ((chunks C ztr ztwwo ztwqo).length +
        (chunks C ztbajv 0 ztbajw).length) * C <
        4 * C := by_grind
    have := Nat.lt_of_mul_lt_mul_right h
    omega

/-- **At most three leaves per run** of at most `2 C` edges. -/
theorem hostLeaves_length_le {n C : ℕ} (hC : 1 ≤ C) : ∀ (H : Host) (p : ℕ),
    zthlu → (hostLeaves n C p H).length ≤ 3 * H.length
  | [], _, _ => by_rfl
  | .pt x :: H, p, h => by
    rw [hostLeaves, List.length_cons]
    have := hostLeaves_length_le (n := n) hC H ztr
      by_grind
    omega
  | .run a ℓ :: H, p, h => by
    rw [hostLeaves, List.length_append, List.length_cons]
    have h1 := runLeaves_length_le (n := n) (p := p) (a := a) hC (h a ℓ (List.mem_cons_self ..))
    have := hostLeaves_length_le (n := n) hC H ztkbv
      by_grind
    omega
end
end DrvG
end Chazelle.Core
namespace Chazelle.Core
public section
theorem granularize : GranularizeSpec := Gran.granularize' buildNFOK
end
namespace Brute
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
def finS : Stmt :=
  block [.copyN 9999 180024, .copyN 40000 180017, .copyN 40001 180018, .copyN 40002 180019]

/-- The arguments of granularity enforcement. -/
def midS : Stmt := block [.copyN 90000 180017, .copyN 90001 40003, .constN 90002 4, .copyN 90003 180002]

/-- The output. -/
def outS : Stmt := .instr (.copyN 180003 90004)

/-- **The brute-force procedure.** -/
def bruteStmt (sB sG : Stmt) : Stmt :=
  .seq ztncv (.seq sB (.seq midS (.seq sG outS)))
variable {r : ℕ}
theorem bandOf_of_bm (h : Bm r = true) : bandOf r = bSign ∨ bandOf r = bBrute := by
  unfold Bm Bk at h
  zubzj
  unfold bandOf bSign bBrute
  omega
theorem bm_false_of_band (h : bandOf r ∉ bruteBands) : Bm r = false := by
  zudxc
  simp only [Bool.not_eq_false] at h'
  rcases bandOf_of_bm h' with e | e <;> zvmwe at h <;> exact h by_decide
theorem bbd_bm (h : Bm r = false) : Bbd r = false := by
  unfold Bm Bk at h; unfold Bbd Bk
  grind
set_option maxHeartbeats 4000000 in
/-- **Set-up, loop and hand-over.** -/
theorem prep_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {C : Chain}
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) (c : Config) (hw : WordsBounded W c)
    (h0 : c.nreg 180000 = C.s) (h1 : c.nreg 180001 = C.m)
    (hroom : c.nreg ALLOC + 10 + 6 * ztyw + 3 ≤ W) :
    ∃ c' k, Exec P W ztncv c c' k ∧
      k ≤ 260 * C.m + 1900 + (ztpuh * ztyw + 10) + 4 ∧
      c'.nreg 40000 = c.nreg ALLOC + 4 ∧ c'.nreg 40001 = c.nreg ALLOC + 10 ∧
      c'.nreg 40002 = (bruteList C).length ∧ c'.nreg 180017 = c.nreg ALLOC + 4 ∧
      c'.nreg 180002 = c.nreg 180002 ∧
      c'.nreg ALLOC = c.nreg ALLOC + 10 + 3 * (bruteList C).length ∧
      ChordListAt c'.nmem (c.nreg ALLOC + 10) ztmct ∧
      DescMem P C c'.nmem ztm ∧ Frame bruteBands c c' k := by
  have hWn : P.n + 2 * C.m + 8 ≤ W := by unfold hostWords at hWh; omega
  zuce
  obtain ⟨c₁, k₁, e₁, hk₁, lb₁, X₁, D₁, low₁, s19, s24, R₁, RR₁, RM₁, O₁⟩ := setup_exec (P := P) hG
    by_omega by_omega hC hsn c hw h0 h1 by_omega
  obtain ⟨c₂, k₂, e₂, hk₂, lb₂, X₂, t19, t24, tL, tM, R₂, RR₂, RM₂, O₂⟩ := loopS_exec (P := P) hG
    hWn ztdha hC hsn (γ := c.nreg 180002) (A₀ := A₀) by_omega c₁
    e₁.wb_right X₁ s19 s24
  have hlen := pre_length_le C ztyw
  rw [pre_full] at hlen
  obtain ⟨c₃, k₃, e₃, hk₃, q9999, q0, q1, q2, R₃, RR₃, M₃, RM₃, O₃⟩ : ∃ c₃ k₃, Exec P W finS c₂ c₃ k₃ ∧ k₃ = 4 ∧
      c₃.nreg 9999 = A₀ + 10 + 3 * (bruteList C).length ∧ c₃.nreg 40000 = A₀ + 4 ∧
      c₃.nreg 40001 = A₀ + 10 ∧ c₃.nreg 40002 = (bruteList C).length ∧
      (∀ r, r ≠ 9999 → r ≠ 40000 → r ≠ 40001 → r ≠ 40002 → c₃.nreg r = c₂.nreg r) ∧
      c₃.rreg = c₂.rreg ∧ c₃.nmem = c₂.nmem ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have w := e₂.wb_right
    unfold finS
    exec_block
    refine ztebd <;>
      zubs
    · omega
    · exact X₂.2.2.2.2.2.2.2.2.2.1
    · exact X₂.2.2.2.2.2.2.2.2.2.2.1
    omega
  have x17 := X₂.2.2.2.2.2.2.2.2.2.1
  refine ⟨c₃, _, .seq e₁ ztcr, by_omega, q0, q1, q2, ?_, ?_, q9999, ?_, ?_, ?_⟩
  · grind
  · rw [R₃ _ by_decide by_decide by_decide by_decide, X₂.2.2.1]
  · simp_all
  · rw [M₃]; exact descMem_agree D₁ by_omega
  · zuife
    · zuljq
      have h4 : r ≠ 40000 ∧ r ≠ 40001 ∧ r ≠ 40002 := by
        refine ztcg <;> rintro rfl <;> exact hr by_decide
      rw [R₃ r hra h4.1 h4.2.1 h4.2.2, R₂ r ztveu, R₁ r hb]
    · zuljq
      rw [RR₃, RR₂ r ztveu, RR₁ r hb]
    · grind
    · simp_all
    · simp_all
    · zujvq

    · zujvq

/-! ## Cost arithmetic -/
theorem f_le {m K : ℕ} (hK : K ≤ 2 * ztcsk) :
    K * ztho + 1 ≤ 30 * ztbl ^ 2 := by
  have hc := Cost.clog_two_le_self K
  have h1 : K * ztho ≤ K * ztbr := Nat.mul_le_mul_left _ by_omega
  have h2 :=
    Nat.mul_le_mul by_omega by_omega
  nlinarith
theorem cost_ok {m K κB κG : ℕ} (hm : 1 ≤ m) (hK : K ≤ 2 * ztcsk) :
    260 * m + 1900 + ((3300 * m + 1402) * ztcsk + 10) + 4 + 10 + 3 * K +
      κB * ztwko + 4 + κG * ztwko + 1 ≤
      (20000 + 30 * κB + 30 * κG) * ztbl ^ 3 := by
  have hf := f_le hK
  have hsq : ztbl ^ 2 ≤ ztbl ^ 3 := by_grind
  have hB : κB * ztwko ≤ 30 * κB * ztbl ^ 3 := by
    calc κB * ztwko ≤ κB * ztzbc := Nat.mul_le_mul_left _ hf
      _ ≤ κB * ztzbd := by_grind
      _ = 30 * κB * ztbl ^ 3 := by_ring
  have hG : κG * ztwko ≤ 30 * κG * ztbl ^ 3 := by
    calc κG * ztwko ≤ κG * ztzbc := Nat.mul_le_mul_left _ hf
      _ ≤ κG * ztzbd := by_grind
      _ = 30 * κG * ztbl ^ 3 := by_ring
  grind

/-- The chord family of a normal form built from a list is the family of the list. -/
theorem nfF_eq {M : Model} {Q : Polygon} {N : NF} {L : List zte}
    (h : N.chords.map ztwma = L) :
    N.F M Q = {c | ∃ x ∈ L, c = (recOf x).toSet M Q} := by
  zubcj
  simp only [NF.F, Set.mem_ofPred_eq, ← h, List.mem_map]
  constructor
  · tauto
  · zudtc
end
end Brute
open Brute Machine Machine.Stmt Programs in
set_option maxHeartbeats 8000000 in
/-- **WP-K: `BruteSpec`** — brute-force `γ`-canonical normal forms of chains. -/
public theorem brute : BruteSpec := by
  obtain ⟨sB, κB, hB⟩ := buildNFOK
  zugqt
  refine ⟨bruteStmt sB sG, 20000 + 30 * κB + 30 * κG 4, ?_⟩
  intro P W c hw ⟨hG, hWh, hm1, hsn, hγ1, hγ⟩ hroom
  zufqq
  have r0 : rd c bBrute 0 = c.nreg 180000 := rfl
  have r1 : rd c bBrute 1 = c.nreg 180001 := rfl
  have r2 : rd c bBrute 2 = c.nreg 180002 := rfl
  rw [r0, r1] at hsn
  zvnal at hm1 hroom
  zvnal at hγ
  rw [r2] at hγ1 hγ
  zuc
  let C : Chain := ⟨Qof P, c.nreg 180000, c.nreg 180001, hm1, by_omega⟩
  have hC : C.P = Qof P := rfl
  have hP : C.P.Simple := (shearInvariance _ P).1 hG.1
  have hDH := (goodShear_epsOf hG.2).2.1
  have hsnC : C.s + C.m + 1 ≤ P.n := hsn
  zuce
  set m := c.nreg 180001 with hmd
  set γ := c.nreg 180002 with hγd
  set K := (bruteList C).length with hKd
  have hK : K ≤ 2 * ztcsk := by
    have := pre_length_le C ztyw; rw [pre_full] at this; omega
  set f := K * ztho + 1 with hfd
  have hcost := cost_ok (κB := κB) (κG := κG 4) hm1 hK
  rw [← hfd] at hcost
  zuku
  -- 1. set-up, loop, hand-over
  obtain ⟨c₃, k₃, e₃, hk₃, q0, q1, q2, q17, q2γ, qA, qL, qD, F₃⟩ := prep_exec (P := P) hG hWh hC
    hsnC c hw rfl rfl by_nlinarith
  zufvv
  have hsP : ztpiv := by_omega
  -- 2. the normal form of the full map
  obtain ⟨hMD₃, hWF₃⟩ := descMem_model hC hn1 hsP qD (E := c₃.nreg ALLOC) by_omega
  zuiv
  obtain ⟨c₄, k₄, e₄, hk₄, post₄, F₄⟩ := hB P W c₃ e₃.wb_right
    ⟨hG, hWh, by show ModelDescWF P _ c₃.nmem ztqkm; grind,
      chainModel C, bruteList C, by show ModelDescAt c₃.nmem ztqkm _ _; grind,
      hGM, q2, by show c₃.nreg 40001 + 3 * K ≤ c₃.nreg ALLOC; omega,
      by show ChordListAt c₃.nmem ztvni _; grind, bruteList_ok hP hDH⟩
    (by show c₃.nreg ALLOC + κB * (c₃.nreg 40002 * (Nat.clog 2 (c₃.nreg 40002) + 1) + 1) ≤ W
        grind)
  obtain ⟨N, hA₄, hNW₄, hNF, hmap, -⟩ := post₄ ztc ztmct
    (by show ModelDescAt c₃.nmem ztqkm _ _; grind) q2
    (by show ChordListAt c₃.nmem ztvni _; grind)
  have hNlen : N.chords.length = K := by
    grind
  -- the band-18 registers survive the construction
  have k17 : c₄.nreg 180017 = A₀ + 4 := by
    rw [F₄.1 _ by_decide by_decide, q17]
  have k2 : c₄.nreg 180002 = γ := by rw [F₄.1 _ by_decide by_decide, q2γ]
  have hk4 : k₄ ≤ κB * f := by
    beta_reduce at hk₄
    have : rd c₃ bBuild 2 = K := q2
    grind
  have hA4 : c₄.nreg ALLOC ≤ c₃.nreg ALLOC + κB * f := by have := F₄.2.2.2.2.2.2; omega
  -- 3. the arguments of granularity enforcement
  obtain ⟨c₅, k₅, e₅, hk₅, p0, p1, p2, p3, R₅, RR₅, M₅, RM₅, O₅⟩ : ∃ c₅ k₅, Exec P W midS c₄ c₅ k₅ ∧
      k₅ = 4 ∧ c₅.nreg 90000 = A₀ + 4 ∧ c₅.nreg 90001 = rd c₄ bBuild 3 ∧ c₅.nreg 90002 = 4 ∧
      c₅.nreg 90003 = γ ∧
      (∀ r, r ≠ 90000 → r ≠ 90001 → r ≠ 90002 → r ≠ 90003 → c₅.nreg r = c₄.nreg r) ∧
      c₅.rreg = c₄.rreg ∧ c₅.nmem = c₄.nmem ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := by
    have w := e₄.wb_right
    unfold midS
    exec_block
    · omega
    · refine ztebd <;>
        zubs
      · omega
      · rfl
      omega
  have A₅ : ztcrj := R₅ _ by_decide by_decide by_decide by_decide
  have hlow₅ : ∀ x, x < c₃.nreg ALLOC → c₅.nmem x = c₃.nmem x := fun x hx => by
    rw [M₅]; exact F₄.2.2.1 x hx
  have qD₅ : DescMem P C c₅.nmem A₀ := descMem_agree qD by_grind
  obtain ⟨hMD₅, hWF₅⟩ := descMem_model hC hn1 hsP qD₅ (E := c₅.nreg ALLOC)
    (by zunji; have := F₄.2.2.2.2.2.1; omega)
  have hNW₅ : NFWithin c₅.nmem ztmif ztvnz N := by
    grind
  have hF : N.F ztc zta = C.chords := by rw [nfF_eq hmap]; exact bruteList_set hP hDH
  have hdeg : (chainModel C).DegLe ztwjq 4 := by
    zuguo
    have := fullDegLe_chain hP hDH zta ∅ ⟨Set.finite_empty, Set.empty_subset _,
      by grind⟩
    rwa [Set.union_empty] at this
  have hsemi : (chainModel C).Semigranular ztwjq γ := by
    zuguo
    exact fullMap_semigranular hP hDH by_grind
  have hK₅ : c₅.nmem ztmif = K := by zunuq; exact hNW₅.nfAt.1
  -- 4. granularity enforcement
  obtain ⟨c₆, k₆, e₆, hk₆, post₆, F₆⟩ := hGr P W c₅ e₅.wb_right
    ⟨hG, hWh, by show 1 ≤ c₅.nreg 90002; omega,
      by show ModelDescWF P _ c₅.nmem ztqks; grind,
      chainModel C, N, by show ModelDescAt c₅.nmem ztqks _ _; grind, hGM,
      hNW₅, hNF, by show (chainModel C).DegLe _ ztvny; grind,
      by show (chainModel C).Semigranular _ (c₅.nreg 90003); grind⟩
    (by show c₅.nreg ALLOC + κG ztvny * (c₅.nmem ztmif *
          (Nat.clog 2 (c₅.nmem ztmif) + 1) + 1) ≤ W
        grind)
  obtain ⟨N', hA₆, hNW₆, -, hcan⟩ := post₆ ztc N
    (by show ModelDescAt c₅.nmem ztqks _ _; grind) hNW₅.nfAt
  have hk6 : k₆ ≤ κG 4 * f := by
    beta_reduce at hk₆
    have e : ztrgy := p2
    have e' : c₅.nmem (rd c₅ bGran 1) = K := hK₅
    grind
  -- 5. the output
  have e₇ := Exec.copyN (P := P) e₆.wb_right 180003 90004
  set c₇ : Config := { c₆ with nreg := upd c₆.nreg 180003 _ } with hc₇
  have ex : Exec P W (bruteStmt sB sG) c c₇ _ :=
    .seq e₃ ztcsc
  refine ⟨c₇, _, ex, ?_, ⟨C, N', rfl, rfl, rfl, ?_, ?_⟩, ?_⟩
  · grind
  · show Robust _ c₇.nmem fun m' => NFAt m' (c₇.nreg 180003) N'
    have e1 : ztfky := by_rfl
    have e2 : c₇.nreg 180003 = c₆.nreg 90004 := by_rfl
    zvmws; exact hNW₆
  · have e3 : rd c₅ bGran 3 = γ := p3
    have e2 : ztrgy := p2
    grind
  · -- the frame
    have F₅ : ztpka := ⟨fun r hr _ => R₅ r ztept
      ztept (by rintro rfl; exact hr by_decide)
      ztept, by_grind, by_grind,
      by grind, O₅, by zunji, by_omega⟩
    have F₇ : Frame {bBrute} c₆ c₇ 1 := ⟨fun r hr _ => by
        zuotu; zumzy; rw [upd_other _ _ _ ztept],
      by grind, by_grind, by_grind, rfl, by_rfl,
      by zuotu; simp [ALLOC]⟩
    have := ((((F₃.trans F₄).trans F₅).trans F₆).trans F₇).mono (B' := bruteBands) by_decide
      (k' := k₃ + (k₄ + (k₅ + zttrk))) by_omega
    omega
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK SearchR WalkKey NFLoc
open OracleQ
open Chazelle.Chain (sideInArc)
@[expose] public section
def candS (rP : ℕ) : Stmt :=
  .seq (block [.copyN 50000 120040, .copyN 50001 120014, .copyN 50002 rP, .addN 50003 120023 120011])
    (.seq myLoc
      (.seq (.instr (.copyN 120110 120170))
        (.seq clusS
          (.seq (.seq (block [.copyN 120186 120170, .addN 120110 120186 120011])
              (.ifLtN 120110 120030 .skip (.instr (.constN 120110 0))))
            (.seq clusS
              (.seq (.ifLtN 120012 120186 ztnbe
                  ztnbd)
                clusS))))))

/-- **The memory facts of double identification.** -/
structure LocMemOK (P : Polygon) (V : QV) (m : ℕ → ℕ) (W : ℕ) (M : Model) (N : NF) : Prop where
  md : ModelDescAt m V.MD zta M
  good : GoodModel M
  md_le : V.MD + 6 ≤ W
  chwf : LocChainWF P W m V.MD
  nf : NFAt m V.NB N
  isNF : IsNF M zta N
  A : V.A = N.arcs.length
  st : ∀ j, j < N.arcs.length → ProperPos M zta P.n (N.arc j).s
  tab : ∀ j, j < V.L → m ztnqe = 2 ^ j
  A_lt : V.A < 2 ^ V.L
  NB_le : V.NB + 7 ≤ V.TB
  AB_le : m ztfos + 5 * V.A ≤ V.TB
  SB_le : m ztfot + V.A ≤ V.TB
  TB_le : V.TB + V.L ≤ W
  A_le : V.A ≤ V.μ

/-- The registers written by `candS`. -/
def BCa (r : ℕ) : Bool := BL r || BC r || decide ztfua || decide zttxo

/-- The cluster scans of the three candidates of a spine position. -/
def clusPts3 (m : ℕ → ℕ) (V : QV) (C : Chain) (p : ℕ) : Set Point :=
  clusPts m V C (lab m V p) ∪ clusPts m V C (lab m V (succP V.A p)) ∪
    clusPts m V C (lab m V zttwj)
open Classical in
/-- **Locate the position and scan the clusters of its candidates.** -/
theorem candS_exec (hcov : ArcCoverSpec) {P : Polygon} {W : ℕ} (hG : GoodEnv P)
    (hW : 8 * P.n + 32 ≤ W) {C : Chain} {V : QV} {z : Point} (hs : SemOK P C V z) (c : Config)
    (hw : WordsBounded W c) (hq : QConst P V c) (hb : BestOK P.n V.s V.m c)
    (hm : QMem V c.nmem W) (hO : OrdOK c.nmem V W) {M : Model} {N : NF}
    (hL : LocMemOK P V c.nmem W M N) {NC CS : ℕ}
    (hNC : ∀ u, u < V.μ → nodeCost c.nmem V u ≤ NC)
    (hCS : ∀ u, u < V.μ → clusSize c.nmem V ztlqo ≤ CS) {rP : ℕ}
    (hrP : 120160 ≤ rP ∧ rP ≤ 120163) (hwn : c.nreg rP < M.W.n)
    (hx : ProperPos M zta P.n ztdao) {S : Set Point}
    (hS : Sweep.FirstHitOpt S z zthx ztwmd) :
    ∃ c' k p, Exec P W ztvlc c c' k ∧ k ≤ 5500 * ztbts + 3 * ztbaad + 30 ∧
      FrameB BCa c c' ∧ BestOK P.n V.s V.m c' ∧ p < V.A ∧
      (¬ M.IsCut ztwiv ztyph →
        N.F M zta = ∅ ∨ sideInArc ztypc
          ztypb ztyph) ∧
      (M.IsCut ztwiv ztyph →
        M.key zta (N.arc ztbjk).s = M.key zta ztdao ∨
          M.key zta (N.arc ztbjk).e = M.key zta ztdao) ∧
      Sweep.FirstHitOpt ztnox z zthx
        (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c')) := by
  zuesm
  have hn := hv.hz_lt
  -- 1. the inputs of double identification
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50000 120040, .copyN 50001 120014,
      .copyN 50002 rP, .addN 50003 120023 120011]) c c₁ k₁ ∧ k₁ = 4 ∧
      (c₁.nreg 50000 = V.MD ∧ c₁.nreg 50001 = V.NB ∧ c₁.nreg 50002 = c.nreg rP ∧
        c₁.nreg 50003 = V.hz + 1 ∧ (∀ r, r < 50000 ∨ 50003 < r → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem) := by
    have q40 := hq.MD
    have q14 := hq.NB
    have q23 := hq.hz
    have q11 := hq.one
    exec_block
    · config_simp; omega
    · refine ⟨rfl, by simp_all, by simp_all, ?_, ?_,
        fun r hr => by config_simp; upd_solve, rfl⟩
      · config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;> first | omega)
      simp_all
  obtain ⟨x50000, x50001, x50002, x50003, r₁, m₁⟩ := v₁
  zubwn
  have hm₁ := m₁
  -- 2. double identification
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hp₂, hloc1, hloc2⟩ := myLoc_exec hcov (P := P) (W := W) (c := c₁)
    e₁.wb_right ⟨hG, by_omega, by rw [x50000]; exact hL.md_le, by zunqa; exact hL.chwf,
      M, by zunqa; exact hL.md, by_omega⟩ hG by_omega
    (by zunqa; exact hL.md) hL.good (by rw [x50001, hm₁]; exact hL.nf) hL.isNF
    by_simp_all hL.st hq₁.TB hq₁.L hq₁.zero hq₁.one
    (fun j hj => by rw [hm₁]; exact hL.tab j hj) (by rw [← hL.A]; exact hL.A_lt)
    (by rw [x50001]; exact hL.NB_le) (by zunwk; exact hL.AB_le)
    (by zunwk; exact hL.SB_le) hL.TB_le
  rw [x50002, x50003] at hloc1 hloc2
  have hBLc : ∀ r, 120010 ≤ r → r ≤ 120049 → BL r = false := fun r h1 h2 => by
    zunfi; omega
  have hq₂ := hq₁.frame f₂ hBLc
  have m₂ := f₂.2.2.1.trans hm₁
  obtain ⟨p, hp⟩ : ∃ p, c₂.nreg 120170 = p := by_simp_all
  zvohk at hp₂ hloc1 hloc2
  have hpA : p < V.A := by rw [hL.A]; omega
  have hpμ : p < V.μ := by have := hL.A_le; omega
  have hBL5 : ∀ r, (r = 120050 ∨ r = 120051 ∨ r = 120052) → BL r = false := fun r hr => by
    rcases hr with rfl | rfl | rfl <;> decide
  have hb₂ : BestOK P.n V.s V.m c₂ := by
    zucku
    rw [f₂.1 _ by_simp_all, f₂.1 _ by_simp_all, f₂.1 _ by_simp_all,
      r₁ _ by_omega, r₁ _ by_omega, r₁ _ by_omega]
    zulfi
  have hbo₂ : ztmue := by
    zulbi
    rw [f₂.1 _ by_simp_all, f₂.1 _ by_simp_all, r₁ _ by_omega, r₁ _ by_omega]
  -- 3. the cluster of `p`
  obtain ⟨c₃, e₃, v₃, r₃⟩ := copy_exec (P := P) e₂.wb_right 120110 120170
  zvohk at v₃
  zuiyz
  have hm₃ : ztckd := by
    rw [← m₂]; exact (exec_frameB e₃ (B := fun r => decide ztfua) by_decide).2.2.1
  have hb₃ : ztsao := by
    unfold BestOK; zuniu; exact hb₂
  have hbo₃ : ztmuf := by
    unfold bestOf; rw [r₃ 120050 by_decide, r₃ 120052 by_decide]; exact hbo₂
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hb₄, hit₄⟩ := clusS_exec (P := P) hG hW hs c₃ e₃.wb_right hq₃ hb₃
    by_simp_all by_simp_all by_omega (NC := NC)
    ztcid (S := S) by_simp_all
  rw [v₃, hm₃] at hk₄ hit₄
  have hq₄ := hq₃.frame f₄ BC_const
  have hm₄ := f₄.2.2.1.trans hm₃
  have x170 : c₄.nreg 120170 = p := (f₄.1 _ by_decide).trans by_simp_all
  -- 4. the cluster of the successor
  obtain ⟨c₅, k₅, e₅, hk₅, v₅⟩ : ∃ c₅ k₅, Exec P W (.seq (block [.copyN 120186 120170,
      .addN 120110 120186 120011]) (.ifLtN 120110 120030 .skip (.instr (.constN 120110 0)))) c₄ c₅ k₅ ∧
      k₅ ≤ 5 ∧ (c₅.nreg 120110 = succP V.A p ∧ c₅.nreg 120186 = p ∧
        (∀ r, r ≠ 120110 → r ≠ 120186 → c₅.nreg r = c₄.nreg r) ∧ c₅.nmem = c₄.nmem ∧
        c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output) := by
    zucc
    obtain ⟨d₁, k₁', e₁', hk₁', q⟩ : ∃ d₁ k₁', Exec P W (block [.copyN 120186 120170,
        .addN 120110 120186 120011]) c₄ d₁ k₁' ∧ k₁' = 2 ∧ (d₁.nreg 120110 = p + 1 ∧
          d₁.nreg 120186 = p ∧ (∀ r, r ≠ 120110 → r ≠ 120186 → d₁.nreg r = c₄.nreg r) ∧
          d₁.nmem = c₄.nmem ∧ d₁.rreg = c₄.rreg ∧ d₁.rmem = c₄.rmem ∧ d₁.output = c₄.output) := by
      exec_block
      · config_simp; zuomr; have := hL.A_le; have := hO.μ_le; omega
      · refine ⟨rfl, ?_, ?_, by_simp_all, rfl, rfl, rfl, rfl⟩
        · config_simp; zuomr
        simp_all
    obtain ⟨q110, q186, qr, qm, qrr, qrm, qo⟩ := q
    have hqA := (qr _ by_decide by_decide).trans hq₄.A
    by_cases hs1 : p + 1 < V.A
    · refine ⟨d₁, _, .seq e₁' (.ifLtN_true by_omega (.skip e₁'.wb_right)),
        by omega, ?_, q186, qr, qm, qrr, qrm, qo⟩
      rw [q110]; unfold succP; grind
    · obtain ⟨d₂, e₂', v₂', r₂'⟩ := const_exec e₁'.wb_right 120110 0 by_omega
      have f₂' := exec_frameB e₂' (B := fun r => decide ztfua) by_decide
      refine ⟨d₂, _, .seq e₁' (.ifLtN_false by_omega e₂'), by_omega, ?_,
        by grind, by_grind,
        f₂'.2.2.1.trans qm, by rw [show d₂.rreg = d₁.rreg from funext fun r =>
          exec_rframe e₂' (B := fun _ => false) by_decide r rfl]; omega,
        f₂'.2.2.2.1.trans qrm, f₂'.2.2.2.2.trans qo⟩
      rw [v₂']; unfold succP; grind
  obtain ⟨v110, v186, r₅, m₅, rr₅, rm₅, o₅⟩ := v₅
  have hq₅ : QConst P V c₅ := hq₄.congr by_grind
  have hm₅ := m₅.trans hm₄
  have hb₅ : BestOK P.n V.s V.m c₅ := by
    zucku
    rw [r₅ 120050 by_decide by_decide, r₅ 120051 by_decide by_decide,
      r₅ 120052 by_decide by_decide]
    exact hb₄
  have hbo₅ : bestOf c₅ = bestOf c₄ := by
    zujqh
  have hsμ : succP V.A p < V.μ := by have := succP_lt hpA; have := hL.A_le; omega
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, hb₆, hit₆⟩ := clusS_exec (P := P) hG hW hs c₅ e₅.wb_right hq₅ hb₅
    by_simp_all by_simp_all by_omega (NC := NC)
    ztgjq
    (S := S ∪ clusPts c.nmem V C ztlqn) by_simp_all
  rw [v110, hm₅] at hk₆ hit₆
  have hq₆ := hq₅.frame f₆ BC_const
  have hm₆ := f₆.2.2.1.trans hm₅
  have x186 := (f₆.1 _ by_decide).trans v186
  -- 5. the cluster of the predecessor
  obtain ⟨c₇, k₇, e₇, hk₇, v₇, r₇, m₇⟩ : ∃ c₇ k₇, Exec P W (.ifLtN 120012 120186
      ztnbe ztnbd) c₆ c₇ k₇ ∧
      k₇ ≤ 3 ∧ c₇.nreg 120110 = predP V.A p ∧ (∀ r, r ≠ 120110 → c₇.nreg r = c₆.nreg r) ∧
      c₇.nmem = c₆.nmem := by
    zujb
    by_cases h0 : 0 < p
    · refine ⟨_, _, .ifLtN_true (by rw [hq₆.zero, x186]; exact h0) ztjio, by_omega,
        ?_, fun r hr => by config_simp; upd_solve, rfl⟩
      config_simp; rw [x186, hq₆.one]; unfold predP; grind
    · refine ⟨_, _, .ifLtN_false by_omega ztjio, by_omega,
        ?_, fun r hr => by config_simp; upd_solve, rfl⟩
      config_simp; rw [hq₆.A, hq₆.one]; unfold predP; grind
  have hq₇ : QConst P V c₇ := hq₆.congr by_grind
  have hm₇ := m₇.trans hm₆
  have hb₇ : BestOK P.n V.s V.m c₇ := by
    zucku
    rw [r₇ 120050 by_decide, r₇ 120051 by_decide, r₇ 120052 by_decide]
    exact hb₆
  have hbo₇ : bestOf c₇ = bestOf c₆ := by
    zujqh
  have hpμ' : predP V.A p < V.μ := by have := predP_lt hpA; have := hL.A_le; omega
  obtain ⟨c₈, k₈, e₈, hk₈, f₈, hb₈, hit₈⟩ := clusS_exec (P := P) hG hW hs c₇ e₇.wb_right hq₇ hb₇
    by_grind by_grind by_omega (NC := NC)
    ztgjq
    (S := S ∪ clusPts c.nmem V C ztlqn ∪ clusPts c.nmem V C ztmmc)
    by_grind
  rw [v₇, hm₇] at hk₈ hit₈
  -- the frame
  have ex : Exec P W ztvlc c c₈ _ :=
    .seq e₁ ztey
  have f₁ := exec_frameB e₁ (B := fun r => decide ztgzd)
    by_rfl
  have f₃ := exec_frameB e₃ (B := fun r => decide ztfua) by_decide
  have f₅ := exec_frameB e₅ (B := fun r => decide ztfua || decide zttxo) by_decide
  have f₇ := exec_frameB e₇ (B := fun r => decide ztfua) by_decide
  have fr : FrameB BCa c c₈ := by
    have g1 : FrameB BCa c c₁ := FrameB.mono f₁ fun r hr => by
      zvmwo at hr; simp [BCa, BL, Bloc]; omega
    have g2 : FrameB BCa c₁ c₂ := FrameB.mono f₂ fun r hr => by zuncz
    have g3 : FrameB BCa c₂ c₃ := FrameB.mono f₃ fun r hr => by
      zueno
    have g4 : FrameB BCa c₃ c₄ := FrameB.mono f₄ fun r hr => by zuncz
    have g5 : FrameB BCa c₄ c₅ := FrameB.mono f₅ fun r hr => by
      zufw
      rcases hr with hr | hr <;> zuncz
    have g6 : FrameB BCa c₅ c₆ := FrameB.mono f₆ fun r hr => by zuncz
    have g7 : FrameB BCa c₆ c₇ := FrameB.mono f₇ fun r hr => by
      zueno
    have g8 : FrameB BCa c₇ c₈ := FrameB.mono f₈ fun r hr => by zuncz
    exact g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (g7.trans g8))))))
  refine ⟨c₈, _, p, ex, ?_, fr, hb₈, hpA, hloc1, hloc2, ?_⟩
  · have a4 := hCS p hpμ
    have a6 := hCS _ hsμ
    have a8 := hCS _ hpμ'
    have b4 : (clusSize c.nmem V ztlqn + 2) * ztdft ≤ zthaf * ztdft :=
      Nat.mul_le_mul_right _ by_omega
    have b6 : (clusSize c.nmem V ztmmc + 2) * ztdft ≤
        zthaf * ztdft := Nat.mul_le_mul_right _ by_omega
    have b8 : (clusSize c.nmem V (lab c.nmem V zttwj) + 2) * ztdft ≤
        zthaf * ztdft := Nat.mul_le_mul_right _ by_omega
    omega
  · unfold clusPts3
    grind
def mainS : Stmt :=
  .seq (.instr (.constN 120050 0))
    (.seq dstarS (.seq tchS (.seq posS (.seq (candS 120160) (.seq (candS 120161)
      (.seq (candS 120162) (.seq (candS 120163) (block [.copyN 120005 120050,
        .copyN 120006 120051]))))))))

/-- The `k`-th walk edge of the stopping point. -/
def posK (q : ℕ × ℕ × ℕ × ℕ) : ℕ → ℕ
  | 0 => q.1
  | 1 => q.2.1
  | 2 => q.2.2.1
  | _ => q.2.2.2

/-- The comparison of the chord's near end and the hit on `D*` (in the program's sense). -/
def CBof (P : Polygon) (C : Chain) (V : QV) (bD : Option ℕ) (near : ℕ) : Prop :=
  match bD with
  | some cD => if V.σb = 1 then EndLtD P C V ztdni near V.hz
      else EndGtD P C V ztdni near V.hz
  | none => False

/-- **The locate facts** for the walk position `(w, hz + 1)` and the answer `p`. -/
def LocFacts (P : Polygon) (M : Model) (N : NF) (hz w p : ℕ) : Prop :=
  (¬ M.IsCut ztwiv ztypj →
    N.F M zta = ∅ ∨ sideInArc ztypc
      ztypb ztypj) ∧
  (M.IsCut ztwiv ztypj →
    M.key zta (N.arc ztbjk).s = M.key zta ztxv ∨
      M.key zta (N.arc ztbjk).e = M.key zta ztxv)

/-- The registers written by `mainS`. -/
def BMain (r : ℕ) : Bool :=
  BD r || BT r || BPo r || BCa r || decide ztftz || decide ztogd || decide ztogg
open Classical in
/-- The choice of `tchS` with the registers' comparison is the choice with `CBof`. -/
theorem selOf_cb {P : Polygon} {C : Chain} {V : QV} {c : Config} (hb : BestOK P.n V.s V.m c)
    (found : Prop) (near : ℕ) :
    selOf C V ztchc found near
        (if V.σb = 1 then EndLtD P C V ztfgp near V.hz
          else EndGtD P C V ztfgp near V.hz) =
      selOf C V ztchc found near (CBof P C V ztchc near) := by
  unfold selOf
  by_cases hf : c.nreg 120050 = 1
  · have hbo : ztzpe := by unfold bestOf; simp_all
    have he := (hb.2 hf).1
    rw [hbo]
    unfold CBof
    zucjo
  · have hbo : ztunc := by unfold bestOf; simp_all
    simp_all

/-- The cost of one locate-and-clusters step. -/
def candCost (V : QV) (NC CS : ℕ) : ℕ := 5500 * ztbts + 3 * ztbaad + 30
theorem BCa_main {r : ℕ} (h : BCa r = true) : BMain r = true := by simp [BMain, h]
open Classical in
/-- **The main phase of the query.** -/
theorem mainS_exec (hcov : ArcCoverSpec) {P : Polygon} {W : ℕ} (hG : GoodEnv P)
    (hW : 8 * P.n + 32 ≤ W) {C : Chain} {V : QV} {z : Point} (hs : SemOK P C V z) (c : Config)
    (hw : WordsBounded W c) (hq : QConst P V c) (hm : QMem V c.nmem W) (hO : OrdOK c.nmem V W)
    {N : NF} (hL : LocMemOK P V c.nmem W ztc N) (hDL : V.DL + V.nD ≤ W)
    (htv : V.tv < P.n) {NC CS : ℕ}
    (hNC : ∀ u, u < V.μ → nodeCost c.nmem V u ≤ NC)
    (hCS : ∀ u, u < V.μ → clusSize c.nmem V ztlqo ≤ CS)
    (hf : c.nreg 120140 ≤ 1)
    (hvalid : ∀ bD : Option ℕ,
      Sweep.FirstHitOpt ztgik z zthx
        ztwqh → ztcxj →
      ∀ k, k < 4 →
        posK (posOf V P.n (selOf C V bD zthui ztdcq
          ztxqo)) k < (chainModel C).W.n ∧
        ProperPos ztc zta P.n ⟨posK (posOf V P.n (selOf C V bD zthui
          ztdcq ztxqo)) k, V.hz + 1⟩) :
    ∃ c' k bD, Exec P W mainS c c' k ∧
      k ≤ dstarCost c.nmem V + 4 * candCost V NC CS + 500 ∧ FrameB BMain c c' ∧
      Sweep.FirstHitOpt ztgik z zthx
        ztwqh ∧ ztcxj ∧
      ∃ pk : ℕ → ℕ, (∀ k, k < 4 → pk k < V.A ∧ LocFacts P ztc N V.hz
          (posK (posOf V P.n (selOf C V bD zthui ztdcq
            ztxqo)) k) (pk k)) ∧
        Sweep.FirstHitOpt (dstarPts c.nmem V C V.nD ∪ clusPts3 c.nmem V C ztmmx ∪
            clusPts3 c.nmem V C ztmmy ∪ clusPts3 c.nmem V C ztmmz ∪ clusPts3 c.nmem V C ztmna)
          z zthx ztwot ∧
        BestOK P.n V.s V.m c' ∧ c'.nreg 120005 = c'.nreg 120050 ∧
        c'.nreg 120006 = c'.nreg 120051 := by
  zuesm
  -- 1. no hit yet
  obtain ⟨c₁, e₁, v₁, r₁⟩ := const_exec (P := P) hw 120050 0 by_omega
  zubwn
  have m₁ :=
    (exec_frameB e₁ (B := fun r => decide ztogg) by_decide).2.2.1
  have hbo₁ : bestOf c₁ = none := by unfold bestOf; simp_all
  have hb₁ : ztiyc := ztomu
  -- 2. the nodes of `D*`
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hb₂, hit₂⟩ := dstarS_exec (P := P) hG hW hs c₁ e₁.wb_right hq₁ hb₁
    by_simp_all hDL (S := ∅) (by rw [hbo₁]; tauto)
  rw [m₁, Set.empty_union] at hit₂
  zvmxn at hk₂
  have hq₂ := hq₁.frame f₂ BD_const
  have m₂ := f₂.2.2.1.trans m₁
  set bD := bestOf c₂ with hbD
  have hbDm : ∀ cb, bD = some cb → cb < V.m := by
    intro cb h
    unfold bestOf at hbD
    by_cases hfl : c₂.nreg 120050 = 1
    · rw [hbD, ite_eq_left hfl] at h; cases h; exact (hb₂.2 hfl).2
    simp_all
  have x140 : ztsgv := by
    zuguh
  have x141 : ztsgw := by
    zuguh
  -- 3. the stopping point
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, s₃⟩ := tchS_exec (P := P) hG hW hv htv c₂ e₂.wb_right hq₂
    by_omega hb₂
  rw [selOf_cb hb₂, x140, x141, ← hbD] at s₃
  set sel := selOf C V bD _ _ _
    with hsel
  have hq₃ := hq₂.frame f₃ fun r h1 h2 => by
    simp only [BT, BX2, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have m₃ := f₃.2.2.1.trans m₂
  have hsel01 : sel.1 = 0 ∨ sel.1 = 1 := by
    zuduo

    · zvnbq; unfold chordSel; grind
    · zvnoi; rcases bD with _ | cD <;> zupac
  have hselm : sel.1 = 0 → sel.2 < V.m := by
    zuduo

    · zvnbq; unfold chordSel
      split_ifs <;> simp <;> rw [hv.m] <;> exact tci_lt C _
    · zubme
      rcases hbd : bD with _ | cD
      · zupac
      simp_all
  -- 4. the walk positions
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, v₄⟩ := posS_exec (P := P) hW hv c₃ e₃.wb_right hq₃ s₃ hsel01 hselm
  have hq₄ := hq₃.frame f₄ fun r h1 h2 => by
    simp only [BPo, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have m₄ := f₄.2.2.1.trans m₃
  have hvd := hvalid bD hit₂ hbDm
  rw [← hsel] at hvd
  set q := posOf V P.n sel with hqdef
  have xq : ∀ k, k < 4 → c₄.nreg ztjek = posK q k := by
    zugf
    interval_cases k
    · exact congrArg Prod.fst v₄
    · exact congrArg (fun x => x.2.1) v₄
    · exact congrArg (fun x => x.2.2.1) v₄
    · exact congrArg (fun x => x.2.2.2) v₄
  -- the best-hit registers before the candidates
  have hBDbest := fun r h1 h2 =>
    (f₄.1 r h2).trans (f₃.1 r h1)
  have hb₄ : BestOK P.n V.s V.m c₄ := by
    zucku
    rw [hBDbest 120050 by_decide by_decide, hBDbest 120051 by_decide by_decide,
      hBDbest 120052 by_decide by_decide]
    exact hb₂
  have hbo₄ : bestOf c₄ = bD := by
    unfold bestOf; rw [hBDbest 120050 by_decide by_decide, hBDbest 120052 by_decide by_decide]
    rfl
  -- 5 – 8. the candidates
  have candStep : ∀ (k : ℕ), k < 4 → ∀ (d : Config), WordsBounded W d → QConst P V d →
      BestOK P.n V.s V.m d → d.nmem = c.nmem → d.nreg ztjek = posK q k →
      ∀ (S : Set Point), Sweep.FirstHitOpt S z zthx
        (bestVal zta V.s V.hz zthx z (bestOf d)) →
      ∃ d' k' p, Exec P W (candS ztjek) d d' k' ∧ k' ≤ candCost V NC CS ∧
        FrameB BCa d d' ∧ BestOK P.n V.s V.m d' ∧ p < V.A ∧
        LocFacts P ztc N V.hz zttwg p ∧
        Sweep.FirstHitOpt ztnox z zthx
          (bestVal zta V.s V.hz zthx z (bestOf d')) := by
    intro k hk d hd hqd hbd hmd hpos S hS
    obtain ⟨hwn, hx⟩ := hvd k hk
    obtain ⟨d', k', p, ex, hk', fr, hb', hp, hl1, hl2, hit⟩ := candS_exec hcov (P := P) hG hW hs d hd
      hqd hbd by_simp_all by_simp_all (by rw [hmd]; exact hL)
      (NC := NC) (CS := CS) ztcid
      ztcid (rP := 120160 + k) by_omega
      by_omega by_simp_all hS
    zvnbl at hl1 hl2
    rw [hmd] at hit
    exact ⟨d', k', p, ex, hk', fr, hb', hp, ⟨hl1, hl2⟩, hit⟩
  have keepPos : ∀ (d d' : Config), FrameB BCa d d' → ∀ k, k < 4 →
      d'.nreg _ = d.nreg ztjek := fun d d' fr k hk =>
    fr.1 _ (by simp only [BCa, BL, BC, BN, BA, BW, BE, Bdir, Bloc, Bcmp, Bk, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]; omega)
  have hBCac : ∀ r, 120010 ≤ r → r ≤ 120049 → BCa r = false := fun r h1 h2 => by
    simp only [BCa, BL, BC, BN, BA, BW, BE, Bdir, Bloc, Bcmp, Bk, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]; omega
  obtain ⟨c₅, k₅, p₀, e₅, hk₅, f₅, hb₅, hp₀, hl₀, hit₅⟩ := candStep 0 by_norm_num c₄ e₄.wb_right hq₄
    hb₄ m₄ (xq 0 by_norm_num) ztgik by_grind
  have hq₅ := hq₄.frame f₅ hBCac
  have m₅ := f₅.2.2.1.trans m₄
  obtain ⟨c₆, k₆, p₁, e₆, hk₆, f₆, hb₆, hp₁, hl₁, hit₆⟩ := candStep 1 by_norm_num c₅ e₅.wb_right hq₅
    hb₅ m₅ (by rw [keepPos c₄ c₅ f₅ 1 by_norm_num]; grind) _ hit₅
  have hq₆ := hq₅.frame f₆ hBCac
  have m₆ := f₆.2.2.1.trans m₅
  obtain ⟨c₇, k₇, p₂, e₇, hk₇, f₇, hb₇, hp₂, hl₂, hit₇⟩ := candStep 2 by_norm_num c₆ e₆.wb_right hq₆
    hb₆ m₆ (by rw [keepPos c₅ c₆ f₆ 2 by_norm_num, keepPos c₄ c₅ f₅ 2 by_norm_num]; grind) _ hit₆
  have hq₇ := hq₆.frame f₇ hBCac
  have m₇ := f₇.2.2.1.trans m₆
  obtain ⟨c₈, k₈, p₃, e₈, hk₈, f₈, hb₈, hp₃, hl₃, hit₈⟩ := candStep 3 by_norm_num c₇ e₇.wb_right hq₇
    hb₇ m₇ (by rw [keepPos c₆ c₇ f₇ 3 by_norm_num, keepPos c₅ c₆ f₆ 3 by_norm_num,
      keepPos c₄ c₅ f₅ 3 by_norm_num]; exact xq 3 by_norm_num) _ hit₇
  -- 9. the output
  zujai
  obtain ⟨c₉, k₉, e₉, hk₉, v₉⟩ : ∃ c₉ k₉, Exec P W (block [.copyN 120005 120050, .copyN 120006 120051])
      c₈ c₉ k₉ ∧ k₉ = 2 ∧ (c₉.nreg 120005 = c₉.nreg 120050 ∧ c₉.nreg 120006 = c₉.nreg 120051 ∧
        ∀ r, r ≠ 120005 → r ≠ 120006 → c₉.nreg r = c₈.nreg r) := by
    exec_block
    exact ⟨rfl, by config_simp, by config_simp, fun r h1 h2 => by config_simp; upd_solve⟩
  obtain ⟨o5, o6, r₉⟩ := v₉
  have hbo₉ : bestOf c₉ = bestOf c₈ := by
    unfold bestOf; rw [r₉ 120050 by_decide by_decide, r₉ 120052 by_decide by_decide]
  have hb₉ : BestOK P.n V.s V.m c₉ := by
    zucku
    rw [r₉ 120050 by_decide by_decide, r₉ 120051 by_decide by_decide,
      r₉ 120052 by_decide by_decide]
    exact hb₈
  -- frames
  have ex : Exec P W mainS c c₉ _ :=
    .seq e₁ ztqr
  have fr : FrameB BMain c c₉ := by
    have g1 : FrameB BMain c c₁ := FrameB.mono (exec_frameB e₁ (B := fun r => decide ztogg)
      by_decide) fun r hr => by zvmwo at hr; zunda
    have g2 : FrameB BMain c₁ c₂ := FrameB.mono f₂ fun r hr => by zunda
    have g3 : FrameB BMain c₂ c₃ := FrameB.mono f₃ fun r hr => by zunda
    have g4 : FrameB BMain c₃ c₄ := FrameB.mono f₄ fun r hr => by zunda
    have g5 := FrameB.mono f₅ fun r hr => BCa_main hr
    have g6 := FrameB.mono f₆ fun r hr => BCa_main hr
    have g7 := FrameB.mono f₇ fun r hr => BCa_main hr
    have g8 := FrameB.mono f₈ fun r hr => BCa_main hr
    have g9 : FrameB BMain c₈ c₉ := FrameB.mono (exec_frameB e₉ (B := fun r => decide ztftz ||
      decide ztogd) by_decide) fun r hr => by
        zufw
        rcases hr with hr | hr <;> zunda
    exact g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (g7.trans (g8.trans g9)))))))
  refine ⟨c₉, _, bD, ex, ?_, fr, hit₂, hbDm, fun k => if k = 0 then p₀ else if k = 1 then p₁ else
    if k = 2 then p₂ else p₃, fun k hk => ?_, ?_, hb₉, o5, o6⟩
  · omega
  · interval_cases k
    · grind
    · grind
    · grind
    grind
  grind
def topS : Stmt :=
  .seq (sgnS 1 ztdbs zthql ztdbs)
    (.ifLtN 120012 10010 ztkqo ztoth)

/-- **The answer of a degenerate start.** -/
def degS : Stmt :=
  .ifLtN 120012 120140
    (.ifLtN 120012 120143
      (.seq (block [.copyN 120120 120142, .copyN 120121 120023])
        (.seq xpS
          (.seq (.ifLtN 120122 120011 ztifr
              (.ifLtN 120122 120048 ztkqp
                ztifr))
            (.instr (.constN 120053 1)))))
      .skip)
    .skip

/-- **The phases after loading.** -/
def restS : Stmt :=
  .seq topS (.ifLtN 120053 120011
    (.seq chordSearchS (.seq chordPostS (.seq degS (.ifLtN 120053 120011 mainS .skip)))) .skip)

/-- The index read off a symbolic point (the edge of an edge point, the vertex of a vertex). -/
def symIdx : SymPt → ℕ
  | .vtx i => i
  | .onEdge e _ => e
variable {P : Polygon} {W : ℕ}
/-- **The top test.** -/
theorem topS_exec (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {V : QV} (hv : QVOK P C V) (htv : V.tv < P.n) (c : Config) (hw : WordsBounded W c)
    (hq : QConst P V c) :
    ∃ c' k, Exec P W topS c c' k ∧ k ≤ 250 ∧
      FrameB (fun r => Bk r || decide ztftz || decide ztkdh) c c' ∧
      c'.nreg 120053 ≤ 1 ∧
      (c'.nreg 120053 = 1 ↔ ((Qof P).vtx V.tv).2 < ((Qof P).vtx V.hz).2) ∧
      ztlkd := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, s₁⟩ := sgnS_exec (P := P) hG by_omega 1 by_norm_num
    ztdbs zthql ztdbs c hw by_decide by_decide by_decide rfl rfl rfl
    ztimd
    (show c.nreg 120023 < P.n by rw [hq.hz]; exact hv.hz_lt)
    ztimd
  simp only [SignTest, SymPt.eval, hq.tv, hq.hz] at s₁
  have hz₁ : ztpmr := (f₁.1 _ by_decide).trans hq.zero
  zud
  suffices H : ∃ c' k, Exec P W (.ifLtN 120012 10010 ztkqo
      ztoth) c₁ c' k ∧ k ≤ 4 ∧
      FrameB (fun r => decide ztftz || decide ztkdh) c₁ c' ∧ c'.nreg 120053 ≤ 1 ∧
      (c'.nreg 120053 = 1 ↔ c₁.nreg 10010 = 1) ∧ ztlkd by
    obtain ⟨c', k, ex, hk, f, h1, h2, h3⟩ := H
    refine ⟨c', _, .seq e₁ ex, by_omega, (FrameB.mono f₁ fun r hr => by_simp_all).trans
      (FrameB.mono f fun r hr => by
        grind), h1, by_simp_all, h3⟩
  by_cases hb : c₁.nreg 10010 = 1
  · obtain ⟨c₂, k₂, e₂, hk₂, v₂⟩ : ∃ c₂ k₂, Exec P W (block [.constN 120005 0, .constN 120053 1])
        c₁ c₂ k₂ ∧ k₂ = 2 ∧ c₂.nreg 120005 = 0 ∧ c₂.nreg 120053 = 1 := by
      exec_block
      · omega
      · omega
      simp
    refine ⟨c₂, _, .ifLtN_true by_omega e₂, by_omega,
      exec_frameB e₂ by_decide, by_omega, by_omega, fun _ => v₂.1⟩
  · have hb0 : ztupx := by_omega
    obtain ⟨c₂, e₂, v₂, -⟩ := const_exec (P := P) w₁ 120053 0 by_omega
    refine ⟨c₂, _, .ifLtN_false by_omega e₂, by_omega,
      exec_frameB e₂ by_decide, by_omega, by_omega, fun h => by_omega⟩
theorem symIdx_of_in {c : Config} {p : SymPt} (h : SymPtIn c 120123 p) :
    c.nreg 120124 = symIdx p := by
  cases p with
  | vtx i => exact h.2
  | onEdge e h' => exact h.2.1

/-- The registers written by `degS`. -/
def BDg (r : ℕ) : Bool :=
  BX r || decide ztgxo || decide ztftz || decide ztogd ||
    decide ztkdh
theorem wr_degS : wr BDg degS = true := by_decide

/-- **The answer of a degenerate start.** -/
theorem degS_exec (hW : 8 * P.n + 32 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c)
    {found deg : Prop} {far : ℕ} (h140 : c.nreg 120140 ≤ 1) (h140' : c.nreg 120140 = 1 ↔ found)
    (h142 : found → c.nreg 120142 = far) (h143 : found → c.nreg 120143 ≤ 1)
    (h143' : found → (c.nreg 120143 = 1 ↔ deg)) :
    ∃ c' k, Exec P W degS c c' k ∧ k ≤ 60 ∧ FrameB BDg c c' ∧
      zthlm ∧
      (found ∧ deg → c'.nreg 120053 = 1 ∧
        ztezy ∧
        ztlup) := by
  suffices H : ∃ c' k, Exec P W degS c c' k ∧ k ≤ 60 ∧
      zthlm ∧
      (found ∧ deg → c'.nreg 120053 = 1 ∧
        ztezy ∧
        ztlup) by
    zudqy
    exact ⟨c', k, ex, hk, exec_frameB ex wr_degS, h1, h2⟩
  unfold degS
  by_cases hf : found
  swap
  · have : c.nreg 120140 = 0 := by_grind
    exact ⟨c, _, .ifLtN_false by_omega ztjd, by_omega,
      fun _ _ => rfl, fun h => absurd h.1 hf⟩
  have hf1 : c.nreg 120140 = 1 := h140'.2 hf
  by_cases hd : deg
  swap
  · have : c.nreg 120143 = 0 := by_grind
    exact ⟨c, _, .ifLtN_true ztlhz
      ztzrl, by_omega,
      fun _ _ => rfl, fun h => absurd h.2 hd⟩
  have hd1 : c.nreg 120143 = 1 := (h143' hf).2 hd
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 120120 120142, .copyN 120121 120023])
      c c₁ k₁ ∧ k₁ = 2 ∧ (c₁.nreg 120120 = far ∧ c₁.nreg 120121 = V.hz ∧
        ∀ r, r ≠ 120120 → r ≠ 120121 → c₁.nreg r = c.nreg r) := by
    exec_block
    exact ⟨rfl, by_simp_all, by config_simp; exact hq.hz,
      fun r h1 h2 => by_simp_all⟩
  obtain ⟨x120, x121, r₁⟩ := v₁
  have hq₁ : ztehw := hq.congr fun r h1 h2 => r₁ r by_omega by_omega
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, v₂, s₂⟩ := xpS_exec (P := P) by_omega hv c₁ e₁.wb_right hq₁
  rw [x120] at v₂
  rw [x120, x121] at s₂
  have hq₂ : ztehx := hq₁.frame f₂ fun r h1 h2 => by
    zunqb; omega
  zue
  have hcl := xpClass_le far
  -- the answer
  obtain ⟨c₃, k₃, e₃, hk₃, a₃, b₃⟩ : ∃ c₃ k₃, Exec P W (.ifLtN 120122 120011 (.instr (.constN 120005 0))
      (.ifLtN 120122 120048 ztkqp
        ztifr)) c₂ c₃ k₃ ∧ k₃ ≤ 5 ∧
      (xpClass far = 1 → c₃.nreg 120005 = 1 ∧ c₃.nreg 120006 = symIdx (xpSym C V P.n far V.hz)) ∧
      (xpClass far ≠ 1 → c₃.nreg 120005 = 0) := by
    by_cases h0 : xpClass far = 0
    · zucnr
      exact ⟨c₃, _, .ifLtN_true (by rw [v₂, hq₂.one, h0]; omega) e₃, by_omega,
        fun h => absurd h by_omega, fun _ => v₃⟩
    by_cases h1 : xpClass far = 1
    · obtain ⟨c₃, k₃, e₃, hk₃, v₃⟩ : ∃ c₃ k₃, Exec P W (block [.constN 120005 1,
          .copyN 120006 120124]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ c₃.nreg 120005 = 1 ∧
          c₃.nreg 120006 = c₂.nreg 120124 := by
        exec_block
        · omega
        simp
      exact ⟨c₃, _, .ifLtN_false (by rw [v₂, hq₂.one, h1]; omega)
        (.ifLtN_true (by rw [v₂, hq₂.two, h1]; omega) e₃), by_omega,
        fun _ => ⟨v₃.1, by rw [v₃.2]; exact symIdx_of_in (s₂ h1)⟩, fun h => absurd h1 h⟩
    · zucnr
      exact ⟨c₃, _, .ifLtN_false (by rw [v₂, hq₂.one]; omega)
        (.ifLtN_false (by zunpz; omega) e₃), by_omega,
        fun h => absurd h h1, fun _ => v₃⟩
  obtain ⟨c₄, e₄, v₄, r₄⟩ := const_exec (P := P) e₃.wb_right 120053 1 by_omega
  refine ⟨c₄, _, .ifLtN_true ztlhz (.ifLtN_true (by rw [hq.zero, hd1]; omega)
    ztwri), by_omega, fun h => absurd ⟨hf, hd⟩ h, fun _ => ⟨v₄, ?_, ?_⟩⟩
  · simp_all
  simp_all

/-- The registers written by `restS`. -/
def BRest (r : ℕ) : Bool :=
  Bk r || decide ztftz || decide ztkdh || BCS r || BCP r || BDg r || BMain r
open Classical in
theorem selOf_congr {C : Chain} {V : QV} {bD : Option ℕ} {f f' : Prop} {w w' : ℕ} {cb cb' : Prop}
    (hf : f ↔ f') (hw : f → w = w') (hcb : f → (cb ↔ cb')) :
    selOf C V bD f w cb = selOf C V bD f' w' cb' := by
  unfold selOf
  grind

/-- The partition point of the chord search. -/
def PartC (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ) (t : ℕ) : Prop :=
  t ≤ V.K ∧ (∀ j, j < t → chPr P C V m ztrne = true) ∧
    (t < V.K → chPr P C V m ztrnf = false)
open Classical in
/-- The four walk positions of the main phase, for the partition point `t` and the hit `bD`. -/
noncomputable def mainPos (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ) (t : ℕ)
    (bD : Option ℕ) : ℕ × ℕ × ℕ × ℕ :=
  posOf V P.n (selOf C V bD zthra ztbbb ztyve)
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK SearchR WalkKey NFLoc
open OracleQ
@[expose] public section
open Classical in
/-- **The trace of the query after loading.** -/
def RestTrace (P : Polygon) (C : Chain) (V : QV) (N : NF) (z : Point) (m : ℕ → ℕ)
    (c' : Config) : Prop :=
  (((Qof P).vtx V.tv).2 < ((Qof P).vtx V.hz).2 ∧ c'.nreg 120005 = 0) ∨
  (¬ ((Qof P).vtx V.tv).2 < ((Qof P).vtx V.hz).2 ∧ ∃ t, PartC P C V m t ∧ FoundC V m t ∧
    DegC P C V m t ∧
    (xpClass zteey = 1 → c'.nreg 120005 = 1 ∧
      c'.nreg 120006 = symIdx ztyxi) ∧
    (xpClass zteey ≠ 1 → c'.nreg 120005 = 0)) ∨
  (¬ ((Qof P).vtx V.tv).2 < ((Qof P).vtx V.hz).2 ∧ ∃ t, PartC P C V m t ∧
    ¬ ztems ∧ ∃ bD,
    Sweep.FirstHitOpt ztqme z zthx
      ztwqh ∧ ztcxj ∧
    ∃ pk : ℕ → ℕ, (∀ k, k < 4 → pk k < V.A ∧
        LocFacts P ztc N V.hz ztzxt ztean) ∧
      Sweep.FirstHitOpt (dstarPts m V C V.nD ∪ clusPts3 m V C ztmmx ∪ clusPts3 m V C ztmmy ∪
          clusPts3 m V C ztmmz ∪ clusPts3 m V C ztmna)
        z zthx ztwot ∧
      BestOK P.n V.s V.m c' ∧ c'.nreg 120005 = c'.nreg 120050 ∧ c'.nreg 120006 = c'.nreg 120051)
open Classical in
/-- **The query after loading.** -/
theorem restS_exec (hcov : ArcCoverSpec) {P : Polygon} {W : ℕ} (hG : GoodEnv P)
    (hW : 8 * P.n + 32 ≤ W) {C : Chain} {V : QV} {z : Point} (hs : SemOK P C V z) (c : Config)
    (hw : WordsBounded W c) (hq : QConst P V c) (hm : QMem V c.nmem W) (hO : OrdOK c.nmem V W)
    (hCM : ChordMemOK V c.nmem W) (hCT : ChordTabOK V c.nmem W)
    {N : NF} (hL : LocMemOK P V c.nmem W ztc N) (hDL : V.DL + V.nD ≤ W)
    (htv : V.tv < P.n) {NC CS : ℕ}
    (hNC : ∀ u, u < V.μ → nodeCost c.nmem V u ≤ NC)
    (hCS : ∀ u, u < V.μ → clusSize c.nmem V ztlqo ≤ CS)
    (hmono : ∀ i j, i ≤ j → j < V.K → chPr P C V c.nmem zteet = true →
      chPr P C V c.nmem ztrnd = true)
    (hvalid : ∀ t, PartC P C V c.nmem t → ¬ (FoundC V c.nmem t ∧ DegC P C V c.nmem t) →
      ∀ bD : Option ℕ,
        Sweep.FirstHitOpt ztgik z zthx
          ztwqh → ztcxj →
        ∀ k, k < 4 → posK ztodf k < (chainModel C).W.n ∧
          ProperPos ztc zta P.n ⟨posK ztodf k, V.hz + 1⟩) :
    ∃ c' k, Exec P W restS c c' k ∧
      k ≤ 715 * V.L + 700 + dstarCost c.nmem V + 4 * candCost V NC CS + 500 ∧
      FrameB BRest c c' ∧ RestTrace P C V N z c.nmem c' := by
  zuesm
  -- 1. the top test
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, t₁, z₁⟩ := topS_exec (P := P) hG hW hv htv c hw hq
  have hq₁ : ztehw := hq.frame f₁ fun r h1 h2 => by
    simp only [Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  zudqa
  have g₁ : FrameB BRest c c₁ := FrameB.mono f₁ fun r hr => by
    zufw
    rcases hr with (hr | hr) | hr <;> zundb
  by_cases hab : ((Qof P).vtx V.tv).2 < ((Qof P).vtx V.hz).2
  · have hd : c₁.nreg 120053 = 1 := t₁.2 hab
    refine ⟨c₁, _, .seq e₁ (.ifLtN_false ztfpm ztekc),
      by omega, g₁, Or.inl ⟨hab, z₁ hd⟩⟩
  have hd : c₁.nreg 120053 = 0 := by_grind
  -- 2. the chord search
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, ht₂, hpre₂, hpost₂⟩ := chordSearch_exec (P := P) hG hW hv htv c₁
    e₁.wb_right hq₁ by_grind by_grind
  zvmxn at hpre₂ hpost₂
  have hq₂ : ztehx := hq₁.frame f₂ fun r h1 h2 => by
    simp only [BCS, BP, BX2, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  zucxa
  obtain ⟨t, htd⟩ : ∃ t, c₂.nreg 50105 = t := zths
  rw [htd] at ht₂ hpre₂ hpost₂
  have hpart : PartC P C V c.nmem t := ⟨ht₂, hpre₂, hpost₂⟩
  -- 3. the chord next to the origin
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, b₃, fd₃, nf₃⟩ := chordPost_exec (P := P) hG hW hv htv c₂
    e₂.wb_right hq₂ by_grind by_omega
  rw [htd, m₂] at fd₃ nf₃
  have hq₃ : ztgan := hq₂.frame f₃ fun r h1 h2 => by
    simp only [BCP, BX2, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have m₃ : ztckd := f₃.2.2.1.trans m₂
  -- 4. a degenerate start
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, nd₄, d₄⟩ := degS_exec (P := P) hW hv c₃ e₃.wb_right hq₃
    (found := FoundC V c.nmem t) (deg := DegC P C V c.nmem t) (far := farC V c.nmem t) b₃ fd₃
    (fun h => (nf₃ h).2.1) (fun h => (nf₃ h).2.2.1) (fun h => (nf₃ h).2.2.2)
  have hq₄ : QConst P V c₄ := hq₃.frame f₄ fun r h1 h2 => by
    simp only [BDg, BX, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have m₄ : zteid := f₄.2.2.1.trans m₃
  have x53 : c₃.nreg 120053 = 0 := by
    rw [f₃.1 _ by_decide, f₂.1 _ by_decide]; exact hd
  have g₂ : FrameB BRest c₁ c₂ := FrameB.mono f₂ fun r hr => by zundb
  have g₃ : FrameB BRest c₂ c₃ := FrameB.mono f₃ fun r hr => by zundb
  have g₄ : FrameB BRest c₃ c₄ := FrameB.mono f₄ fun r hr => by zundb
  by_cases hdg : FoundC V c.nmem t ∧ DegC P C V c.nmem t
  · obtain ⟨h53, hA, hB⟩ := d₄ hdg
    refine ⟨c₄, _, .seq e₁ (.ifLtN_true ztfpm (.seq e₂ (.seq e₃ (.seq e₄
      (.ifLtN_false (by rw [h53, hq₄.one]; omega) ztuvm))))), by_omega,
      g₁.trans (g₂.trans (g₃.trans g₄)), Or.inr (Or.inl ⟨hab, t, hpart, hdg.1, hdg.2, hA, hB⟩)⟩
  -- 5. the main phase
  have x53' : c₄.nreg 120053 = 0 := by_grind
  have x140 : c₄.nreg 120140 = c₃.nreg 120140 := nd₄ hdg _
  have x141 : c₄.nreg 120141 = c₃.nreg 120141 := nd₄ hdg _
  obtain ⟨c₅, k₅, bD, e₅, hk₅, f₅, hD₅, hbD₅, pk, hloc₅, hit₅, hb₅, o5, o6⟩ :=
    mainS_exec hcov (P := P) hG hW hs c₄ e₄.wb_right hq₄ by_grind
      by_grind (by rw [m₄]; exact hL) hDL htv (NC := NC) (CS := CS)
      ztgjq ztgjq
      by_omega (by
        intro bD hbD hbm k hk
        rw [m₄] at hbD
        have := hvalid t hpart hdg bD hbD hbm k hk
        unfold mainPos at this
        rwa [selOf_congr (C := C) (V := V) (bD := bD) (f := c₄.nreg 120140 = 1)
          (f' := FoundC V c.nmem t) (w := c₄.nreg 120141) (w' := nearC V c.nmem t)
          (cb := CBof P C V bD ztqko) (cb' := CBof P C V bD ztftk)
          by_grind ztbay
          ztbay])
  rw [m₄] at hD₅ hit₅ hk₅
  have hsel : selOf C V bD (c₄.nreg 120140 = 1) ztqko (CBof P C V bD ztqko) =
      selOf C V bD (FoundC V c.nmem t) ztftk (CBof P C V bD ztftk) :=
    selOf_congr by_grind
      ztbay
      ztbay
  rw [hsel] at hloc₅
  have g₅ : FrameB BRest c₄ c₅ := FrameB.mono f₅ fun r hr => by zundb
  refine ⟨c₅, _, .seq e₁ (.ifLtN_true ztfpm (.seq e₂ (.seq e₃ (.seq e₄
    (.ifLtN_true (by rw [x53', hq₄.one]; omega) e₅))))), by_omega,
    g₁.trans (g₂.trans (g₃.trans (g₄.trans g₅))),
    Or.inr (Or.inr ⟨hab, t, hpart, hdg, bD, hD₅, hbD₅, pk, fun k hk => ?_, hit₅, hb₅, o5, o6⟩)⟩
  unfold mainPos; grind
open Classical in
/-- The abscissa of the endpoint `(w, h + 1)` of a chord of class `1`. -/
noncomputable def xpX' (P : Polygon) (C : Chain) (V : QV) (w h : ℕ) : ℝ :=
  ((xpSym C V P.n w h).eval zta).1

/-- **The order of the chord table**: by height vertex, then by the class of the left end, then
by the abscissa of the left end. -/
def ChLe (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ) (i j : ℕ) : Prop :=
  chH m V i < chH m V j ∨ (chH m V i = chH m V j ∧
    (xpClass ztbdb < xpClass ztllz ∨ (xpClass ztbdb = xpClass ztllz ∧
      (xpClass ztbdb = 1 →
        xpX' P C V ztbdb ztccz ≤ xpX' P C V ztllz (chH m V j)))))

/-- **The structure of Lemma 3.6 in memory.** -/
structure QAt (P : Polygon) (m : ℕ → ℕ) (O E : ℕ) (V : QV) (H : Host) (C : Chain) (N : NF)
    (B : OracleBook.BookData) (k : ℕ) : Prop where
  lD : m O = V.D
  lNB : m (O + 1) = V.NB
  lE : m ztnnm = E
  lA : m (O + 4) = V.A
  lPOS : m (O + 5) = V.POS
  lFL : m (O + 6) = V.FL
  lLAB : m (O + 7) = V.LAB
  lDL : m (O + 8) = V.DL
  lnD : m (O + 9) = V.nD
  lORD : m (O + 10) = V.ORD
  lRK : m (O + 11) = V.RK
  lCH : m (O + 12) = V.CH
  lK : m (O + 13) = V.K
  lMD : m (O + 14) = V.MD
  lTB : m (O + 15) = V.TB
  lL : m (O + 16) = V.L
  lμ : m (O + 17) = V.μ
  O_le : O + 18 ≤ E
  -- the chain
  ds : m (V.D + 1) = V.s
  dm : m (V.D + 2) = V.m
  dt : m (V.D + 3) = V.tIdx
  dβ : m (V.D + 4) = V.β
  sS : V.sS = if V.β = 1 then V.tIdx else 2 * V.m - V.tIdx
  tv : V.tv = (V.s + V.tIdx) % P.n
  desc : ChainDescAt m V.D zta H C
  CQ : C.P = Qof P
  simple : C.P.Simple
  hostLen : H.length ≤ 64
  hostWF : HostWF P.n H
  D_le : V.D + 5 ≤ E
  host_le : m V.D + 3 * H.length + 4 ≤ E
  s_lt : C.s < C.P.n
  -- the normal form
  nCB : m zttdu = V.CB
  nAB : m ztfos = V.AB
  nRB : m zttdv = V.RB
  nSB : m ztfot = V.SB
  nLB : m zttdw = V.LB
  nf : NFAt m V.NB N
  canon : IsCanonicalNF ztc zta N (m ztbpo) 4
  hA : V.A = N.arcs.length
  hK : V.K = N.chords.length
  regs : ∀ r, r < N.regions.length → V.RB + 5 * r + 4 < E ∧
    ∀ t, t < (N.region r).arcs.length → V.LB + m (V.RB + 5 * r + 1) + t < E
  -- the inverse of the arc-sequence table
  pos : ∀ j, j < V.A → m ztfou < V.A ∧ N.seq.getD ztzgk 0 = j
  POS_le : V.POS + V.A ≤ E
  -- the book and its clusters
  gOK : GraphOK C zta N B
  μ : B.N = V.μ
  FL_le : V.FL + V.μ ≤ E
  LAB_le : V.LAB + V.μ ≤ E
  hlab : ∀ u v (w : (bookGraph B).Walk u v), ztinb →
    m ztnqb = m ztnqc
  dl : ∀ i, i < V.nD → m ztdgi < V.μ ∧ m ztzki = 1
  dl_all : ∀ v, v < V.μ → m ztdtp = 1 → ∃ i, i < V.nD ∧ m ztdgi = v
  DL_le : V.DL + V.nD ≤ E
  nD_le : V.nD ≤ 7 * k ^ 2
  clus : ∀ l, ((Finset.range V.μ).filter fun v => m ztdtp ≠ 1 ∧ m ztnqc = l).card ≤ k ^ 2
  k_pos : 1 ≤ k
  μ_le : V.μ ≤ k ^ 3
  μ_A : V.μ ≤ V.A + 3
  k_min : k = 1 ∨ ztie ^ 3 < V.μ
  -- the order by label
  ord_lt : ∀ i, i < V.μ → m ztjnn < V.μ
  ord_inj : ∀ i j, i < V.μ → j < V.μ → m ztjnn = m zttdx → i = j
  ord_rk : ∀ u, u < V.μ → m ztnqd < V.μ ∧ m (V.ORD + m ztnqd) = u
  ord_sorted : ∀ i j, i ≤ j → j < V.μ → m (V.LAB + m ztjnn) ≤ m (V.LAB + m zttdx)
  ORD_le : V.ORD + V.μ ≤ E
  RK_le : V.RK + V.μ ≤ E
  -- the chord table
  ch_lt : ∀ q, q < V.K → m ztjnm < V.K
  ch_inj : ∀ q q', q < V.K → q' < V.K → m ztjnm = m zttdq → q = q'
  ch_sorted : ∀ q q', q ≤ q' → q' < V.K → ChLe P C V m (m ztjnm) (m zttdq)
  -- the table of powers
  tab : ∀ j, j < V.L → m ztnqe = 2 ^ j
  A_lt : V.A < 2 ^ V.L
  K_lt : V.K < 2 ^ V.L
  L_le : V.L ≤ Nat.clog 2 ztjnl + 1
  TB_le : V.TB + V.L ≤ E
  CH_le : V.CH + V.K ≤ V.TB
  NB_TB : V.NB + 12 ≤ V.TB
  AB_TB : V.AB + 5 * V.A ≤ V.TB
  SB_TB : V.SB + V.A ≤ V.TB
  CB_TB : ∀ i, i < V.K → V.CB + 5 * i + 5 ≤ V.TB
  -- the model descriptor
  md0 : m V.MD = 0
  md : ∀ i, i < 5 → m ztqdd = m zttdr
  MD_le : V.MD + 6 ≤ E

/-- **The structure predicate of the oracle**: the structure, robustly below its bound. -/
def OAt (P : Polygon) (m : ℕ → ℕ) (O : ℕ) : Prop :=
  ∃ E, m ztnnm = E ∧ O + 4 ≤ E ∧
    Robust E m fun m' => ∃ V H C N B k, QAt P m' O E V H C N B k
open NFLoc (seq_lt seq_length)
variable {P : Polygon} {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain} {N : NF}
  {B : OracleBook.BookData} {k : ℕ}
theorem QAt.isNF (h : QAt P m O E V H C N B k) : IsNF ztc zta N := h.canon.1
theorem QAt.nodeMem (h : QAt P m O E V H C N B k) : NodeMemOK m V N :=
  ⟨h.nf, h.nAB, h.nRB, h.nSB, h.nLB, h.hA, h.pos⟩

/-- The ends of the arc records lie on walk edges. -/
theorem QAt.edges_lt (h : QAt P m O E V H C N B k) {j : ℕ} (hj : j < N.arcs.length) :
    (N.arc j).s.edge < 2 * V.m + 7 ∧ (N.arc j).e.edge < 2 * V.m + 7 := by
  zuif

  have hnW : ztkyz := by
    rw [walk_n]
    have := h.desc.2.2.2.1
    rw [← h.dm, this]
  have hkey : ∀ (w : WPos), ProperPos ztc zta (Qof P).n w →
      (chainModel C).key zta w < (chainModel C).W.n → w.edge < 2 * V.m + 7 := by
    zujbr
    have : ztfkn := by
      have := hw.1
      zuckv
      linarith
    zukvd
    zufc
  exact ⟨hkey _ hs harc.2.1, hkey _ he harc.2.2.2.1⟩

/-- **The memory facts of the scans** from the structure. -/
theorem QAt.qmem (h : QAt P m O E V H C N B k) {W : ℕ} (hEW : E ≤ W) : QMem V m W := by
  zudnq
  zuiyi
  zubxu
  have hAB := h.AB_TB
  have hTB := h.TB_le
  have hSB := h.SB_TB
  have hPOS := h.POS_le
  refine ⟨?_, fun j hj => ?_, fun v hv => ?_⟩
  · omega
  · have hjN : ztsjo := by zunkj; exact hj
    obtain ⟨e1, e2⟩ := h.edges_lt hjN
    refine ⟨by rw [arcSe_eq hm hj]; exact e1, by rw [arcEe_eq hm hj]; exact e2,
      (h.pos j hj).1, by_omega, by_omega⟩
  · have hvA : v < N.arcs.length := by zunkj; exact hv
    have hj0 : ztorf := by
      have := hm.nf.2.2.2.2.2.2.2.2.1 v ztmcu
      zucrf
    zuhyt
    have hr : ztorg := by
      have := (hm.nf.2.2.2.2.2.2.1 _ hj0A).1
      zucag
    zufwf
    zubhd
    have hna' : ztygu := by
      zucff
    obtain ⟨hr1, hr2⟩ := h.regs _ hrR
    have hls : nodeLs m V v = m (V.RB + 5 * rgi N v + 1) := by unfold nodeLs; zvnel
    have hne : 0 < (N.region ztcax).arcs.length := by
      have hmem : sj N v ∈ (N.region ztcax).arcs := ((hA.2.2.2 _ hrR _).2 ⟨hj0A, rfl⟩)
      grind
    have h0 := hr2 0 hne
    refine ⟨by_omega, by rw [hj0, ← h.hA] at *; omega, by_omega, by_omega,
      fun t ht => zthma⟩
    zugej
    have hlt : nodeArc m V v t = (N.region ztcax).arcs.getD t 0 := by
      zubiw
    have hmem : (N.region ztcax).arcs.getD t 0 ∈ (N.region ztcax).arcs := by
      simp_all
    rw [hlt, h.hA]
    exact ((hA.2.2.2 _ hrR _).1 hmem).1
theorem QAt.ordOK (h : QAt P m O E V H C N B k) {W : ℕ} (hEW : E ≤ W) : OrdOK m V W := by
  have := h.ORD_le; have := h.RK_le; have := h.LAB_le
  exact ⟨by_omega, h.ord_lt, h.ord_inj, h.ord_rk, h.ord_sorted, by_omega, by_omega, by_omega⟩
theorem QAt.chordMem (h : QAt P m O E V H C N B k) {W : ℕ} (hEW : E ≤ W) :
    ChordMemOK V m W := by
  have := h.TB_le
  exact ⟨h.tab, h.K_lt, h.CH_le, by_omega, fun i hi => by have := h.CB_TB i hi; omega⟩
theorem QAt.chordTab (h : QAt P m O E V H C N B k) {W : ℕ} (hEW : E ≤ W) :
    ChordTabOK V m W := by
  have := h.TB_le; have := h.CH_le
  exact ⟨h.ch_lt, by_omega, fun i hi => by have := h.CB_TB i hi; omega⟩

/-- The chain descriptor copied into the model descriptor. -/
theorem QAt.mdDesc (h : QAt P m O E V H C N B k) : ChainDescAt m zttdt zta H C := by
  obtain ⟨hH, hP, h1, h2, h3, h4⟩ := h.desc
  have e : ∀ i, i < 5 → m ztqdd = m zttdr := h.md
  have e0 := e 0 by_omega; have e1 := e 1 by_omega; have e2 := e 2 by_omega
  have e3 := e 3 by_omega; have e4 := e 4 by_omega
  zufba
  refine ⟨by_simp_all, hP, by_omega, ?_, ?_, ?_⟩
  · omega
  · omega
  simp_all
theorem QAt.modelDesc (h : QAt P m O E V H C N B k) :
    ModelDescAt m V.MD zta ztc :=
  Or.inl ⟨h.md0, H, C, h.mdDesc, rfl⟩
theorem QAt.modelDescWF (h : QAt P m O E V H C N B k) : ModelDescWF P E m V.MD := by
  refine ⟨h.MD_le, fun _ => ⟨by have := h.MD_le; omega, fun H' C' hC' => ?_⟩⟩
  have hH : ztiyi := NFLoc.hostAt_unique hC'.1 h.mdDesc.1
  have hC : ztkzv := NFLoc.chain_eq_of_desc hC' h.mdDesc
  subst hH hC
  have e0 : m zttdt = m V.D := by have := h.md 0 by_omega; omega
  exact ⟨h.hostLen, h.hostWF, by zvokq; exact h.host_le, h.s_lt⟩

/-- **The memory facts of double identification** from the structure. -/
theorem QAt.locMem (h : QAt P m O E V H C N B k) {W : ℕ} (hEW : E ≤ W)
    (hW : hostWords P.n ≤ W) : LocMemOK P V m W ztc N := by
  obtain ⟨hMD, hwf⟩ := NFLoc.locChainWF_of h.modelDescWF hEW hW
  zudnq
  have := h.TB_le; have := h.NB_TB; have := h.AB_TB; have := h.SB_TB
  have hAμ : V.A ≤ V.μ := by rw [h.hA, ← h.μ]; exact h.gOK.arcs_le
  refine ⟨h.modelDesc, Or.inl ztkiq, hMD, hwf, h.nf, hN, h.hA, fun j hj => ?_,
    h.tab, h.A_lt, by_omega, by rw [h.nAB]; omega, by rw [h.nSB]; omega, by_omega, hAμ⟩
  zubtu
  have := (hpp j hj).1
  zuic
