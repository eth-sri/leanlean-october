module

public import Chazelle.Core.NFBuildCmpRam

/-!
# WP-C (BuildNF), RAM part 2: the comparator of the event sort

The event codes `c < 2K` have records of four words at `T + 4 c` (`RecsAt`): the walk position
`wposOf L c` (edge, height code), the parity `c mod 2` and the chord `c / 2`.  `evCmp` compares
the codes in `sr 0`, `sr 1` (the registers of `SortR`) and writes into `sr 2` the bit of the
total preorder `evLeB` (`evCmp_exec`): the order `codeLe` (key, then tie bit) on codes below `2K`,
the codes below `2K` before the others, and the natural order on the others.  Each key comparison
is `keyDec` after the direction procedure of the query edge (`halfS`).
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open BuildNF (codeLe wposOf tieBit)

@[expose] public section

/-! ## The order -/

open Classical in
/-- **The order of the sort**: `codeLe` on the codes below `N`, those before the others, the
natural order on the others. -/
noncomputable def evLeB (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (N a b : ℕ) : Bool :=
  if a < N then (if b < N then decide (codeLe M Q L a b) else true)
  else (if b < N then false else decide (a ≤ b))

theorem evLeB_total (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (N a b : ℕ) :
    (evLeB M Q L N a b || evLeB M Q L N b a) = true := by
  unfold evLeB
  split_ifs <;> simp_all
  · rcases BuildNF.codeLe_total M Q L a b with h | h <;> simp [h]
  · omega

theorem evLeB_trans (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (N a b c : ℕ)
    (h1 : evLeB M Q L N a b = true) (h2 : evLeB M Q L N b c = true) :
    evLeB M Q L N a c = true := by
  unfold evLeB at *
  split_ifs at h1 h2 ⊢ <;> simp_all
  · exact BuildNF.codeLe_trans M Q L h1 h2
  · omega

/-! ## The records -/

/-- **The event records** at `T`: the walk position, the parity and the chord of each code. -/
def RecsAt (m : ℕ → ℕ) (T : ℕ) (L : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ c, c < 2 * L.length → m (T + 4 * c) = (wposOf L c).edge ∧
    m (T + 4 * c + 1) = (wposOf L c).hgt ∧ m (T + 4 * c + 2) = c % 2 ∧ m (T + 4 * c + 3) = c / 2

/-! ## The program -/

/-- Load the record of the code in `src` (address register `ad`): edge, code and parity into
`o`, `o + 1`, `o + 2`; `r42102 = 1`. -/
def loadRec (src ad o : ℕ) : Stmt :=
  block [.addN ad src src, .addN ad ad ad, .addN ad ad 42000, .loadN o ad, .addN ad ad 42102,
    .loadN (o + 1) ad, .addN ad ad 42102, .loadN (o + 2) ad]

/-- The tie bit of parity `par` with direction code `dd` into `dst` (`r42102 = 1`,
`r42104 = 2`). -/
def tbS (dd par dst : ℕ) : Stmt :=
  .ifLtN dd 42104 (.instr (.copyN dst par))
    (.ifLtN 42104 dd (.instr (.copyN dst par)) (.instr (.subN dst 42102 par)))

/-- Both codes in range. -/
def inCmp : Stmt :=
  .seq (block [.constN 42102 1, .constN 42104 2])
    (.seq (loadRec 30000 42101 42110) (.seq (loadRec 30001 42103 42113)
      (.seq (halfS 42113 42114 42110 42111 42116 42117)
        (.seq (halfS 42110 42111 42113 42114 42118 42119)
          (.seq (tbS 42118 42112 42120) (.seq (tbS 42116 42115 42121)
            (.ifLtN 42117 42102 (.instr (.constN 30002 0))
              (.ifLtN 42119 42102 (.instr (.constN 30002 1))
                (.ifLtN 42121 42120 (.instr (.constN 30002 0)) (.instr (.constN 30002 1)))))))))))

/-- **The comparator** of the event sort. -/
def evCmp : Stmt :=
  .ifLtN 30000 42001
    (.ifLtN 30001 42001 inCmp (.instr (.constN 30002 1)))
    (.ifLtN 30001 42001 (.instr (.constN 30002 0))
      (.ifLtN 30001 30000 (.instr (.constN 30002 0)) (.instr (.constN 30002 1))))

/-! ## The mathematics of the comparison -/

section math

variable {M : Model} {P : Polygon} {L : List (ℕ × ℕ × ℕ)}

theorem wposOf_hgt (L : List (ℕ × ℕ × ℕ)) (c : ℕ) :
    (wposOf L c).hgt = (L.getD (c / 2) (0, 0, 0)).1 + 1 := by
  unfold wposOf; split_ifs <;> rfl

/-- The walk positions of the events are positions of the walk proper. -/
theorem properPos_ev (hL : ChordTriplesOK M (Qof P) L) {c : ℕ} (hc : c < 2 * L.length) :
    ProperPos M (Qof P) P.n (wposOf L c) := by
  have hA := BuildNF.attach_wposOf hL hc
  have hi : c / 2 < L.length := by omega
  have hh := hL.2.2.2 _ (BuildOrder.getD_mem hi)
  have hn : (Qof P).n = P.n := shear_n _ _
  refine ⟨hA.2.1, hA.2.2.1, ?_⟩
  rw [wposOf_hgt]
  omega

theorem edge_lt (hL : ChordTriplesOK M (Qof P) L) {c : ℕ} (hc : c < 2 * L.length) :
    (wposOf L c).edge < M.W.n := (BuildNF.attach_wposOf hL hc).1

/-- The machine decision against an event position is the order of keys. -/
theorem keyDec_ev (hL : ChordTriplesOK M (Qof P) L) {a b : ℕ} (ha : a < 2 * L.length)
    (hb : b < 2 * L.length) :
    keyDec (Qof P) P.n (wposOf L b) (dirCode M (wposOf L b).edge) (wposOf L a) = true ↔
      M.key (Qof P) (wposOf L a) ≤ M.key (Qof P) (wposOf L b) := by
  rw [keyDec_iff (properPos_ev hL hb) (properPos_ev hL ha)]
  unfold KeyPred
  rw [ite_eq_right (by rw [wposOf_hgt]; omega)]

/-- The tie bit from the direction code. -/
theorem tieBit_eq (M : Model) (L : List (ℕ × ℕ × ℕ)) (c : ℕ) :
    tieBit M L c = (if dirCode M (wposOf L c).edge = 2 then 1 - c % 2 else c % 2) := by
  unfold tieBit dirCode
  by_cases h1 : (M.wa (wposOf L c).edge).2 < (M.wb (wposOf L c).edge).2
  · rw [ite_eq_right (not_lt.2 h1.le), ite_eq_left h1, ite_eq_right (by norm_num)]
  · rw [ite_eq_right h1]
    by_cases h2 : (M.wb (wposOf L c).edge).2 < (M.wa (wposOf L c).edge).2
    · rw [ite_eq_left h2, ite_eq_left h2, ite_eq_left rfl]
    · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_right (by norm_num)]

theorem dirCode_le (M : Model) (e : ℕ) : dirCode M e ≤ 2 := by
  unfold dirCode; split_ifs <;> omega

end math

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ}

/-- Loading a record. -/
theorem loadRec_exec (d : Config) (hw : WordsBounded W d) {src ad o : ℕ} {c T : ℕ}
    (hs : d.nreg src = c) (hT : d.nreg 42000 = T) (h1 : d.nreg 42102 = 1)
    (_hsrc : src ≠ ad) (hsT : ad ≠ 42000) (h102 : ad ≠ 42102) (hc : T + 4 * c + 2 ≤ W)
    (ho : o ≠ ad ∧ o + 1 ≠ ad ∧ o + 2 ≠ ad) (ho2 : 42102 < o ∨ o + 2 < 42102) :
    ∃ d' k, Exec P W (loadRec src ad o) d d' k ∧ k = 8 ∧
      d'.nreg o = d.nmem (T + 4 * c) ∧ d'.nreg (o + 1) = d.nmem (T + 4 * c + 1) ∧
      d'.nreg (o + 2) = d.nmem (T + 4 * c + 2) ∧
      (∀ r, r ≠ ad → r ≠ o → r ≠ o + 1 → r ≠ o + 2 → d'.nreg r = d.nreg r) ∧
      d'.nmem = d.nmem ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output ∧
      d'.nreg ad = T + 4 * c + 2 := by
  obtain ⟨o1, o2, o3⟩ := ho
  unfold loadRec
  exec_block
  · rw [hs]; omega
  · config_simp; rw [hs]; omega
  · config_simp
    simp (disch := omega) only [upd_other]
    rw [hs, hT]; omega
  · config_simp
    simp (disch := omega) only [upd_other, upd_same]
    rw [hs, hT, h1]; omega
  · config_simp
    simp (disch := omega) only [upd_other, upd_same]
    rw [hs, hT, h1]; omega
  · refine ⟨rfl, ?_, ?_, ?_, fun r r1 r2 r3 r4 => ?_, rfl, rfl, rfl, rfl, ?_⟩
    · simp (disch := omega) only [upd_other, upd_same]
      rw [hs, hT]; congr 1; omega
    · simp (disch := omega) only [upd_other, upd_same]
      rw [hs, hT, h1]; congr 1; omega
    · simp (disch := omega) only [upd_other, upd_same]
      rw [hs, hT, h1]; congr 1; omega
    · simp (disch := omega) only [upd_other]
    · simp (disch := omega) only [upd_other, upd_same]
      rw [hs, hT, h1]; omega

/-- The tie bit on the machine. -/
theorem tbS_exec (d : Config) (hw : WordsBounded W d) {dd par dst : ℕ} (h1 : d.nreg 42102 = 1)
    (h2 : d.nreg 42104 = 2) (hd : d.nreg dd ≤ 2) :
    ∃ d' k, Exec P W (tbS dd par dst) d d' k ∧ k ≤ 5 ∧
      d'.nreg dst = (if d.nreg dd = 2 then 1 - d.nreg par else d.nreg par) := by
  unfold tbS
  by_cases a1 : d.nreg dd < 2
  · refine spec_ifLtN_true (by rwa [h2])
      (spec_instr (Exec.copyN hw _ _) fun _ => ⟨by omega, ?_⟩)
    simp only [upd_same]; rw [ite_eq_right (by omega)]
  · have : d.nreg dd = 2 := by omega
    refine spec_ifLtN_false (by rwa [h2])
      (spec_ifLtN_false (by rw [h2, this]; omega)
        (spec_instr (Exec.subN hw _ _ _) fun _ => ⟨by omega, ?_⟩))
    simp only [upd_same]; rw [ite_eq_left this, h1]


/-- The final decision of `inCmp`. -/
theorem final_exec (d : Config) (hw : WordsBounded W d) (h1 : d.nreg 42102 = 1) :
    ∃ d' k, Exec P W (.ifLtN 42117 42102 (.instr (.constN 30002 0))
      (.ifLtN 42119 42102 (.instr (.constN 30002 1))
        (.ifLtN 42121 42120 (.instr (.constN 30002 0)) (.instr (.constN 30002 1))))) d d' k ∧
      k ≤ 7 ∧ d'.nreg 30002 = (if d.nreg 42117 < 1 then 0 else if d.nreg 42119 < 1 then 1 else
        if d.nreg 42121 < d.nreg 42120 then 0 else 1) := by
  by_cases a1 : d.nreg 42117 < 1
  · exact spec_ifLtN_true (by rwa [h1]) (spec_instr (Exec.constN hw _ _ (by
      have := hw.1 42102; omega)) fun _ => ⟨by omega, by rw [ite_eq_left a1]; simp⟩)
  refine spec_ifLtN_false (by rwa [h1]) ?_
  by_cases a2 : d.nreg 42119 < 1
  · exact spec_ifLtN_true (by rwa [h1]) (spec_instr (Exec.constN hw _ _ (by
      have := hw.1 42102; omega)) fun _ => ⟨by omega, by rw [ite_eq_right a1, ite_eq_left a2]; simp⟩)
  refine spec_ifLtN_false (by rwa [h1]) ?_
  by_cases a3 : d.nreg 42121 < d.nreg 42120
  · exact spec_ifLtN_true a3 (spec_instr (Exec.constN hw _ _ (by
      have := hw.1 42102; omega)) fun _ => ⟨by omega, by rw [ite_eq_right a1, ite_eq_right a2, ite_eq_left a3]; simp⟩)
  · exact spec_ifLtN_false a3 (spec_instr (Exec.constN hw _ _ (by
      have := hw.1 42102; omega)) fun _ => ⟨by omega, by rw [ite_eq_right a1, ite_eq_right a2, ite_eq_right a3]; simp⟩)

/-- The registers `inCmp` writes. -/
def BinCmp (r : ℕ) : Bool :=
  decide (10000 ≤ r ∧ r < 10503) || decide (40000 < r ∧ r < 40103) ||
    decide (42100 ≤ r ∧ r < 42200) || decide (r = 30002)

theorem wr_inCmp : wr BinCmp inCmp = true := by
  have h1 : ∀ qe qh se sh dd dst : ℕ, 42100 ≤ dd → dd < 42200 → 42100 ≤ dst → dst < 42200 →
      wr BinCmp (halfS qe qh se sh dd dst) = true := fun _ _ _ _ _ _ h1 h2 h3 h4 =>
    wr_mono (fun r hr => by
      simp only [BhalfS, Bhalf, Bool.or_eq_true, decide_eq_true_eq] at hr
      simp only [BinCmp, Bool.or_eq_true, decide_eq_true_eq]; omega) wr_halfS
  have e1 := h1 42113 42114 42110 42111 42116 42117 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have e2 := h1 42110 42111 42113 42114 42118 42119 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  simp only [inCmp, wr, block, loadRec, tbS, wrOK, e1, e2, Bool.and_true, Bool.true_and]
  decide


/-- The write set of a tie-bit step. -/
theorem wr_tbS1 : wr (fun r => decide (r = 42120)) (tbS 42118 42112 42120) = true := by decide
theorem wr_tbS2 : wr (fun r => decide (r = 42121)) (tbS 42116 42115 42121) = true := by decide

open Classical in
/-- The comparison bit from the four machine bits. -/
theorem codeLe_bits {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {a b : ℕ} {x y ta tb : ℕ}
    (hx : x = if M.key Q (wposOf L a) ≤ M.key Q (wposOf L b) then 1 else 0)
    (hy : y = if M.key Q (wposOf L b) ≤ M.key Q (wposOf L a) then 1 else 0)
    (hta : ta = tieBit M L a) (htb : tb = tieBit M L b) :
    (if x < 1 then 0 else if y < 1 then 1 else if tb < ta then 0 else 1) =
      (if codeLe M Q L a b then 1 else 0) := by
  unfold codeLe
  subst hx hy hta htb
  by_cases h1 : M.key Q (wposOf L a) ≤ M.key Q (wposOf L b)
  · by_cases h2 : M.key Q (wposOf L b) ≤ M.key Q (wposOf L a)
    · have he := le_antisymm h1 h2
      simp only [he, lt_irrefl, false_or, true_and]
      by_cases h3 : tieBit M L b < tieBit M L a
      · simp [h3, not_le.2 h3]
      · simp [h3, not_lt.1 h3]
    · have hl := lt_of_le_not_ge h1 h2
      simp [h1, h2, hl]
  · have n1 : ¬ M.key Q (wposOf L a) < M.key Q (wposOf L b) := fun h => h1 h.le
    have n2 : ¬ M.key Q (wposOf L a) = M.key Q (wposOf L b) := fun h => h1 h.le
    simp [h1, n1, n2]

open Classical in
/-- **Both codes in range**: the comparison bit of `codeLe`. -/
theorem inCmp_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (d : Config) (hw : WordsBounded W d)
    {M : Model} {L : List (ℕ × ℕ × ℕ)} {D T : ℕ} (hD : d.nreg 40000 = D) (hDW : D + 6 ≤ W)
    (hCW : LocChainWF P W d.nmem D) (hM : ModelDescAt d.nmem D (Qof P) M)
    (hL : ChordTriplesOK M (Qof P) L) (hT : d.nreg 42000 = T) (hR : RecsAt d.nmem T L)
    (hTW : T + 8 * L.length ≤ W) (ha : d.nreg 30000 < 2 * L.length)
    (hb : d.nreg 30001 < 2 * L.length) :
    ∃ d' k, Exec P W inCmp d d' k ∧ k ≤ 11000 ∧
      d'.nreg 30002 = (if codeLe M (Qof P) L (d.nreg 30000) (d.nreg 30001) then 1 else 0) := by
  set a := d.nreg 30000
  set b := d.nreg 30001
  have hW1 : 2 ≤ W := by omega
  -- constants
  obtain ⟨d₀, k₀, x₀, hk₀, r₀⟩ : ∃ d₀ k₀, Exec P W (block [.constN 42102 1, .constN 42104 2]) d
      d₀ k₀ ∧ k₀ = 2 ∧ d₀ = { d with nreg := upd (upd d.nreg 42102 1) 42104 2 } := by
    have y1 := Exec.constN (P := P) hw 42102 1 (by omega)
    have y2 := Exec.constN (P := P) y1.wb_right 42104 2 (by omega)
    exact ⟨_, _, .seq y1 (.seq y2 (.skip y2.wb_right)), rfl, rfl⟩
  have w₀ := x₀.wb_right
  have g₀ : ∀ r, r ≠ 42102 → r ≠ 42104 → d₀.nreg r = d.nreg r := fun r h1 h2 => by
    rw [r₀]; simp [upd_other _ _ _ h1, upd_other _ _ _ h2]
  have o₀ : d₀.nreg 42102 = 1 := by rw [r₀]; simp
  have t₀ : d₀.nreg 42104 = 2 := by rw [r₀]; simp
  have m₀ : d₀.nmem = d.nmem := by rw [r₀]
  -- record of `a`
  obtain ⟨ha1, ha2, ha3, -⟩ := hR a ha
  obtain ⟨hb1, hb2, hb3, -⟩ := hR b hb
  obtain ⟨d₁, k₁, x₁, hk₁, e₁, h₁, p₁, g₁, m₁, -, -, -⟩ := loadRec_exec (P := P) d₀ w₀
    (src := 30000) (ad := 42101) (o := 42110) (c := a) (T := T)
    (by rw [g₀ _ (by norm_num) (by norm_num)]) (by rw [g₀ _ (by norm_num) (by norm_num), hT])
    o₀ (by norm_num) (by norm_num) (by norm_num) (by omega) (by norm_num) (by norm_num)
  have w₁ := x₁.wb_right
  obtain ⟨d₂, k₂, x₂, hk₂, e₂, h₂, p₂, g₂, m₂, -, -, -⟩ := loadRec_exec (P := P) d₁ w₁
    (src := 30001) (ad := 42103) (o := 42113) (c := b) (T := T)
    (by rw [g₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      g₀ _ (by norm_num) (by norm_num)])
    (by rw [g₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      g₀ _ (by norm_num) (by norm_num), hT])
    (by rw [g₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), o₀])
    (by norm_num) (by norm_num) (by norm_num) (by omega) (by norm_num) (by norm_num)
  have w₂ := x₂.wb_right
  have mm₂ : d₂.nmem = d.nmem := by rw [m₂, m₁, m₀]
  -- register values after the loads
  have g₂₁ : ∀ r, r ≠ 42101 → r ≠ 42103 → r ≠ 42102 → r ≠ 42104 → (r < 42110 ∨ 42115 < r) →
      d₂.nreg r = d.nreg r := fun r i1 i2 i3 i4 i5 => by
    rw [g₂ r i2 (by omega) (by omega) (by omega), g₁ r i1 (by omega) (by omega) (by omega),
      g₀ r i3 i4]
  have v10 : d₂.nreg 42110 = (wposOf L a).edge := by
    rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), e₁, m₀, ha1]
  have v11 : d₂.nreg 42111 = (wposOf L a).hgt := by
    rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), h₁, m₀, ha2]
  have v12 : d₂.nreg 42112 = a % 2 := by
    rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), p₁, m₀, ha3]
  have v13 : d₂.nreg 42113 = (wposOf L b).edge := by rw [e₂, m₁, m₀, hb1]
  have v14 : d₂.nreg 42114 = (wposOf L b).hgt := by rw [h₂, m₁, m₀, hb2]
  have v15 : d₂.nreg 42115 = b % 2 := by rw [p₂, m₁, m₀, hb3]
  have o₂ : d₂.nreg 42102 = 1 := by
    rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      g₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), o₀]
  have t₂ : d₂.nreg 42104 = 2 := by
    rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      g₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), t₀]
  have D₂ : d₂.nreg 40000 = D := by
    rw [g₂₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), hD]
  have ppa := properPos_ev hL ha
  have ppb := properPos_ev hL hb
  -- first half: key a ≤ key b
  obtain ⟨d₃, k₃, x₃, hk₃, dd₃, dst₃, f₃⟩ := halfS_exec (P := P) hG hW d₂ w₂
    (qe := 42113) (qh := 42114) (se := 42110) (sh := 42111) (dd := 42116) (dst := 42117)
    (by decide) (by decide) (by decide) (by rwa [D₂]) (by rwa [D₂, mm₂])
    (M := M) (by rwa [D₂, mm₂]) (by rw [v13]; exact edge_lt hL hb)
    (by rw [v14]; exact ppb.2.2)
  have w₃ := x₃.wb_right
  have g₃ : ∀ r, BhalfS 42116 42117 r = false → d₃.nreg r = d₂.nreg r := f₃.1
  have mm₃ : d₃.nmem = d.nmem := by rw [f₃.2.2.1, mm₂]
  have D₃ : d₃.nreg 40000 = D := by rw [g₃ _ (by decide), D₂]
  -- second half: key b ≤ key a
  obtain ⟨d₄, k₄, x₄, hk₄, dd₄, dst₄, f₄⟩ := halfS_exec (P := P) hG hW d₃ w₃
    (qe := 42110) (qh := 42111) (se := 42113) (sh := 42114) (dd := 42118) (dst := 42119)
    (by decide) (by decide) (by decide) (by rwa [D₃]) (by rwa [D₃, mm₃])
    (M := M) (by rwa [D₃, mm₃]) (by rw [g₃ _ (by decide), v10]; exact edge_lt hL ha)
    (by rw [g₃ _ (by decide), v11]; exact ppa.2.2)
  have w₄ := x₄.wb_right
  have g₄ : ∀ r, BhalfS 42118 42119 r = false → d₄.nreg r = d₃.nreg r := f₄.1
  -- tie bits
  have o₄ : d₄.nreg 42102 = 1 := by rw [g₄ _ (by decide), g₃ _ (by decide), o₂]
  have t₄ : d₄.nreg 42104 = 2 := by rw [g₄ _ (by decide), g₃ _ (by decide), t₂]
  obtain ⟨d₅, k₅, x₅, hk₅, v₅⟩ := tbS_exec (P := P) d₄ w₄ (dd := 42118) (par := 42112)
    (dst := 42120) o₄ t₄ (by rw [dd₄]; exact dirCode_le _ _)
  have w₅ := x₅.wb_right
  have f₅ := exec_frameB x₅ wr_tbS1
  have o₅ : d₅.nreg 42102 = 1 := by rw [f₅.1 _ (by decide), o₄]
  have t₅ : d₅.nreg 42104 = 2 := by rw [f₅.1 _ (by decide), t₄]
  obtain ⟨d₆, k₆, x₆, hk₆, v₆⟩ := tbS_exec (P := P) d₅ w₅ (dd := 42116) (par := 42115)
    (dst := 42121) o₅ t₅ (by rw [f₅.1 _ (by decide), g₄ _ (by decide), dd₃]; exact dirCode_le _ _)
  have w₆ := x₆.wb_right
  have f₆ := exec_frameB x₆ wr_tbS2
  have o₆ : d₆.nreg 42102 = 1 := by rw [f₆.1 _ (by decide), o₅]
  obtain ⟨d₇, k₇, x₇, hk₇, v₇⟩ := final_exec (P := P) d₆ w₆ o₆
  have X : Exec P W inCmp d d₇ (k₀ + (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + k₇))))))) :=
    .seq x₀ (.seq x₁ (.seq x₂ (.seq x₃ (.seq x₄ (.seq x₅ (.seq x₆ x₇))))))
  refine ⟨d₇, _, X, by omega, ?_⟩
  rw [v₇]
  apply codeLe_bits (x := d₆.nreg 42117) (y := d₆.nreg 42119)
  · rw [f₆.1 _ (by decide), f₅.1 _ (by decide), g₄ _ (by decide), dst₃, v13, v14, v10, v11]
    have := keyDec_ev hL ha hb
    by_cases hk : M.key (Qof P) (wposOf L a) ≤ M.key (Qof P) (wposOf L b)
    · rw [ite_eq_left (this.2 hk), ite_eq_left hk]
    · rw [ite_eq_right (fun h => hk (this.1 h)), ite_eq_right hk]
  · rw [f₆.1 _ (by decide), f₅.1 _ (by decide), dst₄, g₃ _ (by decide), g₃ _ (by decide),
      g₃ _ (by decide), g₃ _ (by decide), v13, v14, v10, v11]
    have := keyDec_ev hL hb ha
    by_cases hk : M.key (Qof P) (wposOf L b) ≤ M.key (Qof P) (wposOf L a)
    · rw [ite_eq_left (this.2 hk), ite_eq_left hk]
    · rw [ite_eq_right (fun h => hk (this.1 h)), ite_eq_right hk]
  · rw [f₆.1 _ (by decide), v₅, dd₄, g₄ _ (by decide), g₃ _ (by decide), g₃ _ (by decide), v10, v12,
      tieBit_eq]
  · rw [v₆, f₅.1 _ (by decide), f₅.1 _ (by decide), g₄ _ (by decide), g₄ _ (by decide), dd₃,
      g₃ _ (by decide), v13, v15, tieBit_eq]

end exec

/-! ## Separate write sets for natural and real registers -/

/-- The instruction writes a natural register accepted by `BN` or a real one accepted by `BR`. -/
def wrOK2 (BN BR : ℕ → Bool) : Instr → Bool
  | .inputSize r | .constN r _ | .copyN r _ | .addN r _ _ | .subN r _ _ | .loadN r _ => BN r
  | .constR r _ | .copyR r _ | .addR r _ _ | .subR r _ _ | .mulR r _ _ | .divR r _ _ => BR r
  | .loadR r _ | .readX r _ | .readY r _ => BR r
  | _ => false

/-- Every instruction of the statement satisfies `wrOK2 BN BR`. -/
def wr2 (BN BR : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => wrOK2 BN BR i
  | .seq s t => wr2 BN BR s && wr2 BN BR t
  | .ifLtN _ _ t e => wr2 BN BR t && wr2 BN BR e
  | .ifLtR _ _ t e => wr2 BN BR t && wr2 BN BR e
  | .whileLtN _ _ b => wr2 BN BR b
  | .whileLtR _ _ b => wr2 BN BR b

/-- The real registers outside `BR` are unchanged. -/
theorem exec_frameR {P : Polygon} {W : ℕ} {BN BR : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : wr2 BN BR s = true) :
    ∀ r, BR r = false → c'.rreg r = c.rreg r := by
  induction h with
  | skip _ => exact fun _ _ => rfl
  | @instr ins c c' _ he _ _ =>
    simp only [wr2] at hs
    cases ins <;> simp only [wrOK2, Bool.false_eq_true] at hs <;>
      simp only [Instr.effect, Option.some.injEq] at he <;>
      (try split at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;> subst he <;>
      intro j hj <;>
      first
      | rfl
      | (simp only [upd]; split_ifs with hh
         · subst hh; simp_all
         · rfl)
  | seq _ _ ih₁ ih₂ =>
    simp only [wr2, Bool.and_eq_true] at hs
    exact fun r hr => (ih₂ hs.2 r hr).trans (ih₁ hs.1 r hr)
  | ifLtN_true _ _ ih =>
    simp only [wr2, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtN_false _ _ ih =>
    simp only [wr2, Bool.and_eq_true] at hs; exact ih hs.2
  | ifLtR_true _ _ ih =>
    simp only [wr2, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtR_false _ _ ih =>
    simp only [wr2, Bool.and_eq_true] at hs; exact ih hs.2
  | whileLtN_false _ _ => exact fun _ _ => rfl
  | whileLtN_true _ _ _ ih₁ ih₂ => exact fun r hr => (ih₂ hs r hr).trans (ih₁ hs r hr)
  | whileLtR_false _ _ => exact fun _ _ => rfl
  | whileLtR_true _ _ _ ih₁ ih₂ => exact fun r hr => (ih₂ hs r hr).trans (ih₁ hs r hr)

/-- A single write set gives both. -/
theorem wr2_of_wr {B BN BR : ℕ → Bool} (hN : ∀ r, B r = true → BN r = true)
    (hR : ∀ r, B r = true → BR r = true) {s : Stmt} (h : wr B s = true) : wr2 BN BR s = true := by
  induction s with
  | skip => rfl
  | instr i =>
    simp only [wr] at h
    simp only [wr2]
    cases i <;> simp only [wrOK] at h <;> simp only [wrOK2] <;>
      first | exact hN _ h | exact hR _ h | exact h
  | seq s t ihs iht =>
    simp only [wr, Bool.and_eq_true] at h; simp only [wr2, ihs h.1, iht h.2, Bool.and_self]
  | ifLtN a b s t ihs iht =>
    simp only [wr, Bool.and_eq_true] at h; simp only [wr2, ihs h.1, iht h.2, Bool.and_self]
  | ifLtR a b s t ihs iht =>
    simp only [wr, Bool.and_eq_true] at h; simp only [wr2, ihs h.1, iht h.2, Bool.and_self]
  | whileLtN a b s ih => simp only [wr] at h; simp only [wr2, ih h]
  | whileLtR a b s ih => simp only [wr] at h; simp only [wr2, ih h]

/-- The real registers the comparator may write: bands `bSign` and `bBuild`. -/
def BRb (r : ℕ) : Bool := decide (bandOf r = bSign ∨ bandOf r = bBuild)

theorem wr2_evCmp : wr2 BinCmp BRb evCmp = true := by
  have h1 : ∀ qe qh se sh dd dst : ℕ, 42100 ≤ dd → dd < 42200 → 42100 ≤ dst → dst < 42200 →
      wr2 BinCmp BRb (halfS qe qh se sh dd dst) = true := fun _ _ _ _ _ _ h1 h2 h3 h4 =>
    wr2_of_wr (B := BhalfS _ _)
      (fun r hr => by
        simp only [BhalfS, Bhalf, Bool.or_eq_true, decide_eq_true_eq] at hr
        simp only [BinCmp, Bool.or_eq_true, decide_eq_true_eq]; omega)
      (fun r hr => by
        simp only [BhalfS, Bhalf, Bool.or_eq_true, decide_eq_true_eq] at hr
        rw [BRb, decide_eq_true_iff]; unfold bandOf bSign bBuild
        omega) wr_halfS
  have e1 := h1 42113 42114 42110 42111 42116 42117 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have e2 := h1 42110 42111 42113 42114 42118 42119 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  simp only [evCmp, inCmp, wr2, block, loadRec, tbS, wrOK2, e1, e2, Bool.and_true, Bool.true_and]
  decide

/-! ## The comparator contract -/

/-- The invariant of the comparator during the sort: descriptor, record table and code bound in
their registers, memory below `A₀` as at entry. -/
def EvJ (m₀ : ℕ → ℕ) (A₀ D T N : ℕ) (R : ℕ → ℕ) (d : Config) : Prop :=
  d.nreg 40000 = D ∧ d.nreg 42000 = T ∧ d.nreg 42001 = N ∧ (∀ a, a < A₀ → d.nmem a = m₀ a) ∧
    ∀ r, 43000 ≤ r → r < 44000 → d.nreg r = R r

/-- The invariant is insensitive to the writes of the sort. -/
theorem evJ_stable (m₀ : ℕ → ℕ) (A₀ D T N : ℕ) (R : ℕ → ℕ) :
    SortR.JStable (EvJ m₀ A₀ D T N R) A₀ := by
  intro c c' ⟨h1, h2, h3, h4, h5⟩ hr _ hm _ _
  refine ⟨?_, ?_, ?_, fun a ha => (hm a ha).trans (h4 a ha), fun r r1 r2 => ?_⟩
  · rw [hr _ (by unfold bandOf bSort; norm_num) (by unfold ALLOC; norm_num), h1]
  · rw [hr _ (by unfold bandOf bSort; norm_num) (by unfold ALLOC; norm_num), h2]
  · rw [hr _ (by unfold bandOf bSort; norm_num) (by unfold ALLOC; norm_num), h3]
  · rw [hr _ (by unfold bandOf bSort; omega) (by unfold ALLOC; omega), h5 r r1 r2]

theorem binCmp_band {r : ℕ} (h : BinCmp r = true) : bandOf r ∈ ({bSign, bBuild} : Finset ℕ) ∨
    r = 30002 := by
  simp only [BinCmp, Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [Finset.mem_insert, Finset.mem_singleton, bandOf, bSign, bBuild]
  omega

/-- **The comparator contract** of the event sort. -/
theorem evCmp_ok {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hWn : hostWords P.n ≤ W)
    {m₀ : ℕ → ℕ} {A₀ D T : ℕ} {M : Model} {L : List (ℕ × ℕ × ℕ)} (hAW : A₀ ≤ W)
    (hwf : ModelDescWF P A₀ m₀ D) (hM : ModelDescAt m₀ D (Qof P) M)
    (hL : ChordTriplesOK M (Qof P) L) (hR : RecsAt m₀ T L) (hTA : T + 8 * L.length ≤ A₀)
    (R : ℕ → ℕ) : SortR.CmpOK P W evCmp {bSign, bBuild} (EvJ m₀ A₀ D T (2 * L.length) R)
      (evLeB M (Qof P) L (2 * L.length)) 11010 := by
  intro d hw ⟨j1, j2, j3, j4, j5⟩
  have hW1 : 1 ≤ W := by unfold hostWords at hWn; omega
  have hW : P.n + 3 ≤ W := by unfold hostWords at hWn; omega
  -- the frame part, from the write set
  have wr_ev : wr BinCmp evCmp = true := by
    simp only [evCmp, wr, wr_inCmp, Bool.true_and]; decide
  have wr2_ev := wr2_evCmp
  suffices H : ∃ d' k, Exec P W evCmp d d' k ∧ k ≤ 11010 ∧
      d'.nreg 30002 = (if evLeB M (Qof P) L (2 * L.length) (d.nreg 30000) (d.nreg 30001) = true
        then 1 else 0) by
    obtain ⟨d', k, x, hk, hv⟩ := H
    have f := exec_frameB x wr_ev
    refine ⟨d', k, x, hk, ⟨?_, ?_, ?_, fun a ha => ?_, fun r r1 r2 => ?_⟩, hv, fun r r0 r1 r2 hr => ?_,
      fun r hr => exec_frameR x wr2_ev r (by simpa [BRb, Finset.mem_insert, Finset.mem_singleton] using hr), f.2.2.1, f.2.2.2.1, f.2.2.2.2⟩
    · rw [f.1 _ (by decide), j1]
    · rw [f.1 _ (by decide), j2]
    · rw [f.1 _ (by decide), j3]
    · rw [f.2.2.1]; exact j4 a ha
    · rw [f.1 r (by simp only [BinCmp, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega),
        j5 r r1 r2]
    · apply f.1
      by_contra hb
      rcases binCmp_band (Bool.not_eq_false _ ▸ hb) with h | h
      · rcases hr with hr | hr
        · exact hr h
        · rw [hr] at h; simp [bandOf, ALLOC, bSign, bBuild] at h
      · exact r2 h
  unfold evCmp evLeB
  by_cases ha : d.nreg 30000 < 2 * L.length
  · refine spec_ifLtN_true (by rwa [j3]) ?_
    by_cases hb : d.nreg 30001 < 2 * L.length
    · refine spec_ifLtN_true (by rwa [j3]) ?_
      have hm : ∀ a, a < A₀ → d.nmem a = m₀ a := j4
      obtain ⟨hM', hwf'⟩ := desc_agree hwf hM hm
      obtain ⟨hDW, hCW⟩ := locChainWF_of hwf' hAW hWn
      have hR' : RecsAt d.nmem T L := fun c hc => by
        obtain ⟨e1, e2, e3, e4⟩ := hR c hc
        refine ⟨(hm _ (by omega)).trans e1, (hm _ (by omega)).trans e2, (hm _ (by omega)).trans e3,
          (hm _ (by omega)).trans e4⟩
      obtain ⟨d', k, x, hk, hv⟩ := inCmp_exec hG hW d hw j1 hDW hCW hM' hL j2 hR'
        (by omega) ha hb
      refine ⟨d', k, x, by omega, ?_⟩
      rw [hv, ite_eq_left ha, ite_eq_left hb]
      by_cases hc : codeLe M (Qof P) L (d.nreg 30000) (d.nreg 30001) <;> simp [hc]
    · refine spec_ifLtN_false (by rwa [j3]) (spec_instr (Exec.constN hw _ _ hW1)
        fun _ => ⟨by omega, ?_⟩)
      simp [ha, hb]
  · refine spec_ifLtN_false (by rwa [j3]) ?_
    by_cases hb : d.nreg 30001 < 2 * L.length
    · refine spec_ifLtN_true (by rwa [j3]) (spec_instr (Exec.constN hw _ _ (by omega))
        fun _ => ⟨by omega, ?_⟩)
      simp [ha, hb]
    · refine spec_ifLtN_false (by rwa [j3]) ?_
      by_cases hc : d.nreg 30001 < d.nreg 30000
      · refine spec_ifLtN_true hc (spec_instr (Exec.constN hw _ _ (by omega))
          fun _ => ⟨by omega, ?_⟩)
        simp [ha, hb, not_le.2 hc]
      · refine spec_ifLtN_false hc (spec_instr (Exec.constN hw _ _ hW1)
          fun _ => ⟨by omega, ?_⟩)
        simp [ha, hb, not_lt.1 hc]




end

end BuildRam

end Chazelle.Core
