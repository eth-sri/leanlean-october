module

public import Chazelle.MacT
public import Chazelle.Core.OracleQuery
public import Chazelle.Mountain.PieceSteps
public import Chazelle.Chain.Submap
public import Chazelle.Core.NFDecompBfs
public import Chazelle.Core.OracleBook
public import Chazelle.Core.RestoreRound
public import Chazelle.Core.FuseMathCut
public import Chazelle.Core.GranRamBody
public import Chazelle.Core.FactsAttach
public import Chazelle.Core.ShootCutGrade

namespace Chazelle.Core
namespace Gran
open Machine Machine.Stmt Programs SignK
@[expose] public section
structure RegRec (m : ℕ → ℕ) (RB LB r dg w : ℕ) (ex : List ℕ) : Prop where
  deg : m zthci = dg
  wt : m (RB + 5 * r + 4) = w
  lst : ∀ t, t < dg → m ztyvg = ex.getD t 0
  len : ex.length = dg

/-- One slot (`r81 = t`, `r78` the slot base, `r79` the degree, `r80` the list base). -/
def slotBody : Stmt :=
  .seq (.instr (.addN 90082 90078 90081))
    (.seq (.ifLtN 90081 90079 (block [.addN 90083 90080 90081, .loadN 90084 90083,
        .storeN 90082 90084]) (block [.constN 90084 0, .storeN 90082 90084]))
      (.instr (.addN 90081 90081 90019)))

/-- The slot loop. -/
def slotLoop : Stmt := .whileLtN 90081 90002 slotBody

/-- The slot-loop invariant. -/
structure SlotI (W D S L deg : ℕ) (ex : List ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  t_le : c.nreg 90081 ≤ D
  regs : ∀ r, r ≠ 90081 → r ≠ 90082 → r ≠ 90083 → r ≠ 90084 → c.nreg r = c₀.nreg r
  slot : ∀ u, u < c.nreg 90081 → c.nmem zttca = ex.getD u 0
  mem : ∀ a, ztlft → c.nmem a = c₀.nmem a
variable {P : Polygon} {W R D RB LB : ℕ}
theorem slotLoop_exec {W D S L deg : ℕ} {ex : List ℕ} {c₀ : Config}
    (hw : WordsBounded W c₀) (h81 : c₀.nreg 90081 = 0) (h02 : c₀.nreg 90002 = D)
    (h78 : c₀.nreg 90078 = S) (h79 : c₀.nreg 90079 = deg) (h80 : c₀.nreg 90080 = L)
    (h19 : c₀.nreg 90019 = 1) (hlen : ex.length = deg) (_hdeg : deg ≤ D)
    (hsrc : ∀ t, t < deg → c₀.nmem ztsza = ex.getD t 0)
    (hdisj : ∀ t, t < deg → L + t < S ∨ S + D ≤ L + t) (hSW : S + D ≤ W) (hLW : L + deg ≤ W) :
    ∃ c' k, Exec P W slotLoop c₀ c' k ∧ k ≤ 9 * D + 2 ∧
      (∀ u, u < D → c'.nmem zttca = ex.getD u 0) ∧
      (∀ a, ztlft → c'.nmem a = c₀.nmem a) ∧
      (∀ r, r ≠ 90081 → r ≠ 90082 → r ≠ 90083 → r ≠ 90084 → c'.nreg r = c₀.nreg r) := by
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90081) (b := 90002)
    (body := slotBody) (SlotI W D S L deg ex c₀) (fun c => D - c.nreg 90081) 7 ztpf
    (fun c I ht => by
      obtain ⟨hwc, hle, hr, hs, hm⟩ := I
      rw [hr 90002 by_decide by_decide by_decide by_decide, h02] at ht
      have c78 : c.nreg 90078 = S := by_simp_all
      have c79 : c.nreg 90079 = deg := by
        simp_all
      have c80 : c.nreg 90080 = L := by_simp_all
      have c19 : zthoj := by
        grind
      generalize htu : c.nreg 90081 = t at ht hle hs
      have e₁ := Exec.addN (P := P) hwc 90082 90078 90081 by_omega
      set c₁ : Config := { c with nreg := upd c.nreg 90082 _ } with hc₁
      zud
      have d82 : c₁.nreg 90082 = S + t := by zvmxj; simp [upd, c78, htu]
      have d81 : c₁.nreg 90081 = t := by_tauto
      have d79 : c₁.nreg 90079 = deg := by_tauto
      have d80 : c₁.nreg 90080 = L := by_tauto
      have d19 : ztgas := by_tauto
      have dm : ztwh := rfl
      -- the store of the slot value
      obtain ⟨c₂, k₂, e₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 90081 90079
          (block [.addN 90083 90080 90081, .loadN 90084 90083, .storeN 90082 90084])
          (block [.constN 90084 0, .storeN 90082 90084])) c₁ c₂ k₂ ∧ k₂ ≤ 4 ∧
          (c₂.nmem = upd c.nmem zttbz (ex.getD t 0) ∧
            ∀ r, r ≠ 90083 → r ≠ 90084 → c₂.nreg r = c₁.nreg r) := by
        by_cases hlt : t < deg
        · zudd
          exec_block
          · omega
          · refine ⟨by_omega, ?_, fun r a1 a2 => by zunza⟩
            grind
        · zubv
          exec_block
          · omega
          · refine ⟨by_omega, ?_, fun r a1 a2 => by simp [upd, a2]⟩
            grind
      obtain ⟨q2, qr⟩ := q
      zue
      have f19 : ztizn := by_grind
      have f81 : c₂.nreg 90081 = t := by_grind
      have e₃ := Exec.addN (P := P) w₂ 90081 90081 90019 by_omega
      refine ⟨_, _, .seq e₁ ztcr, ⟨e₃.wb_right, ?_, fun r a1 a2 a3 a4 => ?_,
        fun u hu => ?_, fun a ha => ?_⟩, by_omega, ?_⟩
      · config_simp; omega
      · config_simp
        rw [Machine.upd_other _ _ _ a1, qr r a3 a4, hc₁]
        simp only [upd, a2, ite_false]
        grind
      · config_simp at hu; rw [f19, f81] at hu
        config_simp; rw [q2]
        by_cases hut : u = t
        · rw [hut]; simp
        · zugtv
      · config_simp; rw [q2, Machine.upd_other _ _ _ by_omega]; grind
      · config_simp; omega)
    ⟨hw, by_omega, fun _ _ _ _ _ => rfl, fun u hu => by_omega, fun _ _ => rfl⟩
  have hfull : c'.nreg 90081 = D := by
    rw [I'.regs 90002 by_decide by_decide by_decide by_decide, h02] at hx
    have := I'.t_le; omega
  refine ⟨c', k, e, ?_, fun u hu => I'.slot u by_omega, I'.mem, I'.regs⟩
  omega

/-- Degree, list base, weight and exit base of region `r70` (`r71 = RB + 5 r`, `r78` its slots). -/
def regHead : Stmt := block [.addN 90074 90071 90021, .loadN 90079 90074,
  .addN 90072 90035 90070, .storeN 90072 90079, .addN 90074 90071 90020, .loadN 90080 90074,
  .addN 90074 90074 90019, .loadN 90075 90074, .addN 90072 90036 90070, .storeN 90072 90075,
  .addN 90072 90037 90070, .storeN 90072 90078, .constN 90081 0]

/-- The list base `LB + off` (or `0` for a region without exits). -/
def regL : Stmt := .ifLtN 90079 90019 (.instr (.constN 90080 0)) (.instr (.addN 90080 90080 90022))

/-- Advance to the next region. -/
def regTail : Stmt := block [.addN 90078 90078 90002, .addN 90071 90071 90076,
  .addN 90070 90070 90019]

/-- One region. -/
def regBody : Stmt := .seq regHead (.seq regL (.seq slotLoop regTail))

/-- The region loop (`r16 = RB`, `r27` the base of the slots). -/
def regLoop : Stmt := .seq (block [.constN 90070 0, .copyN 90071 90016, .copyN 90078 90027,
  .constN 90076 5]) (.whileLtN 90070 90012 regBody)
theorem wrS_regLoop : wrS Binit regLoop = true := by_decide
set_option maxHeartbeats 1000000 in
theorem regHead_exec {W : ℕ} {d : Dm} (c : Config) (hw : WordsBounded W c)
    {RB LB r S dg w : ℕ} {ex : List ℕ} (hB : Bases c d) (h70 : c.nreg 90070 = r)
    (h71 : c.nreg 90071 = RB + 5 * r) (h78 : c.nreg 90078 = S) (_h22 : c.nreg 90022 = LB)
    (h19 : c.nreg 90019 = 1) (h20 : c.nreg 90020 = 3) (h21 : c.nreg 90021 = 2)
    (hrec : RegRec c.nmem RB LB r dg w ex) (hr : r < d.R) (hRB : RB + 5 * r + 5 ≤ d.b0)
    (hW : d.b0 + d.oEnd ≤ W) :
    ∃ c' k, Exec P W regHead c c' k ∧ k = 13 ∧ c'.nreg 90079 = dg ∧
      c'.nreg 90080 = c.nmem ztvi ∧ c'.nreg 90081 = 0 ∧
      c'.nmem = upd (upd (upd c.nmem ztjth dg) (d.b0 + d.oWt + r) w)
        (d.b0 + d.oExb + r) S ∧
      (∀ q, q ≠ 90072 → q ≠ 90074 → q ≠ 90075 → q ≠ 90079 → q ≠ 90080 → q ≠ 90081 →
        c'.nreg q = c.nreg q) := by
  zuf
  have hEx : d.oEx ≤ d.oEnd := by_omega
  have v1 : upd c.nmem ztjth dg _ = c.nmem ztvi :=
    Machine.upd_other _ _ _ by_omega
  have v2 : upd c.nmem ztjth dg (RB + 5 * r + 3 + 1) = w := by
    zumyl; exact hrec.wt
  unfold regHead
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp only [hB.bDeg, hB.bWt, hB.bExb, h70, h71, h78, h19,
    h20, h21, hrec.deg, v1, v2]; omega)
  refine ⟨rfl, ?_, ?_, rfl, ?_, fun q a1 a2 a3 a4 a5 a6 => by
    config_simp; simp [upd, a1, a2, a3, a4, a5, a6]⟩ <;> config_simp <;>
    simp only [hB.bDeg, hB.bWt, hB.bExb, h70, h71, h78, h19, h20, h21, hrec.deg, v1, v2]

/-- The region-loop invariant. -/
structure RegI (W R D RB : ℕ) (d : Dm) (rg : ℕ → RRec) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  r_le : c.nreg 90070 ≤ R
  ptr : c.nreg 90071 = RB + 5 * c.nreg 90070
  sl : c.nreg 90078 = d.b0 + d.oEx + D * c.nreg 90070
  c76 : c.nreg 90076 = 5
  regs : ∀ r, Binit r = false → c.nreg r = c₀.nreg r
  deg : ∀ x, x < c.nreg 90070 → c.nmem ztjti = (rg x).chords.length
  wt : ∀ x, x < c.nreg 90070 → c.nmem ztjto = (rg x).wt
  exb : ∀ x, x < c.nreg 90070 → c.nmem ztjtj = d.b0 + d.oEx + D * x
  ex : ∀ x t, x < c.nreg 90070 → t < D → c.nmem ztlmw =
    (rg x).chords.getD t 0
  mem : ∀ a, zteos → c.nmem a = c₀.nmem a
theorem regBody_exec {d : Dm} {rg : ℕ → RRec} {c₀ c : Config}
    (hI : RegI W R D RB d rg c₀ c) (hB : Bases c₀ d) (hR : d.R = R) (hD : d.D = D)
    (h02 : c₀.nreg 90002 = D) (h12 : c₀.nreg 90012 = R) (h22 : c₀.nreg 90022 = LB)
    (h19 : c₀.nreg 90019 = 1) (h20 : c₀.nreg 90020 = 3) (h21 : c₀.nreg 90021 = 2)
    (hrec : ∀ r, r < R → RegRec c₀.nmem RB LB r (rg r).chords.length (rg r).wt (rg r).chords)
    (hdeg : ∀ r, r < R → (rg r).chords.length ≤ D) (hRB : RB + 5 * R ≤ d.b0)
    (hL : ∀ r, r < R → 1 ≤ (rg r).chords.length →
      LB + c₀.nmem ztvi + (rg r).chords.length ≤ d.b0)
    (hW : d.b0 + d.oEnd ≤ W) (ht : c.nreg 90070 < R) :
    ∃ c' k, Exec P W regBody c c' k ∧ RegI W R D RB d rg c₀ c' ∧ k ≤ 9 * D + 22 ∧
      c'.nreg 90070 = c.nreg 90070 + 1 := by
  obtain ⟨hw, hle, hp, hsl, h76, hr, hdg, hwt, hexb, hex, hm⟩ := hI
  zuf
  rw [hR] at y1
  rw [hR, hD] at y2 y10
  generalize hrr : c.nreg 90070 = r at ht hle hp hsl hdg hwt hexb hex
  have hs := slot_le (D := D) ht ztbhw
  have hrc := hrec r ht
  have hdr := hdeg r ht
  have hLr := hL r ht
  -- the record reads are below `b0`
  have hrc' : RegRec c.nmem RB LB r (rg r).chords.length (rg r).wt (rg r).chords := by
    obtain ⟨a1, a2, a3, a4⟩ := hrc
    zuhvs
    refine ⟨by_grind, by_grind,
      fun t ht' => ?_, a4⟩
    grind
  zuhvs
  have hBc := hB.frame fun q a1 a2 => hr q ztbjn
  obtain ⟨c₁, k₁, e₁, hk₁, q79, q80, q81, qm, qr⟩ := regHead_exec (P := P) (d := d) c hw
    (S := d.b0 + d.oEx + D * r) hBc hrr hp hsl (by rw [hr _ by_decide, h22])
    (by rw [hr _ by_decide, h19]) (by zunyz) (by rw [hr _ by_decide, h21])
    hrc' by_omega by_omega hW
  zud
  -- the list base
  set L' := if (rg r).chords.length = 0 then 0 else LB + c.nmem ztvi with hL'
  have l19 : ztgas := by
    rw [qr _ by_decide by_decide by_decide by_decide by_decide by_decide,
      hr _ by_decide, h19]
  have l22 : c₁.nreg 90022 = LB := by
    rw [qr _ by_decide by_decide by_decide by_decide by_decide by_decide,
      hr _ by_decide, h22]
  obtain ⟨c₁', k₁', e₁', hk₁', v80, vr, vm⟩ : ∃ c₁' k₁', Exec P W regL c₁ c₁' k₁' ∧ k₁' ≤ 3 ∧
      c₁'.nreg 90080 = L' ∧ (∀ q, q ≠ 90080 → c₁'.nreg q = c₁.nreg q) ∧ c₁'.nmem = c₁.nmem := by
    unfold regL
    by_cases h0 : (rg r).chords.length = 0
    · exact ⟨_, _, .ifLtN_true by_omega ztcta,
        by omega, by simp [upd, hL', h0], fun q hq => by zuola, rfl⟩
    · have hLr' := by_omega
      exact ⟨_, _, .ifLtN_false by_omega
        (Exec.addN w₁ 90080 90080 90022 by_omega), by_omega,
        by simp [upd, hL', h0, q80, l22]; ring, fun q hq => by zuola, rfl⟩
  zumfv
  obtain ⟨c₂, k₂, e₂, hk₂, s₂, m₂, r₂⟩ := slotLoop_exec (P := P) (D := D)
    (S := d.b0 + d.oEx + D * r) (L := L')
    (deg := (rg r).chords.length) (ex := (rg r).chords) w₁'
    by_grind
    (by rw [vr _ by_decide, qr _ by_decide by_decide by_decide by_decide by_decide
      by_decide, hr _ by_decide, h02])
    by_grind
    by_grind v80 by_grind rfl hdr
    (fun t ht' => by
      zulio
      rw [vm, hL', ite_eq_right by_omega, qm, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega, e3,
        hm _ by_omega]
      exact hrc.lst t ht')
    (fun t ht' => by
      zulio
      left; rw [hL', ite_eq_right by_omega, e3]; omega)
    by_omega
    (by
      rw [hL']
      zujpn
      · omega
      omega)
  zue
  have g : ∀ q, q ≠ 90072 → q ≠ 90074 → q ≠ 90075 → q ≠ 90079 → q ≠ 90080 → q < 90081 ∨
      90084 < q → c₂.nreg q = c.nreg q := fun q a1 a2 a3 a4 a5 a6 => by
    rw [r₂ q by_omega by_omega by_omega by_omega, vr q a5, qr q a1 a2 a3 a4 a5 by_omega]
  have f78 := g 90078 by_decide by_decide by_decide by_decide by_decide by_decide
  have f71 := g 90071 by_decide by_decide by_decide by_decide by_decide by_decide
  have f70 := g 90070 by_decide by_decide by_decide by_decide by_decide by_decide
  have f02 := g 90002 by_decide by_decide by_decide by_decide by_decide by_decide
  have f76 := g 90076 by_decide by_decide by_decide by_decide by_decide by_decide
  have f19 := g 90019 by_decide by_decide by_decide by_decide by_decide by_decide
  rw [hsl] at f78; zvohk at f71; zvnhk at f70; rw [hr _ by_decide, h02] at f02
  rw [h76] at f76; rw [hr _ by_decide, h19] at f19
  have hD1 : D * r + D ≤ R * D := by
    omega
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ : ∃ c₃ k₃, Exec P W regTail c₂ c₃ k₃ ∧ k₃ = 3 ∧
      (c₃.nreg 90078 = d.b0 + d.oEx + D * ztgu ∧ c₃.nreg 90071 = RB + 5 * ztgu ∧
        c₃.nreg 90070 = r + 1 ∧ (∀ q, q ≠ 90078 → q ≠ 90071 → q ≠ 90070 → c₃.nreg q = c₂.nreg q) ∧
        c₃.nmem = c₂.nmem) := by
    unfold regTail
    exec_block
    · omega
    · config_simp; omega
    · config_simp; grind
    · refine ⟨rfl, ?_, ?_, ?_, fun q a1 a2 a3 => by zunsq, rfl⟩ <;> config_simp
      · grind
      · omega
      omega
  obtain ⟨q78, q71, q70, qr₃, qm₃⟩ := q
  refine ⟨c₃, _, .seq e₁ (.seq e₁' ztcr), ⟨e₃.wb_right, by_omega, by_omega,
    by grind, ?_, fun q hq => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_,
    fun x t hx htD => ?_, fun a ha => ?_⟩, by_omega, by rw [q70]⟩
  · rw [qr₃ _ by_decide by_decide by_decide, g _ by_decide by_decide by_decide
      by_decide by_decide by_decide, h76]
  · zvnuz at hq
    rw [qr₃ _ by_omega by_omega by_omega, g _ by_omega by_omega by_omega by_omega
      by_omega by_omega, hr q ztbjn]
  · zupx

    · subst hxr
      rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega]; simp
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega]
      exact hdg x by_omega
  · zupx

    · subst hxr
      zumyl; simp
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega]
      exact hwt x by_omega
  · zupx

    · subst hxr; simp
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega]
      grind
  · rw [q70] at hx
    rw [qm₃]
    by_cases hxr : x = r
    · subst hxr; exact s₂ t htD
    · have h1 : D * zthf ≤ D * r := Nat.mul_le_mul_left _ by_omega
      rw [Nat.mul_succ] at h1
      rw [m₂ _ by_omega, vm, qm, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega]
      exact hex x t by_omega htD
  · rw [qm₃, m₂ _ (by rcases ha with h | h <;> [left; right] <;> omega), vm, qm,
      Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      Machine.upd_other _ _ _ by_omega]
    grind
theorem regLoop_exec {d : Dm} {rg : ℕ → RRec} {c₀ : Config}
    (hw : WordsBounded W c₀) (hB : Bases c₀ d) (hR : d.R = R) (hD : d.D = D)
    (h02 : c₀.nreg 90002 = D) (h12 : c₀.nreg 90012 = R) (h16 : c₀.nreg 90016 = RB)
    (h22 : c₀.nreg 90022 = LB) (h27 : c₀.nreg 90027 = d.b0 + d.oEx)
    (h19 : c₀.nreg 90019 = 1) (h20 : c₀.nreg 90020 = 3) (h21 : c₀.nreg 90021 = 2)
    (hrec : ∀ r, r < R → RegRec c₀.nmem RB LB r (rg r).chords.length (rg r).wt (rg r).chords)
    (hdeg : ∀ r, r < R → (rg r).chords.length ≤ D) (hRB : RB + 5 * R ≤ d.b0)
    (hL : ∀ r, r < R → 1 ≤ (rg r).chords.length →
      LB + c₀.nmem ztvi + (rg r).chords.length ≤ d.b0)
    (hW : d.b0 + d.oEnd ≤ W) (hW5 : 5 ≤ W) :
    ∃ c' k, Exec P W regLoop c₀ c' k ∧ k ≤ ztjgg * R + 6 ∧
      (∀ x, x < R → c'.nmem ztjti = (rg x).chords.length ∧
        c'.nmem ztjto = (rg x).wt ∧
        c'.nmem ztjtj = d.b0 + d.oEx + D * x ∧
        ∀ t, t < D → c'.nmem ztlmw = (rg x).chords.getD t 0) ∧
      ztybj ∧
      FrameS Binit c₀ c' := by
  suffices hh : ∃ c' k, Exec P W regLoop c₀ c' k ∧ k ≤ ztjgg * R + 6 ∧
      (∀ x, x < R → c'.nmem _ = (rg x).chords.length ∧
        c'.nmem _ = (rg x).wt ∧
        c'.nmem _ = d.b0 + d.oEx + D * x ∧
        ∀ t, t < D → c'.nmem _ = (rg x).chords.getD t 0) ∧
      ztybj by
    zubgz
    exact ⟨c', k, e, h1, h2, h3, exec_frameS e wrS_regLoop⟩
  obtain ⟨c₁, k₁, e₁, hk₁, q, q0⟩ : ∃ c₁ k₁, Exec P W (block [.constN 90070 0, .copyN 90071 90016,
      .copyN 90078 90027, .constN 90076 5]) c₀ c₁ k₁ ∧ k₁ = 4 ∧ RegI W R D RB d rg c₀ c₁ ∧
      c₁.nreg 90070 = 0 := by
    exec_block
    · omega
    · omega
    · refine ⟨rfl, ⟨by assumption, ?_, ?_, ?_, ?_, fun r hr => ?_, fun x hx => ?_, fun x hx => ?_,
        fun x hx => ?_, fun x t hx _ => ?_, by_simp_all⟩, ?_⟩
      · simp
      · simp_all
      · simp_all
      · config_simp
      · zubzi
        config_simp; simp only [upd]; grind
      all_goals first | (simp [upd] at hx) | config_simp
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90070) (b := 90012)
    (body := regBody) (RegI W R D RB d rg c₀) (fun c => R - c.nreg 90070) (9 * D + 22)
    ztpf
    (fun c I ht => by
      have t : c.nreg 90070 < R := by rw [I.regs 90012 by_decide, h12] at ht; exact ht
      obtain ⟨c', k, e, I', hk, hi⟩ := regBody_exec (P := P) I hB hR hD h02 h12 h22 h19 h20 h21
        hrec hdeg hRB hL hW t
      grind) q
  have hK' : c'.nreg 90070 = R := by
    rw [I'.regs 90012 by_decide, h12] at hx; have := I'.r_le; omega
  refine ⟨c', _, .seq e₁ e, ?_, fun x hx => ⟨I'.deg x by_omega, I'.wt x by_omega,
    I'.exb x by_omega, fun t ht => I'.ex x t by_omega ht⟩, I'.mem⟩
  grind
theorem hostAt_agree' {m m' : ℕ → ℕ} {B E : ℕ} {H : Host} (h : HostAt m B H)
    (hE : B + 3 * H.length + 4 ≤ E) (hm : ∀ a, a < E → m' a = m a) : HostAt m' B H := by
  zuko

/-- A well-formed model descriptor survives every change of memory at or above its bound. -/
theorem desc_agree' {P : Polygon} {E : ℕ} {m m' : ℕ → ℕ} {D : ℕ} {M : Model}
    (hwf : ModelDescWF P E m D) (hM : ModelDescAt m D zta M)
    (hm : ∀ a, a < E → m' a = m a) : ModelDescAt m' D zta M ∧ ModelDescWF P E m' D := by
  zuglm

  zutl
  · zuqs

    have hH' : ztyye := by
      zvmxy; exact hostAt_agree' hH by_omega hm
    have hC' : ChainDescAt m' _ _ H C :=
      ⟨hH', hP, by_grind, by_grind,
        by grind, by_grind⟩
    refine ⟨Or.inl by_grind, hD, fun _ => ztmqm⟩
    have hHH := NFLoc.hostAt_unique hC''.1 hC'.1
    zular
    have hCC := NFLoc.chain_eq_of_desc hC'' hC'
    simp_all
  · refine ⟨Or.inr by_grind, hD,
      by simp_all⟩

/-! ## The stages of one position -/

/-- `cnt j := 0`, `r85 := j + 1` (`r70 = j`). -/
def posA : Stmt := block [.addN 90072 90038 90070, .constN 90073 0, .storeN 90072 90073,
  .addN 90085 90070 90019]

/-- `nxt j := j + 1 mod A`. -/
def posB : Stmt := .seq (.ifLtN 90085 90011 .skip ztoui)
  ztjoz

/-- `prv j := j - 1 mod A`. -/
def posC : Stmt := .seq (.ifLtN 90070 90019 (.instr (.subN 90085 90011 90019))
  (.instr (.subN 90085 90070 90019))) (block [.addN 90072 90040 90070, .storeN 90072 90085])

/-- The start of the arc at position `j`: `r110 = edge`, `r111 = height code`. -/
def posD : Stmt := block [.addN 90074 90017 90070, .loadN 90086 90074, .addN 90087 90086 90086,
  .addN 90087 90087 90087, .addN 90087 90087 90086, .addN 90074 90015 90087,
  .addN 90074 90074 90019, .loadN 90110 90074, .addN 90074 90074 90019, .loadN 90111 90074]

/-- `eg j := bB ch edge` (`r89 = 6`). -/
def posE : Stmt := .seq (.ifLtN 90023 90019 (.instr (.subN 90088 90110 90089))
  (.instr (.copyN 90088 90110))) (block [.addN 90072 90041 90070, .storeN 90072 90088])

/-- `pz j := r112`, `j := j + 1`. -/
def posF : Stmt := block [.addN 90072 90042 90070, .storeN 90072 90112, .addN 90070 90070 90019]

/-- One position. -/
def posBody : Stmt := .seq posA (.seq posB (.seq posC (.seq posD (.seq posE (.seq pzStmt posF)))))

/-- The position loop. -/
def posLoop : Stmt := .seq (block [.constN 90070 0, .constN 90089 6]) (.whileLtN 90070 90011 posBody)

/-- The registers of the position loop. -/
def Bpos (r : ℕ) : Bool := Binit r || Bpz r
theorem wrS_posLoop : wrS Bpos posLoop = true := by_decide
section stages
variable {P : Polygon} {W : ℕ}
theorem posA_exec (c : Config) (hw : WordsBounded W c) {j Cb : ℕ} (h70 : c.nreg 90070 = j)
    (h38 : c.nreg 90038 = Cb) (h19 : c.nreg 90019 = 1) (hb : Cb + j + 1 ≤ W) :
    ∃ c' k, Exec P W posA c c' k ∧ k = 4 ∧ c'.nmem = upd c.nmem ztfng 0 ∧
      c'.nreg 90085 = j + 1 ∧
      (∀ q, q ≠ 90072 → q ≠ 90073 → q ≠ 90085 → c'.nreg q = c.nreg q) := by
  unfold posA
  exec_block
  · omega
  · omega
  · config_simp; omega
  simp_all
theorem posB_exec (c : Config) (hw : WordsBounded W c) {j A Nb : ℕ} (h70 : c.nreg 90070 = j)
    (h85 : c.nreg 90085 = j + 1) (h11 : c.nreg 90011 = A) (h39 : c.nreg 90039 = Nb)
    (hb : Nb + j ≤ W) :
    ∃ c' k, Exec P W posB c c' k ∧ k ≤ 5 ∧
      c'.nmem = upd c.nmem zttbe ztcqa ∧
      ztbva := by
  unfold posB
  have fin : ∀ (c₁ : Config) (k₁ : ℕ), WordsBounded W c₁ → c₁.nreg 90085 =
      ztcqa → c₁.nreg 90070 = j → c₁.nreg 90039 = Nb →
      c₁.nmem = c.nmem → ztiur → k₁ ≤ 3 →
      ∃ c' k, Exec P W ztjoz c₁ c' k ∧
        k₁ + k ≤ 5 ∧ c'.nmem = upd c.nmem zttbe ztcqa ∧
        ztbva := by
    intro c₁ k₁ hw₁ v85 v70 v39 vm vr hk₁
    exec_block
    · omega
    simp_all
  by_cases hlt : j + 1 < A
  · obtain ⟨c', k, e, hk, hm, hr⟩ := fin c 1 hw by_grind h70 h39 rfl
      by_omega by_omega
    exact ⟨c', _, .seq (.ifLtN_true by_omega ztjd) e, by_omega, hm, hr⟩
  · have e₁ := Exec.constN (P := P) hw 90085 0 by_omega
    obtain ⟨c', k, e, hk, hm, hr⟩ := fin _ 3 e₁.wb_right (by simp [upd, ite_eq_right hlt])
      by_tauto by_tauto rfl ztcaa le_rfl
    exact ztgoh
theorem posC_exec (c : Config) (hw : WordsBounded W c) {j A Pb : ℕ} (h70 : c.nreg 90070 = j)
    (h11 : c.nreg 90011 = A) (h19 : c.nreg 90019 = 1) (h40 : c.nreg 90040 = Pb)
    (hb : Pb + j ≤ W) :
    ∃ c' k, Exec P W posC c c' k ∧ k ≤ 5 ∧
      c'.nmem = upd c.nmem ztnnv ztecl ∧
      ztbva := by
  unfold posC
  have fin : ∀ (c₁ : Config) (k₁ : ℕ), WordsBounded W c₁ → c₁.nreg 90085 =
      ztecl → c₁.nreg 90070 = j → c₁.nreg 90040 = Pb →
      c₁.nmem = c.nmem → ztiur → k₁ ≤ 3 →
      ∃ c' k, Exec P W (block [.addN 90072 90040 90070, .storeN 90072 90085]) c₁ c' k ∧
        k₁ + k ≤ 5 ∧ c'.nmem = upd c.nmem ztnnv ztecl ∧
        ztbva := by
    intro c₁ k₁ hw₁ v85 v70 v40 vm vr hk₁
    exec_block
    · omega
    simp_all
  by_cases hj : j < 1
  · have e₁ := Exec.subN (P := P) hw 90085 90011 90019
    obtain ⟨c', k, e, hk, hm, hr⟩ := fin _ 2 e₁.wb_right
      (by simp [upd, h11, h19, show ¬ 0 < j by omega]) by_tauto by_tauto
      rfl ztcaa by_omega
    exact ⟨c', _, .seq ztjdl e, by_omega, hm, hr⟩
  · have e₁ := Exec.subN (P := P) hw 90085 90070 90019
    obtain ⟨c', k, e, hk, hm, hr⟩ := fin _ 3 e₁.wb_right
      (by simp [upd, h70, h19, show 0 < j by omega]) by_tauto by_tauto
      rfl ztcaa le_rfl
    exact ztgoh
theorem posD_exec (c : Config) (hw : WordsBounded W c) {j SB AB : ℕ} (h70 : c.nreg 90070 = j)
    (h17 : c.nreg 90017 = SB) (h15 : c.nreg 90015 = AB) (h19 : c.nreg 90019 = 1)
    (hb1 : SB + j ≤ W) (hb2 : AB + 5 * c.nmem ztfoo + 2 ≤ W) :
    ∃ c' k, Exec P W posD c c' k ∧ k = 10 ∧
      c'.nreg 90110 = c.nmem (AB + 5 * c.nmem ztfoo + 1) ∧
      c'.nreg 90111 = c.nmem (AB + 5 * c.nmem ztfoo + 2) ∧ c'.nmem = c.nmem ∧
      (∀ q, q ≠ 90074 → q ≠ 90086 → q ≠ 90087 → q ≠ 90110 → q ≠ 90111 →
        c'.nreg q = c.nreg q) := by
  unfold posD
  exec_block
  all_goals try (config_simp; zunpc; omega)
  refine ⟨rfl, ?_, ?_, rfl, by_simp_all⟩ <;> config_simp <;>
    zunpc <;> ring_nf
theorem posE_exec (c : Config) (hw : WordsBounded W c) {j kind e Gb : ℕ}
    (h70 : c.nreg 90070 = j) (h23 : c.nreg 90023 = kind) (h19 : c.nreg 90019 = 1)
    (h89 : c.nreg 90089 = 6) (h110 : c.nreg 90110 = e) (h41 : c.nreg 90041 = Gb)
    (hb : Gb + j ≤ W) :
    ∃ c' k, Exec P W posE c c' k ∧ k ≤ 5 ∧
      c'.nmem = upd c.nmem ztsxt ztzvd ∧
      ztgsb := by
  unfold posE
  have fin : ∀ (c₁ : Config) (k₁ : ℕ), WordsBounded W c₁ → c₁.nreg 90088 =
      bB ztfhc e → c₁.nreg 90070 = j → c₁.nreg 90041 = Gb →
      c₁.nmem = c.nmem → (∀ q, q ≠ 90088 → c₁.nreg q = c.nreg q) → k₁ ≤ 3 →
      ∃ c' k, Exec P W (block [.addN 90072 90041 90070, .storeN 90072 90088]) c₁ c' k ∧
        k₁ + k ≤ 5 ∧ c'.nmem = upd c.nmem ztsxt ztzvd ∧
        ztgsb := by
    intro c₁ k₁ hw₁ v88 v70 v41 vm vr hk₁
    exec_block
    · omega
    simp_all
  by_cases hk : kind < 1
  · have e₁ := Exec.subN (P := P) hw 90088 90110 90089
    obtain ⟨c', k, e', hk', hm, hr⟩ := fin _ 2 e₁.wb_right
      (by simp [upd, h110, h89, bB, show kind = 0 by omega]) by_tauto
      by_tauto rfl ztcaa by_omega
    exact ⟨c', _, .seq ztjdl e', by_omega, hm, hr⟩
  · have e₁ := Exec.copyN (P := P) hw 90088 90110
    obtain ⟨c', k, e', hk', hm, hr⟩ := fin _ 3 e₁.wb_right
      (by simp [upd, h110, bB, show kind ≠ 0 by omega]) by_tauto
      by_tauto rfl ztcaa le_rfl
    exact ⟨c', _, .seq ztnac e', by_omega, hm, hr⟩
theorem posF_exec (c : Config) (hw : WordsBounded W c) {j Zb : ℕ} (h70 : c.nreg 90070 = j)
    (h42 : c.nreg 90042 = Zb) (h19 : c.nreg 90019 = 1) (hb : Zb + j + 1 ≤ W) :
    ∃ c' k, Exec P W posF c c' k ∧ k = 3 ∧ c'.nmem = upd c.nmem (Zb + j) (c.nreg 90112) ∧
      c'.nreg 90070 = j + 1 ∧ (∀ q, q ≠ 90072 → q ≠ 90070 → c'.nreg q = c.nreg q) := by
  unfold posF
  exec_block
  · omega
  · config_simp; omega
  simp_all
end stages

/-! ## The loop -/

/-- The position-loop invariant. -/
structure PosI (W A kind : ℕ) (d : Dm) (M : Model) (Q : Polygon) (edge hgt : ℕ → ℕ)
    (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  j_le : c.nreg 90070 ≤ A
  c89 : c.nreg 90089 = 6
  regs : ∀ r, Bpos r = false → c.nreg r = c₀.nreg r
  cnt : ∀ u, u < c.nreg 90070 → c.nmem ztqla = 0
  nxt : ∀ u, u < c.nreg 90070 → c.nmem ztqlg = if u + 1 < A then u + 1 else 0
  prv : ∀ u, u < c.nreg 90070 → c.nmem ztqlh = if 0 < u then u - 1 else A - 1
  eg : ∀ u, u < c.nreg 90070 → c.nmem ztqle = bB ztfhc ztmiz
  pz : ∀ u, u < c.nreg 90070 → c.nmem ztgic ≤ 1 ∧
    (c.nmem ztgic = 1 ↔ M.counted ztmiz ∧ M.param Q ztrci ≠ 0)
  mem : ∀ a, ztjnw → c.nmem a = c₀.nmem a

/-- The facts of the environment the position loop needs. -/
structure PosEnv (P : Polygon) (W A MD SB AB : ℕ) (d : Dm) (M : Model) (edge hgt : ℕ → ℕ)
    (c₀ : Config) : Prop where
  hG : GoodEnv P
  hW : hostWords P.n ≤ W
  hA : d.A = A
  bW : d.b0 + d.oEnd ≤ W
  bases : Bases c₀ d
  h11 : c₀.nreg 90011 = A
  h15 : c₀.nreg 90015 = AB
  h17 : c₀.nreg 90017 = SB
  h19 : c₀.nreg 90019 = 1
  h23 : c₀.nreg 90023 = c₀.nmem MD
  h50 : c₀.nreg 50000 = MD
  wf : ModelDescWF P d.b0 c₀.nmem MD
  desc : ModelDescAt c₀.nmem MD zta M
  arcs : ∀ u, u < A → SB + u < d.b0 ∧ AB + 5 * c₀.nmem ztnpf + 2 < d.b0 ∧
    c₀.nmem (AB + 5 * c₀.nmem ztnpf + 1) = edge u ∧
    c₀.nmem (AB + 5 * c₀.nmem ztnpf + 2) = hgt u
  edge_lt : ∀ u, u < A → edge u < M.W.n
  hgt_le : ∀ u, u < A → hgt u ≤ P.n
set_option maxHeartbeats 2000000 in
theorem posBody_exec {P : Polygon} {W A MD SB AB : ℕ} {d : Dm} {M : Model} {edge hgt : ℕ → ℕ}
    {c₀ c : Config} (hE : PosEnv P W A MD SB AB d M edge hgt c₀)
    (hI : PosI W A zthvy d M zta edge hgt c₀ c) (ht : c.nreg 90070 < A) :
    ∃ c' k, Exec P W posBody c c' k ∧ PosI W A zthvy d M zta edge hgt c₀ c' ∧
      k ≤ 6050 ∧ c'.nreg 90070 = c.nreg 90070 + 1 := by
  obtain ⟨hw, hle, h89, hr, hcnt, hnxt, hprv, heg, hpz, hm⟩ := hI
  zuf
  have hbW := hE.bW
  have hAd := hE.hA
  generalize hjj : c.nreg 90070 = j at ht hle hcnt hnxt hprv heg hpz
  have hB := hE.bases.frame fun q a1 a2 => hr q (by simp [Bpos, Binit, Bpz, NFLoc.Bdir]; omega)
  have c19 : zthoj := by rw [hr _ by_decide, hE.h19]
  have c11 : c.nreg 90011 = A := by rw [hr _ by_decide, hE.h11]
  have c15 : c.nreg 90015 = AB := by rw [hr _ by_decide, hE.h15]
  have c17 : c.nreg 90017 = SB := by rw [hr _ by_decide, hE.h17]
  have c23 : c.nreg 90023 = c₀.nmem MD := by rw [hr _ by_decide, hE.h23]
  have c50 : c.nreg 50000 = MD := by rw [hr _ by_decide, hE.h50]
  obtain ⟨a1, a2, a3, a4⟩ := hE.arcs j ht
  have mSB : c.nmem _ = c₀.nmem ztfoo := hm _ by_omega
  -- A: cnt
  obtain ⟨c₁, k₁, e₁, hk₁, m₁, v85, r₁⟩ := posA_exec (P := P) c hw hjj hB.bCnt c19 by_omega
  -- B: nxt
  obtain ⟨c₂, k₂, e₂, hk₂, m₂, r₂⟩ := posB_exec (P := P) (A := A) c₁ e₁.wb_right
    by_grind v85
    by_grind
    (by rw [r₁ _ by_decide by_decide by_decide, hB.bNxt]) by_omega
  -- C: prv
  have g₂ : ∀ q, q ≠ 90072 → q ≠ 90073 → q ≠ 90085 → c₂.nreg q = c.nreg q := by_grind
  obtain ⟨c₃, k₃, e₃, hk₃, m₃, r₃⟩ := posC_exec (P := P) (A := A) c₂ e₂.wb_right
    (by rw [g₂ _ by_decide by_decide by_decide, hjj])
    (by rw [g₂ _ by_decide by_decide by_decide, c11])
    (by rw [g₂ _ by_decide by_decide by_decide, c19])
    (by rw [g₂ _ by_decide by_decide by_decide, hB.bPrv]) by_omega
  have g₃ : ∀ q, q ≠ 90072 → q ≠ 90073 → q ≠ 90085 → c₃.nreg q = c.nreg q := fun q b1 b2 b3 => by
    rw [r₃ q b1 b3, g₂ q b1 b2 b3]
  -- D: the arc start
  have n₃ : c₃.nmem ztfoo = c₀.nmem ztfoo := by
    rw [m₃, m₂, m₁, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      Machine.upd_other _ _ _ by_omega, mSB]
  have n₃' : ztkoe := fun a ha => by
    rw [m₃, m₂, m₁, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      Machine.upd_other _ _ _ by_omega, hm _ by_omega]
  obtain ⟨c₄, k₄, e₄, hk₄, v110, v111, m₄, r₄⟩ := posD_exec (P := P) c₃ e₃.wb_right
    (by rw [g₃ _ by_decide by_decide by_decide, hjj])
    (by rw [g₃ _ by_decide by_decide by_decide, c17])
    (by rw [g₃ _ by_decide by_decide by_decide, c15])
    (by rw [g₃ _ by_decide by_decide by_decide, c19]) by_omega (by zuoeh; omega)
  rw [n₃, n₃' _ by_omega, a3] at v110
  rw [n₃, n₃' _ by_omega, a4] at v111
  have g₄ : ∀ q, q < 90110 → q ≠ 90072 → q ≠ 90073 → q ≠ 90085 → q ≠ 90074 → q ≠ 90086 →
      q ≠ 90087 → c₄.nreg q = c.nreg q := fun q b0 b1 b2 b3 b4 b5 b6 => by
    rw [r₄ q b4 b5 b6 by_omega by_omega, g₃ q b1 b2 b3]
  -- E: eg
  obtain ⟨c₅, k₅, e₅, hk₅, m₅, r₅⟩ := posE_exec (P := P) (kind := c₀.nmem MD) c₄ e₄.wb_right
    (by rw [g₄ _ by_decide by_decide by_decide by_decide by_decide by_decide
      by_decide, hjj])
    (by rw [g₄ _ by_decide by_decide by_decide by_decide by_decide by_decide
      by_decide, c23])
    (by rw [g₄ _ by_decide by_decide by_decide by_decide by_decide by_decide
      by_decide, c19])
    (by rw [g₄ _ by_decide by_decide by_decide by_decide by_decide by_decide
      by_decide, h89]) v110
    (by rw [g₄ _ by_decide by_decide by_decide by_decide by_decide by_decide
      by_decide, hB.bEg]) by_omega
  -- the pz bit
  have hmem5 : ∀ a, a < d.b0 → c₅.nmem a = c₀.nmem a := fun a ha => by
    rw [m₅, Machine.upd_other _ _ _ by_omega, m₄, n₃' a ha]
  obtain ⟨hdesc, hwf⟩ := desc_agree' hE.wf hE.desc by_omega
  obtain ⟨hDW, hCW⟩ := NFLoc.locChainWF_of hwf by_omega hE.hW
  have hW3 : ztmd := by have := hE.hW; unfold hostWords at this; omega
  have g₅ : ∀ q, q < 90110 → q ≠ 90072 → q ≠ 90073 → q ≠ 90085 → q ≠ 90074 → q ≠ 90086 →
      q ≠ 90087 → q ≠ 90088 → c₅.nreg q = c.nreg q := fun q b0 b1 b2 b3 b4 b5 b6 b7 => by
    rw [r₅ q b1 b7, g₄ q b0 b1 b2 b3 b4 b5 b6]
  obtain ⟨c₆, k₆, e₆, hk₆, F₆, p1, p2⟩ := pz_exec (P := P) (M := M) hE.hG hW3 c₅ e₅.wb_right
    (MD := MD) (e := edge j) (h := hgt j)
    (by rw [g₅ _ by_decide by_decide by_decide by_decide by_decide by_decide
      by_decide by_decide, c50]) hdesc
    (by rw [g₅ _ by_decide by_decide by_decide by_decide by_decide by_decide
      by_decide by_decide, c23, hmem5 _ (by have := hE.wf.1; omega)])
    (by rw [g₅ _ by_decide by_decide by_decide by_decide by_decide by_decide
      by_decide by_decide, c19])
    (by rw [r₅ _ by_decide by_decide, v110])
    (by rw [r₅ _ by_decide by_decide, v111]) (hE.edge_lt j ht) (hE.hgt_le j ht) hDW hCW
  zumav
  -- F: pz and the counter
  obtain ⟨c₇, k₇, e₇, hk₇, m₇, v70, r₇⟩ := posF_exec (P := P) c₆ e₆.wb_right (j := j)
    (by rw [g₆ _ by_decide, g₅ _ by_decide by_decide by_decide by_decide by_decide
      by_decide by_decide by_decide, hjj])
    (by rw [g₆ _ by_decide, g₅ _ by_decide by_decide by_decide by_decide by_decide
      by_decide by_decide by_decide, hB.bPz])
    (by rw [g₆ _ by_decide, g₅ _ by_decide by_decide by_decide by_decide by_decide
      by_decide by_decide by_decide, c19]) by_omega
  rw [F₆.2.2.1] at m₇
  have M7 : c₇.nmem = upd (upd (upd (upd (upd c.nmem ztgib 0) ztqlf
      ztcqa) (d.b0 + d.oPrv + j) (if 0 < j then j - 1 else A - 1))
      ztqld (bB zthgm (edge j))) (d.b0 + d.oPz + j)
      (c₆.nreg 90112) := by
    rw [m₇, m₅, m₄, m₃, m₂, m₁]
  refine ⟨c₇, _, .seq e₁ ztfc,
    ⟨e₇.wb_right, by_omega, ?_, fun q hq => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_,
      fun u hu => ?_, fun u hu => ?_, fun a ha => ?_⟩, by_omega, by zunru⟩
  · rw [r₇ _ by_decide by_decide, g₆ _ by_decide, g₅ _ by_decide by_decide by_decide
      by_decide by_decide by_decide by_decide by_decide, h89]
  · simp only [Bpos, Bool.or_eq_false_iff] at hq
    have hq1 := hq.1
    zvnuz at hq1
    rw [r₇ q by_omega by_omega, g₆ q hq.2, r₅ q by_omega by_omega]
    have hq2 := hq.2
    simp only [Bpz, NFLoc.Bdir, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hq2
    rw [r₄ q by_omega by_omega by_omega by_omega by_omega, g₃ q by_omega by_omega
      by_omega, hr q (by simp only [Bpos, Bool.or_eq_false_iff]; exact hq)]
  · zujp

    · zulti
      rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega]
      simp
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega]
      exact hcnt u by_omega
  · zujp

    · zulti
      rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega]
      simp
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega]
      exact hnxt u by_omega
  · zujp

    · zulti
      zucw
      simp
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega]
      exact hprv u by_omega
  · zujp

    · zulti
      zubc
      simp
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega]
      exact heg u by_omega
  · zujp

    · zulti
      zuvz
      exact ⟨p1, p2⟩
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega]
      exact hpz u by_omega
  · rw [M7, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      Machine.upd_other _ _ _ by_omega]
    exact hm a ha
theorem posLoop_exec {P : Polygon} {W A MD SB AB : ℕ} {d : Dm} {M : Model} {edge hgt : ℕ → ℕ}
    {c₀ : Config} (hw : WordsBounded W c₀) (hE : PosEnv P W A MD SB AB d M edge hgt c₀)
    (hW6 : 6 ≤ W) :
    ∃ c' k, Exec P W posLoop c₀ c' k ∧ k ≤ 6052 * A + 4 ∧
      (∀ u, u < A → c'.nmem ztqla = 0 ∧
        c'.nmem ztqlg = (if u + 1 < A then u + 1 else 0) ∧
        c'.nmem ztqlh = (if 0 < u then u - 1 else A - 1) ∧
        c'.nmem ztqle = bB zthgm ztmiz ∧
        c'.nmem ztgic ≤ 1 ∧
        (c'.nmem ztgic = 1 ↔
          M.counted ztmiz ∧ M.param zta ztrci ≠ 0)) ∧
      (∀ a, ztjnw → c'.nmem a = c₀.nmem a) ∧
      FrameS Bpos c₀ c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, q, q0⟩ : ∃ c₁ k₁, Exec P W (block [.constN 90070 0,
      .constN 90089 6]) c₀ c₁ k₁ ∧ k₁ = 2 ∧
      PosI W A zthvy d M zta edge hgt c₀ c₁ ∧ c₁.nreg 90070 = 0 := by
    exec_block
    · omega
    · omega
    · refine ⟨rfl, ⟨by assumption, ?_, ?_, fun r hr => ?_, fun u hu => ?_, fun u hu => ?_,
        fun u hu => ?_, fun u hu => ?_, fun u hu => ?_, by_simp_all⟩, ?_⟩
      · simp
      · config_simp
      · simp only [Bpos, Binit, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
        config_simp; simp only [upd]; grind
      all_goals first | (simp [upd] at hu) | config_simp
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90070) (b := 90011)
    (body := posBody) (PosI W A zthvy d M zta edge hgt c₀)
    (fun c => A - c.nreg 90070) 6050 ztpf
    (fun c I ht => by
      have t : c.nreg 90070 < A := by rw [I.regs 90011 by_decide, hE.h11] at ht; exact ht
      obtain ⟨c', k, e, I', hk, hi⟩ := posBody_exec (P := P) hE I t
      grind) q
  have hK' : c'.nreg 90070 = A := by
    rw [I'.regs 90011 by_decide, hE.h11] at hx; have := I'.j_le; omega
  refine ⟨c', _, .seq e₁ e, ?_, fun u hu => ⟨I'.cnt u by_omega, I'.nxt u by_omega,
    I'.prv u by_omega, I'.eg u by_omega, (I'.pz u by_omega).1, (I'.pz u by_omega).2⟩,
    I'.mem, exec_frameS (.seq e₁ e) wrS_posLoop⟩
  omega
end
end Gran
namespace MergeAsm
@[expose] public section
open Set

/-! ## Weights and sizes -/
theorem arcWt_le_size (M : Model) (a b : ℝ) : M.arcWt a b ≤ M.size := by
  zultu
  refine Set.ncard_le_ncard ?_ ((Set.finite_lt_nat M.W.n).subset fun _ hp => hp.1)
  simp_all
theorem weight_le_size (M : Model) (F : Set ztf) (U : Set Point) :
    M.weight F U ≤ M.size := by
  unfold Model.weight
  refine csSup_le' ?_
  rintro _ ⟨ab, -, rfl⟩
  exact arcWt_le_size M _ _

/-- A `γ`-semigranular family is `min γ size`-semigranular. -/
theorem semigranular_min {M : Model} {F : Set ztf} {γ : ℕ} (h : M.Semigranular F γ) :
    M.Semigranular F (min γ M.size) :=
  fun U hU => le_min (h U hU) (weight_le_size M F U)
theorem size_le_n (M : Model) : M.size ≤ M.W.n := by
  zujpy
  calc {p : ℕ | p < M.W.n ∧ M.counted p}.ncard ≤ (Set.Iio M.W.n).ncard :=
        Set.ncard_le_ncard ztqoa ztvde
    _ = M.W.n := by zunzd
variable {M : Model} (C : Chain) {Q : Polygon} {N : NF} (a b : ℕ)
theorem chainModel_n : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _

/-- The size of a chain model: its `2 m` tour edges. -/
theorem chainModel_size : (chainModel C).size = 2 * C.m := by
  zujpy
  have e : {p : ℕ | p < (chainModel C).W.n ∧ (chainModel C).counted p} =
      ((Finset.Ico 6 ztcc : Finset ℕ) : Set ℕ) := by
    zufj
    simp only [mem_ofPred_eq, Finset.coe_Ico, Set.mem_Ico, chainModel_n]
    show p < 2 * C.m + 7 ∧ ztbxy ↔ _
    omega
  rw [e, Set.ncard_coe_finset, Nat.card_Ico]
  omega

/-- A `(γ + 1)`-semigranular family of a chain model is `(min γ (2 m) + 1)`-semigranular. -/
theorem semigranular_min_chain' {C : Chain} {F : Set ztf} {γ : ℕ}
    (h : (chainModel C).Semigranular F ztgj) :
    (chainModel C).Semigranular F (min γ ztbb + 1) := by
  refine Model.Semigranular.mono _ (semigranular_min h) ?_
  rw [chainModel_size]
  omega

/-! ## Degrees of normal forms -/

/-- **The degree bound from the chord lists** of the regions. -/
theorem degLe_of_lens (hN : IsNF M Q N) {d : ℕ}
    (h : ∀ r, r < N.nRegions → (N.region r).chords.length ≤ d) : M.DegLe ztdu d := by
  zucdl
  zucne
  zufko
  rw [Gran.deg_region hN hRC hRO hr]
  simp_all

/-- **The chord lists from the degree bound.** -/
theorem lens_of_degLe (hN : IsNF M Q N) {d : ℕ}
    (h : M.DegLe ztdu d) : ∀ r, r < N.nRegions → (N.region r).chords.length ≤ d := by
  zucdl
  zuz
  zuhnt
  exact h _ ztdhm

/-! ## Lemma 2.3 -/

/-- **Chord count of a canonical normal form** of a chain model (Lemma 2.3, with its constant
`c`). -/
theorem nChords_le_canonical {c : ℕ → ℕ} (hc : ∀ (M : Model) (Q : Polygon) (F : Set ztf)
      (γ D : ℕ), GoodModel M → M.ChordFamily Q F → M.DegLe F D → M.Granular F γ →
        F.ncard * ztgj ≤ c D * ztcep)
    {C : Chain} (hP : C.P.Simple) {Q : Polygon} {N : NF} {γ D : ℕ}
    (hN : IsCanonicalNF ztc Q N γ D) : N.nChords ≤ c D * ztgca := by
  zufjw
  have h := hc _ Q _ γ D ztxgi hnf.1 hdeg hgr
  zujgo
  have hs := size_le_n ztc
  rw [chainModel_n] at hs
  calc N.nChords ≤ N.nChords * ztgj := Nat.le_mul_of_pos_right _ by_omega
    _ ≤ c D * zteiv := h
    _ ≤ c D * ztgca := Nat.mul_le_mul_left _ by_omega

/-! ## `Nat.clog` arithmetic -/
theorem clog_mono {a b : ℕ} (h : a ≤ b) : Nat.clog 2 a ≤ Nat.clog 2 b :=
  Nat.clog_mono_right 2 h

/-- `⌈log₂ (a b)⌉ ≤ ⌈log₂ a⌉ + ⌈log₂ b⌉`. -/
theorem clog_mul_le : Nat.clog 2 zthdh ≤ Nat.clog 2 a + Nat.clog 2 b := by
  zudwq
  zujlg
  zulxf
theorem clog_le_self (a : ℕ) : Nat.clog 2 a ≤ a := by
  zudwq
  exact (Nat.lt_two_pow_self).le

/-- `⌈log₂ (a b)⌉ ≤ a + ⌈log₂ b⌉`. -/
theorem clog_mul_le' : Nat.clog 2 zthdh ≤ a + Nat.clog 2 b :=
  (clog_mul_le a b).trans (by have := clog_le_self a; omega)
theorem clog_S {S β m : ℕ} (h : S ≤ β * ztbl) : Nat.clog 2 S ≤ β + Nat.clog 2 ztbl :=
  (clog_mono h).trans (clog_mul_le' β ztbl)
theorem clog_8 (x : ℕ) : Nat.clog 2 (8 * x) ≤ 3 + Nat.clog 2 x := by
  refine (clog_mul_le 8 x).trans ?_
  rfl

/-- The fusion stage. -/
theorem fuse_le {κ S β m F₀ F G H : ℕ} (hS : S ≤ β * ztbl) (hF : F₀ ≤ F) (hF1 : 1 ≤ F)
    (hG1 : 1 ≤ G) :
    κ * S * ztnlb ≤
      κ * zthlo * S * ztwvz := by
  have hc := clog_S hS
  zudvq
  have hY1 : F ≤ F * G * ztbhm := by
    calc F = F * 1 * 1 := by_ring
      _ ≤ F * G * ztbhm := by gcongr; omega
  have hY2 : ztylf := by
    calc L + 1 = 1 * 1 * ztgt := by_ring
      _ ≤ F * G * ztbhm := by gcongr; omega
  have hY3 : 1 ≤ F * G * ztbhm := by_omega
  zuioc
  have : F₀ + Nat.clog 2 S + 1 ≤ zthlo * Y := by_nlinarith
  calc κ * S * ztnlb ≤ κ * S * (zthlo * Y) := Nat.mul_le_mul_left _ this
    _ = κ * zthlo * S * Y := by_ring

/-- The restoration stage. -/
theorem restore_le {κ K S β m γ F₀ G₀ H₀ F G H : ℕ} (hS : S ≤ β * ztbl) (hK : K + 1 ≤ 8 * S)
    (hγ : γ ≤ 8 * ztbl) (hF : F₀ ≤ F) (hG : G₀ ≤ G) (hH : H₀ ≤ H) :
    κ * ztbr * F₀ * G₀ * ztxvd ≤
      8 * zteww * κ * S * ztwvz := by
  zudvq
  have h1 : Nat.clog 2 γ ≤ 3 + L := (clog_mono hγ).trans (clog_8 _)
  have h2 : Nat.clog 2 ztbr ≤ 3 + β + L :=
    (clog_mono hK).trans ((clog_8 S).trans (by have := clog_S hS; omega))
  have hp : H₀ + Nat.clog 2 γ + Nat.clog 2 ztbr + 1 ≤ zteww * ztbhm := by_nlinarith
  calc κ * ztbr * F₀ * G₀ * ztxvd
      ≤ κ * ztnhs * F * G * (zteww * ztbhm) := by gcongr
    _ = 8 * zteww * κ * S * (F * G * ztbhm) := by_ring

/-- The granularity stage. -/
theorem gran_le {κ K c S β m F G H : ℕ} (hS : S ≤ β * ztbl) (hK : K ≤ 8 * c * S)
    (hF1 : 1 ≤ F) (hG1 : 1 ≤ G) (hS1 : 1 ≤ S) :
    κ * ztwko ≤
      κ * ztbam * S * ztwvz := by
  zudvq
  have hl : Nat.clog 2 K ≤ 8 * c * β + L := by
    have : K ≤ ztpuz * ztbl := by
      calc K ≤ 8 * c * S := hK
        _ ≤ 8 * c * (β * ztbl) := Nat.mul_le_mul_left _ hS
        _ = ztpuz * ztbl := by_ring
    exact (clog_mono this).trans (clog_mul_le' _ _)
  have hY : ztylf := by
    calc L + 1 = 1 * 1 * ztgt := by_ring
      _ ≤ F * G * ztbhm := by gcongr; omega
  zuioc
  have e1 : K * ztho ≤ 8 * c * S * ztbaat := by
    calc K * ztho ≤ 8 * c * S * (8 * c * β + L + 1) := by gcongr
      _ ≤ 8 * c * S * ztbaat := by
        grind
  have e2 : K * ztho + 1 ≤ ztbam * S * Y := by
    have : ztbam * S * ztgt ≤ ztbam * S * Y :=
      Nat.mul_le_mul_left _ hY
    nlinarith
  calc κ * ztwko ≤ κ * (ztbam * S * Y) :=
        Nat.mul_le_mul_left _ e2
    _ = κ * ztbam * S * Y := by_ring

/-- `S ≤ β (m + 1)` from Lemma 2.3's bounds on `K₁`, `K₂`. -/
theorem S_le {K₁ K₂ a m₁ m₂ : ℕ} (h₁ : K₁ ≤ a * (2 * m₁ + 8)) (h₂ : K₂ ≤ a * (2 * m₂ + 8)) :
    K₁ + K₂ + 1 ≤ (16 * a + 1) * (m₁ + m₂ + 1) := by
  nlinarith
end
end MergeAsm
namespace FuseAsm
open MergeAsm
@[expose] public section
theorem piece_le (κ T S Fg : ℕ) (hT : T ≤ 8 * S) :
    κ * T * ztnkz ≤ 32 * κ * ztypt := by
  have hc : Nat.clog 2 T ≤ 3 + Nat.clog 2 S := (clog_mono hT).trans (clog_8 S)
  have h4 : Fg + Nat.clog 2 T + 1 ≤ 4 * ztdfo := by_omega
  calc κ * T * ztnkz ≤ κ * ztnhs * (4 * ztdfo) :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl hT) h4
    _ = 32 * κ * ztypt := by_ring
theorem nlog_le (K S Fg : ℕ) (hK : K ≤ 8 * S) :
    K * ztho ≤ 32 * ztypt := by
  have := piece_le 1 K S Fg hK
  grind

/-- The cost bound of the fusion. -/
def fuseκ (κs : ℕ → ℕ) (κB : ℕ) (D : ℕ) : ℕ := 400000 * (κs D + κB + 1)

/-- **The total cost of the fusion.** -/
theorem fuse_total {κs : ℕ → ℕ} {κB D K₁ K₂ L₀ L₁ Kc Kd Fg k₁ k₂ k₃ k₄ k₅ k₆ k₇ : ℕ}
    (hL₀ : L₀ ≤ 2 * K₁ + 5) (hL₁ : L₁ ≤ 2 * K₂ + 3) (hKc : Kc ≤ L₀ + L₁) (hKd : Kd ≤ Kc)
    (h₁ : k₁ ≤ 22 * K₁ + 200000)
    (h₂ : k₂ ≤ 13 + κs D * zthba * (Fg + Nat.clog 2 zthba + 1))
    (h₃ : k₃ ≤ 22 * K₂ + 120000)
    (h₄ : k₄ ≤ 13 + κs D * zthbb * (Fg + Nat.clog 2 zthbb + 1))
    (h₅ : k₅ ≤ 24 * (L₀ + L₁) + 20)
    (h₆ : k₆ ≤ 2 + (SortR.sortCost 40 Kc + 70 * Kc + 30))
    (h₇ : k₇ ≤ 40 + κB * ztjjh) :
    k₁ + ztxkw ≤
      fuseκ κs κB D * ztctf * (Fg + Nat.clog 2 ztctf + 1) := by
  obtain ⟨S, hS⟩ : ∃ S, S = K₁ + K₂ + 1 := zths
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Fg + Nat.clog 2 S + 1 := zths
  rw [← hS, ← hY]
  have p₂ := piece_le ztmpp zthba S Fg by_omega
  have p₄ := piece_le ztmpp zthbb S Fg by_omega
  have p₆ := nlog_le Kc S Fg by_omega
  have p₇ := nlog_le Kd S Fg by_omega
  rw [← hY] at p₂ p₄ p₆ p₇
  obtain ⟨SY, hSY⟩ : ∃ x, x = S * Y := zths
  rw [← hSY] at p₂ p₄ p₆ p₇
  have hS1 : S ≤ SY := by_simp_all
  have hS0 : 1 ≤ S := by_omega
  unfold SortR.sortCost at h₆
  have e7 : κB * ztjjh ≤ κB * ztjfr :=
    Nat.mul_le_mul le_rfl by_omega
  have e7' : κB * ztjfr ≤ 33 * (κB * SY) := by_nlinarith
  have e6 : (40 + 30) * (Kc * (Nat.clog 2 Kc + 1) + 1) ≤ 70 * ztjfr :=
    Nat.mul_le_mul le_rfl by_omega
  obtain ⟨A, hA⟩ : ∃ x, x = κs D * SY := zths
  obtain ⟨B, hB⟩ : ∃ x, x = κB * SY := zths
  have eA : 32 * κs D * SY = 32 * A := by_grind
  rw [eA] at p₂ p₄
  rw [← hB] at e7'
  have goal : fuseκ κs κB D * S * Y = 400000 * A + 400000 * B + 400000 * SY := by
    unfold fuseκ; grind
  omega
theorem sweepc_mono (κ A Fg : ℕ) {L L' : ℕ} (h : L ≤ L') :
    κ * ztpvo * (Fg + Nat.clog 2 ztpvo + 1) ≤
      κ * ztpvp * (Fg + Nat.clog 2 ztpvp + 1) :=
  Nat.mul_le_mul (Nat.mul_le_mul le_rfl by_omega)
    (by have := clog_mono (show A + L + 1 ≤ A + L' + 1 by omega); omega)
variable (κ : ℕ) {K K' : ℕ}
theorem nlogc_mono (h : K ≤ K') :
    κ * ztwko ≤ κ * (K' * ztqao + 1) :=
  Nat.mul_le_mul le_rfl (by
    have := clog_mono h
    have := Nat.mul_le_mul h (show Nat.clog 2 K + 1 ≤ Nat.clog 2 K' + 1 by omega)
    omega)
theorem sortc_mono (h : K ≤ K') :
    SortR.sortCost κ K ≤ SortR.sortCost κ K' := by
  unfold SortR.sortCost; exact nlogc_mono _ h
end
end FuseAsm
namespace BuildOrder
@[expose] public section
open Set List
open Chazelle.Chain (SideAttach sideInArc sidePt sideKey_inj)
open BuildSort (Ev EvLe cycDist)

/-- The chord of index `i` of a triple list. -/
noncomputable def chordSet (M : Model) (Q : Polygon) (L : List zte) (i : ℕ) :
    Set Point :=
  (recOf ztwrk).toSet M Q

/-- The two attachment events of chord `i`. -/
noncomputable def evPair (M : Model) (Q : Polygon) (L : List zte) (i : ℕ) : List Ev :=
  [(i, M.key Q (recOf ztwrk).lpos, M.key Q (recOf ztwrk).rpos),
   (i, M.key Q (recOf ztwrk).rpos, M.key Q (recOf ztwrk).lpos)]

/-- **The attachment events of a chord list.** -/
noncomputable def events (M : Model) (Q : Polygon) (L : List zte) : List Ev :=
  (List.range L.length).flatMap ztrph
theorem events_map_fst (M : Model) (Q : Polygon) (L : List zte) :
    (events M Q L).map Prod.fst = (List.range L.length).flatMap (fun i => [i, i]) := by
  unfold events evPair
  zumlk
  rfl
theorem count_doubles (n i : ℕ) :
    ((List.range n).flatMap (fun j => [j, j])).count i = if i < n then 2 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.count_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_cons,
      List.count_nil, beq_iff_eq]
    by_cases h : i = n
    · simp_all
    · grind
theorem count_events (M : Model) (Q : Polygon) (L : List zte) {i : ℕ}
    (hi : i < L.length) : ((events M Q L).map Prod.fst).count i = 2 := by
  rw [events_map_fst, count_doubles, ite_eq_left hi]
variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {i : ℕ}
theorem mem_events {e : Ev} :
    e ∈ events M Q L ↔ ∃ i < L.length, e ∈ evPair M Q L i := by
  unfold events
  simp

/-- **The two attachments of a record** of an admissible attached chord are at distinct points:
the left endpoint at `lpos`, the right one at `rpos`. -/
theorem endpoints (hM : WalkAx M) {Q : Polygon} {r : CRec}
    (hadm : r.toSet M Q ∈ M.Adm) (hr : r.Attached M Q) :
    (M.pos Q r.lpos).1 < (M.pos Q r.rpos).1 := by
  zubjj

  have hpA : sidePt M.W r.lp _ = M.pos Q r.lpos := rfl
  zuduk

  zuks

  have hsub : ztiem := by
    zugti

  zubfz

/-- A triple of the list, by index. -/
theorem getD_mem (hi : i < L.length) : L.getD i ztt ∈ L := by
  simp_all

/-- Distinct indices of a valid chord list give distinct chords. -/
theorem chordSet_inj (hL : ChordTriplesOK M Q L)
    {i j : ℕ} (hi : i < L.length) (hj : j < L.length) (h : chordSet M Q L i = chordSet M Q L j) :
    i = j := by
  have hnd := hL.2.1
  have hi' : i < (L.map fun x => (recOf x).toSet M Q).length := by_simp_all
  have hj' : j < (L.map fun x => (recOf x).toSet M Q).length := by_simp_all
  refine (hnd.getElem_inj_iff (hi := hi') (hj := hj')).1 ?_
  zukpm
  unfold chordSet at h
  simp_all

/-- The chords of a valid chord list are in its family. -/
theorem chordSet_mem
    (hi : i < L.length) :
    chordSet M Q L i ∈ {c | ∃ x ∈ L, c = (recOf x).toSet M Q} :=
  ⟨_, getD_mem hi, rfl⟩

/-- **The attachment data of an event**: its chord is attached at the positions of its two keys,
at distinct points. -/
theorem event_data (hM : WalkAx M) {Q : Polygon} {L : List zte}
    (hL : ChordTriplesOK M Q L) {e : Ev} (he : e ∈ events M Q L) :
    ∃ i < L.length, e.1 = i ∧ ∃ (pa pb : ℕ) (ta tb : ℝ),
      SideAttach M.W ztrz pa ta ∧ SideAttach M.W ztrz pb tb ∧
      sidePt M.W pa ta ≠ sidePt M.W pb tb ∧ e.2.1 = pa + ta ∧ e.2.2 = pb + tb := by
  zufyj
  set r := recOf ztwrk with hr
  zukbb
  have hadm := hL.1.2.1 ztdcw
  have hlt := endpoints hM hadm hatt
  have hne : sidePt M.W r.lp ztfog ≠ sidePt M.W r.rp zthbi := by
    zuq
    have : M.pos Q r.lpos = M.pos Q r.rpos := h
    simp_all
  unfold evPair at he
  rw [← hr] at he
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨i, hi, rfl, r.lp, r.rp, _, _, hatt.1, hatt.2, hne, rfl, rfl⟩
  · zvojs at he
    zulsz
    exact ⟨i, hi, rfl, r.rp, r.lp, _, _, hatt.2, hatt.1, Ne.symm hne, rfl, rfl⟩

/-- **The sorted attachment events of a valid chord list form a parenthesis word**, for every
ordering sorted by `EvLe` (so for the output of the RAM sort with the corresponding
comparator). -/
theorem parenthesis_of_sorted (hM : WalkAx M) {Q : Polygon}
    {L : List zte} (hL : ChordTriplesOK M Q L) {S : List Ev}
    (hperm : S.Perm ztrpi) (hsorted : S.Pairwise ztmaw) :
    BuildStack.NoCross ztbuq ∧ BuildStack.Twice ztbuq := by
  have hmem : ∀ e, e ∈ S ↔ e ∈ events M Q L := by_grind
  zuixx
  have hAdm := hL.1.2.1
  have keyb : ∀ {pa : ℕ} {ta : ℝ} {c : Set Point}, SideAttach M.W c pa ta →
      0 ≤ (pa : ℝ) + ta ∧ (pa : ℝ) + ta < M.W.n := by
    zumk

  refine BuildSort.noCross_of_sorted ?_ ?_ ?_ ?_ ?_ hsorted
  · zubre
    obtain ⟨i, hi, -, pa, pb, ta, tb, hA, hB, hAB, h1, h2⟩ := event_data hM hL ztfee
    zubuw
    exact ⟨by_grind, by_grind, by_grind, by_grind,
      WalkAx.key_ne_of_pt_ne hA hB hAB⟩
  · zubre
    rw [hmem] at he ⊢
    zufyj
    refine mem_events.2 ztbfn
    unfold evPair at he ⊢
    grind
  · zubre
    obtain ⟨i, hi, hei, -⟩ := event_data hM hL ztfee
    rw [(hperm.map Prod.fst).count_eq, hei]
    exact count_events M Q L hi
  · zuyz

    obtain ⟨j, hj, hfj, pc, pd, tc, td, hC, hD, -, h3, h4⟩ := event_data hM hL ztosv
    rw [h1, h2, h3, h4]
    have hne := fun h =>
      hef (by zuolm; exact chordSet_inj hL hi hj h)
    exact hM.no_cross hAdm hfin ztdcw ztdnb hne hA hB hAB hC hD
  · zuyz

    obtain ⟨j, hj, hfj, pc, pd, tc, td, hC, hD, hCD, h3, h4⟩ := event_data hM hL ztosv
    have k1 : (pa : ℝ) + ta = pc + tc := by_grind
    have k2 : (pb : ℝ) + tb = pd + td := by_grind
    obtain ⟨rfl, rfl⟩ := sideKey_inj hA.2.1 hA.2.2.1 hC.2.1 hC.2.2.1 k1
    obtain ⟨rfl, rfl⟩ := sideKey_inj hB.2.1 hB.2.2.1 hD.2.1 hD.2.2.1 k2
    have e1 := (hM.attach_seg (hAdm ztdcw) hA hB hAB).1
    have e2 := (hM.attach_seg (hAdm ztdnb) hC hD hCD).1
    zuolm
    exact chordSet_inj hL hi hj ztqmh

/-! ## The tie rule is the direction rule -/

/-- **Tie at a vertex whose leaving edge goes down**: the east chord's other end is cyclically
closer to the vertex key than the west chord's, so under `EvLe` the west chord's event (the
larger cyclic distance) comes first. -/
theorem tie_rule_down (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {ce cw : Set Point} (hce : ce ∈ F) (hcw : cw ∈ F) {p : ℕ} {t : ℝ}
    (hAe : SideAttach M.W ce p t) (hAw : SideAttach M.W cw p t)
    (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1) (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1)
    (hdown : (M.wb p).2 < (M.wa p).2) {pe pw : ℕ} {te tw : ℝ}
    (hBe : SideAttach M.W ce pe te) (hBe' : sidePt M.W pe te ≠ sidePt M.W p t)
    (hBw : SideAttach M.W cw pw tw) (hBw' : sidePt M.W pw tw ≠ sidePt M.W p t) :
    t = 0 ∧ cycDist M.W.n p zteuq < cycDist M.W.n p ztbjs := by
  obtain ⟨rfl, U, V, R, -, -, -, -, -, -, -, -, -, hord⟩ :=
    hM.tie_down hF hfin hce hcw hAe hAw hE hW hdown
  zubwp

  have keyb : ∀ {pa : ℕ} {ta : ℝ} {c : Set Point}, SideAttach M.W c pa ta →
      0 ≤ (pa : ℝ) + ta ∧ (pa : ℝ) + ta < M.W.n := by
    zumk

  zufva

  refine ⟨rfl, (BuildSort.sideInArc_iff_cycDist hk ztvxr ztvxs ?_ ?_).1 hin⟩
  · have := WalkAx.key_ne_of_pt_ne hAe hBe by_grind
    grind
  · have := WalkAx.key_ne_of_pt_ne hAw hBw by_grind
    grind

/-- **Tie at a vertex whose leaving edge goes up**: the west chord's other end is cyclically
closer, so under `EvLe` the east chord's event comes first. -/
theorem tie_rule_up (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {ce cw : Set Point} (hce : ce ∈ F) (hcw : cw ∈ F) {p : ℕ} {t : ℝ}
    (hAe : SideAttach M.W ce p t) (hAw : SideAttach M.W cw p t)
    (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1) (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1)
    (hup : (M.wa p).2 < (M.wb p).2) {pe pw : ℕ} {te tw : ℝ}
    (hBe : SideAttach M.W ce pe te) (hBe' : sidePt M.W pe te ≠ sidePt M.W p t)
    (hBw : SideAttach M.W cw pw tw) (hBw' : sidePt M.W pw tw ≠ sidePt M.W p t) :
    t = 0 ∧ cycDist M.W.n p ztbjs < cycDist M.W.n p zteuq := by
  obtain ⟨rfl, U, V, R, -, -, -, -, -, -, -, -, -, hord⟩ :=
    hM.tie_up hF hfin hce hcw hAe hAw hE hW hup
  zubwp

  have keyb : ∀ {pa : ℕ} {ta : ℝ} {c : Set Point}, SideAttach M.W c pa ta →
      0 ≤ (pa : ℝ) + ta ∧ (pa : ℝ) + ta < M.W.n := by
    zumk

  zufva

  refine ⟨rfl, (BuildSort.sideInArc_iff_cycDist hk ztvxs ztvxr ?_ ?_).1 hin⟩
  · have := WalkAx.key_ne_of_pt_ne hAw hBw by_grind
    grind
  · have := WalkAx.key_ne_of_pt_ne hAe hBe by_grind
    grind
end
end BuildOrder
namespace Restore
@[expose] public section
open Set
open Chazelle.Chain (sidePt)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp point_ext)
variable {M : Model}

/-- **The exit point is not on a walk edge through the origin.** -/
theorem no_common_edge (hM : WalkAx M) {z : Point} {σ T : ℝ} (_hσ : σ = 1 ∨ σ = -1) (hT : 0 < T)
    (hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ M.D) {p : ℕ} (hp : p < M.W.n) {t₁ t₂ : ℝ}
    (ht₁ : 0 ≤ t₁) (ht₁1 : t₁ ≤ 1) (ht₂ : 0 ≤ t₂) (ht₂1 : t₂ ≤ 1)
    (hz : sidePt M.W p t₁ = z) (hw : sidePt M.W p t₂ = rayPt z σ T) : False := by
  have hmid : sidePt M.W p ((t₁ + t₂) / 2) = rayPt z σ ztld := by
    have e1 := congrArg Prod.fst hz
    have e2 := congrArg Prod.snd hz
    have e3 := congrArg Prod.fst hw
    have e4 := congrArg Prod.snd hw
    unfold sidePt at *
    simp only [Geometry.lerp_fst, Geometry.lerp_snd, rayPt_fst, rayPt_snd] at *
    zubjw
    · zunkt; linarith
    · simp only [Geometry.lerp_snd, rayPt_snd]; linarith
  exact hM.trace p hp _ by_linarith by_linarith (hmid ▸ hdom ztld by_linarith
    by_linarith)
open Machine
open Chazelle.Chain (SideAttach sideInArc sideLeft regionsIn)
def TestOK (s : Stmt) (κt : ℕ → ℕ) (F : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (Bo : Finset ℕ) : Prop :=
  Meets s zttys
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      X.holds P c.nmem ztmgp ztm ∧
      c.nreg 83003 ≤ X.cap P c.nmem ztmgp ∧
      ModelDescWF P ztm c.nmem ztdcs ∧
      (c.nmem ztdcs = 0 → ∀ H C, ChainDescAt c.nmem ztcms zta H C →
        HostRegular (Qof P).n H) ∧
      (c.nmem ztdcs = 0 → ∀ H C, ChainDescAt c.nmem ztcms zta H C →
        C.P.Simple) ∧ c.nreg 83008 ≤ 1 ∧
      ∃ M N, ModelDescAt c.nmem ztdcs zta M ∧ GoodModel M ∧ Ok P M ∧
        NFWithin c.nmem ztmgn ztm N ∧ IsNF M zta N ∧
        M.DegLe ztwiv ztqik ∧
        M.Semigranular ztwiv ztmgo ∧ c.nreg 83002 < N.nRegions ∧
        c.nreg 83005 < M.W.n ∧ ProperPos M zta P.n ztbcf ∧
        (c.nreg 83006 = 0 ∨ 0 < M.param zta ztbcf) ∧
        (OkModel P M ∨ M = interiorModel zta) ∧
        (∀ C : Chain, M = chainModel C →
          M.pos zta ztbcf ∈ C.set) ∧
        c.nreg 83007 < P.n ∧
        ((Qof P).vtx ztqij).2 = (M.pos zta ztbcf).2)
    (fun P c c' => (∀ q, bandOf q = bRestore → q < 83000 → c'.nreg q = c.nreg q) ∧
      c'.nreg 83010 ≤ 1 ∧ c'.nreg 83011 ≤ 1 ∧ c'.nreg 83014 ≤ 1 ∧
      ∀ M N reg, ModelDescAt c.nmem ztdcs zta M → NFAt c.nmem ztmgn N →
        IsNF M zta N → NFRegs M zta N reg →
        let x : WPos := ztbcf
        let z := M.pos zta x
        let σ := dirOf ztviz
        let R := reg ztqii
        let far : WPos := ⟨c'.nreg 83012, c'.nreg 83013⟩
        let tr := ztdzh
        (c'.nreg 83014 = 1 →
          (recOf tr).Attached M zta ∧ tr.1 < (Qof P).n ∧
          (recOf tr).toSet M zta ∈ M.Adm ∧
          SplitsWell M ztwiv R ((recOf tr).toSet M zta)) ∧
        (c'.nreg 83010 = 1 → c'.nreg 83011 = 1 →
          ∃ T > (0 : ℝ), (∀ t, 0 < t → t < T → rayPt z σ t ∈ R) ∧
            M.pos zta far = rayPt z σ T ∧ far.edge < M.W.n ∧
            ProperPos M zta P.n far ∧
            chordOf z σ T ∈ M.Adm ∧
            SideAttach M.W ztcmu x.edge ztxkg ∧
            SideAttach M.W ztcmu far.edge (M.param zta far) ∧
            (c'.nreg 83014 = 1 ↔
              CountOK M ztwiv R ztwzj (M.key zta far))) ∧
        (sideLeft M.W x.edge ztxkg zthzp →
          (N.region ztqii).chords ≠ [] →
          (∀ T > (0 : ℝ), (∀ t, 0 < t → t < T → rayPt z σ t ∈ M.D) → rayPt z σ T ∉ M.D →
            chordOf z σ T ∈ M.Adm → chordOf z σ T ∉ N.F M zta →
            chordOf z σ T ∩ M.D ⊆ R → c'.nreg 83010 = 1 ∧ c'.nreg 83011 = 1)))
    (fun _ c => κt ztqik * (F ztmgo + 1))
open Filter Topology Metric
open Chazelle.Chain (sideLeftOf sideCcw sideCross sideDot freeIn TouchesIn sideLeft_zero sideCcw_smul sideKey_inj)
open Chazelle.Jordan (offset SectorSide)
open Sweep
section Valid
theorem ray_mem_region_before' (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {a : ℝ} (harc : M.IsArc F U a ztcfa) {c : Set Point} (hc : c ∈ F)
    (hA : SideAttach M.W c p 0) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 ztwph)
    (hnot : ∀ c ∈ F, SideAttach M.W c p 0 → ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∉ c)
    (hcross : 0 < sideCross (ztkn : Point) ztwll) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∈ U := by
  zubm
  zubay

  zubar
  zufii
  zuiy
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hoff.and ztqdx).and ztctd).exists
  zuiaa
  have hf : ztpko :=
    harc.2.2.2.2.2.2 _ _ hq by_grind by_grind hs2
  zubrx
  have hfree : ball _ r ∩ {x | sideLeftOf _
      _ _ x} ⊆ freeIn M.D F := fun x hx => by
    zujpj
  have hδU' : offset ztxvg ztoy zteb ztckn ∈ U := by
    zugwu
    have e : M.W.vtx p = M.W.vtx ztbarx := by
      zuhnd
    zudtv
  zuhfq
  zuiav
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr] with s hs hsr
  zugvp
  exact hsub ztrsb
theorem sideCross_pair (u : Point) (a b : ℝ) : sideCross u (ztvk : Point) = u.1 * b - u.2 * a :=
  rfl
theorem sideCross_pair_left (a b : ℝ) (u : Point) :
    sideCross (ztvk : Point) u = a * u.2 - b * u.1 := rfl

/-- **A chord running along the ray at the start of an arc is an exit chord.**  At a walk vertex
where an arc of `U` begins, if the direction `τ` is in the left sector strictly counterclockwise
from the next walk edge, a chord of the family containing ray points arbitrarily close to the
vertex touches `U`. -/
theorem touches_of_along_after (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n) {b : ℝ}
    (harc : M.IsArc F U ztcfa b) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 ztwph)
    (hcross : 0 < sideCross ztbajf (ztkn : Point))
    {c : Set Point} (hc : c ∈ F) (hfr : ∃ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∈ c) :
    TouchesIn M.D c U := by
  zudr
  zuqu
  zund
  zuee

  zueeh

  have hB0 := sub_ne_zero.2 hbv
  have hκ0 : 0 < -ztlzd := by
    have := hcross; rw [sideCross_pair] at this; linarith
  zufoy
  have hvA : ztsmr := by
    zuq
    simp_all
  have hsecv : ztxtq :=
    fun x => sideLeft_zero _ _ _
  have hdp : ztbadf := by
    have := (hsecv _).1 hsec
    zurl
  set Wg := ball v r ∩ {x | sideLeftOf ztkgk v b' x} with hWg
  have hWsec : ∀ x ∈ Wg, sideCcw _ _ A := fun x hx => by
    have : sideLeftOf _ v b' x := hx.2
    zuof
  have hWleft := fun x hx =>
    (hsecv x).2 (Chazelle.Chain.sideCcw_sub_left hB0 hdp zttmy)
  have hWfree : ∀ x ∈ ball v r, x ∈ (freeIn M.D F)ᶜ → ¬ sideLeftOf ztkgk v b' x := by
    zulno
    zukb

    rcases hWsec x hxW' with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [hAdef, sideCross_pair, Prod.snd_sub, hy, sub_self] at h; grind
    · linarith
    · linarith
    grind
  obtain ⟨hS1, hHc, hoff⟩ := Chazelle.Chain.sideSector hvA hbv hr hWfree
  obtain ⟨-, -, hkb⟩ := WalkAx.arc_cuts ztzx harc
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hoff.and ztved).and ztctd).exists
  have hf :=
    harc.2.2.2.2.2.2 p s hp hs3.1 hs3.2 by_grind
  zubrx
  have hWU :=
    subset_region hU hHc ztlpa hδ.2 ztnui
  -- a point of the chord on the ray, close to the vertex
  zucbo

  · zucyv

  · zugvp
    set κ := -ztlzd with hκ
    set K := |(b' - v).1| + 1 with hK
    zudno
    have hlim : Tendsto (fun ε : ℝ => ((v.1 + τ * s₀, v.2 - τ * ε) : Point)) (𝓝[>] (0 : ℝ))
        (𝓝 (rayPt v τ s₀)) := by
      have hc' : Continuous (fun ε : ℝ => (ztewf : Point)) := by fun_prop
      have h0 : ((v.1 + τ * s₀, v.2 - τ * 0) : Point) = rayPt v τ s₀ :=
        point_ext by_simp by_simp
      have := hc'.tendsto 0
      zubuv
      zuhv
    zubcx

    have hε2 : ztpqw := by
      have := hε'.2.trans_le ztgh
      zudbe
    apply hWU
    zujx
    · zufnz
      zujj
      · constructor
        · zucuc
        · rw [show v.2 - 1 * ε - v.2 = -ε by ring, abs_neg, abs_of_pos hε0]; linarith
      · constructor
        · zucce
        · rw [show v.2 - -1 * ε - v.2 = ε by ring, abs_of_pos hε0]; linarith
    · show sideLeftOf _ v b' _
      zukyp
      have hX : (ztewf : Point) - v = ((τ * s₀, -(τ * ε)) : Point) := by
        zuity
      zuexv
      left
      have hab := le_abs_self (b' - v).1
      have hab' := neg_abs_le (b' - v).1
      zuehw

      · rw [sideCross_pair]
        have hKe : ε * K = ε * |(b' - v).1| + ε := by_linarith
        zujj
        · linarith
        linarith
      · rw [hAdef, sideCross_pair]
        zugrz

/-- **A chord running along the ray at the end of an arc is an exit chord** (mirror of
`touches_of_along_after`: the direction is strictly clockwise from the previous walk edge). -/
theorem touches_of_along_before (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n) {l : ℝ}
    (harc : M.IsArc F U l ztcfa) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 ztwph)
    (hcross : 0 < sideCross (ztkn : Point) ztwll)
    {c : Set Point} (hc : c ∈ F) (hfr : ∃ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∈ c) :
    TouchesIn M.D c U := by
  zudr
  zuqu
  zund
  zudou
  zuee

  zueeh

  have hav : ztiyw := by
    have := hM.nd _ ztwwc
    zudbf
  zuyp

  have hκ0 : 0 < τ * (a - v).2 := by
    have := hcross; rw [sideCross_pair_left] at this; linarith
  zufoy
  have hAne : A ≠ 0 := by
    zuq
    have := congrArg Prod.fst h
    simp only [hAdef, Prod.fst_zero] at this
    simp_all
  have hvA : ztsmr := by
    grind
  have hsecv : ztxtq :=
    fun x => sideLeft_zero _ _ _
  have hdp : ztbadf := by
    have := (hsecv _).1 hsec
    zurl
  set Wg := ball v r ∩ {x | sideLeftOf a v ztkgk x} with hWg
  have hWsec : ∀ x ∈ Wg, sideCcw A _ _ := fun x hx => by
    zueph
    zuof
  have hWleft := fun x hx =>
    (hsecv x).2 (Chazelle.Chain.sideCcw_sub_right hB0 hAne hA0 hdp zttmy)
  have hWfree : ∀ x ∈ ball v r, x ∈ (freeIn M.D F)ᶜ → ¬ sideLeftOf a v ztkgk x := by
    zulno
    zukb

    rcases hWsec x hxW' with ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [hAdef, sideCross_pair_left, Prod.snd_sub, hy, sub_self] at h; grind
    · linarith
    · linarith
    grind
  obtain ⟨hS1, hHc, hoff⟩ := Chazelle.Chain.sideSector hav hvA hr hWfree
  obtain ⟨-, -, hak⟩ := WalkAx.arc_cuts ztzx harc
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hoff.and ztqdx).and ztctd).exists
  have hq : ztyme := Nat.mod_lt _ hn0
  have hf : ztpko :=
    harc.2.2.2.2.2.2 _ _ hq by_grind by_grind hs2
  zubrx
  have hδU' : offset a v zteb ztckn ∈ U := by
    zugwu
    have e : v = M.W.vtx ztbarx := by
      zuhnd
    zudtv
  have hWU :=
    subset_region hU hHc ztlpa hδ.1 hδU'
  zucbo

  · zucyv

  · zugvp
    set κ := τ * (a - v).2 with hκ
    set K := |(a - v).1| + 1 with hK
    zudno
    have hlim : Tendsto (fun ε : ℝ => ((v.1 + τ * s₀, v.2 + τ * ε) : Point)) (𝓝[>] (0 : ℝ))
        (𝓝 (rayPt v τ s₀)) := by
      have hc' : Continuous (fun ε : ℝ => (ztewe : Point)) := by fun_prop
      have h0 : ((v.1 + τ * s₀, v.2 + τ * 0) : Point) = rayPt v τ s₀ :=
        point_ext by_simp by_simp
      have := hc'.tendsto 0
      zubuv
      zuhv
    zubcx

    have hε2 : ztpqw := by
      have := hε'.2.trans_le ztgh
      zudbe
    apply hWU
    zujx
    · zufnz
      zujj
      · constructor
        · zucuc
        · rw [show v.2 + 1 * ε - v.2 = ε by ring, abs_of_pos hε0]; linarith
      · constructor
        · zucce
        · rw [show v.2 + -1 * ε - v.2 = -ε by ring, abs_neg, abs_of_pos hε0]; linarith
    · show sideLeftOf a v _ _
      zukyp
      have hX : (ztewe : Point) - v = ((τ * s₀, τ * ε) : Point) := by
        zuity
      zuexv
      left
      have hab := le_abs_self (a - v).1
      have hab' := neg_abs_le (a - v).1
      zuehw

      · rw [hAdef, sideCross_pair_left]
        zugrz
      · rw [sideCross_pair_left]
        have hKe : ε * K = ε * |(a - v).1| + ε := by rw [hK]; ring
        zujj
        · linarith
        linarith

/-- A chord of the family attached at a walk vertex is attached at the position of the vertex
when some chord is attached at its key. -/
theorem attach_of_cut (_hM : WalkAx M) {F : Set ztf} {p : ℕ} (hk : M.IsCut F ztmm) :
    ∃ c ∈ F, SideAttach M.W c p 0 := by
  obtain ⟨c, hc, p', t', hA', hkey⟩ := hk
  obtain ⟨hpp, htt⟩ := sideKey_inj le_rfl one_pos hA'.2.1 hA'.2.2.1 hkey
  grind

/-- **Validity at the start of an arc.** -/
theorem valid_after (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {b : ℝ} (harc : M.IsArc F U ztcfa b) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 ztwph)
    (hcross : 0 < sideCross ztbajf (ztkn : Point))
    (hex : ∀ c ∈ F, TouchesIn M.D c U →
      ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∉ c) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∈ U := by
  zubm
  zuqx
  · -- the empty family: the region is the domain
    have hUD : U = M.D := by
      have := Chazelle.Chain.regionsIn_empty hM.preconn hM.nonempty
      zuixe

    zumf

  · obtain ⟨hk, -, -⟩ := WalkAx.arc_cuts hne harc
    zufiu
    refine ray_mem_region_after hGM hFam hU hp harc hc hA hτ hsec ?_ hcross
    zumgm
    zubka

    have ht := touches_of_along_after hM hFam.2.1 hFam.1 hU hp harc hτ hsec hcross hc' hfr
    tauto

/-- **Validity at the end of an arc.** -/
theorem valid_before (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {l : ℝ} (harc : M.IsArc F U l ztcfa) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 ztwph)
    (hcross : 0 < sideCross (ztkn : Point) ztwll)
    (hex : ∀ c ∈ F, TouchesIn M.D c U →
      ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∉ c) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∈ U := by
  zubm
  zuqx
  · have hUD : U = M.D := by
      have := Chazelle.Chain.regionsIn_empty hM.preconn hM.nonempty
      zuixe

    zumf

  · obtain ⟨-, hk, -⟩ := WalkAx.arc_cuts hne harc
    zufiu
    refine ray_mem_region_before' hGM hFam hU hp harc hc hA hτ hsec ?_ hcross
    zumgm
    zubka

    have ht := touches_of_along_before hM hFam.2.1 hFam.1 hU hp harc hτ hsec hcross hc' hfr
    tauto

/-- **Validity inside an arc.** -/
theorem valid_inside (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) {a b : ℝ} (harc : M.IsArc F U a b)
    (hin : sideInArc a b ztk) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p t ztznq) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztbp τ s ∈ U :=
  ray_mem_region_of_arc hGM hFam hU hp ht ht1 harc hin hτ hsec

/-- **The exit scan.**  An attached chord record whose left end is not the walk vertex `(p, 0)`
(for `τ = 1`), or whose right end is not (for `τ = -1`), contains no ray points arbitrarily
close to the vertex, when the ray leaves the vertex into its left sector. -/
theorem exit_avoid (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {cr : CRec} (hcF : cr.toSet M Q ∈ F) (hat : cr.Attached M Q)
    {p : ℕ} (hp : p < M.W.n) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 ztwph)
    (hL : τ = 1 → ¬ (cr.lp = p ∧ M.param Q cr.lpos = 0))
    (hR : τ = -1 → ¬ (cr.rp = p ∧ M.param Q cr.rpos = 0)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∉ cr.toSet M Q := by
  zubm
  zuglo
  obtain ⟨r, hr, hsf⟩ := sector_free hM hF hFam.1 hp le_rfl one_pos
  zubka

  obtain ⟨s, hsc, hs⟩ := (hfr.and_eventually ztmbi).exists
  have hs0 := hs.1
  have hsl : sideLeft M.W p 0 _ :=
    (sideLeft_rayPt_iff _ p 0 τ one_pos hs0).1 hsec
  have hball : rayPt ztfs τ s ∈ ball ztfs r := by
    rw [mem_ball, dist_rayPt _ hτ hs0.le]; simp_all
  have hA := (hsf _ hball hsl).2 _ hcF hsc
  have hadm := hF hcF
  set v := sidePt M.W p 0 with hv
  -- the vertex is an end of the chord: its left end if `τ = 1`, its right end if `τ = -1`
  have hvc := hA.2.2.2.1
  have hvD := hM.trace p hp 0 le_rfl zero_le_one
  obtain ⟨hL1, hL2⟩ := hat
  have hlmem : sidePt M.W cr.lp _ ∈ cr.toSet M Q := hL1.2.2.2.1
  have hrmem : sidePt M.W cr.rp _ ∈ cr.toSet M Q := hL2.2.2.2.1
  obtain ⟨y, xa, xb, hH, hcr⟩ := adm_hchord hGM hadm
  have hts : cr.toSet M Q =
      Visibility.hseg (Q.vtx cr.h).2 (M.pos Q cr.lpos).1 (M.pos Q cr.rpos).1 := rfl
  have hxy : ∀ z ∈ cr.toSet M Q, z.2 = y ∧ xa ≤ z.1 ∧ z.1 ≤ xb := fun z hz => by
    rw [hcr] at hz; exact hz
  have hend : ∀ z ∈ cr.toSet M Q, z ∉ M.D → z = (ztkhf : Point) ∨ z = (ztkhg : Point) := by
    zumht
    obtain ⟨hzy, hz1, hz2⟩ := hxy z hz
    rcases hz1.lt_or_eq with h1 | h1
    · rcases hz2.lt_or_eq with h2 | h2
      · exfalso; apply hzD
        have := hH.open_mem z.1 h1 h2
        grind
      grind
    grind
  have hmemA : (ztkhf : Point) ∈ cr.toSet M Q := by
    rw [hcr]; exact ztreg
  have hmemB : (ztkhg : Point) ∈ cr.toSet M Q := by
    rw [hcr]; exact ztred
  have epl : sidePt M.W cr.lp _ = M.pos Q cr.lpos := rfl
  have epr : sidePt M.W cr.rp _ = M.pos Q cr.rpos := rfl
  have hlA : sidePt M.W cr.lp zttaa = (ztkhf : Point) := by
    have h1 : (M.pos Q cr.lpos).1 ≤ xa := by
      have := hmemA; rw [hts] at this; exact this.2.1
    grind
  have hrB : sidePt M.W cr.rp zttab = (ztkhg : Point) := by
    have h1 : xb ≤ (M.pos Q cr.rpos).1 := by
      have := hmemB; rw [hts] at this; exact this.2.2
    grind
  have hsx := (hxy _ hsc).2
  zvogc at hsx
  zujj
  · have hvA : v = (ztkhf : Point) := by
      grind
    have hu := attach_unique hM hadm hA hL1 (hvA.trans hlA.symm)
    grind
  · have hvB : v = (ztkhg : Point) := by
      grind
    have hu := attach_unique hM hadm hA hL2 (hvB.trans hrB.symm)
    grind
end Valid
open Chazelle.Geometry (lerp_fst lerp_snd)
theorem cut_dichotomy (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} (hp : p < M.W.n)
    (hA : SideAttach M.W c p 0) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 ztwph)
    (hav : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∉ c) :
    0 < sideCross ztbajf (ztkn : Point) ∨
      0 < sideCross (ztkn : Point) ztwll := by
  zund
  obtain ⟨d, hd, -, hcD, -⟩ := attached_opposite hM hc hA hτ hav
  zudou
  zuee

  zujmv
  have hsecv : ztwyo :=
    fun x => sideLeft_zero _ _ _
  zuwk
  have hdp : ztxby := by
    have := (hsecv _).1 hsec
    zurl
  have hBdm : ¬ (sideCross ztfd (ztdx : Point) = 0 ∧
      0 < sideDot ztfd (ztdx : Point)) := by
    zubf
    zuxa
    have hb2 : ztplo := by
      grind
    zuhn

    have hmin : 0 < min d k := lt_min hd hk0
    zucmn
    have hsd : ztmwq := by zvmyz; linarith [min_le_left d k]
    have hsk : ztppx := by zvmyz; linarith [min_le_right d k]
    have hmem : zteig := by_grind
    apply hM.trace p hp ztkek ztjub ztfed
    have e : ztccd := by
      zucky
      zubjw
      · zudcf
        have h3 : ztwwu := by
          zubyn
          grind
        grind
      · simp only [lerp_snd, rayPt_snd]
        grind
    grind
  zudl
  · grind
  · zucvi
  · grind
  · rcases lt_trichotomy (sideCross ztfd (ztkn : Point)) 0 with h4 | h4 | h4
    · zuist
    · zugkk
      zujh
      · grind
      · zubyz

    grind

/-- The ray along an admissible chord `e ∉ S` from its end meets no chord of `S` in the domain
(two distinct chords of a chord system meet only off the domain). -/
theorem ray_not_mem_of_chord (hM : WalkAx M) {S : Set ztf} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) {e : Set Point} (he : e ∈ M.Adm) (heS : e ∉ S) {z : Point} {σ T : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hT : 0 < T) (heq : e = chordOf z σ T)
    (hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ M.D) {c : Set Point} (hc : c ∈ S) :
    ∀ t, 0 < t → t < T → rayPt z σ t ∉ c := by
  intro t ht htT hmem
  have hsys := hM.sys ztrc ztobr ztjxv
  have hce : ztsdx := fun h => heS (h ▸ hc)
  have he' : rayPt z σ t ∈ e := by
    zvnbk; exact (mem_chordOf hσ hT.le).2 ⟨t, ht.le, htT.le, rfl⟩
  exact hsys.inter_subset_compl (mem_insert_of_mem e hc) zttte hce ⟨hmem, he'⟩
    (hdom t ht htT)

/-- **The validity checks accept a good chord.** -/
theorem valid_complete (hGM : GoodModel M) {Q : Polygon} {S : Set ztf}
    (hFam : M.ChordFamily Q S) (hne : S.Nonempty) {R : Set Point} (hR : R ∈ M.regions S)
    {e : Set Point} (he : e ∈ M.Adm) (heS : e ∉ S) (heR : e ∩ M.D ⊆ R) {p : ℕ}
    (hp : p < M.W.n) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hsec : sideLeft M.W p 0 ztzns) {T : ℝ} (hT : 0 < T)
    (heq : e = chordOf ztfs σ T)
    (hdom : ∀ t, 0 < t → t < T → rayPt ztfs σ t ∈ M.D) :
    (∀ c ∈ S, ∀ t, 0 < t → t < T → rayPt ztfs σ t ∉ c) ∧
    ((∃ a b, M.IsArc S R a b ∧ sideInArc a b ztmm) ∨
      (∃ b, M.IsArc S R ztmm b ∧
        0 < sideCross ztbajf (ztwn : Point)) ∨
      (∃ a, M.IsArc S R a ztmm ∧
        0 < sideCross (ztwn : Point) ztwll)) := by
  zubm
  zuhxm

  have hnot : ∀ c ∈ S, ∀ t, 0 < t → t < T → rayPt ztfs σ t ∉ c :=
    fun c hc => ray_not_mem_of_chord hM hS hfin he heS hσ hT heq hdom hc
  refine ⟨hnot, ?_⟩
  -- the ray points are in `R`
  have hrayR : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs σ s ∈ R := by
    zumy
    zucgx

  have same : ∀ X ∈ M.regions S, (∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs σ s ∈ X) →
      X = R := by
    intro X hX hev
    zuejk
    zubba
    · zubh
    grind
  have hav : ∀ c ∈ S, ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs σ s ∉ c := by
    zung
    zumy
    grind
  by_cases hcut : M.IsCut S ztmm
  · obtain ⟨c, hc, hA⟩ := attach_of_cut hM hcut
    obtain ⟨U, V, l, r, hU, hV, -, harcU, harcV, -⟩ := hM.attach_face hS hfin hc hA
    rcases cut_dichotomy hM ztbkp hp hA hσ hsec zttnc with h | h
    · have hin := ray_mem_region_after hGM hFam hU hp harcU hc hA hσ hsec
        ztmjl h
      have := same U hU hin
      zumo
      exact Or.inr (Or.inl ⟨r, harcU, h⟩)
    · have hin := ray_mem_region_before' hGM hFam hV hp harcV hc hA hσ hsec
        ztmjl h
      have := same V hV hin
      zumo
      exact Or.inr (Or.inr ⟨l, harcV, h⟩)
  · zuxi
    have hev := ray_mem_region_of_arc hGM hFam hX hp le_rfl one_pos harc hin hσ hsec
    grind
theorem interior_sides (hM : WalkAx M) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) {σ s : ℝ}
    (h1 : sideLeft M.W p t (rayPt ztbp σ s))
    (h2 : sideLeft M.W p t (rayPt ztbp (-σ) s)) : False := by
  zund
  rw [Chazelle.Chain.sideLeft_edge hne ztcoy] at h1 h2
  unfold sidePt at h1 h2
  simp only [det, Visibility.rayPt, Geometry.lerp_fst, Geometry.lerp_snd] at h1 h2
  nlinarith

/-- **The validity check accepts a good chord from inside a walk edge.** -/
theorem valid_complete_int (hGM : GoodModel M) {Q : Polygon} {S : Set ztf}
    (hFam : M.ChordFamily Q S) (hne : S.Nonempty) {R : Set Point} (hR : R ∈ M.regions S)
    {e : Set Point} (he : e ∈ M.Adm) (heS : e ∉ S) (heR : e ∩ M.D ⊆ R) {p : ℕ}
    (hp : p < M.W.n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hsec : sideLeft M.W p t ztwyg) {T : ℝ} (hT : 0 < T)
    (heq : e = chordOf ztbp σ T)
    (hdom : ∀ s, 0 < s → s < T → rayPt ztbp σ s ∈ M.D) :
    ∃ a b, M.IsArc S R a b ∧ sideInArc a b ztdj := by
  zubm
  zuhxm

  zubzh
  have hnot : ∀ c ∈ S, ∀ s, 0 < s → s < T → rayPt w σ s ∉ c :=
    fun c hc => ray_not_mem_of_chord hM hS hfin he heS hσ hT heq hdom hc
  have hav : ∀ c ∈ S, ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w σ s ∉ c := by
    zung
    zumy
    simp_all
  have hrayR : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w σ s ∈ R := by
    zumy
    zucgx

  by_cases hcut : M.IsCut S ztdj
  · exfalso
    obtain ⟨c, hc, p', t', hA', hkey⟩ := hcut
    obtain ⟨hpp, htt⟩ := sideKey_inj ht0.le ht1 hA'.2.1 hA'.2.2.1 hkey
    zudbb
    obtain ⟨d, hd, -, -, hcd⟩ := attached_opposite hM ztbkp hA' hσ zttnc
    obtain ⟨r, hr, hloc⟩ := hA'.2.2.2.2
    set s := min d r / 2 with hs
    have hmin : 0 < min d r := lt_min hd hr
    zucmn
    have hsd : ztmwq := by zvmyz; linarith [min_le_left d r]
    zukfu
    have hσ' : ztjh := by rcases hσ with rfl | rfl <;> norm_num
    have hxc := hcd s hs0 hsd
    have hxne : rayPt w (-σ) s ≠ w := by
      zuq
      have := congrArg Prod.fst h
      simp only [Visibility.rayPt] at this
      zubbe
    have h2 := hloc _ hxc hxne (by rw [dist_rayPt _ hσ' hs0.le]; omega)
    have h1 := (sideLeft_rayPt_iff _ p t σ one_pos hs0).1 hsec
    exact interior_sides hM hp ht0 ht1 h1 h2
  · zuxi
    have hev := ray_mem_region_of_arc hGM hFam hX hp ht0.le ht1 harc hin hσ hsec
    zuejk
    zubba
    · grind
    grind
end
end Restore
namespace ShootCut
open Machine Machine.Stmt Programs
@[expose] public section
def cInit : Stmt := block [.constN 150090 0, .constN 150091 1, .constN 150092 2,
  .constN 150093 3, .constN 150096 6]

/-- The chain descriptor (`lr 0 + 1 …`): host handle, start, number of edges. -/
def cHead1 : Stmt := block [
  .addN 150075 150000 150091, .loadN 150021 150075,
  .addN 150075 150075 150091, .loadN 150022 150075,
  .addN 150075 150075 150091, .loadN 150023 150075]

/-- The top index, the orientation bit and the walk constants. -/
def cHead2 : Stmt := block [
  .addN 150075 150075 150091, .loadN 150024 150075,
  .addN 150075 150075 150091, .loadN 150025 150075,
  .addN 150029 150023 150023, .addN 150032 150029 150096, .subN 150031 150032 150091]

/-- `n` and the grade table. -/
def cHead3 : Stmt := block [
  .inputSize 150027, .loadN 150033 150013,
  .addN 150075 150013 150091, .loadN 150076 150075, .addN 150036 150076 150092,
  .addN 150075 150013 150092, .loadN 150034 150075,
  .addN 150075 150013 150093, .loadN 150035 150075]

/-- The tour start `S = T` (orientation bit set) or `2m - T`. -/
def cS : Stmt :=
  .ifLtN 150025 150091 ztnbg
    (.ifLtN 150091 150025 ztnbg (.instr (.copyN 150028 150024)))

/-- The number of host points (`NFLoc.cntStmt`). -/
def cCount : Stmt :=
  .seq (.instr (.copyN 50060 150021)) (.seq NFLoc.cntStmt (.instr (.copyN 150026 50063)))

/-- The whole set-up. -/
def cPre : Stmt := .seq cInit (.seq cHead1 (.seq cHead2 (.seq cHead3 (.seq cS cCount))))

/-! ## The host item of a host point -/
def itInit : Stmt :=
  block [.constN 150065 0, .constN 150073 0, .addN 150074 150021 150091, .loadN 150077 150021]
def itFound : Stmt := block [.subN 150066 150064 150073, .copyN 150079 150065, .copyN 150065 150077]
def itNext : Stmt := block [.copyN 150073 150078, .addN 150065 150065 150091,
  .addN 150074 150074 150093]
def itBody : Stmt :=
  .seq (block [.loadN 150067 150074, .addN 150075 150074 150091, .loadN 150068 150075,
      .addN 150075 150075 150091, .loadN 150069 150075])
    (.seq (.ifLtN 150067 150091 ztiqf
        ztnap)
      (.ifLtN 150064 150078 itFound itNext))

/-- **The item of the host point `150064`**: item `65`, offset `66`, words `67 … 69`. -/
def itLook : Stmt :=
  .seq itInit (.seq (.whileLtN 150065 150077 itBody) (.instr (.copyN 150065 150079)))

/-! ## A walk vertex of the double boundary -/

/-- **The walk vertex `150044`** (`6 ≤ v ≤ 2m + 6`): tour position, tour coordinate, chain
index, climbing bit, host point and its item. -/
def locV : Stmt :=
  .seq (block [.subN 150060 150044 150096, .subN 150075 150029 150028])
    (.seq (.ifLtN 150060 150075 ztnao
        ztnbh)
      (.seq (.ifLtN 150061 150023 ztkqv
          ztjpc)
        (.seq (.seq (.instr (.addN 150075 150022 150062))
            (.ifLtN 150075 150026 ztove
              ztnbi))
          itLook)))

/-- **The symbolic point of the walk vertex `150044`** into `150045 …`. -/
def vtxPt : Stmt :=
  .seq locV
    (.ifLtN 150067 150091
      (.seq ztdeq
        (.seq (.ifLtN 150075 150027 ztigg
            ztgww)
          ztift))
      (.ifLtN 150067 150092 ztfbi
        ztdlp))

/-! ## Pieces -/

/-- The single-edge piece from the current vertex. -/
def pcSingle : Stmt := block [.copyN 150050 150040, .constN 150051 0, .addN 150052 150040 150091,
  .constN 150053 0, .constN 150054 0]

/-- Emit a single edge and advance. -/
def single (emit : Stmt) : Stmt :=
  .seq pcSingle (.seq emit (.instr (.addN 150040 150040 150091)))

/-- The block piece `[w, w + 2^g]` with its entry (`g > 0`: the entry `(g, 150077)` of the grade
table, kind `1`; `g = 0`: kind `0`); `150056` the first edge of its chain of `Q`, `150057` the
direction. -/
def pcBlock (x dir : ℕ) : Stmt :=
  .seq (block [.copyN 150050 150085, .constN 150051 0, .addN 150052 150085 150084,
      .constN 150053 0, .copyN 150056 x, .constN 150057 dir, .copyN 150058 150084])
    (.ifLtN 150090 150082
      (block [.constN 150054 1, .addN 150075 150034 150082, .loadN 150076 150075,
        .addN 150055 150076 150077, .addN 150055 150055 150077, .addN 150055 150055 150077])
      (.instr (.constN 150054 0)))

/-! ## The dyadic sweeps -/

/-- Upward, ascending sweep body. -/
def upABody (emit : Stmt) : Stmt :=
  .seq ztbus
    (.seq (.ifLtN 150075 150083
        (.seq ztigi
          (.seq ztoej
            (.seq emit (block [.addN 150080 150080 150084, .addN 150085 150085 150084,
              .addN 150086 150086 150091]))))
        .skip)
      (block [.addN 150082 150082 150091, .addN 150075 150036 150082, .loadN 150084 150075,
        .copyN 150083 150086, .addN 150087 150080 150084]))

/-- Upward, descending sweep body (the odd branch as in the ascending sweep, with the index
kept in `86`). -/
def upBBody (emit : Stmt) : Stmt :=
  .seq (block [.subN 150082 150082 150091, .addN 150075 150036 150082, .loadN 150084 150075,
      .addN 150083 150083 150083, .copyN 150086 150083, .addN 150087 150080 150084])
    (.seq (.ifLtN 150087 150088
      (.seq ztigi
        (.seq ztoej
          (.seq emit (block [.addN 150080 150080 150084, .addN 150085 150085 150084,
            .addN 150086 150086 150091]))))
      .skip) (.instr (.copyN 150083 150086)))

/-- **The upward dyadic cover** of `[q, q + L)` (`q` in `70`, `L` in `71`) from the walk vertex
`c`; the new `c` is `c + L`. -/
def dyUp (emit : Stmt) : Stmt :=
  .seq (block [.copyN 150080 150070, .addN 150081 150070 150071, .addN 150088 150081 150091,
      .constN 150082 0, .copyN 150083 150070, .constN 150084 1, .copyN 150085 150040,
      .addN 150087 150080 150084])
    (.seq ztncy
      ztzsi)

/-- Downward sweeps: hand the block below `y` (index `x / 2^g - 1`), then lower `y`. -/
def dnOdd (emit : Stmt) : Stmt :=
  .seq ztirf
    (.seq (pcBlock 150078 0)
      (.seq emit ztirg))

/-- Downward, ascending sweep body. -/
def dnABody (emit : Stmt) : Stmt :=
  .seq ztbus
    (.seq ztlzw
      (block [.addN 150082 150082 150091, .addN 150075 150036 150082, .loadN 150084 150075,
        .copyN 150083 150086, .addN 150087 150080 150084, .addN 150088 150081 150091]))

/-- Downward, descending sweep body. -/
def dnBBody (emit : Stmt) : Stmt :=
  .seq (block [.subN 150082 150082 150091, .addN 150075 150036 150082, .loadN 150084 150075,
      .addN 150083 150083 150083, .addN 150087 150080 150084, .addN 150088 150081 150091])
    ztfei

/-- **The downward dyadic cover** of `[q - L, q)` from the top `q`. -/
def dyDn (emit : Stmt) : Stmt :=
  .seq (block [.copyN 150081 150070, .subN 150080 150070 150071, .addN 150088 150081 150091,
      .constN 150082 0, .copyN 150083 150070, .constN 150084 1, .copyN 150085 150040,
      .addN 150087 150080 150084])
    (.seq ztncx
      ztzsh)

/-! ## One step of the main loop -/

/-- `150071 := min 150071 r`. -/
def minTo (r : ℕ) : Stmt := .ifLtN r 150071 (.instr (.copyN 150071 r)) .skip

/-- The length of a climbing stretch (the item is a run, `t < ℓ`, `q + 1 < n`) into `150071`:
`L = min (m - J) (ℓ - t) (n - 1 - q) lim`. -/
def upLen : Stmt :=
  .seq ztird
    (.seq ztvzd (.seq ztire
      (.seq ztvzd ztvzc)))

/-- A climbing stretch: its length, the upward cover, and the constants set again (the sweeps
keep only `150090`, `150091` of them). -/
def upStretch (emit : Stmt) : Stmt := .seq upLen (.seq ztvph cInit)

/-- The length of a descending stretch (`0 < t`, `0 < q`): `L = min (2m - J) t q lim`. -/
def dnLen : Stmt :=
  .seq (.instr (.subN 150071 150029 150061))
    (.seq (minTo 150066) (.seq (minTo 150070) ztvzc))

/-- A descending stretch. -/
def dnStretch (emit : Stmt) : Stmt := .seq dnLen (.seq ztvpg cInit)

/-- A run item: the index `q = (a + t) mod n`, then a stretch or a single edge. -/
def runStep (emit : Stmt) : Stmt :=
  .seq (.seq ztdeq
      (.ifLtN 150075 150027 ztovf
        ztnbj))
      (.ifLtN 150063 150091
        (.ifLtN 150090 150066 (.ifLtN 150090 150070 ztqmd ztfiq) ztfiq)
        (.ifLtN 150066 150069
          (.seq (.instr (.addN 150075 150070 150091))
            (.ifLtN 150075 150027 ztqxx ztfiq))
          ztfiq))

/-- **A step on the double boundary** from the vertex `c < 2m + 6`. -/
def cStep (emit : Stmt) : Stmt :=
  .seq (.instr (.copyN 150044 150040))
    (.seq locV
      (.seq (.ifLtN 150041 150040 ztnbk
          ztnbl)
        ztyzs))

/-- The piece through the uncounted block, from `2m + 6` to `6`. -/
def uStep (emit : Stmt) : Stmt :=
  .seq (block [.copyN 150050 150032, .constN 150051 0, .copyN 150052 150096, .constN 150053 0,
      .constN 150054 0])
    (.seq emit ztdse)

/-- The loop flag: `1` iff `c ≠ f`. -/
def setFlag : Stmt :=
  .ifLtN 150040 150041 ztots
    (.ifLtN 150041 150040 ztots (.instr (.constN 150042 0)))

/-- **The main loop**: while `c ≠ f`, a step. -/
def mainLoop (emit : Stmt) : Stmt :=
  .whileLtN 150090 150042 ztzsd

/-! ## Tests on walk positions -/

/-- The direction code of the walk edge `150049` into `150059` (`NFLoc.chainDir`). -/
def dirP : Stmt :=
  .seq ztksd
    (.seq NFLoc.chainDir (.instr (.copyN 150059 10502)))

/-- Compare the height of the symbolic point `150045 …` with the height of the vertex `150076`
of `Q`: `150089 := dirOf` (`NFLoc.dirTail`). -/
def hcmp : Stmt :=
  .seq (block [.copyN 50040 150045, .copyN 50041 150046, .copyN 50042 150047,
      .constN 50043 0, .copyN 50044 150076])
    (.seq NFLoc.dirTail (.instr (.copyN 150089 10502)))

/-- **Is the parameter of the position `(150049, 150076 + 1)` positive?** (walk edge
`6 ≤ p ≤ 2m + 6`): the edge is not horizontal and the height differs from the one of its start
vertex; answer in `150089`. -/
def posP : Stmt :=
  .seq dirP
    (.ifLtN 150059 150091 ztcym
      (.seq (.instr (.copyN 150044 150049)) (.seq vtxPt (.seq hcmp
        ztyzt))))

/-- **Is the start before the end** (both on the edge `150049`, codes `≥ 1`)?  Answer in
`150089`: the direction code and the order of the two heights agree. -/
def keyLess : Stmt :=
  .seq dirP
    (.ifLtN 150059 150091 ztcym
      (.seq (block [.constN 50040 0, .subN 50041 150002 150091, .constN 50043 0,
          .subN 50044 150004 150091])
        (.seq NFLoc.dirTail
          (.ifLtN 10502 150059 ztcym
            (.ifLtN 150059 10502 ztcym ztfeo)))))

/-- The flag of the box block: `150038 := [e₁ ∈ U]`, `150039 := [e₂ ∈ U]`; their positions in
the block (`150037`, `150030`: `0` for `2m + 6`, else `p + 1`). -/
def uFlag (src dst idx : ℕ) : Stmt :=
  .ifLtN src 150096 (block [.constN dst 1, .addN idx src 150091])
    (.ifLtN src 150032 ztkrk
      (.ifLtN 150032 src ztkrk
        (block [.constN dst 1, .constN idx 0])))

/-- The box edges: `150048 := 1` on the edges `1, 3, 5` (not horizontal; the end is inside the
box). -/
def decBox : Stmt :=
  .ifLtN 150001 150091 .skip (.ifLtN 150001 150092 ztifu
    (.ifLtN 150001 150093 .skip (.seq (.instr (.subN 150075 150001 150093))
      (.ifLtN 150075 150091 ztifu
        (.ifLtN 150075 150092 .skip ztifu)))))

/-- The start at a vertex, the end inside the edge: is the parameter of the end positive? -/
def decVtx : Stmt :=
  .ifLtN 150001 150096 decBox
    (.seq ztjpi
      (.seq posP ztovd))

/-- Both ends on one edge, the end not at its start vertex. -/
def decSame : Stmt :=
  .ifLtN 150002 150091 decVtx
    (.seq (.instr (.copyN 150049 150001)) (.seq keyLess ztovd))

/-- **The decision `SAME`** (the subarc lies inside the edge of its start), into `150048`. -/
def decideS : Stmt :=
  .seq (.instr (.constN 150048 0))
    (.ifLtN 150001 150003 .skip (.ifLtN 150003 150001 .skip
      (.ifLtN 150090 150004 decSame .skip)))

/-! ## The whole core -/

/-- The piece `[s, e]` (kind `0`). -/
def pcSE : Stmt := block [.copyN 150050 150001, .copyN 150051 150002, .copyN 150052 150003,
  .copyN 150053 150004, .constN 150054 0]

/-- The piece from the start to the walk vertex `150075` (kind `0`). -/
def pcSV : Stmt := block [.copyN 150050 150001, .copyN 150051 150002, .copyN 150052 150075,
  .constN 150053 0, .constN 150054 0]

/-- The piece from the walk vertex `150075` to the end (kind `0`). -/
def pcVE : Stmt := block [.copyN 150050 150075, .constN 150051 0, .copyN 150052 150003,
  .copyN 150053 150004, .constN 150054 0]

/-- The first piece; sets `c` (`150040`) or the done flag (`150043`). -/
def first (emit : Stmt) : Stmt :=
  .ifLtN 150090 150038
    -- the start is in the box block
    (.ifLtN 150090 150039
      (.ifLtN 150037 150030 zthqi
        (.seq ztigh (.seq pcSV (.seq emit
          ztdse))))
      (.seq ztigh (.seq pcSV (.seq emit
        ztdse))))
    -- the start is on the double boundary
    (.seq (.instr (.addN 150075 150001 150091))
      (.ifLtN 150090 150039
        (.ifLtN 150075 150032
          ztdet
          zthqi)
        ztdet))

/-- The last piece. -/
def final (emit : Stmt) : Stmt :=
  .ifLtN 150090 150039
    (.seq (.instr (.copyN 150075 150031)) ztncu)
    (.ifLtN 150090 150004
      (.seq ztjpj
        (.seq posP (.ifLtN 150090 150089
          (.seq (.instr (.copyN 150075 150003)) ztncu) .skip)))
      .skip)

/-- The general case: the first piece, the main loop, the last piece. -/
def general (emit : Stmt) : Stmt :=
  .seq (.seq (uFlag 150001 150038 150037) (uFlag 150003 150039 150030))
    (.seq (.ifLtN 150090 150039 ztovc ztovb)
      (.seq (.instr (.constN 150043 0))
        (.seq zthwr
          (.ifLtN 150043 150091 (.seq setFlag (.seq ztvyq ztvql)) .skip))))

/-- **The core of the arc-cutter.** -/
def core (emit : Stmt) : Stmt :=
  .seq cPre (.seq decideS (.ifLtN 150090 150048 (.seq pcSE emit) ztqor))
open SignK NFLoc
def Bit : ℕ → Bool := Bl [150065, 150066, 150067, 150068, 150069, 150073, 150074, 150075,
  150077, 150078, 150079]
theorem wr_itLook : wr Bit itLook = true := by_decide

/-- What the item search keeps. -/
structure ItEnv (W Hh u L : ℕ) (m : ℕ → ℕ) (d : Config) : Prop where
  wb : WordsBounded W d
  mem : d.nmem = m
  h21 : d.nreg 150021 = Hh
  h91 : d.nreg 150091 = 1
  h93 : d.nreg 150093 = 3
  h64 : d.nreg 150064 = u
  h77 : d.nreg 150077 = L

/-- The item found for `u`. -/
def ItFound (n Hh u : ℕ) (H : Host) (m : ℕ → ℕ) (d : Config) (r : ℕ) : Prop :=
  r < H.length ∧ preLen n H r ≤ u ∧ u < preLen n H ztgu ∧
    d.nreg 150066 = u - preLen n H r ∧ d.nreg 150067 = m ztcln ∧
    d.nreg 150068 = m ztbyi ∧ d.nreg 150069 = m ztclo

/-- The invariant of the item search. -/
def ItI (W n Hh u : ℕ) (H : Host) (m : ℕ → ℕ) (d : Config) : Prop :=
  ItEnv W Hh u H.length m d ∧ d.nreg 150065 ≤ H.length ∧
    ((d.nreg 150073 = preLen n H ztvoj ∧ preLen n H ztvoj ≤ u ∧
        d.nreg 150074 = Hh + 1 + 3 * d.nreg 150065) ∨
      (d.nreg 150065 = H.length ∧ ItFound n Hh u H m d (d.nreg 150079)))
variable {P : Polygon} {W Hh u : ℕ} {H : Host} {m : ℕ → ℕ}
theorem itBody_exec {d : Config}
    (hH : HostAt m Hh H) (haW : Hh + 3 * H.length + 4 ≤ W) (hN : (H.pts P.n).length ≤ W)
    (_hu : u < (H.pts P.n).length) (hI : ItI W P.n Hh u H m d)
    (ht : d.nreg 150065 < d.nreg 150077) :
    ∃ d' k, Exec P W itBody d d' k ∧ ItI W P.n Hh u H m d' ∧ k ≤ 20 ∧
      H.length - d'.nreg 150065 < H.length - d.nreg 150065 := by
  obtain ⟨E, hil, hs⟩ := hI
  zugnh
  rw [E.h77] at ht
  set i := d.nreg 150065 with hi
  zudjm

  · omega
  zubez

  zucqm

  obtain ⟨d₁, k₁, e₁, hk₁, l67, l68, l69⟩ : ∃ d₁ k₁, Exec P W (block [.loadN 150067 150074,
      .addN 150075 150074 150091, .loadN 150068 150075, .addN 150075 150075 150091,
      .loadN 150069 150075]) d d₁ k₁ ∧ k₁ = 5 ∧ d₁.nreg 150067 = k ∧ d₁.nreg 150068 = a ∧
      d₁.nreg 150069 = b := by
    exec_block
    · config_simp; rw [ha, E.h91]; omega
    · config_simp; rw [ha, E.h91]; omega
    · refine ⟨rfl, by config_simp; rw [ha, E.mem], ?_, ?_⟩
      · config_simp; rw [ha, E.h91, E.mem]; grind
      · config_simp; rw [ha, E.h91, E.mem]; grind
  have f₁ := exec_frameB e₁ (B := Bl [150067, 150068, 150069, 150075]) by_decide
  have g := fun r (hr : Bl [150067, 150068, 150069, 150075] r = false) => f₁.1 r hr
  have g21 := (g _ by_decide).trans E.h21
  have g64 := (g _ by_decide).trans E.h64
  have g65 : d₁.nreg 150065 = i := g _ by_decide
  have g73 := (g _ by_decide).trans hacc
  have g74 := (g _ by_decide).trans ha
  have g77 := (g _ by_decide).trans E.h77
  have g91 := (g _ by_decide).trans E.h91
  have g93 := (g _ by_decide).trans E.h93
  zulhf
  zud
  -- the count of the item
  obtain ⟨d₂, k₂, e₂, hk₂, l78⟩ : ∃ d₂ k₂, Exec P W (.ifLtN 150067 150091
      ztiqf
      ztnap) d₁ d₂ k₂ ∧ k₂ ≤ 3 ∧
      d₂.nreg 150078 = preLen P.n H ztg := by
    rw [hpre, ← hcnt]
    zujtn
    · rw [ite_eq_left hkind]
      zudd
      exec_block
      · grind
      · config_simp; grind
      · exact ⟨by_omega, by config_simp; omega⟩
    · rw [ite_eq_right hkind]
      refine spec_ifLtN_false by_omega
        (spec_instr (Exec.addN e₁.wb_right _ _ _ (by
          omega))
          by_simp_all)
  have f₂ := exec_frameB e₂ (B := Bl [150078]) by_decide
  have h2 : ∀ r, r ≠ 150078 → d₂.nreg r = d₁.nreg r := fun r hr => f₂.1 r ztnuo
  zue
  by_cases hf : u < preLen P.n H ztg
  · -- found
    obtain ⟨d₃, k₃, e₃, hk₃, o66, o79, o65⟩ : ∃ d₃ k₃, Exec P W itFound d₂ d₃ k₃ ∧ k₃ = 3 ∧
        d₃.nreg 150066 = u - preLen P.n H i ∧ d₃.nreg 150079 = i ∧
        d₃.nreg 150065 = H.length := by
      unfold itFound
      exec_block
      simp_all
    have f₃ := exec_frameB e₃ (B := Bl [150065, 150066, 150079]) by_decide
    have h3 : ∀ r, r ≠ 150065 → r ≠ 150066 → r ≠ 150079 → d₃.nreg r = d₂.nreg r :=
      fun r h1 h2' h3' => f₃.1 r ztjqj
    have t1 : d₂.nreg 150064 < d₂.nreg 150078 := by_simp_all
    refine ⟨d₃, k₁ + ztdhs, .seq e₁ (.seq e₂ (.ifLtN_true t1 e₃)),
      ⟨⟨e₃.wb_right, f₃.2.2.1.trans ztvqu, ?_, ?_, ?_, ?_, ?_⟩, by_omega,
        Or.inr ⟨o65, ?_⟩⟩, by_omega, by_omega⟩
    · simp_all
    · simp_all
    · simp_all
    · simp_all
    · simp_all
    · rw [o79]
      refine ⟨ht, hpi, hf, o66, ?_, ?_, ?_⟩
      · simp_all
      · simp_all
      simp_all
  · -- the next item
    obtain ⟨d₃, k₃, e₃, hk₃, o73, o65, o74⟩ : ∃ d₃ k₃, Exec P W itNext d₂ d₃ k₃ ∧ k₃ = 3 ∧
        d₃.nreg 150073 = preLen P.n H ztg ∧ d₃.nreg 150065 = i + 1 ∧
        d₃.nreg 150074 = Hh + 1 + 3 * ztg := by
      unfold itNext
      exec_block
      · config_simp; grind
      · config_simp; grind
      · refine ⟨rfl, by_simp_all, ?_, ?_⟩
        · simp_all
        · config_simp; grind
    have f₃ := exec_frameB e₃ (B := Bl [150065, 150073, 150074]) by_decide
    have h3 : ∀ r, r ≠ 150065 → r ≠ 150073 → r ≠ 150074 → d₃.nreg r = d₂.nreg r :=
      fun r h1 h2' h3' => f₃.1 r ztjqj
    have t1 : ¬ d₂.nreg 150064 < d₂.nreg 150078 := by_simp_all
    refine ⟨d₃, k₁ + ztoch, .seq e₁ (.seq e₂ ztspb),
      ⟨⟨e₃.wb_right, f₃.2.2.1.trans ztvqu, ?_, ?_, ?_, ?_, ?_⟩, by_omega,
        by grind⟩, by_omega, by_omega⟩
    · simp_all
    · grind
    · grind
    · simp_all
    grind

/-- **The item of a host point** (at most `22 |H| + 10` steps). -/
theorem itLook_exec (c : Config)
    (hw : WordsBounded W c) (hm : c.nmem = m) (hH : HostAt m Hh H) (h21 : c.nreg 150021 = Hh)
    (h91 : c.nreg 150091 = 1) (h93 : c.nreg 150093 = 3) (h64 : c.nreg 150064 = u)
    (haW : Hh + 3 * H.length + 4 ≤ W) (hN : (H.pts P.n).length ≤ W)
    (hu : u < (H.pts P.n).length) :
    ∃ c' k, Exec P W itLook c c' k ∧ k ≤ 22 * H.length + 10 ∧ FrameB Bit c c' ∧
      ItFound P.n Hh u H m c' ztvgf := by
  zumdu
  obtain ⟨c₁, k₁, e₁, hk₁, I₁⟩ : ∃ c₁ k₁, Exec P W itInit c c₁ k₁ ∧ k₁ = 4 ∧
      ItI W P.n Hh u H m c₁ := by
    unfold itInit
    exec_block
    · omega
    · omega
    · config_simp; omega
    · refine ⟨rfl, ⟨⟨by_omega, by_omega, by_simp_all,
        by simp_all, by_simp_all, by_simp_all, ?_⟩,
        by simp, Or.inl ztcg⟩⟩
      · simp_all
      · rfl
      · positivity
      simp_all
  obtain ⟨c₂, k₂, e₂, I₂, hx₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (a := 150065)
    (b := 150077) (body := itBody) (ItI W P.n Hh u H m) (fun d => H.length - d.nreg 150065) 20
    ztjvt (fun d hd ht => by
      obtain ⟨d', k, e, I', hk, hμ⟩ := itBody_exec hH haW hN hu hd ht
      grind) I₁
  obtain ⟨E₂, hil₂, hs₂⟩ := I₂
  rw [E₂.h77] at hx₂
  rcases hs₂ with ⟨hacc, hpi, -⟩ | ⟨-, hfound⟩
  · -- the search cannot run out: `u` is below the number of points
    exfalso
    have d_eq : c₂.nreg 150065 = H.length := by_omega
    rw [d_eq, preLen_length] at hpi
    omega
  obtain ⟨c₃, k₃, e₃, o65⟩ : ∃ c₃ k₃, Exec P W (.instr (.copyN 150065 150079)) c₂ c₃ k₃ ∧
      c₃.nreg 150065 = c₂.nreg 150079 ∧ k₃ = 1 ∧ (∀ r, r ≠ 150065 → c₃.nreg r = c₂.nreg r) ∧
      c₃.nmem = c₂.nmem := by
    refine ⟨_, 1, Exec.copyN E₂.wb _ _, by config_simp, rfl, by_simp_all, rfl⟩
  obtain ⟨o65, hk₃, hr₃, hm₃⟩ := o65
  have ex : Exec P W itLook c c₃ _ := .seq e₁ ztcr
  refine ⟨c₃, _, ex, ?_, exec_frameB ex wr_itLook, ?_⟩
  · omega
  · rw [o65]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hfound
    exact ⟨h1, h2, h3, by_simp_all, by_simp_all,
      by simp_all, by_simp_all⟩

/-! ## A walk vertex -/

/-- The registers written by `locV`. -/
def Bloc : ℕ → Bool := Bl [150060, 150061, 150062, 150063, 150064, 150065, 150066, 150067,
  150068, 150069, 150073, 150074, 150075, 150077, 150078, 150079]
theorem wr_locV : wr Bloc locV = true := by_decide

/-- The tour coordinate by one conditional subtraction. -/
def jOf (S i m2 : ℕ) : ℕ := if S + i < m2 then S + i else S + i - m2
theorem jOf_eq {S i m2 : ℕ} (hS : S ≤ m2) (hi : i < m2) : jOf S i m2 = ztbat % m2 := by
  unfold jOf
  zus
  · zuclg
  · zul
theorem sideE_jOf {S i m : ℕ} (hS : S ≤ 2 * m) (hi : i ≤ 2 * m) (hm : 1 ≤ m) :
    Chazelle.Chain.sideE m (jOf S i ztdk) = Chazelle.Chain.sideE m ztzyo := by
  rcases hi.lt_or_eq with hi | rfl
  · rw [jOf_eq hS hi]
  · unfold jOf
    rw [ite_eq_right by_omega, Nat.add_mod_right]
    rcases hS.lt_or_eq with hS | rfl
    · rw [Nat.mod_eq_of_lt hS, show S + 2 * m - 2 * m = S by omega]
    · rw [Nat.mod_self, show 2 * m + 2 * m - 2 * m = 2 * m by omega]
      zumqm

/-- The chain index as the machine computes it. -/
theorem kOf_eq (m J : ℕ) : (if J < m then J else 2 * m - J) = Chazelle.Chain.sideE m J := by
  zumqm

/-- The facts `locV` needs about the chain registers. -/
structure ChainRegs (C : Chain) (N Hh : ℕ) (c : Config) : Prop where
  h21 : c.nreg 150021 = Hh
  h22 : c.nreg 150022 = C.s
  h23 : c.nreg 150023 = C.m
  h26 : c.nreg 150026 = N
  h28 : c.nreg 150028 = C.sideS C.sideBeta
  h29 : c.nreg 150029 = 2 * C.m
  h91 : c.nreg 150091 = 1
  h93 : c.nreg 150093 = 3
  h96 : c.nreg 150096 = 6
theorem ChainRegs.of_frame {C : Chain} {N Hh : ℕ} {c c' : Config} (h : ChainRegs C N Hh c)
    (hr : ∀ r, r ∈ [150021, 150022, 150023, 150026, 150028, 150029, 150091, 150093, 150096] →
      c'.nreg r = c.nreg r) : ChainRegs C N Hh c' :=
  ⟨(hr _ by_simp).trans h.h21, (hr _ by_simp).trans h.h22, (hr _ by_simp).trans h.h23,
    (hr _ by_simp).trans h.h26, (hr _ by_simp).trans h.h28, (hr _ by_simp).trans h.h29,
    (hr _ by_simp).trans h.h91, (hr _ by_simp).trans h.h93, (hr _ by_simp).trans h.h96⟩

/-- **A walk vertex of the double boundary**: tour position `i = v - 6`, coordinate `J`, chain
index `k = sideE m J`, climbing bit, host point `u = (C.s + k) mod N` and its item. -/
theorem locV_exec {W : ℕ} {C : Chain} {H : Host} {Hh v : ℕ} {m : ℕ → ℕ}
    (c : Config) (hw : WordsBounded W c) (hm : c.nmem = m) (hH : HostAt m Hh H)
    (R : ChainRegs C (H.pts P.n).length Hh c) (h44 : c.nreg 150044 = v) (hv6 : 6 ≤ v)
    (hv : v ≤ 2 * C.m + 6) (hs : C.s < (H.pts P.n).length) (hmN : C.m < (H.pts P.n).length)
    (haW : Hh + 3 * H.length + 4 ≤ W) (hNW : 2 * (H.pts P.n).length ≤ W) :
    ∃ c' k, Exec P W locV c c' k ∧ k ≤ 22 * H.length + 30 ∧ FrameB Bloc c c' ∧
      c'.nreg 150060 = v - 6 ∧ c'.nreg 150061 = jOf ztboi ztfvc ztbb ∧
      c'.nreg 150062 = Chazelle.Chain.sideE C.m ztxfp ∧
      (c'.nreg 150063 = 1 ↔ jOf ztboi ztfvc ztbb < C.m) ∧
      c'.nreg 150063 ≤ 1 ∧
      c'.nreg 150064 = (C.s + Chazelle.Chain.sideE C.m
        ztxfp) % (H.pts P.n).length ∧
      ItFound P.n Hh (c'.nreg 150064) H m c' ztvgf := by
  zuec
  zubb
  zubad
  set i := v - 6 with hi
  set J := jOf S i _ with hJ
  have hJle : J ≤ 2 * C.m := by rw [hJ]; unfold jOf; grind
  have hk := sideE_jOf hS (show i ≤ 2 * C.m by omega) hm1
  rw [← hJ] at hk
  set k := Chazelle.Chain.sideE C.m _ with hkdef
  have hkm : ztidw := by zunki; exact Chazelle.Chain.sideE_le hJle
  zugyg
  -- straight part
  obtain ⟨c₁, k₁, e₁, hk₁, o60, o75⟩ : ∃ c₁ k₁, Exec P W (block [.subN 150060 150044 150096,
      .subN 150075 150029 150028]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 150060 = i ∧
      c₁.nreg 150075 = 2 * C.m - S := by
    exec_block
    zuknv
    · config_simp; rw [h44, R.h96]
    · config_simp; rw [R.h29, R.h28]
  have f₁ := exec_frameB e₁ (B := Bl [150060, 150075]) by_decide
  have R₁ := R.of_frame fun r hr => f₁.1 r (by
    zuvy
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  zud
  -- `J`
  obtain ⟨c₂, k₂, e₂, hk₂, o61, r₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 150060 150075
      ztnao ztnbh) c₁ c₂ k₂ ∧
      k₂ ≤ 3 ∧ c₂.nreg 150061 = J ∧ ∀ r, r ≠ 150061 → c₂.nreg r = c₁.nreg r := by
    by_cases h : i < 2 * C.m - S
    · refine spec_ifLtN_true by_omega (spec_instr (Exec.addN w₁ _ _ _
        (by rw [R₁.h28, o60]; omega)) fun _ => ⟨by_omega, ?_, by_simp_all⟩)
      config_simp; rw [R₁.h28, o60, hJ]; unfold jOf; grind
    · refine spec_ifLtN_false by_omega (spec_instr ztbly
        fun _ => ztbfk)
      config_simp; rw [o60, o75, hJ]; unfold jOf; grind
  zue
  -- `k` and the climbing bit
  obtain ⟨c₃, k₃, e₃, hk₃, o62, o63, o63', r₃⟩ : ∃ c₃ k₃, Exec P W (.ifLtN 150061 150023
      ztkqv
      ztjpc) c₂ c₃ k₃ ∧ k₃ ≤ 4 ∧
      c₃.nreg 150062 = k ∧ (c₃.nreg 150063 = 1 ↔ J < C.m) ∧ c₃.nreg 150063 ≤ 1 ∧
      ∀ r, r ≠ 150062 → r ≠ 150063 → c₃.nreg r = c₂.nreg r := by
    have e23 : c₂.nreg 150023 = C.m := by rw [r₂ _ by_omega, R₁.h23]
    have e29 : c₂.nreg 150029 = 2 * C.m := by rw [r₂ _ by_omega, R₁.h29]
    by_cases h : J < C.m
    · zudd
      exec_block
      · omega
      · refine ztino
        config_simp; rw [o61, ← hk, ← kOf_eq, ite_eq_left h]
    · zubv
      exec_block
      · omega
      · refine ztino
        config_simp; rw [o61, e29, ← hk, ← kOf_eq, ite_eq_right h]
  zubj
  have e22 : c₃.nreg 150022 = C.s := by
    rw [r₃ _ by_omega by_omega, r₂ _ by_omega, R₁.h22]
  have e26 : c₃.nreg 150026 = N := by
    rw [r₃ _ by_omega by_omega, r₂ _ by_omega, R₁.h26]
  -- `u`
  obtain ⟨c₄, k₄, e₄, hk₄, o64, r₄⟩ : ∃ c₄ k₄, Exec P W (.seq (.instr (.addN 150075 150022 150062))
      (.ifLtN 150075 150026 ztove
        ztnbi)) c₃ c₄ k₄ ∧ k₄ ≤ 4 ∧
      c₄.nreg 150064 = zttw % N ∧
      ∀ r, r ≠ 150064 → r ≠ 150075 → c₄.nreg r = c₃.nreg r := by
    refine spec_seq (spec_instr (Exec.addN w₃ _ _ _ by_omega) fun w' => ?_)
    by_cases h : C.s + k < N
    · refine spec_ifLtN_true (by config_simp; omega)
        (spec_instr ztlej fun _ => ztgsx)
      config_simp; rw [e22, o62, Nat.mod_eq_of_lt h]
    · refine spec_ifLtN_false (by config_simp; omega)
        (spec_instr ztemo fun _ => ztgsx)
      config_simp; rw [e22, o62, e26, Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_of_lt by_omega]
  zucc
  have f₄₃ : ∀ r, Bl [150061, 150062, 150063, 150064, 150075] r = false →
      c₄.nreg r = c₁.nreg r := by
    zuz
    have hne : ∀ a ∈ [150061, 150062, 150063, 150064, 150075], r ≠ a := fun a ha => ne_of_Bl hr ha
    rw [r₄ r zthhq zthhq, r₃ r zthhq zthhq,
      r₂ r zthhq]
  have R₄ := R₁.of_frame fun r hr => f₄₃ r (by
    zuvy
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have m₄ : c₄.nmem = m := by
    rw [← hm, ← f₁.2.2.1]
    exact (exec_frameB ztcb (B := Bl [150061, 150062, 150063, 150064, 150075])
      by_decide).2.2.1
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, found⟩ := itLook_exec (P := P) c₄ w₄ m₄ hH R₄.h21 R₄.h91 R₄.h93
    o64 haW by_omega ztcv
  have ex : Exec P W locV c c₅ ztbamf := by
    unfold locV
    exact .seq e₁ ztbq
  refine ⟨c₅, _, ex, by_omega, exec_frameB ex wr_locV, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₅.1 _ by_decide, f₄₃ _ by_decide, o60]
  · rw [f₅.1 _ by_decide, r₄ _ by_omega by_omega, r₃ _ by_omega by_omega, o61]
  · rw [f₅.1 _ by_decide, r₄ _ by_omega by_omega, o62]
  · rw [f₅.1 _ by_decide, r₄ _ by_omega by_omega, o63]
  · rw [f₅.1 _ by_decide, r₄ _ by_omega by_omega]; omega
  · rw [f₅.1 _ by_decide, o64]
  · rw [show c₅.nreg 150064 = zttw % N by rw [f₅.1 _ by_decide, o64]]
    omega
end
end ShootCut
@[expose] public section
open Machine Machine.Stmt Programs SignK
namespace ShootCut
def PcRegs (c : Config) (pc : Pc) : Prop :=
  c.nreg 150050 = pc.s.edge ∧ c.nreg 150051 = pc.s.hgt ∧ c.nreg 150052 = pc.e.edge ∧
    c.nreg 150053 = pc.e.hgt ∧ c.nreg 150054 = pc.kind ∧
    (pc.kind = 1 → c.nreg 150055 = pc.entry ∧ c.nreg 150056 = pc.x0 ∧ c.nreg 150057 = pc.dir ∧
      c.nreg 150058 = pc.pw)

/-- The registers of the core that `emit` keeps. -/
def Keep (r : ℕ) : Prop := ztbdq ∨ (150080 ≤ r ∧ r < 150100)

/-- The scratch registers of the core: `150020 …` of band `bCut`, the sign kernel (band `1`) and
the host routines (band `5`). -/
def Scr (r : ℕ) : Bool :=
  decide (150020 ≤ r ∧ r < 150100) || decide ztdew ||
    decide ztdfc

/-- **The contract of `emit`**: its invariant survives the core's scratch writes, and it extends
the list by any valid piece. -/
structure EmitOK (P : Polygon) (W : ℕ) (emit : Stmt) (A₀ : ℕ) (Pv : Pc → Prop)
    (I : List Pc → Config → Prop) (K : ℕ) : Prop where
  stable : ∀ ps c c', I ps c → FrameB Scr c c' → I ps c'
  run : ∀ ps pc c, WordsBounded W c → I ps c → PcRegs c pc → Pv pc →
    ∃ c' k, Exec P W emit c c' k ∧ k ≤ K ∧ I ztdvs c' ∧
      (∀ r, Keep r → c'.nreg r = c.nreg r) ∧ ztpt

/-- The list of pieces goes from `s` to the walk position `v`, consecutively. -/
def Chained : WPos → List Pc → WPos → Prop
  | s, [], v => s = v
  | s, pc :: ps, v => pc.s = s ∧ Chained pc.e ps v
theorem Chained.append {s v : WPos} : ∀ {ps : List Pc}, Chained s ps v → ∀ pc : Pc, pc.s = v →
    Chained s ztdvs pc.e
  | [], h, pc, hpc => by simp only [Chained] at h; subst h; tauto
  | _ :: _, h, pc, hpc => ⟨h.1, Chained.append h.2 pc hpc⟩

/-- The fixed registers of the core (after `cPre`). -/
structure CoreRegs (P : Polygon) (C : Chain) (H : Host) (Hh MD h γ mode : ℕ) (s e : WPos)
    (m₀ : ℕ → ℕ) (c : Config) : Prop where
  chain : ChainRegs C (H.pts P.n).length Hh c
  h00 : c.nreg 150000 = MD
  h01 : c.nreg 150001 = s.edge
  h02 : c.nreg 150002 = s.hgt
  h03 : c.nreg 150003 = e.edge
  h04 : c.nreg 150004 = e.hgt
  h09 : c.nreg 150009 = γ
  h13 : c.nreg 150013 = h
  h20 : c.nreg 150020 = mode
  h27 : c.nreg 150027 = P.n
  h31 : c.nreg 150031 = 2 * C.m + 5
  h32 : c.nreg 150032 = 2 * C.m + 6
  h33 : c.nreg 150033 = m₀ h
  h34 : c.nreg 150034 = m₀ zteu
  h35 : c.nreg 150035 = m₀ ztbba
  h36 : c.nreg 150036 = m₀ ztgn + 2
  h90 : c.nreg 150090 = 0
  h92 : c.nreg 150092 = 2
end ShootCut
end
namespace ShotList
open Machine SignK
@[expose] public section
variable {α : Type*} {p : Prop} {B : Finset ℕ} {Wr : ℕ → Prop} {m m' : ℕ → ℕ}
/-- `if` with a false condition (a simp lemma for a discharger). -/
theorem ite_no [Decidable p] (a b : α) (h : ¬ p) :
    ztfhz = b := by zumxk

/-- `if` with a true condition (a simp lemma for a discharger). -/
theorem ite_yes [Decidable p] (a b : α) (h : p) :
    ztfhz = a := by zumxk

/-- Register reads through `upd` with symbolic registers: conditions decided by `omega`. -/
macro "rsimp" : tactic =>
  `(tactic| simp (disch := omega) only [Chazelle.upd, ite_no, ite_yes, ↓reduceIte,
    Chazelle.Programs.Config.nreg_mk, Chazelle.Programs.Config.nmem_mk])

/-- **A frame with named registers**: `Frame B` except that the registers satisfying `Wr` may
also change. -/
def FrameR (B : Finset ℕ) (Wr : ℕ → Prop) (c c' : Config) (k : ℕ) : Prop :=
  (∀ r, bandOf r ∉ B → r ≠ ALLOC → ¬ Wr r → c'.nreg r = c.nreg r) ∧
    (∀ r, bandOf r ∉ B → ¬ Wr r → c'.rreg r = c.rreg r) ∧
    zth ∧
    ztgo ∧
    c'.output = c.output ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k
theorem FrameR.refl (B : Finset ℕ) (Wr : ℕ → Prop) (c : Config) : FrameR B Wr c c 0 :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, le_rfl, by_omega⟩
theorem FrameR.trans {c c₁ c₂ : Config} {k₁ k₂ : ℕ}
    (h₁ : FrameR B Wr c c₁ k₁) (h₂ : FrameR B Wr c₁ c₂ k₂) : FrameR B Wr c c₂ ztbct := by
  zugj

  refine ⟨fun r hr ha hw => ?_, fun r hr hw => ?_, fun a ha => ?_, fun a ha => ?_, o₂.trans o₁,
    a₁.trans a₂, by_omega⟩
  · simp_all
  · simp_all
  · grind
  grind
theorem FrameR.mono {B B' : Finset ℕ} {Wr Wr' : ℕ → Prop} {c c' : Config} {k k' : ℕ}
    (h : FrameR B Wr c c' k) (hB : B ⊆ B') (hW : ∀ r, Wr r → Wr' r) (hk : k ≤ k') :
    FrameR B' Wr' c c' k' := by
  zugw
  exact ⟨fun r hr ha hw => r₁ r ztdzv ha ztloc,
    fun r hr hw => rr₁ r ztdzv ztloc, m₁, rm₁, o₁, a₁,
    by omega⟩

/-- A register frame gives a named frame. -/
theorem FrameR.of_frameB {Bw : ℕ → Bool} {c c' : Config}
    (h : FrameB Bw c c') (hB : ∀ r, Bw r = true → Wr r ∨ bandOf r ∈ B) (hA : Bw ALLOC = false)
    (k : ℕ) : FrameR B Wr c c' k := by
  obtain ⟨r₁, rr₁, m₁, rm₁, o₁⟩ := h
  have hal := r₁ ALLOC hA
  refine ⟨fun r hr _ hw => r₁ r ?_, fun r hr hw => rr₁ r ?_, fun a _ => by zvmxn,
    fun a _ => by zunkf, o₁, by zuozi, by_omega⟩
  · grind
  grind

/-- A frame of the bands `B` is a named frame. -/
theorem FrameR.of_frame {c c' : Config} {k : ℕ}
    (h : Frame B c c' k) : FrameR B Wr c c' k := by
  zugw
  exact ⟨fun r hr ha _ => r₁ r hr ha, fun r hr _ => rr₁ r hr, m₁, rm₁, o₁, a₁, b₁⟩

/-! ## Descriptors below a bound survive memory changes above it -/

/-- A host layout below `E` survives a change of the memory at or above `E`. -/
theorem hostAt_agree {h E : ℕ} {H : Host} (hH : HostAt m h H)
    (hE : h + 3 * H.length + 4 ≤ E) (he : ∀ a, a < E → m' a = m a) : HostAt m' h H := by
  zugpa

  have := h1 i hi
  revert this
  cases H.getD i ztmn with
  | run a l =>
    zufq

  | pt x =>
    cases x with
    | vtx j => intro h; simp only at h ⊢; zundt; exact h
    | onEdge e j =>
      zufq

/-- **A copied chain descriptor** (host layout below `E`, the five words copied to `d`). -/
theorem chainDescAt_copy {bw d E : ℕ} {Q : Polygon} {H : Host} {C : Chain}
    (hC : ChainDescAt m bw Q H C) (hE : m bw + 3 * H.length + 4 ≤ E)
    (he : ∀ a, a < E → m' a = m a) (hc : ∀ j, j < 5 → m' ztfqu = m ztctz) :
    ChainDescAt m' d Q H C := by
  zumm

  refine ⟨?_, h1, by_omega, by_omega, by_omega,
    by simp_all⟩
  zuhkr

/-- **A well-formed copy of a chain descriptor.** -/
theorem chainWF_copy {P : Polygon} {m m' : ℕ → ℕ} {bw d E E' : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw zta H C)
    (he : ∀ a, a < E → m' a = m a) (hc : ∀ j, j < 5 → m' ztfqu = m ztctz)
    (hd : d + 5 ≤ E') (hEE : E ≤ E') : ChainWF P E' m' d := by
  zuhi

  zubvz
