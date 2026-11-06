module

public import Chazelle.Core.GranInitL1

/-!
# WP-F, init part 8: the class arrays

For every region record `r < R`: `deg r`, `wt r`, the exit base `exb r = b0 + oEx + D r` and the
`D` exit slots (the exit chords of the region, then zeros) (`regLoop_exec`).
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- The region data expected in memory: degree, weight, exits. -/
structure RegRec (m : ℕ → ℕ) (RB LB r dg w : ℕ) (ex : List ℕ) : Prop where
  deg : m (RB + 5 * r + 2) = dg
  wt : m (RB + 5 * r + 4) = w
  lst : ∀ t, t < dg → m (LB + m (RB + 5 * r + 3) + t) = ex.getD t 0
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
  slot : ∀ u, u < c.nreg 90081 → c.nmem (S + u) = ex.getD u 0
  mem : ∀ a, (a < S ∨ S + D ≤ a) → c.nmem a = c₀.nmem a

theorem slotLoop_exec {P : Polygon} {W D S L deg : ℕ} {ex : List ℕ} {c₀ : Config}
    (hw : WordsBounded W c₀) (h81 : c₀.nreg 90081 = 0) (h02 : c₀.nreg 90002 = D)
    (h78 : c₀.nreg 90078 = S) (h79 : c₀.nreg 90079 = deg) (h80 : c₀.nreg 90080 = L)
    (h19 : c₀.nreg 90019 = 1) (hlen : ex.length = deg) (_hdeg : deg ≤ D)
    (hsrc : ∀ t, t < deg → c₀.nmem (L + t) = ex.getD t 0)
    (hdisj : ∀ t, t < deg → L + t < S ∨ S + D ≤ L + t) (hSW : S + D ≤ W) (hLW : L + deg ≤ W) :
    ∃ c' k, Exec P W slotLoop c₀ c' k ∧ k ≤ 9 * D + 2 ∧
      (∀ u, u < D → c'.nmem (S + u) = ex.getD u 0) ∧
      (∀ a, (a < S ∨ S + D ≤ a) → c'.nmem a = c₀.nmem a) ∧
      (∀ r, r ≠ 90081 → r ≠ 90082 → r ≠ 90083 → r ≠ 90084 → c'.nreg r = c₀.nreg r) := by
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90081) (b := 90002)
    (body := slotBody) (SlotI W D S L deg ex c₀) (fun c => D - c.nreg 90081) 7 (fun _ h => h.wb)
    (fun c I ht => by
      obtain ⟨hwc, hle, hr, hs, hm⟩ := I
      rw [hr 90002 (by decide) (by decide) (by decide) (by decide), h02] at ht
      have c78 : c.nreg 90078 = S := by rw [hr _ (by decide) (by decide) (by decide) (by decide), h78]
      have c79 : c.nreg 90079 = deg := by
        rw [hr _ (by decide) (by decide) (by decide) (by decide), h79]
      have c80 : c.nreg 90080 = L := by rw [hr _ (by decide) (by decide) (by decide) (by decide), h80]
      have c19 : c.nreg 90019 = 1 := by
        rw [hr _ (by decide) (by decide) (by decide) (by decide), h19]
      generalize htu : c.nreg 90081 = t at ht hle hs
      have e₁ := Exec.addN (P := P) hwc 90082 90078 90081 (by rw [c78, htu]; omega)
      set c₁ : Config := { c with nreg := upd c.nreg 90082 (c.nreg 90078 + c.nreg 90081) } with hc₁
      have w₁ : WordsBounded W c₁ := e₁.wb_right
      have d82 : c₁.nreg 90082 = S + t := by rw [hc₁]; simp [upd, c78, htu]
      have d81 : c₁.nreg 90081 = t := by rw [hc₁]; simp [upd, htu]
      have d79 : c₁.nreg 90079 = deg := by rw [hc₁]; simp [upd, c79]
      have d80 : c₁.nreg 90080 = L := by rw [hc₁]; simp [upd, c80]
      have d19 : c₁.nreg 90019 = 1 := by rw [hc₁]; simp [upd, c19]
      have dm : c₁.nmem = c.nmem := rfl
      -- the store of the slot value
      obtain ⟨c₂, k₂, e₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 90081 90079
          (block [.addN 90083 90080 90081, .loadN 90084 90083, .storeN 90082 90084])
          (block [.constN 90084 0, .storeN 90082 90084])) c₁ c₂ k₂ ∧ k₂ ≤ 4 ∧
          (c₂.nmem = upd c.nmem (S + t) (ex.getD t 0) ∧
            ∀ r, r ≠ 90083 → r ≠ 90084 → c₂.nreg r = c₁.nreg r) := by
        by_cases hlt : t < deg
        · refine spec_ifLtN_true (by rw [d81, d79]; exact hlt) ?_
          exec_block
          · rw [d80, d81]; omega
          · refine ⟨by omega, ?_, fun r a1 a2 => by simp [upd, a1, a2]⟩
            config_simp
            rw [d82, d80, d81, dm, hm _ (hdisj t hlt), hsrc t hlt]
        · refine spec_ifLtN_false (by rw [d81, d79]; exact hlt) ?_
          exec_block
          · omega
          · refine ⟨by omega, ?_, fun r a1 a2 => by simp [upd, a2]⟩
            config_simp
            rw [d82, dm, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      obtain ⟨q2, qr⟩ := q
      have w₂ := e₂.wb_right
      have f19 : c₂.nreg 90019 = 1 := by rw [qr _ (by decide) (by decide), d19]
      have f81 : c₂.nreg 90081 = t := by rw [qr _ (by decide) (by decide), d81]
      have e₃ := Exec.addN (P := P) w₂ 90081 90081 90019 (by rw [f19, f81]; omega)
      refine ⟨_, _, .seq e₁ (.seq e₂ e₃), ⟨e₃.wb_right, ?_, fun r a1 a2 a3 a4 => ?_,
        fun u hu => ?_, fun a ha => ?_⟩, by omega, ?_⟩
      · config_simp; rw [f19, f81]; omega
      · config_simp
        rw [Machine.upd_other _ _ _ a1, qr r a3 a4, hc₁]
        simp only [upd, a2, ite_false]
        exact hr r a1 a2 a3 a4
      · config_simp at hu; rw [f19, f81] at hu
        config_simp; rw [q2]
        by_cases hut : u = t
        · rw [hut]; simp
        · rw [Machine.upd_other _ _ _ (by omega)]; exact hs u (by omega)
      · config_simp; rw [q2, Machine.upd_other _ _ _ (by omega)]; exact hm a ha
      · config_simp; rw [f19, f81]; omega)
    ⟨hw, by omega, fun _ _ _ _ _ => rfl, fun u hu => by rw [h81] at hu; omega, fun _ _ => rfl⟩
  have hfull : c'.nreg 90081 = D := by
    rw [I'.regs 90002 (by decide) (by decide) (by decide) (by decide), h02] at hx
    have := I'.t_le; omega
  refine ⟨c', k, e, ?_, fun u hu => I'.slot u (by omega), I'.mem, I'.regs⟩
  rw [h81] at hk
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

theorem wrS_regLoop : wrS Binit regLoop = true := by decide

set_option maxHeartbeats 1000000 in
theorem regHead_exec {P : Polygon} {W : ℕ} {d : Dm} (c : Config) (hw : WordsBounded W c)
    {RB LB r S dg w : ℕ} {ex : List ℕ} (hB : Bases c d) (h70 : c.nreg 90070 = r)
    (h71 : c.nreg 90071 = RB + 5 * r) (h78 : c.nreg 90078 = S) (_h22 : c.nreg 90022 = LB)
    (h19 : c.nreg 90019 = 1) (h20 : c.nreg 90020 = 3) (h21 : c.nreg 90021 = 2)
    (hrec : RegRec c.nmem RB LB r dg w ex) (hr : r < d.R) (hRB : RB + 5 * r + 5 ≤ d.b0)
    (hW : d.b0 + d.oEnd ≤ W) :
    ∃ c' k, Exec P W regHead c c' k ∧ k = 13 ∧ c'.nreg 90079 = dg ∧
      c'.nreg 90080 = c.nmem (RB + 5 * r + 3) ∧ c'.nreg 90081 = 0 ∧
      c'.nmem = upd (upd (upd c.nmem (d.b0 + d.oDeg + r) dg) (d.b0 + d.oWt + r) w)
        (d.b0 + d.oExb + r) S ∧
      (∀ q, q ≠ 90072 → q ≠ 90074 → q ≠ 90075 → q ≠ 90079 → q ≠ 90080 → q ≠ 90081 →
        c'.nreg q = c.nreg q) := by
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩ := d.lay
  have hEx : d.oEx ≤ d.oEnd := by omega
  have v1 : upd c.nmem (d.b0 + d.oDeg + r) dg (RB + 5 * r + 3) = c.nmem (RB + 5 * r + 3) :=
    Machine.upd_other _ _ _ (by omega)
  have v2 : upd c.nmem (d.b0 + d.oDeg + r) dg (RB + 5 * r + 3 + 1) = w := by
    rw [Machine.upd_other _ _ _ (by omega)]; exact hrec.wt
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
  deg : ∀ x, x < c.nreg 90070 → c.nmem (d.b0 + d.oDeg + x) = (rg x).chords.length
  wt : ∀ x, x < c.nreg 90070 → c.nmem (d.b0 + d.oWt + x) = (rg x).wt
  exb : ∀ x, x < c.nreg 90070 → c.nmem (d.b0 + d.oExb + x) = d.b0 + d.oEx + D * x
  ex : ∀ x t, x < c.nreg 90070 → t < D → c.nmem (d.b0 + d.oEx + D * x + t) =
    (rg x).chords.getD t 0
  mem : ∀ a, (a < d.b0 + d.oDeg ∨ d.b0 + d.oCnt ≤ a) → c.nmem a = c₀.nmem a

theorem regBody_exec {P : Polygon} {W R D RB LB : ℕ} {d : Dm} {rg : ℕ → RRec} {c₀ c : Config}
    (hI : RegI W R D RB d rg c₀ c) (hB : Bases c₀ d) (hR : d.R = R) (hD : d.D = D)
    (h02 : c₀.nreg 90002 = D) (h12 : c₀.nreg 90012 = R) (h22 : c₀.nreg 90022 = LB)
    (h19 : c₀.nreg 90019 = 1) (h20 : c₀.nreg 90020 = 3) (h21 : c₀.nreg 90021 = 2)
    (hrec : ∀ r, r < R → RegRec c₀.nmem RB LB r (rg r).chords.length (rg r).wt (rg r).chords)
    (hdeg : ∀ r, r < R → (rg r).chords.length ≤ D) (hRB : RB + 5 * R ≤ d.b0)
    (hL : ∀ r, r < R → 1 ≤ (rg r).chords.length →
      LB + c₀.nmem (RB + 5 * r + 3) + (rg r).chords.length ≤ d.b0)
    (hW : d.b0 + d.oEnd ≤ W) (ht : c.nreg 90070 < R) :
    ∃ c' k, Exec P W regBody c c' k ∧ RegI W R D RB d rg c₀ c' ∧ k ≤ 9 * D + 22 ∧
      c'.nreg 90070 = c.nreg 90070 + 1 := by
  obtain ⟨hw, hle, hp, hsl, h76, hr, hdg, hwt, hexb, hex, hm⟩ := hI
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩ := d.lay
  rw [hR] at y1
  rw [hR, hD] at y2 y10
  generalize hrr : c.nreg 90070 = r at ht hle hp hsl hdg hwt hexb hex
  have hs := slot_le (R := R) (D := D) (x := r) ht (le_refl _)
  have hrc := hrec r ht
  have hdr := hdeg r ht
  have hLr := hL r ht
  -- the record reads are below `b0`
  have hrc' : RegRec c.nmem RB LB r (rg r).chords.length (rg r).wt (rg r).chords := by
    obtain ⟨a1, a2, a3, a4⟩ := hrc
    have e3 : c.nmem (RB + 5 * r + 3) = c₀.nmem (RB + 5 * r + 3) := hm _ (by left; omega)
    refine ⟨by rw [hm _ (by left; omega)]; exact a1, by rw [hm _ (by left; omega)]; exact a2,
      fun t ht' => ?_, a4⟩
    rw [e3, hm _ (by left; omega)]; exact a3 t ht'
  have e3 : c.nmem (RB + 5 * r + 3) = c₀.nmem (RB + 5 * r + 3) := hm _ (by left; omega)
  have hBc : Bases c d := hB.frame fun q a1 a2 => hr q (by simp [Binit]; omega)
  obtain ⟨c₁, k₁, e₁, hk₁, q79, q80, q81, qm, qr⟩ := regHead_exec (P := P) (d := d) c hw
    (S := d.b0 + d.oEx + D * r) hBc hrr hp hsl (by rw [hr _ (by decide), h22])
    (by rw [hr _ (by decide), h19]) (by rw [hr _ (by decide), h20]) (by rw [hr _ (by decide), h21])
    hrc' (by rw [hR]; exact ht) (by omega) hW
  have w₁ := e₁.wb_right
  -- the list base
  set L' := if (rg r).chords.length = 0 then 0 else LB + c.nmem (RB + 5 * r + 3) with hL'
  have l19 : c₁.nreg 90019 = 1 := by
    rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hr _ (by decide), h19]
  have l22 : c₁.nreg 90022 = LB := by
    rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hr _ (by decide), h22]
  obtain ⟨c₁', k₁', e₁', hk₁', v80, vr, vm⟩ : ∃ c₁' k₁', Exec P W regL c₁ c₁' k₁' ∧ k₁' ≤ 3 ∧
      c₁'.nreg 90080 = L' ∧ (∀ q, q ≠ 90080 → c₁'.nreg q = c₁.nreg q) ∧ c₁'.nmem = c₁.nmem := by
    unfold regL
    by_cases h0 : (rg r).chords.length = 0
    · exact ⟨_, _, .ifLtN_true (by rw [q79, l19, h0]; omega) (Exec.constN w₁ _ _ (by omega)),
        by omega, by simp [upd, hL', h0], fun q hq => by simp [upd, hq], rfl⟩
    · have hLr' := hLr (by omega)
      exact ⟨_, _, .ifLtN_false (by rw [q79, l19]; omega)
        (Exec.addN w₁ 90080 90080 90022 (by rw [q80, l22, e3]; omega)), by omega,
        by simp [upd, hL', h0, q80, l22]; ring, fun q hq => by simp [upd, hq], rfl⟩
  have w₁' := e₁'.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, s₂, m₂, r₂⟩ := slotLoop_exec (P := P) (D := D)
    (S := d.b0 + d.oEx + D * r) (L := L')
    (deg := (rg r).chords.length) (ex := (rg r).chords) w₁'
    (by rw [vr _ (by decide), q81])
    (by rw [vr _ (by decide), qr _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hr _ (by decide), h02])
    (by rw [vr _ (by decide), qr _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hsl])
    (by rw [vr _ (by decide), q79]) v80 (by rw [vr _ (by decide), l19]) rfl hdr
    (fun t ht' => by
      have hLr' := hLr (by omega)
      rw [vm, hL', ite_eq_right (by omega), qm, Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega), e3,
        hm _ (by left; omega)]
      exact hrc.lst t ht')
    (fun t ht' => by
      have hLr' := hLr (by omega)
      left; rw [hL', ite_eq_right (by omega), e3]; omega)
    (by omega)
    (by
      rw [hL']
      split_ifs with h0
      · omega
      · have hLr' := hLr (by omega); rw [e3]; omega)
  have w₂ := e₂.wb_right
  have g : ∀ q, q ≠ 90072 → q ≠ 90074 → q ≠ 90075 → q ≠ 90079 → q ≠ 90080 → q < 90081 ∨
      90084 < q → c₂.nreg q = c.nreg q := fun q a1 a2 a3 a4 a5 a6 => by
    rw [r₂ q (by omega) (by omega) (by omega) (by omega), vr q a5, qr q a1 a2 a3 a4 a5 (by omega)]
  have f78 := g 90078 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have f71 := g 90071 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have f70 := g 90070 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have f02 := g 90002 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have f76 := g 90076 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have f19 := g 90019 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [hsl] at f78; rw [hp] at f71; rw [hrr] at f70; rw [hr _ (by decide), h02] at f02
  rw [h76] at f76; rw [hr _ (by decide), h19] at f19
  have hD1 : D * r + D ≤ R * D := by
    have := slot_le (R := R) (D := D) (x := r) ht (le_refl _); omega
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ : ∃ c₃ k₃, Exec P W regTail c₂ c₃ k₃ ∧ k₃ = 3 ∧
      (c₃.nreg 90078 = d.b0 + d.oEx + D * (r + 1) ∧ c₃.nreg 90071 = RB + 5 * (r + 1) ∧
        c₃.nreg 90070 = r + 1 ∧ (∀ q, q ≠ 90078 → q ≠ 90071 → q ≠ 90070 → c₃.nreg q = c₂.nreg q) ∧
        c₃.nmem = c₂.nmem) := by
    unfold regTail
    exec_block
    · rw [f78, f02]; omega
    · config_simp; rw [f71, f76]; omega
    · config_simp; rw [f70, f19]; omega
    · refine ⟨rfl, ?_, ?_, ?_, fun q a1 a2 a3 => by simp [upd, a1, a2, a3], rfl⟩ <;> config_simp
      · rw [f78, f02, Nat.mul_succ]; ring
      · rw [f71, f76]; ring
      · rw [f70, f19]
  obtain ⟨q78, q71, q70, qr₃, qm₃⟩ := q
  refine ⟨c₃, _, .seq e₁ (.seq e₁' (.seq e₂ e₃)), ⟨e₃.wb_right, by omega, by rw [q70, q71],
    by rw [q70, q78], ?_, fun q hq => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_,
    fun x t hx htD => ?_, fun a ha => ?_⟩, by omega, by rw [q70]⟩
  · rw [qr₃ _ (by decide) (by decide) (by decide), g _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h76]
  · simp only [Binit, decide_eq_false_iff_not] at hq
    rw [qr₃ _ (by omega) (by omega) (by omega), g _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), hr q (by simp [Binit]; omega)]
  · rw [q70] at hx
    rw [qm₃, m₂ _ (by left; omega), vm, qm]
    by_cases hxr : x = r
    · subst hxr
      rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]; simp
    · rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega)]
      exact hdg x (by omega)
  · rw [q70] at hx
    rw [qm₃, m₂ _ (by left; omega), vm, qm]
    by_cases hxr : x = r
    · subst hxr
      rw [Machine.upd_other _ _ _ (by omega)]; simp
    · rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega)]
      exact hwt x (by omega)
  · rw [q70] at hx
    rw [qm₃, m₂ _ (by left; omega), vm, qm]
    by_cases hxr : x = r
    · subst hxr; simp
    · rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega)]
      exact hexb x (by omega)
  · rw [q70] at hx
    rw [qm₃]
    by_cases hxr : x = r
    · subst hxr; exact s₂ t htD
    · have h1 : D * (x + 1) ≤ D * r := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at h1
      rw [m₂ _ (by left; omega), vm, qm, Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]
      exact hex x t (by omega) htD
  · rw [qm₃, m₂ _ (by rcases ha with h | h <;> [left; right] <;> omega), vm, qm,
      Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      Machine.upd_other _ _ _ (by omega)]
    exact hm a ha

theorem regLoop_exec {P : Polygon} {W R D RB LB : ℕ} {d : Dm} {rg : ℕ → RRec} {c₀ : Config}
    (hw : WordsBounded W c₀) (hB : Bases c₀ d) (hR : d.R = R) (hD : d.D = D)
    (h02 : c₀.nreg 90002 = D) (h12 : c₀.nreg 90012 = R) (h16 : c₀.nreg 90016 = RB)
    (h22 : c₀.nreg 90022 = LB) (h27 : c₀.nreg 90027 = d.b0 + d.oEx)
    (h19 : c₀.nreg 90019 = 1) (h20 : c₀.nreg 90020 = 3) (h21 : c₀.nreg 90021 = 2)
    (hrec : ∀ r, r < R → RegRec c₀.nmem RB LB r (rg r).chords.length (rg r).wt (rg r).chords)
    (hdeg : ∀ r, r < R → (rg r).chords.length ≤ D) (hRB : RB + 5 * R ≤ d.b0)
    (hL : ∀ r, r < R → 1 ≤ (rg r).chords.length →
      LB + c₀.nmem (RB + 5 * r + 3) + (rg r).chords.length ≤ d.b0)
    (hW : d.b0 + d.oEnd ≤ W) (hW5 : 5 ≤ W) :
    ∃ c' k, Exec P W regLoop c₀ c' k ∧ k ≤ (9 * D + 24) * R + 6 ∧
      (∀ x, x < R → c'.nmem (d.b0 + d.oDeg + x) = (rg x).chords.length ∧
        c'.nmem (d.b0 + d.oWt + x) = (rg x).wt ∧
        c'.nmem (d.b0 + d.oExb + x) = d.b0 + d.oEx + D * x ∧
        ∀ t, t < D → c'.nmem (d.b0 + d.oEx + D * x + t) = (rg x).chords.getD t 0) ∧
      (∀ a, (a < d.b0 + d.oDeg ∨ d.b0 + d.oCnt ≤ a) → c'.nmem a = c₀.nmem a) ∧
      FrameS Binit c₀ c' := by
  suffices hh : ∃ c' k, Exec P W regLoop c₀ c' k ∧ k ≤ (9 * D + 24) * R + 6 ∧
      (∀ x, x < R → c'.nmem (d.b0 + d.oDeg + x) = (rg x).chords.length ∧
        c'.nmem (d.b0 + d.oWt + x) = (rg x).wt ∧
        c'.nmem (d.b0 + d.oExb + x) = d.b0 + d.oEx + D * x ∧
        ∀ t, t < D → c'.nmem (d.b0 + d.oEx + D * x + t) = (rg x).chords.getD t 0) ∧
      (∀ a, (a < d.b0 + d.oDeg ∨ d.b0 + d.oCnt ≤ a) → c'.nmem a = c₀.nmem a) by
    obtain ⟨c', k, e, h1, h2, h3⟩ := hh
    exact ⟨c', k, e, h1, h2, h3, exec_frameS e wrS_regLoop⟩
  obtain ⟨c₁, k₁, e₁, hk₁, q, q0⟩ : ∃ c₁ k₁, Exec P W (block [.constN 90070 0, .copyN 90071 90016,
      .copyN 90078 90027, .constN 90076 5]) c₀ c₁ k₁ ∧ k₁ = 4 ∧ RegI W R D RB d rg c₀ c₁ ∧
      c₁.nreg 90070 = 0 := by
    exec_block
    · omega
    · omega
    · refine ⟨rfl, ⟨by assumption, ?_, ?_, ?_, ?_, fun r hr => ?_, fun x hx => ?_, fun x hx => ?_,
        fun x hx => ?_, fun x t hx _ => ?_, fun a _ => rfl⟩, ?_⟩
      · config_simp; omega
      · config_simp; rw [h16]; omega
      · config_simp; rw [h27]; omega
      · config_simp
      · simp only [Binit, decide_eq_false_iff_not] at hr
        config_simp; simp only [upd]; split_ifs <;> first | rfl | omega
      all_goals first | (simp [upd] at hx) | config_simp
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90070) (b := 90012)
    (body := regBody) (RegI W R D RB d rg c₀) (fun c => R - c.nreg 90070) (9 * D + 22)
    (fun _ h => h.wb)
    (fun c I ht => by
      have t : c.nreg 90070 < R := by rw [I.regs 90012 (by decide), h12] at ht; exact ht
      obtain ⟨c', k, e, I', hk, hi⟩ := regBody_exec (P := P) I hB hR hD h02 h12 h22 h19 h20 h21
        hrec hdeg hRB hL hW t
      exact ⟨c', k, e, I', hk, by omega⟩) q
  have hK' : c'.nreg 90070 = R := by
    rw [I'.regs 90012 (by decide), h12] at hx; have := I'.r_le; omega
  refine ⟨c', _, .seq e₁ e, ?_, fun x hx => ⟨I'.deg x (by omega), I'.wt x (by omega),
    I'.exb x (by omega), fun t ht => I'.ex x t (by omega) ht⟩, I'.mem⟩
  rw [q0] at hk
  have : (9 * D + 22 + 2) * (R - 0) = (9 * D + 24) * R := by rw [Nat.sub_zero]
  omega

end

end Gran

end Chazelle.Core
