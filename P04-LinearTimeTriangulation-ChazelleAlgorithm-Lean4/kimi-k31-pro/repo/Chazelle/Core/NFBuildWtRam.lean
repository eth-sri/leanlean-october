module

public import Chazelle.Core.NFBuildWt
public import Chazelle.Core.NFBuildCmpRam
public import Chazelle.Core.GranPzExec

/-!
# WP-C (BuildNF), RAM part 6: the weights of the arcs

* `wtF`: the closed form `arcWtNat` with the ceiling of the end key replaced by `eb + pz`, where
  `pz = 1` iff the end edge is counted and the end is strictly inside it; `arcWtNat_eq_wtF`.
* `countedIv`: the counted edges of a described model form the interval `[lo, hi)` read off the
  descriptor (`[6, 2m + 6)` for a chain, `[0, n)` for the interior).
* `lohiS_exec`: the interval on the machine (`r44020 = lo`, `r44021 = hi - lo`, and `r41023` the model
  kind, `r41019 = 1` for the parameter test).
* `pzR_exec`: the parameter test of WP-F (`Gran.pzStmt`) in band `bBuild`.
* `wtS_exec`: `wtF` on the machine, in coordinates shifted by `lo` (`wtG`, `wtF_eq_wtG`), so
  that no intermediate value exceeds the word bound.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK WalkKey NFLoc

@[expose] public section

/-! ## The closed form with the parameter bit -/

/-- The weight from the edges, the parameter bit `pz` of the end and the order bit `lt`. -/
def wtF (lo hi ea eb pz lt : ℕ) : ℕ :=
  if lt = 1 then min (eb + pz) hi - max ea lo else (hi - lo) - (min ea hi - max (eb + pz) lo)

/-- **The parameter bit replaces the ceiling** (off the counted interval the ceiling does not
matter). -/
theorem arcWtNat_eq_wtF {lo hi ea eb pz lt : ℕ} {fa fb : ℝ} {counted : ℕ → Prop}
    (hc : counted eb ↔ lo ≤ eb ∧ eb < hi) (hpz : pz = 1 ↔ counted eb ∧ fb ≠ 0) (hpz1 : pz ≤ 1)
    (hlt : lt = 1 ↔ (ea : ℝ) + fa < eb + fb) :
    arcWtNat lo hi ea fa eb fb = wtF lo hi ea eb pz lt := by
  unfold arcWtNat wtF keyCeil
  by_cases hl : (ea : ℝ) + fa < eb + fb
  · rw [ite_eq_left hl, ite_eq_left (hlt.2 hl)]
    by_cases hcb : counted eb
    · by_cases hf : fb = 0
      · have : pz = 0 := by
          by_contra h; have := hpz.1 (by omega); exact this.2 hf
        rw [ite_eq_left hf, this, Nat.add_zero]
      · have : pz = 1 := hpz.2 ⟨hcb, hf⟩
        rw [ite_eq_right hf, this]
    · have : pz = 0 := by by_contra h; exact hcb (hpz.1 (by omega)).1
      rw [this, Nat.add_zero]
      have hn := (not_congr hc).1 hcb
      split_ifs <;> omega
  · rw [ite_eq_right hl, ite_eq_right (fun h => hl (hlt.1 h))]
    by_cases hcb : counted eb
    · by_cases hf : fb = 0
      · have : pz = 0 := by
          by_contra h; have := hpz.1 (by omega); exact this.2 hf
        rw [ite_eq_left hf, this, Nat.add_zero]
      · have : pz = 1 := hpz.2 ⟨hcb, hf⟩
        rw [ite_eq_right hf, this]
    · have : pz = 0 := by by_contra h; exact hcb (hpz.1 (by omega)).1
      rw [this, Nat.add_zero]
      have hn := (not_congr hc).1 hcb
      split_ifs <;> omega

/-- The counted interval of a described model. -/
def loOf (m : ℕ → ℕ) (D : ℕ) : ℕ := if m D = 0 then 6 else 0

/-- The end of the counted interval of a described model. -/
def hiOf (m : ℕ → ℕ) (D n : ℕ) : ℕ := if m D = 0 then 2 * m (D + 3) + 6 else n

/-- **The counted edges of a described model** form `[loOf, hiOf)`, within the walk. -/
theorem countedIv {m : ℕ → ℕ} {D : ℕ} {P : Polygon} {M : Model}
    (hM : ModelDescAt m D (Qof P) M) :
    (∀ p, p < M.W.n → (M.counted p ↔ loOf m D ≤ p ∧ p < hiOf m D P.n)) ∧
      hiOf m D P.n ≤ M.W.n := by
  rcases hM with ⟨h0, H, C, hC, rfl⟩ | ⟨h1, -, rfl⟩
  · have hm : m (D + 1 + 2) = C.m := hC.2.2.2.1
    unfold loOf hiOf
    rw [ite_eq_left h0, ite_eq_left h0, show D + 3 = D + 1 + 2 by omega, hm, chainModel_n]
    exact ⟨fun p hp => chainModel_counted_iff C p (by rw [chainModel_n]; exact hp), by omega⟩
  · have hn : (Qof P).n = P.n := shear_n _ _
    unfold loOf hiOf
    rw [ite_eq_right (by omega), ite_eq_right (by omega), interiorModel_n, hn]
    refine ⟨fun p hp => ?_, le_rfl⟩
    rw [interiorModel_counted_iff _ p (by rw [interiorModel_n, hn]; exact hp), hn]

/-! ## The counted interval on the machine -/

/-- The length of the counted interval of a described model. -/
def hdOf (m : ℕ → ℕ) (D n : ℕ) : ℕ := if m D = 0 then 2 * m (D + 3) else n

theorem hdOf_eq (m : ℕ → ℕ) (D n : ℕ) : hdOf m D n = hiOf m D n - loOf m D := by
  unfold hdOf hiOf loOf; split_ifs <;> omega

/-- The counted interval: `r44020 = lo`, `r44021 = hi - lo`; also `r41023` the model kind and
`r41019 = 1` (the parameter test reads them). -/
def lohiS : Stmt :=
  .seq (block [.loadN 41023 40000, .constN 41019 1])
    (.ifLtN 41023 41019
      (block [.constN 44020 6, .constN 44022 3, .addN 44022 44022 40000, .loadN 44021 44022,
        .addN 44021 44021 44021])
      (block [.constN 44020 0, .inputSize 44021]))

theorem wr_lohiS : wr (fun r => decide (r = 41023 ∨ r = 41019 ∨ r = 44020 ∨ r = 44021 ∨
    r = 44022)) lohiS = true := by decide

/-- **The counted interval on the machine.** -/
theorem lohiS_exec {P : Polygon} {W : ℕ} (d : Config) (hw : WordsBounded W d) {D : ℕ}
    (hD : d.nreg 40000 = D) (hW : d.nmem D = 0 → 2 * d.nmem (D + 3) ≤ W)
    (hDW : D + 3 ≤ W) (hn : P.n ≤ W) (h6 : 6 ≤ W) :
    ∃ d' k, Exec P W lohiS d d' k ∧ k ≤ 12 ∧
      d'.nreg 44020 = loOf d.nmem D ∧ d'.nreg 44021 = hdOf d.nmem D P.n ∧
      d'.nreg 41023 = d.nmem D ∧ d'.nreg 41019 = 1 ∧
      FrameB (fun r => decide (r = 41023 ∨ r = 41019 ∨ r = 44020 ∨ r = 44021 ∨ r = 44022)) d d' := by
  suffices H : ∃ d' k, Exec P W lohiS d d' k ∧ k ≤ 12 ∧
      d'.nreg 44020 = loOf d.nmem D ∧ d'.nreg 44021 = hdOf d.nmem D P.n ∧
      d'.nreg 41023 = d.nmem D ∧ d'.nreg 41019 = 1 by
    obtain ⟨d', k, x, hk, h1, h2, h3, h4⟩ := H
    exact ⟨d', k, x, hk, h1, h2, h3, h4, exec_frameB x wr_lohiS⟩
  unfold lohiS
  refine spec_seq ?_
  exec_block
  · omega
  by_cases h0 : d.nmem D = 0
  · have hW' := hW h0
    refine spec_ifLtN_true (by config_simp; rw [hD, h0]; omega) ?_
    exec_block
    · omega
    · omega
    · config_simp; rw [hD]; omega
    · config_simp; rw [hD, show 3 + D = D + 3 by omega]; omega
    · refine ⟨by omega, ?_, ?_, ?_, rfl⟩ <;> config_simp
      · unfold loOf; rw [ite_eq_left h0]
      · unfold hdOf; rw [ite_eq_left h0, hD, show 3 + D = D + 3 by omega]; ring
      · rw [hD]
  · refine spec_ifLtN_false (by config_simp; rw [hD]; omega) ?_
    exec_block
    · omega
    · omega
    · refine ⟨by omega, ?_, ?_, ?_, rfl⟩ <;> config_simp
      · unfold loOf; rw [ite_eq_right h0]
      · unfold hdOf; rw [ite_eq_right h0]
      · rw [hD]

/-! ## The parameter test in band `bBuild` -/

/-- `Gran.pzStmt` renamed into band `bBuild` (`r41110`, `r41111` in, `r41112` out). -/
def pzR : Stmt := Stmt.ren σ Gran.pzStmt

/-- The registers `pzR` writes. -/
def BpzR (r : ℕ) : Bool := Gran.Bpz (σ r)

theorem wr_pzR : wr BpzR pzR = true := by
  rw [pzR, wr_ren σ_σ]
  have : (fun r => BpzR (σ r)) = Gran.Bpz := by funext r; simp [BpzR, σ_σ]
  rw [this]; exact Gran.wr_pzStmt

theorem BpzR_true {r : ℕ} (h : BpzR r = true) :
    (10000 ≤ r ∧ r < 10503) ∨ (40000 < r ∧ r < 40100) ∨ (41110 ≤ r ∧ r < 41120) := by
  simp only [BpzR, Gran.Bpz, Bdir, Bool.or_eq_true, decide_eq_true_eq] at h
  unfold σ at h
  split_ifs at h <;> omega

/-- **The parameter test**: `r41112 = 1` iff the edge `r41110` is counted and the position
`⟨r41110, r41111⟩` has a nonzero parameter. -/
theorem pzR_exec {P : Polygon} {W : ℕ} {M : Model} (hG : GoodEnv P) (hW : P.n + 3 ≤ W)
    (d : Config) (hw : WordsBounded W d) {D e h : ℕ} (h40 : d.nreg 40000 = D)
    (hM : ModelDescAt d.nmem D (Qof P) M) (h23 : d.nreg 41023 = d.nmem D)
    (h19 : d.nreg 41019 = 1) (h110 : d.nreg 41110 = e) (h111 : d.nreg 41111 = h)
    (he : e < M.W.n) (hh : h ≤ P.n) (hDW : D + 6 ≤ W) (hCW : LocChainWF P W d.nmem D) :
    ∃ d' k, Exec P W pzR d d' k ∧ k ≤ 6000 ∧ FrameB BpzR d d' ∧ d'.nreg 41112 ≤ 1 ∧
      (d'.nreg 41112 = 1 ↔ M.counted e ∧ M.param (Qof P) ⟨e, h⟩ ≠ 0) := by
  have hw' : WordsBounded W (cfgRen σ d) := (wordsBounded_ren σ_σ d).2 hw
  obtain ⟨c', k, ex, hk, hfr, h1, h2⟩ := Gran.pz_exec (P := P) (W := W) hG hW (cfgRen σ d) hw'
    (MD := D) (e := e) (h := h) h40 hM h23 h19 h110 h111 he hh hDW hCW
  refine ⟨cfgRen σ c', k, exec_of_ren σ_σ ex, hk, ⟨fun r hr => ?_, fun r hr => ?_, hfr.2.2.1,
    hfr.2.2.2.1, hfr.2.2.2.2⟩, h1, h2⟩
  · have := hfr.1 (σ r) hr
    simp only [cfgRen_nreg, σ_σ] at this ⊢
    exact this
  · have := hfr.2.1 (σ r) hr
    simp only [cfgRen, σ_σ] at this ⊢
    exact this

/-! ## The weight on the machine -/

/-- The weight in coordinates shifted by `lo` (`h = hi - lo`), so that no value exceeds the
counted interval. -/
def wtG (lo h ea eb pz lt : ℕ) : ℕ :=
  if lt = 1 then min (eb - lo + pz) h - (ea - lo) else h - (min (ea - lo) h - (eb - lo + pz))

/-- The shifted form. -/
theorem wtF_eq_wtG {lo hi ea eb pz lt : ℕ} (hlh : lo ≤ hi) (hpz : pz = 1 → lo ≤ eb)
    (hpz1 : pz ≤ 1) : wtF lo hi ea eb pz lt = wtG lo (hi - lo) ea eb pz lt := by
  unfold wtF wtG
  have : pz = 0 ∨ pz = 1 := by omega
  rcases this with rfl | rfl
  · split_ifs <;> simp only [Nat.min_def, Nat.max_def] <;> split_ifs <;> omega
  · have := hpz rfl
    split_ifs <;> simp only [Nat.min_def, Nat.max_def] <;> split_ifs <;> omega

/-- `wtG` of `lo = r44020`, `h = r44021`, `ea = r42110`, `eb = r42113`, `pz = r41112`,
`lt = r43120` into `r43121`. -/
def wtS : Stmt :=
  .seq (block [.subN 43122 42113 44020, .addN 43122 43122 41112, .subN 43127 42110 44020])
    (.ifLtN 43120 43011
      (.seq (.ifLtN 43127 44021 (.instr (.copyN 43123 43127)) (.instr (.copyN 43123 44021)))
        (block [.subN 43125 43123 43122, .subN 43121 44021 43125]))
      (.seq (.ifLtN 43122 44021 (.instr (.copyN 43123 43122)) (.instr (.copyN 43123 44021)))
        (.instr (.subN 43121 43123 43127))))

theorem wr_wtS : wr (fun r => decide (43121 ≤ r ∧ r < 43128)) wtS = true := by decide

/-- **The weight on the machine.** -/
theorem wtS_exec {P : Polygon} {W : ℕ} (d : Config) (hw : WordsBounded W d)
    (h1 : d.nreg 43011 = 1) (hlt : d.nreg 43120 ≤ 1)
    (hs : d.nreg 42113 - d.nreg 44020 + d.nreg 41112 ≤ W) :
    ∃ d' k, Exec P W wtS d d' k ∧ k ≤ 12 ∧
      d'.nreg 43121 = wtG (d.nreg 44020) (d.nreg 44021) (d.nreg 42110) (d.nreg 42113)
        (d.nreg 41112) (d.nreg 43120) ∧
      FrameB (fun r => decide (43121 ≤ r ∧ r < 43128)) d d' := by
  suffices H : ∃ d' k, Exec P W wtS d d' k ∧ k ≤ 12 ∧
      d'.nreg 43121 = wtG (d.nreg 44020) (d.nreg 44021) (d.nreg 42110) (d.nreg 42113)
        (d.nreg 41112) (d.nreg 43120) by
    obtain ⟨d', k, x, hk, hv⟩ := H
    exact ⟨d', k, x, hk, hv, exec_frameB x wr_wtS⟩
  unfold wtS wtG
  refine spec_seq ?_
  exec_block
  · config_simp; exact hs
  set t := d.nreg 42113 - d.nreg 44020 + d.nreg 41112 with ht
  set u := d.nreg 42110 - d.nreg 44020 with hu
  by_cases hl : d.nreg 43120 < 1
  · refine spec_ifLtN_true (by config_simp; rw [h1]; exact hl) ?_
    rw [ite_eq_right (by omega)]
    refine spec_seq ?_
    by_cases a1 : u < d.nreg 44021
    · refine spec_ifLtN_true (by config_simp; exact a1)
        (spec_instr (Exec.copyN ‹_› _ _) fun hw₂ => ?_)
      exec_block
      refine ⟨by omega, ?_⟩
      config_simp
      rw [min_eq_left a1.le]
    · refine spec_ifLtN_false (by config_simp; exact a1)
        (spec_instr (Exec.copyN ‹_› _ _) fun hw₂ => ?_)
      exec_block
      refine ⟨by omega, ?_⟩
      config_simp
      rw [min_eq_right (not_lt.1 a1)]
  · refine spec_ifLtN_false (by config_simp; rw [h1]; exact hl) ?_
    rw [ite_eq_left (by omega)]
    refine spec_seq ?_
    by_cases a1 : t < d.nreg 44021
    · refine spec_ifLtN_true (by config_simp; exact a1)
        (spec_instr (Exec.copyN ‹_› _ _) fun hw₂ => ?_)
      refine spec_instr (Exec.subN hw₂ _ _ _) fun _ => ⟨by omega, ?_⟩
      config_simp
      rw [min_eq_left a1.le]
    · refine spec_ifLtN_false (by config_simp; exact a1)
        (spec_instr (Exec.copyN ‹_› _ _) fun hw₂ => ?_)
      refine spec_instr (Exec.subN hw₂ _ _ _) fun _ => ⟨by omega, ?_⟩
      config_simp
      rw [min_eq_right (not_lt.1 a1)]

end

end BuildRam

end Chazelle.Core
