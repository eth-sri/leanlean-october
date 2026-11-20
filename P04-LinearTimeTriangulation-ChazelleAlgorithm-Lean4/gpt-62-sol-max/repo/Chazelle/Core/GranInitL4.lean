module

meta import Chazelle.Programs.RamEval

public import Chazelle.Core.GranInitL3

/-!
# WP-F, init part 9: the ring arrays

For every position `j < A` of the sequence table: `cnt j := 0`, the full ring
`nxt j = j + 1 mod A`, `prv j = j - 1 mod A`, the start edge `eg j = bB ch (edge j)` and the bit
`pz j` (`pzStmt`) (`posLoop_exec`).  The stages of one step are `posA` … `posF`.
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-! ## Descriptors survive changes of memory above them (after `BuildRam.desc_agree`) -/

abbrev hostAt_agree' := @HostAt.agree

abbrev desc_agree' := @ModelDescWF.agree

/-! ## The stages of one position -/

/-- `cnt j := 0`, `r85 := j + 1` (`r70 = j`). -/
def posA : Stmt := block [.addN 90072 90038 90070, .constN 90073 0, .storeN 90072 90073,
  .addN 90085 90070 90019]

/-- `nxt j := j + 1 mod A`. -/
def posB : Stmt := .seq (.ifLtN 90085 90011 .skip (.instr (.constN 90085 0)))
  (block [.addN 90072 90039 90070, .storeN 90072 90085])

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

theorem wrS_posLoop : wrS Bpos posLoop = true := by decide

section stages

variable {P : Polygon} {W : ℕ}

theorem posA_exec (c : Config) (hw : WordsBounded W c) {j Cb : ℕ} (h70 : c.nreg 90070 = j)
    (h38 : c.nreg 90038 = Cb) (h19 : c.nreg 90019 = 1) (hb : Cb + j + 1 ≤ W) :
    ∃ c' k, Exec P W posA c c' k ∧ k = 4 ∧ c'.nmem = upd c.nmem (Cb + j) 0 ∧
      c'.nreg 90085 = j + 1 ∧
      (∀ q, q ≠ 90072 → q ≠ 90073 → q ≠ 90085 → c'.nreg q = c.nreg q) := by
  unfold posA
  exec_block
  · ram_finish
  · omega
  · ram_finish
  simp_all

theorem posB_exec (c : Config) (hw : WordsBounded W c) {j A Nb : ℕ} (h70 : c.nreg 90070 = j)
    (h85 : c.nreg 90085 = j + 1) (h11 : c.nreg 90011 = A) (h39 : c.nreg 90039 = Nb)
    (hb : Nb + j ≤ W) :
    ∃ c' k, Exec P W posB c c' k ∧ k ≤ 5 ∧
      c'.nmem = upd c.nmem (Nb + j) (if j + 1 < A then j + 1 else 0) ∧
      (∀ q, q ≠ 90072 → q ≠ 90085 → c'.nreg q = c.nreg q) := by
  unfold posB
  have fin : ∀ (c₁ : Config) (k₁ : ℕ), WordsBounded W c₁ → c₁.nreg 90085 =
      (if j + 1 < A then j + 1 else 0) → c₁.nreg 90070 = j → c₁.nreg 90039 = Nb →
      c₁.nmem = c.nmem → (∀ q, q ≠ 90085 → c₁.nreg q = c.nreg q) → k₁ ≤ 3 →
      ∃ c' k, Exec P W (block [.addN 90072 90039 90070, .storeN 90072 90085]) c₁ c' k ∧
        k₁ + k ≤ 5 ∧ c'.nmem = upd c.nmem (Nb + j) (if j + 1 < A then j + 1 else 0) ∧
        (∀ q, q ≠ 90072 → q ≠ 90085 → c'.nreg q = c.nreg q) := by
    intro c₁ k₁ hw₁ v85 v70 v39 vm vr hk₁
    exec_block
    · ram_finish
    · simp_all
  by_cases hlt : j + 1 < A
  · obtain ⟨c', k, e, hk, hm, hr⟩ := fin c 1 hw (by ram_finish) h70 h39 rfl
      (fun _ _ => rfl) (by omega)
    exact ⟨c', _, (by ram_path), by omega, hm, hr⟩
  · have e₁ := Exec.constN (P := P) hw 90085 0 (by omega)
    obtain ⟨c', k, e, hk, hm, hr⟩ := fin _ 3 e₁.wb_right (by ram_finish)
      (by simp [upd, h70]) (by simp [upd, h39]) rfl (fun q hq => by simp [upd, hq]) le_rfl
    exact ⟨c', _, .seq (.ifLtN_false (by rwa [h85, h11]) e₁) e, by omega, hm, hr⟩

theorem posC_exec (c : Config) (hw : WordsBounded W c) {j A Pb : ℕ} (h70 : c.nreg 90070 = j)
    (h11 : c.nreg 90011 = A) (h19 : c.nreg 90019 = 1) (h40 : c.nreg 90040 = Pb)
    (hb : Pb + j ≤ W) :
    ∃ c' k, Exec P W posC c c' k ∧ k ≤ 5 ∧
      c'.nmem = upd c.nmem (Pb + j) (if 0 < j then j - 1 else A - 1) ∧
      (∀ q, q ≠ 90072 → q ≠ 90085 → c'.nreg q = c.nreg q) := by
  unfold posC
  have fin : ∀ (c₁ : Config) (k₁ : ℕ), WordsBounded W c₁ → c₁.nreg 90085 =
      (if 0 < j then j - 1 else A - 1) → c₁.nreg 90070 = j → c₁.nreg 90040 = Pb →
      c₁.nmem = c.nmem → (∀ q, q ≠ 90085 → c₁.nreg q = c.nreg q) → k₁ ≤ 3 →
      ∃ c' k, Exec P W (block [.addN 90072 90040 90070, .storeN 90072 90085]) c₁ c' k ∧
        k₁ + k ≤ 5 ∧ c'.nmem = upd c.nmem (Pb + j) (if 0 < j then j - 1 else A - 1) ∧
        (∀ q, q ≠ 90072 → q ≠ 90085 → c'.nreg q = c.nreg q) := by
    intro c₁ k₁ hw₁ v85 v70 v40 vm vr hk₁
    exec_block
    · ram_finish
    · simp_all 
  by_cases hj : j < 1
  · have e₁ := Exec.subN (P := P) hw 90085 90011 90019
    obtain ⟨c', k, e, hk, hm, hr⟩ := fin _ 2 e₁.wb_right
      (by simp [upd, h11, h19, show ¬ 0 < j by omega]) (by simp [upd, h70]) (by simp [upd, h40])
      rfl (fun q hq => by simp [upd, hq]) (by omega)
    exact ⟨c', _, (by ram_path), by omega, hm, hr⟩
  · have e₁ := Exec.subN (P := P) hw 90085 90070 90019
    obtain ⟨c', k, e, hk, hm, hr⟩ := fin _ 3 e₁.wb_right
      (by ram_finish) (by simp [upd, h70]) (by simp [upd, h40])
      rfl (fun q hq => by simp [upd, hq]) le_rfl
    exact ⟨c', _, .seq (.ifLtN_false (by rwa [h70, h19]) e₁) e, by omega, hm, hr⟩

theorem posD_exec (c : Config) (hw : WordsBounded W c) {j SB AB : ℕ} (h70 : c.nreg 90070 = j)
    (h17 : c.nreg 90017 = SB) (h15 : c.nreg 90015 = AB) (h19 : c.nreg 90019 = 1)
    (hb1 : SB + j ≤ W) (hb2 : AB + 5 * c.nmem (SB + j) + 2 ≤ W) :
    ∃ c' k, Exec P W posD c c' k ∧ k = 10 ∧
      c'.nreg 90110 = c.nmem (AB + 5 * c.nmem (SB + j) + 1) ∧
      c'.nreg 90111 = c.nmem (AB + 5 * c.nmem (SB + j) + 2) ∧ c'.nmem = c.nmem ∧
      (∀ q, q ≠ 90074 → q ≠ 90086 → q ≠ 90087 → q ≠ 90110 → q ≠ 90111 →
        c'.nreg q = c.nreg q) := by
  unfold posD
  exec_block
  all_goals try (config_simp; simp only [h70, h17, h15, h19]; omega)
  refine ⟨rfl, ?_, ?_, rfl, fun q a1 a2 a3 a4 a5 => by
    frame_finish⟩ <;> config_simp <;>
    simp only [h70, h17, h15, h19] <;> ring_nf

theorem posE_exec (c : Config) (hw : WordsBounded W c) {j kind e Gb : ℕ}
    (h70 : c.nreg 90070 = j) (h23 : c.nreg 90023 = kind) (h19 : c.nreg 90019 = 1)
    (h89 : c.nreg 90089 = 6) (h110 : c.nreg 90110 = e) (h41 : c.nreg 90041 = Gb)
    (hb : Gb + j ≤ W) :
    ∃ c' k, Exec P W posE c c' k ∧ k ≤ 5 ∧
      c'.nmem = upd c.nmem (Gb + j) (bB (decide (kind = 0)) e) ∧
      (∀ q, q ≠ 90072 → q ≠ 90088 → c'.nreg q = c.nreg q) := by
  unfold posE
  have fin : ∀ (c₁ : Config) (k₁ : ℕ), WordsBounded W c₁ → c₁.nreg 90088 =
      bB (decide (kind = 0)) e → c₁.nreg 90070 = j → c₁.nreg 90041 = Gb →
      c₁.nmem = c.nmem → (∀ q, q ≠ 90088 → c₁.nreg q = c.nreg q) → k₁ ≤ 3 →
      ∃ c' k, Exec P W (block [.addN 90072 90041 90070, .storeN 90072 90088]) c₁ c' k ∧
        k₁ + k ≤ 5 ∧ c'.nmem = upd c.nmem (Gb + j) (bB (decide (kind = 0)) e) ∧
        (∀ q, q ≠ 90072 → q ≠ 90088 → c'.nreg q = c.nreg q) := by
    intro c₁ k₁ hw₁ v88 v70 v41 vm vr hk₁
    exec_block
    · ram_finish
    · simp_all
  by_cases hk : kind < 1
  · have e₁ := Exec.subN (P := P) hw 90088 90110 90089
    obtain ⟨c', k, e', hk', hm, hr⟩ := fin _ 2 e₁.wb_right
      (by simp [upd, h110, h89, bB, show kind = 0 by omega]) (by simp [upd, h70])
      (by simp [upd, h41]) rfl (fun q hq => by simp [upd, hq]) (by omega)
    exact ⟨c', _, (by ram_path), by omega, hm, hr⟩
  · have e₁ := Exec.copyN (P := P) hw 90088 90110
    obtain ⟨c', k, e', hk', hm, hr⟩ := fin _ 3 e₁.wb_right
      (by simp [upd, h110, bB, show kind ≠ 0 by omega]) (by simp [upd, h70])
      (by simp [upd, h41]) rfl (fun q hq => by simp [upd, hq]) le_rfl
    exact ⟨c', _, .seq (.ifLtN_false (by rwa [h23, h19]) e₁) e', by omega, hm, hr⟩

theorem posF_exec (c : Config) (hw : WordsBounded W c) {j Zb : ℕ} (h70 : c.nreg 90070 = j)
    (h42 : c.nreg 90042 = Zb) (h19 : c.nreg 90019 = 1) (hb : Zb + j + 1 ≤ W) :
    ∃ c' k, Exec P W posF c c' k ∧ k = 3 ∧ c'.nmem = upd c.nmem (Zb + j) (c.nreg 90112) ∧
      c'.nreg 90070 = j + 1 ∧ (∀ q, q ≠ 90072 → q ≠ 90070 → c'.nreg q = c.nreg q) := by
  unfold posF
  exec_block
  · ram_finish
  · ram_finish
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
  cnt : ∀ u, u < c.nreg 90070 → c.nmem (d.b0 + d.oCnt + u) = 0
  nxt : ∀ u, u < c.nreg 90070 → c.nmem (d.b0 + d.oNxt + u) = if u + 1 < A then u + 1 else 0
  prv : ∀ u, u < c.nreg 90070 → c.nmem (d.b0 + d.oPrv + u) = if 0 < u then u - 1 else A - 1
  eg : ∀ u, u < c.nreg 90070 → c.nmem (d.b0 + d.oEg + u) = bB (decide (kind = 0)) (edge u)
  pz : ∀ u, u < c.nreg 90070 → c.nmem (d.b0 + d.oPz + u) ≤ 1 ∧
    (c.nmem (d.b0 + d.oPz + u) = 1 ↔ M.counted (edge u) ∧ M.param Q ⟨edge u, hgt u⟩ ≠ 0)
  mem : ∀ a, (a < d.b0 + d.oCnt ∨ d.b0 + d.oStk ≤ a) → c.nmem a = c₀.nmem a

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
  desc : ModelDescAt c₀.nmem MD (Qof P) M
  arcs : ∀ u, u < A → SB + u < d.b0 ∧ AB + 5 * c₀.nmem (SB + u) + 2 < d.b0 ∧
    c₀.nmem (AB + 5 * c₀.nmem (SB + u) + 1) = edge u ∧
    c₀.nmem (AB + 5 * c₀.nmem (SB + u) + 2) = hgt u
  edge_lt : ∀ u, u < A → edge u < M.W.n
  hgt_le : ∀ u, u < A → hgt u ≤ P.n

set_option maxHeartbeats 2000000 in
theorem posBody_exec {P : Polygon} {W A MD SB AB : ℕ} {d : Dm} {M : Model} {edge hgt : ℕ → ℕ}
    {c₀ c : Config} (hE : PosEnv P W A MD SB AB d M edge hgt c₀)
    (hI : PosI W A (c₀.nmem MD) d M (Qof P) edge hgt c₀ c) (ht : c.nreg 90070 < A) :
    ∃ c' k, Exec P W posBody c c' k ∧ PosI W A (c₀.nmem MD) d M (Qof P) edge hgt c₀ c' ∧
      k ≤ 6050 ∧ c'.nreg 90070 = c.nreg 90070 + 1 := by
  obtain ⟨hw, hle, h89, hr, hcnt, hnxt, hprv, heg, hpz, hm⟩ := hI
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩ := d.lay
  have hbW := hE.bW
  have hAd := hE.hA
  generalize hjj : c.nreg 90070 = j at ht hle hcnt hnxt hprv heg hpz
  have hB : Bases c d := hE.bases.frame fun q a1 a2 => hr q (by simp [Bpos, Binit, Bpz, NFLoc.Bdir]; omega)
  have c19 : c.nreg 90019 = 1 := by ram_rw [hr, hE.h19]
  have c11 : c.nreg 90011 = A := by ram_rw [hr, hE.h11]
  have c15 : c.nreg 90015 = AB := by ram_rw [hr, hE.h15]
  have c17 : c.nreg 90017 = SB := by ram_rw [hr, hE.h17]
  have c23 : c.nreg 90023 = c₀.nmem MD := by ram_rw [hr, hE.h23]
  have c50 : c.nreg 50000 = MD := by ram_rw [hr, hE.h50]
  obtain ⟨a1, a2, a3, a4⟩ := hE.arcs j ht
  have mSB : c.nmem (SB + j) = c₀.nmem (SB + j) := hm _ (by left; omega)
  -- A: cnt
  obtain ⟨c₁, k₁, e₁, hk₁, m₁, v85, r₁⟩ := posA_exec (P := P) c hw hjj hB.bCnt c19 (by omega)
  -- B: nxt
  obtain ⟨c₂, k₂, e₂, hk₂, m₂, r₂⟩ := posB_exec (P := P) (A := A) c₁ e₁.wb_right
    (by ram_rw [r₁, hjj]) v85
    (by ram_rw [r₁, c11])
    (by ram_rw [r₁, hB.bNxt]) (by omega)
  -- C: prv
  have g₂ : ∀ q, q ≠ 90072 → q ≠ 90073 → q ≠ 90085 → c₂.nreg q = c.nreg q := fun q b1 b2 b3 => by
    rw [r₂ q b1 b3, r₁ q b1 b2 b3]
  obtain ⟨c₃, k₃, e₃, hk₃, m₃, r₃⟩ := posC_exec (P := P) (A := A) c₂ e₂.wb_right
    (by ram_rw [g₂, hjj])
    (by ram_rw [g₂, c11])
    (by ram_rw [g₂, c19])
    (by ram_rw [g₂, hB.bPrv]) (by omega)
  have g₃ : ∀ q, q ≠ 90072 → q ≠ 90073 → q ≠ 90085 → c₃.nreg q = c.nreg q := fun q b1 b2 b3 => by
    rw [r₃ q b1 b3, g₂ q b1 b2 b3]
  -- D: the arc start
  have n₃ : c₃.nmem (SB + j) = c₀.nmem (SB + j) := by
    ram_rw [m₃, m₂, m₁, Machine.upd_other _ _, Machine.upd_other _ _,
      Machine.upd_other _ _, mSB]
  have n₃' : MemEqBelow d.b0 c₃.nmem c₀.nmem := fun a ha => by
    ram_rw [m₃, m₂, m₁, Machine.upd_other _ _, Machine.upd_other _ _,
      Machine.upd_other _ _, hm _ (by left; omega)]
  obtain ⟨c₄, k₄, e₄, hk₄, v110, v111, m₄, r₄⟩ := posD_exec (P := P) c₃ e₃.wb_right
    (by ram_rw [g₃, hjj])
    (by ram_rw [g₃, c17])
    (by ram_rw [g₃, c15])
    (by ram_rw [g₃, c19]) (by omega) (by rw [n₃]; omega)
  ram_rw [n₃, n₃', a3] at v110
  ram_rw [n₃, n₃', a4] at v111
  have g₄ : ∀ q, q < 90110 → q ≠ 90072 → q ≠ 90073 → q ≠ 90085 → q ≠ 90074 → q ≠ 90086 →
      q ≠ 90087 → c₄.nreg q = c.nreg q := fun q b0 b1 b2 b3 b4 b5 b6 => by
    ram_rw [r₄ q b4 b5 b6, g₃ q b1 b2 b3]
  -- E: eg
  obtain ⟨c₅, k₅, e₅, hk₅, m₅, r₅⟩ := posE_exec (P := P) (kind := c₀.nmem MD) c₄ e₄.wb_right
    (by ram_rw [g₄, hjj])
    (by ram_rw [g₄, c23])
    (by ram_rw [g₄, c19])
    (by ram_rw [g₄, h89]) v110
    (by ram_rw [g₄, hB.bEg]) (by omega)
  -- the pz bit
  have hmem5 : MemEqBelow d.b0 c₅.nmem c₀.nmem := fun a ha => by
    ram_rw [m₅, Machine.upd_other _ _, m₄, n₃' a ha]
  obtain ⟨hdesc, hwf⟩ := desc_agree' hE.wf hE.desc (fun a ha => hmem5 a ha)
  obtain ⟨hDW, hCW⟩ := NFLoc.locChainWF_of hwf (by omega) hE.hW
  have hW3 : P.n + 3 ≤ W := by have := hE.hW; unfold hostWords at this; omega
  have g₅ : ∀ q, q < 90110 → q ≠ 90072 → q ≠ 90073 → q ≠ 90085 → q ≠ 90074 → q ≠ 90086 →
      q ≠ 90087 → q ≠ 90088 → c₅.nreg q = c.nreg q := fun q b0 b1 b2 b3 b4 b5 b6 b7 => by
    rw [r₅ q b1 b7, g₄ q b0 b1 b2 b3 b4 b5 b6]
  obtain ⟨c₆, k₆, e₆, hk₆, F₆, p1, p2⟩ := pz_exec (P := P) (M := M) hE.hG hW3 c₅ e₅.wb_right
    (MD := MD) (e := edge j) (h := hgt j)
    (by ram_rw [g₅, c50]) hdesc
    (by ram_rw [g₅, c23, hmem5 _ (by have := hE.wf.1; omega)])
    (by ram_rw [g₅, c19])
    (by ram_rw [r₅, v110])
    (by ram_rw [r₅, v111]) (hE.edge_lt j ht) (hE.hgt_le j ht) hDW hCW
  have g₆ : ∀ q, Bpz q = false → c₆.nreg q = c₅.nreg q := F₆.1
  -- F: pz and the counter
  obtain ⟨c₇, k₇, e₇, hk₇, m₇, v70, r₇⟩ := posF_exec (P := P) c₆ e₆.wb_right (j := j)
    (by ram_rw [g₆, g₅, hjj])
    (by ram_rw [g₆, g₅, hB.bPz])
    (by ram_rw [g₆, g₅, c19]) (by omega)
  rw [F₆.2.2.1] at m₇
  have M7 : c₇.nmem = upd (upd (upd (upd (upd c.nmem (d.b0 + d.oCnt + j) 0) (d.b0 + d.oNxt + j)
      (if j + 1 < A then j + 1 else 0)) (d.b0 + d.oPrv + j) (if 0 < j then j - 1 else A - 1))
      (d.b0 + d.oEg + j) (bB (decide (c₀.nmem MD = 0)) (edge j))) (d.b0 + d.oPz + j)
      (c₆.nreg 90112) := by
    rw [m₇, m₅, m₄, m₃, m₂, m₁]
  refine ⟨c₇, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))),
    ⟨e₇.wb_right, by omega, ?_, fun q hq => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_,
      fun u hu => ?_, fun u hu => ?_, fun a ha => ?_⟩, by omega, by rw [v70]⟩
  · ram_rw [r₇, g₆, g₅, h89]
  · simp only [Bpos, Bool.or_eq_false_iff] at hq
    have hq1 := hq.1
    simp only [Binit, decide_eq_false_iff_not] at hq1
    ram_rw [r₇ q, g₆ q hq.2, r₅ q]
    have hq2 := hq.2
    simp only [Bpz, NFLoc.Bdir, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hq2
    ram_rw [r₄ q, g₃ q, hr q (by simp only [Bpos, Bool.or_eq_false_iff]; exact hq)]
  · rw [v70] at hu
    rw [M7]
    by_cases huj : u = j
    · subst huj
      ram_rw [Machine.upd_other _ _, Machine.upd_other _ _,
        Machine.upd_other _ _, Machine.upd_other _ _]
      simp
    · ram_rw [Machine.upd_other _ _, Machine.upd_other _ _,
        Machine.upd_other _ _, Machine.upd_other _ _,
        Machine.upd_other _ _]
      exact hcnt u (by omega)
  · rw [v70] at hu
    rw [M7]
    by_cases huj : u = j
    · subst huj
      ram_rw [Machine.upd_other _ _, Machine.upd_other _ _,
        Machine.upd_other _ _]
      simp
    · ram_rw [Machine.upd_other _ _, Machine.upd_other _ _,
        Machine.upd_other _ _, Machine.upd_other _ _,
        Machine.upd_other _ _]
      exact hnxt u (by omega)
  · rw [v70] at hu
    rw [M7]
    by_cases huj : u = j
    · subst huj
      ram_rw [Machine.upd_other _ _, Machine.upd_other _ _]
      simp
    · ram_rw [Machine.upd_other _ _, Machine.upd_other _ _,
        Machine.upd_other _ _, Machine.upd_other _ _,
        Machine.upd_other _ _]
      exact hprv u (by omega)
  · rw [v70] at hu
    rw [M7]
    by_cases huj : u = j
    · subst huj
      ram_rw [Machine.upd_other _ _]
      simp
    · ram_rw [Machine.upd_other _ _, Machine.upd_other _ _,
        Machine.upd_other _ _, Machine.upd_other _ _,
        Machine.upd_other _ _]
      exact heg u (by omega)
  · rw [v70] at hu
    rw [M7]
    by_cases huj : u = j
    · subst huj
      simp only [Machine.upd_same]
      exact ⟨p1, p2⟩
    · ram_rw [Machine.upd_other _ _, Machine.upd_other _ _,
        Machine.upd_other _ _, Machine.upd_other _ _,
        Machine.upd_other _ _]
      exact hpz u (by omega)
  · ram_rw [M7, Machine.upd_other _ _, Machine.upd_other _ _,
      Machine.upd_other _ _, Machine.upd_other _ _,
      Machine.upd_other _ _]
    exact hm a ha

theorem posLoop_exec {P : Polygon} {W A MD SB AB : ℕ} {d : Dm} {M : Model} {edge hgt : ℕ → ℕ}
    {c₀ : Config} (hw : WordsBounded W c₀) (hE : PosEnv P W A MD SB AB d M edge hgt c₀)
    (hW6 : 6 ≤ W) :
    ∃ c' k, Exec P W posLoop c₀ c' k ∧ k ≤ 6052 * A + 4 ∧
      (∀ u, u < A → c'.nmem (d.b0 + d.oCnt + u) = 0 ∧
        c'.nmem (d.b0 + d.oNxt + u) = (if u + 1 < A then u + 1 else 0) ∧
        c'.nmem (d.b0 + d.oPrv + u) = (if 0 < u then u - 1 else A - 1) ∧
        c'.nmem (d.b0 + d.oEg + u) = bB (decide (c₀.nmem MD = 0)) (edge u) ∧
        c'.nmem (d.b0 + d.oPz + u) ≤ 1 ∧
        (c'.nmem (d.b0 + d.oPz + u) = 1 ↔
          M.counted (edge u) ∧ M.param (Qof P) ⟨edge u, hgt u⟩ ≠ 0)) ∧
      (∀ a, (a < d.b0 + d.oCnt ∨ d.b0 + d.oStk ≤ a) → c'.nmem a = c₀.nmem a) ∧
      FrameS Bpos c₀ c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, q, q0⟩ : ∃ c₁ k₁, Exec P W (block [.constN 90070 0,
      .constN 90089 6]) c₀ c₁ k₁ ∧ k₁ = 2 ∧
      PosI W A (c₀.nmem MD) d M (Qof P) edge hgt c₀ c₁ ∧ c₁.nreg 90070 = 0 := by
    exec_block!
    · refine ⟨rfl, ⟨by assumption, ?_, ?_, fun r hr => ?_, fun u hu => ?_, fun u hu => ?_,
        fun u hu => ?_, fun u hu => ?_, fun u hu => ?_, fun a _ => rfl⟩, ?_⟩
      · config_simp; omega
      · config_simp
      · simp only [Bpos, Binit, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
        config_simp; simp only [upd]; split_ifs <;> ram_finish
      all_goals first | (simp [upd] at hu) | config_simp
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90070) (b := 90011)
    (body := posBody) (PosI W A (c₀.nmem MD) d M (Qof P) edge hgt c₀)
    (fun c => A - c.nreg 90070) 6050 (fun _ h => h.wb)
    (fun c I ht => by
      have t : c.nreg 90070 < A := by ram_rw assumption [I.regs 90011, hE.h11] at ht
      obtain ⟨c', k, e, I', hk, hi⟩ := posBody_exec (P := P) hE I t
      exact ⟨c', k, e, I', hk, by omega⟩) q
  have hK' : c'.nreg 90070 = A := by
    ram_rw [I'.regs 90011, hE.h11] at hx; have := I'.j_le; omega
  refine ⟨c', _, .seq e₁ e, ?_, fun u hu => ⟨I'.cnt u (by omega), I'.nxt u (by omega),
    I'.prv u (by omega), I'.eg u (by omega), (I'.pz u (by omega)).1, (I'.pz u (by omega)).2⟩,
    I'.mem, exec_frameS (.seq e₁ e) wrS_posLoop⟩
  rw [q0] at hk
  omega

end

end Gran

end Chazelle.Core
