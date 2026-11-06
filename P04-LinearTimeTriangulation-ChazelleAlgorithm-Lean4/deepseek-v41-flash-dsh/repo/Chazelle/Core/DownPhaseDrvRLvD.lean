module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvRLvC
public import Chazelle.Core.DownPhaseDrvRCostSpec
public import Chazelle.Core.DownPhaseMathLevel
public import Chazelle.Core.GranSize

/-!
# Down-phase driver (RAM side): one level, the straight-line pieces of the region loop

Exec lemmas of `lvRegA … lvRegE` (register sets `BregA … BregD`), and the arithmetic of the level:
`g0_facts` (the targets `γ₀ = 3 · 2^(⌈βμ⌉+10)` of the region procedure), `mu_le_grades` (the merge
grade is served by the up-phase data), `hostChainOf` (the chain of a host), `nch_le` (Lemma 2.3:
a region map has at most `lvNch μ` chords).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SignK BuildRam

@[expose] public section

section exec

variable {P : Polygon} {W : ℕ}

def BregA (r : ℕ) : Bool := decide (215000 ≤ r ∧ r ≤ 215002)
theorem wr_lvRegA : wr BregA lvRegA = true := ⌖
def BregB (r : ℕ) : Bool := decide (219200 ≤ r ∧ r ≤ 219205)
theorem wr_lvRegB : wr BregB lvRegB = true := ⌖
def BregC (r : ℕ) : Bool := decide (217000 ≤ r ∧ r ≤ 217006)
theorem wr_lvRegC : wr BregC lvRegC = true := ⌖
def BregE (r : ℕ) : Bool := decide (r = 211013)
theorem wr_lvRegE : wr BregE lvRegE = true := ⌖
def BregD (r : ℕ) : Bool := decide (r = 211020 ∨ r = 211012 ∨ r = 211010)
theorem wrM_lvRegD : wrM BregD lvRegD = true := ⌖

theorem lvRegA_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W lvRegA c c' k ∧ k = 3 ∧ c'.nreg 215000 = c.nreg 210005 ∧
      c'.nreg 215001 = c.nreg 211010 ∧ c'.nreg 215002 = c.nreg 211008 := by
  unfold lvRegA
  exec_block
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> config_simp

theorem lvRegB_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W lvRegB c c' k ∧ k = 6 ∧ c'.nreg 219200 = c.nreg 215010 ∧
      c'.nreg 219201 = c.nreg 215012 ∧ c'.nreg 219202 = c.nreg 211002 ∧
      c'.nreg 219203 = c.nreg 211004 ∧ c'.nreg 219204 = c.nreg 211006 ∧
      c'.nreg 219205 = c.nreg 230001 := by
  unfold lvRegB
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp

theorem lvRegC_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W lvRegC c c' k ∧ k = 7 ∧ c'.nreg 217000 = c.nreg 210005 ∧
      c'.nreg 217001 = c.nreg 211010 ∧ c'.nreg 217002 = c.nreg 211008 ∧
      c'.nreg 217003 = c.nreg 215010 ∧ c'.nreg 217004 = c.nreg 215012 ∧
      c'.nreg 217005 = c.nreg 219210 ∧ c'.nreg 217006 = c.nreg 219211 := by
  unfold lvRegC
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp

theorem lvRegE_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W lvRegE c c' k ∧ k ≤ 3 ∧
      c'.nreg 211013 = max (c.nreg 211013) (c.nreg 217011) := by
  unfold lvRegE
  by_cases h : c.nreg 211013 < c.nreg 217011
  · have e := Exec.copyN (P := P) hw 211013 217011
    refine ⟨_, _, .ifLtN_true h e, ⋄, ?_⟩
    simp only [Machine.upd_same]; omega
  · exact ⟨_, _, .ifLtN_false h (.skip hw), ⋄, by omega⟩

theorem lvRegD_exec (c : Config) (hw : WordsBounded W c) {T j p ℓ b tot : ℕ}
    (h09 : c.nreg 211009 = T) (h10 : c.nreg 211010 = j) (h14 : c.nreg 211014 = 1)
    (h17 : c.nreg 217010 = p) (h11 : c.nreg 217011 = ℓ) (h12 : c.nreg 217012 = b)
    (ht : c.nreg 211012 = tot) (hW1 : T + 3 * j + 2 ≤ W) (hW2 : tot + ℓ ≤ W) (hW3 : j + 1 ≤ W) :
    ∃ c' k, Exec P W lvRegD c c' k ∧ k = 10 ∧ c'.nreg 211012 = tot + ℓ ∧
      c'.nreg 211010 = j + 1 ∧ c'.nmem (T + 3 * j) = p ∧ c'.nmem (T + 3 * j + 1) = ℓ ∧
      c'.nmem (T + 3 * j + 2) = b ∧
      (∀ a, (a < T + 3 * j ∨ T + 3 * j + 3 ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have wp := hw.1 217010
  have wl := hw.1 217011
  have wb := hw.1 217012
  unfold lvRegD
  exec_block
  all_goals try (config_simp; (try simp only [h09, h10, h14, h17, h11, h12, ht]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · config_simp; simp only [ht, h11]
  · config_simp; simp only [h10, h14]
  · config_simp; simp only [h09, h10, h14, h17, h11, h12, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [h09, h10, h14, h17, h11, h12, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [h09, h10, h14, h17, h11, h12, Machine.upd_apply]; split_ifs <;> omega
  · intro a ha; config_simp; simp only [h09, h10, h14, Machine.upd_apply]
    split_ifs <;> first | rfl | omega
  · config_simp
  · config_simp
  · config_simp

end exec

/-! ## Arithmetic of the level -/

theorem gradeGran_le_nat (g : ℕ) : gradeGran g ≤ 1201 * 2 ^ Cost.ceilBeta g := by
  have h := gradeGran_le_real g
  exact_mod_cast h

/-- The targets of the region procedure. -/
theorem g0_facts (μ : ℕ) :
    2 * gradeGran μ ≤ 3 * 2 ^ (Cost.ceilBeta μ + 10) ∧ 128 ≤ 3 * 2 ^ (Cost.ceilBeta μ + 10) ∧
      3 * 2 ^ (Cost.ceilBeta μ + 10) ≤ 4096 * 2 ^ Cost.ceilBeta μ := by
  have h := gradeGran_le_nat μ
  have e : 2 ^ (Cost.ceilBeta μ + 10) = 1024 * 2 ^ Cost.ceilBeta μ := by rw [pow_add]; ring
  have h1 : 1 ≤ 2 ^ Cost.ceilBeta μ := Nat.one_le_two_pow
  rw [e]; omega

/-- The merge grade is served by the up-phase data. -/
theorem mu_le_grades {n x lam : ℕ} (hcap : n - 1 ≤ 2 ^ (x - 1)) (h16 : 16 ≤ lam)
    (hlp : lam ≤ topGrade n) : nextLvl lam ≤ x := by
  have h1 := nextLvl_lt h16
  have h2 : topGrade n ≤ x - 1 := Nat.clog_le_of_le_pow hcap
  omega

/-- The chain of a host with at least three points. -/
noncomputable def hostChainOf (Q : Polygon) (H : Host) (h : 3 ≤ (H.pts Q.n).length) : Chain :=
  ⟨H.poly Q, 0, (H.pts Q.n).length - 1, ⋄,
    by rw [DownMath.host_poly_n]; omega⟩

theorem hostChainOf_P (Q : Polygon) (H : Host) (h : 3 ≤ (H.pts Q.n).length) :
    (hostChainOf Q H h).P = H.poly Q := rfl

theorem hostChainOf_s (Q : Polygon) (H : Host) (h : 3 ≤ (H.pts Q.n).length) :
    (hostChainOf Q H h).s = 0 := rfl

theorem hostChainOf_m (Q : Polygon) (H : Host) (h : 3 ≤ (H.pts Q.n).length) :
    (hostChainOf Q H h).m + 1 = (hostChainOf Q H h).P.n := by
  show (H.pts Q.n).length - 1 + 1 = (H.poly Q).n
  rw [DownMath.host_poly_n]; omega

/-- **The chords of a region map** (Lemma 2.3). -/
theorem nch_le {Q : Polygon} {C : Chain} (hP : C.P.Simple) {N : NF} {γ γ₀ μ : ℕ}
    (hc : IsCanonicalNF (chainModel C) Q N γ regCap) (hγ : γ₀ ≤ γ)
    (hm : C.m + 1 ≤ 10 * 2 ^ μ + 8) (hγ₀ : γ₀ = 3 * 2 ^ (Cost.ceilBeta μ + 10)) :
    N.chords.length ≤ lvNch μ := by
  obtain ⟨hNF, hdeg, hgran, -⟩ := hc
  have h23 := DownMath.lemma23_chain hP hNF.1 hdeg hgran
  rw [Gran.ncard_F hNF] at h23
  have h2 : N.nChords * (γ₀ + 1) ≤ N.nChords * (γ + 1) := Nat.mul_le_mul_left _ (⋄)
  have h3 : 140 * (regCap + 2) * (2 * C.m + 1) ≤ 140 * (regCap + 2) * (20 * 2 ^ μ + 17) :=
    Nat.mul_le_mul_left _ (⋄)
  unfold lvNch
  rw [← hγ₀, Nat.le_div_iff_mul_le (⋄)]
  exact le_trans h2 (le_trans h23 h3)

end

end DrvR

end Chazelle.Core
