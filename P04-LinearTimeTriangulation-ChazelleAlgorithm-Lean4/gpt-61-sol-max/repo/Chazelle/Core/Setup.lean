module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SpecPhases
public import Chazelle.Programs.Tactics

/-!
# WP-L: the setup phase

Proves `Chazelle.Core.setupSpec : SetupSpec`.  The program `Setup.prog`

1. reads `n` and computes the top grade `p = ⌈log₂ (n - 1)⌉` by doubling (`addN r r r`; the
   machine never multiplies): `q := 0; w := 1; while w < n - 1 do (w := w + w; q := q + 1)`;
2. writes the header `n, p` of the setup record at the allocator `S`;
3. writes the tables `2^i` (at `S + 2 + i`) and `⌈i/5⌉` (at `S + p + 4 + i`) for `i ≤ p + 1`,
   bumping the allocator by two per entry; `⌈i/5⌉` is tabulated incrementally with the
   counter `t = 5 ⌈i/5⌉ - i ∈ [0, 4]`;
4. puts the handle `S` in `coreReg 0`.

The allocator ends at `S + 2 p + 6`, the end of the record.  Cost `≤ 17 p + 51 ≤ 64 (n + 1)`.

Register map (scratch band `bSetup = 2`): `20000` `n`, `20001` the constant `1`, `20002` `n - 1`,
`20003` the power `2^i`, `20004` `p`, `20005` the loop index `i`, `20006` the bound `p + 2`,
`20007` `⌈i/5⌉`, `20008` the counter `t`, `20009` the constant `5`, `20010` / `20011` the table
pointers, `20012` the record base `S`, `20013` the constant `2`.  Band `23`: `coreReg 0 = 230000`.
Band `0`: the allocator `9999`.
-/

namespace Chazelle.Core

namespace Setup

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## A loop rule with an accumulated quantity -/

/-- `whileLtN` with a bounded body cost `B`, a strictly decreasing measure `μ`, and a quantity
`Ψ` growing by at most the cost of each iteration: the whole loop lets `Ψ` grow by at most its
cost. -/
theorem whileLtN_acc {P : Polygon} {W a b : ℕ} {body : Stmt} (I : Config → Prop)
    (μ : Config → ℕ) (B : ℕ) (Ψ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ k ≤ B ∧ μ c' < μ c ∧ Ψ c' ≤ Ψ c + k)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ (B + 2) * μ c + 2 ∧ Ψ c' ≤ Ψ c + k := by
  induction hn : μ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨c₁, k₁, hb, hI₁, hk₁, hμ, hΨ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hk₂, hΨ'⟩ := ih (μ c₁) (by omega) hI₁ rfl
      refine ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', ?_, by omega⟩
      have : (B + 2) * (μ c₁ + 1) ≤ (B + 2) * n := Nat.mul_le_mul_left _ (by omega)
      grind
    · exact ⟨c, 2, .whileLtN_false ht (hI c hc), hc, ht, by omega, by omega⟩

/-! ## Arithmetic -/

/-- `⌈i/5⌉ = (i + 4) / 5`. -/
theorem ceilBeta_eq (i : ℕ) : Cost.ceilBeta i = (i + 4) / 5 := by
  unfold Cost.ceilBeta
  rw [Cost.beta_eq]
  apply le_antisymm
  · rw [Nat.ceil_le]
    have h : i ≤ 5 * ((i + 4) / 5) := by omega
    have h' : (i : ℝ) ≤ 5 * (((i + 4) / 5 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  · rcases Nat.eq_zero_or_pos ((i + 4) / 5) with h0 | hpos
    · omega
    · have hlt : (i + 4) / 5 - 1 < ⌈(1 / 5 : ℝ) * i⌉₊ := by
        rw [Nat.lt_ceil]
        have h : 5 * ((i + 4) / 5 - 1) < i := by omega
        have h' : ((5 * ((i + 4) / 5 - 1) : ℕ) : ℝ) < i := by exact_mod_cast h
        grind
      omega

section
variable {n : ℕ} (hn : 1 ≤ n)
include hn
/-- `2^p ≤ 2 n` for the top grade `p` (`n ≥ 1`). -/
theorem pow_topGrade_le : 2 ^ topGrade n ≤ 2 * n := by
  unfold topGrade
  rcases Nat.eq_zero_or_pos (Nat.clog 2 (n - 1)) with h0 | hpos
  · grind
  · have hlt : 2 ^ (Nat.clog 2 (n - 1) - 1) < n - 1 :=
      (Nat.lt_clog_iff_pow_lt (by norm_num)).mp (by omega)
    have : 2 ^ Nat.clog 2 (n - 1) = 2 * 2 ^ (Nat.clog 2 (n - 1) - 1) := by
      rw [← pow_succ']; grind
    omega

/-- `p < 2 n` for the top grade `p` (`n ≥ 1`). -/
theorem topGrade_lt : topGrade n < 2 * n :=
  lt_of_lt_of_le (Nat.lt_two_pow_self) (pow_topGrade_le hn)

/-! ## The program -/


end

/-- Constants and the start of the doubling loop. -/
def initS : Stmt :=
  block [.inputSize 20000, .constN 20001 1, .constN 20009 5, .constN 20013 2,
    .subN 20002 20000 20001, .constN 20003 1, .constN 20004 0]

/-- The doubling loop: afterwards `20004` holds `p` and `20003` holds `2^p`. -/
def loopA : Stmt :=
  .whileLtN 20003 20002 (block [.addN 20003 20003 20003, .addN 20004 20004 20001])

/-- The header `n, p` at `S = ALLOC`, the allocator bumped by two, the table pointers and the
loop registers initialised. -/
def headerS : Stmt :=
  block [.copyN 20012 9999, .storeN 20012 20000, .addN 20010 20012 20001, .storeN 20010 20004,
    .addN 9999 9999 20013, .addN 20010 20010 20001, .addN 20011 20010 20004,
    .addN 20011 20011 20013, .constN 20003 1, .constN 20005 0, .constN 20007 0,
    .constN 20008 0, .addN 20006 20004 20013]

/-- One table entry: store `2^i` and `⌈i/5⌉`, advance. -/
def bodyB : Stmt :=
  .seq (block [.storeN 20010 20003, .storeN 20011 20007, .addN 20003 20003 20003,
      .addN 20010 20010 20001, .addN 20011 20011 20001, .addN 9999 9999 20013,
      .addN 20005 20005 20001])
    (.seq (.ifLtN 20008 20001 (block [.addN 20007 20007 20001, .addN 20008 20008 20009]) .skip)
      (block [.subN 20008 20008 20001]))

/-- The table loop, `i = 0 … p + 1`. -/
def loopB : Stmt := .whileLtN 20005 20006 bodyB

/-- The handle into `coreReg 0`. -/
def finS : Stmt := block [.copyN 230000 20012]

/-- **The setup program.** -/
def prog : Stmt := .seq initS (.seq loopA (.seq headerS (.seq loopB finS)))

/-! ## Invariants -/

/-- The setup frame relative to the entry configuration `c0`: registers outside band `2`,
`coreReg 0` and the allocator, the real files, the output and the memory below the entry
allocator are unchanged. -/
def SFr (c0 c : Config) : Prop :=
  (∀ r, (r < 20000 ∨ 30000 ≤ r) → r ≠ 9999 → r ≠ 230000 → c.nreg r = c0.nreg r) ∧
    c.rreg = c0.rreg ∧ c.rmem = c0.rmem ∧ c.output = c0.output ∧
    ∀ a, a < c0.nreg 9999 → c.nmem a = c0.nmem a

/-- The invariant of the doubling loop. -/
def InvA (W n : ℕ) (c0 c : Config) : Prop :=
  WordsBounded W c ∧ SFr c0 c ∧ c.nreg 9999 = c0.nreg 9999 ∧ c.nmem = c0.nmem ∧
    c.nreg 20000 = n ∧ c.nreg 20001 = 1 ∧ c.nreg 20002 = n - 1 ∧ c.nreg 20009 = 5 ∧
    c.nreg 20013 = 2 ∧ c.nreg 20003 = 2 ^ c.nreg 20004 ∧ c.nreg 20004 ≤ topGrade n

/-- The invariant of the table loop (record base `S`). -/
def InvB (W n S : ℕ) (c0 c : Config) : Prop :=
  WordsBounded W c ∧ SFr c0 c ∧ S = c0.nreg 9999 ∧
    c.nreg 20000 = n ∧ c.nreg 20001 = 1 ∧ c.nreg 20009 = 5 ∧ c.nreg 20013 = 2 ∧
    c.nreg 20004 = topGrade n ∧ c.nreg 20012 = S ∧ c.nreg 20006 = topGrade n + 2 ∧
    c.nreg 20005 ≤ topGrade n + 2 ∧ c.nreg 20003 = 2 ^ c.nreg 20005 ∧
    c.nreg 20010 = S + 2 + c.nreg 20005 ∧ c.nreg 20011 = S + topGrade n + 4 + c.nreg 20005 ∧
    c.nreg 20007 = (c.nreg 20005 + 4) / 5 ∧
    c.nreg 20008 + c.nreg 20005 = 5 * ((c.nreg 20005 + 4) / 5) ∧
    c.nreg 9999 = S + 2 + 2 * c.nreg 20005 ∧
    c.nmem S = n ∧ c.nmem (S + 1) = topGrade n ∧
    ∀ j, j < c.nreg 20005 →
      c.nmem (S + 2 + j) = 2 ^ j ∧ c.nmem (S + topGrade n + 4 + j) = (j + 4) / 5

/-! ## The pieces -/

/-- The initial block. -/
theorem initS_spec {P : Polygon} {W : ℕ} (c : Config) (hc : WordsBounded W c) (hW : P.n + 5 ≤ W) :
    ∃ c' k, Exec P W initS c c' k ∧ k = 7 ∧ InvA W P.n c c' ∧ c'.nreg 20004 = 0 := by
  unfold initS
  exec_block
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · refine ⟨rfl, ⟨‹_›, ⟨fun r hr h1 h2 => ?_, rfl, rfl, rfl, fun a _ => rfl⟩, rfl, rfl,
      by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
      by ram_simp, by omega_nf⟩, by config_simp⟩
    grind [Machine.upd_other]


section
variable {P : Polygon} {W : ℕ} (c0 c : Config) (hI : InvA W P.n c0 c)
include hI
/-- The doubling loop computes the top grade. -/
theorem loopA_spec
    (hq0 : c.nreg 20004 = 0) (hn : 1 ≤ P.n) (hW : 2 * P.n ≤ W) :
    ∃ c' k, Exec P W loopA c c' k ∧ k ≤ 4 * topGrade P.n + 2 ∧ InvA W P.n c0 c' ∧
      c'.nreg 20004 = topGrade P.n := by
  have hp2 := pow_topGrade_le hn
  obtain ⟨c', k, he, hI', ht, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 20003) (b := 20002)
    (body := block [.addN 20003 20003 20003, .addN 20004 20004 20001]) (InvA W P.n c0)
    (fun c => topGrade P.n - c.nreg 20004) 2 (fun c h => h.1) (fun c h htest => by
      obtain ⟨hw, hfr, hA, hm, h0, h1, h2, h9, h13, h3, h4⟩ := h
      have hlt : c.nreg 20004 < topGrade P.n := by
        unfold topGrade
        rw [Nat.lt_clog_iff_pow_lt (by norm_num)]
        omega
      have hpow : 2 ^ (c.nreg 20004 + 1) ≤ 2 ^ topGrade P.n := Nat.pow_le_pow_right (by norm_num) hlt
      
      have hq : c.nreg 20004 < 2 ^ c.nreg 20004 := Nat.lt_two_pow_self
      exec_block
      · omega
      · omega_nf
      · obtain ⟨hr, hrr, hrm, ho, hmem⟩ := hfr
        refine ⟨⟨‹_›, ⟨fun r hr' h1' h2' => ?_, hrr, hrm, ho, hmem⟩, hA, hm, by ram_simp,
          by ram_simp, by omega_nf, by ram_simp,
          by ram_simp, ?_, ?_⟩, by omega, ?_⟩
        · grind [Machine.upd_other]
        · config_simp; grind
        · config_simp; omega
        · config_simp; omega) hI
  refine ⟨c', k, he, by omega, hI', ?_⟩
  obtain ⟨-, -, -, -, -, -, h2, -, -, h3, h4⟩ := hI'
  refine le_antisymm h4 ?_
  unfold topGrade
  apply Nat.clog_le_of_le_pow
  omega


/-- The header block starts the table loop. -/
theorem headerS_spec
    (hp : c.nreg 20004 = topGrade P.n) (hW : c0.nreg 9999 + 2 * topGrade P.n + 6 ≤ W) :
    ∃ c' k, Exec P W headerS c c' k ∧ k = 13 ∧ InvB W P.n (c0.nreg 9999) c0 c' ∧
      c'.nreg 20005 = 0 := by
  obtain ⟨hw, ⟨hr, hrr, hrm, ho, hmem⟩, hA, hm, h0, h1, h2, h9, h13, h3, h4⟩ := hI
  unfold headerS
  exec_block
  · omega_nf
  · omega_nf
  · omega_nf
  · omega_nf
  · omega_nf
  · omega
  · omega
  · omega
  · omega
  · omega_nf
  · refine ⟨rfl, ⟨‹_›, ⟨fun r hr' h1' h2' => ?_, hrr, hrm, ho, fun a ha => ?_⟩, rfl,
      by omega_nf, by omega_nf, by omega_nf,
      by omega_nf, by ram_simp, by omega_nf,
      by config_simp; rw [hp, h13], by omega_nf, by ram_simp,
      by omega_nf, by config_simp; omega,
      by config_simp, by config_simp, by omega_nf,
      ?_, ?_, fun j hj => by config_simp at hj; omega⟩, by config_simp⟩
    · simp (disch := omega) only [Machine.upd_other]; grind
    · grind [Machine.upd_other]
    all_goals (grind [Machine.upd_other, Machine.upd_same])



end

/-- An `if` with a false condition. -/
theorem iteF {α : Type} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [h]


/-- The table-loop invariant after one iteration, from the effect of the body. -/
theorem bodyB_post {W n S : ℕ} {c0 c c' : Config} (hI : InvB W n S c0 c)
    (hw' : WordsBounded W c')
    (hreg : ∀ r, r ≠ 20003 → r ≠ 20010 → r ≠ 20011 → r ≠ 9999 → r ≠ 20005 → r ≠ 20007 →
      r ≠ 20008 → c'.nreg r = c.nreg r)
    (hrr : c'.rreg = c.rreg) (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output)
    (hmem : c'.nmem = upd (upd c.nmem (c.nreg 20010) (c.nreg 20003)) (c.nreg 20011) (c.nreg 20007))
    (hlt : c.nreg 20005 < topGrade n + 2)
    (h3 : c'.nreg 20003 = c.nreg 20003 + c.nreg 20003)
    (h10 : c'.nreg 20010 = c.nreg 20010 + 1) (h11 : c'.nreg 20011 = c.nreg 20011 + 1)
    (hA : c'.nreg 9999 = c.nreg 9999 + 2) (h5 : c'.nreg 20005 = c.nreg 20005 + 1)
    (h7 : c'.nreg 20007 = (c.nreg 20005 + 5) / 5)
    (h8 : c'.nreg 20008 + c.nreg 20005 + 1 = 5 * ((c.nreg 20005 + 5) / 5)) :
    InvB W n S c0 c' := by
  obtain ⟨hw, ⟨hr, hrr0, hrm0, ho0, hmem0⟩, hS, g0, g1, g9, g13, g4, g12, g6, gi, g3, g10, g11,
    g7, g8, gA, gm0, gm1, gmj⟩ := hI
  have hmem' : ∀ a, c'.nmem a = if a = S + topGrade n + 4 + c.nreg 20005 then (c.nreg 20005 + 4) / 5
      else if a = S + 2 + c.nreg 20005 then 2 ^ c.nreg 20005 else c.nmem a := by
    intro a
    rw [hmem, Machine.upd_apply, Machine.upd_apply, g11, g10, g7, g3]
  refine ⟨hw', ⟨fun r h1 h2 h3' => ?_, hrr.trans hrr0, hrm.trans hrm0, ho.trans ho0,
    fun a ha => ?_⟩, hS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hreg r (by omega) (by omega) (by omega) h2 (by omega) (by omega) (by omega)]
    grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · omega
  · grind
  · omega
  · omega
  · rw [h7, h5]
  · omega
  · omega
  · grind
  · grind
  · intro j hj
    rw [h5] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · rw [hmem', hmem', iteF (by omega), iteF (by omega), iteF (by omega),
        iteF (by omega)]
      grind
    · subst hj
      grind


section
variable {P : Polygon} {W S : ℕ} (c0 c : Config) (hI : InvB W P.n S c0 c)
include hI
/-- One iteration of the table loop. -/
theorem bodyB_spec
    (ht : c.nreg 20005 < c.nreg 20006) (hn : 1 ≤ P.n) (hW : S + 8 * P.n + 9 ≤ W) :
    ∃ c' k, Exec P W bodyB c c' k ∧ InvB W P.n S c0 c' ∧ k ≤ 11 ∧
      topGrade P.n + 2 - c'.nreg 20005 < topGrade P.n + 2 - c.nreg 20005 ∧
      c'.nreg 9999 ≤ c.nreg 9999 + k := by
  have hI0 := hI
  obtain ⟨hw, -, -, g0, g1, g9, g13, g4, g12, g6, gi, g3, g10, g11, g7, g8, gA, -, -, -⟩ := hI
  have hlt : c.nreg 20005 < topGrade P.n + 2 := by omega
  have hp2 := pow_topGrade_le hn
  have hpl := topGrade_lt hn
  have hpow : 2 ^ (c.nreg 20005 + 1) ≤ 2 ^ (topGrade P.n + 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  
  
  unfold bodyB
  refine spec_seq ?_
  exec_block
  · grind
  · omega_nf
  · config_simp; omega
  · omega_nf
  · config_simp; omega
  · by_cases hT : c.nreg 20008 < 1
    · refine spec_seq ?_
      refine spec_ifLtN_true (by ram_simp) ?_
      exec_block
      · config_simp; grind
      · config_simp; grind
      · refine ⟨bodyB_post hI0 ‹_› (fun r a b c d e f g => ?_) rfl rfl rfl ?_ hlt
          (by config_simp) (by ram_simp) (by ram_simp)
          (by ram_simp) (by ram_simp) ?_ ?_, by omega, ?_, ?_⟩
        · ram_simp
        · config_simp
        · config_simp; omega
        · config_simp; grind
        · config_simp; grind
        · omega_nf
    · refine spec_seq ?_
      refine spec_ifLtN_false (by ram_simp) ?_
      refine spec_skip ‹_› ?_
      exec_block
      refine ⟨bodyB_post hI0 ‹_› (fun r a b c d e f g => ?_) rfl rfl rfl ?_ hlt
        (by config_simp) (by ram_simp) (by ram_simp)
        (by ram_simp) (by ram_simp) ?_ ?_, by omega, ?_, ?_⟩
      · ram_simp
      · config_simp
      · omega_nf
      · config_simp; omega
      · config_simp; grind
      · omega_nf


/-- The table loop writes both tables. -/
theorem loopB_spec
    (hi : c.nreg 20005 = 0) (hn : 1 ≤ P.n) (hW : S + 8 * P.n + 9 ≤ W) :
    ∃ c' k, Exec P W loopB c c' k ∧ k ≤ 13 * (topGrade P.n + 2) + 2 ∧ InvB W P.n S c0 c' ∧
      c'.nreg 20005 = topGrade P.n + 2 ∧ c'.nreg 9999 ≤ c.nreg 9999 + k := by
  obtain ⟨c', k, he, hI', ht, hk, hΨ⟩ := whileLtN_acc (P := P) (a := 20005) (b := 20006)
    (body := bodyB) (InvB W P.n S c0) (fun c => topGrade P.n + 2 - c.nreg 20005) 11
    (fun c => c.nreg 9999) (fun c h => h.1)
    (fun c h htest => bodyB_spec c0 c h htest hn hW) hI
  refine ⟨c', k, he, by omega, hI', ?_, hΨ⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, h6, hle, -⟩ := hI'
  omega

/-! ## The specification -/


end

/-- **WP-L: the setup phase meets `SetupSpec`** with the program `Setup.prog` and the constant
`κ = 64`. -/
theorem prog_meets : SetupSpec := by
  refine ⟨prog, 64, ?_⟩
  intro P W c hw ⟨hge, _hn3⟩ hroom
  have hn : 3 ≤ P.n := hge.1.1
  have hAL : ALLOC = 9999 := rfl
  have hc0 : coreReg 0 = 230000 := rfl
  rw [hAL] at hroom
  have hpl := topGrade_lt (by omega : 1 ≤ P.n)
  obtain ⟨c1, k1, e1, hk1, hI1, hq1⟩ := initS_spec c hw (P := P) (by nlinarith)
  obtain ⟨c2, k2, e2, hk2, hI2, hq2⟩ := loopA_spec c c1 hI1 hq1 (by omega) (by nlinarith)
  have hA2 : c2.nreg 9999 = c.nreg 9999 := hI2.2.2.1
  obtain ⟨c3, k3, e3, hk3, hI3, hi3⟩ := headerS_spec c c2 hI2 hq2 (by nlinarith)
  have hA3 : c3.nreg 9999 = c.nreg 9999 + 2 := by
    have := hI3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    omega
  obtain ⟨c4, k4, e4, hk4, hI4, hi4, hΨ⟩ := loopB_spec c c3 hI3 hi3 (by omega) (by nlinarith)
  obtain ⟨hw4, ⟨hr, hrr, hrm, ho, hmem⟩, -, -, -, -, -, -, g12, -, -, -, -, -, -, -, gA, gm0,
    gm1, gmj⟩ := hI4
  have e5c := Exec.copyN (P := P) hw4 230000 20012
  have e5 : Exec P W finS c4 { c4 with nreg := upd c4.nreg 230000 (c4.nreg 20012) } 1 :=
    Exec.block_cons e5c (Exec.block_nil e5c.wb_right)
  refine ⟨_, k1 + (k2 + (k3 + (k4 + 1))), e1.seq (e2.seq (e3.seq (e4.seq e5))), by nlinarith,
    ?_, ?_⟩
  · rw [hAL, hc0]
    simp only [Machine.upd_same, ne_eq, not_false_eq_true, Machine.upd_other,
      Nat.reduceEqDiff]
    rw [g12, gA, hi4]
    intro m hm
    
    refine ⟨?_, ?_, fun i hi => ?_, by omega⟩
    · grind
    all_goals (grind [ceilBeta_eq])
  · refine ⟨fun r hr1 hr2 => ?_, fun r _ => congrFun hrr r, fun a ha => hmem a ha,
      fun a _ => congrFun hrm a,
      ho, ?_, ?_⟩
    · simp only [phaseBands, bandOf, Finset.mem_Icc, not_and_or, not_le] at hr1
      grind [Machine.upd_other]
    · omega_nf
    · omega_nf


end

end Setup

public section

/-- **WP-L (proved)**: the setup phase (`Setup.prog`, constant `κ = 64`). -/
theorem setupSpec : SetupSpec := Setup.prog_meets

end

end Chazelle.Core
