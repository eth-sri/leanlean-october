module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreFTest

/-!
# WP-E, the search on the RAM (`FindOK`), part 3: halving a code (finding R-D3)

`halfS`: `81121 := ⌊x / 2⌋` and `81122 := x mod 2` for `x` in `81120`.  The RAM has no division;
the context of the search stores `⌊y / 2⌋` for `y ≤ n` at the address read at `g + 3`
(`MemCtx.Halves`).  Subtract `2 ⌊n/2⌋` (adding `⌊n/2⌋`) until `x ≤ n`, then read the table:
`O(x / n)` steps.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs

/-- The loop body of the halving. -/
def halfBodyL : List Instr := [.subN 81120 81120 81022, .addN 81121 81121 81023]

/-- The end of the halving: read the table, then the parity. -/
def halfEndL : List Instr := [.addN 81124 81004 81014, .loadN 81124 81124,
  .addN 81124 81124 81120, .loadN 81124 81124, .addN 81121 81121 81124,
  .addN 81124 81121 81121, .subN 81122 81123 81124]

/-- **Halving**: `81121 := 81120 / 2`, `81122 := 81120 % 2` (`81120`, `81123`, `81124` are
scratch). -/
def halfS : Stmt :=
  .seq (Stmt.block [.copyN 81123 81120, .constN 81121 0])
    (.seq (.whileLtN 81020 81120 (Stmt.block halfBodyL)) (Stmt.block halfEndL))

/-! ## Register effects -/

section
variable (m f : ℕ → ℕ)
theorem halfBody_eff :
    regB m halfBodyL f 81120 = f 81120 - f 81022 ∧
      regB m halfBodyL f 81121 = f 81121 + f 81023 ∧
      ∀ q, q ≠ 81120 → q ≠ 81121 → regB m halfBodyL f q = f q := by
  simp_all [halfBodyL, regB, regI, upd, List.mem_cons, List.not_mem_nil, or_false, dstI] 

theorem halfEnd_eff :
    regB m halfEndL f 81121 = f 81121 + m (m (f 81004 + f 81014) + f 81120) ∧
      regB m halfEndL f 81122 =
        f 81123 - (f 81121 + m (m (f 81004 + f 81014) + f 81120) +
          (f 81121 + m (m (f 81004 + f 81014) + f 81120))) ∧
      ∀ q, q ≠ 81121 → q ≠ 81122 → q ≠ 81124 → regB m halfEndL f q = f q := by
  simp_all [halfEndL, regB, regI, upd, List.mem_cons, List.not_mem_nil, or_false, dstI] 


end

/-- The cost bound of a halving of `x`. -/
def halfK (n x : ℕ) : ℕ := 4 * (x / (2 * (n / 2))) + 11

variable {E : FEnv} {c₀ c : Config}

section
variable (hE : FGood E c₀)
include hE
/-- The halving table in a configuration of the search. -/
theorem halves_at (hI : FInv E.W c₀ c) :
    c.nreg 81004 + 3 < c.nreg ALLOC ∧ ∀ x, x ≤ E.P.n →
      c.nmem (c.nreg 81004 + 3) + x < c.nreg ALLOC ∧
      c.nmem (c.nmem (c.nreg 81004 + 3) + x) = x / 2 := by
  have hag := hI.agree hE
  have hA := hI.allocA hE
  have hX : E.X.holds E.P c.nmem E.g (c.nreg ALLOC) :=
    E.X.mono _ _ _ _ _ hA (E.X.local_ _ _ _ _ _ (fun a ha => (hag a ha).symm) hE.hX)
  have g4 : c.nreg 81004 = E.g := by rw [hI.hin _ (by omega_nf), hE.i4]
  rw [g4]
  exact hE.hhalf _ _ _ _ hX

/-- **Halving** as a run step of the search. -/
theorem halfS_fs {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {x : ℕ} (hx : c.nreg 81120 = x) (hroom : c.nreg ALLOC + halfK E.P.n x ≤ E.W) :
    FRS B E.P E.W c₀ halfS c (halfK E.P.n x) (fun c' => c'.nreg 81121 = x / 2 ∧
      c'.nreg 81122 = x % 2 ∧ ∀ q, q ≠ 81120 → q ≠ 81121 → q ≠ 81122 → q ≠ 81123 →
        q ≠ 81124 → c'.nreg q = c.nreg q) := by
  have hn3 : 3 ≤ E.P.n := hE.hG.1.1
  have fx : ∀ c', FInv E.W c₀ c' → c'.nreg 81020 = E.P.n ∧ c'.nreg 81022 = 2 * (E.P.n / 2) ∧
      c'.nreg 81023 = E.P.n / 2 ∧ c'.nreg 81014 = 3 := fun c' hI' =>
    ⟨by rw [hI'.hin _ (by omega_nf), hE.pn],
      by rw [hI'.hin _ (by omega_nf), hE.nE],
      by rw [hI'.hin _ (by omega_nf), hE.hE2],
      by rw [hI'.hin _ (by omega_nf), hE.k3]⟩
  have hxW : x ≤ E.W := by rw [← hx]; exact hI.hw.1 81120
  set nE := 2 * (E.P.n / 2) with hnE
  have hnE2 : 2 ≤ nE := by omega
  have ok0 : okB E.W c.nmem [.copyN 81123 81120, .constN 81121 0] c.nreg := by
    simp [okB, okI, FScr, FOut]
  refine (FRS.seq (K₂ := 4 * (x / nE) + 9) (FRS.block hB _ hI ok0)
    (fun c₁ hI₁ _ h₁ => ?_)).mono (by grind [halfK]) (fun _ h => h)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.copyN 81123 81120, .constN 81121 0] c.nreg q :=
    fun q => by rw [h₁]
  have c1a : c₁.nreg 81123 = x := by rw [e₁]; simp [regB, regI, upd, hx]
  have c1b : c₁.nreg 81121 = 0 := by rw [e₁]; simp [regB, regI, upd]
  have c1c : c₁.nreg 81120 = x := by rw [e₁]; simp [regB, regI, upd, hx]
  have c1fr : ∀ q, q ≠ 81121 → q ≠ 81123 → c₁.nreg q = c.nreg q := fun q h1 h2 => by
    rw [e₁]; simp [regB, regI, upd, h1, h2]
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := c1fr _ (by omega_nf)
    (by omega_nf)
  -- the loop
  let I : Config → Prop := fun c' => c'.nreg 81123 = x ∧ c'.nreg 81120 + 2 * c'.nreg 81121 = x ∧
    ∀ q, q ≠ 81120 → q ≠ 81121 → q ≠ 81122 → q ≠ 81123 → q ≠ 81124 → c'.nreg q = c.nreg q
  have hI1 : I c₁ := ⟨c1a, by omega, fun q h1 h2 _ h4 _ => c1fr q h2 h4⟩
  obtain ⟨f20, f22, f23, f14⟩ := fx c hI
  have hpos : ∀ c', I c' → c'.nreg 81020 < c'.nreg 81120 → 0 < c'.nreg 81120 / nE := by
    intro c' hc' ht
    rw [hc'.2.2 81020 (by omega) (by omega) (by omega) (by omega) (by omega), f20] at ht
    exact Nat.div_pos (by omega) (by omega)
  have hbody : ∀ c', FInv E.W c₀ c' → I c' → c'.nreg 81020 < c'.nreg 81120 →
      c'.nreg ALLOC + 2 ≤ E.W →
      FRS B E.P E.W c₀ (Stmt.block halfBodyL) c' 2
        (fun c'' => I c'' ∧ c''.nreg 81120 / nE < c'.nreg 81120 / nE) := by
    intro c' hI' hc' ht _
    obtain ⟨g20, g22, g23, -⟩ := fx c' hI'
    obtain ⟨i1, i2, i3⟩ := hc'
    rw [g20] at ht
    have ok : okB E.W c'.nmem halfBodyL c'.nreg := by
      simp only [halfBodyL, okB, okI, regI, FScr, FOut]
      refine ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), ⟨Or.inl (Or.inl ⟨by norm_num,
        by norm_num⟩), ?_⟩, trivial⟩
      rw [upd_ne (show (81121 : ℕ) ≠ 81120 by norm_num),
        upd_ne (show (81023 : ℕ) ≠ 81120 by norm_num), g23]; omega
    refine (FRS.block hB halfBodyL hI' ok).mono (by simp [halfBodyL]) (fun c'' h'' => ?_)
    obtain ⟨b0, b1, bfr⟩ := halfBody_eff c'.nmem c'.nreg
    have e'' : ∀ q, c''.nreg q = regB c'.nmem halfBodyL c'.nreg q := fun q => by rw [h'']
    rw [g22] at b0
    rw [g23] at b1
    refine ⟨⟨by ram_grind, ?_, fun q h1 h2 h3 h4 h5 => ?_⟩,
      ?_⟩
    · grind
    · grind
    · have hsd := Nat.sub_mul_div (c'.nreg 81120) nE 1
      ram_grind
  have hroom₁ : c₁.nreg ALLOC + (2 + 2) * (c₁.nreg 81120 / nE) ≤ E.W := by
    grind [halfK]
  refine FRS.seq (K₂ := 7) ((FRS.while I (fun c' => c'.nreg 81120 / nE) 2 hpos hbody hI₁ hI1
    hroom₁).mono (K' := 4 * (x / nE) + 2) (by rw [c1c]) (fun _ h => h))
    (fun c₂ hI₂ _ ⟨⟨j1, j2, j3⟩, jt⟩ => ?_)
  -- the end: the table
  obtain ⟨g20, -, -, g14⟩ := fx c₂ hI₂
  rw [g20, not_lt] at jt
  obtain ⟨hg3, htab⟩ := halves_at hE hI₂
  obtain ⟨ht1, ht2⟩ := htab _ jt
  have hAW : c₂.nreg ALLOC ≤ E.W := hI₂.hw.1 ALLOC
  have ok : okB E.W c₂.nmem halfEndL c₂.nreg := by
    simp only [halfEndL, okB, okI, regI, FScr, FOut]
    refine ⟨⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), by omega⟩,
      Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), ?_⟩,
      Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), ?_⟩,
      ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), ?_⟩, Or.inl (Or.inl ⟨by norm_num, by norm_num⟩),
      trivial⟩ <;> simp [upd, g14] <;> omega
  refine (FRS.block hB halfEndL hI₂ ok).mono (by simp [halfEndL]) (fun c₃ h₃ => ?_)
  obtain ⟨e1, e2, efr⟩ := halfEnd_eff c₂.nmem c₂.nreg
  have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem halfEndL c₂.nreg q := fun q => by rw [h₃]
  rw [g14, ht2] at e1 e2
  refine ⟨by rw [e₃, e1]; omega, by rw [e₃, e2, j1]; omega, fun q h1 h2 h3 h4 h5 => ?_⟩
  rw [e₃, efr q h2 h3 h5]; exact j3 q h1 h2 h3 h4 h5


end

end

end Restore

end Chazelle.Core
