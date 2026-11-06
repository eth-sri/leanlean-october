module

public import Chazelle.Core.DownPhaseDrvPCost
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.ConfigTactics

/-!
# Down-phase pieces (D4), part 9: the sub-procedures and the program

The contracts of the sub-procedures as named predicates (`L41M`, `BruteM`, `BuildM`, `GranM`:
the `Meets` judgements of `Lemma41Spec`, `BruteSpec`, `BuildNFSpec`, `GranularizeSpec` for a
given program and constant), the program `pieceS sL sB sBd sG` of a piece, and the grade loop
`clogS` (`218019 := ⌈log₂ m⌉`, `clogS_exec`).
-/


namespace Chazelle.Core

namespace DrvP

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## The contracts of the sub-procedures -/

/-- The judgement of `Lemma41Spec O` for the program `s` and the constant `κ`. -/
def L41M (O : OracleIface) (s : Stmt) (κ : ℕ) : Prop :=
  Meets s l41Bands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      (gradeCtx O).holds P c.nmem (rd c bL41 0) (c.nreg ALLOC) ∧
      rd c bL41 3 ≤ c.nmem (rd c bL41 0) ∧ lemma41Start ≤ rd c bL41 3 ∧
      rd c bL41 1 + rd c bL41 2 + 1 ≤ P.n ∧
      2 ^ (rd c bL41 3 - 1) < rd c bL41 2 ∧ rd c bL41 2 ≤ 2 ^ rd c bL41 3)
    (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bL41 1 ∧ C.m = rd c bL41 2 ∧
      Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (rd c' bL41 4) N) ∧
      IsCanonicalNF (chainModel C) (Qof P) N (gradeGran (rd c bL41 3)) 4)
    (fun _ c => κ * (lemma41Nat (rd c bL41 3) + 1))

theorem lemma41Spec_iff (O : OracleIface) : Lemma41Spec O ↔ ∃ s κ, L41M O s κ := Iff.rfl

/-- The judgement of `BruteSpec`. -/
def BruteM (s : Stmt) (κ : ℕ) : Prop :=
  Meets s bruteBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bBrute 1 ∧
      rd c bBrute 0 + rd c bBrute 1 + 1 ≤ P.n ∧ 1 ≤ rd c bBrute 2 ∧
      (rd c bBrute 1 = 1 ∨ 2 ≤ rd c bBrute 2))
    (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bBrute 0 ∧ C.m = rd c bBrute 1 ∧
      Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (rd c' bBrute 3) N) ∧
      IsCanonicalNF (chainModel C) (Qof P) N (rd c bBrute 2) 4)
    (fun _ c => κ * (rd c bBrute 1 + 1) ^ 3)

theorem bruteSpec_iff : BruteSpec ↔ ∃ s κ, BruteM s κ := Iff.rfl

/-- The judgement of `BuildNFSpec`. -/
def BuildM (s : Stmt) (κ : ℕ) : Prop :=
  Meets s {bBuild, bSort, bSign}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bBuild 0) ∧
      ∃ M L, ModelDescAt c.nmem (rd c bBuild 0) (Qof P) M ∧
      GoodModel M ∧ rd c bBuild 2 = L.length ∧ rd c bBuild 1 + 3 * L.length ≤ c.nreg ALLOC ∧
      ChordListAt c.nmem (rd c bBuild 1) L ∧ ChordTriplesOK M (Qof P) L)
    (fun P c c' => ∀ M L, ModelDescAt c.nmem (rd c bBuild 0) (Qof P) M →
      rd c bBuild 2 = L.length → ChordListAt c.nmem (rd c bBuild 1) L →
        ∃ N, c.nreg ALLOC ≤ rd c' bBuild 3 ∧ NFWithin c'.nmem (rd c' bBuild 3) (c'.nreg ALLOC) N ∧
          IsNF M (Qof P) N ∧ N.chords.map (fun r => (r.h, r.lp, r.rp)) = L ∧ N.dec = [])
    (fun _ c => κ * (rd c bBuild 2 * (Nat.clog 2 (rd c bBuild 2) + 1) + 1))

theorem buildNFSpec_iff : BuildNFSpec ↔ ∃ s κ, BuildM s κ := Iff.rfl

/-- The judgement of `GranularizeSpec`. -/
def GranM (s : Stmt) (κ : ℕ → ℕ) : Prop :=
  Meets s granBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bGran 2 ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bGran 0) ∧
      ∃ M N, ModelDescAt c.nmem (rd c bGran 0) (Qof P) M ∧ GoodModel M ∧
        NFWithin c.nmem (rd c bGran 1) (c.nreg ALLOC) N ∧ IsNF M (Qof P) N ∧
        M.DegLe (N.F M (Qof P)) (rd c bGran 2) ∧
        M.Semigranular (N.F M (Qof P)) (rd c bGran 3))
    (fun P c c' => ∀ M N, ModelDescAt c.nmem (rd c bGran 0) (Qof P) M → NFAt c.nmem (rd c bGran 1) N →
      ∃ N', c.nreg ALLOC ≤ rd c' bGran 4 ∧ NFWithin c'.nmem (rd c' bGran 4) (c'.nreg ALLOC) N' ∧
        N'.F M (Qof P) ⊆ N.F M (Qof P) ∧
        IsCanonicalNF M (Qof P) N' (rd c bGran 3) (rd c bGran 2))
    (fun _ c => κ (rd c bGran 2) *
      (c.nmem (rd c bGran 1) * (Nat.clog 2 (c.nmem (rd c bGran 1)) + 1) + 1))

theorem granularizeSpec_iff : GranularizeSpec ↔ ∃ s κ, GranM s κ := Iff.rfl

/-! ## The program -/

/-- The empty list of a connector. -/
def connS : Stmt := block [.constN 218016 0, .constN 218017 0]

/-- `218019 := ⌈log₂ m⌉` (`218023 = 2^218019`). -/
def clogS : Stmt := .seq (block [.constN 218019 0, .constN 218023 1])
  (.whileLtN 218023 218002 (block [.addN 218023 218023 218023, .addN 218019 218019 218021]))

/-- Lemma 4.1 on the leaf, at grade `⌈log₂ m⌉`. -/
def l41Call (sL : Stmt) : Stmt := .seq clogS (.seq (block [.copyN 160000 218008,
  .copyN 160001 218004, .copyN 160002 218002, .copyN 160003 218019])
  (.seq sL (block [.copyN 218015 160004])))

/-- Brute force on the leaf (`γ' = 1` for one edge, else `2`). -/
def bruteCall (sB : Stmt) : Stmt :=
  .seq (.ifLtN 218021 218002 (block [.constN 180002 2]) (block [.constN 180002 1]))
    (.seq (block [.copyN 180000 218004, .copyN 180001 218002])
      (.seq sB (block [.copyN 218015 180003])))

/-- The normal form of a leaf, then its wall filter. -/
def leafS (sL sB : Stmt) : Stmt := .seq (.ifLtN 218002 218022 (bruteCall sB) (l41Call sL)) dropS

/-- The chord list of a piece. -/
def listS (sL sB : Stmt) : Stmt := .ifLtN 218003 218021 connS (leafS sL sB)

/-- The build of the normal form from the list. -/
def buildS (sBd : Stmt) : Stmt := .seq (block [.copyN 40000 218010, .copyN 40001 218016,
  .copyN 40002 218017]) (.seq sBd (block [.copyN 218018 40003]))

/-- The granularity enforcement (cap `4`, target `γ`). -/
def granS (sG : Stmt) : Stmt := .seq (block [.copyN 90000 218010, .copyN 90001 218018,
  .constN 90002 4, .copyN 90003 218007]) (.seq sG (block [.copyN 218011 90004]))

/-- The top offset. -/
def topS : Stmt := .ifLtN 218002 218022 scanS gTop

/-- The descriptor part: count, top, bit, descriptor. -/
def frontS : Stmt := .seq cntS (.seq topS (.seq betaS descS))

/-- **The procedure of a piece.** -/
def pieceS (sL sB sBd sG : Stmt) : Stmt :=
  .seq frontS (.seq (listS sL sB) (.seq (buildS sBd) (granS sG)))

/-! ## The grade loop -/

section exec

variable {P : Polygon} {W : ℕ}

/-- **The grade** `⌈log₂ m⌉`. -/
theorem clogS_exec (c : Config) (hw : WordsBounded W c) {m : ℕ} (h02 : c.nreg 218002 = m)
    (hm : 1 ≤ m) (h21 : c.nreg 218021 = 1) (hmW : 2 * m ≤ W) :
    ∃ c' k, Exec P W clogS c c' k ∧ k ≤ 4 * Nat.clog 2 m + 4 ∧
      c'.nreg 218019 = Nat.clog 2 m ∧
      (∀ r, r ≠ 218019 → r ≠ 218023 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v19, v23, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.constN 218019 0, .constN 218023 1]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 218019 = 0 ∧
      c₁.nreg 218023 = 1 ∧ (∀ r, r ≠ 218019 → r ≠ 218023 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, by config_simp, by config_simp, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    simp [Config.nreg_mk, upd, ite_eq_right h1, ite_eq_right h2]
  let I : Config → Prop := fun d => WordsBounded W d ∧ d.nreg 218023 = 2 ^ d.nreg 218019 ∧
    (1 ≤ d.nreg 218019 → 2 ^ (d.nreg 218019 - 1) < m) ∧
    (∀ r, r ≠ 218019 → r ≠ 218023 → d.nreg r = c.nreg r) ∧ d.nmem = c.nmem ∧
    d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output
  have hI₁ : I c₁ := ⟨e₁.wb_right, by rwr [v23, v19], by rwo [v19], r₁, m₁⟩
  obtain ⟨c₂, k₂, e₂, ⟨w₂, p₂, l₂, r₂, m₂, rr₂, rm₂, o₂⟩, hx₂, hk₂⟩ :=
    Exec.whileLtN_bounded (P := P) (W := W) (a := 218023) (b := 218002)
    (body := block [.addN 218023 218023 218023, .addN 218019 218019 218021]) I
    (fun d => Nat.clog 2 m - d.nreg 218019) 2 (fun d hd => hd.1) (fun d ⟨wd, pd, ld, rd', md, rrd, rmd, od⟩ ht => by
      have h2 : d.nreg 218002 = m := by rw [rd' _ (by norm_num) (by norm_num), h02]
      have h21' : d.nreg 218021 = 1 := by rw [rd' _ (by norm_num) (by norm_num), h21]
      rw [h2] at ht
      have hw := wd
      obtain ⟨d', k, e, hk, v23', v19', r', m'⟩ : ∃ d' k, Exec P W
          (block [.addN 218023 218023 218023, .addN 218019 218019 218021]) d d' k ∧ k = 2 ∧
          d'.nreg 218023 = 2 * d.nreg 218023 ∧ d'.nreg 218019 = d.nreg 218019 + 1 ∧
          (∀ r, r ≠ 218019 → r ≠ 218023 → d'.nreg r = d.nreg r) ∧
          (d'.nmem = d.nmem ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output) := by
        exec_block
        · cso
        · config_simp; rw [h21']
          have : d.nreg 218019 < 2 ^ d.nreg 218019 := Nat.lt_two_pow_self
          omega
        refine ⟨rfl, by csring, by config_simp; rw [h21'], fun r h1 h2 => ?_,
          rfl, rfl, rfl, rfl⟩
        simp [Config.nreg_mk, upd, ite_eq_right h1, ite_eq_right h2]
      obtain ⟨m'', rr'', rm'', o''⟩ := m'
      refine ⟨d', k, e, ⟨e.wb_right, ?_, ?_, fun r h1 h2 => (r' r h1 h2).trans (rd' r h1 h2),
        m''.trans md, rr''.trans rrd, rm''.trans rmd, o''.trans od⟩, by omega, ?_⟩
      · rwring [v23', v19', pd, pow_succ]
      · intro _; rwx [v19', Nat.add_sub_cancel, ← pd]
      · rw [v19']
        rw [pd] at ht
        have : d.nreg 218019 < Nat.clog 2 m := by
          by_contra hc
          push Not at hc
          have h3 : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog (by norm_num) m
          have h4 : 2 ^ Nat.clog 2 m ≤ 2 ^ d.nreg 218019 := Nat.pow_le_pow_right (by norm_num) hc
          omega
        omega) hI₁
  have h2 : c₂.nreg 218002 = m := by rw [r₂ _ (by norm_num) (by norm_num), h02]
  rw [h2, p₂] at hx₂
  have hg : c₂.nreg 218019 = Nat.clog 2 m := by
    apply le_antisymm
    · by_contra hlt
      push Not at hlt
      have := l₂ (by omega)
      have h3 : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog (by norm_num) m
      have h4 : 2 ^ Nat.clog 2 m ≤ 2 ^ (c₂.nreg 218019 - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · exact Nat.clog_le_of_le_pow (by omega)
  have hk₂' : k₂ ≤ 4 * Nat.clog 2 m + 2 := by
    rwo [v19, Nat.sub_zero] at hk₂
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, hg, r₂, m₂, rr₂, rm₂, o₂⟩

end exec

end

end DrvP

end Chazelle.Core
