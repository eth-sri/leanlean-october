module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ClusterSplitMath
public import Chazelle.Core.ClusterPhase

/-!
# WP-I, part 28: the class test of a star dart on the RAM

`cpStmt`: for the star dart `X` (register `130630`) of the centroid face `f` (`130631`), compute
the parameters `mode`, `a`, `b` (registers `130637 … 130639`) of the class test
`ClassTest mode a b κ` (`mode = 1`: `a ≤ κ < b`; `mode = 2`: not so; `mode = 0`: never), which
is `inClass` of `ClusterSplitMath.lean` with root face `0` (`cpStmt_exec`).

Registers: static `130632` (`SOPP`), `130633` (`SFACE`), `130634` (`FPAR`), `130635` (`FPRE`),
`130636` (`FSZ`); scratch `130640 … 130642`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- The class test. -/
def ClassTest (mode a b κ : ℕ) : Prop :=
  (mode = 1 ∧ a ≤ κ ∧ κ < b) ∨ (2 ≤ mode ∧ ¬ (a ≤ κ ∧ κ < b))

/-- `if x = y then S`. -/
def eqThen (x y : ℕ) (S : Stmt) : Stmt := .ifLtN x y .skip (.ifLtN y x .skip S)

/-- The parameters of the down test. -/
def setDown : Stmt := block [.addN 130641 130635 130640, .loadN 130638 130641,
  .addN 130641 130636 130640, .loadN 130642 130641, .addN 130639 130638 130642,
  .constN 130637 1]

/-- The parameters of the up test. -/
def setUp : Stmt := block [.addN 130641 130635 130631, .loadN 130638 130641,
  .addN 130641 130636 130631, .loadN 130642 130641, .addN 130639 130638 130642,
  .constN 130637 2]

/-- The down test: the face `g` across `X` is not the root and `FPAR[g] = X`. -/
def downS : Stmt := .ifLtN 130009 130640
  (.seq (block [.addN 130641 130634 130640, .loadN 130641 130641]) (eqThen 130641 130630 setDown))
  .skip

/-- The up test (only if the down test failed): `f` is not the root and `SOPP[FPAR[f]] = X`. -/
def upS : Stmt := .ifLtN 130009 130637 .skip (.ifLtN 130009 130631
  (.seq (block [.addN 130641 130634 130631, .loadN 130641 130641, .addN 130641 130632 130641,
    .loadN 130641 130641]) (eqThen 130641 130630 setUp)) .skip)

/-- **The class parameters of the star dart `X` of `f`.** -/
def cpStmt : Stmt := .seq (block [.addN 130641 130632 130630, .loadN 130641 130641,
    .addN 130641 130633 130641, .loadN 130640 130641, .constN 130637 0])
  (.seq downS upS)

/-- The registers written by `cpStmt`. -/
def CpRG (r : ℕ) : Prop := (130637 ≤ r ∧ r ≤ 130642)

/-- The static memory of the class test. -/
structure CpMem (m : ℕ → ℕ) (W bSO bSF bFP bPR bSZ N : ℕ) : Prop where
  wSO : bSO + 3 * N ≤ W
  wSF : bSF + 3 * N ≤ W
  wFP : bFP + N ≤ W
  wPR : bPR + N ≤ W
  wSZ : bSZ + N ≤ W
  so_lt : ∀ x, x < 3 * N → m (bSO + x) < 3 * N
  sf_lt : ∀ x, x < 3 * N → m (bSF + x) < N
  fp_lt : ∀ g, g < N → m (bFP + g) < 3 * N
  prsz : ∀ g, g < N → m (bPR + g) + m (bSZ + g) ≤ W

section proofs

variable {P : Polygon} {W : ℕ}

/-- The equality test. -/
theorem eqThen_exec {S : Stmt} {c : Config} (hw : WordsBounded W c) (x y : ℕ)
    {R : Config → Prop} {K : ℕ}
    (hS : c.nreg x = c.nreg y → ∃ c' k, Exec P W S c c' k ∧ k ≤ K ∧ R c')
    (hne : c.nreg x ≠ c.nreg y → R c) :
    ∃ c' k, Exec P W (eqThen x y S) c c' k ∧ k ≤ K + 4 ∧ R c' := by
  unfold eqThen
  by_cases h1 : c.nreg x < c.nreg y
  · exact ⟨c, 0 + 1, .ifLtN_true h1 (.skip hw), by omega, hne (by omega)⟩
  · by_cases h2 : c.nreg y < c.nreg x
    · exact ⟨c, 0 + 1 + 2, .ifLtN_false h1 (.ifLtN_true h2 (.skip hw)), by omega, hne (by omega)⟩
    · obtain ⟨c', k, e, hk, hr⟩ := hS (by omega)
      exact ⟨c', k + 2 + 2, .ifLtN_false h1 (.ifLtN_false h2 e), by omega, hr⟩

/-- **The class parameters.** -/
theorem cpStmt_exec {c : Config} (hw : WordsBounded W c) (hzero : c.nreg 130009 = 0)
    {X f bSO bSF bFP bPR bSZ N : ℕ} (hX : c.nreg 130630 = X) (hf : c.nreg 130631 = f)
    (hSO : c.nreg 130632 = bSO) (hSF : c.nreg 130633 = bSF) (hFP : c.nreg 130634 = bFP)
    (hPR : c.nreg 130635 = bPR) (hSZ : c.nreg 130636 = bSZ)
    (hM : CpMem c.nmem W bSO bSF bFP bPR bSZ N) (hXN : X < 3 * N) (hfN : f < N) :
    ∃ c' k, Exec P W cpStmt c c' k ∧ k ≤ 45 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      (∀ r, ¬ CpRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧
      ∀ κ, ClassTest (c'.nreg 130637) (c'.nreg 130638) (c'.nreg 130639) κ ↔
        inClass (fun x => c.nmem (bSO + x)) (fun x => c.nmem (bSF + x))
          (fun x => c.nmem (bFP + x)) (fun x => c.nmem (bPR + x)) (fun x => c.nmem (bSZ + x))
          0 X f κ := by
  set sO : ℕ → ℕ := fun x => c.nmem (bSO + x)
  set sF : ℕ → ℕ := fun x => c.nmem (bSF + x)
  set fp : ℕ → ℕ := fun x => c.nmem (bFP + x)
  set pr : ℕ → ℕ := fun x => c.nmem (bPR + x)
  set sz : ℕ → ℕ := fun x => c.nmem (bSZ + x)
  have hsoX := hM.so_lt X hXN
  set g := sF (sO X)
  have hgN : g < N := hM.sf_lt _ hsoX
  have := hM.wSO; have := hM.wSF; have := hM.wFP; have := hM.wPR; have := hM.wSZ
  -- common frame facts
  have fr : ∀ c1 : Config, (∀ r, ¬ CpRG r → c1.nreg r = c.nreg r) →
      c1.nreg 130009 = 0 ∧ c1.nreg 130630 = X ∧ c1.nreg 130631 = f ∧ c1.nreg 130632 = bSO ∧
      c1.nreg 130633 = bSF ∧ c1.nreg 130634 = bFP ∧ c1.nreg 130635 = bPR ∧
      c1.nreg 130636 = bSZ := fun c1 h => by
    ram_simp
  -- the face across `X`
  obtain ⟨c1, k1, e1, hk1, hw1, h1g, h1m, h1r, hrr1, hrm1, ho1, hm1⟩ : ∃ c1 k1, Exec P W
      (block [.addN 130641 130632 130630, .loadN 130641 130641, .addN 130641 130633 130641,
        .loadN 130640 130641, .constN 130637 0]) c c1 k1 ∧ k1 = 5 ∧ WordsBounded W c1 ∧
      c1.nreg 130640 = g ∧ c1.nreg 130637 = 0 ∧ (∀ r, ¬ CpRG r → c1.nreg r = c.nreg r) ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output ∧ c1.nmem = c.nmem := by
    exec_block
    all_goals first | omega | (config_simp; grind) | skip
    grind [Machine.upd_apply, CpRG]
  obtain ⟨z1, x1, f1, so1, sf1, fp1, pr1, sz1⟩ := fr c1 h1r
  -- the down test
  obtain ⟨c2, k2, e2, hk2, hw2, h2r, h2m, hdown, hndown, hrr2, hrm2, ho2⟩ : ∃ c2 k2,
      Exec P W downS c1 c2 k2 ∧ k2 ≤ 16 ∧ WordsBounded W c2 ∧
      (∀ r, ¬ CpRG r → c2.nreg r = c.nreg r) ∧ c2.nmem = c.nmem ∧
      ((g ≠ 0 ∧ fp g = X) → c2.nreg 130637 = 1 ∧ c2.nreg 130638 = pr g ∧
        c2.nreg 130639 = pr g + sz g) ∧
      (¬ (g ≠ 0 ∧ fp g = X) → c2.nreg 130637 = 0) ∧
      c2.rreg = c.rreg ∧ c2.rmem = c.rmem ∧ c2.output = c.output := by
    unfold downS
    by_cases hg0 : c1.nreg 130009 < c1.nreg 130640
    · rw [z1, h1g] at hg0
      obtain ⟨c3, k3, e3, hk3, hw3, h3p, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3, Exec P W
          (block [.addN 130641 130634 130640, .loadN 130641 130641]) c1 c3 k3 ∧ k3 = 2 ∧
          WordsBounded W c3 ∧ c3.nreg 130641 = fp g ∧ (∀ r, r ≠ 130641 → c3.nreg r = c1.nreg r) ∧
          c3.rreg = c1.rreg ∧ c3.rmem = c1.rmem ∧ c3.output = c1.output ∧ c3.nmem = c1.nmem := by
        exec_block
        · omega
        · refine ⟨rfl, ‹_›, by config_simp; grind, fun r hr => ?_, rfl, rfl, rfl,
            rfl⟩
          simp only [Machine.upd_apply, hr, ite_false]
      have h3x : c3.nreg 130630 = X := (h3r _ (by omega)).trans x1
      have h3g : c3.nreg 130640 = g := (h3r _ (by omega)).trans h1g
      obtain ⟨c4, k4, e4, hk4, hR4⟩ := eqThen_exec (P := P) (S := setDown) hw3 130641 130630
        (R := fun c4 => WordsBounded W c4 ∧ (∀ r, ¬ CpRG r → c4.nreg r = c.nreg r) ∧
          c4.nmem = c.nmem ∧ ((g ≠ 0 ∧ fp g = X) → c4.nreg 130637 = 1 ∧ c4.nreg 130638 = pr g ∧
            c4.nreg 130639 = pr g + sz g) ∧ (¬ (g ≠ 0 ∧ fp g = X) → c4.nreg 130637 = 0) ∧
          c4.rreg = c.rreg ∧ c4.rmem = c.rmem ∧ c4.output = c.output) (K := 6)
        (fun heq => by
          rw [h3p, h3x] at heq
          have h3pr : c3.nreg 130635 = bPR := (h3r _ (by omega)).trans pr1
          have h3sz : c3.nreg 130636 = bSZ := (h3r _ (by omega)).trans sz1
          have hpg := hM.prsz g hgN
          unfold setDown
          exec_block
          all_goals first | omega | (config_simp; grind) |
            skip
          grind [Machine.upd_apply, CpRG])
        (fun hne => by
          ram_grind)
      obtain ⟨hw4, h4r, h4m, hd4, hnd4, hrr4, hrm4, ho4⟩ := hR4
      refine ⟨c4, k3 + k4 + 1, .ifLtN_true (by omega) (.seq e3 e4), by omega,
        hw4, h4r, h4m, hd4, hnd4, hrr4, hrm4, ho4⟩
    · rw [z1, h1g] at hg0
      refine ⟨c1, 0 + 2, .ifLtN_false (by omega) (.skip hw1), by omega, hw1,
        h1r, hm1, fun h => absurd h.1 (by omega), fun _ => h1m, hrr1, hrm1, ho1⟩
  obtain ⟨z2, x2, f2, so2, sf2, fp2, pr2, sz2⟩ := fr c2 h2r
  -- the up test
  obtain ⟨c5, k5, e5, hk5, hw5, h5r, h5m, h5test, hrr5, hrm5, ho5⟩ : ∃ c5 k5,
      Exec P W upS c2 c5 k5 ∧ k5 ≤ 20 ∧ WordsBounded W c5 ∧
      (∀ r, ¬ CpRG r → c5.nreg r = c.nreg r) ∧ c5.nmem = c.nmem ∧
      (∀ κ, ClassTest (c5.nreg 130637) (c5.nreg 130638) (c5.nreg 130639) κ ↔
        inClass sO sF fp pr sz 0 X f κ) ∧
      c5.rreg = c.rreg ∧ c5.rmem = c.rmem ∧ c5.output = c.output := by
    unfold upS
    by_cases hd : g ≠ 0 ∧ fp g = X
    · -- the down test succeeded
      obtain ⟨m1, ma, mb⟩ := hdown hd
      refine ⟨c2, 0 + 1, .ifLtN_true (by omega) (.skip hw2), by omega, hw2, h2r, h2m,
        fun κ => ?_, hrr2, hrm2, ho2⟩
      grind [inClass, ClassTest]
    · have m0 := hndown hd
      have hni : ∀ κ, inClass sO sF fp pr sz 0 X f κ ↔
          (f ≠ 0 ∧ sO (fp f) = X) ∧ ¬ (pr f ≤ κ ∧ κ < pr f + sz f) := by
        grind [inClass]
      by_cases hf0 : c2.nreg 130009 < c2.nreg 130631
      · rw [z2, f2] at hf0
        have hfpf := hM.fp_lt f hfN
        obtain ⟨c3, k3, e3, hk3, hw3, h3q, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3, Exec P W
            (block [.addN 130641 130634 130631, .loadN 130641 130641, .addN 130641 130632 130641,
              .loadN 130641 130641]) c2 c3 k3 ∧ k3 = 4 ∧ WordsBounded W c3 ∧
            c3.nreg 130641 = sO (fp f) ∧ (∀ r, r ≠ 130641 → c3.nreg r = c2.nreg r) ∧
            c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output ∧
            c3.nmem = c2.nmem := by
          exec_block
          all_goals first | omega | (config_simp; grind) | skip
          refine ⟨rfl, ‹_›, by config_simp; grind, fun r hr => ?_,
            rfl, rfl, rfl, rfl⟩
          simp only [Machine.upd_apply, hr, ite_false]
        have h3x : c3.nreg 130630 = X := (h3r _ (by omega)).trans x2
        obtain ⟨c4, k4, e4, hk4, hR4⟩ := eqThen_exec (P := P) (S := setUp) hw3 130641 130630
          (R := fun c4 => WordsBounded W c4 ∧ (∀ r, ¬ CpRG r → c4.nreg r = c.nreg r) ∧
            c4.nmem = c.nmem ∧ (∀ κ, ClassTest (c4.nreg 130637) (c4.nreg 130638)
              (c4.nreg 130639) κ ↔ inClass sO sF fp pr sz 0 X f κ) ∧
            c4.rreg = c.rreg ∧ c4.rmem = c.rmem ∧ c4.output = c.output) (K := 6)
          (fun heq => by
            rw [h3q, h3x] at heq
            have h3pr : c3.nreg 130635 = bPR := (h3r _ (by omega)).trans pr2
            have h3sz : c3.nreg 130636 = bSZ := (h3r _ (by omega)).trans sz2
            have h3f : c3.nreg 130631 = f := (h3r _ (by omega)).trans f2
            have hpf := hM.prsz f hfN
            unfold setUp
            exec_block
            all_goals first | omega | (config_simp; grind) |
              skip
            refine ⟨le_refl _, ‹_›, fun r hr => ?_, by grind, fun κ => ?_,
              by grind, by grind, by grind⟩
            · grind [Machine.upd_apply, CpRG]
            · rw [hni]
              config_simp
              grind [ClassTest])
          (fun hne => by
            grind [CpRG, ClassTest])
        obtain ⟨hw4, h4r, h4m, h4t, hrr4, hrm4, ho4⟩ := hR4
        refine ⟨c4, _, .ifLtN_false (show ¬ c2.nreg 130009 < c2.nreg 130637 by omega)
          (.ifLtN_true (show c2.nreg 130009 < c2.nreg 130631 by omega) (.seq e3 e4)), by omega, hw4, h4r, h4m, h4t,
          hrr4, hrm4, ho4⟩
      · rw [z2, f2] at hf0
        refine ⟨c2, 0 + 2 + 2, .ifLtN_false (show ¬ c2.nreg 130009 < c2.nreg 130637 by omega)
          (.ifLtN_false (show ¬ c2.nreg 130009 < c2.nreg 130631 by omega)
            (.skip hw2)), by omega, hw2, h2r, h2m,
          fun κ => ?_, hrr2, hrm2, ho2⟩
        grind [ClassTest]
  refine ⟨c5, k1 + (k2 + k5), .seq e1 (.seq e2 e5), by omega, hw5, h5m, h5r, hrr5, hrm5, ho5,
    h5test⟩

end proofs

end

end Chazelle.Core.Cluster
