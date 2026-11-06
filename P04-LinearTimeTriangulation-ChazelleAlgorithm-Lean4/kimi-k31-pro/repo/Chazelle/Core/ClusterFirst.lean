module

public import Chazelle.Core.ClusterPhase
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.MiscTactics

/-!
# WP-I, part 13: a dart at every vertex

`firstStmt`: for `d = 0, …, N - 1`, `FIRST[VERT[d]] := d`.  Afterwards every vertex hit by the
tail array has its last dart recorded (`firstStmt_exec`): `FIRST[u] < N` and `VERT[FIRST[u]] = u`.

Registers: `130221` base of `VERT`, `130222` base of `FIRST`, `130223` `N`; scratch `130224`
(counter), `130225`, `130226`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- One dart: `FIRST[VERT[d]] := d`. -/
def firstBody : Stmt := block [.addN 130225 130221 130224, .loadN 130226 130225,
  .addN 130225 130222 130226, .storeN 130225 130224, .addN 130224 130224 130001]

/-- **The first darts.** -/
def firstStmt : Stmt := .seq (.instr (.constN 130224 0)) (.whileLtN 130224 130223 firstBody)

/-- The registers written. -/
def FirstRG (r : ℕ) : Prop := 130224 ≤ r ∧ r ≤ 130226

section proofs

variable {P : Polygon} {W : ℕ}

/-- **The first darts**: if the tails of the `N` darts are below `nv` and every vertex `u < nv`
is a tail, then afterwards `FIRST[u] < N` and `VERT[FIRST[u]] = u` for all `u < nv`, in at most
`7 N + 3` steps, writing only `FIRST` (and the scratch registers). -/
theorem firstStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {bV bF N nv : ℕ} (hbV : c.nreg 130221 = bV) (hbF : c.nreg 130222 = bF) (hN : c.nreg 130223 = N)
    (hvlt : ∀ d, d < N → c.nmem (bV + d) < nv) (hsurj : ∀ u, u < nv → ∃ d, d < N ∧ c.nmem (bV + d) = u)
    (hdisj : bF + nv ≤ bV ∨ bV + N ≤ bF) (hwV : bV + N ≤ W) (hwF : bF + nv ≤ W) (hwN : N + 1 ≤ W) :
    ∃ c' k, Exec P W firstStmt c c' k ∧ k ≤ 7 * N + 3 ∧
      PFr FirstRG (fun a => bF ≤ a ∧ a < bF + nv) c c' ∧
      ∀ u, u < nv → c'.nmem (bF + u) < N ∧ c.nmem (bV + c'.nmem (bF + u)) = u := by
  have e0 := Exec.constN (P := P) hw 130224 0 (by omega)
  obtain ⟨c', k, e, hk, hw', hi', hn', hf', hI⟩ := forN (P := P) (W := W) (ri := 130224)
    (rn := 130223) (body := firstBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130224 = j ∧ c'.nreg 130223 = N ∧
      PFr FirstRG (fun a => bF ≤ a ∧ a < bF + nv) c c' ∧
      ∀ u, u < nv → (∃ d, d < j ∧ c.nmem (bV + d) = u) →
        c'.nmem (bF + u) < j ∧ c.nmem (bV + c'.nmem (bF + u)) = u)
    N 5 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c2 hj ⟨hw2, hi2, hn2, hf2, hI2⟩ => by
      have r1 : c2.nreg 130221 = bV := (hf2.1 _ (by ufo FirstRG)).trans hbV
      have r2 : c2.nreg 130222 = bF := (hf2.1 _ (by ufo FirstRG)).trans hbF
      have r3 : c2.nreg 130001 = 1 := (hf2.1 _ (by ufo FirstRG)).trans hone
      have rv : c2.nmem (bV + j) = c.nmem (bV + j) := hf2.2.2.2.2 _ (by omega)
      have hvj := hvlt j hj
      unfold firstBody
      exec_block
      · rwo [r1, hi2]
      · config_simp; rwo [r2, r1, hi2, rv]
      · config_simp; rwo [hi2, r3]
      · refine ⟨le_refl _, ‹_›, by config_simp; rw [hi2, r3], by config_simp; exact hn2, ?_, ?_⟩
        · refine PFr.of_eq hf2 (fun r hr => ?_) (fun a ha => ?_)
          · simp only [Machine.upd_apply]; unfold FirstRG at hr; splao
          · rw [r2, r1, hi2, rv, Machine.upd_other _ _ _ (by omega)]
        · intro u hu hex
          config_simp
          rw [r2, r1, hi2, rv, Machine.upd_apply]
          split_ifs with h
          · have hu' : c.nmem (bV + j) = u := by omega
            exact ⟨by omega, hu'⟩
          · obtain ⟨d, hd, hdu⟩ := hex
            have hdj : d < j := by
              rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | rfl
              · exact hd
              · exact absurd (by rw [hdu]) h
            have := hI2 u hu ⟨d, hdj, hdu⟩
            exact ⟨by omega, this.2⟩)
    (j₀ := 0) ⟨e0.wb_right, by simp, by simp [hN], PFr.nreg (PFr.refl c) (fun r hr => by
      simp only [Machine.upd_apply]; unfold FirstRG at hr; splao),
      fun u hu ⟨d, hd, _⟩ => absurd hd (Nat.not_lt_zero d)⟩ (Nat.zero_le _)
  refine ⟨c', 1 + k, .seq e0 e, by omega, hf', fun u hu => hI u hu (hsurj u hu)⟩

end proofs

end

end Chazelle.Core.Cluster
