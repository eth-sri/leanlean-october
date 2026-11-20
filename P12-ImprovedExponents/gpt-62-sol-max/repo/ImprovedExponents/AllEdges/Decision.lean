module

import ThreeSumApsp.Lang.Symbolic
import ThreeSumApsp.Lang.Lib.Any

public import ImprovedExponents.AllEdges.Model
public import ImprovedExponents.AllEdges.Host.BruteAE
public import ImprovedExponents.Pipeline.HostBound
public import ThreeSumApsp.Lang.PolyBounded

@[expose] public section

namespace ImprovedExponents.AllEdges

open Light ThreeSumApsp ThreeSumApsp.Spec

private def decisionScan : Stmt := anyPass 7 6 0 (M (v 5 +' v 7) =' k 1)

private theorem scan_spec {lim : Limits} {P : Program} {d m fr : ℕ} {loc μ : ℕ → ℤ}
    (hfr : loc 5 = fr) (hm : loc 6 = m) (hcap : fr + m ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word) :
    Ends lim P d decisionScan ⟨loc, μ⟩ (30 * m + 10)
      fun σ => σ.mem = μ ∧ σ.loc 0 = flag (∃ j < m, μ (fr + j) = 1) :=
  Ends.anyPass _ (fun j => μ (fr + j) = 1) (by intro j hj; light_side [hfr]) (by simp) hm (by omega) h1

private theorem flag_scan_eq {n fr : ℕ} {AB BC AC : List ℤ} {μ : ℕ → ℤ}
    (h : Seg μ fr (aeFlags n AB BC AC)) :
    flag (∃ q < n * n, μ (fr + q) = 1) = flag (triOf n AB BC AC).HasZeroTriangle := by
  apply flag_congr
  have read q (hq : q < n * n) : μ (fr + q) =
      flag (∃ c < n, AB.getD q 0 + BC.getD (q % n * n + c) 0 + AC.getD (q / n * n + c) 0 = 0) := by
    have hi : q < (aeFlags n AB BC AC).length := by simpa
    rw [← aeFlags_getD _ _ _ hq, h q hi]
    rw [List.getD_eq_getElem?_getD, getElem?_pos (aeFlags n AB BC AC) q hi, Option.getD_some]
  constructor
  · rintro ⟨q, hq, hq1⟩
    have hn : 0 < n := by contrapose! hq; simp [Nat.eq_zero_of_le_zero hq]
    obtain ⟨c, hc, hz⟩ := flag_eq_one_iff.mp ((read q hq).symm.trans hq1)
    refine ⟨⟨q / n, Nat.div_lt_of_lt_mul hq⟩, ⟨q % n, Nat.mod_lt _ hn⟩, ⟨c, hc⟩, ?_⟩
    have hsplit : q / n * n + q % n = q := by simpa [Nat.mul_comm] using Nat.div_add_mod q n
    simpa [TriangleInstance.IsZeroTriangle, TriangleInstance.S, triOf, hsplit] using hz
  · rintro ⟨a, b, c, hz⟩
    refine ⟨a * n + b, Nat.mul_add_lt_mul a.isLt b.isLt, ?_⟩
    rw [read _ (Nat.mul_add_lt_mul a.isLt b.isLt), flag_eq_one_iff,
      Nat.mul_add_div_of_lt b.isLt, Nat.mul_add_mod_of_lt b.isLt]
    exact ⟨c, c.isLt, hz⟩

private def decisionBody (p : ℕ) : Stmt :=
  .set 6 (v 0 *' v 0) ;;
  .call p [v 0, v 1, v 2, v 3, v 4, v 5, v 5 +' v 6] 8 ;;
  decisionScan

private def decisionTime (T : ℕ → ℕ → ℕ) (n U : ℕ) := T n U + 30 * (n * n) + 40

private def decisionNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need :=
  ⟨1 + (r n U).word, n * n + (r n U).cells, 1 + (r n U).depth⟩

private theorem isHost_decision : IsHost aeTask etTask decisionTime decisionNeed := by
  refine ⟨?_, fun r hr => ?_⟩
  · intro P p T r hs
    refine ⟨[decisionBody p], P.length, decisionBody p, by simp,
      fun R lim d x μ fr hpre hok => ?_⟩
    change TriInst.Pre x μ fr at hpre
    change (decisionNeed r x.n x.U).Ok lim fr d at hok
    let a := AeInst.scratch x fr
    have hc := hok.cells
    have hw := hok.space
    have h1 := hok.word
    have hd := hok.depth
    simp only [decisionNeed, Nat.cast_add, Nat.cast_one] at hc h1 hd
    have hokA : (r x.n x.U).Ok lim (fr + x.n * x.n) (d + 1) :=
      ⟨by omega, by omega, hw, by omega⟩
    have hcap : fr + x.n * x.n ≤ lim.space := by omega
    have hn : (x.n * x.n : ℤ) ≤ lim.word := by
      exact_mod_cast (Nat.cast_le.2 (by omega : x.n * x.n ≤ lim.space)).trans hw
    rw [List.append_assoc]
    unfold decisionBody
    simp only [decisionTime, etTask]
    light_step
    light_call (hs.meets ([decisionBody p] ++ R) (task := aeTask) a (fr + x.n * x.n) (AeInst.scratch_pre hpre) hokA)
      using aeTask, a with _ μ' ⟨hseg, hkept⟩
    refine Ends.pieceLast (scan_spec (by simp) (by simp) hcap hw (by omega)) ?_
      (hT := by light_time [decisionTime, etTask, aeTask, a])
    rintro σ ⟨rfl, hv⟩
    exact ⟨hv.trans (flag_scan_eq hseg), fun q hq => hkept q ⟨by omega, Or.inl hq⟩⟩
  · refine PolyBounded.polyNeed ?_ ?_ ?_ <;> unfold decisionNeed <;>
      growth_poly [hr.word, hr.cells, hr.depth]

/-- The small-size decision solver is the same brute force used by the all-edges host,
followed by the same flag scan as the fast solver. -/
theorem claim_bruteForce : Claim.BruteForce lightModel := by
  obtain ⟨R, p, hs⟩ := isHost_decision.1 _ _ _ _ bruteAE_solves
  refine ⟨320, _, p, _, _, isHost_decision.2 bruteNeed ?_, hs, ?_⟩
  · apply PolyBounded.polyNeed <;> unfold bruteNeed <;> growth_poly []
  · intro n U u hn _ _
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ h1
    have h2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := pow_le_pow_right₀ h1 (by decide)
    have hlog := one_le_one_add_logU u
    unfold decisionTime tBruteAE
    push_cast
    calc 110 * (n : ℝ) ^ 3 + 100 + 30 * (n * n) + 40 ≤ 320 * (n : ℝ) ^ 3 := by nlinarith
      _ ≤ 320 * ((n : ℝ) ^ 3 * (1 + logU u)) := by
        gcongr
        exact le_mul_of_one_le_right (by positivity) hlog

/-- One scan of the all-edges output yields a decision solver, costing only quadratic overhead. -/
theorem explicitFrom_decision {δ : ℝ} (hδ : δ ≤ 1)
    (h : ExplicitFrom lightModelAE δ 1) : ExplicitFrom lightModel δ 1 := by
  obtain ⟨n₀, K, T, hT, hbound⟩ := h
  refine ⟨max n₀ 3, K + 70, fun n u => T n u + 30 * (n : ℝ) ^ 2 + 40,
    isHost_decision.solvedIn hT (fun _ hTn n U u hn hU hu => ?_), ?_⟩
  · unfold decisionTime
    push_cast
    linarith [hTn n U u hn hU hu]
  · intro n κ u hn hκ hu
    have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.2 (by omega)
    have hl := Real.one_le_log_natCast_of_three_le (show 3 ≤ n by omega)
    have hp : (n : ℝ) ^ 2 ≤ κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ 1) := by
      rw [← one_mul ((n : ℝ) ^ 2), ← mul_one ((n : ℝ) ^ 2), pow_one, ← Real.rpow_ofNat]
      gcongr <;> linarith
    have hn2 : 1 ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
    linarith [hbound n κ u (by omega) hκ hu]

end ImprovedExponents.AllEdges
