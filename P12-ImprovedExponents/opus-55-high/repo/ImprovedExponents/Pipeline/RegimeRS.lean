
import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Sizes
import ImprovedExponents.Pipeline.ThinClaim


/-!
# A regime test with a rational exponent

The solver of `ImprovedExponents.Pipeline.ThinClaim` is generic in its regime test. Upstream's test
decides `D^18 ≤ N`. This file adds, for natural numbers `r` and `s`, a procedure `testRS r s` that
decides `D^r ≤ N^s`: it computes `N^s` by a loop and calls upstream's `powLt` (which computes `D^r`
without ever exceeding its bound). The three procedures `powLt`, `testRS r s` and the solver that
calls it (`allRSBody`) are appended to `program31 G` (`programRS G r s`).

The result is `thinClaimRS_of_offlineWithin`: the thin product is solved within the bounds of the
offline routine on the instances with `D ≤ N^ε`, for `ε ≤ s/r`, if the tile fits in the whole
regime `D^r ≤ N^s` (`FitsRS G r s`). `thinClaimRS_of_offlineWithinT` is the same for any offline
routine (`OfflineRoutine`) in a program that begins with `programRS G r s`; it serves the pruned
routine of `ImprovedExponents.PrunedProgram`, whose solver is `allBody Proc.testRS Proc.offline32P`.
-/

namespace ImprovedExponents

open Light Light.Sec3 Light.Sec4

/-! ## The procedures -/

namespace Proc

/- The number of `powLt` in `programRS`. -/
slots 74 powRS
/- The number of `testRS r s` in `programRS`. -/
slots 75 testRS
/- The number of the solver in `programRS`. -/
slots 76 allRS

end Proc

/-- testRS(N, D) returns 1 if `D^r ≤ N^s` and 0 if not. Local 2 counts, local 3 is `N^count`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Sizes.lean (powLtBody) and
-- ThreeSumApsp/Programs/Sec2/Theorem5/AllInstances/RegimeTest.lean (regimeExp)
def testRSBody (r s : ℕ) : Stmt :=
  .set 2 (k 0) ;;
  .set 3 (k 1) ;;
  .while (v 2 <' k s) (.set 3 (v 3 *' v 0) ;; .set 2 (v 2 +' k 1)) ;;
  .set 3 (v 3 +' k 1) ;;
  .call Proc.powRS [v 1, k r, v 3] 0

/-- The solver with the test `testRS` and upstream's routine `offline32`: `allInstances26Body`
pointed at `testRS`. -/
def allRSBody : Stmt := allBody Proc.testRS Proc.offline32

/-- `program31 G` followed by `powLt`, `testRS r s` and the solver. -/
def programRS (G : RatParams) (r s : ℕ) : Program :=
  program31 G ++ [powLtBody, testRSBody r s, allRSBody]

/-- The largest number that `testRS r s` forms on `N`, `D`. -/
def wordRS (r s N D : ℕ) : ℕ := N ^ s * D + N ^ s + D + r + s + 100

/-- The running time of `testRS r s`. -/
def tTestRS (r s : ℕ) : ℕ := 12 * s + 16 * r + 40


/-- The three new procedures stand at their numbers. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean (program31_at)
theorem programRS_at (G : RatParams) (r s : ℕ) :
    (programRS G r s)[Proc.powRS]? = some powLtBody ∧
      (programRS G r s)[Proc.testRS]? = some (testRSBody r s) ∧
      (programRS G r s)[Proc.allRS]? = some allRSBody := by
  aesop

variable {P : Program}

variable (r s : ℕ)

/-! ## The test -/

/-- **testRS** returns 1 if `D^r ≤ N^s` and 0 if not, and changes no cell. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Sizes.lean (powLt_meets)
-- and ThreeSumApsp/Programs/Sec2/Theorem5/AllInstances/RegimeTest.lean (regimeExp_spec)
theorem testRS_meets {lim : Limits} {d : ℕ}
    (hP : P[Proc.testRS]? = some (testRSBody r s)) (hpow : P[Proc.powRS]? = some powLtBody)
    (hd : d + 1 ≤ lim.depth) (N D : ℕ) (hN : 1 ≤ N) (hD : 1 ≤ D)
    (hword : ((wordRS r s N D : ℕ) : ℤ) ≤ lim.word) (μ : ℕ → ℤ) :
    Meets lim P Proc.testRS d [N, D] μ (tTestRS r s) fun r' μ' =>
      μ' = μ ∧ ((r' = 1 ∧ D ^ r ≤ N ^ s) ∨ (r' = 0 ∧ N ^ s < D ^ r)) := by
  refine .of_body hP ?_
  unfold wordRS at hword
  push_cast at hword
  have hNsD : 0 ≤ (N : ℤ) ^ s * D := by positivity
  have hNs : 0 ≤ (N : ℤ) ^ s := by positivity
  unfold testRSBody tTestRS
  -- cnt := 0; acc := 1
  light_set 0
  light_set 1
  -- while cnt < s: acc := acc * N; cnt := cnt + 1.  Before round i, cnt = i and acc = N^i.
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [N, D, i, (N ^ i)], μ⟩) s (by simp) ?_ ?_
    le_rfl) (by simp; omega)
  ·
    rintro i _ hi rfl
    have hle : N ^ (i + 1) ≤ N ^ s := Nat.pow_le_pow_right hN hi
    have hleZ : N ^ i * N ≤ (N : ℤ) ^ s := by
      rw [← pow_succ]
      linarith
    have hpos : 0 ≤ (N : ℤ) ^ i * N := by positivity
    exact ⟨by light_side, by light_side, ⟨by light_side, by light_side⟩,
      by simp [update_frame_setLocal, pow_succ]⟩
  ·
    rintro _ rfl
    refine ⟨by light_side, by light_side, ?_⟩
    -- acc := acc + 1
    light_set (N ^ s + 1)
    -- powLt(D, r, N^s + 1)
    have hcall := powLt_meets (lim := lim) (d := d + 1) (μ := μ) (e := r)
      (t := N ^ s + 1) hpow hD (by grind)
    refine Ends.callTo hcall fun r' μ' h => ?_
    aesop

/-! ## The regime test and the claim -/

/-- The number `testRS r s` forms is polynomial in `N`, `D`. -/
theorem wordRS_poly (N D : ℕ) :
    wordRS r s N D ≤ 2 ^ (8 + r + s) * ((N + 1) * (D + 1)) ^ (s + 1) := by
  set Q := (N + 1) * (D + 1) with hQ
  have hQ1 : 1 ≤ Q := by grind
  have hNQ : N ≤ Q := by nlinarith
  have hDQ : D ≤ Q := by nlinarith
  have hQp : 1 ≤ Q ^ (s + 1) := by grind
  have hNs : N ^ s ≤ Q ^ (s + 1) :=
    (Nat.pow_le_pow_left hNQ s).trans (by grind)
  have h1 : N ^ s * D ≤ Q ^ (s + 1) := by
    calc N ^ s * D ≤ Q ^ s * Q := Nat.mul_le_mul (Nat.pow_le_pow_left hNQ s) hDQ
      _ = Q ^ (s + 1) := by grind
  have h2 : D ≤ Q ^ (s + 1) := by grind [Nat.le_self_pow]
  have hrs : r + s + 100 ≤ 128 * 2 ^ (r + s) := by
    grind [Nat.lt_two_pow_self]
  have hpow : 2 ^ (8 + r + s) * Q ^ (s + 1) = 256 * (2 ^ (r + s) * Q ^ (s + 1)) := by
    grind
  have hX1 : Q ^ (s + 1) ≤ 2 ^ (r + s) * Q ^ (s + 1) :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hX2 : 128 * 2 ^ (r + s) ≤ 128 * (2 ^ (r + s) * Q ^ (s + 1)) :=
    by simp_all
  unfold wordRS
  omega

/-- **The regime test `D^r ≤ N^s`**, as a `RegimeTest`. -/
def regimeRS (r s : ℕ) : RegimeTest := ⟨fun N D => D ^ r ≤ N ^ s, Proc.testRS, testRSBody r s, fun P => P[Proc.powRS]? = some powLtBody, fun _ Q h => getElem?_append_of_eq_some h Q, tTestRS r s, wordRS r s, ⟨8 + r + s, s + 1, wordRS_poly r s⟩, fun haux hP hd N D hN hD hword μ => (testRS_meets r s hP haux hd N D hN hD hword μ).mono le_rfl fun r' μ' h =>
      ⟨h.1, h.2.imp id fun h' => ⟨h'.1, by omega⟩⟩⟩

/-- In the whole regime `D^r ≤ N^s`, the hypotheses of Theorem 30 hold at the parameters `G` from
the threshold on. -/
def FitsRS (G : RatParams) (r s : ℕ) : Prop :=
  ∀ N D₀ : ℕ, D₀ ^ r ≤ N ^ s → G.m₀ ≤ logFour D₀ → Hyp30 (parOf G N D₀) (switchOf31 G D₀)

/-- **The thin-product claim from an offline routine `O`, with the test `D^r ≤ N^s`.** If the
regime `D^r ≤ N^s` lies where the routine is specified, the instances with `D ≤ N^ε` lie in the
regime (`ε ≤ s/r`), and the routine stays within its bounds there, then the thin product is solved
within these bounds by the procedure `pAll` of a program that begins with `program31 G` and holds
`allBody Proc.testRS O.proc`, the routine and the procedures it calls. -/
theorem thinClaimRS_of_offlineWithinT {G : RatParams} {O : OfflineRoutine}
    {pAll r s : ℕ} {ε γ q : ℝ} (hr : 1 ≤ r) (hfit : ∀ N D : ℕ, D ^ r ≤ N ^ s → O.Ok N D)
    (hP : ∃ Q, P = programRS G r s ++ Q) (hall : P[pAll]? = some (allBody Proc.testRS O.proc))
    (hoff : P[O.proc]? = some O.body) (hauxO : O.aux P) (hε : ε ≤ (s : ℝ) / r)
    (h : OfflineWithinT O.time ε γ q) : ThinClaim lightModel ε γ q := by
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨hpow, htest, -⟩ := programRS_at G r s
  exact thinClaimR_of_offlineWithin (R := regimeRS r s) hfit hall
    (by assumption) (by assumption) hoff hauxO
    (by rfl)
    (fun N D₀ hN _ hDN => pow_le_pow_of_le_rpow hr hε hN hDN) h
