module
public import ImprovedExponents.Pipeline.HostBound
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Program
public import ThreeSumApsp.RunningTimes.FromClaims.Bounds
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22.ThreeSumLayout

/-! The direct hash reduction uses a *growing* side: the square of the side
already dominates the original input length. Hence the same eventually-fast
triangle solver covers every sufficiently large call, even after converting
the weight bound to a polynomial in the call's own size. There is no need to
uniformize the solver by linking a separate small-size algorithm. -/
@[expose] public section
namespace ImprovedExponents
open ThreeSumApsp ThreeSumApsp.WordRam Light Light.Sec3 Light.Sec3.ChanHe Filter

private theorem side_lower (k n : ℕ) : Nat.sqrt n+1 ≤ sideAt k n := by
  unfold sideAt ThreeSumApsp.ChanHe.mPar
  have h : Nat.sqrt n+1 ≤ ThreeSumApsp.ChanHe.wPar n (boundAt k n) :=
    Nat.le_mul_of_pos_left _ (by unfold ThreeSumApsp.ChanHe.Lam; positivity)
  exact h.trans ((Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (by positivity)))

private theorem mag_le (k n : ℕ) (hn : 1≤n) : magAt k n ≤ (sideAt k n)^(2*k+4) := by
  have w := side_lower k n
  have sq : n ≤ (sideAt k n)^2 := (Nat.lt_succ_sqrt n).le.trans (by rw [sq]; gcongr)
  have p := Nat.one_le_pow k n hn
  have two : 2 ≤ sideAt k n := by have := Nat.sqrt_pos.mpr hn; omega
  calc magAt k n ≤ n^k*11 := by unfold magAt boundAt; omega
       _ ≤ ((sideAt k n)^2)^k * 2^4 := by gcongr <;> norm_num
       _ ≤ (sideAt k n)^(2*k+4) := by rw [pow_add,pow_mul]; gcongr

theorem threeSum_of_explicitFrom {δ a : ℝ} {e : ℕ} (ex : ExplicitFrom lightModel δ e)
    (hδ : δ ≤ 1) (ha : 2-δ/2 < a) : SolvedInTime EndStatement.ThreeSum a 0 := by
  obtain ⟨n₀,K,T,et,hT⟩ := ex
  apply FromClaims.solvedInTime_of_claim realized_threeSum
  intro κ _
  let k := ⌈κ⌉₊
  obtain ⟨U,hU,run⟩ := fixedBound isHost_s3 κ k (Nat.le_ceil _) et
  let m := sideAt k
  let pow := 2*k+4
  have sz := (ThreeSumApsp.ChanHe.softO_mPar k).isPowPolylog (a:=1/2) (by norm_num)
  have exe := (((isPowPolylog_rpow_mul_log_pow (3-δ) e).const_mul pow).const_mul K).isPowLittleO.comp sz.isPowLittleO (by linarith) (by norm_num)
  have count := ((ClaimF.softO_callsAt k).isPowPolylog (a:=1/2) (by norm_num)).isPowLittleO
  have own := ((ClaimF.softO_ownAt k).isPowPolylog (a:=3/2) (by norm_num)).isPowLittleO
  have total := (own.mono (b:=2-δ/2) (by linarith)).add ((count.mul exe).mono (b:=2-δ/2) (by linarith))
  refine ⟨U,hU,(total.upperPowLittleO.mono_left ?_).upperBigOPow ha⟩
  filter_upwards [eventually_ge_atTop (n₀*n₀),eventually_ge_atTop 1] with n hn hn1
  have threshold := (Nat.le_sqrt.mpr hn).trans ((Nat.le_succ _).trans (side_lower k n))
  refine (run _ hn1).trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)))
  apply hT _ (pow:ℝ) _ threshold (by dsimp [pow]; push_cast; linarith [Nat.cast_nonneg k (α:=ℝ)])
  exact_mod_cast mag_le k n hn1
end ImprovedExponents
