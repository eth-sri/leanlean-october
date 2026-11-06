
import ImprovedExponents.Pipeline.ThinClaim
import ImprovedExponents.PrunedProgram.Wrapper.Offline


/-!
# The pruned offline routine solves the thin-product task

`offline32P_meets_thinTask` is `offline32_meets_thinTask` (`ImprovedExponents.Pipeline.ThinClaim`)
for the pruned routine: where the hypotheses of Theorem 30 hold from the threshold on, a program
in which `offline32P` meets `OfflineSpec32P` solves the thin-product task within `tOffline32P`.
The limits the routine needs are upstream's (`Lim31`), since the pruned shared stage has the same
layout and forms the same numbers, so `lim31_of_need` applies verbatim.
-/

namespace ImprovedExponents

open Light Light.Sec4

/-- **Where the hypotheses of Theorem 30 hold from the threshold on**, the pruned offline routine
solves the task. -/
-- adapted from ImprovedExponents/Pipeline/ThinClaim.lean (offline32_meets_thinTask)
theorem offline32P_meets_thinTask {lim : Limits} {P : Program} {G : RatParams} {c d : ℕ}
    (task : OfflineSpec32P lim P c G) {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hfit : G.m₀ ≤ logFour x.D → Hyp30 (parOf G x.N x.D) (switchOf31 G x.D))
    (ok : (offline32Need G x.N x.D x.U).Ok lim fr d) :
    Meets lim P Proc.offline32P (d + 1) [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
      (tOffline32P c G x.N x.D x.w) fun r μ' => thinTask.Post x μ fr r μ' := by
  have hU0 : 0 ≤ (x.U : ℤ) := by positivity
  have hdepth : d + G.a * (4 * x.D) + 12 ≤ lim.depth := ok.depth
  have hL :=
    (ratParams_L_le_mul G _).trans (Nat.mul_le_mul_left _ (logFour_le_four_mul hpre.D_pos))
  have spec := task x.N x.D x.x x.y x.wi x.wj x.out fr (thinMX x) (thinMY x) x.U x.U μ
    x.WI x.WJ
    ⟨hpre.D_pos, hpre.N_pos, lim31_of_need hpre.D_pos hfit ok, fun i j => hpre.leX.abs_getD_le hU0 _, fun i j => hpre.leY.abs_getD_le hU0 _, hpre.belowX, hpre.belowY⟩
    ⟨matAt_thinMX hpre, matAt_thinMY hpre, hpre.segWI, hpre.segWJ, by rw [hpre.lenWI, hpre.lenWJ], hpre.ltWI, hpre.ltWJ, by rw [hpre.lenWI]; exact hpre.belowWI, by rw [hpre.lenWI]; exact hpre.belowWJ, by rw [hpre.lenWI]; exact hpre.belowOut, by rw [hpre.lenWI]; exact hpre.apartX, by rw [hpre.lenWI]; exact hpre.apartY, by rw [hpre.lenWI]; exact hpre.apartWI, by rw [hpre.lenWI]; exact hpre.apartWJ⟩
  rw [hpre.lenWI, map_entryN_thin hpre] at spec
  exact (spec _ (by omega)).mono le_rfl fun r μ' h => ⟨h.1, fun a ha => by simp_all⟩

/-- The time of the pruned offline routine is monotone in the number of wanted positions. -/
-- adapted from ImprovedExponents/Pipeline/ThinClaim.lean (tOffline32_mono)
theorem tOffline32P_mono (c : ℕ) (G : RatParams) (N D₀ : ℕ) {w w' : ℕ} (hw : w ≤ w') :
    tOffline32P c G N D₀ w ≤ tOffline32P c G N D₀ w' := by
  unfold tOffline32P
  simp_all
