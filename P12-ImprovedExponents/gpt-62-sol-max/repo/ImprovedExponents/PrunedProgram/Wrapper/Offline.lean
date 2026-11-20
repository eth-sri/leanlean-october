module

import ThreeSumApsp.Lang.Symbolic

public import ImprovedExponents.PrunedProgram.Wrapper.Preprocessing

@[expose] public section

/-!
# Corollary 32 with the pruned encoder: the offline routine

Upstream's `offline32` (`ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean`) runs the
preprocessing and then asks one query for each wanted position.  `offline32P` is the same text with
`pre31P` in place of `pre31`; its specification `OfflineSpec32P` is upstream's `OfflineSpec32` for
the procedure `Proc.offline32P` with the time `tOffline32P`, and the proof is upstream's with
`PreSpec31P`, `QuerySpec31P` and `Ready31P`.

Adapted from upstream (Apache-2.0).
-/

namespace Light.Sec4

open ImprovedExponents

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

open Offline32 in
/-- offline32P(N, D, w, U, x, y, wi, wj, out, fr): preprocess with the pruned encoder, then ask one
query for each wanted position and store its answer. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean (offline32Body)
def offline32PBody : Stmt :=
  .call Proc.pre31P [v Size, v Dim, v MatX, v MatY, v Free] Res ;;
  .for Pos (v Count) offlineAsk32

/-- What a query needs depends only on the cells of X, of Y, and on the cells from fr on. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean (ready31_congr)
theorem ready31P_congr (h : Ready31P G X Y aX aY fr μ)
    (hX : ∀ a, aX ≤ a → a < aX + N * D₀ → μ' a = μ a)
    (hY : ∀ a, aY ≤ a → a < aY + D₀ * N → μ' a = μ a) (hfr : ∀ a, fr ≤ a → μ' a = μ a) :
    Ready31P G X Y aX aY fr μ' := by
  refine ⟨h.matX.congr hX, h.matY.congr hY, fun hs => ?_, fun hl => ?_⟩
  · simpa only [hfr _ le_rfl] using h.small hs
  · obtain ⟨h1, h2, h3⟩ := h.large hl
    exact ⟨by rwa [hfr _ le_rfl], by rwa [hfr _ (by omega)],
      dsReadyP_congr h3 fun a ha => hfr a (by unfold blockAt at ha; omega)⟩

/-- offline32P writes the wanted entries of XY to out. Below fr it changes only the output; nothing
is assumed about the cells from fr on. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean (OfflineSpec32)
def OfflineSpec32P (lim : Limits) (P : Program) (c : ℕ) (G : RatParams) : Prop :=
  ∀ (N D₀ aX aY aI aJ out fr : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ)
    (U : ℤ) (u : ℤ) (μ : ℕ → ℤ) (WI WJ : List ℕ),
    Input31 lim G X Y aX aY fr U → OfflineInput32 X Y aX aY aI aJ out fr WI WJ μ →
    ∀ d, d + (G.L (logFour D₀) + 8) ≤ lim.depth → Meets lim P Proc.offline32P d
      [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr] μ (tOffline32P c G N D₀ WI.length)
      fun _ μ' => Seg μ' out ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) ∧
        ∀ a < fr, (a < out ∨ out + WI.length ≤ a) → μ' a = μ a

/-- The specification holds for the program with more procedures appended. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean
-- (OfflineSpec32.append)
theorem OfflineSpec32P.append {c : ℕ} (h : OfflineSpec32P lim P c G) (R : Program) :
    OfflineSpec32P lim (P ++ R) c G :=
  fun N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin d hd =>
    (h N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin d hd).append R

/-- offline32P meets its specification if the pruned preprocessing and the query meet theirs. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean
-- (offline32_meets)
theorem offline32P_meets {c : ℕ} (hP : P[Proc.offline32P]? = some offline32PBody)
    (hpre : PreSpec31P lim P c G) (hq : QuerySpec31P lim P G) : OfflineSpec32P lim P c G := by
  intro N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin
  refine fun d hd => ⟨offline32PBody, hP, ?_⟩
  have hw := hg.lim.std.space_le
  have hspace := hg.lim.space
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hlen := hin.length_eq
  have hout := hin.out_le
  -- Res := pre31P(N, D, x, y, fr)
  refine Ends.callToThen (hpre N D₀ aX aY fr X Y U μ hg hin.matX hin.matY _ (by omega)) ?_
    (hT := by simp [tOffline32P]; omega)
  rintro r μ₁ ⟨hready, hblock⟩
  let ans := (WI.zip WJ).map fun q => entryN X Y q.1 q.2
  have hlenAns : ans.length = WI.length := by simp [ans, hlen]
  refine Ends.forShape (fun i r ν => ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r], ν⟩)
    (fun i _ => Answered (Ready31P G X Y aX aY fr) (· < fr) out ans μ i) WI.length
    (tQuery31 G D₀ + 20) r ⟨hready, Seg.nil, SameOn.mono hblock fun a ha => Or.inl ha.2⟩ ?_ ?_
    (hT := by light_time [tOffline32P])
  case refine_2 =>
    intro _ ν hinv
    exact ⟨(hlenAns ▸ hinv : Answered _ _ out ans μ ans.length ν).all,
      fun a ha hoff => hinv.same a ⟨hoff, ha⟩⟩
  intro i _ ν hi hinv
  have hiJ : i < WJ.length := by omega
  have hrows := hin.rows_le
  have hcols := hin.cols_le
  have hIN : WI[i] < N := hin.rows_lt _ (List.getElem_mem hi)
  have hJN : WJ[i] < N := hin.cols_lt _ (List.getElem_mem hiJ)
  have read {l : List ℕ} {a : ℕ} (hs : SegN μ a l) (hl : i < l.length)
      (ha : a + l.length ≤ fr) (hd : Apart out WI.length a l.length) : ν (a + i) = (l[i] : ℕ) :=
    (hinv.read hs (by simpa using hl) (by omega) (by omega)).trans (List.getElem_map _)
  unfold offlineAsk32
  light_call (hq N D₀ aX aY fr X Y U ν ⟨WI[i], hIN⟩ ⟨WJ[i], hJN⟩ hg hinv.ready _ (by omega))
    using read hin.rows hi hin.rows_le hin.out_rows,
      read hin.cols hiJ (by rw [hlen]; exact hin.cols_le) (by rw [hlen]; exact hin.out_cols)
    with _ ν' ⟨rfl, hready', hquery⟩
  light_step
  have hstep := hinv.step (by omega) hquery (fun j hj => Or.inl (by omega))
    (fun a ha => Or.inl (by omega)) (ready31P_congr hready'
      (fun a h1 h2 => Function.update_of_ne (by have := hin.out_matX; omega) _ _)
      (fun a h1 h2 => Function.update_of_ne (by have := hin.out_matY; omega) _ _)
      fun a ha => Function.update_of_ne (by omega) _ _)
  dsimp only [ans] at hstep
  rw [List.getElem_map, List.getElem_zip, entryN, dite_eq_left ⟨hIN, hJN⟩] at hstep
  exact ⟨_, _, rfl, hstep⟩

end Light.Sec4
