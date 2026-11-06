module

public import ThreeSumApsp.Util.Types
public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
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



variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : ThreeSumApsp.IntMatrix N D₀}
  {Y : ThreeSumApsp.IntMatrix D₀ N} {aX aY fr : ℕ} {U : ℤ} {μ μ' : Light.Memory}

/-- offline32P(N, D, w, U, x, y, wi, wj, out, fr): preprocess with the pruned encoder, then ask one
query for each wanted position and store its answer. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean (offline32Body)
def offline32PBody  :=
  .call 81 [v 0, v 1, v 4, v 5, v 9] 11 ;;
  .for 10 (v 2) offlineAsk32

/-- What a query needs depends only on the cells of X, of Y, and on the cells from fr on. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean (ready31_congr)
theorem ready31P_congr (h : Ready31P G X Y aX aY fr μ)
    (hX : ∀ a, aX ≤ a → a < aX + N * D₀ → μ' a = μ a)
    (hY : ∀ a, aY ≤ a → a < aY + D₀ * N → μ' a = μ a) (hfr : ∀ a, fr ≤ a → μ' a = μ a) :
    Ready31P G X Y aX aY fr μ' := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun hs => ?_, fun hl => ?_⟩
  · rw [hX _ (by omega) ?_]
    · exact h.matX i j
    · have := Nat.mul_add_le_mul i.isLt (le_refl D₀)
      omega
  · rw [hY _ (by omega) ?_]
    · exact h.matY i j
    · have := Nat.mul_add_le_mul i.isLt (le_refl N)
      omega
  · ram_arith
  · obtain ⟨h1, h2, h3⟩ := h.large hl
    refine ⟨by rw [hfr _ le_rfl]; exact h1, by simp_all,
      dsReadyP_congr h3 fun a ha => hfr a ?_⟩
    unfold blockAt at ha
    omega

/-- offline32P writes the wanted entries of XY to out. Below fr it changes only the output; nothing
is assumed about the cells from fr on. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean (OfflineSpec32)
def OfflineSpec32P lim P c G :=
  ∀ (N D₀ aX aY aI aJ out fr : ℕ) (X : ThreeSumApsp.IntMatrix N D₀) (Y : ThreeSumApsp.IntMatrix D₀ N)
    (U : ℤ) (u : ℤ) (μ : Light.Memory) (WI WJ : List ℕ),
    Input31 lim G X Y aX aY fr U → OfflineInput32 X Y aX aY aI aJ out fr WI WJ μ →
    ∀ d, d + G.L (logFour D₀) + 8 ≤ lim.depth → Meets lim P 82 d
      [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr] μ (tOffline32P c G N D₀ WI.length)
      fun _ μ' => Seg μ' out ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) ∧
        ∀ a < fr, a < out ∨ out + WI.length ≤ a → μ' a = μ a

/-- The specification holds for the program with more procedures appended. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean
-- (OfflineSpec32.append)
def OfflineSpec32P.append {c} (h : OfflineSpec32P lim P c G) R :=
  fun N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin d hd =>
    (h N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin d hd).append R

/-- **One round**: the answer for position i joins the answers that are there. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean
-- (offlineAsk32_ends)
theorem offlineAsk32P_ends (hq : QuerySpec31P lim P G) {aI aJ out d}
    {u} {WI WJ} (hg : Input31 lim G X Y aX aY fr U)
    (hin : OfflineInput32 X Y aX aY aI aJ out fr WI WJ μ) (hd : d + 4 ≤ lim.depth) {i}
    (hi : i < WI.length) r
    (hinv : Answered (Ready31P G X Y aX aY fr) (· < fr) out
      ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ i μ') :
    Ends lim P d offlineAsk32 ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r], μ'⟩
      (tQuery31 G D₀ + 20) fun σ' => ∃ (r' : ℤ) (μ'' : Light.Memory),
        σ' = ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r'], μ''⟩ ∧
        Answered (Ready31P G X Y aX aY fr) (· < fr) out
          ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ (i + 1) μ'' := by
  have  := hg.lim.std.space_le
  have  := hg.lim.space
  have  := add_three_le_structEnd G N D₀ fr
  have hlen := hin.length_eq
  have  := hin.rows_le
  have  := hin.cols_le
  have  := hin.out_le
  have hiJ : i < WJ.length := by omega
  have hIN := hin.rows_lt _ (List.getElem_mem hi)
  have hJN := hin.cols_lt _ (List.getElem_mem hiJ)
  -- the two indices are still in place
  have hrow :=
    (hinv.read hin.rows (j := i) (by simpa using hi)
      (by ram_safe) (by omega)).trans (List.getElem_map _)
  have hcol :=
    (hinv.read hin.cols (j := i) (by simpa using hiJ)
      (by ram_arith) (by omega)).trans (List.getElem_map _)
  -- Res := query31(mem[Rows + Pos], mem[Cols + Pos], N, D, x, y, fr)
  refine Ends.callToThen (hq N D₀ aX aY fr X Y U μ' ⟨WI[i], hIN⟩ ⟨WJ[i], hJN⟩ hg hinv.ready _
    hd) ?_
    (ha := by light_side [hrow, hcol])
  rintro _ μ₂ ⟨rfl, hready, hquery⟩
  -- mem[Out + Pos] := Res
  light_store (out + i) ((X * Y) ⟨WI[i], hIN⟩ ⟨WJ[i], hJN⟩)
  have hstep := hinv.step (by simpa [hlen] using hi) hquery (fun j hj => Or.inl (by omega))
    (fun a ha => Or.inl (by omega)) (ready31P_congr hready
      (fun a h1 h2 => Function.update_of_ne (by ram_safe) _ _)
      (fun a h1 h2 => Function.update_of_ne (by ram_safe) _ _)
      fun a ha => Function.update_of_ne (by omega) _ _)
  rw [List.getElem_map, List.getElem_zip, entryN, dite_eq_left ⟨hIN, hJN⟩] at hstep
  exact ⟨_, _, rfl, hstep⟩

/-- offline32P meets its specification if the pruned preprocessing and the query meet theirs. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean
-- (offline32_meets)
theorem offline32P_meets {c} (hP : P[82]? = some offline32PBody)
    (hpre : PreSpec31P lim P c G) (hq : QuerySpec31P lim P G) : OfflineSpec32P lim P c G := by
  intro N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin
  refine fun d hd => ⟨offline32PBody, hP, ?_⟩
  have  := hg.lim.std.space_le
  have  := hg.lim.space
  have  := add_three_le_structEnd G N D₀ fr
  have hlen := hin.length_eq
  have  := hin.out_le
  have hzip : (WI.zip WJ).length = WI.length := by simp [hlen]
  -- Res := pre31P(N, D, x, y, fr)
  refine Ends.callToThen (hpre N D₀ aX aY fr X Y U μ hg hin.matX hin.matY _ (by omega)) ?_
    (hT := by simp [tOffline32P]; omega)
  rintro r μ₁ ⟨hready, hblock⟩
  -- for Pos < Count: offlineAsk32
  refine Ends.for (fun i σ => ∃ (r : ℤ) (μ' : Light.Memory),
      σ = ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r], μ'⟩ ∧
      Answered (Ready31P G X Y aX aY fr) (· < fr) out
        ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ i μ')
    WI.length (tQuery31 G D₀ + 20) ?start ?round ?done ?bound
    (hT := by simp [tOffline32P]; ring_nf; omega)
  case start =>
    exact ⟨r, μ₁, by simp_all, hready, Seg.nil,
      SameOn.mono hblock fun a ha => Or.inl ha.2⟩
  case bound =>
    simp_all
  case done =>
    rintro _ - ⟨r, μ', rfl, hinv⟩
    rw [← hzip, ← List.length_map (as := WI.zip WJ) fun q => entryN X Y q.1 q.2] at hinv
    refine ⟨hinv.all, fun a ha hoff => hinv.same a ⟨?_, ha⟩⟩
    simpa [hlen] using hoff
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, hinv⟩
    refine (offlineAsk32P_ends hq hg hin (by omega) hi r hinv).mono le_rfl ?_
    rintro _ ⟨r', μ'', rfl, hinv'⟩
    exact ⟨rfl, r', μ'', by rw [update_frame_setLocal]; rfl, hinv'⟩

end Light.Sec4
