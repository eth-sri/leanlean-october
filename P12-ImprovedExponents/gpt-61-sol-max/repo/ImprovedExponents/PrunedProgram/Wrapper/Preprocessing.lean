module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Preprocessing
public import ImprovedExponents.PrunedProgram.Wrapper.Parameters

@[expose] public section

/-!
# Corollary 31 with the pruned encoder: the preprocessing, with rational parameters

Upstream's `pre31` (`ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean`) computes
`m`, pads the matrices and calls the preprocessing of Theorem 30.  `pre31P` is the same text with
`preCoreP` in place of `preCore`; the proof is upstream's with `PreCoreSpecP` and `Ready31P`
(`pre31P_meets`).  The padding stage `prePad31` is upstream's text and is re-verified here only
because its proof is stated for the record of callees `PreCalls31`, whose field `preCore` is now
`PreCoreSpecP`.

Adapted from upstream (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : ThreeSumApsp.IntMatrix N D₀}
  {Y : ThreeSumApsp.IntMatrix D₀ N} {aX aY fr : ℕ} {U : ℤ} {μ μ' : Light.Memory}

/-- The routines that the pruned preprocessing calls meet their specifications. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean
-- (PreCalls31)
structure PreCalls31P (lim : Limits) (P : Program) (c : ℕ) (G : RatParams) : Prop where
  log4 : Log4Spec lim P
  levels : CeilMulSpec lim P 72 G.a G.b
  switch : CeilMulSpec lim P 73 G.p G.q
  padX : PadXSpec lim P
  copy : CopySpec lim P
  fill : FillSpec lim P
  preCore : PreCoreSpecP lim P c

variable (h : PreInput31 lim G X Y aX aY fr U μ)

include h in
/-- Below the threshold the flag 0 is all that a query needs. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean
-- (PreInput31.ready_small)
theorem PreInput31.ready_smallP  (hm : logFour D₀ < G.m₀)
    (hkept : SameOn (· < fr) μ μ') (hflag : μ' fr = 0) : Ready31P G X Y aX aY fr μ' :=
  ⟨h.matX.congr_below hkept h.belowX, h.matY.congr_below hkept h.belowY, fun _ => hflag,
    fun hm' => absurd hm' (by omega)⟩

include h in
/-- From the threshold on a query needs the flag 1, the base address, and the data structure of
Theorem 30 for the padded matrices. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean
-- (PreInput31.ready_large)
theorem PreInput31.ready_largeP  (hm : G.m₀ ≤ logFour D₀)
    (hkept : SameOn (· < fr) μ μ') (hflag : μ' fr = 1) (hbase : μ' (fr + 1) = blockAt N D₀ fr)
    (hDS : Built31P G X Y fr μ') : Ready31P G X Y aX aY fr μ' :=
  ⟨h.matX.congr_below hkept h.belowX, h.matY.congr_below hkept h.belowY,
    fun hm' => absurd hm (by omega), fun _ => ⟨hflag, hbase, hDS⟩⟩

/-! ## From the threshold on -/

/-- **Setting up**: L, t, the addresses, and the padded matrices. The cell fr + 2 holds 4^m. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean
-- (prePad31_ends)
theorem prePad31_endsP {c d} (C : PreCalls31P lim P c G)
    (h : PreInput31 lim G X Y aX aY fr U μ)
    (hm : G.m₀ ≤ logFour D₀) (hd : d + G.L (logFour D₀) + 7 ≤ lim.depth) :
    Ends lim P d prePad31
      ⟨frame [N, D₀, aX, aY, fr, logFour D₀], Function.update μ (fr + 2) (D (logFour D₀) : ℕ)⟩
      (tPrePad31 G N D₀) (Padded31 G X Y aX aY fr μ) := by
  have A := h.areas hm
  unfold prePad31 tPrePad31 Padded31 paddedXAt paddedYAt
  rw [A.base]
  generalize D (logFour D₀) = F at A ⊢
  generalize (F - D₀) * N = R at A ⊢
  obtain ⟨μ₁, hμ₁⟩ : ∃ μ₁, μ₁ = Function.update μ (fr + 2) (F : ℤ) := ⟨_, rfl⟩
  rw [← hμ₁]
  obtain ⟨hR, hb0, hb0lt, hDF, hrows, hFN⟩ := A
  have  := h.lim.std.space_le

  have  := h.one_le_D
  have hbX := h.belowX
  have hbY := h.belowY


  have hout₁ : SameOutside μ μ₁ (fr + 2) 1 := hμ₁ ▸ SameOn.refl.write (by omega) _
  have hkept₁ : ∀ b < fr, μ₁ b = μ b := fun b hb => hout₁ b (.inl (by omega))
  have haddr : ((fr : ℤ) + 2).toNat = fr + 2 := by omega
  -- F := mem[fr + 2]
  light_set F using haddr, (by simp_all : μ₁ (fr + 2) = F)
  -- L := ⌈a m / b⌉
  light_call (C.levels _ μ₁ h.lim.wordL _ (by omega)) with _ μ₁ ⟨rfl, rfl⟩
  -- t := ⌈p m / q⌉
  light_call (C.switch _ μ₁ h.lim.wordT _ (by omega)) with _ μ₁ ⟨rfl, rfl⟩
  -- aX' := fr + 3 ; NF := N * F ; aY' := aX' + NF ; b0 := aY' + NF
  light_set (fr + 3 : ℕ)
  light_set (N * F : ℕ)
  light_set (fr + 3 + N * F : ℕ)
  light_set (fr + 3 + N * F + N * F : ℕ)
  -- padX(N, D, F, aX, aX')
  light_call (C.padX N D₀ F aX (fr + 3) X μ₁ hDF (by omega)
    (h.matX.congr_below hkept₁ hbX) (by omega) (by omega) _ (by omega)) with - μ₂ ⟨hpadX, hout₂⟩
  -- copy(aY, aY', D N)
  light_call (C.copy aY (fr + 3 + N * F) (D₀ * N) μ₂ (by omega) (by omega) (by omega)
    (.inl (by omega)) _ (by omega)) with - μ₃ ⟨hcopy, hout₃⟩
  -- fill(aY' + D N, (F - D) N, 0)
  light_call (C.fill (fr + 3 + N * F + D₀ * N) R 0 μ₃ (by omega) (by omega) _
    (by omega)) using (by simp_all : ((F : ℤ) - D₀) * N = R) with r μ₄ ⟨hfill, hout₄⟩
  refine ⟨r, μ₄, rfl, ?_, ?_, fun b hb => ?_⟩
  · exact hpadX.congr fun b _ hb => by rw [hout₄ b (.inl (by omega)), hout₃ b (.inl hb)]
  · refine matAt_padInnerRows (h.matY.congr_below hkept₁ hbY) (fun i hi => ?_) (hR ▸ hfill)
    rw [hout₄ _ (.inl (by omega)), hcopy i hi, hout₂ _ (.inl (by omega))]
  · rw [hout₄ b (by omega), hout₃ b (by omega), hout₂ b (by omega), hout₁ b (by omega)]

/-- **The preprocessing of Theorem 30 with the pruned encoder** on the padded matrices, the base
address and the flag 1. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean
-- (preBuild31_ends)
theorem preBuild31P_ends {c d} (C : PreCalls31P lim P c G)
    (h : PreInput31 lim G X Y aX aY fr U μ)
    (hm : G.m₀ ≤ logFour D₀) (hd : d + G.L (logFour D₀) + 7 ≤ lim.depth) {σ}
    (hσ : Padded31 G X Y aX aY fr μ σ) :
    Ends lim P d preBuild31P σ (tPreCoreP c (parOf G N D₀) (switchOf31 G D₀) + 60) fun σ' =>
      Ready31P G X Y aX aY fr σ'.mem ∧ SameOutside μ σ'.mem fr (structEnd G N D₀ fr - fr) := by
  obtain ⟨r, μ₄, rfl, mX, mY, hout₄⟩ := hσ
  have  := (h.areas hm).base
  have  := (h.areas hm).base_lt
  have  := h.lim.std.space_le

  have  := G.blockAt_lt_blockEnd N D₀ fr
  have  := add_three_le_structEnd G N D₀ fr
  unfold preBuild31P
  -- preCoreP(L, m, t, N, F, aX', aY', b0)
  light_call (C.preCore (parOf G N D₀) (switchOf31 G D₀) (logFour_le_levels G N D₀) (paddedXAt fr)
      (paddedYAt N D₀ fr)
    (blockAt N D₀ fr) _ _ U μ₄ (G.t_le _) (h.lim.large hm) (abs_padInnerCols_le h.absX h.zero_le_U)
    (abs_padInnerRows_le h.absY h.zero_le_U) mX mY
    (by change fr + 3 + N * D (logFour D₀) ≤ _; omega)
    (by change fr + 3 + N * D (logFour D₀) + D (logFour D₀) * N ≤ _
        rw [Nat.mul_comm (D (logFour D₀)) N]; omega) _
    (by change d + 1 + G.L (logFour D₀) + 6 ≤ _; omega)) using parOf, switchOf31, Sec2.Par.D
    with - μ₅ ⟨hDS, hout₅⟩
  have hout₅ : SameOutside μ₄ μ₅ (blockAt N D₀ fr) (G.blockEnd N D₀ fr - blockAt N D₀ fr) := hout₅
  -- mem[fr + 1] := b0
  light_store (fr + 1) (blockAt N D₀ fr)
  -- mem[fr] := 1
  light_store fr 1
  -- outside the cells from fr to the end of the block nothing has changed
  have hsame : SameOutside μ μ₅ fr (structEnd G N D₀ fr - fr) := by
    rw [structEnd_large hm]
    exact fun b hb => (hout₅ b (by omega)).trans (hout₄ b (by omega))
  dsimp only
  refine ⟨h.ready_largeP hm (fun b (hb : b < fr) => ?_) (Function.update_self ..) ?_
    (dsReadyP_congr hDS fun a ha => ?_), (hsame.write (by omega) _).write (by omega) _⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hsame b (.inl hb)]
  · simp_all
  · grind

/-! ## The routine -/

/-- pre31P meets its specification if its callees meet theirs. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean
-- (pre31_meets)
theorem pre31P_meets {c} G (hP : P[81]? = some (pre31PBody G))
    (C : PreCalls31P lim P c G) : PreSpec31P lim P c G := by
  intro N D₀ aX aY fr X Y U μ hin mX mY
  have h : PreInput31 lim G X Y aX aY fr U μ := ⟨hin, mX, mY⟩
  have hlim := hin.lim
  refine fun d hd => ⟨pre31PBody G, hP, ?_⟩
  have  := hlim.std.space_le

  have  := add_three_le_structEnd G N D₀ fr
  have  := hlim.space
  have  := hlim.m0word

  unfold pre31PBody
  -- m := log4(D, fr + 2), which writes 4^m to the cell fr + 2
  refine Ends.callToThen (C.log4 D₀ (fr + 2) μ (by omega) hlim.pow (by
    have : logFour D₀ ≤ G.a * logFour D₀ := Nat.le_mul_of_pos_left _ (by have := G.hc; omega)
    exact le_trans (by omega) hlim.mword
   : (logFour D₀ : ℤ) ≤ lim.word) _ (by omega)) ?_
    (hT := by simp [tPre31P, logFour]; omega)
  rintro _ _ ⟨rfl, rfl⟩
  -- if m < m₀
  refine Ends.iteLast (fun hsmall => ?_) (fun hlarge => ?_)
    (hT := by simp [tPre31P, logFour]; omega)
  · -- mem[fr] := 0
    have hm := by simpa [logFour] using hsmall

    refine Ends.storeTo fr 0 ⟨h.ready_smallP hm (fun b (hb : b < fr) => ?_)
      (Function.update_self ..), ?_⟩ (hT := by simp [tPre31P, logFour]; omega)
    · grind
    · rw [(by rw [structEnd_small hm]; omega : structEnd G N D₀ fr - fr = 3)]
      exact (SameOn.refl.write (by omega) _).write (by omega) _
  · have hm : G.m₀ ≤ logFour D₀ := by simpa [logFour] using hlarge
    -- the padded matrices, then the data structure of Theorem 30
    refine Ends.next (tPrePad31 G N D₀) ((prePad31_endsP C h hm hd).mono le_rfl fun σ hσ =>
      (preBuild31P_ends C h hm hd hσ).mono ?_ fun _ hQ => hQ) ?_
    all_goals
      simp only [tPre31P, tPrePad31, ite_eq_right (not_lt.mpr hm)]
      simp [logFour]
      omega

end Light.Sec4
