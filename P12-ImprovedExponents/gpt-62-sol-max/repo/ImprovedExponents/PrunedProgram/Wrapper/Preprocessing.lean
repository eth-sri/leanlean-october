module

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Preprocessing
public import ImprovedExponents.PrunedProgram.Wrapper.Parameters

@[expose] public section

/-!
# Corollary 31 with the pruned encoder: the preprocessing, with rational parameters

Upstream's `pre31` (`ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean`) computes
`m`, pads the matrices and calls the preprocessing of Theorem 30.  `pre31P` is the same text with
`preCoreP` in place of `preCore`; the proof is upstream's with `PreCoreSpecP` and `Ready31P`
(`pre31P_meets`).

Adapted from upstream (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp ImprovedExponents

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ} {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ : ℕ → ℤ}

/-- The routines that the pruned preprocessing calls meet their specifications. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean
-- (PreCalls31)
structure PreCalls31P (lim : Limits) (P : Program) (c : ℕ) (G : RatParams) : Prop where
  log4 : Log4Spec lim P
  levels : CeilMulSpec lim P Proc.levels31 G.a G.b
  switch : CeilMulSpec lim P Proc.switch31 G.p G.q
  padX : PadXSpec lim P
  copy : CopySpec lim P
  fill : FillSpec lim P
  preCore : PreCoreSpecP lim P c

/-- pre31P meets its specification if its callees meet theirs. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean
-- (pre31_meets)
theorem pre31P_meets {c : ℕ} (G : RatParams) (hP : P[Proc.pre31P]? = some (pre31PBody G))
    (C : PreCalls31P lim P c G) : PreSpec31P lim P c G := by
  intro N D₀ aX aY fr X Y U μ hin mX mY
  have hlim := hin.lim
  refine fun d hd => ⟨pre31PBody G, hP, ?_⟩
  light_facts hlim.std
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hsp := hlim.space
  have := hlim.m0word
  have hmword : (logFour D₀ : ℤ) ≤ lim.word := by
    have := Nat.le_mul_of_pos_left (logFour D₀) (show 0 < G.a by have := G.hc; omega)
    have := hlim.mword
    omega
  unfold pre31PBody
  -- m := log4(D, fr + 2), which writes 4^m to the cell fr + 2
  light_call (C.log4 D₀ (fr + 2) μ (by omega) hlim.pow hmword) using tPre31P, logFour
    with _ _ ⟨rfl, rfl⟩
  -- if m < m₀
  light_if hm hn : logFour D₀ < G.m₀ using tPre31P, logFour
  · light_step using tPre31P, logFour
    have same : SameOutside μ (Function.update (Function.update μ (fr + 2) (D (logFour D₀))) fr 0)
        fr (structEnd G N D₀ fr - fr) := by
      rw [structEnd_small hm]
      light_keep
    have hbelow : Kept μ _ fr := SameOn.mono same fun _ => Or.inl
    exact ⟨⟨mX.congr_below hbelow hin.belowX, mY.congr_below hbelow hin.belowY,
      fun _ => Function.update_self .., by omega⟩, same⟩
  · have hm := Nat.le_of_not_gt hn
    simp only [tPre31P, ite_eq_right hn, ← show logFour D₀ = Nat.clog 4 D₀ from rfl]
    unfold preLarge31P prePad31 preBuild31P
    set F := D (logFour D₀)
    set R := (F - D₀) * N
    let μ₁ := Function.update μ (fr + 2) (F : ℤ)
    have hstruct := structEnd_large hm N fr
    have hb0 : blockAt N D₀ fr = fr + 3 + N * F + N * F := rfl
    have hb0top := G.blockAt_lt_blockEnd N D₀ fr
    have hb0lt : blockAt N D₀ fr < lim.space := hb0top.trans_le (hstruct ▸ hsp)
    have hDF : D₀ ≤ F := le_D_logFour D₀
    have hrows : D₀ * N + R = N * F := by
      change D₀ * N + (F - D₀) * N = N * F
      rw [← Nat.add_mul, Nat.add_sub_cancel' hDF, Nat.mul_comm]
    have hFN : F ≤ N * F := Nat.le_mul_of_pos_left _ hin.one_le_N
    have hD := hin.one_le_D
    have hbX := hin.belowX
    have hbY := hin.belowY
    have hRZ : ((F : ℤ) - D₀) * N = R := by simp [F, R, Int.natCast_sub hDF]
    have hread : (4 ^ Nat.clog 4 D₀ : ℤ) = F := rfl
    have haddr : ((fr : ℤ) + 2).toNat = fr + 2 := by omega
    have hout₁ : SameOutside μ μ₁ (fr + 2) 1 := by dsimp [μ₁]; light_keep
    have hkept₁ : Kept μ μ₁ fr := by light_keep
    -- F := mem[fr + 2]
    light_set (F : ℤ) using haddr, hread, logFour
    -- L := ⌈a m / b⌉
    light_call (C.levels (logFour D₀) μ₁ hlim.wordL _ (by omega)) with _ μ₁ ⟨rfl, rfl⟩
    -- t := ⌈p m / q⌉
    light_call (C.switch (logFour D₀) μ₁ hlim.wordT _ (by omega)) with _ μ₁ ⟨rfl, rfl⟩
    -- aX' := fr + 3 ; NF := N * F ; aY' := aX' + NF ; b0 := aY' + NF
    light_steps
    -- padX(N, D, F, aX, aX')
    light_call (C.padX N D₀ F aX (fr + 3) X μ₁ hDF (by omega)
      (mX.congr_below hkept₁ hbX) (by omega) (by omega) _ (by omega)) with - μ₂ ⟨hpadX, hout₂⟩
    -- copy(aY, aY', D N)
    light_call (C.copy aY (fr + 3 + N * F) (D₀ * N) μ₂ (by omega) (by omega) (by omega)
      (.inl (by omega)) _ (by omega)) with - μ₃ ⟨hcopy, hout₃⟩
    -- fill(aY' + D N, (F - D) N, 0)
    light_call (C.fill (fr + 3 + N * F + D₀ * N) R 0 μ₃ (by omega) (by omega) _
      (by omega)) using hRZ with - μ₄ ⟨hfill, hout₄⟩
    have mXp : MatAt μ₄ (paddedXAt fr) (padInnerCols F X) :=
      hpadX.congr fun b _ hb => by rw [hout₄ b (.inl (by omega)), hout₃ b (.inl (by omega))]
    have mYp : MatAt μ₄ (paddedYAt N D₀ fr) (padInnerRows F Y) := by
      refine matAt_padInnerRows (mY.congr_below hkept₁ hbY) (fun i hi => ?_) hfill
      change μ₄ (fr + 3 + N * F + i) = _
      rw [hout₄ _ (.inl (by omega)), hcopy i hi, hout₂ _ (.inl (by omega))]
    -- preCoreP(L, m, t, N, F, aX', aY', b0)
    have hcall := C.preCore (parOf G N D₀) (switchOf31 G D₀) (logFour_le_levels G N D₀) (paddedXAt fr)
        (paddedYAt N D₀ fr)
      (blockAt N D₀ fr) _ _ U μ₄ (G.t_le _) (hlim.large hm) (abs_padInnerCols_le hin.absX hin.zero_le_U)
      (abs_padInnerRows_le hin.absY hin.zero_le_U) mXp mYp
      (by exact Nat.le.intro hb0)
      (by change fr + 3 + N * D (logFour D₀) + D (logFour D₀) * N ≤ _
          lia) (d + 1)
      (show d + 1 + (G.L (logFour D₀) + 6) ≤ lim.depth by omega)
    light_call hcall using parOf, switchOf31, Sec2.Par.D, RatParams.L, RatParams.t, logFour, F, D, paddedXAt, paddedYAt, blockAt
      with - μ₅ ⟨hDS, hout₅⟩
    have hout₅ : SameOutside μ₄ μ₅ (blockAt N D₀ fr) (G.blockEnd N D₀ fr - blockAt N D₀ fr) := hout₅
    -- mem[fr + 1] := b0
    light_store (fr + 1) (blockAt N D₀ fr : ℤ) using hb0
    light_store fr (1 : ℤ)
    have same : SameOutside μ (Function.update (Function.update μ₅ (fr + 1) (blockAt N D₀ fr)) fr 1)
        fr (structEnd G N D₀ fr - fr) := by
      rw [hstruct]
      dsimp only [μ₁] at *
      light_keep [hb0]
    have hbelow := SameOn.mono same (fun _ (hb : _ < fr) => Or.inl hb)
    refine ⟨⟨mX.congr_below hbelow hbX, mY.congr_below hbelow hbY,
      fun _ => by omega, fun _ => ⟨Function.update_self .., ?_, dsReadyP_congr hDS ?_⟩⟩, same⟩
    all_goals grind

end Light.Sec4
