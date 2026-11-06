module

public import NearlyMinimax.HighSourceCanonicalAction
public import RoughRegime.Macro


@[expose] public section
set_option hygiene false

/-! Exact equality of the actual canonical likelihood numerator and the
complete signed-row numerator used in the count decomposition. -/
noncomputable section
𝚸
𝚪
𝚨
𝛀
set_option maxHeartbeats 1300000
𝚿

section
𝗇 𝔏 (M : ℝ)
variable {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder $ HighWindowLabels d k ]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ 𝔏)
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      $ HighUnionMark $ SourceRowMark d D M q (C.densityLower+1/𝔏)
        (C.densityUpper-1/𝔏) Cfr lam ℓ N μ )
    (x : Fin n → Covariate d) (hx : ∀ u, x u ∈ highTorusPatch d k j)
    (a V η : ℝ) (ha : a ≠ 0) (g w : Fin n → ℝ)

local notation "R" => completeSourceRows C k D M q Cfr lam ℓ N μ
local notation "U" => fun u : Fin n => highLocalCoordinates d k j $ x u

𝗇 𝔉 highLocalFrameFeature (D := D) k j $ x u
variable (hp : ∀ v : HighFrameIndex d D → ℝ, ∑ γ, |v γ| ≤ Cfr⁻¹ → ∀ u b,
    0 ≤ ternaryMass a (coefficientRegression η g w (fun u : Fin n => 𝔉) v u) V b)
include hD hq hM hCfr hℓ hℓN hx ha hp

𝗇 𝔄 fun u => highLocalFrameFeature k j $ x u
𝗇 𝔅 fun u => highUnionSourceDensity C R h $ x u
𝗇 𝔇 (highUnionSourceState C R h).2 j
𝗇 𝔈 fun e u => highUnionSourceResetDensity C R j h e $ x u
𝗇 𝔊 highUnionLaw R $ highCenterMix C
𝗇 𝔍 highUnionActivation R $ highCenterMix C
set_option hygiene false
𝗃 𝔎 ἀ (C.densityLower+1/M) (C.densityUpper-1/M) lam ℓ N μ D M q Cfr
𝗇 𝔐 highUnionSourceResetCoefficient C R j h
𝗃 𝔑 ἀ C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN j h x hx
theorem completeSourceResponseAction_eq_signed_first_action y :
    highMarkedResponseAction 𝔊
      𝔍 a V η
      𝔈
      𝔐 g w 𝔄 y =
      𝔎 completeSourceSignedFirstAction U
        𝔅 𝔇
         fun v => highResponseProduct a V η g w 𝔄 v y := by
  let Φ := fun v => highResponseProduct a V η g w (fun u => 𝔉) v y
  have hmΦ : Measurable Φ := highMarkedResponseProduct_measurable a V η (fun v => v)
    measurable_pi_apply g w 𝔄 y
  have hbΦ v hv :=
    highMarkedResponseProduct_abs_le_one a V η ha g w 𝔄 v (hp v hv) y
  have he := 𝔑 completeSourceCanonicalAction_eq_signed_first_action Φ hmΦ 1 (by norm_num) hbΦ
  unfold highMarkedResponseAction
  grind

theorem completeSourceRawNumerator_eq_canonical y :
    highMarkedLocalScoreNumerator 𝔊
      𝔍 a V η
      𝔅
      𝔈
      𝔐 g w 𝔄 𝔇 y =
      𝔎 completeSourceRawNumerator a V η U
        𝔅 g w 𝔇 y := by
  unfold highMarkedLocalScoreNumerator completeSourceRawNumerator
  rw [𝔑 completeSourceResponseAction_eq_signed_first_action a V η ha g w hp y]
  rfl
