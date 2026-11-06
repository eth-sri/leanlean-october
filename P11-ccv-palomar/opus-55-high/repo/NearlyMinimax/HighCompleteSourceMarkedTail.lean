module

public import NearlyMinimax.HighCompleteSourceSpatialTail
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Large-count factorial energy of the genuine canonical complete source
in the original periodic-frame field. All source field guards are derived;
the fixed tail constant precedes degree, count, history and spatial grid. -/
𝚫
𝚪
𝚨
𝚩
𝛈
𝚬
𝚿

𝗇 𝔉 B+1
𝗇 𝔄 𝚎₁^n*𝗩*𝔉^2
𝗇 𝔅 Chi^𝘕₁*𝗩*𝔉^2
𝗇 𝔊 𝙈
𝗇 𝔇 ∑ y : 𝔊, R x y ^ 2
theorem crude_raw_square_energy_pointwise Chi η B
    (hChi : 0 ≤ Chi) (hB : 𝙐)
    R
    (hcap : ∀ x y, |R x y| ≤ Chi^n*𝙎*𝔉) (x : 𝙇) :
    selectedRawSquareEnergy R x ≤ 𝔄 := by
  have hp y : R x y ^ 2 ≤ 𝔅 := by
    have hh := (𝘉 𝖠₃ ).mpr $ hcap x y
    simp at hh
    convert hh using 1 <;> (try rw [mul_pow,mul_pow,←pow_mul]) <;> ring
  have he : selectedRawSquareEnergy R x = 𝔇 := by
    apply Finset.sum_congr 𝖤₃
    simp
  calc
    _ = 𝔇 := he
    _ ≤ ∑ _y : 𝔊, 𝔅 :=
      Finset.sum_le_sum 𝘞₂
    _ = 𝔄 := by
      simp
      ring

section Marked
variable {d k D : ℕ} {I : Type*} [Fintype I] {E : 𝗀}
  [𝙪] [𝖭]
  [NeZero k] [LinearOrder 𝙯]

𝗇 𝔈 𝖯
𝗃 𝔍 ἀ R $ highCenterMix C
def highUnionSourceMarkedNumerator (C : ModelConstants d) (R : 𝙭₁ I E)
    (n : ℕ) (a V η : ℝ) (j : 𝙯)
    (h : HistoryMarked 𝖫 $ HighUnionMark E )
    (x : 𝙇) (y : 𝔊) : ℝ :=
  highMarkedSampleNumerator n 𝔍 highUnionLaw
    𝔍 highUnionActivation a V η
    𝙾 𝘖₁
    𝚑₁
    (highLocalFieldWithout d k D η 𝔈 j)
    (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x)
    (𝔈 j) x y
