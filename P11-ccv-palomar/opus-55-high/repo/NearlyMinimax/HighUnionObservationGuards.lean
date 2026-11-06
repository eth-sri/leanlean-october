module

public import NearlyMinimax.HighUnionSourceModel
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Genuine response probability floors on every raw history, including
mass-exceptional histories. The constants precede the extension domain. -/
𝚸
𝚪
𝚨
𝚱
𝚩
𝚬

/-- A larger frame constant imposes a smaller coefficient ball, and therefore
supplies every primitive guard for a smaller admissible frame constant. -/
theorem HighUnionSourceGuards.mono_frame {d k F : ℕ} {I : Type*} [Fintype I]
    {E : 𝗀} [𝙪]
    {C } {M Cfr Cfr' } {R : 𝗽}
    (G : 𝗗) (hfr : 1 ≤ Cfr') (hle : Cfr' ≤ Cfr) :
    HighUnionSourceGuards C M Cfr' R := by
  refine { G with frame := hfr, vector_ball := ?_ }
  intro i e
  exact (G.vector_ball i e).trans $ (inv_le_inv₀  𝖡₄ 
    𝖡₄ ).mpr hle

𝗇 𝔄 𝖿
/-- The actual full-union polynomial regression gives a fixed strictly
positive ternary mass floor on all raw states, without a mass-good premise.
Thus mass-exceptional states still carry a genuine probability experiment. -/
theorem highUnionSource_ternary_floor_uniform C
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr η0 , 𝗹 ∧ 0 < η0 ∧
      ∀ k F , ∀ (_ : NeZero k), ∀ (_ : LinearOrder 𝙯), 𝗑 →
      ∀ I (_ : Fintype I) E (_ : (i : I) → MeasurableSpace $ E i )
        (R : 𝗽) M,
      𝗗 →
      ∀ cf : ℝ, 𝚐₁ → 𝔄 ≤ η0 →
      ∀ h ,
      ∀ V , |𝖮₂| ≤ Q.ρ →
      ∀ x y, Q.c ≤ ternaryMass Q.a
        (highUnionSourceRegression C R 𝔄 h x) V y := by
  obtain ⟨Cfr,hCfr,hbound⟩ := highFrameField_original_model_bounds C
  obtain ⟨η0,hη0,hguard⟩ := highFrame_ternary_amplitude_guards Q
  refine ⟨Cfr,η0,hCfr,hη0,?_⟩
  intro k F hk0 horder hk I hI E hE R M G cf hcf hη h V hV x y
  letI := hk0
  letI := horder
  letI := hI
  letI := hE
  let η := 𝔄
  let P := fun j => highFramePolynomial $ 𝖯 j
  have hP j :=
    (highFramePolynomial_coefficientL1_le _).trans $ 𝘛₁ j
  obtain ⟨_, hηsup⟩ := hguard η  𝖠₃  hη
  have hv := (hbound k hk0 hk cf hcf P hP).1 x
  exact (Q.legal _ V (hv.trans $ hηsup.trans $ by linarith [Q.ρ_pos] ) hV).2.2.1 y
