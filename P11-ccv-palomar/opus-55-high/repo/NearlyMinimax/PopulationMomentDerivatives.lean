module

public import NearlyMinimax.AnchoredMoments
public import NearlyMinimax.PopulationInverseDerivatives
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗎

/-! The inverse derivative chart evaluated at genuine bounded population moments. -/

open Matrix MeasureTheory
𝚺

𝗇 𝔍 𝗎
𝗇 𝔄 (Fintype.equivFin 𝔍).symm i
𝗇 𝔇 if t then 𝙃 else f
𝗇 𝔈 𝚃
/-- The two population vector families are the density-feature moment and the
response-feature moment, with the known Lebesgue Gram preconditioner. -/
def anchoredFinMomentFamilies (u : Covariate d)
    (p f : 𝙀) : Bool → Fin 𝔈 → ℝ :=
  fun t i => anchoredPreconditionedMoment u p 𝔇
    𝔄

theorem anchoredFinMomentFamilies_uniform_bound
    b F (hb : 𝘸) (hF : 0 ≤ F) :
    ∃ W , 0 < W ∧ ∀ u ∈ unitCube d, ∀ p f ,
      𝗍 →
      (∀ w ∈ unitCube d, |f w| ≤ F) →
      ∀ t, ‖anchoredFinMomentFamilies (ℓ := ℓ) u p f t‖ ≤ W := by
  obtain ⟨W, hW, hm⟩ := anchoredPreconditionedMoment_uniform_bound
      b (max 1 F) hb $ le_trans zero_le_one $ le_max_left ..
  refine ⟨W, hW, ?_⟩
  intro u hu p f hp hf t
  have hg : ∀ w ∈ unitCube d, |𝔇 w| ≤ max 1 F := by
    intro w hw
    cases t
    · exact (hf w hw).trans $ le_max_right ..
    · simp
  apply (pi_norm_le_iff_of_nonneg hW.le).mpr
  intro i
  exact (norm_le_pi_norm _ 𝔄).trans $ hm u hu p _ hp hg

𝗇 𝔅 fun w hw => ⟨ha.le.trans hw.1, hw.2⟩
𝗇 𝔉 anchoredFinMomentFamilies u p f
𝗇 𝔊 anchoredFinMomentFamilies v q g
/-- The paper's common all-order inverse derivative estimate, with all matrix
charts and vector-size bounds derived from actual density and response bounds. -/
theorem anchored_actual_population_inverse_derivatives
    [Nonempty 𝔍] a b F Y
    (ha : 𝙆) (hab : 𝙭) (hF : 0 ≤ F) (hY : 0 ≤ Y) :
    ∃ C A , 𝙴 ∧ 𝘪 ∧
      ∀ u v , 𝘨₁ → v ∈ unitCube d →
      ∀ p q f g , Measurable p → Measurable q →
      𝖡 →
      𝗭 →
      (∀ w ∈ unitCube d, |f w| ≤ F) →
      (∀ w ∈ unitCube d, |g w| ≤ F) →
      ∀ y , |y| ≤ Y → ∀ m k ,
      ∀ directions ,
        ‖𝗸₁
          (incrementFinVector 𝔈 a b (anchoredFinTransport d ℓ) y m)
          (fun j => incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q)
            𝔉 𝔊
            $ (Fintype.equivFin $ incrementVariables 𝔈 ).symm j ) directions‖ ≤
          C * k.factorial * 𝚇₁ * ∏ j, ‖directions j‖ := by
  obtain ⟨W, hW, hmom⟩ := anchoredFinMomentFamilies_uniform_bound b F 𝙬₁ hF
  obtain ⟨C, A, hC, hA, hder⟩ := anchored_population_inverse_derivatives
    (d := d) (ℓ := ℓ) a b W Y ha hab hW.le hY
  refine ⟨C, A, hC, hA, ?_⟩
  intro u v hu hv p q f g hpmeas hqmeas hp hq hf hg y hy m k directions
  exact hder u v hu hv p q hpmeas hqmeas hp hq
    𝔉 𝔊
    (hmom u hu p f (hp.mono 𝔅) hf)
    (hmom v hv q g (hq.mono 𝔅) hg)
    y hy m k directions
