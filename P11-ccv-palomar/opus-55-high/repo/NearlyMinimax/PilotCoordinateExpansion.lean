module

public import NearlyMinimax.DyadicPilotFeatures
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Exact linear-coordinate representation of the actual local raw pilot
using one fixed finite global feature vector for all anchors at a level. -/

𝛄
𝚪
𝚨

𝚭
𝚩

𝗇 𝔊 PilotBasisIndex q d ℓ
def pilotPolynomialLinear (c : Fin q) (P : 𝙣)
    (response : Bool) : (Fin (Fintype.card 𝔊) → ℝ) →L[ℝ] ℝ :=
  ∑ β : 𝗫₂, P.coeff (polynomialBoxExponent β) •
    ContinuousLinearMap.proj ((Fintype.equivFin 𝔊) ((c, β), response))

/-- A polynomial with a design-cell indicator and an optional response factor
is exactly a continuous linear function of the finite global coordinates. -/
theorem pilotPolynomialLinear_raw_apply (cell : Covariate d → Fin q)
    c P (hP : P.totalDegree ≤ ℓ)
    response z :
    pilotPolynomialLinear (ℓ := ℓ) c P response (pilotRawVector cell z) =
      if cell z.1 = c then eval z.1 P * if response then z.2 else 1 else 0 := by
  classical
  simp only [pilotPolynomialLinear, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, pilotRawVector, Equiv.symm_apply_apply, smul_eq_mul,
    pilotBasisFeature]
  by_cases h : cell z.1 = c
  · simp only [h, ite_true, ← mul_assoc, ← Finset.sum_mul]
    rw [polynomial_box_evaluation P hP]
    rfl
  · simp_all

𝗇 𝔅 𝗟 ^ j
abbrev DyadicPilotLabelIndex (d j : ℕ) := Fin d → Fin 𝔅

𝗇 𝔄 DyadicPilotLabelIndex d j
def dyadicPilotLabel (j : ℕ) (x : Covariate d) :
    Fin $ Fintype.card 𝔄 :=
  Fintype.equivFin 𝔄
    $ regularGridCell 𝔅  𝖠₃  x

theorem dyadicPilotLabel_measurable j :
    Measurable $ dyadicPilotLabel (d := d) j :=
  (measurable_of_countable _).comp $ regular_grid_cell_measurable ..

𝗃 𝔉 ἀ j x
theorem dyadicPilotLabel_eq_iff j (x z : Covariate d) :
    dyadicPilotLabel j z = 𝔉 dyadicPilotLabel ↔ z ∈ 𝔉 dyadicPilotCell :=
  (Fintype.equivFin 𝔄).injective.eq_iff

𝗇 𝔇 𝗬₂
def dyadicPilotPolynomial (j : ℕ) (x : Covariate d)
    (a : 𝔇) : 𝙣 :=
  match a with
  | 𝙫₂ => 𝔉 dyadicFeaturePolynomial γ * 𝔉 dyadicFeaturePolynomial δ
  | Sum.inr $ Sum.inl γ => 𝔉 dyadicFeaturePolynomial γ
  | Sum.inr $ Sum.inr γ => 𝔉 dyadicFeaturePolynomial γ

def dyadicPilotResponse (a : 𝔇) : Bool :=
  match a with
  | Sum.inl _ => false
  | Sum.inr $ Sum.inl _ => true
  | Sum.inr $ Sum.inr _ => false

𝗇 𝔈 𝔉 dyadicPilotPolynomial a
theorem dyadicPilotPolynomial_degree j x
    (a : 𝔇) : (𝔈).totalDegree ≤ 𝗭₂ := by
  cases a with
  | inl a =>
    exact 𝗯₂
      $ (Nat.add_le_add (𝔉 dyadicFeaturePolynomial_degree a.1)
        $ 𝔉 dyadicFeaturePolynomial_degree a.2 ).trans_eq 𝖡₃
  | inr a =>
    cases a <;> exact (𝔉 dyadicFeaturePolynomial_degree _).trans 𝖡₃

theorem dyadicPilotPolynomial_scalar j x
    (a : 𝔇) z :
    eval z.1 𝔈 * (if dyadicPilotResponse a then z.2 else 1) =
      𝔉 dyadicPilotScalar a z := by
  cases a with
  | inl a => simp [dyadicPilotPolynomial, dyadicPilotResponse, dyadicPilotScalar,
      dyadicFeaturePolynomial_eval]
  | inr a =>
    cases a <;> simp [dyadicPilotPolynomial, dyadicPilotResponse, dyadicPilotScalar,
      dyadicFeaturePolynomial_eval, mul_comm]

def dyadicPilotCoordinate (j : ℕ) (x : Covariate d)
    (a : 𝔇) :
    (Fin (Fintype.card $ PilotBasisIndex (Fintype.card 𝔄) d 𝗭₂ ) → ℝ) →L[ℝ] ℝ :=
  𝘟 • pilotPolynomialLinear 𝔉 dyadicPilotLabel
    𝔈 (dyadicPilotResponse a)

/-- The exact raw current-cell feature is represented for every anchor and
observation by the same global feature vector. No moment equality is assumed. -/
theorem dyadicPilotCoordinate_raw_apply j x
    (a : 𝔇) z :
    𝔉 dyadicPilotCoordinate a (pilotRawVector (dyadicPilotLabel j) z) =
      𝔉 dyadicPilotFeature a z := by
  rw [dyadicPilotCoordinate, ContinuousLinearMap.smul_apply,
    pilotPolynomialLinear_raw_apply _ _ _ $ 𝔉 dyadicPilotPolynomial_degree a ]
  simp only [dyadicPilotPolynomial_scalar,
    dyadicPilotFeature]
  by_cases h : z.1 ∈ 𝔉 dyadicPilotCell
  · have he := (𝔉 dyadicPilotLabel_eq_iff z.1).mpr h
    simp_all
  · have he :=
      fun he => h $ (𝔉 dyadicPilotLabel_eq_iff z.1).mp he
    simp_all
