module

public import Mathlib
public import PottsDiscontinuity.Bethe.ThetaK
public import PottsDiscontinuity.Bethe.FourierPoisson

/-!
# Proposition 2.1: the equations (cBE_Δ), (cOE_Δ) and the change of variables `x = k(α)`

Source: arXiv:1611.09877v2, §2.1 (equations (cBE_Δ), (cOE_Δ) and the proof of Proposition 2.1).

* `d1Theta`, `d2Theta`: the partial derivatives `∂₁Θ`, `∂₂Θ` of `theta`;
* `cBEop`, `IsCBESolution`: the equation (cBE_Δ); `cOEop`, `IsCOESolution`: the equation (cOE_Δ);
* `kInv`: explicit inverse of `kMap` (`kMap_kInv`, `kInv_kMap`);
* `Rtrans`, `Ttrans`, `PsiFn`: `R = 2π ρ(k) k'`, `T = 2π τ(k)`, `Ψ = (Θ(k·,-π) + Θ(k·,π))/2`;
* `isCBESolution_iff`, `isCOESolution_iff`: the change of variables turns (cBE), (cOE) into
  (cBE'): `R + (1/2π) Ξ_{2λ} * R = Ξ_λ` and (cOE'): `T + (1/2π) Ξ_{2λ} * T = Ψ` on `[-π, π]`.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

theorem kMap_surjective {lam : ℝ} (hlam : 0 < lam) : Function.Surjective (kMap lam) := by
  intro x
  have h (u : ℝ) := Real.arctan_mem_Ioo (Real.sin u / (Real.exp lam - Real.cos u))
  have h₁ : kMap lam (x - π) ≤ x := by unfold kMap; linarith [(h (x - π)).2]
  have h₂ : x ≤ kMap lam (x + π) := by unfold kMap; linarith [(h (x + π)).1]
  obtain ⟨y, _, hy⟩ := intermediate_value_Icc (by linarith [pi_pos] : x - π ≤ x + π)
    (continuous_kMap hlam).continuousOn ⟨h₁, h₂⟩
  exact ⟨y, hy⟩

noncomputable def kIso {lam : ℝ} (hlam : 0 < lam) : ℝ ≃o ℝ :=
  (strictMono_kMap hlam).orderIsoOfSurjective _ (kMap_surjective hlam)

/-- The inverse of the strictly increasing change of coordinate `kMap`. -/
noncomputable def kInv (lam x : ℝ) : ℝ := if h : 0 < lam then (kIso h).symm x else x

theorem kMap_kInv {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : kMap lam (kInv lam x) = x := by
  rw [kInv, dite_eq_left hlam]
  exact (kIso hlam).apply_symm_apply x

theorem kInv_kMap {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : kInv lam (kMap lam x) = x := by
  rw [kInv, dite_eq_left hlam]
  exact (kIso hlam).symm_apply_apply x

theorem kInv_neg (lam x : ℝ) : kInv lam (-x) = -kInv lam x := by
  by_cases hlam : 0 < lam
  · apply (strictMono_kMap hlam).injective
    simp [kMap_neg, kMap_kInv hlam]
  · simp [kInv, hlam]

theorem continuous_kInv {lam : ℝ} (hlam : 0 < lam) : Continuous (kInv lam) := by
  rw [show kInv lam = (kIso hlam).symm from funext fun _ => dif_pos hlam]
  exact (kIso hlam).symm.continuous

theorem hasDerivAt_kInv {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    HasDerivAt (kInv lam) (Xi lam (kInv lam x))⁻¹ x :=
  (hasDerivAt_kMap hlam _).of_local_left_inverse (continuous_kInv hlam).continuousAt
    (Xi_pos hlam _).ne' (.of_forall (kMap_kInv hlam))

theorem kInv_mem_Icc {lam x : ℝ} (hlam : 0 < lam) (hx : x ∈ Icc (-π) π) :
    kInv lam x ∈ Icc (-π) π := by
  refine ⟨(strictMono_kMap hlam).le_iff_le.mp ?_, (strictMono_kMap hlam).le_iff_le.mp ?_⟩
  · simpa [kMap_neg_pi, kMap_kInv hlam] using hx.1
  · simpa [kMap_pi, kMap_kInv hlam] using hx.2

theorem kMap_mem_Icc {lam : ℝ} (hlam : 0 < lam) {α : ℝ} (hα : α ∈ Icc (-π) π) :
    kMap lam α ∈ Icc (-π) π := mapsTo_kMap hlam hα

/-! ### The operators of (cBE) and (cOE) -/

/-- `∂₁Θ_Δ(x, y)`, the partial derivative of the Bethe phase in its first variable. -/
noncomputable def d1Theta (Δ x y : ℝ) : ℝ := deriv (fun s => theta Δ s y) x

/-- `∂₂Θ_Δ(x, y)`, the partial derivative of the Bethe phase in its second variable. -/
noncomputable def d2Theta (Δ x y : ℝ) : ℝ := deriv (fun t => theta Δ x t) y

section

variable (Δ : ℝ)

/-- The right-hand side of (cBE_Δ): `1 + ∫_{-π}^{π} ∂₁Θ(x,y) ρ(y) dy`. -/
noncomputable def cBEop (ρ : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 + ∫ y in (-π)..π, d1Theta Δ x y * ρ y

/-- `ρ` solves (cBE_Δ): `2π ρ(x) = 1 + ∫_{-π}^{π} ∂₁Θ(x,y) ρ(y) dy` for all `x ∈ [-π, π]`. -/
def IsCBESolution (ρ : ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc (-π) π, 2 * π * ρ x = cBEop Δ ρ x

/-- The right-hand side of (cOE_Δ):
`(Θ(x,-π) + Θ(x,π))/2 - ∫_{-π}^{π} ∂₂Θ(x,y) τ(y) dy`. -/
noncomputable def cOEop (τ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (theta Δ x (-π) + theta Δ x π) / 2 - ∫ y in (-π)..π, d2Theta Δ x y * τ y

/-- `τ` solves (cOE_Δ): `2π τ(x) = (Θ(x,-π)+Θ(x,π))/2 - ∫_{-π}^{π} ∂₂Θ(x,y) τ(y) dy` for all
`x ∈ [-π, π]`. -/
def IsCOESolution (τ : ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc (-π) π, 2 * π * τ x = cOEop Δ τ x

/-! ### The change of variables `x = k(α)` -/

/-- `R(α) = 2π ρ(k(α)) k'(α)`. -/
noncomputable def Rtrans (ρ : ℝ → ℝ) (α : ℝ) : ℝ :=
  2 * π * ρ (kMap (lamOf Δ) α) * deriv (kMap (lamOf Δ)) α

/-- `T(α) = 2π τ(k(α))`. -/
noncomputable def Ttrans (τ : ℝ → ℝ) (α : ℝ) : ℝ :=
  2 * π * τ (kMap (lamOf Δ) α)

/-- `Ψ(α) = (Θ(k(α),-π) + Θ(k(α),π))/2`. -/
noncomputable def PsiFn (α : ℝ) : ℝ :=
  (theta Δ (kMap (lamOf Δ) α) (-π) + theta Δ (kMap (lamOf Δ) α) π) / 2

end

theorem Rtrans_eq {Δ : ℝ} (hΔ : Δ < -1) (ρ : ℝ → ℝ) (α : ℝ) :
    Rtrans Δ ρ α = 2 * π * ρ (kMap (lamOf Δ) α) * Xi (lamOf Δ) α := by
  rw [Rtrans, deriv_kMap (lamOf_pos hΔ)]

theorem integral_Icc_comp_kMap {lam : ℝ} (hlam : 0 < lam) (g : ℝ → ℝ) :
    ∫ y in (-π)..π, g y = ∫ β in (-π)..π, Xi lam β * g (kMap lam β) := by
  have hpi := Real.pi_pos
  have himg := (bijOn_kMap hlam).image_eq
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Icc (-π) π) (f := kMap lam)
    (f' := Xi lam) measurableSet_Icc (fun x _ => (hasDerivAt_kMap hlam x).hasDerivWithinAt)
    (strictMono_kMap hlam).injective.injOn g
  rw [himg] at hcov
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc, hcov]
  refine setIntegral_congr_fun measurableSet_Icc fun β _ => ?_
  simp only [smul_eq_mul]
  rw [abs_of_pos (Xi_pos hlam β)]

/-- Change of variables `x = k(α)` in (cBE): for every function `ρ` and every `α`,
`cBEop ρ (k α) = 1 - (1/(2π Ξ_λ(α))) ∫_{-π}^{π} Ξ_{2λ}(α-β) (2π ρ(k β) Ξ_λ(β)) dβ`. -/
theorem cBEop_kMap {Δ : ℝ} (hΔ : Δ < -1) (ρ : ℝ → ℝ) (α : ℝ) :
    cBEop Δ ρ (kMap (lamOf Δ) α) =
      1 - (2 * π * Xi (lamOf Δ) α)⁻¹ *
        ∫ β in (-π)..π, Xi (2 * lamOf Δ) (α - β) * (2 * π * ρ (kMap (lamOf Δ) β) * Xi (lamOf Δ) β) := by
  have hlam := lamOf_pos hΔ
  have hcosh := cosh_lamOf hΔ
  have hXa := Xi_pos hlam α
  unfold cBEop
  rw [integral_Icc_comp_kMap hlam]
  have h1 : ∀ β : ℝ, Xi (lamOf Δ) β * (d1Theta Δ (kMap (lamOf Δ) α) (kMap (lamOf Δ) β) * ρ (kMap (lamOf Δ) β)) =
      -((2 * π * Xi (lamOf Δ) α)⁻¹ *
        (Xi (2 * lamOf Δ) (α - β) * (2 * π * ρ (kMap (lamOf Δ) β) * Xi (lamOf Δ) β))) := by
    intro β
    rw [d1Theta, deriv_theta_left_kMap hlam hcosh α β]
    field_simp
  simp_rw [h1]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  ring

/-- Change of variables `x = k(α)` in (cOE): for every function `τ` and every `α`,
`cOEop τ (k α) = Ψ(α) - ∫_{-π}^{π} Ξ_{2λ}(α-β) τ(k β) dβ`. -/
theorem cOEop_kMap {Δ : ℝ} (hΔ : Δ < -1) (τ : ℝ → ℝ) (α : ℝ) :
    cOEop Δ τ (kMap (lamOf Δ) α) =
      PsiFn Δ α - ∫ β in (-π)..π, Xi (2 * lamOf Δ) (α - β) * τ (kMap (lamOf Δ) β) := by
  have hlam := lamOf_pos hΔ
  have hcosh := cosh_lamOf hΔ
  unfold cOEop PsiFn
  rw [integral_Icc_comp_kMap hlam]
  grind only [d2Theta, Xi_pos, deriv_theta_right_kMap]

theorem xiConv_Rtrans {Δ : ℝ} (hΔ : Δ < -1) (ρ : ℝ → ℝ) (α : ℝ) :
    xiConv (2 * lamOf Δ) (Rtrans Δ ρ) α =
      (2 * π)⁻¹ * ∫ β in (-π)..π,
        Xi (2 * lamOf Δ) (α - β) * (2 * π * ρ (kMap (lamOf Δ) β) * Xi (lamOf Δ) β) := by
  have : Rtrans Δ ρ = fun β => 2 * π * ρ (kMap (lamOf Δ) β) * Xi (lamOf Δ) β :=
    funext (Rtrans_eq hΔ ρ)
  rw [xiConv, this]

theorem xiConv_Ttrans {Δ : ℝ} (τ : ℝ → ℝ) (α : ℝ) :
    xiConv (2 * lamOf Δ) (Ttrans Δ τ) α =
      ∫ β in (-π)..π, Xi (2 * lamOf Δ) (α - β) * τ (kMap (lamOf Δ) β) := by
  unfold xiConv Ttrans
  have : ∀ β : ℝ, Xi (2 * lamOf Δ) (α - β) * (2 * π * τ (kMap (lamOf Δ) β)) =
      (2 * π) * (Xi (2 * lamOf Δ) (α - β) * τ (kMap (lamOf Δ) β)) := fun β => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- Pointwise form of the change of variables for (cBE): the equation at `x = k(α)` is
equivalent to (cBE') at `α`. -/
theorem cBE_at_iff {Δ : ℝ} (hΔ : Δ < -1) (ρ : ℝ → ℝ) (α : ℝ) :
    (2 * π * ρ (kMap (lamOf Δ) α) = cBEop Δ ρ (kMap (lamOf Δ) α)) ↔
      Rtrans Δ ρ α + xiConv (2 * lamOf Δ) (Rtrans Δ ρ) α = Xi (lamOf Δ) α := by
  have hlam := lamOf_pos hΔ
  have hpi := Real.pi_pos
  have hXa := Xi_pos hlam α
  grind only [cBEop_kMap, Rtrans_eq, xiConv_Rtrans]

/-- Pointwise form of the change of variables for (cOE). -/
theorem cOE_at_iff {Δ : ℝ} (hΔ : Δ < -1) (τ : ℝ → ℝ) (α : ℝ) :
    (2 * π * τ (kMap (lamOf Δ) α) = cOEop Δ τ (kMap (lamOf Δ) α)) ↔
      Ttrans Δ τ α + xiConv (2 * lamOf Δ) (Ttrans Δ τ) α = PsiFn Δ α := by
  grind [cOEop_kMap, xiConv_Ttrans, Ttrans]

/-- (cBE) is equivalent to (cBE') for `R = 2π ρ(k·) k'`: for `x = k(α)`,
`R + (1/2π) Ξ_{2λ} * R = Ξ_λ`. -/
theorem isCBESolution_iff {Δ : ℝ} (hΔ : Δ < -1) (ρ : ℝ → ℝ) :
    IsCBESolution Δ ρ ↔ ∀ α ∈ Icc (-π) π,
      Rtrans Δ ρ α + xiConv (2 * lamOf Δ) (Rtrans Δ ρ) α = Xi (lamOf Δ) α := by
  have hlam := lamOf_pos hΔ
  constructor
  · intro h α hα
    exact (cBE_at_iff hΔ ρ α).1 (h _ (kMap_mem_Icc hlam hα))
  · intro h x hx
    have hα := kInv_mem_Icc hlam hx
    have := (cBE_at_iff hΔ ρ (kInv (lamOf Δ) x)).2 (h _ hα)
    rwa [kMap_kInv hlam] at this

/-- (cOE) is equivalent to (cOE') for `T = 2π τ(k·)`: `T + (1/2π) Ξ_{2λ} * T = Ψ`. -/
theorem isCOESolution_iff {Δ : ℝ} (hΔ : Δ < -1) (τ : ℝ → ℝ) :
    IsCOESolution Δ τ ↔ ∀ α ∈ Icc (-π) π,
      Ttrans Δ τ α + xiConv (2 * lamOf Δ) (Ttrans Δ τ) α = PsiFn Δ α := by
  have hlam := lamOf_pos hΔ
  constructor
  · intro h α hα
    exact (cOE_at_iff hΔ τ α).1 (h _ (kMap_mem_Icc hlam hα))
  · intro h x hx
    have hα := kInv_mem_Icc hlam hx
    have := (cOE_at_iff hΔ τ (kInv (lamOf Δ) x)).2 (h _ hα)
    rwa [kMap_kInv hlam] at this

end PottsDiscontinuity.Bethe
