/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Shift.Multiplier3
public import DOZZ.ShiftEquations.Rbar.Continuation
import DOZZ.Complex.Identity
public import DOZZ.Correlations.Analytic.UnitVolumeExtension

/-!
# The γ/2 crossing on the two-pole slice

Write `α' = Q - η` and `α = 2/γ + η` (the charges of the two-pole expansion
`structureConstant_two_pole_expansion`). The unit-volume γ/2 crossing holds on its crossing region
`2Q < α + α' + ε - γ/2`. Continuing first in the third charge (along `z ↦ (Q - η, ε, z)` for fixed
`γ/2 + η < ε < 2/γ`, on `2/γ < Re z < Q`) and then in the middle charge (along
`z ↦ (Q - η, z, 2/γ + η)`, on `2η < Re z < 2/γ`), where both sides are holomorphic
(`unitVolumeStructureConstant_holomorphic_near_extended_domain` and the analytic multiplier), gives
the crossing `C̄(Q - η - γ/2, x, 2/γ + η) = T(Q - η, x, 2/γ + η) C̄(Q - η, x + γ/2, 2/γ + η)` for
`2η < x < 2/γ` ([KRV, §10.2]).
-/

@[expose] public section

open Filter Topology Set

namespace DOZZ.Proofs

/-- **The identity theorem along a real interval, from frequent agreement.** -/
theorem eq_of_real_interval_of_frequently {D : Set ℂ} (hD : IsOpen D) {g₁ g₂ : ℂ → ℂ}
    (hg₁ : DifferentiableOn ℂ g₁ D) (hg₂ : DifferentiableOn ℂ g₂ D) {a b x₀ : ℝ}
    (hJD : ∀ t : ℝ, a < t → t < b → (t : ℂ) ∈ D) (hx₀a : a < x₀) (hx₀b : x₀ < b)
    (hfreq : ∃ᶠ z in 𝓝[≠] (x₀ : ℂ), g₁ z = g₂ z) {t : ℝ} (ht₁ : a < t) (ht₂ : t < b) :
    g₁ t = g₂ t := by
  have hx₀D  := hJD x₀ hx₀a hx₀b
  let U := connectedComponentIn D (x₀ : ℂ)
  have hUo : IsOpen U := hD.connectedComponentIn
  have hUD : U ⊆ D := connectedComponentIn_subset D _
  have hEq  :=
    ((hg₁.mono hUD).analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq
      ((hg₂.mono hUD).analyticOnNhd hUo) isPreconnected_connectedComponentIn
      (mem_connectedComponentIn hx₀D) hfreq
  have hJU  :=
    (isPreconnected_Ioo.image _ Complex.continuous_ofReal.continuousOn).subset_connectedComponentIn
      ⟨x₀, ⟨hx₀a, hx₀b⟩, rfl⟩ (image_subset_iff.mpr fun s hs => hJD s hs.1 hs.2)
  exact hEq (hJU ⟨t, ⟨ht₁, ht₂⟩, rfl⟩)

/-- **The identity theorem along a real interval.** -/
theorem eq_of_real_interval {D : Set ℂ} (hD : IsOpen D) {g₁ g₂ : ℂ → ℂ}
    (hg₁ : DifferentiableOn ℂ g₁ D) (hg₂ : DifferentiableOn ℂ g₂ D) {a b c d : ℝ}
    (hJD : ∀ t : ℝ, a < t → t < b → (t : ℂ) ∈ D) (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b)
    (heq : ∀ t : ℝ, c < t → t < d → g₁ t = g₂ t) {t : ℝ} (ht₁ : a < t) (ht₂ : t < b) :
    g₁ t = g₂ t := by
  refine eq_of_real_interval_of_frequently hD hg₁ hg₂ hJD
    (x₀ := (c + d) / 2) (by linarith) (by linarith) ?_ ht₁ ht₂
  apply frequently_eq_of_real_interval _ ((d - c) / 2) (by linarith)
  intro x hx
  obtain ⟨hl, hr⟩ := abs_lt.mp hx
  exact heq x (by linarith) (by linarith)

/-- The charge line `z ↦ (u, z + s, w)`. -/
noncomputable def tripleSecond (u s w : ℂ) (z : ℂ) : Fin 3 → ℂ := ![u, z + s, w]

theorem differentiable_tripleSecond (u s w : ℂ) : Differentiable ℂ (tripleSecond u s w) := by
  rw [differentiable_pi]
  intro i
  fin_cases i
  · exact differentiable_const _
  · exact differentiable_id.add_const _
  · exact differentiable_const _

theorem tripleSecond_ofReal (u s w t : ℝ) :
    tripleSecond u s w (t : ℂ) = complexifyNCharges ![u, t + s, w] := by
  funext i
  fin_cases i <;> simp [tripleSecond, complexifyNCharges]

section
variable (γ : ℝ)

theorem crossA3_add_one_re (a' e a : ℂ) :
    (crossA3 γ a' e a + 1).re = γ / 4 * (a'.re + e.re + a.re - Q γ - γ) + 1 / 2 := by
  unfold crossA3
  simp [Complex.mul_re]
  ring

theorem crossB3_re (a' e a : ℂ) :
    (crossB3 γ a' e a).re = γ / 4 * (a'.re + e.re - a.re - Q γ) + 1 / 2 := by
  unfold crossB3
  simp [Complex.mul_re]

theorem one_sub_crossC3_re (a' : ℂ) :
    (1 - crossC3 γ a').re = γ / 2 * (Q γ - a'.re) := by
  unfold crossC3
  simp [Complex.mul_re]

theorem one_sub_mul_half_re (e : ℂ) : (1 - (γ : ℂ) * e / 2).re = 1 - γ * e.re / 2 := by
  simp [Complex.mul_re]

end

/-- The basic window facts for the slice `(Q - η, ·, 2/γ + η)`. -/
theorem slice_facts {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    Q γ = 2 / γ + γ / 2 ∧ 2 * Q γ = 4 / γ + γ ∧ γ / 2 < 2 / γ ∧ 4 / γ = 2 * (2 / γ) ∧
      0 < 2 / γ := by
  have hγh := half_gamma_lt_two_div hγ hγ2
  refine ⟨rfl, by rw [Q]; ring, hγh, by ring, by positivity⟩

section
variable {γ η ε t : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hη : 0 < η) (hε₁ : γ / 2 + η < ε) (hε₂ : ε < 2 / γ)
  (ht₁ : 2 / γ < t) (ht₂ : t < Q γ)
include hγ hγ2 hη hε₁ hε₂ ht₁ ht₂

theorem extendedSeiberg3_sliceA_left :
    ExtendedSeiberg3 γ (Q γ - η - γ / 2) ε t := by
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  refine extendedSeiberg3_of_lt hγ (by linarith) (by rw [hQ]; linarith) ht₂ ?_ ?_ ?_ ?_ <;>
    linarith

theorem extendedSeiberg3_sliceA_right :
    ExtendedSeiberg3 γ (Q γ - η) (ε + γ / 2) t := by
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  refine extendedSeiberg3_of_lt hγ (by linarith) (by rw [hQ]; linarith) ht₂ ?_ ?_ ?_ ?_ <;>
    linarith

end

section
variable {γ η x : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hη : 0 < η)
include hγ hγ2 hη

theorem extendedSeiberg3_sliceB_left
    (hη2 : η < γ / 2) (hx₁ : 2 * η < x) (hx₂ : x < 2 / γ) :
    ExtendedSeiberg3 γ (Q γ - η - γ / 2) x (2 / γ + η) := by
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  refine extendedSeiberg3_of_lt hγ (by linarith) (by rw [hQ]; linarith) (by rw [hQ]; linarith)
    ?_ ?_ ?_ ?_ <;> rw [hQ] at * <;> linarith

theorem extendedSeiberg3_sliceB_right
    (hη4 : η < γ / 4) (hx₁ : -(2 * η) < x) (hx₂ : x < 2 / γ) :
    ExtendedSeiberg3 γ (Q γ - η) (x + γ / 2) (2 / γ + η) := by
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  refine extendedSeiberg3_of_lt hγ (by linarith) (by rw [hQ]; linarith) (by rw [hQ]; linarith)
    ?_ ?_ ?_ ?_ <;> rw [hQ] at * <;> linarith

end

/-- `γ/4 · (2/γ) = 1/2`-type bound used for the multiplier conditions. -/
theorem quarter_mul_lt {γ u v : ℝ} (hγ : 0 < γ) (h : u < v) : γ / 4 * u < γ / 4 * v :=
  mul_lt_mul_of_pos_left h (by positivity)

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
  (M : Ω → MeasureTheory.Measure ℂ) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
  (hCross : ∀ μ α' ε α : ℝ, 0 < μ → γ / 2 < ε → ε < 2 / γ → α < Q γ → α' < Q γ →
      2 * Q γ < α + α' + ε - γ / 2 →
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α)
  {V₃ : Set (Fin 3 → ℂ)} {f₃ : (Fin 3 → ℂ) → ℂ}
  (hExt : IsUnitVolumeExtension P M γ V₃ f₃)
include Ω hγ hExt

private theorem crossing_of_interval {u a b c d t : ℝ}
    (v w : ℝ → ℝ) (vC wC : ℂ → ℂ)
    (hv : Differentiable ℂ vC) (hw : Differentiable ℂ wC)
    (hvR : ∀ x : ℝ, vC x = v x) (hwR : ∀ x : ℝ, wC x = w x)
    (hvRe : ∀ z, (vC z).re = v z.re) (hwRe : ∀ z, (wC z).re = w z.re)
    (hS : ∀ x, a < x → x < b →
      ExtendedSeiberg3 γ (u - γ / 2) (v x) (w x) ∧
      ExtendedSeiberg3 γ u (v x + γ / 2) (w x))
    (hT : ∀ x, a < x → x < b → γ - 2 / γ < u + v x + w x - Q γ ∧
      -(2 / γ) < u + v x - w x - Q γ ∧ v x < 2 / γ)
    (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b)
    (heq : ∀ x, c < x → x < d →
      unitVolumeStructureConstant P M γ (u - γ / 2) (v x) (w x) =
        crossingMultiplier3Real γ u (v x) (w x) *
          unitVolumeStructureConstant P M γ u (v x + γ / 2) (w x))
    (ht₁ : a < t) (ht₂ : t < b) :
    unitVolumeStructureConstant P M γ (u - γ / 2) (v t) (w t) =
      crossingMultiplier3Real γ u (v t) (w t) *
        unitVolumeStructureConstant P M γ u (v t + γ / 2) (w t) := by
  let L : ℂ → Fin 3 → ℂ := fun z => ![(↑(u - γ / 2) : ℂ), vC z, wC z]
  let R : ℂ → Fin 3 → ℂ := fun z => ![↑u, vC z + (↑(γ / 2) : ℂ), wC z]
  have hL : Differentiable ℂ L := by
    rw [differentiable_pi]
    intro i
    fin_cases i
    exacts [differentiable_const _, hv, hw]
  have hR : Differentiable ℂ R := by
    rw [differentiable_pi]
    intro i
    fin_cases i
    exacts [differentiable_const _, hv.add_const _, hw]
  have hLR (x : ℝ) : L x = complexifyNCharges ![u - γ / 2, v x, w x] := by
    ext i
    fin_cases i <;> simp [L, hvR, hwR, complexifyNCharges]
  have hRR (x : ℝ) : R x = complexifyNCharges ![u, v x + γ / 2, w x] := by
    ext i
    fin_cases i <;> simp [R, hvR, hwR, complexifyNCharges]
  let D := {z : ℂ | a < z.re ∧ z.re < b} ∩ L ⁻¹' V₃ ∩ R ⁻¹' V₃
  have hD : IsOpen D := (((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)).inter
    (hExt.isOpen.preimage hL.continuous)).inter (hExt.isOpen.preimage hR.continuous)
  have hJD (x : ℝ) (hx : a < x) (hx' : x < b) : (x : ℂ) ∈ D := by
    obtain ⟨hl, hr⟩ := hS x hx hx'
    exact ⟨⟨⟨hx, hx'⟩, show L x ∈ V₃ by rw [hLR]; exact hExt.mem _ hl⟩,
      show R x ∈ V₃ by rw [hRR]; exact hExt.mem _ hr⟩
  let T := fun z => crossingMultiplier3 γ (↑u) (vC z) (wC z)
  have hDiffT : DifferentiableOn ℂ T D := by
    rintro z ⟨⟨⟨hz, hz'⟩, _⟩, _⟩
    obtain ⟨hA, hB, hV⟩ := hT z.re hz hz'
    have hγq : γ / 4 * (2 / γ) = 1 / 2 := by field_simp <;> norm_num
    have hγh : γ * (2 / γ) = 2 := mul_div_cancel₀ _ hγ.ne'
    have hu : u < Q γ := (hS t ht₁ ht₂).2.1
    refine (differentiableAt_crossingMultiplier3 (φ₁ := fun _ => (u : ℂ))
      (differentiableAt_const _) (hv z) (hw z) ?_ ?_ ?_ ?_).differentiableWithinAt
    · rw [crossA3_add_one_re, Complex.ofReal_re, hvRe, hwRe]
      have := quarter_mul_lt hγ hA
      linarith
    · rw [crossB3_re, Complex.ofReal_re, hvRe, hwRe]
      have := quarter_mul_lt hγ hB
      linarith [mul_neg (γ / 4) (2 / γ)]
    · rw [one_sub_crossC3_re, Complex.ofReal_re]
      exact mul_pos (by positivity) (sub_pos.mpr hu)
    · rw [one_sub_mul_half_re, hvRe]
      linarith [mul_lt_mul_of_pos_left hV hγ]
  have h₁ (x : ℝ) (hx : a < x) (hx' : x < b) :
      f₃ (L x) = (unitVolumeStructureConstant P M γ (u - γ / 2) (v x) (w x) : ℂ) := by
    rw [hLR]
    exact hExt.value _ (hS x hx hx').1
  have h₂ (x : ℝ) (hx : a < x) (hx' : x < b) :
      T x * f₃ (R x) = (crossingMultiplier3Real γ u (v x) (w x) *
        unitVolumeStructureConstant P M γ u (v x + γ / 2) (w x) : ℝ) := by
    rw [hRR, hExt.value _ (hS x hx hx').2]
    simp only [T, hvR, hwR, crossingMultiplier3_ofReal hγ, Complex.ofReal_mul]
    rfl
  have h := eq_of_real_interval hD
    (hExt.holomorphic.comp hL.differentiableOn fun _ hz => hz.1.2)
    (hDiffT.mul (hExt.holomorphic.comp hR.differentiableOn fun _ hz => hz.2)) hJD hac hcd hdb
    (fun x hx hx' => by
      simp [h₁ x (hac.trans_lt hx) (hx'.trans_le hdb), h₂ x (hac.trans_lt hx) (hx'.trans_le hdb), heq x hx hx']) ht₁ ht₂
  change f₃ (L t) = T t * f₃ (R t) at h
  rw [h₁ t ht₁ ht₂, h₂ t ht₁ ht₂] at h
  exact_mod_cast h

include hγ2 hCross

/-- **Step A**: the crossing at `(Q - η, ε, t)` for `γ/2 + η < ε < 2/γ` and `2/γ < t < Q`,
continued from the crossing region in the third charge. -/
theorem unitVolume_crossing_sliceA
    {η ε : ℝ} (hη : 0 < η) (hε₁ : γ / 2 + η < ε) (hε₂ : ε < 2 / γ)
    {t : ℝ} (ht₁ : 2 / γ < t) (ht₂ : t < Q γ) :
    unitVolumeStructureConstant P M γ (Q γ - η - γ / 2) ε t =
      crossingMultiplier3Real γ (Q γ - η) ε t *
        unitVolumeStructureConstant P M γ (Q γ - η) (ε + γ / 2) t := by
  obtain ⟨hQ, _, hγh, _, _⟩ := slice_facts hγ hγ2
  let c := max (2 / γ) (Q γ + η + γ / 2 - ε)
  refine crossing_of_interval P M hγ hExt
    (fun _ => ε) id (fun _ => (ε : ℂ)) id (differentiable_const _) differentiable_id
    (fun _ => rfl) (fun _ => rfl) (fun _ => Complex.ofReal_re _) (fun _ => rfl) ?_ ?_
    (c := c) (le_max_left _ _) (max_lt (ht₁.trans ht₂) (by linarith)) le_rfl ?_ ht₁ ht₂
  · exact fun _ h1 h2 => ⟨extendedSeiberg3_sliceA_left hγ hγ2 hη hε₁ hε₂ h1 h2,
      extendedSeiberg3_sliceA_right hγ hγ2 hη hε₁ hε₂ h1 h2⟩
  · intro x h1 h2
    exact ⟨by dsimp [id]; rw [hQ] at h2; linarith, by dsimp [id]; rw [hQ] at h2; linarith, hε₂⟩
  · intro x hx h2
    have hx' := (le_max_right (2 / γ) (Q γ + η + γ / 2 - ε)).trans_lt hx
    have hp : 0 < (x + (Q γ - η) + ε - γ / 2 - 2 * Q γ) / γ := div_pos (by linarith) hγ
    exact (hCross 1 (Q γ - η) ε x one_pos (by linarith) hε₂ h2
      (by linarith) (by linarith)).trans
      (by rw [gammaHalfUnitCrossingMultiplier_real hγ one_pos (by linarith) hε₂ hp]; rfl)

/-- **Step B**: the crossing on the two-pole slice, `C̄(Q - η - γ/2, x, 2/γ + η) =
T(Q - η, x, 2/γ + η) C̄(Q - η, x + γ/2, 2/γ + η)` for `2η < x < 2/γ`. -/
theorem unitVolume_crossing_slice
    {η : ℝ} (hη : 0 < η) (hη4 : η < γ / 4) (hηγ : η < 2 / γ - γ / 2)
    {x : ℝ} (hx₁ : 2 * η < x) (hx₂ : x < 2 / γ) :
    unitVolumeStructureConstant P M γ (Q γ - η - γ / 2) x (2 / γ + η) =
      crossingMultiplier3Real γ (Q γ - η) x (2 / γ + η) *
        unitVolumeStructureConstant P M γ (Q γ - η) (x + γ / 2) (2 / γ + η) := by
  obtain ⟨hQ, _, hγh, _, _⟩ := slice_facts hγ hγ2
  refine crossing_of_interval P M hγ hExt
    id (fun _ => 2 / γ + η) id (fun _ => (↑(2 / γ + η) : ℂ))
    differentiable_id (differentiable_const _) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => Complex.ofReal_re _) ?_ ?_
    (c := γ / 2 + η) (by linarith) (by linarith) le_rfl ?_ hx₁ hx₂
  · exact fun _ h1 h2 => ⟨extendedSeiberg3_sliceB_left hγ hγ2 hη (by linarith) h1 h2,
      extendedSeiberg3_sliceB_right hγ hγ2 hη hη4 (by dsimp [id]; linarith) h2⟩
  · intro y h1 h2
    dsimp [id]
    exact ⟨by linarith, by linarith, h2⟩
  · exact fun x h1 h2 => unitVolume_crossing_sliceA P M hγ hγ2 hCross hExt
      hη h1 h2 (t := 2 / γ + η) (by linarith) (by rw [hQ]; linarith)

end

end DOZZ.Proofs

end
