/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Gluing.BandLine
public import DOZZ.ShiftEquations.Gluing.Meromorphy
public import DOZZ.Statements.Defs.ExtendedSeiberg3
import DOZZ.ShiftEquations.Shift.ShiftGluing
import DOZZ.ShiftEquations.Shift.Reflection
public import DOZZ.ShiftEquations.Residual.Calibration
import DOZZ.Complex.Basic
public import DOZZ.ShiftEquations.Representatives
public import DOZZ.Correlations.Analytic.UnitVolumeExtension

/-!
# The γ/2 shifts at exact real points, for spectators near `Q`

For spectators `b, c` near `Q`, the first structure shift
(`DOZZ.structureConstant_first_shift_strip`) and the reflected shift
(`DOZZ.structureConstant_reflected_shift_and_gluing`) are identities between meromorphic germs on a
strip. Their functions agree with the physical structure constant `C(·, b, c)` on `(2η, Q)`, hence
(identity theorem) with its continuation `C_f(·, b, c)` through the holomorphic unit-volume
extension `f` (`DOZZ.unitVolumeStructureConstant_holomorphic_near_extended_domain`). Where the shift
coefficient is analytic, continuity turns the germ identities into exact identities at real points:
`C(α) = -𝒜(α - γ/2) C(α - γ)/(πμ)` for `α < Q` and `R(α) C(2Q - α) = -𝒜(α - γ/2) C(α - γ)/(πμ)` for
`α > Q` near `Q`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- Two germs that agree on a punctured neighbourhood and are continuous at the point agree at
the point. -/
theorem eq_of_eventuallyEq_nhdsNE_of_continuousAt {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[𝓝[≠] z] g) (hf : ContinuousAt f z) (hg : ContinuousAt g z) : f z = g z :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

private theorem extendedSeiberg3_slice_of_near {γ η b c x : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hη : 0 < η ∧ Q γ - 2 * η > γ) (hb : Q γ - η < b ∧ b < Q γ)
    (hc : Q γ - η < c ∧ c < Q γ) (hx : 2 * η < x) (hQ : x < Q γ) :
    ExtendedSeiberg3 γ x b c :=
  extendedSeiberg3_slice hγ hγ2 hη hb hc
    (max_lt (by linarith [hb.2, hc.1, hη.1]) (by linarith [hb.1, hc.2, hη.1])) hQ

private theorem structureConstantH_slice_value {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) {γ μ x b c : ℝ} (hμ : 0 < μ)
    {f : (Fin 3 → ℂ) → ℂ}
    (hf : f (complexifyNCharges ![x,b,c]) = (unitVolumeStructureConstant P M γ x b c : ℂ)) :
    structureConstantH f γ μ (tripleFirst (b : ℂ) (c : ℂ) (x : ℂ)) =
      (structureConstant P M γ μ x b c : ℂ) := by
  rw [tripleFirst_ofReal]
  exact structureConstantH_complexify P M hμ ![x,b,c] hf

/-- **A meromorphic function on a strip that equals the physical slice on `(2η, Q)` has the germs
of the continued slice there.** -/
theorem eventuallyEq_structureConstantH_of_physical {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) {γ μ η b c : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hμ : 0 < μ) (hη : 0 < η ∧ Q γ - 2 * η > γ) (hb : Q γ - η < b ∧ b < Q γ)
    (hc : Q γ - η < c ∧ c < Q γ)
    {V₃ : Set (Fin 3 → ℂ)} {f₃ : (Fin 3 → ℂ) → ℂ}
    (hExt : IsUnitVolumeExtension P M γ V₃ f₃)
    {h : ℝ} (hh : 0 < h) {C : ℂ → ℂ} (hCm : MeromorphicOn C (horizontalStrip h))
    (hCv : RepresentsStructureConstant P M γ μ η b c C)
    {x : ℝ} (hx₁ : 2 * η < x) (hx₂ : x < Q γ) :
    C =ᶠ[𝓝[≠] (x : ℂ)] fun z => structureConstantH f₃ γ μ (tripleFirst (b : ℂ) (c : ℂ) z) := by
  set g : ℂ → ℂ := fun z => structureConstantH f₃ γ μ (tripleFirst (b : ℂ) (c : ℂ) z) with hg
  set D : Set ℂ := horizontalStrip h ∩ tripleFirst (b : ℂ) (c : ℂ) ⁻¹' V₃ with hD
  have hDo : IsOpen D := (isOpen_horizontalStrip h).inter
    (hExt.isOpen.preimage (differentiable_tripleFirst _ _).continuous)
  have hES : ∀ t : ℝ, 2 * η < t → t < Q γ → ExtendedSeiberg3 γ t b c :=
    fun _ => extendedSeiberg3_slice_of_near hγ hγ2 hη hb hc
  have hDmem : ∀ t : ℝ, 2 * η < t → t < Q γ → (t : ℂ) ∈ D := fun t h1 h2 => by
    refine ⟨?_, ?_⟩
    · change |((t : ℝ) : ℂ).im| < h
      simpa using hh
    · change tripleFirst (b : ℂ) (c : ℂ) (t : ℂ) ∈ V₃
      rw [tripleFirst_ofReal]
      exact hExt.mem ![t, b, c] (hES t h1 h2)
  have hgval (t : ℝ) (h1 : 2 * η < t) (h2 : t < Q γ) :
      g t = (structureConstant P M γ μ t b c : ℂ) :=
    structureConstantH_slice_value P M hμ (hExt.value ![t,b,c] (hES t h1 h2))
  have hgm : MeromorphicOn g D := fun z hz =>
    meromorphicOn_structureConstantH_comp hExt.isOpen hExt.holomorphic hμ (differentiable_tripleFirst _ _) z hz.2
  have hCm' : MeromorphicOn C D := fun z hz => hCm z hz.1
  set W := connectedComponentIn D (x : ℂ) with hW
  have hWsub : W ⊆ D := connectedComponentIn_subset D _
  have hxW  := mem_connectedComponentIn (hDmem x hx₁ hx₂)
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] x, C t = g t :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_of_mem (Ioo_mem_nhds hx₁ hx₂)
      fun t ht => (hCv t ht.1 ht.2).trans (hgval t ht.1 ht.2).symm)
  exact ShiftGluing.meromorphicOn_eventuallyEq_of_frequently
    (fun z hz => hCm' z (hWsub hz)) (fun z hz => hgm z (hWsub hz))
    isPreconnected_connectedComponentIn hxW hxW
    ((tendsto_ofReal_nhdsNE_slice x).frequently hev.frequently)

/-- The continued slice is analytic at real points of `(2η, Q)` (there `s > 0`). -/
theorem analyticAt_structureConstantH_slice {γ μ η b c : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hμ : 0 < μ) (hη : 0 < η ∧ Q γ - 2 * η > γ) (hb : Q γ - η < b ∧ b < Q γ)
    (hc : Q γ - η < c ∧ c < Q γ)
    {V₃ : Set (Fin 3 → ℂ)} (hV₃ : IsOpen V₃)
    (hV₃mem : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) → complexifyNCharges α ∈ V₃)
    {f₃ : (Fin 3 → ℂ) → ℂ} (hf₃ : DifferentiableOn ℂ f₃ V₃)
    {x : ℝ} (hx₁ : 2 * η < x) (hx₂ : x < Q γ) :
    AnalyticAt ℂ (fun z => structureConstantH f₃ γ μ (tripleFirst (b : ℂ) (c : ℂ) z)) (x : ℂ) := by
  have hES := extendedSeiberg3_slice_of_near hγ hγ2 hη hb hc hx₁ hx₂
  refine analyticAt_structureConstantH_comp hV₃ hf₃ hμ (differentiable_tripleFirst _ _) ?_ ?_
  · rw [tripleFirst_ofReal]
    apply hV₃mem <;> assumption
  · intro n hn
    rw [tripleFirst_ofReal, sExpC_complexify] at hn
    have hs : 0 < sExp γ x b c := by
      unfold sExp
      exact div_pos (by linarith [hb.1, hc.1]) hγ
    have hn' : sExp γ x b c = -(n : ℝ) := by exact_mod_cast hn
    linarith

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ) {γ μ η b c : ℝ}
  (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) (hη : 0 < η ∧ Q γ - 2 * η > γ) (hb : Q γ - η < b ∧ b < Q γ)
  (hc : Q γ - η < c ∧ c < Q γ) {V₃ : Set (Fin 3 → ℂ)} {f₃ : (Fin 3 → ℂ) → ℂ}
    (hExt : IsUnitVolumeExtension P M γ V₃ f₃)
  {h : ℝ} (hh : 0 < h)
include Ω hγ hγ2 hμ hη hb hc hExt hh

/-- Simultaneously transport the germ, continuity and exact value along an affine change
of the first charge. -/
private theorem structureConstantH_comp_slice_data {C u : ℂ → ℂ}
    (hCm : MeromorphicOn C (horizontalStrip h)) (hCv : RepresentsStructureConstant P M γ μ η b c C)
    {w : ℂ} {x : ℝ} (hu : ContinuousAt u w) (hui : Function.Injective u)
    (he : u w = (x : ℂ)) (h₁ : 2 * η < x) (h₂ : x < Q γ) :
    let g := fun z : ℂ => structureConstantH f₃ γ μ (tripleFirst (b : ℂ) (c : ℂ) (u z))
    (fun z => C (u z)) =ᶠ[𝓝[≠] w] g ∧ ContinuousAt g w ∧
      g w = (structureConstant P M γ μ x b c : ℂ) := by
  have ht : Tendsto u (𝓝[≠] w) (𝓝[≠] (x : ℂ)) := by
    rw [← he]
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hu.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun _ hw h => hw (hui h))
  refine ⟨ht.eventually (eventuallyEq_structureConstantH_of_physical P M hγ hγ2 hμ hη hb hc hExt hh hCm hCv h₁ h₂), ?_, ?_⟩
  · exact (analyticAt_structureConstantH_slice hγ hγ2 hμ hη hb hc hExt.isOpen hExt.mem hExt.holomorphic h₁ h₂).continuousAt
      |>.comp_of_eq hu he
  · dsimp only
    rw [he]
    exact structureConstantH_slice_value P M hμ
      (hExt.value ![x,b,c] (extendedSeiberg3_slice_of_near hγ hγ2 hη hb hc h₁ h₂))

/-- **The first structure shift at an exact real point** near `Q`, from a strip function of
`DOZZ.structureConstant_first_shift_strip`. -/
theorem firstShift_exact_of_strip {C : ℂ → ℂ} (hCm : MeromorphicOn C (horizontalStrip h))
    (hCv : RepresentsStructureConstant P M γ μ η b c C)
    (hCs : ∀ᶠ z in codiscrete ℂ, C (z + γ / 2) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (b : ℂ) (c : ℂ) * C (z - γ / 2))
    {α : ℝ} (hα₁ : 2 * η + γ < α) (hα₂ : α < Q γ)
    (hA : AnalyticAt ℂ (fun z => shiftCoeffA γ (γ / 2) z (b : ℂ) (c : ℂ)) ((α : ℂ) - γ / 2)) :
    (structureConstant P M γ μ α b c : ℂ) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) ((α : ℂ) - γ / 2) (b : ℂ) (c : ℂ) *
        (structureConstant P M γ μ (α - γ) b c : ℂ) := by
  let z₀ := (α : ℂ) - γ / 2
  let u (z : ℂ) := z + (γ : ℂ) / 2
  let v (z : ℂ) := z - (γ : ℂ) / 2
  let g (z : ℂ) := structureConstantH f₃ γ μ (tripleFirst (b : ℂ) (c : ℂ) z)
  have hu : u z₀ = (α : ℂ) := sub_add_cancel ..
  have hv : v z₀ = ((α - γ : ℝ) : ℂ) := by dsimp [v, z₀]; push_cast; ring
  obtain ⟨e₁, c₁, h₁⟩ := structureConstantH_comp_slice_data P M hγ hγ2 hμ hη hb hc hExt hh hCm hCv (u := u) (by dsimp [u]; fun_prop)
    (fun _ _ h => add_right_cancel h) hu (by linarith) hα₂
  obtain ⟨e₂, c₂, h₂⟩ := structureConstantH_comp_slice_data P M hγ hγ2 hμ hη hb hc hExt hh hCm hCv (u := v) (by dsimp [v]; fun_prop)
    (fun _ _ h => sub_left_inj.mp h) hv (by linarith) (by linarith)
  have hrel : ∀ᶠ z in 𝓝[≠] z₀, g (u z) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (b : ℂ) (c : ℂ) * g (v z) := by
    filter_upwards [(eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hCs) z₀, e₁, e₂]
      with z h p q
    calc g (u z) = C (u z) := p.symm
      _ = _ := h.trans (congrArg (fun a => _ * a) q)
  have := eq_of_eventuallyEq_nhdsNE_of_continuousAt hrel c₁
    ((continuousAt_const.mul hA.continuousAt).mul c₂)
  simpa only [g, h₁, h₂, z₀] using this

/-- **The reflected γ/2 shift at an exact real point** to the right of `Q`, from strip functions of
`DOZZ.structureConstant_reflected_shift_and_gluing` and a reference reflection germ `R`. -/
theorem reflectedShift_exact_of_strip {C Rs R : ℂ → ℂ} (hCm : MeromorphicOn C (horizontalStrip h))
    (hRsm : MeromorphicOn Rs (horizontalStrip h)) (hRm : MeromorphicOn R (horizontalStrip h))
    (hCv : RepresentsStructureConstant P M γ μ η b c C)
    (hRsR : ∀ α : ℝ, γ / 2 < α → α < Q γ → Rs (α : ℂ) = R (α : ℂ))
    (hrefl : ReflectedFirstShift γ μ b c C Rs)
    {α : ℝ} (hα₁ : Q γ < α) (hα₂ : α < Q γ + γ)
    (hR : AnalyticAt ℂ R (α : ℂ))
    (hA : AnalyticAt ℂ (fun z => shiftCoeffA γ (γ / 2) z (b : ℂ) (c : ℂ)) ((α : ℂ) - γ / 2)) :
    R α * (structureConstant P M γ μ (2 * Q γ - α) b c : ℂ) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) ((α : ℂ) - γ / 2) (b : ℂ) (c : ℂ) *
        (structureConstant P M γ μ (α - γ) b c : ℂ) := by
  let z₀ := (α : ℂ) - γ / 2
  let t (z : ℂ) := z + (γ : ℂ) / 2
  let u (z : ℂ) := 2 * (Q γ : ℂ) - γ / 2 - z
  let v (z : ℂ) := z - (γ : ℂ) / 2
  let g (z : ℂ) := structureConstantH f₃ γ μ (tripleFirst (b : ℂ) (c : ℂ) z)
  have ht : t z₀ = (α : ℂ) := sub_add_cancel ..
  have hu : u z₀ = ((2 * Q γ - α : ℝ) : ℂ) := by dsimp [u, z₀]; push_cast; ring
  have hv : v z₀ = ((α - γ : ℝ) : ℂ) := by dsimp [v, z₀]; push_cast; ring
  obtain ⟨e₁, c₁, h₁⟩ := structureConstantH_comp_slice_data P M hγ hγ2 hμ hη hb hc hExt hh hCm hCv (u := u) (by dsimp [u]; fun_prop)
    (fun _ _ h => sub_right_inj.mp h) hu (by linarith [hη.2]) (by linarith)
  obtain ⟨e₂, c₂, h₂⟩ := structureConstantH_comp_slice_data P M hγ hγ2 hμ hη hb hc hExt hh hCm hCv (u := v) (by dsimp [v]; fun_prop)
    (fun _ _ h => sub_left_inj.mp h) hv (by linarith [hη.2]) (by linarith)
  -- the two reflection germs agree on the strip
  have hRR : Rs =ᶠ[𝓝[≠] (α : ℂ)] R := by
    let x₀ : ℝ := (γ / 2 + Q γ) / 2
    have hx₀1 : γ / 2 < x₀ := by dsimp [x₀]; linarith
    have hx₀2 : x₀ < Q γ := by dsimp [x₀]; linarith
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] x₀, Rs t = R t :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_of_mem (Ioo_mem_nhds hx₀1 hx₀2)
        fun t ht => hRsR t ht.1 ht.2)
    exact ShiftGluing.meromorphicOn_eventuallyEq_of_frequently hRsm hRm
      (isPreconnected_horizontalStrip h)
      (by change |((x₀ : ℝ) : ℂ).im| < h; simpa using hh)
      (by change |((α : ℝ) : ℂ).im| < h; simpa using hh)
      ((tendsto_ofReal_nhdsNE_slice x₀).frequently hev.frequently)
  have e₀ : ∀ᶠ z in 𝓝[≠] z₀, Rs (t z) = R (t z) :=
    ShiftGluing.eventually_comp_add (z := z₀) (p := fun z => Rs z = R z)
      ((γ : ℂ) / 2) (by change ∀ᶠ z in 𝓝[≠] (t z₀), Rs z = R z; rwa [ht])
  have hrel : ∀ᶠ z in 𝓝[≠] z₀, R (t z) * g (u z) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (b : ℂ) (c : ℂ) * g (v z) := by
    filter_upwards [(eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hrefl) z₀, e₀, e₁, e₂]
      with z h p q r
    rw [← p]
    change C (u z) = g (u z) at q
    change C (v z) = g (v z) at r
    rw [← q, ← r]
    simpa only [u, v, t, sub_right_comm (2 * (Q γ : ℂ)) ((γ : ℂ) / 2) z] using h
  have hRc : ContinuousAt (fun z => R (t z)) z₀ :=
    hR.continuousAt.comp_of_eq (by dsimp [t]; fun_prop) ht
  have := eq_of_eventuallyEq_nhdsNE_of_continuousAt hrel (hRc.mul c₁)
    ((continuousAt_const.mul hA.continuousAt).mul c₂)
  simpa only [g, h₁, h₂, ht, z₀] using this

end

end DOZZ.Proofs

end
