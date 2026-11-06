module

public import ALCS.Background.Semigroup
public import ALCS.Background.Lp

@[expose] public section

/-!
# Abstract linear control systems with `L^∞` inputs (Definition 1.1)

* `ALCS 𝕜 X U` : **Definition 1.1**, an abstract linear control system `(𝕋, Φ)`:
  a strongly continuous semigroup `T` on `X` (the parent structure `C0Semigroup`)
  together with bounded linear input maps `Φ t : L^∞(ℝ₊; U) → X` satisfying the
  composition property `eq:composition`.
* `ALCS.IsZeroClass` : **Definition 1.4**, zero-class systems.
* `ALCS.Phi_zero` : `Φ_0 = 0` (§ 1.2).
* `ALCS.norm_Phi_mono` : equation `eq:Phi-monotone`, `κ(t) ≤ κ(t + τ)`,
  where `κ(t) = ‖Φ t‖`.
* `ALCS.delay` : **Lemma 2.1** (`lem:Phi-properties`), the delay property.

Instead of constructing `u ⋄_τ v` as an element of `L^∞`, the composition property
is required for every `w` whose representative is a.e. equal to `concat τ ⇑u ⇑v`;
since `u ⋄_τ v` does belong to `L^∞` and a.e. classes are unique, this is exactly the
identity of the paper. Only `p = ∞` is needed below; the general-`p` theory is not used.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]

/-- **Definition 1.1** (abstract linear control system with inputs in `L^∞(ℝ₊; U)`). -/
structure ALCS (𝕜 : Type*) (X : Type*) (U : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U] extends C0Semigroup 𝕜 X where
  /-- the input maps `Φ t : L^∞(ℝ₊; U) → X` -/
  Φ : ℝ → Lp U ∞ muPlus →L[𝕜] X
  /-- composition property: `Φ (τ + t) (u ⋄_τ v) = T t (Φ τ u) + Φ t v`,
  where `w` is any input representing `u ⋄_τ v` -/
  composition : ∀ τ t : ℝ, 0 ≤ τ → 0 ≤ t → ∀ u v w : Lp U ∞ muPlus,
    (⇑w =ᵐ[muPlus] concat τ ⇑u ⇑v) → Φ (τ + t) w = T t (Φ τ u) + Φ t v

namespace ALCS

variable (S : ALCS 𝕜 X U)

/-- **Definition 1.4** (zero-class system): `κ(t) = ‖Φ t‖ → 0` as `t → 0⁺`. -/
def IsZeroClass : Prop :=
  Tendsto (fun t => ‖S.Φ t‖) (𝓝[≥] 0) (𝓝 0)

/-! ## Elementary consequences of the composition property -/

/-- `Φ 0 = 0`: composition with `τ = t = 0` and `u = v`, since `u ⋄_0 u = u`. -/
theorem Phi_zero : S.Φ 0 = 0 := by
  refine ContinuousLinearMap.ext (fun u => ?_)
  have hw : ⇑u =ᵐ[muPlus] concat 0 ⇑u ⇑u :=
    Filter.Eventually.of_forall (fun s => by simp [concat])
  have h := S.composition 0 0 le_rfl le_rfl u u u hw
  simpa [S.T_zero] using h

/-- **Lemma 2.1**, delay: `Φ (s + t) (0 ⋄_s v) = Φ t v`, i.e. an initial period of zero
input has no effect. (Composition with `u = 0`.) -/
theorem delay (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (v w : Lp U ∞ muPlus)
    (hw : ⇑w =ᵐ[muPlus] concat s ⇑(0 : Lp U ∞ muPlus) ⇑v) :
    S.Φ (s + t) w = S.Φ t v := by
  have h := S.composition s t hs ht 0 v w hw
  simpa using h

/-- Monotonicity of `κ(t) = ‖Φ t‖`: `‖Φ s‖ ≤ ‖Φ t‖` for `0 ≤ s ≤ t`.
Indeed `Φ s u = Φ t (0 ⋄_{t-s} u)` by `delay`. -/
theorem norm_Phi_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : ‖S.Φ s‖ ≤ ‖S.Φ t‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  obtain ⟨w, hw, hcat⟩ := exists_delay (t - s) u
  have heq : S.Φ t w = S.Φ s u := by
    have h := S.delay (t - s) s (sub_nonneg.2 hst) hs u w hcat
    rwa [sub_add_cancel] at h
  calc ‖S.Φ s u‖ = ‖S.Φ t w‖ := by rw [heq]
    _ ≤ ‖S.Φ t‖ * ‖w‖ := (S.Φ t).le_opNorm w
    _ ≤ ‖S.Φ t‖ * ‖u‖ := by gcongr

end ALCS
