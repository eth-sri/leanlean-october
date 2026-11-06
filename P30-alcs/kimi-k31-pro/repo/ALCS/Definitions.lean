module

public import ALCS.Background.Semigroup
public import ALCS.Background.Lp

@[expose] public section

/-!
# Abstract linear control systems (Section 1 and § 2.1 of the paper)

* `ALCS 𝕜 X U p` : **Definition 1.1**, an abstract linear control system `(𝕋, Φ)`.
* `ALCS.IsZeroClass` : **Definition 1.4**, zero-class systems.
* `ALCS.Phi_zero` : `Φ_0 = 0` (§ 1.2).
* `ALCS.norm_Phi_mono` : equation `eq:Phi-monotone`, `κ(t) ≤ κ(t + τ)`,
  where `κ(t) = ‖Φ t‖`.
* `ALCS.causality`, `ALCS.delay`, `ALCS.free` : **Lemma 2.1** (`lem:Phi-properties`),
  equations `eq:causality`, `eq:delay`, `eq:free`.

## Formalization choices

* Scalars: any nontrivially normed field `𝕜` here; the main theorem uses `ℝ` or `ℂ`
  (`RCLike 𝕜`). Completeness of `X` and `U` is assumed only where it is used.
* `L^p(ℝ₊; U)` is `Lp U p muPlus` (see `ALCS/Background/Lp.lean`).
* Like the semigroup `T`, the input maps form a function `Φ : ℝ → (L^p →L X)`;
  only nonnegative times play a role in the axioms and in the results.
* Instead of constructing `u ⋄_τ v` as an element of `L^p`, the composition property
  is required for every `w ∈ L^p` whose representative is a.e. equal to
  `concat τ ⇑u ⇑v`. Since `u ⋄_τ v` does belong to `L^p` and a.e. classes are unique,
  this is exactly the identity of the paper.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]

/-- **Definition 1.1** (abstract linear control system).
An abstract linear control system with state space `X`, input space `U` and exponent
`p ∈ [1, ∞]` is a strongly continuous semigroup `T` on `X` (the parent structure
`C0Semigroup`) together with bounded linear input maps `Φ t : L^p(ℝ₊; U) → X`
satisfying the composition property `eq:composition`. -/
structure ALCS (𝕜 : Type*) (X : Type*) (U : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] extends C0Semigroup 𝕜 X where
  /-- the input maps `Φ t : L^p(ℝ₊; U) → X` -/
  Φ : ℝ → Lp U p muPlus →L[𝕜] X
  /-- composition property `eq:composition`: `Φ (τ + t) (u ⋄_τ v) = T t (Φ τ u) + Φ t v`,
  where `w` is any input representing `u ⋄_τ v` -/
  composition : ∀ τ t : ℝ, 0 ≤ τ → 0 ≤ t → ∀ u v w : Lp U p muPlus,
    (⇑w =ᵐ[muPlus] concat τ ⇑u ⇑v) → Φ (τ + t) w = T t (Φ τ u) + Φ t v

namespace ALCS

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (S : ALCS 𝕜 X U p)

/-- **Definition 1.4** (zero-class system): `κ(t) = ‖Φ t‖ → 0` as `t → 0⁺`
(equation `eq:kappa-0`). -/
def IsZeroClass : Prop :=
  Tendsto (fun t => ‖S.Φ t‖) (𝓝[≥] 0) (𝓝 0)

/-! ## Elementary consequences of the composition property (§ 1.2 and Lemma 2.1) -/

/-- `Φ 0 = 0` (§ 1.2): composition with `τ = t = 0` and `u = v`, since `u ⋄_0 u = u`. -/
theorem Phi_zero : S.Φ 0 = 0 := by
  refine ContinuousLinearMap.ext fun u => ?_
  have h := S.composition 0 0 le_rfl le_rfl u u u (.of_forall fun s => by simp [concat])
  simpa [S.T_zero] using h

/-- **Lemma 2.1** (`lem:Phi-properties`), causality `eq:causality`. -/
theorem causality (τ : ℝ) (hτ : 0 ≤ τ) (u v w : Lp U p muPlus)
    (hw : ⇑w =ᵐ[muPlus] concat τ ⇑u ⇑v) :
    S.Φ τ w = S.Φ τ u := by
  simpa [S.T_zero, S.Phi_zero] using S.composition τ 0 hτ le_rfl u v w hw

/-- **Lemma 2.1** (`lem:Phi-properties`), delay `eq:delay`. -/
theorem delay (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (v w : Lp U p muPlus)
    (hw : ⇑w =ᵐ[muPlus] concat s ⇑(0 : Lp U p muPlus) ⇑v) :
    S.Φ (s + t) w = S.Φ t v := by
  simpa using S.composition s t hs ht 0 v w hw

/-- **Lemma 2.1** (`lem:Phi-properties`), free evolution `eq:free`. -/
theorem free (τ t : ℝ) (hτ : 0 ≤ τ) (ht : 0 ≤ t) (u w : Lp U p muPlus)
    (hw : ⇑w =ᵐ[muPlus] concat τ ⇑u ⇑(0 : Lp U p muPlus)) :
    S.Φ (τ + t) w = S.T t (S.Φ τ u) := by
  simpa using S.composition τ t hτ ht u 0 w hw

/-- Monotonicity of `κ(t) = ‖Φ t‖`, equation `eq:Phi-monotone`. -/
theorem norm_Phi_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : ‖S.Φ s‖ ≤ ‖S.Φ t‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  obtain ⟨w, hw, hcat⟩ := exists_delay (t - s) u
  rw [← S.delay (t - s) s (sub_nonneg.2 hst) hs u w hcat, sub_add_cancel]
  exact (S.Φ t).le_opNorm_of_le hw

end ALCS
