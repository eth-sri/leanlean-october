module

public import RequestProject.Defs

/-!
# Smooth domains

`IsSmoothDomain Ω`: a domain whose boundary is locally the graph of a `C^∞` function (with the
domain on one side); such domains are Lipschitz domains (`IsSmoothDomain.isLipschitzDomain`).
-/

@[expose] public section

open scoped Real ComplexConjugate
open MeasureTheory Filter Topology

noncomputable section

namespace PolyaNeumann

/-- A domain with rotated graph charts of the given regularity. -/
def IsGraphDomain (P : (ℝ → ℝ) → Prop) (Ω : Set ℂ) : Prop :=
  IsDomain Ω ∧
  ∀ p ∈ frontier Ω, ∃ (c : ℂ) (r h : ℝ) (K : NNReal) (f : ℝ → ℝ),
    ‖c‖ = 1 ∧ 0 < r ∧ 0 < h ∧ P f ∧ LipschitzWith K f ∧ f 0 = 0 ∧
    (∀ x : ℝ, |x| < r → |f x| < h) ∧
    ∀ w : ℂ, |(c * (w - p)).re| < r → |(c * (w - p)).im| < h →
      (w ∈ Ω ↔ f (c * (w - p)).re < (c * (w - p)).im)

/-- A smooth domain: a domain whose boundary is locally, after a rigid change of
coordinates, the graph of a `C^∞` function (which, after shrinking the chart, may be taken
to be globally Lipschitz), with the domain on one side. -/
abbrev IsSmoothDomain := IsGraphDomain (ContDiff ℝ (⊤ : ℕ∞))

/-- A smooth domain with a locally real-analytic graph at each boundary point. -/
abbrev IsAnalyticDomain := IsGraphDomain (fun f => ContDiff ℝ (⊤ : ℕ∞) f ∧ AnalyticAt ℝ f 0)

lemma IsAnalyticDomain.isSmoothDomain {Ω : Set ℂ} (h : IsAnalyticDomain Ω) : IsSmoothDomain Ω := by
  refine ⟨h.1, fun p hp => ?_⟩
  obtain ⟨c, r, k, K, f, hc, hr, hk, hf, hLip, h0, hb, hΩ⟩ := h.2 p hp
  exact ⟨c, r, k, K, f, hc, hr, hk, hf.1, hLip, h0, hb, hΩ⟩

lemma IsSmoothDomain.isLipschitzDomain {Ω : Set ℂ} (h : IsSmoothDomain Ω) :
    IsLipschitzDomain Ω := by
  refine ⟨h.1, fun p hp => ?_⟩
  obtain ⟨c, r, k, K, f, hc, hr, hk, -, hf, h0, hb, hΩ⟩ := h.2 p hp
  exact ⟨c, r, k, K, f, hc, hr, hk, hf, h0, hb, hΩ⟩

lemma IsAnalyticDomain.isLipschitzDomain {Ω : Set ℂ} (h : IsAnalyticDomain Ω) : IsLipschitzDomain Ω :=
  h.isSmoothDomain.isLipschitzDomain

end PolyaNeumann

end
