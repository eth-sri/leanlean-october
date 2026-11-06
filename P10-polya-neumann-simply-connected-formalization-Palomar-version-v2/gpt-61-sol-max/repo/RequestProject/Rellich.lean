module

public import RequestProject.Finite

public import RequestProject.PlanarTypes

public import RequestProject.RellichCompact
public import RequestProject.LipschitzCover

/-!
# Rellich compactness and closedness of the weak gradient

* `rellich_compact`: the Rellich–Kondrachov compactness theorem for bounded Lipschitz domains
  (part of External theorem E2 of the paper), stated for sequences: a sequence bounded in
  `H¹(Ω)` has an `L²(Ω)`-convergent subsequence. It is proved from the cover of `Ω` by
  shiftable pieces (`lipschitz_cover`) and the Kolmogorov–Riesz argument `rellich_of_cover`.
* `isWeakGradient_of_tendsto`: weak gradients are closed under `L²` limits.
* `isWeakGradient_smul`: weak gradients are compatible with scalar multiplication.
* `tendsto_integral_mul`: `u ↦ ∫_Ω u ψ` is continuous on `L²(Ω)` for `ψ ∈ L²(Ω)`.
-/

public section

open MeasureTheory Filter Topology



namespace PolyaNeumann

section
variable {Ω : PlanarSet}
include Ω

/-- **External theorem E2 (Rellich–Kondrachov compactness)**: on a bounded Lipschitz domain,
every sequence bounded in `H¹(Ω)` has a subsequence converging in `L²(Ω)`. -/
theorem rellich_compact (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    u (g : ℕ → Coord → L2 Ω) (hg : ∀ n, IsWeakGradient Ω (u n) (g n)) C
    (hu : ∀ n, ‖u n‖ ≤ C) (hgC : ∀ n i, ‖g n i‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : L2 Ω, Tendsto (u ∘ φ) atTop (𝓝 v) := by
  obtain ⟨m, W, hWo, hWΩ, hcov, hsh⟩ := lipschitz_cover hb hL
  exact rellich_of_cover hL.1.1 hb W hWo hWΩ hcov hsh u g hg C hu hgC

/-- Integration against a fixed function whose conjugate is in `L²(Ω)` is continuous on
`L²(Ω)`. -/
lemma tendsto_integral_mul {ψ : PlaneMap}
    (hψ : MemLp (fun w => (starRingEnd ℂ) (ψ w)) 2 (volume.restrict Ω))
    {f : ℕ → L2 Ω}  (hf : Tendsto f atTop (𝓝 F)) :
    Tendsto (fun n => ∫ w in Ω, f n w * ψ w) atTop (𝓝 (∫ w in Ω, F w * ψ w)) := by
  change MemLp (star ψ) 2 (volume.restrict Ω) at hψ
  have h : MemLp ψ 2 (volume.restrict Ω) := by simpa only [star_star] using hψ.star
  simpa only [Function.comp_def, lpPair_apply] using ((lpPair h).continuous.tendsto F).comp hf


/-- Weak gradients pass to `L²` limits. -/
lemma isWeakGradient_of_tendsto  {g : ℕ → Coord → L2 Ω}
      (hg : ∀ n, IsWeakGradient Ω (u n) (g n))
    (hu : Tendsto u atTop (𝓝 U)) (hG : ∀ i, Tendsto (fun n => g n i) atTop (𝓝 (G i))) :
    IsWeakGradient Ω U G := by
  intro φ hφ i
  have h1 := ((lpPair (hφ.memLp_fderiv (coordDir i))).continuous.tendsto U).comp hu
  have h2 := (((lpPair hφ.memLp).continuous.tendsto (G i)).comp (hG i)).neg
  simp only [Function.comp_def, lpPair_apply] at h1 h2
  exact tendsto_nhds_unique h1 (h2.congr fun n => (hg n φ hφ i).symm)

/-- Weak gradients scale: if `∇u = g` then `∇(c u) = c g`. -/
lemma isWeakGradient_smul  
    (hg : IsWeakGradient Ω u g) (c : ℂ) : IsWeakGradient Ω (c • u) (c • g) := hg.smul c

end


end PolyaNeumann
