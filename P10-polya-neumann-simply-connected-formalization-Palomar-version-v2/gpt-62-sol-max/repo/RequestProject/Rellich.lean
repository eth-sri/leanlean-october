module

public import RequestProject.RellichCompact
public import RequestProject.LipschitzCover
public import RequestProject.Finite

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

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace PolyaNeumann

/-- **External theorem E2 (Rellich–Kondrachov compactness)**: on a bounded Lipschitz domain,
every sequence bounded in `H¹(Ω)` has a subsequence converging in `L²(Ω)`. -/
theorem rellich_compact {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (u : ℕ → L2 Ω) (g : ℕ → Fin 2 → L2 Ω) (hg : ∀ n, IsWeakGradient Ω (u n) (g n)) (C : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ C) (hgC : ∀ n i, ‖g n i‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : L2 Ω, Tendsto (u ∘ φ) atTop (𝓝 v) := by
  obtain ⟨m, W, hWo, hWΩ, hcov, hsh⟩ := lipschitz_cover hb hL
  exact rellich_of_cover hL.1.1 hb W hWo hWΩ hcov hsh u g hg C hu hgC

/-- Strong convergence of values and weak convergence of gradients suffice if each test
identity holds eventually. -/
lemma isWeakGradient_of_eventually_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {Ω : Set ℂ} {u : ι → L2 Ω} {g : ι → Fin 2 → L2 Ω} {U : L2 Ω} {G : Fin 2 → L2 Ω}
    (hg : ∀ φ, TestFunction Ω φ → ∀ i, ∀ᶠ n in l,
      ∫ w in Ω, u n w * fderiv ℝ φ w (coordDir i) = - ∫ w in Ω, g n i w * φ w)
    (hu : Tendsto u l (𝓝 U))
    (hG : ∀ i z, Tendsto (fun n => inner ℂ z (g n i)) l (𝓝 (inner ℂ z (G i)))) :
    IsWeakGradient Ω U G := by
  apply isWeakGradient_iff_pair.mpr
  intro φ hφ i
  have h := (((lpIntegralPair (hφ.memLp_fderiv (coordDir i))).continuous.tendsto U).comp hu)
  have h' := (hG i (hφ.memLp.star.toLp (star φ))).neg
  refine tendsto_nhds_unique h (h'.congr' ?_)
  filter_upwards [hg φ hφ i] with n hn
  change -lpIntegralPair hφ.memLp (g n i) = lpIntegralPair (hφ.memLp_fderiv (coordDir i)) (u n)
  simpa only [lpIntegralPair_apply] using hn.symm

/-- Weak gradients pass to `L²` limits. -/
lemma isWeakGradient_of_tendsto {Ω : Set ℂ} {u : ℕ → L2 Ω} {g : ℕ → Fin 2 → L2 Ω}
    {U : L2 Ω} {G : Fin 2 → L2 Ω} (hg : ∀ n, IsWeakGradient Ω (u n) (g n))
    (hu : Tendsto u atTop (𝓝 U)) (hG : ∀ i, Tendsto (fun n => g n i) atTop (𝓝 (G i))) :
    IsWeakGradient Ω U G :=
  isWeakGradient_of_eventually_tendsto (fun φ hφ i => .of_forall fun n => hg n φ hφ i) hu
    (fun i z => ((innerSL ℂ z).continuous.tendsto _).comp (hG i))

end PolyaNeumann

end
