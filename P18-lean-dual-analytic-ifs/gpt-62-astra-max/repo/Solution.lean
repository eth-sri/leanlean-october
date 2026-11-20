module

public import Mathlib
public import AnalyticESC.Main.Example
public import AnalyticESC.Conjugation.PeriodicPoints
public import AnalyticESC.Generic.OpenDense
public import AnalyticESC.Dimension.NaturalMeasure
public import AnalyticESC.Dimension.OpenDense
public import AnalyticESC.Dimension.Example
public import AnalyticESC.Dimension.Lq

@[expose] public section

/-!
# Proofs of the audited statements

Proofs of the theorems stated in `Challenge.lean`, for B. Bárány, I. Kolossváry and
S. Troscheit, *On exponential separation of analytic self-conformal sets on the real line*,
as stated in `../analytic.tex`. This module repeats the challenge vocabulary with
the same names, types and values, without importing `Challenge.lean`, and proves each audited theorem from
the `AnalyticESC` library. The lemmas below identify the neighbourhood, finite sums, guarded
quotients and restricted limits with the library's versions.
-/

namespace Challenge
open Set Metric
variable {N : ℕ}

open AnalyticESC (IFS block pref pad Address)

lemma dualProjFin_eq_lib (Φ : IFS N) (hd : NonzeroDerivatives Φ.f) (w : Address N) (n : ℕ) (x : I) :
    dualProjFin Φ.f hd (block n w) x = Φ.dualProj n w x := by
  have h : (block n w).length = n := List.length_ofFn
  rw [dualProjFin,Φ.finite_sum,← Fin.sum_univ_eq_sum_range,← (finCongr h).sum_comp]
  apply Finset.sum_congr rfl; intro k _
  have t : (block n w).take k = block k w := List.ext_getElem (by simp [h]; omega) fun _ _ _ => by simp [block,pref]
  simp [t,AnalyticESC.IFS.dualTerm,block,pref,nonlin,AnalyticESC.IFS.comp,AnalyticESC.IFS.nonlin]

/-- Theorem 1.4. The IFSs in `𝔖_N` that satisfy the strong exponential separation condition
contain a subset `U` of `𝔖_N` that is open and dense in `𝔖_N` for the `𝒞²` metric `d₂`. -/
theorem audit_sesc_open_dense (N : ℕ) :
    ∃ U : Set (Fin N → ℂ → ℂ), (∀ f ∈ U, InUnionClass f ∧ SESC f) ∧
      (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2 f g < r → g ∈ U) ∧
      (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2 f g < r) := AnalyticESC.theorem_1_4 N

/-- The polynomial example of Section 1.2.2: the system `x/8`, `x/8 + x²/32`, `x/16 + x²/32 + 29/32` lies in
`𝔖_3` for some `ε > 0` and satisfies the strong exponential separation condition. -/
theorem audit_example_sesc : ∃ ε > 0, (∀ i, InClass ε (exampleMaps i)) ∧ SESC exampleMaps := ⟨_,AnalyticESC.exampleIFS.ε_pos,AnalyticESC.exampleIFS.inClass,AnalyticESC.exampleIFS_sesc⟩

section
variable {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i)) (hd : NonzeroDerivatives f)
include hε hf

/-- Theorem 1.5. Let `Φ = (f_i)_{i ∈ Fin N}` be an analytic IFS in `𝔖_N`. If
`sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > 0` for all distinct `i, j ∈ Σ ∪ Σ_*` with `|i| = |j|`, then `Φ`
satisfies the strong exponential separation condition. Words of equal length are either both
finite of the same length or both infinite. -/
theorem audit_sesc_of_dualProj
    (_hfin : ∀ n, ∀ i j : Fin n → Fin N, i ≠ j →
      0 < ⨆ x : I, ‖dualProjFin f hd (List.ofFn i) x -
        dualProjFin f hd (List.ofFn j) x‖)
    (hinf : ∀ i j : ℕ → Fin N, i ≠ j →
      0 < ⨆ x : I, ‖dualProjInf f hd i x - dualProjInf f hd j x‖) :
    SESC f := (⟨f,hε,hf⟩ : IFS N).theorem_1_5 hinf

/-- Proposition 1.8. Let `Φ = (f_i)_{i ∈ Fin N}` be an analytic IFS in `𝔖_N` with `N ≥ 2` maps.
Suppose that there is `α > 0` such that for all `i ≠ j` there is `x ∈ [0,1]` with
`|f_i''/f_i'(x) - f_j''/f_j'(x)| ≥ α`. Then `β > 0`, and if `α > 2β c_max/(1 - c_max)`, then
`sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > 0` for all distinct `i, j ∈ Σ ∪ Σ_*` with `|i| = |j|`, and `Φ`
satisfies the strong exponential separation condition. The hypothesis `N ≥ 2` ensures `β > 0`,
which can fail for a singleton IFS. -/
theorem audit_example_criterion (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α)
    (hc : 1 - cmax ε f ≠ 0)
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x : I, α ≤ ‖nonlin (f i) x (hd i [] x) - nonlin (f j) x (hd j [] x)‖) :
    0 < beta f hd ∧ (divide (2 * beta f hd * cmax ε f) (1 - cmax ε f) hc < α →
      (∀ n, ∀ i j : Fin n → Fin N, i ≠ j →
        0 < ⨆ x : I, ‖dualProjFin f hd (List.ofFn i) x -
          dualProjFin f hd (List.ofFn j) x‖) ∧
      (∀ i j : ℕ → Fin N, i ≠ j →
        0 < ⨆ x : I, ‖dualProjInf f hd i x - dualProjInf f hd j x‖) ∧
      SESC f) := by
  let Φ : IFS N := ⟨f,hε,hf⟩
  have sep : Φ.Spread α := hsep
  refine ⟨Φ.beta_pos_of_spread sep hα hN,fun H => ?_⟩
  have hi (v w : Address N) (h : v ≠ w) := Φ.infinite_criterion sep H h
  refine ⟨fun n i j hij => ?_,hi,Φ.theorem_1_5 hi⟩
  let addr (v : Fin n → Fin N) := pad (⟨0,by omega⟩ : Fin N) (List.ofFn v)
  have e (v : Fin n → Fin N) : block n (addr v) = List.ofFn v := by simpa [addr] using AnalyticESC.block_pad_length (⟨0,by omega⟩ : Fin N) (List.ofFn v)
  have he : block n (addr i) ≠ block n (addr j) := by simpa [e] using hij
  simpa only [AnalyticESC.dev,← dualProjFin_eq_lib Φ hd,e] using Φ.criterion sep H (AnalyticESC.diff_blocks he)

/-- Individual-map linearisation for Theorem 1.12: an analytic coordinate with nonvanishing
derivative conjugates the chosen map `f_i` to a contracting similarity. -/
theorem audit_conj_similarity (i : Fin N) :
    ∃ g, IsAnalyticCoord g ∧ (∀ x ∈ I, deriv g x ≠ 0) ∧
      ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, g (f i x).re = lam * g x + t := by
  let Φ : IFS N := ⟨f,hε,hf⟩
  obtain ⟨g,hr,h⟩ := Φ.coord_for fun _ => i
  exact ⟨g,hr.coord,hr.2,(Φ.linearizes_iff_match (by simp) (Φ.head_rec fun _ => i) hr).mpr h⟩

/-- Theorem 1.12 (a). If the attractor of `Φ` is not a singleton, then `Φ` is conjugated to a
self-similar IFS if and only if `H_i ≡ H_j` on `[0,1]` for all `i, j ∈ Σ`. -/
theorem audit_conj_iff
    (hnd : ¬ ∃ x, attractor f = {x}) :
    ConjSelfSimilar (fun i (x : ℝ) => (f i x).re) ↔
      ∀ i j : ℕ → Fin N, ∀ x : I, dualProjInf f hd i x = dualProjInf f hd j x := (⟨f,hε,hf⟩ : IFS N).conjSelfSimilar_iff hnd

/-- Theorem 1.12 (b). If the attractor of `Φ` is not a singleton, then `Φ` is sub-conjugated to a
self-similar IFS, that is, `(f_i, f_j)` is conjugated to a self-similar IFS for some distinct
`i, j ∈ Σ_*` of the same length, if and only if `H_{(i)^∞} ≡ H_{(j)^∞}` on `[0,1]` for some distinct
`i, j ∈ Σ_*` of the same length. -/
theorem audit_subconj_iff
    (_hnd : ¬ ∃ x, attractor f = {x}) :
    (∃ (m : ℕ) (i j : Fin m → Fin N), i ≠ j ∧
      ConjSelfSimilar ![fun x : ℝ => (comp f (List.ofFn i) x).re,
        fun x : ℝ => (comp f (List.ofFn j) x).re]) ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        ∀ x : I, dualProjInf f hd (periodic hm i) x = dualProjInf f hd (periodic hm j) x := (⟨f,hε,hf⟩ : IFS N).subConjSelfSimilar_iff

end

section DimensionProofs

open MeasureTheory Filter Topology

/-- Theorem 1.6 (Rapaport), from Rapaport's Theorem 1.2 and Corollary 1.3. Let
`Φ = (f_i)_{i ∈ Fin N}`, `N ≥ 1`, be an analytic IFS in `𝔖_N` whose attractor is not a singleton.
If `Φ` satisfies the ESC, then there is equality in (1.6). -/
theorem audit_dim_of_esc (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) {ε : ℝ}
    (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i))
    (hN : 0 < N) (hnd : ¬ ∃ x, attractor f = {x}) (hesc : ESC f) : DimEquality f := (⟨f,hε,hf⟩ : AnalyticESC.IFS N).theorem_1_6 hM hS hN hnd hesc

/-- Corollary 1.7, from Rapaport's Theorem 1.2 and Corollary 1.3. For `N ≥ 2`, the IFSs in `𝔖_N`
with equality in (1.6) contain a subset `U` of `𝔖_N` that is open and dense in `𝔖_N` for the `𝒞²`
metric `d₂`. Corollary 1.7 is stated for every `N`; its `N = 1` case is omitted here. -/
theorem audit_dim_open_dense (hM : RapaportMeasureStatement) (hS : RapaportSetStatement)
    (hN : 2 ≤ N) :
    ∃ U : Set (Fin N → ℂ → ℂ), (∀ f ∈ U, InUnionClass f ∧ DimEquality f) ∧
      (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2 f g < r → g ∈ U) ∧
      (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2 f g < r) := AnalyticESC.corollary_1_7 hM hS hN

/-- The polynomial example of Section 1.2.2, from Rapaport's Theorem 1.2 and Corollary 1.3:
`dim_H Λ = s(Φ) < 1`, where `s(Φ)` is the unique zero of the pressure, and `dim μ_p = H(p)/χ < 1` at
`μ_p`-almost every point, for every positive probability vector `p`, by Theorem 1.6. -/
theorem audit_example_dim (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (pressureRatio exampleMaps t) atTop (𝓝 0) ↔
        t = s) ∧
      s < 1 ∧ dimH (attractor exampleMaps) = ENNReal.ofReal s ∧
      ∀ p : Fin 3 → ℝ, IsProbVec p → ∀ μ : Measure ℝ, IsSelfConformal exampleMaps p μ →
        ∀ hχ : lyapunov exampleMaps p μ ≠ 0,
        entropy p < lyapunov exampleMaps p μ ∧
        ∀ᵐ x ∂μ, Tendsto (fun r : Scale => logRatio (μ.real (closedBall x r)) r) scaleZero
          (𝓝 (divide (entropy p) (lyapunov exampleMaps p μ) hχ)) := AnalyticESC.example_dim hM hS

/-- The natural measure of the polynomial example in Section 1.2.2, from Bowen's theorem:
the pressure has a unique zero `s = s(Φ)`, the potential `s log|f'_{ω₀}(π(σω))|` has a Gibbs measure,
and for every such Gibbs measure `ν` the natural measure `μ = ν ∘ π⁻¹` has local dimension `s(Φ) - 1/3 < s(Φ)`
at `0`. -/
theorem audit_example_localDim (hB : BowenGibbsStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (pressureRatio exampleMaps t) atTop (𝓝 0) ↔
        t = s) ∧
      (∃ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν ∧
        IsGibbsMeasure (potential exampleMaps s) ν) ∧
      ∀ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν →
        IsGibbsMeasure (potential exampleMaps s) ν →
        Tendsto (fun r : Scale => logRatio ((ν.map (natProj exampleMaps)).real (closedBall 0 r)) r)
          scaleZero (𝓝 (s - 1 / 3)) := by
  obtain ⟨s,hs,g,H⟩ := AnalyticESC.example_gibbs hB
  refine ⟨s,hs,g,fun ν hν hv => (AnalyticESC.edge_mass (H ν hν hv) (S := closedBall 0) (fun _ => measurableSet_closedBall) ?_ ?_).2⟩
  · intro r x hx; simpa [abs_of_nonneg hx.1] using hx.2.le
  · intro r x hx; exact (le_abs_self x).trans (by simpa [Real.dist_eq] using hx)

/-- `L^q` dimensions of the polynomial example in Section 1.2.2, from Bowen's theorem:
for every Gibbs measure `ν` of the potential `s(Φ) log|f'_{ω₀}(π(σω))|` and every `q > 1`,
the natural measure `μ = ν ∘ π⁻¹` has `D_μ(q) ≤ q (s(Φ) - 1/3) / (q - 1)`, which is smaller than `s(Φ)` for `q > 3 s(Φ)`. -/
theorem audit_example_lq (hB : BowenGibbsStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (pressureRatio exampleMaps t) atTop (𝓝 0) ↔
        t = s) ∧
      ∀ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν →
        IsGibbsMeasure (potential exampleMaps s) ν → ∀ q > 1, ∀ hq : q - 1 ≠ 0,
        lqDim (ν.map (natProj exampleMaps)) q hq ≤ divide q (q - 1) hq * (s - 1 / 3) ∧
        (3 * s < q → lqDim (ν.map (natProj exampleMaps)) q hq < s) := by
  obtain ⟨s,hs,_,H⟩ := AnalyticESC.example_gibbs hB
  exact ⟨s,hs,fun ν hν hv _ hq => AnalyticESC.example_lq (H ν hν hv) hq⟩

end DimensionProofs

end Challenge
