module
public import AnalyticESC.Development


@[expose] public section

/-!
# Proofs of the audited statements

Proofs of the theorems stated in `Challenge.lean`, for B. Bárány, I. Kolossváry and
S. Troscheit, *On exponential separation of analytic self-conformal sets on the real line*,
as stated in `../analytic.tex`. The shared vocabulary keeps the challenge definitions unchanged without importing
`Challenge.lean`. The results are proved from the `AnalyticESC` library. The lemmas below identify the neighbourhood, finite sums, guarded
quotients and restricted limits with the library's versions.
-/

namespace Challenge
open Set Metric
variable {N : ℕ}

/-- The system `(f_i)` as an IFS of the library. -/
def toIFS  (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i)) :
    AnalyticESC.IFS N ε := ⟨f, hε, hf⟩

/-- Theorem 1.4. The IFSs in `𝔖_N` that satisfy the strong exponential separation condition
contain a subset `U` of `𝔖_N` that is open and dense in `𝔖_N` for the `𝒞²` metric `d₂`. -/
alias audit_sesc_open_dense := AnalyticESC.theorem_1_4

/-- Theorem 1.5. Let `Φ = (f_i)_{i ∈ Fin N}` be an analytic IFS in `𝔖_N`. If
`sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > 0` for all distinct `i, j ∈ Σ ∪ Σ_*` with `|i| = |j|`, then `Φ`
satisfies the strong exponential separation condition. Words of equal length are either both
finite of the same length or both infinite. -/
theorem audit_sesc_of_dualProj (hε : 0 < ε) f (hf : ∀ i, InClass ε (f i)) hd
    (hfin :
      ∀ n,
        ∀ i j : Fin n → Fin N,
          i ≠ j → 0 < ⨆ x : I, ‖dualProjFin f hd (List.ofFn i) x - dualProjFin f hd (List.ofFn j) x‖)
    (hinf : ∀ i j : ℕ → Fin N, i ≠ j → 0 < ⨆ x : I, ‖dualProjInf f hd i x - dualProjInf f hd j x‖) : SESC f :=
  by
  by_cases hN : 0 < N
  · apply (toIFS hε f hf).theorem_2_2
    refine ⟨hN, fun i j hij => ?_⟩
    obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup (hinf i j fun hw => hij (congrFun hw 0))
    exact ⟨x, x.2, sub_ne_zero.mp (norm_pos_iff.mp hx)⟩
  · refine ⟨1, one_pos, fun n i j hij => ?_⟩
    grind

/-- Proposition 1.8. Let `Φ = (f_i)_{i ∈ Fin N}` be an analytic IFS in `𝔖_N` with `N ≥ 2` maps.
Suppose that there is `α > 0` such that for all `i ≠ j` there is `x ∈ [0,1]` with
`|f_i''/f_i'(x) - f_j''/f_j'(x)| ≥ α`. Then `β > 0`, and if `α > 2β c_max/(1 - c_max)`, then
`sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > 0` for all distinct `i, j ∈ Σ ∪ Σ_*` with `|i| = |j|`, and `Φ`
satisfies the strong exponential separation condition. The hypothesis `N ≥ 2` ensures `β > 0`,
which can fail for a singleton IFS. -/
theorem audit_example_criterion (hε : 0 < ε) f (hf : ∀ i, InClass ε (f i)) hd (hN : 2 ≤ N) {α} (hα : 0 < α) hc
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x : I, α ≤ ‖nonlin (f i) x (hd i [] x) - nonlin (f j) x (hd j [] x)‖) :
    0 < beta f hd ∧
      (divide (2 * beta f hd * cmax ε f) (1 - cmax ε f) hc < α →
        (∀ n,
            ∀ i j : Fin n → Fin N,
              i ≠ j → 0 < ⨆ x : I, ‖dualProjFin f hd (List.ofFn i) x - dualProjFin f hd (List.ofFn j) x‖) ∧
          (∀ i j : ℕ → Fin N, i ≠ j → 0 < ⨆ x : I, ‖dualProjInf f hd i x - dualProjInf f hd j x‖) ∧ SESC f) :=
  by
  obtain ⟨hβ, h⟩ := (toIFS hε f hf).proposition_1_8 hN hα fun i j hij => (hsep i j hij).elim fun x hx => ⟨x, x.2, hx⟩
  refine ⟨hβ, fun hα' => ?_⟩
  obtain ⟨hne, hS⟩ := h hα'
  refine ⟨fun n i j hij => ?_, fun i j hij => hne (.inf i) (.inf j) (fun h => hij (by cases h; rfl)) rfl, hS⟩
  have hfin :=
    hne (.fin (List.ofFn i)) (.fin (List.ofFn j)) (fun h => hij (List.ofFn_injective (AnalyticESC.Word.fin.inj h)))
      (by simp)
  convert hfin using 5 <;>
        simp [dualProjFin, toIFS, AnalyticESC.IFS.dualProj_fin_eq_sum, ← Fin.sum_univ_eq_sum_range,
          AnalyticESC.IFS.dualTerm, nonlin, AnalyticESC.IFS.nonlin] <;>
      congr! 2 <;>
    grind

/-- The polynomial example of Section 1.2.2: the system `x/8`, `x/8 + x²/32`, `x/16 + x²/32 + 29/32` lies in
`𝔖_3` for some `ε > 0` and satisfies the strong exponential separation condition. -/
alias audit_example_sesc := AnalyticESC.example_sesc

/-- Individual-map linearisation for Theorem 1.12: an analytic coordinate with nonvanishing
derivative conjugates the chosen map `f_i` to a contracting similarity. -/
theorem audit_conj_similarity (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i)) i :
    ∃ g,
      IsAnalyticCoord g ∧
        (∀ x ∈ I, deriv g x ≠ 0) ∧ ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, g (f i x).re = lam * g x + t :=
  by
  obtain ⟨g, hco, hd, hode⟩ := AnalyticESC.exists_real_ode_coord hε (hf i)
  exact ⟨g, hco, by grind, AnalyticESC.char_exists_conj_of_ode hε (hf i) hco.1 hode⟩

/-- Theorem 1.12 (a). If the attractor of `Φ` is not a singleton, then `Φ` is conjugated to a
self-similar IFS if and only if `H_i ≡ H_j` on `[0,1]` for all `i, j ∈ Σ`. -/
theorem audit_conj_iff  (hε : 0 < ε) f (hf : ∀ i, InClass ε (f i)) hd
    (hnd : ¬ ∃ x, attractor f = {x}) :
    ConjSelfSimilar (fun i x => (f i x).re) ↔
      ∀ i j : ℕ → Fin N, ∀ x : I, dualProjInf f hd i x = dualProjInf f hd j x := by
  convert Iff.intro ((toIFS hε f hf).dualProj_eq_of_conjSelfSimilar hnd)
    (toIFS hε f hf).conjSelfSimilar_of_dualProj_eq using 1 <;> simp_all <;> rfl

/-- Theorem 1.12 (b). If the attractor of `Φ` is not a singleton, then `Φ` is sub-conjugated to a
self-similar IFS, that is, `(f_i, f_j)` is conjugated to a self-similar IFS for some distinct
`i, j ∈ Σ_*` of the same length, if and only if `H_{(i)^∞} ≡ H_{(j)^∞}` on `[0,1]` for some distinct
`i, j ∈ Σ_*` of the same length. -/
theorem audit_subconj_iff  (hε : 0 < ε) f (hf : ∀ i, InClass ε (f i)) hd
    (hnd : ¬ ∃ x, attractor f = {x}) :
    (∃ (m : ℕ) (i j : Fin m → Fin N), i ≠ j ∧
      ConjSelfSimilar ![fun x : ℝ => (comp f (List.ofFn i) x).re,
        fun x : ℝ => (comp f (List.ofFn j) x).re]) ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        ∀ x : I, dualProjInf f hd (periodic hm i) x = dualProjInf f hd (periodic hm j) x := by
  convert (toIFS hε f hf).subConjSelfSimilar_iff using 1 <;> simp_all [Subtype.forall] <;> rfl

section
open MeasureTheory Filter Topology

/-- Theorem 1.6 (Rapaport), from Rapaport's Theorem 1.2 and Corollary 1.3. Let
`Φ = (f_i)_{i ∈ Fin N}`, `N ≥ 1`, be an analytic IFS in `𝔖_N` whose attractor is not a singleton.
If `Φ` satisfies the ESC, then there is equality in (1.6). -/
theorem audit_dim_of_esc (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) {ε }
    (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i))
    (hN : 0 < N) (hnd : ¬ ∃ x, attractor f = {x}) (hesc : ESC f) : DimEquality f := (toIFS hε f hf).theorem_1_6 hM hS hN hnd hesc

/-- Corollary 1.7, from Rapaport's Theorem 1.2 and Corollary 1.3. For `N ≥ 2`, the IFSs in `𝔖_N`
with equality in (1.6) contain a subset `U` of `𝔖_N` that is open and dense in `𝔖_N` for the `𝒞²`
metric `d₂`. Corollary 1.7 is stated for every `N`; its `N = 1` case is omitted here. -/
alias audit_dim_open_dense := AnalyticESC.corollary_1_7

/-- The polynomial example of Section 1.2.2, from Rapaport's Theorem 1.2 and Corollary 1.3:
`dim_H Λ = s(Φ) < 1`, where `s(Φ)` is the unique zero of the pressure, and `dim μ_p = H(p)/χ < 1` at
`μ_p`-almost every point, for every positive probability vector `p`, by Theorem 1.6. -/
alias audit_example_dim := AnalyticESC.example_dim

/-- The natural measure of the polynomial example in Section 1.2.2, from Bowen's theorem:
the pressure has a unique zero `s = s(Φ)`, the potential `s log|f'_{ω₀}(π(σω))|` has a Gibbs measure,
and for every such Gibbs measure `ν` the natural measure `μ = ν ∘ π⁻¹` has local dimension `s(Φ) - 1/3 < s(Φ)`
at `0`. -/
alias audit_example_localDim := AnalyticESC.example_localDim_of_bowen

/-- `L^q` dimensions of the polynomial example in Section 1.2.2, from Bowen's theorem:
for every Gibbs measure `ν` of the potential `s(Φ) log|f'_{ω₀}(π(σω))|` and every `q > 1`,
the natural measure `μ = ν ∘ π⁻¹` has `D_μ(q) ≤ q (s(Φ) - 1/3) / (q - 1)`, which is smaller than `s(Φ)` for `q > 3 s(Φ)`. -/
alias audit_example_lq := AnalyticESC.example_lq_of_bowen

end
end Challenge
