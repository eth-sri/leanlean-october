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
as stated in `../analytic.tex`.
-/

namespace Challenge

open Set Metric

/-- The open `δ`-neighbourhood `B_δ = {z ∈ ℂ : ∃ x ∈ I, |z - x| < δ}` of `I` in `ℂ`. -/
def nbhd (δ : ℝ) : Set ℂ := {z | ∃ x ∈ I, ‖z - (x : ℂ)‖ < δ}

/-- The class `S^ω_ε(I)` of Section 1.1, for a map given by its holomorphic extension:
(A) `f` is complex analytic on `B_{2ε}` and real at the real points of `B_{2ε}`;
(B) `f(I) ⊆ I` and `f(cl B_ε) ⊆ B_ε`; (C) `0 < |f'(z)| < 1` for `z ∈ cl B_ε`. -/
structure InClass (ε : ℝ) (f : ℂ → ℂ) : Prop where
  differentiableOn : DifferentiableOn ℂ f (nbhd (2 * ε))
  im_eq_zero : ∀ x : ℝ, (x : ℂ) ∈ nbhd (2 * ε) → (f x).im = 0
  re_mem_I : ∀ x ∈ I, (f x).re ∈ I
  mapsTo : ∀ z ∈ closure (nbhd ε), f z ∈ nbhd ε
  deriv_ne_zero : ∀ z ∈ closure (nbhd ε), deriv f z ≠ 0
  norm_deriv_lt_one : ∀ z ∈ closure (nbhd ε), ‖deriv f z‖ < 1

variable {N : ℕ}

/-- Nonvanishing of the derivatives at every finite orbit of a point of `I`. -/
def NonzeroDerivatives (f : Fin N → ℂ → ℂ) : Prop :=
  ∀ (i : Fin N) (w : List (Fin N)) (x : I), deriv (f i) (comp f w x) ≠ 0

/-- The distortion `f''/f'`. -/
noncomputable def nonlin (g : ℂ → ℂ) (z : ℂ) (_h : deriv g z ≠ 0) : ℂ :=
  deriv (deriv g) z / deriv g z

/-- The dual natural projection `H_w` of (1.4) for a finite word `w`. -/
noncomputable def dualProjFin (f : Fin N → ℂ → ℂ) (hd : NonzeroDerivatives f)
    (w : List (Fin N)) (x : I) : ℂ :=
  ∑ n : Fin w.length,
    nonlin (f (w.get n)) (comp f (w.take n).reverse x) (hd (w.get n) (w.take n).reverse x) *
      deriv (comp f (w.take n).reverse) x

/-- The dual natural projection `H_w` of (1.4) for an infinite word `w`. -/
noncomputable def dualProjInf (f : Fin N → ℂ → ℂ) (hd : NonzeroDerivatives f)
    (w : ℕ → Fin N) (x : I) : ℂ :=
  ∑' n, nonlin (f (w n)) (comp f (List.ofFn fun k : Fin n => w k).reverse x)
    (hd (w n) (List.ofFn fun k : Fin n => w k).reverse x) *
      deriv (comp f (List.ofFn fun k : Fin n => w k).reverse) x

/-- The constant `c_max` of (1.7): the supremum of `|f_i'|` over `cl B_ε` and `i`. -/
noncomputable def cmax (ε : ℝ) (f : Fin N → ℂ → ℂ) : ℝ :=
  ⨆ (i : Fin N) (z : closure (nbhd ε)), ‖deriv (f i) z‖

/-- `β = sup_{x ∈ [0,1], i} |f_i''/f_i'(x)|` (Proposition 1.8). -/
noncomputable def beta (f : Fin N → ℂ → ℂ) (hd : NonzeroDerivatives f) : ℝ :=
  ⨆ (x : I) (i : Fin N), ‖nonlin (f i) x (hd i [] x)‖

/-- The space `𝔖_N` of Section 1.1: IFSs whose maps lie in `S^ω_ε(I)` for some `ε > 0`, which may
depend on the system. -/
def InUnionClass (f : Fin N → ℂ → ℂ) : Prop := ∃ ε > 0, ∀ i, InClass ε (f i)

section Dimension

open MeasureTheory Filter Topology

/-- Equality in (1.6). -/
def DimEquality (f : Fin N → ℂ → ℂ) : Prop :=
  (∃ s : ℝ, (∀ t, Tendsto (pressureRatio f t) atTop (𝓝 0) ↔ t = s) ∧
      dimH (attractor f) = ENNReal.ofReal (min 1 s)) ∧
    ∀ p : Fin N → ℝ, IsProbVec p → ∀ μ : Measure ℝ, IsSelfConformal f p μ →
      ∀ hχ : lyapunov f p μ ≠ 0,
      ∀ᵐ x ∂μ, Tendsto (fun r : Scale => logRatio (μ.real (closedBall x r)) r) scaleZero
        (𝓝 (min 1 (divide (entropy p) (lyapunov f p μ) hχ)))

/-- The `L^q` dimension `D_μ(q) = τ_μ(q)/(q - 1)` of Section 1.2.2. -/
noncomputable def lqDim (μ : Measure ℝ) (q : ℝ) (hq : q - 1 ≠ 0) : ℝ :=
  divide (liminf (fun r : Scale =>
    logRatio (∑' k : ℤ, μ.real (Ico (k * (r : ℝ)) ((k + 1) * (r : ℝ))) ^ q) r)
    scaleZero) (q - 1) hq

end Dimension

theorem nbhd_eq_lib (δ : ℝ) : nbhd δ = AnalyticESC.nbhd δ := by
  ext z
  simp [nbhd, AnalyticESC.nbhd, mem_thickening_iff, dist_eq_norm]

theorem inClass_iff_lib {ε : ℝ} {f : ℂ → ℂ} :
    InClass ε f ↔ AnalyticESC.InClass ε f := by
  constructor <;> rintro ⟨h1, h2, h3, h4, h5, h6⟩ <;> constructor <;>
    (try simp only [nbhd_eq_lib] at *) <;> assumption

theorem dualProjFin_eq_lib {ε : ℝ} (Φ : AnalyticESC.IFS N ε) (hd : NonzeroDerivatives Φ.f)
    (w : List (Fin N)) (x : I) : dualProjFin Φ.f hd w x = Φ.dualProj (.fin w) x := by
  rw [dualProjFin, Φ.dualProj_fin_eq_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _
  simp [AnalyticESC.IFS.dualTerm, AnalyticESC.Word.get?, AnalyticESC.Word.take, n.isLt,
    nonlin, comp, AnalyticESC.IFS.nonlin, AnalyticESC.IFS.comp]

/-- The system `(f_i)` as an IFS of the library. -/
noncomputable abbrev toIFS {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i)) :
    AnalyticESC.IFS N ε where
  f := f
  ε_pos := hε
  inClass i := inClass_iff_lib.mp (hf i)

/-- Theorem 1.4. -/
theorem audit_sesc_open_dense (N : ℕ) :
    ∃ U : Set (Fin N → ℂ → ℂ), (∀ f ∈ U, InUnionClass f ∧ SESC f) ∧
      (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2 f g < r → g ∈ U) ∧
      (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2 f g < r) := by
  have hlib : ∀ f : Fin N → ℂ → ℂ, InUnionClass f → AnalyticESC.InUnionClass f :=
    fun f ⟨ε, hε, hf⟩ => ⟨ε, hε, fun i => inClass_iff_lib.mp (hf i)⟩
  obtain ⟨U, hS, hO, hD⟩ := AnalyticESC.theorem_1_4 N
  refine ⟨U, fun f hf => ?_, fun f hf => ?_, fun f hf r hr => hD f (hlib f hf) r hr⟩
  · obtain ⟨ε, ⟨g, hε, hg⟩, rfl, hSE⟩ := hS f hf
    exact ⟨⟨ε, hε, fun i => inClass_iff_lib.mpr (hg i)⟩, hSE⟩
  · obtain ⟨r, hr, h⟩ := hO f hf
    exact ⟨r, hr, fun g hg hd => h g (hlib g hg) hd⟩

/-- Theorem 1.5. -/
theorem audit_sesc_of_dualProj {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) (hd : NonzeroDerivatives f)
    (hfin : ∀ n, ∀ i j : Fin n → Fin N, i ≠ j →
      0 < ⨆ x : I, ‖dualProjFin f hd (List.ofFn i) x -
        dualProjFin f hd (List.ofFn j) x‖)
    (hinf : ∀ i j : ℕ → Fin N, i ≠ j →
      0 < ⨆ x : I, ‖dualProjInf f hd i x - dualProjInf f hd j x‖) :
    SESC f := by
  refine (toIFS hε f hf).theorem_1_5 ?_
  rintro (u | w) (v | w') hij hlen
  · have hl : u.length = v.length := Nat.cast_inj.1 hlen
    have hv : List.ofFn (fun k : Fin u.length => v.get (Fin.cast hl k)) = v :=
      List.ext_get (by simp [hl]) fun _ _ _ => by simp
    have h := hfin u.length u.get (fun k => v.get (Fin.cast hl k)) fun h =>
      hij (congrArg _ (List.ext_get hl fun k hk _ => congrFun h ⟨k, hk⟩))
    simp only [← dualProjFin_eq_lib (toIFS hε f hf) hd]
    rwa [List.ofFn_get, hv] at h
  · exact absurd hlen (by simp [AnalyticESC.Word.length])
  · exact absurd hlen (by simp [AnalyticESC.Word.length])
  · exact hinf w w' fun h => hij (h ▸ rfl)

/-- Proposition 1.8. -/
theorem audit_example_criterion {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) (hd : NonzeroDerivatives f) (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α)
    (hc : 1 - cmax ε f ≠ 0)
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x : I, α ≤ ‖nonlin (f i) x (hd i [] x) - nonlin (f j) x (hd j [] x)‖) :
    0 < beta f hd ∧ (divide (2 * beta f hd * cmax ε f) (1 - cmax ε f) hc < α →
      (∀ n, ∀ i j : Fin n → Fin N, i ≠ j →
        0 < ⨆ x : I, ‖dualProjFin f hd (List.ofFn i) x -
          dualProjFin f hd (List.ofFn j) x‖) ∧
      (∀ i j : ℕ → Fin N, i ≠ j →
        0 < ⨆ x : I, ‖dualProjInf f hd i x - dualProjInf f hd j x‖) ∧
      SESC f) := by
  obtain ⟨hβ, h⟩ := (toIFS hε f hf).proposition_1_8 hN hα fun i j hij =>
    let ⟨x, hx⟩ := hsep i j hij; ⟨x, x.2, hx⟩
  refine ⟨hβ, fun hα' => ?_⟩
  have hc_eq : (toIFS hε f hf).cmax = cmax ε f := by unfold cmax; rw [nbhd_eq_lib]; rfl
  obtain ⟨hne, hS⟩ := h (by rw [hc_eq]; exact hα')
  refine ⟨fun n i j hij => ?_,
    fun i j hij => hne (.inf i) (.inf j) (fun h => hij (by cases h; rfl)) rfl, hS⟩
  simpa only [← dualProjFin_eq_lib (toIFS hε f hf) hd] using hne (.fin (List.ofFn i))
    (.fin (List.ofFn j)) (fun h => hij (List.ofFn_injective (AnalyticESC.Word.fin.inj h))) (by simp)

/-- The polynomial example of Section 1.2.2. -/
theorem audit_example_sesc : ∃ ε > 0, (∀ i, InClass ε (exampleMaps i)) ∧ SESC exampleMaps :=
  ⟨1 / 100, by norm_num, fun i => inClass_iff_lib.mpr (AnalyticESC.exampleMaps_inClass i),
    AnalyticESC.exampleIFS_sesc⟩

/-- Individual-map linearisation for Theorem 1.12. -/
theorem audit_conj_similarity {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) (i : Fin N) :
    ∃ g, IsAnalyticCoord g ∧ (∀ x ∈ I, deriv g x ≠ 0) ∧
      ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, g (f i x).re = lam * g x + t :=
  (toIFS hε f hf).theorem_1_12_similarity i

/-- Theorem 1.12 (a). -/
theorem audit_conj_iff {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i)) (hd : NonzeroDerivatives f)
    (hnd : ¬ ∃ x, attractor f = {x}) :
    ConjSelfSimilar (fun i (x : ℝ) => (f i x).re) ↔
      ∀ i j : ℕ → Fin N, ∀ x : I, dualProjInf f hd i x = dualProjInf f hd j x :=
  (((toIFS hε f hf).theorem_1_12 hnd).1).trans
    ⟨fun h i j x => h i j x x.2, fun h i j x hx => h i j ⟨x, hx⟩⟩

/-- Theorem 1.12 (b). -/
theorem audit_subconj_iff {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i)) (hd : NonzeroDerivatives f)
    (hnd : ¬ ∃ x, attractor f = {x}) :
    (∃ (m : ℕ) (i j : Fin m → Fin N), i ≠ j ∧
      ConjSelfSimilar ![fun x : ℝ => (comp f (List.ofFn i) x).re,
        fun x : ℝ => (comp f (List.ofFn j) x).re]) ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        ∀ x : I, dualProjInf f hd (periodic hm i) x = dualProjInf f hd (periodic hm j) x :=
  (((toIFS hε f hf).theorem_1_12 hnd).2).trans
    (exists_congr fun _ => exists_congr fun _ => exists_congr fun _ => exists_congr fun _ =>
      and_congr_right fun _ => ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩)

section DimensionProofs

open MeasureTheory Filter Topology

theorem dimEquality_of_lib {ε : ℝ} (Φ : AnalyticESC.IFS N ε)
    (h : Φ.DimEquality) : DimEquality Φ.f := by
  obtain ⟨⟨s, hs, hset⟩, hm⟩ := h
  refine ⟨⟨s, fun t => (AnalyticESC.positive_length_tendsto_iff _).trans (hs t), hset⟩,
    fun p hp μ hμ _ => (hm p hp μ hμ).mono fun _ hx => (AnalyticESC.scale_tendsto_iff _ _).mpr hx⟩

/-- Theorem 1.6 (Rapaport). -/
theorem audit_dim_of_esc (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) {ε : ℝ}
    (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i))
    (hN : 0 < N) (hnd : ¬ ∃ x, attractor f = {x}) (hesc : ESC f) : DimEquality f :=
  dimEquality_of_lib (toIFS hε f hf) ((toIFS hε f hf).theorem_1_6 hM hS hN hnd hesc)

/-- Corollary 1.7. -/
theorem audit_dim_open_dense (hM : RapaportMeasureStatement) (hS : RapaportSetStatement)
    (hN : 2 ≤ N) :
    ∃ U : Set (Fin N → ℂ → ℂ), (∀ f ∈ U, InUnionClass f ∧ DimEquality f) ∧
      (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2 f g < r → g ∈ U) ∧
      (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2 f g < r) := by
  have hlib : ∀ f : Fin N → ℂ → ℂ, InUnionClass f → AnalyticESC.InUnionClass f :=
    fun f ⟨ε, hε, hf⟩ => ⟨ε, hε, fun i => inClass_iff_lib.mp (hf i)⟩
  obtain ⟨U, hE, hO, hD⟩ := AnalyticESC.corollary_1_7 hM hS hN
  refine ⟨U, fun f hf => ?_, fun f hf => ?_, fun f hf r hr => hD f (hlib f hf) r hr⟩
  · obtain ⟨ε, ⟨g, hε, hg⟩, rfl, hDE⟩ := hE f hf
    exact ⟨⟨ε, hε, fun i => inClass_iff_lib.mpr (hg i)⟩, dimEquality_of_lib ⟨g, hε, hg⟩ hDE⟩
  · obtain ⟨r, hr, h⟩ := hO f hf
    exact ⟨r, hr, fun g hg hd => h g (hlib g hg) hd⟩

/-- The polynomial example of Section 1.2.2. -/
theorem audit_example_dim (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (pressureRatio exampleMaps t) atTop (𝓝 0) ↔
        t = s) ∧
      s < 1 ∧ dimH (attractor exampleMaps) = ENNReal.ofReal s ∧
      ∀ p : Fin 3 → ℝ, IsProbVec p → ∀ μ : Measure ℝ, IsSelfConformal exampleMaps p μ →
        ∀ hχ : lyapunov exampleMaps p μ ≠ 0,
        entropy p < lyapunov exampleMaps p μ ∧
        ∀ᵐ x ∂μ, Tendsto (fun r : Scale => logRatio (μ.real (closedBall x r)) r) scaleZero
          (𝓝 (divide (entropy p) (lyapunov exampleMaps p μ) hχ)) := by
  obtain ⟨s, hs, hs1, hset, hm⟩ := AnalyticESC.example_dim hM hS
  refine ⟨s, fun t => (AnalyticESC.positive_length_tendsto_iff _).trans (hs t), hs1, hset,
    fun p hp μ hμ _ => ?_⟩
  obtain ⟨hent, hlocal⟩ := hm p hp μ hμ
  exact ⟨hent, hlocal.mono fun _ hx => (AnalyticESC.scale_tendsto_iff _ _).mpr hx⟩

/-- The natural measure of the polynomial example in Section 1.2.2. -/
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
  obtain ⟨s, hs, hG, hm⟩ := AnalyticESC.example_localDim_of_bowen hB
  exact ⟨s, fun t => (AnalyticESC.positive_length_tendsto_iff _).trans (hs t), hG,
    fun ν hν hGν => (AnalyticESC.scale_tendsto_iff _ _).mpr (hm ν hν hGν)⟩

/-- `L^q` dimensions of the polynomial example in Section 1.2.2. -/
theorem audit_example_lq (hB : BowenGibbsStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (pressureRatio exampleMaps t) atTop (𝓝 0) ↔
        t = s) ∧
      ∀ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν →
        IsGibbsMeasure (potential exampleMaps s) ν → ∀ q > 1, ∀ hq : q - 1 ≠ 0,
        lqDim (ν.map (natProj exampleMaps)) q hq ≤ divide q (q - 1) hq * (s - 1 / 3) ∧
        (3 * s < q → lqDim (ν.map (natProj exampleMaps)) q hq < s) := by
  obtain ⟨s, hs, hq⟩ := AnalyticESC.example_lq_of_bowen hB
  refine ⟨s, fun t => (AnalyticESC.positive_length_tendsto_iff _).trans (hs t),
    fun ν hν hG q hq1 hq0 => ?_⟩
  have hlq (μ) : lqDim μ q hq0 = AnalyticESC.lqDim μ q :=
    congrArg (· / (q - 1)) (AnalyticESC.scale_liminf (AnalyticESC.lqRatio μ q))
  simp only [hlq, divide]
  exact hq ν hν hG q hq1

end DimensionProofs

end Challenge
