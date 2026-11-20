module

public import AnalyticESC.Dimension.NaturalMeasure

@[expose] public section

/-! For a measure on the nonnegative half-line, the mesh cell at zero contains the mass
of the closed ball at half the mesh scale. -/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory

abbrev cellMass (μ : Measure ℝ) (r : ℝ) (k : ℤ) := μ.real (Ico (k * r) ((k + 1) * r))

/-- The `L^q` sum `∑_{k ∈ ℤ} μ([kr, (k+1)r))^q` of `μ` at scale `r`. -/
noncomputable def lqSum (μ : Measure ℝ) (q r : ℝ) : ℝ :=
  ∑' k : ℤ, cellMass μ r k ^ q

/-- The quotient `log(∑_{k ∈ ℤ} μ([kr, (k+1)r))^q) / log r`, whose limit inferior as `r → 0` is the
`L^q` spectrum. -/
noncomputable def lqRatio (μ : Measure ℝ) (q r : ℝ) : ℝ := Real.log (lqSum μ q r) / Real.log r

/-- For `q ≥ 1`, the masses of the disjoint cells bound the `L^q` sum by one. -/
private theorem lq_summable_and_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ] {q r : ℝ}
    (hq : 1 ≤ q) : Summable (fun k => cellMass μ r k ^ q) ∧ 0 ≤ lqSum μ q r ∧ lqSum μ q r ≤ 1 := by
  have hp (k : ℤ) : 0 ≤ cellMass μ r k ^ q := by positivity
  have H (s : Finset ℤ) : ∑ k ∈ s, cellMass μ r k ^ q ≤ 1 := by
    refine (Finset.sum_le_sum fun k _ =>
      Real.rpow_le_self_of_le_one (measureReal_nonneg (μ := μ)) measureReal_le_one hq).trans ?_
    simpa using (sum_measureReal_le_measureReal_univ (μ := μ) (s := s)
      (t := fun k : ℤ => Ico (k * r) ((k + 1) * r)) (fun _ _ => measurableSet_Ico)
      (fun i _ j _ hij => by simpa [zsmul_eq_mul] using pairwise_disjoint_Ico_zsmul r hij))
  exact ⟨summable_of_sum_le hp H, tsum_nonneg hp, Real.tsum_le_of_sum_le hp H⟩


end AnalyticESC

namespace Challenge

open AnalyticESC Set Metric Filter Topology MeasureTheory

/-- `L^q` dimensions of the polynomial example in Section 1.2.2, from Bowen's theorem:
for every Gibbs measure `ν` of the potential `s(Φ) log|f'_{ω₀}(π(σω))|` and every `q > 1`,
the natural measure `μ = ν ∘ π⁻¹` has `D_μ(q) ≤ q (s(Φ) - 1/3) / (q - 1)`, which is smaller than `s(Φ)` for `q > 3 s(Φ)`. -/
theorem audit_example_lq (hB : BowenGibbsStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (pressureRatio exampleMaps t) atTop (𝓝 0) ↔ t = s) ∧
      ∀ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν →
        IsGibbsMeasure (potential exampleMaps s) ν → ∀ q > 1, ∀ hq : q - 1 ≠ 0,
        lqDim (ν.map (natProj exampleMaps)) q hq ≤ divide q (q - 1) hq * (s - 1 / 3) ∧
        (3 * s < q → lqDim (ν.map (natProj exampleMaps)) q hq < s) := by
  obtain ⟨s, hs₀, hs, -, h⟩ := exampleIFS.gibbs_at_pressure_zero hB (by norm_num)
  refine ⟨s, hs, fun ν hν hG q hq hq₀ => ?_⟩
  let := hν
  obtain ⟨hpos, hlim⟩ := example_localDim hs₀ (h ν hν hG)
  have hq1  := sub_pos.2 hq
  let μ := ν.map exampleIFS.natProj
  have hdim : lqDim μ q hq₀ ≤ q / (q - 1) * (s - 1 / 3) := by
    change liminf (AnalyticESC.lqRatio μ q) (map Subtype.val scaleZero) / (q - 1) ≤ _
    rw [scaleZero_map, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hq1.le
    have hlim := (hlim (1 / 2) (by norm_num)).const_mul q
    have hμ : ∀ᵐ x ∂μ, 0 ≤ x :=
      (ae_map_iff exampleIFS.measurable_natProj.aemeasurable measurableSet_Ici).2
        (.of_forall fun w => (exampleIFS.natProj_mem_I w).1)
    rw [← hlim.liminf_eq]
    have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, r ∈ Ioo 0 1 := Ioo_mem_nhdsGT one_pos
    have hb := hev.mono fun r hr => lq_summable_and_bounds μ hq.le (r := r)
    refine liminf_le_liminf ?_ (isBoundedUnder_of_eventually_ge (a := 0) ?_) hlim.isCoboundedUnder_ge
    · filter_upwards [hev, hb] with r hr hb
      let m := μ.real (closedBall 0 (1 / 2 * r))
      have hm : 0 < m := hpos _ (by simp_all)
      have he : m ≤ cellMass μ r 0 := by
        apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
        filter_upwards [hμ] with x hx hx'
        grind [mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg]
      rw [lqRatio, ← mul_div_assoc, ← Real.log_rpow hm]
      exact div_le_div_of_nonpos_of_le (Real.log_neg hr.1 hr.2).le
        (Real.log_le_log (Real.rpow_pos_of_pos hm q) ((Real.rpow_le_rpow hm.le he (by linarith : 0 ≤ q)).trans (hb.1.le_tsum 0 (fun _ _ => by positivity))))
    · filter_upwards [hev, hb] with r hr ⟨_, h₀, h₁⟩
      exact div_nonneg_of_nonpos (Real.log_nonpos h₀ h₁) (Real.log_neg hr.1 hr.2).le
  refine ⟨hdim, fun h3 => hdim.trans_lt ?_⟩
  change q / (q - 1) * (s - 1 / 3) < s
  rw [div_mul_eq_mul_div, div_lt_iff₀ hq1]
  linarith

end Challenge
