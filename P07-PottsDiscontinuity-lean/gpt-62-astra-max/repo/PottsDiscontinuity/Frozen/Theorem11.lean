module

public import PottsDiscontinuity.Frozen.Theorem12
public import PottsDiscontinuity.PottsThm.ColoringPushforward
public import PottsDiscontinuity.PottsThm.CriticalParameters
public import PottsDiscontinuity.PottsThm.RateTransfer

@[expose] public section
open Filter Topology MeasureTheory
open scoped ENNReal
namespace PottsDiscontinuity
open PottsThm FK Potts RCInfinite

/-- **Theorem 1.1** (arXiv:1611.09877v2, p. 2). -/
theorem potts_theorem_1_1 (q : ℕ) (hq : 4 < q) :
    ∃ μ : Fin (q + 1) → Measure (ℤ × ℤ → Set.Icc 1 q),
      (∀ i, IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) i (μ i)) ∧
      ((∀ i j, i ≠ j → μ i ≠ μ j) ∧ (∀ i, IsTranslationErgodic (μ i)) ∧
        μ 0 ≠ (q : ℝ≥0∞)⁻¹ • ∑ i : Fin q, μ i.succ) ∧
      (∀ i : Fin q, (1 : ℝ) / q < (μ i.succ).real {σ | ((σ (0, 0) : ℕ)) = (i.succ : ℕ)}) ∧
      (∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
              (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((μ 0).real {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / q))
            atTop (𝓝 (lam + 2 * S)) ∧
          0 < lam + 2 * S) := by
  classical
  have hq2 : 2 ≤ q := by omega
  have hqR : (4 : ℝ) < q := by exact_mod_cast hq
  let θ := criticalFKParameters q hq
  let qI : Set.Ici (1:ℝ) := ⟨q, by show 1 ≤ (q:ℝ); linarith⟩
  choose φ hφ using exists_isRCInfiniteVolumeLimit_interior θ
  have hcrit (i) : IsRCInfiniteVolumeLimit (criticalParameters qI).toP
      (criticalParameters qI).toQ i (φ i) := by
    simpa only [θ, (fkCritical_toP_toQ q hq).1, (fkCritical_toP_toQ q hq).2] using hφ i
  obtain ⟨hz, hp, _, _⟩ := critical_cluster_probabilities q hqR φ hcrit
  have hprob (i) : IsProbabilityMeasure (φ i) := (hφ i).1
  have hfin : ∀ᵐ ω ∂φ 0, ∀ x, (cluster ω x).Finite := by
    refine ae_all_iff.mpr fun x => ae_iff.mpr ?_
    exact (infiniteAt_measure_eq_origin θ 0 _ (hφ 0) x).trans hz
  have hβ := pottsCriticalBeta_pos q hq
  let c₀ : Set.Icc 1 q := ⟨1, le_rfl, by omega⟩
  let c (k : Fin q) := boundaryColor (q := q) (i := k.succ) (by simp)
  let μ : Fin (q+1) → Measure (SpinSpace q) := Fin.cases (colorLaw (φ 0) c₀) fun k => colorLaw (φ 1) (c k)
  have hμ (i) : IsProbabilityMeasure (μ i) := Fin.cases (by dsimp [μ]; infer_instance)
    (fun k => by dsimp [μ]; infer_instance) i
  have hmix (i) : MixingFamily spinShift (μ i) cofinite :=
    Fin.cases (colorLaw_mixing θ 0 (hφ 0) c₀) (fun k => colorLaw_mixing θ 1 (hφ 1) (c k)) i
  let mass := fun (i : Fin (q+1)) (k : Fin q) => (μ i).real {σ | σ (0,0) = c k}
  have hgap : 0 < 1 - (q : ℝ)⁻¹ := by
    apply sub_pos.mpr ((inv_lt_one₀ (by linarith : (0:ℝ) < q)).mpr (by linarith))
  have hθpos : 0 < (φ 1).real (infiniteAt (0,0)) := ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  have hpin (k) : (q : ℝ)⁻¹ < mass k.succ k := by
    simpa [mass, μ, colorLaw_one_site] using mul_pos hgap hθpos
  have hsep (k : Fin q) (j) (hne : k.succ ≠ j) : μ k.succ ≠ μ j := by
    suffices h : mass j k ≤ (q : ℝ)⁻¹ from
      fun e => (hpin k).not_ge ((congrArg (fun ν : Measure (SpinSpace q) => ν.real {σ | σ (0,0) = c k}) e).trans_le h)
    cases j using Fin.cases with
    | zero => simp only [mass, μ, Fin.cases_zero, colorLaw_one_site]; simp [Measure.real_def, hz, show (0,0) = (0 : FK.LatticeVertex) from rfl]
    | succ t =>
      have hct : c t ≠ c k := fun e => hne (Fin.ext (congrArg Subtype.val e).symm)
      simp [mass, μ, colorLaw_one_site, hct]; positivity
  have hd (i j) (h : i ≠ j) : μ i ≠ μ j := by
    cases i using Fin.cases with
    | zero => cases j using Fin.cases with
              | zero => exact (h rfl).elim
              | succ k => exact (hsep k 0 h.symm).symm
    | succ k => exact hsep k j h
  let j : Fin q := ⟨0, by omega⟩
  refine ⟨μ, ?_, ⟨hd, fun i => translation_ergodic (hmix i),
    mixing_ne_average j (ν := (fun t => μ t.succ)) (hmix 0) (hmix j.succ) (hsep j 0 (by simp))⟩, ?_, ?_⟩
  · refine Fin.cases ?_ (fun k => ?_)
    · exact free_colorLaw_limit hq2 hβ ⟨φ 0, hφ 0 |>.1⟩ (by simpa only [θ, criticalFKParameters, boxMeasure_free] using boxMeasure_tendsto θ 0 _ (hφ 0)) hfin
    · exact wired_colorLaw_limit hq2 hβ ⟨φ 1, hφ 1 |>.1⟩ k.succ (by simp) (by simpa only [θ, criticalFKParameters, boxMeasure_wired] using boxMeasure_tendsto θ 1 _ (hφ 1))
  · intro k; simpa [mass, c, boundaryColor, Subtype.ext_iff, one_div] using hpin k
  · intro lam hl hc
    obtain ⟨S, hS, hr, hL⟩ := RCMProof.rc_critical_rate q hqR (μ := _) (hcrit 0) lam hl hc
    exact ⟨S, hS, free_colorLaw_rate hq2 c₀ hfin hL hr, hL⟩

end PottsDiscontinuity
