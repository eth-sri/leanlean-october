/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Assembly.KernelTail

/-! Finite-barrier two-root kernels as tilted Gaussian rectangle probabilities, their uniform off-diagonal convergence, and the off-diagonal uniform Cauchy property of the growing-barrier kernels. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- Pairs of points of `K` at distance at least `s₀`. -/
def separatedPairs (K : Set ℂ) (s₀ : ℝ) : Set (ℂ × ℂ) :=
  (K ×ˢ K) ∩ {p | s₀ ≤ ‖p.1 - p.2‖}

/-- The two-root growing-barrier Wick kernel of one admissible regularization. -/
noncomputable abbrev growingPairKernel {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ → ℂ → ℝ) (g a : ℝ) (k₀ : ℕ) (r s : ℝ) (p : ℂ × ℂ) : ℝ≥0∞ :=
  compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel P Y Y g a k₀ r s p.1 p.2 true true

private def pairScale (k₀ m : ℕ) (i : Fin ((m + 1 - k₀) * 2)) : ℕ :=
  k₀ + ((finProdFinEquiv.symm i).1 : ℕ)

private def pairCenter (k₀ m : ℕ) (p : ℂ × ℂ) (i : Fin ((m + 1 - k₀) * 2)) : ℂ :=
  if (finProdFinEquiv.symm i).2 = 0 then p.1 else p.2

private lemma rect_measurable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Z : Ω → ι → ℝ) (hZ : ∀ i, Measurable fun ω => Z ω i) (b c : ι → ℝ) :
    Measurable (gaussianRectangleIndicator Z b c) := by
  classical
  have hset : MeasurableSet {ω | ∀ i, Z ω i + c i ≤ b i} := by
    rw [show {ω | ∀ i, Z ω i + c i ≤ b i} = ⋂ i, {ω | Z ω i + c i ≤ b i} by ext; simp]
    exact MeasurableSet.iInter fun i => measurableSet_le ((hZ i).add measurable_const) measurable_const
  unfold gaussianRectangleIndicator
  exact Measurable.ite hset measurable_const measurable_const

private lemma finiteBarrier_eq_rect
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ) (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (g a : ℝ) (k₀ m : ℕ) (hk₀cut : Real.exp (-(k₀ : ℝ)) ≤ ε₀)
    {ε δ : ℝ} (hε : 0 < ε) (hεcut : ε ≤ ε₀) (hδ : 0 < δ) (hδcut : δ ≤ ε₀)
    (p : ℂ × ℂ) :
    compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m ε δ p.1 p.2 true true =
      ENNReal.ofReal (Real.exp (g ^ 2 * gaussianCovariance P
          (fun ω => Y ω ε p.1) (fun ω => Y ω δ p.2)) *
        ∫ ω, gaussianRectangleIndicator
          (fun ω i => Y ω (Real.exp (-(pairScale k₀ m i : ℝ))) (pairCenter k₀ m p i))
          (fun i => a * (pairScale k₀ m i : ℝ))
          (fun i => g * gaussianCovariance P
              (fun ω => Y ω (Real.exp (-(pairScale k₀ m i : ℝ))) (pairCenter k₀ m p i))
                (fun ω => Y ω ε p.1) +
            g * gaussianCovariance P
              (fun ω => Y ω (Real.exp (-(pairScale k₀ m i : ℝ))) (pairCenter k₀ m p i))
                (fun ω => Y ω δ p.2)) ω ∂P) := by
  let n := (m + 1 - k₀) * 2
  let tup : Fin n ⊕ Bool → ℝ × ℂ := fun i =>
    match i with
    | .inl j => (Real.exp (-(pairScale k₀ m j : ℝ)), pairCenter k₀ m p j)
    | .inr false => (ε, p.1)
    | .inr true => (δ, p.2)
  let V : Ω → Fin n ⊕ Bool → ℝ := fun ω i => Y ω (tup i).1 (tup i).2
  have hsc (j : Fin n) : Real.exp (-(pairScale k₀ m j : ℝ)) ≤ ε₀ :=
    (Real.exp_le_exp.2 (by linarith [show (k₀ : ℝ) ≤ pairScale k₀ m j from mod_cast Nat.le_add_right k₀ _])).trans hk₀cut
  have hV : IsCenteredJointlyGaussian P V := by
    classical
    let e := Fintype.equivFin (Fin n ⊕ Bool)
    simpa using centeredJointlyGaussian_reindex P e _ (hY.gaussian _ (fun j => tup (e.symm j)) fun j => by
      rcases e.symm j with i | (_ | _)
      · exact ⟨Real.exp_pos _, hsc i⟩
      · exact ⟨hε, hεcut⟩
      · exact ⟨hδ, hδcut⟩)
  let barrier : Fin n → ℝ := fun j => a * (pairScale k₀ m j : ℝ)
  have htilt := finite_gaussian_wick_pair_tilt_with_coarse_rectangle P V hV (.inr false) (.inr true) g Sum.inl barrier
  have hbar_iff (ω : Ω) :
      ((ω, p.1) ∈ admissibleGrowingBarrierSet Y a k₀ (m : ℝ) ∧
        (ω, p.2) ∈ admissibleGrowingBarrierSet Y a k₀ (m : ℝ)) ↔
      ∀ i, V ω (Sum.inl i) ≤ barrier i := by
    refine ⟨fun ⟨hx, hy⟩ i => ?_, fun h => ?_⟩
    · have hle : ((pairScale k₀ m i : ℕ) : ℝ) ≤ m := mod_cast (by unfold pairScale; omega : pairScale k₀ m i ≤ m)
      dsimp [V, tup, pairCenter, barrier]
      split_ifs <;> [exact hx _ (Nat.le_add_right _ _) hle; exact hy _ (Nat.le_add_right _ _) hle]
    · have hcoord (k : ℕ) (hk₀ : k₀ ≤ k) (hkm : (k : ℝ) ≤ m) (c : Fin 2) :
          Y ω (Real.exp (-(k : ℝ))) (if c = 0 then p.1 else p.2) ≤ a * (k : ℝ) := by
        have hkm' : k ≤ m := mod_cast hkm
        have hlt : k - k₀ < m + 1 - k₀ := by omega
        let i : Fin n := finProdFinEquiv (⟨k - k₀, hlt⟩, c)
        have hsym : finProdFinEquiv.symm i = (⟨k - k₀, hlt⟩, c) := finProdFinEquiv.symm_apply_apply _
        have hs : pairScale k₀ m i = k := by unfold pairScale; rw [hsym]; dsimp; omega
        have hc : pairCenter k₀ m p i = if c = 0 then p.1 else p.2 := by unfold pairCenter; rw [hsym]
        simpa [V, tup, barrier, hs, hc] using h i
      exact ⟨fun k hk₀ hkm => by simpa using hcoord k hk₀ hkm 0,
        fun k hk₀ hkm => by simpa using hcoord k hk₀ hkm 1⟩
  have hleft : compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m ε δ p.1 p.2 true true =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (g * V ω (.inr false) - g ^ 2 / 2 * gaussianVariance P (fun ω => V ω (.inr false)))) *
        ENNReal.ofReal (Real.exp (g * V ω (.inr true) - g ^ 2 / 2 * gaussianVariance P (fun ω => V ω (.inr true)))) *
        Set.indicator {z : Fin n ⊕ Bool → ℝ | ∀ i, z (Sum.inl i) ≤ barrier i} (fun _ => (1 : ℝ≥0∞)) (V ω) ∂P := by
    unfold compatibleAdmissibleSelectedFiniteBarrierPairKernel
    refine lintegral_congr fun ω => ?_
    simp only [ite_self]
    have hI : Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ)) (fun _ => (1 : ℝ≥0∞)) (ω, p.1) *
        Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ)) (fun _ => (1 : ℝ≥0∞)) (ω, p.2) =
        Set.indicator {z : Fin n ⊕ Bool → ℝ | ∀ i, z (Sum.inl i) ≤ barrier i} (fun _ => (1 : ℝ≥0∞)) (V ω) := by
      by_cases hb : ∀ i, V ω (Sum.inl i) ≤ barrier i
      · obtain ⟨h1, h2⟩ := (hbar_iff ω).2 hb
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
          Set.indicator_of_mem (show V ω ∈ {z : Fin n ⊕ Bool → ℝ | ∀ i, z (Sum.inl i) ≤ barrier i} from hb), mul_one]
      · rw [Set.indicator_of_notMem (show V ω ∉ {z : Fin n ⊕ Bool → ℝ | ∀ i, z (Sum.inl i) ≤ barrier i} from hb)]
        by_cases hx : (ω, p.1) ∈ admissibleGrowingBarrierSet Y a k₀ (m : ℝ)
        · rw [Set.indicator_of_notMem (fun hy => hb ((hbar_iff ω).1 ⟨hx, hy⟩)), mul_zero]
        · rw [Set.indicator_of_notMem hx, zero_mul]
    rw [mul_assoc (_ * _), hI]; rfl
  let Z : Ω → Fin n → ℝ := fun ω j => Y ω (Real.exp (-(pairScale k₀ m j : ℝ))) (pairCenter k₀ m p j)
  let shift : Fin n → ℝ := fun j =>
    g * gaussianCovariance P (fun ω => Z ω j) (fun ω => Y ω ε p.1) +
      g * gaussianCovariance P (fun ω => Z ω j) (fun ω => Y ω δ p.2)
  have hrm : Measurable (gaussianRectangleIndicator Z barrier shift) :=
    rect_measurable Z (fun _ => admissible_field_measurable_sample P U dens ε₀ Y hY _ _) barrier shift
  have hri : Integrable (gaussianRectangleIndicator Z barrier shift) P :=
    Integrable.of_bound hrm.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      unfold gaussianRectangleIndicator; split_ifs <;> simp)
  have hright : (∫⁻ ω, Set.indicator {z : Fin n ⊕ Bool → ℝ | ∀ i, z (Sum.inl i) ≤ barrier i} (fun _ => (1 : ℝ≥0∞))
      (fun i => V ω i + g * gaussianCovariance P (fun ω => V ω i) (fun ω => V ω (.inr false)) +
        g * gaussianCovariance P (fun ω => V ω i) (fun ω => V ω (.inr true))) ∂P) =
      ENNReal.ofReal (∫ ω, gaussianRectangleIndicator Z barrier shift ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hri (ae_of_all _ fun _ => by
      unfold gaussianRectangleIndicator; split_ifs <;> norm_num)]
    refine lintegral_congr fun ω => ?_
    let fV (i : Fin n ⊕ Bool) := V ω i + g * gaussianCovariance P (fun ω => V ω i) (fun ω => V ω (.inr false)) +
      g * gaussianCovariance P (fun ω => V ω i) (fun ω => V ω (.inr true))
    have hiff : (∀ i, fV (Sum.inl i) ≤ barrier i) ↔ (∀ i, Z ω i + shift i ≤ barrier i) := by
      dsimp [fV, V, tup, Z, shift]; simp only [add_assoc]
    by_cases hc : ∀ i, Z ω i + shift i ≤ barrier i
    · rw [Set.indicator_of_mem (show fV ∈ {z : Fin n ⊕ Bool → ℝ | ∀ i, z (Sum.inl i) ≤ barrier i} from hiff.2 hc)]
      unfold gaussianRectangleIndicator; simp [hc]
    · rw [Set.indicator_of_notMem (show fV ∉ {z : Fin n ⊕ Bool → ℝ | ∀ i, z (Sum.inl i) ≤ barrier i} from mt hiff.1 hc)]
      unfold gaussianRectangleIndicator; simp [hc]
  have hcsym : gaussianCovariance P (fun ω => Y ω δ p.2) (fun ω => Y ω ε p.1) =
      gaussianCovariance P (fun ω => Y ω ε p.1) (fun ω => Y ω δ p.2) :=
    integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  simp only at htilt
  rw [hleft, htilt, hright, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 2
  dsimp [V, tup]; rw [hcsym]; congr 1; ring

/-- Off-diagonal uniform Cauchy property of the growing-barrier kernels. -/
theorem growingPairKernel_offDiagonal_uniform_cauchy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (gLo gHi a : ℝ) (hgLo : 0 < gLo) (hgLoHi : gLo ≤ gHi) (hga : gHi < a)
    (k₀ : ℕ) (hk₀cut : Real.exp (-(k₀ : ℝ)) ≤ ε₀)
    (hvar : ∀ k : ℕ, k₀ ≤ k → ∀ x ∈ K,
      1 ≤ gaussianVariance P (fun ω => Y ω (Real.exp (-(k : ℝ))) x))
    (s₀ : ℝ) (hs₀ : 0 < s₀) (η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, ∀ r s r' s' : ℝ, R ≤ r → R ≤ s → R ≤ r' → R ≤ s' →
      ∀ g ∈ Icc gLo gHi, ∀ p ∈ separatedPairs K s₀,
        growingPairKernel P Y g a k₀ r s p ≠ ⊤ ∧
        |(growingPairKernel P Y g a k₀ r s p).toReal -
          (growingPairKernel P Y g a k₀ r' s' p).toReal| < η := by
  obtain ⟨C, hC, htail⟩ := finiteBarrierPairKernel_le_growing_add_tail P U dens ε₀ Y hY K hK hKU
  let L : ℝ := Real.log (1 / s₀)
  let cHi : ℝ≥0∞ := ENNReal.ofReal (Real.exp (gHi ^ 2 * max (L + C) 0))
  let THi (N : ℕ) : ℝ≥0∞ := ∑' j : ℕ, ENNReal.ofReal (Real.exp (-((a - gHi) ^ 2 * ((j + N : ℕ) : ℝ) / 16)))
  have herr : Tendsto (fun m : ℕ => 2 * (cHi * THi (m + 1))) atTop (𝓝 0) := by
    have h1 := (tendsto_compatible_mixed_double_root_barrier_tail_sum gHi a hga).comp (tendsto_add_atTop_nat 1)
    have h2 := ENNReal.Tendsto.const_mul (a := cHi) h1 (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at h2
    have h3 := ENNReal.Tendsto.const_mul (a := 2) h2 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    rwa [mul_zero] at h3
  have hev : ∀ᶠ m : ℕ in atTop, k₀ ≤ m ∧ C < (m : ℝ) ∧
      gHi * (|L| + 2 * C) ≤ (a - gHi) * (m : ℝ) / 2 ∧
      2 * (cHi * THi (m + 1)) < ENNReal.ofReal (η / 4) := by
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt C
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 * (gHi * (|L| + 2 * C)) / (a - gHi))
    filter_upwards [eventually_ge_atTop k₀, eventually_ge_atTop N₁, eventually_ge_atTop N₂,
      herr.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (by positivity : 0 < η / 4)))] with m hm0 hm1 hm2 hm4
    refine ⟨hm0, hN₁.trans_le (Nat.cast_le.2 hm1), ?_, hm4⟩
    have := (div_lt_iff₀ (sub_pos.2 hga)).1 (hN₂.trans_le (Nat.cast_le.2 hm2))
    nlinarith
  obtain ⟨m, hk₀m, hCm, hlinm, herrm⟩ := hev.exists
  have hmcut : Real.exp (-(m : ℝ)) ≤ ε₀ :=
    (Real.exp_le_exp.2 (by linarith [show (k₀ : ℝ) ≤ m from mod_cast hk₀m])).trans hk₀cut
  -- Finite-barrier uniform Cauchy at level m
  have : Nonempty (Fin ((m + 1 - k₀) * 2)) := ⟨⟨0, by omega⟩⟩
  have hsc (i : Fin ((m + 1 - k₀) * 2)) : Real.exp (-(pairScale k₀ m i : ℝ)) ≤ min ε₀ ε₀ := by
    rw [min_self]
    exact (Real.exp_le_exp.2 (by linarith [show (k₀ : ℝ) ≤ pairScale k₀ m i from mod_cast Nat.le_add_right k₀ _])).trans hk₀cut
  have hcmem (p : ℂ × ℂ) (hp : p ∈ K ×ˢ K) (i : Fin ((m + 1 - k₀) * 2)) : pairCenter k₀ m p i ∈ K := by
    unfold pairCenter; split_ifs <;> [exact hp.1; exact hp.2]
  obtain ⟨H, _, coarseKernel, hconv⟩ := compatible_finite_mixed_pair_kernel_tendsto_uniformly
    P U dens ε₀ ε₀ Y Y hY hY (isCompatibleAdmissibleRegularizations_self P U dens ε₀ Y hY)
    K hK hKU (separatedPairs K s₀)
    ((hK.prod hK).inter_right (isClosed_le continuous_const (continuous_fst.sub continuous_snd).norm))
    inter_subset_left s₀ hs₀ (fun _ hp => hp.2)
    (pairScale k₀ m) hsc (pairCenter k₀ m) (fun p hp i => hcmem p hp.1 i)
    (fun p hp i => hvar _ (Nat.le_add_right _ _) _ (hcmem p hp.1 i))
    (fun i => a * (pairScale k₀ m i : ℝ)) true true (Icc gLo gHi) gHi (hgLo.le.trans hgLoHi)
    (fun g hg => by rw [abs_of_pos (lt_of_lt_of_le hgLo hg.1)]; exact hg.2)
  obtain ⟨δ, hδ, hδconv⟩ := hconv (η / 4) (by positivity)
  have hcut : 0 < min δ ε₀ := lt_min hδ hY.cutoffPositive
  let R := max (-Real.log (min δ ε₀)) m
  refine ⟨R, fun r s r' s' hr hs hr' hs' g hg p hp => ?_⟩
  have hexp_le {t : ℝ} (ht : R ≤ t) : Real.exp (-t) ≤ min δ ε₀ := by
    calc Real.exp (-t) ≤ Real.exp (Real.log (min δ ε₀)) :=
          Real.exp_le_exp.2 (by linarith [(le_max_left (-Real.log (min δ ε₀)) m).trans ht])
      _ = min δ ε₀ := Real.exp_log hcut
  have htrunc {u v : ℝ} (hu : R ≤ u) (hv : R ≤ v) :
      growingPairKernel P Y g a k₀ u v p ≠ ⊤ ∧
      |(compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m
          (Real.exp (-u)) (Real.exp (-v)) p.1 p.2 true true).toReal -
        (growingPairKernel P Y g a k₀ u v p).toReal| < η / 4 := by
    have hmu : (m : ℝ) ≤ u := (le_max_right _ _).trans hu
    have hmv : (m : ℝ) ≤ v := (le_max_right _ _).trans hv
    have hgpos : 0 < g := lt_of_lt_of_le hgLo hg.1
    have hga' : g < a := hg.2.trans_lt hga
    have hp_pos : 0 < ‖p.1 - p.2‖ := lt_of_lt_of_le hs₀ hp.2
    have hLp : Real.log (1 / ‖p.1 - p.2‖) ≤ L :=
      Real.log_le_log (one_div_pos.2 hp_pos) (one_div_le_one_div_of_le hs₀ hp.2)
    have hfin : compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m
        (Real.exp (-u)) (Real.exp (-v)) p.1 p.2 true true ≠ ⊤ := by
      rw [finiteBarrier_eq_rect P U dens ε₀ Y hY g a k₀ m hk₀cut
        (Real.exp_pos _) ((hexp_le hu).trans (min_le_right _ _))
        (Real.exp_pos _) ((hexp_le hv).trans (min_le_right _ _)) p]
      exact ENNReal.ofReal_ne_top
    have hle := compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel_le_finiteBarrier
      P Y Y g a k₀ m u v p.1 p.2 true true hmu hmv
    have hlinG : g * (|L| + 2 * C) ≤ (a - g) * (m : ℝ) / 2 := by
      have h1 := mul_le_mul_of_nonneg_right hg.2 (by positivity : 0 ≤ |L| + 2 * C)
      have h2 := mul_le_mul_of_nonneg_right (show a - gHi ≤ a - g by linarith [hg.2]) (Nat.cast_nonneg (α := ℝ) m)
      linarith
    have hup := htail k₀ m hCm hmcut u v hmu hmv p.1 hp.1.1 p.2 hp.1.2 L hp_pos hLp g a hgpos hga' hlinG
    have hcg : ENNReal.ofReal (Real.exp (g ^ 2 * (L + C))) ≤ cHi :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
        ((mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg g)).trans
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hgpos.le hg.2 2) (le_max_right _ _))))
    have hTg : (∑' j : ℕ, ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * ((j + (m + 1) : ℕ) : ℝ) / 16)))) ≤ THi (m + 1) :=
      ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by
        have h2 : a - gHi ≤ a - g := by linarith [hg.2]
        have hm := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sub_pos.2 hga).le h2 2)
          (Nat.cast_nonneg (α := ℝ) (j + (m + 1)))
        linarith))
    have herrG := mul_le_mul' (le_refl (2 : ℝ≥0∞)) (mul_le_mul' hcg hTg)
    have herrfin : 2 * (cHi * THi (m + 1)) ≠ ⊤ := ne_top_of_lt herrm
    refine ⟨ne_top_of_le_ne_top hfin hle, ?_⟩
    rw [← ENNReal.toReal_sub_of_le hle hfin, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono herrfin (tsub_le_iff_left.2 (hup.trans (add_le_add_right herrG _)))).trans_lt
      (by simpa [ENNReal.toReal_ofReal (by positivity : 0 ≤ η / 4)] using
        (ENNReal.toReal_lt_toReal herrfin ENNReal.ofReal_ne_top).2 herrm)
  obtain ⟨htop, hA⟩ := htrunc hr hs
  obtain ⟨_, hA'⟩ := htrunc hr' hs'
  have hc1 := hδconv (Real.exp (-r)) (Real.exp (-s)) (Real.exp_pos _) (by simpa using hexp_le hr)
    (Real.exp_pos _) (by simpa using hexp_le hs) g hg p hp
  have hc2 := hδconv (Real.exp (-r')) (Real.exp (-s')) (Real.exp_pos _) (by simpa using hexp_le hr')
    (Real.exp_pos _) (by simpa using hexp_le hs') g hg p hp
  simp only [ite_self] at hc1 hc2
  have hnn (ε' δ' : ℝ) : 0 ≤ Real.exp (g ^ 2 * gaussianCovariance P (fun ω => Y ω ε' p.1) (fun ω => Y ω δ' p.2)) *
      ∫ ω, gaussianRectangleIndicator
        (fun ω i => Y ω (Real.exp (-(pairScale k₀ m i : ℝ))) (pairCenter k₀ m p i))
        (fun i => a * (pairScale k₀ m i : ℝ))
        (fun i => g * gaussianCovariance P
            (fun ω => Y ω (Real.exp (-(pairScale k₀ m i : ℝ))) (pairCenter k₀ m p i)) (fun ω => Y ω ε' p.1) +
          g * gaussianCovariance P
            (fun ω => Y ω (Real.exp (-(pairScale k₀ m i : ℝ))) (pairCenter k₀ m p i)) (fun ω => Y ω δ' p.2)) ω ∂P :=
    mul_nonneg (Real.exp_nonneg _) (integral_nonneg fun _ => by unfold gaussianRectangleIndicator; split_ifs <;> norm_num)
  have hF_diff : |(compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m
        (Real.exp (-r)) (Real.exp (-s)) p.1 p.2 true true).toReal -
      (compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m
        (Real.exp (-r')) (Real.exp (-s')) p.1 p.2 true true).toReal| < η / 2 := by
    rw [finiteBarrier_eq_rect P U dens ε₀ Y hY g a k₀ m hk₀cut (Real.exp_pos _) ((hexp_le hr).trans (min_le_right _ _))
        (Real.exp_pos _) ((hexp_le hs).trans (min_le_right _ _)) p,
      finiteBarrier_eq_rect P U dens ε₀ Y hY g a k₀ m hk₀cut (Real.exp_pos _) ((hexp_le hr').trans (min_le_right _ _))
        (Real.exp_pos _) ((hexp_le hs').trans (min_le_right _ _)) p,
      ENNReal.toReal_ofReal (hnn _ _), ENNReal.toReal_ofReal (hnn _ _)]
    exact (abs_sub_le _ _ _).trans_lt ((add_lt_add hc1 (by rw [abs_sub_comm]; exact hc2)).trans_eq (by ring))
  refine ⟨htop, ?_⟩
  linarith [abs_sub_le (growingPairKernel P Y g a k₀ r s p).toReal
    (compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m (Real.exp (-r)) (Real.exp (-s)) p.1 p.2 true true).toReal
    (growingPairKernel P Y g a k₀ r' s' p).toReal,
    abs_sub_le (compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m (Real.exp (-r)) (Real.exp (-s)) p.1 p.2 true true).toReal
      (compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m (Real.exp (-r')) (Real.exp (-s')) p.1 p.2 true true).toReal
      (growingPairKernel P Y g a k₀ r' s' p).toReal,
    abs_sub_comm (compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m (Real.exp (-r)) (Real.exp (-s)) p.1 p.2 true true).toReal
      (growingPairKernel P Y g a k₀ r s p).toReal]

end DOZZ.Assembly
