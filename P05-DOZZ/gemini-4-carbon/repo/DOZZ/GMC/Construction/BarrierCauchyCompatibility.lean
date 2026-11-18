/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.BarrierCauchyLocalEstimates

/-! Uniform finite-scale covariance and rectangle limits for mixed admissible cutoffs. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

private lemma cov_symm {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f g : Ω → ℝ) :
    gaussianCovariance P f g = gaussianCovariance P g f :=
  integral_congr_ae (ae_of_all P fun _ => mul_comm _ _)

theorem compatible_finite_coarse_double_root_barrier_probability_tendsto_uniformly
    {Ω α : Type*} {n : ℕ} [MeasurableSpace Ω] [Nonempty (Fin n)]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (S : Set α) (rootX rootY : α → ℂ)
    (hrootX : ∀ a ∈ S, rootX a ∈ K) (hrootY : ∀ a ∈ S, rootY a ∈ K)
    (scale : Fin n → ℕ) (center : α → Fin n → ℂ)
    (hcenter : ∀ a ∈ S, ∀ i, center a i ∈ K)
    (hscale : ∀ i, Real.exp (-(scale i : ℝ)) ≤ min ε₀ ε₁)
    (hv : ∀ a ∈ S, ∀ i, 1 ≤ gaussianVariance P
      (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i)))
    (b₁ b₂ : Bool) (barrier : Fin n → ℝ) (Γ : Set ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hΓ : ∀ γ ∈ Γ, |γ| ≤ B) :
    ∃ coarseKernel : ℕ → ℂ → ℂ → ℝ, ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε ε' : ℝ,
        0 < ε → ε ≤ min δ (min ε₀ ε₁) →
        0 < ε' → ε' ≤ min δ (min ε₀ ε₁) →
        ∀ γ ∈ Γ, ∀ a ∈ S,
          |(∫ ω, gaussianRectangleIndicator
                (fun ω i => Y ω (Real.exp (-(scale i : ℝ))) (center a i)) barrier
                (fun i => γ * gaussianCovariance P
                    (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
                    (fun ω => if b₁ then Y ω ε (rootX a) else Z ω ε (rootX a)) +
                  γ * gaussianCovariance P
                    (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
                    (fun ω => if b₂ then Y ω ε' (rootY a) else Z ω ε' (rootY a))) ω ∂P) -
            (∫ ω, gaussianRectangleIndicator
                (fun ω i => Y ω (Real.exp (-(scale i : ℝ))) (center a i)) barrier
                (fun i => γ * coarseKernel (scale i) (rootX a) (center a i) +
                  γ * coarseKernel (scale i) (rootY a) (center a i)) ω ∂P)| < η := by
  obtain ⟨coarseKernel, hfixedY⟩ := hY.fixedCoarseLimit
  let W (a : α) (ω : Ω) (i : Fin n) := Y ω (Real.exp (-(scale i : ℝ))) (center a i)
  have hW : ∀ a ∈ S, IsCenteredJointlyGaussian P (W a) := fun a _ =>
    hY.gaussian n (fun i => (Real.exp (-(scale i : ℝ)), center a i))
      fun i => ⟨Real.exp_pos _, (hscale i).trans (min_le_left _ _)⟩
  let c (ε ε' γ : ℝ) (a : α) (i : Fin n) :=
    γ * gaussianCovariance P (fun ω => W a ω i) (fun ω => if b₁ then Y ω ε (rootX a) else Z ω ε (rootX a)) +
      γ * gaussianCovariance P (fun ω => W a ω i) (fun ω => if b₂ then Y ω ε' (rootY a) else Z ω ε' (rootY a))
  let d (γ : ℝ) (a : α) (i : Fin n) :=
    γ * coarseKernel (scale i) (rootX a) (center a i) +
      γ * coarseKernel (scale i) (rootY a) (center a i)
  have hcut_pos : 0 < min ε₀ ε₁ := lt_min hY.cutoffPositive hZ.cutoffPositive
  have hcoord : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε ε' : ℝ, 0 < ε → ε ≤ δ → 0 < ε' → ε' ≤ δ →
        ∀ γ ∈ Γ, ∀ a ∈ S, ∀ i, |c ε ε' γ a i - d γ a i| < η := by
    intro η hη
    let η' := η / (8 * (B + 1))
    have hη' : 0 < η' := by dsimp [η']; positivity
    have hloc (i : Fin n) : ∃ δi : ℝ, 0 < δi ∧ ∀ ε : ℝ, 0 < ε → ε ≤ min δi (min ε₀ ε₁) →
        ∀ (b : Bool) (r : α → ℂ), (∀ a ∈ S, r a ∈ K) → ∀ a ∈ S,
          |gaussianCovariance P (fun ω => W a ω i) (fun ω => if b then Y ω ε (r a) else Z ω ε (r a)) -
            coarseKernel (scale i) (r a) (center a i)| < 2 * η' := by
      obtain ⟨δY, hδY, hYl⟩ := hfixedY K hK hKU (scale i) ((hscale i).trans (min_le_left _ _)) η' hη'
      obtain ⟨δZ, hδZ, hZl⟩ := hYZ.2.2.2.2 K hK hKU (scale i) (hscale i) η' hη'
      refine ⟨min δY δZ, lt_min hδY hδZ, fun ε hε hεm b r hr a ha => ?_⟩
      have hY1 : |gaussianCovariance P (fun ω => W a ω i) (fun ω => Y ω ε (r a)) -
          coarseKernel (scale i) (r a) (center a i)| < η' := by
        rw [cov_symm]
        exact hYl ε hε (le_min ((hεm.trans (min_le_left _ _)).trans (min_le_left _ _))
          ((hεm.trans (min_le_right _ _)).trans (min_le_left _ _))) _ (hr a ha) _ (hcenter a ha i)
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · have hZ1 : |gaussianCovariance P (fun ω => W a ω i) (fun ω => Z ω ε (r a)) -
            gaussianCovariance P (fun ω => W a ω i) (fun ω => Y ω ε (r a))| < η' := by
          dsimp only [W]
          rw [cov_symm P (fun ω => Y _ _ _) (fun ω => Z _ _ _),
            cov_symm P (fun ω => Y _ _ (center a i)) (fun ω => Y _ _ (r a))]
          exact hZl ε hε (le_min ((hεm.trans (min_le_left _ _)).trans (min_le_right _ _))
            (hεm.trans (min_le_right _ _))) _ (hr a ha) _ (hcenter a ha i)
        linarith [abs_sub_le (gaussianCovariance P (fun ω => W a ω i) (fun ω => Z ω ε (r a)))
          (gaussianCovariance P (fun ω => W a ω i) (fun ω => Y ω ε (r a)))
          (coarseKernel (scale i) (r a) (center a i))]
      · linarith
    choose δi hδi hbd using hloc
    obtain ⟨i₀, hmin⟩ := Finite.exists_min δi
    refine ⟨min (δi i₀) (min ε₀ ε₁), lt_min (hδi i₀) hcut_pos,
      fun ε ε' hε hεc hε' hε'c γ hγ a ha i => ?_⟩
    have hm1 : ε ≤ min (δi i) (min ε₀ ε₁) :=
      le_min ((hεc.trans (min_le_left _ _)).trans (hmin i)) (hεc.trans (min_le_right _ _))
    have hm2 : ε' ≤ min (δi i) (min ε₀ ε₁) :=
      le_min ((hε'c.trans (min_le_left _ _)).trans (hmin i)) (hε'c.trans (min_le_right _ _))
    have h1 := hbd i ε hε hm1 b₁ rootX hrootX a ha
    have h2 := hbd i ε' hε' hm2 b₂ rootY hrootY a ha
    have hγB := hΓ γ hγ
    have hη_eq : η' * (8 * (B + 1)) = η := by dsimp [η']; field_simp
    let c₁ := gaussianCovariance P (fun ω => W a ω i) (fun ω => if b₁ then Y ω ε (rootX a) else Z ω ε (rootX a))
    let c₂ := gaussianCovariance P (fun ω => W a ω i) (fun ω => if b₂ then Y ω ε' (rootY a) else Z ω ε' (rootY a))
    let k₁ := coarseKernel (scale i) (rootX a) (center a i)
    let k₂ := coarseKernel (scale i) (rootY a) (center a i)
    change |γ * c₁ + γ * c₂ - (γ * k₁ + γ * k₂)| < η
    calc |γ * c₁ + γ * c₂ - (γ * k₁ + γ * k₂)|
      _ = |γ * (c₁ - k₁) + γ * (c₂ - k₂)| := by congr 1; ring
      _ ≤ |γ| * |c₁ - k₁| + |γ| * |c₂ - k₂| := by simpa only [abs_mul] using abs_add_le (γ * (c₁ - k₁)) (γ * (c₂ - k₂))
      _ ≤ B * (2 * η') + B * (2 * η') := add_le_add
          ((mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)).trans (mul_le_mul_of_nonneg_right hγB (by positivity)))
          ((mul_le_mul_of_nonneg_left h2.le (abs_nonneg _)).trans (mul_le_mul_of_nonneg_right hγB (by positivity)))
      _ < η := by rw [← hη_eq]; nlinarith
  have hprob := finite_gaussian_rectangle_probability_two_shift_tendsto_uniformly
    P Γ S W hW barrier hv c d hcoord
  refine ⟨coarseKernel, fun η hη => ?_⟩
  obtain ⟨δ₀, hδ₀, hp⟩ := hprob η hη
  refine ⟨δ₀, hδ₀, fun ε ε' hε hεc hε' hε'c γ hγ a ha => ?_⟩
  exact hp ε ε' hε (hεc.trans (min_le_left _ _)) hε' (hε'c.trans (min_le_left _ _)) γ hγ a ha

theorem compatible_mixed_off_diagonal_wick_factor_tendsto_uniformly
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (_hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (s : ℝ) (hs : 0 < s)
    (S : Set (ℂ × ℂ)) (hS : IsCompact S)
    (hSxy : ∀ p ∈ S, p.1 ∈ K ∧ p.2 ∈ K ∧ s ≤ ‖p.1 - p.2‖)
    (b₁ b₂ : Bool) (Γ : Set ℝ) (B : ℝ)
    (hΓ : ∀ γ ∈ Γ, |γ| ≤ B) :
    ∃ H : ℂ → ℂ → ℝ, ContinuousOn (Function.uncurry H) (U ×ˢ U) ∧
      ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
        ∀ ε ε' : ℝ, 0 < ε → ε ≤ min δ (min ε₀ ε₁) →
          0 < ε' → ε' ≤ min δ (min ε₀ ε₁) →
          ∀ γ ∈ Γ, ∀ p ∈ S,
            |Real.exp (γ ^ 2 * gaussianCovariance P
                (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
                (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2)) -
              Real.exp (γ ^ 2 * (Real.log (1 / ‖p.1 - p.2‖) + H p.1 p.2))| < η := by
  obtain ⟨H, hH, hYoff⟩ := hY.offDiagonalLimit
  refine ⟨H, hH, fun η hη => ?_⟩
  let lim (p : ℂ × ℂ) := Real.log (1 / ‖p.1 - p.2‖) + H p.1 p.2
  have hsep (p : ℂ × ℂ) (hp : p ∈ S) : 0 < ‖p.1 - p.2‖ := lt_of_lt_of_le hs (hSxy p hp).2.2
  have hlim_c : ContinuousOn (fun p => |lim p|) S :=
    ((Real.continuousOn_log.comp'
      ((continuous_fst.sub continuous_snd).norm.continuousOn.inv₀ fun p hp => (hsep p hp).ne')
      fun p hp => Set.mem_compl_singleton_iff.2 (inv_pos.2 (hsep p hp)).ne').congr
      (fun p _ => by simp [one_div]) |>.add
      (hH.mono fun p hp => ⟨hKU (hSxy p hp).1, hKU (hSxy p hp).2.1⟩)).abs
  obtain ⟨R₀, hR₀⟩ := hS.bddAbove_image hlim_c
  let R := max 0 R₀
  let E (z : ℝ × ℝ) := Real.exp (z.1 ^ 2 * z.2)
  obtain ⟨δE, hδE, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc (a := -B) (b := B)).prod (isCompact_Icc (a := -(R + 1)) (b := R + 1))
      |>.uniformContinuousOn_of_continuous (by fun_prop : Continuous E).continuousOn) η hη
  let η' := min δE 1 / 3
  have hη' : 0 < η' := by dsimp [η']; positivity
  obtain ⟨δY, hδY, hYc⟩ := hYoff K hK hKU s hs η' hη'
  obtain ⟨δC, hδC, hCc⟩ := hYZ.2.2.2.1 K hK hKU s hs η' hη'
  refine ⟨min δY δC, lt_min hδY hδC, fun ε ε' hε hεm hε' hε'm γ hγ p hp => ?_⟩
  obtain ⟨hx, hy, hxy⟩ := hSxy p hp
  have hεY : ε ≤ min δY ε₀ := le_min ((hεm.trans (min_le_left _ _)).trans (min_le_left _ _))
    ((hεm.trans (min_le_right _ _)).trans (min_le_left _ _))
  have hε'Y : ε' ≤ min δY ε₀ := le_min ((hε'm.trans (min_le_left _ _)).trans (min_le_left _ _))
    ((hε'm.trans (min_le_right _ _)).trans (min_le_left _ _))
  have hεC : ε ≤ min δC (min ε₀ ε₁) := le_min ((hεm.trans (min_le_left _ _)).trans (min_le_right _ _))
    (hεm.trans (min_le_right _ _))
  have hε'C : ε' ≤ min δC (min ε₀ ε₁) := le_min ((hε'm.trans (min_le_left _ _)).trans (min_le_right _ _))
    (hε'm.trans (min_le_right _ _))
  have hbase := hYc ε ε' hε hεY hε' hε'Y p.1 hx p.2 hy hxy
  let cov := gaussianCovariance P (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
    (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2)
  have hcovErr : |cov - lim p| < min δE 1 := by
    have h2 : |cov - gaussianCovariance P (fun ω => Y ω ε p.1) (fun ω => Y ω ε' p.2)| ≤ η' := by
      dsimp only [cov]
      cases b₁ <;> cases b₂ <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact (hCc ε ε' hε hεC hε' hε'C p.1 hx p.2 hy hxy).2.le
      · rw [cov_symm P (fun ω => Z _ _ _) (fun ω => Y _ _ _),
          cov_symm P (fun ω => Y _ ε _) (fun ω => Y _ ε' _)]
        exact (hCc ε' ε hε' hε'C hε hεC p.2 hy p.1 hx (by simpa [norm_sub_rev] using hxy)).1.le
      · exact (hCc ε ε' hε hεC hε' hε'C p.1 hx p.2 hy hxy).1.le
      · simp [hη'.le]
    have htri := abs_sub_le cov (gaussianCovariance P (fun ω => Y ω ε p.1) (fun ω => Y ω ε' p.2)) (lim p)
    have hmin_pos : 0 < min δE 1 := lt_min hδE zero_lt_one
    dsimp [η', lim] at h2 hbase htri ⊢; linarith
  have hlimB : |lim p| ≤ R := (hR₀ ⟨p, hp, rfl⟩).trans (le_max_right _ _)
  have hcovB : |cov| ≤ R + 1 := by
    have := abs_add_le (cov - lim p) (lim p)
    rw [sub_add_cancel] at this
    linarith [hcovErr.trans_le (min_le_right _ _)]
  have hdist : dist (γ, lim p) (γ, cov) < δE := by
    simpa [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Real.dist_eq, abs_sub_comm] using
      hcovErr.trans_le (min_le_left _ _)
  simpa [E, lim, cov, Real.dist_eq, abs_sub_comm] using
    hmod (γ, lim p) ⟨abs_le.mp (hΓ γ hγ), by linarith [(abs_le.mp hlimB).1], by linarith [(abs_le.mp hlimB).2]⟩
      (γ, cov) ⟨abs_le.mp (hΓ γ hγ), abs_le.mp hcovB⟩ hdist

end DOZZ.Proofs
