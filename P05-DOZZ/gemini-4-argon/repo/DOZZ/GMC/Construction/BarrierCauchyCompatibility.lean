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

/-- For any choices of the two admissible regularization families, the finite coarse Gaussian
rectangle sees the same limiting two-root tilt shift. The first family supplies the coarse
barrier coordinates; compatibility transfers the fixed-coarse limit for every `Z` root to the
same kernel as for `Y`. -/
theorem compatible_finite_coarse_two_root_shift_tendsto_uniformly
    {Ω α ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (_hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (S : Set α) (rootX rootY : α → ℂ)
    (hrootX : ∀ a ∈ S, rootX a ∈ K) (hrootY : ∀ a ∈ S, rootY a ∈ K)
    (scale : ι → ℕ) (center : α → ι → ℂ)
    (hcenter : ∀ a ∈ S, ∀ i, center a i ∈ K)
    (hscale : ∀ i, Real.exp (-(scale i : ℝ)) ≤ min ε₀ ε₁)
    (b₁ b₂ : Bool) (Γ : Set ℝ) B (hB : 0 ≤ B)
    (hΓ : ∀ γ ∈ Γ, |γ| ≤ B) :
    ∃ coarseKernel : ℕ → ℂ → ℂ → ℝ, ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε ε' : ℝ,
        0 < ε → ε ≤ min δ (min ε₀ ε₁) →
        0 < ε' → ε' ≤ min δ (min ε₀ ε₁) →
        ∀ γ ∈ Γ, ∀ a ∈ S, ∀ i,
          |γ * gaussianCovariance P
                (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
                (fun ω => if b₁ then Y ω ε (rootX a) else Z ω ε (rootX a)) +
            γ * gaussianCovariance P
                (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
                (fun ω => if b₂ then Y ω ε' (rootY a) else Z ω ε' (rootY a)) -
            (γ * coarseKernel (scale i) (rootX a) (center a i) +
              γ * coarseKernel (scale i) (rootY a) (center a i))| < η := by
  rcases hYZ with ⟨_hJoint, _hCov, _hCoarse, _hOffDiagonal, hFixedCoarse⟩
  obtain ⟨coarseKernel, hfixedY⟩ := hY.fixedCoarseLimit
  refine ⟨coarseKernel, ?_⟩
  intro η hη
  let η' : ℝ := η / (8 * (B + 1))
  have hη' : 0 < η' := by dsimp [η']; positivity
  have hcovComm : ∀ (f g : Ω → ℝ),
      gaussianCovariance P f g = gaussianCovariance P g f := by
    intro f g
    unfold gaussianCovariance
    apply integral_congr_ae
    exact ae_of_all P (fun ω => by ring)
  have hrootCov (i : ι) (root coarse : α → ℂ)
      (hroot : ∀ a ∈ S, root a ∈ K) (hcoarse : ∀ a ∈ S, coarse a ∈ K) :
      ∃ δi : ℝ, 0 < δi ∧ ∀ ε : ℝ, 0 < ε →
        ε ≤ min δi (min ε₀ ε₁) → ∀ b : Bool, ∀ a ∈ S,
        |gaussianCovariance P
            (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
            (fun ω => if b then Y ω ε (root a) else Z ω ε (root a)) -
          coarseKernel (scale i) (root a) (coarse a)| < 2 * η' := by
    obtain ⟨δY, hδY, hYlimit⟩ := hfixedY K hK hKU (scale i)
      (le_trans (hscale i) (min_le_left _ _)) η' hη'
    obtain ⟨δZ, hδZ, hZlimit⟩ := hFixedCoarse K hK hKU (scale i)
      (hscale i) η' hη'
    let δi : ℝ := min δY δZ
    refine ⟨δi, (lt_min hδY hδZ), ?_⟩
    intro ε hε hεcut b a ha
    have hεY : ε ≤ min δY ε₀ := by
      apply le_min
      · exact (hεcut.trans (min_le_left _ _)).trans (min_le_left _ _)
      · exact le_trans (hεcut.trans (min_le_right _ _)) (min_le_left _ _)
    have hεZ : ε ≤ min δZ (min ε₀ ε₁) := by
      apply le_min
      · exact (hεcut.trans (min_le_left _ _)).trans (min_le_right _ _)
      · exact hεcut.trans (min_le_right _ _)
    have hYlim' : |gaussianCovariance P
          (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
          (fun ω => Y ω ε (root a)) - coarseKernel (scale i) (root a) (coarse a)| < η' := by
      simpa only [hcovComm] using (hYlimit ε hε hεY (root a) (hroot a ha) (coarse a) (hcoarse a ha))
    cases b
    · have hZlim := hZlimit ε hε hεZ (root a) (hroot a ha) (coarse a) (hcoarse a ha)
      have : |gaussianCovariance P
            (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
            (fun ω => Z ω ε (root a)) - gaussianCovariance P
              (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
              (fun ω => Y ω ε (root a))| < η' := by
        simpa only [hcovComm] using hZlim
      calc
        |gaussianCovariance P (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
              (fun ω => Z ω ε (root a)) - coarseKernel (scale i) (root a) (coarse a)|
            = |(gaussianCovariance P
                  (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
                  (fun ω => Z ω ε (root a)) - gaussianCovariance P
                    (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
                    (fun ω => Y ω ε (root a))) +
                (gaussianCovariance P
                  (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
                  (fun ω => Y ω ε (root a)) - coarseKernel (scale i) (root a) (coarse a))| := by
                    congr 1
                    ring
        _ ≤ |gaussianCovariance P
                (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
                (fun ω => Z ω ε (root a)) - gaussianCovariance P
                  (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
                  (fun ω => Y ω ε (root a))| +
              |gaussianCovariance P
                  (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
                  (fun ω => Y ω ε (root a)) - coarseKernel (scale i) (root a) (coarse a)| :=
                    abs_add_le _ _
        _ < 2 * η' := by linarith
    · exact lt_trans hYlim' (by linarith [hη'])
  have hlocal (i : ι) : ∃ δi : ℝ, 0 < δi ∧
      ∀ ε ε' : ℝ, 0 < ε → ε ≤ min δi (min ε₀ ε₁) →
        0 < ε' → ε' ≤ min δi (min ε₀ ε₁) →
        ∀ γ ∈ Γ, ∀ a ∈ S,
          |γ * gaussianCovariance P
                (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
                (fun ω => if b₁ then Y ω ε (rootX a) else Z ω ε (rootX a)) +
            γ * gaussianCovariance P
                (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
                (fun ω => if b₂ then Y ω ε' (rootY a) else Z ω ε' (rootY a)) -
            (γ * coarseKernel (scale i) (rootX a) (center a i) +
              γ * coarseKernel (scale i) (rootY a) (center a i))| < η := by
    obtain ⟨δ₁, hδ₁, hfirst⟩ := hrootCov i rootX (fun a => center a i)
      hrootX (fun a ha => hcenter a ha i)
    obtain ⟨δ₂, hδ₂, hsecond⟩ := hrootCov i rootY (fun a => center a i)
      hrootY (fun a ha => hcenter a ha i)
    let δi : ℝ := min δ₁ δ₂
    refine ⟨δi, (lt_min hδ₁ hδ₂), ?_⟩
    intro ε ε' hε hεcut hε' hε'cut γ hγ a ha
    have hεfirst : ε ≤ min δ₁ (min ε₀ ε₁) := by
      apply le_min
      · exact (hεcut.trans (min_le_left _ _)).trans (min_le_left _ _)
      · exact hεcut.trans (min_le_right _ _)
    have hε'second : ε' ≤ min δ₂ (min ε₀ ε₁) := by
      apply le_min
      · exact (hε'cut.trans (min_le_left _ _)).trans (min_le_right _ _)
      · exact hε'cut.trans (min_le_right _ _)
    have := hΓ γ hγ
    let c₁ := gaussianCovariance P
      (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
      (fun ω => if b₁ then Y ω ε (rootX a) else Z ω ε (rootX a))
    let c₂ := gaussianCovariance P
      (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
      (fun ω => if b₂ then Y ω ε' (rootY a) else Z ω ε' (rootY a))
    let k₁ := coarseKernel (scale i) (rootX a) (center a i)
    let k₂ := coarseKernel (scale i) (rootY a) (center a i)
    have hsumBound :
        |γ * (c₁ - k₁)| + |γ * (c₂ - k₂)| ≤
          4 * B * η' := by
      calc
        _ = |γ| * |c₁ - k₁| + |γ| * |c₂ - k₂| := by rw [abs_mul, abs_mul]
        _ ≤ |γ| * (2 * η') + |γ| * (2 * η') := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left (show |c₁ - k₁| < 2 * η' by simpa [c₁, k₁] using (hfirst ε hε hεfirst b₁ a ha)).le (abs_nonneg γ))
                (mul_le_mul_of_nonneg_left (show |c₂ - k₂| < 2 * η' by simpa [c₂, k₂] using (hsecond ε' hε' hε'second b₂ a ha)).le (abs_nonneg γ))
        _ ≤ B * (2 * η') + B * (2 * η') := by
              gcongr
        _ = 4 * B * η' := by ring
    calc
      |γ * c₁ + γ * c₂ - (γ * k₁ + γ * k₂)|
          = |γ * (c₁ - k₁) + γ * (c₂ - k₂)| := by congr 1; ring
      _ ≤ |γ * (c₁ - k₁)| + |γ * (c₂ - k₂)| := (abs_add_le _ _)
      _ ≤ 4 * B * η' := hsumBound
      _ < η := (by rw [← (show η' * (8 * (B + 1)) = η by dsimp [η']; field_simp)]; nlinarith [mul_pos hη' (show 0 < B + 2 by linarith)])

  choose δi hδi hshift using hlocal
  obtain ⟨i₀, hmin⟩ := Finite.exists_min (fun i : ι => δi i)
  let δ : ℝ := δi i₀
  refine ⟨δ, (hδi i₀), ?_⟩
  intro ε ε' hε hεcut hε' hε'cut γ hγ a ha i
  have hδle := hmin i
  have hεcut' : ε ≤ min (δi i) (min ε₀ ε₁) := by
    apply le_min
    · exact (hεcut.trans (min_le_left _ _)).trans hδle
    · exact hεcut.trans (min_le_right _ _)
  have hε'cut' : ε' ≤ min (δi i) (min ε₀ ε₁) := by
    apply le_min
    · exact (hε'cut.trans (min_le_left _ _)).trans hδle
    · exact hε'cut.trans (min_le_right _ _)
  exact hshift i ε ε' hε hεcut' hε' hε'cut' γ hγ a ha

/-- The finite-barrier rectangle probabilities for any mixed pair of regularization families
converge uniformly to one common coarse limit. This is the off-diagonal finite-scale convergence
input to the growing-barrier mixed-cutoff Cauchy argument. -/
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
  let q : α → Fin n → ℝ × ℂ := fun a i =>
    (Real.exp (-(scale i : ℝ)), center a i)
  let W : α → Ω → Fin n → ℝ := fun a ω i => Y ω (q a i).1 (q a i).2
  have hW : ∀ a ∈ S, IsCenteredJointlyGaussian P (W a) := by
    intro a ha
    change IsCenteredJointlyGaussian P
      (fun ω i => Y ω (q a i).1 (q a i).2)
    apply hY.gaussian n (q a)
    intro i
    exact ⟨Real.exp_pos _, le_trans (hscale i) (min_le_left _ _)⟩
  have hshift := compatible_finite_coarse_two_root_shift_tendsto_uniformly
    P U dens ε₀ ε₁ Y Z hY hZ hYZ K hK hKU S rootX rootY hrootX hrootY
    scale center hcenter hscale b₁ b₂ Γ B hB hΓ
  obtain ⟨coarseKernel, hshift⟩ := hshift
  let c : ℝ → ℝ → ℝ → α → Fin n → ℝ := fun ε ε' γ a i =>
    γ * gaussianCovariance P (fun ω => W a ω i)
        (fun ω => if b₁ then Y ω ε (rootX a) else Z ω ε (rootX a)) +
      γ * gaussianCovariance P (fun ω => W a ω i)
        (fun ω => if b₂ then Y ω ε' (rootY a) else Z ω ε' (rootY a))
  let d : ℝ → α → Fin n → ℝ := fun γ a i =>
    γ * coarseKernel (scale i) (rootX a) (center a i) +
      γ * coarseKernel (scale i) (rootY a) (center a i)
  have hcoord : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε ε' : ℝ, 0 < ε → ε ≤ δ → 0 < ε' → ε' ≤ δ →
        ∀ γ ∈ Γ, ∀ a ∈ S, ∀ i, |c ε ε' γ a i - d γ a i| < η := by
    intro η hη
    obtain ⟨δ₀, hδ₀, hshift'⟩ := hshift η hη
    let δ : ℝ := min δ₀ (min ε₀ ε₁)
    refine ⟨δ, (lt_min hδ₀ (lt_min hY.cutoffPositive hZ.cutoffPositive)), ?_⟩
    intro ε ε' hε hεcut hε' hε'cut γ hγ a ha i
    have hε'cut' : ε ≤ min δ₀ (min ε₀ ε₁) := by
      apply le_min
      · exact hεcut.trans (min_le_left _ _)
      · exact hεcut.trans (min_le_right _ _)
    have hε''cut' : ε' ≤ min δ₀ (min ε₀ ε₁) := by
      apply le_min
      · exact hε'cut.trans (min_le_left _ _)
      · exact hε'cut.trans (min_le_right _ _)
    simpa [c, d, W, q] using (hshift' ε ε' hε hε'cut' hε' hε''cut' γ hγ a ha i)
  refine ⟨coarseKernel, ?_⟩
  intro η hη
  obtain ⟨δ₀, hδ₀, hprob'⟩ := (finite_gaussian_rectangle_probability_two_shift_tendsto_uniformly P Γ S W hW barrier hv c d hcoord) η hη
  let δ : ℝ := min δ₀ (min ε₀ ε₁)
  refine ⟨δ, (lt_min hδ₀ (lt_min hY.cutoffPositive hZ.cutoffPositive)), ?_⟩
  intro ε ε' hε hεcut hε' hε'cut γ hγ a ha
  simpa [W, q, c, d] using (hprob' ε ε' hε (by exact (hεcut.trans (min_le_left δ (min ε₀ ε₁))).trans (min_le_left δ₀ (min ε₀ ε₁))) hε' (by exact (hε'cut.trans (min_le_left δ (min ε₀ ε₁))).trans (min_le_left δ₀ (min ε₀ ε₁))) γ hγ a ha)

/-- On a compact separated chart, every mixed Y/Z off-diagonal covariance has the same limit as
the Y/Y covariance. The two compatibility convergence clauses cover YZ and ZZ directly; the ZY
case follows by covariance symmetry. -/
theorem compatible_mixed_off_diagonal_covariance_tendsto_uniformly
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (_hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (s : ℝ) (hs : 0 < s)
    (b₁ b₂ : Bool) :
    ∃ H : ℂ → ℂ → ℝ, ContinuousOn (Function.uncurry H) (U ×ˢ U) ∧
      ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
        ∀ ε ε' : ℝ, 0 < ε → ε ≤ min δ (min ε₀ ε₁) →
          0 < ε' → ε' ≤ min δ (min ε₀ ε₁) →
          ∀ x ∈ K, ∀ y ∈ K, s ≤ ‖x - y‖ →
            |gaussianCovariance P
                (fun ω => if b₁ then Y ω ε x else Z ω ε x)
                (fun ω => if b₂ then Y ω ε' y else Z ω ε' y) -
              (Real.log (1 / ‖x - y‖) + H x y)| < η := by
  rcases hYZ with ⟨_hJoint, _hCov, _hCoarse, hOffDiagonal, _hFixedCoarse⟩
  obtain ⟨H, hH, hYoff⟩ := hY.offDiagonalLimit
  refine ⟨H, hH, ?_⟩
  intro η hη
  let η' : ℝ := η / 3
  have hη' : 0 < η' := by dsimp [η']; positivity
  obtain ⟨δY, hδY, hYclose⟩ := hYoff K hK hKU s hs η' hη'
  obtain ⟨δC, hδC, hCclose⟩ := hOffDiagonal K hK hKU s hs η' hη'
  let δ : ℝ := min δY δC
  have hcovComm (f g : Ω → ℝ) :
      gaussianCovariance P f g = gaussianCovariance P g f := by
    unfold gaussianCovariance
    apply integral_congr_ae
    exact ae_of_all P (fun ω => by ring)
  refine ⟨δ, (lt_min hδY hδC), ?_⟩
  intro ε ε' hε hεcut hε' hε'cut x hx y hy hxy
  have hεY : ε ≤ min δY ε₀ := by
    apply le_min
    · exact (hεcut.trans (min_le_left _ _)).trans (min_le_left _ _)
    · exact le_trans (hεcut.trans (min_le_right _ _)) (min_le_left _ _)
  have hε'Y : ε' ≤ min δY ε₀ := by
    apply le_min
    · exact (hε'cut.trans (min_le_left _ _)).trans (min_le_left _ _)
    · exact le_trans (hε'cut.trans (min_le_right _ _)) (min_le_left _ _)
  have hεC : ε ≤ min δC (min ε₀ ε₁) := by
    apply le_min
    · exact (hεcut.trans (min_le_left _ _)).trans (min_le_right _ _)
    · exact hεcut.trans (min_le_right _ _)
  have hε'C : ε' ≤ min δC (min ε₀ ε₁) := by
    apply le_min
    · exact (hε'cut.trans (min_le_left _ _)).trans (min_le_right _ _)
    · exact hε'cut.trans (min_le_right _ _)
  have hbase := hYclose ε ε' hε hεY hε' hε'Y x hx y hy hxy
  have hcombine {A B L : ℝ} (hAB : |A - B| < η') (hBL : |B - L| < η') :
      |A - L| < η := by
    calc
      |A - L| = |(A - B) + (B - L)| := by congr 1; ring
      _ ≤ |A - B| + |B - L| := abs_add_le _ _
      _ < η' + η' := add_lt_add hAB hBL
      _ < η := by dsimp [η']; linarith
  cases b₁ <;> cases b₂
  · have hcomp := hCclose ε ε' hε hεC hε' hε'C x hx y hy hxy
    exact hcombine hcomp.2 hbase
  · have hcomp := hCclose ε' ε hε' hε'C hε hεC y hy x hx
      (by simpa [norm_sub_rev] using hxy)
    exact hcombine (show |gaussianCovariance P (fun ω => Z ω ε x) (fun ω => Y ω ε' y) - gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω ε' y)| < η' by simpa only [hcovComm] using hcomp.1) hbase
  · have hcomp := hCclose ε ε' hε hεC hε' hε'C x hx y hy hxy
    exact hcombine hcomp.1 hbase
  · exact lt_trans hbase (by dsimp [η']; linarith)

/-- The mixed two-root Wick prefactor converges uniformly to the common GMC kernel on compact
separated spatial sets, for all four choices of Y/Z families and bounded charges. -/
theorem compatible_mixed_off_diagonal_wick_factor_tendsto_uniformly
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) U (dens : ℂ → ℝ) ε₀ ε₁
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
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
  obtain ⟨H, hH, hcovlim⟩ := compatible_mixed_off_diagonal_covariance_tendsto_uniformly
    P U dens ε₀ ε₁ Y Z hY hZ hYZ K hK hKU s hs b₁ b₂
  refine ⟨H, hH, ?_⟩
  intro η hη
  let lim : ℂ × ℂ → ℝ := fun p => Real.log (1 / ‖p.1 - p.2‖) + H p.1 p.2
  have hsep (p : ℂ × ℂ) (hp : p ∈ S) : 0 < ‖p.1 - p.2‖ :=
    lt_of_lt_of_le hs (hSxy p hp).2.2
  have hinv : ContinuousOn (fun p : ℂ × ℂ => (‖p.1 - p.2‖)⁻¹) S :=
    (show Continuous fun p : ℂ × ℂ => ‖p.1 - p.2‖ by fun_prop).continuousOn.inv₀ (fun p hp => ne_of_gt (hsep p hp))
  obtain ⟨R₀, hR₀⟩ := hS.bddAbove_image ((show ContinuousOn lim S by exact (ContinuousOn.comp' Real.continuousOn_log (by simpa [one_div] using hinv) (by intro p hp; rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt (one_div_pos.mpr (hsep p hp)))).add (hH.mono (by intro p hp; exact Set.mem_prod.mpr ⟨hKU (hSxy p hp).1, hKU (hSxy p hp).2.1⟩))).abs)
  let R : ℝ := max 0 R₀
  have hlimBound (p : ℂ × ℂ) (hp : p ∈ S) : |lim p| ≤ R := by
    exact (hR₀ ⟨p, hp, rfl⟩).trans (le_max_right _ _)
  let T : Set ℝ := Set.Icc (-(R + 1)) (R + 1)
  let E : ℝ × ℝ → ℝ := fun z => Real.exp (z.1 ^ 2 * z.2)
  obtain ⟨δE, hδE, hmod⟩ := Metric.uniformContinuousOn_iff.mp ((isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous (show Continuous E by fun_prop).continuousOn) η hη
  let ηcov : ℝ := min δE 1
  obtain ⟨δ, hδ, hcov⟩ := hcovlim ηcov (lt_min hδE one_pos)
  refine ⟨δ, hδ, ?_⟩
  intro ε ε' hε hεcut hε' hε'cut γ hγ p hp
  have hpK := hSxy p hp
  have hcovErr : |gaussianCovariance P
        (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
        (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2) - lim p| < ηcov :=
    hcov ε ε' hε hεcut hε' hε'cut p.1 hpK.1 p.2 hpK.2.1 hpK.2.2
  have hgammaD : γ ∈ (Set.Icc (-B) B) := by
    change -B ≤ γ ∧ γ ≤ B
    exact abs_le.mp (hΓ γ hγ)
  have hlimD : lim p ∈ T := by
    change -(R + 1) ≤ lim p ∧ lim p ≤ R + 1
    have := abs_le.mp (hlimBound p hp)
    constructor <;> linarith [(le_max_left _ _ : 0 ≤ R)]
  have hcovD : gaussianCovariance P
      (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
      (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2) ∈ T := by
    change -(R + 1) ≤ gaussianCovariance P
        (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
        (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2) ∧
      gaussianCovariance P (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
        (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2) ≤ R + 1
    have hcovAbs : |gaussianCovariance P
        (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
        (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2)| ≤ R + 1 := by
      calc
        _ = |(gaussianCovariance P
              (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
              (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2) - lim p) + lim p| := by
                congr 1
                ring
        _ ≤ |gaussianCovariance P
              (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
              (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2) - lim p| + |lim p| :=
                abs_add_le _ _
        _ ≤ R + 1 := by linarith [hlimBound p hp, hcovErr.le, (min_le_right _ _ : ηcov ≤ 1)]
    exact abs_le.mp hcovAbs
  simpa [E, lim, Real.dist_eq, abs_sub_comm] using (hmod (γ, lim p) (Set.mem_prod.mpr ⟨hgammaD, hlimD⟩) (γ, gaussianCovariance P (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1) (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2)) (Set.mem_prod.mpr ⟨hgammaD, hcovD⟩) (by simpa [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using (by simpa [Real.dist_eq, abs_sub_comm] using (lt_of_lt_of_le hcovErr (min_le_left _ _)))))


end DOZZ.Proofs
