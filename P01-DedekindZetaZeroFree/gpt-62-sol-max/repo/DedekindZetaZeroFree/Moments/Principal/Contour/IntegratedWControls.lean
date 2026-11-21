module

public import DedekindZetaZeroFree.Moments.Principal.Contour.RightKernelBound
public import DedekindZetaZeroFree.Analysis.Integration.HolomorphicDominatedIntegral

@[expose] public section

set_option maxHeartbeats 1000000

namespace DedekindZetaZeroFree.Quantitative.PrincipalIntegratedWControls

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel
  DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions DedekindZetaZeroFree.Quantitative.PrincipalStripBasicDefinitions
  DedekindZetaZeroFree.Quantitative.PrincipalRightKernelBound31 DedekindZetaZeroFree.Quantitative.EulerDomain
  Set Filter Complex MeasureTheory Metric
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private lemma dom_mem (ξ w z : ℂ) (hξ : Scales.rightLine ≤ ξ.re) (hw : 1 < w.re)
    (hz : z.re = 1 / 6 + Scales.contourOffset) :
    ((ξ, w, z) : Coordinates) ∈ (paddedBox₂ ∩ {p : Coordinates | Scales.rightLine - Scales.contourOffset / 2 < p.1.re} ∩
        {p : Coordinates | 1 / 6 + Scales.contourOffset / 2 < p.2.2.re}) \ {p : Coordinates | p.2.1 = 1} := by
  have hw1 : w ≠ 1 := fun h => by rw [h] at hw; simp at hw
  have hδ : Scales.contourOffset = 1 / 10000000 := rfl
  
  refine ⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · show Scales.rightLine - pad ≤ ξ.re
    unfold pad; linarith
  · show 9 / 10 - pad ≤ w.re
    unfold pad; linarith
  · show 1 / 6 + Scales.contourOffset - pad ≤ z.re
    unfold pad; rw [hz]; linarith
  · show Scales.rightLine - Scales.contourOffset / 2 < ξ.re
    linarith
  · show 1 / 6 + Scales.contourOffset / 2 < z.re
    rw [hz]; linarith
  · exact hw1

set_option maxHeartbeats 4000000 in

private lemma kern_w_diff (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 0 < Z) (ξ z : ℂ)
    (hξ : Scales.rightLine ≤ ξ.re) (hz : z.re = 1 / 6 + Scales.contourOffset) :
    DifferentiableOn ℂ (fun w => kern D u Z ξ w z) {w : ℂ | 1 < w.re} := by
  exact (kern_differentiableOn D u hu Z hZ).comp
    (f := fun w : ℂ => ((ξ, w, z) : Coordinates)) (by fun_prop)
    (fun w hw => dom_mem ξ w z hξ hw hz)

set_option maxHeartbeats 4000000 in

private lemma kern_t_cont (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 0 < Z) (ξ w a : ℂ)
    (hξ : Scales.rightLine ≤ ξ.re) (hw : 1 < w.re) (ha : a.re = 1 / 6 + Scales.contourOffset) :
    Continuous (fun t : ℝ => kern D u Z ξ w (a + (t : ℂ) * I)) := by
  exact (kern_differentiableOn D u hu Z hZ).continuousOn.comp_continuous
    (f := fun t : ℝ => ((ξ, w, a + (t : ℂ) * I) : Coordinates)) (by fun_prop)
    (fun t => dom_mem ξ w _ hξ hw (by simp [ha]))

private lemma hgauss (c : ℝ) : Integrable (fun t : ℝ => Real.exp (-(c + t) ^ 2)) := by
  simpa [add_comm] using (integrable_exp_neg_mul_sq one_pos).comp_add_right c

theorem Iz_w_holo (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (ξ : ℂ)
    (hξ : ξ.re ∈ Icc Scales.rightLine 4) :
    DifferentiableOn ℂ (fun w => Iz D u Z (1 / 6 + Scales.contourOffset) ξ w)
      (comparisonClosedStrip Scales.rightLine 4) := by
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hx1 : Scales.rightLine = 1 + Scales.contourOffset := rfl
  have hδ : Scales.contourOffset = 1 / 10000000 := rfl
  have hξ1 : Scales.rightLine ≤ ξ.re := hξ.1
  obtain ⟨Ck, hCk, hk⟩ := kernel_factor_bound D u hu Z hZ
  obtain ⟨KW, hKW⟩ := D.W1Hat_vertical_decay (Scales.rightLine - Scales.contourOffset / 2) 5
    (by rw [hx1, hδ]; norm_num) 0
  have hv : (0 : ℝ) < 1 / 6 + Scales.contourOffset := by rw [hδ]; norm_num
  obtain ⟨KM, hKM⟩ := D.M_vertical_decay (1 / 6 + Scales.contourOffset) (1 / 6 + Scales.contourOffset) hv le_rfl 0
  let U := {w : ℂ | Scales.rightLine - Scales.contourOffset / 4 < w.re ∧ w.re < 5}
  have hδp : (0 : ℝ) < Scales.contourOffset := by rw [hδ]; norm_num
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)
  have h1U : (1 : ℝ) < Scales.rightLine - Scales.contourOffset / 4 := by linarith
  have hUsub : U ⊆ {w : ℂ | 1 < w.re} := fun w hw => h1U.trans hw.1
  let a : ℝ := 1 / 6 + Scales.contourOffset
  let G (w : ℂ) (t : ℝ) := kern D u Z ξ w ((a : ℂ) + (t : ℂ) * I)
  have hd := HolomorphicDominatedIntegral.differentiableOn_integral_of_dominated (μ := volume)
    hUo (G := G)
    (fun w hw => (kern_t_cont D u hu Z hZ0 ξ w a hξ1 (hUsub hw) (by simp [a])).aestronglyMeasurable)
    (fun t => (kern_w_diff D u hu Z hZ0 ξ ((a : ℂ) + (t : ℂ) * I) hξ1 (by simp [a])).mono hUsub)
    ((hgauss ξ.im).const_mul (Ck * KW * KM)) (by
      intro w hw t
      have hw₁ : Scales.rightLine - Scales.contourOffset / 2 ≤ w.re := by linarith [hw.1]
      have hw₂ := hw.2.le
      let z : ℂ := (a : ℂ) + (t : ℂ) * I
      have hz : z.re = 1 / 6 + Scales.contourOffset := by simp [z, a]
      have hW : ‖D.W1Hat w‖ ≤ KW := by simpa using hKW w hw₁ hw₂
      have hKW0 := (norm_nonneg _).trans hW
      have hM : ‖D.M z‖ ≤ KM := by simpa using hKM z hz.ge hz.le
      refine (hk ξ w z hξ1 hξ.2 hw₁ hw₂ hz).trans ?_
      change _ ≤ Ck * KW * KM * Real.exp (-(ξ.im + t) ^ 2)
      rw [show z.im = t by simp [z]]
      gcongr)
  exact (hd.const_mul ((2 * (Real.pi : ℂ))⁻¹)).mono (fun w ⟨hw₁, hw₂⟩ =>
    ⟨by linarith, by linarith⟩)

theorem Iz_w_decay (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (ξ : ℂ)
    (hξ : ξ.re ∈ Icc Scales.rightLine 4) :
    DecayOn (fun w => Iz D u Z (1 / 6 + Scales.contourOffset) ξ w) Scales.rightLine 4 := by
  intro B hB
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hx1 : Scales.rightLine = 1 + Scales.contourOffset := rfl
  have hδ : Scales.contourOffset = 1 / 10000000 := rfl
  have hξ1 : Scales.rightLine ≤ ξ.re := hξ.1
  obtain ⟨Ck, hCk, hk⟩ := kernel_factor_bound D u hu Z hZ
  have hv : (0 : ℝ) < 1 / 6 + Scales.contourOffset := by rw [hδ]; norm_num
  obtain ⟨KM, hKM⟩ := D.M_vertical_decay (1 / 6 + Scales.contourOffset) (1 / 6 + Scales.contourOffset) hv le_rfl 0
  have hMb : ∀ z : ℂ, z.re = 1 / 6 + Scales.contourOffset → ‖D.M z‖ ≤ KM := fun z hz => by
    have := hKM z (by rw [hz]) (by rw [hz])
    simpa using this
  have hKM0 : 0 ≤ KM := le_trans (norm_nonneg _) (hMb ((1 / 6 + Scales.contourOffset : ℝ) : ℂ) (by simp))
  set I0 : ℝ := ∫ t : ℝ, Real.exp (-(ξ.im + t) ^ 2) with hI0def
  have hI0 : 0 ≤ I0 := integral_nonneg fun t => (Real.exp_pos _).le
  set A : ℝ := ‖(2 * (Real.pi : ℂ))⁻¹‖ * Ck * KM * I0 with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    have := norm_nonneg ((2 * (Real.pi : ℂ))⁻¹)
    exact mul_nonneg (mul_nonneg (mul_nonneg this hCk) hKM0) hI0
  obtain ⟨Cw, hCw⟩ := D.W1Hat_vertical_decay Scales.rightLine 4 (by rw [hx1, hδ]; norm_num) ⌈B⌉₊
  refine ⟨A * Cw, 0, fun x hx y _ => ?_⟩
  show ‖Iz D u Z (1 / 6 + Scales.contourOffset) ξ ((x : ℂ) + (y : ℂ) * I)‖ ≤ (A * Cw) * (1 + |y|) ^ (-B)
  have hwre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have hwim : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  have hxa : Scales.rightLine - Scales.contourOffset / 2 ≤ ((x : ℂ) + (y : ℂ) * I).re := by
    rw [hwre]; linarith [hx.1]
  have hxb : ((x : ℂ) + (y : ℂ) * I).re ≤ 5 := by rw [hwre]; linarith [hx.2]
  have hxb4 : ((x : ℂ) + (y : ℂ) * I).re ≤ 4 := by rw [hwre]; exact hx.2
  have hxa' : Scales.rightLine ≤ ((x : ℂ) + (y : ℂ) * I).re := by rw [hwre]; exact hx.1
  have hIz : ‖Iz D u Z (1 / 6 + Scales.contourOffset) ξ ((x : ℂ) + (y : ℂ) * I)‖ ≤
      A * ‖D.W1Hat ((x : ℂ) + (y : ℂ) * I)‖ := by
    show ‖(2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
      kern D u Z ξ ((x : ℂ) + (y : ℂ) * I) (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ _
    rw [norm_mul]
    have hpt : ∀ t : ℝ, ‖kern D u Z ξ ((x : ℂ) + (y : ℂ) * I)
        (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        (Ck * ‖D.W1Hat ((x : ℂ) + (y : ℂ) * I)‖ * KM) * Real.exp (-(ξ.im + t) ^ 2) := by
      intro t
      have hz : (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I).re = 1 / 6 + Scales.contourOffset := by simp
      have hzi : (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I).im = t := by simp
      have h := hk ξ ((x : ℂ) + (y : ℂ) * I) _ hξ1 hξ.2 hxa hxb hz
      rw [hzi] at h
      have hM := hMb (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I) hz
      have hE := Real.exp_pos (-(ξ.im + t) ^ 2)
      have hCW : 0 ≤ Ck * ‖D.W1Hat ((x : ℂ) + (y : ℂ) * I)‖ :=
        mul_nonneg hCk (norm_nonneg _)
      refine le_trans h ?_
      apply mul_le_mul_of_nonneg_right _ hE.le
      exact mul_le_mul_of_nonneg_left hM hCW
    have hint : ‖∫ t : ℝ, kern D u Z ξ ((x : ℂ) + (y : ℂ) * I)
        (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        ∫ t : ℝ, (Ck * ‖D.W1Hat ((x : ℂ) + (y : ℂ) * I)‖ * KM) * Real.exp (-(ξ.im + t) ^ 2) :=
      norm_integral_le_of_norm_le ((hgauss ξ.im).const_mul _) (Eventually.of_forall hpt)
    rw [integral_const_mul] at hint
    calc ‖(2 * (Real.pi : ℂ))⁻¹‖ * ‖∫ t : ℝ, kern D u Z ξ ((x : ℂ) + (y : ℂ) * I)
          (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ * ((Ck * ‖D.W1Hat ((x : ℂ) + (y : ℂ) * I)‖ * KM) * I0) :=
          mul_le_mul_of_nonneg_left hint (norm_nonneg _)
      _ = A * ‖D.W1Hat ((x : ℂ) + (y : ℂ) * I)‖ := by rw [hA]; ring
  have hs : 0 < (1 + |y|) ^ ⌈B⌉₊ := by positivity
  have hW : ‖D.W1Hat ((x : ℂ) + (y : ℂ) * I)‖ ≤ Cw * ((1 + |y|) ^ ⌈B⌉₊)⁻¹ := by
    have h := hCw _ hxa' hxb4
    rw [hwim] at h
    rw [← div_eq_mul_inv, le_div_iff₀ hs, mul_comm]
    exact h
  have hCw0 : 0 ≤ Cw := le_trans (mul_nonneg (by positivity) (norm_nonneg _))
    (hCw _ hxa' hxb4)
  have hb : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hpow : ((1 + |y|) ^ ⌈B⌉₊)⁻¹ ≤ (1 + |y|) ^ (-B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith [abs_nonneg y])]
    exact Real.rpow_le_rpow_of_exponent_le hb (by linarith [Nat.le_ceil B])
  calc ‖Iz D u Z (1 / 6 + Scales.contourOffset) ξ ((x : ℂ) + (y : ℂ) * I)‖
      ≤ A * ‖D.W1Hat ((x : ℂ) + (y : ℂ) * I)‖ := hIz
    _ ≤ A * (Cw * ((1 + |y|) ^ ⌈B⌉₊)⁻¹) := mul_le_mul_of_nonneg_left hW hA0
    _ ≤ A * (Cw * (1 + |y|) ^ (-B)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hCw0) hA0
    _ = (A * Cw) * (1 + |y|) ^ (-B) := by ring

end

end DedekindZetaZeroFree.Quantitative.PrincipalIntegratedWControls
