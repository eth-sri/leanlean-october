/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Shifts.Seeds.Reflection
public import DOZZ.ShiftEquations.DualR.Segment
public import DOZZ.ShiftEquations.Shift.FullShift
import DOZZ.ShiftEquations.DualR.SegFactors
import DOZZ.ShiftEquations.Shift.Wrappers
import DOZZ.FourPoint.Crossing.GammaHalfCrossing
import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
import DOZZ.Brownian.Reflection.RtheorAnalytic
import DOZZ.Hypergeom.PhysicalRange

/-!
# Continuation of the dual reflection identity in the first charge
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

private lemma seeds_es3 {γ α₁ α₂ α₃ : ℝ} (hγ : 0 < γ)
    (h₁ : α₁ < Q γ) (h₂ : α₂ < Q γ) (h₃ : α₃ < Q γ) (hs : 0 < sExp γ α₁ α₂ α₃) :
    0 < sExp γ α₁ α₂ α₃ ∧ ExtendedSeiberg3 γ α₁ α₂ α₃ := by
  have h2γ := div_pos two_pos hγ
  have hm := lt_min (show (0 : ℝ) < 4 / γ ^ 2 by positivity) (lt_min (mul_pos h2γ (sub_pos.mpr h₁))
    (lt_min (mul_pos h2γ (sub_pos.mpr h₂)) (mul_pos h2γ (sub_pos.mpr h₃))))
  exact ⟨hs, h₁, h₂, h₃, by linarith⟩

private lemma seeds_shifted_triple {γ α α₂ α₃ : ℝ} (hγ : 0 < γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hα : α < Q γ) (hs : 2 * Q γ + 2 / γ < α + α₂ + α₃) :
    0 < sExp γ (α - 2 / γ) α₂ α₃ ∧ ExtendedSeiberg3 γ (α - 2 / γ) α₂ α₃ :=
  have := div_pos two_pos hγ
  seeds_es3 hγ (by linarith) hα₂ hα₃ (by unfold sExp; exact div_pos (by linarith) hγ)

/-- On the same interval, the reflected triple is ordinary Seiberg. -/
theorem seeds_reflected_triple {γ α α₂ α₃ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hα : α < Q γ) (hs : 2 * Q γ + 2 / γ < α + α₂ + α₃) :
    0 < sExp γ (2 * Q γ - α - 2 / γ) α₂ α₃ ∧ ExtendedSeiberg3 γ (2 * Q γ - α - 2 / γ) α₂ α₃ := by
  have : γ / 2 < 2 / γ := (div_lt_div_iff₀ two_pos hγ).mpr (by nlinarith)
  have : Q γ = γ / 2 + 2 / γ := by unfold Q; ring
  exact seeds_es3 hγ (by linarith) hα₂ hα₃ (by unfold sExp; exact div_pos (by linarith) hγ)

private def ratioC (a b c : ℂ) : ℂ :=
  -(Complex.Gamma c ^ 2 * Complex.Gamma (1 - a) * Complex.Gamma (1 - b) *
      Complex.Gamma (a - c + 1) * Complex.Gamma (b - c + 1)) /
    (Complex.Gamma (2 - c) ^ 2 * Complex.Gamma (c - a) * Complex.Gamma (c - b) *
      Complex.Gamma a * Complex.Gamma b)

/-- **Continuation of the dual reflection identity in the first charge.** -/
theorem dual_reflection_identity_continuation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ)
    (γ μ α₂ α₃ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hnear : ∀ α₁ : ℝ, α₁ < Q γ → Q γ - α₁ < dualSeedWindow γ →
      2 * Q γ + 2 / γ < α₁ + α₂ + α₃ →
      ∀ (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ),
        IsReflectionData P γ α₁ B Z →
        structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ *
            gaussCoefficientRatio (gaussParameterA γ (2 / γ) α₁ α₂ α₃)
              (gaussParameterB γ (2 / γ) α₁ α₂ α₃) (gaussParameterC γ (2 / γ) α₁) =
          reflectionR P γ μ α₁ B Z *
            structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃)
    (α₁ : ℝ) (hα₁ : α₁ < Q γ) (hs : 2 * Q γ + 2 / γ < α₁ + α₂ + α₃)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : IsReflectionData P γ α₁ B Z) :
    structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ *
        gaussCoefficientRatio (gaussParameterA γ (2 / γ) α₁ α₂ α₃)
          (gaussParameterB γ (2 / γ) α₁ α₂ α₃) (gaussParameterC γ (2 / γ) α₁) =
      reflectionR P γ μ α₁ B Z * structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃ := by
  have hγ0 : γ ≠ 0 := hγ.ne'
  have hhalf_lt : γ / 2 < 2 / γ := (div_lt_div_iff₀ two_pos hγ).mpr (by nlinarith)
  set a₀ : ℝ := 2 * Q γ + 2 / γ - α₂ - α₃
  have ha₀ : a₀ < α₁ := by dsimp [a₀]; linarith
  have hint (y : ℝ) (hy : a₀ < y) : 2 * Q γ + 2 / γ < y + α₂ + α₃ := by dsimp [a₀] at hy; linarith
  obtain ⟨V, hVo, hVmem, f, hf, hfeq⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  obtain ⟨B', Z', -, hB', VR, hVRo, hVRmem, fR, -, -, hGd, hGval⟩ :=
    reflectionBarR_holomorphic_representation_of_crossing P X M γ hγ hγ2 hX hM
      (fun μ' α' ε α hμ' h1 h2 h3 h4 h5 =>
        (gammaHalf_crossing P X M γ μ' α' ε α hγ hγ2 hμ' h1 h2 h3 h4 h5 hX hM).2)
      (Ioo a₀ (Q γ)) fun y hy =>
        ⟨by linarith [(dual_seed_charge_lower γ y α₂ α₃ hy.2 hα₂ hα₃ (hint y hy.1)).1], hy.2⟩
  let G : ℂ → ℂ := fun z => rbarCoefficient γ z * fR z
  have hGm : MeromorphicOn G VR := fun z hz => (hGd.analyticAt (hVRo.mem_nhds hz)).meromorphicAt
  let pA (z : ℂ) : ℂ := (gaussParameterA γ (2 / γ) 0 α₂ α₃ : ℂ) + z / γ
  let pB (z : ℂ) : ℂ := (gaussParameterB γ (2 / γ) 0 α₂ α₃ : ℂ) + z / γ
  let pC (z : ℂ) : ℂ := (gaussParameterC γ (2 / γ) 0 : ℂ) + 2 * z / γ
  let sLine (z : ℂ) : Fin 3 → ℂ := ![z - 2 / γ, (α₂ : ℂ), (α₃ : ℂ)]
  let rLine (z : ℂ) : Fin 3 → ℂ := ![2 * (Q γ : ℂ) - z - 2 / γ, (α₂ : ℂ), (α₃ : ℂ)]
  let L (z : ℂ) : ℂ := structureConstantH f γ μ (sLine z) * ratioC (pA z) (pB z) (pC z)
  let R (z : ℂ) : ℂ := reflectionRFromBar γ μ G z * structureConstantH f γ μ (rLine z)
  have hdA : Differentiable ℂ pA := by dsimp [pA]; fun_prop
  have hdB : Differentiable ℂ pB := by dsimp [pB]; fun_prop
  have hdC : Differentiable ℂ pC := by dsimp [pC]; fun_prop
  have hdS : Differentiable ℂ sLine := differentiable_pi.2 fun i => by
    fin_cases i <;> [exact (by dsimp [sLine]; fun_prop); exact differentiable_const _; exact differentiable_const _]
  have hdR : Differentiable ℂ rLine := differentiable_pi.2 fun i => by
    fin_cases i <;> [exact (by dsimp [rLine]; fun_prop); exact differentiable_const _; exact differentiable_const _]
  have hpA (y : ℝ) : pA y = (gaussParameterA γ (2 / γ) y α₂ α₃ : ℂ) := by
    dsimp [pA]; unfold gaussParameterA; push_cast; field_simp; ring
  have hpB (y : ℝ) : pB y = (gaussParameterB γ (2 / γ) y α₂ α₃ : ℂ) := by
    dsimp [pB]; unfold gaussParameterB; push_cast; field_simp; ring
  have hpC (y : ℝ) : pC y = (gaussParameterC γ (2 / γ) y : ℂ) := by
    dsimp [pC]; unfold gaussParameterC; push_cast; field_simp; ring
  have hsL (y : ℝ) : sLine y = complexifyNCharges ![y - 2 / γ, α₂, α₃] := by
    rw [← vec3_ofReal]; dsimp [sLine]; push_cast; rfl
  have hrL (y : ℝ) : rLine y = complexifyNCharges ![2 * Q γ - y - 2 / γ, α₂, α₃] := by
    rw [← vec3_ofReal]; dsimp [rLine]; push_cast; rfl
  have hL_real {y : ℝ} (hyQ : y < Q γ) (hy0 : a₀ < y) :
      L y = ((structureConstant P M γ μ (y - 2 / γ) α₂ α₃ *
        gaussCoefficientRatio (gaussParameterA γ (2 / γ) y α₂ α₃)
          (gaussParameterB γ (2 / γ) y α₂ α₃) (gaussParameterC γ (2 / γ) y) : ℝ) : ℂ) := by
    have hrc (a b c : ℝ) : ratioC a b c = (gaussCoefficientRatio a b c : ℂ) := by
      have h (x : ℝ) : (Real.Gamma x : ℂ) = Complex.Gamma x := (Complex.Gamma_ofReal x).symm
      unfold ratioC gaussCoefficientRatio; push_cast [h]; ring
    dsimp only [L]
    rw [hsL, structureConstantH_complexify P M hμ _ (hfeq _ (seeds_shifted_triple hγ hα₂ hα₃ hyQ (hint y hy0)).2),
      hpA, hpB, hpC, hrc, Complex.ofReal_mul]; rfl
  have hR_real {y : ℝ} (hyQ : y < Q γ) (hy0 : a₀ < y) :
      R y = ((reflectionR P γ μ y (B' y) Z' *
        structureConstant P M γ μ (2 * Q γ - y - 2 / γ) α₂ α₃ : ℝ) : ℂ) := by
    dsimp only [R]
    rw [reflectionRFromBar_ofReal P hμ y (B' y) Z' (hGval y ⟨hy0, hyQ⟩), hrL,
      structureConstantH_complexify P M hμ _ (hfeq _ (seeds_reflected_triple hγ hγ2 hα₂ hα₃ hyQ (hint y hy0)).2),
      Complex.ofReal_mul]; rfl
  have hsne {a : ℝ} (hpos : 0 < sExp γ a α₂ α₃) (n : ℕ) :
      sExpC γ (complexifyNCharges ![a, α₂, α₃]) ≠ -(n : ℂ) := fun hn => by
    rw [sExpC_complexify] at hn
    have hn' : sExp γ a α₂ α₃ = -(n : ℝ) := by
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] using (by exact_mod_cast hn : _ = -(n : ℝ))
    linarith [Nat.cast_nonneg (α := ℝ) n]
  -- Segment setup
  have := dualSeedWindow_pos hγ hγ2
  set m : ℝ := max a₀ (Q γ - dualSeedWindow γ)
  have hmQ : m < Q γ := max_lt (by linarith) (by linarith)
  set x₀ : ℝ := (m + Q γ) / 2
  have hx₀m : m < x₀ := by dsimp [x₀]; linarith
  have hx₀Q : x₀ < Q γ := by dsimp [x₀]; linarith
  have hx₀a : a₀ < x₀ := (le_max_left _ _).trans_lt hx₀m
  have hsegpt {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      a₀ < x₀ + t * (α₁ - x₀) ∧ x₀ + t * (α₁ - x₀) < Q γ :=
    ⟨by linarith [add_mul_sub_lt_of_lt (c := -a₀) (x := -x₀) (y := -α₁) (by linarith) (by linarith) ht0 ht1],
      add_mul_sub_lt_of_lt hx₀Q hα₁ ht0 ht1⟩
  set U : Set ℂ := segC x₀ α₁ ⁻¹' (sLine ⁻¹' V ∩ (rLine ⁻¹' V ∩ VR))
  have hseg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (t : ℂ) ∈ U := by
    obtain ⟨h1, h2⟩ := hsegpt ht0 ht1
    show segC x₀ α₁ (t : ℂ) ∈ sLine ⁻¹' V ∩ (rLine ⁻¹' V ∩ VR)
    rw [segC_ofReal]
    exact ⟨by show sLine _ ∈ V; rw [hsL]; exact hVmem _ (seeds_shifted_triple hγ hα₂ hα₃ h2 (hint _ h1)).2,
      by show rLine _ ∈ V; rw [hrL]; exact hVmem _ (seeds_reflected_triple hγ hγ2 hα₂ hα₃ h2 (hint _ h1)).2,
      hVRmem _ ⟨h1, h2⟩⟩
  have hF₁ : MeromorphicOn (fun t => L (segC x₀ α₁ t)) U := fun t ht => by
    have hr_m : MeromorphicAt (fun z => ratioC (pA z) (pB z) (pC z)) (segC x₀ α₁ t) := by
      have : ∀ g : ℂ → ℂ, AnalyticAt ℂ g (segC x₀ α₁ t) →
          MeromorphicAt (fun z => Complex.Gamma (g z)) (segC x₀ α₁ t) :=
        fun g hg => (meromorphicAt_complexGamma _).comp_analyticAt hg
      have := hdA.analyticAt (segC x₀ α₁ t)
      have := hdB.analyticAt (segC x₀ α₁ t)
      have := hdC.analyticAt (segC x₀ α₁ t)
      have : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) (segC x₀ α₁ t) := analyticAt_const
      have : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) (segC x₀ α₁ t) := analyticAt_const
      dsimp only [ratioC]; fun_prop
    exact ((meromorphicOn_structureConstantH_comp (γ := γ) hVo hf hμ hdS _ ht.1).fun_mul
      hr_m).comp_analyticAt (g := segC x₀ α₁) (analyticAt_segC x₀ α₁ t)
  have hF₂ : MeromorphicOn (fun t => R (segC x₀ α₁ t)) U := fun t ht =>
    ((meromorphicOn_reflectionRFromBar (γ := γ) hμ hGm _ ht.2.2).fun_mul
      (meromorphicOn_structureConstantH_comp (γ := γ) hVo hf hμ hdR _ ht.2.1)).comp_analyticAt
      (g := segC x₀ α₁) (analyticAt_segC x₀ α₁ t)
  have hstart : ∀ᶠ t : ℝ in 𝓝[>] 0, L (segC x₀ α₁ t) = R (segC x₀ α₁ t) := by
    filter_upwards [eventually_segC_mem (b := α₁) isOpen_Ioo (show x₀ ∈ Ioo m (Q γ) from ⟨hx₀m, hx₀Q⟩)]
      with t ⟨hym, hyQ⟩
    have hya := (le_max_left _ _).trans_lt hym
    have hyw : Q γ - (x₀ + t * (α₁ - x₀)) < dualSeedWindow γ := by
      linarith [(le_max_right _ _).trans_lt hym]
    rw [segC_ofReal, hL_real hyQ hya, hR_real hyQ hya, hnear _ hyQ hyw (hint _ hya) _ _ (hB' _ ⟨hya, hyQ⟩)]
  -- Analyticity at t = 1 (z = α₁)
  have hL_an : AnalyticAt ℂ L (α₁ : ℂ) := by
    obtain ⟨hspos, hES⟩ := seeds_shifted_triple hγ hα₂ hα₃ hα₁ hs
    obtain ⟨ha0, hab, hbc, hc1, -⟩ :=
      gauss_physical_parameter_range γ (2 / γ) α₁ α₂ α₃ hγ hγ2 (Or.inr rfl) hs hα₁ hα₂ hα₃
    refine (analyticAt_structureConstantH_comp hVo hf hμ hdS (by rw [hsL]; exact hVmem _ hES)
      (by rw [hsL]; exact hsne hspos)).mul ?_
    have hΓ (g : ℂ → ℂ) (r : ℝ) (hg : AnalyticAt ℂ g α₁) (hgr : g α₁ = r) (hr : 0 < r) :
        AnalyticAt ℂ (fun z => Complex.Gamma (g z)) α₁ :=
      AnalyticAt.comp_of_eq (analyticAt_Gamma_ofReal_pos hr) hg hgr
    have hΓne (g : ℂ → ℂ) (r : ℝ) (hgr : g α₁ = r) (hr : 0 < r) : Complex.Gamma (g α₁) ≠ 0 := by
      rw [hgr]; exact Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.ofReal_re]; exact hr)
    have ha := hpA α₁; have hb := hpB α₁; have hc := hpC α₁
    set a := gaussParameterA γ (2 / γ) α₁ α₂ α₃
    set b := gaussParameterB γ (2 / γ) α₁ α₂ α₃
    set c := gaussParameterC γ (2 / γ) α₁
    have : (fun z => 1 - pA z) α₁ = ((1 - a : ℝ) : ℂ) := by simp [ha]
    have : (fun z => 1 - pB z) α₁ = ((1 - b : ℝ) : ℂ) := by simp [hb]
    have : (fun z => pA z - pC z + 1) α₁ = ((a - c + 1 : ℝ) : ℂ) := by simp [ha, hc]
    have : (fun z => pB z - pC z + 1) α₁ = ((b - c + 1 : ℝ) : ℂ) := by simp [hb, hc]
    have e6 : (fun z => 2 - pC z) α₁ = ((2 - c : ℝ) : ℂ) := by simp [hc]
    have e7 : (fun z => pC z - pA z) α₁ = ((c - a : ℝ) : ℂ) := by simp [ha, hc]
    have e8 : (fun z => pC z - pB z) α₁ = ((c - b : ℝ) : ℂ) := by simp [hb, hc]
    have : (0 : ℝ) < 1 - a := by linarith
    have : (0 : ℝ) < 1 - b := by linarith
    have : (0 : ℝ) < a - c + 1 := by linarith
    have : (0 : ℝ) < b - c + 1 := by linarith
    have p6 : (0 : ℝ) < 2 - c := by linarith
    have p7 : (0 : ℝ) < c - a := by linarith
    have p8 : (0 : ℝ) < c - b := by linarith
    have hb0 : 0 < b := by linarith
    have : 0 < c := by linarith
    have := hdA.analyticAt (α₁ : ℂ); have := hdB.analyticAt (α₁ : ℂ); have := hdC.analyticAt (α₁ : ℂ)
    have : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) α₁ := analyticAt_const
    have : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) α₁ := analyticAt_const
    have := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (pow_ne_zero 2 (hΓne (fun z => 2 - pC z) _ e6 p6))
      (hΓne (fun z => pC z - pA z) _ e7 p7))
      (hΓne (fun z => pC z - pB z) _ e8 p8))
      (hΓne pA _ ha ha0)) (hΓne pB _ hb hb0)
    dsimp only [ratioC]; fun_prop
  have hR_an : AnalyticAt ℂ R (α₁ : ℂ) := by
    obtain ⟨hspos, hES⟩ := seeds_reflected_triple hγ hγ2 hα₂ hα₃ hα₁ hs
    have hre0 : 0 < reflectionExponent γ α₁ := by unfold reflectionExponent; exact div_pos (by linarith) hγ
    have hre1 : reflectionExponent γ α₁ < 1 := by
      unfold reflectionExponent; rw [div_lt_one hγ]; have : Q γ = 2 / γ + γ / 2 := by unfold Q; ring
      linarith
    have hΓ : AnalyticAt ℂ Complex.Gamma (-reflectionExponentC γ (α₁ : ℂ)) := by
      rw [reflectionExponentC_ofReal, ← Complex.ofReal_neg]
      exact analyticAt_Gamma_ofReal_neg_one_lt (by linarith) (by linarith)
    have hp : AnalyticAt ℂ (reflectionExponentC γ) (α₁ : ℂ) := by unfold reflectionExponentC; fun_prop
    have hGa : AnalyticAt ℂ G (α₁ : ℂ) := hGd.analyticAt (hVRo.mem_nhds (hVRmem _ ⟨ha₀, hα₁⟩))
    have := Complex.ofReal_mem_slitPlane.mpr hμ
    have hRbar : AnalyticAt ℂ (reflectionRFromBar γ μ G) (α₁ : ℂ) := by
      unfold reflectionRFromBar; fun_prop
    exact hRbar.mul (analyticAt_structureConstantH_comp hVo hf hμ hdR
      (by rw [hrL]; exact hVmem _ hES) (by rw [hrL]; exact hsne hspos))
  have hmain := eq_at_one_of_segment hseg hF₁ hF₂ hstart
    (AnalyticAt.comp_of_eq hL_an (analyticAt_segC x₀ α₁ 1) (segC_one x₀ α₁))
    (AnalyticAt.comp_of_eq hR_an (analyticAt_segC x₀ α₁ 1) (segC_one x₀ α₁))
  simp only [segC_one] at hmain
  rw [hL_real hα₁ ha₀, hR_real hα₁ ha₀] at hmain
  rw [Complex.ofReal_injective hmain,
    reflectionR_eq_of_isReflectionData P P γ μ α₁ (B' α₁) Z' B Z (hB' _ ⟨ha₀, hα₁⟩) hB]

end DOZZ.Proofs

end
