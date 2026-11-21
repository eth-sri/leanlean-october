module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalIncompleteSeries
public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.SpectralFunction
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRowCount
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.NormalConvergence
public import DedekindZetaZeroFree.Moments.Principal.Contour.Kernel

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalResidueFormulas

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel
  DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem zetaSCont_eq_zetaS (s : ℂ) (hs : 1 < s.re) : D.zetaSCont s = D.zetaS s :=
  D.recipe.L_eq_zeta s hs

theorem zetaSCont_analytic :
    AnalyticOnNhd ℂ D.zetaSCont ({s : ℂ | 0 < s.re} \ {1}) := by
  have hopen : IsOpen ({s : ℂ | 0 < s.re} \ {1}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  refine DifferentiableOn.analyticOnNhd ?_ hopen
  have hL : DifferentiableOn ℂ D.recipe.continuation.L ({s : ℂ | 0 < s.re} \ {1}) :=
    D.recipe.continuation.L_holo.mono (fun s hs => ⟨hs.1, hs.2⟩)
  have hE : Differentiable ℂ (fun s : ℂ => ∏ v ∈ D.recipe.A.Sf,
      (1 - D.recipe.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))) := by
    intro s
    apply DifferentiableAt.fun_finsetProd
    intro v _
    unfold comparisonRealPower
    fun_prop
  exact hL.mul hE.differentiableOn

private theorem eqOn_punctured {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f ({s : ℂ | 0 < s.re} \ {1}))
    (hg : AnalyticOnNhd ℂ g ({s : ℂ | 0 < s.re} \ {1}))
    (h : ∀ s : ℂ, 1 < s.re → f s = g s) (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    f s = g s := by
  have step : ∀ T : Set ℂ, IsPreconnected T → T ⊆ ({s : ℂ | 0 < s.re} \ {1}) → ∀ z₀ ∈ T,
      f =ᶠ[nhds z₀] g → ∀ s ∈ T, f s = g s :=
    fun T hT hsub z₀ hz₀ hev s hs =>
      (hf.mono hsub).eqOn_of_preconnected_of_eventuallyEq (hg.mono hsub) hT hz₀ hev hs
  have hop1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re

  have hT2o : IsOpen ({c : ℂ | 0 < c.re} ∩ {c : ℂ | 0 < c.im}) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have h2 : ∀ s ∈ ({c : ℂ | 0 < c.re} ∩ {c : ℂ | 0 < c.im}), f s = g s := by
    refine step _ ((convex_halfSpace_re_gt (0 : ℝ)).inter
      (convex_halfSpace_im_gt (0 : ℝ))).isPreconnected ?_ ((2 : ℂ) + Complex.I) ?_ ?_
    · rintro x ⟨hx1, hx2⟩
      refine ⟨hx1, ?_⟩
      rintro rfl
      simp at hx2
    · exact ⟨by norm_num, by norm_num⟩
    · have hm : {z : ℂ | 1 < z.re} ∈ nhds ((2 : ℂ) + Complex.I) :=
        hop1.mem_nhds (by norm_num)
      exact Filter.eventually_of_mem hm (fun z hz => h z hz)
  have h3 : ∀ s ∈ ({c : ℂ | 0 < c.re} ∩ {c : ℂ | c.im < 0}), f s = g s := by
    refine step _ ((convex_halfSpace_re_gt (0 : ℝ)).inter
      (convex_halfSpace_im_lt (0 : ℝ))).isPreconnected ?_ ((2 : ℂ) - Complex.I) ?_ ?_
    · rintro x ⟨hx1, hx2⟩
      refine ⟨hx1, ?_⟩
      rintro rfl
      simp at hx2
    · exact ⟨by norm_num, by norm_num⟩
    · have hm : {z : ℂ | 1 < z.re} ∈ nhds ((2 : ℂ) - Complex.I) :=
        hop1.mem_nhds (by norm_num)
      exact Filter.eventually_of_mem hm (fun z hz => h z hz)
  have h4 : ∀ s ∈ ({c : ℂ | 0 < c.re} ∩ {c : ℂ | c.re < 1}), f s = g s := by
    refine step _ ((convex_halfSpace_re_gt (0 : ℝ)).inter
      (convex_halfSpace_re_lt (1 : ℝ))).isPreconnected ?_ ((1 / 2 : ℂ) + Complex.I) ?_ ?_
    · rintro x ⟨hx1, hx2⟩
      refine ⟨hx1, ?_⟩
      rintro rfl
      simp at hx2
    · refine ⟨?_, ?_⟩
      · show (0 : ℝ) < ((1 / 2 : ℂ) + Complex.I).re
        norm_num
      · show ((1 / 2 : ℂ) + Complex.I).re < (1 : ℝ)
        norm_num
    · have hm : ({c : ℂ | 0 < c.re} ∩ {c : ℂ | 0 < c.im}) ∈ nhds ((1 / 2 : ℂ) + Complex.I) :=
        hT2o.mem_nhds ⟨by show (0 : ℝ) < ((1 / 2 : ℂ) + Complex.I).re; norm_num,
          by show (0 : ℝ) < ((1 / 2 : ℂ) + Complex.I).im; norm_num⟩
      exact Filter.eventually_of_mem hm (fun z hz => h2 z hz)
  rcases lt_trichotomy s.im 0 with him | him | him
  · exact h3 s ⟨hs, him⟩
  · rcases lt_trichotomy s.re 1 with hre | hre | hre
    · exact h4 s ⟨hs, hre⟩
    · exact absurd (Complex.ext (by simpa using hre) (by simpa using him)) hs1
    · exact h s hre
  · exact h2 s ⟨hs, him⟩

private theorem LpsiRaw_principal (u : D.Row) (hu : u.u = 1) (s : ℂ) :
    D.LpsiRaw u s = InitialSeparatedEuler.zetaS D.recipe.A s := by
  unfold FixedData.LpsiRaw MaskedHeckeMeromorphic.incompleteL
  have hu' : u.toFrequency.u = 1 := hu
  have hsupport : Function.support (fun I : Ideal (𝓞 F) =>
      MaskedHeckeMeromorphic.coefficient u.toFrequency MaskedHeckeMeromorphic.Row.plus I *
        (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
      {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ D.recipe.A.cS = ⊤} := by
    intro I hI
    by_contra hn
    change ¬ (I ≠ ⊥ ∧ I ⊔ D.recipe.A.cS = ⊤) at hn
    apply hI
    simp [MaskedHeckeMeromorphic.coefficient, FrequencyCharacterMasks.plusCoefficient, hn]
  rw [← tsum_subtype_eq_of_support_subset hsupport]
  unfold InitialSeparatedEuler.zetaS
  apply tsum_congr
  intro I
  simp [MaskedHeckeMeromorphic.coefficient, FrequencyCharacterMasks.plusCoefficient,
    I.property.1, I.property.2, FrequencyCharacterMasks.plusExteriorCoefficient, hu']

private theorem LlamRaw_principal (u : D.Row) (hu : u.u = 1) (s : ℂ) :
    D.LlamRaw u s = InitialSeparatedEuler.zetaS D.recipe.A s := by
  unfold FixedData.LlamRaw MaskedHeckeMeromorphic.incompleteL
  have hu' : u.toFrequency.u = 1 := hu
  have hsupport : Function.support (fun I : Ideal (𝓞 F) =>
      MaskedHeckeMeromorphic.coefficient u.toFrequency MaskedHeckeMeromorphic.Row.minus I *
        (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
      {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ D.recipe.A.cS = ⊤} := by
    intro I hI
    by_contra hn
    change ¬ (I ≠ ⊥ ∧ I ⊔ D.recipe.A.cS = ⊤) at hn
    apply hI
    simp [MaskedHeckeMeromorphic.coefficient, FrequencyCharacterMasks.minusCoefficient,
      FrequencyCharacterMasks.plusCoefficient, hn]
  rw [← tsum_subtype_eq_of_support_subset hsupport]
  unfold InitialSeparatedEuler.zetaS
  apply tsum_congr
  intro I
  have hη := D.recipe.probe.principal I.val I.property.1 (PrincipalProbeConstruction.Inputs.exterior_coprime D.recipe.A I)
  simp [MaskedHeckeMeromorphic.coefficient, FrequencyCharacterMasks.minusCoefficient,
    FrequencyCharacterMasks.plusCoefficient, I.property.1, I.property.2,
    FrequencyCharacterMasks.plusExteriorCoefficient, hu', hη]

theorem q_principal (u : D.Row) (hu : u.u = 1) : D.q u = 1 := by
  rw [ActualRowCount.eq_principalRow D hu]; exact ActualRowCount.q_principalRow D

theorem Lpsi_principal_eq (u : D.Row) (hu : u.u = 1) (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    D.Lpsi u s = D.zetaSCont s := by
  have h1 : ∀ s : ℂ, 1 < s.re → D.Lpsi u s = D.zetaSCont s := by
    intro s hs
    rw [D.Lpsi_eq_raw u s hs, LpsiRaw_principal D u hu s]
    exact (zetaSCont_eq_zetaS D s hs).symm
  exact eqOn_punctured (D.Lpsi_analyticOnNhd u) (zetaSCont_analytic D)
    h1 s hs hs1

theorem Llam_principal_eq (u : D.Row) (hu : u.u = 1) (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    D.Llam u s = D.zetaSCont s := by
  have h1 : ∀ s : ℂ, 1 < s.re → D.Llam u s = D.zetaSCont s := by
    intro s hs
    rw [D.Llam_eq_raw u s hs, LlamRaw_principal D u hu s]
    exact (zetaSCont_eq_zetaS D s hs).symm
  exact eqOn_punctured (D.Llam_analyticOnNhd u) (zetaSCont_analytic D)
    h1 s hs hs1

theorem Hu_slice_eq_H (u : D.Row) (hu : u.u = 1) (ξ : ℂ) (hξ : 1 < ξ.re) :
    EulerDomain.Hu D u ξ 1 (1 / 6) = Spectral.H D ξ := by
  have h1 : EulerDomain.Hu D u ξ 1 (1 / 6) =
      PrincipalMellinComparison.principalContourCorrection D.recipe ξ 1 (1 / 6) := by
    obtain rfl := ActualRowCount.eq_principalRow D hu
    rfl
  rw [h1]
  exact PrincipalMellinComparison.principalContourCorrection_at_double_residue D.recipe ξ
    (by linarith)

def remainingKernel (u : D.Row) (ξ z : ℂ) (Z : ℝ) : ℂ :=
  (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z) *
    Complex.exp ((ξ + z - 1) ^ 2) * D.M z * (D.q u : ℂ) ^ (-z) *
      (D.zetaSCont (6 * z) * EulerDomain.Hu D u ξ 1 z / D.Llam u ξ)

variable {D} in

theorem kern_w_tendsto (u : D.Row) (hu : u.u = 1) (ξ z : ℂ) (Z : ℝ) (hZ : 0 < Z)
    (hξ : 1 < ξ.re) (hz : 1 / 20 - EulerDomain.pad ≤ z.re) (hz6 : 6 * z ≠ 1) :
    Filter.Tendsto (fun w : ℂ => (w - 1) * kernelWith D (rowContLocal D) u ξ w z Z)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (Spectral.RS D * D.W1Hat 1 * remainingKernel D u ξ z Z)) := by
  have hZc := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hmem : ((ξ, (1 : ℂ), z) : EulerDomain.Coordinates) ∈ EulerDomain.OmegaStar := by
    simp only [EulerDomain.OmegaStar, Set.mem_setOf_eq, Complex.one_re]
    simp only [EulerDomain.pad] at hz
    grind only
  have hHu : ContinuousAt (fun w : ℂ => EulerDomain.Hu D u ξ w z) 1 := by
    have hd := (EulerDomain.Hu_normal_convergence D u).2.2.1
    have hat : DifferentiableAt ℂ
        (fun p : EulerDomain.Coordinates => EulerDomain.Hu D u p.1 p.2.1 p.2.2) (ξ, 1, z) :=
      hd.differentiableAt (EulerDomain.OmegaStar_isOpen.mem_nhds hmem)
    have hc : Continuous fun w : ℂ => ((ξ, w, z) : EulerDomain.Coordinates) := by fun_prop
    exact ContinuousAt.comp (f := fun w : ℂ => ((ξ, w, z) : EulerDomain.Coordinates)) (x := 1)
      hat.continuousAt hc.continuousAt
  have hW : Continuous D.W1Hat :=
    (ProbeSheet.MellinProof.realWeight_mellin_differentiable D.recipe.probe.W1).continuous
  have hpow : ContinuousAt (fun w : ℂ => (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 +
      (Scales.smoothingExponent : ℂ) * z + (Scales.yExponent : ℂ) * (w - 1))) 1 :=
    ContinuousAt.const_cpow (by fun_prop) (Or.inl hZc)
  have hQ := (hpow.mul hW.continuousAt).mul hHu
  have hlim := ((Spectral.RS_spec D).mul (hQ.tendsto.mono_left nhdsWithin_le_nhds)).mul_const
    (Complex.exp ((ξ + z - 1) ^ 2) * D.M z * (D.q u : ℂ) ^ (-z) *
      (D.zetaSCont (6 * z) / D.Llam u ξ))
  have hev : ∀ᶠ w in nhdsWithin (1 : ℂ) {1}ᶜ,
      ((w - 1) * D.zetaSCont w * ((Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 +
          (Scales.smoothingExponent : ℂ) * z + (Scales.yExponent : ℂ) * (w - 1)) * D.W1Hat w *
          EulerDomain.Hu D u ξ w z)) *
        (Complex.exp ((ξ + z - 1) ^ 2) * D.M z * (D.q u : ℂ) ^ (-z) *
          (D.zetaSCont (6 * z) / D.Llam u ξ)) =
      (w - 1) * kernelWith D (rowContLocal D) u ξ w z Z := by
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hpos : ∀ᶠ w in nhdsWithin (1 : ℂ) {1}ᶜ, 0 < w.re :=
      eventually_nhdsWithin_of_eventually_nhds (hopen.mem_nhds (by simp))
    filter_upwards [hpos, self_mem_nhdsWithin] with w hw hw1
    have hw1' : w ≠ 1 := hw1
    unfold kernelWith rowContLocal
    rw [Lpsi_principal_eq D u hu w hw hw1']
    ring
  have hfin := Filter.Tendsto.congr' hev hlim
  convert hfin using 2
  unfold remainingKernel
  grind only [Pi.mul_apply, sub_self, mul_zero, add_zero]

theorem wResidue_eq (u : D.Row) (hu : u.u = 1) (ξ z : ℂ) (Z : ℝ) (hZ : 0 < Z)
    (hξ : 1 < ξ.re)
    (hz : 1 / 20 - EulerDomain.pad ≤ z.re) (hz6 : 6 * z ≠ 1) :
    wResidueLocal D u ξ z Z = Spectral.RS D * D.W1Hat 1 * remainingKernel D u ξ z Z :=
  (kern_w_tendsto u hu ξ z Z hZ hξ hz hz6).limUnder_eq

theorem remainingKernel_principal (u : D.Row) (hu : u.u = 1) (ξ z : ℂ) (Z : ℝ) :
    remainingKernel D u ξ z Z =
      (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z) *
        Complex.exp ((ξ + z - 1) ^ 2) * D.M z *
          (D.zetaSCont (6 * z) * EulerDomain.Hu D u ξ 1 z / D.Llam u ξ) := by
  unfold remainingKernel
  rw [q_principal D u hu]
  simp

theorem zetaSCont_six_residue :
    Filter.Tendsto (fun z : ℂ => (z - 1 / 6) * D.zetaSCont (6 * z))
      (nhdsWithin (1 / 6 : ℂ) {1 / 6}ᶜ) (nhds (Spectral.RS D / 6)) := by
  have h1 : Filter.Tendsto (fun z : ℂ => 6 * z) (nhds (1 / 6 : ℂ))
      (nhds ((6 : ℂ) * (1 / 6))) :=
    (by fun_prop : Continuous fun z : ℂ => 6 * z).tendsto _
  rw [show (6 : ℂ) * (1 / 6) = 1 by norm_num] at h1
  have hφ : Filter.Tendsto (fun z : ℂ => 6 * z) (nhdsWithin (1 / 6 : ℂ) {1 / 6}ᶜ)
      (nhdsWithin (1 : ℂ) {1}ᶜ) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (h1.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
    intro h
    apply hz
    linear_combination h / 6
  have hmain := ((Spectral.RS_spec D).comp hφ).const_mul (1 / 6 : ℂ)
  have key : Spectral.RS D / 6 = 1 / 6 * Spectral.RS D := by ring
  rw [key]
  refine hmain.congr (fun z => ?_)
  simp only [Function.comp]
  ring

variable {D} in

theorem wResidue_tendsto (u : D.Row) (hu : u.u = 1) (ξ : ℂ) (hξ : 1 < ξ.re) (Z : ℝ)
    (hZ : 0 < Z) :
    Filter.Tendsto (fun z : ℂ => (z - 1 / 6) * wResidueLocal D u ξ z Z)
      (𝓝[≠] (1 / 6 : ℂ))
      (𝓝 (Spectral.c₀ D * (Z : ℂ) ^ (ξ - 61 / 100) * Spectral.G D ξ)) := by
  have hZc := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hne1 : ξ ≠ 1 := fun h => by rw [h] at hξ; simp at hξ
  have h16 : (1 / 6 : ℂ) = ((1 / 6 : ℝ) : ℂ) := by
    first | norm_num | simp | (push_cast; ring)
  have h16re : ((1 / 6 : ℂ)).re = 1 / 6 := by rw [h16, Complex.ofReal_re]
  have hmem : ((ξ, (1 : ℂ), (1 / 6 : ℂ)) : EulerDomain.Coordinates) ∈
      EulerDomain.OmegaStar := by
    simp only [EulerDomain.OmegaStar, Set.mem_setOf_eq, Complex.one_re, h16re]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have hHuz : ContinuousAt (fun z : ℂ => EulerDomain.Hu D u ξ 1 z) (1 / 6) := by
    have hd := (EulerDomain.Hu_normal_convergence D u).2.2.1
    have hat : DifferentiableAt ℂ
        (fun p : EulerDomain.Coordinates => EulerDomain.Hu D u p.1 p.2.1 p.2.2)
        (ξ, 1, 1 / 6) :=
      hd.differentiableAt (EulerDomain.OmegaStar_isOpen.mem_nhds hmem)
    have hc : Continuous fun z : ℂ => ((ξ, (1 : ℂ), z) : EulerDomain.Coordinates) := by
      fun_prop
    exact ContinuousAt.comp
      (f := fun z : ℂ => ((ξ, (1 : ℂ), z) : EulerDomain.Coordinates)) (x := 1 / 6)
      hat.continuousAt hc.continuousAt
  have hMopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hM : ContinuousAt D.M (1 / 6) :=
    (D.M_differentiableOn.differentiableAt
      (hMopen.mem_nhds (by show (0 : ℝ) < ((1 / 6 : ℂ)).re; rw [h16re]; norm_num))).continuousAt
  have hpow : ContinuousAt (fun z : ℂ => (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 +
      (Scales.smoothingExponent : ℂ) * z)) (1 / 6) :=
    ContinuousAt.const_cpow (by fun_prop) (Or.inl hZc)
  have hexp : ContinuousAt (fun z : ℂ => Complex.exp ((ξ + z - 1) ^ 2)) (1 / 6) :=
    (Complex.continuous_exp.comp
      (by fun_prop : Continuous fun z : ℂ => (ξ + z - 1) ^ 2)).continuousAt
  have hT : ContinuousAt (fun z : ℂ => (Spectral.RS D * D.W1Hat 1) *
      (((Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z) *
        Complex.exp ((ξ + z - 1) ^ 2) * D.M z * EulerDomain.Hu D u ξ 1 z) / D.Llam u ξ))
      (1 / 6) :=
    ((((hpow.mul hexp).mul hM).mul hHuz).div_const _).const_mul _
  have hlim := (zetaSCont_six_residue D).mul
    (hT.tendsto.mono_left nhdsWithin_le_nhds)
  have hre : ∀ᶠ z in nhdsWithin (1 / 6 : ℂ) {1 / 6}ᶜ, 1 / 20 - EulerDomain.pad < z.re := by
    have hopen : IsOpen {z : ℂ | 1 / 20 - EulerDomain.pad < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hm : ∀ᶠ z in nhds (1 / 6 : ℂ), 1 / 20 - EulerDomain.pad < z.re :=
      hopen.mem_nhds (by
        show 1 / 20 - EulerDomain.pad < ((1 / 6 : ℂ)).re
        rw [h16re]; simp only [EulerDomain.pad]; norm_num)
    exact eventually_nhdsWithin_of_eventually_nhds hm
  have hev : ∀ᶠ z in nhdsWithin (1 / 6 : ℂ) {1 / 6}ᶜ,
      (z - 1 / 6) * D.zetaSCont (6 * z) * ((Spectral.RS D * D.W1Hat 1) *
      (((Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z) *
        Complex.exp ((ξ + z - 1) ^ 2) * D.M z * EulerDomain.Hu D u ξ 1 z) / D.Llam u ξ)) =
      (z - 1 / 6) * wResidueLocal D u ξ z Z := by
    filter_upwards [hre, self_mem_nhdsWithin] with z hz hz1
    have hz1' : z ≠ 1 / 6 := hz1
    have h6 : 6 * z ≠ 1 := by
      intro h
      apply hz1'
      linear_combination h / 6
    rw [wResidue_eq D u hu ξ z Z hZ hξ hz.le h6,
      remainingKernel_principal D u hu]
    ring
  have hfin := Filter.Tendsto.congr' hev hlim
  have hE : (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * (1 / 6)) =
      (Z : ℂ) ^ (ξ - 61 / 100) := by
    congr 1
    simp only [Scales.xExponent, Scales.smoothingExponent]
    push_cast
    ring
  have hex : Complex.exp ((ξ + 1 / 6 - 1) ^ 2) = Complex.exp ((ξ - 5 / 6) ^ 2) := by
    congr 1
    ring
  convert hfin using 2
  beta_reduce
  rw [hE, hex, Hu_slice_eq_H D u hu ξ hξ,
    Llam_principal_eq D u hu ξ (by linarith) hne1]
  unfold Spectral.c₀ Spectral.G
  ring

theorem zResidue_eq (u : D.Row) (hu : u.u = 1) (ξ : ℂ) (hξ : 1 < ξ.re) (Z : ℝ) (hZ : 0 < Z) :
    zResidueLocal D u ξ Z = Spectral.c₀ D * (Z : ℂ) ^ (ξ - 61 / 100) * Spectral.G D ξ :=
  (wResidue_tendsto u hu ξ hξ Z hZ).limUnder_eq


end

end DedekindZetaZeroFree.Quantitative.PrincipalResidueFormulas
