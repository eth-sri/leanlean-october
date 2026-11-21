module

public import DedekindZetaZeroFree.Moments.Principal.Contour.Deformation

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalWShift

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def rowCont (u : D.Row) (ξ w z : ℂ) : ℂ :=
  D.zetaSCont (6 * z) * D.Lpsi u w * EulerDomain.Hu D u ξ w z / D.Llam u ξ

def JCont (C : Set D.Row) (x y v Z : ℝ) : ℂ :=
  ∑ᶠ u ∈ C, comparisonVerticalIntegral x (fun ξ =>
    comparisonVerticalIntegral y (fun w =>
      comparisonVerticalIntegral v (fun z => kernelWith D (rowCont D) u ξ w z Z)))

def wResidue (u : D.Row) (ξ z : ℂ) (Z : ℝ) : ℂ :=
  Filter.limUnder (nhdsWithin (1 : ℂ) {1}ᶜ)
    (fun w : ℂ => (w - 1) * kernelWith D (rowCont D) u ξ w z Z)

def Jwres (Z : ℝ) : ℂ :=
  ∑ᶠ u ∈ principalRows D, comparisonVerticalIntegral Scales.rightLine (fun ξ =>
    comparisonVerticalIntegral (1 / 6 + Scales.contourOffset) (fun z => wResidue D u ξ z Z))

def Rw (Z : ℝ) : ℂ :=
  JCont D (principalRows D) Scales.rightLine (9 / 10) (1 / 6 + Scales.contourOffset) Z

theorem E_remainder :
    Scales.kernelExponent Scales.rightLine (9 / 10) (1 / 6 + Scales.contourOffset) =
      Scales.mainExponent - 37749867 / 1000000000 := by
  unfold Scales.kernelExponent Scales.rightLine Scales.contourOffset Scales.xExponent Scales.smoothingExponent Scales.yExponent Scales.mainExponent
  norm_num

theorem rowFactor_eq_rowCont : rowFactor D = rowCont D := by
  funext u ξ w z
  unfold rowFactor rowCont
  ring

theorem Jpr_eq_JCont (Z : ℝ) :
    Jpr D Z = JCont D (principalRows D) 4 4 2 Z := by
  unfold Jpr J wzIntegral K JCont
  rw [rowFactor_eq_rowCont]

open MeasureTheory in

theorem lvl1 {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : α → ℂ) (m : α → ℝ)
    (hm : Integrable m ν) (h : ∀ᵐ x ∂ν, ‖f x‖ ≤ m x) : ‖∫ x, f x ∂ν‖ ≤ ∫ x, m x ∂ν :=
  (norm_integral_le_integral_norm f).trans
    (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hm h)

open MeasureTheory in
theorem lvl2' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [SFinite μ] [SFinite ν] (f : α → ℂ) (m : α × β → ℝ)
    (hm : Integrable m (μ.prod ν))
    (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ ∫ b, m (a, b) ∂ν) : ‖∫ a, f a ∂μ‖ ≤ ∫ p, m p ∂(μ.prod ν) := by
  rw [integral_prod m hm]
  exact lvl1 μ f _ hm.integral_prod_left h

open MeasureTheory in
theorem lvl2 {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [SFinite μ] [SFinite ν] (f : α → β → ℂ) (m : α × β → ℝ)
    (hm : Integrable m (μ.prod ν)) (h : ∀ a b, ‖f a b‖ ≤ m (a, b)) :
    ‖∫ a, ∫ b, f a b ∂ν ∂μ‖ ≤ ∫ p, m p ∂(μ.prod ν) := by
  refine lvl2' μ ν (fun a => ∫ b, f a b ∂ν) m hm ?_
  filter_upwards [hm.prod_right_ae] with a ha
  solve_by_elim [lvl1, Filter.Eventually.of_forall]

open MeasureTheory in
theorem lvl3 (F : ℝ → ℝ → ℝ → ℂ) (m : ℝ × ℝ × ℝ → ℝ) (hm : Integrable m)
    (h : ∀ a b d, ‖F a b d‖ ≤ m (a, b, d)) :
    ‖∫ a : ℝ, ∫ b : ℝ, ∫ d : ℝ, F a b d‖ ≤ ∫ p, m p := by
  have hm' := hm
  refine lvl2' (volume : Measure ℝ) ((volume : Measure ℝ).prod (volume : Measure ℝ))
    (fun a => ∫ b : ℝ, ∫ d : ℝ, F a b d) m hm' ?_
  filter_upwards [hm'.prod_right_ae] with a ha
  solve_by_elim [lvl2]

open MeasureTheory in
theorem cvi_iter_eq (x y v : ℝ) (k : ℂ → ℂ → ℂ → ℂ) :
    comparisonVerticalIntegral x (fun ξ => comparisonVerticalIntegral y (fun w =>
      comparisonVerticalIntegral v (fun z => k ξ w z))) =
      ((2 * (Real.pi : ℂ))⁻¹) ^ 3 * ∫ a : ℝ, ∫ b : ℝ, ∫ d : ℝ,
        k ((x : ℂ) + (a : ℂ) * Complex.I) ((y : ℂ) + (b : ℂ) * Complex.I)
          ((v : ℂ) + (d : ℂ) * Complex.I) := by
  unfold comparisonVerticalIntegral
  simp only [integral_const_mul]
  ring

theorem cvi_congr {σ : ℝ} {f g : ℂ → ℂ}
    (h : ∀ t : ℝ, f ((σ : ℂ) + (t : ℂ) * Complex.I) = g ((σ : ℂ) + (t : ℂ) * Complex.I)) :
    comparisonVerticalIntegral σ f = comparisonVerticalIntegral σ g := by
  unfold comparisonVerticalIntegral
  rw [show (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) =
    fun t : ℝ => g ((σ : ℂ) + (t : ℂ) * Complex.I) from funext h]

theorem principalRows_eq : principalRows D = {ActualRowCount.principalRow D} := by
  ext u
  exact ActualRowCount.u_eq_one_iff D

theorem JCont_eq (x y v Z : ℝ) :
    JCont D (principalRows D) x y v Z =
      comparisonVerticalIntegral x
        (fun ξ => PrincipalContourDeformation.Iwz D (ActualRowCount.principalRow D) Z y v ξ) := by
  unfold JCont
  rw [principalRows_eq, finsum_mem_singleton]
  rfl

theorem rowCont_eq_local : rowCont D = PrincipalKernelDefinitions.rowContLocal D := rfl

theorem JCont_shift_initial (Z : ℝ) (hZ : 2 ≤ Z) :
    JCont D (principalRows D) 4 4 2 Z =
      JCont D (principalRows D) Scales.rightLine Scales.rightLine (1 / 6 + Scales.contourOffset) Z := by
  classical
  have hu : (ActualRowCount.principalRow D).u = 1 := ActualRowCount.principalRow_u D
  have h4 : (4 : ℝ) ∈ Set.Icc Scales.rightLine 4 := ⟨by rw [Scales.rightLine_eq]; norm_num, le_rfl⟩
  rw [JCont_eq D, JCont_eq D]
  have e1 : comparisonVerticalIntegral 4
      (fun ξ => PrincipalContourDeformation.Iwz D (ActualRowCount.principalRow D) Z 4 2 ξ) =
      comparisonVerticalIntegral 4
      (fun ξ => PrincipalContourDeformation.Iwz D (ActualRowCount.principalRow D) Z 4
        (1 / 6 + Scales.contourOffset) ξ) := by
    refine cvi_congr fun s => ?_
    unfold PrincipalContourDeformation.Iwz
    refine cvi_congr fun t => ?_
    exact PrincipalContourDeformation.initial_z_shift D _ hu Z hZ 4 4 h4 h4 s t
  have e2 : comparisonVerticalIntegral 4
      (fun ξ => PrincipalContourDeformation.Iwz D (ActualRowCount.principalRow D) Z 4
        (1 / 6 + Scales.contourOffset) ξ) =
      comparisonVerticalIntegral 4
      (fun ξ => PrincipalContourDeformation.Iwz D (ActualRowCount.principalRow D) Z Scales.rightLine
        (1 / 6 + Scales.contourOffset) ξ) := by
    refine cvi_congr fun s => ?_
    exact PrincipalContourDeformation.initial_w_shift D _ hu Z hZ 4 h4 s
  exact e1.trans (e2.trans (PrincipalContourDeformation.initial_xi_shift D _ hu Z hZ))

open MeasureTheory in
theorem sec3 (F : ℝ → ℝ → ℝ → ℂ)
    (hF : Integrable (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2)) :
    Integrable (fun a : ℝ => ∫ q : ℝ × ℝ, F a q.1 q.2) ∧
    (∀ᵐ a : ℝ, ∫ b : ℝ, ∫ d : ℝ, F a b d = ∫ q : ℝ × ℝ, F a q.1 q.2) ∧
    (∀ᵐ a : ℝ, ∫ d : ℝ, ∫ b : ℝ, F a b d = ∫ q : ℝ × ℝ, F a q.1 q.2) ∧
    (∀ᵐ a : ℝ, Integrable (fun d : ℝ => ∫ b : ℝ, F a b d)) := by
  have hF' : Integrable (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2.1 p.2.2)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))) := hF
  refine ⟨hF'.integral_prod_left, ?_, ?_, ?_⟩
  · filter_upwards [hF'.prod_right_ae] with a ha
    exact (integral_prod (fun q : ℝ × ℝ => F a q.1 q.2) ha).symm
  · filter_upwards [hF'.prod_right_ae] with a ha
    exact (integral_prod_symm (fun q : ℝ × ℝ => F a q.1 q.2) ha).symm
  · filter_upwards [hF'.prod_right_ae] with a ha
    exact ha.integral_prod_right

def wsKP (r : D.Row) (Z y a b d : ℝ) : ℂ :=
  kernelWith D (PrincipalKernelDefinitions.rowContLocal D) r
    ((Scales.rightLine : ℂ) + (a : ℂ) * Complex.I) ((y : ℂ) + (b : ℂ) * Complex.I)
    (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (d : ℂ) * Complex.I) Z

def wsKR (r : D.Row) (Z a d : ℝ) : ℂ :=
  PrincipalKernelDefinitions.wResidueLocal D r ((Scales.rightLine : ℂ) + (a : ℂ) * Complex.I)
    (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (d : ℂ) * Complex.I) Z

theorem JCont_eq_wsKP (Z y : ℝ) :
    JCont D (principalRows D) Scales.rightLine y (1 / 6 + Scales.contourOffset) Z =
      ((2 * (Real.pi : ℂ))⁻¹) ^ 3 * ∫ a : ℝ, ∫ b : ℝ, ∫ d : ℝ,
        wsKP D (ActualRowCount.principalRow D) Z y a b d := by
  unfold JCont
  rw [principalRows_eq, finsum_mem_singleton, rowCont_eq_local]
  exact cvi_iter_eq _ _ _ _

theorem Jwres_eq_wsKR (Z : ℝ) :
    Jwres D Z = ((2 * (Real.pi : ℂ))⁻¹) * (((2 * (Real.pi : ℂ))⁻¹) *
      ∫ a : ℝ, ∫ d : ℝ, wsKR D (ActualRowCount.principalRow D) Z a d) := by
  unfold Jwres
  rw [principalRows_eq, finsum_mem_singleton]
  unfold comparisonVerticalIntegral
  simp only [MeasureTheory.integral_const_mul]
  rfl

theorem wsKR_eq (Z : ℝ) (hZ : 2 ≤ Z) (a d : ℝ) :
    wsKR D (ActualRowCount.principalRow D) Z a d =
      ((2 * (Real.pi : ℂ))⁻¹) *
        (∫ b : ℝ, wsKP D (ActualRowCount.principalRow D) Z Scales.rightLine a b d) -
      ((2 * (Real.pi : ℂ))⁻¹) *
        (∫ b : ℝ, wsKP D (ActualRowCount.principalRow D) Z (9 / 10) a b d) := by
  have h := PrincipalContourDeformation.w_shift_across_one D (ActualRowCount.principalRow D)
    (ActualRowCount.principalRow_u D) Z hZ a d
  unfold comparisonVerticalIntegral at h
  exact h.symm

private theorem wsKP_majorant (y : ℝ) (hy₁ : 9 / 10 - EulerDomain.pad ≤ y) (hy₂ : y ≠ 1) :
    ∃ g : ℝ × ℝ × ℝ → ℝ, MeasureTheory.Integrable g ∧ (∀ p, 0 ≤ g p) ∧
      ∀ Z : ℝ, 2 ≤ Z → ∀ p : ℝ × ℝ × ℝ,
        ‖wsKP D (ActualRowCount.principalRow D) Z y p.1 p.2.1 p.2.2‖ ≤
        Z ^ Scales.kernelExponent Scales.rightLine y (1 / 6 + Scales.contourOffset) * g p := by
  have hδ : (0 : ℝ) < Scales.contourOffset := by norm_num [Scales.contourOffset]
  obtain ⟨g, hgi, hg0, hg⟩ := PrincipalKernelMajorants.kernel_majorant_paddedBox₂ D _
    (ActualRowCount.principalRow_u D)
    Scales.rightLine Scales.rightLine y y (1 / 6 + Scales.contourOffset) (1 / 6 + Scales.contourOffset)
    (fun x hx => by linarith [hx.1])
    (fun y' hy' => by simpa only [le_antisymm hy'.2 hy'.1] using And.intro hy₁ hy₂)
    (fun v hv => by linarith [hv.1])
  exact ⟨g, hgi, hg0, hg _ ⟨le_rfl, le_rfl⟩ _ ⟨le_rfl, le_rfl⟩ _ ⟨le_rfl, le_rfl⟩⟩

set_option maxHeartbeats 1000000 in
theorem wsKP_integrable (Z y : ℝ) (hZ : 2 ≤ Z) (hy1 : 9 / 10 - EulerDomain.pad ≤ y)
    (hy2 : y ≠ 1) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ × ℝ => wsKP D (ActualRowCount.principalRow D) Z y p.1 p.2.1 p.2.2) := by
  obtain ⟨g, hgi, _, hg⟩ := wsKP_majorant D y hy1 hy2
  have hδ : (0 : ℝ) < Scales.contourOffset := by norm_num [Scales.contourOffset]
  have hpad : (0 : ℝ) < EulerDomain.pad := by norm_num [EulerDomain.pad]
  have hcont : Continuous
      (fun p : ℝ × ℝ × ℝ => wsKP D (ActualRowCount.principalRow D) Z y p.1 p.2.1 p.2.2) := by
    apply (PrincipalKernelMajorants.kernel_analytic_paddedBox₂ D _
      (ActualRowCount.principalRow_u D) Z (by linarith)).continuousOn.comp_continuous
      (f := fun p : ℝ × ℝ × ℝ => ((Scales.rightLine : ℂ) + (p.1 : ℂ) * Complex.I,
        (y : ℂ) + (p.2.1 : ℂ) * Complex.I,
        (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (p.2.2 : ℂ) * Complex.I))) (by fun_prop)
    intro p
    have hne : (y : ℂ) + (p.2.1 : ℂ) * Complex.I ≠ 1 :=
      fun h => hy2 (by simpa using congrArg Complex.re h)
    simp [EulerDomain.paddedBox₂, EulerDomain.box, PrincipalKernelMajorants.xiPrincipal,
      PrincipalKernelMajorants.zPrincipal, PrincipalKernelMajorants.singW, hne]
    grind only
  exact MeasureTheory.Integrable.mono' (hgi.const_mul _) hcont.aestronglyMeasurable (.of_forall (hg Z hZ))

theorem JCont_w_shift (Z : ℝ) (hZ : 2 ≤ Z) :
    JCont D (principalRows D) Scales.rightLine Scales.rightLine (1 / 6 + Scales.contourOffset) Z =
      Jwres D Z + Rw D Z := by
  classical
  have hx1 : Scales.rightLine = 10000001 / 10000000 := Scales.rightLine_eq
  have hPi := wsKP_integrable D Z Scales.rightLine hZ
    (by rw [hx1]; unfold EulerDomain.pad; norm_num) (by rw [hx1]; norm_num)
  have hQi := wsKP_integrable D Z (9 / 10) hZ
    (by unfold EulerDomain.pad; norm_num) (by norm_num)
  obtain ⟨hVP, hP1, hP2, hP3⟩ := sec3 (wsKP D (ActualRowCount.principalRow D) Z Scales.rightLine) hPi
  obtain ⟨hVQ, hQ1, hQ2, hQ3⟩ := sec3 (wsKP D (ActualRowCount.principalRow D) Z (9 / 10)) hQi
  unfold Rw
  rw [JCont_eq_wsKP D Z Scales.rightLine, JCont_eq_wsKP D Z (9 / 10), Jwres_eq_wsKR]
  set c : ℂ := (2 * (Real.pi : ℂ))⁻¹ with hc
  have e1 := MeasureTheory.integral_congr_ae hP1
  have e2 := MeasureTheory.integral_congr_ae hQ1
  have e3 : ∫ a : ℝ, ∫ d : ℝ, wsKR D (ActualRowCount.principalRow D) Z a d =
      ∫ a : ℝ, (c * (∫ q : ℝ × ℝ, wsKP D (ActualRowCount.principalRow D) Z Scales.rightLine a q.1 q.2) -
        c * (∫ q : ℝ × ℝ, wsKP D (ActualRowCount.principalRow D) Z (9 / 10) a q.1 q.2)) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hP2, hP3, hQ2, hQ3] with a ha2 ha3 hb2 hb3
    simp_rw [wsKR_eq D Z hZ a]
    rw [MeasureTheory.integral_sub (ha3.const_mul c) (hb3.const_mul c),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, ha2, hb2]
  have e4 : ∫ a : ℝ, (c * (∫ q : ℝ × ℝ, wsKP D (ActualRowCount.principalRow D) Z Scales.rightLine a q.1 q.2) -
        c * (∫ q : ℝ × ℝ, wsKP D (ActualRowCount.principalRow D) Z (9 / 10) a q.1 q.2)) =
      c * (∫ a : ℝ, ∫ q : ℝ × ℝ, wsKP D (ActualRowCount.principalRow D) Z Scales.rightLine a q.1 q.2) -
      c * (∫ a : ℝ, ∫ q : ℝ × ℝ, wsKP D (ActualRowCount.principalRow D) Z (9 / 10) a q.1 q.2) := by
    rw [MeasureTheory.integral_sub (hVP.const_mul c) (hVQ.const_mul c),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [e1, e2, e3, e4]
  ring

theorem Jpr_eq (Z : ℝ) (hZ : 2 ≤ Z) : Jpr D Z = Jwres D Z + Rw D Z := by
  rw [Jpr_eq_JCont, JCont_shift_initial D Z hZ, JCont_w_shift D Z hZ]

theorem Rw_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖Rw D Z‖ ≤ C * Z ^ (Scales.mainExponent - 37749867 / 1000000000) := by
  obtain ⟨g, hgi, hg0, hg⟩ := wsKP_majorant D (9 / 10) (by norm_num [EulerDomain.pad]) (by norm_num)
  let K := ‖((2 * (Real.pi : ℂ))⁻¹)‖ ^ 3 * ∫ p, g p
  have hK : 0 ≤ K := mul_nonneg (by positivity) (MeasureTheory.integral_nonneg hg0)
  refine ⟨K + 1, by positivity, fun Z hZ => ?_⟩
  have hbd := lvl3 (wsKP D (ActualRowCount.principalRow D) Z (9 / 10)) _ (hgi.const_mul _)
    (fun a b d => hg Z hZ (a, b, d))
  rw [E_remainder] at hbd
  rw [Rw, JCont_eq_wsKP, norm_mul, norm_pow]
  refine (mul_le_mul_of_nonneg_left hbd (by positivity)).trans ?_
  rw [MeasureTheory.integral_const_mul]
  calc
    _ = K * _ := by dsimp [K]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)

end

end DedekindZetaZeroFree.Quantitative.PrincipalWShift
