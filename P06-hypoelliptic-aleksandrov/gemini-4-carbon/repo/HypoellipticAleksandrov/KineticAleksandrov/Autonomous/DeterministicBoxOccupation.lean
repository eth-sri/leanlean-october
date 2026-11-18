module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsActual
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxConcentrationSetting
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierModulus
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsBarrierGreenBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsRegularizedBarrier
import Mathlib.MeasureTheory.Group.Integral
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsMollifier
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set Filter
open scoped ENNReal Topology

/-- The exact deterministic second-moment conditions, with constants 2 and 4/3. -/
theorem terminal_second_moments
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) :
    let E := fullSpaceEvolution hH hLE hlam hLam A
    (∫⁻ w, ENNReal.ofReal ((w.2-z.2)^2) ∂kernelXV E T z) ≤
      ENNReal.ofReal (2*Lam*(T : ℝ)) ∧
    (∫⁻ w, ENNReal.ofReal ((w.1-z.1)^2) ∂kernelXV E T z) ≤
      ENNReal.ofReal (2*z.2^2*(T : ℝ)^2+4/3*Lam*(T : ℝ)^3) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  have hE := fullSpaceEvolution_spec hH hLE hlam hLam A
  refine ⟨kernelXV_velocity_2_moment hlam A E hE z T, ?_⟩
  apply (kernelXV_position_2_moment hlam A E hE z T).trans
  apply ENNReal.ofReal_le_ofReal
  have hL := hlam.le.trans hLam
  have hh : 0 ≤ z.2^2*(T : ℝ)^2+(2/3 : ℝ)*Lam*(T : ℝ)^3 := by positivity
  linarith only [hh]

/-- Both actual real second moments are integrable, rather than merely total integrals. -/
theorem terminal_second_moments_integrable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) :
    let E := fullSpaceEvolution hH hLE hlam hLam A
    Integrable (fun w : Z => (w.2-z.2)^2) (kernelXV E T z) ∧
      Integrable (fun w : Z => (w.1-z.1)^2) (kernelXV E T z) := by
  have h := terminal_second_moments hH hLE hlam hLam A z T
  constructor
  · apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (Filter.Eventually.of_forall (fun w : Z => sq_nonneg (w.2-z.2)))).mp
    exact ne_of_lt (h.1.trans_lt ENNReal.ofReal_lt_top)
  · apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (Filter.Eventually.of_forall (fun w : Z => sq_nonneg (w.1-z.1)))).mp
    exact ne_of_lt (h.2.trans_lt ENNReal.ofReal_lt_top)



/-- Jensen's inequality for a fractional power, with integrability proved from the first moment. -/
theorem integral_subunit_rpow_le {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (f : Ω → ℝ)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f mu)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Integrable (fun x => (f x)^p) mu ∧
      (∫ x, (f x)^p ∂mu) ≤ (∫ x, f x ∂mu)^p  := by
  have subunit_rpow_le_one_add {x : ℝ} (hx : 0 ≤ x) :
      x ^ p ≤ 1+x := by
    by_cases hx1 : x ≤ 1
    · exact (Real.rpow_le_one hx hx1 hp0).trans (by linarith)
    · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) hp1
      rw [Real.rpow_one] at h
      linarith
  have hpow : Integrable (fun x => (f x)^p) mu := by
    apply Integrable.mono' ((integrable_const 1).add hfi)
      ((Real.continuous_rpow_const hp0).measurable.comp hf).aestronglyMeasurable
    filter_upwards with x
    change ‖(f x)^p‖ ≤ 1+f x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hf0 x) _)]
    exact subunit_rpow_le_one_add (hf0 x)
  refine ⟨hpow, ?_⟩
  exact (Real.concaveOn_rpow hp0 hp1).le_map_integral
    (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici
    (Eventually.of_forall hf0) hfi hpow

/-- Fractional powers of displacement are controlled by their second moment. -/
theorem integral_abs_rpow_le_second {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (f : Ω → ℝ) (hf : Measurable f)
    (hfi : Integrable (fun x => (f x)^2) mu) {a : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    Integrable (fun x => |f x|^a) mu ∧
      (∫ x, |f x|^a ∂mu) ≤ (∫ x, (f x)^2 ∂mu)^(a/2) := by
  have hp0 : 0 ≤ a/2 := by linarith
  have hp1 : a/2 ≤ 1 := by linarith
  have he (x : Ω) : ((f x)^2)^(a/2) = |f x|^a := by
    rw [← sq_abs, ← Real.rpow_natCast_mul (abs_nonneg _) 2]
    congr 1
    ring
  simpa only [he] using integral_subunit_rpow_le mu (fun x => (f x)^2)
    (hf.pow_const 2) (fun _ => sq_nonneg _) hfi hp0 hp1

/-- Actual canonical velocity fractional moments, with no moment hypothesis. -/
theorem terminal_velocity_fractional_moment
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal)
    {a : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    let E := fullSpaceEvolution hH hLE hlam hLam A
    Integrable (fun w : Z => |w.2-z.2|^a) (kernelXV E T z) ∧
      (∫ w, |w.2-z.2|^a ∂kernelXV E T z) ≤ (2*Lam*(T : ℝ))^(a/2) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let : IsProbabilityMeasure (kernelXV E T z) :=
    ⟨kernelXV_mass_one hlam A E (fullSpaceEvolution_spec hH hLE hlam hLam A) T z⟩
  have hi := (terminal_second_moments_integrable hH hLE hlam hLam A z T).1
  obtain ⟨hfi, hle⟩ := integral_abs_rpow_le_second (kernelXV E T z)
    (fun w => w.2-z.2) (by fun_prop) hi ha0 ha2
  refine ⟨hfi, hle.trans ?_⟩
  apply Real.rpow_le_rpow (integral_nonneg (fun _ => sq_nonneg _)) ?_ (by linarith)
  have h := (terminal_second_moments hH hLE hlam hLam A z T).1
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun w => sq_nonneg (w.2-z.2)))] at h
  have hL := hlam.le.trans hLam
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- Actual canonical position fractional moments, with no moment hypothesis. -/
theorem terminal_position_fractional_moment
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal)
    {a : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    let E := fullSpaceEvolution hH hLE hlam hLam A
    Integrable (fun w : Z => |w.1-z.1|^a) (kernelXV E T z) ∧
      (∫ w, |w.1-z.1|^a ∂kernelXV E T z) ≤
        (2*z.2^2*(T : ℝ)^2+4/3*Lam*(T : ℝ)^3)^(a/2) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let : IsProbabilityMeasure (kernelXV E T z) :=
    ⟨kernelXV_mass_one hlam A E (fullSpaceEvolution_spec hH hLE hlam hLam A) T z⟩
  have hi := (terminal_second_moments_integrable hH hLE hlam hLam A z T).2
  obtain ⟨hfi, hle⟩ := integral_abs_rpow_le_second (kernelXV E T z)
    (fun w => w.1-z.1) (by fun_prop) hi ha0 ha2
  refine ⟨hfi, hle.trans ?_⟩
  apply Real.rpow_le_rpow (integral_nonneg (fun _ => sq_nonneg _)) ?_ (by linarith)
  have h := (terminal_second_moments hH hLE hlam hLam A z T).2
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun w => sq_nonneg (w.1-z.1)))] at h
  have hL := hlam.le.trans hLam
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h


/-- The source modulus controls signed endpoint differences using the actual kernel moments. -/
theorem deterministic_barrier_endpoint_of_modulus
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (alpha B : ℝ) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hB : 0 ≤ B)
    (Phi : Z → ℝ) (hPhi : Continuous Phi)
    (hmod : ∀ z w : Z, |Phi z-Phi w| ≤
      B*(|z.1-w.1|^(alpha/3)+|z.2-w.2|^alpha))
    (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) (Y : ℝ) :
    let E := fullSpaceEvolution hH hLE hlam hLam A
    Integrable (fun w : Z => Phi (w.1-Y,w.2)-Phi (z.1-Y,z.2)) (kernelXV E T z) ∧
      (∫ w, |Phi (w.1-Y,w.2)-Phi (z.1-Y,z.2)| ∂kernelXV E T z) ≤
        B*((2*z.2^2*(T : ℝ)^2+4/3*Lam*(T : ℝ)^3)^(alpha/6)+
          (2*Lam*(T : ℝ))^(alpha/2)) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  have hx := terminal_position_fractional_moment hH hLE hlam hLam A z T
    (a := alpha/3) (by linarith) (by linarith)
  have hv := terminal_velocity_fractional_moment hH hLE hlam hLam A z T ha0 (by linarith)
  let f := fun w : Z => Phi (w.1-Y,w.2)-Phi (z.1-Y,z.2)
  let g := fun w : Z => B*(|w.1-z.1|^(alpha/3)+|w.2-z.2|^alpha)
  have hf : Measurable f := by
    apply (hPhi.measurable.comp ((measurable_fst.sub_const Y).prodMk measurable_snd)).sub_const
  have hb (w : Z) : |f w| ≤ g w := by
    have he : w.1-Y-(z.1-Y) = w.1-z.1 := by ring
    simpa using (hmod (w.1-Y,w.2) (z.1-Y,z.2))
  have hgi : Integrable g (kernelXV E T z) := (hx.1.add hv.1).const_mul B
  have hfi : Integrable f (kernelXV E T z) := by
    apply hgi.mono' hf.aestronglyMeasurable
    exact Eventually.of_forall (fun w => by simpa using hb w)
  refine ⟨hfi, ?_⟩
  have he : alpha/3/2 = alpha/6 := by ring
  change (∫ w, |f w| ∂kernelXV E T z) ≤ _
  apply (integral_mono hfi.abs hgi hb).trans
  change (∫ w, B*(|w.1-z.1|^(alpha/3)+|w.2-z.2|^alpha) ∂kernelXV E T z) ≤ _
  rw [integral_const_mul]
  rw [integral_add hx.1 hv.1]
  simpa only [he] using (mul_le_mul_of_nonneg_left (add_le_add hx.2 hv.2) hB)


/-- The singular weight is infinite at the origin for a positive exponent. -/
theorem rhoWeight_origin {g : ℝ} (hg : 0 < g) : rhoWeight g (0,0) = ⊤ := by
  have hr : rho (0,0) = 0 := by
    dsimp only [rho]
    norm_num
  rw [rhoWeight, hr, ENNReal.ofReal_zero]
  exact ENNReal.zero_rpow_of_neg (by linarith)

/-- The literal box has the precise homogeneous gauge radius. -/
theorem box_rho_le {A0 r Y : ℝ} (hA0 : 0 < A0) (hr : 0 < r)
    {z : Z} (hz : z ∈ box A0 r Y) :
    rho (z.1-Y,z.2) ≤ (A0^2+A0^6)^(1/6 : ℝ)*r := by
  have hx := pow_le_pow_left₀ (abs_nonneg (z.1-Y)) hz.1 2
  have hv := pow_le_pow_left₀ (abs_nonneg z.2) hz.2 6
  rw [sq_abs] at hx
  rw [pow_abs, abs_of_nonneg (Even.pow_nonneg (by decide : Even 6) z.2)] at hv
  have hs : (z.1-Y)^2+z.2^6 ≤ (A0^2+A0^6)*r^6 := by
    calc
      _ ≤ (A0*r^3)^2+(A0*r)^6 := add_le_add hx hv
      _ = _ := by ring
  have ha : 0 ≤ A0^2+A0^6 := by positivity
  have he : (r^6)^(1/6 : ℝ) = r := by
    convert Real.pow_rpow_inv_natCast hr.le (by decide : 6 ≠ 0) using 1
    norm_num
  have hm := Real.mul_rpow (z := (1/6 : ℝ)) ha (pow_nonneg hr.le 6)
  rw [he] at hm
  change Real.rpow ((z.1-Y)^2+z.2^6) (1/6) ≤ _
  exact (Real.rpow_le_rpow (bellmanGaugePower_nonneg (z.1-Y,z.2)) hs (by norm_num : 0 ≤ (1/6 : ℝ))).trans_eq hm




/-- The source velocity restriction gives the cubic position moment scale. -/
theorem position_moment_scale_le {v M T Lam : ℝ} (hT : 0 ≤ T)
    (hv : |v| ≤ M*Real.sqrt T) :
    2*v^2*T^2+4/3*Lam*T^3 ≤ (2*M^2+4/3*Lam)*T^3 := by
  have hsq : v^2 ≤ M^2*T := by
    have h := mul_self_le_mul_self (abs_nonneg v) hv
    rw [← pow_two, ← pow_two, sq_abs, mul_pow, (Real.sq_sqrt hT)] at h
    exact h
  nlinarith only [(mul_le_mul_of_nonneg_right hsq (sq_nonneg T))]





/-- A measurable position convolution is a measurable physical-plane function. -/
theorem positionConvolution_measurable (eta : ℝ → ℝ) (heta : Measurable eta)
    (Phi : Z → ℝ) (hPhi : Measurable Phi) : Measurable (positionConvolution eta Phi) := by
  have hm :=
    (heta.comp ((measurable_fst.comp measurable_fst).sub measurable_snd)).mul
      (hPhi.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable



/-- On the zero-velocity axis, the weight has precisely the integrable position power. -/
theorem barrier_weight_position_axis (beta X : ℝ) :
    bellmanGauge (X, 0) ^ beta = |X| ^ (beta / 3) := by
  simp only [bellmanGauge, bellmanGaugePower, zero_pow (by decide : 6 ≠ 0),
    add_zero, ((sq_abs X).symm)]
  rw [← Real.rpow_natCast_mul (abs_nonneg X), ← Real.rpow_mul (abs_nonneg X)]
  congr 1
  ring


/-- Position regularization and extended Fatou retain the singular weight at every atom.
The first bound is the signed terminal endpoint difference. -/
theorem deterministic_barrier_green_fatou
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam alpha c : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    {phi : Z → ℝ} (h : IsBellmanHomogeneous alpha phi)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hc : 0 < c)
    (hbound : ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
      c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b phi q)
    (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) (hT : 0 < (T : ℝ)) (Y : ℝ) :
    let E := fullSpaceEvolution hH hLE hlam hLam A
    ENNReal.ofReal c *
      (∫⁻ q, rhoWeight (gamma alpha) (q.1 - Y, q.2)
        ∂physicalOccupationMeasure E z T) ≤
      ENNReal.ofReal (∫ q, bellmanOriginExtension phi (q.1 - Y, q.2) -
        bellmanOriginExtension phi (z.1 - Y, z.2) ∂kernelXV E T z)       := by
  let regularizedBarrierWeight (alpha : ℝ) (n : ℕ) :=
    positionConvolution (barrierMollifier n) (fun q => bellmanGauge q ^ (alpha - 2))
  have barrier_green_cutoff_removal (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (f : Z → ℝ) (hf : ContDiff ℝ 2 f) (D : ℝ) (Bv : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hD : 0 ≤ D) (hBv : 0 ≤ Bv) (hm : ∀ z w : Z, |f z - f w| ≤
      D * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha)) (hbv : ∀ z : Z, |deriv (fun v => f (z.1, v)) z.2| ≤ Bv) (w : Z → ℝ) (hw : Measurable w) (hwn : ∀ q, 0 ≤ w q) (hbound : ∀ q, c * w q ≤ physicalSpatialOperator A.a f q) (hfi : Integrable f (kernelXV E T z)) :
      ENNReal.ofReal c * (∫⁻ q, ENNReal.ofReal (w q) ∂physicalOccupationMeasure E z T) ≤
      ENNReal.ofReal ((∫ q, f q ∂kernelXV E T z) - f z) := by
    obtain ⟨C, hC, hb⟩ := barrier_cutoff_green_bounds hH hlam hLam A E hE f hf alpha D Bv
      ha ha1 hD hBv hm hbv c hc w hw hwn hbound Y z T hT
    let F := fun n : ℕ => fun q =>
      ENNReal.ofReal (c * (barrierRectCutoff Y ((n : ℝ) + 1) q * w q))
    let b := fun n : ℕ => (∫ q, barrierRectCutoff Y ((n : ℝ) + 1) q * f q ∂kernelXV E T z) -
      barrierRectCutoff Y ((n : ℝ) + 1) z * f z + C * (T : ℝ) / ((n : ℝ) + 1)
    have hmF (n : ℕ) : Measurable (F n) :=
      (((barrierRectCutoff_continuous _ _).measurable.mul hw).const_mul c).ennreal_ofReal
    have hpF (q : Z) : Tendsto (fun n => F n q) atTop (𝓝 (ENNReal.ofReal (c * w q))) := by
      apply Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [barrierRectCutoff_eventually_one Y q] with n hn
      simp [F, hn]
    have hcut0 : Tendsto (fun n : ℕ => barrierRectCutoff Y ((n : ℝ) + 1) z * f z)
        atTop (𝓝 (f z)) := by
      apply Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [barrierRectCutoff_eventually_one Y z] with n hn
      simp [hn]
    have herr : Tendsto (fun n : ℕ => C * (T : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [mul_zero, mul_one_div] using
        (tendsto_const_nhds (x := C * (T : ℝ))).mul
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hbt : Tendsto b atTop (𝓝 ((∫ q, f q ∂kernelXV E T z) - f z)) := by
      have hi := barrierRectCutoff_integral_tendsto (kernelXV E T z) f
        hf.continuous.measurable hfi Y
      simpa using (hi.sub hcut0).add herr
    have hboundF (n : ℕ) : (∫⁻ q, F n q ∂physicalOccupationMeasure E z T) ≤ ENNReal.ofReal (b n) :=
      hb ((n : ℝ) + 1) (by
        have hn : 0 ≤ n := by positivity
        linarith only [hn])
    have hh := singular_fatou_of_real_bounds (physicalOccupationMeasure E z T) F
      (fun q => ENNReal.ofReal (c * w q)) hmF hpF b _ hbt hboundF
    simpa only [ENNReal.ofReal_mul hc.le,
      lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne] using hh
  have regularizedBarrierWeight_tendsto (q : Z) :
      Tendsto (fun n => ENNReal.ofReal (regularizedBarrierWeight alpha n q))
      atTop (𝓝 (rhoWeight (gamma alpha) q)) := by
    have regularizedBarrierWeight_punctured_tendsto (hq : q ≠ (0, 0)) :
        Tendsto (fun n => ENNReal.ofReal (regularizedBarrierWeight alpha n q))
        atTop (𝓝 (rhoWeight (gamma alpha) q)) := by
      have hr := bellmanGauge_pos q hq
      have hbase : ContinuousAt (fun X : ℝ => bellmanGauge (X, q.2)) q.1 :=
        (bellmanGauge_continuous.comp (continuous_id.prodMk continuous_const)).continuousAt
      have hc : ContinuousAt (fun X : ℝ => bellmanGauge (X, q.2) ^ (alpha - 2)) q.1 :=
        hbase.rpow_const (Or.inl hr.ne')
      have hm : Measurable (fun X : ℝ => bellmanGauge (X, q.2) ^ (alpha - 2)) :=
        (bellmanGauge_continuous.measurable.comp
          (measurable_id.prodMk measurable_const)).pow_const _
      have hh := ContDiffBump.convolution_tendsto_right (μ := volume)
        (φ := barrierMollifierBump)
        (g := fun _ : ℕ => fun X : ℝ => bellmanGauge (X, q.2) ^ (alpha - 2))
        (k := fun _ : ℕ => q.1) barrierMollifierRadius_tendsto
        (Eventually.of_forall (fun _ => hm.aestronglyMeasurable))
        (hc.tendsto.comp tendsto_snd) tendsto_const_nhds
      have ht : Tendsto (fun n => regularizedBarrierWeight alpha n q)
          atTop (𝓝 (bellmanGauge q ^ (alpha - 2))) := by
        simpa [regularizedBarrierWeight, positionConvolution_displacement, barrierMollifier, convolution_def, ContinuousLinearMap.lsmul_apply] using hh
      have he : rhoWeight (gamma alpha) q = ENNReal.ofReal (bellmanGauge q ^ (alpha - 2)) := by
        change (ENNReal.ofReal (bellmanGauge q)) ^ (-(2 - alpha)) = _
        have he : -(2 - alpha) = alpha - 2 := by ring
        rw [he, ENNReal.ofReal_rpow_of_pos hr]
      rw [he]
      exact (ENNReal.continuous_ofReal.tendsto _).comp ht
    have regularizedBarrierWeight_origin_tendsto :
        Tendsto (fun n => ENNReal.ofReal (regularizedBarrierWeight alpha n (0, 0)))
        atTop (𝓝 ⊤) := by
      have regularizedBarrierWeight_origin_atTop :
          Tendsto (fun n => regularizedBarrierWeight alpha n (0, 0)) atTop atTop := by
        have regularizedBarrierWeight_origin_lower (n : ℕ) :
            barrierMollifierRadius n ^ ((alpha - 2) / 3) ≤ regularizedBarrierWeight alpha n (0, 0) := by
          let eta := barrierMollifier n
          have heta := barrierMollifier_spec n
          have hi := position_kernel_integrable eta (fun X => bellmanGauge (X, 0) ^ (alpha - 2))
            heta.1.continuous heta.2.1 (barrier_weight_fiber_locallyIntegrable alpha ha ha1 0) 0
          have hiη := (barrierMollifierBump n).integrable_normed (μ := volume)
          have hbound : ∀ᵐ X : ℝ ∂volume,
              eta (0 - X) * barrierMollifierRadius n ^ ((alpha - 2) / 3) ≤
              eta (0 - X) * bellmanGauge (X, 0) ^ (alpha - 2) := by
            filter_upwards [volume.ae_ne 0] with X hX
            by_cases hη : eta (0 - X) = 0
            · simp only [hη, zero_mul, le_refl]
            have hsupport : 0 - X ∈ Function.support ((barrierMollifierBump n).normed volume) := hη
            rw [(barrierMollifierBump n).support_normed_eq] at hsupport
            have hx : |X| < barrierMollifierRadius n := by
              simpa [Metric.mem_ball, Real.dist_eq, abs_neg, barrierMollifierBump] using hsupport
            rw [barrier_weight_position_axis]
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hX) hx.le (by linarith)) (heta.2.2.1 _)
          have hh := integral_mono_ae ((hiη.comp_sub_left 0).mul_const
            (barrierMollifierRadius n ^ ((alpha - 2) / 3))) hi hbound
          rw [integral_mul_const, integral_sub_left_eq_self, (barrierMollifierBump n).integral_normed,
            one_mul] at hh
          exact hh
        have hh := (tendsto_rpow_neg_nhdsGT_zero (by linarith : (alpha - 2) / 3 < 0)).comp (tendsto_nhdsWithin_iff.mpr ⟨barrierMollifierRadius_tendsto, Eventually.of_forall barrierMollifierRadius_pos⟩)
        exact tendsto_atTop_mono (regularizedBarrierWeight_origin_lower) hh
      exact ENNReal.tendsto_ofReal_atTop.comp (regularizedBarrierWeight_origin_atTop)
    by_cases hq : q = (0, 0)
    · subst q
      rw [rhoWeight_origin (by dsimp only [gamma]; linarith : 0 < gamma alpha)]
      exact regularizedBarrierWeight_origin_tendsto
    · exact regularizedBarrierWeight_punctured_tendsto hq
  have barrier_mollifier_endpoint_tendsto :
      let E := fullSpaceEvolution hH hLE hlam hLam A
    Tendsto (fun n : ℕ =>
      (∫ q, positionConvolution (barrierMollifier n) (bellmanOriginExtension phi)
        (q.1 - Y, q.2) ∂kernelXV E T z) -
      positionConvolution (barrierMollifier n) (bellmanOriginExtension phi) (z.1 - Y, z.2))
      atTop (𝓝 (∫ q, bellmanOriginExtension phi (q.1 - Y, q.2) -
        bellmanOriginExtension phi (z.1 - Y, z.2) ∂kernelXV E T z)) := by
    let E := fullSpaceEvolution hH hLE hlam hLam A
    have hE := fullSpaceEvolution_spec hH hLE hlam hLam A
    let : IsProbabilityMeasure (kernelXV E T z) := ⟨kernelXV_mass_one hlam A E hE T z⟩
    obtain ⟨D, hD, hm⟩ := BarrierRegularization.barrier_coordinate_modulus h ha ha1
    let Phi := fun n : ℕ => positionConvolution (barrierMollifier n) (bellmanOriginExtension phi)
    have hc (n : ℕ) : Continuous (Phi n) :=
      (barrier_position_regularization_joint h ha ha1 _ (barrierMollifier_spec n)).continuous
    have hmod (n : ℕ) := positionConvolution_modulus (barrierMollifier n) (barrierMollifier_spec n)
      (bellmanOriginExtension phi) (h.origin_extension_continuous ha) alpha D hD hm
    let f := fun n : ℕ => fun q : Z => Phi n (q.1 - Y, q.2) - Phi n (z.1 - Y, z.2)
    let g := fun q : Z => D * (|q.1 - z.1| ^ (alpha / 3) + |q.2 - z.2| ^ alpha)
    have hx := terminal_position_fractional_moment hH hLE hlam hLam A z T
      (a := alpha / 3) (by linarith) (by linarith)
    have hv := terminal_velocity_fractional_moment hH hLE hlam hLam A z T ha.le (by linarith)
    have hgi := (hx.1.add hv.1).const_mul D
    have hfm (n : ℕ) : Measurable (f n) :=
      ((hc n).measurable.comp ((measurable_fst.sub_const Y).prodMk measurable_snd)).sub_const _
    have hfb (n : ℕ) (q : Z) : ‖f n q‖ ≤ g q := by
      have he : q.1 - Y - (z.1 - Y) = q.1 - z.1 := by ring
      simpa [f, Phi, g, he] using hmod n (q.1 - Y, q.2) (z.1 - Y, z.2)
    have hlim : Tendsto (fun n => ∫ q, f n q ∂kernelXV E T z) atTop
        (𝓝 (∫ q, bellmanOriginExtension phi (q.1 - Y, q.2) -
          bellmanOriginExtension phi (z.1 - Y, z.2) ∂kernelXV E T z)) := by
      apply tendsto_integral_of_dominated_convergence g (fun n => (hfm n).aestronglyMeasurable) hgi
        (fun n => Eventually.of_forall (hfb n))
      filter_upwards with q
      exact (barrier_position_mollifier_tendsto h ha (q.1 - Y, q.2)).sub
        (barrier_position_mollifier_tendsto h ha (z.1 - Y, z.2))
    apply hlim.congr'
    filter_upwards with n
    have hdiff :=
      hgi.mono' (hfm n).aestronglyMeasurable (Eventually.of_forall (hfb n))
    have hi : Integrable (fun q : Z => Phi n (q.1 - Y, q.2)) (kernelXV E T z) := by
      convert hdiff.add (integrable_const (Phi n (z.1 - Y, z.2))) using 1
      funext q
      simp only [Pi.add_apply, f]
      ring
    change (∫ q, Phi n (q.1 - Y, q.2) - Phi n (z.1 - Y, z.2) ∂kernelXV E T z) = _
    rw [integral_sub hi (integrable_const _), integral_const, smul_eq_mul, measureReal_def,
      kernelXV_mass_one hlam A E hE, ENNReal.toReal_one, one_mul]
  have deterministic_regularized_barrier_green (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta) :
      let E := fullSpaceEvolution hH hLE hlam hLam A
    let Phi := positionConvolution eta (bellmanOriginExtension phi)
    ENNReal.ofReal c *
      (∫⁻ q, ENNReal.ofReal (positionConvolution eta
        (fun w => bellmanGauge w ^ (alpha - 2)) (q.1 - Y, q.2))
          ∂physicalOccupationMeasure E z T) ≤
      ENNReal.ofReal ((∫ q, Phi (q.1 - Y, q.2) ∂kernelXV E T z) - Phi (z.1 - Y, z.2)) := by
    have barrier_smoothed_velocity_bounded :
        ∃ Bv : ℝ, 0 ≤ Bv ∧ ∀ q : ℝ × ℝ,
        |deriv (fun v => positionConvolution eta (bellmanOriginExtension phi) (q.1, v)) q.2| ≤ Bv := by
      have barrier_smoothed_velocity_far :
          ∃ S Cv : ℝ, 0 < S ∧ 0 ≤ Cv ∧ ∀ q : ℝ × ℝ,
          S + 1 < |q.1| ∨ 1 ≤ |q.2| →
          |deriv (fun v => positionConvolution eta (bellmanOriginExtension phi) (q.1, v)) q.2| ≤ Cv := by
        have barrier_convolution_far_gauge (S : ℝ) (hb : ∀ x ∈ tsupport eta, |x| < S) (q : ℝ × ℝ) (hq : S + 1 < |q.1| ∨ 1 ≤ |q.2|) (Y : ℝ) (hη : eta (q.1 - Y) ≠ 0) :
            1 ≤ bellmanGauge (Y, q.2) := by
          rcases hq with hx | hv
          · have he := hb (q.1 - Y) (subset_tsupport eta hη)
            have ht : |q.1| ≤ |q.1 - Y| + |Y| := by
              calc
                |q.1| = |q.1 - Y + Y| := by congr 1; ring
                _ ≤ _ := abs_add_le _ _
            have hY : 1 ≤ |Y| := by linarith only [hx, he, ht]
            exact (Real.one_le_rpow hY (by norm_num : 0 ≤ (1 / 3 : ℝ))).trans
              (BarrierRegularization.barrier_position_gauge_lower (Y, q.2))
          · exact hv.trans (bellmanGauge_coordinate_bounds (Y, q.2)).2
        obtain ⟨S, hS, hbS⟩ := heta.2.1.isBounded.exists_pos_norm_lt
        have hbS' : ∀ x ∈ tsupport eta, |x| < S := by
          simpa only [Real.norm_eq_abs] using hbS
        obtain ⟨_, _, hv, _⟩ := h.origin_jet_bounds
        obtain ⟨Cv, hCv, hbv⟩ := hv
        refine ⟨S, Cv, hS, hCv, fun q hq => ?_⟩
        rw [((barrier_position_convolution_velocity_jets h ha ha1 eta heta q.1 q.2).1).deriv]
        have hi := position_kernel_integrable eta (fun Y => bellmanDv phi (Y, q.2))
          heta.1.continuous heta.2.1
          (barrier_velocity_fibers_locallyIntegrable h ha ha1 q.2).1 q.1
        have hηi : Integrable eta volume :=
          heta.1.continuous.integrable_of_hasCompactSupport heta.2.1
        have hbound (Y : ℝ) : |eta (q.1 - Y) * bellmanDv phi (Y, q.2)| ≤
            eta (q.1 - Y) * Cv := by
          by_cases hη : eta (q.1 - Y) = 0
          · simp only [hη, zero_mul, abs_zero, le_refl]
          have hρ := barrier_convolution_far_gauge S hbS' q hq Y hη
          have hn := BarrierRegularization.barrier_gauge_one_ne_zero hρ
          have hv := (hbv (Y, q.2) hn).trans
            (mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hρ (by linarith)) hCv)
          rw [mul_one] at hv
          rw [abs_mul, abs_of_nonneg (heta.2.2.1 _)]
          exact mul_le_mul_of_nonneg_left hv (heta.2.2.1 _)
        unfold positionConvolution
        calc
          _ ≤ ∫ Y, |eta (q.1 - Y) * bellmanDv phi (Y, q.2)| := abs_integral_le_integral_abs
          _ ≤ ∫ Y, eta (q.1 - Y) * Cv :=
            integral_mono hi.abs ((hηi.comp_sub_left q.1).mul_const Cv) hbound
          _ = Cv := by
            rw [integral_mul_const, integral_sub_left_eq_self, heta.2.2.2, one_mul]
      let f := positionConvolution eta (bellmanOriginExtension phi)
      have hf := barrier_position_regularization_joint h ha ha1 eta heta
      have hc : Continuous (fun q : ℝ × ℝ => (fderiv ℝ f q) (0, 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ (0, 1)).continuous.comp (hf.continuous_fderiv (by norm_num))
      have he (q : ℝ × ℝ) : deriv (fun v => f (q.1, v)) q.2 = (fderiv ℝ f q) (0, 1) :=
        (bellman_hasDerivAt_second (hf.differentiable (by norm_num) q)).deriv
      obtain ⟨S, Cv, hS, hCv, hbfar⟩ := barrier_smoothed_velocity_far
      obtain ⟨B, hb⟩ := ((isCompact_Icc (a := -(S + 1)) (b := S + 1)).prod
        (isCompact_Icc (a := -1) (b := 1))).exists_bound_of_continuousOn hc.continuousOn
      refine ⟨max B Cv, hCv.trans (le_max_right _ _), fun q => ?_⟩
      by_cases hq : q ∈ Icc (-(S + 1)) (S + 1) ×ˢ Icc (-1) 1
      · rw [he q]
        have hqb : |(fderiv ℝ f q) (0, 1)| ≤ B := by
          simpa only [Real.norm_eq_abs] using hb q hq
        exact hqb.trans (le_max_left _ _)
      · have hfar : S + 1 < |q.1| ∨ 1 ≤ |q.2| := by
          by_contra hn
          push Not at hn
          exact hq ⟨abs_le.mp hn.1, (abs_le.mp hn.2.le)⟩
        exact (hbfar q hfar).trans (le_max_right _ _)
    let E := fullSpaceEvolution hH hLE hlam hLam A
    let Phi := positionConvolution eta (bellmanOriginExtension phi)
    let f := fun q : Z => Phi (q.1 - Y, q.2)
    let w := fun q : Z => positionConvolution eta
      (fun u => bellmanGauge u ^ (alpha - 2)) (q.1 - Y, q.2)
    have hE := fullSpaceEvolution_spec hH hLE hlam hLam A
    let : IsProbabilityMeasure (kernelXV E T z) := ⟨kernelXV_mass_one hlam A E hE T z⟩
    have hPhi := barrier_position_regularization_joint h ha ha1 eta heta
    have hf : ContDiff ℝ 2 f := hPhi.comp
      ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
    obtain ⟨D, hD, hm⟩ := BarrierRegularization.barrier_coordinate_modulus h ha ha1
    have hconvmod := positionConvolution_modulus eta heta (bellmanOriginExtension phi)
      (h.origin_extension_continuous ha) alpha D hD hm
    have hfm (q u : Z) : |f q - f u| ≤
        D * (|q.1 - u.1| ^ (alpha / 3) + |q.2 - u.2| ^ alpha) := by
      have he : q.1 - Y - (u.1 - Y) = q.1 - u.1 := by ring
      simpa only [f, Prod.fst, Prod.snd, he] using hconvmod (q.1 - Y, q.2) (u.1 - Y, u.2)
    obtain ⟨Bv, hBv, hbv⟩ := barrier_smoothed_velocity_bounded
    have hfbv (q : Z) : |deriv (fun v => f (q.1, v)) q.2| ≤ Bv := hbv (q.1 - Y, q.2)
    have hw : Measurable w := (positionConvolution_measurable eta heta.1.continuous.measurable
      _ (bellmanGauge_continuous.measurable.pow_const _)).comp
        ((measurable_fst.sub measurable_const).prodMk measurable_snd)
    have hwn (q : Z) : 0 ≤ w q := integral_nonneg
      (fun X => mul_nonneg (heta.2.2.1 _) (Real.rpow_nonneg (bellmanGauge_nonneg _) _))
    have hfbound (q : Z) : c * w q ≤ physicalSpatialOperator A.a f q :=
      (barrier_position_regularization_of_positive_degree ha ha1 h hbound eta heta).2 A Y q
    have hfi : Integrable f (kernelXV E T z) := by
      convert ((deterministic_barrier_endpoint_of_modulus hH hLE hlam hLam alpha D ha.le ha1.le hD Phi hPhi.continuous hconvmod A z T Y).1).add (integrable_const (Phi (z.1 - Y, z.2))) using 1
      funext q
      simp only [Pi.add_apply, f]
      rw [show q.1 - Y = -Y + q.1 by ring]
      ring
    exact barrier_green_cutoff_removal E hE f hf D Bv
      ha.le ha1.le hD hBv hfm hfbv w hw hwn hfbound hfi
  have regularizedBarrierWeight_measurable (n : ℕ) : Measurable (regularizedBarrierWeight alpha n) :=
    positionConvolution_measurable _ (barrierMollifier_spec n).1.continuous.measurable _
        (bellmanGauge_continuous.measurable.pow_const _)
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let f := fun n : ℕ => fun q : Z => ENNReal.ofReal c *
    ENNReal.ofReal (regularizedBarrierWeight alpha n (q.1 - Y, q.2))
  let F := fun q : Z => ENNReal.ofReal c * rhoWeight (gamma alpha) (q.1 - Y, q.2)
  let b := fun n : ℕ =>
    (∫ q, positionConvolution (barrierMollifier n) (bellmanOriginExtension phi)
      (q.1 - Y, q.2) ∂kernelXV E T z) -
    positionConvolution (barrierMollifier n) (bellmanOriginExtension phi) (z.1 - Y, z.2)
  have hm (n : ℕ) : Measurable (f n) := measurable_const.mul
    (ENNReal.measurable_ofReal.comp ((regularizedBarrierWeight_measurable n).comp
      ((measurable_fst.sub_const Y).prodMk measurable_snd)))
  have hp (q : Z) : Tendsto (fun n => f n q) atTop (𝓝 (F q)) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).tendsto
      (rhoWeight (gamma alpha) (q.1 - Y, q.2)) |>.comp
        (regularizedBarrierWeight_tendsto (q.1 - Y, q.2))
  have hi (n : ℕ) : (∫⁻ q, f n q ∂physicalOccupationMeasure E z T) ≤
      ENNReal.ofReal (b n) := by
    rw [show f n = fun q => ENNReal.ofReal c *
      ENNReal.ofReal (regularizedBarrierWeight alpha n (q.1 - Y, q.2)) from rfl,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact deterministic_regularized_barrier_green
      _ (barrierMollifier_spec n)
  simpa only [F, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] using (singular_fatou_of_real_bounds (physicalOccupationMeasure E z T) f F hm hp b _ (barrier_mollifier_endpoint_tendsto) hi)



/-- The literal source box occupation estimate, with its constant before all dynamic data. -/
theorem deterministic_box_occupation
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) - 2 < alpha)
    (ha1 : alpha < 1) (A0 M : ℝ) (hA0 : 0 < A0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (z : Z) (Y r : ℝ) (T : NNReal),
      0 < r → |z.2| ≤ M * Real.sqrt (T : ℝ) →
      (∫ t in Ioc 0 (T : ℝ),
        (kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t) z
          (box A0 r Y)).toReal) ≤ C * r ^ (gamma alpha) * (T : ℝ) ^ (alpha / 2)   := by
  have box_measure_le_weight (mu : Measure Z) {r : ℝ} {Y : ℝ} {g : ℝ} (hr : 0 < r) (hg : 0 ≤ g) :
      mu (box A0 r Y) ≤ ENNReal.ofReal (((A0^2+A0^6)^(1/6 : ℝ)*r)^g)*
      ∫⁻ z, rhoWeight g (z.1-Y,z.2) ∂mu := by
    have box_indicator_le_weight (z : Z) :
        (box A0 r Y).indicator (fun _ => 1) z ≤
        ENNReal.ofReal (((A0^2+A0^6)^(1/6 : ℝ)*r)^g)*rhoWeight g (z.1-Y,z.2) := by
      by_cases hz : z ∈ box A0 r Y
      · rw [indicator_of_mem hz]
        let D : ℝ := (A0^2+A0^6)^(1/6 : ℝ)*r
        have hD : 0 < D := by dsimp only [D]; positivity
        have hC : 0 < D^g := Real.rpow_pos_of_pos hD _
        have hb : (ENNReal.ofReal (rho (z.1-Y,z.2)))^g ≤ ENNReal.ofReal (D^g) := by
          exact (ENNReal.rpow_le_rpow
            (ENNReal.ofReal_le_ofReal (box_rho_le hA0 hr hz)) hg).trans_eq
              (ENNReal.ofReal_rpow_of_pos hD)
        have hi := ENNReal.inv_le_inv' hb
        rw [← ENNReal.rpow_neg] at hi
        calc
          1 = ENNReal.ofReal (D^g)*(ENNReal.ofReal (D^g))⁻¹ :=
            (ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_lt_top.ne).symm
          _ ≤ _ := mul_le_mul le_rfl hi bot_le bot_le
      · rw [indicator_of_notMem hz]
        exact bot_le
    rw [← lintegral_indicator_one (box_measurable A0 r Y)]
    apply (lintegral_mono (box_indicator_le_weight)).trans_eq
    exact lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne
  have deterministic_barrier_occupation_uniform :
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) (Y : ℝ),
        0 < (T : ℝ) → |z.2| ≤ M * Real.sqrt (T : ℝ) →
        let E := fullSpaceEvolution hH hLE hlam hLam A
        ENNReal.ofReal c *
          (∫⁻ q, rhoWeight (gamma alpha) (q.1 - Y, q.2)
            ∂physicalOccupationMeasure E z T) ≤
          ENNReal.ofReal (C * (T : ℝ) ^ (alpha / 2)) := by
    have deterministic_barrier_endpoint_uniform {alpha : ℝ} {phi : Z → ℝ} (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1) (M : ℝ) :
        ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) (Y : ℝ),
        |z.2| ≤ M * Real.sqrt (T : ℝ) →
        let E := fullSpaceEvolution hH hLE hlam hLam A
        Integrable (fun w : Z => bellmanOriginExtension phi (w.1 - Y, w.2) -
          bellmanOriginExtension phi (z.1 - Y, z.2)) (kernelXV E T z) ∧
        (∫ w, |bellmanOriginExtension phi (w.1 - Y, w.2) -
          bellmanOriginExtension phi (z.1 - Y, z.2)| ∂kernelXV E T z) ≤
          C * (T : ℝ) ^ (alpha / 2) := by
      have deterministic_barrier_endpoint_uniform_of_modulus (B : ℝ) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hB : 0 ≤ B) (Phi : Z → ℝ) (hPhi : Continuous Phi) (hmod : ∀ z w : Z, |Phi z-Phi w| ≤
          B*(|z.1-w.1|^(alpha/3)+|z.2-w.2|^alpha)) :
          ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) (Y : ℝ),
          |z.2| ≤ M*Real.sqrt (T : ℝ) →
          let E := fullSpaceEvolution hH hLE hlam hLam A
          Integrable (fun w : Z => Phi (w.1-Y,w.2)-Phi (z.1-Y,z.2)) (kernelXV E T z) ∧
            (∫ w, |Phi (w.1-Y,w.2)-Phi (z.1-Y,z.2)| ∂kernelXV E T z) ≤
              C*(T : ℝ)^(alpha/2) := by
        let D := 2*M^2+4/3*Lam
        let C0 := B*(D^(alpha/6)+(2*Lam)^(alpha/2))
        have hL : 0 ≤ Lam := hlam.le.trans hLam
        have hD : 0 ≤ D := by dsimp only [D]; positivity
        have hC : 0 ≤ C0 := by
          exact mul_nonneg hB (add_nonneg (Real.rpow_nonneg hD _) (Real.rpow_nonneg (by positivity) _))
        refine ⟨C0+1, by linarith, ?_⟩
        intro A z T Y hv
        have h := deterministic_barrier_endpoint_of_modulus hH hLE hlam hLam
          alpha B ha0 ha1 hB Phi hPhi hmod A z T Y
        refine ⟨h.1, h.2.trans ?_⟩
        have hp : 0 ≤ 2*z.2^2*(T : ℝ)^2+4/3*Lam*(T : ℝ)^3 := by
          positivity
        have hbound := Real.rpow_le_rpow hp (position_moment_scale_le T.property hv)
          (show 0 ≤ alpha/6 by linarith)
        have he : ((T : ℝ)^3)^(alpha/6) = (T : ℝ)^(alpha/2) := by
          exact (Real.rpow_natCast_mul T.property 3 (alpha/6)).symm.trans
            (congrArg (fun a : ℝ => (T : ℝ)^a) (by ring))
        have hpos : (D*(T : ℝ)^3)^(alpha/6) = D^(alpha/6)*(T : ℝ)^(alpha/2) :=
          (Real.mul_rpow hD (pow_nonneg T.property 3)).trans
            (congrArg (fun a : ℝ => D^(alpha/6)*a) he)
        have hvel : (2*Lam*(T : ℝ))^(alpha/2) = (2*Lam)^(alpha/2)*(T : ℝ)^(alpha/2) :=
          Real.mul_rpow (by positivity) T.property
        calc
          _ ≤ B*((D*(T : ℝ)^3)^(alpha/6)+(2*Lam*(T : ℝ))^(alpha/2)) :=
            mul_le_mul_of_nonneg_left (add_le_add hbound le_rfl) hB
          _ = C0*(T : ℝ)^(alpha/2) := by
            rw [hpos, hvel]
            change B*(D^(alpha/6)*(T : ℝ)^(alpha/2)+
              (2*Lam)^(alpha/2)*(T : ℝ)^(alpha/2)) =
                (B*(D^(alpha/6)+(2*Lam)^(alpha/2)))*(T : ℝ)^(alpha/2)
            ring
          _ ≤ (C0+1)*(T : ℝ)^(alpha/2) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg T.property _)
      obtain ⟨B, hB, hb⟩ := BarrierRegularization.barrier_coordinate_modulus h ha ha1
      exact deterministic_barrier_endpoint_uniform_of_modulus B ha.le ha1.le hB _ (h.origin_extension_continuous ha) hb
    obtain ⟨hlo, _, _⟩ := exists_bellman_barrier lam Lam hlam hLam
    have ha0 : 0 < alpha := lt_of_le_of_lt (sub_nonneg.mpr hlo) ha
    obtain ⟨phi, c, D, h, hc, _, hbound, _⟩ :=
      exists_bellman_barrier_with_modulus lam Lam hlam hLam alpha ha ha1
    obtain ⟨C, hC, hendpoint⟩ :=
      deterministic_barrier_endpoint_uniform h ha0 ha1 M
    refine ⟨c, C, hc, hC, ?_⟩
    intro A z T Y hT hz
    have he := hendpoint A z T Y hz
    apply (deterministic_barrier_green_fatou hH hLE hlam hLam h ha0 ha1 hc hbound
      A z T hT Y).trans
    apply ENNReal.ofReal_le_ofReal
    apply (integral_mono he.1 he.1.abs (fun q => le_abs_self _)).trans he.2
  obtain ⟨hlo, _, _⟩ := exists_bellman_barrier lam Lam hlam hLam
  have ha0 : 0 < alpha := lt_of_le_of_lt (sub_nonneg.mpr hlo) ha
  have hg : 0 < gamma alpha := by dsimp only [gamma]; linarith
  obtain ⟨c, B, hc, hB, hb⟩ :=
    deterministic_barrier_occupation_uniform
  let D : ℝ := (A0 ^ 2 + A0 ^ 6) ^ (1 / 6 : ℝ)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D ^ (gamma alpha) * B / c, by positivity, ?_⟩
  intro A z Y r T hr hz
  let E := fullSpaceEvolution hH hLE hlam hLam A
  by_cases hT : (T : ℝ) = 0
  · simp only [hT, Ioc_self, Measure.restrict_empty, integral_zero_measure]
    positivity
  have hTp : 0 < (T : ℝ) := lt_of_le_of_ne T.property (Ne.symm hT)
  have hw : (∫⁻ q, rhoWeight (gamma alpha) (q.1 - Y, q.2) ∂physicalOccupationMeasure E z T) ≤ ENNReal.ofReal (B * (T : ℝ) ^ (alpha / 2) / c) := by
    have hh := mul_le_mul (le_refl ((ENNReal.ofReal c)⁻¹)) (hb A z T Y hTp hz) bot_le bot_le
    rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hc).ne'
      ENNReal.ofReal_ne_top, one_mul] at hh
    exact hh.trans_eq (by
      rw [ENNReal.ofReal_div_of_pos hc]
      simp only [div_eq_mul_inv]
      exact mul_comm _ _)
  have hbox := (box_measure_le_weight (physicalOccupationMeasure E z T) hr hg.le).trans
    (mul_le_mul le_rfl hw bot_le bot_le)
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg hD.le hr.le) _)] at hbox
  have he : (D * r) ^ (gamma alpha) * (B * (T : ℝ) ^ (alpha / 2) / c) =
      (D ^ (gamma alpha) * B / c) * r ^ (gamma alpha) * (T : ℝ) ^ (alpha / 2) := by
    rw [Real.mul_rpow hD.le hr.le]
    ring
  rw [he, physicalOccupationMeasure_apply _ _ _ _ (box_measurable A0 r Y),
    ← box_occupation_ofReal_integral] at hbox
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbox

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

