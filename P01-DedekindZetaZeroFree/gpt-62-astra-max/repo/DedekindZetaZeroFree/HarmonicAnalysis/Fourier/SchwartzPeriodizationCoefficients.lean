module

public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.LatticeDecay
public import DedekindZetaZeroFree.Theta.Profiles.FractionalIdealShapeLattice

@[expose] public section

noncomputable section

open Module MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

section

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L)
    (f : SchwartzMap E ℂ)

theorem continuous_intPeriodization_coordinateSchwartz :
    Continuous (intPeriodization
      (fun x => f ((b.ofZLatticeBasis ℝ L).equivFun.symm x))) := by
  classical
  have hF : Summable (coordinateSchwartzTranslate L b f) := by
    apply ContinuousMap.summable_of_locally_summable_norm
    intro K
    exact schwartzLatticeDecay_coordinates L b f K
  have heval (x : ι → ℝ) :
      (∑' n, coordinateSchwartzTranslate L b f n) x =
        intPeriodization
          (fun x => f ((b.ofZLatticeBasis ℝ L).equivFun.symm x)) x := by
    rw [← ContinuousMap.tsum_apply hF x]
    rfl
  rw [show intPeriodization
        (fun x => f ((b.ofZLatticeBasis ℝ L).equivFun.symm x)) =
      fun x => (∑' n, coordinateSchwartzTranslate L b f n) x from
    funext fun x => (heval x).symm]
  exact (∑' n, coordinateSchwartzTranslate L b f n).continuous

def schwartzTorusPeriodization : C(UnitAddTorus ι, ℂ) :=
  torusPeriodization
    (fun x => f ((b.ofZLatticeBasis ℝ L).equivFun.symm x))
    (continuous_intPeriodization_coordinateSchwartz L b f)

@[simp] theorem schwartzTorusPeriodization_apply_quotient (x : ι → ℝ) :
    schwartzTorusPeriodization L b f (torusQuotientMap x) =
      ∑' k : ι → ℤ,
        f ((b.ofZLatticeBasis ℝ L).equivFun.symm
          (x + fun i => (k i : ℝ))) := torusPeriodization_apply_quotient _ _ x

noncomputable def coordinateFourierSchwartz (n : ι → ℤ) (x : ι → ℝ) : ℂ :=
  coordinateFourierCharacter n x *
    f ((b.ofZLatticeBasis ℝ L).equivFun.symm x)

noncomputable def coordinateFourierSchwartzTranslate (n k : ι → ℤ)
    (x : ι → ℝ) : ℂ :=
  coordinateFourierCharacter n x *
    f ((b.ofZLatticeBasis ℝ L).equivFun.symm
      (x + fun i => (k i : ℝ)))

end

noncomputable def ambientFourierSchwartz (f : SchwartzMap E ℂ)
    (w y : E) : ℂ :=
  𝐞 (-(inner ℝ y w)) • f y

private alias continuous_coordinateFourierCharacter := GaussianLattice.continuous_coordinateFourierCharacter

private alias coordinateFourierCharacter_add_intPi := GaussianLattice.coordinateFourierCharacter_add_intPi

section

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L)
    (f : SchwartzMap E ℂ)

private theorem continuous_coordinateFourierSchwartz (n : ι → ℤ) :
    Continuous (coordinateFourierSchwartz L b f n) := by
  unfold coordinateFourierSchwartz
  exact (continuous_coordinateFourierCharacter n).mul
    (f.continuous.comp (LinearEquiv.toContinuousLinearEquiv
      (b.ofZLatticeBasis ℝ L).equivFun.symm).continuous)

private theorem continuous_coordinateFourierSchwartzTranslate (n k : ι → ℤ) :
    Continuous (coordinateFourierSchwartzTranslate L b f n k) := by
  unfold coordinateFourierSchwartzTranslate
  refine (continuous_coordinateFourierCharacter n).mul ?_
  exact f.continuous.comp
    ((LinearEquiv.toContinuousLinearEquiv
      (b.ofZLatticeBasis ℝ L).equivFun.symm).continuous.comp
        (continuous_id.add continuous_const))

private theorem coordinateFourierSchwartz_add_intPi (n k : ι → ℤ) (x : ι → ℝ) :
    coordinateFourierSchwartz L b f n ((fun i => (k i : ℝ)) + x) =
      coordinateFourierSchwartzTranslate L b f n k x := by
  rw [coordinateFourierSchwartz, coordinateFourierSchwartzTranslate,
    coordinateFourierCharacter_add_intPi]
  congr 1
  rw [add_comm]

end

private theorem coordinateFourierSchwartz_eq_ambient [DecidableEq ι]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (f : SchwartzMap E ℂ) (n : ι → ℤ) (x : ι → ℝ) :
    coordinateFourierSchwartz L b f n x =
      ambientFourierSchwartz f (dualLatticePoint L b n)
        ((b.ofZLatticeBasis ℝ L).equivFun.symm x) := by
  rw [coordinateFourierSchwartz, ambientFourierSchwartz,
    coordinateFourierCharacter, mFourier_neg_torusQuotientMap,
    real_inner_comm,
    inner_dualLatticePoint_ofZLatticeBasis_equivFun_symm]
  simp only [Circle.smul_def, Real.fourierChar_apply]
  push_cast
  ring_nf

section

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L)
    (f : SchwartzMap E ℂ) (n : ι → ℤ)

private theorem integrable_coordinateFourierSchwartz :
    Integrable (coordinateFourierSchwartz L b f n) := by
  refine (integrable_comp_ofZLatticeBasis_equivFun_symm L b f.integrable).congr'
    (continuous_coordinateFourierSchwartz L b f n).aestronglyMeasurable ?_
  filter_upwards with x
  rw [coordinateFourierSchwartz, norm_mul, norm_coordinateFourierCharacter,
    one_mul]

private theorem summable_integral_norm_coordinateFourierSchwartzTranslate :
    Summable (fun k : ι → ℤ =>
      ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
        ‖coordinateFourierSchwartzTranslate L b f n k x‖) := by
  classical
  let S : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc 0 1}
  let K : TopologicalSpace.Compacts (ι → ℝ) :=
    ⟨Icc (0 : ι → ℝ) 1, isCompact_Icc⟩
  have hSK : S ⊆ K := fun x hx =>
    ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩
  have hbound (k : ι → ℤ) :
      ∫ x in S, ‖coordinateFourierSchwartzTranslate L b f n k x‖ ≤
        volume.real S *
          ‖(coordinateSchwartzTranslate L b f k).restrict K‖ := by
    calc
      _ ≤
          ∫ _x in S,
            ‖(coordinateSchwartzTranslate L b f k).restrict K‖ := by
        apply integral_mono_ae (((continuous_coordinateFourierSchwartzTranslate L b f n k).norm.integrableOn_Icc).mono_set hSK) (integrableOn_const (ne_of_lt (lt_of_le_of_lt (measure_mono hSK) K.2.measure_lt_top)))
        filter_upwards [ae_restrict_mem measurableSet_pi_Ioc] with x hx
        rw [coordinateFourierSchwartzTranslate, norm_mul,
          norm_coordinateFourierCharacter, one_mul]
        exact ContinuousMap.norm_coe_le_norm
          ((coordinateSchwartzTranslate L b f k).restrict K) ⟨x, hSK hx⟩
      _ = volume.real S *
          ‖(coordinateSchwartzTranslate L b f k).restrict K‖ := by simp
  apply Summable.of_nonneg_of_le
      (fun _ => integral_nonneg fun _ => norm_nonneg _) hbound
  exact (schwartzLatticeDecay_coordinates L b f K).mul_left (volume.real S)

private theorem integral_tsum_coordinateFourierSchwartzTranslate :
    ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
        ∑' k : ι → ℤ, coordinateFourierSchwartzTranslate L b f n k x =
      ∑' k : ι → ℤ,
        ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
          coordinateFourierSchwartzTranslate L b f n k x := by
  classical
  symm
  apply integral_tsum_of_summable_integral_norm
  · intro k
    exact ((continuous_coordinateFourierSchwartzTranslate L b f n k).integrableOn_Icc).mono_set (fun x hx =>
      ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩)
  · exact summable_integral_norm_coordinateFourierSchwartzTranslate L b f n

end

private theorem integral_ambientFourierSchwartz (f : SchwartzMap E ℂ)
    (w : E) :
    (∫ y : E, ambientFourierSchwartz f w y) =
      (FourierTransform.fourier f) w := by
  rw [show (FourierTransform.fourier f) w = 𝓕 (f : E → ℂ) w from rfl,
    Real.fourier_eq]
  rfl

private theorem toNNReal_inv_smul (c : ℝ) (hc : 0 < c) (z : ℂ) :
    (Real.toNNReal c)⁻¹ • z = (c : ℂ)⁻¹ * z := by
  rw [NNReal.smul_def, Complex.real_smul]
  congr 1
  rw [NNReal.coe_inv, Real.coe_toNNReal _ (le_of_lt hc), Complex.ofReal_inv]

private theorem integral_coordinateFourierSchwartz [DecidableEq ι]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (f : SchwartzMap E ℂ) (n : ι → ℤ) :
    (∫ x : ι → ℝ, coordinateFourierSchwartz L b f n x) =
      (ZLattice.covolume L : ℂ)⁻¹ *
        (FourierTransform.fourier f) (dualLatticePoint L b n) := by
  have hfun : (fun x : ι → ℝ => coordinateFourierSchwartz L b f n x) =
      fun x => ambientFourierSchwartz f (dualLatticePoint L b n)
        ((b.ofZLatticeBasis ℝ L).equivFun.symm x) := by
    funext x
    exact coordinateFourierSchwartz_eq_ambient L b f n x
  rw [hfun, integral_comp_ofZLatticeBasis_equivFun_symm L b
      (fun y => ambientFourierSchwartz f (dualLatticePoint L b n) y),
    integral_ambientFourierSchwartz f (dualLatticePoint L b n)]
  exact toNNReal_inv_smul (ZLattice.covolume L volume) (ZLattice.covolume_pos L volume) _

theorem mFourierCoeff_schwartzTorusPeriodization (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] [DecidableEq ι]
    (b : Basis ι ℤ L) (f : SchwartzMap E ℂ) (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (schwartzTorusPeriodization L b f) n =
      (ZLattice.covolume L : ℂ)⁻¹ *
        (FourierTransform.fourier f) (dualLatticePoint L b n) := by
  classical
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ n 0]
  simp only [Pi.zero_apply, zero_add]
  have hpoint (x : ι → ℝ) :
      UnitAddTorus.mFourier (-n) (fun i => (x i : UnitAddCircle)) •
          schwartzTorusPeriodization L b f (fun i => (x i : UnitAddCircle)) =
        ∑' k : ι → ℤ, coordinateFourierSchwartzTranslate L b f n k x := by
    rw [schwartzTorusPeriodization, show (fun i => (x i : UnitAddCircle)) = torusQuotientMap x from rfl,
      torusPeriodization_apply_quotient]
    unfold intPeriodization coordinateFourierSchwartzTranslate
      coordinateFourierCharacter
    rw [smul_eq_mul, tsum_mul_left]
  simp_rw [hpoint]
  rw [integral_tsum_coordinateFourierSchwartzTranslate L b f n,
    ← integral_coordinateFourierSchwartz L b f n,
    integral_eq_tsum_integral_pi_Ioc (coordinateFourierSchwartz L b f n)
      (integrable_coordinateFourierSchwartz L b f n)]
  apply tsum_congr
  intro k
  apply setIntegral_congr_fun measurableSet_pi_Ioc
  intro x hx
  exact (coordinateFourierSchwartz_add_intPi L b f n k x).symm

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
