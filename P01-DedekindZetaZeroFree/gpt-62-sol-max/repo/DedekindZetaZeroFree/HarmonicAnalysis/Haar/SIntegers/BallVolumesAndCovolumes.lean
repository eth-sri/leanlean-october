module

public import ClassFieldTheory.AlgebraicNumberTheory.Completion.IntegerRingComparison
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompletionBallMass
public import DedekindZetaZeroFree.Arithmetic.LocalFields.DifferentDiscriminantNormalization

@[expose] public section

section

noncomputable section
open scoped Classical nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree
namespace PoissonS

attribute [local instance] completionMeasurable completionBorel

def finiteBall (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ) :
    Set (PoissonFinite.Space F S) :=
  {x | ∀ v : S, ‖x v‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v)}

def ballFractionalIdeal (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ) :
    FractionalIdeal (RingOfIntegers F)⁰ F :=
  ∏ v : S, (FractionalIdeal.coeIdeal v.val.asIdeal) ^ k v

def ballArchLattice (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ) :
    Submodule ℤ (PoissonArch.Space F) :=
  Submodule.map
    (((NumberField.mixedEmbedding.euclidean.toMixed F).symm.toLinearMap.restrictScalars ℤ).comp
      (NumberField.mixedEmbedding F).toIntAlgHom.toLinearMap)
    ((ballFractionalIdeal F S k : Submodule (RingOfIntegers F) F).restrictScalars ℤ)

def finiteBallVolume (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ)
    (μ : (v : S) → Measure (v.val.adicCompletion F)) : ℝ :=
  (Measure.pi μ).real (finiteBall F S k)

def ballArchCovolume (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ) : ℝ :=
  ZLattice.covolume (ballArchLattice F S k) (PoissonArch.traceMeasure F)

theorem ballFractionalIdeal_ne_zero (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ) :
    ballFractionalIdeal F S k ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  apply zpow_ne_zero
  exact FractionalIdeal.coeIdeal_ne_zero.mpr v.val.ne_bot

theorem ballArchLattice_eq (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ) :
    ballArchLattice F S k = PoissonArch.idealLattice F
      (Units.mk0 (ballFractionalIdeal F S k) (ballFractionalIdeal_ne_zero F S k)) := by
  ext y
  rw [PoissonArch.mem_idealLattice]
  change (∃ x : F, x ∈ ballFractionalIdeal F S k ∧ _ = y) ↔ _
  rfl

theorem ballArchCovolume_eq (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ) :
    ballArchCovolume F S k = Real.sqrt |(NumberField.discr F : ℝ)| *
      ∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ k v := by
  rw [ballArchCovolume, ballArchLattice_eq]
  rw [← PoissonArch.covolume, PoissonArch.covolume_eq_sqrt_discr_mul_absNorm]
  congr 1
  simp [ballFractionalIdeal, map_prod, map_zpow₀, FractionalIdeal.coeIdeal_absNorm]

theorem completion_secondCountable (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) : SecondCountableTopology (v.adicCompletion F) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (v.denseRange_algebraMap F)
  infer_instance
attribute [local instance] completion_secondCountable

theorem completion_sigmaFinite (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure] (hnorm : LocalNormalization F S μ)
    (v : S) : SigmaFinite (μ v) := by
  letI : IsLocallyFiniteMeasure (μ v) :=
    isLocallyFiniteMeasure_of_vaddInvariant (v.val.adicCompletion F)
      (show IsOpen {x : v.val.adicCompletion F | ‖x‖ ≤ 1} from by
        simpa [Metric.closedBall, dist_zero_right] using
          IsUltrametricDist.isOpen_closedBall (0 : v.val.adicCompletion F) one_ne_zero)
      ⟨0, by simp⟩ (by rw [hnorm v]; exact ENNReal.ofReal_ne_top)
  infer_instance

theorem integerVolume_pos (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) : 0 < integerVolume F v := by
  have hqv : (0 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
    have := NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (lt_trans Nat.zero_lt_one this)
  unfold integerVolume
  exact inv_pos.mpr (Real.sqrt_pos.mpr (zpow_pos hqv _))

theorem local_ball_volume (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (μv : Measure (v.adicCompletion F)) [μv.IsAddHaarMeasure]
    (h1 : μv {x | ‖x‖ ≤ 1} = ENNReal.ofReal (integerVolume F v)) (k : ℤ) :
    μv.real {x | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-k)}
      = (v.asIdeal.absNorm : ℝ) ^ (-k) * integerVolume F v := by
  rw [CompletionHaarModule.closedBall_measure F v μv (-k), Measure.real, h1,
    ENNReal.toReal_ofReal (integerVolume_pos F v).le]

theorem finiteBallVolume_eq_prod (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure] (hnorm : LocalNormalization F S μ) :
    finiteBallVolume F S k μ = ∏ v : S,
      (μ v).real {x | ‖x‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v)} := by
  letI : ∀ v, SigmaFinite (μ v) := fun v => completion_sigmaFinite F S μ hnorm v
  unfold finiteBallVolume finiteBall
  have hset : {x : PoissonFinite.Space F S | ∀ v : S,
      ‖x v‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v)} =
      Set.pi Set.univ (fun v => {x | ‖x‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v)}) := by
    ext x
    simp
  rw [hset]
  simp [Measure.real, Measure.pi_pi, ENNReal.toReal_prod]

theorem ball_measure_balance (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (hS : ContainsDifferent F S)
    (k : (v : S) → ℤ) (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure] (hnorm : LocalNormalization F S μ) :
    0 < finiteBallVolume F S k μ ∧
    0 < ballArchCovolume F S k ∧
    ballArchCovolume F S k * finiteBallVolume F S k μ = 1 ∧
    finiteBallVolume F S k μ = (ballArchCovolume F S k)⁻¹ := by
  have hqv : ∀ v : S, (0 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := by
    intro v
    have := NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v.val
    exact_mod_cast (lt_trans Nat.zero_lt_one this)

  have hvol : finiteBallVolume F S k μ =
      ∏ v : S, ((v.val.asIdeal.absNorm : ℝ) ^ (- k v) * integerVolume F v.val) := by
    rw [finiteBallVolume_eq_prod F S k μ hnorm]
    exact Finset.prod_congr rfl (fun v _ =>
      local_ball_volume F v.val (μ v) (hnorm v) (k v))

  have hcov := ballArchCovolume_eq F S k

  have hprod : ∏ v : S, ((v.val.asIdeal.absNorm : ℝ) ^ differentExponent F v.val).sqrt
      = Real.sqrt |(NumberField.discr F : ℝ)| :=
    BallMeasureBalance.prod_sqrt_absNorm_pow_differentExponent F S hS
  have hsqrt_pos : 0 < Real.sqrt |(NumberField.discr F : ℝ)| := by
    apply Real.sqrt_pos.mpr
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  have hP_pos : 0 < ∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ (k v) :=
    Finset.prod_pos (fun v _ => zpow_pos (hqv v) _)
  have hP_ne : (∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ (k v)) ≠ 0 := ne_of_gt hP_pos
  have h1 : (∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ (- k v))
      = (∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ (k v))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl (fun v _ => zpow_neg _ _)
  have h2 : (∏ v : S, integerVolume F v.val)
      = (Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ := by
    have : (∏ v : S, integerVolume F v.val)
        = (∏ v : S, ((v.val.asIdeal.absNorm : ℝ) ^ differentExponent F v.val).sqrt)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      simp only [integerVolume]
    rw [this, hprod]
  have hvol' : finiteBallVolume F S k μ =
      (∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ (k v))⁻¹ *
        (Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ := by
    rw [hvol, Finset.prod_mul_distrib, h1, h2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hvol]
    exact Finset.prod_pos (fun v _ => mul_pos (zpow_pos (hqv v) _) (integerVolume_pos F v.val))
  · rw [hcov]
    exact mul_pos hsqrt_pos hP_pos
  · rw [hcov, hvol']
    field_simp
  · rw [hcov, hvol', mul_inv_rev]

end PoissonS
end DedekindZetaZeroFree

end

end
