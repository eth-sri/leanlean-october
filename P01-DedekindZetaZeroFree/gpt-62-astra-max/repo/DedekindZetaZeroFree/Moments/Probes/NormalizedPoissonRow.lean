module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.PrincipalProbes.CosetSummation

@[expose] public section

namespace DedekindZetaZeroFree.PoissonNormalizedRow
noncomputable section
open scoped Classical NumberField
open MeasureTheory IsDedekindDomain NumberField

variable {F : Type} [Field F] [NumberField F]

local instance completionMeasurable (v : HeightOneSpectrum (RingOfIntegers F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance localProductMeasurable
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :
    MeasurableSpace (SLocalProduct F S) := borel _

section

variable (A : SArithmeticData F)

def modulus (a : A.R) : ℝ :=
  (FiniteTransform.exteriorNorm A.R.toSubring a : ℝ)

def originalTerm (D : ComparisonPoissonCoefficientData F A)
    (W0 : SLocalProduct F A.Sf → ℂ) (s a : A.R) (hs : s ≠ 0)
    (X : ℝ) (t : A.G1) (m : A.R) : ℂ := by
  letI := D.finiteResidue s hs
  exact (Real.sqrt (modulus A s) : ℂ)⁻¹ *
    FiniteTransform.gaussSum A.R.toSubring s (D.character s) D.additiveCharacter (-m) *
    D.character a (FiniteTransform.residueMap A.R.toSubring a m) *
    W0 (sLocalDiagonal F A.Sf (m : F) *
      NormalizedProbe.asLocalPoint A
        (((t : A.G) * NormalizedProbe.radialSection A (modulus A s * X))⁻¹))

def frequencyPoint (s a : A.R)
    (X : ℝ) (t : A.G1) (h : A.R) : SLocalProduct F A.Sf :=
  NormalizedProbe.asLocalPoint A
      ((t : A.G) * NormalizedProbe.radialSection A (modulus A s * X)) *
    sLocalDiagonal F A.Sf ((h : F) / ((s : F) * (a : F)))

def frequencyTerm (D : ComparisonPoissonCoefficientData F A)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (W0 : SLocalProduct F A.Sf → ℂ) (s a : A.R) (hs : s ≠ 0) (ha : a ≠ 0)
    (X : ℝ) (t : A.G1) (h : A.R) : ℂ := by
  letI := D.finiteResidue s hs
  letI := D.finiteResidue a ha
  exact FiniteTransform.finiteCoefficient A.R.toSubring s a h
      (D.character s) (D.character a) D.additiveCharacter *
    ProbeWeight.fourier F A.Sf e μ W0 (frequencyPoint A s a X t h)

end

structure Normalization (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS) where
  localMeasure : (v : ↥A.Sf) → Measure (v.val.adicCompletion F)
  localHaar : ∀ v, (localMeasure v).IsAddHaarMeasure
  localNormalization : PoissonS.LocalNormalization F A.Sf localMeasure
  traceConductor : PoissonS.TraceConductor F A.Sf P.finiteTrace
  containsDifferent : PoissonS.ContainsDifferent F A.Sf
  sameMeasure : P.additiveMeasure =
    Measure.map (PoissonS.localProductToSpace F A.Sf).symm
      (PoissonS.productMeasure F A.Sf localMeasure)

section

variable (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)

theorem frequencyTerm_zero
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (W0 : SLocalProduct F A.Sf → ℂ)
    (hzero : ProbeWeight.fourier F A.Sf e μ W0 0 = 0)
    (s a : A.R) (hs : s ≠ 0) (ha : a ≠ 0) (X : ℝ) (t : A.G1) :
    frequencyTerm A D e μ W0 s a hs ha X t 0 =
      (letI := D.finiteResidue s hs
       letI := D.finiteResidue a ha
       FiniteTransform.finiteCoefficient A.R.toSubring s a 0
         (D.character s) (D.character a) D.additiveCharacter *
         ProbeWeight.fourier F A.Sf e μ W0 0) ∧
    frequencyTerm A D e μ W0 s a hs ha X t 0 = 0 := by
  simp [frequencyTerm, frequencyPoint, hzero]

include D in
theorem modulus_pos
    {a : A.R} (ha : a ≠ 0) : 0 < modulus A a := by apply @DedekindZetaZeroFree.ProbeCoset.modulus_pos <;> assumption

end

theorem exact_normalized_poisson_row_of_coset_dilation
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS) (N : Normalization A σ η hS P)
    (s a : A.R) (hs : s ≠ 0) (ha : a ≠ 0)
    (X : ℝ) (hX : 0 < X) (t : A.G1)
    (hsumOrig : Summable (fun m : A.R =>
      ‖originalTerm A P.coefficients P.W0 s a hs X t m‖))
    (hsumFreq : Summable (fun h : A.R =>
      ‖frequencyTerm A P.coefficients P.finiteTrace P.additiveMeasure P.W0
        s a hs ha X t h‖))
    (hrow : (Real.sqrt (modulus A s * X) : ℂ)⁻¹ *
        (∑' m : A.R, originalTerm A P.coefficients P.W0 s a hs X t m) =
      ((Real.sqrt X / modulus A a : ℝ) : ℂ) *
        ∑' h : A.R,
          frequencyTerm A P.coefficients P.finiteTrace P.additiveMeasure P.W0
            s a hs ha X t h) :
    Summable (fun m : A.R => ‖originalTerm A P.coefficients P.W0 s a hs X t m‖) ∧
    Summable (fun h : A.R =>
      ‖frequencyTerm A P.coefficients P.finiteTrace P.additiveMeasure P.W0
        s a hs ha X t h‖) ∧
    Summable (fun h : {h : A.R // h ≠ 0} =>
      ‖frequencyTerm A P.coefficients P.finiteTrace P.additiveMeasure P.W0
        s a hs ha X t h.val‖) ∧
    (Real.sqrt (modulus A s * X) : ℂ)⁻¹ *
        (∑' m : A.R, originalTerm A P.coefficients P.W0 s a hs X t m) =
      ((Real.sqrt X / modulus A a : ℝ) : ℂ) *
        ∑' h : {h : A.R // h ≠ 0},
          frequencyTerm A P.coefficients P.finiteTrace P.additiveMeasure P.W0
            s a hs ha X t h.val := by
  let frequencyTerm₀ := frequencyTerm A P.coefficients P.finiteTrace P.additiveMeasure P.W0 s a hs ha X t
  have hsub : (∑' x : {x : A.R // x ∉ ({0} : Finset A.R)},
      frequencyTerm₀ x) =
      ∑' h : A.R,
        frequencyTerm₀ h := by
    have h := (hsumFreq.of_norm.sum_add_tsum_subtype_compl ({0} : Finset A.R))
    rw [Finset.sum_singleton, ((frequencyTerm_zero A P.coefficients P.finiteTrace P.additiveMeasure P.W0
      P.zeroFrequency s a hs ha X t).2), zero_add] at h
    exact h
  have hcongr := tsum_congr_subtype (fun h : A.R =>
      frequencyTerm₀ h)
    (P := fun x : A.R => x ∉ ({0} : Finset A.R)) (Q := fun x : A.R => x ≠ 0)
    (fun x => by simp [Finset.mem_singleton])
  have heq : (∑' h : A.R,
      frequencyTerm₀ h) =
      ∑' h : {h : A.R // h ≠ 0},
        frequencyTerm₀ h.val := by
    rw [← hsub, hcongr]
  exact ⟨hsumOrig, hsumFreq, hsumFreq.subtype (fun h => h ≠ 0),
    by rw [heq] at hrow; exact hrow⟩

theorem normalized_dilation_scalar {qs qa X : ℝ}
    (hqs : 0 < qs) (hqa : 0 < qa) (hX : 0 < X) :
    (Real.sqrt (qs * X) : ℂ)⁻¹ * ((X * Real.sqrt qs / qa : ℝ) : ℂ) =
      ((Real.sqrt X / qa : ℝ) : ℂ) := by
  have hc : (Real.sqrt (qs * X) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (mul_pos hqs hX)))
  apply mul_left_cancel₀ hc
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, ← Complex.ofReal_mul]
  congr 1
  rw [Real.sqrt_mul hqs.le]
  calc
    _ = Real.sqrt qs * (Real.sqrt X * Real.sqrt X) / qa := by
      rw [(Real.mul_self_sqrt hX.le)]; ring
    _ = Real.sqrt qs * Real.sqrt X * (Real.sqrt X / qa) := by ring

variable (A : SArithmeticData F) (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (hS : A.ContainsTraceBadPlaces) (P : NormalizedProbe.PrincipalData A σ η hS)
    (N : Normalization A σ η hS P) (s a : A.R) (hs : s ≠ 0) (ha : a ≠ 0) (X : ℝ) (hX : 0 < X) (t : A.G1)

include N hX in
theorem exact_normalized_poisson_row_of_unnormalized_coset
    (hcoset :
      Summable (fun m : A.R => ‖originalTerm A P.coefficients P.W0 s a hs X t m‖) ∧
      Summable (fun h : A.R =>
        ‖frequencyTerm A P.coefficients P.finiteTrace P.additiveMeasure P.W0
          s a hs ha X t h‖) ∧
      (∑' m : A.R, originalTerm A P.coefficients P.W0 s a hs X t m) =
        ((X * Real.sqrt (modulus A s) / modulus A a : ℝ) : ℂ) *
          ∑' h : A.R,
            frequencyTerm A P.coefficients P.finiteTrace P.additiveMeasure P.W0
              s a hs ha X t h) :
    Summable (fun m : A.R => ‖originalTerm A P.coefficients P.W0 s a hs X t m‖) ∧
    Summable (fun h : A.R =>
      ‖frequencyTerm A P.coefficients P.finiteTrace P.additiveMeasure P.W0
        s a hs ha X t h‖) ∧
    Summable (fun h : {h : A.R // h ≠ 0} =>
      ‖frequencyTerm A P.coefficients P.finiteTrace P.additiveMeasure P.W0
        s a hs ha X t h.val‖) ∧
    (Real.sqrt (modulus A s * X) : ℂ)⁻¹ *
        (∑' m : A.R, originalTerm A P.coefficients P.W0 s a hs X t m) =
      ((Real.sqrt X / modulus A a : ℝ) : ℂ) *
        ∑' h : {h : A.R // h ≠ 0},
          frequencyTerm A P.coefficients P.finiteTrace P.additiveMeasure P.W0
            s a hs ha X t h.val := by
  obtain ⟨hO, hF, hrow⟩ := hcoset
  apply exact_normalized_poisson_row_of_coset_dilation
    A σ η hS P N s a hs ha X hX t hO hF
  rw [hrow, ← mul_assoc,
    normalized_dilation_scalar (modulus_pos A P.coefficients hs)
      (modulus_pos A P.coefficients ha) hX]

include N hX in
theorem exact_normalized_poisson_row :
    Summable (fun m : A.R => ‖originalTerm A P.coefficients P.W0 s a hs X t m‖) ∧
    Summable (fun h : A.R =>
      ‖frequencyTerm A P.coefficients P.finiteTrace P.additiveMeasure P.W0
        s a hs ha X t h‖) ∧
    Summable (fun h : {h : A.R // h ≠ 0} =>
      ‖frequencyTerm A P.coefficients P.finiteTrace P.additiveMeasure P.W0
        s a hs ha X t h.val‖) ∧
    (Real.sqrt (modulus A s * X) : ℂ)⁻¹ *
        (∑' m : A.R, originalTerm A P.coefficients P.W0 s a hs X t m) =
      ((Real.sqrt X / modulus A a : ℝ) : ℂ) *
        ∑' h : {h : A.R // h ≠ 0},
          frequencyTerm A P.coefficients P.finiteTrace P.additiveMeasure P.W0
            s a hs ha X t h.val := by
  apply exact_normalized_poisson_row_of_unnormalized_coset
    A σ η hS P N s a hs ha X hX t
  exact ProbeCoset.raw_exact_coset_poisson A σ η hS P (⟨N.localMeasure, N.localHaar, N.localNormalization, N.traceConductor,
    N.containsDifferent, N.sameMeasure⟩) s a hs ha X hX t

end
end DedekindZetaZeroFree.PoissonNormalizedRow
