module

public import OAI.NumberTheory.DirichletL.Detector.SpectralSeparation
public import OAI.NumberTheory.DirichletL.Detector.PhysicalAnalytic
public import OAI.NumberTheory.DirichletL.Detector.Windows

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeCompleted ProbeRow CanonicalQuadraticSieve

lemma supportedElement_ne_zero (s : ActualEisensteinCubic.O) (hs : Supported (Ideal.span {s})) : s≠0 := by
  intro h
  apply hs.1
  simp_all

lemma finite_support_tsum_comm {α β : Type*} (f : α → β → ℂ) (S : Finset α)
    (hz : ∀ a, a∉S → ∀ b, f a b=0) (hs : ∀ a∈S, Summable (f a)) :
    (∑' a, ∑' b, f a b) = ∑' b, ∑' a, f a b := by
  calc
    _ = ∑ a∈S, ∑' b, f a b := tsum_eq_sum (fun a ha => by simp_all)
    _ = ∑' b, ∑ a∈S, f a b := (Summable.tsum_finsetSum hs).symm
    _ = _ := by
      apply tsum_congr
      intro b
      exact (tsum_eq_sum (by grind)).symm

theorem physical_spectral_reopen (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : Ideal ActualEisensteinCubic.O) (s : ActualEisensteinCubic.O)
    (hs : Supported (Ideal.span {s})) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (K : ℝ) (hK : 0<K) (t : ℂ) (ht : 1<t.re) :
    (∑' m : ActualEisensteinCubic.O, C.residueMonoid m * sexticGauss s (supportedElement_ne_zero s hs) (-m) *
      W (elementNorm m/K) * spectralRow S D (rowCoefficient η C.Xi s hs m) t) =
    ∑' p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O, spectralSummand S D (baseRowCoefficient η C.Xi s hs) t p.1 p.2 *
      ∑' m : ActualEisensteinCubic.O, calibratedNumerator C (completedIndex p.1 p.2) m *
        sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K) := by
  let F (m : ActualEisensteinCubic.O) (p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) : ℂ :=
    C.residueMonoid m * sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K) *
      spectralSummand S D (rowCoefficient η C.Xi s hs m) t p.1 p.2
  have hfin := elementWindow_finite_support W hW K hK
  have hzero : ∀ m, m∉hfin.toFinset → ∀ p, F m p=0 := by
    intro m hm p
    have hz : W (elementNorm m/K)=0 := by simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hm
    simp only [F, hz, mul_zero, zero_mul]
  have hsum (m : ActualEisensteinCubic.O) : Summable (F m) :=
    (spectralRow_summable S D (rowCoefficient η C.Xi s hs m)
      (rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one s hs m) t ht).mul_left _
  have he := finite_support_tsum_comm F hfin.toFinset hzero (fun m _ => hsum m)
  calc
    _ = ∑' m : ActualEisensteinCubic.O, ∑' p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O, F m p := by
      simp only [F, spectralRow, tsum_mul_left]
    _ = ∑' p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O, ∑' m : ActualEisensteinCubic.O, F m p := he
    _ = _ := by
      apply tsum_congr
      intro p
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      unfold F
      rw [spectralSummand_row_separation]
      unfold calibratedNumerator
      ring

end SevenEighths.ProbePhysical
end

end OAI
