module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import OAI.NumberTheory.DirichletL.Moments.SupportedCorrelation

public import OAI.NumberTheory.DirichletL.Detector.SpectralSeparation
public import OAI.NumberTheory.DirichletL.Detector.PhysicalAnalytic
public import OAI.NumberTheory.DirichletL.Detector.Windows

@[expose] public section

namespace OAI


open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve CanonicalRowCompletion


section
variable (η : HeckeFamily.Character) (C : CalibrationData) (S : Finset (Ideal ActualEisensteinCubic.O)) (D : Ideal ActualEisensteinCubic.O) (s : ActualEisensteinCubic.O) (hs : Supported (Ideal.span {s}))


include hs in
lemma supportedElement_ne_zero     : s≠0 := by solve_by_elim [_root_.OAI.SevenEighths.CenteredMomentSupportedCorrelation.supported_element_ne_zero]

lemma finite_support_tsum_comm {α β : Type*} (f : α → β → ℂ) (S : Finset α)
    (hz : ∀ a, a∉S → ∀ b, f a b=0) (hs : ∀ a∈S, Summable (f a)) :
    (∑' a, ∑' b, f a b) = ∑' b, ∑' a, f a b := by
  calc
    _ = ∑ a∈S, ∑' b, f a b := tsum_eq_sum (fun a ha => by simp only [hz a ha, tsum_zero])
    _ = ∑' b, ∑ a∈S, f a b := (Summable.tsum_finsetSum hs).symm
    _ = _ := by
      apply tsum_congr
      intro b
      exact (tsum_eq_sum (fun a ha => hz a ha b)).symm

theorem physical_spectral_reopen    
         
      (W : ℝ → ℂ) (hW : HasCompactSupport W)
     K  (hK : 0<K)  t  (ht : 1<t.re) :
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
    aesop
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

end

end SevenEighths.ProbePhysical


end OAI
