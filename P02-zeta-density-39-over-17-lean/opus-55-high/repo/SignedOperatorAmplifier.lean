module
public import GuthMaynard.Improvement.OperatorNuclearSpectral
public import GuthMaynard.Improvement.SpectralMassAssembly
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory InnerProductSpace Filter Set
open scoped InnerProductSpace Topology
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- The exact signed cubic comparison is stronger than the older absolute
trace helper. Only diagonal positivity of G and C is needed. -/
theorem finite_diagonal_signed_trace {ι : Type*} [Fintype ι]
    (c e : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hg : ∀ i, 0 ≤ c i+e i) :
    (∑ i, (max (e i) 0)^3) ≤ (∑ i, (e i)^3)+∑ i, c i*(e i)^2 := by
  pm_4541
  exact (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)).trans_eq Finset.sum_add_distrib

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem operator_finite_signed_spectral_comparison [FiniteDimensional ℂ E]
    [Fintype ι] [Fintype κ] (d : OrthonormalBasis ι ℂ E)
    (G C : E →L[ℂ] E) (hG : G.IsPositive) (hC : C.IsPositive)
    (v : κ → E) (hv : Orthonormal ℂ v) {k a B : ℝ}
    (hk : (Fintype.card κ:ℝ) ≤ k) (hB : ‖C‖ ≤ B)
    (hw : k*a ≤ ∑ j, (inner ℂ (v j) (G (v j))).re) :
    k*(max (a-B) 0)^3 ≤
      (∑ i, inner ℂ (d i) (((G-C)^3) (d i))).re+
      (∑ i, inner ℂ (d i) ((C*(G-C)^2) (d i))).re := by
  pm_4542
  pm_4544 finite_diagonal_signed_trace
  pm_4543
  change k*(max (a-B) 0)^3 ≤ (∑ i, inner ℂ (b i) ((H^3) (b i))).re+
    (∑ i, inner ℂ (b i) ((C*H^2) (b i))).re
  rw [hcubes.1, hcubes.2, Complex.ofReal_re]
  exact hp.trans hd

end Montgomery.RationalMoment
