module
public import GuthMaynard.Improvement.OperatorNuclearSpectral
public import GuthMaynard.Improvement.SpectralMassAssembly

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
  have hp (i : ι) : (max (e i) 0)^3 ≤ (e i)^3+c i*(e i)^2 := by
    by_cases he : 0 ≤ e i
    · rw [max_eq_left he]
      nlinarith [mul_nonneg (hc i) (sq_nonneg (e i))]
    · rw [max_eq_right (le_of_not_ge he)]
      nlinarith [mul_nonneg (hg i) (sq_nonneg (e i))]
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
  let H := G-C
  have hs : H.toLinearMap.IsSymmetric := hG.isSymmetric.sub hC.isSymmetric
  let b := hs.eigenvectorBasis rfl
  let e := hs.eigenvalues rfl
  have he (i : Fin (Module.finrank ℂ E)) : H (b i) = (e i:ℂ) • b i :=
    hs.apply_eigenvectorBasis rfl i
  have hp := finite_operator_positive_cube b H C hs e he v hv hk hB
    (by simpa [H] using hw)
  have hd := finite_diagonal_signed_trace
    (fun i => (inner ℂ (b i) (C (b i))).re) e
    (fun i => (operator_eigenbasis_diagonal_nonneg b G C hG hC e he i).1)
    (fun i => (operator_eigenbasis_diagonal_nonneg b G C hG hC e he i).2)
  have hcubes := operator_eigenbasis_trace_values b H C e he
  have htrace (T : E →L[ℂ] E) :
      (∑ i, inner ℂ (d i) (T (d i))) = ∑ i, inner ℂ (b i) (T (b i)) := by
    exact (LinearMap.trace_eq_sum_inner T.toLinearMap d).symm.trans
      (LinearMap.trace_eq_sum_inner T.toLinearMap b)
  rw [htrace ((G-C)^3), htrace (C*(G-C)^2)]
  change k*(max (a-B) 0)^3 ≤ (∑ i, inner ℂ (b i) ((H^3) (b i))).re+
    (∑ i, inner ℂ (b i) ((C*H^2) (b i))).re
  rw [hcubes.1, hcubes.2, Complex.ofReal_re]
  exact hp.trans hd

end Montgomery.RationalMoment
