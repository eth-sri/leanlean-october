module

public import NearlyMinimax.GaussianPrimitiveSeparated
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Algebra.Order.Antidiag.Pi


@[expose] public section

/-! Coefficient moment tensorization under actual finite product measures.
Only the primitive weighted coefficient pairs need to be integrable. -/
noncomputable section
open MeasureTheory MvPolynomial
open scoped BigOperators Classical
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {σ E : Type*} [DecidableEq σ]

local instance : AddCancelCommMonoid (σ →₀ ℕ) where
  __ := (inferInstance : AddCommMonoid (σ →₀ ℕ))
  add_left_cancel a b c h := by
    ext j
    exact add_left_cancel (congrArg (fun f : σ →₀ ℕ => f j) h)

def polynomialPairMoment (w : E → ℝ) (P P' : E → MvPolynomial σ ℝ)
    (β β' : σ →₀ ℕ) (e : E) : ℝ := w e * (P e).coeff β * (P' e).coeff β'

/-- Only exponent assignments whose sum is the requested exponent contribute. -/
private theorem coeff_finset_prod {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ ℝ) (β : σ →₀ ℕ) :
    (∏ j ∈ s, P j).coeff β = ∑ b ∈ s.piAntidiag β, ∏ j ∈ s, (P j).coeff (b j) := by
  classical
  induction s using Finset.cons_induction_on generalizing β with
  | empty => by_cases h : β = 0 <;> simp [coeff_one, h, Ne.symm]
  | cons i s hi ih =>
    rw [Finset.prod_cons, coeff_mul]
    erw [Finset.piAntidiag_cons hi, Finset.sum_disjiUnion]
    apply Finset.sum_congr rfl
    intro u _
    rw [ih, Finset.mul_sum, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro b hb
    have h0 : b i = 0 := by
      by_contra h
      exact hi ((Finset.mem_piAntidiag.mp hb).2 _ h)
    rw [Finset.prod_cons]
    simp only [addRightEmbedding_apply, Pi.add_apply, ite_true, h0, zero_add]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp [show j ≠ i from fun h => hi (h ▸ hj)]

section
variable {κ : Type*} [Fintype κ]

def tensorPolynomialPairMoment_fintype
    (w : κ → E → ℝ) (P P' : κ → E → MvPolynomial σ ℝ)
    (β β' : σ →₀ ℕ) (e : κ → E) : ℝ :=
  (∏ j, w j (e j)) * (∏ j, P j (e j)).coeff β * (∏ j, P' j (e j)).coeff β'

private theorem tensorPolynomialPairMoment_expand
    (w : κ → E → ℝ) (P P' : κ → E → MvPolynomial σ ℝ)
    (β β' : σ →₀ ℕ) (e : κ → E) :
    tensorPolynomialPairMoment_fintype w P P' β β' e =
      ∑ u ∈ Finset.univ.piAntidiag β, ∑ v ∈ Finset.univ.piAntidiag β',
        ∏ j, polynomialPairMoment (w j) (P j) (P' j) (u j) (v j) (e j) := by
  classical
  unfold tensorPolynomialPairMoment_fintype
  simp only [coeff_finset_prod, Finset.mul_sum, Finset.sum_mul,
    polynomialPairMoment, Finset.prod_mul_distrib]
  exact Finset.sum_comm

theorem tensorPolynomialPairMoment_fintype_integral [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ]
    (w : κ → E → ℝ) (P P' : κ → E → MvPolynomial σ ℝ)
    (p p' : κ → MvPolynomial σ ℝ) (a : κ → ℝ)
    (hi : ∀ j β β', Integrable (polynomialPairMoment (w j) (P j) (P' j) β β') μ)
    (he : ∀ j β β', (∫ e, polynomialPairMoment (w j) (P j) (P' j) β β' e ∂μ) =
      a j * (p j).coeff β * (p' j).coeff β') (β β' : σ →₀ ℕ) :
    Integrable (tensorPolynomialPairMoment_fintype w P P' β β') (Measure.pi (fun _ => μ)) ∧
      (∫ e, tensorPolynomialPairMoment_fintype w P P' β β' e ∂Measure.pi (fun _ => μ)) =
        (∏ j, a j) * (∏ j, p j).coeff β * (∏ j, p' j).coeff β' := by
  classical
  have h (u v : κ → σ →₀ ℕ) := Integrable.fintype_prod (fun j => hi j (u j) (v j))
  have heq := funext (tensorPolynomialPairMoment_expand w P P' β β')
  rw [heq]
  refine ⟨integrable_finsetSum _ (fun u _ => integrable_finsetSum _ fun v _ => h u v), ?_⟩
  rw [integral_finsetSum _ (fun u _ => integrable_finsetSum _ fun v _ => h u v)]
  simp_rw [integral_finsetSum _ (fun v _ => h _ v), integral_fintype_prod_eq_prod, he]
  simpa [tensorPolynomialPairMoment_fintype, polynomialPairMoment] using
    (tensorPolynomialPairMoment_expand (fun j (_ : Unit) => a j) (fun j _ => p j)
      (fun j _ => p' j) β β' (fun _ => ())).symm

end
end NearlyMinimax
