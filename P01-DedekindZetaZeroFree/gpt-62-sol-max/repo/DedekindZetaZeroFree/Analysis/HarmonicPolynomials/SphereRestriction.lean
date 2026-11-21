module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Analysis.Normed.Module.Connected
public meta import Mathlib.Tactic.Ring
public meta import Mathlib.Tactic.FunProp
public meta import Mathlib.Tactic.Choose

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse

abbrev Ambient := EuclideanSpace ℝ (Fin 3)
abbrev Sphere := ↥(Metric.sphere (0 : Ambient) 1)

noncomputable def polynomialSphere (p : MvPolynomial (Fin 3) ℂ) (x : Sphere) : ℂ :=
  MvPolynomial.eval (fun i => ((x : Ambient) i : ℂ)) p

theorem homogeneous_eval_scale {p : MvPolynomial (Fin 3) ℂ} {ℓ : ℕ}
    (hp : p.IsHomogeneous ℓ) (t : ℂ) (x : Fin 3 → ℂ) :
    MvPolynomial.eval (fun i => t * x i) p = t ^ ℓ * MvPolynomial.eval x p := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : ∑ i : Fin 3, d i = ℓ := by
    have hh := hp (MvPolynomial.mem_support_iff.mp hd)
    change Finsupp.weight (fun _ : Fin 3 => (1 : ℕ)) d = ℓ at hh
    rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum] at hh
    exact hh
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, hdeg]
  ring
theorem homogeneous_sphere_eq_zero {p : MvPolynomial (Fin 3) ℂ} {ℓ : ℕ}
    (hp : p.IsHomogeneous ℓ) (h : ∀ x : Sphere, polynomialSphere p x = 0) : p = 0 := by
  apply MvPolynomial.funext_set (fun _ => Set.range Complex.ofReal)
    (fun _ => by simpa using Set.infinite_univ.image Complex.ofReal_injective.injOn)
  let f : Ambient → ℂ := fun y => MvPolynomial.eval (fun i => (y i : ℂ)) p
  have hf : Continuous f := (MvPolynomial.continuous_eval p).comp (by fun_prop)
  have hzero : f = fun _ => 0 := by
    refine Continuous.ext_on (dense_compl_singleton 0) hf continuous_const ?_
    intro y hy
    have hy0 : y ≠ 0 := hy
    let u : Sphere := ⟨‖y‖⁻¹ • y, by
      simp [norm_smul, Real.norm_eq_abs, norm_ne_zero_iff.mpr hy0]⟩
    have hs := homogeneous_eval_scale hp (‖y‖ : ℂ) (fun i => ((u : Ambient) i : ℂ))
    have he : (fun i => (‖y‖ : ℂ) * ((u : Ambient) i : ℂ)) = (fun i => (y i : ℂ)) := by
      funext i
      change (‖y‖ : ℂ) * ((‖y‖⁻¹ * y i : ℝ) : ℂ) = _
      rw [← Complex.ofReal_mul, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy0), one_mul]
    have hu := h u
    change MvPolynomial.eval (fun i => ((u : Ambient) i : ℂ)) p = 0 at hu
    rw [he, hu, mul_zero] at hs
    exact hs
  intro z hz
  choose r hr using fun i => hz i (Set.mem_univ i)
  simpa [f, hr] using congrFun hzero (WithLp.toLp 2 r)

end DedekindZetaZeroFree.ComplexFractionalInverse
