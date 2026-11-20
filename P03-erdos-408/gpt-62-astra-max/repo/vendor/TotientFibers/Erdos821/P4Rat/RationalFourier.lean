module
public import Mathlib.Algebra.Order.Chebyshev

public import Erdos821.Blueprint.Analytic
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators Classical ComplexConjugate

namespace Erdos821.P4Rat

open Blueprint.Analytic

/-- Rational Fourier expansion on the group of reduced residue classes. -/
def RationalFourierTask : Prop :=
  ∀ (r : ℕ) (u : ℤ), 1 ≤ r →
    ∃ c : DirichletCharacter ℂ r → ℂ,
      (∑ ψ, ‖c ψ‖) ≤ Real.sqrt (r.totient : ℝ) ∧
      ∀ n : ℕ, Nat.Coprime n r →
        e ((u : ℝ) * n / r) = ∑ ψ, c ψ * ψ (n : ZMod r)

lemma rf_e_norm (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  have h : (2 * Real.pi * t * Complex.I : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

lemma rf_e_add_int (t : ℝ) (k : ℤ) : e (t + (k : ℝ)) = e t := by
  have hcast : (((t + (k : ℝ)) : ℝ) : ℂ) = ((t : ℝ) : ℂ) + ((k : ℤ) : ℂ) := by
    push_cast
    ring
  have harg : (2 * (Real.pi : ℂ) * (((t + (k : ℝ)) : ℝ) : ℂ) * Complex.I : ℂ)
      = 2 * (Real.pi : ℂ) * ((t : ℝ) : ℂ) * Complex.I
        + ((k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    simp
    ring
  have h1  :=
    Complex.exp_int_mul_two_pi_mul_I k
  unfold e
  rw [harg, Complex.exp_add, h1, mul_one]

lemma rf_e_nat_mod (r : ℕ) (hr : 0 < r) (u : ℤ) (n : ℕ) :
    e ((u : ℝ) * (n : ℝ) / (r : ℝ)) = e ((u : ℝ) * ((n % r : ℕ) : ℝ) / (r : ℝ)) := by
  have hr_ne : (r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  have hdivmod : n / r * r + n % r = n := by
    rw [mul_comm]
    exact Nat.div_add_mod n r
  have hcast : (n : ℝ) = ((n / r : ℕ) : ℝ) * (r : ℝ) + ((n % r : ℕ) : ℝ) := by
    exact_mod_cast hdivmod.symm
  have hk : (((u * ((n / r : ℕ) : ℤ) : ℤ)) : ℝ) = (u : ℝ) * ((n / r : ℕ) : ℝ) := by
    rw [Int.cast_mul, Int.cast_natCast]
  have hsplit : (u : ℝ) * (n : ℝ) / (r : ℝ)
      = (u : ℝ) * ((n % r : ℕ) : ℝ) / (r : ℝ) + ((u * ((n / r : ℕ) : ℤ) : ℤ) : ℝ) := by
    grind
  rw [hsplit]
  exact rf_e_add_int _ _

noncomputable def rf_unitPhase (r : ℕ) (u : ℤ) (v : (ZMod r)ˣ) : ℂ :=
  e ((u : ℝ) * ((v.val.val : ℕ) : ℝ) / (r : ℝ))

lemma rf_unitPhase_norm (r : ℕ) (u : ℤ) (v : (ZMod r)ˣ) : ‖rf_unitPhase r u v‖ = 1 :=
  rf_e_norm _

/-- Move a finite transform across the bilinear pairing. -/
private lemma sum_pair {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ℂ) (a : ι → κ → ℂ) (g : κ → ℂ) :
    ∑ j, (∑ i, f i * a i j) * g j = ∑ i, f i * ∑ j, a i j * g j := by
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- Inversion on reduced residues and the corresponding ℓ¹ bound. The ℓ²
identity follows by pairing the inversion formula with the original function. -/
private theorem unit_expansion {r : ℕ} [NeZero r] (f : (ZMod r)ˣ → ℂ) (hf : ∀ v, ‖f v‖ = 1) :
    ∃ c : DirichletCharacter ℂ r → ℂ, (∑ χ, ‖c χ‖) ≤ √(r.totient : ℝ) ∧
      ∀ w : (ZMod r)ˣ, ∑ χ, c χ * χ w.val = f w := by
  classical
  have hφ : (r.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos r)).ne'
  let : NeZero ((Monoid.exponent ((ZMod r)ˣ) : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  let c (χ : DirichletCharacter ℂ r) := (r.totient : ℂ)⁻¹ * ∑ v, f v * conj (χ (v : (ZMod r)ˣ).val)
  have orth (v w : (ZMod r)ˣ) : (∑ χ : DirichletCharacter ℂ r, conj (χ v.val) * χ w.val) =
      if v = w then (r.totient : ℂ) else 0 := by
    have hs (χ : DirichletCharacter ℂ r) : conj (χ v.val) = χ (v.val⁻¹) := by
      change star _ = _
      rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
    simp_rw [hs, DirichletCharacter.sum_char_inv_mul_char_eq ℂ v.isUnit, Units.val_inj]
  have inv (w : (ZMod r)ˣ) : ∑ χ, c χ * χ w.val = f w := by
    simp only [c, mul_assoc, ← Finset.mul_sum]
    rw [sum_pair f (fun v (χ : DirichletCharacter ℂ r) => conj (χ v.val)) (fun χ => χ w.val)]
    simp [orth, mul_ite, mul_left_comm, hφ]
  refine ⟨c, ?_, inv⟩
  have hc (χ : DirichletCharacter ℂ r) : conj (c χ) = (r.totient : ℂ)⁻¹ * ∑ v : (ZMod r)ˣ, χ v.val * conj (f v) := by
    simp [c, mul_comm]
  have h₂ : (∑ χ, ‖c χ‖ ^ 2) = 1 := by
    apply Complex.ofReal_injective
    calc ((∑ χ, ‖c χ‖ ^ 2 : ℝ) : ℂ) = ∑ χ, c χ * conj (c χ) := by simp [Complex.mul_conj']
         _ = (r.totient : ℂ)⁻¹ * ∑ χ, c χ * ∑ v : (ZMod r)ˣ, χ v.val * conj (f v) := by
               simp only [hc, Finset.mul_sum, mul_left_comm]
         _ = (r.totient : ℂ)⁻¹ * ∑ v, f v * conj (f v) := by
               rw [← sum_pair c (fun χ v => χ v.val) (fun v => conj (f v))]
               simp_rw [inv]
         _ = _ := by simp [Complex.mul_conj', hf, ZMod.card_units_eq_totient, hφ]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun χ => ‖c χ‖)
  rw [h₂, mul_one, Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ r] at hcs
  exact Real.le_sqrt_of_sq_le hcs

theorem RationalFourierTask_proof : RationalFourierTask := by
  intro r u hr
  have hr' : 0 < r := hr
  let : NeZero r := ⟨hr'.ne'⟩
  obtain ⟨c,hc,hinv⟩ := unit_expansion (rf_unitPhase r u) (rf_unitPhase_norm r u)
  refine ⟨c,hc,fun n hn => ?_⟩
  let v := ((ZMod.isUnit_iff_coprime n r).mpr hn).unit
  rw [rf_e_nat_mod r hr' u n]
  simpa only [rf_unitPhase, v, IsUnit.unit_spec, ZMod.val_natCast] using (hinv v).symm

end Erdos821.P4Rat
