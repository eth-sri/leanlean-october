module

public import Erdos821.P5MarkedEnergy.MarkRemoval
public import Erdos821.S56.GroupParts
public import Erdos821.P5.EndpointInvariance
public import Erdos821.P5.EndpointBounds
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! The full integer factorization `w = m p_s p r` of a marked endpoint (paper
§4, four-factor endpoint): the endpoint times the residual mark sum is a
four-fold Dirichlet convolution. -/

@[expose] public section

noncomputable section
open Classical

namespace Erdos821.P5Marked
open Blueprint.Analytic

/-! ### Group-part facts -/

/-! ### Endpoint coefficient functions -/

/-! ### The four-fold identity -/

/-! ### Rational phases by characters -/

theorem e_int (k : ℤ) : e (k : ℝ) = 1 := by
  unfold e
  have : (2 * (Real.pi : ℂ) * ((k : ℝ) : ℂ) * Complex.I) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  simp_all

theorem e_add' (a b : ℝ) : e (a + b) = e a * e b := by
  unfold e; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem e_periodic (a : ℝ) (k : ℤ) : e (a + k) = e a := by
  rw [e_add', e_int, mul_one]

/-- The character coefficient of the rational phase. -/
def cchi (r : ℕ) (u : ℤ) (χ : DirichletCharacter ℂ r) (k : ℕ) : ℂ :=
  ((Nat.totient r : ℂ))⁻¹ * ∑ a ∈ (Finset.range r).filter (fun a => Nat.Coprime a r),
    χ ((a : ZMod r)⁻¹) * e (u * a * k / r)

theorem norm_cchi_le (r : ℕ) (u : ℤ) (χ : DirichletCharacter ℂ r) (k : ℕ) : ‖cchi r u χ k‖ ≤ 1 := by
  unfold cchi
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hcard : ((Finset.range r).filter (fun a => Nat.Coprime a r)).card = Nat.totient r := by
    rw [Nat.totient]
    congr 1
    ext a
    simp only [Finset.mem_filter]
    rw [Nat.coprime_comm]
  rcases Nat.eq_zero_or_pos (Nat.totient r) with h0 | hpos
  · simp_all
  · rw [inv_mul_le_iff₀ (by positivity), mul_one]
    calc ‖∑ a ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), χ ((a : ZMod r)⁻¹) *
          e (u * a * k / r)‖
        ≤ ∑ a ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), ‖χ ((a : ZMod r)⁻¹) *
          e (u * a * k / r)‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a _
          rw [norm_mul]
          have h1 := χ.norm_le_one ((a : ZMod r)⁻¹)
          have h2 : ‖e (u * a * k / r)‖ = 1 := by
            unfold e; rw [Complex.norm_exp]; simp
          simp_all
      _ = Nat.totient r := by simp_all

/-- Character expansion of the rational phase on units. -/
theorem e_eq_sum_cchi (r : ℕ) (hr : 1 ≤ r) (u : ℤ) (v k : ℕ) (hv : Nat.Coprime v r) :
    e (u * (v * k : ℕ) / r) = ∑ χ : DirichletCharacter ℂ r, cchi r u χ k * χ (v : ZMod r) := by
  have : NeZero r := ⟨by omega⟩
  unfold cchi
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ a ∈ (Finset.range r).filter (fun a => Nat.Coprime a r),
      ∑ χ : DirichletCharacter ℂ r, ((Nat.totient r : ℂ))⁻¹ * (χ ((a : ZMod r)⁻¹) *
        e (u * a * k / r)) * χ (v : ZMod r) =
      if a = v % r then e (u * a * k / r) else 0 := by
    intro a ha
    have hau :=
      (ZMod.isUnit_iff_coprime a r).mpr (by grind)
    have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hau (v : ZMod r)
    have hrw : ∀ χ : DirichletCharacter ℂ r, ((Nat.totient r : ℂ))⁻¹ * (χ ((a : ZMod r)⁻¹) *
        e (u * a * k / r)) * χ (v : ZMod r) =
        ((Nat.totient r : ℂ))⁻¹ * e (u * a * k / r) * (χ ((a : ZMod r)⁻¹) * χ (v : ZMod r)) := by
      intro χ; ring
    rw [Finset.sum_congr rfl (fun χ _ => hrw χ), ← Finset.mul_sum, horth]
    have hiff : (a : ZMod r) = (v : ZMod r) ↔ a = v % r := by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by grind)]
    have htot : (Nat.totient r : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity)
    by_cases h : a = v % r
    · grind
    · simp_all
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq']
  have hmem : v % r ∈ (Finset.range r).filter (fun a => Nat.Coprime a r) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), ?_⟩
    show Nat.gcd (v % r) r = 1
    rw [← Nat.gcd_rec r v]
    exact hv.symm
  rw [ite_eq_left hmem]
  -- periodicity
  have hdecomp : (u : ℝ) * ((v * k : ℕ) : ℝ) / r =
      (u : ℝ) * ((v % r : ℕ) : ℝ) * k / r + ((u * ((v / r : ℕ) : ℤ) * k : ℤ) : ℝ) := by
    have hv' : (v : ℝ) = ((v % r : ℕ) : ℝ) + r * ((v / r : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mod_add_div v r).symm
    have hrpos : (r : ℝ) ≠ 0 := by exact_mod_cast (by positivity)
    simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    rw [hv']
    field_simp
  rw [hdecomp, e_periodic]

end Erdos821.P5Marked
