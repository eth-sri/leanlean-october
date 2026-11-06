module
import Mathlib
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import GuthMaynard.NativeSource.GuthMaynard.ZeroDetector
public import GuthMaynard.NativeSource.GuthMaynard.Asymptotics
public import GuthMaynard.NativeSource.GuthMaynard.Pigeonhole
public import GuthMaynard.NativeSource.GuthMaynard.DirichletPolynomial
public import Mathlib.Tactic

@[expose] public section

open Complex Finset
open scoped BigOperators

namespace GuthMaynard.NativeMoment

/-- Source-faithful general factorization-count input. The constant may depend
    on `k` and `ε`, but is uniform in the positive target `m`. -/
def FactorizationCountBoundProp : Prop :=
  ∀ (k : ℕ) (ε : ℝ), 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m →
      (((Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 m)).filter
        (fun p => (∏ x : Fin k, p x) = m)).card : ℝ) ≤ C * (m : ℝ) ^ ε

lemma pow_coeff_subset (N k m : ℕ) (hm : 0 < m) :
  (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))).filter (fun p => (∏ x : Fin k, p x) = m) ⊆
  (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 m)).filter (fun p => (∏ x : Fin k, p x) = m) := by
  intro p hp
  rw [mem_filter] at hp ⊢
  rcases hp with ⟨hp_pi, hp_prod⟩
  refine ⟨?_, hp_prod⟩
  rw [Fintype.mem_piFinset] at hp_pi ⊢
  intro x
  have hpx := hp_pi x
  rw [mem_Ioc] at hpx ⊢
  rcases hpx with ⟨hpx1, hpx2⟩
  constructor
  · by_cases hN : N = 0
    · rw [hN] at hpx1 hpx2
      linarith
    · have hN_pos : N ≥ 1 := Nat.pos_of_ne_zero hN
      linarith
  · have hdvd : p x ∣ ∏ y : Fin k, p y := dvd_prod_of_mem (fun y => p y) (mem_univ x)
    rw [hp_prod] at hdvd
    exact Nat.le_of_dvd hm hdvd

/-- Complex powers of a finite product of natural numbers factor coordinatewise. -/
lemma prod_natCast_cpow_eq {k : ℕ} (p : Fin k → ℕ) (s : ℂ) :
    (∏ x : Fin k, (p x : ℂ) ^ s) = ((∏ x : Fin k, p x : ℕ) : ℂ) ^ s := by
  classical
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simp
  | @insert a u ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow, ih]

/-- A tuple supported on `(N, 2N]` has product supported on `[N^k, (2N)^k]`.
    This includes the empty-product case `k = 0`. -/
lemma powCoeff_product_mem_support (N k : ℕ) (p : Fin k → ℕ)
    (hp : p ∈ Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))) :
    (∏ x : Fin k, p x) ∈ Finset.Icc (N ^ k) ((2 * N) ^ k) := by
  rw [Fintype.mem_piFinset] at hp
  rw [Finset.mem_Icc]
  constructor
  · calc
      N ^ k = ∏ _x : Fin k, N := by simp
      _ ≤ ∏ x : Fin k, p x := by
        apply Finset.prod_le_prod₀
        all_goals (grind)
  · calc
      ∏ x : Fin k, p x ≤ ∏ _x : Fin k, 2 * N := by
        apply Finset.prod_le_prod₀
        all_goals (grind)
      _ = (2 * N) ^ k := by simp

/-- A wide polynomial supported on `(Q,2^k Q]`. -/
noncomputable def wideDirichletPoly (Q k : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc Q (2 ^ k * Q), a m * (m : ℂ) ^ (-t * I)

section
variable (Q k : ℕ) (a : ℕ → ℂ)
include Q k a

/-- The wide powered support is the disjoint union of exactly `k` ordinary
dyadic blocks. -/
theorem wideDirichletPoly_eq_sum_blocks  (t : ℝ) :
    wideDirichletPoly Q k a t =
      ∑ r ∈ Finset.range k, dirichletPoly (2 ^ r * Q) a t := by
  induction k with
  | zero => simp [wideDirichletPoly]
  | succ k ih =>
      rw [wideDirichletPoly]
      have hQ : Q ≤ 2 ^ k * Q := by
        exact Nat.le_mul_of_pos_left Q (pow_pos (by omega : 0 < 2) k)
      have hBlock : 2 ^ k * Q ≤ 2 ^ (k + 1) * Q := by bound
      rw [← Finset.Ioc_union_Ioc_eq_Ioc hQ hBlock,
        Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
      change wideDirichletPoly Q k a t + _ = _
      rw [ih]
      rw [Finset.sum_range_succ, dirichletPoly, dyadicInterval]
      congr 1
      ring_nf

/-- One dyadic block carries at least the average of the sum of block norms. -/
theorem exists_large_dyadic_block  (t V : ℝ)
    (hk : 0 < k) (hV : V ≤ ‖wideDirichletPoly Q k a t‖) :
    ∃ r ∈ Finset.range k,
      V / k ≤ ‖dirichletPoly (2 ^ r * Q) a t‖ := by
  have hTriangle : ‖wideDirichletPoly Q k a t‖ ≤
      ∑ r ∈ Finset.range k, ‖dirichletPoly (2 ^ r * Q) a t‖ := by
    rw [wideDirichletPoly_eq_sum_blocks]
    exact norm_sum_le _ _
  exact pigeonhole_real_sum k
    (fun r => ‖dirichletPoly (2 ^ r * Q) a t‖) V
    (hV.trans hTriangle) hk

/-- Simultaneous block-and-ordinate pigeonholing. The chosen block is fixed on
the output subset, which is essential before invoking a large-values or
mean-value estimate. -/
theorem exists_dyadic_block_and_subset
     (W : Finset ℝ) (V : ℝ)
    (hk : 0 < k)
    (hWide : ∀ t ∈ W, V ≤ ‖wideDirichletPoly Q k a t‖) :
    ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
      (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
      ∀ t ∈ W', V / k ≤ ‖dirichletPoly (2 ^ r * Q) a t‖ := by
  classical
  have hEach : ∀ t ∈ W, ∃ r ∈ Finset.range k,
      V / k ≤ ‖dirichletPoly (2 ^ r * Q) a t‖ := by
    intro t ht
    exact exists_large_dyadic_block Q k a t V hk (hWide t ht)
  let index (t : ℝ) : ℕ :=
    if ht : t ∈ W then Classical.choose (hEach t ht) else 0
  have hIndexMem : ∀ t ∈ W, index t ∈ Finset.range k := by grind
  have hIndexLarge : ∀ t ∈ W,
      V / k ≤ ‖dirichletPoly (2 ^ index t * Q) a t‖ := by grind
  have hCard : W.card = ∑ r ∈ Finset.range k,
      (W.filter fun t => index t = r).card := by
    exact Finset.card_eq_sum_card_fiberwise hIndexMem
  have hCardReal : (W.card : ℝ) = ∑ r ∈ Finset.range k,
      ((W.filter fun t => index t = r).card : ℝ) := by
    exact_mod_cast hCard
  obtain ⟨r, hr, hrLarge⟩ := pigeonhole_real_sum k
    (fun r => ((W.filter fun t => index t = r).card : ℝ))
    (W.card : ℝ) (by rw [hCardReal]) hk
  refine ⟨r, hr, W.filter fun t => index t = r, Finset.filter_subset _ _, ?_, ?_⟩
  · have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
    calc
      (W.card : ℝ) = k * ((W.card : ℝ) / k) := by field_simp
      _ ≤ k * ((W.filter fun t => index t = r).card : ℝ) := by gcongr
  · intro t ht
    rw [Finset.mem_filter] at ht
    simpa [ht.2] using hIndexLarge t ht.1
end



