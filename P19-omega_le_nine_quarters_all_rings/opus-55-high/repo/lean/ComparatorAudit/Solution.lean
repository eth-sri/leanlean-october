
import OAI.LinearAlgebra.MatrixMultiplication.AllRings



/-! Proofs for a separately compiled frozen challenge. Never import Challenge here.
The sixth statement uses literal integer coefficient identities, not project
rank definitions or equality restricted to a finite set of field inputs. -/

namespace ComparatorChecks

universe u
open OAI.MatrixMultiplication Arithmetic

theorem admissible_bddBelow (R : Type u) [Ring R] [Nontrivial R] :
    BddBelow {τ : ℝ | Arithmetic.AdmissibleExponent R τ} :=
  ⟨2, fun _ => admissibleExponent_two_le⟩

theorem omega_bound (R : Type u) [Ring R] :
    Arithmetic.omega R ≤ (9 : ℝ) / 4 := by
  by_cases h : BddBelow {τ | AdmissibleExponent R τ}
  · exact csInf_le h (admissibleExponent_nine_quarters_all_rings R)
  rw [omega, Real.sInf_of_not_bddBelow h]; norm_num

theorem admissible_nonempty (R : Type u) [Ring R] :
    Set.Nonempty {τ : ℝ | Arithmetic.AdmissibleExponent R τ} :=
  ⟨_, admissibleExponent_nine_quarters_all_rings R⟩

theorem omega_lower (R : Type u) [Ring R] [Nontrivial R] :
    (2 : ℝ) ≤ Arithmetic.omega R :=
  le_csInf ⟨_, admissibleExponent_nine_quarters_all_rings R⟩ fun _ => admissibleExponent_two_le

theorem epsilon_cost (R : Type u) [Ring R] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : Arithmetic.MatrixAlgorithm R n n n,
        P.Correct ∧ (P.cost : ℝ) ≤
          C * (n : ℝ) ^ ((9 : ℝ) / 4 + ε) :=
  admissibleExponent_nine_quarters_all_rings R ε hε

theorem exact_coefficients (ε : ℝ) (hε : 0 < ε) :
    ∃ n r : ℕ, 2 ≤ n ∧ (r : ℝ) ≤ (n : ℝ) ^ ((9 : ℝ) / 4 + ε) ∧
      ∃ (a : Fin r → (Fin n × Fin n) → ℤ)
        (b : Fin r → (Fin n × Fin n) → ℤ)
        (c : Fin r → (Fin n × Fin n) → ℤ),
        ∀ x y z : Fin n × Fin n,
          (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0 : ℤ) =
            ∑ i, a i x * b i y * c i z :=
  let ⟨n, r, hn, ⟨a, b, c, h⟩, hr⟩ := int_rank_nine_quarters hε
  ⟨n, r, hn, hr, a, b, c, fun x y z => congrFun₂ (congrFun h x) y z⟩
