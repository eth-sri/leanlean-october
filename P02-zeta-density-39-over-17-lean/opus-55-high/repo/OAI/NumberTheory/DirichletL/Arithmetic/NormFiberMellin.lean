module
public import OAI.NumberTheory.DirichletL.Mellin.LocalNonvanishing
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius

namespace ShortDraftLocal

end ShortDraftLocal


namespace ActualEisensteinCubic

end ActualEisensteinCubic

namespace ShortDraftHeckeBridge

noncomputable def chiMinusThree : DirichletCharacter ℂ 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

noncomputable def baseChangeWeight {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ) * χ (Ideal.absNorm I)

theorem baseChangeWeight_prime {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Ideal O) (hP : Prime P) :
    baseChangeWeight χ P = -χ (Ideal.absNorm P) := by
  rw [baseChangeWeight, hP.irreducible.moebius_eq]
  norm_num

noncomputable def invCharAF {q : ℕ} (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  (toArithmeticFunction (χ ·)).pmul (ArithmeticFunction.moebius : ArithmeticFunction ℂ)

section
variable {q : ℕ} (χ : DirichletCharacter ℂ q)
include q χ
theorem invCharAF_apply
    {n : ℕ} (hn : n ≠ 0) :
    invCharAF χ n = χ n * (ArithmeticFunction.moebius n : ℂ) := by
  change ((toArithmeticFunction (χ ·)).pmul
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) n = _
  rw [ArithmeticFunction.pmul_apply]
  simp [toArithmeticFunction, hn]

private theorem invCharAF_mult :
    (invCharAF χ).IsMultiplicative := by
  exact (χ.isMultiplicative_toArithmeticFunction).pmul
    (ArithmeticFunction.isMultiplicative_moebius.intCast)
end

noncomputable def pairAF {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : ArithmeticFunction ℂ :=
  invCharAF χ * invCharAF ψ

section
variable {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
include q r χ ψ
theorem pairAF_mult :
    (pairAF χ ψ).IsMultiplicative :=
  (invCharAF_mult χ).mul (invCharAF_mult ψ)

theorem pairAF_eq_pairInverseCoeff
    (n : ℕ) : pairAF χ ψ n = pairInverseCoeff χ ψ n := by
  rw [pairAF, ← ArithmeticFunction.coe_mul]
  apply congrFun
  exact (LSeries.convolution_congr
    (fun {k} hk => invCharAF_apply χ hk)
    (fun {k} hk => invCharAF_apply ψ hk))

theorem normFiber_eq_pair_of_prime_powers
    (weight : Ideal O → ℂ)
    (hb : (toArithmeticFunction (normFiberCoeff weight)).IsMultiplicative)
    (hlocal : ∀ p k : ℕ, p.Prime →
      (toArithmeticFunction (normFiberCoeff weight)) (p ^ k) =
        pairAF χ ψ (p ^ k))
    (n : ℕ) (hn : n ≠ 0) :
    normFiberCoeff weight n = pairInverseCoeff χ ψ n := by
  have heq : toArithmeticFunction (normFiberCoeff weight) = pairAF χ ψ :=
    (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
      _ hb _ (pairAF_mult χ ψ)).2 hlocal
  have h := congrFun (congrArg DFunLike.coe heq) n
  calc
    normFiberCoeff weight n = (toArithmeticFunction (normFiberCoeff weight)) n := by
      simp [toArithmeticFunction, hn]
    _ = pairAF χ ψ n := h
    _ = pairInverseCoeff χ ψ n := pairAF_eq_pairInverseCoeff χ ψ n
end

section
variable {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) {p : ℕ} (hp : p.Prime)
include q r χ ψ p hp
theorem pairAF_prime :
    pairAF χ ψ p = -(χ p + ψ p) := by
  pm_3512
  pm_3513
  rw [hp.divisors]
  have hnot : 1 ∉ ({p} : Finset ℕ) := by simpa using hp.ne_one.symm
  rw [Finset.sum_insert hnot, Finset.sum_singleton]
  simp [Nat.div_one, Nat.div_self hp.pos, h1χ, h1ψ, hpχ, hpψ]

theorem pairAF_prime_sq :
    pairAF χ ψ (p ^ 2) = χ p * ψ p := by
  pm_3512
  pm_5404 hp2χ χ
  pm_5404 hp2ψ ψ
  have hdiv : (p ^ 2).divisors = ({1, p, p ^ 2} : Finset ℕ) := by
    ext x
    rw [Nat.mem_divisors_prime_pow hp 2]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨j, hj, rfl⟩
      interval_cases j <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by decide, by simp⟩
      · exact ⟨1, by decide, by simp⟩
      · exact ⟨2, by decide, by simp⟩
  pm_3513
  rw [hdiv]
  have hpge : 2 ≤ p := hp.two_le
  have h1p2 : 1 ≠ p ^ 2 := by nlinarith
  have hpp2 : p ≠ p ^ 2 := by nlinarith
  have hnot1 : 1 ∉ ({p, p ^ 2} : Finset ℕ) := by
    simp [hp.ne_one.symm, h1p2]
  have hnotp : p ∉ ({p ^ 2} : Finset ℕ) := by
    simp [hpp2]
  rw [Finset.sum_insert hnot1, Finset.sum_insert hnotp, Finset.sum_singleton]
  have hdivp : p ^ 2 / p = p := by simp [pow_two, hp.pos]
  simp [Nat.div_one, hdivp, h1χ,  hpχ, hpψ, hp2χ, hp2ψ]
end

theorem chiMinusThree_two : chiMinusThree (2 : ℕ) = -1 := by
  have h3 : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  change ((quadraticChar (ZMod 3) (2 : ZMod 3) : ℤ) : ℂ) = -1
  rw [quadraticChar_eq_pow_of_char_ne_two h3 h2]
  simp [h21]

theorem chiMinusThree_ne_one : chiMinusThree ≠ 1 := by
  intro h
  have hh := congrArg (fun ξ : DirichletCharacter ℂ 3 => ξ (2 : ℕ)) h
  rw [chiMinusThree_two] at hh
  have hunit : IsUnit (2 : ZMod 3) := by decide
  change (-1 : ℂ) = (1 : DirichletCharacter ℂ 3) (2 : ZMod 3) at hh
  rw [MulChar.one_apply hunit] at hh
  norm_num at hh

theorem not_both_principal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ¬ ((χ.changeLevel (Nat.dvd_mul_right q 3) = 1) ∧
      χ.changeLevel (Nat.dvd_mul_right q 3) *
        chiMinusThree.changeLevel (Nat.dvd_mul_left 3 q) = 1) := by
  rintro ⟨hχ, hprod⟩
  rw [hχ, one_mul] at hprod
  have hη : chiMinusThree = 1 :=
    (DirichletCharacter.changeLevel_eq_one_iff (Nat.dvd_mul_left 3 q)).mp hprod
  exact chiMinusThree_ne_one hη

end ShortDraftHeckeBridge

namespace ShortDraftHeckeBridge

end ShortDraftHeckeBridge

end

end OAI
