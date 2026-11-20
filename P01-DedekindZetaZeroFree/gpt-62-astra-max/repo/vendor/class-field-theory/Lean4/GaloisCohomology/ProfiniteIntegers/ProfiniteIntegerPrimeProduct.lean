module

public import GaloisCohomology.ProfiniteIntegers.ProfiniteInteger
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.NumberTheory.Padics.RingHoms

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Prime decomposition of the profinite integers

This file constructs the canonical map
`ℤ̂ → ∏ p : Nat.Primes, ℤ_p` from the compatible finite reductions.
-/

open scoped Topology

noncomputable section

namespace ClassFormation

local instance (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

/-- The product of the additive rings of `p`-adic integers over all
rational primes. -/
abbrev ProfiniteIntegerPrimeProduct :=
  ∀ p : Nat.Primes, ℤ_[p.1]

section

variable (n : ℕ) (hn : 0 < n)

/-- The ring form of the canonical reduction `ℤ̂ → ℤ/nℤ`. -/
def zHatReductionRingHom :
    ZHat →+* ZMod n where
  toFun := zHatReduction n hn
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem zHatReductionRingHom_apply (z : ZHat) :
    zHatReductionRingHom n hn z = zHatReduction n hn z :=
  rfl

end

section

variable (p : Nat.Primes)

/-- The compatible `p`-power reductions of a profinite integer. -/
def zHatPadicReduction (n : ℕ) :
    ZHat →+* ZMod (p.1 ^ n) :=
  zHatReductionRingHom (p.1 ^ n) (pow_pos p.2.pos n)

theorem zHatPadicReduction_compatible (m n : ℕ) (hmn : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow p.1 hmn) (ZMod (p.1 ^ m))).comp
        (zHatPadicReduction p n) =
      zHatPadicReduction p m := by
  ext z
  exact zHatReduction_transition
    (pow_pos p.2.pos m) (pow_pos p.2.pos n)
    (pow_dvd_pow p.1 hmn) z

/-- The `p`-adic coordinate of a profinite integer. -/
def zHatToPadicInt :
    ZHat →+* ℤ_[p.1] :=
  PadicInt.lift (zHatPadicReduction_compatible p)

@[simp]
theorem toZModPow_zHatToPadicInt (n : ℕ) :
    (PadicInt.toZModPow n).comp (zHatToPadicInt p) =
      zHatPadicReduction p n :=
  PadicInt.lift_spec (zHatPadicReduction_compatible p) n

end

/-- The canonical ring homomorphism `ℤ̂ → ∏ₚ ℤ_p`. -/
def zHatToProfiniteIntegerPrimeProduct :
    ZHat →+* ProfiniteIntegerPrimeProduct :=
  RingHom.pi zHatToPadicInt

@[simp]
theorem zHatToProfiniteIntegerPrimeProduct_apply
    (z : ZHat) (p : Nat.Primes) :
    zHatToProfiniteIntegerPrimeProduct z p =
      zHatToPadicInt p z :=
  rfl

/-- The prime-coordinate map separates profinite integers. -/
theorem zHatToProfiniteIntegerPrimeProduct_injective :
    Function.Injective zHatToProfiniteIntegerPrimeProduct := by
  intro x y hxy
  apply ZHat.ext
  intro n hn
  let e := ZMod.equivPi (n := n) hn.ne'
  apply e.injective
  funext p
  have hpPrime :=
    Nat.prime_of_mem_primeFactors p.2
  let p' : Nat.Primes := ⟨p.1, hpPrime⟩
  have hpReduction :=
    congrArg (PadicInt.toZModPow (n.factorization p.1)) (congrArg (fun z : ProfiniteIntegerPrimeProduct => z p') hxy)
  change
    ((PadicInt.toZModPow (n.factorization p.1)).comp
        (zHatToPadicInt p')) x =
      ((PadicInt.toZModPow (n.factorization p.1)).comp
        (zHatToPadicInt p')) y at hpReduction
  simp at hpReduction
  have hpowDvd :=
    (hpPrime.pow_dvd_iff_le_factorization hn.ne').2 le_rfl
  let castHom₀ := ZMod.castHom hpowDvd (ZMod (p.1 ^ n.factorization p.1))
  have hcast :
      castHom₀
          (zHatReduction n hn x) =
        castHom₀
          (zHatReduction n hn y) := by
    rw [zHatReduction_transition
        (pow_pos hpPrime.pos _) hn hpowDvd x,
      zHatReduction_transition
        (pow_pos hpPrime.pos _) hn hpowDvd y]
    exact hpReduction
  have heval (z : ZMod n) :
      e z p =
        castHom₀ z := by
    change
      ((Pi.evalRingHom
          (fun q : n.primeFactors =>
            ZMod (q.1 ^ n.factorization q.1)) p).comp
        e.toRingHom) z =
        castHom₀ z
    exact RingHom.congr_fun (Subsingleton.elim _ _) z
  rw [heval, heval]
  exact hcast

/-- Each `p`-adic coordinate map is continuous. -/
theorem continuous_zHatToPadicInt (p : Nat.Primes) :
    Continuous (zHatToPadicInt p) := by
  apply continuous_of_continuousAt_zero
    (zHatToPadicInt p).toAddMonoidHom
  rw [ContinuousAt, Metric.nhds_basis_closedBall.tendsto_right_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p.1 hε
  let K : Set ZHat :=
    (zHatPadicReduction p n).toAddMonoidHom.ker
  have hKopen : IsOpen K := by
    exact (isOpen_discrete ({0} : Set (ZMod (p.1 ^ n)))).preimage
      (zHatReduction (p.1 ^ n) (pow_pos p.2.pos n)).continuous
  have hKzero : (0 : ZHat) ∈ K := by
    exact map_zero _
  apply Filter.mem_of_superset (hKopen.mem_nhds hKzero)
  intro z hz
  change zHatPadicReduction p n z = 0 at hz
  have hmod :
      PadicInt.toZModPow n (zHatToPadicInt p z) = 0 := by
    have hspec :=
      RingHom.congr_fun (toZModPow_zHatToPadicInt p n) z
    rw [RingHom.comp_apply] at hspec
    rw [hspec]
    exact hz
  simp only [Set.mem_ofPred_eq, map_zero]
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow
    (zHatToPadicInt p z) n).2 (by
      simp [← PadicInt.ker_toZModPow n]
      exact hmod) |>.trans hn.le

/-- The canonical map to the full prime product is continuous. -/
theorem continuous_zHatToProfiniteIntegerPrimeProduct :
    Continuous zHatToProfiniteIntegerPrimeProduct :=
  continuous_pi continuous_zHatToPadicInt

/-- The diagonal copy of `ℤ` is dense in the product of all `ℤ_p`.
This is the topological form of the finite Chinese remainder theorem. -/
theorem denseRange_intCast_profiniteIntegerPrimeProduct :
    DenseRange
      (Int.castRingHom ProfiniteIntegerPrimeProduct) := by
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨x, hx⟩
  obtain ⟨S, u, hu, hSu⟩ :=
    isOpen_pi_iff.mp hU x hx
  have hNhd (p : ↥S) :
      u p.1 ∈ 𝓝 (x p.1) :=
    (hu p.1 p.2).1.mem_nhds (hu p.1 p.2).2
  choose ε hε hεsub using fun p : ↥S =>
    Metric.nhds_basis_closedBall.mem_iff.mp (hNhd p)
  choose k hk using fun p : ↥S =>
    PadicInt.exists_pow_neg_lt p.1.1 (hε p)
  let modulus :=
    fun p => p.1.1 ^ k p
  have hcoprime :
      Pairwise (fun p q : ↥S =>
        Nat.Coprime (modulus p) (modulus q)) := by
    intro p q hpq
    apply Nat.coprime_pow_primes
      (k p) (k q) p.1.2 q.1.2
    intro hpval
    apply hpq
    apply Subtype.ext
    apply Nat.Primes.coe_nat_injective
    exact hpval
  let target :=
    fun p => PadicInt.toZModPow (k p) (x p.1)
  let crt :=
    ZMod.prodEquivPi modulus hcoprime
  obtain ⟨a, ha⟩ :=
    ZMod.intCast_surjective (crt.symm target)
  use Int.castRingHom ProfiniteIntegerPrimeProduct a
  refine ⟨hSu ?_, a, rfl⟩
  intro p hp
  let pS : ↥S := ⟨p, hp⟩
  apply hεsub pS
  rw [Metric.mem_closedBall, dist_eq_norm]
  let castHom₀ := ZMod.castHom (Finset.dvd_prod_of_mem modulus (Finset.mem_univ pS)) (ZMod (modulus pS))
  have hres :
      PadicInt.toZModPow (k pS)
          ((a : ℤ_[p.1])) =
        PadicInt.toZModPow (k pS) (x p) := by
    let ZMod₀ := ZMod (∏ q : ↥S, modulus q)
    have heval (z : ZMod₀) :
        crt z pS =
          castHom₀ z := by
      change
        ((Pi.evalRingHom
            (fun q : ↥S => ZMod (modulus q)) pS).comp
          crt.toRingHom) z =
          castHom₀ z
      exact RingHom.congr_fun (Subsingleton.elim _ _) z
    calc
      _ =
          (a : ZMod (modulus pS)) := by
            simp [modulus, pS]
      _ =
          castHom₀
            (a : ZMod₀) := (map_intCast
                  (castHom₀) a).symm
      _ = crt (a : ZMod₀) pS :=
            (heval (a : ZMod₀)).symm
      _ = crt (crt.symm target) pS := by rw [ha]
      _ = target pS := congrFun (crt.apply_symm_apply target) pS
      _ = PadicInt.toZModPow (k pS) (x p) := rfl
  have hmem :
      (a : ℤ_[p.1]) - x p ∈
        Ideal.span
          ({(p.1 : ℤ_[p.1]) ^ k pS} : Set ℤ_[p.1]) := by
    rw [← PadicInt.ker_toZModPow (k pS), RingHom.mem_ker,
      map_sub, hres, sub_self]
  exact
    (PadicInt.norm_le_pow_iff_mem_span_pow
      ((a : ℤ_[p.1]) - x p) (k pS)).2 hmem |>.trans
      (hk pS).le

@[simp]
theorem zHatToPadicInt_intCast
    (p : Nat.Primes) (a : ℤ) :
    zHatToPadicInt p (a : ZHat) = (a : ℤ_[p.1]) :=
  map_intCast (zHatToPadicInt p) a

@[simp]
theorem zHatToProfiniteIntegerPrimeProduct_intCast
    (a : ℤ) :
    zHatToProfiniteIntegerPrimeProduct (a : ZHat) =
      Int.castRingHom ProfiniteIntegerPrimeProduct a := by
  funext p
  apply zHatToPadicInt_intCast

/-- The canonical map from the profinite integers to the product of all
`p`-adic integers is onto.  Compactness closes its range, while the finite
Chinese remainder theorem makes that range dense. -/
theorem zHatToProfiniteIntegerPrimeProduct_surjective :
    Function.Surjective zHatToProfiniteIntegerPrimeProduct := by
  have hsubset :
      Set.range (Int.castRingHom ProfiniteIntegerPrimeProduct) ⊆
        Set.range zHatToProfiniteIntegerPrimeProduct := by
    rintro y ⟨a, rfl⟩
    exact
      ⟨(a : ZHat),
        zHatToProfiniteIntegerPrimeProduct_intCast a⟩
  intro y
  have hy :
      y ∈ closure
        (Set.range zHatToProfiniteIntegerPrimeProduct) := by
    rw [(denseRange_intCast_profiniteIntegerPrimeProduct.mono hsubset).closure_eq]
    trivial
  rwa [((isCompact_range
    continuous_zHatToProfiniteIntegerPrimeProduct).isClosed).closure_eq] at hy

/-- The Chinese-remainder ring equivalence
`ℤ̂ ≃ ∏ p : Nat.Primes, ℤ_p`. -/
noncomputable def zHatRingEquivProfiniteIntegerPrimeProduct :
    ZHat ≃+* ProfiniteIntegerPrimeProduct :=
  RingEquiv.ofBijective zHatToProfiniteIntegerPrimeProduct
    ⟨zHatToProfiniteIntegerPrimeProduct_injective,
      zHatToProfiniteIntegerPrimeProduct_surjective⟩

@[simp]
theorem zHatRingEquivProfiniteIntegerPrimeProduct_apply
    (z : ZHat) :
    zHatRingEquivProfiniteIntegerPrimeProduct z =
      zHatToProfiniteIntegerPrimeProduct z :=
  rfl

end ClassFormation

end
