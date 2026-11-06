module
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import DensityEnergyGM.DFIWeight
public import GuthMaynard.NativeSource.GuthMaynard.QuadraticDivisor

@[expose] public section

open Complex Finset Set Classical
open scoped BigOperators ContDiff Topology ArithmeticFunction.Moebius

namespace GuthMaynard.NativeMoment

/-!
# DFI equations (9)--(19): the delta symbol

The source chooses an even smooth function `w`, supported where
`Q ≤ |u| ≤ 2Q`, normalized by `∑_{r≥1} w(r)=1`, and satisfying
`w^(j)(u) ≪_j Q^(-j-1)`.  These are equations (9) and (13).

The support makes every series in the delta symbol finite at each argument.
The definitions below expose an explicit radius large enough to contain every
nonzero term; later identities can therefore use ordinary `Finset` algebra.
-/

/-- The source cutoff used in DFI equations (9)--(19). -/
structure DFIDeltaWeight (Q : ℝ) where
  /-- The `toFun` component of `DFIDeltaWeight`. -/
  toFun : ℝ → ℝ
  one_le_Q : 1 ≤ Q
  smooth : ContDiff ℝ ∞ toFun
  even : ∀ u : ℝ, toFun (-u) = toFun u
  support_annulus : Function.support toFun ⊆
    {u : ℝ | Q ≤ |u| ∧ |u| ≤ 2 * Q}
  normalized : ∑' r : ℕ, toFun (r + 1 : ℕ) = 1
  derivativeBound : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ,
    ‖iteratedDeriv j toFun u‖ ≤ C * (Q ^ (j + 1))⁻¹

instance {Q : ℝ} : CoeFun (DFIDeltaWeight Q) (fun _ => ℝ → ℝ) :=
  ⟨DFIDeltaWeight.toFun⟩

theorem DFIDeltaWeight.Q_pos {Q : ℝ} (w : DFIDeltaWeight Q) : 0 < Q :=
  lt_of_lt_of_le zero_lt_one w.one_le_Q

/-- The annular support forces the source weight to vanish close to zero. -/
theorem DFIDeltaWeight.eq_zero_of_abs_lt {Q u : ℝ} (w : DFIDeltaWeight Q)
    (hu : |u| < Q) : w u = 0 := by
  by_contra hne
  have hmem : u ∈ Function.support w.toFun := hne
  exact (not_le_of_gt hu) (w.support_annulus hmem).1

@[simp]
theorem DFIDeltaWeight.zero {Q : ℝ} (w : DFIDeltaWeight Q) : w 0 = 0 := by
  apply w.eq_zero_of_abs_lt
  simpa using w.Q_pos

/-- A common finite radius containing the `r`-support of both
`w(qr)` and `w(u/(qr))`.  It is deliberately a generous radius; exact
minimality is irrelevant, while its explicit dependence is useful below. -/
noncomputable def dfiDeltaRadius (Q u : ℝ) : ℕ :=
  ⌈2 * Q + |u| / Q⌉₊ + 1

/-- Ramanujan's complete reduced-residue sum at an integer frequency. -/
noncomputable def ramanujanSumInt (q : ℕ) (n : ℤ) : ℂ :=
  if hq : q = 0 then 0
  else
    letI : NeZero q := ⟨hq⟩
    ∑ d ∈ Finset.range q with Nat.Coprime d q,
      ZMod.stdAddChar ((n : ZMod q) * (d : ZMod q))

@[simp]
theorem ramanujanSumInt_zero (q : ℕ) :
    ramanujanSumInt q 0 = (Nat.totient q : ℂ) := by
  by_cases hq : q = 0
  · simp [ramanujanSumInt, hq]
  · let : NeZero q := ⟨hq⟩
    simp only [ramanujanSumInt, hq, ↓reduceDIte, Int.cast_zero, zero_mul,
      sum_const, nsmul_eq_mul]
    norm_cast
    simpa [Nat.coprime_comm] using (Nat.totient_eq_card_coprime q).symm

/-- Positive reduced residue classes, represented by the literal range used
in the complete exponential sum. -/
def dfiCoprimeResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun d => Nat.Coprime d q

/-- Raising the standard primitive `q`-th root to reduced residue powers is
the bijection between reduced residues and all primitive `q`-th roots. -/
noncomputable def dfiCoprimeResiduesEquivPrimitiveRoots (q : ℕ) [NeZero q] :
    ↥(dfiCoprimeResidues q) ≃ ↥(primitiveRoots q ℂ) := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)
  have hζ : IsPrimitiveRoot ζ q := Complex.isPrimitiveRoot_exp q NeZero.out
  let F : ↥(dfiCoprimeResidues q) → ↥(primitiveRoots q ℂ) := fun d =>
    ⟨ζ ^ d.1, by
      rw [mem_primitiveRoots (Nat.pos_of_ne_zero NeZero.out)]
      exact hζ.pow_of_coprime d.1 (Finset.mem_filter.mp d.2).2⟩
  apply Equiv.ofBijective F
  constructor
  · intro d e hde
    apply Subtype.ext
    apply hζ.pow_inj
    · exact Finset.mem_range.mp (Finset.mem_filter.mp d.2).1
    · exact Finset.mem_range.mp (Finset.mem_filter.mp e.2).1
    · exact congrArg Subtype.val hde
  · intro ξ
    have hξ := ξ.2
    rw [mem_primitiveRoots (Nat.pos_of_ne_zero NeZero.out),
      hζ.isPrimitiveRoot_iff] at hξ
    obtain ⟨i, hi, hcop, hpow⟩ := hξ
    let d : ↥(dfiCoprimeResidues q) :=
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hcop⟩⟩
    refine ⟨d, ?_⟩
    apply Subtype.ext
    exact hpow

@[simp]
theorem dfiCoprimeResiduesEquivPrimitiveRoots_apply
    (q : ℕ) [NeZero q] (d : ↥(dfiCoprimeResidues q)) :
    ((dfiCoprimeResiduesEquivPrimitiveRoots q d : ↥(primitiveRoots q ℂ)) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I / q) ^ d.1 := by
  rfl

end GuthMaynard.NativeMoment
