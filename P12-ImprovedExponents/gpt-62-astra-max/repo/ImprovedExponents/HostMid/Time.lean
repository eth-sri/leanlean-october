module

public import ImprovedExponents.HostMid.Arrays

@[expose] public section

/-!
# The variant host: the time of a run is within the worst case

The time of the third part depends on the data of the run.  As upstream (`Host/Time.lean`), this
file bounds it by the worst case that `hostTime'` charges: at most `4ng` instances, each with a
piece of at most `q` vertices and at most `⌊n²/√D⌋` query pairs, and at most
`falsePositiveBound + 1` scans.  The solver is charged at the inner dimension `midSize D g` that it
is called with; writing the matrices is charged at `D`, which is more.
-/

namespace ImprovedExponents.HostMid

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- Writing the two matrices of an instance takes longer for a larger inner dimension and for a
longer piece. -/
theorem tWrites_le (n : ℕ) {D D'} (hD : D ≤ D') :
    tWrites n D ≤ tWrites n D' := by
  unfold tWrites MatrixWrite.cost
  gcongr

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Time.lean

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Time.lean
/-- A sum of `m ≤ M` terms `f t ≤ A + B e(t)` is at most `M A + B E` if the `e(t)` add up to at most
`E`. -/
theorem sum_le_mul_add {m M A B E } {f e : ℕ → ℕ} (hf : ∀ t < m, f t ≤ A + B * e t)
    (hm : m ≤ M) (he : ∑ t ∈ Finset.range m, e t ≤ E) :
    ∑ t ∈ Finset.range m, f t ≤ M * A + B * E :=
  calc ∑ t ∈ Finset.range m, f t ≤ ∑ t ∈ Finset.range m, (A + B * e t) :=
        Finset.sum_le_sum fun t ht => hf t (Finset.mem_range.1 ht)
    _ = m * A + B * ∑ t ∈ Finset.range m, e t := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
          Finset.mul_sum]
    _ ≤ M * A + B * E := Nat.add_le_add (Nat.mul_le_mul_right _ hm) (Nat.mul_le_mul_left _ he)

variable {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ}

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Time.lean
/-- There are at most as many chunks as instances. -/
theorem chunkCount_le_m {X : HostData} (hv : X.Valid) : X.chunkCount ≤ X.m := by
  have hn := hv.n_pos
  have hq := hv.q_pos
  have hpieces : 1 ≤ X.h := by
    rw [HostData.h, Nat.ceilDiv_eq_add_pred_div, Nat.le_div_iff_mul_le (by omega)]
    omega
  exact Nat.le_mul_of_pos_left _ hpieces

end ImprovedExponents.HostMid
