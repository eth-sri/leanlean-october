/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.FailedScans
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Need

/-!
# The host of Theorem 17: the time of a run is within the worst case

The host procedure `et17` (Exact Triangle by Theorem 17) first computes the parameters, chooses the
prime and computes the sizes.  The time of what follows (the table of doubles, the residues, the
classes, the chunks and the loop over the instances; `hostRunTime`) depends on the data: the prime,
the number of chunks, the scans.  Here it is bounded by the corresponding summands of `hostMain`,
which depend on `n`, `U`, `D` and `g` only (`hostRunTime_le`).

* The prime is at most `√D` (`hostData_p_le`), and there are at most `4ng` instances and no more
  chunks than instances (`hostData_m_le`, `HostTime.chunkCount_le_m`).
* An instance has a piece of at most `q = ⌈s/g⌉` vertices, where `s = ⌊√D⌋`, and at most `⌊n²/√D⌋`
  query pairs, so its time without the scans is at most the worst case (`HostTime.instance_le`).
* All scans but one fail, and a failed scan belongs to a false positive of the chosen prime.  The
  proof of Theorem 17 bounds their number (`F_le_falsePositiveBound`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp.Spec

/-- The number of false positives of the chosen prime is at most `falsePositiveBound`. -/
theorem F_le_falsePositiveBound {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ} (hpre : x.Pre μ fr)
    (h : BigCase x.n D g) :
    (triOf x.n x.AB x.BC x.AC).F (chosenPrime x.n D x.AB x.BC x.AC)
      ≤ falsePositiveBound x.n x.U D :=
  Nat.le_floor (F_chosenPrime_le h.sixteen_le h.le_n hpre.U_pos hpre.arrAB.bound hpre.arrBC.bound hpre.arrAC.bound)

/-- Writing the two matrices of an instance takes longer for a larger inner dimension and for a
longer piece. -/
theorem tWrites_le (n : ℕ) {D D' a b : ℕ} (hD : D ≤ D') (h : a ≤ b) :
    tWrites n D a ≤ tWrites n D' b := by
  unfold tWrites tWrite
  gcongr


/-- A sum of `m ≤ M` terms `f t ≤ A + B e(t)` is at most `M A + B E` if the `e(t)` add up to at most
`E`. -/
theorem sum_le_mul_add {m M A B E : ℕ} {f e : ℕ → ℕ} (hf : ∀ t < m, f t ≤ A + B * e t)
    (hm : m ≤ M) (he : ∑ t ∈ Finset.range m, e t ≤ E) :
    ∑ t ∈ Finset.range m, f t ≤ M * A + B * E :=
  calc ∑ t ∈ Finset.range m, f t ≤ ∑ t ∈ Finset.range m, (A + B * e t) :=
        Finset.sum_le_sum fun t ht => hf t (Finset.mem_range.1 ht)
    _ = m * A + B * ∑ t ∈ Finset.range m, e t := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
          Finset.mul_sum]
    _ ≤ M * A + B * E := Nat.add_le_add (Nat.mul_le_mul_right _ hm) (Nat.mul_le_mul_left _ he)

/-- There are at most as many chunks as instances. -/
theorem chunkCount_le_m {X : HostData} (hv : X.Valid) : X.chunkCount ≤ X.m := by
  have hn := hv.n_pos
  have hq := hv.q_pos
  have hpieces : 1 ≤ X.h := by
    rw [HostData.h, Nat.ceilDiv_eq_add_pred_div, Nat.le_div_iff_mul_le (by omega)]
    omega
  rw [HostData.m]
  nlinarith


end Light.Sec3
