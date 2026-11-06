module

public import ThreeSumApsp.Util.Types
public import Mathlib.Tactic
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

open Light Light.Sec3 ThreeSumApsp.Spec

/-- Writing the two matrices of an instance takes longer for a larger inner dimension and for a
longer piece. -/
theorem tWrites_le n {D D' a b} (hD : D ≤ D') (h : a ≤ b) :
    tWrites n D a ≤ tWrites n D' b := by
  unfold tWrites tWriteX tWriteY
  gcongr

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Time.lean
/-- The time of an instance of the variant with a piece of `len ≤ q` vertices, `w ≤ cap` query
pairs and `execs` scans is at most the worst case for `q` and `cap` plus the time of the scans. -/
theorem instance_le' Tn n D g execs {len q w cap} (hlen : len ≤ q)
    (hw : w ≤ cap) :
    tWrites n (midSize D g) len + Tn [n, midSize D g, w] + tScanPairs w len execs
      ≤ tWrites n D q + supTime Tn n (midSize D g) cap + tAnswers cap + tScanCall q * execs := by
  have  := tWrites_le n (midSize_le D g) hlen
  have : _ ≤ supTime Tn n (midSize D g) cap :=
    Finset.le_sup (Finset.mem_range.2 (Nat.lt_succ_of_le hw))
  simp_all [tAnswers, tScanCall, tScan, tScanPairs] <;> nlinarith

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Time.lean
/-- A sum of `m ≤ M` terms `f t ≤ A + B e(t)` is at most `M A + B E` if the `e(t)` add up to at most
`E`. -/
def sum_le_mul_add {m M A B E} {f e : ℕ → ℕ} (hf : ∀ t < m, f t ≤ A + B * e t)
     hm he :=
  calc ∑ t ∈ Finset.range m, f t ≤ ∑ t ∈ Finset.range m, (A + B * e t) :=
        Finset.sum_le_sum fun t ht => hf t (Finset.mem_range.1 ht)
    _ = m * A + B * ∑ t ∈ Finset.range m, e t := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
          Finset.mul_sum]
    _ ≤ M * A + B * E := Nat.add_le_add (Nat.mul_le_mul_right _ hm) (Nat.mul_le_mul_left _ he)

variable {x : TriInst} {μ : Light.Memory} {fr D g : ℕ}

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Time.lean
/-- There are at most as many chunks as instances. -/
theorem chunkCount_le_m {X : HostData} (hv : X.Valid) : X.chunkCount ≤ X.m := by
  have  := hv.n_pos
  have  := hv.q_pos

  rw [HostData.m]
  exact Nat.le_mul_of_pos_left _ (by
    rw [HostData.h, Nat.ceilDiv_eq_add_pred_div, Nat.le_div_iff_mul_le (by omega)]
    omega
   : 1 ≤ X.h)

/-- All scans but one fail, and there are at most `falsePositiveBound` failed scans. -/
def sum_execs_le_falsePositiveBound' (hpre : x.Pre μ fr) hbig :=
  (hostData' x D g).sum_execs_le.trans (Nat.add_le_add_right
    ((HostData.sum_fails_le (hostData'_valid hpre hbig)).trans
      (F_le_falsePositiveBound hpre hbig)) 1)

variable (hpre : x.Pre μ fr) (hbig : BigCase x.n D g)

include hpre hbig in
/-- The time of the loop over the instances of the variant is within its bound. -/
theorem tHostLoop_le'  Tn :
    tHostLoop Tn (hostData' x D g) ≤ hostLoopBound' Tn x.n x.U D g :=
  Nat.add_le_add_right (sum_le_mul_add
    (fun _ ht => instance_le' Tn x.n D g _ (Nat.min_le_left _ _) ((hostData' x D g).w_le_cap ht))
    (hostData'_m_le hbig) (sum_execs_le_falsePositiveBound' hpre hbig)) 14

include hpre hbig in
/-- **The time of a run of the variant after the choice of the prime is within the worst case.** -/
theorem hostRunTime_le'  Tn :
    hostRunTime Tn (hostData' x D g) x.U
      ≤ tDblTable (bitLen x.U) + 3 * tResidues (x.n * x.n) (bitLen x.U)
        + tClasses x.n (Nat.sqrt D) + tChunks (Nat.sqrt D) (4 * x.n * g)
        + hostLoopBound' Tn x.n x.U D g + 80 := by
  have  := hostData'_p_le x g hbig.sixteen_le
  have  :=
    (chunkCount_le_m (hostData'_valid hpre hbig)).trans (hostData'_m_le hbig)
  have  := tHostLoop_le' hpre hbig Tn
  have hn : (hostData' x D g).n = x.n := rfl
  unfold hostRunTime
  rw [hn]
  unfold tClasses tChunks
  omega

end ImprovedExponents.HostMid
