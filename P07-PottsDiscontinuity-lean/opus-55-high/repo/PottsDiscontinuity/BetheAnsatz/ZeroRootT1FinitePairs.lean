module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamResidue

/-!
# Finite sums of corrected T₁ pairs

This module sums the already checked ordinary-edge and seam-pair limits over a
finite type of canonical pair representatives. The combinatorial identification
of that type with the source's W₁ indexing is kept separate.
-/

@[expose] public noncomputable section

open Finset Complex Filter Topology Classical

namespace PottsDiscontinuity.BetheAnsatz

section
variable {n : ℕ}
/-- The left endpoint of an ordinary or seam edge in the cyclic word. -/
def t1EdgeLeft (a : Option (Fin n)) : Fin (n + 1) :=
  a.elim (Fin.last n) Fin.castSucc

/-- The right endpoint of an ordinary or seam edge in the cyclic word. -/
def t1EdgeRight (a : Option (Fin n)) : Fin (n + 1) :=
  a.elim 0 Fin.succ
end

theorem t1EdgeLeft_rotate {n : ℕ} (e : Option (Fin n)) :
    finRotate (n + 1) (t1EdgeLeft e) = t1EdgeRight e := by
  cases e with
  | none => exact finRotate_last
  | some a => exact finRotate_of_lt a.isLt

/-- A canonical representative of a paired T₁ contribution. `none` denotes
the seam edge `last → 0`; `some a` denotes the ordinary edge `a.castSucc → a.succ`.
The word is required to have this as its unique cyclic `ML` edge. -/
structure T1PairIndex (n : ℕ) (l : Fin (n + 1)) where
  σ : Equiv.Perm (Fin (n + 1))
  w : Fin (n + 1) → Bool
  edge : Option (Fin n)
  hσ : σ (t1EdgeRight edge) = l
  hleft : w (t1EdgeLeft edge) = false
  hright : w (t1EdgeRight edge) = true
  hunique : ∀ k, w k = false → w (finRotate (n + 1) k) = true →
    k = t1EdgeLeft edge

instance t1PairIndexFintype {n : ℕ} {l : Fin (n + 1)} :
    Fintype (T1PairIndex n l) := by
  classical
  apply Fintype.ofInjective (fun i => (i.σ, i.w, i.edge))
  intro i j hij
  cases i with
  | mk σ w edge hσ hleft hright hunique =>
    simp_all

section
variable {N n : ℕ} (c : ℝ) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
/-- One fixed-amplitude summand together with its paired permutation term. -/
def t1PairTerm (t : ℝ)
    (i : T1PairIndex n l) : ℂ :=
  perturbedWordTerm (N := N) c x p l t i.σ i.w +
    perturbedWordTerm (N := N) c x p l t
      (i.σ * Equiv.swap (t1EdgeLeft i.edge) (t1EdgeRight i.edge)) i.w

/-- The finite limit of a paired term, with the `N` seam slope included. -/
def t1PairLimit (i : T1PairIndex n l) : ℂ :=
  ((c : ℂ)^2 * amplitude (anisotropy c) p i.σ * M c (z (p (i.σ (t1EdgeLeft i.edge)))) *
    wordCoefficientEraseEdge c (perturbedMomenta p l 0) i.σ i.w (t1EdgeLeft i.edge) *
    wordPhase (N := N) x p i.σ i.w) *
    (zeroRootPhaseDerivative (N := N) (anisotropy c) (p (i.σ (t1EdgeLeft i.edge))) (i.edge = none) : ℂ)
end

section
variable {N n : ℕ} {c : ℝ} (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0) (hBE : BetheEquations N (anisotropy c) p)
include c hc x p hp hinj hpl hBE
/-- Every canonical ordinary or seam pair has the stated finite limit. -/
theorem tendsto_t1PairTerm (i : T1PairIndex n l) :
    Tendsto (fun t : ℝ => t1PairTerm (N := N) c x p l t i)
      (𝓝[≠] (0 : ℝ)) (𝓝 (t1PairLimit (N := N) c x p l i)) := by
  have h1 := i.hσ
  have h2 := i.hleft
  have h3 := i.hright
  rw [← t1EdgeLeft_rotate] at h1 h3
  have := tendsto_T1_pair (N := N) hc x p l hpl i.σ i.w _ (i.edge = none) h1 h2 h3 fun t ht => ?_
  · simpa only [t1PairTerm, t1PairLimit, t1EdgeLeft_rotate] using this
  cases hEdge : i.edge with
  | none =>
      have hn : 0 < n := by
        rcases n with _ | n
        · simp_all [t1EdgeLeft]
        omega
      simpa [hEdge, t1EdgeLeft, t1EdgeRight] using perturbedWordTerm_seam_pair hc x p hp hinj l hpl hBE t ht i.σ i.w hn
        (by simpa [hEdge, t1EdgeRight] using i.hσ) (by simpa [hEdge, t1EdgeLeft] using i.hleft) (by simpa [hEdge, t1EdgeRight] using i.hright)
  | some a =>
      simpa [hEdge, t1EdgeLeft, t1EdgeRight, finRotate_apply, zeroRootPhaseExponent] using
        perturbedWordTerm_adjacent_pair hc x p hp hinj l hpl t ht i.σ i.w a
        (by simpa [hEdge, t1EdgeRight] using i.hσ) (by simpa [hEdge, t1EdgeLeft] using i.hleft) (by simpa [hEdge, t1EdgeRight] using i.hright)

/-- The finite sum over canonical T₁ pair representatives commutes with the
punctured limit. -/
theorem tendsto_sum_t1PairTerm  :
    Tendsto (fun t : ℝ => ∑ i : T1PairIndex n l, t1PairTerm (N := N) c x p l t i)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∑ i : T1PairIndex n l, t1PairLimit (N := N) c x p l i)) :=
  tendsto_finsetSum _ fun i _ => tendsto_t1PairTerm hc x p hp hinj l hpl hBE i
end

end PottsDiscontinuity.BetheAnsatz
