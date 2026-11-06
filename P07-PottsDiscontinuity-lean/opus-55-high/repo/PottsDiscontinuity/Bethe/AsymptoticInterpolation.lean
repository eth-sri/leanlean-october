module

public import PottsDiscontinuity.Bethe.AsymptoticOffsetControl

/-! # Canonical continuous extensions of the root offsets

The finite McShane envelope is a total, explicitly defined function. For
Lipschitz root data it agrees at every root, is Lipschitz with the same
constant, and is uniformly close to the offset step function.
-/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

noncomputable def rootOffsetExtension {n : ℕ} (hn : 0 < n)
    (q u : Fin n → ℝ) (K : NNReal) (x : ℝ) : ℝ :=
  Finset.univ.inf' (show (Finset.univ : Finset (Fin n)).Nonempty from
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩) (fun j => u j + K * |x - q j|)

section
variable {n : ℕ} (hn : 0 < n) (q u : Fin n → ℝ) (K : NNReal)
theorem rootOffsetExtension_lipschitz  :
    LipschitzWith K (rootOffsetExtension hn q u K) := by
  apply LipschitzWith.of_le_add_mul K
  intro x y
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf'
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
    (fun j => u j + K * |y - q j|)
  have hupper : rootOffsetExtension hn q u K x ≤ u j + K * |x - q j| :=
    Finset.inf'_le _ hj
  change rootOffsetExtension hn q u K y = u j + K * |y - q j| at he
  rw [he, Real.dist_eq]
  have htri : |x - q j| ≤ |y - q j| + |x - y| := by
    grind
  have := mul_le_mul_of_nonneg_left htri K.coe_nonneg
  linarith

theorem rootOffsetExtension_at_root (hpair : ∀ i j, |u i - u j| ≤ (K : ℝ) * |q i - q j|) (j : Fin n) :
    rootOffsetExtension hn q u K (q j) = u j := by
  apply le_antisymm
  · have hi : rootOffsetExtension hn q u K (q j) ≤ u j + K * |q j - q j| :=
      Finset.inf'_le _ (Finset.mem_univ j)
    simp_all
  · apply Finset.le_inf'
    grind
end

/-- The continuous envelope and the source step function differ by at most
the Lipschitz constant times the largest root gap. -/
theorem offsetFunction_sub_extension_le {N r : ℕ} (h4 : 4 ∣ N) (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hn : 0 < N / 2 - r) (hq : q ∈ S_n (N / 2 - r)) (K : NNReal)
    (hpair : ∀ i j,
      |offsetDisplacement N r h4 hr p q i - offsetDisplacement N r h4 hr p q j| ≤
        (K : ℝ) * |q i - q j|) {d : ℝ}
    (hmesh : ∀ j : Fin (N / 2 - r + 1),
      rootPartitionPoint (N / 2 - r) q hn j.succ -
        rootPartitionPoint (N / 2 - r) q hn j.castSucc ≤ d)
    {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    |offsetFunction N r h4 hr p q hn x -
      rootOffsetExtension hn q (offsetDisplacement N r h4 hr p q) K x| ≤ (K : ℝ) * d := by
  obtain ⟨j, hj, hd⟩ := offsetFunction_near_root h4 hr hn hq hmesh hx
  rw [hj, ← rootOffsetExtension_at_root hn q (offsetDisplacement N r h4 hr p q) K hpair j]
  have hl := (rootOffsetExtension_lipschitz hn q (offsetDisplacement N r h4 hr p q) K).dist_le_mul
    (q j) x
  rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (q j) x] at hl
  nlinarith

end PottsDiscontinuity.Bethe
