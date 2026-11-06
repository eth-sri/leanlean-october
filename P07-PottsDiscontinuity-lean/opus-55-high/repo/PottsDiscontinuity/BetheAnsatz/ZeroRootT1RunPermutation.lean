module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1RunPath

/-!
# Permutation carried by a zero-root zipper run

The successive adjacent swaps in the zipper run form one explicit permutation.
It moves the root from the first path slot to the last and fixes slots outside
the path.
-/

@[expose] public section

namespace PottsDiscontinuity.BetheAnsatz

/-- The permutation accumulated by the adjacent swaps along a zipper path. -/
def zeroRootZipperPerm {n : ℕ} : List (Fin (n + 1)) → Equiv.Perm (Fin (n + 1))
  | [] => 1
  | [_] => 1
  | a :: b :: rest => Equiv.swap a b * zeroRootZipperPerm (b :: rest)

section
variable {n : ℕ} (path : List (Fin (n + 1)))
theorem zeroRootZipperRun_perm (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) :
    (zeroRootZipperRun path (σ, w)).1 = σ * zeroRootZipperPerm path := by
  induction path generalizing σ w with
  | nil => rfl
  | cons a tail ih =>
      cases tail with
      | nil => rfl
      | cons b rest =>
          tauto

theorem zeroRootZipperPerm_apply_of_not_mem (k : Fin (n + 1))
    (hk : k ∉ path) : zeroRootZipperPerm path k = k := by
  induction path with
  | nil => rfl
  | cons a tail ih =>
      cases tail with
      | nil => rfl
      | cons b rest =>
          have htail : k ∉ b :: rest := by
            simp_all
          rw [zeroRootZipperPerm, Equiv.Perm.mul_apply, ih htail]
          grind

theorem zeroRootZipperPerm_getLast_eq_headD (hne : path ≠ []) :
    zeroRootZipperPerm path (path.getLast hne) = path.headD 0 := by
  have h := zeroRootZipperRun_root_at_last
    path 1 (fun _ => false) hne rfl
  simp_all [zeroRootZipperRun_perm]
end

section
variable {n : ℕ} {l : Fin (n + 1)} (i : T1PairIndex n l)
theorem t1PairZipperPath_left_not_mem  : t1EdgeLeft i.edge ∉ t1PairZipperPath i := by
  intro hmem
  have htrue := t1PairZipperPath_letters i (t1EdgeLeft i.edge) hmem
  rw [i.hleft] at htrue
  contradiction

/-- The run changes only the labels on its path. In particular, the original
ML left endpoint keeps its momentum label. -/
theorem t1PairZipperRun_left  :
    (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).1
      (t1EdgeLeft i.edge) = i.σ (t1EdgeLeft i.edge) := by
  simp [zeroRootZipperRun_perm, zeroRootZipperPerm_apply_of_not_mem, t1PairZipperPath_left_not_mem]
end

end PottsDiscontinuity.BetheAnsatz
