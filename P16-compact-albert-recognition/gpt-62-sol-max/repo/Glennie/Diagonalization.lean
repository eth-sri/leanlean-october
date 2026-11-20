/- Native compact diagonalization from actual automorphisms and a maximum.
No compact spectral theorem is an assumption of this proof. -/
module
public import Glennie.Compactness
public import Glennie.ScalarRotation
public import Glennie.Native.Triality
public import Glennie.Native.RealConjugation
@[expose] public section
namespace Glennie
noncomputable section

def HasMaximalDiagonalEnergy (x : Albert) : Prop :=
  ∀ g : CompactAutomorphism, diagonalEnergy (g.equiv x) ≤ diagonalEnergy x

theorem maximalDiagonalEnergy_after (x : Albert) (hx : HasMaximalDiagonalEnergy x)
    (g : CompactAutomorphism) (hg : diagonalEnergy (g.equiv x) = diagonalEnergy x) :
    HasMaximalDiagonalEnergy (g.equiv x) := by
  intro h
  rw [hg]
  exact hx (h.comp g)

theorem maximalDiagonalEnergy_slot12_zero (x : Albert) (hx : HasMaximalDiagonalEnergy x) :
    x.o12 = 0 := by
  by_contra hn
  obtain ⟨g, n, hn, h0, h1, h2, hslot⟩ := OctRelatedTriple.make_slot12_real x hn
  obtain ⟨c, s, hcs, he⟩ := exists_rotation_improving_energy x.d1 x.d2 n hn
  have hmax := hx ((realRotation12Automorphism c s hcs).comp g)
  change diagonalEnergy (realConjugateAlbert (realRotation12 c s) (g.equiv x)) ≤
    diagonalEnergy x at hmax
  have hD := realRotation12_diag c s (g.equiv x)
  have hx0 := hD 0
  have hx1 := hD 1
  have hx2 := hD 2
  simp [toMatrix, h0, h1, h2, hslot] at hx0 hx1 hx2
  rw [diagonalEnergy, hx0, hx1, hx2, diagonalEnergy] at hmax
  nlinarith [he]

private theorem permutation_diagonalEnergy (s : Equiv.Perm (Fin 3)) (x : Albert) :
    diagonalEnergy ((permutationAutomorphism s).equiv x) = diagonalEnergy x := by
  have h (y : Albert) : diagonalEnergy y = ∑ i, octRe (toMatrix y i i) ^ 2 := by
    simp [diagonalEnergy, Fin.sum_univ_three, toMatrix]
  simp only [h, toMatrix_permutation]
  exact Equiv.sum_comp s (fun i => octRe (toMatrix x i i) ^ 2)

theorem maximalDiagonalEnergy_isDiagonal (x : Albert) (hx : HasMaximalDiagonalEnergy x) :
    IsDiagonal x := by
  have h (s : Equiv.Perm (Fin 3)) : toMatrix x (s 1) (s 2) = 0 := by
    rw [← toMatrix_permutation]
    exact maximalDiagonalEnergy_slot12_zero _
      (maximalDiagonalEnergy_after x hx _ (permutation_diagonalEnergy s x))
  refine ⟨?_, ?_, maximalDiagonalEnergy_slot12_zero x hx⟩
  · exact h (Equiv.subRight 1)
  · change toMatrix x 0 2 = 0
    simpa only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 1) (by decide : (2 : Fin 3) ≠ 0)] using h (Equiv.swap 1 0)

/-- Diagonalization in the genuine native product/trace automorphism group. -/
theorem native_diagonalization (x : Albert) :
    ∃ g : CompactAutomorphism, IsDiagonal (g.equiv x) := by
  obtain ⟨g, hg⟩ := exists_diagonalEnergy_maximum x
  refine ⟨g, maximalDiagonalEnergy_isDiagonal _ ?_⟩
  intro h
  exact hg (h.comp g)

end
end Glennie
