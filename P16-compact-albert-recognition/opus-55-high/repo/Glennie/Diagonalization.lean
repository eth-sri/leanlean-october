/- Native compact diagonalization from actual automorphisms and a maximum.
No compact spectral theorem is an assumption of this proof. -/
module
public import Glennie.Compactness
public import Glennie.ScalarRotation
public import Glennie.Native.Triality
public import Glennie.Native.RealConjugation

@[expose] public section
namespace Glennie

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
  unfold diagonalEnergy at hmax
  rw [realRotation12_d0, realRotation12_d1, realRotation12_d2,
    h0, h1, h2, hslot, octRe_scalar] at hmax
  nlinarith 

theorem realSwap01_diagonalEnergy (x : Albert) :
    diagonalEnergy (realSwap01Automorphism.equiv x) = diagonalEnergy x := by
  change diagonalEnergy (realConjugateAlbert realSwap01 x) = _
  rw [realSwap01_coordinates]
  simp [diagonalEnergy]
  ring

theorem realSwap02_diagonalEnergy (x : Albert) :
    diagonalEnergy (realSwap02Automorphism.equiv x) = diagonalEnergy x := by
  change diagonalEnergy (realConjugateAlbert realSwap02 x) = _
  rw [realSwap02_coordinates]
  simp [diagonalEnergy]
  ring

theorem maximalDiagonalEnergy_isDiagonal (x : Albert) (hx : HasMaximalDiagonalEnergy x) :
    IsDiagonal x := by
  have h12 := maximalDiagonalEnergy_slot12_zero x hx
  have h02 := maximalDiagonalEnergy_slot12_zero (realSwap01Automorphism.equiv x)
    (maximalDiagonalEnergy_after x hx _ (realSwap01_diagonalEnergy x))
  have h01 := maximalDiagonalEnergy_slot12_zero (realSwap02Automorphism.equiv x)
    (maximalDiagonalEnergy_after x hx _ (realSwap02_diagonalEnergy x))
  change (realConjugateAlbert realSwap01 x).o12 = 0 at h02
  change (realConjugateAlbert realSwap02 x).o12 = 0 at h01
  rw [realSwap01_coordinates] at h02
  rw [realSwap02_coordinates] at h01
  have h01' : x.o01 = 0 := by
    have h := congrArg octConj h01
    have hz : octConj (0 : Octonion) = 0 := by
      change (star (0 : Quaternion ℝ), -(0 : Quaternion ℝ)) = (0,0)
      simp [star_zero, neg_zero]
    simpa [octConj_conj, hz] using h
  exact ⟨h01', h02, h12⟩

/-- Diagonalization in the genuine native product/trace automorphism group. -/
theorem native_diagonalization (x : Albert) :
    ∃ g : CompactAutomorphism, IsDiagonal (g.equiv x) := by
  obtain ⟨g, hg⟩ := exists_diagonalEnergy_maximum x
  refine ⟨g, maximalDiagonalEnergy_isDiagonal _ ?_⟩
  intro h
  exact hg (h.comp g)

end Glennie
