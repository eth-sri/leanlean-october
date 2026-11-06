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
variable (x : Albert)
include x in

def HasMaximalDiagonalEnergy  : Prop :=
  ∀ g : CompactAutomorphism, diagonalEnergy (g.equiv x) ≤ diagonalEnergy x
include x in

theorem maximalDiagonalEnergy_after  (hx : HasMaximalDiagonalEnergy x)
    (g : CompactAutomorphism) (hg : diagonalEnergy (g.equiv x) = diagonalEnergy x) :
    HasMaximalDiagonalEnergy (g.equiv x) := by
  intro h
  rw [hg]
  exact hx (h.comp g)
include x in

theorem maximalDiagonalEnergy_slot12_zero  (hx : HasMaximalDiagonalEnergy x) :
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
  nlinarith [he]
include x in

theorem realSwap01_diagonalEnergy  :
    diagonalEnergy (realSwap01Automorphism.equiv x) = diagonalEnergy x := by
  change diagonalEnergy (realConjugateAlbert realSwap01 x) = _
  rw [realSwap01_coordinates]
  simp only [diagonalEnergy]
  ring
include x in

theorem realSwap02_diagonalEnergy  :
    diagonalEnergy (realSwap02Automorphism.equiv x) = diagonalEnergy x := by
  change diagonalEnergy (realConjugateAlbert realSwap02 x) = _
  rw [realSwap02_coordinates]
  simp only [diagonalEnergy]
  ring
include x in

theorem maximalDiagonalEnergy_isDiagonal  (hx : HasMaximalDiagonalEnergy x) :
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
      simp only [star_zero, neg_zero]
    simpa only [octConj_conj, hz] using h
  exact ⟨h01', h02, h12⟩
include x in

/-- Diagonalization in the genuine native product/trace automorphism group. -/
theorem native_diagonalization  :
    ∃ g : CompactAutomorphism, IsDiagonal (g.equiv x) := by
  obtain ⟨g, hg⟩ := exists_diagonalEnergy_maximum x
  refine ⟨g, maximalDiagonalEnergy_isDiagonal _ ?_⟩
  intro h
  exact hg (h.comp g)

end
end Glennie
