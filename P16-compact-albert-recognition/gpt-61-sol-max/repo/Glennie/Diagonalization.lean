/- Native compact diagonalization from actual automorphisms and a maximum.
No compact spectral theorem is an assumption of this proof. -/
module
public import Glennie.Compactness
public import Mathlib.Analysis.Real.Sqrt
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
  let D := Real.sqrt ((x.d1-x.d2)^2+4*n^2)
  have hrad : 0 < (x.d1-x.d2)^2+4*n^2 := by nlinarith [sq_nonneg (x.d1-x.d2)]
  have hD         := Real.sqrt_pos.mpr hrad
  have hD2                       := Real.sq_sqrt (le_of_lt hrad)
  have hp : 0 < D+(x.d1-x.d2) := by nlinarith
  have hm : 0 < D-(x.d1-x.d2) := by nlinarith
  let c := Real.sqrt ((D+(x.d1-x.d2))/(2*D))
  let s := Real.sqrt ((D-(x.d1-x.d2))/(2*D))


  have hc2 : 2*D*c^2 = D+(x.d1-x.d2) := by
    dsimp [c]
    rw [Real.sq_sqrt (by positivity), mul_div_cancel₀ _ (by positivity)]
  have hs2 : 2*D*s^2 = D-(x.d1-x.d2) := by
    dsimp [s]
    rw [Real.sq_sqrt (by positivity), mul_div_cancel₀ _ (by positivity)]
  have hcsNorm : c^2+s^2=1 := by grind
  have hprod : (2*D*c*s)^2 = (2*n)^2 := by grind
  have hcsProd : 2*D*c*s = 2*n := by
    have hnonneg : 0 ≤ 2*D*c*s := by positivity
    nlinarith [hprod]
  have he : (c^2*x.d1+s^2*x.d2+2*c*s*n)^2 +
      (s^2*x.d1+c^2*x.d2-2*c*s*n)^2 = x.d1^2+x.d2^2+2*n^2 := by
    grind only
  have hmax := hx ((realRotation12Automorphism c s hcsNorm).comp g)
  change diagonalEnergy (realConjugateAlbert (realRotation12 c s) (g.equiv x)) ≤
    diagonalEnergy x at hmax
  unfold diagonalEnergy at hmax
  rw [realRotation12_d0, realRotation12_d1, realRotation12_d2,
    h0, h1, h2, hslot, octRe_scalar] at hmax
  nlinarith [he]

theorem realSwap01_diagonalEnergy (x : Albert) :
    diagonalEnergy (realSwap01Automorphism.equiv x) = diagonalEnergy x := by
  change diagonalEnergy (realConjugateAlbert realSwap01 x) = _
  rw [realSwap01_coordinates]
  simp only [diagonalEnergy]
  ring

theorem realSwap02_diagonalEnergy (x : Albert) :
    diagonalEnergy (realSwap02Automorphism.equiv x) = diagonalEnergy x := by
  change diagonalEnergy (realConjugateAlbert realSwap02 x) = _
  rw [realSwap02_coordinates]
  simp only [diagonalEnergy]
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
      simp only [star_zero, neg_zero]
    simpa only [octConj_conj, hz] using h
  exact ⟨h01', h02, h12⟩

/-- Diagonalization in the genuine native product/trace automorphism group. -/
theorem native_diagonalization (x : Albert) :
    ∃ g : CompactAutomorphism, IsDiagonal (g.equiv x) := by
  obtain ⟨g, hg⟩ := exists_diagonalEnergy_maximum x
  refine ⟨g, maximalDiagonalEnergy_isDiagonal _ ?_⟩
  intro h
  exact hg (h.comp g)

end
end Glennie
