/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Plane.IntegralAffineLine
public import CCDN.Surface.TransversePlane
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.Plane.Bezout
import CCDN.Surface.DirectionalDerivative
import CCDN.Surface.TopFormBadPrimes

/-! A transverse plane injects distinct parallel lines on a surface into
the common zeros of two proper plane equations. The second equation will
be the directional derivative. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A surface with absolutely irreducible top form has at most d(d-1)
distinct lines in any prescribed nonzero rational direction. The directional
derivative and the transverse plane are constructed inside the proof. -/
theorem surface_parallel_lines_card_le
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : HasAbsIrreducibleTopForm f)
    (hd : 2 ≤ f.totalDegree)
    (v : RatPoint 3) (hv : v ≠ 0)
    (S : Finset (Set (RatPoint 3)))
    (hlines : ∀ L ∈ S, ∃ a, L = rationalAffineLine a v)
    (hSf : ∀ L ∈ S, L ⊆ zeroLocus (map (Int.castRingHom ℚ) f)) :
    S.card ≤ f.totalDegree * (f.totalDegree - 1) := by
  classical
  let g := directionalDerivative v (map (Int.castRingHom ℚ) f)
  have hg : g ≠ 0 := surface_directionalDerivative_ne_zero f hir hd v hv
  have hgdeg : g.totalDegree ≤ f.totalDegree - 1 := by
    simpa only [rational_map_totalDegree] using
      directionalDerivative_totalDegree_le v (map (Int.castRingHom ℚ) f)
  obtain ⟨a, b, c, hdet, hF, hFd, hG⟩ := exists_surface_transverse_plane f
    (absolute_irreducible_of_top_homogeneousComponent_irreducible f hir)
    (by omega) v hv g hg
  choose x hx using fun L : S => hlines L.val L.property
  have hunit : IsUnit (planeDirectionMatrix b c v) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hex (L : S) : ∃ (z : Fin 2 → ℚ) (t : ℚ),
      (fun i => a i + b i * z 0 + c i * z 1) = x L + t • v := by
    obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hunit (x L - a)
    refine ⟨![w 0, w 1], -w 2, funext fun i => ?_⟩
    have hi := congrFun hw i
    have hmul : (planeDirectionMatrix b c v).mulVec w i = b i * w 0 + c i * w 1 + v i * w 2 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, planeDirectionMatrix]; ring
    rw [hmul, Pi.sub_apply] at hi
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  choose z t hzt using hex
  have hz : Function.Injective z := fun L M he => Subtype.ext <| by
    rw [hx L, hx M, ← rationalAffineLine_shift_base (x L) v (t L),
      ← rationalAffineLine_shift_base (x M) v (t M), ← hzt L, ← hzt M, he]
  have hFG : ¬ affinePlaneMap a b c (map (Int.castRingHom ℚ) f) ∣ affinePlaneMap a b c g := by
    rintro ⟨q, hq⟩
    have hq0 : q ≠ 0 := fun hz => hG (by rw [hq, hz, mul_zero])
    have hh : f.totalDegree ≤ (affinePlaneMap a b c g).totalDegree := by
      rw [hq, totalDegree_mul_of_isDomain hF.ne_zero hq0, hFd]; omega
    have := hh.trans ((affinePlaneMap_totalDegree_le a b c g).trans hgdeg)
    omega
  have hcount := plane_common_zeros_card_le
    (affinePlaneMap a b c (map (Int.castRingHom ℚ) f)) (affinePlaneMap a b c g)
    hF hFG z hz
    (fun L => by rw [affinePlaneMap_eval, hzt L]; exact hSf L.val L.property (by rw [hx L]; exact ⟨t L, rfl⟩))
    (fun L => by
      rw [affinePlaneMap_eval, hzt L]
      exact rationalAffineLine_contained_directionalDerivative (x L) v
        (map (Int.castRingHom ℚ) f) (hx L ▸ hSf L.val L.property) ⟨t L, rfl⟩)
  rw [Fintype.card_coe, hFd] at hcount
  exact hcount.trans (Nat.mul_le_mul_left _ ((affinePlaneMap_totalDegree_le a b c g).trans hgdeg))

end
end CCDN
