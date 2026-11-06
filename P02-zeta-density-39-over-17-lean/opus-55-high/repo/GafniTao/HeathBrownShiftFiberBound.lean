module
public import GafniTao.HeathBrownSpacingRealBound
import WeylPort.Analytic.RealLaplace

public section

/-!
# Quantitative bound for one positive shift

This is the exact real-valued consequence of the spacing lemma for a fixed
`d`.  It keeps all factorials, endpoint rounding losses, and the natural
truncation `N-d` visible.
-/

namespace GafniTao


theorem heathBrownPositiveShiftFiber_card_cast_le_raw
    {N k H K d : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N - d) (hd : 1 ≤ d) (hdN : d ≤ N)
    (hA : 0 ≤ A) (hlambda : 0 < lambda)
    (hcoord : ContinuousOn
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Icc 0 (N : ℝ)))
    (hcoordd : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Ioo 0 (N : ℝ)))
    (hraw : ContinuousOn (iteratedDeriv (k - 1) f)
      (Set.Icc 0 (N : ℝ)))
    (hrawd : DifferentiableOn ℝ (iteratedDeriv (k - 1) f)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda) :
    ((heathBrownPositiveShiftFiber N k H K f d).card : ℝ) ≤
      (2 * (4 * (((H : ℝ) ^ (k - 2))⁻¹)) /
            (lambda * d / ((k - 2).factorial : ℝ)) + 1) *
        ((A * lambda * d / ((k - 2).factorial : ℝ)) * (N - d : ℕ) +
          2 * (4 * (((H : ℝ) ^ (k - 2))⁻¹)) + 3) := by
  let g := heathBrownShiftedDifference f (k - 2) d
  pm_5786 theta
  let mu : ℝ := lambda * d / ((k - 2).factorial : ℝ)
  let M : ℝ := A * lambda * d / ((k - 2).factorial : ℝ)
  pm_64 hmu mu
  pm_61 htheta theta
  pm_2825
  have hg := heathBrown_shiftedDifference_continuousOn hdN hcoord
  have hgd := heathBrown_shiftedDifference_differentiableOn hdN hcoordd
  have hbounds := heathBrown_shiftedDifference_deriv_bounds
    (by omega : 2 ≤ k) hdN hraw hrawd hcoordd hkBounds
  have hspacing := heathBrown_spacing_card_cast_le hN hmu htheta hM
    hg hgd (fun x hx => (hbounds x hx).1) (fun x hx => (hbounds x hx).2)
  have hfiber :
      ((heathBrownPositiveShiftFiber N k H K f d).card : ℝ) ≤
        ((heathBrownSpacingSet (N - d) g theta).card : ℝ) := by
    have hnat := heathBrownPositiveShiftFiber_card_le_spacingSet
      (N := N) (k := k) (H := H) (K := K) (d := d) (f := f)
    have hcast : ((heathBrownPositiveShiftFiber N k H K f d).card : ℝ) ≤
        ((heathBrownSpacingSet (N - d)
          (heathBrownShiftedDifference f (k - 2) d)
          (4 * (((H : ℝ) ^ (k - 2))⁻¹))).card : ℝ) := by
      exact_mod_cast hnat
    grind
  grind

theorem heathBrownPositiveShiftFiber_card_cast_le_harmonic
    {N k H K D d : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N - d) (hd : 1 ≤ d) (hdN : d ≤ N)
    (hdD : d ≤ D) (hA : 0 ≤ A) (hlambda : 0 < lambda)
    (hcoord : ContinuousOn
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Icc 0 (N : ℝ)))
    (hcoordd : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Ioo 0 (N : ℝ)))
    (hraw : ContinuousOn (iteratedDeriv (k - 1) f)
      (Set.Icc 0 (N : ℝ)))
    (hrawd : DifferentiableOn ℝ (iteratedDeriv (k - 1) f)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda) :
    let c := 8 * ((k - 2).factorial : ℝ) *
      (((H : ℝ) ^ (k - 2))⁻¹) / lambda
    let b := 8 * (((H : ℝ) ^ (k - 2))⁻¹) + 3
    let a := A * lambda * N / ((k - 2).factorial : ℝ)
    ((heathBrownPositiveShiftFiber N k H K f d).card : ℝ) ≤
      ((D : ℝ) + c) * (b + a * D) / d := by
  dsimp only
  have hrawBound := heathBrownPositiveShiftFiber_card_cast_le_raw
    (H := H) (K := K) hk hN hd hdN hA hlambda hcoord hcoordd
    hraw hrawd hkBounds
  let u : ℝ := (((H : ℝ) ^ (k - 2))⁻¹)
  let fac : ℝ := ((k - 2).factorial : ℝ)
  let c : ℝ := 8 * fac * u / lambda
  let b : ℝ := 8 * u + 3
  let a : ℝ := A * lambda * N / fac
  pm_64 hfac fac
  pm_456 hdR d hd
  pm_106 hDR d D hdD
  pm_61 hu u
  pm_61 hc c
  pm_61 hb b
  pm_61 ha a
  have hNd : ((N - d : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N d
  have hsecond :
      (A * lambda * (d : ℝ) / fac) * ((N - d : ℕ) : ℝ) + 8 * u + 3 ≤
        b + a * d := by
    dsimp [a, b]
    have hcoef : 0 ≤ A * lambda * (d : ℝ) / fac := by positivity
    calc
      (A * lambda * (d : ℝ) / fac) * ((N - d : ℕ) : ℝ) + 8 * u + 3 ≤
          (A * lambda * (d : ℝ) / fac) * (N : ℝ) + 8 * u + 3 := by
        gcongr
      _ = 8 * u + 3 + (A * lambda * (N : ℝ) / fac) * d := by ring
  have hfirst :
      2 * (4 * u) / (lambda * (d : ℝ) / fac) + 1 =
        ((d : ℝ) + c) / d := by
    dsimp [c]
    field_simp
    ring
  rw [show (((H : ℝ) ^ (k - 2))⁻¹) = u by rfl] at hrawBound
  rw [show ((k - 2).factorial : ℝ) = fac by rfl] at hrawBound
  rw [hfirst] at hrawBound
  have htwoFour : 2 * (4 * u) = 8 * u := by ring
  rw [htwoFour] at hrawBound
  have hfactorNonneg : 0 ≤ ((d : ℝ) + c) / d := by positivity
  have hmiddle :
      ((d : ℝ) + c) / d *
          ((A * lambda * (d : ℝ) / fac) * ((N - d : ℕ) : ℝ) + 8 * u + 3) ≤
        ((d : ℝ) + c) / d * (b + a * d) :=
    mul_le_mul_of_nonneg_left hsecond hfactorNonneg
  have hthird :
      ((d : ℝ) + c) / d * (b + a * d) ≤
        ((D : ℝ) + c) / d * (b + a * D) := by
    have hleft : ((d : ℝ) + c) / d ≤ ((D : ℝ) + c) / d := by
      exact div_le_div_of_nonneg_right
        (by simpa only [add_comm] using add_le_add_right hDR c) hdR.le
    have hright : b + a * (d : ℝ) ≤ b + a * D := by
      simpa only [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_left hDR ha) b
    pm_149 hleft hright
  calc
    ((heathBrownPositiveShiftFiber N k H K f d).card : ℝ) ≤
        ((d : ℝ) + c) / d *
          ((A * lambda * (d : ℝ) / fac) * ((N - d : ℕ) : ℝ) + 8 * u + 3) :=
      hrawBound
    _ ≤ ((d : ℝ) + c) / d * (b + a * d) := hmiddle
    _ ≤ ((D : ℝ) + c) / d * (b + a * D) := hthird
    _ = ((D : ℝ) + c) * (b + a * D) / d := by ring



end GafniTao
