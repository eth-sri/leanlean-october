module

public import HypoellipticAleksandrov.Measure.IntervalUnion
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Linarith
import all HypoellipticAleksandrov.Measure.InkSpotsWind

open private HypoellipticAleksandrov.Parabolic.isOpen_ordConnected_eq_Ioo_csInf_csSup from HypoellipticAleksandrov.Measure.InkSpotsWind


/-!
# Boundary-shifted midpoint enlargements

This file implements the one-dimensional enlargement used when the centres of
the intervals vary.  Each interval is expanded about its own endpoint
midpoint, and an expansion meeting the boundary of `(-1, 1)` is translated
flush to that boundary before being clipped.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set


namespace HypoellipticAleksandrov.Parabolic

/-- Endpoint length of a real interval; used only with an eligible open
subinterval in the public lemmas below. -/
def intervalEndpointLength (J : Set Real) : Real := sSup J - sInf J

/-- Midpoint determined by interval endpoints. -/
def intervalEndpointMidpoint (J : Set Real) : Real := (sInf J + sSup J) / 2

/-- Krylov--Safonov, Lemma 2.4 expansion: expand about `J`'s own midpoint, shift a
crossing expansion flush to the appropriate boundary, then clip to `(-1,1)`. -/
def boundaryShiftedMidpointExpansion (kappa : Real) (J : Set Real) : Set Real :=
  Ioo
    (max (-1 : Real)
      (min (1 - kappa * intervalEndpointLength J)
        (intervalEndpointMidpoint J - kappa * intervalEndpointLength J / 2)))
    (min 1
      (max (-1 + kappa * intervalEndpointLength J)
        (intervalEndpointMidpoint J + kappa * intervalEndpointLength J / 2)))




private theorem open_subinterval_endpoint_data {J : Set Real}
    (hJ : IsOpenSubinterval (Ioo (-1 : Real) 1) J) :
    BddBelow J ∧ BddAbove J ∧ J = Ioo (sInf J) (sSup J) ∧
      (-1 : Real) ≤ sInf J ∧ sInf J < sSup J ∧ sSup J ≤ 1 := by
  have hbelow : BddBelow J :=
    ⟨-1, fun x hx => (hJ.2.2.2 hx).1.le⟩
  have habove : BddAbove J :=
    ⟨1, fun x hx => (hJ.2.2.2 hx).2.le⟩
  have heq  :=
    _root_.HypoellipticAleksandrov.Parabolic.isOpen_ordConnected_eq_Ioo_csInf_csSup J hJ.2.1 hJ.2.2.1 hJ.1 hbelow habove



  exact ⟨hbelow, habove, heq, (by
      apply le_csInf hJ.1
      intro x hx
      exact (hJ.2.2.2 hx).1.le), (by
      obtain ⟨x, hx⟩ := hJ.1
      rw [heq] at hx
      exact hx.1.trans hx.2), (by
      apply csSup_le hJ.1
      intro x hx
      exact (hJ.2.2.2 hx).2.le)⟩

variable {kappa a b : Real}

section
variable (hkappa : 1 < kappa)

section
variable (hab : a < b)

include hkappa hab
private theorem midpoint_left_lt_left
      :
    (a + b) / 2 - kappa * (b - a) / 2 < a := by
  nlinarith

private theorem right_lt_midpoint_right
      :
    b < (a + b) / 2 + kappa * (b - a) / 2 := by
  nlinarith
end


include hkappa in
private theorem boundary_shifted_endpoints_strict
     (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    max (-1 : Real)
        (min (1 - kappa * (b - a)) ((a + b) / 2 - kappa * (b - a) / 2)) <
      min 1
        (max (-1 + kappa * (b - a)) ((a + b) / 2 + kappa * (b - a) / 2)) := (lt_of_le_of_lt
  (max_le ha
    (LE.le.trans (min_le_right (1 - kappa * (b - a)) ((a + b) / 2 - kappa * (b - a) / 2))
      (LT.lt.le (midpoint_left_lt_left hkappa hab))))
  (lt_of_lt_of_le hab
    (le_min hb
      (LE.le.trans (LT.lt.le (right_lt_midpoint_right hkappa hab))
        (le_max_right (-1 + kappa * (b - a)) ((a + b) / 2 + kappa * (b - a) / 2))))))
end


private theorem boundary_shifted_length_le
    (_hkappa : 1 < kappa) (_ha : -1 ≤ a) (_hab : a < b) (_hb : b ≤ 1) :
    min 1
        (max (-1 + kappa * (b - a)) ((a + b) / 2 + kappa * (b - a) / 2)) -
      max (-1 : Real)
        (min (1 - kappa * (b - a)) ((a + b) / 2 - kappa * (b - a) / 2)) ≤
        kappa * (b - a) := by
  let sharedTerm_96018a8e7c := ((-1 + kappa * (b - a)))
  let L := (a + b) / 2 - kappa * (b - a) / 2
  let R := (a + b) / 2 + kappa * (b - a) / 2
  have hLR : R = L + kappa * (b - a) := by
    dsimp only [L, R]
    ring
  by_cases hL : L ≤ 1 - kappa * (b - a)
  · rw [min_eq_right hL]
    by_cases hLminus : L ≤ -1
    · rw [max_eq_left hLminus]

      rw [max_eq_left (show R ≤ sharedTerm_96018a8e7c by linarith)]
      have hupper : min 1 sharedTerm_96018a8e7c ≤ sharedTerm_96018a8e7c :=
        min_le_right _ _
      linarith
    · grind
  · rw [min_eq_left (le_of_not_ge hL)]
    by_cases hk : kappa * (b - a) ≤ 2
    · grind
    · grind

/-- The boundary-shifted midpoint expansion is again an eligible interval. -/
theorem isOpenSubinterval_boundaryShiftedMidpointExpansion
    (kappa : Real) (hkappa : 1 < kappa) {J : Set Real}
    (hJ : IsOpenSubinterval (Ioo (-1 : Real) 1) J) :
    IsOpenSubinterval (Ioo (-1 : Real) 1)
      (boundaryShiftedMidpointExpansion kappa J) := by
  rcases open_subinterval_endpoint_data hJ with ⟨_, _, heq, hlow, hlt, hupp⟩
  unfold boundaryShiftedMidpointExpansion intervalEndpointLength intervalEndpointMidpoint
  refine ⟨?_, isOpen_Ioo, ordConnected_Ioo, Ioo_subset_Ioo ?_ ?_⟩
  · rw [heq]
    simpa only [csInf_Ioo hlt, csSup_Ioo hlt] using
      nonempty_Ioo.mpr (boundary_shifted_endpoints_strict hkappa hlow hlt hupp)
  · exact le_max_left _ _
  · exact min_le_left _ _

private theorem endpoint_mono_of_subset {J₁ J₂ : Set Real}
    (hJ₁ : IsOpenSubinterval (Ioo (-1 : Real) 1) J₁)
    (hJ₂ : IsOpenSubinterval (Ioo (-1 : Real) 1) J₂)
    (hsubset : J₁ ⊆ J₂) :
    sInf J₂ ≤ sInf J₁ ∧ sSup J₁ ≤ sSup J₂ := by
  rcases open_subinterval_endpoint_data hJ₁ with ⟨_, hJ₁above, _, _, _, _⟩
  rcases open_subinterval_endpoint_data hJ₂ with ⟨hJ₂below, hJ₂above, _, _, _, _⟩
  constructor
  · apply le_csInf hJ₁.1
    intro x hx
    exact csInf_le hJ₂below (hsubset hx)
  · apply (csSup_le_iff hJ₁above hJ₁.1).2
    intro x hx
    exact le_csSup hJ₂above (hsubset hx)

private theorem midpoint_expansion_mono_of_endpoints {kappa a₁ b₁ a₂ b₂ : Real}
    (hkappa : 1 < kappa) (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
    max (-1 : Real)
        (min (1 - kappa * (b₂ - a₂)) ((a₂ + b₂) / 2 - kappa * (b₂ - a₂) / 2)) ≤
      max (-1 : Real)
        (min (1 - kappa * (b₁ - a₁)) ((a₁ + b₁) / 2 - kappa * (b₁ - a₁) / 2)) ∧
    min 1
        (max (-1 + kappa * (b₁ - a₁)) ((a₁ + b₁) / 2 + kappa * (b₁ - a₁) / 2)) ≤
      min 1
        (max (-1 + kappa * (b₂ - a₂)) ((a₂ + b₂) / 2 + kappa * (b₂ - a₂) / 2)) := by

  have hlen : b₁ - a₁ ≤ b₂ - a₂ := by linarith


  constructor
  · apply max_le_max_left
    apply min_le_min
    · gcongr
    · exact (by
        have hda  := sub_nonneg.mpr ha
        have hdb  := sub_nonneg.mpr hb
        have hka : 0 ≤ (kappa + 1) * (a₁ - a₂) :=
          mul_nonneg (by linarith) hda
        have hkb  :=
          mul_nonneg (sub_nonneg.mpr hkappa.le) hdb
        nlinarith)
  · apply min_le_min_left
    apply max_le_max
    · gcongr
    · exact (by
        have hda  := sub_nonneg.mpr ha
        have hdb  := sub_nonneg.mpr hb
        have hka  :=
          mul_nonneg (sub_nonneg.mpr hkappa.le) hda
        have hkb : 0 ≤ (kappa + 1) * (b₂ - b₁) :=
          mul_nonneg (by linarith) hdb
        nlinarith)

section
variable (kappa : Real) (hkappa : 1 < kappa)

include hkappa
/-- Boundary-shifted midpoint expansion is monotone even when the two
intervals encounter different boundary cases. -/
theorem boundaryShiftedMidpointExpansion_mono_of_subset
     {J₁ J₂ : Set Real}
    (hJ₁ : IsOpenSubinterval (Ioo (-1 : Real) 1) J₁)
    (hJ₂ : IsOpenSubinterval (Ioo (-1 : Real) 1) J₂)
    (hsubset : J₁ ⊆ J₂) :
    boundaryShiftedMidpointExpansion kappa J₁ ⊆
      boundaryShiftedMidpointExpansion kappa J₂ := by
  rcases endpoint_mono_of_subset hJ₁ hJ₂ hsubset with ⟨hinf, hsup⟩
  rcases open_subinterval_endpoint_data hJ₁ with ⟨_, _, heq₁, _, hlt₁, _⟩
  rcases open_subinterval_endpoint_data hJ₂ with ⟨_, _, heq₂, _, hlt₂, _⟩
  unfold boundaryShiftedMidpointExpansion intervalEndpointLength intervalEndpointMidpoint
  rw [heq₁, heq₂, csInf_Ioo hlt₁, csSup_Ioo hlt₁, csInf_Ioo hlt₂,
    csSup_Ioo hlt₂]
  exact Ioo_subset_Ioo (midpoint_expansion_mono_of_endpoints hkappa hinf hsup).1
    (midpoint_expansion_mono_of_endpoints hkappa hinf hsup).2

/-- The boundary-shifted expansion has at most the sharp local `kappa`
volume factor. -/
theorem volume_boundaryShiftedMidpointExpansion_le
     {J : Set Real}
    (hJ : IsOpenSubinterval (Ioo (-1 : Real) 1) J) :
    volume (boundaryShiftedMidpointExpansion kappa J) ≤
      ENNReal.ofReal kappa * volume J := by
  rcases open_subinterval_endpoint_data hJ with ⟨_, _, heq, hlow, hlt, hupp⟩


  rw [boundaryShiftedMidpointExpansion, intervalEndpointLength,
    intervalEndpointMidpoint, heq, csInf_Ioo hlt, csSup_Ioo hlt,
    Real.volume_Ioo, Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (le_trans zero_le_one hkappa.le)]
  apply ENNReal.ofReal_le_ofReal
  exact (boundary_shifted_length_le hkappa hlow hlt hupp)

/-- Sharp uncountable-family estimate for varying-centre expansions. -/
theorem volume_sUnion_boundaryShiftedMidpointExpansion
     (B : Set (Set Real))
    (hB : ∀ J ∈ B, IsOpenSubinterval (Ioo (-1 : Real) 1) J) :
    volume (⋃₀ (boundaryShiftedMidpointExpansion kappa '' B)) ≤
      ENNReal.ofReal kappa * volume (⋃₀ B) := by
  apply volume_sUnion_monotone_interval_enlargement_Ioo_of_le kappa hkappa (-1) 1
    (by norm_num) B (boundaryShiftedMidpointExpansion kappa)
  · exact hB
  · simp_all [isOpenSubinterval_boundaryShiftedMidpointExpansion]
  · simp_all [volume_boundaryShiftedMidpointExpansion_le]
  · simp_all [boundaryShiftedMidpointExpansion_mono_of_subset]
end


private theorem interval_inter_reference_eq {a b : Real} :
    Ioo a b ∩ Ioo (-1 : Real) 1 = Ioo (max (-1 : Real) a) (min 1 b) := by
  grind

private theorem boundary_shifted_affine_image_formula
    (c zeta l u : Real) (hzeta0 : 0 < zeta) (_hl : -1 ≤ l) (_hu : u ≤ 1)
    (hlu : l < u) :
    boundaryShiftedMidpointExpansion zeta⁻¹
        ((fun x  => c + zeta * (x - c)) '' Ioo l u) =
      Ioo
        (max (-1 : Real)
          (min (1 - (u - l))
            (c + zeta * ((l + u) / 2 - c) - (u - l) / 2)))
        (min 1
          (max (-1 + (u - l))
            (c + zeta * ((l + u) / 2 - c) + (u - l) / 2))) := by
  let sharedTerm_1a22cd08dd := (zeta * u + (1 - zeta) * c)
  let sharedTerm_3a51062cd7 := (zeta * l + (1 - zeta) * c)
  have hcontracted : sharedTerm_3a51062cd7 < sharedTerm_1a22cd08dd := by
    have hmul  := mul_pos hzeta0 (sub_pos.mpr hlu)
    nlinarith
  unfold boundaryShiftedMidpointExpansion intervalEndpointLength intervalEndpointMidpoint
  rw [show (fun x  => c + zeta * (x - c)) =
      fun x => zeta * x + (1 - zeta) * c by
        funext x
        ring,
    image_affine_Ioo hzeta0, csInf_Ioo hcontracted, csSup_Ioo hcontracted]
  have hmid :
      (sharedTerm_3a51062cd7 + (sharedTerm_1a22cd08dd)) / 2 =
        c + zeta * ((l + u) / 2 - c) := by
    ring
  have hlength : zeta⁻¹ * ((sharedTerm_1a22cd08dd) -
      (sharedTerm_3a51062cd7)) = u - l := by
    field_simp [ne_of_gt hzeta0]
    ring
  rw [hmid, hlength]

/-- Exact source recovery for the contraction of a clipped centred interval.
The four possible clipping cases are split explicitly; after clipping, the
midpoint expansion recovers the same endpoint interval in each case. -/
theorem boundaryShiftedMidpointExpansion_image_centeredInterval_inter
    (c r zeta : Real) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hc : c ∈ Ioo (-1 : Real) 1) (hr : 0 < r) :
    boundaryShiftedMidpointExpansion zeta⁻¹
        ((fun x  => c + zeta * (x - c)) ''
          (Ioo (c - r) (c + r) ∩ Ioo (-1 : Real) 1)) =
      Ioo (c - r) (c + r) ∩ Ioo (-1 : Real) 1 := by
  let sharedTerm_54ecdf1b2f := ((c + r) - (-1))
  let sharedTerm_16732a3af6 := ((c + r) - (c - r))

  rw [interval_inter_reference_eq]


  by_cases hleft : c - r < -1
  · by_cases hright : 1 < c + r
    · rw [max_eq_left hleft.le, min_eq_left hright.le]
      rw [boundary_shifted_affine_image_formula c zeta (-1) 1 hzeta0 le_rfl le_rfl
        (by norm_num)]
      have hmin : (1 : Real) - (1 - (-1)) = -1 := by norm_num
      have hmax : (-1 : Real) + (1 - (-1)) = 1 := by norm_num
      rw [hmin, hmax, max_eq_left (min_le_left _ _),
        min_eq_left (le_max_left _ _)]
    · rw [max_eq_left hleft.le, min_eq_right (le_of_not_gt hright)]
      rw [boundary_shifted_affine_image_formula c zeta (-1) (c + r) hzeta0 le_rfl
        (le_of_not_gt hright) (by linarith [hc.1, hr])]



      have hR : c + zeta * ((-1 + (c + r)) / 2 - c) +
          (sharedTerm_54ecdf1b2f) / 2 ≤ c + r := by nlinarith
      have hK : -1 + (sharedTerm_54ecdf1b2f) = c + r := by ring
      rw [min_eq_right (by nlinarith), max_eq_left (by nlinarith), hK, max_eq_left hR,
        min_eq_right (le_of_not_gt hright)]
  · by_cases hright : 1 < c + r
    · rw [max_eq_right (le_of_not_gt hleft), min_eq_left hright.le]
      rw [boundary_shifted_affine_image_formula c zeta (c - r) 1 hzeta0
        (le_of_not_gt hleft) le_rfl (by linarith [hc.2, hr])]


      have hR : 1 ≤ c + zeta * (((c - r) + 1) / 2 - c) +
          (1 - (c - r)) / 2 := by nlinarith
      have hK : 1 - (1 - (c - r)) = c - r := by ring

      rw [hK, min_eq_left (by nlinarith), max_eq_right (le_of_not_gt hleft),
        max_eq_right ((show -1 + (1 - (c - r)) ≤ 1 by linarith).trans hR), min_eq_left hR]
    · rw [max_eq_right (le_of_not_gt hleft), min_eq_right (le_of_not_gt hright)]
      rw [boundary_shifted_affine_image_formula c zeta (c - r) (c + r) hzeta0
        (le_of_not_gt hleft) (le_of_not_gt hright) (by linarith)]
      have hmid : c + zeta * (((c - r) + (c + r)) / 2 - c) = c := by ring
      rw [hmid]
      have hrawL : c - (sharedTerm_16732a3af6) / 2 = c - r := by ring
      have hrawR : c + (sharedTerm_16732a3af6) / 2 = c + r := by ring
      rw [hrawL, hrawR]


      rw [min_eq_right (by linarith), max_eq_right (le_of_not_gt hleft),
        max_eq_right (by linarith), min_eq_right (le_of_not_gt hright)]

end HypoellipticAleksandrov.Parabolic
