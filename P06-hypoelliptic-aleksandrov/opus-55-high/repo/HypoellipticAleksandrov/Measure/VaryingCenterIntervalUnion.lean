module

public import HypoellipticAleksandrov.Measure.IntervalUnion

/-!
# Boundary-shifted midpoint enlargements

This file implements the one-dimensional enlargement used when the centres of
the intervals vary.  Each interval is expanded about its own endpoint
midpoint, and an expansion meeting the boundary of `(-1, 1)` is translated
flush to that boundary before being clipped.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal Topology

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

private theorem open_ordConnected_eq_Ioo_csInf_csSup (J : Set Real)
    (hJopen : IsOpen J) (hJord : J.OrdConnected) (hJnonempty : J.Nonempty)
    (hJbelow : BddBelow J) (hJabove : BddAbove J) :
    J = Ioo (sInf J) (sSup J) := by
  apply Subset.antisymm
  · intro x hx
    have hinf : sInf J ≤ x := csInf_le hJbelow hx
    have hsup : x ≤ sSup J := le_csSup hJabove hx
    constructor
    · by_contra hnot
      rcases Metric.mem_nhds_iff.1 (hJopen.mem_nhds hx) with ⟨eps, heps, hball⟩
      have hleft : x - eps / 2 ∈ J := hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        grind)
      have hle : sInf J ≤ x - eps / 2 := csInf_le hJbelow hleft
      linarith
    · by_contra hnot
      rcases Metric.mem_nhds_iff.1 (hJopen.mem_nhds hx) with ⟨eps, heps, hball⟩
      have hright : x + eps / 2 ∈ J := hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        grind)
      have hle : x + eps / 2 ≤ sSup J := le_csSup hJabove hright
      linarith
  · exact IsConnected.Ioo_csInf_csSup_subset
      ⟨hJnonempty, hJord.isPreconnected⟩ hJbelow hJabove

private theorem open_subinterval_endpoint_data {J : Set Real}
    (hJ : IsOpenSubinterval (Ioo (-1 : Real) 1) J) :
    BddBelow J ∧ BddAbove J ∧ J = Ioo (sInf J) (sSup J) ∧
      (-1 : Real) ≤ sInf J ∧ sInf J < sSup J ∧ sSup J ≤ 1 := by
  have hbelow : BddBelow J :=
    ⟨-1, fun x hx => (hJ.2.2.2 hx).1.le⟩
  have habove : BddAbove J :=
    ⟨1, fun x hx => (hJ.2.2.2 hx).2.le⟩
  have heq  :=
    open_ordConnected_eq_Ioo_csInf_csSup J hJ.2.1 hJ.2.2.1 hJ.1 hbelow habove
  have hlow : (-1) ≤ sInf J := by
    apply le_csInf hJ.1
    intro x hx
    exact (hJ.2.2.2 hx).1.le
  have hupp : sSup J ≤ 1 := by
    apply csSup_le hJ.1
    intro x hx
    exact (hJ.2.2.2 hx).2.le
  have hlt : sInf J < sSup J := by
    obtain ⟨x, hx⟩ := hJ.1
    grind
  grind

variable {kappa a b : Real}

private theorem midpoint_left_lt_left 
    (hkappa : 1 < kappa) (hab : a < b) :
    (a + b) / 2 - kappa * (b - a) / 2 < a := by
  nlinarith

private theorem boundary_shifted_endpoints_strict 
    (hkappa : 1 < kappa) (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    max (-1 : Real)
        (min (1 - kappa * (b - a)) ((a + b) / 2 - kappa * (b - a) / 2)) <
      min 1
        (max (-1 + kappa * (b - a)) ((a + b) / 2 + kappa * (b - a) / 2)) := by
  have hleft : max (-1)
      (min (1 - kappa * (b - a)) ((a + b) / 2 - kappa * (b - a) / 2)) ≤ a := by
    apply max_le
    · exact ha
    · exact (min_le_right _ _).trans (midpoint_left_lt_left hkappa hab).le
  grind

private theorem boundary_shifted_length_le 
    (_hkappa : 1 < kappa) (_ha : -1 ≤ a) (_hab : a < b) (_hb : b ≤ 1) :
    min 1
        (max (-1 + kappa * (b - a)) ((a + b) / 2 + kappa * (b - a) / 2)) -
      max (-1 : Real)
        (min (1 - kappa * (b - a)) ((a + b) / 2 - kappa * (b - a) / 2)) ≤
        kappa * (b - a) := by
  let L := (a + b) / 2 - kappa * (b - a) / 2
  let R := (a + b) / 2 + kappa * (b - a) / 2
  have hLR : R = L + kappa * (b - a) := by
    ring
  by_cases hL : L ≤ 1 - kappa * (b - a)
  · grind
  grind

/-- The boundary-shifted midpoint expansion is again an eligible interval. -/
theorem isOpenSubinterval_boundaryShiftedMidpointExpansion
    (kappa : Real) (hkappa : 1 < kappa) {J : Set Real}
    (hJ : IsOpenSubinterval (Ioo (-1 : Real) 1) J) :
    IsOpenSubinterval (Ioo (-1 : Real) 1)
      (boundaryShiftedMidpointExpansion kappa J) := by
  rcases open_subinterval_endpoint_data hJ with ⟨_, _, heq, hlow, hlt, hupp⟩
  unfold boundaryShiftedMidpointExpansion intervalEndpointLength intervalEndpointMidpoint
  refine ⟨?_, isOpen_Ioo, ordConnected_Ioo, Ioo_subset_Ioo ?_ ?_⟩
  · simpa using
      nonempty_Ioo.mpr (boundary_shifted_endpoints_strict hkappa hlow hlt hupp)
  · simp
  simp

private theorem endpoint_mono_of_subset {J₁ J₂ : Set Real}
    (hJ₁ : IsOpenSubinterval (Ioo (-1 : Real) 1) J₁)
    (hJ₂ : IsOpenSubinterval (Ioo (-1 : Real) 1) J₂)
    (hsubset : J₁ ⊆ J₂) :
    sInf J₂ ≤ sInf J₁ ∧ sSup J₁ ≤ sSup J₂ := by
  rcases open_subinterval_endpoint_data hJ₁ with ⟨_, hJ₁above, _, _, _, _⟩
  rcases open_subinterval_endpoint_data hJ₂ with ⟨hJ₂below, hJ₂above, _, _, _, _⟩
  constructor
  · apply le_csInf hJ₁.1
    grind
  · apply (csSup_le_iff hJ₁above hJ₁.1).2
    grind

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
  have hleft : (a₂ + b₂) / 2 - kappa * (b₂ - a₂) / 2 ≤
      (a₁ + b₁) / 2 - kappa * (b₁ - a₁) / 2 := by
    nlinarith
  have hright : (a₁ + b₁) / 2 + kappa * (b₁ - a₁) / 2 ≤
      (a₂ + b₂) / 2 + kappa * (b₂ - a₂) / 2 := by
    nlinarith
  grind

/-- Boundary-shifted midpoint expansion is monotone even when the two
intervals encounter different boundary cases. -/
theorem boundaryShiftedMidpointExpansion_mono_of_subset
    (kappa : Real) (hkappa : 1 < kappa) {J₁ J₂ : Set Real}
    (hJ₁ : IsOpenSubinterval (Ioo (-1 : Real) 1) J₁)
    (hJ₂ : IsOpenSubinterval (Ioo (-1 : Real) 1) J₂)
    (hsubset : J₁ ⊆ J₂) :
    boundaryShiftedMidpointExpansion kappa J₁ ⊆
      boundaryShiftedMidpointExpansion kappa J₂ := by
  rcases endpoint_mono_of_subset hJ₁ hJ₂ hsubset with ⟨hinf, hsup⟩
  exact Ioo_subset_Ioo (midpoint_expansion_mono_of_endpoints hkappa hinf hsup).1
    (midpoint_expansion_mono_of_endpoints hkappa hinf hsup).2

/-- The boundary-shifted expansion has at most the sharp local `kappa`
volume factor. -/
theorem volume_boundaryShiftedMidpointExpansion_le
    (kappa : Real) (hkappa : 1 < kappa) {J : Set Real}
    (hJ : IsOpenSubinterval (Ioo (-1 : Real) 1) J) :
    volume (boundaryShiftedMidpointExpansion kappa J) ≤
      ENNReal.ofReal kappa * volume J := by
  rcases open_subinterval_endpoint_data hJ with ⟨_, _, heq, hlow, hlt, hupp⟩
  have hlength := boundary_shifted_length_le hkappa hlow hlt hupp
  rw [boundaryShiftedMidpointExpansion, intervalEndpointLength,
    intervalEndpointMidpoint, heq, csInf_Ioo hlt, csSup_Ioo hlt,
    Real.volume_Ioo, Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (le_trans zero_le_one hkappa.le)]
  apply ENNReal.ofReal_le_ofReal
  omega

/-- Sharp uncountable-family estimate for varying-centre expansions. -/
theorem volume_sUnion_boundaryShiftedMidpointExpansion
    (kappa : Real) (hkappa : 1 < kappa) (B : Set (Set Real))
    (hB : ∀ J ∈ B, IsOpenSubinterval (Ioo (-1 : Real) 1) J) :
    volume (⋃₀ (boundaryShiftedMidpointExpansion kappa '' B)) ≤
      ENNReal.ofReal kappa * volume (⋃₀ B) := by
  apply volume_sUnion_monotone_interval_enlargement_Ioo_of_le kappa hkappa (-1) 1
    (by norm_num) B _
  · exact hB
  · intro J hJ
    exact isOpenSubinterval_boundaryShiftedMidpointExpansion kappa hkappa hJ
  · intro J hJ
    exact volume_boundaryShiftedMidpointExpansion_le kappa hkappa hJ
  · intro J₁ J₂ hJ₁ hJ₂ hsubset
    exact boundaryShiftedMidpointExpansion_mono_of_subset kappa hkappa hJ₁ hJ₂ hsubset

private theorem interval_inter_reference_eq {a b : Real} :
    Ioo a b ∩ Ioo (-1 : Real) 1 = Ioo (max (-1 : Real) a) (min 1 b) := by
  grind

private theorem boundary_shifted_affine_image_formula
    (c zeta l u : Real) (hzeta0 : 0 < zeta) (_hl : -1 ≤ l) (_hu : u ≤ 1)
    (hlu : l < u) :
    boundaryShiftedMidpointExpansion zeta⁻¹
        ((fun x : Real => c + zeta * (x - c)) '' Ioo l u) =
      Ioo
        (max (-1 : Real)
          (min (1 - (u - l))
            (c + zeta * ((l + u) / 2 - c) - (u - l) / 2)))
        (min 1
          (max (-1 + (u - l))
            (c + zeta * ((l + u) / 2 - c) + (u - l) / 2))) := by
  have hcontracted : zeta * l + (1 - zeta) * c < zeta * u + (1 - zeta) * c := by
    nlinarith
  unfold boundaryShiftedMidpointExpansion intervalEndpointLength intervalEndpointMidpoint
  rw [show (fun x : Real => c + zeta * (x - c)) =
      fun x => zeta * x + (1 - zeta) * c by
        ring,
    image_affine_Ioo hzeta0, csInf_Ioo hcontracted, csSup_Ioo hcontracted]
  grind

/-- Exact source recovery for the contraction of a clipped centred interval.
The four possible clipping cases are split explicitly; after clipping, the
midpoint expansion recovers the same endpoint interval in each case. -/
theorem boundaryShiftedMidpointExpansion_image_centeredInterval_inter
    (c r zeta : Real) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hc : c ∈ Ioo (-1 : Real) 1) (hr : 0 < r) :
    boundaryShiftedMidpointExpansion zeta⁻¹
        ((fun x : Real => c + zeta * (x - c)) ''
          (Ioo (c - r) (c + r) ∩ Ioo (-1 : Real) 1)) =
      Ioo (c - r) (c + r) ∩ Ioo (-1 : Real) 1 := by
  have hab : c - r < c + r := by linarith
  rw [interval_inter_reference_eq]
  have hclow : -1 < c := hc.1
  have hcupp : c < 1 := hc.2
  by_cases hleft : c - r < -1
  · by_cases hright : 1 < c + r
    · rw [max_eq_left hleft.le, min_eq_left hright.le]
      rw [boundary_shifted_affine_image_formula c zeta (-1) 1 hzeta0 le_rfl le_rfl
        (by norm_num)]
      simp
    · rw [max_eq_left hleft.le, min_eq_right (le_of_not_gt hright)]
      rw [boundary_shifted_affine_image_formula c zeta (-1) (c + r) hzeta0 le_rfl
        (le_of_not_gt hright) (by linarith)]
      have hL : c + zeta * ((-1 + (c + r)) / 2 - c) -
          ((c + r) - (-1)) / 2 ≤ -1 := by nlinarith
      grind
  · by_cases hright : 1 < c + r
    · rw [max_eq_right (le_of_not_gt hleft), min_eq_left hright.le]
      rw [boundary_shifted_affine_image_formula c zeta (c - r) 1 hzeta0
        (le_of_not_gt hleft) le_rfl (by linarith)]
      have hL : c - r ≤ c + zeta * (((c - r) + 1) / 2 - c) -
          (1 - (c - r)) / 2 := by nlinarith
      grind
    · rw [max_eq_right (le_of_not_gt hleft), min_eq_right (le_of_not_gt hright)]
      rw [boundary_shifted_affine_image_formula c zeta (c - r) (c + r) hzeta0
        (le_of_not_gt hleft) (le_of_not_gt hright) hab]
      grind

end HypoellipticAleksandrov.Parabolic
