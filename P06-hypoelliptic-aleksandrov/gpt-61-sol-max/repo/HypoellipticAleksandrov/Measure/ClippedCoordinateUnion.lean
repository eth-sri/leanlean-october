module

public import HypoellipticAleksandrov.Measure.IntervalUnion
public import HypoellipticAleksandrov.Parabolic.Geometry
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Prod
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Measure.InkSpotsWind

open private HypoellipticAleksandrov.Parabolic.isOpen_ordConnected_eq_Ioo_csInf_csSup from HypoellipticAleksandrov.Measure.InkSpotsWind


/-!
# Clipped centred coordinate enlargements

This file formalizes the two-sided, clipped interval enlargement used for a
single coordinate in the crawling-of-ink-spots argument.  It also provides a
Fubini lifting theorem from coordinate sections to product volume.

## Main definitions

- `centeredCoordinateContraction` contracts a real coordinate about a centre.
- `clippedCoordinateExpansion` expands a centred interval inside `(-1, 1)`.
- `coordinateSection` records a section with the remaining coordinates ordered
  by `Fin.succAbove`.

## Main results

- `volume_sUnion_clippedCoordinateExpansion` controls arbitrary, including
  uncountable, families of centred intervals.
- `volume_le_of_forall_volume_coordinateSection_le` is the one-coordinate
  Fubini lift.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set


namespace HypoellipticAleksandrov.Parabolic

/-- Contraction of a real coordinate about its prescribed centre. -/
def centeredCoordinateContraction (c zeta : Real) : Real -> Real :=
  fun x => c + zeta * (x - c)

/-- An open interval of the reference coordinate interval which contains the
prescribed contraction centre. -/
def IsClippedCoordinateInterval (c : Real) (I : Set Real) : Prop :=
  IsOpenSubinterval (Ioo (-1 : Real) 1) I /\ c ∈ I




private theorem clipped_coordinate_interval_data {c : Real} {I : Set Real}
    (hI : IsClippedCoordinateInterval c I) :
    BddBelow I ∧ BddAbove I ∧ I = Ioo (sInf I) (sSup I) ∧
      sInf I < c ∧ c < sSup I ∧ (-1 : Real) ≤ sInf I ∧ sSup I ≤ 1 := by
  have hIbelow : BddBelow I :=
    ⟨-1, fun x hx => (hI.1.2.2.2 hx).1.le⟩
  have hIabove : BddAbove I :=
    ⟨1, fun x hx => (hI.1.2.2.2 hx).2.le⟩
  have hIeq  :=
    _root_.HypoellipticAleksandrov.Parabolic.isOpen_ordConnected_eq_Ioo_csInf_csSup I hI.1.2.1 hI.1.2.2.1 hI.1.1
      hIbelow hIabove
  have hc : sInf I < c ∧ c < sSup I := by
    have hc' := hI.2
    rw [hIeq] at hc'
    exact hc'


  exact ⟨hIbelow, hIabove, hIeq, hc.1, hc.2, (by
      by_contra hnot

      obtain ⟨x, hx, hxc⟩ := exists_between (lt_of_not_ge hnot)

      exact (not_lt_of_ge ((hI.1.2.2.2 (by
          rw [hIeq]

          exact ⟨hx, (hxc.trans ((hI.1.2.2.2 hI.2).1)).trans hc.2⟩)).1.le)) hxc), (by
          by_contra hnot

          obtain ⟨x, hcx, hx⟩ := exists_between (lt_of_not_ge hnot)

          exact (not_lt_of_ge ((hI.1.2.2.2 (by
              rw [hIeq]
              exact ⟨hc.1.trans ((hI.1.2.2.2 hI.2).2.trans hcx), hx⟩)).2.le)) hcx)⟩

/-- Centered coordinate contraction preserves clipped coordinate intervals. -/
theorem isClippedCoordinateInterval_centeredCoordinateContraction_image
    (c zeta : Real) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    {I : Set Real} (hI : IsClippedCoordinateInterval c I) :
    IsClippedCoordinateInterval c
      (centeredCoordinateContraction c zeta '' I) := by
  let sharedTerm_bcb0bf68a6 := (zeta * sInf I + (1 - zeta) * c)
  let sharedTerm_00abbbc8f8 := (zeta * sSup I + (1 - zeta) * c)
  rcases clipped_coordinate_interval_data hI with
    ⟨_, _, hIeq, hcinf, hcsup, hinf, hsup⟩
  rw [hIeq]
  unfold centeredCoordinateContraction
  have hone : 0 < 1 - zeta := sub_pos.mpr hzeta1
  have hleft : sharedTerm_bcb0bf68a6 < c := by
    nlinarith [mul_pos hzeta0 (sub_pos.mpr hcinf)]
  have hright : c < sharedTerm_00abbbc8f8 := by
    nlinarith [mul_pos hzeta0 (sub_pos.mpr hcsup)]


  rw [show (fun x  => c + zeta * (x - c)) =
      fun x => zeta * x + (1 - zeta) * c by
        funext x
        ring, image_affine_Ioo hzeta0]
  refine ⟨?_, ?_⟩
  · refine ⟨?_, isOpen_Ioo, ordConnected_Ioo, ?_⟩
    · exact nonempty_Ioo.mpr (hleft.trans hright)
    · exact Ioo_subset_Ioo (show -1 < sharedTerm_bcb0bf68a6 by
        nlinarith [mul_nonneg hzeta0.le (sub_nonneg.mpr hinf),
          mul_pos hone (sub_pos.mpr ((hI.1.2.2.2 hI.2).1))]).le (show sharedTerm_00abbbc8f8 < 1 by
        nlinarith [mul_nonneg hzeta0.le (sub_nonneg.mpr hsup),
          mul_pos hone (sub_pos.mpr ((hI.1.2.2.2 hI.2).2))]).le
  · exact ⟨hleft, hright⟩

variable {n : Nat} (i : Fin (n + 1))

variable (S : Set (Fin (n + 1) -> Real))

variable (w : Fin n -> Real)

/-- The section obtained by varying `i`; remaining coordinates use
`i.succAbove` order. -/
def coordinateSection
      : Set Real :=
  {x | (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => Real) i).symm (x, w) ∈ S}

private theorem coordinateSection_eq_preimage_image    :
    (fun x : Real => (x, w)) ⁻¹'
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Real) i '' S) =
      coordinateSection i S w := by
  ext x
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Real) i
  change (x ) ∈ (fun x : Real => (x, w)) ⁻¹' (e '' S) ↔
    e.symm (x, w) ∈ S
  constructor
  · rintro ⟨y, hy, hey⟩
    have hyeq : y = e.symm (x, w) := by
      apply e.injective
      simpa
    rw [← hyeq]
    exact hy
  · intro hx
    exact ⟨e.symm (x, w), hx, e.apply_symm_apply (x, w)⟩

private theorem volume_eq_lintegral_coordinateSection
    (hS : MeasurableSet S) :
    volume S = ∫⁻ w, volume (coordinateSection i S w) := by
  let sharedTerm_52ecebface := ((fun _ : Fin (n + 1) => Real))
  let e := MeasurableEquiv.piFinSuccAbove sharedTerm_52ecebface i


  calc
    volume S = volume (e '' S) := (show volume (e '' S) = volume S by
        rw [← (volume_preserving_piFinSuccAbove sharedTerm_52ecebface i).map_eq, Measure.map_apply e.measurable (e.measurableSet_image.2 hS),
          e.preimage_image]).symm
    _ = ∫⁻ w, volume (coordinateSection i S w) := by
      rw [Measure.volume_eq_prod, Measure.prod_apply_symm
        (e.measurableSet_image.2 hS)]
      exact lintegral_congr fun w =>
        congr_arg volume (coordinateSection_eq_preimage_image i S w)

/-- Fubini lift of pointwise one-coordinate section inequalities. -/
theorem volume_le_of_forall_volume_coordinateSection_le
     (S T : Set (Fin (n + 1) -> Real))
    (hS : MeasurableSet S) (hT : MeasurableSet T) (kappa : Real)
    (hsection : ∀ w : Fin n -> Real,
      volume (coordinateSection i S w) ≤
        ENNReal.ofReal kappa * volume (coordinateSection i T w)) :
    volume S ≤ ENNReal.ofReal kappa * volume T := by
  rw [volume_eq_lintegral_coordinateSection i S hS,
    volume_eq_lintegral_coordinateSection i T hT]
  calc
    (∫⁻ w, volume (coordinateSection i S w)) ≤
        ∫⁻ w, ENNReal.ofReal kappa * volume (coordinateSection i T w) :=
      lintegral_mono hsection
    _ = ENNReal.ofReal kappa *
        ∫⁻ w, volume (coordinateSection i T w) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

variable (d : Nat)

/-- Time is coordinate zero and velocity coordinate `j` is `Fin.succ j`. -/
def timeVelocityCoordinateEquiv  :
    TimeVelocity d ≃ᵐ (Fin (d + 1) -> Real) :=
  (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (d + 1) => Real) 0).symm

/-- Coordinate section of a time--velocity set after the fixed coordinate
identification. -/
def timeVelocityCoordinateSection  (i : Fin (d + 1))
    (S : HypoellipticAleksandrov.Parabolic.Region d) (w : Fin d -> Real) : Set Real :=
  coordinateSection i (timeVelocityCoordinateEquiv d '' S) w

variable {d : Nat}

private theorem volume_timeVelocityCoordinateEquiv_image
    (S : HypoellipticAleksandrov.Parabolic.Region d) (hS : MeasurableSet S) :
    volume (timeVelocityCoordinateEquiv d '' S) = volume S := by
  let e := timeVelocityCoordinateEquiv d
  have he : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => Real) 0).symm
  rw [← he.map_eq, Measure.map_apply e.measurable (e.measurableSet_image.2 hS),
    e.preimage_image]

/-- Fubini lift of coordinate-section bounds to time--velocity volume. -/
theorem volume_timeVelocity_le_of_forall_volume_coordinateSection_le
     (i : Fin (d + 1)) (S T : HypoellipticAleksandrov.Parabolic.Region d)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (kappa : Real)
    (hsection : ∀ w : Fin d -> Real,
      volume (timeVelocityCoordinateSection d i S w) ≤
        ENNReal.ofReal kappa * volume (timeVelocityCoordinateSection d i T w)) :
    volume S ≤ ENNReal.ofReal kappa * volume T := by
  calc
    volume S = volume (timeVelocityCoordinateEquiv d '' S) :=
      (volume_timeVelocityCoordinateEquiv_image S hS).symm
    _ ≤ ENNReal.ofReal kappa * volume (timeVelocityCoordinateEquiv d '' T) :=
      volume_le_of_forall_volume_coordinateSection_le i
        (timeVelocityCoordinateEquiv d '' S) (timeVelocityCoordinateEquiv d '' T)
        ((timeVelocityCoordinateEquiv d).measurableSet_image.2 hS)
        ((timeVelocityCoordinateEquiv d).measurableSet_image.2 hT) kappa
        (hsection)
    _ = ENNReal.ofReal kappa * volume T := by
      rw [volume_timeVelocityCoordinateEquiv_image T hT]

end HypoellipticAleksandrov.Parabolic
