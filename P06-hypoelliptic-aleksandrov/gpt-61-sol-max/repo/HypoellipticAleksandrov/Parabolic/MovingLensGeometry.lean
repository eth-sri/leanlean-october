module

public import HypoellipticAleksandrov.Parabolic.HarnackGeometry
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
import Aesop



/-!
# Moving-lens geometry for forward propagation

This file records the compact moving lens used in the source proof of the
forward propagation lemma.  Its direct inequalities avoid introducing a
division into the set definitions.  Under a positive denominator they are
equivalent to the usual radius-ratio conditions.

The active lens includes its terminal interior face.  Accordingly, its local
neighborhood statement is relative to the causal past, not an ambient-open
statement at the terminal time.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

open Filter Set
open scoped Topology

/-- The positive time-dependent denominator of a moving lens. -/
def movingLensDenominator (xi eps t : ℝ) : ℝ :=
  xi * t + eps ^ 2

variable {d : ℕ}

/-- The velocity displacement from the free-transport center `t • y`. -/
def movingLensDisplacement  (y : PDE.Vec d) (z : TimeVelocity d) : PDE.Vec d :=
  z.2 - z.1 • y

/-- The squared radius ratio of a moving lens, wherever its denominator is nonzero. -/
def movingLensRadiusSq  (xi eps : ℝ) (y : PDE.Vec d) (z : TimeVelocity d) : ℝ :=
  PDE.vecNormSq (movingLensDisplacement y z) / movingLensDenominator xi eps z.1

variable (xi eps tau : ℝ) (y : PDE.Vec d)

/-- The compact closed moving lens, including its initial and lateral faces. -/
def movingLensClosed   : HypoellipticAleksandrov.Parabolic.Region d :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ tau ∧
    PDE.vecNormSq (movingLensDisplacement y z) ≤ movingLensDenominator xi eps z.1}

/-- The active moving lens.  Its terminal interior face is deliberately included. -/
def movingLensActive   : HypoellipticAleksandrov.Parabolic.Region d :=
  {z | 0 < z.1 ∧ z.1 ≤ tau ∧
    PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1}

variable {xi eps tau : ℝ} {y : PDE.Vec d} {z : TimeVelocity d}

/-- Membership in the closed moving lens. -/
@[simp] theorem mem_movingLensClosed_iff   :
    z ∈ movingLensClosed xi eps tau y ↔ 0 ≤ z.1 ∧ z.1 ≤ tau ∧
      PDE.vecNormSq (movingLensDisplacement y z) ≤ movingLensDenominator xi eps z.1 :=
  Iff.rfl

/-- Membership in the active moving lens. -/
@[simp] theorem mem_movingLensActive_iff   :
    z ∈ movingLensActive xi eps tau y ↔ 0 < z.1 ∧ z.1 ≤ tau ∧
      PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1 :=
  Iff.rfl

/-- The moving-lens denominator is positive on nonnegative times. -/
theorem movingLensDenominator_pos {xi eps t : ℝ}
    (hxi : 0 ≤ xi) (heps : 0 < eps) (ht : 0 ≤ t) :
    0 < movingLensDenominator xi eps t := by
  unfold movingLensDenominator
  nlinarith [mul_nonneg hxi ht, sq_pos_of_pos heps]

section
variable {d : ℕ} {xi eps : ℝ} {y : PDE.Vec d} {z : TimeVelocity d} (hden : 0 < movingLensDenominator xi eps z.1)

include hden
/-- Under a positive denominator, the radius-ratio inequality is the direct strict
spatial inequality used by the active lens. -/
theorem movingLensRadiusSq_lt_one_iff  :
    movingLensRadiusSq xi eps y z < 1 ↔
      PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1 := by
  unfold movingLensRadiusSq
  rw [div_lt_iff₀ hden]
  ring_nf

/-- Under a positive denominator, the radius-ratio inequality is the direct closed
spatial inequality used by the closed lens. -/
theorem movingLensRadiusSq_le_one_iff  :
    movingLensRadiusSq xi eps y z ≤ 1 ↔
      PDE.vecNormSq (movingLensDisplacement y z) ≤ movingLensDenominator xi eps z.1 := by
  unfold movingLensRadiusSq
  rw [div_le_iff₀ hden]
  ring_nf
end


/-- The moving-lens denominator varies continuously with time. -/
theorem continuous_movingLensDenominator (xi eps : ℝ) :
    Continuous (movingLensDenominator xi eps) := by
  unfold movingLensDenominator
  fun_prop

variable {d : ℕ}

/-- The moving-lens displacement varies continuously with the time--velocity point. -/
theorem continuous_movingLensDisplacement  (y : PDE.Vec d) :
    Continuous (movingLensDisplacement y) := by
  unfold movingLensDisplacement
  fun_prop

variable (xi eps : ℝ) (y : PDE.Vec d)

/-- The direct spatial gap of a moving lens is continuous. -/
theorem continuous_movingLensSpatialGap   :
    Continuous (fun z  =>
      PDE.vecNormSq (movingLensDisplacement y z) - movingLensDenominator xi eps z.1) := (PDE.continuous_vecNormSq.comp (continuous_movingLensDisplacement y)).sub
    ((continuous_movingLensDenominator xi eps).comp continuous_fst)

/-- The strict spatial moving-lens inequality is open. -/
theorem isOpen_movingLensSpatialStrict   :
    IsOpen {z : TimeVelocity d |
      PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1} := by
  rw [show {z : TimeVelocity d |
      PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1} =
      (fun z => PDE.vecNormSq (movingLensDisplacement y z) -
        movingLensDenominator xi eps z.1) ⁻¹' Iio 0 by
    aesop]
  exact isOpen_Iio.preimage (continuous_movingLensSpatialGap xi eps y)

/-- The positive-time strict spatial conditions of a moving lens are open. -/
theorem isOpen_movingLensPositiveSpatialStrict   :
    IsOpen {z : TimeVelocity d | 0 < z.1 ∧
      PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1} := (isOpen_Ioi.preimage continuous_fst).inter (isOpen_movingLensSpatialStrict xi eps y)

variable (xi eps tau : ℝ) (y : PDE.Vec d)

/-- The closed moving lens is closed. -/
theorem isClosed_movingLensClosed   :
    IsClosed (movingLensClosed xi eps tau y) := by
  let sharedTerm_5c7afb25b0 := ({z : TimeVelocity d | PDE.vecNormSq (movingLensDisplacement y z) ≤ movingLensDenominator xi eps z.1})



  have hset : movingLensClosed xi eps tau y =
      (({z : TimeVelocity d | 0 ≤ z.1 ∧ z.1 ≤ tau})) ∩
        sharedTerm_5c7afb25b0 := by
    ext z
    change (0 ≤ z.1 ∧ z.1 ≤ tau ∧
      PDE.vecNormSq (movingLensDisplacement y z) ≤ movingLensDenominator xi eps z.1) ↔
      ((0 ≤ z.1 ∧ z.1 ≤ tau) ∧
        PDE.vecNormSq (movingLensDisplacement y z) ≤ movingLensDenominator xi eps z.1)
    constructor
    · simp_all
    · simp_all
  rw [hset]
  exact ((isClosed_Ici.preimage continuous_fst).inter (isClosed_Iic.preimage continuous_fst)).inter (by
      rw [show sharedTerm_5c7afb25b0 =
          (fun z => PDE.vecNormSq (movingLensDisplacement y z) -
            movingLensDenominator xi eps z.1) ⁻¹' Iic 0 by
        aesop]
      exact isClosed_Iic.preimage (continuous_movingLensSpatialGap xi eps y))

/-- Every active point lies in the corresponding closed lens. -/
theorem movingLensActive_subset_movingLensClosed   :
    movingLensActive xi eps tau y ⊆ movingLensClosed xi eps tau y := by
  rintro z ⟨ht, htau, hspatial⟩
  exact ⟨ht.le, htau, hspatial.le⟩

/-- The closed lens minus the active lens consists exactly of its initial and lateral
faces; there is no terminal boundary contribution. -/
theorem mem_movingLensClosed_diff_active_iff  {xi eps tau : ℝ}
    {y : PDE.Vec d} {z : TimeVelocity d} :
    z ∈ movingLensClosed xi eps tau y \ movingLensActive xi eps tau y ↔
      (z.1 = 0 ∧ z.1 ≤ tau ∧
        PDE.vecNormSq (movingLensDisplacement y z) ≤ movingLensDenominator xi eps z.1) ∨
      (0 ≤ z.1 ∧ z.1 ≤ tau ∧
        PDE.vecNormSq (movingLensDisplacement y z) = movingLensDenominator xi eps z.1) := by
  constructor
  · rintro ⟨⟨hzero, htau, hle⟩, hnot⟩
    by_cases htime : z.1 = 0
    · exact Or.inl ⟨htime, htau, hle⟩
    · right
      refine ⟨hzero, htau, le_antisymm hle ?_⟩
      exact le_of_not_gt fun hlt => hnot ⟨lt_of_le_of_ne hzero (Ne.symm htime), htau, hlt⟩
  · rintro (hinitial | hlateral)
    · aesop
    · simp_all

variable (y : PDE.Vec d)

private def movingLensTransport   : TimeVelocity d → TimeVelocity d :=
  fun z => (z.1, z.2 + z.1 • y)

private theorem continuous_movingLensTransport   :
    Continuous (movingLensTransport y) := by
  unfold movingLensTransport
  fun_prop

variable {xi eps tau : ℝ} {y : PDE.Vec d}

/-- A closed moving lens is compact under the source-side nonnegative time and
opening parameters. -/
theorem isCompact_movingLensClosed
    (hxi : 0 ≤ xi) (heps : 0 < eps) (htau : 0 ≤ tau) :
    IsCompact (movingLensClosed xi eps tau y) := by
  let R : ℝ := Real.sqrt (xi * tau + eps ^ 2)
  let container : HypoellipticAleksandrov.Parabolic.Region d := Icc 0 tau ×ˢ PDE.euclideanClosedBall 0 R
  have hboundPos  :=
    add_pos_of_nonneg_of_pos (mul_nonneg hxi htau) (sq_pos_of_pos heps)
  have hbound  := hboundPos.le
  have hR : 0 ≤ R := Real.sqrt_nonneg _


  refine ((show IsCompact container from isCompact_Icc.prod (PDE.isCompact_euclideanClosedBall 0 hR)).image (continuous_movingLensTransport y)).of_isClosed_subset (isClosed_movingLensClosed xi eps tau y) ?_
  intro z hz
  rcases hz with ⟨hzero, hzTau, hspatial⟩
  refine ⟨(z.1, movingLensDisplacement y z), ?_, ?_⟩
  · constructor
    · exact ⟨hzero, hzTau⟩
    · change PDE.vecNormSq (movingLensDisplacement y z - 0) ≤ R ^ 2
      have hden : movingLensDenominator xi eps z.1 ≤ xi * tau + eps ^ 2 := by
        unfold movingLensDenominator
        nlinarith [mul_le_mul_of_nonneg_left hzTau hxi]
      calc
        PDE.vecNormSq (movingLensDisplacement y z - 0) =
            PDE.vecNormSq (movingLensDisplacement y z) := by simp
        _ ≤ movingLensDenominator xi eps z.1 := hspatial
        _ ≤ xi * tau + eps ^ 2 := hden
        _ = R ^ 2 := by
          dsimp only [R]
          rw [Real.sq_sqrt hbound]
  · change (z.1, (z.2 - z.1 • y) + z.1 • y) = z
    rw [sub_add_cancel]

/-- Every active point has an active relative neighborhood in its causal past,
including when the point is on the terminal face. -/
theorem movingLensActive_mem_nhdsWithin_past   {z : TimeVelocity d} (hz : z ∈ movingLensActive xi eps tau y) :
    movingLensActive xi eps tau y ∈ 𝓝[Iic z.1 ×ˢ Set.univ] z := by
  rcases hz with ⟨hpos, htau, hspatial⟩
  let neighborhood  :=
    {q | 0 < q.1 ∧
      PDE.vecNormSq (movingLensDisplacement y q) < movingLensDenominator xi eps q.1}

  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine ⟨neighborhood, (isOpen_movingLensPositiveSpatialStrict xi eps y).mem_nhds ⟨hpos, hspatial⟩, ?_⟩
  rintro q ⟨hq, hpast⟩
  exact ⟨hq.1, hpast.1.trans htau, hq.2⟩

end

end HypoellipticAleksandrov.Parabolic
