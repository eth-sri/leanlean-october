module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Coordinate geometry for the parabolic Harnack argument

The Krylov--Safonov boxes in this file use coordinate cubes.  In particular,
they are not the metric balls inherited by `PDE.Vec d`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/- The open coordinate cube of radius `r` about `v₀`. -/
def velocityCube {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) : Set (PDE.Vec d) :=
  {v | ∀ i : Fin d, |v i - v₀ i| < r}

/- The closed coordinate cube of radius `r` about `v₀`. -/
def velocityClosedCube {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) : Set (PDE.Vec d) :=
  {v | ∀ i : Fin d, |v i - v₀ i| ≤ r}

/- The forward parabolic coordinate box of height `vartheta * r^2`. -/
def parabolicBox {d : ℕ} (vartheta r t₀ : ℝ) (v₀ : PDE.Vec d) :
    Set (TimeVelocity d) :=
  Ioo t₀ (t₀ + vartheta * r ^ 2) ×ˢ velocityCube v₀ r

/- The compact closed counterpart of `parabolicBox`. -/
def parabolicClosedBox {d : ℕ} (vartheta r t₀ : ℝ) (v₀ : PDE.Vec d) :
    Set (TimeVelocity d) :=
  Icc t₀ (t₀ + vartheta * r ^ 2) ×ˢ velocityClosedCube v₀ r

/- The backward unit-height coordinate box ending at `terminalTime`. -/
def parabolicAffine {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ) :
    TimeVelocity d → TimeVelocity d :=
  fun z => (t₀ + r ^ 2 * z.1, v₀ + r • z.2)

@[simp] theorem mem_velocityCube_iff {d : ℕ} {v v₀ : PDE.Vec d} {r : ℝ} :
    v ∈ velocityCube v₀ r ↔ ∀ i : Fin d, |v i - v₀ i| < r :=
  Iff.rfl

@[simp] theorem mem_velocityClosedCube_iff {d : ℕ} {v v₀ : PDE.Vec d} {r : ℝ} :
    v ∈ velocityClosedCube v₀ r ↔ ∀ i : Fin d, |v i - v₀ i| ≤ r :=
  Iff.rfl

@[simp] theorem mem_parabolicBox_iff {d : ℕ} {vartheta r t₀ t : ℝ}
    {v₀ v : PDE.Vec d} :
    (t, v) ∈ parabolicBox vartheta r t₀ v₀ ↔
      t₀ < t ∧ t < t₀ + vartheta * r ^ 2 ∧ v ∈ velocityCube v₀ r := by
  constructor
  · rintro ⟨⟨ht₀, ht⟩, hv⟩
    exact ⟨ht₀, ht, hv⟩
  · rintro ⟨ht₀, ht, hv⟩
    exact ⟨⟨ht₀, ht⟩, hv⟩

@[simp] theorem mem_parabolicClosedBox_iff {d : ℕ} {vartheta r t₀ t : ℝ}
    {v₀ v : PDE.Vec d} :
    (t, v) ∈ parabolicClosedBox vartheta r t₀ v₀ ↔
      t₀ ≤ t ∧ t ≤ t₀ + vartheta * r ^ 2 ∧ v ∈ velocityClosedCube v₀ r := by
  constructor
  · rintro ⟨⟨ht₀, ht⟩, hv⟩
    exact ⟨ht₀, ht, hv⟩
  · rintro ⟨ht₀, ht, hv⟩
    exact ⟨⟨ht₀, ht⟩, hv⟩

theorem velocityCube_eq_pi {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) :
    velocityCube v₀ r =
      Set.univ.pi fun i => Ioo (v₀ i - r) (v₀ i + r) := by
  ext v
  constructor
  · intro hv i _
    rw [mem_Ioo]
    rcases abs_lt.mp (hv i) with ⟨hleft, hright⟩
    constructor <;> linarith
  · intro hv i
    rcases hv i trivial with ⟨hleft, hright⟩
    exact abs_lt.mpr (by constructor <;> linarith)

/- The coordinate presentation of a closed cube as a finite product of intervals. -/
theorem velocityClosedCube_eq_pi {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) :
    velocityClosedCube v₀ r =
      Set.univ.pi fun i => Icc (v₀ i - r) (v₀ i + r) := by
  ext v
  constructor
  · intro hv i _
    rw [mem_Icc]
    rcases abs_le.mp (hv i) with ⟨hleft, hright⟩
    constructor <;> linarith
  · intro hv i
    rcases hv i trivial with ⟨hleft, hright⟩
    exact abs_le.mpr (by constructor <;> linarith)

/- A positive-radius forward coordinate box has the expected literal closed-box closure. -/
theorem closure_parabolicBox_of_pos {d : Nat} {vartheta r t0 : Real}
    {v0 : PDE.Vec d} (hvartheta : 0 < vartheta) (hr : 0 < r) :
    closure (parabolicBox vartheta r t0 v0) =
      parabolicClosedBox vartheta r t0 v0 := by
  unfold parabolicBox parabolicClosedBox
  rw [closure_prod_eq,
    closure_Ioo (by nlinarith [mul_pos hvartheta (sq_pos_of_pos hr)])]
  congr 1
  rw [velocityCube_eq_pi, closure_pi_set, velocityClosedCube_eq_pi]
  exact Set.pi_congr rfl fun i _ => closure_Ioo (by nlinarith [hr])

/- Open coordinate cubes are open in the native finite-product topology. -/
theorem isOpen_velocityCube {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) :
    IsOpen (velocityCube v₀ r) := by
  rw [velocityCube_eq_pi]
  have hpi : Set.univ.pi (fun i : Fin d => Ioo (v₀ i - r) (v₀ i + r)) =
      ⋂ i ∈ (Finset.univ : Finset (Fin d)),
        (fun v : PDE.Vec d => v i) ⁻¹' Ioo (v₀ i - r) (v₀ i + r) := by
    ext v
    simp
  rw [hpi]
  exact isOpen_biInter_finset fun i _ =>
    isOpen_Ioo.preimage (continuous_apply i)

/- Closed coordinate cubes are closed in the native finite-product topology. -/
theorem isClosed_velocityClosedCube {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) :
    IsClosed (velocityClosedCube v₀ r) := by
  rw [velocityClosedCube_eq_pi]
  have hpi : Set.univ.pi (fun i : Fin d => Icc (v₀ i - r) (v₀ i + r)) =
      ⋂ i : Fin d, (fun v : PDE.Vec d => v i) ⁻¹' Icc (v₀ i - r) (v₀ i + r) := by
    ext v
    rw [Set.mem_pi]
    simp only [Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro hv i
      exact hv i (Set.mem_univ i)
    · intro hv i _
      exact hv i
  rw [hpi]
  exact isClosed_iInter fun i =>
    isClosed_Icc.preimage (continuous_apply i)

/- Open coordinate cubes are measurable. -/
theorem measurableSet_velocityCube {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) :
    MeasurableSet (velocityCube v₀ r) :=
  (isOpen_velocityCube v₀ r).measurableSet

/- Closed coordinate cubes are compact. -/
theorem isCompact_velocityClosedCube {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) :
    IsCompact (velocityClosedCube v₀ r) := by
  rw [velocityClosedCube_eq_pi]
  exact isCompact_univ_pi fun i => isCompact_Icc

/- Forward coordinate boxes are open. -/
theorem isOpen_parabolicBox {d : ℕ} (vartheta r t₀ : ℝ) (v₀ : PDE.Vec d) :
    IsOpen (parabolicBox vartheta r t₀ v₀) :=
  isOpen_Ioo.prod (isOpen_velocityCube v₀ r)

/- Forward coordinate boxes are measurable. -/
theorem measurableSet_parabolicBox {d : ℕ} (vartheta r t₀ : ℝ) (v₀ : PDE.Vec d) :
    MeasurableSet (parabolicBox vartheta r t₀ v₀) :=
  measurableSet_Ioo.prod (measurableSet_velocityCube v₀ r)

/- Closed coordinate boxes are closed. -/
theorem isClosed_parabolicClosedBox {d : ℕ} (vartheta r t₀ : ℝ) (v₀ : PDE.Vec d) :
    IsClosed (parabolicClosedBox vartheta r t₀ v₀) :=
  isClosed_Icc.prod (isClosed_velocityClosedCube v₀ r)

/- Closed coordinate boxes are compact. -/
theorem isCompact_parabolicClosedBox {d : ℕ} (vartheta r t₀ : ℝ) (v₀ : PDE.Vec d) :
    IsCompact (parabolicClosedBox vartheta r t₀ v₀) :=
  isCompact_Icc.prod (isCompact_velocityClosedCube v₀ r)

/- The open cube has the coordinate volume `(2 * r)^d` for nonnegative radii. -/
theorem volume_velocityCube_toReal {d : ℕ} {v₀ : PDE.Vec d} {r : ℝ} (hr : 0 ≤ r) :
    (volume (velocityCube v₀ r)).toReal = (2 * r) ^ d := by
  rw [velocityCube_eq_pi, Real.volume_pi_Ioo_toReal]
  · simp [Finset.prod_const, two_mul]
  · intro i
    linarith

/- The time interval in a forward box has length `vartheta * r^2`. -/
theorem volume_parabolicBox_toReal {d : ℕ} {vartheta r t₀ : ℝ} {v₀ : PDE.Vec d}
    (hvartheta : 0 ≤ vartheta) (hr : 0 ≤ r) :
    (volume (parabolicBox vartheta r t₀ v₀)).toReal =
      (vartheta * r ^ 2) * (2 * r) ^ d := by
  rw [parabolicBox, Measure.volume_eq_prod]
  rw [MeasureTheory.Measure.prod_prod]
  rw [ENNReal.toReal_mul]
  have _h_inl_32 : (volume (Ioo t₀ (t₀ + vartheta * r ^ 2))).toReal = vartheta * r ^ 2 := by
      rw [Real.volume_Ioo, ENNReal.toReal_ofReal]
      · ring
      · nlinarith [mul_nonneg hvartheta (sq_nonneg r)]

    /- Product volume of a forward coordinate box. -/
  rw [_h_inl_32,
    volume_velocityCube_toReal hr]

/- The forward-box volume displays the parabolic scaling factor `r^(d + 2)`. -/
theorem volume_parabolicBox_toReal_eq_parabolicScaling {d : ℕ}
    {vartheta r t₀ : ℝ} {v₀ : PDE.Vec d} (hvartheta : 0 ≤ vartheta) (hr : 0 ≤ r) :
    (volume (parabolicBox vartheta r t₀ v₀)).toReal =
      (vartheta * 2 ^ d) * r ^ (d + 2) := by
  rw [volume_parabolicBox_toReal hvartheta hr]
  rw [mul_pow]
  ring

/- A round Euclidean ball is contained in the coordinate cube of the same radius. -/
theorem euclideanBall_subset_velocityCube {d } {v₀ : PDE.Vec d} {r }
    (hr : 0 < r) :
    PDE.euclideanBall v₀ r ⊆ velocityCube v₀ r := by
  intro v hv i
  have hcoord : (v i - v₀ i) ^ 2 < r ^ 2 := by
    simpa [PDE.euclideanSqDist, Pi.sub_apply] using
      (PDE.sq_apply_le_vecNormSq (v - v₀) i).trans_lt hv
  exact abs_lt_of_sq_lt_sq hcoord hr.le

/- The affine scaling map pulls a translated box back to the reference box. -/
theorem mem_parabolicAffine_preimage_parabolicBox_iff {d vartheta r t₀ t} {v₀ v : PDE.Vec d} (hr : 0 < r) :
    parabolicAffine t₀ v₀ r (t, v) ∈ parabolicBox vartheta r t₀ v₀ ↔
      (t, v) ∈ parabolicBox vartheta 1 0 0 := by
  have hrsq := sq_pos_of_pos hr
  have hspace : v₀ + r • v ∈ velocityCube v₀ r ↔
      v ∈ velocityCube (0 : PDE.Vec d) 1 := by
    constructor
    · intro hv i
      have hi := hv i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      rw [add_sub_cancel_left, abs_mul, abs_of_pos hr] at hi
      have hi' : |v i| < 1 :=
        lt_of_mul_lt_mul_left (by simpa only [mul_one] using hi) hr.le
      simpa using hi'
    · intro hv i
      have hi := hv i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      rw [add_sub_cancel_left, abs_mul, abs_of_pos hr]
      have hi' : |v i| < 1 := by simpa using hi
      simpa using mul_lt_mul_of_pos_left hi' hr
  rw [mem_parabolicBox_iff, mem_parabolicBox_iff]
  simp only [parabolicAffine]
  change t₀ < t₀ + r ^ 2 * t ∧
      t₀ + r ^ 2 * t < t₀ + vartheta * r ^ 2 ∧
      v₀ + r • v ∈ velocityCube v₀ r ↔
    0 < t ∧ t < 0 + vartheta * 1 ^ 2 ∧ v ∈ velocityCube (0 : PDE.Vec d) 1
  norm_num only [zero_add, one_pow]
  rw [hspace]
  constructor <;> rintro ⟨hleft, hright, hv⟩ <;>
    refine ⟨?_, ?_, hv⟩ <;> nlinarith

/- The affine map sends every reference-box point into its translated box. -/
theorem mapsTo_parabolicAffine_parabolicBox {d vartheta r t₀}
    {v₀ : PDE.Vec d} (hr : 0 < r) :
    Set.MapsTo (parabolicAffine t₀ v₀ r) (parabolicBox vartheta 1 0 0)
      (parabolicBox vartheta r t₀ v₀) := by
  intro z hz
  exact (mem_parabolicAffine_preimage_parabolicBox_iff hr).mpr hz

/- Parabolic affine scaling is injective for positive radii. -/
theorem parabolicAffine_injective {d t₀ r} {v₀ : PDE.Vec d}
    (hr : 0 < r) : Function.Injective (parabolicAffine t₀ v₀ r) := by
  intro z w hzw
  have hrsq := sq_pos_of_pos hr
  have htime : z.1 = w.1 := by
    have := congrArg Prod.fst hzw
    dsimp [parabolicAffine] at this
    nlinarith
  have hvelocity : z.2 = w.2 := by
    ext i
    have hi := congrFun (congrArg Prod.snd hzw) i
    dsimp [parabolicAffine] at hi
    nlinarith
  exact Prod.ext htime hvelocity

end

end HypoellipticAleksandrov.Parabolic
