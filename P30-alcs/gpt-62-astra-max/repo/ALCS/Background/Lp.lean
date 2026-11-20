module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

/-- Use everywhere bounded representatives to compute joins and pastings pointwise. -/
@[ext] structure PalomarALCS.Control (U : Type*) [NormedAddCommGroup U] (C : ℝ≥0) where
  val : ℝ → U
  meas : StronglyMeasurable val
  bound : ∀ t, ‖val t‖ ≤ C

namespace PalomarALCS.Control
scoped notation "μ₊" => volume.restrict (Ici (0 : ℝ))
scoped notation "L∞(" V ")" => Lp V ∞ μ₊
variable {U : Type*} [NormedAddCommGroup U] {C : ℝ≥0} (f g : Control U C)

attribute [fun_prop] meas

instance : CoeFun (Control U C) (fun _ => ℝ → U) := ⟨val⟩

lemma mem : MemLp f ∞ μ₊ :=
  memLp_top_of_bound f.meas.aestronglyMeasurable _ (.of_forall f.bound)

abbrev lp := f.mem.toLp f
instance : CoeOut (Control U C) L∞(U) := ⟨lp⟩

lemma norm_lp : ‖f.lp‖ ≤ C := by
  rw [lp, Lp.norm_toLp, eLpNorm_exponent_top f.meas.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal C.2 (eLpNormEssSup_le_of_ae_bound (.of_forall f.bound))

lemma rep (u : L∞(U)) (hu : ‖u‖ ≤ C) : ∃ f : Control U C, f.lp = u := by
  borelize U
  obtain ⟨g, hm, hb, e⟩ := (Lp.aestronglyMeasurable u).exists_stronglyMeasurable_range_subset
    (s := {x | ‖x‖ ≤ C}) (by measurability) ⟨0, by simp⟩
    ((ae_le_lpNorm_exponent_top (Lp.memLp u)).mono fun _ h =>
      (by simpa [← toReal_eLpNorm, Lp.norm_def] using h : _ ≤ ‖u‖).trans hu)
  exact ⟨⟨g, hm, hb⟩, Lp.ext (MemLp.coeFn_toLp _ |>.trans e.symm)⟩

@[simps] instance : Zero (Control U C) := ⟨0, stronglyMeasurable_zero, by simp⟩
@[simp] lemma lp_zero : (0 : Control U C).lp = 0 := rfl

def cat (a : ℝ) : Control U C :=
  ⟨fun t => if t < a then f t else g (t - a), .ite measurableSet_Iio f.meas (by fun_prop),
    fun t => by split <;> apply bound⟩

/-- Paste disjoint pulses. Flipping the signs outside any one pulse preserves the bound. -/
lemma pack [CompleteSpace U] (v : ℕ → Control U C)
    (unique : ∀ {t i j}, v i t ≠ 0 → v j t ≠ 0 → i = j) :
    ∃ f : Control U C, ∀ i, ‖(v i).lp + (v i).lp - f.lp‖ ≤ C := by
  have on {i t} (hi : v i t ≠ 0) : (∑' j, v j t) = v i t :=
    tsum_eq_single i (by grind)
  let f : Control U C := ⟨_, .tsum (fun i => (v i).meas), fun t => by
    by_cases h : ∀ i, v i t = 0
    · simp [h]
    · obtain ⟨i, hi⟩ := not_forall.mp h; rw [on hi]; apply bound⟩
  refine ⟨f, fun i => norm_lp ⟨fun t => v i t + v i t - f t, by fun_prop, fun t => ?_⟩⟩
  convert f.bound t using 1
  by_cases hi : v i t = 0
  · simp [hi]
  · simp [f, on hi]

end PalomarALCS.Control
