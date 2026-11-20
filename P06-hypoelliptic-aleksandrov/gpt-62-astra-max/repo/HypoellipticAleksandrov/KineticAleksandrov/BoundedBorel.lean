module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Bounded Borel functions

This module defines the bounded real Borel-function carrier used by the
kinetic evolution statement.  Bounds are existential witnesses, so the
carrier has extensional equality and inherits its real vector-space API from
a `Submodule` of all real-valued functions.
-/

@[expose] public section

set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Bounded real Borel functions, represented as a submodule of all functions. -/
def boundedBorelSubmodule (α : Type*) [MeasurableSpace α] :
    Submodule ℝ (α → ℝ) where
  carrier := {f | Measurable f ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, abs (f x) ≤ C}
  zero_mem' := by
    constructor
    · exact measurable_const
    · exact ⟨0, le_rfl, fun x => by simp⟩
  add_mem' := by
    intro f g hf hg
    constructor
    · exact hf.1.add hg.1
    · rcases hf.2 with ⟨Cf, hCf, hf⟩
      rcases hg.2 with ⟨Cg, hCg, hg⟩
      refine ⟨Cf + Cg, add_nonneg hCf hCg, ?_⟩
      intro x
      exact (abs_add_le _ _).trans (add_le_add (hf x) (hg x))
  smul_mem' := by
    intro c f hf
    constructor
    · exact measurable_const.smul hf.1
    · rcases hf.2 with ⟨C, hC, hf⟩
      refine ⟨abs c * C, mul_nonneg (abs_nonneg _) hC, ?_⟩
      intro x
      simpa only [Pi.smul_apply, smul_eq_mul, abs_mul] using
        mul_le_mul_of_nonneg_left (hf x) (abs_nonneg c)

/-- The literal bounded-Borel real-function carrier. -/
abbrev BoundedBorel (α : Type*) [MeasurableSpace α] :=
  ↥(boundedBorelSubmodule α)

instance {α : Type*} [MeasurableSpace α] :
    CoeFun (BoundedBorel α) (fun _ => α → ℝ) where
  coe f := f.1

namespace BoundedBorel

section
variable {α : Type*}

/-- Bounded-Borel functions are equal when they agree pointwise. -/
@[ext]
theorem ext [MeasurableSpace α]
    {f g : BoundedBorel α} (h : ∀ x, f x = g x) : f = g := by
  apply Subtype.ext
  funext x
  apply h

/-- The underlying function of a bounded-Borel function is measurable. -/
theorem measurable [MeasurableSpace α]
    (f : BoundedBorel α) : Measurable f := f.property.1

/-- A bounded-Borel function has a finite nonnegative uniform absolute bound. -/
theorem exists_bound [MeasurableSpace α]
    (f : BoundedBorel α) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, abs (f x) ≤ C :=
  f.property.2

/-- The bounded-Borel constant function with value `c`. -/
def const [MeasurableSpace α] (c : ℝ) : BoundedBorel α :=
  ⟨fun _ => c, measurable_const, ⟨abs c, abs_nonneg _, fun _ => le_rfl⟩⟩

end

/-- The constant-one bounded-Borel function. -/
instance {α : Type*} [MeasurableSpace α] : One (BoundedBorel α) :=
  ⟨const 1⟩

section
variable {α : Type*}

@[simp]
theorem zero_apply [MeasurableSpace α] (x : α) :
    (0 : BoundedBorel α) x = 0 := rfl

@[simp]
theorem one_apply [MeasurableSpace α] (x : α) :
    (1 : BoundedBorel α) x = 1 := rfl

@[simp]
theorem add_apply [MeasurableSpace α]
    (f g : BoundedBorel α) (x : α) : (f + g) x = f x + g x := rfl

@[simp]
theorem neg_apply [MeasurableSpace α]
    (f : BoundedBorel α) (x : α) : (-f) x = -f x := rfl

@[simp]
theorem smul_apply [MeasurableSpace α]
    (c : ℝ) (f : BoundedBorel α) (x : α) : (c • f) x = c • f x := rfl

end

/-- Pull a bounded-Borel function back along a measurable map. -/
def pullback {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (g : β → α) (hg : Measurable g) (f : BoundedBorel α) : BoundedBorel β :=
  ⟨fun x => f (g x), by
    constructor
    · exact f.measurable.comp hg
    · rcases f.exists_bound with ⟨C, hC, hf⟩
      exact ⟨C, hC, fun x => hf (g x)⟩⟩

@[simp]
theorem pullback_apply {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (g : β → α) (hg : Measurable g)
    (f : BoundedBorel α) (x : β) : f.pullback g hg x = f (g x) := rfl

/-- Restrict a bounded-Borel function to a subtype. -/
def restrict {α : Type*} [MeasurableSpace α]
    (s : Set α) (f : BoundedBorel α) : BoundedBorel s :=
  pullback ((↑) : s → α) measurable_subtype_coe f

end BoundedBorel
end HypoellipticAleksandrov.KineticAleksandrov
