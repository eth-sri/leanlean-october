module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelDefs

/-!
# Source slices and their classical solutions

For a smooth compactly supported source `g` with `tsupport g ⊆ U₀ = {(s,v) : s < T, v ∈ Ω_s}`,
each slice `g(r,·)` is a smooth compact terminal datum on the moving domain at time `r`.  The
supplied parabolic marginal bundle then provides the classical solution `V_r` with terminal value
`g(r,·)` and zero lateral values, and `V_r` is the marginal-kernel source integral.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal ProbabilityTheory

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/- The open starting set `U₀ = {(s,v) : s < T, v ∈ Ω_s}` of the Duhamel potential. -/
def duhamelFiber (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (T : ℝ) : Set (TimeVelocity d) :=
  {p | p.1 < T ∧ p.2 ∈ movingDomain Ω γ p.1}

/- The closed region `{(s,v) : s ≤ T, v ∈ closure Ω_s}` carrying the continuous extension. -/
def duhamelClosedFiber (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (T : ℝ) :
    Set (TimeVelocity d) :=
  {p | p.1 ≤ T ∧ p.2 ∈ closure (movingDomain Ω γ p.1)}

/- The open past cylinder at the source time `r`. -/
def sliceOpenCylinder (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (r : ℝ) :
    Set (TimeVelocity d) :=
  ParabolicProbe.scalarPastOpenCylinder Ω γ r

/- The closed past cylinder at the source time `r`. -/
def sliceClosedCylinder (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (r : ℝ) :
    Set (TimeVelocity d) :=
  ParabolicProbe.scalarPastClosedCylinder Ω γ r

/- The fiber `U₀` is open when the curve is continuous and the base domain is open. -/
theorem isOpen_duhamelFiber (hΩ : IsOpen Ω) (hγ : Continuous γ) (T : ℝ) :
    IsOpen (duhamelFiber Ω γ T) := by
  have hc : Continuous (fun p : TimeVelocity d => p.2 - γ p.1) :=
    continuous_snd.sub (hγ.comp continuous_fst)
  have h1 : IsOpen {p : TimeVelocity d | p.2 - γ p.1 ∈ Ω} := hΩ.preimage hc
  have h2 : IsOpen {p : TimeVelocity d | p.1 < T} := isOpen_lt continuous_fst continuous_const
  convert h2.inter h1 using 1
  ext p
  simp only [duhamelFiber, mem_ofPred_eq, mem_inter_iff]
  change (_ ∧ _ ∈ PDE.translateSet (γ p.1) Ω) ↔ _
  rw [PDE.mem_translateSet_iff_sub_mem]

/- `U₀` lies in the closed region. -/
theorem duhamelFiber_subset_closedFiber (T : ℝ) :
    duhamelFiber Ω γ T ⊆ duhamelClosedFiber Ω γ T := fun _ hp =>
  ⟨hp.1.le, subset_closure hp.2⟩

/- The slice `v ↦ g(r,v)` of a continuous compactly supported source, as a bounded Borel
function. -/
def sliceBorel (g : TimeVelocity d → ℝ) (hg : Continuous g) (hc : HasCompactSupport g) (r : ℝ) :
    BoundedBorel (PDE.Vec d) :=
  ⟨fun v => g (r, v), (hg.comp (continuous_const.prodMk continuous_id)).measurable, by
    obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hc
    refine ⟨max C 0, le_max_right _ _, fun v => ?_⟩
    simpa only [Real.norm_eq_abs] using (hC (r, v)).trans (le_max_left _ _)⟩

@[simp] theorem sliceBorel_apply (g : TimeVelocity d → ℝ) (hg : Continuous g)
    (hc : HasCompactSupport g) (r : ℝ) (v : PDE.Vec d) : sliceBorel g hg hc r v = g (r, v) :=
  rfl

variable (K : MovingFiberKernel Ω γ)

/- The classical solution of the source slice at time `r`, identified with the
marginal-kernel source integral. -/
end HypoellipticAleksandrov.KineticAleksandrov.Occupation
