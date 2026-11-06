module

public import GS.UnitaryLocalModel.OuterFibres

@[expose] public section


/-!
# Exact fibres of the complex middle blocks

The coefficients are complex, but the common Pauli axis is real. Therefore the
only nonzero ambiguity is simultaneous interchange of the two middle matrices
and reversal of the sphere axis. The zero difference collapses the whole sphere.
-/
noncomputable section
namespace GS.UnitaryLocalModel

section
variable {κ : Type*}
def realify (z : κ → ℂ) : κ × Fin 2 → ℝ :=
  fun p => if p.2 = 0 then (z p.1).re else (z p.1).im

theorem realify_injective : Function.Injective (@realify κ) := by
  intro z w h
  funext j
  apply Complex.ext
  · simpa [realify] using congrFun h (j,0)
  · simpa [realify] using congrFun h (j,1)

@[simp] theorem realify_zero : realify (0 : κ → ℂ) = 0 := by
  funext p
  simp [realify]

@[simp] theorem realify_neg (z : κ → ℂ) :
    realify (-z) = -realify z := by
  funext p
  by_cases h : p.2 = 0 <;> simp [realify,h]

def complexOuter (u : AxisVector) (z : κ → ℂ) : Matrix (Fin 3) κ ℂ :=
  fun i j => (u i : ℂ) * z j

theorem complexOuter_eq_iff (u v : AxisVector) (z w : κ → ℂ) :
    complexOuter u z = complexOuter v w ↔
      sphereOuter u (realify z) = sphereOuter v (realify w) := by
  constructor
  · intro h
    ext i p
    have hh := congrFun (congrFun h i) p.1
    by_cases hp : p.2 = 0
    · simpa [sphereOuter,realify,hp,complexOuter] using congrArg Complex.re hh
    · simpa [sphereOuter,realify,hp,complexOuter] using congrArg Complex.im hh
  · intro h
    ext i j
    apply Complex.ext
    · have hh := congrFun (congrFun h i) (j,0)
      simpa [sphereOuter,realify,complexOuter] using hh
    · have hh := congrFun (congrFun h i) (j,1)
      simpa [sphereOuter,realify,complexOuter] using hh

end

def axisCoefficient (H : CMat 2) : Fin 3 → ℂ :=
  ![H 0 0 - H 1 1, H 0 1 + H 1 0, Complex.I * (H 0 1 - H 1 0)]

section
variable (a b : ℂ) (u : AxisVector)
theorem middleBlock_trace :
    Matrix.trace (middleBlock a b u) = a+b := by
  simp [Matrix.trace,Fin.sum_univ_two,middleBlock,pauli]
  ring

theorem middleBlock_axisCoefficient :
    axisCoefficient (middleBlock a b u) = fun i => (u i : ℂ) * (a-b) := by
  funext i
  fin_cases i <;> simp [axisCoefficient,middleBlock,pauli] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

end

theorem middleBlock_family_fibres {κ : Type*} (a b c d : κ → ℂ)
    {u v : AxisVector} (hu : OnSphere u) (hv : OnSphere v) :
    (∀ j, middleBlock (a j) (b j) u = middleBlock (c j) (d j) v) ↔
      (a = b ∧ c = d ∧ a = c) ∨
      (u = v ∧ a = c ∧ b = d) ∨ (u = -v ∧ a = d ∧ b = c) := by
  constructor
  · intro h
    have hsum (j : κ) : a j + b j = c j + d j := by
      simpa only [middleBlock_trace] using congrArg Matrix.trace (h j)
    have ho : complexOuter u (a-b) = complexOuter v (c-d) := by
      ext i j
      have hh := congrFun (congrArg axisCoefficient (h j)) i
      simpa only [middleBlock_axisCoefficient,complexOuter,Pi.sub_apply] using hh
    simp only [complexOuter_eq_iff, sphereOuter_fibres hu hv, ← realify_neg, ← realify_zero, realify_injective.eq_iff] at ho
    rcases ho with h | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp only [funext_iff, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply] at * <;> grind
  · rintro (⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩)
    · intro j
      rw [middleBlock_equal,middleBlock_equal]
    · simp
    · intro j
      exact middleBlock_simultaneous_swap _ _ _

end GS.UnitaryLocalModel
