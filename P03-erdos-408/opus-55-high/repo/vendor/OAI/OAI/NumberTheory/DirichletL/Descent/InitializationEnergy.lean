module

public import OAI.NumberTheory.DirichletL.Inversion.InitialFibers
public import OAI.NumberTheory.DirichletL.Descent.Fibers
public import OAI.NumberTheory.DirichletL.Descent.Sharp

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
open CompletedGauss CanonicalQuadraticSieve SevenEighths.InverseInitialFibers
open IdealMobiusDivisorSum
noncomputable section

abbrev InitialChild := Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O

def initialChild {J : ℕ} (x : InitialTuple J) : InitialChild :=
  (idealQuotient x.divisor x.common, x.divisor * x.residual,
    primaryGenerator x.divisor * x.frequency)

structure InitialSourceValid {J : ℕ} (x : InitialTuple J) : Prop where
  common_ne_zero : x.common ≠ 0
  residual_ne_zero : x.residual ≠ 0
  divisor_good : primaryGenerator x.divisor ≠ 0
  divisor_dvd : x.divisor ∣ x.common
  assigned_dvd : ∀ i, (x.assigned i).val ∣ x.common * x.residual

theorem initialChild_valid {J : ℕ} (x : InitialTuple J) (hx : InitialSourceValid x) :
    Valid x (initialChild x).1 (initialChild x).2.1 (initialChild x).2.2 := by
  have ht : idealQuotient x.divisor x.common * x.divisor = x.common := by
    rw [mul_comm, idealQuotient_mul hx.divisor_dvd]
  refine ⟨ht, rfl, hx.divisor_good, rfl, ?_⟩
  intro i
  change (x.assigned i).val ∣ idealQuotient x.divisor x.common * (x.divisor * x.residual)
  rw [← mul_assoc, ht]
  exact hx.assigned_dvd i

theorem initialChild_nonzero {J : ℕ} (x : InitialTuple J) (hx : InitialSourceValid x) :
    (initialChild x).1 ≠ 0 ∧ (initialChild x).2.1 ≠ 0 := by
  have hD : x.divisor ≠ 0 := by intro he; exact hx.divisor_good (by simp_all)
  constructor
  · intro ht
    have he := (initialChild_valid x hx).common_eq
    rw [ht, zero_mul] at he
    exact hx.common_ne_zero he.symm
  · exact mul_ne_zero hD hx.residual_ne_zero

def initialQuotientSet {J : ℕ} (source : Finset (InitialTuple J)) : Finset (Ideal ActualEisensteinCubic.O) :=
  source.image (fun x => (initialChild x).1)

def initialDivisorWeight (J : ℕ) (c : InitialChild) : ℝ :=
  ((idealDivisors c.2.1).card : ℝ) ^ (J + 1) * ((idealDivisors c.1).card : ℝ) ^ J

theorem initialChild_fiber_weight {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x) (c : InitialChild)
    (ht : c.1 ≠ 0) (hf : c.2.1 ≠ 0) (w : InitialTuple J → ℝ)
    (hw : ∀ x ∈ source, w x ≤ 1) :
    (∑ x ∈ source with initialChild x = c, w x) ≤ initialDivisorWeight J c := by
  have hvalid : ∀ x ∈ source.filter (fun x => initialChild x = c), Valid x c.1 c.2.1 c.2.2 := by
    intro x hx
    obtain ⟨hxs, he⟩ := Finset.mem_filter.mp hx
    simpa only [he] using initialChild_valid x (by grind)
  calc
    _ ≤ ∑ _x ∈ source.filter (fun x => initialChild x = c), (1 : ℝ) :=
      Finset.sum_le_sum (by grind)
    _ = ((source.filter (fun x => initialChild x = c)).card : ℝ) := by simp
    _ ≤ initialDivisorWeight J c := by
      have hh := valid_tuple_card_le_separated _ c.1 c.2.1 c.2.2 ht hf hvalid
      dsimp only [initialDivisorWeight]
      exact_mod_cast hh

theorem initial_energy_projection {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (rows : Finset ActualEisensteinCubic.O)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ source, (initialChild x).2.1 ∈ labels ∧ (initialChild x).2.2 ∈ rows)
    (w : InitialTuple J → ℝ) (hw : ∀ x ∈ source, w x ≤ 1) (F : InitialChild → ℂ) :
    (∑ x ∈ source, w x * ‖F (initialChild x)‖ ^ 2) ≤
      ∑ t ∈ initialQuotientSet source, ((idealDivisors t).card : ℝ) ^ J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ) ^ (J + 1) *
          ∑ k ∈ rows, ‖F (t, f, k)‖ ^ 2 := by
  have hmaps : ∀ x ∈ source, initialChild x ∈ initialQuotientSet source ×ˢ (labels ×ˢ rows) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr (by grind),
      by grind⟩
  have hfiber : ∀ c ∈ initialQuotientSet source ×ˢ (labels ×ˢ rows),
      (∑ x ∈ source with initialChild x = c, w x) ≤ initialDivisorWeight J c := by
    intro c hc
    obtain ⟨ht, hfk⟩ := Finset.mem_product.mp hc
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp ht
    have ht0 := he ▸ (initialChild_nonzero x (by grind)).1
    exact initialChild_fiber_weight source hsource c ht0
      (by grind) w hw
  have he := fiber_energy_bound source (initialQuotientSet source ×ˢ (labels ×ˢ rows))
    initialChild w (initialDivisorWeight J) (fun c => ‖F c‖ ^ 2) hmaps
    (by simp) hfiber
  apply he.trans_eq
  simp only [Finset.sum_product, initialDivisorWeight, Finset.mul_sum]
  grind

end
end SevenEighths.InverseMoment

end OAI
