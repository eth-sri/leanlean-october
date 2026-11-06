module

public import OAI.NumberTheory.DirichletL.Moments.Correlation
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Group.Pi.Units

@[expose] public section

namespace OAI

open scoped Classical
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

theorem fullCorrelation_ringEquiv (e : A ≃+* B) (u v k : A) (f g : B → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => f (e x)) (fun y => g (e y)) k =
      fullCorrelation (fun x => e v * x) (fun y => e u * y) f g (e k) := by
  unfold fullCorrelation
  apply Fintype.sum_equiv e.toEquiv
  intro x
  apply Fintype.sum_equiv e.toEquiv
  intro y
  have heq : v * x - u * y = k ↔ e v * e x - e u * e y = e k := by
    rw [← map_mul, ← map_mul, ← map_sub, e.injective.eq_iff]
  simp_all

theorem fullCorrelation_pi {ι : Type*} [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] [∀ i, Fintype (R i)]
    (u v k : ∀ i, R i) (f g : ∀ i, R i → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)) k =
      ∏ i, fullCorrelation (fun x => v i * x) (fun y => u i * y) (f i) (g i) (k i) := by
  classical
  have hterm (x y : ∀ i, R i) :
      (if v * x - u * y = k then (∏ i, f i (x i)) * star (∏ i, g i (y i)) else 0) =
      ∏ i, if v i * x i - u i * y i = k i then f i (x i) * star (g i (y i)) else 0 := by
    by_cases h : ∀ i, v i * x i - u i * y i = k i
    · have heq : v * x - u * y = k := funext h
      simp only [heq, ite_true, h, star_prod, Finset.prod_mul_distrib]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have hne : v * x - u * y ≠ k := fun heq => hi (congrFun heq i)
      rw [ite_eq_right hne]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp_all
  simp only [fullCorrelation]
  simp_rw [hterm]
  calc
    _ = ∑ x : ∀ i, R i, ∏ i, ∑ y : R i,
        if v i * x i - u i * y = k i then f i (x i) * star (g i y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_sum (fun i (y : R i) =>
        if v i * x i - u i * y = k i then f i (x i) * star (g i y) else (0 : ℂ))).symm
    _ = _ := (Fintype.prod_sum (fun i (x : R i) => ∑ y : R i,
      if v i * x - u i * y = k i then f i x * star (g i y) else (0 : ℂ))).symm

def crtCharacter {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) :
    MulChar S ℂ where
  toFun x := ∏ i, χ i (e x i)
  map_one' := by simp
  map_mul' := by intro x y; simp [map_mul, Finset.prod_mul_distrib]
  map_nonunit' := by
    intro x hx
    have hn : ¬IsUnit (e x) := fun h => hx ((isUnit_map_iff e x).mp h)
    have hsome : ∃ i, ¬IsUnit (e x i) := by
      by_contra h
      apply hn
      exact Pi.isUnit_iff.mpr (by simpa only [not_exists, not_not] using h)
    obtain ⟨i, hi⟩ := hsome
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((χ i).map_nonunit hi)

@[simp] theorem crtCharacter_apply {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) (x : S) :
    crtCharacter e χ x = ∏ i, χ i (e x i) := rfl

end
end SevenEighths.CenteredMomentCorrelation

end OAI
