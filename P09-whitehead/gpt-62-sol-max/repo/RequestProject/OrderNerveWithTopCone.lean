module

public import RequestProject.OrderNerveFiniteCoordinates
public import RequestProject.OrderNerveRealizationContraction
public import Mathlib.Data.Fintype.Option

@[expose] public section

/-! The actual realization of `WithTop P` is the radial cone on the actual
realization of `P`. The equal-fiber statement records the collapsed radius-zero
face exactly; no abstract cone-realization comparison is assumed. -/

noncomputable section

namespace FiniteChains.Comb
open scoped Classical unitInterval

variable (P : Type) [PartialOrder P]

def orderNerveConeBase : C(orderNerveRealization P, orderNerveRealization (WithTop P)) :=
  (orderNerveRealizationMap (fun p : P => (p : WithTop P)) WithTop.coe_mono).hom

def orderNerveRadialCone : C(I × orderNerveRealization P,
    orderNerveRealization (WithTop P)) where
  toFun rx := orderNerveRealizationCone (⊤ : WithTop P)
    (fun _ => Or.inl le_top) (unitInterval.symm rx.1) (orderNerveConeBase P rx.2)
  continuous_toFun := (orderNerveRealizationCone_continuous
    (⊤ : WithTop P) (fun _ => Or.inl le_top)).comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk
        ((orderNerveConeBase P).continuous.comp continuous_snd))

@[simp] theorem orderNerveConeBase_coordinate (x : orderNerveRealization P) (p : P) :
    orderNerveRealizationCoordinates (WithTop P) (orderNerveConeBase P x) p =
      orderNerveRealizationCoordinates P x p :=
  orderNerveRealizationCoordinates_map_injective _ WithTop.coe_mono
    WithTop.coe_injective x p

@[simp] theorem orderNerveConeBase_top (x : orderNerveRealization P) :
    orderNerveRealizationCoordinates (WithTop P) (orderNerveConeBase P x) ⊤ = 0 :=
  orderNerveRealizationCoordinates_map_outside _ WithTop.coe_mono x ⊤
    (fun ⟨p, hp⟩ => WithTop.coe_ne_top hp)

@[simp] theorem orderNerveRadialCone_top (r : I) (x : orderNerveRealization P) :
    orderNerveRealizationCoordinates (WithTop P) (orderNerveRadialCone P (r, x)) ⊤ =
      1 - (r : ℝ) := by
  simp [orderNerveRadialCone, orderNerveRealizationCone_coordinates]

@[simp] theorem orderNerveRadialCone_coordinate (r : I) (x : orderNerveRealization P)
    (p : P) :
    orderNerveRealizationCoordinates (WithTop P) (orderNerveRadialCone P (r, x)) p =
      (r : ℝ) * orderNerveRealizationCoordinates P x p := by
  simp [orderNerveRadialCone, orderNerveRealizationCone_coordinates]

@[simp] theorem orderNerveRadialCone_zero (x : orderNerveRealization P) :
    orderNerveRadialCone P (0, x) = orderNerveRealizationVertex (⊤ : WithTop P) := by
  simp [orderNerveRadialCone]

@[simp] theorem orderNerveRadialCone_one (x : orderNerveRealization P) :
    orderNerveRadialCone P (1, x) = orderNerveConeBase P x := by
  simp [orderNerveRadialCone]

theorem orderNerveRadialCone_eq_iff (a b : I × orderNerveRealization P) :
    orderNerveRadialCone P a = orderNerveRadialCone P b ↔
      a.1 = b.1 ∧ (a.1 = 0 ∨ a.2 = b.2) := by
  obtain ⟨r, x⟩ := a
  obtain ⟨s, y⟩ := b
  constructor
  · intro h
    have hr : r = s := Subtype.ext (by
      simpa only [orderNerveRadialCone_top, sub_right_inj] using
        congrArg (fun z => orderNerveRealizationCoordinates (WithTop P) z ⊤) h)
    subst s
    refine ⟨rfl, or_iff_not_imp_left.mpr fun hn => ?_⟩
    apply orderNerveRealizationCoordinates_injective P
    funext p
    have hn' : (r : ℝ) ≠ 0 := fun hz => hn (Subtype.ext hz)
    have hp := congrArg (fun z => orderNerveRealizationCoordinates (WithTop P) z p) h
    simp only [orderNerveRadialCone_coordinate, mul_right_inj' hn'] at hp
    exact hp
  · rintro ⟨rfl, h | rfl⟩
    · change r = 0 at h
      subst r
      simp
    · rfl

theorem orderNerveRadialCone_surjective [Fintype P] [Nonempty P] :
    Function.Surjective (orderNerveRadialCone P) := by
  intro x
  let c := orderNerveRealizationCoordinates (WithTop P) x
  have hc (p : WithTop P)  := orderNerveRealizationCoordinates_nonneg x p
  have hsum : c ⊤ + ∑ p : P, c p = 1 := by
    have hs := orderNerveRealizationCoordinates_sum x
    change (∑ p : Option P, c p) = 1 at hs
    erw [Fintype.sum_option] at hs
    exact hs
  have hsnonneg : 0 ≤ ∑ p : P, c p := Finset.sum_nonneg (fun p _ => hc p)
  let r : I := ⟨1 - c ⊤, by constructor <;> linarith [hc ⊤]⟩
  have hsumr : ∑ p : P, c p = r := by dsimp [r]; linarith
  have hy : ∃ y : orderNerveRealization P, ∀ p : P,
      (r : ℝ) * orderNerveRealizationCoordinates P y p = c p := by
    rcases (r.property.1).eq_or_lt with h | h
    · refine ⟨orderNerveRealizationVertex (Classical.choice inferInstance), fun p => ?_⟩
      rw [← h, zero_mul]
      exact ((Finset.sum_eq_zero_iff_of_nonneg (fun p : P => fun _ => hc p)).mp
        (hsumr.trans h.symm) p (Finset.mem_univ p)).symm
    · let d : P → ℝ := fun p => c p / r
      have hdn p : 0 ≤ d p := div_nonneg (hc p) r.property.1
      have hds : ∑ p, d p = 1 := by simp [d, ← Finset.sum_div, hsumr, h.ne']
      have hdc : IsChain (· ≤ ·) {p | 0 < d p} := by
        intro p hp q hq hpq
        simpa only [WithTop.coe_le_coe] using orderNerveRealizationCoordinates_support_chain x
          ((div_pos_iff_of_pos_right h).mp hp) ((div_pos_iff_of_pos_right h).mp hq)
          (fun e => hpq (WithTop.coe_injective e))
      obtain ⟨y, hy⟩ := orderNerveRealizationCoordinates_exists d hdn hds hdc
      exact ⟨y, fun p => by rw [hy p, show d p = c p / r from rfl]; field_simp⟩
  obtain ⟨y, hy⟩ := hy
  refine ⟨(r, y), orderNerveRealizationCoordinates_injective _ (funext fun p => ?_)⟩
  induction p using WithTop.recTopCoe with
  | top => simp [r, c]
  | coe p => simpa only [orderNerveRadialCone_coordinate] using hy p

end FiniteChains.Comb
