import RequestProject.OrderNerveFiniteCoordinates
import RequestProject.OrderNerveRealizationContraction
import Mathlib.Data.Fintype.Option
import RequestProject.Tac


/-! The actual realization of `WithTop P` is the radial cone on the actual
realization of `P`. The equal-fiber statement records the collapsed radius-zero
face exactly; no abstract cone-realization comparison is assumed. -/

noncomputable section
bwd

namespace FiniteChains.Comb
open scoped Classical unitInterval

variable (P : Type) [PartialOrder P]

def orderNerveConeBase :=
  (orderNerveRealizationMap (fun p : P => (p : WithTop P)) WithTop.coe_mono).hom

def orderNerveRadialCone : C(I × orderNerveRealization P,
    orderNerveRealization (WithTop P)) where
  toFun rx := orderNerveRealizationCone (⊤ : WithTop P)
    (fun _ => Or.inl le_top) (unitInterval.symm rx.1) (orderNerveConeBase P rx.2)
  continuous_toFun := (orderNerveRealizationCone_continuous
    (⊤ : WithTop P) (fun _ => Or.inl le_top)).comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk
        ((orderNerveConeBase P).continuous.comp continuous_snd))

@[simp] theorem orderNerveConeBase_coordinate x (p : P) :
    orderNerveRealizationCoordinates (WithTop P) (orderNerveConeBase P x) p =
      orderNerveRealizationCoordinates P x p :=
  orderNerveRealizationCoordinates_map_injective _ WithTop.coe_mono
    WithTop.coe_injective x p

@[simp] theorem orderNerveConeBase_top x :
    orderNerveRealizationCoordinates (WithTop P) (orderNerveConeBase P x) ⊤ = 0 :=
  orderNerveRealizationCoordinates_map_outside _ WithTop.coe_mono x ⊤
    (by rintro ⟨p, hp⟩; exact WithTop.coe_ne_top hp)

@[simp] theorem orderNerveRadialCone_top r x :
    orderNerveRealizationCoordinates (WithTop P) (orderNerveRadialCone P (r, x)) ⊤ =
      1 - r := by
  simp [orderNerveRadialCone, orderNerveRealizationCone_coordinates]

@[simp] theorem orderNerveRadialCone_coordinate r x
    (p : P) :
    orderNerveRealizationCoordinates (WithTop P) (orderNerveRadialCone P (r, x)) p =
      r * orderNerveRealizationCoordinates P x p := by
  simp [orderNerveRadialCone, orderNerveRealizationCone_coordinates]

@[simp] theorem orderNerveRadialCone_zero x :
    orderNerveRadialCone P (0, x) = orderNerveRealizationVertex (⊤) := by
  simp [orderNerveRadialCone]

@[simp] theorem orderNerveRadialCone_one x :
    orderNerveRadialCone P (1, x) = orderNerveConeBase P x := by
  simp [orderNerveRadialCone]

theorem orderNerveRadialCone_eq_iff a b :
    orderNerveRadialCone P a = orderNerveRadialCone P b ↔
      a.1 = b.1 ∧ (a.1 = 0 ∨ a.2 = b.2) := by
  constructor
  · intro h
    have ht := (orderNerveRadialCone_top P a.1 a.2).symm.trans
      ((congrArg _ h).trans
        (orderNerveRadialCone_top P b.1 b.2))
    have hr : a.1 = b.1 := by grind
    refine ⟨hr, ?_⟩
    by_cases hz : a.1 = 0
    · exact Or.inl hz
    · right
      apply orderNerveRealizationCoordinates_injective P
      funext p
      have hp := (orderNerveRadialCone_coordinate P a.1 a.2 p).symm.trans
        ((congrArg _ h).trans
          (orderNerveRadialCone_coordinate P b.1 b.2 p))
      simp_all
  aesop

theorem orderNerveRadialCone_surjective [Fintype P] [Nonempty P] :
    Function.Surjective (orderNerveRadialCone P) := by
  intro x
  let c := orderNerveRealizationCoordinates _ x
  have hc (p : WithTop P) : 0 ≤ c p := orderNerveRealizationCoordinates_nonneg x p
  have hsum : c ⊤ + ∑ p : P, c p = 1 := by
    have hs := orderNerveRealizationCoordinates_sum x
    change (∑ p : Option P, c p) = 1 at hs
    aesop
  have hsnonneg : 0 ≤ ∑ p : P, c p := Finset.sum_nonneg (by simp_all)
  let r : I := ⟨1 - c ⊤, by grind [hc ⊤]⟩
  have hsumr : ∑ p : P, c p = r := by grind
  by_cases hr : r = 0
  · let p₀ : P := Classical.choice inferInstance
    refine ⟨(0, orderNerveRealizationVertex p₀), ?_⟩
    rwd [orderNerveRadialCone_zero]
    apply orderNerveRealizationCoordinates_injective _
    funext p
    induction p using WithTop.recTopCoe with
    | top =>
        have hz := congrArg (fun t : I => (t : ℝ)) hr
        dsimp at hz
        simp [orderNerveRealizationCoordinates_vertex, ite_true]
        grind
    | coe p =>
        have hp :=
          Finset.single_le_sum (f := fun q : P => c q)
            (by simp_all) (Finset.mem_univ p)
        rwd [hsumr, hr] at hp
        simp [Set.Icc.coe_zero] at hp
        simp [orderNerveRealizationCoordinates_vertex, WithTop.top_ne_coe, ite_false]
        grind
  · have hrpos : 0 < (r : ℝ) := by grind
    let d : P → ℝ := fun p => c p / r
    have hd : ∀ p, 0 ≤ d p := fun p => div_nonneg (hc p) r.property.1
    have hdsum : ∑ p, d p = 1 := by
      simp [d, ← Finset.sum_div, hsumr, div_self (ne_of_gt hrpos)]
    have hdchain : IsChain (· ≤ ·) {p | 0 < d p} := by
      intro p hp q hq hpq
      have hp' : 0 < c p := by aesop
      have hq' : 0 < c q := by aesop
      have h := orderNerveRealizationCoordinates_support_chain x hp' hq'
        (by simp_all)
      simp_all
    cases' orderNerveRealizationCoordinates_exists d hd hdsum hdchain with y hy
    refine ⟨(r, y), ?_⟩
    apply orderNerveRealizationCoordinates_injective _
    funext p
    induction p using WithTop.recTopCoe with
    | top =>
        aesop
    | coe p =>
        grind [orderNerveRadialCone_coordinate]
