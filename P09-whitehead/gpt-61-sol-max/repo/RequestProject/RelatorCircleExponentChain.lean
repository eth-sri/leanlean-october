import Mathlib.Tactic

import RequestProject.RelatorCircleFundamentalChain
import RequestProject.StrictNormalizedOneMaps
import RequestProject.ExponentCorrection
import RequestProject.CombHurewicz1Pres

/-! The actual normalized attaching-circle fundamental chain reads the
exponent vector in the subdivided rose. The rose coefficient realization
is injective and consists of genuine one-cycles. No genus modules or
topological classification hypotheses are used. Pending Lean verification. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
open scoped Classical
variable {A J : Type u}

  (a : A)
def roseIntegerBaseEdge  (b : Bool) : StrictOrdEdge (Rose A) :=
  ⟨(Rose.base, Rose.edg a b), lt_of_le_of_ne (Rose.base_le_edg a b) (by simp)⟩

def roseIntegerMidEdge  (b : Bool) : StrictOrdEdge (Rose A) :=
  ⟨(Rose.mid a, Rose.edg a b), lt_of_le_of_ne (Rose.mid_le_edg a b) (by simp)⟩

def roseIntegerGeneratorChain  : StrictOrdEdge (Rose A) →₀ ℤ :=
  Finsupp.single (roseIntegerBaseEdge a false) 1 -
    Finsupp.single (roseIntegerMidEdge a false) 1 +
    Finsupp.single (roseIntegerMidEdge a true) 1 -
    Finsupp.single (roseIntegerBaseEdge a true) 1

def roseIntegerRealize : (A →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (Rose A) →₀ ℤ) :=
  Finsupp.linearCombination ℤ roseIntegerGeneratorChain

theorem roseIntegerGeneratorChain_selected (a b : A) :
    roseIntegerGeneratorChain a (roseIntegerMidEdge b true) = if a = b then 1 else 0 := by
  aesop (add simp [roseIntegerBaseEdge, roseIntegerMidEdge, StrictOrdEdge, roseIntegerGeneratorChain])

theorem roseIntegerRealize_selected (c : A →₀ ℤ) (a : A) :
    roseIntegerRealize c (roseIntegerMidEdge a true) = c a := by
  induction c using Finsupp.induction_linear <;> simp_all [roseIntegerRealize, roseIntegerGeneratorChain_selected, Finsupp.single_apply]

theorem roseIntegerRealize_injective : Function.Injective (roseIntegerRealize (A := A)) := by
  intro c d h
  apply Finsupp.ext
  intro a
  have he := congrArg (fun z => z (roseIntegerMidEdge a true)) h
  simpa [roseIntegerRealize_selected] using he

theorem roseIntegerGeneratorChain_cycle  :
    Comb.bdry1 (strictOrderCx (Rose A)) (roseIntegerGeneratorChain a) = 0 := by
  simp only [roseIntegerGeneratorChain, map_sub, map_add, Comb.bdry1_single (X := strictOrderCx (Rose A)), one_smul]
  change (Finsupp.single (Rose.edg a false) 1 - Finsupp.single Rose.base 1) -
      (Finsupp.single (Rose.edg a false) 1 - Finsupp.single (Rose.mid a) 1) +
      (Finsupp.single (Rose.edg a true) 1 - Finsupp.single (Rose.mid a) 1) -
      (Finsupp.single (Rose.edg a true) 1 - Finsupp.single Rose.base 1) = 0
  abel

theorem roseIntegerRealize_cycle (c : A →₀ ℤ) :
    Comb.bdry1 (strictOrderCx (Rose A)) (roseIntegerRealize c) = 0 := by
  induction c using Finsupp.induction_linear <;> simp_all [roseIntegerRealize, roseIntegerGeneratorChain_cycle]

theorem mapOne_single_of_endpoints {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (e : StrictOrdEdge P) (d : StrictOrdEdge Q)
    (he : (f e.val.1, f e.val.2) = d.val) :
    StrictNormalized.mapOne f hf (Finsupp.single e 1) = Finsupp.single d 1 := by
  rw  [StrictNormalized.mapOne_single, one_smul]
  have hn : f e.val.1 ≠ f e.val.2 := by
    grind
  simp_all [normalizeOrdEdge]

variable (w : J → List (A × Bool)) (j : J)

theorem relatorCircleLetterChain_exponent (k : Fin (w j).length) :
    StrictNormalized.mapOne (fun x : RelatorCircle w j => aFun w x.val)
      ((aFun_monotone w).comp (fun _ _ h => h)) (relatorCircleLetterChain w j k) =
        if (w j)[k.val].2 then roseIntegerGeneratorChain (w j)[k.val].1
          else -roseIntegerGeneratorChain (w j)[k.val].1 := by
  let f := fun x : RelatorCircle w j => aFun w x.val
  let hf : Monotone f := (aFun_monotone w).comp (fun _ _ h => h)
  have hp  := List.getElem?_eq_getElem k.isLt
  have hmid  :=
    aFun_pt_cmid_of_get w hp
  have hL  :=
    aFun_pt_cedgL_of_get w hp
  have hR  :=
    aFun_pt_cedgR_of_get w hp
  have h₀ := mapOne_single_of_endpoints f hf (relatorCircleEdge0 w j k)
    (roseIntegerBaseEdge (w j)[k.val].1 (!(w j)[k.val].2)) (Prod.ext rfl hL)
  have h₁ := mapOne_single_of_endpoints f hf (relatorCircleEdge1 w j k)
    (roseIntegerMidEdge (w j)[k.val].1 (!(w j)[k.val].2)) (Prod.ext hmid hL)
  have h₂ := mapOne_single_of_endpoints f hf (relatorCircleEdge2 w j k)
    (roseIntegerMidEdge (w j)[k.val].1 (w j)[k.val].2) (Prod.ext hmid hR)
  have h₃ := mapOne_single_of_endpoints f hf (relatorCircleEdge3 w j k)
    (roseIntegerBaseEdge (w j)[k.val].1 (w j)[k.val].2) (Prod.ext rfl hR)
  change StrictNormalized.mapOne f hf (relatorCircleLetterChain w j k) = _
  rw  [relatorCircleLetterChain, map_sub, map_add, map_sub, h₀, h₁, h₂, h₃]
  cases (w j)[k.val].2 <;> simp only [Bool.not_false, Bool.not_true,
    Bool.false_eq_true, if_false, if_true, roseIntegerGeneratorChain]
  abel

variable (l : List (A × Bool))
theorem pathChain_eq_sum_get  :
    pathChain l = ∑ k : Fin l.length,
      if l[k.val].2 then Finsupp.single l[k.val].1 (1 : ℤ) else -Finsupp.single l[k.val].1 1 := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw  [pathChain_cons]
    change _ = ∑ k : Fin (l.length + 1),
      if (p :: l)[k.val].2 then Finsupp.single (p :: l)[k.val].1 (1 : ℤ)
        else -Finsupp.single (p :: l)[k.val].1 1
    rw  [Fin.sum_univ_succ]
    simp_all

theorem expVec_mk_eq_pathChain  :
    FiniteChains.expVec (FreeGroup.mk l) = pathChain l := congrArg Multiplicative.toAdd (Comb.expVec_pathChain l)

/-- Exact exponent-vector formula for the normalized image of the genuine
attaching-circle fundamental chain; valid also for the empty circle. -/
theorem relatorCircleFundamentalChain_exponent :
    StrictNormalized.mapOne (fun x : RelatorCircle w j => aFun w x.val)
      ((aFun_monotone w).comp (fun _ _ h => h)) (relatorCircleFundamentalChain w j) =
        roseIntegerRealize (FiniteChains.expVec (FreeGroup.mk (w j))) := by
  rw  [relatorCircleFundamentalChain, map_sum]
  simp_rw [relatorCircleLetterChain_exponent]
  rw  [expVec_mk_eq_pathChain, pathChain_eq_sum_get, map_sum]
  apply Finset.sum_congr rfl
  aesop (add simp [roseIntegerRealize])

end FiniteChains.PresModel
