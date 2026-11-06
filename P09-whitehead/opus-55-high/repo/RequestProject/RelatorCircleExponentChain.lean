import RequestProject.RelatorCircleFundamentalChain
import RequestProject.StrictNormalizedOneMaps
import RequestProject.ExponentCorrection
import RequestProject.CombHurewicz1Pres
import RequestProject.Tac


/-! The actual normalized attaching-circle fundamental chain reads the
exponent vector in the subdivided rose. The rose coefficient realization
is injective and consists of genuine one-cycles. No genus modules or
topological classification hypotheses are used. Pending Lean verification. -/

noncomputable section
bwd

namespace FiniteChains.PresModel
open Comb
open scoped Classical
universe u
variable {A J : Type u}

def roseIntegerBaseEdge (a : A) (b : Bool) : StrictOrdEdge (Rose A) :=
  ⟨(Rose.base, Rose.edg a b), by tauto⟩

def roseIntegerMidEdge (a : A) (b : Bool) : StrictOrdEdge (Rose A) :=
  ⟨(Rose.mid a, Rose.edg a b), by tauto⟩

def roseIntegerGeneratorChain (a : A) : StrictOrdEdge (Rose A) →₀ ℤ :=
  Finsupp.single (roseIntegerBaseEdge a false) 1 -
    Finsupp.single (roseIntegerMidEdge a false) 1 +
    Finsupp.single (roseIntegerMidEdge a true) 1 -
    Finsupp.single (roseIntegerBaseEdge a true) 1

def roseIntegerRealize : (A →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (Rose A) →₀ ℤ) :=
  Finsupp.linearCombination ℤ roseIntegerGeneratorChain

theorem roseIntegerGeneratorChain_selected (a b : A) :
    roseIntegerGeneratorChain a (roseIntegerMidEdge b true) = if a = b then 1 else 0 := by
  classical
  have hb (s : Bool) : roseIntegerBaseEdge a s ≠ roseIntegerMidEdge b true := by
    intro h
    have he := congrArg (·.val.1) h
    tauto
  have hm : roseIntegerMidEdge a false ≠ roseIntegerMidEdge b true := by
    intro h
    have he := congrArg (·.val.2) h
    cases he
  have he : roseIntegerMidEdge a true = roseIntegerMidEdge b true ↔ a = b := by
    constructor
    · intro h
      exact Rose.mid.inj (congrArg (·.val.1) h)
    simp_all
  simp [roseIntegerGeneratorChain, Finsupp.single_apply, hb, hm, he]

theorem roseIntegerRealize_selected c (a : A) :
    roseIntegerRealize c (roseIntegerMidEdge a true) = c a := by
  classical
  lin_ind c b n =>
    simp only [roseIntegerRealize, Finsupp.linearCombination_single, Finsupp.smul_apply,
      roseIntegerGeneratorChain_selected, Finsupp.single_apply]
    simp

theorem roseIntegerRealize_injective : Function.Injective (roseIntegerRealize (A := A)) := by
  intro c d h
  apply Finsupp.ext
  intro a
  have he := congrArg (· (roseIntegerMidEdge a true)) h
  grind [roseIntegerRealize_selected]

theorem roseIntegerGeneratorChain_cycle a :
    Comb.bdry1 (strictOrderCx (Rose A)) (roseIntegerGeneratorChain a) = 0 := by
  simp [roseIntegerGeneratorChain, map_sub, map_add, Comb.bdry1_single (X := strictOrderCx (Rose A)),
    Finsupp.linearCombination_single, one_smul]
  change (Finsupp.single (Rose.edg a false) 1 - Finsupp.single Rose.base 1) -
      (Finsupp.single (Rose.edg a false) 1 - Finsupp.single (Rose.mid a) 1) +
      (Finsupp.single (Rose.edg a true) 1 - Finsupp.single (Rose.mid a) 1) -
      (Finsupp.single (Rose.edg a true) 1 - Finsupp.single Rose.base 1) = 0
  abel

theorem roseIntegerRealize_cycle c :
    Comb.bdry1 (strictOrderCx (Rose A)) (roseIntegerRealize c) = 0 := by
  lin_ind c a n =>
    simp [roseIntegerRealize, Finsupp.linearCombination_single, map_smul, roseIntegerGeneratorChain_cycle, smul_zero]

theorem mapOne_single_of_endpoints {P Q} [PartialOrder P] [PartialOrder Q]
    f hf (e : StrictOrdEdge P) (d : StrictOrdEdge Q)
    (he : (f e.val.1, f e.val.2) = d.val) :
    StrictNormalized.mapOne f hf (Finsupp.single e 1) = Finsupp.single d 1 := by
  rwd [StrictNormalized.mapOne_single, one_smul]
  have hn : f e.val.1 ≠ f e.val.2 := by
    grind
  unfold normalizeOrdEdge
  simp_all

variable (w : J → List (A × Bool)) (j : J)

theorem relatorCircleLetterChain_exponent (k : Fin (w j).length) :
    StrictNormalized.mapOne (fun x : RelatorCircle w j => aFun w x.val)
      ((aFun_monotone w).comp (fun _ _ h => h)) (relatorCircleLetterChain w j k) =
        if (w j)[k.val].2 then roseIntegerGeneratorChain (w j)[k.val].1
          else -roseIntegerGeneratorChain (w j)[k.val].1 := by
  let f := fun x : RelatorCircle w j => aFun w x.val
  let hf : Monotone f := (aFun_monotone w).comp (fun _ _ h => h)
  have hp := List.getElem?_eq_getElem k.isLt
  have hmid :=
    aFun_pt_cmid_of_get w hp
  have hL :=
    aFun_pt_cedgL_of_get w hp
  have hR :=
    aFun_pt_cedgR_of_get w hp
  have h₀ := mapOne_single_of_endpoints f hf (relatorCircleEdge0 w j k)
    (roseIntegerBaseEdge (w j)[k.val].1 (!(w j)[k.val].2)) (Prod.ext rfl hL)
  have h₁ := mapOne_single_of_endpoints f hf (relatorCircleEdge1 w j k)
    (roseIntegerMidEdge (w j)[k.val].1 (!(w j)[k.val].2)) (Prod.ext hmid hL)
  have h₂ := mapOne_single_of_endpoints f hf (relatorCircleEdge2 w j k)
    (roseIntegerMidEdge (w j)[k.val].1 (w j)[k.val].2) (Prod.ext hmid hR)
  have h₃ := mapOne_single_of_endpoints f hf (relatorCircleEdge3 w j k)
    (roseIntegerBaseEdge (w j)[k.val].1 (w j)[k.val].2) (Prod.ext rfl hR)
  rwd [relatorCircleLetterChain, map_sub, map_add, map_sub, h₀, h₁, h₂, h₃]
  cases (w j)[k.val].2 <;> simp only [Bool.not_false, Bool.not_true,
    Bool.false_eq_true, if_false, if_true, roseIntegerGeneratorChain]
  abel

theorem pathChain_eq_sum_get (l : List (A × Bool)) :
    pathChain l = ∑ k : Fin l.length,
      if l[k.val].2 then Finsupp.single l[k.val].1 (1 : ℤ) else -Finsupp.single l[k.val].1 1 := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp_all [pathChain_cons, Fin.sum_univ_succ]

theorem expVec_mk_eq_pathChain (l : List (A × Bool)) :
    FiniteChains.expVec (FreeGroup.mk l) = pathChain l := by
  classical
  exact congrArg Multiplicative.toAdd (Comb.expVec_pathChain l)

/-- Exact exponent-vector formula for the normalized image of the genuine
attaching-circle fundamental chain; valid also for the empty circle. -/
theorem relatorCircleFundamentalChain_exponent :
    StrictNormalized.mapOne (fun x : RelatorCircle w j => aFun w x.val)
      ((aFun_monotone w).comp (fun _ _ h => h)) (relatorCircleFundamentalChain w j) =
        roseIntegerRealize (FiniteChains.expVec (FreeGroup.mk (w j))) := by
  rwd [relatorCircleFundamentalChain, map_sum]
  simp_rw [relatorCircleLetterChain_exponent]
  rwd [expVec_mk_eq_pathChain, pathChain_eq_sum_get, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  cases (w j)[k.val].2 <;>
    simp only [Bool.false_eq_true, if_false, if_true, map_neg,
      roseIntegerRealize, Finsupp.linearCombination_single, one_smul]
