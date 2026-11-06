module

public import RequestProject.FiniteCycleWordComparison
public import RequestProject.OrderRoseRealizationHomeomorph
public import RequestProject.PresPosetAlpha

@[expose] public section

noncomputable section
open scoped Classical unitInterval Topology
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb RelativeAttachment ContinuousEdgeWords ClassicalGraphModel

variable {A J : Type}

def roseGeneratorWord (a : A) : List ((orderCx (Rose A)).E × Bool) :=
  [ordPos (Rose.base_le_edg a false), ordNeg (Rose.mid_le_edg a false),
    ordPos (Rose.mid_le_edg a true), ordNeg (Rose.base_le_edg a true)]

theorem roseGeneratorWord_valid (a : A) :
    IsPath (orderCx (Rose A)).src (orderCx (Rose A)).tgt (roseGeneratorWord a) .base .base :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def roseLetterWord (p : A × Bool) : List ((orderCx (Rose A)).E × Bool) :=
  if p.2 then roseGeneratorWord p.1 else revPath (X := orderCx (Rose A)) (roseGeneratorWord p.1)

def roseWord (l : List (A × Bool)) : List ((orderCx (Rose A)).E × Bool) := l.flatMap roseLetterWord

theorem roseLetterWord_valid (p : A × Bool) :
    IsPath (orderCx (Rose A)).src (orderCx (Rose A)).tgt (roseLetterWord p) .base .base := by
  rcases p with ⟨a, _ | _⟩
  exacts [isPath_revPath (roseGeneratorWord_valid a), roseGeneratorWord_valid a]

theorem roseWord_valid (l : List (A × Bool)) :
    IsPath (orderCx (Rose A)).src (orderCx (Rose A)).tgt (roseWord l) .base .base := by
  induction l with
  | nil => rfl
  | cons p _ ih => exact (roseLetterWord_valid p).append ih

def roseGeneratorPath (a : A) : Path (orderRoseBase A) (orderRoseBase A) :=
  roseFourCycle.mappedLoop (roseCopy a) (roseCopy a).monotone

theorem roseGeneratorPath_homotopic_word (a : A) :
    (roseGeneratorPath a).Homotopic (affineOrderWordPath (roseGeneratorWord a) (roseGeneratorWord_valid a)) := by
  let g : Fin 4 → (orderCx (Rose A)).E × Bool :=
    ![ordPos (Rose.base_le_edg a false), ordNeg (Rose.mid_le_edg a false),
      ordPos (Rose.mid_le_edg a true), ordNeg (Rose.base_le_edg a true)]
  have H := roseFourCycle.mappedLoop_homotopic_word (roseCopy a) (roseCopy a).monotone g
    (fun i => by fin_cases i <;> rfl) (fun i => by fin_cases i <;> rfl) rfl
  have hg : List.ofFn g = roseGeneratorWord a := by simp [g, roseGeneratorWord, List.ofFn_succ]
  simpa only [hg, roseGeneratorPath, roseFourCycle, orderRoseBase] using H

def orderRoseRead : List (A × Bool) → Path (orderRoseBase A) (orderRoseBase A)
  | [] => Path.refl _
  | (a, b) :: l => (if b then roseGeneratorPath a else (roseGeneratorPath a).symm).trans (orderRoseRead l)

theorem roseWord_homotopic_read (l : List (A × Bool)) :
    (affineOrderWordPath (roseWord l) (roseWord_valid l)).Homotopic (orderRoseRead l) := by
  induction l with
  | nil => exact Path.Homotopic.refl _
  | cons p l ih =>
    refine (realize_append (orderCx (Rose A)).src (orderCx (Rose A)).tgt
      (orderNerveRealizationVertex (P := Rose A))
      (fun e => orderNerveAffineEdgePath (P := Rose A) e.property)
      (roseLetterWord p) (roseWord l) (roseLetterWord_valid p) (roseWord_valid l)).symm.trans
      (Path.Homotopic.hcomp ?_ ih)
    rcases p with ⟨a, _ | _⟩
    · exact (realize_revPath (K := orderCx (Rose A)) (orderNerveRealizationVertex (P := Rose A))
        (fun e => orderNerveAffineEdgePath (P := Rose A) e.property) (roseGeneratorWord a)
        (roseGeneratorWord_valid a)).symm.trans (roseGeneratorPath_homotopic_word a).symm.symm₂
    · exact (roseGeneratorPath_homotopic_word a).symm

def classicalRoseRead : List (A × Bool) → Path (roseVertex A) (roseVertex A)
  | [] => Path.refl _
  | (a, b) :: l =>
      (if b then graphEdgePath (roseAttaching A) a else (graphEdgePath (roseAttaching A) a).symm).trans
        (classicalRoseRead l)

theorem orderRoseRead_classical (l : List (A × Bool)) (t : I) :
    orderRoseRealizationHomeomorph A (orderRoseRead l t) = classicalRoseRead l t := by
  have hgen (a : A) (s : I) : roseGeneratorPath a s = roseCopyRealization a (orderRoseTraversal s) :=
    roseFourCycle.mappedLoop_apply (roseCopy a) (roseCopy a).monotone s
  induction l generalizing t with
  | nil => exact orderRoseRealizationHomeomorph_base A
  | cons p l ih =>
    rcases p with ⟨a, b⟩
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [orderRoseRead, classicalRoseRead, Path.trans_apply, dif_pos ht]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Path.symm_apply, Function.comp_apply,
        hgen, orderRoseRealizationHomeomorph_interval] <;> rfl
    · simp only [orderRoseRead, classicalRoseRead, Path.trans_apply, dif_neg ht]
      exact ih _

theorem classicalRoseRead_eq_realize (l : List (A × Bool))
    (hl : IsPath (graphSrc (roseAttaching A)) (graphTgt (roseAttaching A)) l PUnit.unit PUnit.unit) :
    classicalRoseRead l = realize (graphSrc (roseAttaching A)) (graphTgt (roseAttaching A))
      (old (roseAttaching A) (boundaryFamilyInclusion A (Fin 1 → ℝ)))
      (graphEdgePath (roseAttaching A)) l hl := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨a, _ | _⟩ <;> simp only [classicalRoseRead, Bool.false_eq_true, ↓reduceIte,
      realize, germPath, Path.cast_rfl_rfl] <;> (congr 1; exact ih _)

variable (w : J → List (A × Bool))

theorem mapPath_aFun_circLoop (j : J) :
    mapPath (orderCxMap (aFun w) (aFun_monotone w)) (circLoop w j) = roseWord (w j) := by
  have hseg {k : ℕ} (hk : k < (w j).length) :
      mapPath (orderCxMap (aFun w) (aFun_monotone w)) (segAt w j k) = roseLetterWord (w j)[k] := by
    have hp : (w j)[k]? = some (w j)[k] := List.getElem?_eq_getElem hk
    have hmid := aFun_pt_cmid_of_get w hp
    have hL := aFun_pt_cedgL_of_get w hp
    have hR := aFun_pt_cedgR_of_get w hp
    rw [segAt, dif_pos hk]
    change [ordPos ((aFun_monotone w) (TCirc.cor_le_cedgL w hk)),
      ordNeg ((aFun_monotone w) (TCirc.cmid_le_cedgL w hk)),
      ordPos ((aFun_monotone w) (TCirc.cmid_le_cedgR w hk)),
      ordNeg ((aFun_monotone w) (TCirc.cor_csucc_le_cedgR w hk))] = _
    rcases he : (w j)[k] with ⟨a, _ | _⟩ <;> rw [he] at hmid hL hR
    · change _ = [ordPos (Rose.base_le_edg a true), ordNeg (Rose.mid_le_edg a true),
        ordPos (Rose.mid_le_edg a false), ordNeg (Rose.base_le_edg a false)]
      exact List.cons_eq_cons.mpr ⟨ordPos_congr rfl hL _ _, List.cons_eq_cons.mpr
        ⟨ordNeg_congr hmid hL _ _, List.cons_eq_cons.mpr ⟨ordPos_congr hmid hR _ _,
          List.cons_eq_cons.mpr ⟨ordNeg_congr rfl hR _ _, rfl⟩⟩⟩⟩
    · change _ = roseGeneratorWord a
      exact List.cons_eq_cons.mpr ⟨ordPos_congr rfl hL _ _, List.cons_eq_cons.mpr
        ⟨ordNeg_congr hmid hL _ _, List.cons_eq_cons.mpr ⟨ordPos_congr hmid hR _ _,
          List.cons_eq_cons.mpr ⟨ordNeg_congr rfl hR _ _, rfl⟩⟩⟩⟩
  have hpath : ∀ {m : ℕ}, m ≤ (w j).length →
      mapPath (orderCxMap (aFun w) (aFun_monotone w)) (circPath w j m) = roseWord ((w j).take m) := by
    intro m; induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have hlt : m < (w j).length := by omega
      change mapPath _ (circPath w j m ++ segAt w j m) = _
      rw [mapPath_append, ih (Nat.le_of_lt hlt), hseg hlt,
        show (w j).take (m + 1) = (w j).take m ++ [(w j)[m]] by
          rw [List.take_add_one, List.getElem?_eq_getElem hlt]; rfl]
      simp only [roseWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simpa only [List.take_length, circLoop] using hpath le_rfl

end FiniteChains.PresModel
