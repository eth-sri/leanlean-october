module
public import proofs.RAFCriticalWindowQuantitative.SmallOpenness

/-! Certified truncation rates and total interval evaluation including the zero endpoint. -/

@[expose] public section

namespace RAFCriticalWindowQuantitative
open MeasureTheory HordijkSteelThreshold unitInterval

abbrev Encloses (v : ℚ × ℚ) (x : ℝ) (ε : ℚ) := (v.1 : ℝ) ≤ x ∧ x ≤ (v.2 : ℝ) ∧ v.2-v.1 < ε

variable (M : Model) (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε)

namespace Model

def cap := let L := M.seedLength ⟨q,hq,hq1⟩ (precisionIndex ε); recordCap L (recordIndex q hq hq1 L ε hε)

theorem uniform (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) :
    (M.escapeProb a (M.cap q hq hq1 ε hε)).toReal ≤ (M.survival a).toReal + ε/2 := by
  let m := precisionIndex ε
  let L := M.seedLength ⟨q,hq,hq1⟩ m
  let r := recordIndex q hq hq1 L ε hε
  have spec : geometricTest _ _ _ r := Nat.find_spec (p := geometricTest _ _ _) _
  have recBound : (2:ENNReal)^(L+1)*(missRate a (L+1))^r ≤ ENNReal.ofReal ((ε:ℝ)/4) := by
    simpa using geometric_budget (c := 2^(L+1)) (e := ε/4) hq.le (show (q:ℝ) ≤ a from ha) (by simpa using spec.2)
  have precision : (m:ENNReal)⁻¹ ≤ ENNReal.ofReal ((ε:ℝ)/4) := by
    rw [ENNReal.inv_le_iff_inv_le,←ENNReal.ofReal_inv_of_pos (by positivity),inv_div,←ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast (Nat.le_ceil (4/ε)).trans (by dsimp [m,precisionIndex]; push_cast; linarith : (⌈4/ε⌉₊:ℚ) ≤ m)
  have h := (M.truncation ⟨q,hq,hq1⟩ m a ha r).trans
    (add_le_add (add_le_add_right precision _) recBound)
  rw [add_assoc,←ENNReal.ofReal_add (by positivity) (by positivity)] at h
  rw [show (ε:ℝ)/4+ε/4 = ε/2 by ring] at h
  have hs : M.survival a ≠ ⊤ := by simp [M.survival_eq]
  change (M.escapeProb a (recordCap L r)).toReal ≤ _
  simpa [ENNReal.toReal_ofReal (by positivity : 0 ≤ (ε:ℝ)/2)] using ENNReal.toReal_le_add h hs (by simp)

def interval := let e := M.escapeEval q (M.cap q hq hq1 ε hε-2); (e-ε/2,e)

lemma certified : Encloses (M.interval q hq hq1 ε hε) (M.survival (rationalParameter q hq.le hq1)).toReal ε := by
  let K := M.cap q hq hq1 ε hε
  let a := rationalParameter q hq.le hq1
  let e := M.escapeEval q (K-2)
  have he : (e : ℝ) = (M.escapeProb a K).toReal := by
    rw [M.escapeEval_eq q a rfl, Nat.sub_add_cancel (show 2 ≤ K from recordCap_ge_two _ _)]
  have hu : (M.survival a).toReal ≤ (e : ℝ) := he ▸ ENNReal.toReal_mono (measure_ne_top _ _) (M.survival_le a K)
  have hl : (M.escapeProb a K).toReal ≤ _ := M.uniform q hq hq1 ε hε a le_rfl
  change ((e-ε/2 : ℚ) : ℝ) ≤ _ ∧ _ ≤ (e : ℝ) ∧ e-(e-ε/2) < ε
  aesop

end Model
def splitEvaluationCap : ℕ :=
  let L := 10*seedIndex q hq hq1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)
def quotientEvaluationCap : ℕ :=
  let hhalf : 0 < q/2 := rationalHalf_pos q hq
  let hhalf1 : q/2 ≤ 1 := rationalHalf_le_one q hq hq1
  let L := 10*seedIndex (q/2) hhalf hhalf1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)
def splitCertifiedInterval : ℚ × ℚ :=
  let e := splitEscapeEval q (splitEvaluationCap q hq hq1 ε hε-2)
  (e-ε/2,e)

def quotientCertifiedInterval : ℚ × ℚ :=
  let e := quotientEscapeEval q (quotientEvaluationCap q hq hq1 ε hε-2)
  (e-ε/2,e)

variable (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε)

def splitTotalInterval : ℚ × ℚ :=
  if h : q = 0 then (0,0) else splitCertifiedInterval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε
def quotientTotalInterval : ℚ × ℚ :=
  if h : q = 0 then (0,0) else quotientCertifiedInterval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

namespace Model

def total := if h : q = 0 then (0,0) else M.interval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

theorem total_correct : Encloses (M.total q hq hq1 ε hε) (M.survival (rationalParameter q hq hq1)).toReal ε := by
  unfold total
  split
  · subst q
    have h : rationalParameter 0 hq hq1 = 0 := by simp [rationalParameter]
    rw [h]
    have hz := M.sparse_real 0 1
    aesop
  · exact M.certified ..
end Model
end RAFCriticalWindowQuantitative
