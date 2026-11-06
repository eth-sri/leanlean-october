module
public import NearlyMinimax.HistoryCanonicalDeletion
public import NearlyMinimax.HighCenteredRowUnion
@[expose] public section
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Recursion
variable {J X E C I : Type*} [DecidableEq J]
def affineRawHistory (patch : J → Set X) (slope intercept : J → E → X → ℝ)
    (response : J → E → C → C) (labels : I → J) (indices : List I)
    (marks : I → E) (initial : (X → ℝ) × (J → C)) : (X → ℝ) × (J → C) :=
  indices.foldl (fun state i => rawPatchUpdate (labels i) (patch (labels i))
    (slope (labels i) (marks i)) (intercept (labels i) (marks i))
    (response (labels i) (marks i)) state) initial
theorem affineRawHistory_density_eq_outside_label
    (patch : J → Set X) (slope intercept : J → E → X → ℝ)
    (response : J → E → C → C) (labels : I → J) (indices : List I)
    (marks marks' : I → E) (j : J) (hm : ∀ i, labels i ≠ j → marks i = marks' i)
    (initial initial' : (X → ℝ) × (J → C)) (x : X) (hx : x ∉ patch j)
    (hi : initial.1 x = initial'.1 x) :
    (affineRawHistory patch slope intercept response labels indices marks initial).1 x =
      (affineRawHistory patch slope intercept response labels indices marks' initial').1 x := by
  induction indices generalizing initial initial' with
  | nil => exact hi
  | cons i indices ih =>
    apply ih
    dsimp only
    by_cases hlabel : labels i = j
    · simp only [rawPatchUpdate, affinePatchUpdate, hlabel, ite_eq_right hx]
      exact hi
    · rw [hm i hlabel]
      change (if x ∈ patch (labels i) then
        slope (labels i) (marks' i) x * initial.1 x + intercept (labels i) (marks' i) x
        else initial.1 x) = (if x ∈ patch (labels i) then
        slope (labels i) (marks' i) x * initial'.1 x + intercept (labels i) (marks' i) x
        else initial'.1 x)
      rw [hi]
theorem affineRawHistory_density_interval (patch : J → Set X)
    (slope intercept : J → E → X → ℝ) (response : J → E → C → C)
    (labels : I → J) (indices : List I) (marks : I → E)
    (a b : ℝ)
    (hlegal : ∀ j e x v, v ∈ Icc a b → slope j e x * v + intercept j e x ∈ Icc a b)
    (initial : (X → ℝ) × (J → C)) (hi : ∀ x, initial.1 x ∈ Icc a b) :
    ∀ x, (affineRawHistory patch slope intercept response labels indices marks initial).1 x ∈ Icc a b := by
  induction indices generalizing initial with
  | nil => exact hi
  | cons i indices ih =>
    apply ih
    intro x
    dsimp only
    change (if x ∈ patch (labels i) then slope (labels i) (marks i) x * initial.1 x +
      intercept (labels i) (marks i) x else initial.1 x) ∈ Icc a b
    split_ifs
    · exact hlegal _ _ _ _ (hi x)
    · exact hi x
theorem affineRawHistory_density_measurable [MeasurableSpace X]
    (patch ) (hpatch : ∀ j, MeasurableSet (patch j))
    (slope intercept )
    (hSlope : ∀ j e, Measurable (slope j e)) (hIntercept : ∀ j e, Measurable (intercept j e))
    (response : J → E → C → C) (labels : I → J) (indices : List I) (marks : I → E)
    (initial : (X → ℝ) × (J → C)) (hi : Measurable initial.1) :
    Measurable (affineRawHistory patch slope intercept response labels indices marks initial).1 := by
  induction indices generalizing initial with
  | nil => exact hi
  | cons i indices ih =>
    apply ih
    change Measurable (fun x => if x ∈ patch (labels i) then
      slope (labels i) (marks i) x * initial.1 x + intercept (labels i) (marks i) x else initial.1 x)
    exact Measurable.ite (hpatch _) (((hSlope _ _).mul hi).add (hIntercept _ _)) hi
end Recursion
theorem integral_mass_difference_le_patch  [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (P : Set X) (hP : MeasurableSet P)
    (p p' ) (hpm : Measurable p) (hp'm : Measurable p')
    (a b ) (hab : a ≤ b) (hp : ∀ x, p x ∈ Icc a b) (hp' : ∀ x, p' x ∈ Icc a b)
    (hsupport : ∀ x, x ∉ P → p x = p' x) :
    |(∫ x, p x ∂μ) - ∫ x, p' x ∂μ| ≤ μ.real P * (b - a) := by
  let K : ℝ := max |a| |b|
  have hbound (q : X → ℝ) (hq : ∀ x, q x ∈ Icc a b) (x : X) : ‖q x‖ ≤ K := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · have : |a| ≤ K := le_max_left _ _
      linarith [(hq x).1, neg_abs_le a]
    · have hKb : |b| ≤ K := le_max_right _ _
      exact (hq x).2.trans ((le_abs_self b).trans hKb)
  have hi : Integrable p μ := (integrable_const K).mono' hpm.aestronglyMeasurable
    (Filter.Eventually.of_forall (hbound p hp))
  have hi' : Integrable p' μ := (integrable_const K).mono' hp'm.aestronglyMeasurable
    (Filter.Eventually.of_forall (hbound p' hp'))
  have hdiff (x : X) : |p x - p' x| ≤ P.indicator (fun _ => b-a) x := by
    by_cases hx : x ∈ P
    · rw [Set.indicator_of_mem hx]
      apply abs_le.mpr
      constructor <;> linarith [(hp x).1, (hp x).2, (hp' x).1, (hp' x).2]
    · rw [Set.indicator_of_notMem hx, hsupport x hx, sub_self, abs_zero]
  rw [← integral_sub hi hi']
  calc
    _ ≤ ∫ x, |p x-p' x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => p x-p' x)
    _ ≤ ∫ x, P.indicator (fun _ => b-a) x ∂μ :=
      integral_mono (hi.sub hi').abs ((integrable_const (b-a)).indicator hP) hdiff
    _ = _ := by rw [integral_indicator_const _ hP, smul_eq_mul]
theorem highAffineRawHistory_mass_block_oscillation {E C : Type*}
    (d k n : ℕ) [NeZero k] (hk : 2 ≤ k)
    (slope intercept : HighWindowLabels d k → E → Covariate d → ℝ)
    (hSlope : ∀ j e, Measurable (slope j e)) (hIntercept : ∀ j e, Measurable (intercept j e))
    (response : HighWindowLabels d k → E → C → C)
    (labels : Fin n → HighWindowLabels d k) (indices : List (Fin n))
    (marks marks' : Fin n → E) (j : HighWindowLabels d k)
    (hm : ∀ i, labels i ≠ j → marks i = marks' i)
    (a b : ℝ) (hab : a ≤ b)
    (hlegal : ∀ l e x v, v ∈ Icc a b → slope l e x * v + intercept l e x ∈ Icc a b)
    (initial : (Covariate d → ℝ) × (HighWindowLabels d k → C))
    (him : Measurable initial.1) (hi : ∀ x, initial.1 x ∈ Icc a b) :
    |(∫ x, (affineRawHistory (highTorusPatch d k) slope intercept response labels indices marks initial).1 x
        ∂cubeVolume d) -
      ∫ x, (affineRawHistory (highTorusPatch d k) slope intercept response labels indices marks' initial).1 x
        ∂cubeVolume d| ≤ (2 / ↑k)^d * (b-a) := by
  let _ := cubeVolume_isProbability d
  apply (integral_mass_difference_le_patch (cubeVolume d) (highTorusPatch d k j)
    (highTorusPatch_measurableSet d k j) _ _
    (affineRawHistory_density_measurable (highTorusPatch d k) (highTorusPatch_measurableSet d k)
      slope intercept hSlope hIntercept response labels indices marks initial him)
    (affineRawHistory_density_measurable (highTorusPatch d k) (highTorusPatch_measurableSet d k)
      slope intercept hSlope hIntercept response labels indices marks' initial him)
    a b hab
    (affineRawHistory_density_interval (highTorusPatch d k) slope intercept response labels indices
      marks a b hlegal initial hi)
    (affineRawHistory_density_interval (highTorusPatch d k) slope intercept response labels indices
      marks' a b hlegal initial hi)
    (fun x hx => affineRawHistory_density_eq_outside_label (highTorusPatch d k) slope intercept response
      labels indices marks marks' j hm initial initial x hx rfl)).trans
  have h_highTorusPatch_real_volume_le : (cubeVolume d).real (highTorusPatch d k j) ≤ (2 / ↑k)^d := by
    have : ↑0 < k := by exact_mod_cast (by omega : 0 < k)
    have h_highTorusPatch_volume_le : cubeVolume d (highTorusPatch d k j) ≤ ENNReal.ofReal (2 / ↑k) ^ d := by
      rw [cubeVolume, Measure.restrict_apply (highTorusPatch_measurableSet d k j)]
      have h_highPatchCoordinate_volume_le (hk : 0 < k) (j) : volume (highPatchCoordinate k j) ≤ ENNReal.ofReal (2 / k) := by
        unfold highPatchCoordinate
        split_ifs
        · calc
            _ ≤ volume (Icc (0 : ℝ) (1 / k)) + volume (Icc (1 - 1 / (k : ℝ)) 1) :=
              measure_union_le _ _
            _ = ENNReal.ofReal (1 / k) + ENNReal.ofReal (1 / k) := by
              rw [Real.volume_Icc, Real.volume_Icc]
              congr 1 <;> congr 1 <;> ring
            _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
        · rw [Real.volume_Icc]
          apply ENNReal.ofReal_le_ofReal
          ring_nf
          exact le_rfl
      have h_highTorusPatch_cube_subset : highTorusPatch d k j ∩ unitCube d ⊆
          Set.pi Set.univ (fun r => highPatchCoordinate k (j r)) := by
        intro x hx r hr
        obtain ⟨z, hz, hclose⟩ := hx.1
        have h_highPatchCoordinate_contains_lift (j : ZMod k) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (z : ℤ) (hz : (z : ZMod k) = j) (hclose : |(k : ℝ) * x - z| < 1) : x ∈ highPatchCoordinate k j := by
          have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
          have : (j.val : ℤ) < k := by exact_mod_cast ZMod.val_lt j
          obtain ⟨q, hq⟩ := (ZMod.intCast_eq_iff k z j).mp hz
          have : 0 ≤ z ∧ z ≤ (k : ℤ) := by
            have h := abs_lt.mp hclose
            have hzL : (-1 : ℝ) < z := by nlinarith [mul_nonneg hkR.le hx.1]
            have hzU : (z : ℝ) < k + 1 := by nlinarith [mul_le_mul_of_nonneg_left hx.2 hkR.le]
            have : (-1 : ℤ) < z := by exact_mod_cast hzL
            have : z < ↑k + 1 := by exact_mod_cast hzU
            omega
          have hqs : q = 0 ∨ q = 1 := by
            have hj0 : (0 : ℤ) ≤ j.val := Int.natCast_nonneg _
            have : ↑0 < k := by exact_mod_cast (by omega : 0 < k)
            have : 0 ≤ q := by
              by_contra h
              have : q ≤ -1 := by omega
              nlinarith
            have : q ≤ 1 := by
              by_contra h
              have : 2 ≤ q := by omega
              nlinarith
            omega
          have := abs_lt.mp hclose
          rcases hqs with hq0 | hq1
          · have hzval : z = (j.val : ℤ) := by simpa only [hq0, mul_zero, add_zero] using hq
            have hzvalR : (z : ℝ) = j.val := by exact_mod_cast hzval
            unfold highPatchCoordinate
            split_ifs with hj
            · apply Or.inl
              rw [hj] at hzvalR
              simp only [ZMod.val_zero, Nat.cast_zero] at hzvalR
              refine ⟨hx.1, ?_⟩
              apply (le_div_iff₀ hkR).mpr
              nlinarith
            · constructor
              · apply (div_le_iff₀ hkR).mpr
                nlinarith
              · apply (le_div_iff₀ hkR).mpr
                nlinarith
          · have hjval : j.val = 0 := by rw [hq1, mul_one] at hq; omega
            have hv := ZMod.natCast_zmod_val j
            have : (z : ℝ) = k := by
              have hz' : z = (k : ℤ) := by simp only [hjval, Nat.cast_zero, hq1, mul_one, zero_add] at hq; exact hq
              exact_mod_cast hz'
            unfold highPatchCoordinate
            rw [ite_eq_left (by rw [hjval, Nat.cast_zero] at hv; exact hv.symm)]
            apply Or.inr
            refine ⟨?_, hx.2⟩
            have hr : ((k : ℝ) - 1) / k ≤ x := (div_le_iff₀ hkR).mpr (by nlinarith)
            convert hr using 1
            field_simp
        exact h_highPatchCoordinate_contains_lift (j r) (x r) (hx.2 r) (z r) (hz r) (hclose r)
      calc
        _ ≤ volume (Set.pi Set.univ (fun r => highPatchCoordinate k (j r))) :=
          measure_mono h_highTorusPatch_cube_subset
        _ = ∏ r, volume (highPatchCoordinate k (j r)) := volume_pi_pi _
        _ ≤ ∏ _r : Fin d, ENNReal.ofReal (2 / ↑k) :=
          Finset.prod_le_prod (fun r _ => (h_highPatchCoordinate_volume_le (by omega) (j r)))
        _ = _ := by simp
    have h := ENNReal.toReal_mono (by finiteness)
      h_highTorusPatch_volume_le
    simpa only [measureReal_def, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 / (k : ℝ))] using h
  exact mul_le_mul_of_nonneg_right h_highTorusPatch_real_volume_le (sub_nonneg.mpr hab)
def highAffineMarkedMass  (d k ) [NeZero k]
    [LinearOrder (HighWindowLabels d k)] (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)
    (slope intercept : HighWindowLabels d k → E → Covariate d → ℝ)
    (response : HighWindowLabels d k → E → C → C)
    (initial : (Covariate d → ℝ) × (HighWindowLabels d k → C))
    (h : HistoryMarked dependent E) : ℝ :=
  ∫ x, (historyMarkedRawState dependent
    (fun j e state => rawPatchUpdate j (highTorusPatch d k j) (slope j e) (intercept j e)
      (response j e) state) initial h).1 x ∂cubeVolume d
theorem highAffineMarkedMass_block_oscillation 
    (d k ) [NeZero k] [LinearOrder (HighWindowLabels d k)] (hk : 2 ≤ k)
    (dependent )
    (slope intercept : HighWindowLabels d k → E → Covariate d → ℝ)
    (hSlope : ∀ j e, Measurable (slope j e)) (hIntercept : ∀ j e, Measurable (intercept j e))
    (response : HighWindowLabels d k → E → C → C)
    (a b : ℝ) (hab : a ≤ b)
    (hlegal : ∀ l e x v, v ∈ Icc a b → slope l e x * v + intercept l e x ∈ Icc a b)
    (initial : (Covariate d → ℝ) × (HighWindowLabels d k → C))
    (him : Measurable initial.1) (hi : ∀ x, initial.1 x ∈ Icc a b)
    (g : HistoryShape (fun l j => ¬ dependent l j))
    (marks marks' : Fin (historyShapeLength dependent g) → E) (j : HighWindowLabels d k)
    (hm : ∀ i, historyShapeCanonicalLabels dependent g i ≠ j → marks i = marks' i) :
    |highAffineMarkedMass d k dependent slope intercept response initial ⟨g, marks⟩ -
      highAffineMarkedMass d k dependent slope intercept response initial ⟨g, marks'⟩| ≤
        (2 / ↑k)^d * (b-a) := by
  exact highAffineRawHistory_mass_block_oscillation d k (historyShapeLength dependent g) hk
    slope intercept hSlope hIntercept response (historyShapeCanonicalLabels dependent g)
    (List.ofFn (fun i => i)) marks marks' j hm
    a b hab hlegal initial him hi
def finiteAffineHistory  (slope offset : J → E → ℝ)
    (n ) (labels : Fin n → J) (marks : Fin n → E) : ℝ :=
  (List.ofFn (fun i => i)).foldl
    (fun value i => slope (labels i) (marks i) * value + offset (labels i) (marks i)) 1
theorem finiteAffineHistory_succ {J E : Type*} (slope offset : J → E → ℝ)
    (n : ℕ) (labels : Fin (n + 1) → J) (marks : Fin (n + 1) → E) :
    finiteAffineHistory slope offset (n + 1) labels marks =
      slope (labels (Fin.last n)) (marks (Fin.last n)) *
        finiteAffineHistory slope offset n (fun i => labels i.castSucc) (fun i => marks i.castSucc) +
      offset (labels (Fin.last n)) (marks (Fin.last n)) := by
  unfold finiteAffineHistory
  rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  congr 2
  have hh : (List.ofFn (fun i : Fin n => i.castSucc)) =
      (List.ofFn (fun i : Fin n => i)).map Fin.castSucc := by rw [List.map_ofFn]; rfl
  rw [hh, List.foldl_map]
theorem finiteAffineHistory_integral_one {J E : Type*} [MeasurableSpace E]
    (π ) [IsProbabilityMeasure π] (slope offset : J → E → ℝ)
    (hs : ∀ j, Integrable (slope j) π) (ho : ∀ j, Integrable (offset j) π)
    (hmean : ∀ j, (∫ e, slope j e ∂π) + (∫ e, offset j e ∂π) = 1)
    (n : ℕ) (labels : Fin n → J) :
    (∫ marks, finiteAffineHistory slope offset n labels marks
      ∂Measure.pi (fun _ : Fin n => π)) = 1 := by
  induction n with
  | zero => simp only [finiteAffineHistory, List.ofFn_zero, List.foldl_nil, integral_const,
      measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one]
  | succ n ih =>
    let j := labels (Fin.last n)
    rw [← (historyFiniteMarkAppendEquiv_preserving n π).integral_comp
      (historyFiniteMarkAppendEquiv n).measurableEmbedding]
    have he : (fun p =>
        finiteAffineHistory slope offset (n + 1) labels (historyFiniteMarkAppendEquiv n p)) =
        (fun p => slope j p.1 * (finiteAffineHistory slope offset n (fun i => labels i.castSucc)) p.2 + offset j p.1) := by
      funext ⟨fresh, marks⟩
      simp only [finiteAffineHistory_succ, historyFiniteMarkAppendEquiv_last,
        historyFiniteMarkAppendEquiv_old]
      rfl
    have h_finiteAffineHistory_integrable (n : ℕ) (labels : Fin n → J) : Integrable (finiteAffineHistory slope offset n labels) (Measure.pi (fun _ : Fin n => π)) := by
      induction n with
      | zero => exact integrable_const _
      | succ n ih =>
        let j := labels (Fin.last n)
        apply ((historyFiniteMarkAppendEquiv_preserving n π).integrable_comp_emb
          (historyFiniteMarkAppendEquiv n).measurableEmbedding).mp
        convert (((hs j).mul_prod (ih _)).add ((ho j).comp_fst _)) using 1
        funext ⟨fresh, marks⟩
        simp only [Function.comp_apply, finiteAffineHistory_succ,
          historyFiniteMarkAppendEquiv_last, historyFiniteMarkAppendEquiv_old]
        rfl
    rw [he, integral_add ((hs j).mul_prod (h_finiteAffineHistory_integrable n _))
      ((ho j).comp_fst _), integral_prod_mul, integral_fun_fst]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, ih, mul_one]
    exact hmean j
theorem affinePatchFold_density_eq {J X E V I : Type*} [DecidableEq J]
    (patch : J → Set X) (slope offset : J → E → X → ℝ)
    (response : J → E → V → V) (labels : I → J) (marks : I → E)
    (indices : List I) (initial : (X → ℝ) × (J → V)) (x : X) :
    (indices.foldl (fun θ i => rawPatchUpdate (labels i) (patch (labels i))
      (slope (labels i) (marks i)) (offset (labels i) (marks i))
      (response (labels i) (marks i)) θ) initial).1 x =
      indices.foldl (fun v i =>
        (if x ∈ patch (labels i) then slope (labels i) (marks i) x else 1) * v +
        (if x ∈ patch (labels i) then offset (labels i) (marks i) x else 0)) (initial.1 x) := by
  induction indices generalizing initial with
  | nil => rfl
  | cons i indices ih =>
    simp only [List.foldl_cons]
    rw [ih]
    by_cases hx : x ∈ patch (labels i) <;>
      simp only [rawPatchUpdate, affinePatchUpdate, hx, ite_true, ite_false, one_mul, add_zero]
theorem affinePatchFold_density_joint_measurable {J X E V : Type*} [DecidableEq J]
    [MeasurableSpace X] [MeasurableSpace E]
    (patch : J → Set X) (hpatch : ∀ j, MeasurableSet (patch j))
    (slope offset : J → E → X → ℝ)
    (hs : ∀ j, Measurable (fun ex : E × X => slope j ex.1 ex.2))
    (ho : ∀ j, Measurable (fun ex : E × X => offset j ex.1 ex.2))
    (response : J → E → V → V) (n : ℕ) (labels : Fin n → J) (indices : List (Fin n))
    (initial : (Fin n → E) → (X → ℝ) × (J → V))
    (hi : Measurable (fun mx : (Fin n → E) × X => (initial mx.1).1 mx.2)) :
    Measurable (fun mx : (Fin n → E) × X =>
      (indices.foldl (fun θ i => rawPatchUpdate (labels i) (patch (labels i))
        (slope (labels i) (mx.1 i)) (offset (labels i) (mx.1 i))
        (response (labels i) (mx.1 i)) θ) (initial mx.1)).1 mx.2) := by
  induction indices generalizing initial with
  | nil => exact hi
  | cons i indices ih =>
    simp only [List.foldl_cons]
    apply ih (fun marks => rawPatchUpdate (labels i) (patch (labels i))
      (slope (labels i) (marks i)) (offset (labels i) (marks i))
      (response (labels i) (marks i)) (initial marks))
    change Measurable (fun mx : (Fin n → E) × X =>
      if mx.2 ∈ patch (labels i) then slope (labels i) (mx.1 i) mx.2 *
        (initial mx.1).1 mx.2 + offset (labels i) (mx.1 i) mx.2 else (initial mx.1).1 mx.2)
    have hcoord : Measurable (fun mx : (Fin n → E) × X => (mx.1 i, mx.2)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
    exact Measurable.ite ((hpatch _).preimage measurable_snd)
      (((hs (labels i)).comp hcoord).mul hi |>.add ((ho (labels i)).comp hcoord)) hi
section Packet
variable {Z : Type*} [MeasurableSpace Z] (d k F m r D q : ℕ)
end Packet
theorem packetSum_borelSpace  [TopologicalSpace A] [TopologicalSpace B]
    [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B] : BorelSpace (A ⊕ B) := by
  constructor
  apply le_antisymm
  · intro s hs
    have hsec := measurableSet_sum_iff.mp hs
    let : MeasurableSpace (A ⊕ B) := borel (A ⊕ B)
    let : BorelSpace (A ⊕ B) := ⟨rfl⟩
    have he : s = Sum.inl '' (Sum.inl ⁻¹' s) ∪ Sum.inr '' (Sum.inr ⁻¹' s) := by
      ext x
      cases x <;> simp
    rw [he]
    exact (Topology.IsClosedEmbedding.inl.measurableEmbedding.measurableSet_image' hsec.1).union (Topology.IsClosedEmbedding.inr.measurableEmbedding.measurableSet_image' hsec.2)
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact measurableSet_sum_iff.mpr ⟨(hs.preimage continuous_inl).measurableSet,
      (hs.preimage continuous_inr).measurableSet⟩
section Canonical
variable {Z : Type*} [MeasurableSpace Z] (d k F m r D q : ℕ) [NeZero k]
  [LinearOrder (HighWindowLabels d k)]
  (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)
variable (σ : Measure Z) [IsFiniteMeasure σ] (a b C δ : ℝ)
  (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
  (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
  (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
  (ha : 0 < a) (hab : a < b) (hr : 1 ≤ r) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
  (radius width : ℝ) (hR : 0 < radius) (ha1 : a + radius ≤ 1) (hb1 : 1 + radius ≤ b)
  (hW : b - a ≤ width) (hδW : δ * width ≤ radius / 2)
  (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
  (hmB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
  (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1)
  (initial : HighRawState d k F) (hinit : ∀ x, initial.1 x = 1)
include hA hcost hpos ha hab hr hδ0 hδ1 hR ha1 hb1 hW hδW hB hinit
end Canonical
structure HighUnionRowData (d k F : ℕ) (I : Type*) (E : I → Type*)
    [∀ i, MeasurableSpace (E i)] where
  rowLaw : (i : I) → Measure (E i)
  rowMass : I → ℝ
  rowActivation : (i : I) → E i → ℝ
  rowIntercept : (i : I) → E i → ℝ
  rowSlope : HighWindowLabels d k → (i : I) → E i → Covariate d → ℝ
  rowVector : (i : I) → E i → HighFrameIndex d F → ℝ
  rowTime : (i : I) → E i → ℝ
abbrev HighUnionMark {I : Type*} (E : I → Type*) := (Sigma E) ⊕ Unit
theorem highUnionMark_standardBorel  [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)] :
    StandardBorelSpace (HighUnionMark E) := by
  letI : StandardBorelSpace (Sigma E) := (by letI := fun j => upgradeStandardBorel (E j); letI : BorelSpace (Sigma E) := historySigma_borelSpace; infer_instance)
  letI := upgradeStandardBorel (Sigma E)
  letI : BorelSpace ((Sigma E) ⊕ Unit) := packetSum_borelSpace
  infer_instance
section Reset
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] (R : HighUnionRowData d k F I E)
def highUnionLaw (δ : ℝ) : Measure (HighUnionMark E) :=
  highCenteredRowUnionLaw R.rowLaw R.rowMass δ
def highUnionActivation (δ : ℝ) : HighUnionMark E → ℝ :=
  highCenteredRowUnionActivation R.rowMass R.rowActivation δ
def highUnionIntercept (δ : ℝ) : HighUnionMark E → ℝ :=
  highCenteredRowUnionIntercept R.rowLaw R.rowMass R.rowIntercept δ
def highUnionSlope (j : HighWindowLabels d k) (e : HighUnionMark E) (x : Covariate d) : ℝ :=
  highCenteredRowUnionSlope (fun i e => R.rowSlope j i e x) e
def highUnionResponseVector : HighUnionMark E → HighFrameIndex d F → ℝ :=
  Sum.elim (fun e => R.rowVector e.1 e.2) (fun _ => 0)
def highUnionResponseTime : HighUnionMark E → ℝ :=
  Sum.elim (fun e => R.rowTime e.1 e.2) (fun _ => 0)
def highUnionResponseReset (e : HighUnionMark E) (c : HighFrameIndex d F → ℝ) :
    HighFrameIndex d F → ℝ :=
  coefficientReset c (highUnionResponseVector R e) (highUnionResponseTime R e)
def highUnionRawUpdate (δ : ℝ) (j : HighWindowLabels d k) (e : HighUnionMark E)
    (θ : HighRawState d k F) : HighRawState d k F :=
  rawPatchUpdate j (highTorusPatch d k j) (highUnionSlope R j e)
    (fun _ => highUnionIntercept R δ e) (highUnionResponseReset R e) θ
theorem highUnionLaw_probability [∀ i, IsProbabilityMeasure (R.rowLaw i)]
    (hMass : ∀ i, 0 ≤ R.rowMass i) (hTotal : 0 < highRowTotalMass R.rowMass)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : IsProbabilityMeasure (highUnionLaw R δ) :=
  (by letI := highRowReferenceUnion_probability R.rowLaw R.rowMass hMass hTotal; exact balancedReferenceLaw_probability _ δ hδ0 hδ1)
theorem highUnionActivation_measurable (hAct : ∀ i, Measurable (R.rowActivation i)) (δ ) :
    Measurable (highUnionActivation R δ) :=
  balancedActivation_measurable _ (highRowUnionActivation_measurable R.rowMass R.rowActivation hAct) δ
theorem highUnionActivation_centered (hMass : ∀ i, 0 ≤ R.rowMass i)
    (hAct : ∀ i, Measurable (R.rowActivation i))
    (hiAct : ∀ i, Integrable (R.rowActivation i) (R.rowLaw i))
    (hcAct : ∀ i, (∫ e, R.rowActivation i e ∂(R.rowLaw i)) = 0)
    (δ ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ e, highUnionActivation R δ e ∂highUnionLaw R δ) = 0 :=
  have h_balancedActivation_integral_zero {E} [MeasurableSpace E] (μ) (w : E → ℝ) (hw : Measurable w) (hwi : Integrable w μ) (hc : ∫ e, w e ∂μ = 0) : ∫ e, balancedActivation w δ e ∂balancedReferenceLaw μ δ = 0 := by
    have hh := balancedActivation_integral μ δ hδ hδ1 w hw (fun _ => 1) measurable_const
      (by simpa only [mul_one] using hwi)
    simpa only [mul_one, hc] using hh
  have h_highCenteredRowUnionActivation_centered  := h_balancedActivation_integral_zero _ _ (highRowUnionActivation_measurable R.rowMass R.rowActivation hAct) (highRowUnionActivation_integrable R.rowLaw R.rowMass R.rowActivation hAct hiAct) (highRowUnionActivation_centered R.rowLaw R.rowMass hMass R.rowActivation hAct hiAct hcAct)
  h_highCenteredRowUnionActivation_centered
theorem highUnionIntercept_measurable (hOffset : ∀ i, Measurable (R.rowIntercept i)) (δ ) :
    Measurable (highUnionIntercept R δ) :=
  balancedIntercept_measurable _ (rowSigmaFunction_measurable R.rowIntercept hOffset) δ _
theorem highUnionSlope_joint_measurable [∀ i, StandardBorelSpace (E i)]
    (hSlope : ∀ j i, Measurable (fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2))
    (j : HighWindowLabels d k) :
    Measurable (fun ex : HighUnionMark E × Covariate d => highUnionSlope R j ex.1 ex.2) := by
  let G : Sigma (fun i => E i × Covariate d) → ℝ := fun ex =>
    R.rowSlope j ex.1 ex.2.1 ex.2.2
  have h := ((((historySigma_measurable_iff G).mpr (hSlope j)).comp (historySigmaProdMeasurableEquiv E (Covariate d)).measurable).sumElim (measurable_const (a := 0))).comp
    (MeasurableEquiv.sumProdDistrib (Sigma E) Unit (Covariate d)).measurable
  convert h using 1
  funext ⟨e,x⟩
  cases e <;> rfl
theorem highUnionResponseVector_measurable
    (hVector : ∀ i γ, Measurable (fun e => R.rowVector i e γ)) (γ ) :
    Measurable (fun e => highUnionResponseVector R e γ) :=
  (rowSigmaFunction_measurable (fun i e => R.rowVector i e γ) (fun i => hVector i γ)).sumElim
    measurable_const
theorem highUnionResponseTime_measurable (hTime : ∀ i, Measurable (R.rowTime i)) :
    Measurable (highUnionResponseTime R) :=
  (rowSigmaFunction_measurable R.rowTime hTime).sumElim measurable_const
theorem highUnionRawUpdate_measurable [∀ i, StandardBorelSpace (E i)]
    (hSlope : ∀ j i, Measurable (fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2))
    (hOffset : ∀ i, Measurable (R.rowIntercept i))
    (hVector : ∀ i γ, Measurable (fun e => R.rowVector i e γ))
    (hTime : ∀ i, Measurable (R.rowTime i)) (δ j) :
    Measurable (fun eθ : HighUnionMark E × HighRawState d k F =>
      highUnionRawUpdate R δ j eθ.1 eθ.2) := by
  have hs (x : Covariate d) : Measurable (fun e => highUnionSlope R j e x) :=
    (highUnionSlope_joint_measurable R hSlope j).comp (measurable_id.prodMk measurable_const)
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro x
    by_cases hx : x ∈ highTorusPatch d k j
    · simp only [affinePatchUpdate, if_pos hx]
      exact ((hs x).comp measurable_fst).mul
        ((measurable_pi_apply x).comp (measurable_fst.comp measurable_snd)) |>.add
        ((highUnionIntercept_measurable R hOffset δ).comp measurable_fst)
    · simp only [affinePatchUpdate, if_neg hx]
      exact (measurable_pi_apply x).comp (measurable_fst.comp measurable_snd)
  · apply measurable_pi_lambda
    intro l
    apply measurable_pi_lambda
    intro γ
    by_cases hl : l = j
    · subst l
      simp only [responseCoordinateUpdate, Function.update_self, highUnionResponseReset, coefficientReset]
      exact ((measurable_const.sub ((highUnionResponseTime_measurable R hTime).comp
          measurable_fst)).mul (by fun_prop)).add
        (((highUnionResponseTime_measurable R hTime).comp measurable_fst).mul
          ((highUnionResponseVector_measurable R hVector γ).comp measurable_fst))
    · simp only [responseCoordinateUpdate, Function.update_of_ne hl]
      fun_prop
theorem highUnionResponseReset_ball (Cfr ) (hCfr : 0 < Cfr)
    (hVector : ∀ i e, (∑ γ, |R.rowVector i e γ|) ≤ Cfr⁻¹)
    (hTime : ∀ i e, R.rowTime i e ∈ Icc (0 : ℝ) 1)
    (e c)
    (hc : (∑ γ, |c γ|) ≤ Cfr⁻¹) :
    (∑ γ, |highUnionResponseReset R e c γ|) ≤ Cfr⁻¹ := by
  have hτ : highUnionResponseTime R e ∈ Icc 0 1 := by
    cases e with
    | inl e => exact hTime e.1 e.2
    | inr e => simp [highUnionResponseTime]
  have hv : (∑ γ, |highUnionResponseVector R e γ|) ≤ Cfr⁻¹ := by
    cases e with
    | inl e => exact hVector e.1 e.2
    | inr e => simp [highUnionResponseVector, hCfr.le]
  exact coefficientReset_mem_ball Cfr c _ _ hτ hc hv
end Reset
end NearlyMinimax
