module
public import Mathlib.Tactic.FunProp

public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

/-!
# One-dimensional stretching maps (towards External theorem BZ)

For `T > 0` and `|b| ≤ T/2`, the piecewise linear map `σ_b(a) = a + b θ(a)`, with the tent
`θ(a) = max(0, 1 - |a|/T)`, is a bi-Lipschitz homeomorphism of `ℝ` with `σ_b(0) = b` that is the
identity outside `(-T, T)`. We record its inverse and Lipschitz bounds, uniform in `b`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

/-- The tent `θ(a) = max(0, 1 - |a|/T)`. -/
def tentθ (T a : ℝ)  := max 0 (1 - |a| / T)

/-- The stretching map `σ_b(a) = a + b θ(a)`. -/
def sigmaMap T b a  := a + b * tentθ T a

variable {T : ℝ}

lemma tentθ_nonneg a : 0 ≤ tentθ T a := le_max_left _ _

lemma tentθ_le_one (hT : 0 < T) a : tentθ T a ≤ 1 :=
  max_le zero_le_one (by have : 0 ≤ |a| / T := by positivity
                         linarith)

lemma tentθ_eq_zero (hT : 0 < T)  (ha : T ≤ |a|) : tentθ T a = 0 := by
  refine max_eq_left ?_
  have : 1 ≤ |a| / T := by rw [le_div_iff₀ hT]; linarith
  linarith

lemma tentθ_zero : tentθ T 0 = 1 := by
  simp [tentθ]

lemma abs_tentθ_sub_le (hT : 0 < T) a a' : |tentθ T a - tentθ T a'| ≤ |a - a'| / T := by
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp; positivity) ?_)
  rw [show 1 - |a| / T - (1 - |a'| / T) = (|a'| - |a|) / T by ring, abs_div, abs_of_pos hT]
  exact div_le_div_of_nonneg_right
    (by grind) hT.le

@[fun_prop]
lemma continuous_tentθ T : Continuous (tentθ T) := by
  unfold tentθ; fun_prop

variable {b b' : ℝ}

lemma continuous_sigmaMap T b : Continuous (sigmaMap T b) := by
  unfold sigmaMap; fun_prop

lemma sigmaMap_zero : sigmaMap T b 0 = b := by
  simp [sigmaMap, tentθ_zero]

lemma sigmaMap_of_le_abs (hT : 0 < T)  (ha : T ≤ |a|) : sigmaMap T b a = a := by
  simp [sigmaMap, tentθ_eq_zero hT ha]

section
variable (hT : 0 < T) (hb : |b| ≤ T / 2)

include hT hb in
/-- `σ_b` increases at rate at least `1/2`. -/
lemma sigmaMap_sub_ge  (h : a' ≤ a) :
    (a - a') / 2 ≤ sigmaMap T b a - sigmaMap T b a' := by
  unfold sigmaMap
  have h1 := abs_tentθ_sub_le hT a a'
  have h2 : |b * (tentθ T a - tentθ T a')| ≤ (a - a') / 2 := by
    rw [abs_mul]
    calc |b| * |tentθ T a - tentθ T a'| ≤ (T / 2) * (|a - a'| / T) :=
          mul_le_mul hb h1 (abs_nonneg _) (by positivity)
      _ = (a - a') / 2 := by grind
  grind [tentθ, PolyaNeumann.tentθ]

include hT hb in
lemma sigmaMap_strictMono : StrictMono (sigmaMap T b) :=
  fun a' a h => by have := sigmaMap_sub_ge hT hb h.le; linarith

lemma abs_sigmaMap_sub_param (hT : 0 < T) a :
    |sigmaMap T b a - sigmaMap T b' a| ≤ |b - b'| := by
  unfold sigmaMap
  rw [show a + b * tentθ T a - (a + b' * tentθ T a) = (b - b') * tentθ T a by ring, abs_mul,
    abs_of_nonneg (tentθ_nonneg a)]
  exact mul_le_of_le_one_right (abs_nonneg _) (tentθ_le_one hT a)

include hT hb in
lemma sigmaMap_pos (hb0 : 0 ≤ b)  (ha : 0 < a) :
    0 < sigmaMap T b a := by
  have := sigmaMap_strictMono hT hb ha
  rw [sigmaMap_zero] at this; linarith

include hT hb in
lemma existsUnique_sigmaMap_eq w :
    ∃! a, sigmaMap T b a = w := by
  have hm := sigmaMap_strictMono hT hb
  refine existsUnique_of_exists_of_unique ?_ (fun a a' h1 h2 => hm.injective (h1.trans h2.symm))
  by_cases hw : T ≤ |w|
  · exact ⟨w, sigmaMap_of_le_abs hT hw⟩
  · have h1 : sigmaMap T b (-T) = -T := sigmaMap_of_le_abs hT (by rw [abs_neg, abs_of_pos hT])
    have h2 : sigmaMap T b T = T := sigmaMap_of_le_abs hT (by rw [abs_of_pos hT])
    obtain ⟨a, -, ha⟩ := intermediate_value_Icc (show -T ≤ T by linarith)
      (continuous_sigmaMap T b).continuousOn
      (show w ∈ Set.Icc (sigmaMap T b (-T)) (sigmaMap T b T) by
        grind)
    exact ⟨a, ha⟩

end


open Classical in
/-- The inverse of `σ_b` (for `|b| ≤ T/2`; the identity otherwise). -/
def sigmaInv T b w  :=
  if h : 0 < T ∧ |b| ≤ T / 2 then (existsUnique_sigmaMap_eq h.1 h.2 w).exists.choose else w

section
variable (hT : 0 < T) (hb : |b| ≤ T / 2)
include hT hb

lemma sigmaMap_sigmaInv w :
    sigmaMap T b (sigmaInv T b w) = w := by
  simp  [sigmaInv]
  grind

lemma sigmaInv_sigmaMap a :
    sigmaInv T b (sigmaMap T b a) = a :=
  (sigmaMap_strictMono hT hb).injective (sigmaMap_sigmaInv hT hb _)

lemma sigmaInv_of_le_abs  (hw : T ≤ |w|) :
    sigmaInv T b w = w := by
  conv_lhs => rw [← sigmaMap_of_le_abs (b := b) hT hw]
  exact sigmaInv_sigmaMap hT hb w

lemma sigmaInv_pos_iff w :
    0 < sigmaInv T b w ↔ b < w := by
  have hm := sigmaMap_strictMono hT hb
  have h0 := sigmaMap_zero (T := T) (b := b)
  have h1 := sigmaMap_sigmaInv hT hb w
  constructor
  · intro h
    have := hm h
    rwa [h0, h1] at this
  · intro h
    by_contra hle
    push_neg at hle
    have := hm.monotone hle
    linarith

lemma abs_sigmaInv_sub_le (hb' : |b'| ≤ T / 2) w w' :
    |sigmaInv T b w - sigmaInv T b' w'| ≤ 2 * |w - w'| + 2 * |b - b'| := by
  set a := sigmaInv T b w
  set a' := sigmaInv T b' w'
  have hw  := sigmaMap_sigmaInv hT hb w
  have hw'  := sigmaMap_sigmaInv hT hb' w'
  have h1 : |a - a'| / 2 ≤ |sigmaMap T b a - sigmaMap T b a'| := by
    rcases le_total a' a with h | h
    · have := sigmaMap_sub_ge hT hb h
      grind
    · have := sigmaMap_sub_ge hT hb h
      grind
  have h2 := abs_sigmaMap_sub_param (b := b) (b' := b') hT a'
  grind

end


end PolyaNeumann

end
