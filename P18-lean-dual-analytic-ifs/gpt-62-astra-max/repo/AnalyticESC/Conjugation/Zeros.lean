module

public import AnalyticESC.Conjugation.Uniqueness

@[expose] public section

/-!
# Conjugacies by injective analytic maps

Two facts about an analytic map `g` that is injective on `[0,1]` and conjugates contractions of
`[0,1]` to affine maps: `g'` has no zero in `[0,1]` once two of the maps have distinct fixed
points, and maps with a common fixed point commute.
-/

namespace AnalyticESC

open Set Filter Topology
open scoped NNReal

/-- The critical set of an injective analytic coordinate is finite. -/
private lemma finite_critical {g} (hg : IsAnalyticCoord g) : {x ∈ I | deriv g x = 0}.Finite := by
  by_contra hi
  have he := agree_Icc hg.1.deriv (g := fun _ => 0) analyticOnNhd_const hi (fun _ hx => hx.1) (fun _ hx => hx.2)
  have hc x (hx : x ∈ I) : HasDerivWithinAt g 0 I x := by
    rw [← show deriv g x = 0 from he hx]; exact (hg.1 x hx).differentiableAt.hasDerivAt.hasDerivWithinAt
  exact zero_ne_one (hg.2 zero_I (1:I).2
    (eq_of_hasDerivWithinAt_zero_I hc (by norm_num) (by norm_num)))

/-- A conjugated word permutes the finite critical set. Each critical point is therefore
periodic, and a periodic point of a strict contraction must be fixed. -/
lemma IFS.fixes_critical {N} (Φ : IFS N) {a : Letters N} (ha : a ≠ []) {g}
    (hg : IsAnalyticCoord g) (hl : Linearizes g (Φ.R a)) {z} (hz : z ∈ I) (hd : deriv g z = 0) : Φ.R a z = z := by
  let Z := {x ∈ I | deriv g x = 0}
  have : Finite Z := (finite_critical hg).to_subtype
  have hf := Φ.regular_R a
  have hm : MapsTo (Φ.R a) I I := Φ.re_comp_mem_I a
  obtain ⟨l,b,-,-,hl⟩ := hl
  have inv : MapsTo (Φ.R a) Z Z := by
    rintro x ⟨hx,h⟩
    have he := affine_deriv (hg.1.comp hf.1 hm) hg.1 hl hx
    rw [deriv_comp x (hg.1 _ (hm hx)).differentiableAt (hf.1 x hx).differentiableAt,h,mul_zero] at he
    exact ⟨hm hx,(mul_eq_zero.mp he).resolve_right (hf.2 x hx)⟩
  let T := inv.restrict (Φ.R a) Z Z
  have inj : Function.Injective T := fun x y h => Subtype.ext ((Φ.regular_R a).injOn x.2.1 y.2.1 (congrArg Subtype.val h))
  let E (y : Z) := |Φ.R a y - y|
  have step (p : Z) : ∃ q, E p ≤ Φ.cmax^a.length * E q := by
    obtain ⟨q,rfl⟩ := Finite.surjective_of_injective inj p
    exact ⟨q,by simpa [E,T] using Φ.R_lip a (hm q.2.1) q.2.1⟩
  have hlt := pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one (List.length_pos_iff.mpr ha).ne'
  simpa [E,sub_eq_zero] using contraction_estimate (pow_nonneg Φ.cmax_nonneg _) hlt (finite_range E).bddAbove step ⟨z,hz,hd⟩

/-- Two maps of `[0,1]` with a common fixed point that are conjugated by an injective `g` to
affine maps commute on `[0,1]`. -/
theorem comp_comm_of_conj {F G g : ℝ → ℝ} (hinj : InjOn g I) (hF : MapsTo F I I)
    (hG : MapsTo G I I) (h₁ : Linearizes g F) (h₂ : Linearizes g G) {p : ℝ} (hp : p ∈ I) (hFp : F p = p) (hGp : G p = p) :
    ∀ x ∈ I, F (G x) = G (F x) := by
  obtain ⟨a,s,-,-,hgF⟩ := h₁; obtain ⟨b,t,-,-,hgG⟩ := h₂
  intro x hx
  refine hinj (hF (hG hx)) (hG (hF hx)) ?_
  dsimp only [AffineRel,Function.comp_apply] at hgF hgG
  rw [hgF _ (hG hx),hgG _ (hF hx),hgG x hx,hgF x hx]
  grind
