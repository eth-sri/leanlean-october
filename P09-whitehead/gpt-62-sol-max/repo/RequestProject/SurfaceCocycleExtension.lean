module

public import RequestProject.SurfaceCocycleFan
public import RequestProject.BarycentricCocycleDescent

@[expose] public section

/-! Boundary flat sections extend across the actual closed polygon surface. -/
namespace FiniteChains.Davis.SurfaceSection
open RACG Mirror Comb Cell
universe u v w
variable {κ ι : Type u} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  {G : Type v} [Group G] {Ω : Type w} [MulAction G Ω]
  (c : OrdCocycle (SCell vc ec hc) G) (rv : κ → Ω) (re : ι → Ω)
  (hb : ∀ p : Fin M,
    c.val (cV hc p) (cE hc p) • re (ec p) = rv (vc p) ∧
    c.val (cV hc (p + 1)) (cE hc p) • re (ec p) = rv (vc (p + 1)))

include hb in
theorem section_flat : c.IsFlatSection (surfaceSection hc c rv re (centreValue hc c rv)) := by
  intro a b hab
  rcases hab with heq | h
  · simp_all
  change plt vc ec a b at h
  cases a <;> cases b <;> simp only [plt] at h
  case vtx.bed =>
    obtain ⟨p, rfl, rfl | rfl⟩ := h
    · exact (hb p).1
    · exact (hb p).2
  all_goals
    (try rcases h with h | h) <;> subst_vars <;>
      (solve_by_elim (maxDepth := 4) only [*, v_d, v_g, w_d, w_f, w1_f, w1_g, w_r,
        c_r, e_t1, f_t2, f_i, d1_t1, d_t2, g_t1, g_t2, r_i, r1_i,
        v_t1, v1_t1, v_t2, w1_t1, w_t2, w1_t2, w_i, w1_i, c_i])

include hb in
/-- No new monodromy is introduced by the collar and the interior fan. All
flat boundary data extend for an arbitrary group action. -/
theorem exists_flat_section : ∃ s : SCell vc ec hc → Ω,
    c.IsFlatSection s ∧
    (∀ v, s (toS vc ec hc (.vtx v)) = rv v) ∧
    (∀ e, s (toS vc ec hc (.bed e)) = re e) :=
  ⟨surfaceSection hc c rv re (centreValue hc c rv), section_flat hc c rv re hb,
    fun _ => rfl, fun _ => rfl⟩

end FiniteChains.Davis.SurfaceSection











