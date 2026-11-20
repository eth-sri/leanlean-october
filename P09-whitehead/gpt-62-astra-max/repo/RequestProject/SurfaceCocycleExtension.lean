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
  cases a <;> cases b <;> simp only [plt] at h
  case vtx.bed v e =>
    obtain ⟨p, hp, hv⟩ := h
    subst e
    rcases hv with hv | hv
    · subst v; exact (hb p).1
    · subst v; exact (hb p).2
  case vtx.dia v p =>
    subst v
    apply v_d
  case vtx.gdi v p =>
    subst v
    apply v_g
  case cvx.ced x p =>
    rcases h with h | h
    · subst x; apply w_f
    · subst x; apply w1_f <;> assumption
  case cvx.dia x p =>
    aesop
  case cvx.gdi x p =>
    subst x
    apply w1_g <;> assumption
  case cvx.rad x p =>
    subst x
    apply w_r <;> assumption
  case ctr.rad p => apply c_r
  case bed.tr1 e p =>
    subst e
    apply e_t1
  case ced.tr2 x p =>
    subst x
    apply f_t2
  case ced.inn x p =>
    subst x
    apply f_i <;> assumption
  case dia.tr1 x p =>
    subst x
    apply d1_t1 <;> assumption
  case dia.tr2 x p =>
    subst x
    apply d_t2
  case gdi.tr1 x p =>
    subst x
    apply g_t1 <;> assumption
  case gdi.tr2 x p =>
    subst x
    apply g_t2
  case rad.inn x p =>
    rcases h with h | h
    · subst x; apply r_i
    · subst x; apply r1_i
  case vtx.tr1 v p =>
    rcases h with h | h
    · subst v; apply v_t1 <;> assumption
    · subst v; apply v1_t1 <;> assumption
  case vtx.tr2 v p =>
    subst v
    apply v_t2
  case cvx.tr1 x p =>
    subst x
    apply w1_t1 <;> assumption
  case cvx.tr2 x p =>
    rcases h with h | h
    · subst x; apply w_t2
    · subst x; apply w1_t2 <;> assumption
  case cvx.inn x p =>
    rcases h with h | h
    · subst x; apply w_i <;> assumption
    · subst x; apply w1_i <;> assumption
  case ctr.inn p => apply c_i

end FiniteChains.Davis.SurfaceSection
