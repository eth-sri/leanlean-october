module

public import RequestProject.SurfaceCocycleFan
public import RequestProject.BarycentricCocycleDescent

@[expose] public section

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

include hb

theorem section_flat : c.IsFlatSection (surfaceSection hc c rv re (centreValue hc c rv)) := by
  let z := centreValue hc c rv
  rintro a b (rfl | h)
  · rw [c.val_refl, one_smul]
  change plt vc ec a b at h
  cases a <;> cases b <;> simp only [plt] at h
  case vtx.bed v e =>
    rcases h with ⟨p, rfl, rfl | rfl⟩
    · exact (hb p).1
    · exact (hb p).2
  case vtx.dia v p => subst v; exact v_d hc c rv re z p
  case vtx.gdi v p => subst v; exact v_g hc c rv re z p
  case cvx.ced x p =>
    rcases h with rfl | rfl
    · exact w_f hc c rv re z x
    · exact w1_f hc c rv re z hb p
  case cvx.dia x p => subst x; exact w_d hc c rv re z p
  case cvx.gdi x p => subst x; exact w1_g hc c rv re z hb p
  case cvx.rad x p => subst x; exact w_r hc c rv re hb p
  case ctr.rad p => exact c_r hc c rv re p
  case bed.tr1 e p => subst e; exact e_t1 hc c rv re z p
  case ced.tr2 x p => subst x; exact f_t2 hc c rv re z p
  case ced.inn x p => subst x; exact f_i hc c rv re hb p
  case dia.tr1 x p => subst x; exact d1_t1 hc c rv re z hb p
  case dia.tr2 x p => subst x; exact d_t2 hc c rv re z p
  case gdi.tr1 x p => subst x; exact g_t1 hc c rv re z hb p
  case gdi.tr2 x p => subst x; exact g_t2 hc c rv re z p
  case rad.inn x p =>
    rcases h with rfl | rfl
    · exact r_i hc c rv re x
    · exact r1_i hc c rv re p
  case vtx.tr1 v p =>
    rcases h with rfl | rfl
    · exact v_t1 hc c rv re z hb p
    · exact v1_t1 hc c rv re z hb p
  case vtx.tr2 v p => subst v; exact v_t2 hc c rv re z p
  case cvx.tr1 x p => subst x; exact w1_t1 hc c rv re z hb p
  case cvx.tr2 x p =>
    rcases h with rfl | rfl
    · exact w_t2 hc c rv re z x
    · exact w1_t2 hc c rv re z hb p
  case cvx.inn x p =>
    rcases h with rfl | rfl
    · exact w_i hc c rv re hb x
    · exact w1_i hc c rv re hb p
  case ctr.inn p => exact c_i hc c rv re p



theorem exists_flat_section : ∃ s : SCell vc ec hc → Ω,
    c.IsFlatSection s ∧
    (∀ v, s (toS vc ec hc (.vtx v)) = rv v) ∧
    (∀ e, s (toS vc ec hc (.bed e)) = re e) :=
  ⟨surfaceSection hc c rv re (centreValue hc c rv), section_flat hc c rv re hb,
    fun _ => rfl, fun _ => rfl⟩
