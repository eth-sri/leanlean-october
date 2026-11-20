module
public import GS.Topology.Germs
public import Mathlib.Topology.UrysohnsLemma
public import GS.Topology.SphereNoncontractible
@[expose] public section

/-! A section with an isolated-zero retraction must cover a neighbourhood
of the zero in a Euclidean chart. Otherwise push the chart origin to a
nearby missing point, leaving the boundary data unchanged. Composing with
the retraction then gives an impossible zero-free extension of the sphere. -/
noncomputable section
open Metric Set ContinuousMap GS.Topology
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace GS.Local
variable {m n : ℕ}
/-- If the intermediate map misses points arbitrarily close to the
origin, a cutoff translation moves its image off zero relative to the sphere. -/
private lemma fills (a : C(Eucl m,Eucl n)) (b : C(Eucl n,Eucl m))
    (fix : EqOn (b ∘ a) id (sphere 0 1)) (iso : ∀ z, b z = 0 ↔ z = 0) : range a ∈ 𝓝 0 := by
  let K := a '' sphere 0 1
  have hc : IsClosed K := ((isCompact_sphere _ _).image a.continuous).isClosed
  have nz : 0 ∉ K := by
    rintro ⟨x,hx,h⟩; have ex : x = 0 := (fix hx).symm.trans ((congrArg b h).trans ((iso 0).2 rfl)); simp_all
  obtain ⟨r,hr,sub⟩ := nhds_basis_closedBall.mem_iff.mp (hc.isOpen_compl.mem_nhds nz)
  obtain ⟨u,out,one,bounds⟩ := exists_continuous_zero_one_of_isClosed hc isClosed_closedBall (disjoint_right.mpr sub)
  apply Filter.mem_of_superset (closedBall_mem_nhds 0 hr); intro y hy
  by_contra miss
  let g z := a z - u (a z) • y
  have ne z : g z ≠ 0 := by
    intro h; have eq := sub_eq_zero.mp h
    have mem : a z ∈ closedBall 0 r := by
      rw [mem_closedBall_zero_iff,eq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (bounds _).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (bounds _).2).trans (mem_closedBall_zero_iff.mp hy)
    exact miss ⟨z,by simpa [show u (a z) = 1 from one mem] using eq⟩
  apply sphere_zero (b.continuous.comp (show Continuous g by dsimp [g]; fun_prop)) _ (fun z h => ne z ((iso _).1 h))
  intro x hx; have hs := mem_sphere_zero_iff_norm.mpr hx
  simpa [g,show u (a x) = 0 from out (mem_image_of_mem a hs)] using fix hs

variable {X : Type} [TopologicalSpace X] {x : X}
lemma expandChart {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : OpenPartialHomeomorph X E) (hx : x ∈ c.source) :
    ∃ b : OpenPartialHomeomorph X E, x ∈ b.source ∧ b x = 0 ∧ ∀ z, z ∈ b.target := by
  obtain ⟨r,hr,sub⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source hx))
  let e : OpenPartialHomeomorph E E := .univBall (c x) r
  have he : e.target = ball (c x) r := OpenPartialHomeomorph.univBall_target _ hr
  have hs (z) : z ∈ e.source := by simp [e]
  have h1 : c x ∈ e.target := he ▸ mem_ball_self hr
  have h2 : e.target ⊆ c.target := he ▸ sub
  have h3 : e.symm (c x) = 0 := OpenPartialHomeomorph.univBall_symm_apply_center (c x) r
  exact ⟨c.trans e.symm,⟨hx,h1⟩,h3,fun z => ⟨hs z,h2 (e.map_source (hs z))⟩⟩

structure Retract (x : X) (E : Type) [TopologicalSpace E] [Zero E] where
  project : C(X,E)
  lift : C(E,X)
  cancel : ∀ y, project (lift y) = y
  isolated : ∀ z, project z = 0 ↔ z = x

lemma section_fills (R : Retract x (Eucl m)) : Euclidean x → range R.lift ∈ 𝓝 x := by
  rintro ⟨n,c,hc,_⟩; obtain ⟨b,hs,he,ht⟩ := expandChart c hc
  have h₀ : R.lift 0 = x := (R.isolated _).1 (R.cancel 0)
  obtain ⟨r,hr,sub⟩ := nhds_basis_closedBall.mem_iff.mp ((b.open_source.preimage R.lift.continuous).mem_nhds (h₀ ▸ hs))
  let s (v : Eucl m) := (r / max 1 ‖v‖) • v
  have pos (v : Eucl m) : 0 < max 1 ‖v‖ := lt_max_of_lt_left zero_lt_one
  have hk v : R.lift (s v) ∈ b.source := sub (by
    rw [mem_closedBall_zero_iff]; dsimp only [s]; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),div_mul_eq_mul_div,div_le_iff₀ (pos v)]; gcongr; exact le_max_right ..)
  let a : C(Eucl m,Eucl n) := ⟨fun v => b (R.lift (s v)),b.continuousOn.comp_continuous (R.lift.continuous.comp (by dsimp [s]; fun_prop (disch := exact fun v => (pos v).ne'))) hk⟩
  have hb : Continuous b.symm := continuousOn_univ.mp (b.continuousOn_symm.mono fun z _ => ht z)
  let g : C(Eucl n,Eucl m) := ⟨fun z => r⁻¹ • R.project (b.symm z),by fun_prop⟩
  have fix : EqOn (g ∘ a) id (sphere 0 1) := by
    intro z hz; change r⁻¹ • R.project (b.symm (b _)) = z
    rw [b.left_inv (hk _),R.cancel]; simp [s,mem_sphere_zero_iff_norm.mp hz,smul_smul,hr.ne']
  have iso (z) : g z = 0 ↔ z = 0 := by
    change r⁻¹ • R.project (b.symm z) = 0 ↔ _; simp only [smul_eq_zero,inv_eq_zero,hr.ne',false_or,R.isolated]
    exact ⟨fun h => (b.right_inv (ht z)).symm.trans ((congrArg b h).trans he), fun h => h ▸ he ▸ b.left_inv hs⟩
  filter_upwards [(b.continuousAt hs).preimage_mem_nhds (he ▸ fills a g fix iso : range a ∈ 𝓝 (b x)),b.open_source.mem_nhds hs] with y ⟨z,hz⟩ hy
  exact ⟨s z,b.injOn (hk z) hy hz⟩
end GS.Local
