module
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsPhysicalOperator
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrier
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginJetsBounds
import Mathlib

/-! # Classical test functions at a translated kinetic scale -/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxBarrier
open Set Filter
open scoped Topology ContDiff
abbrev C2 (f : Z → ℝ) := ContDiff ℝ 2 f
abbrev P (b : ℝ) (f : Z → ℝ) := physicalSpatialOperator (fun _ _ => b) f

private lemma dx {f : Z → ℝ} {q : Z} (hd : DifferentiableAt ℝ f q) : deriv (fun x => f (x,q.2)) q.1 = bellmanDx f q :=
  (hd.hasFDerivAt.comp_hasDerivAt q.1 ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))).deriv

private lemma dv {f : Z → ℝ} {q : Z} (hd : DifferentiableAt ℝ f q) : deriv (fun v => f (q.1,v)) q.2 = bellmanDv f q :=
  (hd.hasFDerivAt.comp_hasDerivAt q.2 ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))).deriv

private lemma first_dv {f : Z → ℝ} (hf : C2 f) : ContDiff ℝ 1 (bellmanDv f) :=
  (hf.fderiv_right (by norm_num)).clm_apply contDiff_const

lemma physical_eq_bellman {f : Z → ℝ} (hf : C2 f) (b : ℝ) (q : Z) : P b f q = bellmanOperator b f q := by
  have h1 x : deriv (fun v => f (q.1,v)) x = bellmanDv f (q.1,x) := dv (hf.differentiable (by norm_num) (q.1,x))
  unfold P physicalSpatialOperator
  rw [bellmanOperator,dx (hf.differentiable (by norm_num) q), funext h1, dv ((first_dv hf).differentiable (by norm_num) q)]
  rfl

lemma continuous_P {f : Z → ℝ} (hf : C2 f) : Continuous (fun p : Z × ℝ => P p.2 f p.1) := by
  simp_rw [physical_eq_bellman hf]
  have hx : Continuous (bellmanDx f) := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hvv : Continuous (bellmanDvv f) := ((first_dv hf).continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact (continuous_fst.snd.mul (hx.comp continuous_fst)).add (continuous_snd.mul (hvv.comp continuous_fst))

lemma P_add {f g : Z → ℝ} (hf : C2 f) (hg : C2 g) (b : ℝ) (q : Z) : P b (f+g) q = P b f q + P b g q := by
  have add (z : Z) (e : Z) : fderiv ℝ (f+g) z e = fderiv ℝ f z e + fderiv ℝ g z e := by
    rw [fderiv_add (hf.differentiable (by norm_num) z) (hg.differentiable (by norm_num) z)]; rfl
  have he : bellmanDv (f+g) = bellmanDv f + bellmanDv g := funext fun z => add z (0,1)
  rw [physical_eq_bellman (f := f+g) (hf.add hg),physical_eq_bellman hf,physical_eq_bellman hg]
  simp only [bellmanOperator,bellmanDx,bellmanDvv,he,add,fderiv_add ((first_dv hf).differentiable (by norm_num) q) ((first_dv hg).differentiable (by norm_num) q),add_apply]; ring

lemma P_smul {f : Z → ℝ} (hf : C2 f) (a b : ℝ) (q : Z) : P b (a • f) q = a * P b f q :=
  (physical_eq_bellman (f := a • f) (contDiff_const.mul hf) b q).trans ((bellman_operator_mul a b f q).trans (congrArg (a * ·) (physical_eq_bellman hf b q).symm))

lemma P_sub {f g : Z → ℝ} (hf : C2 f) (hg : C2 g) (b : ℝ) (q : Z) : P b (f-g) q = P b f q - P b g q := by
  rw [sub_eq_add_neg,← neg_one_smul ℝ g,P_add (g := (-1:ℝ) • g) hf (contDiff_const.mul hg),P_smul hg]; ring

lemma smooth_sum {ι : Type*} (s : Finset ι) (f : ι → Z → ℝ) (h : ∀ i, C2 (f i)) : C2 (∑ i ∈ s, f i) := by
  convert ContDiff.sum (s := s) (fun i _ => h i) using 1; ext; simp

lemma P_sum {ι : Type*} (s : Finset ι) (f : ι → Z → ℝ) (h : ∀ i, C2 (f i)) (b : ℝ) (q : Z) :
    P b (∑ i ∈ s, f i) q = ∑ i ∈ s, P b (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [P,physicalSpatialOperator]
  | insert i s hi ih => simp only [Finset.sum_insert hi,P_add (g := ∑ j ∈ s, f j) (h i) (smooth_sum s f h),ih]

def coord (r Y : ℝ) (z : Z) : Z := ((r⁻¹)^3*(z.1-Y), r⁻¹*z.2)

def resize (a r Y : ℝ) (f : Z → ℝ) (z : Z) := a * f (coord r Y z)

lemma smooth_resize {f : Z → ℝ} (hf : C2 f) (a r Y : ℝ) : C2 (resize a r Y f) :=
  contDiff_const.mul (hf.comp ((contDiff_const.mul (contDiff_fst.sub contDiff_const)).prodMk (contDiff_const.mul contDiff_snd)))

lemma P_resize (f : Z → ℝ) (a b r Y : ℝ) (hr : 0 < r) (q : Z) :
    P b (resize a r Y f) q = a / r^2 * P b f (coord r Y q) := by
  let X := (coord r Y q).1
  let V := (coord r Y q).2
  have ex : deriv (fun x => f ((r⁻¹)^3*(x-Y),V)) q.1 = (r⁻¹)^3 * deriv (fun x => f (x,V)) X := by
    exact (deriv_comp_sub_const (fun x => f ((r⁻¹)^3*x,V)) Y q.1).trans (deriv_comp_mul_left (c := (r⁻¹)^3) (f := fun x => f (x,V)) (x := q.1-Y))
  have ev (x) : deriv (fun v => f (X,r⁻¹*v)) x = r⁻¹ * deriv (fun v => f (X,v)) (r⁻¹*x) := deriv_comp_mul_left _ (fun v => f (X,v)) _
  change q.2 * deriv (fun x => a*f ((r⁻¹)^3*(x-Y),V)) q.1 + b * deriv (deriv (fun v => a*f (X,r⁻¹*v))) q.2 = a/r^2*(V*deriv (fun x => f (x,V)) X+b*deriv (deriv (fun v => f (X,v))) V)
  simp_rw [deriv_const_mul_field',ex,funext ev,deriv_const_mul_field',deriv_comp_mul_left]
  dsimp only [V,coord,smul_eq_mul]; field_simp <;> ring

lemma compact_resize {f : Z → ℝ} (hf : HasCompactSupport f) (a r Y : ℝ) (hr : 0 < r) : HasCompactSupport (resize a r Y f) := by
  let e : Z ≃ₜ Z := {toFun := coord r Y,invFun := fun z => (r^3*z.1+Y,r*z.2),
                      left_inv := fun z => by ext <;> simp [coord,hr.ne'],right_inv := fun z => by ext <;> simp [coord,hr.ne'],
                      continuous_toFun := by unfold coord; fun_prop, continuous_invFun := by fun_prop}
  exact (hf.comp_homeomorph e).mul_left

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxBarrier
