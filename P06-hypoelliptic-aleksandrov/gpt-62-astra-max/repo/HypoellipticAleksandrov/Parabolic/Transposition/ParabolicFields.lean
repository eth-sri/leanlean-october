module

public import HypoellipticAleksandrov.Parabolic.Transposition.Integration
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketSpan
import Mathlib

/-! # The parabolic operator as a full-rank Hörmander generator

Use rows of the positive square root as spatial vector fields. Its drift correction
cancels the first derivatives of the square root in the expansion of their squares.
-/

@[expose] public noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Transposition
open KineticAleksandrov KineticAleksandrov.Evolution Hypoellipticity Set Filter
open scoped ContDiff Topology MatrixOrder Matrix.Norms.Elementwise

variable {d : ℕ} {U : Domain d}
abbrev Row (d : ℕ) := Fin d → Field d
abbrev Tensor (d : ℕ) := Fin d → Row d

private def head (c : ℝ) (b : Row d) : Vector d := Fin.cons ⟨fun _ => c,contDiff_const⟩ b
private def correction (s : Tensor d) (b : Row d) (j : Fin d) : Field d :=
  ⟨fun z => (b j).val z - ∑ p, along (head 0 (s p)) (s p j).val z,
    (b j).prop.sub (ContDiff.sum (fun p _ => along_sm _ (s p j).prop))⟩
private def fields (s : Tensor d) (b : Row d) : Fin (d+1) → Vector d := Fin.cons (head 1 (correction s b)) (fun i => head 0 (s i))

private theorem fields_span (s : Tensor d) (b : Row d)
    (hs : ∀ z, (Matrix.of (fun i j => (s i j).1 z)).PosDef) (V : Set (PDE.Vec (d+1))) :
    LieAlgebraSpansOn V (fun i => liftField (fields s b i)) := by
  intro x _
  let W := Submodule.span ℝ (range fun w : LieWord d => LieWord.eval (fun i => liftField (fields s b i)) w x)
  have gen (i : Fin (d+1)) : liftField (fields s b i) x ∈ W := Submodule.subset_span ⟨.generator i,rfl⟩
  apply eq_top_iff.mpr; intro y _
  obtain ⟨v,hv⟩ := exists_row_combination (hs (unpack d x)) (fun j => y j.succ - y 0 * (correction s b j).val (unpack d x))
  simp only [Matrix.of_apply] at hv
  rw [show y = y 0 • liftField (fields s b 0) x + ∑ i, v i • liftField (fields s b i.succ) x from by
    ext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp [liftField,fields,head,Finset.sum_apply]
    · simpa [liftField,fields,head,Finset.sum_apply] using (eq_add_of_sub_eq' (hv j).symm)]
  exact W.add_mem (W.smul_mem _ (gen 0)) (W.sum_mem fun i _ => W.smul_mem _ (gen i.succ))

private theorem along_head (c : ℝ) (v : Row d) (f : TimeVelocity d → ℝ) (z) : along (head c v) f z =
    c * pd 0 f z + ∑ j, (v j).val z * pd j.succ f z := by simp [along,Fin.sum_univ_succ,head]

private theorem along_sum {ι : Type*} [Fintype ι] (v : Vector d) (f : ι → TimeVelocity d → ℝ) {z}
    (h : ∀ j, DifferentiableAt ℝ (f j) z) : along v (fun z => ∑ j, f j z) z = ∑ j, along v (f j) z := by
  simp only [along,pd,fderiv_fun_sum (fun j _ => h j),ContinuousLinearMap.sum_apply,Finset.mul_sum]
  exact Finset.sum_comm

private theorem along_mul_at (v : Vector d) {f g : TimeVelocity d → ℝ} {z}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    along v (fun z => f z*g z) z = f z*along v g z + g z*along v f z := by
  simp only [along,pd,fderiv_fun_mul hf hg,add_apply,smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib,mul_left_comm,Finset.mul_sum]

private theorem has_time {f : TimeVelocity d → ℝ} {z} (hf : DifferentiableAt ℝ f z) :
    HasDerivAt (fun t => f (t,z.2)) (pd 0 f z) z.1 := by
  unfold pd; rw [dir_zero]; simpa only [Function.comp_def,id_eq] using! hf.hasFDerivAt.comp_hasDerivAt z.1
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))

private theorem spatial_pd {f : TimeVelocity d → ℝ} {z} (hf : DifferentiableAt ℝ f z) (i : Fin d) :
    pd i.succ f z = fderiv ℝ (fun y => f (z.1,y)) z.2 (PDE.basisVec i) := by
  change pd i.succ f z = fderiv ℝ (f ∘ Prod.mk z.1) z.2 _
  rw [pd,dir_succ,(hf.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)).fderiv]; rfl

private theorem grad_pd (w : Local U) {z} (hz : z ∈ U) (i : Fin d) :
    scalarSpatialGradient w.val z i = pd i.succ w.val z := (spatial_pd (difAt w hz) i).symm

private theorem hess_pd (w : Local U) {z} (hz : z ∈ U) (i j : Fin d) :
    scalarSpatialHessian w.val z i j = pd i.succ (pd j.succ w.val) z := by
  let p (y : PDE.Vec d) (j : Fin d) := (diff j.succ w).val (z.1,y)
  have h (k : Fin d) : DifferentiableAt ℝ (fun y => p y k) z.2 :=
    (difAt (diff k.succ w) hz).comp z.2 (hasFDerivAt_prodMk_right z.1 z.2).differentiableAt
  have eq : (fun y => scalarSpatialGradient w.val (z.1,y)) =ᶠ[𝓝 z.2] p := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (U.isOpen.mem_nhds hz)] with y hy
    exact funext fun k => grad_pd w hy k
  change (fderiv ℝ (fun y => scalarSpatialGradient w.val (z.1,y)) z.2 (PDE.basisVec i)) j = pd i.succ (diff j.succ w).val z
  rw [eq.fderiv_eq,spatial_pd (difAt (diff j.succ w) hz), fderiv_pi h]; rfl

private theorem expand (s : Tensor d) (b : Row d) (w : Local U) {z} (hz : z ∈ U) : generator (fields s b) w.val z =
    pd 0 w.val z + ∑ j, (b j).val z * pd j.succ w.val z + ∑ j, ∑ i,
      (∑ p, (s p j).val z * (s p i).val z) * pd i.succ (pd j.succ w.val) z := by
  have D (j : Fin d) : DifferentiableAt ℝ (pd j.succ w.val) z := difAt (diff j.succ w) hz
  have V (v : Row d) (f : TimeVelocity d → ℝ) : along (head 0 v) f = fun z => ∑ j, (v j).val z * pd j.succ f z :=
    funext fun z => by simp [along_head]
  have sq p : along (head 0 (s p)) (along (head 0 (s p)) w.val) z = ∑ j,
      ((s p j).val z * ∑ i, (s p i).val z * pd i.succ (pd j.succ w.val) z + pd j.succ w.val z * along (head 0 (s p)) (s p j).val z) := by
    rw [V (s p) w.val, along_sum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [along_mul_at _ ((s p j).prop.differentiable (by simp) z) (D j),V _ (pd j.succ w.val)]
    · exact fun j => ((s p j).prop.differentiable (by simp) z).mul (D j)
  change along (head 1 (correction s b)) w.val z + ∑ p, along (head 0 (s p)) (along (head 0 (s p)) w.val) z = _
  simp only [along_head 1,sq,one_mul,correction,sub_mul,Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun p j => (s p j).val z * _ + _ * along (head 0 (s p)) (s p j).val z)]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  have hx j : (∑ p, (s p j).val z * ∑ i, (s p i).val z * pd i.succ (pd j.succ w.val) z) =
      ∑ i, (∑ p, (s p j).val z * (s p i).val z) * pd i.succ (pd j.succ w.val) z := by
    simp only [Finset.mul_sum,← mul_assoc,Finset.sum_mul]; exact Finset.sum_comm
  simp_rw [hx, mul_comm (pd _ _ z) _]; ring

theorem parabolic_fields (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (ha : IsSmoothCoefficient A) (hb : ContDiff ℝ ∞ (fun z : TimeVelocity d => b z.1 z.2))
    (hp : ∀ z, (coefficientAt A z).PosDef) : ∃ X : Fin (d+1) → Vector d,
      LieAlgebraSpansOn ((unpack d) ⁻¹' (U : Set _)) (fun i => liftField (X i)) ∧
      ∀ w : Local U, EqOn (generator X w.val) (scalarParabolicZeroOrderOperator A b (fun _ _ => 0) w.val) U := by
  let a := coefficientAt A
  let s : Tensor d := fun p j => ⟨_,contDiff_sqrt_entry a (fun i j => (contDiff_apply_apply ℝ ℝ i j).comp ha) hp p j⟩
  let B : Row d := fun j => ⟨_, (contDiff_apply ℝ ℝ j).comp hb⟩
  have hs (z) : (Matrix.of (fun i j => (s i j).val z)).PosDef := posDef_sqrt (hp z)
  have hgram (z i j) : ∑ p, (s p j).val z * (s p i).val z = a z i j := by
    let m := CFC.sqrt (a z)
    have he (p) : m p i = m i p := by simpa [m,Matrix.conjTranspose_apply] using congrFun (congrFun (CFC.sqrt_nonneg (a z)).isSelfAdjoint.star_eq i) p
    have sq := congrFun (congrFun (CFC.sqrt_mul_sqrt_self (a z) (hp z).posSemidef.nonneg) i) j
    simpa only [Matrix.mul_apply,← he,s,m,mul_comm] using! sq
  refine ⟨fields s B,fields_span s B hs _,fun w z hz => ?_⟩
  rw [expand s B w hz,scalarParabolicZeroOrderOperator_apply]
  simp only [← hess_pd w hz, hgram,← grad_pd w hz,zero_mul,add_zero, ← (has_time (difAt w hz)).deriv]
  rw [Finset.sum_comm]; exact add_right_comm _ _ _

end HypoellipticAleksandrov.Parabolic.Transposition
