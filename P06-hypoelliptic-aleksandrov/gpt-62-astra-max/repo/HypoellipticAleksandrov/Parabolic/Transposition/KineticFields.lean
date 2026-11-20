module
public import HypoellipticAleksandrov.Parabolic.Transposition.Integration
public import HypoellipticAleksandrov.Parabolic.Transposition.Rows
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeOperator
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeDiv
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketHormander
import Mathlib

/-! # Transposition in the packed kinetic coordinates -/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Transposition
open Hypoellipticity KineticAleksandrov KineticAleksandrov.Evolution Set
open scoped ContDiff MatrixOrder
variable {n : ℕ}
abbrev Plane (n : ℕ) := TimeVelocity (n+n)
abbrev split (n : ℕ) := (unpack (n+n)).symm.trans (evolutionProdCLE n)
abbrev world (n : ℕ) := (unpack (n+n)).symm.toHomeomorph.trans (evolutionHomeomorph n)

private def pulled (V : EvolutionVec n → EvolutionVec n) (hV : ContDiff ℝ ∞ V) : Vector (n+n) :=
  fun j => ⟨_, (contDiff_apply ℝ ℝ j).comp (hV.comp (unpack (n+n)).symm.contDiff)⟩

private theorem along_pull (V : EvolutionVec n → EvolutionVec n) (hV : ContDiff ℝ ∞ V) (f : Plane n → ℝ) (x : EvolutionVec n) :
    along (pulled V hV) f (unpack _ x) = fderiv ℝ (f ∘ unpack _) x (V x) := by
  rw [PDE.ContinuousLinearMap.apply_eq_vecDot_basisValues, (unpack _).comp_right_fderiv]
  change ∑ j, V ((unpack _).symm (unpack _ x)) j * fderiv ℝ f (unpack _ x) (dir j) = ∑ j, fderiv ℝ f (unpack _ x) (dir j) * V x j
  simp only [ContinuousLinearEquiv.symm_apply_apply,mul_comm]

private theorem on_pack (L : EvolutionVec n →L[ℝ] ℝ) (a : ℝ) (v z : PDE.Vec n) :
    L (packPoint a v z) = a * L basisT + (∑ j, v j * L (basisV j)) + ∑ j, z j * L (basisZ j) := by
  rw [PDE.ContinuousLinearMap.apply_eq_vecDot_basisValues]; unfold PDE.vecDot
  simp only [Fin.sum_univ_succ, Fin.sum_univ_add,packPoint_zero_apply,packPoint_diffused_apply,packPoint_transported_apply,
    basisT_eq_basisVec,basisV_eq_basisVec,basisZ_eq_basisVec,mul_comm]; ring

private theorem expand_kinetic {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} {lam Lam : ℝ}
    (hlam : 0 < lam) (hell : HasEverywhereLoewnerBounds lam Lam B) (hB : IsSmoothFullKineticCoefficient B)
    {f : EvolutionVec n → ℝ} {x} (hf : ContDiffAt ℝ 2 f x) :
    fderiv ℝ f x (driftField B b x) + ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (diffusionField B i y)) x (diffusionField B i x) = transportedOperator B b f x := by
  let s (p j : Fin n) (y : EvolutionVec n) := sqrtCoeffAt B y p j
  have D (g : EvolutionVec n → ℝ) i : (fun y => fderiv ℝ g y (diffusionField B i y)) = row basisV (s i) g :=
    funext fun y => by rw [diffusionField,on_pack]; simp [row,s]
  have sq := row_squares basisV s (fun i j => (contDiff_sqrtCoeffAt_entry hlam hB hell i j).differentiable (by simp) x) hf
  have sqeq i : fderiv ℝ (fun y => fderiv ℝ f y (diffusionField B i y)) x (diffusionField B i x) = row basisV (s i) (row basisV (s i) f) x := by
    rw [D]; exact congrFun (D _ i) x
  simp_rw [sqeq]
  rw [sq,driftField,on_pack]; simp only [row,driftCorrection,transportedOperator,one_mul,neg_mul,Finset.sum_neg_distrib,s,
    basisV,sum_sqrtCoeffAt_mul hlam hell]; ring

/-- Convert the sum of squares to the classical operator on any smooth germ. -/
theorem kinetic_fields (U : Domain (n+n)) {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    {lam Lam m : ℝ} (hlam : 0 < lam) (hB : IsSmoothFullKineticCoefficient B)
    (hell : HasEverywhereLoewnerBounds lam Lam B) (hb : IsSmoothDrift b) (hm : 0 < m)
    (hcoerc : HasUnitDirectionDriftCoercivity m b) : ∃ X : Fin (n+1) → Vector (n+n),
      LieAlgebraSpansOn ((unpack _) ⁻¹' (U : Set _)) (fun i => liftField (X i)) ∧
      ∀ (u : KineticPoint n → ℝ) (z : Plane n), ContDiffAt ℝ 2 (u ∘ world n) z →
        generator X (u ∘ world n) z = transportedForwardOperator B b u (world n z) := by
  let V := transportedFields B b
  have hV i : ContDiff ℝ ∞ (V i) := contDiff_transportedFields (contDiff_sqrtCoeffAt_entry hlam hB hell) hb i
  let X i := pulled (V i) (hV i)
  have hX : (fun i => liftField (X i)) = V := by
    funext i x j; change V i ((unpack _).symm (unpack _ x)) j = _; rw [ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨X,hX ▸ (hormander_hypotheses_transportedFields hlam hB hell hb hm hcoerc _).2,?_⟩
  intro u z; obtain ⟨x,rfl⟩ := (unpack (n+n)).surjective z
  let f := u ∘ world n
  let g := u ∘ evolutionHomeomorph n
  have e : f ∘ unpack (n+n) = g := by
    funext y; change g ((unpack _).symm (unpack _ y)) = g y; rw [ContinuousLinearEquiv.symm_apply_apply]
  intro h
  have h2 : ContDiffAt ℝ 2 g x := e ▸ h.comp x (unpack (n+n)).contDiff.contDiffAt
  have op := expand_kinetic (b := b) hlam hell hB h2
  have val i : along (X i) f ∘ unpack _ = fun y => fderiv ℝ g y (V i y) := funext fun y => (along_pull _ _ f y).trans (e ▸ rfl)
  change along (X 0) f _ + ∑ i : Fin n, along (X i.succ) (along (X i.succ) f) _ = _
  rw [show along (X 0) f (unpack _ x) = _ from congrFun (val 0) x]
  simp_rw [show ∀ i : Fin n, along (X i.succ) (along (X i.succ) f) (unpack _ x) = _ from fun i =>
    (along_pull _ _ _ x).trans (congrArg (fun t => fderiv ℝ t x (V i.succ x)) (val i.succ))]
  change _ = transportedForwardOperator B b u (evolutionHomeomorph n ((unpack _).symm (unpack _ x)))
  rw [ContinuousLinearEquiv.symm_apply_apply]; exact op.trans (transportedOperator_comp h2)

end HypoellipticAleksandrov.Parabolic.Transposition
