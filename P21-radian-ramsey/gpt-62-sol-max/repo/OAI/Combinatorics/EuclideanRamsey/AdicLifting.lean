/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/AdicLifting.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Adapted to the Lean module system and simplified for this proof.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.LatticeMoments

@[expose] public section

open scoped TensorProduct
open Finset AddMonoidAlgebra Classical
namespace OAI.EuclideanRamsey
noncomputable section
variable {k : Type}

abbrev atom (x : Lattice k) : LatticeRing k := AddMonoidAlgebra.single x 1
@[simp] lemma atom_zero : atom (0 : Lattice k) = 1 := rfl
@[simp] lemma atom_add (x y : Lattice k) : atom (x+y) = atom x * atom y := by
  simp [atom, AddMonoidAlgebra.single_mul_single]

abbrev diff (x : Lattice k) := atom x - 1

private abbrev I (k : Type) : Ideal (LatticeRing k) := augmentationIdeal

private lemma ideal_smul {J : Ideal (LatticeRing k)} (c : ℚ) {x : LatticeRing k} (hx : x∈J) : c • x ∈ J :=
  (J.restrictScalars ℚ).smul_mem c hx

lemma augmentation_span : (augmentationIdeal : Ideal (LatticeRing k)) =
    Ideal.span (Set.range (fun y : Lattice k => diff y)) := by
  refine le_antisymm (fun x hx => ?_) (Ideal.span_le.mpr (by rintro _ ⟨y,rfl⟩; exact monomial_sub_one_mem y))
  have he : (∑ a ∈ x.coeff.support, x.coeff a • diff a) = x - mass x • 1 := by
    simp_rw [smul_sub,Finset.sum_sub_distrib,← Finset.sum_smul,smul_single,smul_eq_mul,mul_one]
    rw [← Finsupp.sum,AddMonoidAlgebra.sum_coeff_single,mass_apply,Finsupp.sum]
  rw [← show _ = x by simpa [(mem_augmentationIdeal _).mp hx] using he]
  exact Ideal.sum_mem _ fun a _ => ideal_smul _ (Ideal.subset_span ⟨a,rfl⟩)

def rowMap (f : Lattice k →+ ℝ) := AddMonoidAlgebra.mapDomainAlgHom ℚ ℚ f
abbrev rowIdeal (f : Lattice k →+ ℝ) : Ideal (LatticeRing k) := RingHom.ker (rowMap f)

/-- An additive map from the lattice that kills the kernel of a row evaluation
extends to a rational-linear map on the reals. -/
private lemma additive_factor {A : Type} [AddCommGroup A] [Module ℚ A]
    (f : Lattice k →+ ℝ) (g : Lattice k →+ A) (h : f.ker ≤ g.ker) :
    ∃ u : ℝ →ₗ[ℚ] A, ∀ x, u (f x) = g x := by
  let : DivisibleBy A ℤ := ⟨fun x n => (n:ℚ)⁻¹ • x,by simp,
    fun {n} x hn => by rw [← Int.cast_smul_eq_zsmul ℚ,smul_inv_smul₀ (Int.cast_ne_zero.mpr hn)]⟩
  obtain ⟨u,hu⟩ := (Module.Baer.of_divisible A).extension_property_addMonoidHom
    (QuotientAddGroup.kerLift f) (QuotientAddGroup.kerLift_injective f) (QuotientAddGroup.lift f.ker g h)
  exact ⟨u.toRatLinearMap,fun x => DFunLike.congr_fun hu (QuotientAddGroup.mk x)⟩

open PowerSeries (HasEval HasSubst coeff)
open PowerSeries.WithPiTopology

private def truncLog {A : Type*} [CommRing A] [Algebra ℚ A] (n : ℕ) (t : A) : A :=
  t + t^2 * ∑ i ∈ range n, PowerSeries.coeff (2+i) (PowerSeries.log ℚ) • t^i

section
variable {A : Type*} [CommRing A] [Algebra ℚ A]
local instance : UniformSpace ℚ := ⊥
local instance : UniformSpace A := ⊥
attribute [local instance] DiscreteTopology.instContinuousSMul

private abbrev evalP (t : A) (p : PowerSeries ℚ) := PowerSeries.eval₂ (algebraMap ℚ A) t p

private lemma eval_sum {n : ℕ} {t : A} (h : t^n = 0) (p : PowerSeries ℚ) :
    evalP t p = ∑ i ∈ range n, coeff i p • t^i := by
  rw [evalP, ← PowerSeries.coe_aeval (IsNilpotent.isTopologicallyNilpotent ⟨n,h⟩),
    PowerSeries.aeval_eq_sum, tsum_eq_sum]
  exact fun i hi => by rw [pow_eq_zero_of_le (by simpa using hi) h, smul_zero]

private lemma eval_subst {t : A} (ht : HasEval t) {p : PowerSeries ℚ} (hp : HasSubst p)
    (q : PowerSeries ℚ) : evalP t (q.subst p) = evalP (evalP t p) q :=
  MvPowerSeries.eval₂_subst hp.const (PowerSeries.hasEval ht) q

private lemma eval_exp {t : A} (h : IsNilpotent t) : evalP t (PowerSeries.exp ℚ) = IsNilpotent.exp t := by
  obtain ⟨n,hn⟩ := h
  simp [eval_sum hn,IsNilpotent.exp_eq_sum hn]

private lemma log_exp {t : A} (h : IsNilpotent t) : evalP (IsNilpotent.exp t - 1) (PowerSeries.log ℚ) = t := by
  have ht := h.isTopologicallyNilpotent
  have hh : evalP t (PowerSeries.exp ℚ - 1) = IsNilpotent.exp t - 1 := by
    simp [← PowerSeries.coe_aeval ht,evalP, ← eval_exp h]
  rw [← hh, ← eval_subst ht HasSubst.exp_sub_one, PowerSeries.subst_log_exp_sub_one]
  simp

private lemma truncLog_eq {n : ℕ} {t : A} (h : t^(n+2)=0) :
    truncLog n t = evalP t (PowerSeries.log ℚ) := by
  rw [eval_sum h,Nat.add_comm n 2,sum_range_add,truncLog,mul_sum]
  simp [sum_range_succ,PowerSeries.coeff_log,pow_add]

private lemma log_nil {n : ℕ} {t : A} (h : t^(n+2)=0) : IsNilpotent (evalP t (PowerSeries.log ℚ)) := by
  rw [← truncLog_eq h, truncLog, pow_two, mul_assoc, ← mul_one_add]
  exact (Commute.all ..).isNilpotent_mul_right ⟨_,h⟩

private lemma exp_log {n : ℕ} {t : A} (h : t^(n+2)=0) : IsNilpotent.exp (evalP t (PowerSeries.log ℚ)) = 1+t := by
  have ht := IsNilpotent.isTopologicallyNilpotent ⟨_,h⟩
  rw [← eval_exp (log_nil h), ← eval_subst ht HasSubst.log, PowerSeries.subst_exp_log]
  rw [evalP, ← PowerSeries.coe_aeval ht]
  simp [← Polynomial.coe_X]

private lemma truncLog_mul {n : ℕ} {x y : A} (hx : (x-1)^(n+2)=0) (hy : (y-1)^(n+2)=0)
    (hxy : (x*y-1)^(n+2)=0) : truncLog n (x*y-1) = truncLog n (x-1) + truncLog n (y-1) := by
  rw [truncLog_eq hxy,truncLog_eq hx,truncLog_eq hy]
  have ha := log_nil hx
  have hb := log_nil hy
  rw [← log_exp (Commute.isNilpotent_add (Commute.all ..) ha hb),
    IsNilpotent.exp_add_of_commute (Commute.all ..) ha hb,exp_log hx,exp_log hy]
  simp
end

private def additiveDiff (J : Ideal (LatticeRing k)) (n : ℕ) (hJ : I k ^ (n+2) ≤ J) :
    Lattice k →+ (LatticeRing k ⧸ J) where
  toFun x := Ideal.Quotient.mkₐ ℚ J (truncLog n (diff x))
  map_zero' := by
    simp [truncLog]
  map_add' x y := by
    let q := Ideal.Quotient.mkₐ ℚ J
    have hn (x : Lattice k) : (q (atom x)-1)^(n+2)=0 := by
      rw [← map_one q, ← map_sub, ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hJ (Ideal.pow_mem_pow (monomial_sub_one_mem x) _))
    simpa only [truncLog,map_sub,map_one,atom_add,map_mul,map_add,map_pow,map_smul,map_sum] using
      truncLog_mul (hn x) (hn y) (by simpa only [atom_add,map_mul] using hn (x+y))

/-- Symmetric two-atom measure. -/
def sample (x : Lattice k) : LatticeRing k := (1/2:ℚ) • (atom x + atom (-x))

abbrev axis (j : k) : Lattice k := Pi.single j 1

def stencil [Fintype k] (c : k → ℚ) : LatticeRing k := ∑ j, c j • (sample (axis j)-1)

@[simp] lemma mass_sample (x : Lattice k) : mass (sample x) = 1 := by norm_num [sample]
@[simp] lemma integral_sample (f : Lattice k →+ ℝ) (x : Lattice k) : integral f (sample x) = 0 := by simp [sample]
@[simp] lemma quadratic_sample (f g : Lattice k →+ ℝ) (x : Lattice k) : quadratic f g (sample x) = f x * g x := by
  simp [sample,quadratic,Rat.smul_def]; ring

private lemma sample_jet (n : ℕ) (x : Lattice k) :
    (1/2:ℚ) • (truncLog n (diff x))^2 - (sample x-1) ∈ I k ^ 3 := by
  let d := diff x
  let a := truncLog n d
  have h : d ∈ I k := monomial_sub_one_mem x
  have ha : a-d ∈ I k ^ 2 := by
    dsimp only [a]
    rw [truncLog,add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow h 2)
  have he : sample x - 1 = (1/2:ℚ) • (d^2*atom (-x)) := by
    have hh : atom x * atom (-x) = 1 := by rw [← atom_add,add_neg_cancel,atom_zero]
    rw [sample]
    have h' : atom x + atom (-x) = d^2*atom (-x)+(1+1) := by
      dsimp [d]; linear_combination (2-atom x)*hh
    rw [h']; module
  rw [he,← smul_sub,pow_succ,show a^2-d^2*atom (-x) = (a-d)*(a+d)-d^2*diff (-x) by ring]
  refine ideal_smul _ (Submodule.sub_mem _ (Ideal.mul_mem_mul ha ?_) (Ideal.mul_mem_mul
    (Ideal.pow_mem_pow h 2) (monomial_sub_one_mem (-x))))
  simpa using (I k).add_mem (Ideal.pow_le_self two_ne_zero ha) ((I k).add_mem h h)

theorem finite_lattice_identity [Fintype k] {s : ℕ} (f : Fin s → Lattice k →+ ℝ)
    (c : k → ℚ) (h : ∀ i, (∑ j, c j • (f i (axis j) ⊗ₜ[ℚ] f i (axis j))) = 0) :
    ∃ ν : LatticeRing k, (∀ i, ν ∈ rowIdeal (f i)) ∧
      ν - stencil c ∈ (augmentationIdeal : Ideal (LatticeRing k)) ^ 3 := by
  classical
  let J (i : Fin s) := rowIdeal (f i)
  let F : LatticeRing k →ₗ[LatticeRing k] (∀ i, LatticeRing k ⧸ J i) := LinearMap.pi (fun i => Algebra.linearMap _ _)
  obtain ⟨n,hn⟩ := (I k).exists_pow_inf_eq_pow_smul F.range
  let l (x : Lattice k) := truncLog (n+1) (diff x)
  let x := ∑ j, c j • ((1/2:ℚ) • (l (axis j))^2)
  have hx : x - stencil c ∈ I k ^ 3 := by
    dsimp only [x]
    rw [stencil,← Finset.sum_sub_distrib]
    exact Ideal.sum_mem _ fun j _ => by rw [← smul_sub]; exact ideal_smul _ (sample_jet _ _)
  have hrow (i : Fin s) : x ∈ J i ⊔ I k ^ (n+3) := by
    let K := J i ⊔ I k ^ (n+3)
    let q := Ideal.Quotient.mkₐ ℚ K
    obtain ⟨u,hu⟩ := additive_factor (f i) (additiveDiff K (n+1) le_sup_right) (fun v hv => by
      have hJ : diff v ∈ J i := by
        change rowMap (f i) (diff v) = 0
        rw [map_sub,map_one]
        simp [rowMap,AddMonoidAlgebra.one_def,AddMonoidAlgebra.mapDomain_single,show f i v = 0 from hv]
      have hz : q (diff v) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hJ)
      change q (truncLog (n+1) (diff v)) = 0
      simp [truncLog,hz])
    let Ψ := (Algebra.TensorProduct.lmul' ℚ).toLinearMap.comp (TensorProduct.map u u)
    have hx (j : k) : u (f i (axis j)) = q (l (axis j)) := hu _
    have he : (∑ j, c j • (q (l (axis j)))^2) = 0 := by
      simpa [Ψ,hx,pow_two] using congrArg Ψ (h i)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q x = 0
    simp only [x,map_sum,map_smul,map_pow,smul_comm (c _),← Finset.smul_sum,he,smul_zero]
  have hF : F x ∈ I k ^ (n+3) • (⊤ : Submodule (LatticeRing k) (∀ i, LatticeRing k ⧸ J i)) := by
    rw [← Finset.univ_sum_single (F x)]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨y,hy,z,hz,hx⟩ := Submodule.mem_sup.mp (hrow i)
    have he : F (y+z) i = z • (1 : LatticeRing k ⧸ J i) := by
      change Ideal.Quotient.mk (J i) (y+z) = _
      simp [Algebra.smul_def,Ideal.Quotient.eq_zero_iff_mem.mpr hy]
    rw [← hx,he,Pi.single_smul (f := fun i => LatticeRing k ⧸ J i)]
    exact Submodule.smul_mem_smul hz Submodule.mem_top
  have H := show F x ∈ I k ^ (n+3) • ⊤ ⊓ F.range from ⟨hF,⟨x,rfl⟩⟩
  rw [hn _ (by omega),Nat.add_sub_cancel_left] at H
  have H' := (smul_mono_right _ (inf_le_right : _ ⊓ F.range ≤ F.range)) H
  rw [LinearMap.range_eq_map,← Submodule.map_smul'',Ideal.smul_eq_mul,Ideal.mul_top] at H'
  obtain ⟨z,hz,he⟩ := H'
  refine ⟨x-z,fun i => Ideal.Quotient.eq_zero_iff_mem.mp ?_,?_⟩
  · exact congrFun (show F (x-z) = 0 by rw [map_sub,he,sub_self]) i
  · simpa only [sub_right_comm] using (I k ^ 3).sub_mem hx hz

end
end OAI.EuclideanRamsey
