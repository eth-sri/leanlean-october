module

public import OAI.Combinatorics.EuclideanRamsey.AdicLifting

@[expose] public section

open Finset AddMonoidAlgebra
open scoped Pointwise NNReal

namespace OAI.EuclideanRamsey.Discrete

noncomputable section

variable {k : Type} {d : ℕ}

/-- The order on lattice measures compares their coefficients. -/
scoped instance : _root_.Lattice (LatticeRing k) := (AddMonoidAlgebra.coeffEquiv).lattice

scoped instance : IsOrderedAddMonoid (LatticeRing k) where
  add_le_add_left _ _ h z i := add_le_add_left (h i) (z.coeff i)

lemma atom_nonneg (x : Lattice k) : 0 ≤ atom x := Finsupp.single_nonneg.mpr one_pos.le

scoped instance : ZeroLEOneClass (LatticeRing k) := ⟨atom_nonneg 0⟩

scoped instance : IsOrderedRing (LatticeRing k) := .of_mul_nonneg fun x y hx hy => by
  classical
  intro u
  change 0 ≤ (x*y).coeff u
  rw [AddMonoidAlgebra.coeff_mul]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    ite_nonneg (mul_nonneg (hx _) (hy _)) le_rfl

scoped instance : PosSMulMono ℚ (LatticeRing k) :=
  ⟨fun _ ha _ _ h i => mul_le_mul_of_nonneg_left (h i) ha⟩

private lemma abs_smul (a : ℚ) (x : LatticeRing k) : |a • x| = |a| • |x| := by
  ext i
  exact abs_mul a (x.coeff i)

lemma abs_mul_le_of_nonneg (x : LatticeRing k) {y : LatticeRing k} (hy : 0 ≤ y) :
    |x*y| ≤ |x| * y :=
  sup_le (mul_le_mul_of_nonneg_right (le_abs_self x) hy)
    (by simpa using mul_le_mul_of_nonneg_right (neg_le_abs x) hy)

private lemma abs_mul_le (x y : LatticeRing k) : |x*y| ≤ |x| * |y| := by
  conv_lhs => rw [← posPart_sub_negPart y,mul_sub,sub_eq_add_neg]
  rw [← posPart_add_negPart y,mul_add]
  refine (abs_add_le ..).trans ?_
  rw [abs_neg]
  gcongr <;> exact abs_mul_le_of_nonneg _ (by positivity)

abbrev Projection (k : Type) (d : ℕ) := Lattice k →+ Space d

abbrev latticeLift {E : Type*} [AddCommGroup E] [Fintype k] (u : k → E) : Lattice k →+ E :=
  (Fintype.linearCombination ℤ u).toAddMonoidHom

@[simp] lemma latticeLift_axis {E : Type*} [AddCommGroup E] [Fintype k] (u : k → E) (j : k) :
    latticeLift u (axis j) = u j := by simp [latticeLift,axis]

def gradientCoord (U : Projection k d) (a : Fin d) : Lattice k →+ ℝ :=
  (PiLp.proj 2 (β := fun _ : Fin d => ℝ) (𝕜 := ℝ) a).toLinearMap.toAddMonoidHom.comp U

def energy (U : Projection k d) : LatticeRing k →ₗ[ℚ] ℝ := integral fun u => ‖U u‖^2

lemma energy_mono (U : Projection k d) : Monotone (energy U) :=
  (monotone_iff_map_nonneg _).2 fun _ hx => Finsupp.sum_nonneg' fun u =>
    mul_nonneg (Rat.cast_nonneg.mpr (hx u)) (sq_nonneg _)

lemma energy_pos (U : Projection k d) {x : LatticeRing k} (hx : 0 ≤ x) : 0 ≤ energy U x := by
  simpa using energy_mono U hx

@[simp] lemma energy_one (U : Projection k d) : energy U 1 = 0 := by simp [energy]

lemma sum_quadratic (U : Projection k d) (ν : LatticeRing k) :
    (∑ a, quadratic (gradientCoord U a) (gradientCoord U a) ν) = energy U ν := by
  simp only [energy,quadratic,integral_apply,Finsupp.sum,Rat.smul_def,EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
  simp only [pow_two]
  exact Finset.sum_comm

lemma energy_mul_center (U : Projection k d) {x y : LatticeRing k} (hx : Centered x) :
    energy U (x*y) = (mass x : ℝ)*energy U y + (mass y : ℝ)*energy U x := by
  simp only [← sum_quadratic,quadratic_mul,hx _,zero_mul,add_zero,Finset.mul_sum,Finset.sum_add_distrib,mul_comm]

@[simp] lemma energy_sample (U : Projection k d) (x : Lattice k) : energy U (sample x) = ‖U x‖^2 := by
  simp [energy,sample,Rat.smul_def] ; ring

structure Probability (x : LatticeRing k) : Prop where
  pos : 0 ≤ x
  center : Centered x
  mass_eq : mass x = 1

namespace Probability
lemma one : Probability (1 : LatticeRing k) := ⟨zero_le_one,fun f => by simp,map_one mass⟩
lemma sample (x : Lattice k) : Probability (EuclideanRamsey.sample x) :=
  ⟨smul_nonneg (by norm_num) (add_nonneg (atom_nonneg _) (atom_nonneg _)),
    (integral_sample · x), mass_sample _⟩
lemma mul {x y : LatticeRing k} (hx : Probability x) (hy : Probability y) : Probability (x*y) :=
  ⟨mul_nonneg hx.pos hy.pos,fun f => by simp [integral_addHom_mul,hx.center f,hy.center f],
    by simp [hx.mass_eq,hy.mass_eq]⟩
lemma pow {x : LatticeRing k} (hx : Probability x) (n : ℕ) : Probability (x ^ n) := by
  induction n with
  | zero => simpa using Probability.one
  | succ n ih => exact ih.mul hx
lemma energy_mul (U : Projection k d) {x y : LatticeRing k}
    (hx : Probability x) (hy : Probability y) : energy U (x*y) = energy U x + energy U y := by
  simp [energy_mul_center U hx.center,hx.mass_eq,hy.mass_eq,add_comm]
lemma energy_pow (U : Projection k d) {x : LatticeRing k} (hx : Probability x) (n : ℕ) :
    energy U (x^n) = n * energy U x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, (hx.pow n).energy_mul U hx, ih, Nat.cast_succ, add_mul, one_mul]
end Probability

variable {U : Projection k d}

private lemma mass_mono : Monotone (mass : LatticeRing k → ℚ) :=
  (monotone_iff_map_nonneg _).2 fun x hx => by simpa only [mass_apply] using Finsupp.sum_nonneg' hx

lemma mass_nonneg {x : LatticeRing k} (hx : 0 ≤ x) : 0 ≤ mass x := by simpa using mass_mono hx

private lemma abs_mass_mul (x y : LatticeRing k) : mass |x*y| ≤ mass |x| * mass |y| :=
  (mass_mono (abs_mul_le x y)).trans_eq (map_mul mass _ _)

private def radius (U : Projection k d) (x : LatticeRing k) : ℝ≥0 := x.coeff.support.sup fun v => ‖U v‖₊

private lemma radius_mul (x y : LatticeRing k) : radius U (x*y) ≤ radius U x + radius U y :=
  AddMonoidAlgebra.sup_support_coeff_mul_le (degb := fun v => ‖U v‖₊) (fun a b => by rw [map_add]; exact nnnorm_add_le _ _) x y

@[simp] private lemma radius_one : radius U (1 : LatticeRing k) = 0 := by
  change (Finsupp.single 0 (1:ℚ)).support.sup (fun v : Lattice k => ‖U v‖₊) = 0
  simp

@[simp] private lemma radius_abs (x : LatticeRing k) : radius U |x| = radius U x := by
  unfold radius
  congr 1
  ext v
  simp only [Finsupp.mem_support_iff]
  exact not_congr abs_eq_zero

private lemma energy_radius {x : LatticeRing k} (hx : 0 ≤ x) {R : ℝ} (hR : (radius U x:ℝ) ≤ R) :
    energy U x ≤ (mass x : ℝ)*R^2 := by
  simp only [energy,integral_apply,mass_apply,Finsupp.sum,Rat.cast_sum,Rat.smul_def,Finset.sum_mul]
  refine sum_le_sum fun v hv => mul_le_mul_of_nonneg_left ?_ (Rat.cast_nonneg.mpr (hx v))
  have h : ‖U v‖ ≤ (radius U x:ℝ) := NNReal.coe_le_coe.mpr (Finset.le_sup (f:=fun y : Lattice k => ‖U y‖₊) hv)
  gcongr
  exact h.trans hR

def latticeAverage (n : ℕ) (f : ℕ → LatticeRing k) : LatticeRing k :=
  (n:ℚ)⁻¹ • ∑ i ∈ range n, f i

lemma latticeAverage_mass {n : ℕ} (hn : 0<n) {f : ℕ → LatticeRing k}
    (hf : ∀ j ∈ range n, mass (f j) = 1) : mass (latticeAverage n f) = 1 := by
  simp [latticeAverage,sum_congr rfl hf,Nat.cast_ne_zero.mpr hn.ne']

lemma latticeAverage_pos (n : ℕ) {f : ℕ → LatticeRing k}
    (h : ∀ j ∈ range n, 0 ≤ f j) : 0 ≤ latticeAverage n f :=
  smul_nonneg (by positivity) (Finset.sum_nonneg h)

lemma latticeAverage_le {n : ℕ} (hn : 0<n) (L : LatticeRing k →ₗ[ℚ] ℝ)
    {f : ℕ → LatticeRing k} {B : ℝ} (h : ∀ j ∈ range n, L (f j) ≤ B) :
    L (latticeAverage n f) ≤ B := by
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  simpa [latticeAverage,Rat.smul_def,← mul_assoc,hn'.ne'] using
    mul_le_mul_of_nonneg_left (sum_le_sum h) (inv_nonneg.mpr hn'.le)

def geomKernel (p q : LatticeRing k) (n : ℕ) :=
  latticeAverage n fun j => p^j * q^(n-1-j)

lemma geomKernel_sub (p q : LatticeRing k) (n : ℕ) :
    (p-q)*geomKernel p q n = ((n:ℚ)⁻¹) • (p^n-q^n) := by
  rw [geomKernel,latticeAverage, mul_smul_comm, mul_comm (p-q), geom_sum₂_mul]

/-- At width `n` a finite kernel has radius `O(n)` and makes the convolution error `O(n⁻ᵉ)` in total variation. -/
private def Smooth (U : Projection k d) (e : ℕ) (x : LatticeRing k) : Prop :=
  ∃ A : ℝ≥0, ∃ B : ℚ, ∀ n : ℕ, 0 < n → ∃ b : LatticeRing k, 0 ≤ b ∧ mass b = 1 ∧
    radius U b ≤ (n:ℝ≥0)*A ∧ mass |x*b| ≤ B/(n:ℚ)^e

namespace Smooth
variable {e f : ℕ} {x y : LatticeRing k}

private lemma base (x : LatticeRing k) : Smooth U 0 x :=
  ⟨0,mass |x|,fun _ _ => ⟨1,zero_le_one,map_one mass,by simp,by simp⟩⟩

private lemma mul (hx : Smooth U e x) (hy : Smooth U f y) : Smooth U (e+f) (x*y) := by
  obtain ⟨A,B,hx⟩ := hx
  obtain ⟨C,D,hy⟩ := hy
  refine ⟨A+C,B*D,fun n hn => ?_⟩
  obtain ⟨b,hb,hbm,hbA,hbB⟩ := hx n hn
  obtain ⟨c,hc,hcm,hcC,hcD⟩ := hy n hn
  refine ⟨b*c,mul_nonneg hb hc,by simp [hbm,hcm],(radius_mul _ _).trans (by rw [mul_add]; gcongr),?_⟩
  rw [mul_mul_mul_comm, pow_add, ← div_mul_div_comm]
  exact (abs_mass_mul _ _).trans (mul_le_mul hbB hcD (mass_nonneg (abs_nonneg _)) ((mass_nonneg (abs_nonneg _)).trans hbB))

private lemma add (hx : Smooth U e x) (hy : Smooth U e y) : Smooth U e (x+y) := by
  obtain ⟨A,B,hx⟩ := hx
  obtain ⟨C,D,hy⟩ := hy
  refine ⟨A+C,B+D,fun n hn => ?_⟩
  obtain ⟨b,hb,hbm,hbA,hbB⟩ := hx n hn
  obtain ⟨c,hc,hcm,hcC,hcD⟩ := hy n hn
  refine ⟨b*c,mul_nonneg hb hc,by simp [hbm,hcm],(radius_mul _ _).trans (by rw [mul_add]; gcongr),?_⟩
  rw [show (x+y)*(b*c) = (x*b)*c+(y*c)*b by ring,add_div]
  refine (mass_mono (abs_add_le _ _)).trans ?_
  rw [map_add]
  exact add_le_add ((abs_mass_mul _ _).trans (by simpa [abs_of_nonneg hc,hcm] using hbB))
    ((abs_mass_mul _ _).trans (by simpa [abs_of_nonneg hb,hbm] using hcD))

private lemma diff (v : Lattice k) : Smooth U 1 (atom v-1) := by
  refine ⟨‖U v‖₊,2,fun n hn =>
    ⟨geomKernel (atom v) 1 n,latticeAverage_pos _ (fun i _ => mul_nonneg (pow_nonneg (atom_nonneg _) i)
      (pow_nonneg zero_le_one _)),latticeAverage_mass hn (by simp),?_,?_⟩⟩
  · simp only [geomKernel,latticeAverage,one_pow,mul_one,radius,coeff_smul]
    refine (Finset.sup_mono Finsupp.support_smul).trans (AddMonoidAlgebra.supDegree_sum_le.trans ?_)
    refine Finset.sup_le fun i hi => (AddMonoidAlgebra.sup_support_pow_le (by simp)
      (fun x y => by rw [map_add]; exact nnnorm_add_le _ _) i (atom v)).trans ?_
    change i • (atom v).supDegree (fun v => ‖U v‖₊) ≤ _
    rw [supDegree_single_ne_zero v (one_ne_zero : (1:ℚ) ≠ 0),nsmul_eq_mul]
    gcongr
    exact_mod_cast (mem_range.mp hi).le
  · rw [geomKernel_sub,one_pow,
      abs_smul,abs_of_nonneg (by positivity : 0 ≤ (n:ℚ)⁻¹),map_smul,smul_eq_mul,pow_one,div_eq_inv_mul]
    gcongr
    rw [sub_eq_add_neg]
    refine (mass_mono (abs_add_le ..)).trans_eq ?_
    rw [abs_neg,abs_of_nonneg (pow_nonneg (atom_nonneg v) n),abs_of_nonneg zero_le_one]
    norm_num
end Smooth

private def smoothIdeal (U : Projection k d) (e : ℕ) : Ideal (LatticeRing k) where
  carrier := {z | Smooth U e z}
  zero_mem' := ⟨0,0,fun _ _ => ⟨1,zero_le_one,map_one mass,by simp,by simp⟩⟩
  add_mem' := fun hx hy => Smooth.add (U:=U) hx hy
  smul_mem' := fun a z ha => by
    change Smooth U e (a*z)
    simpa using (Smooth.base (U:=U) a).mul (show Smooth U e z from ha)

lemma smooth_of_cube {z : LatticeRing k} (hz : z ∈ (augmentationIdeal : Ideal (LatticeRing k)) ^ 3) :
    ∃ J K : ℝ, ∀ n : ℕ, 0 < n → ∃ b : LatticeRing k, 0 ≤ b ∧ mass b = 1 ∧
      energy U b ≤ J*(n:ℝ)^2 ∧ (mass |z*b| : ℝ) ≤ K/(n:ℝ)^3 ∧ energy U |z*b| ≤ J*K/n := by
  have h₁ : augmentationIdeal ≤ smoothIdeal U 1 := by
    rw [augmentation_span]
    exact Ideal.span_le.mpr (by rintro _ ⟨v,rfl⟩; exact Smooth.diff v)
  have h (n : ℕ) : augmentationIdeal ^ n ≤ smoothIdeal U n := by
    induction n with
    | zero => exact fun x _ => Smooth.base x
    | succ n ih =>
      rw [pow_succ]
      exact Ideal.mul_le.mpr fun x hx y hy => (ih hx : Smooth U n x).mul (h₁ hy : Smooth U 1 y)
  obtain ⟨A,B,hB⟩ := h 3 hz
  let C := radius U z + A
  refine ⟨(C:ℝ)^2,B,fun n hn => ?_⟩
  obtain ⟨b,hb,hm,hbr,he⟩ := hB n hn
  have hC : radius U z + radius U b ≤ C*n := by
    rw [mul_comm,mul_add]
    exact add_le_add (le_mul_of_one_le_left zero_le (by exact_mod_cast hn)) hbr
  have hb' : (radius U b:ℝ) ≤ (C:ℝ)*n := NNReal.coe_le_coe.mpr (le_add_left le_rfl |>.trans hC)
  have hz' : (radius U |z*b|:ℝ) ≤ (C:ℝ)*n := by
    rw [radius_abs]
    exact NNReal.coe_le_coe.mpr ((radius_mul z b).trans hC)
  have he' : (mass |z*b| : ℝ) ≤ (B:ℝ)/(n:ℝ)^3 := by exact_mod_cast he
  refine ⟨b,hb,hm,by simpa [hm,mul_pow] using energy_radius hb hb',he',?_⟩
  refine (energy_radius (abs_nonneg _) hz').trans ((mul_le_mul_of_nonneg_right he' (sq_nonneg _)).trans_eq ?_)
  field_simp
end
end OAI.EuclideanRamsey.Discrete
