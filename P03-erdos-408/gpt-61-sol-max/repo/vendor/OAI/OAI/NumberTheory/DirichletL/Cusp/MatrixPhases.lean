module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.ChineseRemainder.AdditiveCharacters
public import OAI.NumberTheory.DirichletL.Arithmetic.EisensteinIdeals

@[expose] public section

namespace OAI

open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap
noncomputable section

namespace ShortDraftCusp

variable {R : Type*} [CommRing R]

def U (t : R)  := !![1,t;0,1]
def L (t : R)  := !![1,0;t,1]


end ShortDraftCusp

namespace ShortDraftConcretePhase
open ShortDraftTrace

end ShortDraftConcretePhase

namespace ShortDraftGauss

open Complex
open scoped ComplexConjugate

variable {F : Type*} [Field F] [Fintype F]

theorem norm_gaussSum_eq_sqrt_card (χ : MulChar F ℂ)  ψ 
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  let g := gaussSum χ ψ
  have hprod : g * conj g = (Fintype.card F : ℂ) := by
    have h := gaussSum_mul_gaussSum_eq_card hχ hψ
    rw [← star_gaussSum_eq] at h
    simpa only [g, Complex.star_def] using h
  have hnorm : ‖g‖ ^ 2 = (Fintype.card F : ℝ) := by
    apply Complex.ofReal_injective
    calc
      ((‖g‖ ^ 2 : ℝ) : ℂ) = (‖g‖ : ℂ) ^ 2 := by norm_cast
      _ = g * conj g := (Complex.mul_conj' g).symm
      _ = (Fintype.card F : ℂ) := hprod
      _ = ((Fintype.card F : ℝ) : ℂ) := by norm_cast
  have hcard : (0 : ℝ) ≤ Fintype.card F := by positivity
  have hsqrt := Real.sq_sqrt hcard
  nlinarith [norm_nonneg g, Real.sqrt_nonneg (Fintype.card F)]

theorem norm_normalized_gaussSum (χ : MulChar F ℂ)  ψ 
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖((Real.sqrt (Fintype.card F) : ℝ) : ℂ)⁻¹ * gaussSum χ ψ‖ = 1 := by
  have hcard : (0 : ℝ) < Fintype.card F := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  have hsqrt : Real.sqrt (Fintype.card F) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcard)
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 hcard), norm_gaussSum_eq_sqrt_card χ ψ hχ hψ]
  exact inv_mul_cancel₀ hsqrt

end ShortDraftGauss

namespace EisensteinRayPhase





end EisensteinRayPhase

namespace ShortDraftSextic
open scoped Classical
variable {R : Type*} [CommRing R]

theorem sextic_power_is_unit_mask (χ : MulChar R ℂ)
    (hχ : χ ^ 6 = 1)  u  :
    χ (u ^ 6) = if IsUnit u then 1 else 0 := by
  classical
  rw [map_pow, ← MulChar.pow_apply' χ (by decide : 6 ≠ 0), hχ]
  rfl

end ShortDraftSextic

namespace ShortDraftGaussJacobi
open Finset

variable {F : Type*} [Field F] [Fintype F]

end ShortDraftGaussJacobi

namespace ShortDraftQuadraticGauss
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem quadratic_gauss_as_square_phase  ψ 
    (hchar : ringChar F ≠ 2) (hψ : ψ ≠ 1) :
    gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ =
      ∑ x : F, ψ (x ^ 2) := by
  have hfiber : (∑ x : F, ψ (x ^ 2)) =
      ∑ y : F, (#{x : F | x ^ 2 = y}.toFinset : ℂ) * ψ y := by
    rw [← Finset.sum_fiberwise (s := Finset.univ)
      (g := fun x : F => x ^ 2) (f := fun x : F => ψ (x ^ 2))]
    apply Finset.sum_congr rfl
    intro y _
    have hterm : (∑ x ∈ Finset.univ with x ^ 2 = y, ψ (x ^ 2)) =
        (#{x : F | x ^ 2 = y}.toFinset : ℂ) * ψ y := by
      rw [Finset.sum_congr rfl (fun x hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [hx])]
      simp
    exact hterm
  have hcount (y : F) :
      (#{x : F | x ^ 2 = y}.toFinset : ℂ) =
        (quadraticChar F y : ℂ) + 1 := by
    exact_mod_cast quadraticChar_card_sqrts hchar y
  rw [hfiber]
  simp_rw [hcount, add_mul]
  rw [Finset.sum_add_distrib]
  have hzero : (∑ y : F, ψ y) = 0 := AddChar.sum_eq_zero_of_ne_one hψ
  simp only [one_mul, hzero, add_zero]
  rfl

end ShortDraftQuadraticGauss

namespace ShortDraftQuotientPhase
variable {A B : Type*} [CommGroup A] [CommGroup B]

end ShortDraftQuotientPhase

namespace EisensteinEPrimaryPhase

abbrev Coord := ZMod 4 × ZMod 4


def mul (x y : Coord)  :=
  (x.1 * y.1 - x.2 * y.2,
   x.1 * y.2 + x.2 * y.1 - x.2 * y.2)

def odd (x : Coord)  := x.1.val % 2 = 1 ∨ x.2.val % 2 = 1

instance : DecidablePred odd := fun x =>
  inferInstanceAs (Decidable (x.1.val % 2 = 1 ∨ x.2.val % 2 = 1))









theorem odd_mul  x y  (hx : odd x) (hy : odd y) : odd (mul x y) := by
  decide +revert

end EisensteinEPrimaryPhase

namespace ShortDraftGaussianPhaseTable

end ShortDraftGaussianPhaseTable

namespace ActualEisensteinCoordinates
abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K
instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
theorem hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K) 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ K
def omega  := hζ.toInteger
def pb  := hζ.integralPowerBasis

theorem pb_dim : pb.dim = 2 := by
  simp [pb, Nat.totient_prime Nat.prime_three]

theorem pb_gen : pb.gen = omega := hζ.integralPowerBasis_gen

theorem exists_coordinates  x  :
    ∃ a b : ℤ, x = (a : O) + (b : O) * omega := by
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let a : ℤ := (pb.basis.repr x) i0
  let b : ℤ := (pb.basis.repr x) i1
  refine ⟨a, b, ?_⟩
  have hsum := pb.basis.sum_repr x
  have huniv : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    grind [pb_dim]
  rw [huniv] at hsum
  have hne : i0 ≠ i1 := by decide
  have hnot : i0 ∉ ({i1} : Finset (Fin pb.dim)) := by
    simpa only [Finset.mem_singleton] using hne
  rw [Finset.sum_insert hnot, Finset.sum_singleton] at hsum
  simp only [pb.basis_eq_pow] at hsum
  have hi0 : (i0 : ℕ) = 0 := rfl
  have hi1 : (i1 : ℕ) = 1 := rfl
  simpa [a, b, hi0, hi1, pb_gen, smul_eq_mul, mul_comm] using hsum.symm

def i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
def i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩

def eval (a b : ℤ)  := (a : O) + (b : O) * omega

theorem eval_basis  a b  :
    eval a b = a • pb.basis i0 + b • pb.basis i1 := by
  simp_all [eval, i0, i1, pb_gen]

theorem unique_coordinates {a b c d : ℤ}
    (h : eval a b = eval c d) : a = c ∧ b = d := by
  have h0 := congrArg (fun x : O => (pb.basis.repr x) i0) h
  have h1 := congrArg (fun x : O => (pb.basis.repr x) i1) h
  have hne : i0 ≠ i1 := by decide
  rw [eval_basis, eval_basis] at h0 h1
  constructor
  · simpa only [map_add, map_smul, pb.basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, ite_eq_left, ite_eq_right hne.symm,
      smul_eq_mul, mul_one, mul_zero, add_zero] using h0
  · simpa only [map_add, map_smul, pb.basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, ite_eq_left, ite_eq_right hne,
      smul_eq_mul, mul_one, mul_zero, zero_add] using h1

theorem omega_sq : omega ^ 2 = -omega - 1 := by
  simpa [omega] using IsCyclotomicExtension.Rat.Three.eta_sq hζ

theorem eval_mul  a b c d  :
    eval a b * eval c d = eval (a*c-b*d) (a*d+b*c-b*d) := by
  simp only [eval]
  calc
    ((a : O) + (b : O) * omega) * ((c : O) + (d : O) * omega)
      = (a : O) * c + ((a : O) * d + (b : O) * c) * omega +
          ((b : O) * d) * omega ^ 2 := by ring
    _ = ((a*c-b*d : ℤ) : O) + ((a*d+b*c-b*d : ℤ) : O) * omega := by
          rw [omega_sq]
          push_cast
          ring

theorem eval_congr_mod_four {a b c d : ℤ}
    (ha : (a : ZMod 4) = c) (hb : (b : ZMod 4) = d) :
    ∃ z : O, eval a b - eval c d = 4 * z := by
  have ha4 : (4 : ℤ) ∣ a-c := (ZMod.intCast_eq_intCast_iff_dvd_sub c a 4).mp ha.symm
  have hb4 : (4 : ℤ) ∣ b-d := (ZMod.intCast_eq_intCast_iff_dvd_sub d b 4).mp hb.symm
  obtain ⟨u, hu⟩ := ha4
  obtain ⟨v, hv⟩ := hb4
  refine ⟨(u : O) + (v : O) * omega, ?_⟩
  dsimp [eval]
  rw [show a = c + 4*u by omega, show b = d + 4*v by omega]
  push_cast
  ring

theorem exists_pair  x  :
    ∃ p : ℤ × ℤ, eval p.1 p.2 = x := by
  obtain ⟨a, b, h⟩ := exists_coordinates x
  exact ⟨(a, b), h.symm⟩

def coords (x : O)  := Classical.choose (exists_pair x)

theorem eval_coords  x  : eval (coords x).1 (coords x).2 = x :=
  Classical.choose_spec (exists_pair x)

def residue (x : O) : EisensteinEPrimaryPhase.Coord :=
  ((coords x).1, (coords x).2)

theorem residue_eval  a b  :
    residue (eval a b) = ((a : ZMod 4), (b : ZMod 4)) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext (congrArg (fun n : ℤ => (n : ZMod 4)) h.1)
    (congrArg (fun n : ℤ => (n : ZMod 4)) h.2)

theorem residue_mul  x y  :
    residue (x*y) = EisensteinEPrimaryPhase.mul (residue x) (residue y) := by
  calc
    residue (x*y) = residue (eval (coords x).1 (coords x).2 *
        eval (coords y).1 (coords y).2) := by rw [eval_coords, eval_coords]
    _ = EisensteinEPrimaryPhase.mul (residue x) (residue y) := by
      rw [eval_mul, residue_eval]
      simp [residue, EisensteinEPrimaryPhase.mul]

theorem congr_mod_four_of_residue_eq  {x y} 
    (h : residue x = residue y) : ∃ z : O, x-y = 4*z := by
  rw [←eval_coords x, ←eval_coords y]
  apply eval_congr_mod_four
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

def lift (v : EisensteinEPrimaryPhase.Coord)  :=
  eval (v.1.val : ℤ) (v.2.val : ℤ)

theorem residue_lift  v  :
    residue (lift v) = v := by
  simp [lift, residue_eval]

theorem residue_two : residue (2 : O) = (2, 0) := by
  have h : eval 2 0 = (2 : O) := by simp [eval]
  rw [← h, residue_eval]
  norm_num

theorem not_odd_mul_two  v  :
    ¬ EisensteinEPrimaryPhase.odd
      (EisensteinEPrimaryPhase.mul (2, 0) v) := by
  decide +revert

theorem not_odd_cast_zero (v : EisensteinEPrimaryPhase.Coord)
    (h : ¬ EisensteinEPrimaryPhase.odd v) :
    (ZMod.cast v.1 : ZMod 2) = 0 ∧
      (ZMod.cast v.2 : ZMod 2) = 0 := by
  decide +revert

theorem odd_residue_iff_not_two_dvd  x  :
    EisensteinEPrimaryPhase.odd (residue x) ↔ ¬ (2 : O) ∣ x := by
  constructor
  · intro hx hdiv
    obtain ⟨y, hy⟩ := hdiv
    rw [hy, residue_mul, residue_two] at hx
    exact not_odd_mul_two (residue y) hx
  · intro hdiv
    by_contra hodd
    obtain ⟨ha, hb⟩ := not_odd_cast_zero (residue x) hodd
    have ha' : ((coords x).1 : ZMod 2) = 0 := by
      simp_all [residue]
    have hb' : ((coords x).2 : ZMod 2) = 0 := by
      simp_all [residue]
    obtain ⟨a, ha2⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (coords x).1 2).mp ha'
    obtain ⟨b, hb2⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (coords x).2 2).mp hb'
    apply hdiv
    refine ⟨eval a b, ?_⟩
    rw [← eval_coords x]
    dsimp [eval]
    rw [ha2, hb2]
    push_cast
    ring

end ActualEisensteinCoordinates

end

end OAI
