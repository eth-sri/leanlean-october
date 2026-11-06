module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Arithmetic.EisensteinCoordinates

@[expose] public section

namespace OAI

open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap
noncomputable section
open Finset Complex

open scoped Classical

namespace GaussCRT

end GaussCRT

 

namespace IdealGaussCRT

variable {T R S : Type*} [CommRing T] [CommRing R] [CommRing S]

def leftAddChar (e : T ≃+* R × S) (ψ : AddChar T ℂ) : AddChar R ℂ where
  toFun z := ψ (e.symm (z, 0))
  map_zero_eq_one' := by
    change ψ (e.symm (0 : R × S)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ (e.symm (z + w, 0)) = ψ (e.symm (z, 0)) * ψ (e.symm (w, 0))
    rw [show (z + w, (0 : S)) = (z, 0) + (w, 0) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

def rightAddChar (e : T ≃+* R × S) (ψ : AddChar T ℂ) : AddChar S ℂ where
  toFun z := ψ (e.symm (0, z))
  map_zero_eq_one' := by
    change ψ (e.symm (0 : R × S)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ (e.symm (0, z + w)) = ψ (e.symm (0, z)) * ψ (e.symm (0, w))
    rw [show ((0 : R), z + w) = (0, z) + (0, w) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

theorem addChar_crt_factor (e : T ≃+* R × S)  ψ  (x : T) :
    ψ x = leftAddChar e ψ (e x).1 * rightAddChar e ψ (e x).2 := by
  let z := e x
  have hz : (z.1, (0 : S)) + ((0 : R), z.2) = z := by ext <;> simp
  calc
    ψ x = ψ (e.symm z) := by simp [z]
    _ = ψ (e.symm (z.1, 0) + e.symm (0, z.2)) := by rw [← map_add, hz]
    _ = _ := by rw [AddChar.map_add_eq_mul]; rfl

theorem gauss_sum_crt [Fintype T] [Fintype R] [Fintype S]
    (e : T ≃+* R × S)  χR   χS 
     ψ  :
    (∑ x : T, χR (e x).1 * χS (e x).2 * ψ x) =
      gaussSum χR (leftAddChar e ψ) * gaussSum χS (rightAddChar e ψ) := by
  simp_rw [addChar_crt_factor e ψ]
  let F : R × S → ℂ := fun z =>
    χR z.1 * χS z.2 * leftAddChar e ψ z.1 * rightAddChar e ψ z.2
  calc
    (∑ x : T,
      χR (e x).1 * χS (e x).2 *
        (leftAddChar e ψ (e x).1 * rightAddChar e ψ (e x).2)) =
        ∑ x : T, F (e x) := by congr 1; ext x; simp [F]; ring
    _ = ∑ z : R × S, F z := Equiv.sum_comp e.toEquiv F
    _ = ∑ z : R, ∑ w : S, F (z, w) := Fintype.sum_prod_type F
    _ = gaussSum χR (leftAddChar e ψ) * gaussSum χS (rightAddChar e ψ) := by
      simp only [F, gaussSum]
      rw [Finset.sum_mul_sum]
      grind

theorem gauss_sum_ideal_crt  {A}  [CommRing A]
     I J   h 
    [Fintype (A ⧸ I * J)] [Fintype (A ⧸ I)] [Fintype (A ⧸ J)]
     χI   χJ 
     ψ  :
    (∑ x : A ⧸ I * J,
      χI (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) x) *
      χJ (Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) x) * ψ x) =
      gaussSum χI (leftAddChar (Ideal.quotientMulEquivQuotientProd I J h) ψ) *
      gaussSum χJ (rightAddChar (Ideal.quotientMulEquivQuotientProd I J h) ψ) := by
  let e := Ideal.quotientMulEquivQuotientProd I J h
  convert gauss_sum_crt e χI χJ ψ using 1
  congr 1
  ext x
  simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
    Ideal.quotientMulEquivQuotientProd_snd]

noncomputable def quotientAddChar {A : Type*} [CommRing A]
    (I : Ideal A) (ψ : AddChar A ℂ)
    (hper : ∀ a : A, a ∈ I → ψ a = 1) : AddChar (A ⧸ I) ℂ where
  toFun := fun x => Quotient.liftOn' x ψ (by
    intro a b hab
    have hsub : a - b ∈ I := I.quotientRel_def.mp hab
    have h := ψ.map_add_eq_mul (a - b) b
    simp_all)
  map_zero_eq_one' := by
    change ψ 0 = 1
    exact AddChar.map_zero_eq_one ψ
  map_add_eq_mul' := by
    intro x y
    refine Quotient.inductionOn₂' x y ?_
    intro a b
    exact AddChar.map_add_eq_mul ψ a b

section
variable {A : Type*} [CommRing A]
include A



theorem principal_coprime_of_bezout    
    {a b u v : A} (h : u * a + v * b = 1) :
    IsCoprime (Ideal.span {a}) (Ideal.span {b}) := by
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨u * a, ?_, v * b, ?_, h⟩
  · exact Ideal.mem_span_singleton.mpr ⟨u, by ring⟩
  · exact Ideal.mem_span_singleton.mpr ⟨v, by ring⟩

theorem bezout_of_principal_coprime    
     {a b}  (h : IsCoprime (Ideal.span {a}) (Ideal.span {b})) :
    ∃ u v : A, u * a + v * b = 1 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hy
  refine ⟨u, v, ?_⟩
  rw [hu, hv] at hxy
  convert hxy using 1; ring

section
variable {a b u v : A} (hbez : u * a + v * b = 1)
include a b u v hbez

theorem crt_left_inverse_coordinate    
        (x : A) :
    (Ideal.quotientMulEquivQuotientProd
      (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm
        (Ideal.Quotient.mk (Ideal.span {a}) x, 0) =
      Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) (x * v * b) := by
  let I : Ideal A := Ideal.span {a}
  let J : Ideal A := Ideal.span {b}
  let e := Ideal.quotientMulEquivQuotientProd I J
    (principal_coprime_of_bezout hbez)
  apply e.injective
  apply Prod.ext
  · change (e (e.symm (Ideal.Quotient.mk I x, 0))).1 =
      (e (Ideal.Quotient.mk (I * J) (x * v * b))).1
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    change x - x * v * b ∈ I
    rw [Ideal.mem_span_singleton]
    refine ⟨x * u, ?_⟩
    grind
  · change (e (e.symm (Ideal.Quotient.mk I x, 0))).2 =
      (e (Ideal.Quotient.mk (I * J) (x * v * b))).2
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_snd,
      Ideal.Quotient.factor_mk]
    aesop

theorem crt_right_inverse_coordinate    
         y  :
    (Ideal.quotientMulEquivQuotientProd
      (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm
        (0, Ideal.Quotient.mk (Ideal.span {b}) y) =
      Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) (y * u * a) := by
  let I : Ideal A := Ideal.span {a}
  let J : Ideal A := Ideal.span {b}
  let e := Ideal.quotientMulEquivQuotientProd I J
    (principal_coprime_of_bezout hbez)
  apply e.injective
  apply Prod.ext
  · change (e (e.symm (0, Ideal.Quotient.mk J y))).1 =
      (e (Ideal.Quotient.mk (I * J) (y * u * a))).1
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.Quotient.factor_mk]
    aesop
  · change (e (e.symm (0, Ideal.Quotient.mk J y))).2 =
      (e (Ideal.Quotient.mk (I * J) (y * u * a))).2
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_snd,
      Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    change y - y * u * a ∈ J
    rw [Ideal.mem_span_singleton]
    refine ⟨y * v, ?_⟩
    grind

end

end

noncomputable def rawTraceChar {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A) : AddChar A ℂ where
  toFun x := ψ (ι x / (ι c * lam))
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [map_add, add_div, AddChar.map_add_eq_mul]

theorem rawTraceChar_period {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ)  lam   c 
    (hc : ι c ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1)
    (x : A) (hx : x ∈ Ideal.span {c}) :
    rawTraceChar ι ψ lam c x = 1 := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  rw [hy]
  change ψ (ι (c * y) / (ι c * lam)) = 1
  rw [map_mul]
  have hfrac : ι c * ι y / (ι c * lam) = ι y / lam := by
    field_simp
  rw [hfrac]
  exact hbase y

noncomputable def traceModChar {A } [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam ) (c )
    (hc : ι c ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1)  :=
  quotientAddChar (Ideal.span {c}) (rawTraceChar ι ψ lam c)
    (rawTraceChar_period ι ψ lam c hc hlam hbase)

@[simp] theorem traceModChar_mk  {A}  [CommRing A]
     ι   ψ   lam   c 
     hc   hlam 
     hbase  (x : A) :
    traceModChar ι ψ lam c hc hlam hbase
      (Ideal.Quotient.mk (Ideal.span {c}) x) =
      ψ (ι x / (ι c * lam)) := rfl

noncomputable def traceProdChar {A } [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam ) (a b )
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1)  :=
  quotientAddChar ((Ideal.span {a}) * (Ideal.span {b}))
    (rawTraceChar ι ψ lam (a * b)) (by
      intro x hx
      have hx' : x ∈ Ideal.span {a * b} := by
        simpa only [Ideal.span_singleton_mul_span_singleton] using hx
      simp_all [rawTraceChar_period])

section
variable {A : Type*} [CommRing A]
include A

section
variable (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
include ι ψ lam

@[simp] theorem traceProdChar_mk    
           a b 
     ha   hb   hlam 
     hbase  (x : A) :
    traceProdChar ι ψ lam a b ha hb hlam hbase
      (Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) x) =
      ψ (ι x / (ι (a * b) * lam)) := rfl

section
variable {a b u v : A} (hbez : u * a + v * b = 1) (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0) (hbase : ∀ x : A, ψ (ι x / lam) = 1)
include a b u v hbez ha hb hlam hbase

theorem leftAddChar_traceProd    
         
       
         
      :
    leftAddChar
      (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez))
      (traceProdChar ι ψ lam a b ha hb hlam hbase) =
      (traceModChar ι ψ lam a ha hlam hbase).mulShift
        (Ideal.Quotient.mk (Ideal.span {a}) v) := by
  ext z
  refine Quotient.inductionOn' z ?_
  intro x
  change traceProdChar ι ψ lam a b ha hb hlam hbase
      ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez)).symm
        (Ideal.Quotient.mk (Ideal.span {a}) x, 0)) =
    (traceModChar ι ψ lam a ha hlam hbase).mulShift
      (Ideal.Quotient.mk (Ideal.span {a}) v)
      (Ideal.Quotient.mk (Ideal.span {a}) x)
  rw [crt_left_inverse_coordinate hbez x]
  simp only [traceProdChar_mk, AddChar.mulShift_apply, ← map_mul,
    traceModChar_mk]
  congr 1
  simp only [map_mul]
  field_simp

theorem rightAddChar_traceProd    
         
       
         
      :
    rightAddChar
      (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez))
      (traceProdChar ι ψ lam a b ha hb hlam hbase) =
      (traceModChar ι ψ lam b hb hlam hbase).mulShift
        (Ideal.Quotient.mk (Ideal.span {b}) u) := by
  ext z
  refine Quotient.inductionOn' z ?_
  intro y
  change traceProdChar ι ψ lam a b ha hb hlam hbase
      ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez)).symm
        (0, Ideal.Quotient.mk (Ideal.span {b}) y)) =
    (traceModChar ι ψ lam b hb hlam hbase).mulShift
      (Ideal.Quotient.mk (Ideal.span {b}) u)
      (Ideal.Quotient.mk (Ideal.span {b}) y)
  rw [crt_right_inverse_coordinate hbez y]
  simp only [traceProdChar_mk, AddChar.mulShift_apply, ← map_mul,
    traceModChar_mk]
  congr 1
  simp only [map_mul]
  field_simp

end

end

section
variable {a b u v : A}
include a b u v

section
variable (hbez : u * a + v * b = 1)
include hbez

theorem bezout_inverse_left    
        :
    (Ideal.Quotient.mk (Ideal.span {a}) b) *
      (Ideal.Quotient.mk (Ideal.span {a}) v) = 1 := by
  rw [← map_mul]
  apply Ideal.Quotient.eq.mpr
  change b * v - 1 ∈ Ideal.span {a}
  rw [Ideal.mem_span_singleton]
  refine ⟨-u, ?_⟩
  grind

theorem bezout_inverse_right    
        :
    (Ideal.Quotient.mk (Ideal.span {b}) a) *
      (Ideal.Quotient.mk (Ideal.span {b}) u) = 1 := by
  rw [← map_mul]
  apply Ideal.Quotient.eq.mpr
  change a * u - 1 ∈ Ideal.span {b}
  rw [Ideal.mem_span_singleton]
  refine ⟨-v, ?_⟩
  grind

end

theorem gauss_shift_bezout_left    
      [Fintype (A ⧸ Ideal.span {a})]
    (hbez : u * a + v * b = 1)
    (χ : MulChar (A ⧸ Ideal.span {a}) ℂ)
     ψ  :
    gaussSum χ (ψ.mulShift (Ideal.Quotient.mk (Ideal.span {a}) v)) =
      χ (Ideal.Quotient.mk (Ideal.span {a}) b) * gaussSum χ ψ := by
  let mb := Ideal.Quotient.mk (Ideal.span {a}) b
  let mv := Ideal.Quotient.mk (Ideal.span {a}) v
  have hprod : mb * mv = 1 := bezout_inverse_left hbez
  have hu : IsUnit mv := IsUnit.of_mul_eq_one_right mb hprod
  have hχ : χ mb * χ mv = 1 := by rw [← map_mul, hprod, map_one]
  have hshift := gaussSum_mulShift χ ψ hu.unit
  have hshift' : χ mv * gaussSum χ (ψ.mulShift mv) = gaussSum χ ψ := by
    simpa only [hu.unit_spec] using hshift
  calc
    gaussSum χ (ψ.mulShift mv) =
        (χ mb * χ mv) * gaussSum χ (ψ.mulShift mv) := by rw [hχ, one_mul]
    _ = χ mb * (χ mv * gaussSum χ (ψ.mulShift mv)) := by ring
    _ = χ mb * gaussSum χ ψ := by rw [hshift']

theorem gauss_shift_bezout_right    
      [Fintype (A ⧸ Ideal.span {b})]
    (hbez : u * a + v * b = 1)
    (χ : MulChar (A ⧸ Ideal.span {b}) ℂ)
     ψ  :
    gaussSum χ (ψ.mulShift (Ideal.Quotient.mk (Ideal.span {b}) u)) =
      χ (Ideal.Quotient.mk (Ideal.span {b}) a) * gaussSum χ ψ := by
  let ma := Ideal.Quotient.mk (Ideal.span {b}) a
  let mu := Ideal.Quotient.mk (Ideal.span {b}) u
  have hprod : ma * mu = 1 := bezout_inverse_right hbez
  have hu : IsUnit mu := IsUnit.of_mul_eq_one_right ma hprod
  have hχ : χ ma * χ mu = 1 := by rw [← map_mul, hprod, map_one]
  have hshift := gaussSum_mulShift χ ψ hu.unit
  have hshift' : χ mu * gaussSum χ (ψ.mulShift mu) = gaussSum χ ψ := by
    simpa only [hu.unit_spec] using hshift
  calc
    gaussSum χ (ψ.mulShift mu) =
        (χ ma * χ mu) * gaussSum χ (ψ.mulShift mu) := by rw [hχ, one_mul]
    _ = χ ma * (χ mu * gaussSum χ (ψ.mulShift mu)) := by ring
    _ = χ ma * gaussSum χ ψ := by rw [hshift']

end

section
variable (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
include ι ψ lam

theorem gauss_sum_trace_crt    
         
    {a b u v : A} (hbez : u * a + v * b = 1)
    [Fintype (A ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (A ⧸ Ideal.span {a})]
    [Fintype (A ⧸ Ideal.span {b})]
     ha   hb   hlam 
     hbase 
     χa 
     χb  :
    (∑ x : A ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      traceProdChar ι ψ lam a b ha hb hlam hbase x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (traceModChar ι ψ lam a ha hlam hbase) *
      gaussSum χb (traceModChar ι ψ lam b hb hlam hbase) := by
  
  have h := gauss_sum_ideal_crt (Ideal.span {a}) (Ideal.span {b})
    (principal_coprime_of_bezout hbez) χa χb
    (traceProdChar ι ψ lam a b ha hb hlam hbase)
  rw [leftAddChar_traceProd ι ψ lam hbez ha hb hlam hbase,
      rightAddChar_traceProd ι ψ lam hbez ha hb hlam hbase,
      gauss_shift_bezout_left hbez χa (traceModChar ι ψ lam a ha hlam hbase),
      gauss_shift_bezout_right hbez χb (traceModChar ι ψ lam b hb hlam hbase)] at h
  calc
    _ = (χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
          gaussSum χa (traceModChar ι ψ lam a ha hlam hbase)) *
        (χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
          gaussSum χb (traceModChar ι ψ lam b hb hlam hbase)) := h
    _ = _ := by ring

theorem gauss_sum_trace_crt_of_coprime    
         
     a b 
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    [Fintype (A ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (A ⧸ Ideal.span {a})]
    [Fintype (A ⧸ Ideal.span {b})]
     ha   hb   hlam 
     hbase 
     χa 
     χb  :
    (∑ x : A ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      traceProdChar ι ψ lam a b ha hb hlam hbase x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (traceModChar ι ψ lam a ha hlam hbase) *
      gaussSum χb (traceModChar ι ψ lam b hb hlam hbase) := by
  obtain ⟨u, v, hbez⟩ := bezout_of_principal_coprime hcop
  solve_by_elim [gauss_sum_trace_crt]

end

end

end IdealGaussCRT

end

end OAI
