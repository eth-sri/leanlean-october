module

public import OAI.NumberTheory.DirichletL.Arithmetic.LatticeCount

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical

namespace ActualEisensteinCubic

section

open ActualEisensteinCoordinates ShortDraftLatticeCount

theorem omega_sq_for_norm : omega ^ 2 = -omega - 1 := by
  simpa [omega] using
    IsCyclotomicExtension.Rat.Three.eta_sq
      (IsCyclotomicExtension.zeta_spec 3 ℚ K)

theorem conjO_eval_coordinates (a b : ℤ) :
    conjO (eval a b) = eval (a - b) (-b) := by
  have hω : ActualEisensteinCoordinates.omega = omega := rfl
  simp only [eval, map_add, map_mul, map_intCast, hω, conjO_omega]
  rw [omega_sq_for_norm]
  push_cast
  ring

theorem coordinate_norm_eq_mul_conjO (p : O) :
    ((q (coords p) : ℤ) : O) = p * conjO p := by
  let a := (coords p).1
  let b := (coords p).2
  have hp : p = eval a b := (eval_coords p).symm
  symm
  calc
    p * conjO p = eval a b * eval (a - b) (-b) := by
      rw [hp, conjO_eval_coordinates]
    _ = ((q (coords p) : ℤ) : O) := by
      rw [eval_mul]
      simp only [eval, q]
      dsimp [a, b]
      push_cast
      ring

theorem algebraNorm_eq_coordinate_norm (p : O) :
    Algebra.norm ℤ p = q (coords p) := by
  have h := (norm_int_eq_mul_conjO p).trans
    (coordinate_norm_eq_mul_conjO p).symm
  exact_mod_cast h

theorem qNat_eq_absNorm_span (p : O) :
    qNat p = Ideal.absNorm (Ideal.span {p}) := by
  rw [Ideal.absNorm_span_singleton, algebraNorm_eq_coordinate_norm]
  unfold qNat
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg (qO_nonneg p),
    Int.natAbs_of_nonneg (qO_nonneg p)]

end

section

theorem prime_sixth_row_approx_ideal_norm
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (p : O) (hp : p ≠ 0)
    (hprime : (Ideal.span {p} : Ideal O).IsMaximal)
    (D : ℕ)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns,
      Ideal.absNorm (Ideal.span {n}) ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p ^ 6))‖ ≤
      (64 * (D / Ideal.absNorm (Ideal.span {p}) + 1) : ℕ) := by
  have hcol : ∀ n ∈ columns, ShortDraftLatticeCount.qNat n ≤ D := by
    intro n hn
    rw [qNat_eq_absNorm_span]
    exact hcolnorm n hn
  simpa only [qNat_eq_absNorm_span] using
    (prime_sixth_row_approx_maximal P hgood columns support weight p hp
      hprime D hsupport hcol hweight)

theorem sixth_power_eq_implies_same_prime_ideal
    (p q : O)
    (hp : (Ideal.span {p} : Ideal O).IsMaximal)
    (hq : (Ideal.span {q} : Ideal O).IsMaximal)
    (h : p ^ 6 = q ^ 6) :
    (Ideal.span {p} : Ideal O) = Ideal.span {q} := by
  have hq6 : q ^ 6 ∈ Ideal.span {q} :=
    Ideal.mem_span_singleton.mpr (dvd_pow_self q (by decide))
  have hp6 : p ^ 6 ∈ Ideal.span {q} := by rw [h]; exact hq6
  have hpmem : p ∈ Ideal.span {q} :=
    hq.isPrime.mem_of_pow_mem 6 hp6
  have hle : (Ideal.span {p} : Ideal O) ≤ Ideal.span {q} :=
    (Ideal.span_singleton_le_iff_mem _).mpr hpmem
  exact hp.eq_of_le hq.ne_top hle

theorem sixth_power_rows_injective
    {ι : Type*} (S : Finset ι) (P : ι → Ideal O) (p : ι → O)
    (hprime : ∀ i ∈ S, (P i).IsMaximal)
    (hgen : ∀ i ∈ S, P i = Ideal.span {p i})
    (hinj : Set.InjOn P (S : Set ι)) :
    Set.InjOn (fun i => p i ^ 6) (S : Set ι) := by
  intro i hi j hj heq
  have hsame : Ideal.span {p i} = (Ideal.span {p j} : Ideal O) :=
    sixth_power_eq_implies_same_prime_ideal (p i) (p j)
      (hgen i hi ▸ hprime i hi)
      (hgen j hj ▸ hprime j hj) heq
  apply hinj hi hj
  rw [hgen i hi, hgen j hj]
  exact hsame

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE

theorem rational_modulus_card (m : ℕ) (_hm : m ≠ 0) :
    Nat.card (O ⧸ Ideal.span {(m : O)}) = m ^ 2 := by
  have hnorm : Algebra.norm ℤ (m : O) = (m : ℤ) ^ 2 := by
    have h := Algebra.norm_algebraMap_of_basis
      EisensteinEmbedding.pb.basis (m : ℤ)
    simpa [EisensteinEmbedding.pb_dim] using h
  calc
    Nat.card (O ⧸ Ideal.span {(m : O)}) =
        Ideal.absNorm (Ideal.span {(m : O)}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = (Algebra.norm ℤ (m : O)).natAbs :=
      Ideal.absNorm_span_singleton (m : O)
    _ = m ^ 2 := by rw [hnorm]; simp

private theorem mk_eval_congr_mod (m : ℕ) (a b c d : ℤ)
    (ha : (a : ZMod m) = c) (hb : (b : ZMod m) = d) :
    Ideal.Quotient.mk (Ideal.span {(m : O)})
        (ActualEisensteinCoordinates.eval a b) =
      Ideal.Quotient.mk (Ideal.span {(m : O)})
        (ActualEisensteinCoordinates.eval c d) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  have hda : (m : ℤ) ∣ a - c :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub c a m).mp ha.symm
  have hdb : (m : ℤ) ∣ b - d :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub d b m).mp hb.symm
  obtain ⟨r, hr⟩ := hda
  obtain ⟨s, hs⟩ := hdb
  apply (Ideal.mem_span_singleton).mpr
  refine ⟨ActualEisensteinCoordinates.eval r s, ?_⟩
  dsimp [ActualEisensteinCoordinates.eval]
  rw [show a = c + m*r by omega, show b = d + m*s by omega]
  push_cast
  ring

noncomputable def rationalCoordMap (m : ℕ) :
    ZMod m × ZMod m → (O ⧸ Ideal.span {(m : O)}) :=
  fun ab => Ideal.Quotient.mk (Ideal.span {(m : O)})
    (ActualEisensteinCoordinates.eval (ZMod.cast ab.1) (ZMod.cast ab.2))

theorem rationalCoordMap_surjective (m : ℕ) :
    Function.Surjective (rationalCoordMap m) := by
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, b, hab⟩ := ActualEisensteinCoordinates.exists_coordinates z
  refine ⟨((a : ZMod m), (b : ZMod m)), ?_⟩
  change Ideal.Quotient.mk (Ideal.span {(m : O)})
      (ActualEisensteinCoordinates.eval (ZMod.cast (a : ZMod m))
        (ZMod.cast (b : ZMod m))) = _
  rw [hab]
  apply mk_eval_congr_mod
  · exact ZMod.intCast_zmod_cast _
  · exact ZMod.intCast_zmod_cast _

noncomputable def rationalCoordEquiv (m : ℕ) (hm : m ≠ 0) :
    ZMod m × ZMod m ≃ (O ⧸ Ideal.span {(m : O)}) := by
  letI : NeZero m := ⟨hm⟩
  letI : Finite (O ⧸ Ideal.span {(m : O)}) :=
    finite_quotient_span (by exact_mod_cast hm)
  letI : Fintype (O ⧸ Ideal.span {(m : O)}) := Fintype.ofFinite _
  refine Equiv.ofBijective (rationalCoordMap m) ?_
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · exact rationalCoordMap_surjective m
  · have hq : Fintype.card (O ⧸ Ideal.span {(m : O)}) = m ^ 2 := by
      simpa only [Nat.card_eq_fintype_card] using rational_modulus_card m hm
    simp [hq, Fintype.card_prod, sq]

theorem eisEmbedding_eval (a b : ℤ) :
    eisEmbedding (ActualEisensteinCoordinates.eval a b) =
      (a : ℂ) + (b : ℂ) * omega3 := by
  have hgen : ActualEisensteinCoordinates.omega =
      EisensteinEmbedding.pb.gen := by
    rw [← ActualEisensteinCoordinates.pb_gen]
    rfl
  rw [ActualEisensteinCoordinates.eval, hgen]
  change EisensteinEmbedding.embedding omega3 omega3_sq
    (a + b * EisensteinEmbedding.pb.gen : O) = _
  exact EisensteinEmbedding.embedding_apply_ab omega3 omega3_sq a b

theorem rationalCoordEquiv_apply (m : ℕ) (hm : m ≠ 0)
    (a b : ZMod m) :
    rationalCoordEquiv m hm (a,b) =
      Ideal.Quotient.mk (Ideal.span {(m : O)})
        (ActualEisensteinCoordinates.eval (ZMod.cast a) (ZMod.cast b)) := rfl

end

section

theorem cubic_roots_reduce_injective (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) {x y : O}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y) : x = y := by
  obtain ⟨i, hi, rfl⟩ := omega_primitive.eq_pow_of_pow_eq_one hx
  obtain ⟨j, hj, rfl⟩ := omega_primitive.eq_pow_of_pow_eq_one hy
  have hij : i = j := by
    apply (omega_reduced_primitive P hgood).pow_inj hi hj
    simpa only [map_pow] using hxy
  rw [hij]

theorem cubicChar_omega (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    cubicChar P hgood (Ideal.Quotient.mk P omega) =
      omega ^ ((Nat.card (O ⧸ P) - 1) / 3) := by
  let χ := cubicChar P hgood
  have hx : (χ (Ideal.Quotient.mk P omega)) ^ 3 = 1 := by
    rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
    exact MulChar.one_apply ((omega_reduced_primitive P hgood).isUnit (by decide))
  have hy : (omega ^ ((Nat.card (O ⧸ P) - 1) / 3)) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, omega_primitive.pow_eq_one, one_pow]
  apply cubic_roots_reduce_injective P hgood hx hy
  rw [map_pow]
  exact cubicChar_reduce P hgood (Ideal.Quotient.mk P omega)

theorem finiteSquarefreeRow_one
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) :
    finiteSquarefreeRow P hgood S 1 = 1 := by
  classical
  unfold finiteSquarefreeRow
  apply Finset.prod_eq_one
  intro i hi
  simp

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem breveE_int_trace_div (q u v : ℤ) (_hq : q ≠ 0) :
    ShortDraftTrace.breveE
      ((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q) =
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / q) := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj u v
  have hL : ((u : ℂ) + (v : ℂ) * omega3) / eisLam +
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) = (v : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q) +
      star (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q)))) = _
  rw [show star (((u : ℂ) + (v : ℂ) * omega3) / eisLam / q) =
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q by simp]
  rw [← add_div, hL]
  congr 1
  ring

theorem breveE_quadratic_coordinate (a b x y : ℤ)
    (hq : a*a - a*b + b*b ≠ 0) :
    let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
    let z : ℂ := (x : ℂ) + (y : ℂ) * omega3
    ShortDraftTrace.breveE (z ^ 2 / (c * eisLam)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((-b*x*x + 2*a*x*y + (b-a)*y*y : ℤ) : ℂ) /
        ((a*a-a*b+b*b : ℤ) : ℂ)) := by
  let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
  let z : ℂ := (x : ℂ) + (y : ℂ) * omega3
  let cb : ℂ := ((a-b : ℤ) : ℂ) - (b : ℂ) * omega3
  let q : ℤ := a*a-a*b+b*b
  let U : ℤ := (x*x-y*y)*(a-b)+b*(2*x*y-y*y)
  let V : ℤ := -b*x*x+2*a*x*y+(b-a)*y*y
  have hnorm : c * cb = (q : ℂ) := by
    dsimp [c, cb, q]
    push_cast
    linear_combination -(b : ℂ)^2 * omega3_sq
  have hnum : z ^ 2 * cb = (U : ℂ) + (V : ℂ) * omega3 := by
    dsimp [z, cb, U, V]
    push_cast
    linear_combination
      ((y : ℂ)^2 * ((a : ℂ)-(b : ℂ)-(b : ℂ)*omega3) -
        (b : ℂ) * (2*(x : ℂ)*(y : ℂ)-(y : ℂ)^2)) * omega3_sq
  have hqC : (q : ℂ) ≠ 0 := by
    dsimp [q]
    exact_mod_cast hq
  have hc : c ≠ 0 := by
    intro hc
    apply hqC
    rw [← hnorm, hc, zero_mul]
  have hcb : cb ≠ 0 := by
    intro hcb
    apply hqC
    rw [← hnorm, hcb, mul_zero]
  have hdiv : z ^ 2 / (c * eisLam) =
      ((z ^ 2 * cb) / eisLam) / q := by
    rw [← hnorm]
    field_simp [hc, hcb, eisLam_ne_zero]
  change ShortDraftTrace.breveE (z ^ 2 / (c * eisLam)) = _
  rw [hdiv, hnum, breveE_int_trace_div q U V (by simpa [q] using hq)]

end

end ActualEisensteinCubic

end

end OAI
