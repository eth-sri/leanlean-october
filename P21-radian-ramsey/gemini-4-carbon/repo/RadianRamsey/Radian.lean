module

public import OAI.Combinatorics.EuclideanRamsey.Main

@[expose] public section

namespace OAI
open scoped TensorProduct BigOperators
open Polynomial

namespace EuclideanRamsey.Radian

noncomputable def radianConfig (θ : ℝ) (k : Fin 9) : Space 2 :=
  WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]

def qv {R : Type*} [CommRing R] (z : R) : ℕ → ℕ → R
  | 0, 0 | 0, 1 => 1
  | 0, _ => 0
  | n + 1, 0 => (1 + z ^ 2) * qv z n 0
  | n + 1, 1 => (1 - z ^ 2) * qv z n 1 - 2 * z * qv z n 2
  | n + 1, _ => 2 * z * qv z n 1 + (1 - z ^ 2) * qv z n 2

theorem qv_two_ne : ∀ m : Fin 8, qv (2 : ℤ) (m.1 + 1) 2 ≠ 0 := by decide

def Ecl {R : Type*} [CommRing R] (z w : R) : Matrix (Fin 9) (Fin 9) R :=
  fun k j => qv z k (j / 3) * qv w k (j % 3)

def gj : ℕ → Matrix (Fin 9) (Fin 9) (ZMod 11)
  | 0 => 1
  | p + 1 =>
    let L := gj p
    let A := L * Ecl 1 2
    if h : p < 9 then
      let p' : Fin 9 := ⟨p, h⟩
      fun i k => if i = p' then (A p' p')⁻¹ * L p' k else L i k - A i p' * (A p' p')⁻¹ * L p' k
    else L

theorem gj_mul : gj 9 * Ecl (1 : ZMod 11) 2 = 1 := by decide +kernel

def idx : Option (Fin 2) → ℕ
  | none => 0
  | some i => i.1 + 1

def colEquiv : Fin 9 ≃ Option (Fin 2) × Option (Fin 2) :=
  finProdFinEquiv.symm.trans ((finSuccEquiv 2).prodCongr (finSuccEquiv 2))

theorem idx_colEquiv : ∀ j : Fin 9,
    idx (colEquiv j).1 = j.1 / 3 ∧ idx (colEquiv j).2 = j.1 % 3 := by decide

noncomputable section

theorem map_qv {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (z : R) (n m : ℕ) :
    f (qv z n m) = qv (f z) n m := by
  induction n generalizing m with
  | zero => match m with | 0 | 1 | _ + 2 => simp [qv]
  | succ _ ih => match m with | 0 | 1 | _ + 2 => simp [qv, map_ofNat, ih 0, ih 1, ih 2]

theorem map_Ecl {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (z w : R) :
    f.mapMatrix (Ecl z w) = Ecl (f z) (f w) := by ext; simp [Ecl, map_qv]

theorem det_Ecl_real {t : ℝ} (ht : Transcendental ℚ t) :
    (Ecl (C t) (X : ℝ[X])).det ≠ 0 := by
  have h11 : (Ecl (1 : ZMod 11) 2).det ≠ 0 := fun h => by
    have hd := congrArg Matrix.det gj_mul
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at hd; exact absurd hd (by decide)
  let Pℤ : ℤ[X][X] := (Ecl (C (X : ℤ[X])) (X : ℤ[X][X])).det
  have hPℤ : Pℤ ≠ 0 := fun h => h11 <| by
    let φ : ℤ[X][X] →+* ZMod 11 := eval₂RingHom ((evalRingHom 1).comp (mapRingHom (Int.castRingHom _))) 2
    have hd := congrArg φ h
    rw [map_zero, RingHom.map_det, map_Ecl] at hd
    convert hd <;> simp [φ]
  let ψ : ℤ[X] →+* ℚ[X] := mapRingHom (Int.castRingHom ℚ)
  have hPℚ : Pℤ.map ψ ≠ 0 := (Polynomial.map_ne_zero_iff (Polynomial.map_injective _ Int.cast_injective)).mpr hPℤ
  obtain ⟨m, hm⟩ : ∃ m, (Pℤ.map ψ).coeff m ≠ 0 := by
    by_contra! h; exact hPℚ (Polynomial.ext fun m => by simp [h m])
  intro h0
  have hmap : mapRingHom (aeval t).toRingHom (mapRingHom ψ Pℤ) = (Ecl (C t) (X : ℝ[X])).det := by
    rw [RingHom.map_det, RingHom.map_det, map_Ecl, map_Ecl]; congr 1; simp [ψ]
  exact ht ⟨(Pℤ.map ψ).coeff m, hm, by
    simpa only [coe_mapRingHom, coeff_map, coeff_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      using congrArg (fun p : ℝ[X] => p.coeff m) (hmap.trans h0)⟩

theorem half_angle {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) :
    (1 + Real.tan (θ / 2) ^ 2) * Real.cos θ = 1 - Real.tan (θ / 2) ^ 2 ∧
      (1 + Real.tan (θ / 2) ^ 2) * Real.sin θ = 2 * Real.tan (θ / 2) := by
  have h1 := Real.sin_sq_add_cos_sq (θ / 2)
  rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul', Real.sin_two_mul,
    show 2 * (θ / 2) / 2 = θ / 2 by ring, Real.tan_eq_sin_div_cos]
  exact ⟨by field_simp; linear_combination (Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) * h1,
    by field_simp; linear_combination Real.sin (θ / 2) * h1⟩

theorem tan_trans_ne {θ : ℝ} (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    Real.cos (θ / 2) ≠ 0 ∧ Real.tan (θ / 2) ≠ 0 :=
  ⟨fun h => ht (by rw [Real.tan_eq_sin_div_cos, h, div_zero]; exact isAlgebraic_zero),
   fun h => ht (h ▸ isAlgebraic_zero)⟩

theorem qv_trig {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) (n : ℕ) :
    qv (Real.tan (θ / 2)) n 1 = qv (Real.tan (θ / 2)) n 0 * Real.cos (n * θ) ∧
      qv (Real.tan (θ / 2)) n 2 = qv (Real.tan (θ / 2)) n 0 * Real.sin (n * θ) ∧
      0 < qv (Real.tan (θ / 2)) n 0 := by
  obtain ⟨h1, h2⟩ := half_angle hc
  induction n with
  | zero => simp [qv]
  | succ n ih =>
    obtain ⟨i1, i2, i0⟩ := ih
    rw [Nat.cast_succ, add_mul, one_mul, Real.cos_add, Real.sin_add]
    exact ⟨by simp only [qv, i1, i2]; linear_combination -qv (Real.tan (θ / 2)) n 0 * (Real.cos (n * θ) * h1 - Real.sin (n * θ) * h2),
      by simp only [qv, i1, i2]; linear_combination -qv (Real.tan (θ / 2)) n 0 * (Real.sin (n * θ) * h1 + Real.cos (n * θ) * h2),
      by simp only [qv]; positivity⟩

theorem radianConfig_injective {θ : ℝ} (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    Function.Injective (radianConfig θ) := by
  have hc := (tan_trans_ne ht).1
  have hlt {i j : Fin 9} (hij : i < j) (heq : radianConfig θ i = radianConfig θ j) : False := by
    have hcos : Real.cos ((i : ℕ) * θ) = Real.cos ((j : ℕ) * θ) := by simpa [radianConfig] using congrArg (· 0) heq
    have hsin : Real.sin ((i : ℕ) * θ) = Real.sin ((j : ℕ) * θ) := by simpa [radianConfig] using congrArg (· 1) heq
    let n := j.1 - i.1
    have hsin0 : Real.sin ((n : ℕ) * θ) = 0 := by
      rw [show ((n : ℕ) : ℝ) * θ = (j : ℕ) * θ - (i : ℕ) * θ by simp [n, Nat.cast_sub hij.le]; ring,
        Real.sin_sub, hcos, hsin]; ring
    have hq0 : qv (Real.tan (θ / 2)) n 2 = 0 := by rw [(qv_trig hc n).2.1, hsin0, mul_zero]
    let p : ℚ[X] := qv X n 2
    have hp2 : evalRingHom 2 p ≠ 0 := by
      rw [show p = qv X n 2 from rfl, map_qv, coe_evalRingHom, eval_X,
        show (2 : ℚ) = Int.castRingHom ℚ 2 from rfl, ← map_qv]
      simpa [show n - 1 + 1 = n by omega] using Int.cast_ne_zero (α := ℚ).mpr (qv_two_ne ⟨n - 1, by omega⟩)
    exact ht ⟨p, fun h => hp2 (by simp [h]), by
      change (aeval (Real.tan (θ / 2))).toRingHom (qv X n 2) = 0; simpa [map_qv] using hq0⟩
  intro i j heq
  rcases lt_trichotomy i j with h | rfl | h
  · exact (hlt h heq).elim
  · rfl
  · exact (hlt h heq.symm).elim

theorem radianConfig_affineSpan {θ : ℝ} (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    affineSpan ℝ (Set.range (radianConfig θ)) = ⊤ := by
  obtain ⟨hc, ht0⟩ := tan_trans_ne ht
  obtain ⟨h1, h2⟩ := half_angle hc
  let A := affineSpan ℝ (Set.range (radianConfig θ))
  have hp (k : Fin 9) : radianConfig θ k ∈ A := mem_affineSpan ℝ (Set.mem_range_self k)
  let u := radianConfig θ 1 - radianConfig θ 0
  let v := radianConfig θ 2 - radianConfig θ 0
  have hu : u ∈ A.direction := AffineSubspace.vsub_mem_direction (hp 1) (hp 0)
  have hv : v ∈ A.direction := AffineSubspace.vsub_mem_direction (hp 2) (hp 0)
  let D : ℝ := u 0 * v 1 - v 0 * u 1
  have hD : D ≠ 0 := by
    have hd : D = 2 * Real.sin θ * (1 - Real.cos θ) := by
      simp only [D, u, v, radianConfig, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero,
        Nat.cast_one, Nat.cast_ofNat, zero_mul, one_mul, Real.cos_zero, Real.sin_zero,
        Real.cos_two_mul, Real.sin_two_mul]; ring
    have hs : Real.sin θ ≠ 0 := fun h => ht0 (by linarith [show 2 * Real.tan (θ / 2) = 0 by rw [← h2, h, mul_zero]])
    have hc1 : 1 - Real.cos θ ≠ 0 := fun h => pow_ne_zero 2 ht0
      (by linear_combination (h1 + (1 + Real.tan (θ / 2) ^ 2) * h) / 2)
    rw [hd]; exact mul_ne_zero (mul_ne_zero two_ne_zero hs) hc1
  refine top_unique fun x _ => ?_
  let w := x - radianConfig θ 0
  let α : ℝ := (w 0 * v 1 - v 0 * w 1) / D
  let β : ℝ := (u 0 * w 1 - w 0 * u 1) / D
  have hcomb : α • u + β • v = w := by
    ext j; fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, α, β] <;> rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD] <;>
      dsimp only [D] <;> ring
  simpa [hcomb, w, vadd_eq_add] using AffineSubspace.vadd_mem_of_mem_direction
    (A.direction.add_mem (A.direction.smul_mem α hu) (A.direction.smul_mem β hv)) (hp 0)

theorem radian_not_ramsey (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    ¬ Ramsey (radianConfig θ) := by
  intro hR
  let t := Real.tan (θ / 2)
  have hc := (tan_trans_ne ht).1
  obtain ⟨P, hP, hmult⟩ := ramsey_realCriterion (radianConfig θ) (by decide) (radianConfig_affineSpan ht) hR
  let ev : ℝ[X] →+* ℝ := evalRingHom t
  let Ip := RingHom.ker ev
  have : Ip.IsPrime := RingHom.ker_isPrime ev
  let L := Localization.AtPrime Ip
  have hle : Ip.primeCompl ≤ nonZeroDivisors ℝ[X] := Ip.primeCompl_le_nonZeroDivisors
  have : IsDomain L := IsLocalization.isDomain_localization hle
  have hinjL : Function.Injective (algebraMap ℝ[X] L) := IsLocalization.injective L hle
  let evalL : L →+* ℝ := IsLocalization.lift (M := Ip.primeCompl) (g := ev) fun y => Ne.isUnit y.2
  have haeval_ne {q : ℚ[X]} (hq : q ≠ 0) : aeval t q ≠ 0 := fun h0 => ht ⟨q, hq, h0⟩
  have haeval_inj : Function.Injective ((aeval t).toRingHom : ℚ[X] →+* ℝ) := fun p q hpq =>
    sub_eq_zero.mp <| Classical.byContradiction fun hne => haeval_ne hne (by simpa [map_sub, sub_eq_zero] using hpq)
  let K := FractionRing ℚ[X]
  let σ : K →+* ℝ := IsFractionRing.lift (A := ℚ[X]) (K := K) (L := ℝ) haeval_inj
  let gL : ℚ[X] →+* L := (algebraMap ℝ[X] L).comp (mapRingHom (algebraMap ℚ ℝ))
  have hgL (y : nonZeroDivisors ℚ[X]) : IsUnit (gL y) := IsLocalization.map_units L
    (⟨Polynomial.map (algebraMap ℚ ℝ) y.1,
      show ev _ ≠ 0 by simpa only [ev, coe_evalRingHom, aeval_def, eval₂_eq_eval_map] using haeval_ne (nonZeroDivisors.ne_zero y.2)⟩ : Ip.primeCompl)
  let ρ₀ : K →+* L := IsLocalization.lift (M := nonZeroDivisors ℚ[X]) (g := gL) hgL
  have hev_ρ₀ : evalL.comp ρ₀ = σ := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℚ[X])
    refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
    simp only [RingHom.comp_apply, ρ₀]
    rw [IsLocalization.lift_eq, IsFractionRing.lift_algebraMap]; simp [gL, evalL, ev]
  let F : Subfield ℝ := σ.fieldRange
  let eF : K ≃+* F := RingEquiv.ofBijective (σ.codRestrict F.toSubring fun x => ⟨x, rfl⟩)
    ⟨fun _ _ h => σ.injective (congrArg Subtype.val h), fun ⟨_, x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩
  let ρ : F →ₐ[ℚ] L := (ρ₀.comp eF.symm.toRingHom).toRatAlgHom
  let alR : ℝ →ₐ[ℚ] L := ((algebraMap ℝ[X] L).comp C).toRatAlgHom
  let b := Module.Free.chooseBasis F ℝ
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F (one_ne_zero : (1 : ℝ) ≠ 0)
  let lj (j : _) : ℝ →ₗ[ℚ] L :=
    alR.toLinearMap.comp ((IsScalarTower.toAlgHom ℚ F ℝ).toLinearMap.comp ((φ.restrictScalars ℚ).comp (LinearMap.mulRight ℚ (b j))))
  let B : ℝ →ₗ[ℚ] ℝ →ₗ[ℚ] L :=
    ((Finsupp.lsum ℚ fun j => (((LinearMap.mul ℚ L).comp (lj j)).compl₂ ρ.toLinearMap).flip).comp
      (b.repr.restrictScalars ℚ).toLinearMap).flip
  let Φ : (ℝ ⊗[ℚ] ℝ) →ₗ[ℚ] L := TensorProduct.lift B
  have hB (u v : ℝ) : B u v = (b.repr v).sum fun j cj => alR (φ (u * b j) : ℝ) * ρ cj := by
    simp [B, lj]; rfl
  have hΦ_eval (T : ℝ ⊗[ℚ] ℝ) : evalL (Φ T) = (φ (Algebra.TensorProduct.lmul' ℚ T) : ℝ) := by
    induction T using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul u v =>
      simp only [Φ, TensorProduct.lift.tmul, hB, Algebra.TensorProduct.lmul'_apply_tmul]
      conv_rhs => rw [← b.linearCombination_repr v]
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum, map_sum, AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hev_alR (r : ℝ) : evalL (alR r) = r := by simp [alR, evalL, ev]
      have hev_r (x : F) : evalL (ρ x) = (x : ℝ) := by
        obtain ⟨y, rfl⟩ := eF.surjective x
        change (evalL.comp ρ₀) (eF.symm (eF y)) = (eF y : ℝ); rw [eF.symm_apply_apply, hev_ρ₀]; rfl
      rw [map_mul, hev_alR, hev_r, show u * (b.repr v j • b j) = b.repr v j • (u * b j) by
        change u * ((_ : ℝ) * b j) = (_ : ℝ) * (u * b j); ring, φ.map_smul, smul_eq_mul, Subfield.coe_mul, mul_comm]
  have hΦ_sand (x y : F) (T : ℝ ⊗[ℚ] ℝ) :
      Φ (((x : ℝ) ⊗ₜ[ℚ] 1) * T * (1 ⊗ₜ[ℚ] (y : ℝ))) = alR (x : ℝ) * ρ y * Φ T := by
    induction T using TensorProduct.inductionOn with
    | add z w hz hw => simp [mul_add, add_mul, hz, hw]
    | tmul u v =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Φ, TensorProduct.lift.tmul, hB]
      rw [show v * (y : ℝ) = y • v from mul_comm _ _, b.repr.map_smul, Finsupp.sum_smul_index' (by simp), Finsupp.mul_sum]
      refine Finsupp.sum_congr fun j _ => ?_
      rw [show (x : ℝ) * u * b j = x • (u * b j) from mul_assoc _ _ _, φ.map_smul]
      simp only [smul_eq_mul, map_mul, Subfield.coe_mul]; ring
  let τ : F := eF (algebraMap ℚ[X] K X)
  have hτ : (τ : ℝ) = t := by change σ (algebraMap ℚ[X] K X) = t; simp [σ, IsFractionRing.lift_algebraMap]
  have hρτ : ρ τ = algebraMap ℝ[X] L X := by
    change ρ₀ (eF.symm (eF _)) = _; rw [eF.symm_apply_apply]; simp [ρ₀, IsLocalization.lift_eq, gL]
  have hq (n m : ℕ) : ((qv τ n m : F) : ℝ) = qv t n m := (map_qv F.subtype τ n m).trans (by rw [show F.subtype τ = t from hτ])
  have hq0_ne (n : ℕ) : qv τ n 0 ≠ 0 := fun h => (qv_trig hc n).2.2.ne' (by rw [← hq, h, ZeroMemClass.coe_zero])
  let augF (k : Fin 9) (α : Option (Fin 2)) : F := qv τ k (idx α) / qv τ k 0
  have haug (k : Fin 9) (α : Option (Fin 2)) : realAugmented (radianConfig θ) k α = (augF k α : ℝ) := by
    obtain ⟨h1, h2, h0⟩ := qv_trig hc k
    simp only [augF, Subfield.coe_div]
    cases α with
    | none => rw [idx, hq]; exact (div_self h0.ne').symm
    | some m =>
      fin_cases m <;> simp only [realAugmented, radianConfig, Fin.zero_eta, Fin.mk_one,
        WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        idx, zero_add, Nat.reduceAdd, hq] at h1 h2 h0 ⊢
      · rw [h1, mul_div_cancel_left₀ _ h0.ne']
      · rw [h2, mul_div_cancel_left₀ _ h0.ne']
  let M : Matrix (Fin 9) (Fin 9) L := (algebraMap ℝ[X] L).mapMatrix (Ecl (C t) X)
  let v : Fin 9 → L := fun j => Φ (P (colEquiv j).1 (colEquiv j).2)
  have hMv : M.mulVec v = 0 := by
    ext k
    have hk := congrArg (fun z => alR ((qv τ k 0 : F) : ℝ) * ρ (qv τ k 0) * Φ z) (hP k)
    simp only [arrayEvaluation, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_zero, mul_zero, haug, hΦ_sand] at hk
    rw [← Fintype.sum_prod_type', ← colEquiv.sum_comp, Finset.mul_sum] at hk
    convert hk using 1
    simp only [Matrix.mulVec, dotProduct, M, Matrix.map_apply, RingHom.mapMatrix_apply, Ecl, v]
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨hi1, hi2⟩ := idx_colEquiv j
    have hL1 : alR ((qv τ k 0 : F) : ℝ) * alR (augF k (colEquiv j).1 : ℝ) = algebraMap ℝ[X] L (qv (C t) k (j / 3)) := by
      rw [← map_mul, ← Subfield.coe_mul, mul_div_cancel₀ _ (hq0_ne k), hi1, hq]; simp [alR, ← map_qv C]
    have hL2 : ρ (qv τ k 0) * ρ (augF k (colEquiv j).2) = algebraMap ℝ[X] L (qv X k (j % 3)) := by
      rw [← map_mul, mul_div_cancel₀ _ (hq0_ne k), hi2]
      exact (map_qv ρ.toRingHom τ k _).trans (by rw [show ρ.toRingHom τ = _ from hρτ, ← map_qv])
    rw [show alR ((qv τ k 0 : F) : ℝ) * ρ (qv τ k 0) * (alR (augF k (colEquiv j).1 : ℝ) * ρ (augF k (colEquiv j).2) * v j) =
      (alR ((qv τ k 0 : F) : ℝ) * alR (augF k (colEquiv j).1 : ℝ)) * (ρ (qv τ k 0) * ρ (augF k (colEquiv j).2)) * v j by ring,
      hL1, hL2, ← map_mul]
  have hdet_v : M.det • v = 0 := by
    rw [← Matrix.one_mulVec v, ← Matrix.smul_mulVec, ← Matrix.adjugate_mul, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_zero]
  have hMdet : M.det ≠ 0 := by
    rw [← RingHom.map_det]; exact fun h => det_Ecl_real ht (hinjL (h.trans (map_zero _).symm))
  have hv4 : v 4 = 0 := by simpa [smul_eq_mul, hMdet] using congrFun hdet_v 4
  have hbad := congrArg evalL hv4
  rw [map_zero] at hbad; dsimp only [v] at hbad
  rw [show colEquiv 4 = (some 0, some 0) by decide, hΦ_eval,
    show Algebra.TensorProduct.lmul' ℚ (P (some 0) (some 0)) = 1 from congrFun (congrFun hmult 0) 0,
    hφ, OneMemClass.coe_one] at hbad
  exact zero_ne_one hbad.symm

theorem radian_configuration (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    Function.Injective (radianConfig θ) ∧ (∀ k, dist (radianConfig θ k) 0 = 1) ∧
      ¬ Ramsey (radianConfig θ) :=
  ⟨radianConfig_injective ht, fun k => by rw [EuclideanSpace.dist_eq]; simp [radianConfig, Fin.sum_univ_two, sq_abs],
    radian_not_ramsey θ ht⟩

theorem algebraic_of_tan {θ : ℝ} (h : IsAlgebraic ℚ (Real.tan (θ / 2))) :
    IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ) := by
  let A := algebraicClosure ℚ ℝ
  by_cases hc : Real.cos (θ / 2) = 0
  · rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul, Real.sin_two_mul, hc]
    exact ⟨by rw [← mem_algebraicClosure_iff]; norm_num, by simpa using isAlgebraic_zero⟩
  · have hA : Real.tan (θ / 2) ∈ A := mem_algebraicClosure_iff.mpr h
    obtain ⟨h1, h2⟩ := half_angle hc
    have hne : 1 + Real.tan (θ / 2) ^ 2 ≠ 0 := by positivity
    have hd : 1 + Real.tan (θ / 2) ^ 2 ∈ A := A.add_mem A.one_mem (A.pow_mem hA 2)
    rw [← mem_algebraicClosure_iff, ← mem_algebraicClosure_iff,
      show Real.cos θ = (1 - Real.tan (θ / 2) ^ 2) / (1 + Real.tan (θ / 2) ^ 2) by rw [eq_div_iff hne, mul_comm, h1],
      show Real.sin θ = 2 * Real.tan (θ / 2) / (1 + Real.tan (θ / 2) ^ 2) by rw [eq_div_iff hne, mul_comm, h2]]
    exact ⟨A.div_mem (A.sub_mem A.one_mem (A.pow_mem hA 2)) hd,
      A.div_mem (A.mul_mem (A.natCast_mem 2) hA) hd⟩

theorem radian_ramsey_iff (θ : ℝ) (hinj : Function.Injective (radianConfig θ)) :
    Ramsey (radianConfig θ) ↔ IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ) := by
  refine ⟨fun hR => Classical.byContradiction fun hna =>
    radian_not_ramsey θ (fun htan => hna (algebraic_of_tan htan)) hR, fun ⟨hc, hs⟩ => ?_⟩
  let S : Set ℝ := {Real.cos θ, Real.sin θ}
  let F : IntermediateField ℚ ℝ := IntermediateField.adjoin ℚ S
  have : FiniteDimensional ℚ F := IntermediateField.finiteDimensional_adjoin fun x hx => by
    rcases hx with rfl | rfl; exact hc.isIntegral; exact hs.isIntegral
  have : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  obtain ⟨u, hu, hu1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := ℚ) (S := F)).mp inferInstance
  let ι : F ⊗[ℚ] F →ₐ[ℚ] RealTensor := Algebra.TensorProduct.map F.val F.val
  let T : RealTensor := ι u
  have hT1 : Algebra.TensorProduct.lmul' ℚ T = 1 := by
    have hmul (z : F ⊗[ℚ] F) : Algebra.TensorProduct.lmul' ℚ (ι z) = (Algebra.TensorProduct.lmul' ℚ (S := F) z : ℝ) := by
      induction z using TensorProduct.inductionOn with | tmul => rfl | add _ _ hx hy => simp [hx, hy]
    rw [hmul, hu1, OneMemClass.coe_one]
  have hswap {x : ℝ} (hx : x ∈ F) : T * (1 ⊗ₜ[ℚ] x) = (x ⊗ₜ[ℚ] 1) * T := by
    have h := congrArg ι (hu ⟨x, hx⟩)
    simp only [map_mul, map_sub, map_zero] at h
    change ((1 : ℝ) ⊗ₜ[ℚ] x - x ⊗ₜ[ℚ] (1 : ℝ)) * T = 0 at h
    rw [sub_mul, mul_comm _ T] at h; exact sub_eq_zero.mp h
  have hmem (n : ℕ) : Real.cos (n * θ) ∈ F ∧ Real.sin (n * θ) ∈ F := by
    have hcF : Real.cos θ ∈ F := IntermediateField.subset_adjoin ℚ S (Or.inl rfl)
    have hsF : Real.sin θ ∈ F := IntermediateField.subset_adjoin ℚ S (Or.inr rfl)
    induction n with
    | zero => simp [F.one_mem, F.zero_mem]
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, Real.cos_add, Real.sin_add]
      exact ⟨F.sub_mem (F.mul_mem ih.1 hcF) (F.mul_mem ih.2 hsF),
        F.add_mem (F.mul_mem ih.2 hcF) (F.mul_mem ih.1 hsF)⟩
  refine realCriterion_ramsey (radianConfig θ) (by decide) (by decide) hinj ⟨fun α β =>
    match α, β with
    | none, none => -T
    | some j, some j' => if j = j' then T else 0
    | _, _ => 0, fun k => ?_, ?_⟩
  · simp only [arrayEvaluation, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_option,
      realAugmented, radianConfig, Fin.sum_univ_two, WithLp.ofLp_toLp, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, zero_mul, add_zero, zero_add,
      ite_true, show ((0 : Fin 2) = 1) = False by decide,
      show ((1 : Fin 2) = 0) = False by decide, ite_false, ← Algebra.TensorProduct.one_def, one_mul, mul_one]
    rw [mul_assoc _ T, hswap (hmem k).1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      mul_assoc _ T, hswap (hmem k).2, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      ← add_mul, ← TensorProduct.add_tmul,
      show Real.cos ((k : ℕ) * θ) * Real.cos ((k : ℕ) * θ) + Real.sin ((k : ℕ) * θ) * Real.sin ((k : ℕ) * θ) = 1 by
        simpa [sq] using Real.cos_sq_add_sin_sq ((k : ℕ) * θ),
      ← Algebra.TensorProduct.one_def, one_mul, neg_add_cancel]
  · ext α β
    change Algebra.TensorProduct.lmul' ℚ (if α = β then T else 0) = (1 : Matrix (Fin 2) (Fin 2) ℝ) α β
    rw [Matrix.one_apply]; split_ifs <;> simp [hT1]

theorem radian_ramsey_iff_tan (θ : ℝ) (hinj : Function.Injective (radianConfig θ)) :
    Ramsey (radianConfig θ) ↔ IsAlgebraic ℚ (Real.tan (θ / 2)) :=
  ⟨fun hR => Classical.byContradiction fun hna => radian_not_ramsey θ hna hR,
    fun h => (radian_ramsey_iff θ hinj).2 (algebraic_of_tan h)⟩

end
end EuclideanRamsey.Radian
end OAI

namespace RadianRamsey
open OAI.EuclideanRamsey.Radian

theorem oai_ramsey_iff {s d : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin d)) :
    OAI.EuclideanRamsey.Ramsey a ↔
      ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
        ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin s → EuclideanSpace ℝ (Fin D),
          Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k := by
  have hcong {D : ℕ} (b : Fin s → EuclideanSpace ℝ (Fin D)) :
      OAI.EuclideanRamsey.Congruent a b ↔ Congruent a b := by
    rw [congruent_iff_dist_eq]; exact forall₂_congr fun _ _ => eq_comm
  simp only [OAI.EuclideanRamsey.Ramsey, hcong]

theorem radian_configuration_mathlib (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    let a : Fin 9 → EuclideanSpace ℝ (Fin 2) := fun k =>
      WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]
    Function.Injective a ∧ (∀ k, a k ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
      ¬ (∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
        ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin 9 → EuclideanSpace ℝ (Fin D),
          Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k) := by
  intro a
  obtain ⟨h1, h2, h3⟩ := radian_configuration θ ht
  exact ⟨h1, fun k => Metric.mem_sphere.mpr (h2 k), fun h => h3 ((oai_ramsey_iff a).2 h)⟩

theorem radian_ramsey_iff_mathlib (θ : ℝ) :
    let a : Fin 9 → EuclideanSpace ℝ (Fin 2) := fun k =>
      WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]
    Function.Injective a →
      ((∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
          ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin 9 → EuclideanSpace ℝ (Fin D),
            Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k) ↔
        IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ)) :=
  fun hinj => (oai_ramsey_iff _).symm.trans (radian_ramsey_iff θ hinj)

theorem radian_ramsey_iff_tan_mathlib (θ : ℝ) :
    let a : Fin 9 → EuclideanSpace ℝ (Fin 2) := fun k =>
      WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]
    Function.Injective a →
      ((∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
          ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin 9 → EuclideanSpace ℝ (Fin D),
            Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k) ↔
        IsAlgebraic ℚ (Real.tan (θ / 2))) :=
  fun hinj => (oai_ramsey_iff _).symm.trans (radian_ramsey_iff_tan θ hinj)

end RadianRamsey
