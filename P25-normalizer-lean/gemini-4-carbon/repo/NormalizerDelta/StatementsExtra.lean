module

public import NormalizerLean.Defs

@[expose] public section

open Matrix MatrixGroups CongruenceSubgroup
open Matrix.SpecialLinearGroup (coe_mul coe_inv coe_one coe_neg det_coe map_intCast_injective)

namespace NormalizerLean

noncomputable section

abbrev MatR := Matrix (Fin 2) (Fin 2) ℝ

section Helpers

variable {N : ℕ} {Δ : Subgroup (ZMod N)ˣ}

theorem coe_inv_smul {g : SL(2, ℝ)} {s a b c d : ℝ} (h : (g : MatR) = s • !![a, b; c, d]) :
    ((g⁻¹ : SL(2, ℝ)) : MatR) = s • !![d, -b; -c, a] := by
  rw [coe_inv, h, adjugate_smul, adjugate_fin_two_of]; simp

theorem coe_ofZ (γ : SL(2, ℤ)) : (ofZ γ : MatR) = !![(γ 0 0 : ℝ), γ 0 1; γ 1 0, γ 1 1] :=
  eta_fin_two _

def mkSL (a b c d : ℤ) (h : a * d - b * c = 1) : SL(2, ℤ) :=
  ⟨!![a, b; c, d], by rw [det_fin_two_of]; exact h⟩

theorem exists_bezout_unit (u : (ZMod N)ˣ) :
    ∃ x y : ℤ, x * (u : ZMod N).val - y * N = 1 :=
  let ⟨x, y, h⟩ := Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime u)
  ⟨x, -y, by linear_combination h⟩

theorem GammaDelta_subgroupOf (Δ : Subgroup (ZMod N)ˣ) :
    (GammaDelta N Δ).subgroupOf (Gamma0 N) = Δ.comap (Gamma0Map N).toHomUnits := by
  ext γ
  exact ⟨fun ⟨_, u, hu, hud⟩ => ((Units.ext hud : u = (Gamma0Map N).toHomUnits γ) ▸ hu : _ ∈ Δ),
    fun h => ⟨γ.2, (Gamma0Map N).toHomUnits γ, h, rfl⟩⟩

theorem Gamma0R_le_normG_GammaDeltaR : Gamma0R N ≤ NormG (GammaDeltaR N Δ) := by
  have : ((GammaDelta N Δ).subgroupOf (Gamma0 N)).Normal :=
    GammaDelta_subgroupOf (N := N) Δ ▸ inferInstance
  exact (Subgroup.map_mono (Subgroup.le_normalizer_of_normal_subgroupOf
    fun _ (h : _ ∈ GammaDelta N Δ) => h.1)).trans (Subgroup.le_normalizer_map _)

def conjM (g : SL(2, ℝ)) (M : MatR) : MatR := (g : MatR) * M * (g : MatR).adjugate

def vv (B p : ℕ) (x : ℤ) : ℕ := if x = 0 then B else x.natAbs.factorization p

theorem dvd_of_forall_vv {m : ℕ} {x : ℤ} (hm : m ≠ 0)
    (h : ∀ p : ℕ, p.Prime → ∃ B, m.factorization p ≤ vv B p x) : (m : ℤ) ∣ x := by
  by_cases hx : x = 0; · simp [hx]
  exact Int.ofNat_dvd_left.2 ((Nat.factorization_prime_le_iff_dvd hm (by positivity)).1
    fun p hp => by obtain ⟨_, hB⟩ := h p hp; simpa [vv, hx] using hB)

theorem dvd_val_sq {p m : ℕ} (hp : p.Prime) (hd : p ∣ N) (u : (ZMod N)ˣ) :
    m ∣ (u : ZMod N).val ^ 2 - 1 ↔ ((u : ZMod N).val : ZMod m) ^ 2 = 1 := by
  have h1 : 1 ≤ (u : ZMod N).val ^ 2 := Nat.pos_of_ne_zero fun h => by
    have := ZMod.val_coe_unit_coprime u; simp_all [hp.ne_one]
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, sub_eq_zero]; push_cast; rfl

def L0 (N : ℕ) (g : SL(2, ℝ)) : AddSubgroup MatR where
  carrier := {A | (∀ i j, (conjM g A) i j ∈ (Int.castRingHom ℝ).range) ∧
    (conjM g A) 1 0 / N ∈ (Int.castRingHom ℝ).range}
  zero_mem' := by simp [conjM]
  add_mem' ha hb := by simp_all [-RingHom.mem_range, conjM, mul_add, add_mul, add_div, add_mem]
  neg_mem' ha := by simp_all [-RingHom.mem_range, conjM, neg_div]

variable [NeZero N]

theorem conjM_basis {g : SL(2, ℝ)} (hg : g ∈ NormG (GammaDeltaR N Δ)) :
    !![0, 1; 0, 0] ∈ L0 N g ∧ !![0, 0; (N : ℝ), 0] ∈ L0 N g ∧ !![0, 0; 0, (N : ℝ)] ∈ L0 N g ∧
      ∀ (x y t : ℤ) {u : (ZMod N)ˣ}, x * t - y * N = 1 → u ∈ Δ → (u : ZMod N) = t →
        !![0, 0; 0, ↑(t - x)] ∈ L0 N g := by
  have hm (γ) (hγ : γ ∈ GammaDelta N Δ) : (ofZ γ : MatR) ∈ L0 N g := by
    obtain ⟨A, ⟨hA, _⟩, hAY⟩ := (Subgroup.mem_normalizer_iff.1 hg _).1 ⟨γ, hγ, rfl⟩
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (Gamma0_mem.1 hA)
    have hc : conjM g (ofZ γ) = ofZ A := by rw [conjM, ← coe_inv, ← coe_mul, ← coe_mul, ← hAY]
    exact ⟨fun i j => hc ▸ ⟨A i j, rfl⟩,
      ⟨k, by have : (N : ℝ) ≠ 0 := mod_cast NeZero.ne N; rw [hc]; simp [hk, this]⟩⟩
  have h1 : (1 : MatR) ∈ L0 N g := by simpa using hm 1 (one_mem _)
  let mkN (x y t : ℤ) h {u} (hu : u ∈ Δ) (hud : (u : ZMod N) = t) :=
    hm (mkSL x y N t h) ⟨Gamma0_mem.2 (by simp [mkSL]), u, hu, by simpa [mkSL] using hud⟩
  have hE12 : !![0, 1; 0, 0] ∈ L0 N g := by
    convert sub_mem (hm ModularGroup.T ⟨Gamma0_mem.2 Int.cast_zero, 1, one_mem _, by simp⟩) h1 using 1
    rw [coe_ofZ, one_fin_two]; simp [ModularGroup.T]
  have hE21 : !![0, 0; (N : ℝ), 0] ∈ L0 N g := by
    convert sub_mem (mkN 1 0 1 (by ring) (one_mem _) (by simp)) h1 using 1
    rw [coe_ofZ, one_fin_two]; simp [mkSL]
  refine ⟨hE12, hE21, And.imp_left (fun h4 => by simpa using h4 1 1 (N + 1) (by ring) (one_mem _) (by simp))
    (and_self_iff.2 fun x y t {u} hdet hu hut => ?_)⟩
  convert sub_mem (sub_mem (sub_mem (mkN x y t hdet hu hut) (zsmul_mem h1 x))
    (zsmul_mem hE12 y)) hE21 using 1
  rw [coe_ofZ, one_fin_two]; simp [mkSL, zsmul_eq_mul]

theorem dvd_epsDelta_iff {m : ℕ} :
    m ∣ epsDelta N Δ ↔ m ∣ N ∧ ∀ u ∈ Δ, m ∣ (u : ZMod N).val ^ 2 - 1 := by
  classical
  unfold epsDelta; rw [Nat.dvd_gcd_iff, Finset.dvd_gcd_iff]; simp

theorem epsDelta_pos : 0 < epsDelta N Δ :=
  Nat.pos_of_dvd_of_pos (dvd_epsDelta_iff.1 dvd_rfl).1 (Nat.pos_of_ne_zero (NeZero.ne N))

theorem factorization_hDelta (p : ℕ) :
    (hDelta N Δ).factorization p =
      min ((epsDelta N Δ).factorization p) (N.factorization p / 2) := by
  unfold hDelta
  rw [Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero),
    Finset.sum_congr rfl (fun q hq => by
      rw [(Nat.prime_of_mem_primeFactors hq).factorization_pow, Finsupp.single_apply]),
    Finset.sum_ite_eq']
  split_ifs with hp
  · rfl
  · simp [Finsupp.notMem_support_iff.1 (Nat.support_factorization N ▸ hp)]

theorem hDelta_pos : 0 < hDelta N Δ :=
  Finset.prod_pos fun _ hq => pow_pos (Nat.pos_of_mem_primeFactors hq) _

theorem nDelta_mul : nDelta N Δ * hDelta N Δ ^ 2 = N := by
  refine Nat.div_mul_cancel ?_
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hDelta_pos.ne') (NeZero.ne N)]
  intro p; simp [factorization_hDelta]; omega

instance nDelta_neZero : NeZero (nDelta N Δ) :=
  ⟨fun h => NeZero.ne N (by rw [← nDelta_mul (Δ := Δ), h, zero_mul])⟩

theorem cast_N {R : Type*} [Semiring R] : (N : R) = nDelta N Δ * (hDelta N Δ : R) ^ 2 := by
  rw [← Nat.cast_pow, ← Nat.cast_mul, nDelta_mul]

def alSub (n : ℕ) [NeZero n] : Subgroup SL(2, ℝ) where
  carrier := {g | ∃ Q : ℕ, Q ∣ n ∧ IsAtkinLehner n Q g}
  one_mem' := ⟨1, one_dvd n, 1, 0, 0, 1, by simp, by simp [one_fin_two]⟩
  inv_mem' := by
    rintro g ⟨Q, hQ, x, y, z, w, hdet, hgm⟩
    exact ⟨Q, hQ, w, -y, -z, x, by linear_combination hdet, by rw [coe_inv_smul hgm]; simp⟩
  mul_mem' := by
    rintro g₁ g₂ ⟨Q₁, hQ₁, x₁, y₁, z₁, w₁, hd₁, hg₁⟩ ⟨Q₂, hQ₂, x₂, y₂, z₂, w₂, hd₂, hg₂⟩
    set G := Q₁.gcd Q₂ with hG
    have hG0 : 0 < G := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos hQ₁ (Nat.pos_of_ne_zero (NeZero.ne n)))
    obtain ⟨q₁, hq₁⟩ := Q₁.gcd_dvd_left Q₂
    obtain ⟨q₂, hq₂⟩ := Q₁.gcd_dvd_right Q₂
    rw [← hG] at hq₁ hq₂
    obtain ⟨L, hn⟩ : G * (q₁ * q₂) ∣ n := by
      convert Nat.lcm_dvd hQ₁ hQ₂ using 1
      exact Nat.eq_of_mul_eq_mul_left hG0 (by (conv_rhs => rw [Nat.gcd_mul_lcm, hq₁, hq₂]); ring)
    have h12 := congrArg₂ (· * ·) hd₁ hd₂
    rw [hq₁, hq₂, hn] at h12; push_cast at h12
    refine ⟨q₁ * q₂, ⟨G * L, by rw [hn]; ring⟩,
      G * x₁ * x₂ + L * y₁ * z₂, q₁ * x₁ * y₂ + q₂ * y₁ * w₂,
      q₂ * z₁ * x₂ + q₁ * w₁ * z₂, L * z₁ * y₂ + G * w₁ * w₂,
      mul_left_cancel₀ (by positivity : (G : ℤ) ^ 2 ≠ 0)
        (by rw [hn]; push_cast; linear_combination h12), ?_⟩
    have hsq : Real.sqrt Q₁ * Real.sqrt Q₂ = G * Real.sqrt ((q₁ * q₂ : ℕ) : ℝ) := by
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_sq (Nat.cast_nonneg G), ← Real.sqrt_mul (by positivity), hq₁, hq₂]
      exact congrArg _ (by push_cast; ring)
    rw [coe_mul, hg₁, hg₂, smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_inv, hsq, mul_inv,
      mul_comm (G : ℝ)⁻¹, mul_smul]
    congr 1; rw [inv_smul_eq_iff₀ (by positivity), hn, hq₁, hq₂, mul_fin_two]
    simp; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

theorem mem_MDelta_iff {g : SL(2, ℝ)} :
    g ∈ MDelta N Δ ↔ IsNewmanFormH N (hDelta N Δ) g := by
  set h := hDelta N Δ
  have hhr_pos : (0 : ℝ) < h := Nat.cast_pos.2 hDelta_pos
  have hhr : (h : ℝ) ≠ 0 := hhr_pos.ne'
  have hnz (z : ℝ) : (nDelta N Δ : ℝ) * (hDelta N Δ : ℝ) ^ 2 * z / h = nDelta N Δ * z * h := by
    dsimp [h]; rw [div_eq_iff hhr]; ring
  let T : MatR → MatR := fun M => !![M 0 0, M 0 1 / h; M 1 0 * h, M 1 1]
  let D : SL(2, ℝ) := projSL !![(h : ℝ), 0; 0, 1]
  have hD : (D : MatR) = (Real.sqrt h)⁻¹ • !![(h : ℝ), 0; 0, 1] := by simp [D, projSL, hhr_pos]
  let w := MulAut.conj D g
  have hgT : (g : MatR) = T w := by
    have hwg : D⁻¹ * w * D = g := by simp [w, MulAut.conj_apply]; group
    rw [← hwg, coe_mul, coe_mul, coe_inv_smul hD, hD]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [← sq, inv_pow, Real.sq_sqrt hhr_pos.le, eta_fin_two (w : MatR), mul_fin_two, mul_fin_two]
    simp [T, hhr, div_eq_inv_mul, mul_comm, mul_left_comm]
  rw [MDelta, show Gamma0Plus (nDelta N Δ) = alSub (nDelta N Δ) from Subgroup.closure_eq (alSub (nDelta N Δ)),
    Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply, inv_inv]
  change w ∈ alSub (nDelta N Δ) ↔ _
  constructor
  · rintro ⟨Q, hQ, x, y, z, w', hdet, hwm⟩
    refine ⟨x, y, z, w', Q, Nat.pos_of_dvd_of_pos hQ (Nat.pos_of_ne_zero (NeZero.ne _)), hQ,
      by change _ - _ * (nDelta N Δ : ℤ) = _; linear_combination hdet, 1, Or.inl rfl, ?_⟩
    rw [hgT, hwm, cast_N (Δ := Δ), hnz]
    simp [T, div_eq_inv_mul, mul_comm, mul_assoc, mul_left_comm]
  · rintro ⟨a, b, c, d, e, he0, he, hdet, ε, hε, hgm⟩
    have hn : N / h ^ 2 = nDelta N Δ := rfl; rw [hn] at he hdet
    obtain ⟨s, rfl, hs⟩ : ∃ s : ℤ, (s : ℝ) = ε ∧ s ^ 2 = 1 :=
      hε.elim (fun h => ⟨1, by simp [h]⟩) (fun h => ⟨-1, by simp [h]⟩)
    refine ⟨e, he, s * a, s * b, s * c, s * d,
      by linear_combination s ^ 2 * hdet + (e : ℤ) * hs, ?_⟩
    have hTi {A B} (h : T A = T B) : A = B := by rw [eta_fin_two A, eta_fin_two B]; simpa [T, hhr] using h
    refine hTi ?_
    rw [← hgT, hgm, cast_N (Δ := Δ), hnz]; push_cast
    simp [T, div_eq_inv_mul, mul_comm, mul_assoc, mul_left_comm]

theorem exists_gamma_delta {p : ℕ} (hp : p.Prime) :
    ∃ s : ℤ, s ≠ 0 ∧ s.natAbs.factorization p ≤ (epsDelta N Δ).factorization p ∧
      ∀ g ∈ NormG (GammaDeltaR N Δ), !![0, 0; 0, (s : ℝ)] ∈ L0 N g := by
  have hN := NeZero.ne N
  set j := (epsDelta N Δ).factorization p
  by_cases hj : j < N.factorization p
  · have hpj1 : p ^ (j + 1) ∣ N := (hp.pow_dvd_iff_le_factorization hN).2 hj
    obtain ⟨u, hu, hnd⟩ : ∃ u ∈ Δ, ¬ p ^ (j + 1) ∣ (u : ZMod N).val ^ 2 - 1 := by
      by_contra! hc
      have := (hp.pow_dvd_iff_le_factorization epsDelta_pos.ne').1 (dvd_epsDelta_iff.2 ⟨hpj1, hc⟩)
      omega
    obtain ⟨x, y, hdxy⟩ := exists_bezout_unit u
    set v := (u : ZMod N).val
    have hnd1 : ¬ (↑(p ^ (j + 1)) : ℤ) ∣ (v : ℤ) - x := fun ⟨q, hq⟩ => by
      obtain ⟨k, hk⟩ := hpj1
      have hv1 : 1 ≤ v ^ 2 := Nat.pos_of_ne_zero fun h => hnd (by simp [h])
      exact hnd (Int.natCast_dvd_natCast.1 ⟨v * q + y * k, by
        rw [Nat.cast_sub hv1]; rw [hk] at hdxy; push_cast at hq hdxy ⊢; linear_combination v * hq + hdxy⟩)
    have hs0 : (v : ℤ) - x ≠ 0 := fun h0 => hnd1 (by simp [h0])
    exact ⟨(v : ℤ) - x, hs0, not_lt.1 fun hc => hnd1 (Int.ofNat_dvd_left.2
      ((hp.pow_dvd_iff_le_factorization (by positivity)).2 hc)),
      fun g hg => (conjM_basis hg).2.2.2 x y v hdxy hu (by simp [v])⟩
  · exact ⟨N, mod_cast hN, by simp; omega, fun g hg => (conjM_basis hg).2.2.1⟩

end Helpers

/-! ## §M. The group M_Δ and the σH coset description -/

/-- The matrices of the generalized Newman bound form the group M_Δ = D⁻¹ Γ₀(n_Δ)⁺ D. -/
theorem coe_MDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    (MDelta N Δ : Set SL(2, ℝ)) = {g | IsNewmanFormH N (hDelta N Δ) g} :=
  Set.ext fun _ => mem_MDelta_iff

/-- The generalized Newman bound, restated: Nor(Γ_Δ(N)) ≤ M_Δ. -/
theorem normG_GammaDeltaR_le_MDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    NormG (GammaDeltaR N Δ) ≤ MDelta N Δ := by
  intro g hg
  refine mem_MDelta_iff.2 ?_
  set h := hDelta N Δ
  let Smat (α β γ δ : ℤ) : MatR := !![(α : ℝ), (β : ℝ) / h; (h : ℝ) * γ, (δ : ℝ)]
  have hh0 : 0 < h := hDelta_pos
  have hN0 := Nat.pos_of_ne_zero (NeZero.ne N)
  have hn0 : nDelta N Δ ≠ 0 := NeZero.ne _
  let M := (g : MatR)
  have hdetM := det_fin_two M ▸ det_coe g
  obtain ⟨hE12, -, hE22, -⟩ := conjM_basis hg
  let j : Fin 2 := if M 0 0 = 0 then 0 else 1
  let t := if M 0 0 = 0 then -M 1 0 else M 0 0
  have ht : t ≠ 0 := by dsimp [t]; split_ifs <;> intro <;> simp_all
  have hcol : ∀ i (u v : ℝ), (conjM g !![0, u; 0, v]) i j = t * (u * M i 0 + v * M i 1) :=
    fun i u v => by
      dsimp [j, t, conjM, M]; fin_cases i <;> split_ifs <;>
        simp [adjugate_fin_two, mul_apply, Fin.sum_univ_two] <;> ring
  obtain ⟨a0, ha0⟩ := hE12.1 0 j; obtain ⟨a1, ha1⟩ := hE22.1 0 j
  obtain ⟨a2, ha2⟩ := hE12.1 1 j; obtain ⟨a3, ha3⟩ := hE22.1 1 j
  simp [hcol] at ha0 ha1 ha2 ha3
  set G := Int.gcd ((h * N * a0 : ℤ).gcd (h ^ 2 * a1)) ((N * a2 : ℤ).gcd (h * a3)) with hG
  have hG0 : 0 < G := Nat.pos_of_ne_zero fun h0 => by simp_all [G, hh0.ne', hN0.ne']
  obtain ⟨α, hα⟩ := (hG ▸ Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
  obtain ⟨β, hβ⟩ := (hG ▸ Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
  obtain ⟨γ, hγ⟩ := (hG ▸ Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_left _ _)
  obtain ⟨δ, hδ⟩ := (hG ▸ Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _)
  have hprim : Int.gcd (Int.gcd α β) (Int.gcd γ δ) = 1 := Nat.eq_of_mul_eq_mul_left hG0 (by
    conv_rhs => rw [mul_one, hG, hα, hβ, hγ, hδ]
    simp [Int.gcd, Int.natAbs_mul, Nat.gcd_mul_left])
  let κ : ℝ := G / (h * N * t)
  have hgm : (g : MatR) = κ • Smat α β γ δ := by
    rw [← Int.cast_inj (α := ℝ)] at hα hβ hγ hδ
    push_cast [ha0, ha1, ha2, ha3] at hα hβ hγ hδ
    change M = _; ext i j; fin_cases i <;> fin_cases j <;> simp [κ, Smat] <;> field_simp
    exacts [by linear_combination hα, by linear_combination hβ,
      by linear_combination hγ, by linear_combination hδ]
  have hdet : κ ^ 2 * ((α * δ - β * γ : ℤ) : ℝ) = 1 := by
    have := det_coe g
    simp [hgm, Smat] at this; field_simp at this; push_cast; linear_combination this
  obtain ⟨e, hEe⟩ := Int.eq_ofNat_of_zero_le (a := α * δ - β * γ)
    (by exact_mod_cast (show (0 : ℝ) ≤ (α * δ - β * γ : ℤ) by nlinarith [sq_nonneg κ]))
  rw [hEe, Int.cast_natCast] at hdet
  have he0 : 0 < e := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hdet
  have hginv : ((g⁻¹ : SL(2, ℝ)) : MatR) = κ • Smat δ (-β) (-γ) α := by
    rw [coe_inv_smul hgm]; simp [Smat, neg_div]
  have hloc : ∀ p : ℕ, p.Prime →
      let B := e.factorization p + N.factorization p + 1
      e.factorization p ≤ (nDelta N Δ).factorization p ∧
        (nDelta N Δ).factorization p ≤ vv B p γ ∧
        e.factorization p ≤ vv B p α ∧ e.factorization p ≤ vv B p δ := by
    intro p hp B; dsimp [h] at hh0
    have := Nat.pos_of_ne_zero hn0
    have hnk : (nDelta N Δ).factorization p + 2 * (hDelta N Δ).factorization p = N.factorization p := by
      conv_rhs => rw [← nDelta_mul (Δ := Δ), Nat.factorization_mul hn0 (pow_ne_zero 2 hh0.ne')]
      simp
    obtain ⟨s, hs0, hvs, hsL⟩ := exists_gamma_delta (N := N) (Δ := Δ) hp
    have prim : vv B p α = 0 ∨ vv B p β = 0 ∨ vv B p γ = 0 ∨ vv B p δ = 0 := by
      by_contra! hcon
      have key {x} (hx : vv B p x ≠ 0) : p ∣ x.natAbs := by
        by_cases hx0 : x = 0; · simp [hx0]
        exact Nat.dvd_of_factorization_pos (by simpa [vv, hx0] using hx)
      exact hp.not_dvd_one (hprim ▸ Nat.dvd_gcd (Nat.dvd_gcd (key hcon.1) (key hcon.2.1))
        (Nat.dvd_gcd (key hcon.2.2.1) (key hcon.2.2.2)))
    have u2 : min (vv B p α + vv B p δ) (vv B p β + vv B p γ) ≤ e.factorization p := by
      have pmul {x y} (hm : e.factorization p + 1 ≤ vv B p x + vv B p y) :
          (p : ℤ) ^ (e.factorization p + 1) ∣ x * y := by
        rcases eq_or_ne x 0 with rfl | hx; · simp
        rcases eq_or_ne y 0 with rfl | hy; · simp
        simp only [vv, hx, hy, ↓reduceIte] at hm
        rwa [← Int.natCast_pow, Int.ofNat_dvd_left, Int.natAbs_mul,
          hp.pow_dvd_iff_le_factorization (by positivity), Nat.factorization_mul (by positivity) (by positivity)]
      by_contra! hc
      have := (hp.pow_dvd_iff_le_factorization he0.ne').1 <| Int.natCast_dvd_natCast.1 <| by
        rw [Int.natCast_pow, ← hEe]; exact dvd_sub (pmul (by omega)) (pmul (by omega))
      omega
    have df {g'} (hg' : g' ∈ NormG (GammaDeltaR N Δ)) {α' β' γ' δ'}
        (hgm' : (g' : MatR) = κ • Smat α' β' γ' δ') :=
      let S := Smat α' β' γ' δ'
      have hSM (M') : conjM g' M' = (e : ℝ)⁻¹ • (S * M' * S.adjugate) := by
        rw [eq_inv_smul_iff₀ (by positivity), conjM, hgm', adjugate_smul, Fintype.card_fin]
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
        rw [show (e : ℝ) * (κ ^ (2 - 1) * κ) = κ ^ 2 * e by ring, hdet, one_smul]
      have dv (M' : ℕ) (k x y : ℤ) {r : ℝ} (hr : r ∈ (Int.castRingHom ℝ).range)
          (heq : ((k * (x * y) : ℤ) : ℝ) = (e * M' : ℕ) * r := by
            simp [hSM, S, Smat, h, adjugate_fin_two_of, cast_N (Δ := Δ)]; field_simp)
          (hM : M' ≠ 0 := by positivity)
          (hk : k ≠ 0 := by first | positivity | assumption)
          (hB : e.factorization p + M'.factorization p ≤ B := by
            simp [B, Nat.factorization_mul hn0 hh0.ne']; omega) :
          e.factorization p + M'.factorization p ≤ k.natAbs.factorization p + vv B p x + vv B p y := by
        obtain ⟨z, hz⟩ := hr
        have hd : ((e * M' : ℕ) : ℤ) ∣ k * (x * y) :=
          ⟨z, by exact_mod_cast heq.trans (congrArg _ (show r = z from hz.symm))⟩
        rcases eq_or_ne x 0 with rfl | hx; · simp [vv]; omega
        rcases eq_or_ne y 0 with rfl | hy; · simp [vv]; omega
        rw [← Int.natAbs_ne_zero] at hk hx hy
        have h1 := (Nat.factorization_le_iff_dvd (mul_ne_zero he0.ne' hM) (mul_ne_zero hk (mul_ne_zero hx hy))).2
          (by simpa [Int.natAbs_mul] using Int.ofNat_dvd_left.1 hd) p
        simp [Nat.factorization_mul he0.ne' hM, Nat.factorization_mul hk (mul_ne_zero hx hy),
          Nat.factorization_mul hx hy, vv, Int.natAbs_ne_zero.1 hx, Int.natAbs_ne_zero.1 hy] at h1 ⊢
        omega
      let ⟨hE12, hE21, _⟩ := conjM_basis hg'
      let hs := hsL g' hg'
      And.intro (dv 1 1 α' α' (hE12.1 0 1)) <| And.intro (dv (nDelta N Δ) 1 γ' γ' (neg_mem hE12.2)) <|
        And.intro (dv 1 (nDelta N Δ) β' β' (neg_mem (hE21.1 0 1))) <|
        And.intro (dv (hDelta N Δ) s α' β' (hs.1 0 1)) (dv (nDelta N Δ * hDelta N Δ) s γ' δ' (neg_mem hs.2))
    obtain ⟨c2, c3, c6, s10, s11⟩ := df hg hgm
    obtain ⟨c7, -, -, t10, t11⟩ := df (inv_mem hg) hginv
    simp [Nat.factorization_mul hn0 hh0.ne',
      show ∀ x, vv B p (-x) = vv B p x by simp [vv]] at c2 c3 c6 c7 s10 s11 t10 t11
    have := factorization_hDelta (N := N) (Δ := Δ) p
    omega
  have hen : e ∣ nDelta N Δ :=
    (Nat.factorization_prime_le_iff_dvd he0.ne' hn0).1 fun p hp => (hloc p hp).1
  obtain ⟨c', hc'⟩ := dvd_of_forall_vv hn0 fun p hp => ⟨_, (hloc p hp).2.1⟩
  obtain ⟨a', ha'⟩ := dvd_of_forall_vv he0.ne' fun p hp => ⟨_, (hloc p hp).2.2.1⟩
  obtain ⟨d', hd'⟩ := dvd_of_forall_vv he0.ne' fun p hp => ⟨_, (hloc p hp).2.2.2⟩
  refine ⟨a', β, c', d', e, he0, hen, ?_, κ * Real.sqrt e, ?_, ?_⟩
  · rw [ha', hd', hc'] at hEe
    change _ - _ * (nDelta N Δ : ℤ) = _; linear_combination hEe
  · exact sq_eq_one_iff.1 (by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), hdet])
  · rw [hgm, mul_div_assoc, div_self (by positivity), mul_one]
    congr 1; simp [Smat, ha', hc', hd', cast_N (Δ := Δ), mul_comm]; rw [eq_div_iff (by positivity)]; ring

/-- Γ₀(N) ≤ M_Δ. -/
theorem Gamma0R_le_MDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : Gamma0R N ≤ MDelta N Δ :=
  Gamma0R_le_normG_GammaDeltaR.trans (normG_GammaDeltaR_le_MDelta N Δ)

/-- Every right coset Γ₀(N)g in M_Δ contains a real multiple of a matrix σH. -/
theorem exists_sigmaH {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ) {R : Set SL(2, ℤ)}
    (hR : IsGamma0Reps N R) {g : SL(2, ℝ)} (hg : g ∈ MDelta N Δ) :
    ∃ γ ∈ Gamma0R N, ∃ r ∈ R, ∃ a b d : ℕ, IsHermiteN N a b d ∧ ∃ c : ℝ, c ≠ 0 ∧
      ((γ * g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
        c • ((ofZ r : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a b d) := by
  obtain ⟨a, b, c, d, e, he0, he, hdet, ε, hε, hgm⟩ := mem_MDelta_iff.1 hg
  set h := hDelta N Δ
  have hh : 0 < h := hDelta_pos
  have hn : N / h ^ 2 = nDelta N Δ := rfl
  rw [hn] at he hdet
  let w00 : ℤ := a * e * h; let w10 : ℤ := N * c; let w11 : ℤ := d * e * h
  have hWdet : w00 * w11 - b * w10 = (h : ℤ) ^ 2 * e := by
    dsimp [w00, w10, w11]; rw [cast_N (Δ := Δ)]; linear_combination (h : ℤ) ^ 2 * hdet
  set G := w00.gcd w10 with hGdef
  have hG0 : 0 < G := Nat.pos_of_ne_zero fun hc => by simp_all [G, hh.ne', he0.ne']
  obtain ⟨p, q, hpq, hp, hq⟩ := Int.exists_gcd_one hG0
  rw [← hGdef] at hp hq
  let A0 := p.gcdA q; let B0 := p.gcdB q
  have hbez : p * A0 + q * B0 = 1 := by simpa [hpq] using (Int.gcd_eq_gcd_ab p q).symm
  let δ := p * w11 - q * b
  have hGδ : (G : ℤ) * δ = (h : ℤ) ^ 2 * e := by rw [← hWdet, hp, hq]; dsimp [δ]; ring
  have hδ : 0 < δ := pos_of_mul_pos_right (by rw [hGδ]; positivity) (Nat.cast_nonneg G)
  let β := A0 * b + B0 * w11; set k := β / δ with hk
  let σ := mkSL p (p * k - B0) q (q * k + A0) (by linear_combination hbez)
  set r0 := (β % δ).natAbs; set d0 := δ.natAbs
  have hd0 : 0 < d0 := Int.natAbs_pos.2 hδ.ne'
  set t := (G.gcd r0).gcd d0 with ht
  have ht0 : 0 < t := Nat.gcd_pos_of_pos_right _ hd0
  obtain ⟨A', hA'⟩ := (Nat.gcd_dvd_left _ d0).trans (G.gcd_dvd_left r0)
  obtain ⟨B', hB'⟩ := (Nat.gcd_dvd_left _ d0).trans (G.gcd_dvd_right r0)
  obtain ⟨D', hD'⟩ := (G.gcd r0).gcd_dvd_right d0
  rw [← ht] at hA' hB' hD'
  have hBz : β % δ = t * B' := by have := Int.emod_nonneg β hδ.ne'; rw [← Int.natCast_mul, ← hB']; omega
  have hDz : δ = t * D' := by rw [← Int.natCast_mul, ← hD']; omega
  obtain ⟨m, hm⟩ := he
  obtain ⟨r, ⟨hrR, hσr⟩, -⟩ := hR σ
  set κ := ε / (Real.sqrt e * h)
  refine ⟨ofZ (r * σ⁻¹), ?_, r, hrR, A', B', D',
    ⟨Nat.pos_of_mul_pos_left (hA' ▸ hG0),
      Nat.pos_of_mul_pos_left (hD' ▸ hd0),
      ⟨t ^ 2 * m, by
        zify [← nDelta_mul (Δ := Δ), show hDelta N Δ = h from rfl, hm]
        rw [hDz, hA'] at hGδ; push_cast at hGδ; linear_combination -m * hGδ⟩,
      by have := Int.emod_lt_of_pos β hδ; nlinarith,
      Nat.eq_of_mul_eq_mul_left ht0 (by rw [← Nat.gcd_mul_left, ← Nat.gcd_mul_left, ← hA', ← hB', ← hD', mul_one])⟩,
    κ * t, by rcases hε with rfl | rfl <;> simp [κ, hh.ne', he0.ne', ht0.ne'], ?_⟩
  · rw [show r * σ⁻¹ = (σ * r⁻¹)⁻¹ by group]; exact Subgroup.mem_map_of_mem _ (inv_mem hσr)
  · rw [coe_mul, show (ofZ r : MatR) = ofZ (r * σ⁻¹) * ofZ σ by
      rw [← coe_mul, ← map_mul, inv_mul_cancel_right], mul_assoc, ← mul_smul_comm]
    congr 1
    trans κ • !![(w00 : ℝ), b; w10, w11]
    · rw [hgm]; simp [κ, w00, w10, w11, show (h : ℝ) ≠ 0 by positivity, div_eq_inv_mul, mul_comm, mul_assoc, mul_left_comm]
    · rw [mul_smul]; congr 1
      have hβ := Int.mul_ediv_add_emod β δ; rw [← hk, hBz, hDz] at hβ
      dsimp [β, δ] at hβ hDz
      rw [coe_ofZ, hermMat, mul_fin_two]; simp [σ, mkSL]; norm_cast
      exact ⟨⟨by rw [hp, hA']; push_cast; ring,
        by linear_combination -b * hbez - p * hβ - B0 * hDz⟩,
        by rw [hq, hA']; push_cast; ring,
        by linear_combination -w11 * hbez - q * hβ + A0 * hDz⟩

/-- The pair (σ, H) of `exists_sigmaH` is unique. -/
theorem sigmaH_unique {N : ℕ} [NeZero N] {R : Set SL(2, ℤ)} (hR : IsGamma0Reps N R)
    {r r' : SL(2, ℤ)} (hr : r ∈ R) (hr' : r' ∈ R) {a b d a' b' d' : ℕ}
    (hH : IsHermiteN N a b d) (hH' : IsHermiteN N a' b' d') {c c' : ℝ} (hc : c ≠ 0) (_hc' : c' ≠ 0)
    {γ : SL(2, ℝ)} (hγ : γ ∈ Gamma0R N)
    (h : c • ((ofZ r : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a b d) =
      (γ : Matrix (Fin 2) (Fin 2) ℝ) * (c' • ((ofZ r' : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a' b' d'))) :
    r = r' ∧ a = a' ∧ b = b' ∧ d = d' := by
  obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
  obtain ⟨ha, hd, -, hbd, hprim⟩ := hH
  obtain ⟨ha', hd', -, hbd', hprim'⟩ := hH'
  let M : SL(2, ℤ) := r'⁻¹ * γ₀⁻¹ * r
  have key := congrArg ((ofZ (r'⁻¹ * γ₀⁻¹) : MatR) * ·) h
  simp only [mul_smul_comm, ← mul_assoc, ← coe_mul, ← map_mul,
    show r'⁻¹ * γ₀⁻¹ * (γ₀ * r') = 1 by group, map_one, coe_one, one_mul] at key
  rw [show r'⁻¹ * γ₀⁻¹ * r = M from rfl, coe_ofZ, hermMat, mul_fin_two] at key
  obtain ⟨⟨e00, e01⟩, e10, e11⟩ := by simpa [hermMat] using key
  have hM10 : M 1 0 = 0 := by simpa [hc, ha.ne'] using e10
  simp [hM10] at e11
  have hdetM : M 0 0 * M 1 1 = 1 := by simpa [-det_coe, det_fin_two, hM10] using M.2
  have hss : M 1 1 = M 0 0 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdetM with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  rw [hss] at hdetM e11
  set s := M 0 0
  let k : ℤ := s * M 0 1
  have hsr : (s : ℝ) * s = 1 := by exact_mod_cast hdetM
  have hcs : c * s ≠ 0 := mul_ne_zero hc (left_ne_zero_of_mul_eq_one hsr)
  let B₁ : ℤ := b + d * k
  have Y1 : (a : ℤ) * b' = B₁ * a' := Int.cast_injective (α := ℝ) <|
    mul_left_cancel₀ hcs (by dsimp [B₁, k]; push_cast; linear_combination b' * e00 - a' * e01 - c * a' * d * M 0 1 * hsr)
  have Y2 : a * d' = d * a' := Nat.cast_injective (R := ℝ) <|
    mul_left_cancel₀ hcs (by push_cast; linear_combination d' * e00 - a' * e11)
  have Y1n : a * b' = B₁.natAbs * a' := by simpa [Int.natAbs_mul] using congrArg Int.natAbs Y1
  have hg1 : Nat.gcd (Nat.gcd a B₁.natAbs) d = 1 := by
    rw [Nat.gcd_assoc, show B₁.natAbs.gcd d = B₁.gcd d from rfl,
      Int.gcd_add_mul_left_left, Int.gcd_natCast_natCast, ← Nat.gcd_assoc, hprim]
  obtain rfl : a = a' := by
    simpa [Nat.gcd_mul_left, Nat.gcd_mul_right, hprim', hg1] using
      congrArg₂ Nat.gcd (congrArg ((a * a').gcd ·) Y1n) Y2
  obtain rfl : d = d' := by nlinarith only [ha, Y2]
  have hb' : (b' : ℤ) = b + d * k := by nlinarith only [ha, Y1, show B₁ = b + d * k from rfl]
  have hk0 : k = 0 := by rcases lt_trichotomy k 0 with hk | hk | hk <;> nlinarith only [hb', hbd, hbd', hd, hk]
  have hM01 : M 0 1 = 0 := by dsimp [k] at hk0; linear_combination -M 0 1 * hdetM + s * hk0
  have hMr : r' * M = M * r' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, hM10, hM01, hss] <;> ring
  refine ⟨(hR r).unique ⟨hr, by simp⟩ ⟨hr', ?_⟩, rfl, by rw [hk0] at hb'; omega, rfl⟩
  rw [show r * r'⁻¹ = γ₀ * M by rw [show r = γ₀ * (r' * M) by simp [M, mul_assoc], hMr]; group]
  exact mul_mem hγ₀ (Gamma0_mem.2 (by simp [hM10]))

def gamma0Reps (N : ℕ) : Set SL(2, ℤ) :=
  Set.range fun q : SL(2, ℤ) ⧸ Gamma0 N => (Quotient.out q)⁻¹

theorem isGamma0Reps (N : ℕ) : IsGamma0Reps N (gamma0Reps N) := by
  let mk : SL(2, ℤ) → SL(2, ℤ) ⧸ Gamma0 N := QuotientGroup.mk
  refine fun σ => ⟨(mk σ⁻¹).out⁻¹, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · simpa using QuotientGroup.eq.1 (QuotientGroup.out_eq' (mk σ⁻¹)).symm
  · rintro _ ⟨⟨q, rfl⟩, hq⟩
    congr 1; rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 (by simpa using inv_mem hq)

/-- Sets of representatives of Γ₀(N)\SL₂(ℤ) exist. -/
theorem exists_Gamma0Reps (N : ℕ) : ∃ R : Set SL(2, ℤ), IsGamma0Reps N R :=
  ⟨_, isGamma0Reps N⟩

abbrev pSH (r : SL(2, ℤ)) (a b d : ℕ) : SL(2, ℝ) := projSL ((ofZ r : MatR) * hermMat a b d)

abbrev SigmaHSet (N : ℕ) (R : Set SL(2, ℤ)) (K : Subgroup SL(2, ℝ)) : Type :=
  {x : SL(2, ℤ) × ℕ × ℕ × ℕ // x.1 ∈ R ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2 ∧
    pSH x.1 x.2.1 x.2.2.1 x.2.2.2 ∈ K}

def sigmaHMap (N : ℕ) (R : Set SL(2, ℤ)) (K : Subgroup SL(2, ℝ)) :
    SigmaHSet N R K → K ⧸ (Gamma0R N).subgroupOf K :=
  fun ⟨⟨r, a, b, d⟩, h⟩ => QuotientGroup.mk ⟨(pSH r a b d)⁻¹, K.inv_mem h.2.2⟩

theorem sigmaHMap_bijective {N : ℕ} [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {R : Set SL(2, ℤ)}
    (hR : IsGamma0Reps N R) {K : Subgroup SL(2, ℝ)} (hK0 : Gamma0R N ≤ K) (hKM : K ≤ MDelta N Δ) :
    Function.Bijective (sigmaHMap N R K) := by
  have hd (r) (a b d) : ((ofZ r : MatR) * hermMat a b d).det = a * d := by
    rw [det_mul, det_coe, one_mul, hermMat, det_fin_two_of]; ring
  have cproj (r) {a b d} (hH : IsHermiteN N a b d) :
      (pSH r a b d : MatR) =
        (Real.sqrt (a * d))⁻¹ • ((ofZ r : MatR) * hermMat a b d) ∧ Real.sqrt (a * d) ≠ 0 := by
    have hp : 0 < (a : ℝ) * d := by have := hH.1; have := hH.2.1; positivity
    exact ⟨by simp only [pSH, projSL, hd, hp, ↓reduceDIte], by positivity⟩
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨r, a, b, d⟩, hr, hH, _⟩ ⟨⟨r', a', b', d'⟩, hr', hH', _⟩ hxy
    have h1 : pSH r a b d * (pSH r' a' b' d')⁻¹ ∈ Gamma0R N := by
      simpa [sigmaHMap, QuotientGroup.eq, Subgroup.mem_subgroupOf] using hxy
    have hm := congrArg ((↑) : SL(2, ℝ) → MatR) (inv_mul_cancel_right (pSH r a b d) (pSH r' a' b' d')).symm
    rw [coe_mul, (cproj r hH).1, (cproj r' hH').1] at hm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := sigmaH_unique hR hr hr' hH hH'
      (inv_ne_zero (cproj r hH).2) (inv_ne_zero (cproj r' hH').2) h1 hm
    rfl
  · intro y
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨γ, hγ, r, hr, a, b, d, hH, c, _, heq⟩ := exists_sigmaH Δ hR (hKM (K.inv_mem hk))
    have hdet : c ^ 2 * (a * d) = 1 := by
      simpa only [det_coe, det_smul, Fintype.card_fin, hd, eq_comm] using congrArg det heq
    have hgk := congrArg ((c * Real.sqrt (a * d)) • ·) (cproj r hH).1
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ (cproj r hH).2, mul_one, ← heq] at hgk
    obtain ⟨δ, hδ0, hPeq⟩ : ∃ δ ∈ Gamma0R N, pSH r a b d = δ * k⁻¹ := by
      rcases (sq_eq_one_iff (a := c * Real.sqrt (a * d))).1
          (by rw [mul_pow, Real.sq_sqrt (by positivity), hdet]) with hu | hu
      · exact ⟨γ, hγ, Subtype.ext (by rwa [hu, one_smul] at hgk)⟩
      · exact ⟨-γ, by simpa using mul_mem (⟨-1, Gamma0_mem.2 (by simp), by simp⟩ : (-1 : SL(2, ℝ)) ∈ Gamma0R N) hγ,
          Subtype.ext (by rw [neg_mul, coe_neg, ← hgk, hu, neg_one_smul, neg_neg])⟩
    exact ⟨⟨(r, a, b, d), hr, hH, hPeq ▸ mul_mem (hK0 hδ0) (K.inv_mem hk)⟩,
      QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf, hPeq, mul_assoc] using hδ0)⟩

/-- **The count of `aut_orders.py`**. -/
theorem relIndex_normG_eq_card_sigmaH {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ)
    {R : Set SL(2, ℤ)} (hR : IsGamma0Reps N R) :
    (Gamma0R N).relIndex (NormG (GammaDeltaR N Δ)) =
      Nat.card {x : SL(2, ℤ) × ℕ × ℕ × ℕ // x.1 ∈ R ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2 ∧
        projSL ((ofZ x.1 : Matrix (Fin 2) (Fin 2) ℝ) * hermMat x.2.1 x.2.2.1 x.2.2.2) ∈
          NormG (GammaDeltaR N Δ)} :=
  (Nat.card_congr (Equiv.ofBijective _ (sigmaHMap_bijective hR
    Gamma0R_le_normG_GammaDeltaR (normG_GammaDeltaR_le_MDelta N Δ)))).symm

/-- Γ₀(N) has finite index in M_Δ. -/
theorem relIndex_Gamma0R_MDelta_ne_zero (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    (Gamma0R N).relIndex (MDelta N Δ) ≠ 0 := by
  have : Finite (SL(2, ℤ) ⧸ Gamma0 N) := Subgroup.finite_quotient_of_finiteIndex
  let I := Set.finite_Iic N
  have : Finite (SigmaHSet N (gamma0Reps N) (MDelta N Δ)) := Set.Finite.to_subtype <|
    ((Set.finite_range _).prod (I.prod (I.prod I))).subset fun _ ⟨hr, ⟨ha, hd, had, hbd, _⟩, _⟩ => by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) had
      refine ⟨hr, ?_⟩; simp; refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  have := Finite.of_surjective _
    (sigmaHMap_bijective (Δ := Δ) (isGamma0Reps N) (Gamma0R_le_MDelta N Δ) le_rfl).2
  exact Subgroup.index_ne_zero_of_finite

/-- The index: [Nor(Γ_Δ(N)) : Γ_Δ(N)] = i_Δ · [Nor(Γ_Δ(N)) : Γ₀(N)]. -/
theorem card_BG_GammaDeltaR_eq (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    Nat.card (BG (GammaDeltaR N Δ)) = Δ.index * (Gamma0R N).relIndex (NormG (GammaDeltaR N Δ)) := by
  change (GammaDeltaR N Δ).relIndex (NormG (GammaDeltaR N Δ)) = _
  have h1 : GammaDeltaR N Δ ≤ Gamma0R N := Subgroup.map_mono fun _ h => h.1
  rw [← Subgroup.relIndex_mul_relIndex (hHK := h1) (hKL := Gamma0R_le_normG_GammaDeltaR),
    GammaDeltaR, toR, Gamma0R, Subgroup.relIndex_map_map_of_injective _ _ map_intCast_injective,
    Subgroup.relIndex, GammaDelta_subgroupOf]
  refine congrArg (· * _) (Subgroup.index_comap_of_surjective _ fun u => ?_)
  obtain ⟨x, y, hdet⟩ := exists_bezout_unit u
  exact ⟨⟨mkSL _ _ _ _ hdet, Gamma0_mem.2 (by simp [mkSL])⟩, Units.ext (by simp [mkSL, Gamma0Map])⟩

/-- Nor(Γ_Δ(N))/Γ_Δ(N) is finite, for every Δ. -/
theorem finite_BG_GammaDeltaR (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    Finite (BG (GammaDeltaR N Δ)) :=
  Nat.finite_of_card_ne_zero (card_BG_GammaDeltaR_eq N Δ ▸ mul_ne_zero Subgroup.index_ne_zero_of_finite
    (mt (Subgroup.relIndex_eq_zero_of_le_right (normG_GammaDeltaR_le_MDelta N Δ))
      (relIndex_Gamma0R_MDelta_ne_zero N Δ)))

/-! ## §H. When h_Δ ≠ h(N) -/

/-- h_Δ = h(N) iff none of cases i)–iii) hold. -/
theorem hDelta_eq_hPart_iff (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    hDelta N Δ = hPart N ↔
      ¬ ((∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ^ 2 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod p d) ∨
        (3 ^ 4 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod 9 d) ∨
        (2 ^ 8 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod 8 d)) := by
  have hN := NeZero.ne N
  have hε0 := (epsDelta_pos (N := N) (Δ := Δ)).ne'
  let c (p : ℕ) := if p = 2 then 3 else if p = 3 then 1 else 0
  let M (p : ℕ) := if p = 2 then 8 else if p = 3 then 9 else p
  have hloc : ∀ {p : ℕ}, p.Prime →
      ((hDelta N Δ).factorization p ≠ (hPart N).factorization p ↔
        p ^ (2 * c p + 2) ∣ N ∧ ∀ u ∈ Δ, IsPmOneMod (M p) u) := fun {p} hp => by
    have hle : min (N.factorization p) (c p) ≤ (epsDelta N Δ).factorization p := by
      by_cases hpN : p ∣ N; swap; · simp [Nat.factorization_eq_zero_of_not_dvd hpN]
      by_cases hc0 : c p = 0; · simp [hc0]
      refine (hp.pow_dvd_iff_le_factorization hε0).1 (dvd_epsDelta_iff.2
        ⟨(pow_dvd_pow p (min_le_left _ _)).trans (Nat.ordProj_dvd N p),
          fun u _ => (pow_dvd_pow p (min_le_right _ _)).trans ?_⟩)
      rw [dvd_val_sq hp hpN,
        ← ZMod.coe_unitOfCoprime _ (((ZMod.val_coe_unit_coprime u).coprime_dvd_right hpN).pow_right (c p))]
      generalize ZMod.unitOfCoprime _ _ = v
      rcases (show p = 2 ∨ p = 3 by grind) with rfl | rfl <;> (dsimp [c] at v ⊢; revert v; decide)
    have hhp : (hPart N).factorization p = min (c p) (N.factorization p / 2) := by
      unfold hPart; simp [Nat.prime_two.factorization, Nat.prime_three.factorization]; grind
    refine Iff.trans (b := 2 * c p + 2 ≤ N.factorization p ∧ c p + 1 ≤ (epsDelta N Δ).factorization p)
      (by rw [factorization_hDelta, hhp]; omega) ?_
    rw [← hp.pow_dvd_iff_le_factorization hN, ← hp.pow_dvd_iff_le_factorization hε0, dvd_epsDelta_iff]
    refine and_congr_right fun hN' => ?_
    rw [and_iff_right ((pow_dvd_pow p (m := c p + 1) (by omega)).trans hN')]
    refine forall₂_congr fun u _ => (dvd_val_sq hp ((dvd_pow_self p (by omega)).trans hN') u).trans ?_
    rcases eq_or_ne p 2 with rfl | h2
    · rw [show 2 ^ (c 2 + 1) = 16 from rfl, (by decide : ∀ y : ZMod 16, y ^ 2 = 1 ↔
        (ZMod.castHom (by decide) (ZMod 8) y = 1 ∨ ZMod.castHom (by decide) (ZMod 8) y = -1)), map_natCast]
      simp [M, IsPmOneMod]
    rcases eq_or_ne p 3 with rfl | h3
    · rw [show 3 ^ (c 3 + 1) = 9 from rfl, (by decide : ∀ y : ZMod 9, y ^ 2 = 1 ↔ y = 1 ∨ y = -1)]
      simp [M, IsPmOneMod]
    have : Fact p.Prime := ⟨hp⟩
    rw [show c p = 0 by grind, show M p = p by grind, zero_add, pow_one]
    simp [sq_eq_one_iff, IsPmOneMod]
  have h2 := hloc Nat.prime_two; have h3 := hloc Nat.prime_three
  dsimp [c, M] at h2 h3
  refine ⟨fun h => by grind,
    fun h => Nat.eq_of_factorization_eq hDelta_pos.ne' (by unfold hPart; positivity) fun p => by
      rcases eq_or_ne p 2 with rfl | _; · grind
      rcases eq_or_ne p 3 with rfl | _; · grind
      by_cases hp : p.Prime
      · have := hp.two_le; grind [show ¬ Nat.Prime 4 by decide]
      · simp [Nat.factorization_eq_zero_of_not_prime _ hp]⟩

end

end NormalizerLean
