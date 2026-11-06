module

public import NormalizerLean.Defs

@[expose] public section

open Matrix MatrixGroups CongruenceSubgroup

namespace NormalizerLean

noncomputable section

local notation "M2" => Matrix (Fin 2) (Fin 2) ℝ
local notation "SLR" => SL(2, ℝ)
local notation "SLZ" => SL(2, ℤ)
local macro "mext" : tactic => `(tactic| (ext i j; fin_cases i <;> fin_cases j))

variable {N : ℕ} {Δ : Subgroup (ZMod N)ˣ}

theorem coe_projSL (A) (hA : 0 < A.det) :
    (projSL A : M2) = (Real.sqrt A.det)⁻¹ • A := by
  simp [projSL, hA]

def conjM (g : SLR) (M : M2) : M2 :=
  (g : M2) * M * (g : M2).adjugate

theorem coe_conj (g Y : SLR) :
    (↑(g * Y * g⁻¹) : M2) = conjM g Y := by
  simp [conjM]

def Smat (h : ℕ) (α β γ δ : ℤ) : M2 :=
  !![(α : ℝ), (β : ℝ) / h; (h : ℝ) * γ, (δ : ℝ)]

theorem det_Smat {h} (hh : h ≠ 0) (α β γ δ) :
    (Smat h α β γ δ).det = ((α * δ - β * γ : ℤ) : ℝ) := by
  have hhr : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  rw [Smat, det_fin_two_of]; push_cast; field_simp

theorem conjM_eq_Smat {g : SLR} {κ : ℝ} {h α β γ δ}
    (hg : (g : M2) = κ • Smat h α β γ δ) (hh : h ≠ 0) (M) :
    conjM g M = ((α * δ - β * γ : ℤ) : ℝ)⁻¹ •
      (Smat h α β γ δ * M * !![(δ : ℝ), -((β : ℝ) / h); -((h : ℝ) * γ), (α : ℝ)]) := by
  rw [conjM, hg, adjugate_smul, Fintype.card_fin, Smat, adjugate_fin_two_of, ← Smat]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Nat.add_one_sub_one, pow_one]
  congr 1; exact eq_inv_of_mul_eq_one_left (by simpa [hg, det_smul, sq, det_Smat hh] using g.2)

def vz (p : ℕ) (x : ℤ) : ℕ := x.natAbs.factorization p

theorem vz_mul {p x y} (hx : x ≠ 0) (hy : y ≠ 0) : vz p (x * y) = vz p x + vz p y := by
  simp [vz, Int.natAbs_mul, Nat.factorization_mul (Int.natAbs_ne_zero.2 hx)
    (Int.natAbs_ne_zero.2 hy)]

@[simp] theorem vz_natCast (p n : ℕ) : vz p n = n.factorization p := by simp [vz]

@[simp] theorem vz_one (p : ℕ) : vz p 1 = 0 := by simp [vz]

theorem pow_dvd_iff_le_vz {p : ℕ} (hp : p.Prime) {x} (hx : x ≠ 0) (m) :
    (p : ℤ) ^ m ∣ x ↔ m ≤ vz p x := by
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_pow, Int.natAbs_natCast,
    hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.2 hx), vz]

def vv (B p : ℕ) (x : ℤ) : ℕ := if x = 0 then B else vz p x

theorem le_vv2 (B p) {e : ℤ} (he : e ≠ 0) (m K x y a : ℤ)
    (h : ((e : ℝ))⁻¹ * (K * (x * y)) = m * a)
    (hm : m ≠ 0 := by positivity) (hK : K ≠ 0 := by positivity) :
    vz p e + vz p m ≤ B → vz p e + vz p m ≤ vz p K + vv B p x + vv B p y := by
  by_cases hx : x = 0; · simp [vv, hx]; omega
  by_cases hy : y = 0; · simp [vv, hy]; omega
  have her : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have heq : K * (x * y) = e * m * a := by
    exact_mod_cast (by rw [mul_assoc (e : ℝ), ← h]; field_simp : (K * (x * y) : ℝ) = e * m * a)
  have ha : a ≠ 0 := fun ha => mul_ne_zero hK (mul_ne_zero hx hy) (by simp [heq, ha])
  have := congrArg (vz p) heq
  rw [vz_mul hK (mul_ne_zero hx hy), vz_mul hx hy, vz_mul (mul_ne_zero he hm) ha, vz_mul he hm] at this
  simp [vv, hx, hy]; omega

theorem pow_vv_dvd {B p : ℕ} (hp : p.Prime) (x) : (p : ℤ) ^ vv B p x ∣ x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (pow_dvd_iff_le_vz hp hx _).2 (by simp [vv, hx])

theorem dvd_mul_of_vv_ne {B p : ℕ} (hp : p.Prime) {G x M : ℤ} (hM : M = G * x) (hx : vv B p x ≠ 0) :
    G * p ∣ M :=
  hM ▸ mul_dvd_mul_left G ((dvd_pow_self _ hx).trans (pow_vv_dvd hp x))

theorem dvd_of_forall_vv_le {m x} {B : ℕ → ℕ}
    (h : ∀ p : ℕ, p.Prime → vz p m ≤ vv (B p) p x) (hm : m ≠ 0 := by assumption) : m ∣ x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [← Int.natAbs_dvd_natAbs, ← Nat.factorization_le_iff_dvd (Int.natAbs_ne_zero.2 hm) (Int.natAbs_ne_zero.2 hx)]
  intro p
  by_cases hp : p.Prime
  · simpa [vv, hx, vz] using h p hp
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem GammaDeltaR_le_Gamma0R : GammaDeltaR N Δ ≤ Gamma0R N :=
  Subgroup.map_mono fun _ h => h.1

def mkSL (a b c d : ℤ) (h : a * d - b * c = 1) : SLZ := ⟨!![a, b; c, d], by
  rw [det_fin_two_of]; exact h⟩

theorem dvd_epsDelta_iff [NeZero N] {m} :
    m ∣ epsDelta N Δ ↔ m ∣ N ∧ ∀ u ∈ Δ, m ∣ (u : ZMod N).val ^ 2 - 1 := by
  classical
  unfold epsDelta
  rw [Nat.dvd_gcd_iff, Finset.dvd_gcd_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem epsDelta_ne_zero [NeZero N] (Δ) : epsDelta N Δ ≠ 0 :=
  fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ (dvd_epsDelta_iff.1 dvd_rfl).1))

theorem epsDelta_le [NeZero N] (Δ) (p) :
    (epsDelta N Δ).factorization p ≤ N.factorization p :=
  (Nat.factorization_le_iff_dvd (epsDelta_ne_zero Δ) (NeZero.ne N)).2 (dvd_epsDelta_iff.1 dvd_rfl).1 p

theorem one_le_sq_val [NeZero N] (hN : N ≠ 1) (u : (ZMod N)ˣ) : 1 ≤ (u : ZMod N).val ^ 2 := by
  have := ZMod.nontrivial_iff.2 hN
  exact Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (mt (ZMod.val_eq_zero _).1 u.ne_zero))

theorem factorization_hDelta [NeZero N] (p) :
    (hDelta N Δ).factorization p =
      min ((epsDelta N Δ).factorization p) (N.factorization p / 2) := by
  unfold hDelta
  rw [Nat.factorization_prod (fun q hq => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero),
    Finset.sum_apply', Finset.sum_congr rfl (fun q hq => by
      rw [(Nat.prime_of_mem_primeFactors hq).factorization_pow, Finsupp.single_apply]),
    Finset.sum_ite_eq']
  split_ifs with hp; · rfl
  simp [Finsupp.notMem_support_iff.1 (Nat.support_factorization N ▸ hp)]

theorem hDelta_pos [NeZero N] : 0 < hDelta N Δ :=
  Finset.prod_pos fun _ hq => pow_pos (Nat.pos_of_mem_primeFactors hq) _

theorem nDelta_mul [NeZero N] (Δ) : nDelta N Δ * hDelta N Δ ^ 2 = N := by
  refine Nat.div_mul_cancel ((Nat.factorization_le_iff_dvd (pow_ne_zero 2 hDelta_pos.ne') (NeZero.ne N)).1 fun p => ?_)
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, factorization_hDelta]
  omega

instance [NeZero N] : NeZero (nDelta N Δ) :=
  ⟨fun h => NeZero.ne N (by rw [← nDelta_mul Δ, h, zero_mul])⟩

theorem unit_bezout (u : (ZMod N)ˣ) :
    Int.gcdA (u : ZMod N).val N * (u : ZMod N).val - -Int.gcdB (u : ZMod N).val N * N = 1 := by
  have hb := Int.gcd_eq_gcd_ab (u : ZMod N).val N
  rw [Int.gcd_natCast_natCast, ZMod.val_coe_unit_coprime u] at hb
  push_cast at hb; linear_combination -hb

def InLe (N : ℕ) (M : M2) : Prop :=
  (∀ i j, ∃ m : ℤ, M i j = m) ∧ ∃ c : ℤ, M 1 0 = N * c

theorem InLe.sub {g M M'}
    (h : InLe N (conjM g M)) (m : ℤ) (h' : InLe N (conjM g M')) :
    InLe N (conjM g (M - (m : ℝ) • M')) := by
  obtain ⟨hb, c, hc⟩ := h; obtain ⟨hb', c', hc'⟩ := h'
  simp only [conjM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul] at *
  refine ⟨fun i j => ?_, c - m * c', by simp [hc, hc']; ring⟩
  obtain ⟨a, ha⟩ := hb i j; obtain ⟨b, hb⟩ := hb' i j
  exact ⟨a - m * b, by simp [ha, hb]⟩

theorem InLe.eq {g M M'} (h : InLe N (conjM g M))
    (heq : M = M' := by mext <;> simp) :
    InLe N (conjM g M') :=
  heq ▸ h

theorem mkSL_InLe {g} (hg : g ∈ NormG (GammaDeltaR N Δ))
    (a b c d : ℤ) (h : a * d - b * c = 1) (hc : (N : ℤ) ∣ c)
    {u} (hu : u ∈ Δ) (hud : (d : ZMod N) = u) :
    InLe N (conjM g !![(a : ℝ), b; c, d]) := by
  rcases GammaDeltaR_le_Gamma0R ((Subgroup.mem_normalizer_iff.1 hg _).1
    (Subgroup.mem_map_of_mem _ (show mkSL a b c d h ∈ GammaDelta N Δ from
      ⟨Gamma0_mem.2 ((ZMod.intCast_zmod_eq_zero_iff_dvd c N).2 hc), u, hu, hud.symm⟩)))
    with ⟨A, hA, hAm⟩
  rw [show !![(a : ℝ), b; c, d] = (ofZ (mkSL a b c d h) : M2) by
    mext <;> rfl, ← coe_conj, ← hAm]
  obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 hA)
  exact ⟨fun i j => ⟨A i j, rfl⟩, z, by simp [hz]⟩

theorem InLe_basic {g} (hg : g ∈ NormG (GammaDeltaR N Δ)) :
    InLe N (conjM g 1) ∧
      InLe N (conjM g !![0, 1; 0, 0]) ∧
      InLe N (conjM g ((N : ℝ) • !![0, 0; 1, 0])) ∧
      InLe N (conjM g ((N : ℝ) • !![0, 0; 0, 1])) := by
  have m (a b k : ℤ) (h : a * 1 - b * (N * k) = 1 := by ring) :=
    mkSL_InLe hg a b (N * k) 1 h (dvd_mul_right _ _) (one_mem _) Int.cast_one
  have h1 := m 1 0 0; have hT := m 1 1 0; have hU := m 1 0 1; have hTU := m (N + 1) 1 1
  simp only [Int.cast_one, Int.cast_zero, Int.cast_add, Int.cast_natCast,
    mul_zero, mul_one, ← Matrix.one_fin_two] at h1 hT hU hTU
  exact ⟨h1, (hT.sub 1 h1).eq, (hU.sub 1 h1).eq,
    (((hT.sub (-1) hU).sub 1 hTU).sub (1 - N) h1).eq⟩

def unitMap (N : ℕ) : Gamma0 N →* (ZMod N)ˣ :=
  (Gamma0Map N).toHomUnits

theorem GammaDelta_subgroupOf (Δ) :
    (GammaDelta N Δ).subgroupOf (Gamma0 N) = Δ.comap (unitMap N) :=
  Subgroup.ext fun x =>
    ⟨fun ⟨_, _, hu, hud⟩ => by rwa [Subgroup.mem_comap, show unitMap N x = _ from Units.ext hud.symm],
      fun h => ⟨x.2, _, h, rfl⟩⟩

theorem Gamma0R_le_normG_GammaDeltaR' :
    Gamma0R N ≤ NormG (GammaDeltaR N Δ) := by
  have conj {g γ} (hg : g ∈ Gamma0 N) (hγ : γ ∈ GammaDelta N Δ) :
      g * γ * g⁻¹ ∈ GammaDelta N Δ := by
    let g' : Gamma0 N := ⟨g, hg⟩
    let γ' : Gamma0 N := ⟨γ, hγ.1⟩
    have h := Subgroup.ext_iff.1 (GammaDelta_subgroupOf Δ)
    exact (h (g' * γ' * g'⁻¹)).2 (by simpa [Subgroup.mem_comap, mul_right_comm] using (h γ').1 hγ)
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  exact fun Y => ⟨fun ⟨γ, hγ, hY⟩ => ⟨g * γ * g⁻¹, conj hg hγ, by simp [← hY]⟩,
    fun ⟨γ, hγ, hY⟩ => ⟨g⁻¹ * γ * g⁻¹⁻¹, conj (inv_mem hg) hγ, by simp [hY, mul_assoc]⟩⟩

abbrev Dm (M : ℕ) : SLR := projSL !![(M : ℝ), 0; 0, 1]

theorem coe_conj_Dm {M} (hM : 0 < M) (Y) :
    (MulAut.conj (Dm M) Y : M2) =
      !![(Y : M2) 0 0, M * (Y : M2) 0 1;
        (Y : M2) 1 0 / M, (Y : M2) 1 1] := by
  rw [MulAut.conj_apply, coe_conj, conjM, Dm, coe_projSL _ (by rw [det_fin_two_of]; simp; positivity),
    adjugate_smul, det_fin_two_of, adjugate_fin_two_of]
  mext <;> simp [mul_apply, vecMul, dotProduct] <;> field_simp <;>
    rw [Real.sq_sqrt (Nat.cast_nonneg M)] <;> ring

def alSub (n : ℕ) [NeZero n] : Subgroup SLR where
  carrier := {g | ∃ Q, Q ∣ n ∧ IsAtkinLehner n Q g}
  one_mem' := ⟨1, one_dvd n, 1, 0, 0, 1, by ring, by mext <;> simp⟩
  mul_mem' := by
    rintro g₁ g₂ ⟨Q₁, hQ₁, x₁, y₁, z₁, w₁, hd₁, hg₁⟩ ⟨Q₂, hQ₂, x₂, y₂, z₂, w₂, hd₂, hg₂⟩
    set G := Nat.gcd Q₁ Q₂
    have hG0 : 0 < G := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos hQ₁ (Nat.pos_of_ne_zero (NeZero.ne n)))
    obtain ⟨q₁, hq₁⟩ : G ∣ Q₁ := Nat.gcd_dvd_left Q₁ Q₂
    obtain ⟨q₂, hq₂⟩ : G ∣ Q₂ := Nat.gcd_dvd_right Q₁ Q₂
    obtain ⟨L, hLN⟩ : G * q₁ * q₂ ∣ n := by
      refine Nat.dvd_of_mul_dvd_mul_left hG0 ?_
      rw [← mul_assoc, ← hq₁, mul_comm G, mul_assoc, ← hq₂, ← Nat.gcd_mul_lcm Q₁ Q₂]
      exact mul_dvd_mul_left G (Nat.lcm_dvd hQ₁ hQ₂)
    refine ⟨q₁ * q₂, ⟨G * L, by rw [hLN]; ring⟩,
      G * x₁ * x₂ + L * y₁ * z₂, q₁ * x₁ * y₂ + q₂ * y₁ * w₂, q₂ * z₁ * x₂ + q₁ * w₁ * z₂,
      L * z₁ * y₂ + G * w₁ * w₂, ?_, ?_⟩
    · refine mul_left_cancel₀ (by positivity : (G : ℤ) ^ 2 ≠ 0) ?_
      push_cast [hLN, hq₁, hq₂] at hd₁ hd₂ ⊢
      linear_combination (G : ℤ) * q₂ * (G * q₂ * x₂ * w₂ - q₁ * L * y₂ * z₂) * hd₁ + G * q₁ * hd₂
    · have hsq : Real.sqrt Q₁ * Real.sqrt Q₂ = G * Real.sqrt (q₁ * q₂ : ℕ) := by
        rw [← Real.sqrt_mul (Nat.cast_nonneg _), hq₁, hq₂]
        push_cast
        rw [show (G : ℝ) * q₁ * (G * q₂) = G ^ 2 * (q₁ * q₂) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg _)]
      rw [Matrix.SpecialLinearGroup.coe_mul, hg₁, hg₂, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        ← mul_inv, hsq, mul_inv, mul_comm (G : ℝ)⁻¹, mul_smul]
      congr 1; rw [hLN, hq₁, hq₂]; push_cast
      mext <;> simp <;> field_simp
  inv_mem' := by
    rintro g ⟨Q, hQ, x, y, z, w, hdet, hgm⟩
    exact ⟨Q, hQ, w, -y, -z, x, by linear_combination hdet, by simp [hgm, adjugate_fin_two_of]⟩

theorem coe_MDelta (N) [NeZero N] (Δ) :
    (MDelta N Δ : Set SLR) = {g | IsNewmanFormH N (hDelta N Δ) g} := by
  ext g
  rw [MDelta, show Gamma0Plus _ = _ from Subgroup.closure_eq (alSub _)]
  have hh : 0 < hDelta N Δ := hDelta_pos
  have hNr : (N : ℝ) = nDelta N Δ * (hDelta N Δ : ℝ) ^ 2 := by
    exact_mod_cast (nDelta_mul Δ).symm
  constructor
  · rintro ⟨w, ⟨Q, hQ, x, y, z, w', hdet, hwm⟩, hgw⟩
    have hQ0 : 0 < Q := Nat.pos_of_dvd_of_pos hQ (Nat.pos_of_ne_zero (NeZero.ne _))
    refine ⟨x, y, z, w', Q, hQ0, hQ, by rw [← nDelta]; linear_combination hdet, 1, Or.inl rfl, ?_⟩
    have hwg := coe_conj_Dm hh g
    rw [show MulAut.conj (Dm _) g = w by rw [← hgw]; simp [MulAut.conj_apply, mul_assoc], hwm] at hwg
    ext i j
    have hij := congrFun (congrFun hwg i) j
    fin_cases i <;> fin_cases j <;> simp [hNr] at hij ⊢ <;> field_simp at hij ⊢ <;> linarith
  · rintro ⟨a, b, c, d, e, he0, he, hdet, ε, hε, hgm⟩
    refine ⟨MulAut.conj (Dm (hDelta N Δ)) g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [← nDelta] at hdet
    obtain ⟨s, hs, rfl⟩ : ∃ s : ℤ, s * s = 1 ∧ (s : ℝ) = ε := by
      rcases hε with rfl | rfl; exacts [⟨1, rfl, Int.cast_one⟩, ⟨-1, rfl, by simp⟩]
    refine ⟨e, he, s * a, s * b, s * c, s * d,
      by linear_combination s * s * hdet + (e : ℤ) * hs, ?_⟩
    rw [coe_conj_Dm hh, hgm]; mext <;> simp [hNr] <;> field_simp

theorem Gamma0R_le_MDelta (N) [NeZero N] (Δ) : Gamma0R N ≤ MDelta N Δ := by
  rintro g ⟨A, hA, rfl⟩
  rw [← SetLike.mem_coe, coe_MDelta]
  obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 hA)
  have hh : 0 < hDelta N Δ := hDelta_pos
  have hNz : (N : ℤ) = nDelta N Δ * (hDelta N Δ : ℤ) ^ 2 := by
    exact_mod_cast (nDelta_mul Δ).symm
  have hdet := A.2; rw [det_fin_two, hz, hNz] at hdet
  refine ⟨A 0 0, A 0 1 * hDelta N Δ, z * hDelta N Δ, A 1 1, 1, one_pos, one_dvd _,
    by rw [← nDelta]; push_cast; linear_combination hdet, 1, Or.inl rfl, ?_⟩
  mext <;> simp [hz] <;> field_simp

theorem normG_GammaDeltaR_le_MDelta (N) [NeZero N] (Δ) :
    NormG (GammaDeltaR N Δ) ≤ MDelta N Δ := by
  intro g hg
  rw [← SetLike.mem_coe, coe_MDelta]
  obtain ⟨-, ⟨h01', c1', h10⟩, ⟨i01', c2', i10⟩, ⟨hE22, -⟩⟩ := InLe_basic hg
  obtain ⟨j, ht⟩ : ∃ j, (g : M2).adjugate 1 j ≠ 0 := by
    by_contra! h0; have := g.2; rw [det_fin_two] at this
    simp [adjugate_fin_two] at h0; simp [h0] at this
  set t := (g : M2).adjugate 1 j
  obtain ⟨Ix, hIx⟩ := h01' 0 j
  obtain ⟨Iz, hIz⟩ := h01' 1 j
  obtain ⟨Iy, hIy⟩ := hE22 0 j
  obtain ⟨Iw, hIw⟩ := hE22 1 j
  simp [conjM, Matrix.mul_apply] at hIx hIz hIy hIw
  have hN := NeZero.ne N
  have hNr0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hNz : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hN
  set h := hDelta N Δ
  have hh0 : 0 < h := hDelta_pos
  have hh := hh0.ne'
  have hhz : (h : ℤ) ≠ 0 := by positivity
  have hnz : (nDelta N Δ : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne _)
  have hNr : (N : ℝ) = nDelta N Δ * (h : ℝ) ^ 2 := by exact_mod_cast (nDelta_mul Δ).symm
  set M0 : ℤ := N * h * Ix
  set M1 : ℤ := h ^ 2 * Iy
  set M2' : ℤ := N * Iz
  set M3 : ℤ := h * Iw
  set G : ℕ := Int.gcd (Int.gcd M0 M1) (Int.gcd M2' M3) with hG
  obtain ⟨α, hα⟩ : (G : ℤ) ∣ M0 := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
  obtain ⟨β, hβ⟩ : (G : ℤ) ∣ M1 := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
  obtain ⟨γ, hγ⟩ : (G : ℤ) ∣ M2' := (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_left _ _)
  obtain ⟨δ, hδ⟩ : (G : ℤ) ∣ M3 := (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _)
  set κ : ℝ := G / ((h : ℝ) * N * t)
  have hgm : (g : M2) = κ • Smat h α β γ δ := by
    mext <;> simp [κ, Smat] <;> field_simp <;>
      rw [← Int.cast_natCast G, ← Int.cast_mul] <;>
      simp [← hα, ← hβ, ← hγ, ← hδ, M0, M1, M2', M3, ← hIx, ← hIy, ← hIz, ← hIw] <;> ring
  have hG0 : 0 < G := Nat.pos_of_ne_zero fun h0 => by simpa [hgm, κ, h0] using g.2
  have hdet : κ ^ 2 * ((α * δ - β * γ : ℤ) : ℝ) = 1 := by
    have := g.2
    rwa [hgm, det_smul, Fintype.card_fin, det_Smat hh] at this
  have hepos : 0 < α * δ - β * γ := by
    have : (0 : ℝ) < ((α * δ - β * γ : ℤ) : ℝ) := by by_contra! hc; nlinarith [sq_nonneg κ]
    exact_mod_cast this
  have he := hepos.ne'
  have hginv : (↑g⁻¹ : M2) =
      κ • Smat h δ (-β) (-γ) α := by
    simp [hgm, Smat, adjugate_fin_two_of]; ring
  have hgM := conjM_eq_Smat hgm hh
  have hginvM := conjM_eq_Smat hginv hh
  rw [show δ * α - -β * -γ = α * δ - β * γ by ring] at hginvM
  obtain ⟨b1, h01⟩ := h01' 0 1
  obtain ⟨b2, i01⟩ := i01' 0 1
  have hloc (p : ℕ) (hp : p.Prime) :
      let B := vz p (α * δ - β * γ) + N.factorization p + 1
      vz p (α * δ - β * γ) ≤ vv B p (nDelta N Δ) ∧
        vz p (nDelta N Δ) ≤ vv B p γ ∧
        vz p (α * δ - β * γ) ≤ vv B p α ∧
        vz p (α * δ - β * γ) ≤ vv B p δ := by
    intro B
    have prim : vv B p α = 0 ∨ vv B p β = 0 ∨ vv B p γ = 0 ∨ vv B p δ = 0 := by
      by_contra! hcon
      have hpG : G * p ∣ G := Int.natCast_dvd_natCast.1 <| by
        rw [hG, Nat.cast_mul]
        exact Int.dvd_coe_gcd
          (Int.dvd_coe_gcd (dvd_mul_of_vv_ne hp hα hcon.1) (dvd_mul_of_vv_ne hp hβ hcon.2.1))
          (Int.dvd_coe_gcd (dvd_mul_of_vv_ne hp hγ hcon.2.2.1) (dvd_mul_of_vv_ne hp hδ hcon.2.2.2))
      have := Nat.le_of_dvd hG0 hpG
      nlinarith [hp.two_le]
    have hkj : h.factorization p = _ := factorization_hDelta p
    have hnk : (nDelta N Δ).factorization p + 2 * h.factorization p = N.factorization p := by
      have := congrArg (·.factorization p) (nDelta_mul Δ)
      rw [Nat.factorization_mul (NeZero.ne _) (pow_ne_zero 2 hh), Nat.factorization_pow] at this
      simpa using this
    generalize nDelta N Δ = n at *
    set ν := N.factorization p
    set j := (epsDelta N Δ).factorization p
    have vn := vz_natCast p n
    have vvn : vv B p (n : ℤ) = n.factorization p := by simp [vv, vz]; omega
    have d (x y) : (p : ℤ) ^ (vv B p x + vv B p y) ∣ x * y :=
      pow_add (p : ℤ) _ _ ▸ mul_dvd_mul (pow_vv_dvd hp x) (pow_vv_dvd hp y)
    have u1 := (pow_dvd_iff_le_vz hp he _).1 (dvd_sub
      ((pow_dvd_pow _ (min_le_left _ _)).trans (d α δ))
      ((pow_dvd_pow _ (min_le_right _ _)).trans (d β γ)))
    have c2 := le_vv2 B p he 1 1 α α b1 (by simp [← h01, hgM, Smat])
    have c3 := le_vv2 B p he N (h * h) γ γ (-c1') (by simp [← h10, hgM, Smat]; left; ring)
    have c6 := le_vv2 B p he 1 n β β (-b2) (by simp [← i01, hgM, Smat, hNr]; left; field_simp)
    have c7 := le_vv2 B p he N N δ δ c2' (by simp [← i10, hgM, Smat]; left; ring)
    simp only [vz_mul hhz hhz, vz_natCast, vz_one] at c2 c3 c6 c7
    obtain ⟨s, hs0, hvs, ⟨j01', c4', j10⟩⟩ : ∃ s : ℤ, s ≠ 0 ∧ vz p s = j ∧
        InLe N (conjM g⁻¹ ((s : ℝ) • !![0, 0; 0, 1])) := by
      by_cases hνj : j < ν
      · have hpN : p ^ (j + 1) ∣ N := (hp.pow_dvd_iff_le_factorization hN).2 hνj
        have hε0 := epsDelta_ne_zero Δ
        obtain ⟨u, hu, hnd⟩ : ∃ u ∈ Δ, ¬ p ^ (j + 1) ∣ (u : ZMod N).val ^ 2 - 1 := by
          by_contra! hcon
          have := (hp.pow_dvd_iff_le_factorization hε0).1 (dvd_epsDelta_iff.2 ⟨hpN, hcon⟩)
          omega
        have hpj : p ^ j ∣ (u : ZMod N).val ^ 2 - 1 :=
          (Nat.ordProj_dvd (epsDelta N Δ) p).trans ((dvd_epsDelta_iff.1 dvd_rfl).2 u hu)
        set v := (u : ZMod N).val
        set x := Int.gcdA v N
        set y := -Int.gcdB v N
        have hdet' : x * v - y * N = 1 := unit_bezout u
        have hpv : IsCoprime (p : ℤ) v := by
          rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
          exact (Nat.Coprime.coprime_dvd_right
            ((dvd_pow_self p j.succ_ne_zero).trans hpN) (ZMod.val_coe_unit_coprime u)).symm
        have hdvd (m : ℕ) (hm : m ≤ j + 1 := by omega) :
            (p : ℤ) ^ m ∣ (v : ℤ) - x ↔ p ^ m ∣ v ^ 2 - 1 := by
          have hN' : (p : ℤ) ^ m ∣ y * N := dvd_mul_of_dvd_right
            (Int.natCast_dvd_natCast.2 ((pow_dvd_pow p hm).trans hpN)) y
          rw [← Int.natCast_dvd_natCast, Int.natCast_sub (one_le_sq_val (by rintro rfl; simp [ν] at hνj) u)]
          push_cast
          rw [show (v : ℤ) ^ 2 - 1 = v * (v - x) + y * N by linear_combination hdet', dvd_add_left hN']
          exact ⟨fun h => dvd_mul_of_dvd_right h _, hpv.pow_left.dvd_of_dvd_mul_left⟩
        have hnot : ¬ (p : ℤ) ^ (j + 1) ∣ (v : ℤ) - x := (hdvd (j + 1)).not.2 hnd
        have hs : (v : ℤ) - x ≠ 0 := fun h0 => hnot (by simp [h0])
        rw [pow_dvd_iff_le_vz hp hs] at hnot
        have := (pow_dvd_iff_le_vz hp hs j).1 ((hdvd j).2 hpj)
        have hP := mkSL_InLe (inv_mem hg) x y N v hdet' (dvd_refl _) hu (by simp [v])
        obtain ⟨h1, hE12, hE21, -⟩ := InLe_basic (inv_mem hg)
        exact ⟨(v : ℤ) - x, hs, by omega, (((hP.sub x h1).sub y hE12).sub 1 hE21).eq⟩
      · have hjν : j ≤ ν := epsDelta_le Δ p
        exact ⟨N, hNz, by rw [vz_natCast]; omega, (InLe_basic (inv_mem hg)).2.2.2⟩
    obtain ⟨b4, j01⟩ := j01' 0 1
    have t10 := le_vv2 B p he h s δ β (-b4) (by simp [← j01, hginvM, Smat]; field_simp)
    have t11 := le_vv2 B p he N (s * h) γ α c4' (by simp [← j10, hginvM, Smat]; left; ring)
    simp only [vz_mul hs0 hhz, hvs, vz_natCast] at t10 t11
    omega
  obtain ⟨c', hc'⟩ := dvd_of_forall_vv_le fun p hp => (hloc p hp).2.1
  obtain ⟨a', ha'⟩ := dvd_of_forall_vv_le fun p hp => (hloc p hp).2.2.1
  obtain ⟨d', hd'⟩ := dvd_of_forall_vv_le fun p hp => (hloc p hp).2.2.2
  set e : ℕ := (α * δ - β * γ).toNat
  have hEe : (e : ℤ) = α * δ - β * γ := Int.toNat_of_nonneg hepos.le
  have he0 : 0 < e := by omega
  have hs0 : Real.sqrt e ≠ 0 := by positivity
  have hdvd := Int.natCast_dvd_natCast.1 (hEe ▸ dvd_of_forall_vv_le fun p hp => (hloc p hp).1)
  rw [← hEe] at ha' hd' hdet
  refine ⟨a', β, c', d', e, he0, hdvd,
    by rw [← nDelta]; linear_combination -hEe - δ * ha' - e * a' * hd' + β * hc',
    κ * Real.sqrt e, ?_, ?_⟩
  · exact sq_eq_one_iff.1 (by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← Int.cast_natCast, hdet])
  · rw [hgm, mul_div_assoc, div_self hs0, mul_one, ha', hd', hc']
    congr 1; mext <;> simp [Smat, hNr] <;> field_simp

theorem exists_sigmaH {N} [NeZero N] (Δ) {R}
    (hR : IsGamma0Reps N R) {g} (hg : g ∈ MDelta N Δ) :
    ∃ γ ∈ Gamma0R N, ∃ r ∈ R, ∃ a b d, IsHermiteN N a b d ∧ ∃ c : ℝ, c ≠ 0 ∧
      ((γ * g : SLR) : M2) = c • ((ofZ r : M2) * hermMat a b d) := by
  rw [← SetLike.mem_coe, coe_MDelta] at hg
  obtain ⟨a, b, c, d, e, he0, ⟨m, hm⟩, hdet, ε, hε, hgm⟩ := hg
  rw [← nDelta] at hdet hm
  have hh : 0 < hDelta N Δ := hDelta_pos
  set h := hDelta N Δ
  have hNz : (N : ℤ) = nDelta N Δ * (h : ℤ) ^ 2 := by exact_mod_cast (nDelta_mul Δ).symm
  set w00 : ℤ := a * e * h
  set w10 : ℤ := N * c
  set w11 : ℤ := d * e * h
  obtain ⟨p, hp⟩ := Int.gcd_dvd_left w00 w10
  obtain ⟨q, hq⟩ := Int.gcd_dvd_right w00 w10
  set A := Int.gcd w00 w10
  set u := Int.gcdA w00 w10
  set v := Int.gcdB w00 w10
  set δ := p * w11 - q * b
  have hdetW : (A : ℤ) * δ = (h : ℤ) ^ 2 * e := by
    linear_combination -w11 * hp + b * hq + (h : ℤ) ^ 2 * hdet - b * c * hNz
  have hAD0 : 0 < (A : ℤ) * δ := by rw [hdetW]; positivity
  have hA : 0 < A := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hAD0
  have hδ : 0 < δ := pos_of_mul_pos_right hAD0 (by positivity)
  have hbez : p * u + q * v = 1 := mul_left_cancel₀ (by positivity : (A : ℤ) ≠ 0)
    (by linear_combination -Int.gcd_eq_gcd_ab w00 w10 - u * hp - v * hq)
  set β := u * b + v * w11
  set k := β / δ
  set B := (β % δ).toNat
  set D := δ.toNat
  have hB : (B : ℤ) = β % δ := Int.toNat_of_nonneg (Int.emod_nonneg β hδ.ne')
  have hD : (D : ℤ) = δ := Int.toNat_of_nonneg hδ.le
  have hBD : B < D := by have := Int.emod_lt_of_pos β hδ; omega
  have hD0 : 0 < D := by omega
  have hβ := Int.mul_ediv_add_emod β δ
  set σ := mkSL p (p * k - v) q (q * k + u) (by linear_combination hbez)
  set t := Nat.gcd (Nat.gcd A B) D with htdef
  have ht0 : 0 < t := Nat.gcd_pos_of_pos_right _ hD0
  obtain ⟨A', hA'⟩ : t ∣ A := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  obtain ⟨B', hB'⟩ : t ∣ B := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  obtain ⟨D', hD'⟩ : t ∣ D := Nat.gcd_dvd_right _ _
  obtain ⟨r, ⟨hrR, hσr⟩, -⟩ := hR σ
  have hεr : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  set κ := ε / (Real.sqrt e * h)
  rw [hA'] at hp hq hdetW; rw [hB'] at hB; rw [hD'] at hD; rw [hm] at hNz
  push_cast at hB hD hdetW hNz
  refine ⟨ofZ (r * σ⁻¹), ?_, r, hrR, A', B', D',
    ⟨Nat.pos_of_mul_pos_left (hA' ▸ hA), Nat.pos_of_mul_pos_left (hD' ▸ hD0),
      ⟨m * t ^ 2, by
        exact_mod_cast (by linear_combination hNz - m * hdetW - m * t * A' * hD :
          (N : ℤ) = A' * D' * (m * t ^ 2))⟩,
      Nat.lt_of_mul_lt_mul_left (a := t) (by rwa [← hB', ← hD']),
      Nat.eq_of_mul_eq_mul_left ht0 (by
        conv_rhs => rw [mul_one, htdef, hA', hB', hD', Nat.gcd_mul_left, Nat.gcd_mul_left])⟩,
    κ * t, mul_ne_zero (div_ne_zero hεr (by positivity)) (by positivity), ?_⟩
  · rw [show r * σ⁻¹ = (σ * r⁻¹)⁻¹ by group]
    exact Subgroup.mem_map_of_mem _ (inv_mem hσr)
  · have H0 : (a : ℝ) * e * h = t * A' * p := by exact_mod_cast hp
    have H1 : (b : ℝ) = p * t * B' + (p * k - v) * t * D' := by
      exact_mod_cast (by linear_combination -b * hbez - p * hβ - p * hB - (p * k - v) * hD)
    have H2 : (N : ℝ) * c = t * A' * q := by exact_mod_cast hq
    have H3 : (d : ℝ) * e * h = q * t * B' + (q * k + u) * t * D' := by
      exact_mod_cast (by linear_combination -w11 * hbez - q * hβ - q * hB - (q * k + u) * hD)
    rw [Matrix.SpecialLinearGroup.coe_mul,
      show (ofZ r : M2) = ofZ (r * σ⁻¹) * ofZ σ by
        rw [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, inv_mul_cancel_right],
      Matrix.mul_assoc, ← Matrix.mul_smul, hgm]
    congr 1; mext <;>
      simp [κ, hermMat, Matrix.mul_apply] <;> field_simp <;>
      simp [H0, H1, H2, H3, σ, mkSL, ← sub_eq_zero] <;> ring

theorem sigmaH_unique {N} [NeZero N] {R} (hR : IsGamma0Reps N R)
    {r r'} (hr : r ∈ R) (hr' : r' ∈ R) {a b d a' b' d'}
    (hH : IsHermiteN N a b d) (hH' : IsHermiteN N a' b' d') {c c' : ℝ} (hc : c ≠ 0) (_hc' : c' ≠ 0)
    {γ} (hγ : γ ∈ Gamma0R N)
    (h : c • ((ofZ r : M2) * hermMat a b d) =
      (γ : M2) * (c' • ((ofZ r' : M2) * hermMat a' b' d'))) :
    r = r' ∧ a = a' ∧ b = b' ∧ d = d' := by
  obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
  obtain ⟨ha, hd, -, hbd, hprim⟩ := hH
  obtain ⟨ha', hd', -, hbd', hprim'⟩ := hH'
  set M := r'⁻¹ * γ₀⁻¹ * r
  have key : c • ((ofZ M : M2) * hermMat a b d) = c' • hermMat a' b' d' := by
    simpa only [M, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      ← map_mul, ← mul_assoc, inv_mul_cancel_right, inv_mul_cancel, map_one,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul] using
      congrArg ((ofZ (r'⁻¹ * γ₀⁻¹) : M2) * ·) h
  have entry (i j) := congrFun (congrFun key i) j
  have e00 := entry 0 0; have e01 := entry 0 1; have e10 := entry 1 0; have e11 := entry 1 1
  simp [hermMat, Matrix.mul_apply] at e00 e01 e10 e11
  have hM10 : M 1 0 = 0 := (e10.resolve_left hc).resolve_right ha.ne'
  have hdetM : M 0 0 * M 1 1 = 1 := by
    have := M.2; rwa [det_fin_two, hM10, mul_zero, sub_zero] at this
  have hss : M 1 1 = M 0 0 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdetM with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  rw [hM10, hss] at e11
  rw [hss] at hdetM
  set s := M 0 0; set m := M 0 1
  have hdetR : (s : ℝ) * s = 1 := by exact_mod_cast hdetM
  have cancel {x y : ℤ} (h : c * x = c * y) : x = y := by exact_mod_cast mul_left_cancel₀ hc h
  have Y1 : (a : ℤ) * b' = (b + s * m * d) * a' := cancel
    (by push_cast; linear_combination (s : ℝ) * b' * e00 - s * a' * e01 - c * ((a : ℝ) * b' - b * a') * hdetR)
  have Y2 : (a : ℤ) * d' = d * a' := cancel
    (by push_cast; linear_combination (s : ℝ) * d' * e00 - s * a' * e11 - c * ((a : ℝ) * d' - d * a') * hdetR)
  have hdvd {x y z w : ℕ} (hp : Nat.gcd (Nat.gcd x y) z = 1)
      (hy : (x : ℤ) ∣ y * w) (hz : (x : ℤ) ∣ z * w) : x ∣ w := by
    rw [← one_mul w, ← hp, ← Nat.gcd_mul_right, ← Nat.gcd_mul_right]
    exact Nat.dvd_gcd (Nat.dvd_gcd (dvd_mul_right x w) (by exact_mod_cast hy)) (by exact_mod_cast hz)
  obtain rfl : a = a' := Nat.dvd_antisymm
    (hdvd hprim ⟨b' - s * m * d', by linear_combination -Y1 + s * m * Y2⟩
      ⟨d', by linear_combination -Y2⟩)
    (hdvd hprim' ⟨b + s * m * d, by linear_combination Y1⟩
      ⟨d, by linear_combination Y2⟩)
  obtain rfl : d = d' := by nlinarith
  have hbk : (b' : ℤ) = b + s * m * d := by nlinarith
  have : -1 < s * m ∧ s * m < 1 := ⟨by nlinarith, by nlinarith⟩
  have hsm : s * m = 0 := by omega
  obtain rfl : b = b' := by nlinarith
  have hM01 : m = 0 := by linear_combination -m * hdetM + s * hsm
  refine ⟨?_, rfl, rfl, rfl⟩
  have hM : (M : Matrix (Fin 2) (Fin 2) ℤ) = s • 1 := by
    mext <;> simp [s, m, hss, hM01, hM10]
  have hrM : r' * M * r'⁻¹ = M := Subtype.ext (by
    simp [hM]; rw [← Int.cast_comm, mul_assoc, mul_adjugate]; simp)
  exact (hR r).unique ⟨hr, by simp⟩ ⟨hr', by
    rw [show r * r'⁻¹ = γ₀ * (r' * M * r'⁻¹) by simp [M, mul_assoc], hrM]
    exact mul_mem hγ₀ (by simp [hM10])⟩

theorem exists_Gamma0Reps (N) : ∃ R, IsGamma0Reps N R := by
  let f (q : SLZ ⧸ Gamma0 N) := (Quotient.out q)⁻¹
  refine ⟨Set.range f, fun σ => ⟨f (QuotientGroup.mk σ⁻¹), ⟨⟨_, rfl⟩, ?_⟩, ?_⟩⟩
  · simpa [f, -Gamma0_mem] using
      QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk σ⁻¹)).symm
  · rintro _ ⟨⟨q, rfl⟩, hq⟩
    exact congrArg f (QuotientGroup.out_eq' q ▸ (QuotientGroup.eq.2 (by simpa [f] using hq)).symm)

abbrev pSH (r : SLZ) (a b d : ℕ) := projSL ((ofZ r : M2) * hermMat a b d)

set_option quotPrecheck false in
local notation "SHS" N:max R:max K:max =>
  {x : SLZ × ℕ × ℕ × ℕ // x.1 ∈ R ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2 ∧
    projSL ((ofZ x.1 : M2) * hermMat x.2.1 x.2.2.1 x.2.2.2) ∈ K}

theorem det_sigmaH (r a b d) :
    ((ofZ r : M2) * hermMat a b d).det = a * d := by
  rw [det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul, hermMat, det_fin_two_of]; ring

theorem IsHermiteN.ad_pos {a b d} (h : IsHermiteN N a b d) : 0 < (a : ℝ) * d := by
  have := h.1; have := h.2.1; positivity

theorem coe_projSL_sigmaH {r a b d} (h : IsHermiteN N a b d) :
    (pSH r a b d : M2) =
      (Real.sqrt (a * d))⁻¹ • ((ofZ r : M2) * hermMat a b d) := by
  rw [pSH, coe_projSL _ (det_sigmaH r a b d ▸ h.ad_pos), det_sigmaH]

def sigmaHMap (N) (R : Set SLZ) (K : Subgroup SLR) :
    SHS N R K → K ⧸ (Gamma0R N).subgroupOf K :=
  fun ⟨⟨r, a, b, d⟩, h⟩ => QuotientGroup.mk ⟨(pSH r a b d)⁻¹, K.inv_mem h.2.2⟩

theorem sigmaHMap_surjective [NeZero N] {R}
    (hR : IsGamma0Reps N R) {K} (hK0 : Gamma0R N ≤ K) (hKM : K ≤ MDelta N Δ) :
    Function.Surjective (sigmaHMap N R K) := by
  intro y
  obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨γ, hγ, r, hr, a, b, d, hH, c, hc, heq⟩ := exists_sigmaH Δ hR (hKM (K.inv_mem hk))
  have hcs : (c * Real.sqrt (a * d)) ^ 2 = 1 := by
    simpa only [mul_pow, Real.sq_sqrt hH.ad_pos.le, Matrix.SpecialLinearGroup.det_coe,
      det_smul, Fintype.card_fin, det_sigmaH, eq_comm, Nat.cast_ofNat] using congrArg Matrix.det heq
  have hPm : (pSH r a b d : M2) =
      (c * Real.sqrt (a * d)) • (↑(γ * k⁻¹) : M2) := by
    rw [coe_projSL_sigmaH hH, heq, smul_smul]
    congr 1; exact inv_eq_of_mul_eq_one_left (by linear_combination hcs)
  obtain ⟨γ₁, hγ₁, hPe⟩ : ∃ γ₁ ∈ Gamma0R N, pSH r a b d = γ₁ * k⁻¹ := by
    rcases sq_eq_one_iff.1 hcs with hu | hu
    · exact ⟨γ, hγ, Subtype.ext (by rw [hPm, hu, one_smul])⟩
    · exact ⟨-1 * γ, mul_mem ⟨-1, by simp, by simp⟩ hγ,
        Subtype.ext (by rw [hPm, hu]; simp)⟩
  refine ⟨⟨(r, a, b, d), hr, hH, by change pSH r a b d ∈ K; rw [hPe]; exact mul_mem (hK0 hγ₁) (K.inv_mem hk)⟩,
    QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf, hPe] using hγ₁)⟩

theorem relIndex_normG_eq_card_sigmaH {N} [NeZero N] (Δ)
    {R} (hR : IsGamma0Reps N R) :
    (Gamma0R N).relIndex (NormG (GammaDeltaR N Δ)) =
      Nat.card (SHS N R (NormG (GammaDeltaR N Δ))) := by
  refine (Nat.card_congr (Equiv.ofBijective _ ⟨?_,
    sigmaHMap_surjective hR Gamma0R_le_normG_GammaDeltaR' (normG_GammaDeltaR_le_MDelta N Δ)⟩)).symm
  rintro ⟨⟨r, a, b, d⟩, hr, hH, hPK⟩ ⟨⟨r', a', b', d'⟩, hr', hH', hPK'⟩ hxy
  have h1 : pSH r a b d * (pSH r' a' b' d')⁻¹ ∈ Gamma0R N := by
    simpa [sigmaHMap, Subgroup.mem_subgroupOf] using QuotientGroup.eq.1 hxy
  have hm := congrArg (↑· : SLR → M2)
    (inv_mul_cancel_right (pSH r a b d) (pSH r' a' b' d')).symm
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_projSL_sigmaH hH, coe_projSL_sigmaH hH'] at hm
  obtain ⟨rfl, rfl, rfl, rfl⟩ := sigmaH_unique hR hr hr' hH hH'
    (by have := hH.ad_pos; positivity) (by have := hH'.ad_pos; positivity) h1 hm
  rfl

theorem relIndex_Gamma0R_MDelta_ne_zero (N) [NeZero N] (Δ) :
    (Gamma0R N).relIndex (MDelta N Δ) ≠ 0 := by
  obtain ⟨R, hR⟩ := exists_Gamma0Reps N
  have : Finite (SLZ ⧸ Gamma0 N) := Subgroup.finite_quotient_of_finiteIndex
  refine Subgroup.index_ne_zero_iff_finite.2
    (@Finite.of_surjective _ _ ?_ _ (sigmaHMap_surjective hR (Gamma0R_le_MDelta N Δ) le_rfl))
  refine Finite.of_injective (fun ⟨⟨r, a, b, d⟩, _, ⟨ha, hd, had, hbd, _⟩, _⟩ =>
    have : a * d ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) had
    let mk (x) (h : x < N + 1 := by nlinarith) : Fin (N + 1) := ⟨x, h⟩
    ((QuotientGroup.mk r⁻¹ : _ ⧸ Gamma0 N), mk a, mk b, mk d)) ?_
  rintro ⟨⟨r, a, b, d⟩, hr, _⟩ ⟨⟨r', a', b', d'⟩, hr', _⟩ h
  simp only [Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨hrr, rfl, rfl, rfl⟩ := h
  congr 2
  exact (hR r).unique ⟨hr, by simp⟩ ⟨hr', by simpa using QuotientGroup.eq.1 hrr⟩

theorem card_BG_GammaDeltaR_eq (N) [NeZero N] (Δ) :
    Nat.card (BG (GammaDeltaR N Δ)) = Δ.index * (Gamma0R N).relIndex (NormG (GammaDeltaR N Δ)) := by
  change (GammaDeltaR N Δ).relIndex (NormG (GammaDeltaR N Δ)) = _
  rw [← Subgroup.relIndex_mul_relIndex (hHK := GammaDeltaR_le_Gamma0R)
    (hKL := Gamma0R_le_normG_GammaDeltaR'), GammaDeltaR, toR, Gamma0R,
    Subgroup.relIndex_map_map_of_injective _ _ (fun a b h => by
      ext i j; simpa using congrArg (· i j) h),
    Subgroup.relIndex, GammaDelta_subgroupOf,
    Subgroup.index_comap_of_surjective _ (fun u =>
      ⟨⟨mkSL _ _ _ _ (unit_bezout u), Gamma0_mem.2 (by simp [mkSL])⟩,
        Units.ext (by simp [unitMap, Gamma0Map, mkSL])⟩)]

theorem finite_BG_GammaDeltaR (N) [NeZero N] (Δ) :
    Finite (BG (GammaDeltaR N Δ)) := by
  refine (Nat.card_ne_zero.1 ?_).2
  rw [card_BG_GammaDeltaR_eq]
  refine mul_ne_zero Subgroup.index_ne_zero_of_finite fun h0 => relIndex_Gamma0R_MDelta_ne_zero N Δ ?_
  rw [← Subgroup.relIndex_mul_relIndex (hHK := Gamma0R_le_normG_GammaDeltaR')
    (hKL := normG_GammaDeltaR_le_MDelta N Δ), h0, zero_mul]

theorem dvd_eps_zmod [NeZero N] {m} (hm : m ∣ N) :
    m ∣ epsDelta N Δ ↔ ∀ u ∈ Δ, ((u : ZMod N).val : ZMod m) ^ 2 = 1 := by
  rcases eq_or_ne N 1 with rfl | hN
  · obtain rfl := Nat.eq_one_of_dvd_one hm
    simp [Subsingleton.elim (_ : ZMod 1) 1]
  · rw [dvd_epsDelta_iff]
    simp only [hm, true_and, ← ZMod.natCast_eq_zero_iff,
      Nat.cast_sub (one_le_sq_val hN _), sub_eq_zero, Nat.cast_pow, Nat.cast_one]

theorem dvd_eps_iff [NeZero N] {m m'} (hm : m ∣ N)
    (h : ∀ x : ℕ, (x : ZMod m) ^ 2 = 1 ↔ (x : ZMod m') = 1 ∨ (x : ZMod m') = -1) :
    m ∣ epsDelta N Δ ↔ ∀ u ∈ Δ, IsPmOneMod m' u := by
  simp only [dvd_eps_zmod hm, IsPmOneMod, ZMod.cast_eq_val, ← h]

theorem fact_ne_iff [NeZero N] (Δ) {p c} (hp : p.Prime)
    (hc : c = if p = 2 then 3 else if p = 3 then 1 else 0 := by split_ifs <;> omega) :
    (hDelta N Δ).factorization p ≠ (hPart N).factorization p ↔
      p ^ (2 * (c + 1)) ∣ N ∧ p ^ (c + 1) ∣ epsDelta N Δ := by
  have hN := NeZero.ne N
  have hε0 := epsDelta_ne_zero Δ
  have hgcd : Nat.gcd N 24 ∣ epsDelta N Δ :=
    (dvd_eps_zmod (Nat.gcd_dvd_left N 24)).2 fun u _ => by
      have hk (k) (hk : k ∣ 24) (v : (ZMod k)ˣ) : (v : ZMod k) ^ 2 = 1 := by
        have := Nat.le_of_dvd (by decide) hk; revert v; interval_cases k <;> norm_num at hk <;> decide
      rw [← ZMod.cast_eq_val, ← ZMod.castHom_apply (h := Nat.gcd_dvd_left N 24)]
      exact hk _ (Nat.gcd_dvd_right N 24) (Units.map (ZMod.castHom (Nat.gcd_dvd_left N 24) _).toMonoidHom u)
  have hle := (Nat.factorization_le_iff_dvd
    (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hN)).ne' hε0).2 hgcd p
  have heν := epsDelta_le Δ p
  unfold hPart
  rw [Nat.factorization_gcd hN (by decide), Finsupp.inf_apply,
    show (24 : ℕ) = 2 ^ 3 * 3 by decide, Nat.factorization_mul (by decide) (by decide)] at hle
  rw [factorization_hDelta, Nat.factorization_mul (by positivity) (by positivity),
    hp.pow_dvd_iff_le_factorization hN, hp.pow_dvd_iff_le_factorization hε0]
  simp only [Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow,
    Nat.prime_three.factorization, Finsupp.add_apply, Finsupp.single_apply] at hle ⊢
  split_ifs at hc hle ⊢ <;> subst_vars <;> omega

theorem hDelta_eq_hPart_iff (N) [NeZero N] (Δ) :
    hDelta N Δ = hPart N ↔
      ¬ ((∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ^ 2 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod p d) ∨
        (3 ^ 4 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod 9 d) ∨
        (2 ^ 8 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod 8 d)) := by
  have h2 := (fact_ne_iff Δ Nat.prime_two).trans <| and_congr_right fun h =>
    dvd_eps_iff ((pow_dvd_pow 2 (by decide : 4 ≤ 8)).trans h) fun x => by
      rw [← map_natCast (ZMod.castHom (by decide : 8 ∣ 16) (ZMod 8))]
      generalize (x : ZMod 16) = y; revert y; decide
  have h3 := (fact_ne_iff Δ Nat.prime_three).trans <| and_congr_right fun h =>
    dvd_eps_iff ((pow_dvd_pow 3 (by decide : 2 ≤ 4)).trans h) fun x => by
      generalize (x : ZMod 9) = y; revert y; decide
  have hp5 (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :=
    (fact_ne_iff Δ hp (c := 0)).trans <|
      and_congr_right fun h => (pow_one p).symm ▸
        dvd_eps_iff ((dvd_pow_self p two_ne_zero).trans h) fun x => by
          have := Fact.mk hp; exact sq_eq_one_iff
  refine ⟨fun h => ?_, fun hn => Nat.eq_of_factorization_eq hDelta_pos.ne' (by unfold hPart; positivity) fun p => ?_⟩
  · rintro (⟨p, hp, h5, hp2⟩ | h9 | h8)
    · exact (hp5 p hp h5).2 hp2 (h ▸ rfl)
    · exact h3.2 h9 (h ▸ rfl)
    · exact h2.2 h8 (h ▸ rfl)
  · by_cases hp : p.Prime
    · by_contra hne
      rcases (by have := hp.two_le; omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with rfl | rfl | rfl | h5
      · exact hn (Or.inr (Or.inr (h2.1 hne)))
      · exact hn (Or.inr (Or.inl (h3.1 hne)))
      · exact absurd hp (by decide)
      · exact hn (Or.inl ⟨p, hp, h5, (hp5 p hp h5).1 hne⟩)
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

end

end NormalizerLean
