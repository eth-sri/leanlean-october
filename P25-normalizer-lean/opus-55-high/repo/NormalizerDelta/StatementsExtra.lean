module

public import NormalizerLean.Defs

@[expose] public section

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {N : ℕ} [NeZero N] {Δ : Subgroup (ZMod N)ˣ}

local notation "M2" => Matrix (Fin 2) (Fin 2) ℝ

local notation "SR" => SL(2, ℝ)
local notation "SZ" => SL(2, ℤ)

macro "fc" : tactic => `(tactic| (ext i j; fin_cases i <;> fin_cases j))

theorem coe_ofZ (γ : SZ) :
    (ofZ γ : M2) = !![(γ 0 0 : ℝ), γ 0 1; γ 1 0, γ 1 1] := by
  fc <;> rfl

theorem exists_entries_of_mem_Gamma0R {N : ℕ} {g : SR} (hg : g ∈ Gamma0R N) :
    ∃ a b c d : ℤ, a * d - b * c = 1 ∧ (N : ℤ) ∣ c ∧
      (g : M2) = !![(a : ℝ), b; c, d] := by
  obtain ⟨A, hA, rfl⟩ := hg
  exact ⟨_, _, _, _, (det_fin_two _).symm.trans A.2,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (CongruenceSubgroup.Gamma0_mem.1 hA), coe_ofZ A⟩

theorem coe_projSL (A : M2) (hA : 0 < A.det) :
    ((projSL A : SR) : M2) = (Real.sqrt A.det)⁻¹ • A := by
  simp [projSL, hA]

def vz (p : ℕ) (x : ℤ) : ℕ := x.natAbs.factorization p

theorem vz_mul {p : ℕ} {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) : vz p (x * y) = vz p x + vz p y := by
  simp [vz, Int.natAbs_mul, Nat.factorization_mul (Int.natAbs_ne_zero.2 hx)
    (Int.natAbs_ne_zero.2 hy)]

theorem vz_natCast (p n : ℕ) : vz p n = n.factorization p := by simp [vz]

theorem pow_dvd_iff_le_vz {p : ℕ} (hp : p.Prime) {x : ℤ} (hx : x ≠ 0) (m : ℕ) :
    (p : ℤ) ^ m ∣ x ↔ m ≤ vz p x := by
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_pow, Int.natAbs_natCast,
    hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.2 hx)]
  rfl

theorem vz_le_of_dvd (p : ℕ) {x y : ℤ} (hy : y ≠ 0) (hxy : x ∣ y) : vz p x ≤ vz p y :=
  (Nat.factorization_le_iff_dvd (by simpa using ne_zero_of_dvd_ne_zero hy hxy) (by simpa)).2 (Int.natAbs_dvd_natAbs.2 hxy) p

def vv (B p : ℕ) (x : ℤ) : ℕ := if x = 0 then B else vz p x

theorem vv_of_ne {B p : ℕ} {x : ℤ} (hx : x ≠ 0) : vv B p x = vz p x := if_neg hx

theorem factorization_24 (p : ℕ) :
    (24 : ℕ).factorization p = if p = 2 then 3 else if p = 3 then 1 else 0 := by
  rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.prime_two.factorization_pow, Nat.prime_three.factorization]
  aesop

theorem GammaDelta_le_Gamma0 : GammaDelta N Δ ≤ CongruenceSubgroup.Gamma0 N := fun _ h => h.1

theorem GammaDeltaR_le_Gamma0R : GammaDeltaR N Δ ≤ Gamma0R N :=
  Subgroup.map_mono GammaDelta_le_Gamma0

def mkSL (a b c d : ℤ) (h : a * d - b * c = 1) : SZ := ⟨!![a, b; c, d], by
  rw [det_fin_two_of]; exact h⟩

theorem coe_ofZ_mkSL {a b c d : ℤ} (h : a * d - b * c = 1) :
    (ofZ (mkSL a b c d h) : M2) = !![(a : ℝ), b; c, d] := by
  rw [coe_ofZ]; rfl

theorem dvd_epsDelta_iff {m : ℕ} :
    m ∣ epsDelta N Δ ↔ m ∣ N ∧ ∀ u ∈ Δ, m ∣ (u : ZMod N).val ^ 2 - 1 := by
  simp [epsDelta, Nat.dvd_gcd_iff, Finset.dvd_gcd_iff]

theorem epsDelta_pos : 0 < epsDelta N Δ :=
  Nat.pos_of_dvd_of_pos (dvd_epsDelta_iff.1 dvd_rfl).1 (NeZero.pos N)

theorem factorization_hDelta (p : ℕ) :
    (hDelta N Δ).factorization p =
      min ((epsDelta N Δ).factorization p) (N.factorization p / 2) := by
  rw [hDelta, Nat.factorization_prod fun q hq => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero,
    Finset.sum_apply', Finset.sum_congr rfl fun q hq => by
    rw [(Nat.prime_of_mem_primeFactors hq).factorization_pow, Finsupp.single_apply]]
  simp [← Nat.support_factorization]
  aesop

variable (Δ) in
theorem hDelta_ne_zero : hDelta N Δ ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun q hq => pow_ne_zero _ (Nat.pos_of_mem_primeFactors hq).ne'

variable (N Δ) in
theorem hDelta_sq_dvd' : hDelta N Δ ^ 2 ∣ N := by
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 (hDelta_ne_zero Δ)) (NeZero.ne N)]
  intro p
  simp [factorization_hDelta]
  omega

theorem le_vv2' {X K : ℤ} (B p : ℕ) (x y : ℤ) (hK : K ≠ 0) (h : X ∣ K * (x * y)) :
    min (vz p X) B ≤ vz p K + vv B p x + vv B p y := by
  by_cases hx : x = 0; · simp [vv, hx]; omega
  by_cases hy : y = 0; · simp [vv, hy]
  have := vz_le_of_dvd p (mul_ne_zero hK (mul_ne_zero hx hy)) h
  rw [vz_mul hK (mul_ne_zero hx hy), vz_mul hx hy] at this
  rw [vv_of_ne hx, vv_of_ne hy]; omega

theorem pow_dvd_of_le_vv {B p : ℕ} (hp : p.Prime) {m : ℕ} {x y : ℤ} (h : m ≤ vv B p x + vv B p y) :
    (p : ℤ) ^ m ∣ x * y := by
  by_cases hx : x = 0; · simp_all
  by_cases hy : y = 0; · simp_all
  rw [pow_dvd_iff_le_vz hp (mul_ne_zero hx hy), vz_mul hx hy]; rwa [vv_of_ne hx, vv_of_ne hy] at h

theorem dvd_of_vv {m x : ℤ} (hm : m ≠ 0) (h : ∀ p : ℕ, p.Prime → ∃ B, vz p m ≤ vv B p x) : m ∣ x := by
  by_cases hx : x = 0; · simp_all
  exact Int.natAbs_dvd_natAbs.1 ((Nat.factorization_prime_le_iff_dvd (by simpa) (by simpa)).1
    fun p hp => by obtain ⟨B, h⟩ := h p hp; rwa [vv_of_ne hx] at h)

theorem dvd_sq_sub_one_iff {m x : ℕ} (hx : 1 ≤ x) : m ∣ x ^ 2 - 1 ↔ (x : ZMod m) ^ 2 = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hx), sub_eq_zero]; push_cast; rfl

theorem sq_of_dvd_24 {k : ℕ} (hk : k ∣ 24) : ∀ x : (ZMod k)ˣ, (x : ZMod k) ^ 2 = 1 := by
  have := Nat.le_of_dvd (by norm_num) hk
  interval_cases k <;> simp_all <;> decide

def unitMap (N : ℕ) : CongruenceSubgroup.Gamma0 N →* (ZMod N)ˣ :=
  (CongruenceSubgroup.Gamma0Map N).toHomUnits

theorem unitMap_surjective : Function.Surjective (unitMap N) := by
  intro u
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime u)
  exact ⟨⟨mkSL x (-y) N (u : ZMod N).val (by linear_combination hxy), CongruenceSubgroup.Gamma0_mem.2 (by simp [mkSL])⟩,
    Units.ext (by simp [mkSL, unitMap, CongruenceSubgroup.Gamma0Map])⟩

theorem GammaDelta_subgroupOf (Δ : Subgroup (ZMod N)ˣ) :
    (GammaDelta N Δ).subgroupOf (CongruenceSubgroup.Gamma0 N) = Δ.comap (unitMap N) := by
  ext γ
  exact ⟨fun ⟨_, u, hu, hud⟩ => show unitMap N γ ∈ Δ from (Units.ext hud : u = unitMap N γ) ▸ hu, fun h => ⟨γ.2, _, h, rfl⟩⟩

theorem Gamma0R_le_normG_GammaDeltaR' :
    Gamma0R N ≤ NormG (GammaDeltaR N Δ) :=
  (Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer GammaDelta_le_Gamma0).1
    (GammaDelta_subgroupOf Δ ▸ inferInstance))).trans (Subgroup.le_normalizer_map _)

abbrev Dm (M : ℕ) : SR := projSL !![(M : ℝ), 0; 0, 1]

def alSub (n : ℕ) [NeZero n] : Subgroup SR where
  carrier := {g | ∃ Q : ℕ, Q ∣ n ∧ IsAtkinLehner n Q g}
  one_mem' := ⟨1, one_dvd n, 1, 0, 0, 1, by simp, by fc <;> simp⟩
  mul_mem' := by
    rintro g g' ⟨Q, hQ, hg⟩ ⟨Q', hQ', hg'⟩
    obtain ⟨G, q₁, q₂, -, hcop, rfl, rfl⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_left Q' (Nat.pos_of_dvd_of_pos hQ (NeZero.pos n)))
    obtain ⟨L, hL⟩ := Nat.lcm_dvd hQ hQ'
    rw [Nat.lcm_mul_right, hcop.lcm_eq_mul] at hL
    refine ⟨q₁ * q₂, ⟨G * L, by simp_all; ring⟩, ?_⟩
    have h0 := NeZero.ne n
    subst hL
    simp_all
    obtain ⟨x₁, y₁, z₁, w₁, hd₁, hg₁⟩ := hg
    obtain ⟨x₂, y₂, z₂, w₂, hd₂, hg₂⟩ := hg'
    simp_all
    have r₁ : (G : ℤ) * q₁ * x₁ * w₁ - q₂ * L * y₁ * z₁ = 1 := mul_left_cancel₀ (by simp [h0] : (q₁ * G : ℤ) ≠ 0) (by linear_combination hd₁)
    have r₂ : (G : ℤ) * q₂ * x₂ * w₂ - q₁ * L * y₂ * z₂ = 1 := mul_left_cancel₀ (by simp [h0] : (q₂ * G : ℤ) ≠ 0) (by linear_combination hd₂)
    refine ⟨G * x₁ * x₂ + L * y₁ * z₂, q₁ * x₁ * y₂ + q₂ * y₁ * w₂, q₂ * z₁ * x₂ + q₁ * w₁ * z₂,
      L * z₁ * y₂ + G * w₁ * w₂, ?_, ?_⟩
    · grind
    · fc <;> simp_all <;> ring_nf <;> simp <;> field_simp [h0.1.2] <;> ring
  inv_mem' := by
    rintro g ⟨Q, hQ, x, y, z, w, hdet, hgm⟩
    refine ⟨Q, hQ, w, -y, -z, x, by linear_combination hdet, ?_⟩
    simp_all


instance : NeZero (nDelta N Δ) :=
  ⟨Nat.div_ne_zero_iff.2 ⟨pow_ne_zero 2 (hDelta_ne_zero Δ), Nat.le_of_dvd (NeZero.pos N) (hDelta_sq_dvd' N Δ)⟩⟩

theorem mem_MDelta_iff {g : SR} :
    g ∈ MDelta N Δ ↔ IsNewmanFormH N (hDelta N Δ) g := by
  have hh := Nat.pos_of_ne_zero (hDelta_ne_zero Δ)
  obtain ⟨n, hn⟩ := hDelta_sq_dvd' N Δ
  have hn0 : 0 < N / hDelta N Δ ^ 2 := NeZero.pos (nDelta N Δ)
  erw [MDelta, Subgroup.mem_map_equiv, Gamma0Plus, Subgroup.closure_eq (alSub _)]
  simp [alSub, IsNewmanFormH, nDelta, IsAtkinLehner, coe_projSL, hh, Matrix.mul_apply, vecMul, dotProduct, ← Matrix.ext_iff]
  generalize hDelta N Δ = h at *
  simp_all
  ring_nf
  simp
  constructor
  · rintro ⟨Q, hQ, x, y, z, w, hdet, ⟨h1, h2⟩, h3, h4⟩
    refine ⟨x, y, z, w, Q, Nat.pos_of_dvd_of_pos hQ hn0, hQ, ?_, Or.inl ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩ <;> field_simp at * <;> linarith
  · rintro ⟨a, b, c, d, e, he0, he, hdet, (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩)⟩
    · refine ⟨e, he, a, b, c, d, ?_, ⟨?_, ?_⟩, ?_, ?_⟩ <;> field_simp at * <;> linarith
    · refine ⟨e, he, -a, -b, -c, -d, ?_, ⟨?_, ?_⟩, ?_, ?_⟩ <;> field_simp at * <;> push_cast <;> linarith

theorem coe_MDelta :
    (MDelta N Δ : Set SR) = {g | IsNewmanFormH N (hDelta N Δ) g} :=
  Set.ext fun _ => mem_MDelta_iff

theorem normG_GammaDeltaR_le_MDelta :
    NormG (GammaDeltaR N Δ) ≤ MDelta N Δ := by
  intro g hg
  rw [mem_MDelta_iff]
  have hN := NeZero.ne N
  have hη := hDelta_ne_zero Δ
  have hk := factorization_hDelta (Δ := Δ)
  obtain ⟨n, hn⟩ := hDelta_sq_dvd' N Δ
  generalize hDelta N Δ = η at *
  have hc := fun (x y w t : ℤ) (h : x * t - y * (N * w) = 1) {u : (ZMod N)ˣ}
    (hu : u ∈ Δ) (hut : (u : ZMod N) = t) => GammaDeltaR_le_Gamma0R
      ((Subgroup.mem_normalizer_iff.1 hg _).1 (Subgroup.mem_map_of_mem _ (show mkSL x y (N * w) t h ∈ GammaDelta N Δ from
        ⟨CongruenceSubgroup.Gamma0_mem.2 (by simp [mkSL]),
          u, hu, by simpa [mkSL] using hut⟩)))
  have hT := hc 1 1 0 1 (by norm_num) (one_mem _) (by simp)
  have hU := hc 1 0 1 1 (by norm_num) (one_mem _) (by simp)
  have hTU := hc (1 + N) 1 1 1 (by ring) (one_mem _) (by simp)
  obtain ⟨κ, f, hprim, hg'⟩ : ∃ κ : ℝ, ∃ f : Fin 4 → ℤ, (∀ p : ℕ, p.Prime → ∃ i, ¬ (p : ℤ) ∣ f i) ∧
      (g : M2) = κ • !![(f 0 : ℝ), f 1 / η; η * f 2, f 3] := by
    obtain ⟨κ, M, hM⟩ : ∃ κ : ℝ, ∃ M : Fin 4 → ℤ,
        (g : M2) = κ • !![(M 0 : ℝ), M 1; M 2, M 3] := by
      have hdet := g.2; rw [det_fin_two] at hdet
      obtain ⟨A1, B1, C1, D1, -, -, h1⟩ := exists_entries_of_mem_Gamma0R hT
      obtain ⟨A2, B2, C2, D2, -, -, h2⟩ := exists_entries_of_mem_Gamma0R hU
      obtain ⟨A3, B3, C3, D3, -, -, h3⟩ := exists_entries_of_mem_Gamma0R hTU
      simp [← Matrix.ext_iff, coe_ofZ_mkSL, -SpecialLinearGroup.map_apply_coe, adjugate_fin_two, Matrix.mul_apply] at h1 h2 h3
      by_cases ha : g 0 0 = 0
      · rw [ha] at hdet
        have hc : g 1 0 ≠ 0 := by rintro h; simp_all
        refine ⟨(N * g 1 0)⁻¹, ![0, -N, -N * C1, C3 - C2 - C1], ?_⟩
        fc <;> simp [ha] <;> field_simp <;> linarith
      · refine ⟨(N * g 0 0)⁻¹, ![N * B1, B1 + B2 - B3, N * (1 - A1), A3 - A2 + 1 - A1], ?_⟩
        fc <;> simp <;> field_simp <;> linarith
    set v : Fin 4 → ℤ := ![η * M 0, η ^ 2 * M 1, M 2, η * M 3]
    obtain ⟨f, hf, h1⟩ := Finset.extract_gcd v Finset.univ_nonempty
    refine ⟨κ * (Finset.univ.gcd v / η), f, fun p hp => ?_, ?_⟩
    · by_contra! h
      exact hp.not_dvd_one (by exact_mod_cast h1 ▸ Finset.dvd_gcd fun i _ => h i)
    have e := fun i => congrArg (Int.cast : ℤ → ℝ) (hf i (Finset.mem_univ i))
    simp [v, Fin.forall_fin_succ] at e
    rw [hM, ← smul_smul]; congr 1
    fc <;> simp <;> field_simp <;> linarith
  have hE : κ ^ 2 * ((f 0 * f 3 - f 1 * f 2 : ℤ) : ℝ) = 1 := by
    have := g.2; simp_all; simp_all; field_simp at this; push_cast; linear_combination this
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le (a := f 0 * f 3 - f 1 * f 2) (by rify; simp_all; nlinarith)
  rw [he] at hE
  have key : ∀ {x y z t : ℤ} {h : x * t - y * z = 1}, g * ofZ (mkSL x y z t h) * g⁻¹ ∈ Gamma0R N →
      (e : ℤ) * η ^ 2 ∣ f 0 * f 1 * η * (t - x) - f 1 ^ 2 * z + f 0 ^ 2 * y * η ^ 2 ∧
      (e : ℤ) * N ∣ η * f 2 * f 3 * (x - t) + f 3 ^ 2 * z - η ^ 2 * f 2 ^ 2 * y := by
    intro x y z t hx hm
    obtain ⟨A, B, c, D, h0, ⟨C, rfl⟩, h⟩ := exists_entries_of_mem_Gamma0R hm
    simp [hg', coe_ofZ_mkSL hx] at h
    ring_nf at h
    have := right_ne_zero_of_mul_eq_one hE
    rw [eq_inv_of_mul_eq_one_left hE] at h
    field_simp at h
    refine ⟨⟨B, ?_⟩, ⟨C, ?_⟩⟩ <;> rify
    · linear_combination h.1.2
    · linear_combination h.2.1
  obtain ⟨T1, T2⟩ := key hT
  obtain ⟨U1, U2⟩ := key hU
  obtain ⟨V1, V2⟩ := key hTU
  have hKf : ∀ p : ℕ, p.Prime → ∃ K : ℤ, K ≠ 0 ∧ vz p K ≤ (epsDelta N Δ).factorization p ∧
      (e : ℤ) * η ^ 2 ∣ K * η * (f 0 * f 1) ∧ (e : ℤ) * N ∣ K * η * (f 2 * f 3) := by
    intro p hp
    by_cases hj : N.factorization p ≤ (epsDelta N Δ).factorization p
    · exact ⟨N, Nat.cast_ne_zero.2 hN, by rwa [vz_natCast], by convert (T1.add U1).sub V1 using 1; ring,
        by convert (V2.sub U2).sub T2 using 1; ring⟩
    obtain ⟨u, hu, hnd⟩ : ∃ u ∈ Δ, ¬ p ^ ((epsDelta N Δ).factorization p + 1) ∣ (u : ZMod N).val ^ 2 - 1 := by
      by_contra! hcon
      have := (hp.pow_dvd_iff_le_factorization epsDelta_pos.ne').1
        (dvd_epsDelta_iff.2 ⟨(hp.pow_dvd_iff_le_factorization hN).2 (by omega), hcon⟩)
      omega
    set v := (u : ZMod N).val
    have h1 : 1 ≤ v ^ 2 := Nat.one_le_iff_ne_zero.2 fun h => hnd (by simp [h])
    have hK : v ^ 2 - 1 ≠ 0 := fun h => hnd (by simp [h])
    obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime u)
    obtain ⟨P1, P2⟩ := key (hc x (-y) 1 v (by linear_combination hxy) hu (by simp [v]))
    refine ⟨(v ^ 2 - 1 : ℕ), Nat.cast_ne_zero.2 hK, by
      rw [vz_natCast]; exact not_lt.1 fun h' => hnd ((hp.pow_dvd_iff_le_factorization hK).2 h'), ?_, ?_⟩
    · convert ((((P1.sub U1).sub (T1.mul_left (-y))).mul_left v).add (((T1.add U1).sub V1).mul_left (-y))) using 1
      rw [Nat.cast_sub h1]; push_cast; linear_combination (η * f 0 * f 1 : ℤ) * hxy
    · convert ((((P2.sub U2).add (T2.mul_left y)).mul_left (-v)).add (((V2.sub U2).sub T2).mul_left (-y))) using 1
      rw [Nat.cast_sub h1]; push_cast; linear_combination (η * f 2 * f 3 : ℤ) * hxy
  have hn0 : n ≠ 0 := by rintro rfl; simp_all
  have he0 : e ≠ 0 := by rintro rfl; simp_all
  have hloc : ∀ p : ℕ, p.Prime → ∃ B, e.factorization p ≤ n.factorization p ∧
      vz p n ≤ vv B p (f 2) ∧ vz p e ≤ vv B p (f 0) ∧ vz p e ≤ vv B p (f 3) := by
    intro p hp
    obtain ⟨K, hK, hKj, P1, P2⟩ := hKf p hp
    use e.factorization p + N.factorization p
    set B := e.factorization p + N.factorization p
    have hη2 : (η : ℤ) ^ 2 ≠ 0 := by positivity
    have c2 := le_vv2' B p (f 0) (f 0) hη2 (by convert T1 using 1; ring)
    have c3 := le_vv2' B p (f 2) (f 2) hη2 (by convert T2.neg_right using 1; ring)
    have c6 := le_vv2' B p (f 1) (f 1) (K := N) (by simpa) (by convert U1.neg_right using 1; ring)
    have c7 := le_vv2' B p (f 3) (f 3) (K := N) (by simpa) (by convert U2 using 1; ring)
    have c10 := le_vv2' B p _ _ (mul_ne_zero hK (by simpa)) P1
    have c11 := le_vv2' B p _ _ (mul_ne_zero hK (by simpa)) P2
    have u1 : min (vv B p (f 0) + vv B p (f 3)) (vv B p (f 1) + vv B p (f 2)) ≤ vz p e := by
      rw [← not_lt, lt_min_iff]
      rintro ⟨h1, h2⟩
      have := (pow_dvd_iff_le_vz hp (by simpa) _).1 (he ▸ dvd_sub (pow_dvd_of_le_vv hp h1) (pow_dvd_of_le_vv hp h2))
      omega
    obtain ⟨i, hi⟩ := hprim p hp
    have h0 : vv B p (f i) = 0 := by
      rw [vv_of_ne (by rintro h; simp_all)]; exact Nat.factorization_eq_zero_of_not_dvd (by simpa [Int.natCast_dvd] using hi)
    have hn' := congrArg (·.factorization p) hn
    simp [B, vz, Int.natAbs_mul, he0, hη, hN, hK, hn0, hk] at c2 c3 c6 c7 c10 c11 u1 hn' hKj h0 ⊢
    fin_cases i <;> simp at h0 <;> omega
  obtain ⟨m, hm⟩ := (Nat.factorization_prime_le_iff_dvd he0 hn0).1 fun p hp => (hloc p hp).choose_spec.1
  obtain ⟨c, hc⟩ := dvd_of_vv (by simpa) fun p hp => (hloc p hp).imp fun _ h => h.2.1
  obtain ⟨a, ha⟩ := dvd_of_vv (by simpa) fun p hp => (hloc p hp).imp fun _ h => h.2.2.1
  obtain ⟨d, hd⟩ := dvd_of_vv (by simpa) fun p hp => (hloc p hp).imp fun _ h => h.2.2.2
  push_cast at hE
  rw [IsNewmanFormH, hn, Nat.mul_div_cancel_left _ (by positivity)]
  refine ⟨a, f 1, c, d, e, by omega, ⟨m, hm⟩, by rw [ha, hd, hc] at he; linear_combination he, κ * Real.sqrt e,
    mul_self_eq_one_iff.1 (by nlinarith [Real.mul_self_sqrt (Nat.cast_nonneg e)]), hg'.trans ?_⟩
  fc <;> simp [ha, hc, hd] <;> field_simp <;> simp

theorem Gamma0R_le_MDelta : Gamma0R N ≤ MDelta N Δ :=
  Gamma0R_le_normG_GammaDeltaR'.trans normG_GammaDeltaR_le_MDelta

theorem exists_sigmaH {R : Set SZ}
    (hR : IsGamma0Reps N R) {g : SR} (hg : g ∈ MDelta N Δ) :
    ∃ γ ∈ Gamma0R N, ∃ r ∈ R, ∃ a b d : ℕ, IsHermiteN N a b d ∧ ∃ c : ℝ, c ≠ 0 ∧
      ((γ * g : SR) : M2) =
        c • ((ofZ r : M2) * hermMat a b d) := by
  obtain ⟨a, b, c, d, e, he0, ⟨m, hm⟩, hdet, ε, hε, hgm⟩ := mem_MDelta_iff.1 hg
  have hh := hDelta_ne_zero Δ
  have hn := (Nat.mul_div_cancel' (hDelta_sq_dvd' N Δ)).symm
  generalize hDelta N Δ = h at *
  generalize N / h ^ 2 = n at *
  obtain ⟨G, p, q, hG, hpq, hp, hq⟩ := Int.exists_gcd_one' (m := a * e * h) (n := N * c) (Int.gcd_pos_iff.2 (by
    by_contra! H; simp [he0.ne', hh, NeZero.ne N] at H; simp_all; omega))
  obtain ⟨A, B, hpq⟩ := Int.isCoprime_iff_gcd_eq_one.2 hpq
  have hGD : (G : ℤ) * (p * (d * e * h) - q * b) = h ^ 2 * e := by
    simp_all; grind
  have hD0 : 0 < p * (d * e * h) - q * b := pos_of_mul_pos_right (by rw [hGD]; positivity) (by positivity)
  lift p * (d * e * h) - q * b to ℕ using hD0.le with D hD
  generalize hX : A * b + B * (d * e * h) = X
  have hdiv := Int.emod_add_mul_ediv X D
  have hrD := Int.emod_lt_of_pos X hD0
  generalize X / D = k at hdiv
  lift X % D to ℕ using Int.emod_nonneg X hD0.ne' with r
  generalize ht : Nat.gcd (Nat.gcd G r) D = t
  obtain ⟨A', rfl⟩ : t ∣ G := ht ▸ (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  obtain ⟨B', rfl⟩ : t ∣ r := ht ▸ (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  obtain ⟨D', rfl⟩ : t ∣ D := ht ▸ Nat.gcd_dvd_right _ _
  have H : t * A' * (t * D') = h ^ 2 * e := by exact_mod_cast hGD
  have H0 : 0 < t * A' * (t * D') := H ▸ by positivity
  simp at H0
  set σ := mkSL p (p * k - B) q (q * k + A) (by linear_combination hpq)
  obtain ⟨r0, ⟨hr0, hσr⟩, -⟩ := hR σ
  refine ⟨_, ⟨_, inv_mem hσr, rfl⟩, r0, hr0, A', B', D', ⟨H0.1.2, H0.2.2, ⟨t ^ 2 * m, by
    rw [hn, hm, ← mul_assoc, ← H]; ring⟩, Nat.lt_of_mul_lt_mul_left (by exact_mod_cast hrD),
    Nat.eq_of_mul_eq_mul_left H0.1.1 (by rw [← Nat.gcd_mul_left, ← Nat.gcd_mul_left, ht, mul_one])⟩,
    ε / (√e * h) * t, by rcases hε with rfl | rfl <;> simp [H0.1.1.ne', he0.ne', hh], ?_⟩
  have key : (g : M2) = (ε / (√e * h) * t) • ((ofZ σ : M2) * hermMat A' B' D') := by
    rw [hgm, coe_ofZ_mkSL, hermMat]; fc <;> simp <;> field_simp <;> simp only [mul_assoc] <;> congr 1 <;> norm_cast <;> push_cast at *
    · linear_combination hp
    · linear_combination (-b) * hpq - p * hdiv + B * hD + p * hX
    · linear_combination hq
    · linear_combination (-(d * e * h)) * hpq - q * hdiv - A * hD + q * hX
  rw [Matrix.SpecialLinearGroup.coe_mul, key, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul]; simp

theorem bezout3 {x y z : ℕ} (h : Nat.gcd (Nat.gcd x y) z = 1) :
    ∃ u v w : ℤ, u * x + v * y + w * z = 1 := by
  obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.2 h
  rw [Nat.gcd_eq_gcd_ab] at huw
  exact ⟨u * Nat.gcdA x y, u * Nat.gcdB x y, w, by linear_combination huw⟩

theorem sigmaH_unique {R : Set SZ} (hR : IsGamma0Reps N R)
    {r r' : SZ} (hr : r ∈ R) (hr' : r' ∈ R) {a b d a' b' d' : ℕ}
    (hH : IsHermiteN N a b d) (hH' : IsHermiteN N a' b' d') {c c' : ℝ} (hc : c ≠ 0) (hc' : c' ≠ 0)
    {γ : SR} (hγ : γ ∈ Gamma0R N)
    (h : c • ((ofZ r : M2) * hermMat a b d) =
      (γ : M2) * (c' • ((ofZ r' : M2) * hermMat a' b' d'))) :
    r = r' ∧ a = a' ∧ b = b' ∧ d = d' := by
  obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
  obtain ⟨ha, hd, -, hbd, hprim⟩ := hH
  obtain ⟨ha', hd', -, hbd', hprim'⟩ := hH'
  have key := congrArg ((ofZ (r'⁻¹ * γ₀⁻¹) : M2) * ·) h
  simp only [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul] at key
  generalize hM : r'⁻¹ * γ₀⁻¹ * r = M at key
  rw [coe_ofZ] at key
  simp [hermMat, hc, ha.ne'] at key
  obtain ⟨⟨e00, e01⟩, e10, e11⟩ := key
  have hdet := M.2
  rw [det_fin_two, e10, mul_zero, sub_zero] at hdet
  have hs := Int.eq_of_mul_eq_one hdet
  simp [e10, ← hs] at e11 hdet
  have hdR : (M 0 0 * M 0 0 : ℝ) = 1 := by exact_mod_cast hdet
  have Z1 : (a : ℤ) * b' = (b + M 0 0 * M 0 1 * d) * a' := by
    rify; grind
  have Z2 : (a : ℤ) * d' = d * a' := by
    rify; grind
  generalize hk : M 0 0 * M 0 1 = k at Z1
  obtain ⟨u, v, w, huvw⟩ := bezout3 hprim
  obtain ⟨u', v', w', huvw'⟩ := bezout3 hprim'
  obtain rfl : a = a' := Nat.dvd_antisymm (Int.natCast_dvd_natCast.1 ⟨u * a' + v * (b' - k * d') + w * d', by grind⟩) (Int.natCast_dvd_natCast.1 ⟨u' * a + v' * (b + k * d) + w' * d, by grind⟩)
  obtain rfl := Nat.eq_of_mul_eq_mul_left ha (by grind : a * d = a * d')
  have hb : (b' : ℤ) = b + k * d := mul_left_cancel₀ (by omega : (a : ℤ) ≠ 0) (by linear_combination Z1)
  obtain rfl : k = 0 := by nlinarith
  obtain rfl : b = b' := by omega
  have h01 : M 0 1 = 0 := (mul_eq_zero.1 hk).resolve_left (by grind)
  have hcomm : r' * M = M * r' := by
    fc <;> simp [Matrix.mul_apply] <;> grind
  refine ⟨(hR r).unique ⟨hr, by simp⟩ ⟨hr', ?_⟩, rfl, rfl, rfl⟩
  rw [show r = γ₀ * (r' * M) by rw [← hM]; group, hcomm, mul_assoc]
  exact mul_mem hγ₀ (CongruenceSubgroup.Gamma0_mem.2 (by simp [e10]))

theorem gamma0Reps (N : ℕ) : IsGamma0Reps N (Set.range fun q : SZ ⧸ CongruenceSubgroup.Gamma0 N => q.out⁻¹) := by
  refine fun σ => ⟨_, ⟨⟨QuotientGroup.mk σ⁻¹, rfl⟩, ?_⟩, ?_⟩
  · simpa using QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk σ⁻¹ : SZ ⧸ CongruenceSubgroup.Gamma0 N)).symm
  · rintro _ ⟨⟨q, rfl⟩, hq⟩
    obtain rfl : (QuotientGroup.mk σ⁻¹ : SZ ⧸ _) = q := by
      rw [← QuotientGroup.out_eq' q, QuotientGroup.eq]; simp_all
    rfl

theorem exists_Gamma0Reps (N : ℕ) : ∃ R : Set SZ, IsGamma0Reps N R := ⟨_, gamma0Reps N⟩

abbrev SigmaHSet (N : ℕ) (R : Set SZ) (K : Subgroup SR) : Type :=
  {x : SZ × ℕ × ℕ × ℕ // x.1 ∈ R ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2 ∧
    projSL ((ofZ x.1 : M2) * hermMat x.2.1 x.2.2.1 x.2.2.2) ∈ K}

theorem det_sigmaH (r : SZ) (a b d : ℕ) :
    ((ofZ r : M2) * hermMat a b d).det = a * d := by
  rw [det_mul, Matrix.SpecialLinearGroup.det_coe, hermMat, det_fin_two_of]; ring

theorem IsHermiteN.pos {n a b d : ℕ} (h : IsHermiteN n a b d) : 0 < (a : ℝ) * d := by
  have := h.1; have := h.2.1; positivity

theorem coe_projSL_sigmaH {r : SZ} {n a b d : ℕ} (hH : IsHermiteN n a b d) :
    ((projSL ((ofZ r : M2) * hermMat a b d) : SR) : M2) =
      (Real.sqrt (a * d))⁻¹ • ((ofZ r : M2) * hermMat a b d) := by
  rw [coe_projSL _ (det_sigmaH r a b d ▸ hH.pos), det_sigmaH]

theorem sigmaHMap_surjective {R : Set SZ}
    (hR : IsGamma0Reps N R) {K : Subgroup SR} (hK0 : Gamma0R N ≤ K) (hKM : K ≤ MDelta N Δ) :
    Function.Surjective fun x : SigmaHSet N R K => (QuotientGroup.mk ⟨(projSL ((ofZ x.1.1 : M2) *
      hermMat x.1.2.1 x.1.2.2.1 x.1.2.2.2))⁻¹, K.inv_mem x.2.2.2⟩ : K ⧸ (Gamma0R N).subgroupOf K) := by
  rintro ⟨k, hk⟩
  obtain ⟨γ, hγ, r, hr, a, b, d, hH, c, hc, heq⟩ := exists_sigmaH hR (hKM (K.inv_mem hk))
  have hdet := congrArg Matrix.det heq
  rw [Matrix.SpecialLinearGroup.det_coe, det_smul, Fintype.card_fin, det_sigmaH] at hdet
  suffices H : ∃ s ∈ Gamma0R N, projSL ((ofZ r : M2) * hermMat a b d) = s * (γ * k⁻¹) by
    obtain ⟨s, hs, hP⟩ := H
    refine ⟨⟨(r, a, b, d), hr, hH, hP ▸ mul_mem (hK0 hs) (mul_mem (hK0 hγ) (K.inv_mem hk))⟩, QuotientGroup.eq.2 ?_⟩
    simp only [hP]; simpa [Subgroup.mem_subgroupOf, mul_assoc] using mul_mem hs hγ
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (show c ^ 2 = ((√(a * d))⁻¹) ^ 2 by
    simp [hH.pos.le]; grind) with rfl | rfl
  · exact ⟨1, one_mem _, Subtype.ext (by rw [coe_projSL_sigmaH hH, one_mul, heq])⟩
  · exact ⟨-1, ⟨-1, by simp, by simp⟩, Subtype.ext (by rw [coe_projSL_sigmaH hH, neg_one_mul, Matrix.SpecialLinearGroup.coe_neg, heq]; simp)⟩

theorem relIndex_normG_eq_card_sigmaH
    {R : Set SZ} (hR : IsGamma0Reps N R) :
    (Gamma0R N).relIndex (NormG (GammaDeltaR N Δ)) =
      Nat.card {x : SZ × ℕ × ℕ × ℕ // x.1 ∈ R ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2 ∧
        projSL ((ofZ x.1 : M2) * hermMat x.2.1 x.2.2.1 x.2.2.2) ∈
          NormG (GammaDeltaR N Δ)} :=
  (Nat.card_congr (Equiv.ofBijective _ ⟨by
    rintro ⟨⟨r, a, b, d⟩, hr, hH, _⟩ ⟨⟨r', a', b', d'⟩, hr', hH', _⟩ hxy
    have h1 := QuotientGroup.eq.1 hxy
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at h1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := sigmaH_unique hR hr hr' hH hH' (inv_ne_zero (Real.sqrt_ne_zero'.2 hH.pos))
      (inv_ne_zero (Real.sqrt_ne_zero'.2 hH'.pos)) h1 (by
        rw [← coe_projSL_sigmaH hH, ← coe_projSL_sigmaH hH',
          ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right])
    rfl, sigmaHMap_surjective hR Gamma0R_le_normG_GammaDeltaR' normG_GammaDeltaR_le_MDelta⟩)).symm

theorem relIndex_Gamma0R_MDelta_ne_zero :
    (Gamma0R N).relIndex (MDelta N Δ) ≠ 0 := by
  refine Subgroup.index_ne_zero_iff_finite.2 (@Finite.of_surjective (SigmaHSet N _ _) _ ?_ _ (sigmaHMap_surjective (gamma0Reps N) Gamma0R_le_MDelta le_rfl))
  refine Set.Finite.to_subtype (((Set.finite_range fun q : SZ ⧸ CongruenceSubgroup.Gamma0 N => q.out⁻¹).prod (Set.finite_Iic (N, N, N))).subset ?_)
  rintro ⟨r, a, b, d⟩ ⟨hr, ⟨ha, hd, hadN, hbd, -⟩, -⟩
  refine ⟨hr, ?_, ?_, ?_⟩ <;> nlinarith [Nat.le_of_dvd (NeZero.pos N) hadN]

theorem card_BG_GammaDeltaR_eq :
    Nat.card (BG (GammaDeltaR N Δ)) = Δ.index * (Gamma0R N).relIndex (NormG (GammaDeltaR N Δ)) := by
  rw [← Subgroup.index_comap_of_surjective Δ unitMap_surjective, ← GammaDelta_subgroupOf, ← Subgroup.relIndex, ← Subgroup.relIndex_map_map_of_injective _ _ (SpecialLinearGroup.map_intCast_injective (R := ℝ))]
  exact (Subgroup.relIndex_mul_relIndex _ _ _ GammaDeltaR_le_Gamma0R Gamma0R_le_normG_GammaDeltaR').symm

theorem finite_BG_GammaDeltaR :
    Finite (BG (GammaDeltaR N Δ)) :=
  Nat.finite_of_card_ne_zero (by rw [card_BG_GammaDeltaR_eq]; exact mul_ne_zero Subgroup.index_ne_zero_of_finite (mt (Subgroup.relIndex_eq_zero_of_le_right normG_GammaDeltaR_le_MDelta) relIndex_Gamma0R_MDelta_ne_zero))

theorem factorization_hDelta_ne_iff {p : ℕ} (hp : p.Prime) :
    (hDelta N Δ).factorization p ≠ (hPart N).factorization p ↔
      p ^ (2 * (24 : ℕ).factorization p + 2) ∣ N ∧ p ^ ((24 : ℕ).factorization p + 1) ∣ epsDelta N Δ := by
  have hN := NeZero.ne N
  have h1 := (Nat.factorization_le_iff_dvd (by positivity) epsDelta_pos.ne').2 ((dvd_epsDelta_iff (Δ := Δ)).2 ⟨Nat.gcd_dvd_left N 24, fun u _ => by
    by_cases hN : N = 1
    · simp_all
    rw [dvd_sq_sub_one_iff (ZMod.val_pos.2 (haveI := ZMod.nontrivial_iff.2 hN; u.ne_zero)), ← ZMod.cast_eq_val, ← ZMod.unitsMap_val (Nat.gcd_dvd_left N 24)]
    exact sq_of_dvd_24 (Nat.gcd_dvd_right _ _) _⟩) p
  rw [Nat.factorization_gcd hN (by norm_num)] at h1
  rw [factorization_hDelta, hPart, Nat.factorization_mul (by positivity) (by positivity), Nat.prime_two.factorization_pow,
    Nat.prime_three.factorization_pow, hp.pow_dvd_iff_le_factorization hN, hp.pow_dvd_iff_le_factorization epsDelta_pos.ne']
  simp [factorization_24, Finsupp.single_apply] at *
  grind

theorem hDelta_eq_hPart_iff :
    hDelta N Δ = hPart N ↔
      ¬ ((∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ^ 2 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod p d) ∨
        (3 ^ 4 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod 9 d) ∨
        (2 ^ 8 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod 8 d)) := by
  have hc : ∀ {m m' k : ℕ}, 1 < k → m ∣ k → m' ∣ m →
      (∀ y : ZMod m, y ^ 2 = 1 ↔ (y.cast : ZMod m') = 1 ∨ (y.cast : ZMod m') = -1) →
      (k ∣ N ∧ m ∣ epsDelta N Δ ↔ k ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod m' d) := by
    refine fun hk hm hm' H => and_congr_right fun hkN => ?_
    have hN : N ≠ 1 := by rintro rfl; simp_all
    simp only [dvd_epsDelta_iff, hm.trans hkN, true_and, IsPmOneMod, ZMod.cast_eq_val]
    exact forall₂_congr fun u _ => (dvd_sq_sub_one_iff (ZMod.val_pos.2 (haveI := ZMod.nontrivial_iff.2 hN; u.ne_zero))).trans ((H _).trans (by rw [ZMod.cast_natCast hm']))
  have H16 := hc (m := 2 ^ 4) (k := 2 ^ 8) (by norm_num) (by norm_num) (by norm_num : 8 ∣ _) (by decide)
  have H9 := hc (m := 3 ^ 2) (k := 3 ^ 4) (by norm_num) (by norm_num) dvd_rfl (by decide)
  have Hp := fun {p : ℕ} (hp : p.Prime) => hc (m := p) (k := p ^ 2) (Nat.one_lt_pow two_ne_zero hp.one_lt) (dvd_pow_self _ two_ne_zero) dvd_rfl fun x => by have := Fact.mk hp; simp
  rw [← not_iff_not, ← Nat.factorization_inj.eq_iff (hDelta_ne_zero Δ) (by simp [hPart]), Finsupp.ext_iff]
  push Not
  constructor
  · rintro ⟨p, hp⟩
    have hpp : p.Prime := by by_contra h; simp_all
    rw [factorization_hDelta_ne_iff hpp, factorization_24] at hp
    rcases eq_or_ne p 2 with rfl | h2
    · grind
    rcases eq_or_ne p 3 with rfl | h3
    · grind
    simp [h2, h3] at hp
    exact Or.inl ⟨p, hpp, hpp.five_le_of_ne_two_of_ne_three h2 h3, (Hp hpp).1 hp⟩
  · rintro (⟨p, hp, h5, h⟩ | h | h)
    · refine ⟨p, (factorization_hDelta_ne_iff hp).2 ?_⟩
      simpa [factorization_24, show p ≠ 2 by omega, show p ≠ 3 by omega] using (Hp hp).2 h
    · exact ⟨3, (factorization_hDelta_ne_iff Nat.prime_three).2 (by rw [factorization_24]; grind)⟩
    · exact ⟨2, (factorization_hDelta_ne_iff Nat.prime_two).2 (by rw [factorization_24]; grind)⟩

end

end NormalizerLean
