module
public import ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal

public import DedekindZetaZeroFree.Arithmetic.LocalFields.CubicUnitRootBalls

@[expose] public section

section
namespace DedekindZetaZeroFree.KPCubicUnitIndices.CubicPreimageCosets
open ValuativeRel
open scoped Valued
section

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem mem_pow (a : O) (j : ℕ) :
    a ∈ IsLocalRing.maximalIdeal O ^ j ↔ (j : ℕ∞) ≤ IsDiscreteValuationRing.addVal O a := by apply @IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge <;> assumption

private theorem shallow (z : O) (hz : IsPrimitiveRoot z 3)
    (x : O) (j : ℕ) (hs : j ≤ 3 * (IsDiscreteValuationRing.addVal O (1 - z)).toNat) :
    (j : ℕ∞) ≤ IsDiscreteValuationRing.addVal O (x ^ 3 - 1) ↔
      (((j + 2) / 3 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal O (x - 1) := by
  let v := IsDiscreteValuationRing.addVal O
  let r := (v (1 - z)).toNat
  have hr := (ENat.natCast_toNat (fun h => hz.ne_one (by decide)
      (sub_eq_zero.mp (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)).symm)).symm
  have hzv : v z = 0 := by
    obtain ⟨u, hu⟩ := hz.isUnit (by decide)
    rw [← hu]
    exact IsDiscreteValuationRing.addVal_eq_zero_of_unit u
  have hp : z ^ 2 + z + 1 = 0 := by
    refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr (hz.ne_one (by decide)))
    calc
    _ = z ^ 3 - 1 := by ring
    _ = 0 := by rw [hz.pow_eq_one]; ring
  have hg : v (1 - z ^ 2) = r := by
    have h : 1 - z ^ 2 = -z ^ 2 * (1 - z) := by
      calc
        _ = -z ^ 2 * (1 - z) + (1 - z ^ 3) := by ring
        _ = _ := by rw [hz.pow_eq_one]; ring
    rw [h, v.map_mul, v.map_neg, v.map_pow, hzv, nsmul_zero, zero_add, hr]
  have hf : x ^ 3 - 1 = (x - 1) * (x - z) * (x - z ^ 2) := by
    calc
      _ = (x - 1) * (x - z) * (x - z ^ 2) +
        (x - 1) * x * (z ^ 2 + z + 1) - (x - 1) * (z ^ 3 - 1) := by ring
      _ = _ := by rw [hp, hz.pow_eq_one]; ring
  rw [hf, v.map_mul, v.map_mul]
  by_cases ht : v (x - 1) < r
  · have hb : v (x - z) = v (x - 1) := by
      rw [show x - z = (x - 1) + (1 - z) by ring]
      exact v.map_add_eq_of_lt_left (by rwa [hr])
    have hc : v (x - z ^ 2) = v (x - 1) := by
      rw [show x - z ^ 2 = (x - 1) + (1 - z ^ 2) by ring]
      exact v.map_add_eq_of_lt_left (by rwa [hg])
    rw [hb, hc]
    cases he : v (x - 1) with
    | top => simp [he] at ht
    | coe a =>
      norm_cast
      omega
  · have ha := le_of_not_gt ht
    have hb : r ≤ v (x - z) := by
      rw [show x - z = (x - 1) + (1 - z) by ring]
      exact (le_min ha hr.ge).trans (v.map_add _ _)
    have hc : r ≤ v (x - z ^ 2) := by
      rw [show x - z ^ 2 = (x - 1) + (1 - z ^ 2) by ring]
      exact (le_min ha hg.ge).trans (v.map_add _ _)
    have hjr : (j : ℕ∞) ≤ (r : ℕ∞) + r + r := by
      norm_cast
      dsimp [r, v] at *
      omega
    have hceil : (((j + 2) / 3 : ℕ) : ℕ∞) ≤ (r : ℕ∞) := by
      norm_cast
      dsimp [r, v] at *
      omega
    exact iff_of_true (hjr.trans (add_le_add (add_le_add ha hb) hc)) (hceil.trans ha)

end

theorem cubic_preimage_shallow
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : (valuation K).integer) (hζ : IsPrimitiveRoot ζ 3)
    (j : ℕ) (hj : 1 ≤ j)
    (hshallow : j ≤ 3 * (IsDiscreteValuationRing.addVal
      (valuation K).integer (1 - ζ)).toNat) :
    let O := (valuation K).integer
    let U := fun n : ℕ =>
      (Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n)).toMonoidHom).ker
    (U j).comap (powMonoidHom 3) = U ((j + 2) / 3) := by
  dsimp only
  ext u
  have hm (n : ℕ) (w : (valuation K).integerˣ) :
      w ∈ (Units.map (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (valuation K).integer ^ n)).toMonoidHom).ker ↔
      (w : (valuation K).integer) - 1 ∈
        IsLocalRing.maximalIdeal (valuation K).integer ^ n := by
    change Units.map _ w = 1 ↔ _
    rw [Units.ext_iff]
    exact Ideal.Quotient.eq
  rw [Subgroup.mem_comap, hm, hm, mem_pow, mem_pow]
  exact shallow ζ hζ u j hshallow

end DedekindZetaZeroFree.KPCubicUnitIndices.CubicPreimageCosets

end

section
namespace DedekindZetaZeroFree.KPCubicUnitIndices.CubicPreimageCosets

open ValuativeRel
open scoped Valued

set_option backward.isDefEq.respectTransparency false

def logNeg (x : WithZero (Multiplicative ℤ)) : WithTop ℤ := x.recZeroCoe ⊤ (fun a => (-a.toAdd : ℤ))
lemma logNeg_mul (x y : WithZero (Multiplicative ℤ)) : logNeg (x*y) = logNeg x + logNeg y := by
  cases x using WithZero.recZeroCoe <;> cases y using WithZero.recZeroCoe <;> simp [logNeg, ← WithZero.coe_mul]
  push_cast
  ac_rfl
lemma logNeg_anti {x y : WithZero (Multiplicative ℤ)} (h : x ≤ y) : logNeg y ≤ logNeg x := by
  cases x using WithZero.recZeroCoe with
  | zero => simp [logNeg]
  | coe a =>
    cases y using WithZero.recZeroCoe with
    | zero => exact (WithZero.not_coe_le_zero _ h).elim
    | coe b =>
      change (-(b.toAdd) : WithTop ℤ) ≤ (-(a.toAdd) : WithTop ℤ)
      have hh : a.toAdd ≤ b.toAdd := WithZero.coe_le_coe.mp h
      exact_mod_cast (neg_le_neg hh)
variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
noncomputable def av : AddValuation K (WithTop ℤ) :=
  let w := (valuation K).map (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
  AddValuation.of (fun x => logNeg (w x)) (by simp [logNeg]) (by simp [logNeg])
    (fun x y => (logNeg_anti (w.map_add x y)).trans' (by
      cases le_total (w x) (w y) with
      | inl h => rw [max_eq_right h, min_eq_right (logNeg_anti h)]
      | inr h => rw [max_eq_left h, min_eq_left (logNeg_anti h)]))
    (by intro x y; rw [map_mul, logNeg_mul])
private lemma av_normalized : ∃ p : K, av K p = 1 := by
  obtain ⟨p, hp⟩ := valuation_surjective ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm (WithZero.exp (-1 : ℤ)))
  refine ⟨p, ?_⟩
  change logNeg ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K) ((valuation K) p)) = 1
  rw [hp, OrderMonoidIso.apply_symm_apply]
  rfl
lemma rings : (DedekindZetaZeroFree.CubicUnitBalls.Ring (av K)).toSubring = (valuation K).integer := by
  apply SetLike.ext
  intro x
  change (0 : WithTop ℤ) ≤ logNeg ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K) (valuation K x)) ↔ valuation K x ≤ 1
  have hh := (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.le_iff_le (x := valuation K x) (y := 1)
  change ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K) (valuation K x) ≤ (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K) 1 ↔ _) at hh
  rw [map_one] at hh
  rw [← hh]
  generalize (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K) (valuation K x) = z
  cases z using WithZero.recZeroCoe with
  | zero => simp [logNeg]
  | coe a =>
    change (0 : WithTop ℤ) ≤ (-(a.toAdd) : WithTop ℤ) ↔ (a : WithZero (Multiplicative ℤ)) ≤ (↑(1 : Multiplicative ℤ))
    rw [WithZero.coe_le_coe]
    change _ ↔ a.toAdd ≤ 0
    norm_cast
    omega

noncomputable instance av_dvr : IsDiscreteValuationRing (DedekindZetaZeroFree.CubicUnitBalls.Ring (av K)) := by
  change IsDiscreteValuationRing (DedekindZetaZeroFree.CubicUnitBalls.Ring (av K)).toSubring
  rw [rings K]
  infer_instance

private lemma depth_identify (a : DedekindZetaZeroFree.CubicUnitBalls.Ring (av K)) :
    (IsDiscreteValuationRing.addVal (DedekindZetaZeroFree.CubicUnitBalls.Ring (av K)) a).toNat =
      ((av K (a : K)).untopD 0).toNat := by
  let v := av K
  let O := DedekindZetaZeroFree.CubicUnitBalls.Ring v
  obtain ⟨p, hp⟩ := av_normalized K
  let π : O := ⟨p, by change 0 ≤ v p; rw [hp]; decide⟩
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {π} := by
    ext b
    rw [Valuation.mem_maximalIdeal_iff, Ideal.mem_span_singleton,
      (Valuation.valuationSubring.integers v.toValuation).dvd_iff_le]
    change 0 < v (b : K) ↔ v p ≤ v (b : K)
    rw [hp]
    cases v (b : K) with
    | top => simp
    | coe b => norm_cast
  have hi := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hm
  by_cases ha : a = 0
  · simp [ha, IsDiscreteValuationRing.addVal_zero]
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hi
  rw [hu, IsDiscreteValuationRing.addVal_def' u hi]
  change n = ((v (((u : O) : K) * p ^ n)).untopD 0).toNat
  rw [v.map_mul, v.map_pow, DedekindZetaZeroFree.CubicUnitBalls.unit_valuation_eq_zero,
    hp, zero_add]
  rw [nsmul_one]
  change n = (WithTop.untopD 0 (↑(n : ℤ) : WithTop ℤ)).toNat
  rw [WithTop.untopD_coe, Int.toNat_natCast]

private theorem generic_deep
    (S : Subring K) [IsDiscreteValuationRing S]
    (hS : S = (DedekindZetaZeroFree.CubicUnitBalls.Ring (av K)).toSubring)
    (ζ : S) (hζ : IsPrimitiveRoot ζ 3)
    (j : ℕ) (hdeep : 3 * (IsDiscreteValuationRing.addVal
      S (1 - ζ)).toNat < j) :
    let O := S
    let r := (IsDiscreteValuationRing.addVal O (1 - ζ)).toNat
    let U := fun n : ℕ =>
      (Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n)).toMonoidHom).ker
    let P := U (j - 2 * r)
    let B := (U j).comap (powMonoidHom 3)
    (B : Set Oˣ) =
        ⋃ ξ ∈ (rootsOfUnity 3 O : Set Oˣ),
          (fun u => ξ * u) '' (P : Set Oˣ) ∧
      (rootsOfUnity 3 O : Set Oˣ).Pairwise
        (fun ξ η => Disjoint
          ((fun u => ξ * u) '' (P : Set Oˣ))
          ((fun u => η * u) '' (P : Set Oˣ))) := by
    subst S
    dsimp only at hζ hdeep ⊢
    let v := av K
    let O := DedekindZetaZeroFree.CubicUnitBalls.Ring v
    let z := (hζ.isUnit (by decide)).unit
    have hz : IsPrimitiveRoot ((z : O) : K) 3 := by
      have hh := hζ.map_of_injective (f := O.subtype) Subtype.val_injective
      change IsPrimitiveRoot (ζ : K) 3 at hh
      simpa only [z, IsUnit.unit_spec] using hh
    haveI : IsDiscreteValuationRing O := inferInstance
    have hd : (IsDiscreteValuationRing.addVal (DedekindZetaZeroFree.CubicUnitBalls.Ring (av K)).toSubring (1 - ζ)).toNat =
        DedekindZetaZeroFree.CubicUnitBalls.rootDepth v z := by
      unfold DedekindZetaZeroFree.CubicUnitBalls.rootDepth
      simp only [z, IsUnit.unit_spec]
      with_unfolding_all exact depth_identify K (1 - ζ)
    have deep : 3 * DedekindZetaZeroFree.CubicUnitBalls.rootDepth v z < j := by
      simpa only [hd] using hdeep
    have roots : (rootsOfUnity 3 (DedekindZetaZeroFree.CubicUnitBalls.Ring (av K)).toSubring : Set Oˣ) = DedekindZetaZeroFree.CubicUnitBalls.cubeRoots v z := by
      have hzu : IsPrimitiveRoot z 3 := by
        simpa using hζ.isUnit_unit (by decide)
      ext ξ
      constructor
      · intro hξ
        obtain ⟨i, hi, he⟩ := hzu.eq_pow_of_mem_rootsOfUnity hξ
        have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases this with rfl | rfl | rfl <;> simp [← he, DedekindZetaZeroFree.CubicUnitBalls.cubeRoots]
      · intro hξ
        simp only [DedekindZetaZeroFree.CubicUnitBalls.cubeRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hξ
        rcases hξ with rfl | rfl | rfl
        · exact (rootsOfUnity 3 _).one_mem
        · exact hzu.mem_rootsOfUnity
        · exact (rootsOfUnity 3 _).pow_mem hzu.mem_rootsOfUnity 2
    let maximalIdeal₀ := IsLocalRing.maximalIdeal (DedekindZetaZeroFree.CubicUnitBalls.Ring (av K)).toSubring
    have ker (n : ℕ) (hn : n ≠ 0) :
        ((Units.map (Ideal.Quotient.mk (maximalIdeal₀ ^ n)).toMonoidHom).ker : Set Oˣ) =
          DedekindZetaZeroFree.CubicUnitBalls.principalUnits v n := by
      ext u
      rw [DedekindZetaZeroFree.CubicUnitBalls.principalUnits, if_neg hn]
      change Units.map _ u = 1 ↔ _
      rw [Units.ext_iff]
      change Ideal.Quotient.mk _ (u : O) = 1 ↔ _
      rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      with_unfolding_all rfl
    rw [hd]
    rw [roots, ker (j - 2 * DedekindZetaZeroFree.CubicUnitBalls.rootDepth v z) (by omega)]
    have kb : ((Subgroup.comap (powMonoidHom 3) (Units.map (Ideal.Quotient.mk (maximalIdeal₀ ^ j)).toMonoidHom).ker : Subgroup Oˣ) : Set Oˣ) = DedekindZetaZeroFree.CubicUnitBalls.cubicPreimage v j := by
      ext u
      change u ^ 3 ∈ ((Units.map (Ideal.Quotient.mk (maximalIdeal₀ ^ j)).toMonoidHom).ker : Set Oˣ) ↔ _
      rw [ker j (by omega)]
      rfl
    rw [kb]
    exact ⟨DedekindZetaZeroFree.CubicUnitBalls.cubicPreimage_deep v (av_normalized K) z hz j (by omega) deep,
      DedekindZetaZeroFree.CubicUnitBalls.rootCosets_pairwise_disjoint v (av_normalized K) z hz j (by omega) deep⟩

theorem cubic_preimage_deep_cosets
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : (valuation K).integer) (hζ : IsPrimitiveRoot ζ 3)
    (j : ℕ) (hdeep : 3 * (IsDiscreteValuationRing.addVal
      (valuation K).integer (1 - ζ)).toNat < j) :
    let O := (valuation K).integer
    let r := (IsDiscreteValuationRing.addVal O (1 - ζ)).toNat
    let U := fun n : ℕ =>
      (Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n)).toMonoidHom).ker
    let P := U (j - 2 * r)
    let B := (U j).comap (powMonoidHom 3)
    (B : Set Oˣ) =
        ⋃ ξ ∈ (rootsOfUnity 3 O : Set Oˣ),
          (fun u => ξ * u) '' (P : Set Oˣ) ∧
      (rootsOfUnity 3 O : Set Oˣ).Pairwise
        (fun ξ η => Disjoint
          ((fun u => ξ * u) '' (P : Set Oˣ))
          ((fun u => η * u) '' (P : Set Oˣ))) := generic_deep K (valuation K).integer (rings K).symm ζ hζ j hdeep

end DedekindZetaZeroFree.KPCubicUnitIndices.CubicPreimageCosets

end

section
namespace DedekindZetaZeroFree.KPCubicUnitIndices.CubicPreimageCosets

theorem relIndex_of_disjoint_cosets
    {G : Type*} [Group G] (P B : Subgroup G) (S : Set G) [Finite S]
    (hunion : (B : Set G) = ⋃ ξ ∈ S, (fun u => ξ * u) '' (P : Set G))
    (hdisjoint : S.Pairwise (fun ξ η => Disjoint
      ((fun u => ξ * u) '' (P : Set G))
      ((fun u => η * u) '' (P : Set G)))) :
    P.relIndex B = Nat.card S := by
  classical
  have hmem (ξ : S) : (ξ : G) ∈ B := by
    change (ξ : G) ∈ (B : Set G)
    rw [hunion]
    exact Set.mem_iUnion.mpr ⟨ξ, Set.mem_iUnion.mpr ⟨ξ.property,
      ⟨1, P.one_mem, mul_one _⟩⟩⟩
  let f : S → B ⧸ P.subgroupOf B := fun ξ =>
    QuotientGroup.mk ⟨ξ, hmem ξ⟩
  have hf : Function.Bijective f := by
    constructor
    · intro ξ η heq
      by_contra hne
      exact Set.disjoint_left.mp (hdisjoint ξ.property η.property (fun h => hne (Subtype.ext h))) (⟨(ξ : G)⁻¹ * (η : G), by
        have := QuotientGroup.eq.mp heq
        exact this, mul_inv_cancel_left _ _⟩) ⟨1, P.one_mem, mul_one _⟩
    · intro q
      refine Quotient.inductionOn q ?_
      intro x
      have hx : (x : G) ∈ ⋃ ξ ∈ S, (fun u => ξ * u) '' P := by
        rw [← hunion]
        exact x.property
      rcases Set.mem_iUnion.mp hx with ⟨ξ, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨hξ, u, hu, hxu⟩
      refine ⟨⟨ξ, hξ⟩, QuotientGroup.eq.mpr ?_⟩
      change ξ⁻¹ * (x : G) ∈ P
      rw [← hxu, inv_mul_cancel_left]
      exact hu
  exact Nat.card_congr (Equiv.ofBijective f hf).symm

end DedekindZetaZeroFree.KPCubicUnitIndices.CubicPreimageCosets

end

section
namespace DedekindZetaZeroFree
namespace KPCubicUnitIndices
noncomputable section
open ValuativeRel
open scoped Valued

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

abbrev Integers := (valuation K).integer

def principalUnits (j : ℕ) : Subgroup (Integers K)ˣ :=
  (Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Integers K) ^ j)).toMonoidHom).ker

def cubeUnits : Subgroup (Integers K)ˣ := (powMonoidHom 3).range

def truncatedIndex (j : ℕ) : ℕ :=
  (cubeUnits K ⊔ principalUnits K j).index

def residueCard : ℕ := Nat.card (IsLocalRing.ResidueField (Integers K))

def rootDepth (ζ : Integers K) : ℕ :=
  (IsDiscreteValuationRing.addVal (Integers K) (1 - ζ)).toNat

@[simp] theorem principalUnits_zero : principalUnits K 0 = ⊤ := by
  ext u
  simp only [principalUnits, MonoidHom.mem_ker, Subgroup.mem_top, iff_true]
  apply Units.ext
  apply Ideal.Quotient.eq.mpr
  simp

@[simp] theorem truncatedIndex_zero : truncatedIndex K 0 = 1 := by
  simp [truncatedIndex]

theorem two_le_residueCard : 2 ≤ residueCard K := by
  classical
  let R := IsLocalRing.ResidueField (Integers K)
  haveI : Finite R := inferInstance
  letI : Fintype R := Fintype.ofFinite R
  simpa [R, residueCard, Nat.card_eq_fintype_card, Nat.add_one_le_iff] using (Fintype.one_lt_card)

theorem mem_principalUnits (j : ℕ) (u : (Integers K)ˣ) :
    u ∈ principalUnits K j ↔
      (u : Integers K) - 1 ∈ IsLocalRing.maximalIdeal (Integers K) ^ j := by
  change Units.map _ u = 1 ↔ _
  rw [Units.ext_iff]
  exact Ideal.Quotient.eq

theorem principalUnits_antitone (a b : ℕ) (hab : a ≤ b) :
    principalUnits K b ≤ principalUnits K a := by
  intro u hu
  rw [mem_principalUnits] at hu ⊢
  exact Ideal.pow_le_pow_right hab hu

instance principalUnits_finiteIndex (j : ℕ) : (principalUnits K j).FiniteIndex := by
  unfold principalUnits
  infer_instance

theorem truncatedIndex_eq_preimage_relIndex (j : ℕ) :
    truncatedIndex K j =
      (principalUnits K j).relIndex ((principalUnits K j).comap (powMonoidHom 3)) := by
  let P := principalUnits K j
  let f : (Integers K)ˣ →* (Integers K)ˣ := powMonoidHom 3
  have hPB : P ≤ P.comap f := fun u hu => P.pow_mem hu 3
  haveI : (P.comap f).FiniteIndex := Subgroup.finiteIndex_of_le hPB
  have hB : (P.comap f).index = P.relIndex (f.range ⊔ P) := by
    rw [Subgroup.index_comap, Subgroup.relIndex_sup_right]
  apply mul_left_cancel₀
    (show (P.comap f).index ≠ 0 from Subgroup.index_ne_zero_of_finite)
  calc
    (P.comap f).index * (f.range ⊔ P).index = P.index := by rw [hB, (Subgroup.relIndex_mul_index (show P ≤ f.range ⊔ P from le_sup_right))]
    _ = (P.comap f).index * P.relIndex (P.comap f) := by rw [← (Subgroup.relIndex_mul_index hPB), Nat.mul_comm]

variable (a b : ℕ) (ha : 1 ≤ a)

def principalUnits_reductionEquivIdeal :
    ((principalUnits K a).map
      (Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Integers K) ^ b)).toMonoidHom)) ≃
    (IsLocalRing.maximalIdeal (Integers K) ^ a).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Integers K) ^ b)) := by
  let p := IsLocalRing.maximalIdeal (Integers K)
  let f := Ideal.Quotient.mk (p ^ b)
  let uf := Units.map f.toMonoidHom
  let P := (principalUnits K a).map uf
  let A := (p ^ a).map f
  have hmap (u : P) : (u.val : Integers K ⧸ p ^ b) - 1 ∈ A := by
    obtain ⟨v, hv, hvu⟩ := u.property
    rw [← hvu]
    change f v - 1 ∈ A
    rw [← map_one f, ← map_sub]
    exact Ideal.mem_map_of_mem f ((mem_principalUnits K a v).mp hv)
  refine Equiv.ofBijective (fun u : P => (⟨_, hmap u⟩ : A)) ⟨?_, ?_⟩
  · intro u v huv
    apply Subtype.ext
    apply Units.ext
    exact sub_left_injective (congrArg Subtype.val huv)
  · intro x
    obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mp x.property
    have hyp : y ∈ p := by simpa only [pow_one] using Ideal.pow_le_pow_right ha hy
    have hu : IsUnit (1 + y) := by
      apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
      apply (IsLocalRing.mem_maximalIdeal _).mp
      convert p.neg_mem hyp using 1 <;> ring
    let u := hu.unit
    have hua : u ∈ principalUnits K a := by
      rw [mem_principalUnits, hu.unit_spec]
      simpa using hy
    refine ⟨⟨uf u, Subgroup.mem_map.mpr ⟨u, hua, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change f u - 1 = x.val
    rw [hu.unit_spec, map_add, map_one, add_sub_cancel_left, hyx]

include ha in
theorem principalUnits_relIndex_eq_addIndex :
    (principalUnits K b).relIndex (principalUnits K a) =
      (IsLocalRing.maximalIdeal (Integers K) ^ b).toAddSubgroup.relIndex
        (IsLocalRing.maximalIdeal (Integers K) ^ a).toAddSubgroup := by
  unfold principalUnits
  rw [Subgroup.relIndex_ker]
  change Nat.card ((principalUnits K a).map (Units.map
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Integers K) ^ b)).toMonoidHom)) = _
  rw [Nat.card_congr (principalUnits_reductionEquivIdeal K a b ha)]
  let p := IsLocalRing.maximalIdeal (Integers K)
  let f := Ideal.Quotient.mk (p ^ b)
  have hker : f.toAddMonoidHom.ker = (p ^ b).toAddSubgroup := by
    ext x
    exact (Ideal.Quotient.eq_zero_iff_mem)
  rw [← hker, AddSubgroup.relIndex_ker]
  congr 1
  congr 1
  ext x
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mp h
    exact ⟨y, hy, hyx⟩
  · rintro ⟨y, hy, hyx⟩
    exact (Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mpr ⟨y, hy, hyx⟩

include ha in
theorem principalUnits_relIndex (hab : a ≤ b) :
    (principalUnits K b).relIndex (principalUnits K a) = residueCard K ^ (b - a) := by
  rw [principalUnits_relIndex_eq_addIndex K a b ha]
  let p := IsLocalRing.maximalIdeal (Integers K)
  have hp : p.cardQuot = residueCard K := rfl
  have hpow (n : ℕ) : (p ^ n).toAddSubgroup.index = residueCard K ^ n := by
    change (p ^ n : Submodule (Integers K) (Integers K)).cardQuot = _
    rw [cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field _), hp]
  have hdiv := AddSubgroup.relIndex_mul_index
    (show (p ^ b).toAddSubgroup ≤ (p ^ a).toAddSubgroup from Ideal.pow_le_pow_right hab)
  rw [hpow, hpow] at hdiv
  apply mul_right_cancel₀ (show residueCard K ^ a ≠ 0 from pow_ne_zero _ (by
    have := two_le_residueCard K
    omega))
  rw [hdiv, ← pow_add, Nat.sub_add_cancel hab]

end
end KPCubicUnitIndices

open KPCubicUnitIndices

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ζ : Integers K) (hζ : IsPrimitiveRoot ζ 3)

include hζ in
theorem kp_cubic_unit_truncated_indices :
    let q := residueCard K
    let r := rootDepth K ζ
    2 ≤ q ∧ truncatedIndex K 0 = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 3 * r → truncatedIndex K j = q ^ (j - (j + 2) / 3)) ∧
      (∀ j : ℕ, 3 * r < j → truncatedIndex K j = 3 * q ^ (2 * r)) := by
  refine ⟨two_le_residueCard K, truncatedIndex_zero K, ?_, ?_⟩
  · intro j hj hshallow
    have hpre : (principalUnits K j).comap (powMonoidHom 3) =
        principalUnits K ((j + 2) / 3) :=
      CubicPreimageCosets.cubic_preimage_shallow K ζ hζ j hj hshallow
    rw [truncatedIndex_eq_preimage_relIndex, hpre]
    exact principalUnits_relIndex K ((j + 2) / 3) j (by omega) (by omega)
  let rootsOfUnity₀ := rootsOfUnity 3 (Integers K)
  · intro j hdeep
    let a := j - 2 * rootDepth K ζ
    let P := principalUnits K a
    let B := (principalUnits K j).comap (powMonoidHom 3)
    let Set₀ := Set (Integers K)ˣ
    have hcosets :
        B =
          ⋃ ξ ∈ (rootsOfUnity₀ : Set₀),
            (fun u => ξ * u) '' P ∧
        (rootsOfUnity₀ : Set₀).Pairwise
          (fun ξ η => Disjoint
            ((fun u => ξ * u) '' P)
            ((fun u => η * u) '' P)) :=
      CubicPreimageCosets.cubic_preimage_deep_cosets K ζ hζ j hdeep
    have hPB : P ≤ B := by
      intro u hu
      change u ∈ (B : Set₀)
      rw [hcosets.1]
      exact Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr
        ⟨(rootsOfUnity₀).one_mem, ⟨u, hu, one_mul u⟩⟩⟩
    have hcard := hζ.card_rootsOfUnity
    haveI : Finite (rootsOfUnity₀) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
    have hindex : P.relIndex B = 3 := by
      rw [CubicPreimageCosets.relIndex_of_disjoint_cosets P B
        (rootsOfUnity₀ : Set₀) hcosets.1 hcosets.2]
      exact hcard
    rw [truncatedIndex_eq_preimage_relIndex]
    rw [← Subgroup.relIndex_mul_relIndex (principalUnits K j) P B (principalUnits_antitone K a j (by dsimp [a]; omega)) hPB,
      hindex, principalUnits_relIndex K a j (by dsimp [a]; omega) (by dsimp [a]; omega)]
    have hexp : j - a = 2 * rootDepth K ζ := by dsimp [a]; omega
    rw [hexp, Nat.mul_comm]

include hζ in
theorem kp_cubic_unit_truncated_indices_stable :
    ∀ j : ℕ, 3 * rootDepth K ζ + 1 ≤ j →
      truncatedIndex K j = truncatedIndex K (3 * rootDepth K ζ + 1) := by
  intro j hj
  have h := (kp_cubic_unit_truncated_indices K ζ hζ).2.2.2
  rw [h j (by omega), h (3 * rootDepth K ζ + 1) (by omega)]

end DedekindZetaZeroFree

end
