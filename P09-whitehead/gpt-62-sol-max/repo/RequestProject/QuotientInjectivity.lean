module

public import Mathlib

@[expose] public section

/-!
# Injectivity detected by a quotient (Lemma 2.1)

Lemma 2.1 of the paper states: if `H ◁ Q` is torsion-free abelian and
`f : U → V` is a map of free left `ℤ[Q]`-modules whose reduction along
`ℤ[Q] → ℤ[Q/H]` is injective, then `f` is injective; likewise over `𝔽ₚ`.

After restricting scalars to the *commutative* domain `R = k[H]` the statement
becomes the purely commutative-algebra fact formalized here: for a ring
homomorphism `ε : R →+* S` between commutative domains, coefficientwise
reduction along `ε` detects injectivity of maps between free modules, with no
finiteness assumption on the ranks.  This is exactly the elementary proof
sketched in the paper ("Outline of a direct proof"): one chooses a coordinate
functional with `ε`-nonzero value and induces on the size of a finite family.

The group-theoretic reduction (`k[Q]` is free over `k[H]` on coset
representatives, and `k[Q/H] ⊗_{k[Q]} U ≅ k ⊗_{k[H]} U`) is *not* formalized
here; it is what the ring homomorphism `ε` of the statements below stands for.
-/

namespace FiniteChains

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]

/-- Coefficientwise reduction of a finitely supported vector along a ring map. -/
noncomputable def reduceVec (ε : R →+* S) {κ : Type*} (v : κ →₀ R) : κ →₀ S :=
  Finsupp.mapRange ε ε.map_zero v


omit [IsDomain R] [IsDomain S] in
theorem reduceVec_smul (ε : R →+* S) {κ : Type*} (a : R) (v : κ →₀ R) :
    reduceVec ε (a • v) = ε a • reduceVec ε v := by
  ext k; simp [reduceVec]

omit [IsDomain R] [IsDomain S] in
theorem reduceVec_sub (ε : R →+* S) {κ : Type*} (v w : κ →₀ R) :
    reduceVec ε (v - w) = reduceVec ε v - reduceVec ε w := by
  ext k; simp [reduceVec]

/-- Fraction-free elimination of one coordinate. -/
private noncomputable def clearCoordinate {κ : Type*} (v : κ →₀ R) (k : κ) :
    (κ →₀ R) →ₗ[R] (κ →₀ R) :=
  v k • LinearMap.id - (Finsupp.lapply k).smulRight v

/-- **Independence is detected after reduction.**  If a finite family of vectors in a free
module over a commutative domain `R` becomes linearly independent after coefficientwise
reduction along `ε : R →+* S` to a commutative domain `S`, then the family was already
linearly independent over `R`. -/
theorem eq_zero_of_reduction_indep {κ ι : Type*} (ε : R →+* S)
    (T : Finset ι) (v : ι → (κ →₀ R))
    (hred : ∀ d : ι → S, (∑ j ∈ T, d j • reduceVec ε (v j)) = 0 → ∀ j ∈ T, d j = 0)
    (c : ι → R) (hc : (∑ j ∈ T, c j • v j) = 0) : ∀ j ∈ T, c j = 0 := by
  classical
  induction T using Finset.strongInduction generalizing v c with
  | _ T ih =>
    intro i hi
    let U := T.erase i
    obtain ⟨k, hk⟩ : ∃ k, ε (v i k) ≠ 0 := by
      by_contra! he
      have hz : reduceVec ε (v i) = 0 := by ext k; exact he k
      have h := hred (Pi.single i 1) (by simp [Pi.single_apply, hz]) i hi
      simp at h
    let a := v i k
    let L := clearCoordinate (v i) k
    let w := L ∘ v
    have hw : w i = 0 := by simp [w, L, clearCoordinate]
    have hred' (d : ι → S) (hd : ∑ j ∈ U, d j • reduceVec ε (w j) = 0) :
        ∀ j ∈ U, d j = 0 := by
      let e j := if j = i then -(∑ j ∈ U, d j * ε (v j k)) else d j * ε a
      have hsum : (∑ j ∈ T, e j • reduceVec ε (v j)) = 0 := by
        rw [← Finset.add_sum_erase T (fun j => e j • reduceVec ε (v j)) hi]
        change e i • reduceVec ε (v i) + ∑ j ∈ U, e j • reduceVec ε (v j) = 0
        have he (j) (hj : j ∈ U) : e j = d j * ε a :=
          ite_eq_right (Finset.ne_of_mem_erase hj)
        simp only [← sub_eq_neg_add, show e i = -(∑ j ∈ U, d j * ε (v j k)) by simp [e], neg_smul]
        rw [Finset.sum_congr rfl (fun j hj => congrArg (· • reduceVec ε (v j)) (he j hj)),
          Finset.sum_smul, ← Finset.sum_sub_distrib]
        simpa only [w, L, clearCoordinate, Function.comp_apply, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.id_apply, LinearMap.smulRight_apply, Finsupp.lapply_apply,
          reduceVec_smul, reduceVec_sub, smul_sub, smul_smul] using hd
      intro j hj
      have h := hred e hsum j (Finset.mem_of_mem_erase hj)
      exact (mul_eq_zero.mp (by simpa only [e, ite_eq_right (Finset.ne_of_mem_erase hj)] using h)).resolve_right hk
    have hcw : ∑ j ∈ U, c j • w j = 0 := by
      have h := congrArg L hc
      rw [← Finset.add_sum_erase T (fun j => c j • v j) hi] at h
      simpa [map_sum, w, hw, show L (v i) = 0 from hw] using h
    have hzero := ih U (Finset.erase_ssubset hi) w hred' c hcw
    have hz : c i • v i = 0 := by
      rw [← hc]
      exact (Finset.sum_eq_single (f := fun j => c j • v j) i (fun j hj hn => by
        rw [hzero j (Finset.mem_erase.mpr ⟨hn, hj⟩), zero_smul]) (by simp [hi])).symm
    have hh : c i * a = 0 := by simpa using congrArg (· k) hz
    exact (mul_eq_zero.mp hh).resolve_right (fun ha => hk (by simp [← show a = v i k from rfl, ha]))

/-- The reduction along `ε : R →+* S` of an `R`-linear map between free modules. -/
noncomputable def reduceMap (ε : R →+* S) {ι κ : Type*}
    (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) : (ι →₀ S) →ₗ[S] (κ →₀ S) :=
  Finsupp.lsum S fun i =>
    LinearMap.toSpanSingleton S (κ →₀ S) (reduceVec ε (f (Finsupp.single i 1)))

omit [IsDomain R] [IsDomain S] in
@[simp] theorem reduceMap_single (ε : R →+* S) {ι κ : Type*}
    (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) (i : ι) (s : S) :
    reduceMap ε f (Finsupp.single i s) = s • reduceVec ε (f (Finsupp.single i 1)) := by
  simp [reduceMap, LinearMap.toSpanSingleton_apply]

/-- **Lemma 2.1, module-theoretic core.**  Reduction along a ring homomorphism between
commutative domains detects injectivity of maps between free modules of arbitrary rank. -/
theorem injective_of_reduceMap_injective (ε : R →+* S) {ι κ : Type*}
    (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) (h : Function.Injective (reduceMap ε f)) :
    Function.Injective f := by
  classical
  rw [injective_iff_map_eq_zero]
  intro u hu
  -- the reduced images of the relevant basis vectors are independent
  set v : ι → (κ →₀ R) := fun i => f (Finsupp.single i 1) with hv
  have hred : ∀ d : ι → S, (∑ j ∈ u.support, d j • reduceVec ε (v j)) = 0 →
      ∀ j ∈ u.support, d j = 0 := by
    intro d hd j hj
    have hmap : reduceMap ε f (∑ j ∈ u.support, Finsupp.single j (d j)) = 0 := by
      rw [map_sum]
      simpa [hv] using hd
    have hzero : (∑ j ∈ u.support, Finsupp.single j (d j)) = 0 := by
      tauto
    have := congrArg (fun x  => x j) hzero
    simpa [Finset.sum_apply', Finsupp.single_apply, Finset.sum_ite_eq' u.support j, hj] using this
  -- the coefficients of `u` satisfy the corresponding relation
  have hc : (∑ j ∈ u.support, u j • v j) = 0 := by
    have hu'  := (Finsupp.sum_single u).symm
    calc (∑ j ∈ u.support, u j • v j)
        = f (∑ j ∈ u.support, Finsupp.single j (u j)) := by
          simp [map_sum, hv, ← LinearMap.map_smul, Finsupp.smul_single]
      _ = f u := by tauto
      _ = 0 := hu
  have hzero := eq_zero_of_reduction_indep ε u.support v hred u hc
  ext j
  by_cases hj : j ∈ u.support
  · tauto
  · simpa using Finsupp.notMem_support_iff.mp hj

end FiniteChains
