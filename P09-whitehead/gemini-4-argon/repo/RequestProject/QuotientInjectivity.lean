module

public import Mathlib

@[expose] public section

noncomputable section
namespace FiniteChains

variable {R S : Type*} [CommRing R] [CommRing S]

def reduceVec (ε : R →+* S) {κ : Type*} (v : κ →₀ R) : κ →₀ S :=
  Finsupp.mapRange ε ε.map_zero v

@[simp] theorem reduceVec_apply (ε : R →+* S) {κ : Type*} (v : κ →₀ R) (k : κ) :
    reduceVec ε v k = ε (v k) := rfl

theorem reduceVec_smul (ε : R →+* S) {κ : Type*} (a : R) (v : κ →₀ R) :
    reduceVec ε (a • v) = ε a • reduceVec ε v := by ext k; simp

theorem reduceVec_sub (ε : R →+* S) {κ : Type*} (v w : κ →₀ R) :
    reduceVec ε (v - w) = reduceVec ε v - reduceVec ε w := by ext k; simp

def reduceMap (ε : R →+* S) {ι κ : Type*}
    (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) : (ι →₀ S) →ₗ[S] (κ →₀ S) :=
  Finsupp.lsum S fun i =>
    LinearMap.toSpanSingleton S (κ →₀ S) (reduceVec ε (f (Finsupp.single i 1)))

@[simp] theorem reduceMap_single (ε : R →+* S) {ι κ : Type*}
    (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) (i : ι) (s : S) :
    reduceMap ε f (Finsupp.single i s) = s • reduceVec ε (f (Finsupp.single i 1)) := by
  simp [reduceMap, LinearMap.toSpanSingleton_apply]

variable [IsDomain R] [IsDomain S]

theorem eq_zero_of_reduction_indep {κ ι : Type*} (ε : R →+* S)
    (T : Finset ι) (v : ι → (κ →₀ R))
    (hred : ∀ d : ι → S, (∑ j ∈ T, d j • reduceVec ε (v j)) = 0 → ∀ j ∈ T, d j = 0)
    (c : ι → R) (hc : (∑ j ∈ T, c j • v j) = 0) : ∀ j ∈ T, c j = 0 := by
  classical
  induction T using Finset.strongInduction generalizing v with
  | _ T ih =>
    intro j₀ hj₀
    set T' := T.erase j₀
    have ⟨k, hk⟩ : ∃ k : κ, ε (v j₀ k) ≠ 0 := by
      by_contra! hall
      have hzero : reduceVec ε (v j₀) = 0 := Finsupp.ext hall
      simpa using hred (fun j => if j = j₀ then 1 else 0)
        (by simp [Finset.sum_ite_eq', hj₀, hzero]) j₀ hj₀
    set a : R := v j₀ k
    have ha0 : a ≠ 0 := fun h => hk (by rw [h, map_zero])
    let w : ι → (κ →₀ R) := fun j => a • v j - (v j k) • v j₀
    have hred' (d : ι → S) (hd : (∑ j ∈ T', d j • reduceVec ε (w j)) = 0) (j : ι) (hj : j ∈ T') :
        d j = 0 := by
      let e : ι → S := fun i => if i = j₀ then -(∑ i ∈ T', d i * ε (v i k)) else d i * ε a
      have hsplit : (∑ i ∈ T, e i • reduceVec ε (v i)) = 0 := by
        rw [← Finset.add_sum_erase T _ hj₀]
        simp only [e, ↓reduceIte, neg_smul, ← sub_eq_neg_add]
        rw [Finset.sum_congr rfl fun i hi => by rw [if_neg (Finset.ne_of_mem_erase hi)]]
        simpa [w, reduceVec_sub, reduceVec_smul, smul_sub, smul_smul, Finset.sum_sub_distrib,
          Finset.sum_smul] using hd
      simpa [e, Finset.ne_of_mem_erase hj, hk] using hred e hsplit j (Finset.mem_of_mem_erase hj)
    have hcw : (∑ j ∈ T', c j • w j) = 0 := by
      have hw0 : c j₀ • w j₀ = 0 := by simp [w, a]
      conv_lhs => rw [← zero_add (∑ j ∈ T', c j • w j), ← hw0, Finset.add_sum_erase T (fun j => c j • w j) hj₀]
      have hck : (∑ j ∈ T, c j * v j k) = 0 := by
        simpa [Finset.sum_apply'] using congrArg (fun x : κ →₀ R => x k) hc
      calc (∑ j ∈ T, c j • w j)
          = a • (∑ j ∈ T, c j • v j) - (∑ j ∈ T, c j * v j k) • v j₀ := by
            rw [Finset.smul_sum, Finset.sum_smul, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun j _ => by
              simp only [w, smul_sub, smul_smul, mul_comm (c j) a]
        _ = 0 := by rw [hc, hck, smul_zero, zero_smul, sub_self]
    have hzero' := ih T' (Finset.erase_ssubset hj₀) w hred' hcw
    have honly : c j₀ • v j₀ = 0 := by
      rw [← Finset.add_sum_erase T _ hj₀,
        Finset.sum_eq_zero fun j hj => by rw [hzero' j hj, zero_smul], add_zero] at hc
      exact hc
    simpa [a, ha0] using congrArg (fun x : κ →₀ R => x k) honly

theorem injective_of_reduceMap_injective (ε : R →+* S) {ι κ : Type*}
    (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) (h : Function.Injective (reduceMap ε f)) :
    Function.Injective f := by
  classical
  rw [injective_iff_map_eq_zero]
  intro u hu
  let v (i : ι) := f (Finsupp.single i 1)
  have hred (d : ι → S) (hd : (∑ j ∈ u.support, d j • reduceVec ε (v j)) = 0)
      (j : ι) (hj : j ∈ u.support) : d j = 0 := by
    have hzero : (∑ i ∈ u.support, Finsupp.single i (d i)) = 0 :=
      h (by rw [map_sum, map_zero]; simpa [v] using hd)
    simpa [Finset.sum_apply', Finsupp.single_apply, Finset.sum_ite_eq' u.support j, hj]
      using congrArg (fun x : ι →₀ S => x j) hzero
  have hc : (∑ j ∈ u.support, u j • v j) = 0 := by
    have h1 := (congrArg f (Finsupp.sum_single u)).trans hu
    simpa [Finsupp.sum, v, map_sum, ← LinearMap.map_smul, Finsupp.smul_single] using h1
  have hzero := eq_zero_of_reduction_indep ε u.support v hred u hc
  ext j
  by_cases hj : j ∈ u.support
  · exact hzero j hj
  · exact Finsupp.notMem_support_iff.mp hj
