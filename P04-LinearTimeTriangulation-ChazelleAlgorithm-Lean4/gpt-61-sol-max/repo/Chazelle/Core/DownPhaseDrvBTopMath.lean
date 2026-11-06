module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvBTopProg
public import Chazelle.Core.DownPhaseDrvBSize
public import Chazelle.Core.Setup

/-!
# Down-phase base (D9), top level, part 2: the math

* interior descriptors: `desc_int`, `liBit_iff`, `descWF_int`;
* `reg_sizes`: from the level invariant at a level with `γ = 2^(⌈βλ⌉+12)`, the bounds the region
  loop needs (`S₀ = 5 γ + 8` points per region, `Cm = γ + 2` walk edges per arc, `n ≤ Cm` when
  `K = 0`), from `regPts_length_le`, `arcCnt_le`, `n_le_of_empty`;
* `newLB_facts`: `L ++ newLB` is a valid chord list containing every vertex chord of `Q`
  (`newL_ok`, `newL_full`, `newL0_ok`, `newL0_full`);
* `count_le`: `K ≤ cnt λ (2^p + 1)` from (I3);
* `top_cost`: the total cost is `O(n)`.
-/

namespace Chazelle.Core

namespace DrvB.BTop

open Machine
open BuildNF (codeLe)
open Chazelle.Visibility (chords)

@[expose] public section

/-! ## Interior descriptors -/

theorem desc_int {m : ℕ → ℕ} {D : ℕ} {Q : Polygon} (h : ModelDescAt m D Q (interiorModel Q)) :
    m D = 1 ∧ (m (D + 1) = 1 ↔ Mountain.LeftInside Q) := by
  rcases h with ⟨-, H, C, -, hC⟩ | ⟨h1, h2, -⟩
  · exact absurd hC.symm (Restore.chainModel_ne_interior C Q)
  simp_all

theorem liBit_iff {m : ℕ → ℕ} {D : ℕ} {Q : Polygon} (h : ModelDescAt m D Q (interiorModel Q)) :
    liBit m D = true ↔ Mountain.LeftInside Q := by
  unfold liBit; rw [decide_eq_true_iff]; exact (desc_int h).2

theorem descWF_int {P : Polygon} {A : ℕ} {m : ℕ → ℕ} {D : ℕ}
    (h : ModelDescAt m D (Qof P) (interiorModel (Qof P))) (hA : D + 6 ≤ A) :
    ModelDescWF P A m D :=
  ⟨hA, fun h0 => by have := (desc_int h).1; omega⟩

/-! ## Sizes of the regions -/

theorem host_run_length {n : ℕ} (hn : 1 ≤ n) : (Host.pts n [HostItem.run 0 (n - 1)]).length = n := by
  core_grind [HostItem.pts]

theorem topGrade_le' (n : ℕ) : topGrade n ≤ n := by
  unfold topGrade
  exact Nat.clog_le_of_le_pow ((Nat.sub_le n 1).trans (Nat.lt_two_pow_self).le)

section sizes

variable {P : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {li : Bool} {γ : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The bounds of the region loop.** -/
theorem reg_sizes (hG : GoodEnv P) (hok : ChordTriplesOK (interiorModel (Qof P)) (Qof P) L)
    (hperm : E.Perm (List.range (2 * L.length)))
    (hsort : E.Pairwise (codeLe (interiorModel (Qof P)) (Qof P) L))
    (hdeg : (interiorModel (Qof P)).DegLe
      ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) 4)
    (hwt : (interiorModel (Qof P)).Semigranular
      ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) γ)
    (hli : li = true ↔ Mountain.LeftInside (Qof P)) :
    (∀ r, r < L.length + 1 → (ptsB li (Qof P) L E r).length ≤ 5 * γ + 8) ∧
      (L.length = 0 → P.n ≤ γ + 2) ∧
      (∀ r, r < L.length + 1 →
        ∀ j ∈ ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).region r).arcs,
          arcCnt P.n ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).arc j) ≤ γ + 2) := by
  have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hG.1
  have hDH : DistinctHeights (Qof P) := (goodShear_epsOf hG.2).2.1
  have hn : (Qof P).n = P.n := shear_n _ _
  have hn3 : 3 ≤ (Qof P).n := by have := hQ.1; omega
  by_cases hK : L.length = 0
  · have hL : L = [] := List.length_eq_zero_iff.1 hK
    subst hL
    have hE : E = [] := by
      simp_all
    have hnγ : (Qof P).n ≤ γ := n_le_of_empty hQ hE hwt
    refine ⟨fun r _ => ?_, fun _ => by omega, fun r _ j _ => ?_⟩
    · unfold ptsB
      rw [ite_eq_left hK, wlist_length, host_run_length (by omega)]
      omega
    · unfold arcCnt
      
      have := Nat.mod_lt (((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) [] E).arc j).e.edge +
        P.n - ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) [] E).arc j).s.edge)
        (show 0 < P.n by omega)
      omega
  · obtain ⟨-, -, -, reg, hRC, hCS, hAO, hRO, -⟩ := DownMath.isNF_build hQ hok hperm hsort
    have B : BaseCtx (Qof P) L E reg li := ⟨hQ, hDH, hok, hperm, hsort, by omega,
      ⟨hRC, hCS, hAO, hRO⟩, hli⟩
    have hR : ∀ r, r < L.length + 1 →
        r < (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions := fun r hr => by
      core_grind [BuildNF.buildNF, List.length_map, List.length_range]
    refine ⟨fun r hr => ?_, fun h => absurd h hK, fun r hr j hj => ?_⟩
    · unfold ptsB
      rw [ite_eq_right hK]
      have h1 := regPts_length_le B (hR r hr) hwt
      have h2 := hdeg _ (B.hregs.1.1 r (hR r hr))
      have h3 : ((interiorModel (Qof P)).deg
          ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P))
          (reg r) + 1) * γ ≤ 5 * γ := Nat.mul_le_mul_right _ (by omega)
      omega
    · have := arcCnt_le B (hR r hr) hwt hj
      simp_all

/-- **The completed chord list**: valid, and containing every vertex chord of `Q`. -/
theorem newLB_facts (hG : GoodEnv P) (hok : ChordTriplesOK (interiorModel (Qof P)) (Qof P) L)
    (hperm : E.Perm (List.range (2 * L.length)))
    (hsort : E.Pairwise (codeLe (interiorModel (Qof P)) (Qof P) L))
    (hli : li = true ↔ Mountain.LeftInside (Qof P)) :
    ChordTriplesOK (interiorModel (Qof P)) (Qof P) (L ++ newLB li (Qof P) L E) ∧
      chords (Qof P) ⊆ famL (interiorModel (Qof P)) (Qof P) (L ++ newLB li (Qof P) L E) := by
  have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hG.1
  have hDH : DistinctHeights (Qof P) := (goodShear_epsOf hG.2).2.1
  by_cases hK : L.length = 0
  · rw [newLB_zero li (Qof P) E hK]
    have hL : L = [] := List.length_eq_zero_iff.1 hK
    subst hL
    rw [List.nil_append]
    exact ⟨newL0_ok hQ hDH hli, newL0_full hQ hDH hli⟩
  · rw [newLB_pos li (Qof P) E (by omega)]
    obtain ⟨-, -, -, reg, hRC, hCS, hAO, hRO, -⟩ := DownMath.isNF_build hQ hok hperm hsort
    have B : BaseCtx (Qof P) L E reg li := ⟨hQ, hDH, hok, hperm, hsort, by omega,
      ⟨hRC, hCS, hAO, hRO⟩, hli⟩
    exact ⟨newL_ok B, newL_full B⟩

end sizes

/-! ## Counts and costs -/

/-- (I3) as a bound: `K ≤ cnt (2^p + 1)`. -/
theorem count_le {K c p b : ℕ} (h : K * 2 ^ b ≤ c * (2 ^ p + 2 ^ b)) : K ≤ c * (2 ^ p + 1) := by
  have h1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have h2 : c * (2 ^ p + 2 ^ b) ≤ c * (2 ^ p + 1) * 2 ^ b := by
    have : 2 ^ p + 2 ^ b ≤ (2 ^ p + 1) * 2 ^ b := by
      simp_all [Nat.add_mul, Nat.one_mul] 
    calc c * (2 ^ p + 2 ^ b) ≤ c * ((2 ^ p + 1) * 2 ^ b) := Nat.mul_le_mul_left _ this
      _ = c * (2 ^ p + 1) * 2 ^ b := by ring
  exact Nat.le_of_mul_le_mul_right (h.trans h2) (by omega)

/-- A count below the threshold is at most the sum of the counts below it. -/
theorem cnt_le_sum (cnt : ℕ → ℕ) {Λ lam : ℕ} (h : lam < Λ) :
    cnt lam ≤ ∑ i ∈ Finset.range Λ, cnt i :=
  Finset.single_le_sum (f := cnt) (fun _i _ => Nat.zero_le _) (Finset.mem_range.2 h)

theorem clog_le_self (m : ℕ) : Nat.clog 2 m ≤ m :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

/-- **The cost constant of the top level.** -/
def topK (κR κS κD κB Cc Γ : ℕ) : ℕ :=
  κR * (3 * Cc + 1) * (5 * Γ + 9) * (Γ + 3) + κS * (9 * Cc + 2) * (20 * Γ + 33) +
    (κD + κB) * (3 * Cc + 2) + 40

theorem topK_ge {κR κS κD κB Cc Γ : ℕ} (h : 1 ≤ κS) : 20 * Γ + 73 ≤ topK κR κS κD κB Cc Γ := by
  unfold topK
  have h1 : 1 ≤ κS * (9 * Cc + 2) := Nat.mul_le_mul h (by omega : 1 ≤ 9 * Cc + 2)
  have h2 : 20 * Γ + 33 ≤ κS * (9 * Cc + 2) * (20 * Γ + 33) := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- **The total cost is linear.** -/
theorem top_cost {n K K₂ A K' S₀ Cm Mb Cc Γ κR κS κD κB : ℕ} (hK : K ≤ Cc * (2 * n + 3))
    (hK₂ : K₂ ≤ 2 * n) (hA : A ≤ 2 * K + 1) (hK' : K' ≤ K + K₂) (hS₀ : S₀ ≤ 5 * Γ + 8)
    (hCm : Cm ≤ Γ + 2) (hMb : Mb ≤ 20 * Γ + 32) :
    16 * n + 30 + κR * (K + 1) * (S₀ + 1) * (Cm + 1) +
        κS * (K + K₂ + A + 1) * (Nat.clog 2 Mb + 1) + κD * (K + K₂ + 1) + κB * (K' + 1) ≤
      topK κR κS κD κB Cc Γ * (n + 1) := by
  have e : topK κR κS κD κB Cc Γ * (n + 1) =
      κR * ((3 * Cc + 1) * (n + 1)) * (5 * Γ + 9) * (Γ + 3) +
        κS * ((9 * Cc + 2) * (n + 1)) * (20 * Γ + 33) + κD * ((3 * Cc + 2) * (n + 1)) +
        κB * ((3 * Cc + 2) * (n + 1)) + 40 * (n + 1) := by
    unfold topK; ring
  have hX1 : K + 1 ≤ (3 * Cc + 1) * (n + 1) := by
    grind
  have hX2 : K + K₂ + A + 1 ≤ (9 * Cc + 2) * (n + 1) := by
    grind
  have hX3 : K + K₂ + 1 ≤ (3 * Cc + 2) * (n + 1) := by
    grind
  have hX4 : K' + 1 ≤ (3 * Cc + 2) * (n + 1) := by omega
  have t1 : κR * (K + 1) * (S₀ + 1) * (Cm + 1) ≤
      κR * ((3 * Cc + 1) * (n + 1)) * (5 * Γ + 9) * (Γ + 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hX1) (by omega)) (by omega)
  have hcl : Nat.clog 2 Mb + 1 ≤ 20 * Γ + 33 := by have := clog_le_self Mb; omega
  have t2 : κS * (K + K₂ + A + 1) * (Nat.clog 2 Mb + 1) ≤
      κS * ((9 * Cc + 2) * (n + 1)) * (20 * Γ + 33) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hX2) hcl
  have t3 : κD * (K + K₂ + 1) ≤ κD * ((3 * Cc + 2) * (n + 1)) := Nat.mul_le_mul_left _ hX3
  have t4 : κB * (K' + 1) ≤ κB * ((3 * Cc + 2) * (n + 1)) := Nat.mul_le_mul_left _ hX4
  omega

end

end DrvB.BTop

end Chazelle.Core
