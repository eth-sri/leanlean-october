module

public import Erdos408.OneSided.Moment.Phased.Edge
public import Erdos408.OneSided.Moment.Phased.Rows

/-!
# Edge rows with prescribed births

PD `mem:edge-atoms`: an edge row with prescribed fresh labels. Fix all labels first; the
targets then contribute the kernel bound of `sum_crudeKernel_le` uniformly in the labels. A
group whose label is prescribed to be the fresh prime `p` contributes the atom `ν(p)`, and a
free group contributes `∑_p (2 S(p, ·) + ν(p)) ≤ 2B + 4`.

* `memSize_chainEdgeOut_le`: an edge stores at most `K` particles, so the memory grows by at
  most `K`.
* `sum_chainEdge_pres_le`: the weighted row sums of the edge against the prescription
  indicators `∏_i [β_i = π_i]` of its labels, with weight `v₀^{size}`, are at most
  `v₀^K 2^K (2B + 4)^K 16 (1 + 52 L^{3A₀}) ∏_i atomCost(π_i) v₀^{size}`.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

section EdgeAtoms

variable {q A₀ x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

/-- An edge stores at most `K` particles: the memory after the edge has size at most the size
before it plus `K`. -/
theorem memSize_chainEdgeOut_le (s : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r) :
    memSize (chainEdgeOut x d Y d₀ u v r B s c).2.2.1 ≤ memSize s.2.2.1 + K := by
  classical
  unfold chainEdgeOut
  split_ifs with hv
  · -- removals only decrease the size, and the stored particles number at most `|S| ≤ K`
    change memSize (edgeMem s c) ≤ _
    have hstored : ∑ xp : Particle x d, (c.2.1.filter fun i => edgeStored s c i = xp.1).card ≤
        K := by
      simp only [card_filter]
      rw [sum_comm]
      calc ∑ i ∈ c.2.1, ∑ xp : Particle x d, (if edgeStored s c i = xp.1 then 1 else 0)
          ≤ ∑ _i ∈ c.2.1, 1 := sum_le_sum fun i _ => by
            rw [← card_filter]
            exact card_le_one.2 fun a ha b hb =>
              Subtype.ext ((mem_filter.1 ha).2.symm.trans (mem_filter.1 hb).2)
        _ = c.2.1.card := by simp
        _ ≤ K := card_le_univ _ |>.trans_eq (Fintype.card_fin K)
    calc memSize (edgeMem s c)
        ≤ ∑ xp : Particle x d,
            (s.2.2.1 xp + (c.2.1.filter fun i => edgeStored s c i = xp.1).card) :=
          sum_le_sum fun xp _ => by unfold edgeMem; omega
      _ ≤ memSize s.2.2.1 + K := by
          rw [sum_add_distrib]
          exact Nat.add_le_add_left hstored _
  · exact Nat.le_add_right _ _

/-- **The edge rows with prescribed labels** (PD `mem:edge-atoms`): with weight `v₀^{size}`,
the absolute edge coefficients against `∏_i [β_i = π_i]` sum to at most
`v₀^K 2^K (2B + 4)^K 16 (1 + 52 L^{3A₀}) ∏_i atomCost(π_i)` times the weight of the source. A
group prescribed to the prime `p` is a fresh draw of `p`, of weight `ν(p)`. -/
theorem sum_chainEdge_pres_le (hq : 0 < q) (hq₁ : q < 1) (hd₀ : 0 < d₀) (hY : 1 ≤ Y)
    (hU : 0 < d₀ * Y * d.Hm) (hL : 0 < Real.log x) (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hνi : ∀ i, ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 4)
    (hV : ∀ i, ∀ p ∈ band x (d.a i), 1 / 2 ≤ primeMass x d p) {v₀ c₀ : ℝ} (hv₀ : 1 ≤ v₀)
    (hc₀ : 1 ≤ c₀) (π : Fin K → Option ℕ) (s : ChainState x d Y d₀ u v r B) :
    ∑ c ∈ edgeChoices x d Y d₀ u v r, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖ *
        (∏ i, presInd (π i) (if (c.2.2.2.1 i).2 then none else some (c.2.2.2.1 i).1)) *
        v₀ ^ memSize (chainEdgeOut x d Y d₀ u v r B s c).2.2.1 ≤
      v₀ ^ K * 2 ^ K * (2 * B + 4) ^ K * (16 * (1 + 52 * Real.log x ^ (3 * A₀))) *
        (∏ i, atomCost c₀ (primeWeight q x d N) (π i)) * v₀ ^ memSize s.2.2.1 := by
  classical
  let f (i : Fin K) (pf : ℕ × Bool) := presInd (π i) (if pf.2 then none else some pf.1)
  have hlab : ∀ i, ∑ pf ∈ band x (d.a i) ×ˢ (univ : Finset Bool),
      edgeLabelWeight q x d N s.2.2.1 pf * f i pf ≤ (2 * B + 4) * atomCost c₀ (primeWeight q x d N) (π i) := by
    intro i
    cases hπ : π i with
    | none =>
      simpa only [f, hπ, presInd_none, mul_one, atomCost, Option.elim] using sum_edgeLabelWeight_le s i (hνi i)
    | some p =>
      -- only the fresh draw of `p` survives
      simp only [f, hπ, presInd_some, atomCost, Option.elim]
      rw [sum_product]
      simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false,
        reduceCtorEq, mul_zero, Option.some.injEq, edgeLabelWeight, zero_add, mul_ite, mul_one,
        sum_ite_eq']
      have h1 : (1 : ℝ) ≤ (2 * B + 4) * c₀ :=
        one_le_mul_of_one_le_of_one_le (by linarith [(B.cast_nonneg : (0 : ℝ) ≤ B)]) hc₀
      calc (if p ∈ band x (d.a i) then primeWeight q x d N p else 0)
          ≤ primeWeight q x d N p := by
            split_ifs
            exacts [le_rfl, hν p]
        _ ≤ (2 * B + 4) * c₀ * primeWeight q x d N p := le_mul_of_one_le_left (hν p) h1
        _ = (2 * B + 4) * (c₀ * primeWeight q x d N p) := mul_assoc _ _ _
  have h := sum_norm_chainEdgeCoef_weighted_le (A₀ := A₀) hq hq₁ hd₀ hY hU hL hν hV s f
    (fun i => atomCost c₀ (primeWeight q x d N) (π i)) (fun i pf => presInd_nonneg _ _) hlab
  let W := v₀^(memSize s.2.2.1+K)
  calc
    _ ≤ ∑ c ∈ edgeChoices x d Y d₀ u v r, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖ *
        (∏ i, f i (c.2.2.2.1 i)) * W := sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hv₀ (memSize_chainEdgeOut_le s c))
        (mul_nonneg (norm_nonneg _) (prod_nonneg fun i _ => presInd_nonneg _ _))
    _ ≤ _ := by
      rw [← sum_mul]
      refine (mul_le_mul_of_nonneg_right h (show 0 ≤ W from pow_nonneg (by linarith) _)).trans_eq ?_
      dsimp only [W]
      rw [pow_add]
      ring

end EdgeAtoms

end Erdos408.OneSided
