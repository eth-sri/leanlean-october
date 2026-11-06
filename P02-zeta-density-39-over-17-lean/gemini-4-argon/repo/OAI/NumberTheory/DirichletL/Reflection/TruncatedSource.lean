module
public import OAI.NumberTheory.DirichletL.Reflection.DyadicBox
public import OAI.NumberTheory.DirichletL.Reflection.HeightTail

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def retainedDyads (scale B : ℝ) : Finset (ℕ×ℕ×ℕ) :=
  (retainedDyadicBox scale B).filter (fun i => rawDyadicCenter scale i≤B)

lemma mem_retainedDyads (scale B : ℝ) (hs : 0<scale) (i : ℕ×ℕ×ℕ) :
    i∈retainedDyads scale B ↔ rawDyadicCenter scale i≤B := by
  simp only [retainedDyads,Finset.mem_filter]
  exact ⟨And.right,fun hi => ⟨center_mem_retainedDyadicBox scale B hs i hi,hi⟩⟩

lemma literalDyadicBlock_summable (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) (u : Eisˣ) :
    Summable (literalDyadicBlock G D s hc j S W X u) := by
  have hs := ((literalRawSeries_summable_norm G D s hc hN hbase hchar j hj S W lo hi hlo hWs hW X hX).of_norm).prod_factor u
  have hh := (dualDyadicIndexEquiv.symm.summable_iff.mpr hs).sigma
  apply hh.congr
  intro i
  simp only [tsum_fintype,Fintype.sum_prod_type,literalDyadicBlock,Function.comp_apply]
  rfl

lemma tsum_sub_finset_eq_tail {α : Type*} (f : α→ℂ) (hf : Summable f) (A : Finset α) :
    (∑' i,f i)-(∑ i∈A,f i)=∑' i,if i∉A then f i else 0 := by
  have hh := hf.sum_add_tsum_subtype_compl A
  have ht : (∑' x : {x // x∉A}, f x.val)=∑' i,if i∉A then f i else 0 := by
    calc
      _ = ∑' x, ({x | x∉A} : Set α).indicator f x := tsum_subtype {x | x∉A} f
      _ = _ := by
        apply tsum_congr
        intro i
        by_cases hi : i∈A <;> simp [hi]
  rw [ht] at hh
  exact eq_sub_of_add_eq' hh |>.symm
