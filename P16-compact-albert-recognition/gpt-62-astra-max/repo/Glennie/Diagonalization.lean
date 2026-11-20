module
public import Glennie.Compact.Flows
public import Glennie.Obligations
@[expose] public section
namespace Glennie
noncomputable section

private def testDiagonal : Albert := ⟨1,0,-1,0,0,0⟩
private theorem test_mul (x : Albert) : jordan testDiagonal x =
    ⟨x.d0,0,-x.d2,(1/2:ℝ) • x.o01,0,-(1/2:ℝ) • x.o12⟩ := by
  ext <;> simp [testDiagonal,jordan_d0,jordan_d1,jordan_d2,jordan_o01,jordan_o02,jordan_o12,
    octDot_coordinates,octMul,octConj,smul_eq_mul] <;> ring

/-- At a maximum of the linear functional B(diag(1,0,−1), ·), the derivative
along the inner commutator with the maximizing element is a positive weighted
sum of its three off-diagonal squared norms. Thus all three vanish. -/
theorem native_diagonalization (x : Albert) : ∃ g : CompactAutomorphism, IsDiagonal (g.equiv x) := by
  let f := nativeInnerContinuous testDiagonal
  obtain ⟨g,hg⟩ := orbit_max f f.continuous x
  let y := g.equiv x
  have v := Compact.Flows.stationary f y testDiagonal y (fun k => hg (k.comp g))
  have read (z : Albert) : f z = z.d0-z.d2 := by change inner testDiagonal z = _; simp [inner_coordinates,testDiagonal,octDot_coordinates,sub_eq_add_neg]
  have sum : octNormSq y.o01 + 4*octNormSq y.o02 + octNormSq y.o12 = 0 := by
    rw [read, Compact.innerDer,test_mul,test_mul] at v
    simp [jordan_d0,jordan_d2,octDot_coordinates,octNormSq,Quaternion.normSq_def',smul_eq_mul] at v ⊢
    linarith
  refine ⟨g,?_⟩; change y.o01 = 0 ∧ y.o02 = 0 ∧ y.o12 = 0
  simp only [← octNormSq_eq_zero]; have := octNormSq_nonneg y.o01
  have := octNormSq_nonneg y.o02; have := octNormSq_nonneg y.o12; grind

end
end Glennie
