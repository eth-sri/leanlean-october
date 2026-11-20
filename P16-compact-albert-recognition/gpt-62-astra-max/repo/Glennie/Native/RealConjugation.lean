module
public import Glennie.Native.AlgebraLaws
public import Glennie.Obligations

/-! Transpositions of the labeled axes. An upper-triangular slot crossing the
diagonal is conjugated. These two involutions generate the coordinate permutations. -/
@[expose] public section
namespace Glennie
noncomputable section
set_option maxHeartbeats 1200000
def transposeAxes : Bool → Albert → Albert
  | false,x => ⟨x.d1,x.d0,x.d2,octConj x.o01,x.o12,x.o02⟩
  | true,x => ⟨x.d2,x.d1,x.d0,octConj x.o12,octConj x.o02,octConj x.o01⟩
def flipEquiv (b : Bool) : Albert ≃ₗ[ℝ] Albert where
  toFun := transposeAxes b
  invFun := transposeAxes b
  left_inv x := by cases b <;> simp [transposeAxes]
  right_inv x := by cases b <;> simp [transposeAxes]
  map_add' x y := by cases b <;> simp [transposeAxes,octConj_add] <;> rfl
  map_smul' r x := by cases b <;> simp [transposeAxes,octConj_smul] <;> rfl
def flipAut (b : Bool) : CompactAutomorphism where
  equiv := flipEquiv b
  map_trace x := by cases b <;> simp [flipEquiv,transposeAxes,trace] <;> ring
  map_jordan x y := by
    change transposeAxes b (jordan x y) = jordan (transposeAxes b x) (transposeAxes b y)
    have cd (u v : Octonion) : octDot (octConj u) (octConj v) = octDot u v := by simp [octDot_coordinates,octConj]
    cases b <;> apply Albert.ext <;>
      simp [transposeAxes,jordan_d0,jordan_d1,jordan_d2,jordan_o01,jordan_o02,jordan_o12,
        octConj_add,octConj_smul,octConj_mul,cd,add_comm,add_left_comm,add_assoc]

abbrev realSwap01Automorphism := flipAut false
abbrev realSwap02Automorphism := flipAut true

theorem realSwap01_coordinates (x : Albert) : realSwap01Automorphism.equiv x =
    ⟨x.d1,x.d0,x.d2,octConj x.o01,x.o12,x.o02⟩ := rfl
theorem realSwap02_coordinates (x : Albert) : realSwap02Automorphism.equiv x =
    ⟨x.d2,x.d1,x.d0,octConj x.o12,octConj x.o02,octConj x.o01⟩ := rfl
end
end Glennie
