/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/PathFractions.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.FiniteEuclidean

@[expose] public section

namespace OAI.EuclideanRamsey


noncomputable section



section Fractions
variable {G : Type*} {ι : Type*} [Group G]

def RightFraction (M : Submonoid (ι → G)) (z : ι → G) : Prop :=
  ∃ u ∈ M,∃ v ∈ M,z=u*v⁻¹

def HasDiagonal (M : Submonoid (ι → G)) : Prop := ∀ g : G,(fun _ => g)∈M

def PairInverse (M : Submonoid (ι → G)) : Prop :=
  ∀ i j : ι,∀ v∈M,∃ b∈M,b i=(v i)⁻¹ ∧ b j=(v j)⁻¹

lemma RightFraction.one (M : Submonoid (ι → G)) : RightFraction M 1 :=
  ⟨1,M.one_mem,1,M.one_mem,by simp⟩
lemma RightFraction.inv {M : Submonoid (ι → G)} {z : ι → G}
    (h : RightFraction M z) : RightFraction M z⁻¹ := by
  obtain ⟨u,hu,v,hv,rfl⟩ := h
  exact ⟨v,hv,u,hu,by group⟩
lemma RightFraction.conjugate {M : Submonoid (ι → G)} (hM : HasDiagonal M)
    {z : ι → G} (h : RightFraction M z) (g : G) :
    RightFraction M (fun i => g*z i*g⁻¹) := by
  obtain ⟨u,hu,v,hv,rfl⟩ := h
  refine ⟨(fun _ => g)*u,M.mul_mem (hM g) hu,(fun _ => g)*v,M.mul_mem (hM g) hv,?_⟩
  ext i
  simp
  group

variable [DecidableEq ι]

lemma conjugate_single (i : ι) (g h : G) :
    (fun j => g*(Pi.mulSingle i h : ι → G) j*g⁻¹)=Pi.mulSingle i (g*h*g⁻¹) := by
  ext j
  by_cases hj : j=i <;> simp [hj]

lemma single_conjugate (v : ι → G) (i : ι) (g : G) :
    v⁻¹*Pi.mulSingle i g = Pi.mulSingle i ((v i)⁻¹*g*v i)*v⁻¹ := by
  ext j
  by_cases hj : j=i <;> simp [hj]

lemma RightFraction.mul_single {M : Submonoid (ι → G)} (hM : HasDiagonal M)
    {z : ι → G} (hz : RightFraction M z) (i : ι) {g : G}
    (hg : RightFraction M (Pi.mulSingle i g)) : RightFraction M (z*Pi.mulSingle i g) := by
  obtain ⟨u,hu,v,hv,rfl⟩ := hz
  have hh := hg.conjugate hM (v i)⁻¹
  rw [conjugate_single,inv_inv] at hh
  obtain ⟨a,ha,b,hb,he⟩ := hh
  refine ⟨u*a,M.mul_mem hu ha,v*b,M.mul_mem hv hb,?_⟩
  rw [mul_assoc,single_conjugate,he]
  group

def singleFractions (M : Submonoid (ι → G)) (hM : HasDiagonal M) (i : ι) : Subgroup G where
  carrier := {g | RightFraction M (Pi.mulSingle i g)}
  one_mem' := by simp_all [RightFraction.one]
  mul_mem' {a b} ha hb := by
    simpa only [Set.mem_ofPred_eq, Pi.mulSingle_mul] using ha.mul_single hM i hb
  inv_mem' {a} ha := by
    simpa only [Set.mem_ofPred_eq, Pi.mulSingle_inv] using ha.inv

instance singleFractions_normal (M : Submonoid (ι → G)) (hM : HasDiagonal M) (i : ι) :
    (singleFractions M hM i).Normal where
  conj_mem g hg k := by
    change RightFraction M _
    simpa only [conjugate_single] using hg.conjugate hM k

lemma RightFraction.mul_pair {M : Submonoid (ι → G)} (hM : PairInverse M)
    {z t : ι → G} (hz : RightFraction M z) (ht : RightFraction M t)
    (i j : ι) (hs : ∀ l,l≠i → l≠j → t l=1) :
    RightFraction M (z*t) := by
  obtain ⟨u,hu,v,hv,rfl⟩ := hz
  obtain ⟨c,hc,d,hd,rfl⟩ := ht
  obtain ⟨b,hb,hi,hj⟩ := hM i j v hv
  have hcomm : Commute (v*b) (c*d⁻¹) := by
    ext l
    by_cases hli : l=i <;> by_cases hlj : l=j <;> simp_all
  refine ⟨u*b*c,M.mul_mem (M.mul_mem hu hb) hc,(v*b)*d,M.mul_mem (M.mul_mem hv hb) hd,?_⟩
  have he : u*v⁻¹ = (u*b)*(v*b)⁻¹ := by group
  rw [he,mul_assoc,hcomm.inv_left.eq]
  group
end Fractions


variable {G : Type*} {ι : Type*} [Group G]

structure GradedPaths (ι : Type*) (G : Type*) [Group G] where
  Holds : (ι → G) → ℕ → Prop
  diag : ∀ g,Holds (fun _ => g) 0
  mul : ∀ {u v m n},Holds u m → Holds v n → Holds (u*v) (m+n)
namespace GradedPaths
variable (P : GradedPaths ι G)
def monoid : Submonoid (ι → G) where
  carrier := {u | ∃ n,P.Holds u n}
  one_mem' := ⟨0,P.diag 1⟩
  mul_mem' := by rintro u v ⟨m,hm⟩ ⟨n,hn⟩; exact ⟨m+n,P.mul hm hn⟩
lemma diagonal : HasDiagonal P.monoid := fun g => ⟨0,P.diag g⟩

def BoundedFraction (z : ι → G) (c : ℕ) : Prop :=
  ∃ (u v : ι → G) (m n : ℕ),P.Holds u m ∧ P.Holds v n ∧ z=u*v⁻¹ ∧ m+n≤c
lemma bounded_exists {z : ι → G} (h : RightFraction P.monoid z) :
    ∃ c,P.BoundedFraction z c := by
  obtain ⟨u,⟨m,hm⟩,v,⟨n,hn⟩,he⟩ := h
  exact ⟨m+n,u,v,m,n,hm,hn,he,le_rfl⟩
lemma bounded_one : P.BoundedFraction 1 0 :=
  ⟨1,1,0,0,P.diag 1,P.diag 1,by simp,le_rfl⟩
lemma bounded_inv {z : ι → G} {c : ℕ} (h : P.BoundedFraction z c) :
    P.BoundedFraction z⁻¹ c := by
  obtain ⟨u,v,m,n,hm,hn,rfl,hc⟩ := h
  exact ⟨v,u,n,m,hn,hm,by group,by omega⟩
lemma bounded_conjugate {z : ι → G} {c : ℕ} (h : P.BoundedFraction z c) (g : G) :
    P.BoundedFraction (fun i => g*z i*g⁻¹) c := by
  obtain ⟨u,v,m,n,hm,hn,rfl,hc⟩ := h
  refine ⟨(fun _ => g)*u,(fun _ => g)*v,m,n,?_,?_,?_,hc⟩
  · simpa using P.mul (P.diag g) hm
  · simpa using P.mul (P.diag g) hn
  · ext i; simp; group
variable [DecidableEq ι]

lemma bounded_mul_single {z : ι → G} {c d : ℕ} (hz : P.BoundedFraction z c)
    (i : ι) {g : G} (hg : P.BoundedFraction (Pi.mulSingle i g) d) :
    P.BoundedFraction (z*Pi.mulSingle i g) (c+d) := by
  obtain ⟨u,v,m,n,hm,hn,rfl,hc⟩ := hz
  have hh := P.bounded_conjugate hg (v i)⁻¹
  rw [conjugate_single,inv_inv] at hh
  obtain ⟨a,b,k,l,hk,hl,he,hd⟩ := hh
  refine ⟨u*a,v*b,m+k,n+l,P.mul hm hk,P.mul hn hl,?_,by omega⟩
  rw [mul_assoc,single_conjugate,he]
  group

def singleCost (i : ι) (g : G) : ℕ := sInf {c | P.BoundedFraction (Pi.mulSingle i g) c}
lemma singleCost_bounded (i : ι) {g : G} (hg : g∈singleFractions P.monoid P.diagonal i) :
    P.BoundedFraction (Pi.mulSingle i g) (P.singleCost i g) :=
  Nat.sInf_mem (P.bounded_exists hg)
lemma singleCost_le (i : ι) {g : G} {c : ℕ} (hc : P.BoundedFraction (Pi.mulSingle i g) c) :
    P.singleCost i g ≤ c := Nat.sInf_le hc
lemma singleCost_one (i : ι) : P.singleCost i 1=0 := by
  apply Nat.eq_zero_of_le_zero
  apply P.singleCost_le
  simpa using P.bounded_one
lemma singleCost_inv (i : ι) (g : G) : P.singleCost i g⁻¹=P.singleCost i g := by
  unfold singleCost
  congr 1
  ext c
  simp
  constructor <;> intro h
  · simpa only [Pi.mulSingle_inv, inv_inv] using P.bounded_inv h
  · simpa only [Pi.mulSingle_inv] using P.bounded_inv h
lemma singleCost_conjugate (i : ι) (g k : G) :
    P.singleCost i (k*g*k⁻¹)=P.singleCost i g := by
  unfold singleCost
  congr 1
  ext c
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h
  · have hh := P.bounded_conjugate h k⁻¹
    rw [conjugate_single] at hh
    simpa [mul_assoc] using hh
  · simpa only [conjugate_single] using P.bounded_conjugate h k
lemma singleCost_mul (i : ι) {g h : G}
    (hg : g∈singleFractions P.monoid P.diagonal i) (hh : h∈singleFractions P.monoid P.diagonal i) :
    P.singleCost i (g*h)≤P.singleCost i g+P.singleCost i h := by
  apply P.singleCost_le
  rw [Pi.mulSingle_mul]
  exact P.bounded_mul_single (P.singleCost_bounded i hg) i (P.singleCost_bounded i hh)

lemma bounded_tuple [Fintype ι] (z : ι → G) (c : ι → ℕ)
    (h : ∀ i,P.BoundedFraction (Pi.mulSingle i (z i)) (c i)) :
    P.BoundedFraction z (∑ i,c i) := by
  have aux S : P.BoundedFraction (fun i => if i ∈ S then z i else 1) (∑ i ∈ S,c i) := by
    induction S using Finset.induction with
    | empty => simpa [Pi.one_def] using P.bounded_one
    | @insert i S hi ih =>
      have hh := P.bounded_mul_single ih i (h i)
      convert hh using 1
      · ext j
        by_cases hj : j=i <;> simp [hj, hi]
      · simp [hi, Nat.add_comm]
  simpa using aux Finset.univ
end GradedPaths
end

end OAI.EuclideanRamsey
