module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSource

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialPhysicalReassembly
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialRayAttachment InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes

variable {ι:Type*}[DecidableEq ι](p:ι→ActualEisensteinCubic.O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem initialColumn_zero_common  Ψ  j d h  H 
     G U (hd:¬Disjoint G U):
    initialColumn p hp hcop hg Ψ j (∏i∈G,p i) d h H U=0:=by
  obtain ⟨i,hiG,hiU⟩:=Finset.not_disjoint_iff.mp hd
  have hm:rowCoprimeMask (fun i=>Ideal.span {p i}) U (j*∏i∈G,p i)=0:=by
    have hh:∃i∈U,j*∏k∈G,p k∈Ideal.span {p i}:=
      ⟨i,hiU,Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hiG) j)⟩
    simp only [rowCoprimeMask,ite_eq_left hh]
  simp only [initialColumn,hm,mul_zero,zero_mul]

theorem physicalTerm_zero_left_common  Ψ  j  σ 
     W₁ W₂  Φ  Z D m  G E V N M  h  ρ 
    (hd:¬Disjoint G (V∪N)):
    physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ=0:=by
  simp_all [physicalTerm, initialColumn_zero_common]

theorem physicalTerm_zero_right_common  Ψ  j  σ 
     W₁ W₂  Φ  Z D m  G E V N M  h  ρ 
    (hd:¬Disjoint G (V∪M)):
    physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ=0:=by
  simp_all [physicalTerm, initialColumn_zero_common]

private theorem missing_residual_common (pool G V N:Finset ι)
    (hN:N∈(pool\V).powerset)(hn:N∉((pool\G)\V).powerset):¬Disjoint G (V∪N):=by
  intro hd
  apply hn
  apply Finset.mem_powerset.mpr
  intro i hi
  have hh:=Finset.mem_sdiff.mp (Finset.mem_powerset.mp hN hi)
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hh.1,
    fun hG=>Finset.disjoint_left.mp hd hG (Finset.mem_union_right V hi)⟩,hh.2⟩

theorem rectangle_restore_common
     Ψ  j  σ  W₁ W₂  Φ 
     Z D m  pool G E V  h :
    (∑N∈((pool\G)\V).powerset,∑M∈((pool\G)\V).powerset,∑ρ:SecondRayIndex,
      physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ)=
    ∑N∈(pool\V).powerset,∑M∈(pool\V).powerset,∑ρ:SecondRayIndex,
      physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ:=by
  have hs:((pool\G)\V).powerset⊆(pool\V).powerset:=
    Finset.powerset_mono.mpr (Finset.sdiff_subset_sdiff Finset.sdiff_subset (Finset.Subset.refl _))
  calc
    _=∑N∈(pool\V).powerset,∑M∈((pool\G)\V).powerset,∑ρ:SecondRayIndex,
        physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ:=by
      apply Finset.sum_subset hs
      intro N hN hn
      apply Finset.sum_eq_zero
      intro M hM
      apply Finset.sum_eq_zero
      intro ρ hρ
      exact physicalTerm_zero_left_common p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m G E V N M h ρ
        (missing_residual_common pool G V N hN hn)
    _=_:=by
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_subset hs
      intro M hM hm
      apply Finset.sum_eq_zero
      intro ρ hρ
      exact physicalTerm_zero_right_common p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m G E V N M h ρ
        (missing_residual_common pool G V M hM hm)

def sourceCodes (pool:Finset ι)(T:Finset ActualEisensteinCubic.O):=
  pool.powerset.sigma (fun G=>G.powerset.sigma (fun _E=>(pool\G).powerset×ˢT))

def sourceOfCode (x:Σ _G:Finset ι,Σ _E:Finset ι,Finset ι×ActualEisensteinCubic.O):Source (ι:=ι) 0 where
  common:=x.1
  divisor:=x.2.1
  overlap:=x.2.2.1
  frequency:=x.2.2.2
  assigned:=Fin.elim0

omit [DecidableEq ι] in
theorem sourceOfCode_injective:Function.Injective (sourceOfCode (ι:=ι)):=by
  rintro ⟨G,E,V,h⟩ ⟨G',E',V',h'⟩ he
  simp_all [sourceOfCode]

def finiteSource (pool:Finset ι)(T:Finset ActualEisensteinCubic.O):=
  (sourceCodes pool T).image sourceOfCode

theorem finiteSource_sum {A:Type*}[AddCommMonoid A]
    (pool:Finset ι)(T:Finset ActualEisensteinCubic.O)(f:Source (ι:=ι) 0→A):
    (∑x∈finiteSource pool T,f x)=
      ∑G∈pool.powerset,∑E∈G.powerset,∑V∈(pool\G).powerset,∑h∈T,
        f ⟨G,E,V,h,Fin.elim0⟩:=by
  rw [finiteSource,Finset.sum_image (fun _ _ _ _ he=>sourceOfCode_injective he)]
  simp only [sourceCodes,Finset.sum_sigma,Finset.sum_product,sourceOfCode]

theorem mem_finiteSource  pool  T (x:Source (ι:=ι) 0):
    x∈finiteSource pool T ↔ x.common⊆pool ∧ x.divisor⊆x.common ∧
      x.overlap⊆pool\x.common ∧ x.frequency∈T:=by
  constructor
  · intro hx
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
    simp_all [sourceCodes, sourceOfCode]
  · rintro ⟨hG,hE,hV,hh⟩
    refine Finset.mem_image.mpr ⟨⟨x.common,x.divisor,x.overlap,x.frequency⟩,?_,?_⟩
    · simp_all [sourceCodes]
    · apply Source.ext <;> try rfl
      funext i
      exact Fin.elim0 i

theorem finiteSource_divisor (pool:Finset ι) T :
    ∀x∈finiteSource pool T,x.divisor⊆x.common:=by
  simp_all [mem_finiteSource]

theorem finiteSource_nonzero (pool:Finset ι) T (hT:(0:ActualEisensteinCubic.O)∉T):
    ∀x∈finiteSource pool T,x.frequency≠0:=by
  grind [mem_finiteSource]

theorem finite_physical_reassembly
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
     pool  freqT  Ψ  j  σ 
     W  Φ  Z D m :
    (∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
      if Disjoint U T then ∑E∈G.powerset,∑h∈freqT,
        initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E h else 0)=
    physicalBlock p hp hcop hg (pointSource pool (finiteSource pool freqT))
      (fun _=>1) Ψ j σ (fun x=>star (W x)) W Φ Z D m:=by
  unfold physicalBlock
  rw [pointSource_sum,finiteSource_sum]
  simp only [one_mul]
  apply Finset.sum_congr rfl
  intro G hG
  have hif (U T:Finset ι):
      (if Disjoint U T then ∑E∈G.powerset,∑h∈freqT,
        initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E h else 0)=
      ∑E∈G.powerset,∑h∈freqT,if Disjoint U T then
        initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E h else 0:=by
    split_ifs <;> simp
  simp_rw [hif,Finset.sum_comm (s:=(pool\G).powerset) (t:=G.powerset)]
  apply Finset.sum_congr rfl
  intro E hE
  simp_rw [Finset.sum_comm (s:=(pool\G).powerset) (t:=freqT)]
  apply Finset.sum_congr rfl
  intro h hh
  rw [original_ray_common_insertion p hp hcop hg hinj]
  apply Finset.sum_congr rfl
  intro V hV
  solve_by_elim [rectangle_restore_common, star]

end SevenEighths.InverseInitialPhysicalReassembly

end

end OAI
