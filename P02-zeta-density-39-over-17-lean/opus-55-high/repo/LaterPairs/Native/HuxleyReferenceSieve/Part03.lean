module
public import LaterPairs.Native.HuxleyReferenceSieve.Part02
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth
open Filter
open Polynomial
open Set
open scoped Classical
open scoped ContDiff
open scoped FourierTransform
open scoped Topology
noncomputable section
namespace TaoTrudgianYang2025.HuxleyRationalPhase




                                                                
                                                                          
                                                                    
            
theorem positive_difference_minimal_anchor_complement_count
    (S : Finset ℤ) (F : ℝ → ℝ) (anchor : ℤ → ℚ)
    (N : ℕ) (s : ℝ) {σ c J η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ i∈S, s+(N:ℝ)*i∈Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun i : ℤ => s+(N:ℝ)*i
    let delta := c/(64*σ*R^2)
    let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
    (∀ i∈S, (anchor i:ℝ)∈Ioo (h (t i)-delta) (h (t i)+delta) ∧
      ∀ a : ℚ, (a:ℝ)∈Ioo (h (t i)-delta) (h (t i)+delta) → (anchor i).den ≤ a.den) →
    ∀ (Q Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 0 ≤ Bmajor →
    let Bad := S.filter (fun i => ¬ (Acut*(anchor i).den ≤ Q ∧
      Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i).den))
    let Dlow := Bmajor*R^2/(c*(Q:ℝ))
    let Khigh := Q/Acut+1
    let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
    let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
      Dlow*(2*(Vbound+delta)*Dlow+1)
    (Bad.card:ℝ) ≤ Cost ∧
      ∀ H : ℤ → ℕ, (∀ i∈S, H i ≤ N) →
        (∑ i∈Bad,(H i:ℝ)) ≤ (N:ℝ)*Cost := by
  classical
  intro f h t delta Vbound hanchors Q Acut Bmajor hAcut hAQ hBmajor
    Bad Dlow Khigh Dhigh Cost
  pm_1803
  have hQ : 0 < Q := by omega
  pm_2141
  have hApos : 0 < Acut := by omega
  pm_2150
  pm_82 hV Vbound
  pm_82 hDlow Dlow
  have hnear i (hi : i∈S) : |(anchor i:ℝ)-h (t i)| ≤ delta := by
    have hh := (hanchors i hi).1
    exact abs_le.mpr ⟨by linarith only [hh.1],by linarith only [hh.2]⟩
  have hinj := positive_difference_near_anchor_injective S F anchor N s
    hσ hc hη hηmax hy hf hnegative hT hM hN hR hphase hpoints hnear
  pm_1682
  have hhigh : (High.card:ℝ) ≤ 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)) := by
    exact (positive_difference_actual_minimal_anchor_sharp_tail S F anchor N s
      hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM hN hR hphase hpoints
      (fun i hi => (hanchors i hi).2) Khigh hK).1
  have hscale2 : T/M^2=M/((N:ℝ)*R^2) := by
    pm_1804
    nlinarith only [hphase]
  have hvalues i (hi : i∈S) : |(anchor i:ℝ)| ≤ Vbound+delta := by
    pm_1249
    have he : (3*J/σ)*T/(2*M^2)=Vbound := by
      calc
        _ = (3*J/(2*σ))*(T/M^2) := by ring
        _ = Vbound := by rw [hscale2]; dsimp only [Vbound]; ring
    rw [he] at hh
    calc
      |(anchor i:ℝ)| = |((anchor i:ℝ)-h (t i))+h (t i)| := by rw [sub_add_cancel]
      _ ≤ |(anchor i:ℝ)-h (t i)|+|h (t i)| := abs_add_le _ _
      _ ≤ delta+Vbound := add_le_add (hnear i hi) hh
      _ = Vbound+delta := by ring
  pm_1681
  have hlow : (Low.card:ℝ) ≤ Dlow*(2*(Vbound+delta)*Dlow+1) := by
    pm_1680
  pm_1679



                                                                  
                                                                      
                                                                  
private theorem tagged_cost_source_scale
    {a N C D Q L cost : ℝ}
    (ha : 0 ≤ a) (hN : 0 < N) (hQ : 0 < Q)
    (hcost : cost ≤ C*(D/(N*Q))*L) :
    a*N*cost ≤ a*C*(D/Q)*L := by
  calc
    _ ≤ a*N*(C*(D/(N*Q))*L) :=
      mul_le_mul_of_nonneg_left hcost (mul_nonneg ha hN.le)
    _ = _ := by field_simp

private theorem tagged_anchor_complement_grouped_count
    {ι : Type*} [DecidableEq ι] (Y : Finset ι) (S : ι → Finset ℤ)
    (F : ℝ → ℝ) (y : ι → ℝ) (anchor : ι → ℤ → ℚ)
    (N : ℕ) (s : ℝ) {σ c J η T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : ∀ i∈Y, y i∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ i∈Y, ∀ k∈S i, s+(N:ℝ)*k∈Icc M (2*M))
    (hdisjoint : ∀ i∈Y, ∀ j∈Y, i≠j → y i=y j → Disjoint (S i) (S j)) :
    let f := fun u w => T*(F (w/M)-F (w/M+η*u))/(σ*η)
    let h := fun u w => iteratedDeriv 2 (f u) w/2
    let t := fun k : ℤ => s+(N:ℝ)*k
    let delta := c/(64*σ*R^2)
    let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
    (∀ i∈Y, ∀ k∈S i,
      (anchor i k:ℝ)∈Ioo (h (y i) (t k)-delta) (h (y i) (t k)+delta) ∧
      ∀ a : ℚ, (a:ℝ)∈Ioo (h (y i) (t k)-delta) (h (y i) (t k)+delta) →
        (anchor i k).den ≤ a.den) →
    ∀ (Q Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 0 ≤ Bmajor →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good : ι × ℤ → Prop := fun p => Acut*(anchor p.1 p.2).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor p.1 p.2).den
      let Dlow := Bmajor*R^2/(c*(Q:ℝ))
      let Dhigh := 64*σ*R^2/(c*((Q/Acut+1:ℕ):ℝ))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ((Sall.filter (fun p => ¬ Good p)).card:ℝ) ≤ ((Y.image y).card:ℝ)*Cost ∧
      ∀ H : ι → ℤ → ℕ, (∀ i∈Y, ∀ k∈S i, H i k ≤ N) →
        (∑ p∈Sall.filter (fun p => ¬ Good p),(H p.1 p.2:ℝ)) ≤
          ((Y.image y).card:ℝ)*(N:ℝ)*Cost := by
  classical
  intro f h t delta Vbound hanchors Q Acut Bmajor hA hAQ hB Sall Good Dlow Dhigh Cost
  let Phases := Y.image y
  let P := Sall.filter (fun p => ¬ Good p)
  let Grid := fun u => (Y.filter (fun i => y i=u)).biUnion S
  have hgrid u k : k∈Grid u ↔ ∃ i∈Y, y i=u ∧ k∈S i := by
    constructor
    · intro hk
      obtain ⟨i,hi,hk⟩ := Finset.mem_biUnion.mp hk
      exact ⟨i,(Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2,hk⟩
    · rintro ⟨i,hi,hu,hk⟩
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hu⟩,hk⟩
  let ag := fun u k => if hh : ∃ i∈Y, y i=u ∧ k∈S i then
    anchor (Classical.choose hh) k else (0:ℚ)
  have hag i (hi : i∈Y) k (hk : k∈S i) : ag (y i) k=anchor i k := by
    have hex : ∃ j∈Y, y j=y i ∧ k∈S j := ⟨i,hi,rfl,hk⟩
    dsimp only [ag]
    rw [dite_eq_left hex]
    have hh := Classical.choose_spec hex
    have he : Classical.choose hex=i := by
      by_contra hne
      exact Finset.disjoint_left.mp
        (hdisjoint _ hh.1 i hi hne hh.2.1) hh.2.2 hk
    rw [he]
  have hmem p : p∈Sall ↔ p.1∈Y ∧ p.2∈S p.1 := by
    pm_5393 hp p
    · rintro ⟨hi,hk⟩
      exact Finset.mem_biUnion.mpr ⟨p.1,hi,Finset.mem_image.mpr ⟨p.2,hk,rfl⟩⟩
  have hGcount u (hu : u∈Phases) :
      ((Grid u).filter (fun k => ¬ (Acut*(ag u k).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(ag u k).den))).card ≤ (Cost:ℝ) := by
    have hyp : u∈Icc (1:ℝ) 2 := by
      pm_386 i hi hu hy
    have hpts k (hk : k∈Grid u) : t k∈Icc M (2*M) := by
      pm_7105 _hui
      exact hpoints i hi k hk
    have hanc k (hk : k∈Grid u) :
        (ag u k:ℝ)∈Ioo (h u (t k)-delta) (h u (t k)+delta) ∧
        ∀ a : ℚ, (a:ℝ)∈Ioo (h u (t k)-delta) (h u (t k)+delta) →
          (ag u k).den ≤ a.den := by
      pm_7105 hui
      rw [←hui,hag i hi k hk]
      exact hanchors i hi k hk
    exact (positive_difference_minimal_anchor_complement_count (Grid u) F (ag u) N s
      hσ hc hJ hη hηmax hyp hf hbound htests hnegative hT hM hN hR hphase
      hpts hanc Q Acut Bmajor hA hAQ hB).1
  have hfiber u (hu : u∈Phases) :
      ((P.filter (fun p => y p.1=u)).card:ℝ) ≤ Cost := by
    let V := P.filter (fun p => y p.1=u)
    have hdata p (hp : p∈V) : p.1∈Y ∧ p.2∈S p.1 ∧ ¬ Good p ∧ y p.1=u := by
      pm_8447 hp hpP
      have hm := (hmem p).mp hpP.1
      exact ⟨hm.1,hm.2,hpP.2,hh.2⟩
    have hinj : Set.InjOn Prod.snd (V:Set (ι × ℤ)) := by
      intro p hp q hq he
      pm_268 hpS hdata p hp hqS q hq
      have hij : p.1=q.1 := by
        by_contra hne
        exact Finset.disjoint_left.mp
          (hdisjoint p.1 hpS.1 q.1 hqS.1 hne (hpS.2.2.2.trans hqS.2.2.2.symm))
          hpS.2.1 (by rw [he]; exact hqS.2.1)
      exact Prod.ext hij he
    have hsub : V.image Prod.snd ⊆ (Grid u).filter (fun k =>
        ¬ (Acut*(ag u k).den ≤ Q ∧ Bmajor*R^2 ≤ c*(Q:ℝ)*(ag u k).den)) := by
      pm_2532 k hk p hp
      have hh := hdata p hp
      refine Finset.mem_filter.mpr ⟨(hgrid u p.2).mpr ⟨p.1,hh.1,hh.2.2.2,hh.2.1⟩,?_⟩
      rw [←hh.2.2.2,hag p.1 hh.1 p.2 hh.2.1]
      exact hh.2.2.1
    have hh := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hGcount u hu)
    rwa [Finset.card_image_of_injOn hinj] at hh
  have hcard : (P.card:ℝ) ≤ (Phases.card:ℝ)*Cost := by
    have he : (P.card:ℝ)=∑ u∈Phases,((P.filter (fun p => y p.1=u)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise
        (fun p hp => Finset.mem_image_of_mem y ((hmem p).mp (Finset.mem_filter.mp hp).1).1)
    calc
      _ = _ := he
      _ ≤ ∑ _u∈Phases,Cost := Finset.sum_le_sum hfiber
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  refine ⟨hcard,?_⟩
  intro H hH
  pm_491 hNp N
  calc
    (∑ p∈P,(H p.1 p.2:ℝ)) ≤ ∑ _p∈P,(N:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := (hmem p).mp (Finset.mem_filter.mp hp).1
      exact Nat.cast_le.mpr (hH p.1 hh.1 p.2 hh.2)
    _ = (N:ℝ)*(P.card:ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
    _ ≤ (N:ℝ)*((Phases.card:ℝ)*Cost) := mul_le_mul_of_nonneg_left hcard hNp
    _ = _ := by ring

                                                                       
                                                                       
                                                                     
                                                       
private theorem strong_anchor_cutoff_dense
    (Acut Q d : ℕ) {σ c R Bmajor : ℝ}
    (hσ : 0 < σ) (hR : 0 < R)
    (hA : 768 ≤ Acut) (hB : 24576*σ ≤ Bmajor)
    (hcut : Acut*d ≤ Q) (hlow : Bmajor*R^2 ≤ c*(Q:ℝ)*d) :
    256*(d:ℝ) ≤ (Q:ℝ)/3 ∧
      ∀ eps : ℝ, c/(64*σ*R^2) ≤ eps →
        256 ≤ 2*eps*((Q:ℝ)/3)*d := by
  have hcut' : (768:ℝ)*d ≤ Q := by
    exact_mod_cast (Nat.mul_le_mul_right d hA).trans hcut
  have hraw := (mul_le_mul_of_nonneg_right hB (sq_nonneg R)).trans hlow
  have hdelta : 256 ≤ 2*(c/(64*σ*R^2))*((Q:ℝ)/3)*d := by
    have hh : (256:ℝ) ≤ c*(Q:ℝ)*d/(96*σ*R^2) := by
      apply (le_div_iff₀ (by positivity : 0 < 96*σ*R^2)).mpr
      nlinarith only [hraw]
    convert hh using 1
    ring
  refine ⟨by linarith only [hcut'],?_⟩
  intro eps heps
  apply hdelta.trans
  gcongr


                                                                            
                                                                             
theorem positive_difference_tagged_gap_controlled_complement_fourier
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (Y : Finset ι) (F : ℝ → ℝ)
      (N : ℕ) (s : ℤ) (H : ι → ℤ → ℕ)
      (η T M R U : ℝ) (y x₁ x₂ : ι → ℝ),
      1 ≤ N → (∀ i∈Y, ∀ k, H i k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ i∈Y, y i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      (∀ i∈Y, x₁ i∈Icc M (2*M)) → (∀ i∈Y, x₂ i∈Icc M (2*M)) →
      (∀ i∈Y, ∀ j∈Y, i≠j → y i=y j → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      (∀ i∈Y, U/(4*R^2) ≤ h i (x₂ i)-h i (x₁ i) ∧
        h i (x₂ i)-h i (x₁ i) ≤ 7*U/(2*R^2)) →
      ∃ (S : ι → Finset ℤ) (anchor : ι → ℤ → ℚ) (za : ι → ℤ → ℝ),
        (∀ i∈Y,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      ∀ (Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 128*σ ≤ Bmajor →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => Acut*(anchor i.1 i.2).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      let Dlow := Bmajor*R^2/(c*(Q:ℝ))
      let Khigh := Q/Acut+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Dlog := 64*σ*R^2/(c*((Q:ℝ)/Acut))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ∃ (r : ι × ℤ → ℚ) (z : ι × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      (768 ≤ Acut → 24576*σ ≤ Bmajor →
        ∀ i∈G, 256*((anchor i.1 i.2).den:ℝ) ≤ (Q:ℝ)/3 ∧
          ∀ eps : ℝ, delta ≤ eps → 256 ≤ 2*eps*((Q:ℝ)/3)*(anchor i.1 i.2).den) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
      let ℓ := fun i => deriv (f i.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
      let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
      let Cerror := (Acut:ℝ)*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c)
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤ C*(((Y.image y).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤
          C*(((Y.image y).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)) := by
  pc_262 positive_difference_tagged_gap_dyadic_source_fourier_cutoffs
  intro ι Y F N s H η T M R U y x₁ x₂ hN hH hη hηmax hy hT hM hR hU
    hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂
    hGapSep f h t L delta Vbound hgap
  obtain ⟨S,anchor,za,hinfo,hfourier⟩ :=
    hentry ι Y F N s H η T M R U y x₁ x₂ hN hH hη hηmax hy hT hM hR hU
      hf hbound hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂ hgap
  pm_119 S anchor za hinfo
  intro Q hQ hQN Acut Bmajor hAcut hAQ hBmajor Sall Good G Dlow Khigh Dhigh Dlog Cost
  have hB0 : 0 ≤ Bmajor := (show 0 ≤ 128*σ by positivity).trans hBmajor
  pm_1807
  have hpoints i (hi : i∈Y) k (hk : k∈S i) : t k∈Icc M (2*M) := by
    pm_8794 hh i hi hk
    constructor <;> linarith only [hh.1,hh.2,(hx₁ i hi).1,(hx₂ i hi).2,hNp]
  have hanchors i (hi : i∈Y) k (hk : k∈S i) := ((hinfo i hi).2.1 k hk).2.2.2
  have hdisjoint i (hi : i∈Y) j (hj : j∈Y) (hne : i≠j) (hye : y i=y j) :
      Disjoint (S i) (S j) := by
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    pm_8794 hai i hi hki
    pm_8794 haj j hj hkj
    rcases hGapSep i hi j hj hne hye with hij | hji
    pm_7671 hij
    pm_7671 hji
  have hgroup := tagged_anchor_complement_grouped_count Y S F y anchor N (s:ℝ)
    hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM
    (show 0 < N by omega) hR hphase hpoints hdisjoint hanchors
    Q Acut Bmajor hAcut hAQ hB0
  have hweight : (∑ i∈Sall.filter (fun i => ¬ Good i),(H i.1 i.2:ℝ)) ≤
      ((Y.image y).card:ℝ)*(N:ℝ)*Cost :=
    hgroup.2 H (fun i hi k _ => hH i hi k)
  obtain ⟨r,z,hr,hzg,hcenter,hcompletion⟩ := hfourier Q hQN Acut Bmajor hAcut hBmajor
  have hdense : 768 ≤ Acut → 24576*σ ≤ Bmajor →
      ∀ i∈G, 256*((anchor i.1 i.2).den:ℝ) ≤ (Q:ℝ)/3 ∧
        ∀ eps : ℝ, delta ≤ eps → 256 ≤ 2*eps*((Q:ℝ)/3)*(anchor i.1 i.2).den := by
    intro hAstrong hBstrong i hi
    exact strong_anchor_cutoff_dense Acut Q (anchor i.1 i.2).den hσ hR
      hAstrong hBstrong (Finset.mem_filter.mp hi).2.1 (Finset.mem_filter.mp hi).2.2
  pm_211 r z hr hzg hdense hcenter
  dsimp only
  intro K₀ _ hK₀
  pm_205 v hv k hfour hcompletion K₀ hK₀
  refine ⟨v,hv,k,?_⟩
  let m := fun i => round (z i)
  let A := fun i => (L i.2-m i).toNat
  let q := fun i => (r i).den
  let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
  let ℓ := fun i => deriv (f i.1) (m i)
  pm_2254
  let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
  let stretch := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
  let K := fun i => -2*μ i*(stretch i)^3
  pm_1683 K τ
  let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
  let Cerror := (Acut:ℝ)*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c)
  have hbase : (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤ C*(((Y.image y).card:ℝ)*(N:ℝ)*Cost+FourierCost) := by
    apply hfour.trans
    dsimp only [FourierCost]
    rw [←add_assoc (((Y.image y).card:ℝ)*(N:ℝ)*Cost)]
    gcongr
  refine ⟨hbase,?_⟩
  intro hRQ hNR
  have hcost : Cost ≤ Cerror*(M*R/((N:ℝ)*Q))*(2+Real.log (Dlog+1)) :=
    huxley_anchor_complement_source_scale Q Acut
      hσ hc hJ hM hNp hR hAcut hAQ hB0 hRQ hNR
  have hscaled : ((Y.image y).card:ℝ)*(N:ℝ)*Cost ≤
      ((Y.image y).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1)) :=
    tagged_cost_source_scale (Nat.cast_nonneg _) hNp
      (by exact_mod_cast (show 0 < Q by omega)) hcost
  apply hbase.trans
  apply mul_le_mul_of_nonneg_left _ (by linarith only [hC])
  exact add_le_add hscaled (le_refl FourierCost)

                                                                    
                                                                   
private theorem resonance_matrix_reciprocal_sum
    (S : Finset (Fin 4 → ℤ)) {X Gamma : ℝ}
    (hX : 0 ≤ X) (hGamma : 0 ≤ Gamma)
    (hdet : ∀ M∈S, M 0*M 3-M 1*M 2=1)
    (hc : ∀ M∈S, M 2 ≠ 0 ∧ |(M 2:ℝ)| ≤ Gamma)
    (ha : ∀ M∈S, |(M 0:ℝ)| ≤ |(M 2:ℝ)| *X+2)
    (hd : ∀ M∈S, |(M 3:ℝ)| ≤ |(M 2:ℝ)| *X+2) :
    ∑ M∈S,1/|(M 2:ℝ)| ≤ (2*Gamma+1)*(2*X+5)^2 := by
  let Z := ∑ M∈S,1/|(M 2:ℝ)|
  let K := (2*Gamma+1)*(2*X+5)^2
  pm_2207
  by_contra! hbad
  pm_5221 hgap Z K hbad
  let W := (K*Gamma+1)/(Z-K)
  pm_82 hW W
  pm_528 hh bourgain_resonance_matrix_weight_sum S hX hGamma hW hdet hc ha hd
  have he : (∑ M∈S,(1+W/|(M 2:ℝ)|))=(S.card:ℝ)+W*Z := by
    dsimp only [Z]
    simp only [Finset.sum_add_distrib,div_eq_mul_inv,←Finset.mul_sum,
      Finset.sum_const,nsmul_eq_mul,mul_one,one_mul]
  rw [he] at hh
  have hw : W*(Z-K)=K*Gamma+1 := by dsimp only [W]; field_simp
  change (S.card:ℝ)+W*Z ≤ K*(Gamma+W) at hh
  nlinarith only [hh,hw,(show (0:ℝ) ≤ S.card from Nat.cast_nonneg _)]

private theorem adjacent_reference_pairs_order
    (S : Finset ℝ) {a b : ℝ × ℝ}
    (ha : a.1∈S ∧ a.2∈S ∧ a.1<a.2 ∧ ∀ t∈S, ¬(a.1<t ∧ t<a.2))
    (hb : b.1∈S ∧ b.2∈S ∧ b.1<b.2 ∧ ∀ t∈S, ¬(b.1<t ∧ t<b.2))
    (hne : a≠b) : a.2 ≤ b.1 ∨ b.2 ≤ a.1 := by
  rcases lt_trichotomy a.1 b.1 with hlt | he | hgt
  · left
    exact le_of_not_gt (fun hh => ha.2.2.2 _ hb.1 ⟨hlt,hh⟩)
  · exfalso
    apply hne
    apply Prod.ext he
    rcases lt_trichotomy a.2 b.2 with hlt₂ | he₂ | hgt₂
    · exact False.elim (hb.2.2.2 _ ha.2.1 ⟨by rw [←he]; exact ha.2.2.1,hlt₂⟩)
    · exact he₂
    · exact False.elim (ha.2.2.2 _ hb.2.1 ⟨by rw [he]; exact hb.2.2.1,hgt₂⟩)
  · right
    exact le_of_not_gt (fun hh => hb.2.2.2 _ ha.1 ⟨hgt,hh⟩)

private theorem adjacent_reference_crossing_family_card
    (Y S : Finset ℝ) (E : Finset (ℝ × (ℝ × ℝ))) (t : ℝ → ℝ)
    (hdata : ∀ i∈E, i.1∈Y ∧
      (i.2.1∈S ∧ i.2.2∈S ∧ i.2.1 < i.2.2 ∧ ∀ u∈S, ¬(i.2.1 < u ∧ u < i.2.2)) ∧
      i.2.1 < t i.1 ∧ t i.1 < i.2.2) :
    E.card ≤ Y.card := by
  classical
  have hinj : Set.InjOn Prod.fst (E : Set (ℝ × (ℝ × ℝ))) := by
    intro i hi j hj he
    by_contra hne
    pm_8845 hh he
    have ho := adjacent_reference_pairs_order S (hdata i hi).2.1 (hdata j hj).2.1 hp
    have hti := (hdata i hi).2.2
    have htj := (hdata j hj).2.2
    rw [←he] at htj
    rcases ho with hleft | hright
    pm_8236 hleft
    pm_8236 hright
  have hsub : E.image Prod.fst ⊆ Y := by
    pm_2532 y hy i hi
    exact (hdata i hi).1
  rw [←Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hsub


                                                                 
                                                                    
                                                              
theorem positive_difference_reference_family_interior_geometry
    (F : ℝ → ℝ) (Y S : Finset ℝ)
    {σ c J η T M N R U : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 < U)
    (hphase : T*N*R^2=M^3)
    (hsep : ∀ a∈S, ∀ b∈S, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgapUpper : ∀ a∈S, ∀ b∈S, a<b →
      (∀ t∈S, ¬(a<t ∧ t<b)) → b-a ≤ 7*U/(2*R^2)) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let V := (Y ×ˢ (S ×ˢ S)).filter (fun i =>
      i.2.1 < i.2.2 ∧ (∀ t∈S, ¬(i.2.1 < t ∧ t < i.2.2)) ∧
        i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
    let G := V.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
    (V.card:ℝ) ≤ ((12*J/σ)*M/(N*U)+2)*(Y.card:ℝ) ∧
    (V \ G).card ≤ 2*Y.card ∧ (G.image Prod.fst).card ≤ Y.card ∧
    ∃ x₁ x₂ : ℝ × (ℝ × ℝ) → ℝ,
      (∀ i∈G, x₁ i∈Icc M (2*M) ∧ x₂ i∈Icc M (2*M) ∧ x₁ i < x₂ i ∧
        h i.1 (x₁ i)=i.2.1 ∧ h i.1 (x₂ i)=i.2.2 ∧
        U/(4*R^2) ≤ h i.1 (x₂ i)-h i.1 (x₁ i) ∧
        h i.1 (x₂ i)-h i.1 (x₁ i) ≤ 7*U/(2*R^2)) ∧
      (∀ i∈G, ∀ j∈G, i≠j → i.1=j.1 → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) := by
  classical
  intro f h V G
  have hVdata i (hi : i∈V) : i.1∈Y ∧
      (i.2.1∈S ∧ i.2.2∈S ∧ i.2.1 < i.2.2 ∧ ∀ t∈S, ¬(i.2.1 < t ∧ t < i.2.2)) ∧
      i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2 := by
    have hh := Finset.mem_filter.mp hi
    have hp := Finset.mem_product.mp hh.1
    have he := Finset.mem_product.mp hp.2
    exact ⟨hp.1,⟨he.1,he.2,hh.2.1,hh.2.2.1⟩,hh.2.2.2⟩
  pm_4982 hGS G V
  let Left := V.filter (fun i => i.2.1 < h i.1 M)
  let Right := V.filter (fun i => h i.1 (2*M) < i.2.2)
  have hleft : Left.card ≤ Y.card := by
    apply adjacent_reference_crossing_family_card Y S Left (fun y => h y M)
    pm_623 hVdata
    exact ⟨hd.1,hd.2.1,hh.2,hd.2.2.2⟩
  have hright : Right.card ≤ Y.card := by
    apply adjacent_reference_crossing_family_card Y S Right (fun y => h y (2*M))
    pm_623 hVdata
    exact ⟨hd.1,hd.2.1,hd.2.2.1,hh.2⟩
  have hbadSub : V \ G ⊆ Left∪Right := by
    intro i hi
    have hh := Finset.mem_sdiff.mp hi
    by_cases hlo : h i.1 M ≤ i.2.1
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      refine ⟨hh.1,?_⟩
      by_contra hnot
      exact hh.2 (Finset.mem_filter.mpr ⟨hh.1,hlo,le_of_not_gt hnot⟩)
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hh.1,lt_of_not_ge hlo⟩))
  have hboundary : (V \ G).card ≤ 2*Y.card := by
    have hh := (Finset.card_le_card hbadSub).trans (Finset.card_union_le Left Right)
    omega
  have hphaseCount : (G.image Prod.fst).card ≤ Y.card := by
    apply Finset.card_le_card
    pm_2532 y hyG i hi
    exact (hVdata i (hGS hi)).1
  have hmono y (hyY : y∈Y) : StrictMonoOn (h y) (Icc M (2*M)) := by
    apply (positive_difference_physical_curvature_strictMono F hσ hc hη hηmax
      (hy y hyY) hf hnegative hT hM).mono
    pm_624 hM
  have hcont y (hyY : y∈Y) : ContinuousOn (h y) (Icc M (2*M)) := by
    intro w hw
    pm_6919
    have hs0 : 0 < w/M+η*y := add_pos hw0 (mul_pos hη (zero_lt_one.trans_le (hy y hyY).1))
    pm_2607 w hw0
    pm_2604
  have hex : ∀ i∈G, ∃ a b : ℝ, a∈Icc M (2*M) ∧ b∈Icc M (2*M) ∧
      h i.1 a=i.2.1 ∧ h i.1 b=i.2.2 := by
    pm_623 hVdata
    have ha : i.2.1∈Icc (h i.1 M) (h i.1 (2*M)) := ⟨hh.2.1,hd.2.2.1.le⟩
    have hb : i.2.2∈Icc (h i.1 M) (h i.1 (2*M)) := ⟨hd.2.2.2.le,hh.2.2⟩
    pm_7034 a haM hae ha
    pm_7034 b hbM hbe hb
    exact ⟨a,b,haM,hbM,hae,hbe⟩
  choose! x₁ x₂ hroots using hex
  have hpack := positive_difference_reference_family_packing F Y S hσ hc hJ
    hη hηmax hy hf hbound htests hnegative hT hM hN hR hU hphase hsep
  refine ⟨hpack,hboundary,hphaseCount,x₁,x₂,?_,?_⟩
  · intro i hi
    have hd := hVdata i (hGS hi)
    have hr := hroots i hi
    have hlt : x₁ i < x₂ i := by
      by_contra hnot
      have hh := (hmono i.1 hd.1).monotoneOn hr.2.1 hr.1 (le_of_not_gt hnot)
      rw [hr.2.2.1,hr.2.2.2] at hh
      exact (not_le_of_gt hd.2.1.2.2.1) hh
    refine ⟨hr.1,hr.2.1,hlt,hr.2.2.1,hr.2.2.2,?_,?_⟩
    · rw [hr.2.2.1,hr.2.2.2]
      have hh := hsep _ hd.2.1.1 _ hd.2.1.2.1 (ne_of_lt hd.2.1.2.2.1)
      rw [abs_sub_comm,abs_of_pos (sub_pos.mpr hd.2.1.2.2.1)] at hh
      exact hh
    · rw [hr.2.2.1,hr.2.2.2]
      exact hgapUpper _ hd.2.1.1 _ hd.2.1.2.1 hd.2.1.2.2.1 hd.2.1.2.2.2
  · intro i hi j hj hne hye
    have hdi := hVdata i (hGS hi)
    have hdj := hVdata j (hGS hj)
    pm_8845 he hye
    have ho := adjacent_reference_pairs_order S hdi.2.1 hdj.2.1 hp
    pm_268 hri hroots i hi hrj j hj
    have hjleft : h i.1 (x₁ j)=j.2.1 := by simpa only [hye] using hrj.2.2.1
    have hjright : h i.1 (x₂ j)=j.2.2 := by simpa only [hye] using hrj.2.2.2
    rcases ho with hleft | hright
    · left
      apply le_of_not_gt
      intro hbad
      have hh := hmono i.1 hdi.1 hrj.1 hri.2.1 hbad
      rw [hjleft,hri.2.2.2] at hh
      exact (not_lt_of_ge hleft) hh
    · right
      apply le_of_not_gt
      intro hbad
      have hh := hmono i.1 hdi.1 hri.1 hrj.2.1 hbad
      rw [hri.2.2.1,hjright] at hh
      exact (not_lt_of_ge hright) hh


                                                               
                                                                        
                                                                         
                                                                             
public  theorem finite_reference_closed_bracket (S : Finset ℝ) {l u lo hi x : ℝ}
    (hl : l ∈ S) (hu : u ∈ S) (hlo : l ≤ lo) (hhi : hi ≤ u)
    (hwidth : lo < hi) (hx : x ∈ Icc lo hi) :
    ∃ a ∈ S, ∃ b ∈ S, a < b ∧ a ≤ x ∧ x ≤ b ∧
      (∀ z ∈ S, ¬ (a < z ∧ z < b)) ∧ a < hi ∧ lo < b := by
  classical
  by_cases htop : x < hi
  · let A := S.filter (fun z => z ≤ x)
    pm_7738
    have hA : A.Nonempty := ⟨l,Finset.mem_filter.mpr ⟨hl,hlo.trans hx.1⟩⟩
    have hB : B.Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,htop.trans_le hhi⟩⟩
    pm_2608
    refine ⟨a,ha.1,b,hb.1,ha.2.trans_lt hb.2,ha.2,hb.2.le,?_,
      ha.2.trans_lt htop,hx.1.trans_lt hb.2⟩
    intro z hz hzab
    by_cases hzx : z ≤ x
    pm_1684 lt_of_not_ge
  · have hxe : x = hi := le_antisymm hx.2 (le_of_not_gt htop)
    let A := S.filter (fun z => z < x)
    let B := S.filter (fun z => x ≤ z)
    have hA : A.Nonempty := ⟨l,Finset.mem_filter.mpr ⟨hl,by linarith⟩⟩
    have hB : B.Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,by linarith⟩⟩
    pm_2608
    refine ⟨a,ha.1,b,hb.1,ha.2.trans_le hb.2,ha.2.le,hb.2,?_,
      by simpa only [hxe] using ha.2,by linarith only [hwidth,hxe,hb.2]⟩
    intro z hz hzab
    by_cases hzx : z < x
    pm_1684 le_of_not_gt

private theorem grid_short_interval_card (K : Finset ℤ) {s N a : ℝ}
    (hN : 0 < N)
    (hK : ∀ k ∈ K, a ≤ s+N*(k:ℝ) ∧ s+N*(k:ℝ) ≤ a+N/4) :
    K.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  pm_268 hiw hK i hi hjw j hj
  pm_8831 hij i j
  pm_8831 hji j i
  have hij' : i < j+1 := by exact_mod_cast hij
  have hji' : j < i+1 := by exact_mod_cast hji
  omega

private theorem trimmed_grid_boundary_card (K : Finset ℤ) {s N a b : ℝ}
    (hN : 0 < N)
    (hK : ∀ k ∈ K, a ≤ s+N*(k:ℝ) ∧ s+N*(k:ℝ) ≤ b ∧
      ¬(a+N/4 ≤ s+N*(k:ℝ) ∧ s+N*(k:ℝ) ≤ b-N/4)) :
    K.card ≤ 2 := by
  classical
  let L := K.filter (fun k : ℤ => s+N*(k:ℝ) < a+N/4)
  let R := K.filter (fun k : ℤ => b-N/4 < s+N*(k:ℝ))
  have hL : L.card ≤ 1 := grid_short_interval_card L hN (by
    intro k hk
    have hh := Finset.mem_filter.mp hk
    exact ⟨(hK k hh.1).1,hh.2.le⟩)
  have hR : R.card ≤ 1 := grid_short_interval_card R hN (by
    intro k hk
    have hh := Finset.mem_filter.mp hk
    exact ⟨hh.2.le,by linarith only [(hK k hh.1).2.1]⟩)
  have hsub : K ⊆ L∪R := by
    intro k hk
    by_cases hleft : s+N*(k:ℝ) < a+N/4
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hk,hleft⟩))
    · have hr : b-N/4 < s+N*(k:ℝ) := by
        by_contra hnot
        exact (hK k hk).2.2 ⟨le_of_not_gt hleft,le_of_not_gt hnot⟩
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hk,hr⟩))
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le L R)
  omega


private theorem reference_grid_missing_card
    (Y S : Finset ℝ) (I : Finset ℤ) (h : ℝ → ℝ → ℝ)
    {M N s C : ℝ} (hM : 0 < M) (hN : 0 < N) (hC : 0 ≤ C)
    (hI : ∀ k∈I, s+N*(k:ℝ)∈Icc M (2*M))
    (hmono : ∀ y∈Y, StrictMonoOn (h y) (Icc M (2*M)))
    (henclose : ∀ y∈Y, ∃ l∈S, ∃ u∈S, l ≤ h y M ∧ h y (2*M) ≤ u)
    (x₁ x₂ : ℝ × (ℝ × ℝ) → ℝ) :
    let V := (Y ×ˢ (S ×ˢ S)).filter (fun i =>
      i.2.1 < i.2.2 ∧ (∀ z∈S, ¬(i.2.1 < z ∧ z < i.2.2)) ∧
        i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
    let G := V.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
    (∀ i∈G, x₁ i∈Icc M (2*M) ∧ x₂ i∈Icc M (2*M) ∧
      h i.1 (x₁ i)=i.2.1 ∧ h i.1 (x₂ i)=i.2.2) →
    (∀ i∈V, ∀ j∈I, ∀ k∈I,
      h i.1 (s+N*(j:ℝ))∈Icc i.2.1 i.2.2 →
      h i.1 (s+N*(k:ℝ))∈Icc i.2.1 i.2.2 →
      |(s+N*(k:ℝ))-(s+N*(j:ℝ))| ≤ C*N) →
    let Bad := (Y ×ˢ I).filter (fun p => ¬∃ i∈G, p.1=i.1 ∧
      x₁ i+N/4 ≤ s+N*(p.2:ℝ) ∧ s+N*(p.2:ℝ) ≤ x₂ i-N/4)
    (Bad.card:ℝ) ≤ 2*(V.card:ℝ)+C*((V\G).card:ℝ) := by
  classical
  intro V G hroots hwidth Bad
  let K := fun i : ℝ × (ℝ × ℝ) => I.filter (fun k : ℤ =>
    (i.1,k)∈Bad ∧ h i.1 (s+N*(k:ℝ))∈Icc i.2.1 i.2.2)
  have hVdata i (hi : i∈V) : i.1∈Y := by
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hi).1).1
  have hcover : Bad ⊆ V.biUnion (fun i => (K i).image (fun k => (i.1,k))) := by
    intro p hp
    have hpfull := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    obtain ⟨l,hl,u,hu,hlo,hhi⟩ := henclose p.1 hpfull.1
    have hleft : M∈Icc M (2*M) := ⟨le_rfl,by linarith only [hM]⟩
    have hright : 2*M∈Icc M (2*M) := ⟨by linarith only [hM],le_rfl⟩
    have hm := hmono p.1 hpfull.1
    have hpr := hI p.2 hpfull.2
    have hcurv : h p.1 (s+N*(p.2:ℝ))∈Icc (h p.1 M) (h p.1 (2*M)) :=
      ⟨hm.monotoneOn hleft hpr hpr.1,hm.monotoneOn hpr hright hpr.2⟩
    obtain ⟨a,ha,b,hb,hab,hax,hxb,hadj,hahi,hlob⟩ :=
      finite_reference_closed_bracket S hl hu hlo hhi
        (hm hleft hright (by linarith only [hM])) hcurv
    have hi : (p.1,(a,b))∈V :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hpfull.1,Finset.mem_product.mpr ⟨ha,hb⟩⟩,hab,hadj,hahi,hlob⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(p.1,(a,b)),hi,Finset.mem_image.mpr ?_⟩
    exact ⟨p.2,Finset.mem_filter.mpr ⟨hpfull.2,hp,hax,hxb⟩,Prod.eta p⟩
  have hKgood i (hi : i∈G) : (K i).card ≤ 2 := by
    apply trimmed_grid_boundary_card (K i) hN
    intro k hk
    have hh := Finset.mem_filter.mp hk
    have hr := hroots i hi
    have hm := hmono i.1 (hVdata i (Finset.mem_filter.mp hi).1)
    have hpk := hI k hh.1
    have hlo : x₁ i ≤ s+N*(k:ℝ) := by
      by_contra hnot
      have hz := hm hpk hr.1 (lt_of_not_ge hnot)
      rw [hr.2.2.1] at hz
      exact (not_lt_of_ge hh.2.2.1) hz
    have hhi : s+N*(k:ℝ) ≤ x₂ i := by
      by_contra hnot
      have hz := hm hr.2.1 hpk (lt_of_not_ge hnot)
      rw [hr.2.2.2] at hz
      exact (not_lt_of_ge hh.2.2.2) hz
    refine ⟨hlo,hhi,?_⟩
    intro htrim
    exact (Finset.mem_filter.mp hh.2.1).2 ⟨i,hi,rfl,htrim⟩
  have hKall i (hi : i∈V) : ((K i).card:ℝ) ≤ 2+C := by
    apply TaoTrudgianYang2025.HuxleyRationalPhase.physical_block_count_of_pairwise_width
      (K i) (fun k => s+N*(k:ℝ)) (Z:=s) hN hC
    · intro k _
      constructor <;> nlinarith only [hN]
    · intro j hj k hk
      have hjd := Finset.mem_filter.mp hj
      have hkd := Finset.mem_filter.mp hk
      exact hwidth i hi j hjd.1 k hkd.1 hjd.2.2 hkd.2.2
  have hcard : Bad.card ≤ ∑ i∈V, (K i).card :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le.trans
      (Finset.sum_le_sum (fun i _ => Finset.card_image_le)))
  have hcardR : (Bad.card:ℝ) ≤ ∑ i∈V, ((K i).card:ℝ) := by exact_mod_cast hcard
  have hsum : (∑ i∈V, ((K i).card:ℝ)) ≤
      ∑ i∈V, (2 + if i∈G then 0 else C) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hg : i∈G
    · simpa only [ite_eq_left hg,add_zero] using
        (show ((K i).card:ℝ) ≤ 2 by exact_mod_cast hKgood i hg)
    · simpa only [ite_eq_right hg] using hKall i hi
  have he : (∑ i∈V, (2 + if i∈G then (0:ℝ) else C)) =
      2*(V.card:ℝ)+C*((V\G).card:ℝ) := by
    rw [Finset.sum_add_distrib]
    have hid : (∑ i∈V, if i∈G then (0:ℝ) else C) = ∑ i∈V\G, C := by
      conv_rhs => rw [Finset.sdiff_eq_filter,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i∈G <;> simp only [hi,ite_true,ite_false,not_true_eq_false,not_false_eq_true]
    rw [hid]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  exact hcardR.trans (hsum.trans_eq he)


private theorem finite_sum_le_tagged_image_add_complement
    {α β : Type*} [DecidableEq α] (A : Finset α) (B : Finset β)
    (g : β → α) (w : α → ℝ) {N : ℝ}
    (hw : ∀ a, 0 ≤ w a) (hupper : ∀ a∈A, w a ≤ N) :
    (∑ a∈A, w a) ≤ (∑ b∈B, w (g b))+N*((A\B.image g).card:ℝ) := by
  classical
  have hc : (∑ a∈A∩B.image g, w a) ≤ ∑ b∈B, w (g b) :=
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun a _ _ => hw a)).trans (Finset.sum_image_le_of_nonneg (fun a _ => hw a))
  have hb : (∑ a∈A\B.image g, w a) ≤ N*((A\B.image g).card:ℝ) := by
    calc
      (∑ a∈A\B.image g, w a) ≤ ∑ _a∈A\B.image g, N :=
        Finset.sum_le_sum (fun a ha => hupper a (Finset.mem_sdiff.mp ha).1)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
  have he : (∑ a∈A∩B.image g, w a)+(∑ a∈A\B.image g, w a)=∑ a∈A, w a := by
    simpa only [Finset.filter_mem_eq_inter,←Finset.sdiff_eq_filter] using
      Finset.sum_filter_add_sum_filter_not A (fun a => a∈B.image g) w
  linarith only [hc,hb,he]


                                                                                               
theorem positive_difference_reference_family_whole_grid_geometry
    (F : ℝ → ℝ) (Y S : Finset ℝ)
    {σ c J η T M N R U : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 < U)
    (hphase : T*N*R^2=M^3)
    (hsep : ∀ a∈S, ∀ b∈S, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgapUpper : ∀ a∈S, ∀ b∈S, a<b →
      (∀ t∈S, ¬(a<t ∧ t<b)) → b-a ≤ 7*U/(2*R^2)) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let V := (Y ×ˢ (S ×ˢ S)).filter (fun i =>
      i.2.1 < i.2.2 ∧ (∀ t∈S, ¬(i.2.1 < t ∧ t < i.2.2)) ∧
        i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
    let G := V.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
    (V.card:ℝ) ≤ ((12*J/σ)*M/(N*U)+2)*(Y.card:ℝ) ∧
    (V \ G).card ≤ 2*Y.card ∧ (G.image Prod.fst).card ≤ Y.card ∧
    ∃ x₁ x₂ : ℝ × (ℝ × ℝ) → ℝ,
      (∀ i∈G, x₁ i∈Icc M (2*M) ∧ x₂ i∈Icc M (2*M) ∧ x₁ i < x₂ i ∧
        h i.1 (x₁ i)=i.2.1 ∧ h i.1 (x₂ i)=i.2.2 ∧
        U/(4*R^2) ≤ h i.1 (x₂ i)-h i.1 (x₁ i) ∧
        h i.1 (x₂ i)-h i.1 (x₁ i) ≤ 7*U/(2*R^2)) ∧
      (∀ i∈G, ∀ j∈G, i≠j → i.1=j.1 → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) ∧
      (∀ (s : ℝ) (I : Finset ℤ),
        (∀ k∈I, s+N*(k:ℝ)∈Icc M (2*M)) →
        (∀ y∈Y, ∃ l∈S, ∃ u∈S, l ≤ h y M ∧ h y (2*M) ≤ u) →
        let Bad := (Y ×ˢ I).filter (fun p => ¬∃ i∈G, p.1=i.1 ∧
          x₁ i+N/4 ≤ s+N*(p.2:ℝ) ∧ s+N*(p.2:ℝ) ≤ x₂ i-N/4)
        let Inner := (G ×ˢ I).filter (fun i =>
          x₁ i.1+N/4 ≤ s+N*(i.2:ℝ) ∧ s+N*(i.2:ℝ) ≤ x₂ i.1-N/4)
        let ErrorCount := (Y.card:ℝ)*((24*J/σ)*M/(N*U)+28*σ*U/c+4)
        (Bad.card:ℝ) ≤ ErrorCount ∧
        ∀ (L : ℤ → ℤ) (H : ℝ → ℤ → ℕ),
          (∀ y∈Y, ∀ k∈I, (H y k:ℝ) ≤ N) →
          (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),
            (𝐞 (f p.1 n):ℂ)‖) ≤
          (∑ i∈Inner, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),
            (𝐞 (f i.1.1 n):ℂ)‖)+N*ErrorCount) := by
  classical
  intro f h V G
  obtain ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint⟩ :=
    TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reference_family_interior_geometry
      F Y S hσ hc hJ hη hηmax hy hf hbound htests hnegative
      hT hM hN hR hU hphase hsep hgapUpper
  pm_2030 hpack hboundary hphaseCount x₁ x₂ hgeometry hdisjoint
  intro s I hI henclose Bad Inner ErrorCount
  have hm y (hyY : y∈Y) : StrictMonoOn (h y) (Icc M (2*M)) := by
    apply (TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_curvature_strictMono
      F hσ hc hη hηmax (hy y hyY) hf hnegative hT hM).mono
    pm_624 hM
  have hraw := reference_grid_missing_card Y S I h hM hN
    (show 0 ≤ (14*σ/c)*U by positivity) hI hm henclose x₁ x₂
    (fun i hi => ⟨(hgeometry i hi).1,(hgeometry i hi).2.1,
      (hgeometry i hi).2.2.2.1,(hgeometry i hi).2.2.2.2.1⟩) (by
      intro i hi j hj k hk hjc hkc
      have hv := Finset.mem_filter.mp hi
      have hp := Finset.mem_product.mp hv.1
      have hs := Finset.mem_product.mp hp.2
      have hgap := hgapUpper _ hs.1 _ hs.2 hv.2.1 hv.2.2.1
      apply TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reference_preimage_width
        F hσ hc hη hηmax (hy i.1 hp.1) hf hnegative hT hM hN hR hphase
        (hI j hj) (hI k hk)
      change |h i.1 (s+N*(k:ℝ))-h i.1 (s+N*(j:ℝ))| ≤ 7*U/(2*R^2)
      apply (abs_le.mpr ?_).trans hgap
      constructor <;> linarith only [hjc.1,hjc.2,hkc.1,hkc.2])
  have hbd : ((V\G).card:ℝ) ≤ 2*(Y.card:ℝ) := by exact_mod_cast hboundary
  have hcount : (Bad.card:ℝ) ≤ ErrorCount := by
    calc
      (Bad.card:ℝ) ≤ 2*(V.card:ℝ)+((14*σ/c)*U)*((V\G).card:ℝ) := hraw
      _ ≤ 2*(((12*J/σ)*M/(N*U)+2)*(Y.card:ℝ))+
          ((14*σ/c)*U)*(2*(Y.card:ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hpack (by norm_num))
          (mul_le_mul_of_nonneg_left hbd (by positivity))
      _ = ErrorCount := by dsimp only [ErrorCount]; ring
  refine ⟨hcount,?_⟩
  intro L H hH
  let w := fun p : ℝ × ℤ => ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),
    (𝐞 (f p.1 n):ℂ)‖
  let tag := fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)
  have he : Bad=(Y ×ˢ I)\Inner.image tag := by
    ext p
    constructor
    · intro hp
      have hh := Finset.mem_filter.mp hp
      apply Finset.mem_sdiff.mpr
      refine ⟨hh.1,?_⟩
      intro hin
      obtain ⟨⟨i,k⟩,hik,hpeq⟩ := Finset.mem_image.mp hin
      have hd := Finset.mem_filter.mp hik
      have hg := Finset.mem_product.mp hd.1
      have hye : i.1=p.1 := congrArg Prod.fst hpeq
      have hke : k=p.2 := congrArg Prod.snd hpeq
      exact hh.2 ⟨i,hg.1,hye.symm,by simpa only [hke] using hd.2⟩
    · intro hp
      have hh := Finset.mem_sdiff.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨hh.1,?_⟩
      rintro ⟨i,hi,hye,htrim⟩
      apply hh.2
      apply Finset.mem_image.mpr
      refine ⟨(i,p.2),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hi,(Finset.mem_product.mp hh.1).2⟩,htrim⟩,?_⟩
      exact Prod.ext hye.symm rfl
  have hwbound p (hp : p∈Y ×ˢ I) : w p ≤ N := by
    have hh := Finset.mem_product.mp hp
    have hsum : w p ≤ H p.1 p.2 := by
      apply (norm_sum_le _ _).trans_eq
      simp
    exact hsum.trans (hH p.1 hh.1 p.2 hh.2)
  have hs := finite_sum_le_tagged_image_add_complement
    (Y ×ˢ I) Inner tag w (fun _ => norm_nonneg _) hwbound
  rw [←he] at hs
  exact hs.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcount hN.le))


                                                                                                                                               
section
variable (S : Finset ℝ) (G : Finset (ℝ × ℝ))
include S G
private theorem adjacent_reference_gap_card_closed {lo hi d : ℝ}
    (hd : 0 < d) (hlohi : lo ≤ hi)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → d ≤ |x-y|)
    (hgap : ∀ ab∈G, ab.1∈S ∧ ab.2∈S ∧ ab.1<ab.2 ∧
      ∀ t∈S, ¬(ab.1<t ∧ t<ab.2))
    (hmeet : ∀ ab∈G, ab.1 ≤ hi ∧ lo ≤ ab.2) :
    (G.card:ℝ) ≤ (hi-lo)/d+2 := by
  pm_1840
  have hsmall : G₀.card ≤ 1 := by
    pm_1842
    · exact False.elim ((hgap ab ha.1).2.2.2 _ (hgap cd hc.1).1
        ⟨hlt,hc.2.trans_le (hmeet ab ha.1).2⟩)
    · exact heq
    · exact False.elim ((hgap cd hc.1).2.2.2 _ (hgap ab ha.1).1
        ⟨hgt,ha.2.trans_le (hmeet cd hc.1).2⟩)
  have hlarge := separated_reference_interval_card (G₁.image Prod.fst) hd hlohi
    (by
      intro x hx y hy hne
      pm_2533 ab hab hx cd hcd hy
      exact hsep _ (hgap ab (Finset.mem_filter.mp hab).1).1
        _ (hgap cd (Finset.mem_filter.mp hcd).1).1 hne)
    (by
      pm_2532 x hx ab hab
      have ha := Finset.mem_filter.mp hab
      exact ⟨le_of_not_gt ha.2,(hmeet ab ha.1).1⟩)
  pm_1841


public  theorem reference_gap_count_of_closed_profile_width (p : ℝ × ℝ → ℝ)
    {d D : ℝ} (hd : 0 < d) (hD : 0 ≤ D)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → d ≤ |x-y|)
    (hgap : ∀ ab∈G, ab.1∈S ∧ ab.2∈S ∧ ab.1 < ab.2 ∧
      ∀ t∈S, ¬(ab.1 < t ∧ t < ab.2))
    (hpoint : ∀ ab∈G, p ab∈Icc ab.1 ab.2)
    (hwidth : ∀ ab∈G, ∀ cd∈G, |p cd-p ab| ≤ D) :
    (G.card:ℝ) ≤ D/d+2 := by
  classical
  by_cases hG : G.Nonempty
  · let Values := G.image p
    have hv : Values.Nonempty := Finset.Nonempty.image hG p
    let lo := Values.min' hv
    let hi := Values.max' hv
    obtain ⟨ab,hab,hablo⟩ := Finset.mem_image.mp (Finset.min'_mem Values hv)
    obtain ⟨cd,hcd,hcdhi⟩ := Finset.mem_image.mp (Finset.max'_mem Values hv)
    have hbounds g (hg : g∈G) : lo ≤ p g ∧ p g ≤ hi :=
      ⟨Finset.min'_le Values _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩),
        Finset.le_max' Values _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩)⟩
    have hlohi : lo ≤ hi := (hbounds ab hab).1.trans (hbounds ab hab).2
    have hspan : hi-lo ≤ D := by
      change Values.max' hv-Values.min' hv ≤ D
      rw [←hablo,←hcdhi]
      exact (abs_le.mp (hwidth ab hab cd hcd)).2
    have hc := adjacent_reference_gap_card_closed S G hd hlohi hsep hgap (by
      intro g hg
      exact ⟨(hpoint g hg).1.trans (hbounds g hg).2,
        (hbounds g hg).1.trans (hpoint g hg).2⟩)
    exact hc.trans (add_le_add (div_le_div_of_nonneg_right hspan hd.le) le_rfl)
  · have he : G=∅ := Finset.not_nonempty_iff_eq_empty.mp hG
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity
end


section
variable (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (x y : ℝ × ℝ → ℝ) (Mat : Fin 4 → ℤ) {σ δ T M R U Δ : ℝ} {τ A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ} (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ) (hT : 0 < T) (hτ : ∀ i, T ≤ τ i ∧ τ i ≤ 2*T) (hM : 0 < M) (hR : 0 < R) (hU : 0 < U) (hΔ : 0 ≤ Δ) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M) (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0) (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|) (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧ ∀ z∈Refs, ¬(ab.1 < z ∧ z < ab.2)) (hx : ∀ ab∈Gaps, x ab∈Ioo (1/2:ℝ) (W 0-1/2)) (hy : ∀ ab∈Gaps, y ab∈Ioo (1/2:ℝ) (W 1-1/2))
include Refs Gaps x y Mat σ δ T M R U Δ τ A W F hσ hδ hF hT hτ hM hR hU hΔ hA hW hMat hc hlarge hsep hgap hx hy
private theorem paired_large_entry_closed_reference_gap_packing :
    let f := fun i => heathBrownPhysicalPhase (F i) (τ i) M (A i) 1
    let p := fun ab => iteratedDeriv 2 (f 0) (x ab)/2
    let mu := fun i z => iteratedDeriv 3 (f i) (round z)/6
    let t := fun ab => (Mat 2:ℝ)*p ab+Mat 3
    (∀ ab∈Gaps, p ab∈Icc ab.1 ab.2) →
    (∀ ab∈Gaps, ((Mat 0:ℝ)*p ab+Mat 1)/t ab=iteratedDeriv 2 (f 1) (y ab)/2) →
    (∀ ab∈Gaps, t ab∈Icc (1/2:ℝ) 2) →
    (∀ ab∈Gaps, |mu 1 (y ab)*(t ab)^3/mu 0 (x ab)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let eta := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    (Gaps.card:ℝ) ≤ 64*Cphys*(Gamma^2*Δ+2*Gamma*eta)*R^2/
      (κ*|(Mat 2:ℝ)| *U)+2 := by
  classical
  intro f p mu t hpoint hmap ht hthird κ Cphys Gamma eta
  pm_1778
  pm_1685
  have hC₃ : 0 ≤ modelPhaseJetCoefficient σ 3+δ :=
    add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  pm_82 heta eta
  pm_1781 hcpos hc
  let Width := 16*Cphys*(Gamma^2*Δ+2*Gamma*eta)/(κ*|(Mat 2:ℝ)|)
  pm_82 hw0 Width
  have hordered ab (hab : ab∈Gaps) cd (hcd : cd∈Gaps) (horder : p ab ≤ p cd) :
      p cd-p ab ≤ Width := by
    exact physicalModelPhase_paired_large_entry_curvature_diameter
      ![x ab,x cd] ![y ab,y cd] (Mat 0) (Mat 1) (Mat 2) (Mat 3)
      hσ hδ hδ0 hF hT hτ hM hA hW hΔ hMat hc hlarge
      (by intro i; fin_cases i; exact hx ab hab; exact hx cd hcd)
      (by intro i; fin_cases i; exact hy ab hab; exact hy cd hcd)
      horder
      (by intro i; fin_cases i; exact hmap ab hab; exact hmap cd hcd)
      (by intro i; fin_cases i; exact ht ab hab; exact ht cd hcd)
      (by intro i; fin_cases i; exact hthird ab hab; exact hthird cd hcd)
  have hwidth ab (hab : ab∈Gaps) cd (hcd : cd∈Gaps) : |p cd-p ab| ≤ Width := by
    by_cases hle : p ab ≤ p cd
    · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      exact hordered ab hab cd hcd hle
    · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hle))]
      exact hordered cd hcd ab hab (le_of_not_ge hle)
  have hp := reference_gap_count_of_closed_profile_width Refs Gaps p
    (show 0 < U/(4*R^2) by positivity) hw0 hsep hgap hpoint hwidth
  apply hp.trans_eq
  dsimp only [Width]
  field_simp
  ring_nf




private theorem paired_large_entry_reference_gap_packing :
    let f := fun i => heathBrownPhysicalPhase (F i) (τ i) M (A i) 1
    let p := fun ab => iteratedDeriv 2 (f 0) (x ab)/2
    let mu := fun i z => iteratedDeriv 3 (f i) (round z)/6
    let t := fun ab => (Mat 2:ℝ)*p ab+Mat 3
    (∀ ab∈Gaps, p ab∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, ((Mat 0:ℝ)*p ab+Mat 1)/t ab=iteratedDeriv 2 (f 1) (y ab)/2) →
    (∀ ab∈Gaps, t ab∈Icc (1/2:ℝ) 2) →
    (∀ ab∈Gaps, |mu 1 (y ab)*(t ab)^3/mu 0 (x ab)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let eta := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    (Gaps.card:ℝ) ≤ 64*Cphys*(Gamma^2*Δ+2*Gamma*eta)*R^2/
      (κ*|(Mat 2:ℝ)| *U)+2 := by
  intro f p mu t hpoint hmap ht hthird κ Cphys Gamma eta
  exact paired_large_entry_closed_reference_gap_packing Refs Gaps x y Mat
    hσ hδ hF hT hτ hM hR hU hΔ hA hW hMat hc hlarge hsep hgap hx hy
    (fun ab hab => ⟨(hpoint ab hab).1.le,(hpoint ab hab).2.le⟩) hmap ht hthird
end


public  theorem reference_chart_fraction_antitone {e v r s a b : ℝ}
    (hdet : v*r-e*s=1) (ha : 0 < r*a+s) (hb : 0 < r*b+s) (hab : a ≤ b) :
    (e*b+v)/(r*b+s) ≤ (e*a+v)/(r*a+s) := by
  apply (div_le_div_iff₀ hb ha).mpr
  have he : (e*a+v)*(r*b+s)-(e*b+v)*(r*a+s)=b-a := by
    linear_combination (b-a)*hdet
  have hh := sub_nonneg.mpr hab
  rw [←he] at hh
  exact sub_nonneg.mp hh


theorem physicalModelPhase_quartic_long_reference_gap_packing
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (Mat : Fin 4 → ℤ)
    (x : ℝ × ℝ → Fin 4 → ℝ)
    (xref e r v s : ℝ × ℝ → Fin 2 → ℝ)
    (curve : ℝ × ℝ → ℝ → Fin 2 → ℝ) (d alpha beta : ℝ × ℝ → ℝ)
    {σ δ T M N R U L K : ℝ} {A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hU : 0 < U) (hL : 0 < L) (hNL : (L*N)^2 ≤ M*R) (hK : 0 ≤ K)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2))
    (hd : ∀ ab∈Gaps, 0 < d ab)
    (href : ∀ ab∈Gaps, ∀ i, xref ab i∈Ioo (1/2:ℝ) (W i-1/2))
    (hcurve : ∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      curve ab t i∈Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ ab∈Gaps, ∀ i, r ab i≠0)
    (hdet : ∀ ab∈Gaps, ∀ i, v ab i*r ab i-e ab i*s ab i=1)
    (hden : ∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      d ab ≤ r ab i*t+s ab i ∧ r ab i*t+s ab i ≤ 2*d ab)
    (hmono : ∀ ab∈Gaps, StrictMono (x ab))
    (htransport : ∀ ab∈Gaps,
      e ab 1=(Mat 0:ℝ)*e ab 0+Mat 1*r ab 0 ∧
      v ab 1=(Mat 0:ℝ)*v ab 0+Mat 1*s ab 0 ∧
      r ab 1=(Mat 2:ℝ)*e ab 0+Mat 3*r ab 0 ∧
      s ab 1=(Mat 2:ℝ)*v ab 0+Mat 3*s ab 0) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun ab t i => (round (curve ab t i):ℝ)-(round (xref ab i):ℝ)
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (xref ab i))/6
    let munew := fun ab t i => iteratedDeriv 3 (f i) (round (curve ab t i))/6
    let nu := fun ab i => iteratedDeriv 4 (f i) (round (xref ab i))/24
    let Den := fun ab t i => r ab i*t+s ab i
    let g := fun ab => rationalPhase (mu ab 0) (r ab 0) (s ab 0) (mu ab 1) (r ab 1) (s ab 1)
    let H := fun ab => quarticPhase (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1)
    let Gcoord := fun ab => minorArcCoordinate (mu ab 0) (r ab 0) (s ab 0)
    let profile := fun ab t => iteratedDeriv 2 (f 0) (curve ab t 0)/2
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (xref ab i)/2=e ab i/r ab i) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      iteratedDeriv 2 (f i) (curve ab t i)/2=(e ab i*t+v ab i)/Den ab t i) →
    (∀ ab∈Gaps, profile ab (x ab 0)∈Ioo ab.1 ab.2 ∧
      profile ab (x ab 3)∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i, |n ab t i|^2 ≤ M*R) →
    (∀ ab∈Gaps, ∀ j : Fin 3, L*N ≤ |Gcoord ab (x ab j.succ)-Gcoord ab (x ab j.castSucc)|) →
    (∀ ab∈Gaps, ∀ j : Fin 4, |alpha ab*x ab j+beta ab-g ab (x ab j)+H ab (x ab j)| ≤
      K*R^2/|r ab 0*Gcoord ab (x ab j)|) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*K+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    ∃ z : ℝ × ℝ → ℝ,
      (∀ ab∈Gaps, z ab∈Ioo (x ab 0) (x ab 3) ∧ profile ab (z ab)∈Ioo ab.1 ab.2 ∧
        let t := (Mat 2:ℝ)*profile ab (z ab)+Mat 3
        t∈Icc (1/2:ℝ) 2 ∧
        ((Mat 0:ℝ)*profile ab (z ab)+Mat 1)/t=iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2 ∧
        |munew ab (z ab) 1*t^3/munew ab (z ab) 0-1| ≤ Cthird*R^2/(L^2*N^2)) ∧
      (Gaps.card:ℝ) ≤ Cpack*R^4/(L^2*N^2*|(Mat 2:ℝ)| *U)+2 := by
  classical
  intro f n mu munew nu Den g H Gcoord profile hbase hpoint hends hsquare hspacing hres
    κ Cphys Gamma Cthird Cpack
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  pm_1685
  pm_1778
  pm_2669
  pm_1004
  pm_82 hCt Cthird
  have hdenpos ab (hab : ab∈Gaps) t (ht : t∈Icc (x ab 0) (x ab 3)) i :
      0 < Den ab t i := (hd ab hab).trans_le (hden ab hab t ht i).1
  have hex : ∀ ab∈Gaps, ∃ z∈Ioo (x ab 0) (x ab 3),
      |munew ab z 1*(Den ab z 1)^3/(munew ab z 0*(Den ab z 0)^3)-1| ≤ Cthird*R^2/(L^2*N^2) := by
    intro ab hab
    exact physicalModelPhase_quartic_long_block_third_condition (x ab)
      hσ hδ hF hT hM hN hR hL hNL (hd ab hab) hK hA hW
      (href ab hab) (hcurve ab hab) (hr ab hab) (hdet ab hab)
      (fun t ht i => (hden ab hab t ht i).1)
      (fun t ht i => (hden ab hab t ht i).2) (hmono ab hab)
      (hbase ab hab) (hpoint ab hab) (hsquare ab hab) (hspacing ab hab) (hres ab hab)
  choose! z hz hthird using hex
  have hzcc ab (hab : ab∈Gaps) : z ab∈Icc (x ab 0) (x ab 3) := ⟨(hz ab hab).1.le,(hz ab hab).2.le⟩
  have hinside ab (hab : ab∈Gaps) : profile ab (z ab)∈Ioo ab.1 ab.2 := by
    have hx03 : x ab 0 ≤ x ab 3 := (hmono ab hab).monotone (by decide)
    have hx0 : x ab 0∈Icc (x ab 0) (x ab 3) := ⟨le_rfl,hx03⟩
    have hx3 : x ab 3∈Icc (x ab 0) (x ab 3) := ⟨hx03,le_rfl⟩
    have hlow : profile ab (x ab 3) ≤ profile ab (z ab) := by
      dsimp only [profile]
      rw [hpoint ab hab _ hx3 0,hpoint ab hab _ (hzcc ab hab) 0]
      exact reference_chart_fraction_antitone (hdet ab hab 0)
        (hdenpos ab hab _ (hzcc ab hab) 0) (hdenpos ab hab _ hx3 0) (hzcc ab hab).2
    have hhigh : profile ab (z ab) ≤ profile ab (x ab 0) := by
      dsimp only [profile]
      rw [hpoint ab hab _ (hzcc ab hab) 0,hpoint ab hab _ hx0 0]
      exact reference_chart_fraction_antitone (hdet ab hab 0)
        (hdenpos ab hab _ hx0 0) (hdenpos ab hab _ (hzcc ab hab) 0) (hzcc ab hab).1
    exact ⟨(hends ab hab).2.1.trans_le hlow,hhigh.trans_lt (hends ab hab).1.2⟩
  let t := fun ab => (Mat 2:ℝ)*profile ab (z ab)+Mat 3
  have htid ab (hab : ab∈Gaps) : t ab=Den ab (z ab) 1/Den ab (z ab) 0 := by
    change (Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (curve ab (z ab) 0)/2)+Mat 3=_
    pm_1686
    pm_1687
    ring_nf
  have htband ab (hab : ab∈Gaps) : t ab∈Icc (1/2:ℝ) 2 := by
    rw [htid ab hab]
    constructor
    · apply (le_div_iff₀ (hdenpos ab hab _ (hzcc ab hab) 0)).mpr
      linarith only [(hden ab hab _ (hzcc ab hab) 1).1,(hden ab hab _ (hzcc ab hab) 0).2]
    · apply (div_le_iff₀ (hdenpos ab hab _ (hzcc ab hab) 0)).mpr
      linarith only [(hden ab hab _ (hzcc ab hab) 1).2,(hden ab hab _ (hzcc ab hab) 0).1]
  have hmap ab (hab : ab∈Gaps) :
      ((Mat 0:ℝ)*profile ab (z ab)+Mat 1)/t ab=
        iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2 := by
    rw [htid ab hab]
    have he : (Mat 0:ℝ)*profile ab (z ab)+Mat 1=
        (e ab 1*z ab+v ab 1)/Den ab (z ab) 0 := by
      change (Mat 0:ℝ)*(iteratedDeriv 2 (f 0) (curve ab (z ab) 0)/2)+Mat 1=_
      pm_1686
      pm_6662
      dsimp only [Den]
      ring_nf
    rw [he,div_div_div_cancel_right₀ (hdenpos ab hab _ (hzcc ab hab) 0).ne']
    exact (hpoint ab hab _ (hzcc ab hab) 1).symm
  have hthirdMat ab (hab : ab∈Gaps) :
      |munew ab (z ab) 1*(t ab)^3/munew ab (z ab) 0-1| ≤ Cthird*R^2/(L^2*N^2) := by
    rw [htid ab hab]
    have he : munew ab (z ab) 1*(Den ab (z ab) 1/Den ab (z ab) 0)^3/munew ab (z ab) 0=
        munew ab (z ab) 1*(Den ab (z ab) 1)^3/(munew ab (z ab) 0*(Den ab (z ab) 0)^3) := by
      rw [div_pow]
      ring_nf
    rw [he]
    exact hthird ab hab
  refine ⟨z,fun ab hab => ⟨hz ab hab,hinside ab hab,htband ab hab,hmap ab hab,hthirdMat ab hab⟩,?_⟩
  have hp := paired_large_entry_reference_gap_packing Refs Gaps
    (fun ab => curve ab (z ab) 0) (fun ab => curve ab (z ab) 1) Mat
    hσ hδ (fun i => approximateModelPhase_mono (hF i) (by norm_num : 3 ≤ 4) le_rfl)
    hT (fun _ => ⟨le_rfl,by linarith only [hT]⟩) hM hRpos hU
    (show 0 ≤ Cthird*R^2/(L^2*N^2) by positivity) hA hW hMat hc hlarge hsep hgap
    (fun ab hab => hcurve ab hab _ (hzcc ab hab) 0)
    (fun ab hab => hcurve ab hab _ (hzcc ab hab) 1)
    hinside hmap htband hthirdMat
  have hNL' : L^2*N^2 ≤ M*R^2 := by
    have hRR : R ≤ R^2 := by nlinarith only [hR]
    calc
      L^2*N^2 = (L*N)^2 := by ring_nf
      _ ≤ M*R := hNL
      _ ≤ M*R^2 := mul_le_mul_of_nonneg_left hRR hM.le
  pm_1780
  have heta : 2*Gamma*((modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)) ≤
      (Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)*(R^2/(L^2*N^2)) := by
    pm_1688
  apply hp.trans
  calc
    _ ≤ 64*Cphys*(Gamma^2*(Cthird*R^2/(L^2*N^2))+
        (Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)*(R^2/(L^2*N^2)))*R^2/
          (κ*|(Mat 2:ℝ)| *U)+2 := by
      apply add_le_add _ le_rfl
      pm_2680
      pm_6431
    _ = Cpack*R^4/(L^2*N^2*|(Mat 2:ℝ)| *U)+2 := by
      dsimp only [Cpack]
      ring_nf



                                                                          
                                                                             
                                                                    
private theorem reciprocal_square_prefix (J : ℕ) :
    (∑ m∈Finset.range J, 1/((m:ℝ)+1)^2) ≤ 2-2/((J:ℝ)+1) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
    have hJ : (0:ℝ) ≤ J := Nat.cast_nonneg J
    have hstep : 1/((J:ℝ)+1)^2 ≤ 2/((J:ℝ)+1)-2/((J:ℝ)+1+1) := by
      have h₁ : (J:ℝ)+1 ≠ 0 := by positivity
      have h₂ : (J:ℝ)+1+1 ≠ 0 := by positivity
      have he : 2/((J:ℝ)+1)-2/((J:ℝ)+1+1)=2/(((J:ℝ)+1)*((J:ℝ)+1+1)) := by
        field_simp
        ring
      rw [he]
      apply (div_le_div_iff₀ (by positivity : 0 < ((J:ℝ)+1)^2)
        (by positivity : 0 < ((J:ℝ)+1)*((J:ℝ)+1+1))).mpr
      nlinarith
    linarith only [ih,hstep]

section
variable {ι : Type*} (S : Finset ι) (n : ι → ℕ)
include ι S n
private theorem finite_occupied_tail_sum (J : ℕ)
    {A B : ℝ} (hB : 0 ≤ B) (hcap : ∀ i∈S, n i ≤ J)
    (htail : ∀ m∈Finset.range J,
      ((S.filter (fun i => m < n i)).card:ℝ) ≤ A+B/((m:ℝ)+1)^2) :
    (∑ i∈S, (n i:ℝ)) ≤ A*(J:ℝ)+2*B := by
  classical
  have hrepr :
      (∑ m∈Finset.range J, ((S.filter (fun i => m < n i)).card:ℝ)) =
        ∑ i∈S, (n i:ℝ) := by
    calc
      _ = ∑ m∈Finset.range J, ∑ i∈S, if m < n i then (1:ℝ) else 0 := by
        simp
      _ = ∑ i∈S, ∑ m∈Finset.range J, if m < n i then (1:ℝ) else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hfilter : (Finset.range J).filter (fun m => m < n i)=Finset.range (n i) := by
          ext m
          simp only [Finset.mem_filter,Finset.mem_range]
          have hiCap := hcap i hi
          omega
        rw [← Finset.sum_filter,hfilter]
        simp
  rw [← hrepr]
  calc
    _ ≤ ∑ m∈Finset.range J, (A+B/((m:ℝ)+1)^2) := Finset.sum_le_sum htail
    _ = A*(J:ℝ)+B*(∑ m∈Finset.range J,1/((m:ℝ)+1)^2) := by
      pm_341 Finset.sum_add_distrib Finset.sum_const Finset.card_range nsmul_eq_mul div_eq_mul_inv one_mul Finset.mul_sum
      ring
    _ ≤ A*(J:ℝ)+2*B := by
      have hh : (∑ m∈Finset.range J,1/((m:ℝ)+1)^2) ≤ 2 :=
        (reciprocal_square_prefix J).trans (sub_le_self _ (by positivity))
      nlinarith only [mul_le_mul_of_nonneg_left hh hB]

public  theorem finite_occupied_cubic_tail_sum
    {A B K c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hc : 0 < c)
    (hcap : ∀ i∈S, (n i:ℝ)^3*c ≤ K)
    (htail : ∀ m : ℕ, 0 < m →
      ((S.filter (fun i => m ≤ n i)).card:ℝ) ≤ A+B/(m:ℝ)^2) :
    (∑ i∈S, (n i:ℝ)) ≤ A*(K/c)^((3:ℝ)⁻¹)+2*B := by
  classical
  let J := S.sup n
  let root := (K/c)^((3:ℝ)⁻¹)
  have hroot : 0 ≤ root := Real.rpow_nonneg (div_nonneg hK hc.le) _
  have hrootcube : root^3=K/c :=
    Real.rpow_inv_natCast_pow (div_nonneg hK hc.le) (by norm_num : (3:ℕ) ≠ 0)
  have hJcube : (J:ℝ)^3 ≤ K/c := by
    by_cases hs : S.Nonempty
    · obtain ⟨i,hi,he⟩ := Finset.sup_mem_of_nonempty (f:=n) hs
      change n i=J at he
      rw [← he]
      exact (le_div_iff₀ hc).mpr (hcap i hi)
    · have hJzero : J=0 := by simp [J,Finset.not_nonempty_iff_eq_empty.mp hs]
      rw [hJzero]
      simpa using div_nonneg hK hc.le
  have hJ : (J:ℝ) ≤ root := (pow_le_pow_iff_left₀ (Nat.cast_nonneg J)
    hroot (by decide : (3:ℕ) ≠ 0)).mp (by rw [hrootcube]; exact hJcube)
  have hh := finite_occupied_tail_sum S n J hB (fun i hi => Finset.le_sup hi)
    (fun m _ => by
      simpa only [Nat.lt_iff_add_one_le,Nat.cast_add,Nat.cast_one] using htail (m+1) (by omega))
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hJ hA) le_rfl)
end


public  theorem quotient_block_mass (a b : ℕ) (hb : 0 < b) (hba : b ≤ a) :
    0 < a/b ∧ b*(a/b) ≤ a ∧ a ≤ 2*b*(a/b) := by
  have hpos := Nat.div_pos hba hb
  have hrem := Nat.mod_lt a hb
  have he := Nat.div_add_mod a b
  have hmul : b ≤ b*(a/b) := Nat.le_mul_of_pos_right b hpos
  refine ⟨hpos,Nat.mul_div_le a b,?_⟩
  nlinarith only [hrem,he,hmul]

private theorem two_term_first_cubic_cap
    {C A B N scale length n : ℝ}
    (hC : 0 ≤ C) (hN : 0 < N) (hs : 0 < scale)
    (hl : 0 < length) (hn : 0 ≤ n) (hshort : scale*n ≤ length)
    (hfirst : C ≤ A/(length^3*N^2)+B) (hsmall : 2*B ≤ C) :
    n^3*C ≤ 2*A/(scale^3*N^2) := by
  have hden : 0 < length^3*N^2 := by positivity
  have hhalf : C/2 ≤ A/(length^3*N^2) := by linarith only [hfirst,hsmall]
  have hm := (le_div_iff₀ hden).mp hhalf
  have hp := pow_le_pow_left₀ (mul_nonneg hs.le hn) hshort 3
  have hh := mul_le_mul_of_nonneg_right hp (mul_nonneg (sq_nonneg N) hC)
  pm_6856 scale
  nlinarith only [hm,hh]

                                                                    
                                                                             
                                                                         
                                                               
private theorem physicalModelPhase_actual_fourier_large_entry_closed_reference_gap_count
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (Mat : Fin 4 → ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → Fin 2 → ℚ) (vinv : ℝ × ℝ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → Fin 2 → Fin 2) (x : ℝ × ℝ → Fin 2 → ℝ)
    {σ δ T M N R U : ℝ} {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 < U)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2) (hNscale : N^2 ≤ M*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2))
    (hx : ∀ ab∈Gaps, ∀ i, x ab i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ ab∈Gaps, ∀ i, (rat ab i).den ≤ Q ∧ Q ≤ 2*(rat ab i).den)
    (hinv : ∀ ab∈Gaps, ∀ i, ((rat ab i).den:ℤ) ∣ (rat ab i).num*vinv ab i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (x ab i)/2=(rat ab i:ℝ)) →
    let q := fun ab i => (rat ab i).den
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (x ab i))/6
    let ell := fun ab i => deriv (f i) (round (x ab i))
    let b := fun ab i => (⌊(q ab i:ℝ)*ell ab i⌋+(parity ab i:ℕ) : ℤ)
    let cround := fun ab i => round ((q ab i:ℝ)*ell ab i)
    let tau := fun ab i => ((b ab i:ℝ)-(q ab i:ℝ)*ell ab i)/2
    let dual := fun ab i => -2*mu ab i*(Real.sqrt (2/(3*mu ab i*(q ab i:ℝ))))^3
    let cloud := fun ab i => (![Int.fract (-(vinv ab i:ℝ)*b ab i/q ab i),
      Int.fract (-(vinv ab i:ℝ)/q ab i),dual ab i/Real.sqrt K₀,
      (3*dual ab i*tau ab i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, b ab 0-cround ab 0=b ab 1-cround ab 1) →
    (∀ ab∈Gaps, ∀ a, |cloud ab 0 a-cloud ab 1 a| ≤ 2*radius a) →
    (∀ ab∈Gaps, (Mat 2:ℝ)*(rat ab 0:ℝ)+Mat 3=(q ab 1:ℝ)/q ab 0) →
    (∀ ab∈Gaps, ((Mat 0:ℝ)*(rat ab 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat ab 0:ℝ)+Mat 3)=(rat ab 1:ℝ)) →
    (∀ ab∈Gaps, (rat ab 0:ℝ)∈Icc ab.1 ab.2) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let Gamma := Cphys/κ
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    (Gaps.card:ℝ) ≤ 2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *U) := by
  classical
  intro f hlevel q mu ell b cround tau dual cloud radius hcolor hnear hMatt hMatmap
    hsourceGap κ Cphys c J B Gamma Cgap
  pm_1689
  have hGamma : 0 < Gamma := div_pos hCphys hκ
  pm_1856
  pm_1691
  have hratio ab (hab : ab∈Gaps) : (q ab 1:ℝ)/q ab 0∈Icc (1/2:ℝ) 2 := by
    have hq : (0:ℝ) < q ab 0 := by exact_mod_cast (rat ab 0).den_pos
    have hlo₀ : ((q ab 0):ℝ) ≤ Q := by exact_mod_cast (hden ab hab 0).1
    have hhi₀ : (Q:ℝ) ≤ 2*q ab 0 := by exact_mod_cast (hden ab hab 0).2
    have hlo₁ : ((q ab 1):ℝ) ≤ Q := by exact_mod_cast (hden ab hab 1).1
    have hhi₁ : (Q:ℝ) ≤ 2*q ab 1 := by exact_mod_cast (hden ab hab 1).2
    constructor
    · apply (le_div_iff₀ hq).mpr
      linarith only [hlo₀,hhi₁]
    · apply (div_le_iff₀ hq).mpr
      linarith only [hlo₁,hhi₀]
  have hthird ab (hab : ab∈Gaps) :
      |mu ab 1*((Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+Mat 3)^3/mu ab 0-1| ≤ B*R^2/N^2 := by
    pm_1692 hR
    pm_1690
  have hp := paired_large_entry_closed_reference_gap_packing (τ:=fun _ => T)
    Refs Gaps (fun ab => x ab 0) (fun ab => x ab 1) Mat
    hσ hδ hF hT (fun _ => ⟨le_rfl,by linarith only [hT]⟩) hM hR hU
    (show 0 ≤ B*R^2/N^2 by positivity) hA hW hMat hc hlarge hsep hgap
    (fun ab hab => hx ab hab 0) (fun ab hab => hx ab hab 1)
    (fun ab hab => by
      change iteratedDeriv 2 (f 0) (x ab 0)/2∈Icc ab.1 ab.2
      rw [hlevel ab hab 0]
      exact hsourceGap ab hab)
    (fun ab hab => by
      change ((Mat 0:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+Mat 1)/
        ((Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+Mat 3)=iteratedDeriv 2 (f 1) (x ab 1)/2
      rw [hlevel ab hab 0,hlevel ab hab 1]
      exact hMatmap ab hab)
    (fun ab hab => by
      change (Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+Mat 3∈Icc (1/2:ℝ) 2
      rw [hlevel ab hab 0,hMatt ab hab]
      exact hratio ab hab)
    hthird
  have hInv : 1/M ≤ R^2/N^2 := (div_le_div_iff₀ hM (sq_pos_of_pos hN)).mpr
    (by simpa only [one_mul,mul_one,mul_comm] using hNscale)
  have heta : 2*Gamma*((modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)) ≤
      (Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)*(R^2/N^2) := by
    pm_1688
  apply hp.trans
  calc
    _ ≤ 64*Cphys*(Gamma^2*(B*R^2/N^2)+
        (Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)*(R^2/N^2))*R^2/
        (κ*|(Mat 2:ℝ)| *U)+2 := by
      apply add_le_add _ le_rfl
      pm_2680
      pm_6431
    _ = _ := by dsimp only [Cgap]; ring_nf


                                                                        
                                                                             
                                                                            
private theorem charted_selected_blocks
    {b B c C n nSource nSelected : ℕ}
    (hc : 0 < c) (hbB : b ≤ B) (hcC : c ≤ C) (hn : 0 < n)
    (hselection : nSource ≤ 6+c*(105+17*nSelected))
    (hblocks : (6+C*(105+544*B))*n ≤ nSource) :
    32*b*n ≤ nSelected := by
  have hbudget : 6+c*(105+544*b) ≤ 6+C*(105+544*B) := by gcongr
  have hlower := (Nat.mul_le_mul_right n hbudget).trans hblocks
  have hoffset : 6+105*c ≤ (6+105*c)*n := Nat.le_mul_of_pos_right _ hn
  have hmul : c*(17*(32*b*n)) ≤ c*(17*nSelected) := by
    nlinarith only [hlower,hselection,hoffset]
  have hh := Nat.le_of_mul_le_mul_left hmul hc
  exact Nat.le_of_mul_le_mul_left hh (by decide : 0 < (17:ℕ))

                                                                  
                                                                     
public  theorem charted_selected_source_length
    {b B c C n nSource nSelected : ℕ} {κ Cphys : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hbB : b ≤ B) (hcC : c ≤ C) (hn : 0 < n)
    (hκ : 0 < κ) (hCphys : 0 < Cphys)
    (hselection : nSource ≤ 6+c*(105+17*nSelected))
    (hblocks : (6+C*(105+544*B))*n ≤ nSource) :
    (2*κ/Cphys)*(n:ℝ) ≤ κ/(16*(b:ℝ)*Cphys)*(nSelected:ℝ) := by
  have hmass : (32:ℝ)*(b:ℝ)*(n:ℝ) ≤ (nSelected:ℝ) := by
    exact_mod_cast charted_selected_blocks hc hbB hcC hn hselection hblocks
  pm_4474 hbreal b Nat.cast_pos.mpr hb
  calc
    _ = κ/(16*(b:ℝ)*Cphys)*((32:ℝ)*(b:ℝ)*(n:ℝ)) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

                                                                 
                                                                     
                                                                     
                                                                    
                                                                        
theorem physicalModelPhase_actual_fourier_charted_long_gap_packing
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor n : ℕ) (hn : 0 < n)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < N)
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband)
    (hinv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2)
    (hc : Mat 2 ≠ 0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    (∀ ab∈Gaps, m0*n ≤ (S ab).card) →
    let L := (2*κ/Cphys)*(n:ℝ)
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    (Gaps.Nonempty →
      |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M) ∧
    (Gaps.card:ℝ) ≤ Cpack*R^4/(L^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2 := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor hblocks L Gamma Cthird Cpack Cfirst Csecond
  pm_1689
  pm_116 hLp L
  pm_1693
  pm_1697
  have hall ab (hab : ab∈Gaps) :=
    physicalModelPhase_actual_fourier_charted_reference_gap_quartic_witnesses
      Uref Refs (Bselect:=Bselect) (gapLo:=ab.1) (gapHi:=ab.2)
      (S ab) Q K₀ (rat ab) (vinv ab) (parity ab) (anchor ab) Mat
      (e ab) (r ab) (v ab) (s ab)
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (hx ab hab) (hwindow ab hab) (hden ab hab) hlambda hUband hθ hθmax (hcurv ab hab) (hinv ab hab) (hchart ab hab) (horientation ab hab) hBcut (hs ab hab) (hrefSet ab hab) (hparentSet ab hab) hsep (hwideL ab hab) (hwideU ab hab) hUref hBselectSize hcutMargin hselectedWrap (hreferenceDen ab hab) (hgapWidth ab hab) hRQ hselectedUpper hscaleTen (hfamilyGap ab hab)
      (hsourceColor ab hab) (hS ab hab) (hlevel ab hab) (hcolor ab hab) (hnear ab hab)
      hsmall hNR hRN hNcube hminscale hMatdet (hMatt ab hab) (hMatmap ab hab) hMatgamma
      hNtwo (hL ab hab) (hU ab hab) (hanchor ab hab) (hcut ab hab) (hcount ab hab)
  pm_1695
  pm_1698 charted_selected_source_length
  · obtain ⟨ab₀,hab₀⟩ := hne
    pm_1691
    have hCR := (physical_source_quartic_constants_nonneg hσ hδ0).1
    have hΓ : 0 ≤ Gamma := div_nonneg hCphys.le hκ.le
    have hCthird : 0 ≤ Cthird :=
      mul_nonneg hΓ (add_nonneg (mul_nonneg (by norm_num) (hKp ab₀ hab₀))
        (mul_nonneg (by norm_num) hCR))
    have hCfirst : 0 ≤ Cfirst :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le)
        (add_nonneg (mul_nonneg (sq_nonneg Gamma) hCthird)
          (div_nonneg (mul_nonneg hΓ hC₃) hκ.le))) (sq_nonneg κ)
    pm_1694
    have htransport ab : (ep ab 1:ℝ)=(Mat 0:ℝ)*ep ab 0+Mat 1*rp ab 0 ∧
        (vp ab 1:ℝ)=(Mat 0:ℝ)*vp ab 0+Mat 1*sp ab 0 ∧
        (rp ab 1:ℝ)=(Mat 2:ℝ)*ep ab 0+Mat 3*rp ab 0 ∧
        (sp ab 1:ℝ)=(Mat 2:ℝ)*vp ab 0+Mat 3*sp ab 0 := by
      simp [ep,vp,rp,sp,Int.cast_add,Int.cast_mul]
    pm_1696
    have hFirst := physicalModelPhase_quartic_matrix_long_block_first_condition
      (e:=fun i => (ep ab₀ i:ℝ)) (r:=fun i => (rp ab₀ i:ℝ))
      (v:=fun i => (vp ab₀ i:ℝ)) (s:=fun i => (sp ab₀ i:ℝ))
      (x₁:=curve ab₀) (α:=alpha ab₀) (β:=beta ab₀) (z ab₀) Mat
      hσ hδ hF hT hM hN hR (hLsource ab₀ hab₀) (hNL ab₀ hab₀) (hd ab₀ hab₀)
      (hKp ab₀ hab₀) hA hW (fun i => (hxr ab₀ hab₀ i).2.1)
      (fun t ht i => ((hcurve ab₀ hab₀ t ht).2 i).1)
      (fun i => by
        exact_mod_cast (mul_ne_zero_iff.mp (hxr ab₀ hab₀ i).1.ne').1)
      (fun i => by
        exact_mod_cast hdetp ab₀ hab₀ i)
      (fun t ht i => ((hcurve ab₀ hab₀ t ht).2 i).2.1)
      (fun t ht i => ((hcurve ab₀ hab₀ t ht).2 i).2.2.1)
      (hmono ab₀ hab₀) hscale hMatdet (htransport ab₀)
      (fun i => (hxr ab₀ hab₀ i).2.2.1)
      (fun t ht i => ((hcurve ab₀ hab₀ t ht).2 i).2.2.2.1)
      (fun t ht i => ((hcurve ab₀ hab₀ t ht).2 i).2.2.2.2)
      (hspacing ab₀ hab₀) (hres ab₀ hab₀)
    have hFirstUnit :
        |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M := by
      apply hFirst.trans
      apply add_le_add _ le_rfl
      apply div_le_div_of_nonneg_left (mul_nonneg hCfirst (by positivity)) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hLp.le (hlong ab₀ hab₀) 3) (sq_nonneg N)
    obtain ⟨_t,_ht,hpack⟩ := physicalModelPhase_quartic_long_reference_gap_packing
      Refs Gaps Mat z4 xref
      (fun ab i => (ep ab i:ℝ)) (fun ab i => (rp ab i:ℝ))
      (fun ab i => (vp ab i:ℝ)) (fun ab i => (sp ab i:ℝ))
      curve d alpha beta hσ hδ hF hT hM hN hR hUp hLp hNLL (hKp ab₀ hab₀)
      hA hW hMatdet hc hlarge
      (by
        intro a ha b hb hne
        calc
          (Uref:ℝ)/(4*R^2)=((Uref:ℝ)/R^2)/4 := by ring
          _ ≤ |a-b| := (hsep a ha b hb hne).le)
      hgap hd
      (fun ab hab i => (hxr ab hab i).2.1)
      (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).1)
      (fun ab hab i => by
        exact_mod_cast (mul_ne_zero_iff.mp (hxr ab hab i).1.ne').1)
      (fun ab hab i => by
        exact_mod_cast hdetp ab hab i)
      (fun ab hab t ht i => ⟨((hcurve ab hab t (hsub ab hab ht)).2 i).2.1,
        ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.1⟩)
      (fun ab hab => (hmono ab hab).comp htake) (fun ab _ => htransport ab)
      (fun ab hab i => (hxr ab hab i).2.2.1)
      (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.2.1)
      (fun ab hab => ⟨hends ab hab 0,hends ab hab 3⟩)
      (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.2.2)
      (fun ab hab i => (mul_le_mul_of_nonneg_right (hlong ab hab) hN.le).trans
        (hspacing ab hab (⟨i.val,by omega⟩ : Fin 7)))
      (fun ab hab i => hres ab hab (take i))
    exact ⟨fun _ => hFirstUnit,hpack⟩
  · refine ⟨fun hh => False.elim (hne hh),?_⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
    pm_2669
    obtain ⟨hCR,hCN⟩ := physical_source_quartic_constants_nonneg hσ hδ0
    pm_1856
    dsimp only [Cpack,Cthird,Kres,Gamma,Cc,Ct,C₂,C₃]
    positivity


                                                                       
                                                                          
theorem physicalModelPhase_actual_fourier_charted_reference_sample_mass
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < N)
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband)
    (hinv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2)
    (hc : Mat 2 ≠ 0)
    (hlarge : 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    (∀ ab∈Gaps, m0 ≤ (S ab).card) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤
      4*(m0:ℝ)*((2*Cfirst*R^4/(Lunit^3*N^2)/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+
        Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))) := by
  pm_4924 hS Lunit Gamma Cthird Cpack Cfirst
  let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
  pm_1689
  pm_1700
  pm_1699
  pm_1781 hCmat hc
  pm_1703
  have habsorb : 2*(Csecond*N*R^2/M) ≤ |(Mat 2:ℝ)| := by
    have hs : 64*(modelPhaseJetCoefficient σ 3+δ)*N*R^2 ≤ |(Mat 2:ℝ)| *κ^2*M := by
      apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hM)).mp
      calc
        _ = (64*(modelPhaseJetCoefficient σ 3+δ)*M^2)*(N*R^2) := by ring
        _ ≤ (|(Mat 2:ℝ)| *κ^2*T)*(N*R^2) :=
          mul_le_mul_of_nonneg_right hlarge (by positivity)
        _ = (|(Mat 2:ℝ)| *κ^2)*(T*N*R^2) := by ring
        _ = _ := by rw [hscale]; ring
    calc
      _ = (64*(modelPhaseJetCoefficient σ 3+δ)*N*R^2)/(κ^2*M) := by
        dsimp only [Csecond]
        ring
      _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hs])
  let n := fun ab => (S ab).card/m0
  have hn ab (hab : ab∈Gaps) := quotient_block_mass (S ab).card m0 hm0 (hS ab hab)
  have hfamily (G : Finset (ℝ × ℝ)) (hsub : G ⊆ Gaps) (m : ℕ) (hm : 0 < m)
      (hblocks : ∀ ab∈G, m0*m ≤ (S ab).card) :
      (G.Nonempty → |(Mat 2:ℝ)| ≤
        Cfirst*R^4/((Lunit*(m:ℝ))^3*N^2)+Csecond*N*R^2/M) ∧
      (G.card:ℝ) ≤ Cpack*R^4/((Lunit*(m:ℝ))^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2 := by
    exact physicalModelPhase_actual_fourier_charted_long_gap_packing
      Uref Refs G (Bselect:=Bselect) Bmajor Cmajor m hm
      S Q K₀ rat vinv parity anchor Mat e r v s
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (fun ab hab => hx ab (hsub hab)) (fun ab hab => hwindow ab (hsub hab)) (fun ab hab => hden ab (hsub hab)) hlambda hUband hθ hθmax (fun ab hab => hcurv ab (hsub hab)) (fun ab hab => hinv ab (hsub hab)) (fun ab hab => hchart ab (hsub hab)) (fun ab hab => horientation ab (hsub hab)) hBcut (fun ab hab => hs ab (hsub hab)) (fun ab hab => hrefSet ab (hsub hab)) (fun ab hab => hparentSet ab (hsub hab)) hsep (fun ab hab => hwideL ab (hsub hab)) (fun ab hab => hwideU ab (hsub hab)) hUref hBselectSize hcutMargin hselectedWrap (fun ab hab => hreferenceDen ab (hsub hab)) (fun ab hab => hgapWidth ab (hsub hab)) hRQ hselectedUpper hscaleTen (fun ab hab => hfamilyGap ab (hsub hab))
      hc hlarge32 (fun ab hab => hgap ab (hsub hab))
      (fun ab hab => hsourceColor ab (hsub hab)) (fun ab hab => hlevel ab (hsub hab)) (fun ab hab => hcolor ab (hsub hab)) (fun ab hab => hnear ab (hsub hab)) hsmall hNR hRN hNcube hminscale hMatdet (fun ab hab => hMatt ab (hsub hab)) (fun ab hab => hMatmap ab (hsub hab)) hMatgamma hNtwo (fun ab hab => hL ab (hsub hab)) (fun ab hab => hU ab (hsub hab)) (fun ab hab => hanchor ab (hsub hab)) (fun ab hab => hcut ab (hsub hab)) (fun ab hab => hcount ab (hsub hab))
      hsize hD hΔ hBsize
      (fun ab hab => hBmajor ab (hsub hab))
      (fun ab hab => hCmajor ab (hsub hab)) hblocks
  have hfirst ab (hab : ab∈Gaps) :
      |(Mat 2:ℝ)| ≤ Cfirst*R^4/((Lunit*(n ab:ℝ))^3*N^2)+Csecond*N*R^2/M := by
    have hs : ({ab} : Finset (ℝ × ℝ)) ⊆ Gaps := Finset.singleton_subset_iff.mpr hab
    have hb : ∀ t∈({ab} : Finset (ℝ × ℝ)), m0*n ab ≤ (S t).card := by
      intro t ht
      have he : t=ab := Finset.mem_singleton.mp ht
      subst t
      exact (hn ab hab).2.1
    exact (hfamily {ab} hs (n ab) (hn ab hab).1 hb).1 (Finset.singleton_nonempty ab)
  have hcap ab (hab : ab∈Gaps) :
      (n ab:ℝ)^3*|(Mat 2:ℝ)| ≤ 2*(Cfirst*R^4)/(Lunit^3*N^2) :=
    two_term_first_cubic_cap hCmat.le hN hunit
      (mul_pos hunit (by exact_mod_cast (hn ab hab).1))
      (Nat.cast_nonneg _) le_rfl (hfirst ab hab) habsorb
  let Cost := Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))
  have htail (m : ℕ) (hm : 0 < m) :
      ((Gaps.filter (fun ab => m ≤ n ab)).card:ℝ) ≤ 2+Cost/(m:ℝ)^2 := by
    pm_1701
    exact (hfamily Long hin m hm hb).2.trans_eq (by dsimp only [Cost]; ring)
  have hsum := finite_occupied_cubic_tail_sum Gaps n (by norm_num : (0:ℝ) ≤ 2)
    (show 0 ≤ Cost by dsimp only [Cost]; positivity)
    (show 0 ≤ 2*(Cfirst*R^4)/(Lunit^3*N^2) by positivity) hCmat hcap htail
  pm_1702
  calc
    _ ≤ 2*(m0:ℝ)*(∑ ab∈Gaps, (n ab:ℝ)) := hmass
    _ ≤ 2*(m0:ℝ)*(2*(2*(Cfirst*R^4)/(Lunit^3*N^2)/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+2*Cost) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp only [Cost]; ring_nf


                                                                       
                                                                            
theorem physicalModelPhase_actual_fourier_charted_all_reference_sample_mass
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < N)
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband)
    (hinv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2)
    (hc : Mat 2 ≠ 0)
    (hlarge : 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤
      4*(m0:ℝ)*((2*Cfirst*R^4/(Lunit^3*N^2)/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+
        Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))+
      (m0:ℝ)*(2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))) := by
  pm_4924 Lunit Gamma Cthird Cpack Cfirst Cgap
  pm_1705
  have hlong := physicalModelPhase_actual_fourier_charted_reference_sample_mass
    Uref Refs Long (Bselect:=Bselect) Bmajor Cmajor S Q K₀ rat vinv parity anchor Mat e r v s
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (fun ab hab => hx ab (hinLong hab)) (fun ab hab => hwindow ab (hinLong hab)) (fun ab hab => hden ab (hinLong hab)) hlambda hUband hθ hθmax (fun ab hab => hcurv ab (hinLong hab)) (fun ab hab => hinv ab (hinLong hab)) (fun ab hab => hchart ab (hinLong hab)) (fun ab hab => horientation ab (hinLong hab)) hBcut (fun ab hab => hs ab (hinLong hab)) (fun ab hab => hrefSet ab (hinLong hab)) (fun ab hab => hparentSet ab (hinLong hab)) hsep (fun ab hab => hwideL ab (hinLong hab)) (fun ab hab => hwideU ab (hinLong hab)) hUref hBselectSize hcutMargin hselectedWrap (fun ab hab => hreferenceDen ab (hinLong hab)) (fun ab hab => hgapWidth ab (hinLong hab)) hRQ hselectedUpper hscaleTen (fun ab hab => hfamilyGap ab (hinLong hab))
    hc hlarge (fun ab hab => hgap ab (hinLong hab))
    (fun ab hab => hsourceColor ab (hinLong hab)) (fun ab hab => hlevel ab (hinLong hab)) (fun ab hab => hcolor ab (hinLong hab)) (fun ab hab => hnear ab (hinLong hab)) hsmall hNR hRN hNcube hminscale hMatdet (fun ab hab => hMatt ab (hinLong hab)) (fun ab hab => hMatmap ab (hinLong hab)) hMatgamma hNtwo (fun ab hab => hL ab (hinLong hab)) (fun ab hab => hU ab (hinLong hab)) (fun ab hab => hanchor ab (hinLong hab)) (fun ab hab => hcut ab (hinLong hab)) (fun ab hab => hcount ab (hinLong hab))
    hsize hD hΔ hBsize
    (fun ab hab => hBmajor ab (hinLong hab))
    (fun ab hab => hCmajor ab (hinLong hab))
    (fun _ hab => (Finset.mem_filter.mp hab).2)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  pm_1691
  pm_1703
  pm_1693
  pm_1756
  have hNscale : N^2 ≤ M*R^2 := by
    have hm := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ N by linarith only [hNtwo])
      (sq_nonneg N)
    nlinarith only [hm,hNcube]
  have hchoose ab (hab : ab∈Short) : ∃ j, j∈S ab :=
    (Finset.mem_filter.mp hab).2.1
  choose! j hj using hchoose
  have hshortcount :
      (Short.card:ℝ) ≤ 2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ)) := by
    exact physicalModelPhase_actual_fourier_large_entry_closed_reference_gap_count
      Refs Short Mat Q K₀ (fun ab => rat ab (j ab)) (fun ab => vinv ab (j ab))
      (fun ab => parity ab (j ab)) (fun ab => x ab (j ab))
      hσ hδ hF₃ hT hM hN (zero_lt_one.trans_le hR) hUp hQ hscale hmesh hNscale
      hA hW hMatdet hc hlarge32
      (by
        intro a ha b hb hne
        calc
          (Uref:ℝ)/(4*R^2)=((Uref:ℝ)/R^2)/4 := by ring
          _ ≤ |a-b| := (hsep a ha b hb hne).le)
      (fun ab hab => hgap ab (hinShort hab))
      (fun ab hab => hx ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hden ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hinv ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hlevel ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hcolor ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hnear ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hMatt ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hMatmap ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hfamilyGap ab (hinShort hab) _ (hj ab hab))
  have hshortmass : (∑ ab∈Short, ((S ab).card:ℝ)) ≤
      (m0:ℝ)*(2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))) := by
    calc
      _ ≤ ∑ _ab∈Short, (m0:ℝ) := by
        pm_8042
      _ = (m0:ℝ)*(Short.card:ℝ) := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hshortcount (Nat.cast_nonneg _)
  pm_1704
  rw [hpartition]
  exact add_le_add hlong hshortmass

                                                                       
                                                              
theorem fourier_matrix_narrowed_coordinate_entry_bound
    (q e vinv : Fin 2 → ℤ) (A : Fin 4 → ℤ) {Q K V N R : ℝ}
    (hq : ∀ i, 0 < q i) (hK : 1 ≤ K) (hV : 1 ≤ V)
    (hN : 0 < N)
    (hmesh : Q*N ≤ K*R^2)
    (hband : ∀ i, (q i:ℝ) ≤ Q ∧ Q ≤ 2*q i)
    (hinv : ∀ i, q i ∣ e i*vinv i-1)
    (hdet : A 0*A 3-A 1*A 2=1)
    (ht : (A 2:ℝ)*((e 0:ℝ)/q 0)+A 3=(q 1:ℝ)/q 0)
    (hmap : ((A 0:ℝ)*((e 0:ℝ)/q 0)+A 1)/
      ((A 2:ℝ)*((e 0:ℝ)/q 0)+A 3)=(e 1:ℝ)/q 1)
    (hgamma : |(A 2:ℝ)| ≤ Q^2/(6*K^2))
    (hnear : |Int.fract (-(vinv 0:ℝ)/q 0)-
      Int.fract (-(vinv 1:ℝ)/q 1)| ≤ 1/(6*K^2*V)) :
    |(A 2:ℝ)| ≤ Q^2/(6*K^2*V) ∧ |(A 2:ℝ)| ≤ R^4/(6*N^2*V) := by
  pm_1610 hKp K hK hVp V hV
  pm_6432
  pm_7390 hQp
  have hnear₀ : |Int.fract (-(vinv 0:ℝ)/q 0)-
      Int.fract (-(vinv 1:ℝ)/q 1)| ≤ 1/(6*K^2) := by
    apply hnear.trans
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_left hV (show 0 ≤ 6*K^2 by positivity)]
  obtain ⟨v,hv,hs,htransport⟩ := fourier_matrix_normalized_chart_transport
    q e vinv A (Q:=Q) (K:=K) hq hK hband hinv hdet ht hmap hgamma hnear₀
  let s := fun i => -vinv i-q i*⌊-(vinv i:ℝ)/q i⌋
  have hc : A 2=q 0*s 1-s 0*q 1 := by
    have hden := (htransport 1 0).2
    have hcomp := (htransport 0 1).2
    simp only [mul_one,mul_zero,add_zero,zero_add] at hden hcomp
    change A 2*v 0+A 3*s 0=s 1 at hcomp
    linear_combination -(A 2)*(hv 0)+(q 0)*hcomp-(s 0)*hden
  have hcR : (A 2:ℝ)=(q 0:ℝ)*s 1-(s 0:ℝ)*q 1 := by exact_mod_cast hc
  have hp : 0 < (q 0:ℝ)*q 1 := mul_pos (hqr 0) (hqr 1)
  have hentry : |(A 2:ℝ)| ≤ Q^2/(6*K^2*V) := by
    calc
      _ = |(s 1:ℝ)/q 1-(s 0:ℝ)/q 0| *((q 0:ℝ)*q 1) := by
        rw [←abs_of_pos hp,←abs_mul,hcR]
        congr 1
        field_simp [(hqr 0).ne',(hqr 1).ne']
      _ ≤ (1/(6*K^2*V))*((q 0:ℝ)*q 1) := by
        pm_7955 hs
      _ ≤ (1/(6*K^2*V))*Q^2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith only [mul_le_mul (hband 0).1 (hband 1).1 (hqr 1).le hQp.le]
      _ = _ := by ring
  refine ⟨hentry,hentry.trans ?_⟩
  apply (div_le_div_iff₀ (by positivity : 0 < 6*K^2*V)
    (by positivity : 0 < 6*N^2*V)).mpr
  pm_8136 hsq hQp hN hmesh
  have hm := mul_le_mul_of_nonneg_right hsq (show 0 ≤ 6*V by positivity)
  nlinarith only [hm]


private theorem mobius_upper_right_large_action_comparison
    {a b c d x y lambda H : ℝ}
    (hlambda : 0 ≤ lambda)
    (hdet : a*d-b*c=1) (htl : (1:ℝ)/2 ≤ c*x+d) (htu : c*x+d ≤ 2)
    (hmap : (a*x+b)/(c*x+d)=y)
    (hx : lambda ≤ |x| ∧ |x| ≤ H) (hy : lambda ≤ |y| ∧ |y| ≤ H)
    (hlarge : 8*H ≤ |c| *lambda^2) :
    |c| *lambda^2/2 ≤ |b| ∧ |b| ≤ (3/2)*|c| *H^2 := by
  let t := c*x+d
  have ht : 0 < t := by dsimp only [t]; linarith only [htl]
  have hH : 0 ≤ H := (abs_nonneg x).trans hx.2
  have he := (div_eq_iff ht.ne').mp hmap
  have ha : a=c*y+1/t := by
    have hid : (a-c*y)*t=1 := by
      dsimp only [t]
      pm_6213
    have hh : a-c*y=1/t := (eq_div_iff ht.ne').mpr hid
    linarith only [hh]
  have herrorId : b+c*x*y=t*y-x/t := by
    rw [ha] at he
    change (c*y+1/t)*x+b=y*t at he
    linear_combination he
  have htInv : 1/t ≤ 2 := by
    apply (div_le_iff₀ ht).mpr
    change (1:ℝ)/2 ≤ t at htl
    linarith only [htl]
  have herror : |b+c*x*y| ≤ 4*H := by
    rw [herrorId]
    calc
      _ ≤ |t*y|+|x/t| := abs_sub _ _
      _ = t*|y|+(1/t)*|x| := by
        rw [abs_mul,abs_div,abs_of_pos ht]
        ring
      _ ≤ 2*H+2*H := add_le_add
        (mul_le_mul htu hy.2 (abs_nonneg y) (by norm_num))
        (mul_le_mul htInv hx.2 (abs_nonneg x) (by norm_num))
      _ = _ := by ring
  have hprod : |c*x*y|=|c| *|x| *|y| := by rw [abs_mul,abs_mul]
  have hlo : |c| *lambda^2 ≤ |c*x*y| := by
    rw [hprod]
    have hh := mul_le_mul hx.1 hy.1 hlambda (abs_nonneg x)
    nlinarith only [mul_le_mul_of_nonneg_left hh (abs_nonneg c)]
  have hhi : |c*x*y| ≤ |c| *H^2 := by
    rw [hprod]
    have hh := mul_le_mul hx.2 hy.2 (abs_nonneg y) hH
    nlinarith only [mul_le_mul_of_nonneg_left hh (abs_nonneg c)]
  have hlowTri : |c*x*y| ≤ |b+c*x*y|+|b| := by
    calc
      _ = |(b+c*x*y)-b| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  have hhighTri : |b| ≤ |b+c*x*y|+|c*x*y| := by
    calc
      _ = |(b+c*x*y)-(c*x*y)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  constructor
  · nlinarith only [hlo,hlowTri,herror,hlarge]
  · nlinarith only [hlo,hhi,hhighTri,herror,hlarge]

private theorem mobius_reciprocal_entry_bounds
    {a b c d x y lambda : ℝ}
    (hlambda : 0 < lambda)
    (hdet : a*d-b*c=1) (ht : c*x+d ≠ 0)
    (hmap : (a*x+b)/(c*x+d)=y)
    (hx : lambda ≤ |x|) (hy : lambda ≤ |y|)
    (hnumlo : (1:ℝ)/2 ≤ (a*x+b)/x)
    (hnumhi : (a*x+b)/x ≤ 2) :
    |a| ≤ |b|/lambda+2 ∧ |d| ≤ |b|/lambda+2 := by
  have hx0 : x ≠ 0 := abs_pos.mp (hlambda.trans_le hx)
  have hy0 : y ≠ 0 := abs_pos.mp (hlambda.trans_le hy)
  have he := (div_eq_iff ht).mp hmap
  have hden : b*(1/x)+a=(a*x+b)/x := by
    field_simp [hx0]
    ring
  have hdenp : 0 < b*(1/x)+a := by rw [hden]; linarith only [hnumlo]
  have hrmap : (d*(1/x)+c)/(b*(1/x)+a)=1/y := by
    apply (div_eq_iff hdenp.ne').mpr
    field_simp [hx0,hy0]
    nlinarith only [he]
  pm_7604 hrx x hx
  pm_7604 hry y hy
  have hh := bourgain_mobius_entry_bounds
    (a:=d) (b:=c) (c:=b) (d:=a) (x:=1/x) (y:=1/y)
    (by nlinarith only [hdet]) (by rw [hden]; exact hnumlo)
    (by rw [hden]; exact hnumhi) hrmap hrx hry
  constructor
  · simpa only [mul_one_div] using hh.2
  · simpa only [mul_one_div] using hh.1

private theorem cubic_reciprocal_majorant {K c Gamma : ℝ}
    (hK : 0 ≤ K) (hc : 0 < c) (hcap : c ≤ Gamma) :
    (K/c)^((3:ℝ)⁻¹) ≤ K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)/c := by
  apply (le_div_iff₀ hc).mpr
  calc
    _ = K^((3:ℝ)⁻¹)*c^(1-(3:ℝ)⁻¹) := by
      rw [Real.div_rpow hK hc.le,Real.rpow_sub hc,Real.rpow_one]
      ring
    _ ≤ K^((3:ℝ)⁻¹)*Gamma^(1-(3:ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc.le hcap (by norm_num))
        (Real.rpow_nonneg hK _)
    _ = _ := by norm_num

private theorem resonance_matrix_cubic_weight_sum
    (S : Finset (Fin 4 → ℤ)) {Vbound Gamma A K B : ℝ}
    (hV : 0 ≤ Vbound) (hGamma : 0 ≤ Gamma)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hdet : ∀ Mat∈S, Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hc : ∀ Mat∈S, Mat 2 ≠ 0 ∧ |(Mat 2:ℝ)| ≤ Gamma)
    (ha : ∀ Mat∈S, |(Mat 0:ℝ)| ≤ |(Mat 2:ℝ)| *Vbound+2)
    (hd : ∀ Mat∈S, |(Mat 3:ℝ)| ≤ |(Mat 2:ℝ)| *Vbound+2) :
    ∑ Mat∈S,(A*(K/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+B/|(Mat 2:ℝ)|) ≤
      ((2*Gamma+1)*(2*Vbound+5)^2)*(A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B) := by
  have hw := resonance_matrix_reciprocal_sum S hV hGamma hdet hc ha hd
  pm_1086 hp
  pm_1487 C
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hK _))
      (Real.rpow_nonneg hGamma _)) hB
  calc
    _ ≤ ∑ Mat∈S,C*(1/|(Mat 2:ℝ)|) := by
      apply Finset.sum_le_sum
      intro Mat hMat
      have hh := mul_le_mul_of_nonneg_left
        (cubic_reciprocal_majorant hK (hp Mat hMat) (hc Mat hMat).2) hA
      dsimp only [C]
      calc
        _ ≤ A*(K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)/|(Mat 2:ℝ)|)+B/|(Mat 2:ℝ)| :=
          add_le_add hh le_rfl
        _ = _ := by ring
    _ = C*(∑ Mat∈S,1/|(Mat 2:ℝ)|) := (Finset.mul_sum S _ _).symm
    _ ≤ C*((2*Gamma+1)*(2*Vbound+5)^2) := mul_le_mul_of_nonneg_left hw hC
    _ = _ := by dsimp only [C]; ring

private theorem resonance_matrix_reciprocal_cubic_weight_sum
    (S : Finset (Fin 4 → ℤ)) {X Gamma Theta A K B : ℝ}
    (hX : 0 ≤ X) (hGamma : 0 ≤ Gamma) (hTheta : 0 ≤ Theta)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hdet : ∀ Mat∈S, Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hc : ∀ Mat∈S, Mat 2 ≠ 0)
    (hb : ∀ Mat∈S, Mat 1 ≠ 0 ∧ |(Mat 1:ℝ)| ≤ Gamma)
    (hcompare : ∀ Mat∈S, |(Mat 1:ℝ)| ≤ Theta*|(Mat 2:ℝ)|)
    (ha : ∀ Mat∈S, |(Mat 0:ℝ)| ≤ |(Mat 1:ℝ)| *X+2)
    (hd : ∀ Mat∈S, |(Mat 3:ℝ)| ≤ |(Mat 1:ℝ)| *X+2) :
    ∑ Mat∈S,(A*(K/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+B/|(Mat 2:ℝ)|) ≤
      ((2*Gamma+1)*(2*X+5)^2)*
        (A*(Theta*K)^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+Theta*B) := by
  classical
  let flip := fun Mat : Fin 4 → ℤ => (![Mat 3,Mat 2,Mat 1,Mat 0] : Fin 4 → ℤ)
  have hflip Mat : flip (flip Mat)=Mat := by
    funext i
    fin_cases i <;> rfl
  have hinj : Function.Injective flip := by
    intro Mat Mat' he
    have hh := congrArg flip he
    rw [hflip,hflip] at hh
    exact hh
  have hw := resonance_matrix_cubic_weight_sum (S.image flip)
    hX hGamma hA (mul_nonneg hTheta hK) (mul_nonneg hTheta hB)
    (by
      pm_1706
      change Mat 3*Mat 0-Mat 2*Mat 1=1
      nlinarith only [hdet Mat hMat])
    (by
      pm_1706
      exact hb Mat hMat)
    (by
      pm_1706
      exact hd Mat hMat)
    (by
      pm_1706
      exact ha Mat hMat)
  rw [Finset.sum_image hinj.injOn] at hw
  apply le_trans _ hw
  apply Finset.sum_le_sum
  intro Mat hMat
  have hcp : 0 < |(Mat 2:ℝ)| := abs_pos.mpr (by exact_mod_cast hc Mat hMat)
  have hbp : 0 < |(Mat 1:ℝ)| := abs_pos.mpr (by exact_mod_cast (hb Mat hMat).1)
  pm_4980 hKbound K hK
  pm_4980 hBbound B hB
  exact add_le_add (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (div_nonneg hK hcp.le) hKbound (by norm_num)) hA) hBbound

private theorem resonance_matrix_curvature_band_cubic_weight_sum
    (S : Finset (Fin 4 → ℤ)) (x y : (Fin 4 → ℤ) → ℝ)
    {lambda H Gamma A K B : ℝ}
    (hlambda : 0 < lambda) (hGamma : 0 ≤ Gamma)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hdet : ∀ Mat∈S, Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hc : ∀ Mat∈S, Mat 2 ≠ 0 ∧ |(Mat 2:ℝ)| ≤ Gamma)
    (hx : ∀ Mat∈S, lambda ≤ |x Mat| ∧ |x Mat| ≤ H)
    (hy : ∀ Mat∈S, lambda ≤ |y Mat| ∧ |y Mat| ≤ H)
    (ht : ∀ Mat∈S, (1:ℝ)/2 ≤ (Mat 2:ℝ)*x Mat+Mat 3 ∧
      (Mat 2:ℝ)*x Mat+Mat 3 ≤ 2)
    (hmap : ∀ Mat∈S, ((Mat 0:ℝ)*x Mat+Mat 1)/
      ((Mat 2:ℝ)*x Mat+Mat 3)=y Mat)
    (hnum : ∀ Mat∈S, (1:ℝ)/2 ≤ ((Mat 0:ℝ)*x Mat+Mat 1)/x Mat ∧
      ((Mat 0:ℝ)*x Mat+Mat 1)/x Mat ≤ 2)
    (hlarge : ∀ Mat∈S, 8*H ≤ |(Mat 2:ℝ)| *lambda^2) :
    ∑ Mat∈S,(A*(K/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+B/|(Mat 2:ℝ)|) ≤
      588*(H/lambda)^2*H^2*Gamma*
        (A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B) := by
  classical
  pm_1487 E
  pm_2280
  have hFactor {g v : ℝ} (hg : 1 ≤ g) (hv : 1 ≤ v) :
      (2*g+1)*(2*v+5)^2 ≤ 147*g*v^2 := by
    pm_4914 hg0 g hg hv0 v hv
    have hgl : 2*g+1 ≤ 3*g := by linarith only [hg]
    have hvl : 2*v+5 ≤ 7*v := by linarith only [hv]
    have hvp := pow_le_pow_left₀ (by positivity : 0 ≤ 2*v+5) hvl 2
    have hh := mul_le_mul hgl hvp (sq_nonneg _) (by positivity : 0 ≤ 3*g)
    nlinarith only [hh]
  by_cases hS : S.Nonempty
  · obtain ⟨Mat₀,hMat₀⟩ := hS
    have hLH : lambda ≤ H := (hx Mat₀ hMat₀).1.trans (hx Mat₀ hMat₀).2
    have hH : 0 < H := hlambda.trans_le hLH
    have hGammaOne : 1 ≤ Gamma :=
      (show (1:ℝ) ≤ |(Mat₀ 2:ℝ)| by exact_mod_cast Int.one_le_abs (hc Mat₀ hMat₀).1).trans
        (hc Mat₀ hMat₀).2
    pm_1086 hcp
    have hdetR Mat (hMat : Mat∈S) :
        (Mat 0:ℝ)*Mat 3-(Mat 1:ℝ)*Mat 2=1 := by exact_mod_cast hdet Mat hMat
    by_cases hWide : 1 ≤ H
    · have hentries Mat (hMat : Mat∈S) :=
        bourgain_mobius_entry_bounds (hdetR Mat hMat) (ht Mat hMat).1 (ht Mat hMat).2
          (hmap Mat hMat) (hx Mat hMat).2 (hy Mat hMat).2
      have hw := resonance_matrix_cubic_weight_sum S hH.le hGamma hA hK hB hdet hc
        (fun Mat hMat => (hentries Mat hMat).1) (fun Mat hMat => (hentries Mat hMat).2)
      pm_4971 hratio H lambda le_div_iff₀ hlambda hLH
      have hsquare : 1 ≤ (H/lambda)^2 := by nlinarith only [hratio,sq_nonneg (H/lambda-1)]
      have hscale := mul_le_mul_of_nonneg_right hsquare (sq_nonneg H)
      have hmul := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 147*Gamma by positivity)
      have hpos : 0 ≤ (H/lambda)^2*H^2*Gamma := by positivity
      have hfac : 147*Gamma*H^2 ≤ 588*(H/lambda)^2*H^2*Gamma := by
        nlinarith only [hmul,hpos]
      exact hw.trans ((mul_le_mul_of_nonneg_right (hFactor hGammaOne hWide) hE).trans
        (mul_le_mul_of_nonneg_right hfac hE))
    · let Theta := 2*H^2
      let G := Theta*Gamma
      pm_116 hTheta Theta
      have hG : 0 ≤ G := mul_nonneg hTheta.le hGamma
      have hcompare Mat (hMat : Mat∈S) : |(Mat 1:ℝ)| ≤ Theta*|(Mat 2:ℝ)| := by
        pm_1707
        have hp := mul_nonneg (abs_nonneg (Mat 2:ℝ)) (sq_nonneg H)
        dsimp only [Theta]
        nlinarith only [hh.2,hp]
      have hb Mat (hMat : Mat∈S) : Mat 1 ≠ 0 ∧ |(Mat 1:ℝ)| ≤ G := by
        pm_1707
        have hcpos := hcp Mat hMat
        have hp : 0 < |(Mat 1:ℝ)| :=
          (show 0 < |(Mat 2:ℝ)| *lambda^2/2 by positivity).trans_le hh.1
        refine ⟨?_,(hcompare Mat hMat).trans
          (mul_le_mul_of_nonneg_left (hc Mat hMat).2 hTheta.le)⟩
        exact_mod_cast abs_pos.mp hp
      have hentries Mat (hMat : Mat∈S) :=
        mobius_reciprocal_entry_bounds hlambda (hdetR Mat hMat)
          (show (Mat 2:ℝ)*x Mat+Mat 3 ≠ 0 by linarith only [(ht Mat hMat).1])
          (hmap Mat hMat) (hx Mat hMat).1 (hy Mat hMat).1
          (hnum Mat hMat).1 (hnum Mat hMat).2
      have hw := resonance_matrix_reciprocal_cubic_weight_sum S
        (show 0 ≤ 1/lambda by positivity) hG hTheta.le hA hK hB hdet
        (fun Mat hMat => (hc Mat hMat).1) hb hcompare
        (fun Mat hMat => by simpa only [mul_one_div] using (hentries Mat hMat).1)
        (fun Mat hMat => by simpa only [mul_one_div] using (hentries Mat hMat).2)
      have hGOne : 1 ≤ G :=
        (show (1:ℝ) ≤ |(Mat₀ 1:ℝ)| by exact_mod_cast Int.one_le_abs (hb Mat₀ hMat₀).1).trans
          (hb Mat₀ hMat₀).2
      have hInv : 1 ≤ 1/lambda := (le_div_iff₀ hlambda).mpr
        (by linarith only [hLH,le_of_not_ge hWide])
      pm_5171 Theta hTheta
      have he : A*(Theta*K)^((3:ℝ)⁻¹)*G^((2:ℝ)/3)+Theta*B=Theta*E := by
        dsimp only [G,E]
        rw [Real.mul_rpow hTheta.le hK,Real.mul_rpow hTheta.le hGamma]
        calc
          _ = (Theta^((3:ℝ)⁻¹)*Theta^((2:ℝ)/3))*
              (A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3))+Theta*B := by ring
          _ = _ := by rw [hpow]; ring
      rw [he] at hw
      calc
        _ ≤ ((2*G+1)*(2*(1/lambda)+5)^2)*(Theta*E) := hw
        _ ≤ (147*G*(1/lambda)^2)*(Theta*E) :=
          mul_le_mul_of_nonneg_right (hFactor hGOne hInv) (mul_nonneg hTheta.le hE)
        _ = _ := by dsimp only [Theta,G,E]; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.sum_empty]
    change 0 ≤ 588*(H/lambda)^2*H^2*Gamma*E
    positivity

private theorem matrix_sample_mass_weight_majorant
    {mass m K P G R L N U C Gamma : ℝ}
    (hm : 0 ≤ m) (hC : 0 < C) (hcap : C ≤ Gamma)
    (hmass : mass ≤ 4*m*((K/C)^((3:ℝ)⁻¹)+P*R^4/(L^2*N^2*C*U))+
      m*(2+G*R^4/(N^2*C*U))) :
    mass ≤ 4*m*(K/C)^((3:ℝ)⁻¹)+
      (4*m*P*R^4/(L^2*N^2*U)+m*G*R^4/(N^2*U)+2*m*Gamma)/C := by
  have hconstant : 2*m ≤ 2*m*Gamma/C :=
    (le_div_iff₀ hC).mpr (mul_le_mul_of_nonneg_left hcap (mul_nonneg (by norm_num) hm))
  calc
    _ ≤ 4*m*((K/C)^((3:ℝ)⁻¹)+P*R^4/(L^2*N^2*C*U))+
        m*(2+G*R^4/(N^2*C*U)) := hmass
    _ = 4*m*(K/C)^((3:ℝ)⁻¹)+
        (4*m*P*R^4/(L^2*N^2*U)+m*G*R^4/(N^2*U))/C+2*m := by ring
    _ ≤ 4*m*(K/C)^((3:ℝ)⁻¹)+
        (4*m*P*R^4/(L^2*N^2*U)+m*G*R^4/(N^2*U))/C+2*m*Gamma/C :=
      add_le_add le_rfl hconstant
    _ = _ := by ring

private theorem cubic_matrix_source_scale
    {Z k b m U V G : ℝ}
    (hZ : 0 < Z) (hk : 0 ≤ k) (hb : 0 ≤ b) (hm : 0 ≤ m)
    (hU : 0 < U) (hV : 1 ≤ V) (hG : 0 ≤ G) (hcap : G ≤ Z/V) :
    G*(4*m*(k*Z)^((3:ℝ)⁻¹)*G^((2:ℝ)/3)+m*b*Z/U+2*m*G) ≤
      m*Z^2*((4*k^((3:ℝ)⁻¹)+2)/V^((5:ℝ)/3)+b/(U*V)) := by
  have hVp : 0 < V := zero_lt_one.trans_le hV
  have hratio : 0 ≤ Z/V := (div_pos hZ hVp).le
  have hcoeff : 0 ≤ 4*m*(k*Z)^((3:ℝ)⁻¹) := by positivity
  have hinner :
      4*m*(k*Z)^((3:ℝ)⁻¹)*G^((2:ℝ)/3)+m*b*Z/U+2*m*G ≤
      4*m*(k*Z)^((3:ℝ)⁻¹)*(Z/V)^((2:ℝ)/3)+m*b*Z/U+2*m*(Z/V) := by
    exact add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hG hcap (by norm_num)) hcoeff) le_rfl)
      (mul_le_mul_of_nonneg_left hcap (by positivity))
  have hproduct : (k*Z)^((3:ℝ)⁻¹)*(Z/V)^((2:ℝ)/3)=
      k^((3:ℝ)⁻¹)*Z/V^((2:ℝ)/3) := by
    rw [Real.mul_rpow hk hZ.le,Real.div_rpow hZ.le hVp.le]
    pm_5171 Z hZ
    calc
      _ = k^((3:ℝ)⁻¹)*(Z^((3:ℝ)⁻¹)*Z^((2:ℝ)/3))/V^((2:ℝ)/3) := by ring
      _ = _ := by rw [hpow]
  have hVpow : V*V^((2:ℝ)/3)=V^((5:ℝ)/3) := by
    calc
      _ = V^(1:ℝ)*V^((2:ℝ)/3) := by rw [Real.rpow_one]
      _ = V^((1:ℝ)+2/3) := (Real.rpow_add hVp _ _).symm
      _ = _ := by norm_num
  have hsquare : V^((5:ℝ)/3) ≤ V^2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hV (by norm_num : (5:ℝ)/3 ≤ 2)
    simpa only [Real.rpow_two] using hh
  have htail : 2/V^2 ≤ 2/V^((5:ℝ)/3) :=
    div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hVp _) hsquare
  calc
    _ ≤ (Z/V)*(4*m*(k*Z)^((3:ℝ)⁻¹)*(Z/V)^((2:ℝ)/3)+m*b*Z/U+2*m*(Z/V)) :=
      mul_le_mul hcap hinner (by positivity) hratio
    _ = m*Z^2*(4*k^((3:ℝ)⁻¹)/V^((5:ℝ)/3)+b/(U*V)+2/V^2) := by
      have he : 4*m*(k*Z)^((3:ℝ)⁻¹)*(Z/V)^((2:ℝ)/3)=
          4*m*(k^((3:ℝ)⁻¹)*Z/V^((2:ℝ)/3)) := by rw [←hproduct]; ring
      rw [he,←hVpow]
      ring
    _ ≤ m*Z^2*(4*k^((3:ℝ)⁻¹)/V^((5:ℝ)/3)+b/(U*V)+2/V^((5:ℝ)/3)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl htail) (by positivity)
    _ = _ := by ring

private theorem matrix_physical_source_scale
    {R N L U V Cfirst Cpack Cgap m H lambda : ℝ}
    (hR : 0 < R) (hN : 0 < N) (hL : 0 < L) (hU : 0 < U) (hV : 1 ≤ V)
    (hCf : 0 ≤ Cfirst) (hCp : 0 ≤ Cpack) (hCg : 0 ≤ Cgap) (hm : 0 ≤ m) :
    let G := R^4/(6*N^2*V)
    let K := 2*Cfirst*R^4/(L^3*N^2)
    let B := 4*m*Cpack*R^4/(L^2*N^2*U)+m*Cgap*R^4/(N^2*U)+2*m*G
    588*(H/lambda)^2*H^2*G*(4*m*K^((3:ℝ)⁻¹)*G^((2:ℝ)/3)+B) ≤
      588*m*(H/lambda)^2*H^2*(R^8/N^4)*
        ((4*(2*Cfirst/L^3)^((3:ℝ)⁻¹)+2)/V^((5:ℝ)/3)+
          (4*Cpack/L^2+Cgap)/(U*V)) := by
  intro G K B
  let Z := R^4/N^2
  let k := 2*Cfirst/L^3
  let b := 4*Cpack/L^2+Cgap
  have hVp : 0 < V := zero_lt_one.trans_le hV
  pm_116 hZ Z
  pm_82 hk k
  pm_82 hb b
  pm_82 hG G
  have hcap : G ≤ Z/V := by
    calc
      G = Z/(6*V) := by dsimp only [G,Z]; ring
      _ ≤ Z/V := div_le_div_of_nonneg_left hZ.le hVp (by linarith only [hVp])
  pm_528 hh cubic_matrix_source_scale hZ hk hb hm hU hV hG hcap
  have hK : K=k*Z := by dsimp only [K,k,Z]; ring
  have hB : B=m*b*Z/U+2*m*G := by dsimp only [B,b,Z]; ring
  have hZsquare : Z^2=R^8/N^4 := by dsimp only [Z]; ring
  have hs := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ 588*(H/lambda)^2*H^2 by positivity)
  rw [hK,hB]
  convert hs using 1
  · ring
  · rw [hZsquare]
    dsimp only [k,b]
    ring

section
variable (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ} (Matrices : Finset (Fin 4 → ℤ)) (Bmajor Cmajor : ℕ) (S : (Fin 4 → ℤ) → ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀] (rat : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℤ) (parity : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → ℚ) (e r v s : ℝ × ℝ → ℤ) {σ δ T M N R base Bcut lambda Uband θ V : ℝ} {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ} {x : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℝ} (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M) (hQ : 0 < Q) (hscale : T*N*R^2=M^3) (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M) (hx : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i∈Ioo (1/2:ℝ) (W i-1/2)) (hwindow : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((x Mat) ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) (hden : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, (((rat Mat) ab) j i).den ≤ Q ∧ Q ≤ 2*(((rat Mat) ab) j i).den) (hlambda : 0 < lambda) (hUband : 0 ≤ Uband) (hθ : 0 < θ) (hθmax : θ ≤ 1/24) (hcurv : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, lambda ≤ |(((rat Mat) ab) j i:ℝ)| ∧ |(((rat Mat) ab) j i:ℝ)| ≤ Uband) (hinv : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((((rat Mat) ab) j i).den:ℤ) ∣ (((rat Mat) ab) j i).num*((vinv Mat) ab) j i-1) (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨ (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) (hBcut : 0 < Bcut) (hs : ∀ ab∈Gaps, (s ab) ≠ 0) (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) (hwideL : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) (hwideU : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) (hUref : 1 ≤ Uref) (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect) (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect) (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) (hRQ : R ≤ (Q:ℝ)) (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) (hscaleTen : N^10 ≤ M^3*R^7) (hfamilyGap : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), (((rat Mat) ab) j 0:ℝ)∈Icc ab.1 ab.2) (hc : ∀ Mat∈Matrices, Mat 2 ≠ 0) (hlarge : ∀ Mat∈Matrices, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) (haction : ∀ Mat∈Matrices, 8*Uband ≤ |(Mat 2:ℝ)| *lambda^2) (hV : 1 ≤ V) (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧ ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2))
include Uref Refs Gaps Bselect Matrices Bmajor Cmajor S Q K₀ rat vinv parity anchor e r v s σ δ T M N R base Bcut lambda Uband θ V F A W x hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap
private theorem physicalModelPhase_actual_fourier_charted_matrix_source_mass_core :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (⌊((((rat Mat) ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((((rat Mat) ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((sourceColor Mat) ab) j 0=((sourceColor Mat) ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, iteratedDeriv 2 (f i) (((x Mat) ab) j i)/2=(((rat Mat) ab) j i:ℝ)) →
    let q := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (((rat Mat) ab) j i).den
    let mu := fun Mat => fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round (((x Mat) ab) j i))/6
    let ell := fun Mat => fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round (((x Mat) ab) j i))
    let b := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (⌊(((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i⌋+(((parity Mat) ab) j i:ℕ) : ℤ)
    let cround := fun Mat => fun (ab : ℝ × ℝ) => fun j i => round ((((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i)
    let tau := fun Mat => fun (ab : ℝ × ℝ) => fun j i => ((((b Mat) ab) j i:ℝ)-(((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i)/2
    let dual := fun Mat => fun (ab : ℝ × ℝ) => fun j i => -2*((mu Mat) ab) j i*(Real.sqrt (2/(3*((mu Mat) ab) j i*(((q Mat) ab) j i:ℝ))))^3
    let cloud := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-(((vinv Mat) ab) j i:ℝ)*((b Mat) ab) j i/((q Mat) ab) j i),
      Int.fract (-(((vinv Mat) ab) j i:ℝ)/((q Mat) ab) j i),((dual Mat) ab) j i/Real.sqrt K₀,
      (3*((dual Mat) ab) j i*((tau Mat) ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((b Mat) ab) j 0-((cround Mat) ab) j 0=((b Mat) ab) j 1-((cround Mat) ab) j 1) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ a, |((cloud Mat) ab) j 0 a-((cloud Mat) ab) j 1 a| ≤ 2*radius a) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈S Mat ab,
      |cloud Mat ab j 0 1-cloud Mat ab j 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ Mat∈Matrices, Mat 0*Mat 3-Mat 1*Mat 2=1) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), (Mat 2:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 3=(((q Mat) ab) j 1:ℝ)/((q Mat) ab) j 0) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((Mat 0:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 3)=(((rat Mat) ab) j 1:ℝ)) →
    (∀ Mat∈Matrices, |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), |(((anchor Mat) ab) j:ℝ)-(((rat Mat) ab) j 0:ℝ)| ≤ ε) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), 256*((((anchor Mat) ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*(((anchor Mat) ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Gcap := R^4/(6*N^2*V)
    let Kstar := 2*Cfirst*R^4/(Lunit^3*N^2)
    let Aweight := 4*(m0:ℝ)
    let Bweight := 4*(m0:ℝ)*Cpack*R^4/(Lunit^2*N^2*(Uref:ℝ))+
      (m0:ℝ)*Cgap*R^4/(N^2*(Uref:ℝ))+2*(m0:ℝ)*Gcap
    (∑ Mat∈Matrices, ∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
      588*(Uband/lambda)^2*Uband^2*Gcap*
        (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight) := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear hnearNarrow
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Cpack Cfirst Cgap
    Gcap Kstar Aweight Bweight
  pm_1689
  pm_1700
  pm_1699
  pm_1708
  have hVp : 0 < V := zero_lt_one.trans_le hV
  pm_82 hGcap Gcap
  pm_82 hKstar Kstar
  pm_82 hAweight Aweight
  pm_82 hBweight Bweight
  have hK₀ : (1:ℝ) ≤ K₀ := by exact_mod_cast (show 1 ≤ K₀ from NeZero.pos K₀)
  have hmass Mat (hMat : Mat∈Matrices) :
      (∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
        4*(m0:ℝ)*((Kstar/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+
          Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))) := by
    exact physicalModelPhase_actual_fourier_charted_all_reference_sample_mass
      Uref Refs Gaps (Bselect:=Bselect) Bmajor Cmajor (S Mat) Q K₀
      (rat Mat) (vinv Mat) (parity Mat) (anchor Mat) Mat e r v s
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (hx Mat hMat) (hwindow Mat hMat) (hden Mat hMat) hlambda hUband hθ hθmax (hcurv Mat hMat) (hinv Mat hMat) hchart horientation hBcut hs hrefSet hparentSet hsep (hwideL Mat hMat) (hwideU Mat hMat) hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen (hfamilyGap Mat hMat)
      (hc Mat hMat) (hlarge Mat hMat) hgap
      (hsourceColor Mat hMat) (hlevel Mat hMat) (hcolor Mat hMat) (hnear Mat hMat) hsmall hNR hRN hNcube hminscale (hMatdet Mat hMat) (hMatt Mat hMat) (hMatmap Mat hMat) (hMatgamma Mat hMat) hNtwo (hL Mat hMat) (hU Mat hMat) (hanchor Mat hMat) (hcut Mat hMat) (hcount Mat hMat)
      hsize hD hΔ hBsize hBmajor hCmajor
  let Occupied := Matrices.filter (fun Mat => ∃ ab∈Gaps, (S Mat ab).Nonempty)
  have hin : Occupied ⊆ Matrices := Finset.filter_subset _ _
  have hpick Mat (hMat : Mat∈Occupied) : ∃ ab, ab∈Gaps ∧ ∃ j, j∈S Mat ab := by
    obtain ⟨ab,hab,hne⟩ := (Finset.mem_filter.mp hMat).2
    obtain ⟨j,hj⟩ := hne
    exact ⟨ab,hab,j,hj⟩
  choose! ab hab j hj using hpick
  let pr := fun Mat i => rat Mat (ab Mat) (j Mat) i
  pm_5406 hpden hden
  pm_5406 hpcurv hcurv
  pm_5574 hpMatt hMatt
  pm_5574 hpmap hMatmap
  have hpcap Mat (hMat : Mat∈Occupied) : Mat 2 ≠ 0 ∧ |(Mat 2:ℝ)| ≤ Gcap := by
    have hh := fourier_matrix_narrowed_coordinate_entry_bound
      (fun i => ((pr Mat i).den:ℤ)) (fun i => (pr Mat i).num)
      (vinv Mat (ab Mat) (j Mat)) Mat (Q:=(Q:ℝ)) (K:=(K₀:ℝ)) (V:=V)
      (N:=N) (R:=R)
      (fun i => by
        exact_mod_cast (pr Mat i).den_pos)
      hK₀ hV hN hmesh
      (fun i => by
        have hlo : ((pr Mat i).den:ℝ) ≤ Q := by exact_mod_cast (hpden Mat hMat i).1
        have hhi : (Q:ℝ) ≤ 2*((pr Mat i).den:ℝ) := by exact_mod_cast (hpden Mat hMat i).2
        simpa only [Int.cast_natCast] using And.intro hlo hhi)
      (hinv Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat))
      (hMatdet Mat (hin hMat))
      (by simpa only [Int.cast_natCast,Rat.cast_def] using hpMatt Mat hMat)
      (by simpa only [Int.cast_natCast,Rat.cast_def] using hpmap Mat hMat)
      (hMatgamma Mat (hin hMat))
      (by
        have hh := hnearNarrow Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat)
        change |Int.fract (-(vinv Mat (ab Mat) (j Mat) 0:ℝ)/(pr Mat 0).den)-
          Int.fract (-(vinv Mat (ab Mat) (j Mat) 1:ℝ)/(pr Mat 1).den)| ≤
            1/(6*(K₀:ℝ)^2*V) at hh
        simpa only [Int.cast_natCast] using hh)
    exact ⟨hc Mat (hin hMat),hh.2⟩
  have hratios Mat (hMat : Mat∈Occupied) :
      |((pr Mat 1).den:ℝ)/(pr Mat 0).den-1| ≤ θ ∧
      |((pr Mat 1).num:ℝ)/(pr Mat 0).num-1| ≤ θ := by
    have hh := (rational_narrow_band_partition Finset.univ (pr Mat) Q
      hQ hlambda hUband hθ (fun i _ => hpcurv Mat hMat i)
      (fun i _ => hpden Mat hMat i)).2
    exact hh 0 (Finset.mem_univ _) 1 (Finset.mem_univ _)
      (hsourceColor Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat))
  have hpt Mat (hMat : Mat∈Occupied) :
      (1:ℝ)/2 ≤ (Mat 2:ℝ)*(pr Mat 0:ℝ)+Mat 3 ∧
      (Mat 2:ℝ)*(pr Mat 0:ℝ)+Mat 3 ≤ 2 := by
    rw [hpMatt Mat hMat]
    have hh := abs_le.mp (hratios Mat hMat).1
    pm_4893 hθmax
  have hpnum Mat (hMat : Mat∈Occupied) :
      (1:ℝ)/2 ≤ ((Mat 0:ℝ)*(pr Mat 0:ℝ)+Mat 1)/(pr Mat 0:ℝ) ∧
      ((Mat 0:ℝ)*(pr Mat 0:ℝ)+Mat 1)/(pr Mat 0:ℝ) ≤ 2 := by
    have hx0 : (pr Mat 0:ℝ) ≠ 0 := abs_pos.mp (hlambda.trans_le (hpcurv Mat hMat 0).1)
    have hnum0 : ((pr Mat 0).num:ℝ) ≠ 0 := by
      intro hh
      apply hx0
      rw [Rat.cast_def,hh,zero_div]
    have hq0 : (0:ℝ) < (pr Mat 0).den := by exact_mod_cast (pr Mat 0).den_pos
    have hq1 : (0:ℝ) < (pr Mat 1).den := by exact_mod_cast (pr Mat 1).den_pos
    have htp : 0 < (Mat 2:ℝ)*(pr Mat 0:ℝ)+Mat 3 := by
      linarith only [(hpt Mat hMat).1]
    have he := (div_eq_iff htp.ne').mp (hpmap Mat hMat)
    have hid : ((Mat 0:ℝ)*(pr Mat 0:ℝ)+Mat 1)/(pr Mat 0:ℝ)=
        ((pr Mat 1).num:ℝ)/(pr Mat 0).num := by
      rw [he,hpMatt Mat hMat]
      change ((pr Mat 1:ℝ)*(((pr Mat 1).den:ℝ)/(pr Mat 0).den))/(pr Mat 0:ℝ)=
        ((pr Mat 1).num:ℝ)/(pr Mat 0).num
      simp only [Rat.cast_def]
      field_simp [hq0.ne',hq1.ne',hnum0]
    rw [hid]
    have hh := abs_le.mp (hratios Mat hMat).2
    pm_4893 hθmax
  have hpointMass Mat (hMat : Mat∈Occupied) :
      (∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
        Aweight*(Kstar/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+Bweight/|(Mat 2:ℝ)| := by
    exact matrix_sample_mass_weight_majorant (Nat.cast_nonneg m0)
      (abs_pos.mpr (by exact_mod_cast (hpcap Mat hMat).1)) (hpcap Mat hMat).2
      (hmass Mat (hin hMat))
  have hsum := resonance_matrix_curvature_band_cubic_weight_sum Occupied
    (fun Mat => (pr Mat 0:ℝ)) (fun Mat => (pr Mat 1:ℝ))
    hlambda hGcap hAweight hKstar hBweight
    (fun Mat hMat => hMatdet Mat (hin hMat)) hpcap
    (fun Mat hMat => hpcurv Mat hMat 0) (fun Mat hMat => hpcurv Mat hMat 1)
    hpt hpmap hpnum (fun Mat hMat => haction Mat (hin hMat))
  have hsumOcc : (∑ Mat∈Matrices, ∑ ab∈Gaps, ((S Mat ab).card:ℝ))=
      ∑ Mat∈Occupied, ∑ ab∈Gaps, ((S Mat ab).card:ℝ) := by
    symm
    apply Finset.sum_subset hin
    intro Mat hMat hnot
    apply Finset.sum_eq_zero
    intro ab hab
    have he : S Mat ab=∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      pm_8846 hne hMat
    simp only [he,Finset.card_empty,Nat.cast_zero]
  rw [hsumOcc]
  exact (Finset.sum_le_sum hpointMass).trans hsum

                                                                                                 
theorem physicalModelPhase_actual_fourier_charted_matrix_source_mass :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (⌊((((rat Mat) ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((((rat Mat) ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((sourceColor Mat) ab) j 0=((sourceColor Mat) ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, iteratedDeriv 2 (f i) (((x Mat) ab) j i)/2=(((rat Mat) ab) j i:ℝ)) →
    let q := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (((rat Mat) ab) j i).den
    let mu := fun Mat => fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round (((x Mat) ab) j i))/6
    let ell := fun Mat => fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round (((x Mat) ab) j i))
    let b := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (⌊(((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i⌋+(((parity Mat) ab) j i:ℕ) : ℤ)
    let cround := fun Mat => fun (ab : ℝ × ℝ) => fun j i => round ((((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i)
    let tau := fun Mat => fun (ab : ℝ × ℝ) => fun j i => ((((b Mat) ab) j i:ℝ)-(((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i)/2
    let dual := fun Mat => fun (ab : ℝ × ℝ) => fun j i => -2*((mu Mat) ab) j i*(Real.sqrt (2/(3*((mu Mat) ab) j i*(((q Mat) ab) j i:ℝ))))^3
    let cloud := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-(((vinv Mat) ab) j i:ℝ)*((b Mat) ab) j i/((q Mat) ab) j i),
      Int.fract (-(((vinv Mat) ab) j i:ℝ)/((q Mat) ab) j i),((dual Mat) ab) j i/Real.sqrt K₀,
      (3*((dual Mat) ab) j i*((tau Mat) ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((b Mat) ab) j 0-((cround Mat) ab) j 0=((b Mat) ab) j 1-((cround Mat) ab) j 1) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ a, |((cloud Mat) ab) j 0 a-((cloud Mat) ab) j 1 a| ≤ 2*radius a) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈S Mat ab,
      |cloud Mat ab j 0 1-cloud Mat ab j 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ Mat∈Matrices, Mat 0*Mat 3-Mat 1*Mat 2=1) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), (Mat 2:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 3=(((q Mat) ab) j 1:ℝ)/((q Mat) ab) j 0) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((Mat 0:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 3)=(((rat Mat) ab) j 1:ℝ)) →
    (∀ Mat∈Matrices, |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), |(((anchor Mat) ab) j:ℝ)-(((rat Mat) ab) j 0:ℝ)| ≤ ε) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), 256*((((anchor Mat) ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*(((anchor Mat) ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Gcap := R^4/(6*N^2*V)
    let Kstar := 2*Cfirst*R^4/(Lunit^3*N^2)
    let Aweight := 4*(m0:ℝ)
    let Bweight := 4*(m0:ℝ)*Cpack*R^4/(Lunit^2*N^2*(Uref:ℝ))+
      (m0:ℝ)*Cgap*R^4/(N^2*(Uref:ℝ))+2*(m0:ℝ)*Gcap
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    ((∑ Mat∈Matrices, ∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
      588*(Uband/lambda)^2*Uband^2*Gcap*
        (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight)) ∧
    (∑ Mat∈Matrices, ∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
      588*(m0:ℝ)*(Uband/lambda)^2*Uband^2*(R^8/N^4)*
        (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)) := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear hnearNarrow
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Cpack Cfirst Cgap
    Gcap Kstar Aweight Bweight Cmain Ctail
  have hraw := physicalModelPhase_actual_fourier_charted_matrix_source_mass_core
    Uref Refs Gaps (Bselect:=Bselect) Matrices Bmajor Cmajor S Q K₀
    rat vinv parity anchor e r v s
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap
    hc hlarge haction hV hgap
    hsourceColor hlevel hcolor hnear hnearNarrow
    hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize hBmajor hCmajor
  pm_1689
  have hunit : 0 < Lunit := div_pos (mul_pos (by norm_num) hκ) hCphys
  pm_1699
  pm_1708
  refine ⟨hraw,hraw.trans ?_⟩
  exact matrix_physical_source_scale (zero_lt_one.trans_le hR) hN hunit hUp hV
    hCfirst hCpack hCgap (Nat.cast_nonneg m0)
end


                                                                                          
theorem physicalModelPhase_reference_matrix_window_selection
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (F : Fin 2 → ℝ → ℝ) (A Wlim : Fin 2 → ℝ) (za zb : ℤ → ℝ) (AlenA Alen : ℤ → ℕ)
    (N : ℕ) (Za Z : ℤ) (W : ℝ)
    {σ δ T M : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+Wlim i ≤ 2*M)
    (hbase : ∀ ij∈P, W ≤ za ij.1.1)
    (hz : ∀ ij∈P, zb ij.2.1∈Ioo 0 (Wlim 1))
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometry : ∀ ij∈P, N ≤ Alen ij.2.1 ∧ Alen ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(Alen ij.2.1:ℤ)=Z+(N:ℤ)*ij.2.1+2*(N:ℤ)) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    (∀ ij∈P, ((Mat ij 0:ℝ)*h 0 (za ij.1.1)+Mat ij 1)/
      ((Mat ij 2:ℝ)*h 0 (za ij.1.1)+Mat ij 3)=h 1 (zb ij.2.1)) →
    let block := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
      ⌊(za ij.1.1-W)/(N:ℝ)⌋.toNat
    let S := fun A ab => (P.filter (fun ij => Mat ij=A ∧ gap ij=ab)).image block
    ∃ pick : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → (ℤ × Fin 2) × (ℤ × Fin 2),
      (∀ A∈P.image Mat, ∀ ab∈P.image gap, ∀ j∈S A ab,
        pick A ab j∈P ∧ Mat (pick A ab j)=A ∧ gap (pick A ab j)=ab ∧
        block (pick A ab j)=j ∧
        za (pick A ab j).1.1∈Icc (W+(N:ℝ)*j) (W+(N:ℝ)*((j:ℝ)+1))) ∧
      P.card ≤ 60*∑ A∈P.image Mat, ∑ ab∈P.image gap, (S A ab).card := by
  classical
  intro f h hmap block S
  pm_1815
  have hnonneg ij (hij : ij∈P) : 0 ≤ ⌊(za ij.1.1-W)/(N:ℝ)⌋ :=
    Int.floor_nonneg.mpr (div_nonneg (sub_nonneg.mpr (hbase ij hij)) hNp.le)
  have hwindow ij (hij : ij∈P) :
      za ij.1.1∈Icc (W+(N:ℝ)*block ij) (W+(N:ℝ)*((block ij:ℝ)+1)) := by
    have he : (block ij:ℤ)=⌊(za ij.1.1-W)/(N:ℝ)⌋ :=
      Int.toNat_of_nonneg (hnonneg ij hij)
    have heR : (block ij:ℝ)=(⌊(za ij.1.1-W)/(N:ℝ)⌋:ℝ) := by exact_mod_cast he
    pm_8203 hlo Int.floor_le
    pm_8203 hhi Int.lt_floor_add_one
    rw [←heR] at hlo hhi
    have hl := (le_div_iff₀ hNp).mp hlo
    have hu := (div_lt_iff₀ hNp).mp hhi
    constructor <;> nlinarith only [hl,hu]
  have hex A ab j (hj : j∈S A ab) :
      ∃ ij, ij∈P ∧ Mat ij=A ∧ gap ij=ab ∧ block ij=j := by
    obtain ⟨ij,hij,he⟩ := Finset.mem_image.mp hj
    have hh := Finset.mem_filter.mp hij
    exact ⟨ij,hh.1,hh.2.1,hh.2.2,he⟩
  let pick := fun A ab j => if hj : j∈S A ab then
    Classical.choose (hex A ab j hj) else ((0,0),(0,0))
  refine ⟨pick,?_,?_⟩
  · intro A _hA ab _hab j hj
    have hp : pick A ab j∈P ∧ Mat (pick A ab j)=A ∧
        gap (pick A ab j)=ab ∧ block (pick A ab j)=j := by
      dsimp only [pick]
      rw [dite_eq_left hj]
      exact Classical.choose_spec (hex A ab j hj)
    refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,?_⟩
    simpa only [hp.2.2.2] using hwindow (pick A ab j) hp.1
  · have hmono : StrictMonoOn (h 1) (Ioo 0 (Wlim 1)) := by
      intro a ha b hb hab
      have hh := physicalModelPhase_halfCurvature_growth hσ hδ (hF 1)
        hT hM (hA 1) (hW 1) ha hb hab.le
      have hκ := modelPhaseThirdLower_pos hσ
      pm_1855
    have hspan ij (hij : ij∈P) :
        (N:ℝ) ≤ (Z:ℝ)+(ij.2.1:ℝ)*N+2*N-(round (zb ij.2.1):ℝ) ∧
        (Z:ℝ)+(ij.2.1:ℝ)*N+2*N-(round (zb ij.2.1):ℝ) ≤ 3*N := by
      have hg := hgeometry ij hij
      have hlo : (N:ℝ) ≤ Alen ij.2.1 := by exact_mod_cast hg.1
      have hhi : (Alen ij.2.1:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hg.2.1
      have he : (round (zb ij.2.1):ℝ)+(Alen ij.2.1:ℝ)=
          (Z:ℝ)+(N:ℝ)*ij.2.1+2*(N:ℝ) := by exact_mod_cast hg.2.2
      constructor <;> nlinarith only [hlo,hhi,he]
    have hprojection := curvature_pair_card_le_matrix_blocks P Mat (h 0) (h 1)
      za zb (Ioo 0 (Wlim 1)) hNp hmono.injOn hz hspan hmap
    let Vfirst := P.image (fun ij => (Mat ij,ij.1.1))
    have hcard : Vfirst.card=∑ B∈P.image Mat,
        ((P.filter (fun ij => Mat ij=B)).image (fun ij => ij.1.1)).card := by
      calc
        _ = ∑ B∈P.image Mat, (Vfirst.filter (fun v => v.1=B)).card := by
          apply Finset.card_eq_sum_card_fiberwise
          pm_2532 v hv ij hij
          exact Finset.mem_image.mpr ⟨ij,hij,rfl⟩
        _ = _ := by
          apply Finset.sum_congr rfl
          intro B _
          have hImage : (Vfirst.filter (fun v => v.1=B)).image Prod.snd=
              (P.filter (fun ij => Mat ij=B)).image (fun ij => ij.1.1) := by
            ext k
            simp only [Vfirst,Finset.mem_image,Finset.mem_filter]
            constructor
            · rintro ⟨v,⟨⟨ij,hij,he⟩,hvB⟩,hvk⟩
              refine ⟨ij,⟨hij,?_⟩,?_⟩
              · rw [←he] at hvB
                exact hvB
              · rw [←he] at hvk
                exact hvk
            · rintro ⟨ij,⟨hij,hB⟩,hk⟩
              exact ⟨(Mat ij,ij.1.1),⟨⟨ij,hij,rfl⟩,hB⟩,hk⟩
          rw [←hImage]
          symm
          apply Finset.card_image_of_injOn
          intro x hx y hy he
          pm_8858 hx hy
    change P.card ≤ 12*Vfirst.card at hprojection
    rw [hcard] at hprojection
    have hper B : ((P.filter (fun ij => Mat ij=B)).image (fun ij => ij.1.1)).card ≤
        5*((P.filter (fun ij => Mat ij=B)).image
          (fun ij => ⌊(za ij.1.1-W)/(N:ℝ)⌋)).card := by
      have hh := rounded_offset_floor_block_count
        ((P.filter (fun ij => Mat ij=B)).image (fun ij => ij.1.1))
        za AlenA N Za W hN
        (by
          pm_2532 k hk ij hij
          exact hgeometryA ij (Finset.mem_filter.mp hij).1)
      simpa only [Finset.image_image,Function.comp_def] using hh
    have hp : P.card ≤ 60*∑ B∈P.image Mat,
        ((P.filter (fun ij => Mat ij=B)).image
          (fun ij => ⌊(za ij.1.1-W)/(N:ℝ)⌋)).card := by
      calc
        _ ≤ 12*∑ B∈P.image Mat,
            ((P.filter (fun ij => Mat ij=B)).image (fun ij => ij.1.1)).card := hprojection
        _ ≤ 12*∑ B∈P.image Mat, 5*((P.filter (fun ij => Mat ij=B)).image
            (fun ij => ⌊(za ij.1.1-W)/(N:ℝ)⌋)).card :=
          Nat.mul_le_mul_left 12 (Finset.sum_le_sum (fun B _ => hper B))
        _ = _ := by rw [←Finset.mul_sum]; ring
    apply hp.trans
    apply Nat.mul_le_mul_left 60
    apply Finset.sum_le_sum
    intro A _hA
    pm_2283 E P.filter ij Mat A
    let I := E.image (fun ij => ⌊(za ij.1.1-W)/(N:ℝ)⌋)
    have hinj : Set.InjOn Int.toNat (↑I) := by
      intro x hx y hy he
      pm_2533 ij hij hx kl hkl hy
      have hix := hnonneg ij (Finset.mem_filter.mp hij).1
      have hiy := hnonneg kl (Finset.mem_filter.mp hkl).1
      omega
    have he : I.card=(E.image block).card := by
      rw [←Finset.card_image_of_injOn hinj,Finset.image_image]
      rfl
    change I.card ≤ _
    rw [he]
    have hsub : E.image block ⊆ (P.image gap).biUnion (fun ab => S A ab) := by
      pm_2532 j hj ij hij
      have hh := Finset.mem_filter.mp hij
      exact Finset.mem_biUnion.mpr ⟨gap ij,Finset.mem_image_of_mem gap hh.1,
        Finset.mem_image.mpr ⟨ij,Finset.mem_filter.mpr ⟨hh.1,hh.2,rfl⟩,rfl⟩⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)

universe huxleyNarrowV

private theorem huxley_narrowed_sieve_frequency_scale {N t η ζ Vscale : ℝ}
    (hN : 1≤N) (ht : t∈Icc 1 N) (hη : 0<η) (hζ : 0<ζ) (hV : 1≤Vscale) :
    let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2*Vscale),η/12,ζ/12]
    let U : Fin 4 → ℝ := ![t,t^2,(1/η)*(t/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt (t/N)]
    ∀ d, a d*|U d| ≤ 1/12 := by
  have hNp : 0<N := by linarith
  have hVp : 0<Vscale := zero_lt_one.trans_le hV
  pm_2222
  · change (1/(12*N^2*Vscale))*|t^2|≤1/12
    pm_1386
    have hh := mul_le_mul_of_nonneg_left hsq (by positivity : 0≤1/(12*N^2*Vscale))
    calc
      _ ≤ (1/(12*N^2*Vscale))*N^2 := hh
      _ = 1/(12*Vscale) := by field_simp
      _ ≤ 1/12 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  pm_2223

private theorem huxley_narrowed_sieve_box_scale {N η ζ Vscale : ℝ}
    (hN : 1≤N) (hη : η∈Ioc 0 1) (hζ : ζ∈Ioc 0 1) (hV : 1≤Vscale) :
    let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2*Vscale),η/12,ζ/12]
    let δ : Fin 4 → ℝ := ![1,1,2,2]
    (∀ d, 0<a d) ∧
    (∀ d, 1/(δ d+2*a d) ≤ (![1,1,1/2,1/2] : Fin 4 → ℝ) d) ∧
    16777216*(∏ d, (δ d+2*a d))/(∏ d, a d) ≤
      (16777216*36*12^4)*N^3*Vscale/(η*ζ) := by
  dsimp only
  let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2*Vscale),η/12,ζ/12]
  pm_900
  have hVp : 0<Vscale := zero_lt_one.trans_le hV
  pm_2225
  · have ha1 d : a d≤1/12 := by
      fin_cases d
      · change 1/(12*N)≤1/12
        exact one_div_le_one_div_of_le (by norm_num) (by linarith)
      · change 1/(12*N^2*Vscale)≤1/12
        have hNsq : (1:ℝ) ≤ N^2 := by nlinarith
        have hNV : (1:ℝ) ≤ N^2*Vscale :=
          one_mul (1:ℝ) ▸ mul_le_mul hNsq hV zero_le_one (sq_nonneg N)
        exact one_div_le_one_div_of_le (by norm_num) (by nlinarith only [hNV])
      · change η/12≤1/12
        exact div_le_div_of_nonneg_right hη.2 (by norm_num)
      · change ζ/12≤1/12
        exact div_le_div_of_nonneg_right hζ.2 (by norm_num)
    pm_2224
    have hprod : (∏ d, a d) = η*ζ/(12^4*N^3*Vscale) := by
      norm_num [a,Fin.prod_univ_succ]
      field_simp
      ring
    pm_2227


private theorem huxley_narrowed_sieve_final_scale
    {N η ζ Vscale L C B a p ε : ℝ}
    (hN : 0<N) (hη : 0<η) (hζ : 0<ζ) :
    (a*p)*((L*N^3*Vscale/(η*ζ))*
      (C*η*ζ*N^((9:ℝ)+ε)*B^12)) =
    (L*C)*Vscale*N^((12:ℝ)+ε)*a*B^12*p := by
  have hpow : N^3*N^((9:ℝ)+ε)=N^((12:ℝ)+ε) := by
    pm_5470 Real.rpow_ofNat hN
  rw [←hpow]
  field_simp

                                                                        
                                                                        
                                                                     
private theorem exists_huxleySourceCurve_narrowed_double_sieve {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (N : ℕ), 1≤N → ∀ (η ζ Vscale : ℝ),
      η∈Icc (1/(N:ℝ)^2) 1 → ζ∈Icc (1/(N:ℝ)) 1 → 1≤Vscale →
      ∀ (ι κ : Type huxleyNarrowV) (S : Finset ι) (T : Finset κ) (w : κ → ℂ)
        (m : κ → ℤ) (x : ι → Fin 4 → ℝ) (B : ℝ),
        0≤B → (∀ j∈T,1 ≤ m j ∧ m j≤N) →
        (∀ j∈T,‖w j‖≤1) →
        (∀ q : ℤ,((T.filter (fun j => m j=q)).card:ℝ)≤B) →
        (∀ i∈S,x i∈Icc ![0,0,-1,-1] (fun _ => 1)) →
        let U := fun j => ![(m j:ℝ),(m j:ℝ)^2,
          (1/η)*((m j:ℝ)/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt ((m j:ℝ)/N)]
        let a : Fin 4 → ℝ := ![1/(12*(N:ℝ)),1/(12*(N:ℝ)^2*Vscale),η/12,ζ/12]
        (∑ i∈S,‖∑ j∈T,w j*GafniTao.fordAdditiveCharacter (∑ d,U j d*x i d)‖)^12 ≤
          C*Vscale*(N:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*B^12*
            (((S ×ˢ S).filter (fun ij => ∀ d, |x ij.1 d-x ij.2 d|≤2*a d)).card:ℝ) := by
  classical
  obtain ⟨C,hC,hcount⟩ := exists_bourgainSourceCurve_six_tuple_first_spacing.{huxleyNarrowV} hε
  pm_2236
  intro N hN η ζ Vscale hη hζ hV ι κ S T w m x B hB hm hw hmass hx
  pm_2232
  let a : Fin 4 → ℝ := ![1/(12*(N:ℝ)),1/(12*(N:ℝ)^2*Vscale),η/12,ζ/12]
  pm_2239
  pm_2231
  pm_7065 huxley_narrowed_sieve_box_scale hV
  pm_6018
  have hU j (hj : j∈T) : ∀ d,a d*|U j d|≤1/12 :=
    huxley_narrowed_sieve_frequency_scale hNr
      (by exact ⟨by exact_mod_cast (hm j hj).1,by exact_mod_cast (hm j hj).2⟩) hηp hζp hV
  pm_2233
  change (∑ i∈S,‖∑ j∈T,w j*GafniTao.fordAdditiveCharacter (∑ d,U j d*x i d)‖)^12 ≤
    (S.card:ℝ)^10*K*(P.card:ℝ)*(Q.card:ℝ) at hs
  pm_2230
  have hbound := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hscale hR) hCouter
  calc
    _ ≤ (S.card:ℝ)^10*K*(P.card:ℝ)*(C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12) :=
      hs.trans (mul_le_mul_of_nonneg_left hQ (by positivity))
    _ = ((S.card:ℝ)^10*(P.card:ℝ))*(K*(C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12)) := by ring
    _ ≤ ((S.card:ℝ)^10*(P.card:ℝ))*
        ((L*(N:ℝ)^3*Vscale/(η*ζ))*(C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12)) := hbound
    _ = _ := huxley_narrowed_sieve_final_scale hNp hηp hζp

private theorem huxley_completed_phase_normalize
    {M : ℕ} (hM : 0 < M) (x : Fin 4 → ℝ) (n : ℤ) (hn : 0 ≤ n) :
    GafniTao.fordAdditiveCharacter (∑ d,x d*
      (![(n:ℝ),(n:ℝ)^2,(n:ℝ)^((3:ℝ)/2),Real.sqrt (n:ℝ)] : Fin 4 → ℝ) d)=
    GafniTao.fordAdditiveCharacter (∑ d,
      (![(n:ℝ),(n:ℝ)^2,(M:ℝ)^2*((n:ℝ)/M)^((3:ℝ)/2),
        (M:ℝ)*Real.sqrt ((n:ℝ)/M)] : Fin 4 → ℝ) d*
      (![Int.fract (x 0),Int.fract (x 1),x 2/Real.sqrt M,x 3/Real.sqrt M] : Fin 4 → ℝ) d) := by pm_2255 GafniTao.fordAdditiveCharacter_add GafniTao.fordAdditiveCharacter


public  theorem huxley_completed_narrowed_source_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (M : ℕ) [NeZero M] (Vscale : ℝ), 1≤Vscale → ∀ (ι : Type huxleyNarrowV) (S : Finset ι)
      (x : ι → Fin 4 → ℝ),
      (∀ i∈S, |x i 2| ≤ Real.sqrt M ∧ |x i 3| ≤ Real.sqrt M) →
      let y := fun i => (![Int.fract (x i 0),Int.fract (x i 1),
        x i 2/Real.sqrt M,x i 3/Real.sqrt M] : Fin 4 → ℝ)
      let a : Fin 4 → ℝ :=
        ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2*Vscale),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
      ∀ k : ZMod M,
      (∑ i∈S, ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x i d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*Vscale*(M:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*
          (((S ×ˢ S).filter (fun ij => ∀ d,|y ij.1 d-y ij.2 d| ≤ 2*a d)).card:ℝ) := by
  classical
  obtain ⟨C,hC,hsource⟩ := exists_huxleySourceCurve_narrowed_double_sieve.{huxleyNarrowV} hε
  refine ⟨C,hC,?_⟩
  intro M inst Vscale hV ι S x hx y a k
  pm_2258
  pm_4410
  have hsqrt : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMr
  let T : Finset (ULift.{huxleyNarrowV} (ZMod M)) := Finset.univ
  let m := fun j : ULift.{huxleyNarrowV} (ZMod M) => (j.down.val:ℤ)+1
  pm_5781 huxleyNarrowV
  pm_2256
  have hh := hsource M (by omega) (1/(M:ℝ)^2) (1/(M:ℝ))
    Vscale hη hζ hV ι (ULift.{huxleyNarrowV} (ZMod M)) S T w m y 1 (by norm_num) hm
    (fun j _ => (sargos_stdAddChar_norm _).le) hmass hy
  pm_2260 huxleyNarrowV
  have he :
      (∑ i∈S, ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x i d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)=
      ∑ i∈S, ‖∑ j∈T,w j*GafniTao.fordAdditiveCharacter (∑ d,U j d*y i d)‖ := by
    apply Finset.sum_congr rfl
    intro i _hi
    congr 1
    calc
      _ = ∑ j : ULift.{huxleyNarrowV} (ZMod M),w j*
          GafniTao.fordAdditiveCharacter (∑ d,x i d*
            (![(m j:ℝ),(m j:ℝ)^2,(m j:ℝ)^((3:ℝ)/2),
              Real.sqrt (m j:ℝ)] : Fin 4 → ℝ) d) := by
        apply Fintype.sum_equiv Equiv.ulift.symm
        intro j
        simp [w,m,Equiv.ulift]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _hj
        congr 1
        exact huxley_completed_phase_normalize hM (x i) (m j) (by dsimp only [m]; omega)
  rw [he]
  exact hh


private theorem huxley_dual_physical_scale {μ q N : ℝ}
    (hμ : 0<μ) (hq : 0<q) (hN : 0<N) (hqN : q≤N)
    (hscale : 1≤μ*q^2*N) :
    1≤μ*q*N^2 ∧
    |-2*μ*(Real.sqrt (2/(3*μ*q)))^3|/Real.sqrt (μ*q*N^2) ≤ 2 := by pm_2240

public  theorem huxley_actual_dual_source_box
    {M q N : ℕ} [NeZero M] (hq : 0 < q) (hN : 1 ≤ N) (hqN : q ≤ N)
    {μ ℓ : ℝ} (hμ : 0 < μ) (hscale : 1 ≤ μ*(q:ℝ)^2*N)
    (hM : 7*(μ*(q:ℝ)*(N:ℝ)^2) ≤ M) (r : ℤ) (p : Fin 2) :
    let b : ℤ := ⌊(q:ℝ)*ℓ⌋+(p:ℕ)
    let τ := ((b:ℝ)-(q:ℝ)*ℓ)/2
    let K := -2*μ*(Real.sqrt (2/(3*μ*(q:ℝ))))^3
    let x : Fin 4 → ℝ := ![-(r:ℝ)*b/q,-(r:ℝ)/q,K,3*K*τ/2]
    |x 2| ≤ Real.sqrt M ∧ |x 3| ≤ Real.sqrt M := by
  pm_2262
  obtain ⟨hA,hK⟩ := huxley_dual_physical_scale hμ hqr hNr hqNr hscale
  pm_2261


                                                                      
                                                                         
                                                                          
private theorem exists_huxley_cubic_dual_narrowed_source_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (M : ℕ) [NeZero M] (Vscale : ℝ), 1≤Vscale → ∀ (ι : Type huxleyNarrowV) (S : Finset ι)
      (q N : ι → ℕ) (r : ι → ℤ) (μ ℓ : ι → ℝ),
      (∀ i∈S, 0 < q i ∧ 1 ≤ N i ∧ q i ≤ N i ∧ 0 < μ i ∧
        1 ≤ μ i*(q i:ℝ)^2*N i) →
      (∀ i∈S, 7*(μ i*(q i:ℝ)*(N i:ℝ)^2) ≤ M) →
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
      let x := fun i p =>
        (![-(r i:ℝ)*b i p/q i,-(r i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      let V := S ×ˢ (Finset.univ : Finset (Fin 2))
      let y := fun ip : ι × Fin 2 =>
        (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
          x ip.1 ip.2 2/Real.sqrt M,x ip.1 ip.2 3/Real.sqrt M] : Fin 4 → ℝ)
      let a : Fin 4 → ℝ :=
        ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2*Vscale),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
      ∀ k : ZMod M,
      (∑ i∈S, ∑ p : Fin 2, ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x i p d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*Vscale*(M:ℝ)^((12:ℝ)+ε)*(V.card:ℝ)^10*
          (((V ×ˢ V).filter (fun ij => ∀ d,|y ij.1 d-y ij.2 d| ≤ 2*a d)).card:ℝ) := by
  classical
  obtain ⟨C,hC,hsource⟩ := huxley_completed_narrowed_source_sieve.{huxleyNarrowV} hε
  refine ⟨C,hC,?_⟩
  intro M inst Vscale hV ι S q N r μ ℓ hscale hM b τ K x V y a k
  pm_2263 huxley_actual_dual_source_box
  have hh := hsource M Vscale hV (ι × Fin 2) V (fun ip => x ip.1 ip.2) hbox k
  simpa only [V,Finset.sum_product] using hh

theorem exists_source_arc_fourier_narrowed_sieve_matrices {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (ι : Type huxleyNarrowV) [DecidableEq ι] (S : Finset ι)
    (f : ι → ℝ → ℝ) (z : ι → ℝ) (r : ι → ℚ) (v : ι → ℤ)
    (Q K₀ : ℕ) [NeZero K₀] (μ₀ U₀ : ℝ), 0 < μ₀ →
    (∀ i∈S, μ₀ ≤ iteratedDeriv 3 (f i) (round (z i))/6 ∧
      iteratedDeriv 3 (f i) (round (z i))/6 ≤ U₀) →
    (∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
    (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) →
    (∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) →
    ∀ (Nlen : ι → ℕ) (Vscale Nphys Rphys : ℝ),
    1 ≤ Vscale → 0 < Nphys →
    (Q:ℝ)*Nphys ≤ (K₀:ℝ)*Rphys^2 →
    (∀ i∈S, 1 ≤ Nlen i ∧ (r i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f i) (round (z i))/6)*((r i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f i) (round (z i))/6)*
      ((r i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : ι × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    ∃ A : ((ι × Fin 2) × (ι × Fin 2)) → Fin 4 → ℤ,
      (∀ k : ZMod K₀,
        (∑ i∈S, ∑ p : Fin 2, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x i p d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+ε)*(V.card:ℝ)^10*(P.card:ℝ)) ∧
      (∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num)) ∧
      (∀ ij∈P, |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2*Vscale) ∧
        |(A ij 2:ℝ)| ≤ Rphys^4/(6*Nphys^2*Vscale)) := by
  classical
  obtain ⟨C,hC,hsieve⟩ := exists_huxley_cubic_dual_narrowed_source_sieve.{huxleyNarrowV} hε
  refine ⟨C,hC,?_⟩
  intro ι inst S f z r v Q K₀ instK μ₀ U₀ hμ₀ hμbounds hlevel hden hinv
    Nlen Vscale Nphys Rphys hV hNphys hmesh hminor hcomplete
    q μ ℓ b τ K x V w radius P h D
  have hsum := hsieve K₀ Vscale hV ι S q Nlen v μ ℓ
    (by
      intro i hi
      exact ⟨(r i).pos,(hminor i hi).1,(hminor i hi).2.1,
        hμ₀.trans_le (hμbounds i hi).1,(hminor i hi).2.2⟩) hcomplete
  pm_1713 radius0
  pm_2136 P0 d w radius0
  pm_5054 hKpos K₀
  pm_7391 hKone
  have hVp : 0 < Vscale := zero_lt_one.trans_le hV
  have hrad d : radius d ≤ radius0 d := by
    fin_cases d
    · exact le_rfl
    · change 1/(12*(K₀:ℝ)^2*Vscale) ≤ 1/(12*(K₀:ℝ)^2)
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith only [mul_nonneg (show 0 ≤ 12*(K₀:ℝ)^2 by positivity)
        (sub_nonneg.mpr hV)]
    · exact le_rfl
    · exact le_rfl
  pm_5157 P P0 d
  obtain ⟨A,hA⟩ := source_arc_fourier_cloud_matrices S f z r v Q K₀ μ₀ U₀
    hμ₀ hμbounds hlevel hden hinv
  change ∀ ij∈P0, _ at hA
  refine ⟨A,hsum,(fun ij hij => hA ij (hsub hij)),?_⟩
  intro ij hij
  pm_1710
  have hcast d : (ei d:ℝ)/qi d=(pr d:ℝ) := by
    fin_cases d
    pm_1712
  have hband : ∀ d, (qi d:ℝ) ≤ (Q:ℝ) ∧ (Q:ℝ) ≤ 2*(qi d:ℝ) := by
    intro d
    fin_cases d
    pm_1711
  pm_5969 hdet
  have ht' : (A ij 2:ℝ)*((ei 0:ℝ)/qi 0)+A ij 3=(qi 1:ℝ)/qi 0 := by
    rw [hcast]
    change (A ij 2:ℝ)*(r ij.1.1:ℝ)+A ij 3=
      ((r ij.2.1).den:ℝ)/(r ij.1.1).den
    simpa only [hlevel _ hi] using ht
  have hmap' : ((A ij 0:ℝ)*((ei 0:ℝ)/qi 0)+A ij 1)/
      ((A ij 2:ℝ)*((ei 0:ℝ)/qi 0)+A ij 3)=(ei 1:ℝ)/qi 1 := by
    rw [hcast,hcast]
    change ((A ij 0:ℝ)*(r ij.1.1:ℝ)+A ij 1)/
      ((A ij 2:ℝ)*(r ij.1.1:ℝ)+A ij 3)=(r ij.2.1:ℝ)
    simpa only [hlevel _ hi,hlevel _ hj] using hmap
  pm_1709
  pm_1714 d hV hdet

private theorem huxley_narrowing_balanced_scale
    {U V a b : ℝ} (hU : 0 < U) (hV : V=U^((3:ℝ)/2)) :
    V*(a/V^((5:ℝ)/3)+b/(U*V))=(a+b)/U := by
  subst V
  have hUp : 0 < U^((3:ℝ)/2) := Real.rpow_pos_of_pos hU _
  have he : (U^((3:ℝ)/2))^((5:ℝ)/3)=U*U^((3:ℝ)/2) := by
    rw [←Real.rpow_mul hU.le]
    rw [show ((3:ℝ)/2)*(5/3)=1+3/2 by norm_num,Real.rpow_add hU,Real.rpow_one]
  rw [he]
  field_simp

private theorem huxley_narrowing_balanced_mass
    {mass K a b U V : ℝ} (hU : 0 < U) (hV : V=U^((3:ℝ)/2))
    (h : mass ≤ K*(a/V^((5:ℝ)/3)+b/(U*V))) :
    V*mass ≤ K*(a+b)/U := by
  have hVp : 0 < V := by rw [hV]; exact Real.rpow_pos_of_pos hU _
  calc
    V*mass ≤ V*(K*(a/V^((5:ℝ)/3)+b/(U*V))) :=
      mul_le_mul_of_nonneg_left h hVp.le
    _ = K*(V*(a/V^((5:ℝ)/3)+b/(U*V))) := by ring
    _ = K*((a+b)/U) := by rw [huxley_narrowing_balanced_scale hU hV]
    _ = _ := by ring

private theorem huxley_reference_reciprocal_scale
    {N Q B U : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hB : 0 < B)
    (hU : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    1/U ≤ 2*B*(Q/N)^((2:ℝ)/3) := by
  have hp : 0 < (N/Q)^((2:ℝ)/3) :=
    Real.rpow_pos_of_pos (div_pos hN hQ) _
  have hh := one_div_le_one_div_of_le (div_pos hp (by positivity)) hU
  apply hh.trans_eq
  rw [one_div_div,div_eq_mul_inv,←Real.inv_rpow (div_pos hN hQ).le]
  rw [inv_div]

                                                                      
                                                                             
                                                               
theorem physicalModelPhase_actual_fourier_original_pair_mass
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ) (Bmajor Cmajor : ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ)
    (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2)
    (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M R base Bcut lambda Uband θ V : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ}
    (hbase : ∀ ij∈P, base ≤ za ij.1.1)
    (hxa : ∀ ij∈P, x ij 0=za ij.1.1)
    (hxb : ∀ ij∈P, x ij 1=zb ij.2.1)
    (hgapMem : ∀ ij∈P, gap ij∈Gaps)
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometryB : ∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ))
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < (N:ℝ))
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hmesh : (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband)
    (hinv : ∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : (N:ℝ)^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2)
    (hc : ∀ ij∈P, Mat ij 2 ≠ 0)
    (hlarge : ∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (haction : ∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2)
    (hV : 1 ≤ V)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, x ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Gcap := R^4/(6*(N:ℝ)^2*V)
    let Kstar := 2*Cfirst*R^4/(Lunit^3*(N:ℝ)^2)
    let Aweight := 4*(m0:ℝ)
    let Bweight := 4*(m0:ℝ)*Cpack*R^4/(Lunit^2*(N:ℝ)^2*(Uref:ℝ))+
      (m0:ℝ)*Cgap*R^4/((N:ℝ)^2*(Uref:ℝ))+2*(m0:ℝ)*Gcap
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Kmass := 60*588*(m0:ℝ)*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)
    ((P.card:ℝ) ≤
      60*588*(Uband/lambda)^2*Uband^2*Gcap*
        (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight)) ∧
    (P.card:ℝ) ≤
      60*588*(m0:ℝ)*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)) ∧
    (V=(Uref:ℝ)^((3:ℝ)/2) →
      V*(P.card:ℝ) ≤ Kmass*(Cmain+Ctail)/(Uref:ℝ)) ∧
    (V=(Uref:ℝ)^((3:ℝ)/2) →
      ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
      V*(P.card:ℝ) ≤ 2*Bselect*Kmass*(Cmain+Ctail)*
        ((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)) := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear hnearNarrow
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Cpack Cfirst Cgap
    Gcap Kstar Aweight Bweight Cmain Ctail Kmass
  have hNnat : 0 < N := by exact_mod_cast hN
  pm_1776
  pm_1717
  have hmodelMap ij (hij : ij∈P) :
      ((Mat ij 0:ℝ)*(iteratedDeriv 2 (f 0) (za ij.1.1)/2)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(iteratedDeriv 2 (f 0) (za ij.1.1)/2)+Mat ij 3)=
        iteratedDeriv 2 (f 1) (zb ij.2.1)/2 := by
    pm_1005
  pm_1718
  pm_6352 B Mat
  let Matrices := P.image Mat
  obtain ⟨pick,hpick,hpairNat⟩ := physicalModelPhase_reference_matrix_window_selection
    P Mat gap F A W za zb AlenA AlenB N Za Zb base hσ hδ hF₂ hT hM hNnat
    hA hW hbase hz hgeometryA hgeometryB hmodelMap
  have hdata B (hB : B∈Matrices) ab (_hab : ab∈Gaps) j (hj : j∈S B ab) :
      pick B ab j∈P ∧ Mat (pick B ab j)=B ∧ gap (pick B ab j)=ab ∧
        block (pick B ab j)=j ∧
        za (pick B ab j).1.1∈Icc (base+(N:ℝ)*j) (base+(N:ℝ)*((j:ℝ)+1)) := by
    pm_1719
    exact hpick B hB ab hab' j hj
  have hgapSub : P.image gap ⊆ Gaps := by
    pm_2532 ab hab ij hij
    exact hgapMem ij hij
  have hpairNat' : P.card ≤ 60*∑ B∈Matrices, ∑ ab∈Gaps, (S B ab).card := by
    apply hpairNat.trans
    apply Nat.mul_le_mul_left 60
    apply Finset.sum_le_sum
    intro B _hB
    pm_7739
  have hpair : (P.card:ℝ) ≤ 60*(∑ B∈Matrices, ∑ ab∈Gaps, ((S B ab).card:ℝ)) := by
    exact_mod_cast hpairNat'
  have hmass :
      ((∑ B∈Matrices, ∑ ab∈Gaps, ((S B ab).card:ℝ)) ≤
        588*(Uband/lambda)^2*Uband^2*Gcap*
          (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight)) ∧
      (∑ B∈Matrices, ∑ ab∈Gaps, ((S B ab).card:ℝ)) ≤
        588*(m0:ℝ)*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
          (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)) := by
    exact physicalModelPhase_actual_fourier_charted_matrix_source_mass
      Uref Refs Gaps (Bselect:=Bselect) Matrices Bmajor Cmajor S Q K₀
      (fun B ab j => rat (pick B ab j))
      (fun B ab j => vinv (pick B ab j))
      (fun B ab j => parity (pick B ab j))
      (fun B ab j => anchor (pick B ab j)) e r v s
      (x:=fun B ab j => x (pick B ab j))
      hσ
      hδ
      hF
      hT
      hM
      hN
      hR
      hRM
      hQ
      hscale
      hmesh
      hA
      hW
      (by
        intro B hB ab hab j hj
        exact hx _ (hdata B hB ab hab j hj).1)
      (by
        pm_1716
        pm_7392 B
        exact hp.2.2.2.2)
      (by
        intro B hB ab hab j hj
        exact hden _ (hdata B hB ab hab j hj).1)
      hlambda
      hUband
      hθ
      hθmax
      (by
        intro B hB ab hab j hj
        exact hcurv _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hinv _ (hdata B hB ab hab j hj).1)
      hchart
      horientation
      hBcut
      hs
      hrefSet
      hparentSet
      hsep
      (by
        intro B hB ab hab j hj
        exact hwideL _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hwideU _ (hdata B hB ab hab j hj).1)
      hUref
      hBselectSize
      hcutMargin
      hselectedWrap
      hreferenceDen
      hgapWidth
      hRQ
      hselectedUpper
      hscaleTen
      (by
        pm_1716
        pm_7740
        exact hh)
      (by
        pm_1715
        exact hc ij hij)
      (by
        pm_1715
        exact hlarge ij hij)
      (by
        pm_1715
        exact haction ij hij)
      hV
      hgap
      (by
        intro B hB ab hab j hj
        exact hsourceColor _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hlevel _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hcolor _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hnear _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hnearNarrow _ (hdata B hB ab hab j hj).1)
      hsmall
      hNR
      hRN
      hNcube
      hminscale
      (by
        pm_1715
        exact hMatdet ij hij)
      (by
        pm_1716
        pm_1212 hMatt
        exact hh)
      (by
        pm_1716
        pm_1212 hMatmap
        exact hh)
      (by
        pm_1715
        exact hMatgamma ij hij)
      hNtwo
      (by
        intro B hB ab hab j hj
        exact hL _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hU _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hanchor _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hcut _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hcount _ (hdata B hB ab hab j hj).1)
      hsize
      hD
      hΔ
      hBsize
      hBmajor
      hCmajor
  have hraw : (P.card:ℝ) ≤ 60*588*(Uband/lambda)^2*Uband^2*Gcap*
      (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight) := by
    simpa only [mul_assoc] using hpair.trans
      (mul_le_mul_of_nonneg_left hmass.1 (by norm_num : (0:ℝ) ≤ 60))
  have hnorm : (P.card:ℝ) ≤ Kmass*
      (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)) := by
    simpa only [Kmass,mul_assoc] using hpair.trans
      (mul_le_mul_of_nonneg_left hmass.2 (by norm_num : (0:ℝ) ≤ 60))
  pm_1693
  have hbalanced (hv : V=(Uref:ℝ)^((3:ℝ)/2)) :
      V*(P.card:ℝ) ≤ Kmass*(Cmain+Ctail)/(Uref:ℝ) :=
    huxley_narrowing_balanced_mass hUp hv hnorm
  pm_253 hraw hnorm hbalanced hv hUlo
  have hκ := modelPhaseThirdLower_pos hσ
  have hBsel : 0 < Bselect := (by positivity : (0:ℝ) < 2+168/modelPhaseThirdLower σ).trans_le hBselectSize
  have hinvU := huxley_reference_reciprocal_scale hN
    (by exact_mod_cast hQ) hBsel hUlo
  have hVm : 0 ≤ V*(P.card:ℝ) :=
    mul_nonneg (zero_le_one.trans hV) (Nat.cast_nonneg _)
  have hcoef : 0 ≤ Kmass*(Cmain+Ctail) :=
    (mul_nonneg hVm hUp.le).trans ((le_div_iff₀ hUp).mp (hbalanced hv))
  calc
    V*(P.card:ℝ) ≤ Kmass*(Cmain+Ctail)/(Uref:ℝ) := hbalanced hv
    _ = Kmass*(Cmain+Ctail)*(1/(Uref:ℝ)) := by ring
    _ ≤ Kmass*(Cmain+Ctail)*(2*Bselect*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)) :=
      mul_le_mul_of_nonneg_left hinvU hcoef
    _ = _ := by ring

public  theorem eventually_reference_chart_majorants
    {Ch Cc ε : ℝ} (hCh : 1 ≤ Ch) (hCc : 1 ≤ Cc) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop,
    let Bmajor := 6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1)
    let Cmajor := ⌊Real.logb (5/4) (Cc*T)⌋₊+1
    ((6+Cmajor*(105+544*Bmajor):ℕ):ℝ) ≤ T^ε := by
  let Kb : ℝ := 222+1728/Real.log 2
  let Kc : ℝ := 1+2/Real.log (5/4)
  let K : ℝ := 6+Kc*(105+544*Kb)
  pm_123 hl2
  have hlc : 0 < Real.log (5/4) := Real.log_pos (by norm_num)
  pm_82 hKb Kb
  pm_82 hKc Kc
  pm_2207
  filter_upwards [eventually_const_log_pow_le_rpow K hK 2 hε,
    Filter.eventually_ge_atTop Ch, Filter.eventually_ge_atTop Cc,
    Filter.eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hsmall hh hc hT hlogT
  dsimp only
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hheight1 : 1 ≤ Ch*T^3 := one_le_mul_of_one_le_of_one_le hCh (one_le_pow₀ hT)
  have hheight : (Ch*T^3)^2 ≤ T^8 := by
    calc
      _ ≤ (T*T^3)^2 := pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right hh (by positivity)) 2
      _ = _ := by ring
  have hlogh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by positivity : 0 < (Ch*T^3)^2) hheight
  rw [Real.logb_pow 2 T 8] at hlogh
  have hfloorh := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<2)
    (one_le_pow₀ hheight1 : 1 ≤ (Ch*T^3)^2))
  have hB : ((6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1):ℕ):ℝ) ≤ Kb*Real.log T := by
    have he : Kb*Real.log T=222*Real.log T+216*(8*Real.logb 2 T) := by
      dsimp only [Kb,Real.logb]
      ring
    pm_7619 hlogh hfloorh
  have hchart1 : 1 ≤ Cc*T := one_le_mul_of_one_le_of_one_le hCc hT
  have hchart : Cc*T ≤ T^2 := by nlinarith only [mul_le_mul_of_nonneg_right hc hTp.le]
  have hlogc := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<5/4)
    (zero_lt_one.trans_le hchart1) hchart
  rw [Real.logb_pow] at hlogc
  have hfloorc := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<5/4) hchart1)
  have hC : ((⌊Real.logb (5/4) (Cc*T)⌋₊+1:ℕ):ℝ) ≤ Kc*Real.log T := by
    have he : Kc*Real.log T=Real.log T+2*Real.logb (5/4) T := by
      dsimp only [Kc,Real.logb]
      ring
    pm_7619 hlogc hfloorc
  have hinner : 105+544*((6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1):ℕ):ℝ) ≤
      (105+544*Kb)*Real.log T := by linarith only [hB,hlogT]
  have hmul := mul_le_mul hC hinner (by positivity) (mul_nonneg hKc (by linarith only [hlogT]))
  have hlogsq : 1 ≤ (Real.log T)^2 := one_le_pow₀ hlogT
  have hcost : ((6+(⌊Real.logb (5/4) (Cc*T)⌋₊+1)*
      (105+544*(6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1))):ℕ):ℝ) ≤ K*(Real.log T)^2 := by
    push_cast
    dsimp only [K]
    push_cast at hmul
    nlinarith only [hmul,hlogsq]
  exact hcost.trans hsmall

public  theorem physical_reference_chart_ratio
    {κ Cp R U d : ℝ} (hκ : 0 < κ) (hCp : 0 < Cp+2) (hR : 0 < R)
    (hd : d ≤ 7*U/(2*R^2)) :
    d/(12*(κ/(16*(Cp+2)*R^2))) ≤ ((14:ℝ)/3)*(Cp+2)/κ*U := by
  have hh := div_le_div_of_nonneg_right hd
    (by positivity : 0 ≤ 12*(κ/(16*(Cp+2)*R^2)))
  apply hh.trans_eq
  field_simp
  ring

private theorem physical_reference_radius_le_source
    {T M N R Q : ℝ} (hT : 0 < T) (hM : 0 < M) (hR : 1 ≤ R)
    (hRQ : R ≤ Q) (hQN : Q ≤ N) (hNM : N^2 ≤ M)
    (hscale : T*N*R^2=M^3) : R^2 ≤ T := by
  have hN : 1 ≤ N := hR.trans (hRQ.trans hQN)
  pm_1772 hN
  have hR₂ : R^2 ≤ M :=
    (pow_le_pow_left₀ (zero_le_one.trans hR) (hRQ.trans hQN) 2).trans hNM
  pm_1771
  exact hR₂.trans hMT

                                                                     
                                                                      
                                                                             
public  theorem eventually_physical_reference_chart_budgets
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀
    (Gaps : Finset (ℝ × ℝ)) (e r v s : ℝ × ℝ → ℤ) (Q Uref : ℕ)
    {δ M N R : ℝ},
    0 ≤ δ → δ ≤ 1 → 0 < T → 0 < M → 1 ≤ R →
    R ≤ (Q:ℝ) → (Q:ℝ) ≤ N → N^2 ≤ M →
    1 ≤ Uref → (Uref:ℝ) ≤ R^2 → T*N*R^2=M^3 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, ab.1 < ab.2 ∧ ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun ab => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun ab => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let εchart := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    ∃ Bmajor Cmajor : ℕ,
      (∀ ab∈Gaps, 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1) ≤ Bmajor) ∧
      (∀ ab∈Gaps, ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*εchart))⌋₊+1 ≤ Cmajor) ∧
      ((6+Cmajor*(105+544*Bmajor):ℕ):ℝ) ≤ T^εloss := by
  pm_1720
  filter_upwards [eventually_reference_chart_majorants hCh hCc hεloss,
    Filter.eventually_ge_atTop (1:ℝ)] with T hmajor hT1
  intro Gaps e r v s Q Uref δ M N R hδ₀ hδmax hT hM hR hRQ hQN hNM
    hU hUR hscale hr hs he hv hgap Vheight P₁ P₂ εchart
  pm_1721
  have hheight ab (hab : ab∈Gaps) :=
    source_reference_seed_height_polynomial hσ hJref hJv hT hM hR hRQ hQN hNM
      hUr hscale hV₀ hVmax (hr ab hab) (hs ab hab) (he ab hab) (hv ab hab)
  pm_1723
  have hRT := physical_reference_radius_le_source hT hM hR hRQ hQN hNM hscale
  refine ⟨Bmajor,Cmajor,?_,?_,hmajor⟩
  · intro ab hab
    pm_1724
    calc
      P₁ ab*P₂ ab ≤ (Ch*T^3)*(Ch*T^3) :=
        mul_le_mul (hheight ab hab).2.2.1 (hheight ab hab).2.2.2
          (zero_le_one.trans (hP₂ ab)) (by positivity)
      _ = _ := by ring
  · intro ab hab
    pm_1725 physical_reference_chart_ratio
    pm_1722


                                                                         
                                                                     
                                                                             
                                                    
theorem eventually_physicalModelPhase_actual_fourier_original_pair_mass
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ)
    (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2)
    (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut lambda Uband θ V : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ij∈P, Mat ij 2 ≠ 0) →
    (∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) →
    (∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2) →
    (1 ≤ V) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, x ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    V=(Uref:ℝ)^((3:ℝ)/2) →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    V*(P.card:ℝ) ≤
      (2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3))*T^εloss := by
  filter_upwards [eventually_physical_reference_chart_budgets hσ hJref hεloss] with T hbudgets
  intro Uref Refs Gaps Bselect P Mat gap Q K₀ _ N za zb AlenA AlenB Za Zb
    rat vinv parity anchor e r v s δ M R base Bcut lambda Uband θ V F A W x
    hbase hxa hxb hgapMem hgeometryA hgeometryB hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    ε sourceColor hsourceColor f hlevel q mu ell b cround tau dual cloud radius
    hcolor hnear hnearNarrow κ Cphys c J B hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma H hNtwo hL hU hanchor hcut hcount
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail hvchoice hUlo
  pm_1727
  pm_1726
  have hmass := hh.2.2.2 hvchoice hUlo
  pm_883
  let Kbase := 2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
    (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)
  have hmass' : V*(P.card:ℝ) ≤ (m0:ℝ)*Kbase := by
    pm_736 hmass m0 Kbase
  pm_6019
  have hknon : 0 ≤ Kbase := by
    have hnon : 0 ≤ (m0:ℝ)*Kbase :=
      (mul_nonneg (zero_le_one.trans hV) (Nat.cast_nonneg _)).trans hmass'
    nlinarith only [hnon,hmpos]
  pm_1728

                                                                     
                                                                       
private theorem positive_difference_actual_endpoint_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/2 ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b l r δ : ℝ) (xa xb : Fin 2 → ℝ),
    0 < η → η ≤ 1/8 → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let G := fun z : ℝ × ℝ =>
      (iteratedDeriv 3 F z.2-iteratedDeriv 3 F (z.2+η*z.1))/(σ*η)
    let t : Fin 2 → ℝ := ![l,r]
    let z₀ := (y₀,H (y₀,x₀))
    l < r →
    (∀ i, xa i∈Icc (1:ℝ) 2 ∧ xb i∈Icc (1:ℝ) 2 ∧
      H (ya,xa i)=t i ∧ H (yb,xb i)=t i+b) →
    (∀ i, ‖((ya,t i):ℝ × ℝ)-z₀‖ < a ∧ ‖((yb,t i+b):ℝ × ℝ)-z₀‖ < a) →
    (∀ i, |G (yb,xb i)-G (ya,xa i)| ≤ δ) →
    ‖((yb-ya,b):ℝ × ℝ)‖*(r-l) ≤ C*δ := by
  pm_114 a₀ ha₀ hcompression positive_difference_constructed_endpoint_compression hσ hc hU
  pm_7741
  pm_2570
  pm_2572
  pm_2546 hR R zero_lt_one.trans_le le_max_left
  pm_116 hκ κ
  refine ⟨a,64*R^6/κ,lt_min ha₀ (by norm_num),min_le_right _ _,by positivity,?_⟩
  pm_1488 hηmax
  pm_1731
  pm_1730
  have hcanonical i : |g (yb,t i+b)-g (ya,t i)| ≤ δ := by
    have ha : ρ (ya,t i)=xa i := positive_difference_curvature_inverse_eq F
      hσ hc hU hη hηmax (hxext _ (hroots i).1) (hyext _ hya)
      hf hbound htests (hroots i).2.2.1
    have hb : ρ (yb,t i+b)=xb i := positive_difference_curvature_inverse_eq F
      hσ hc hU hη hηmax (hxext _ (hroots i).2.1) (hyext _ hyb)
      hf hbound htests (hroots i).2.2.2
    dsimp only [g]
    pm_1006
    exact hnear i
  pm_1729
  have hh := hcompression F η x₀ y₀ ya yb b l r δ hη hηmax hx₀ hy₀
    hf hbound htests hlr hlen hpts (hcanonical 0) (hcanonical 1)
  have hdiv := (le_div_iff₀ hκ).mpr (by nlinarith only [hh] :
    ‖((yb-ya,b):ℝ × ℝ)‖*(r-l)*κ ≤ 64*R^6*δ)
  exact hdiv.trans_eq (by ring)

                                                                  
                                                                            
public  theorem positive_difference_physical_upper_endpoint_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/2 ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b Δ T M : ℝ) (xa xb : Fin 2 → ℝ),
    0 < η → η ≤ 1/8 → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    0 < T → 2 ≤ M → 0 ≤ Δ →
    (∀ i, xa i∈Icc M (2*M) ∧ xb i∈Icc M (2*M)) →
    let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
    let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
    let u := fun i => iteratedDeriv 2 (f ya) (xa i)/2
    let t := fun i => (2*M^2/T)*u i
    let bnorm := 2*M^2*b/T
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let z₀ := (y₀,H (y₀,x₀))
    u 0 < u 1 →
    (∀ i, iteratedDeriv 2 (f yb) (xb i)/2=u i+b) →
    (∀ i, |μ yb (xb i)/μ ya (xa i)-1| ≤ Δ) →
    (∀ i, ‖((ya,t i):ℝ × ℝ)-z₀‖ < a ∧
      ‖((yb,t i+bnorm):ℝ × ℝ)-z₀‖ < a) →
    4*M^4*|b| *(u 1-u 0) ≤ C*(Δ+1/M)*T^2 := by
  obtain ⟨a,C,ha,hac,hC,hcompression⟩ :=
    positive_difference_actual_endpoint_compression hσ hc hU
  pm_1839
  pm_2546 hB B zero_lt_one.trans_le le_max_left
  refine ⟨a,C*B,ha,hac,mul_pos hC hB,?_⟩
  intro F η x₀ y₀ ya yb b Δ T M xa xb hη hηmax hx₀ hy₀ hya hyb
    hf hbound htests hT hM hΔ hpoints f μ u t bnorm H z₀ hu hmap hthird hends
  pm_1811
  let G := fun z : ℝ × ℝ =>
    (iteratedDeriv 3 F z.2-iteratedDeriv 3 F (z.2+η*z.1))/(σ*η)
  have hnorm z (hz : z∈Icc M (2*M)) : z/M∈Icc (1:ℝ) 2 := by
    constructor
    · exact (le_div_iff₀ hMp).mpr (by simpa using hz.1)
    · exact (div_le_iff₀ hMp).mpr hz.2
  have hpos z (hz : z∈Icc M (2*M)) : 0 < z := hMp.trans_le hz.1
  have hroundpos z (hz : z∈Icc M (2*M)) : (0:ℝ) < round z := by
    pm_2586
  have hd n z y (hz : 0 < z) (hy : y∈Icc (1:ℝ) 2) :
      iteratedDeriv n (f y) z=
        T/M^n*((iteratedDeriv n F (z/M)-iteratedDeriv n F (z/M+η*y))/(σ*η)) :=
    positive_difference_physical_iteratedDeriv F hMp hz
      (mul_nonneg hη.le (by linarith only [hy.1])) hf n
  have hrootA i : H (ya,xa i/M)=t i := by
    dsimp only [t,u]
    rw [hd 2 _ _ (hpos _ (hpoints i).1) hya]
    change H (ya,xa i/M)=(2*M^2/T)*(T/M^2*H (ya,xa i/M)/2)
    field_simp
  have hrootB i : H (yb,xb i/M)=t i+bnorm := by
    have he := congrArg (fun z : ℝ => (2*M^2/T)*z) (hmap i)
    rw [hd 2 _ _ (hpos _ (hpoints i).2) hyb] at he
    change (2*M^2/T)*(T/M^2*H (yb,xb i/M)/2)=(2*M^2/T)*(u i+b) at he
    change H (yb,xb i/M)=(2*M^2/T)*u i+2*M^2*b/T
    field_simp at he ⊢
    nlinarith only [he]
  have hrounded i :
      |G (yb,(round (M*(xb i/M)):ℝ)/M)/
        G (ya,(round (M*(xa i/M)):ℝ)/M)-1| ≤ Δ := by
    pm_5727 z hMp.ne'
    pm_1735 i
    pm_1734
  have hnear i : |G (yb,xb i/M)-G (ya,xa i/M)| ≤ B*(Δ+1/M) :=
    positive_difference_rounded_third_bound F hσ hc hU hη hηmax hM
      (hnorm _ (hpoints i).1) (hnorm _ (hpoints i).2) hya hyb
      hf hbound htests hΔ (hrounded i)
  pm_1733
  have hh := hcompression F η x₀ y₀ ya yb bnorm (t 0) (t 1) (B*(Δ+1/M))
    (fun i => xa i/M) (fun i => xb i/M) hη hηmax hx₀ hy₀ hya hyb hf hbound htests ht
    (by intro i; rw [htvec]; exact ⟨hnorm _ (hpoints i).1,hnorm _ (hpoints i).2,hrootA i,hrootB i⟩)
    (by intro i; rw [htvec]; exact hends i)
    hnear
  have hn : 2*M^2*|b|/T ≤ ‖((yb-ya,bnorm):ℝ × ℝ)‖ := by
    pm_1732
  have hm := (mul_le_mul_of_nonneg_right hn (sub_nonneg.mpr ht.le)).trans hh
  have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg T)
  have he : (2*M^2*|b|/T*(t 1-t 0))*T^2=4*M^4*|b| *(u 1-u 0) := by
    dsimp only [t]
    field_simp
    ring
  rw [he] at hm'
  exact hm'.trans_eq (by ring)


private theorem huxley_upper_endpoint_source_scale
    {κ L R M N T S E C D b g : ℝ}
    (hL : 0 < L) (hR : 1 ≤ R) (hM : 0 < M)
    (hN : 0 < N) (hS : 0 < S)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hb : 0 ≤ b)
    (hNL : (L*N)^2 ≤ M*R) (hscale : T*N*R^2=M^3)
    (hST : S ≤ E*T) (hlow : κ*L/(8*R^2) ≤ g)
    (hu : 4*M^4*b*g ≤ C*(D*R^2/(L^2*N^2)+1/M)*S^2) :
    κ*b*L^3*N^4 ≤ 2*C*(D+1)*E^2*M^2 := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNLR : L^2*N^2 ≤ M*R^2 := by
    calc
      _ = (L*N)^2 := by ring
      _ ≤ M*R := hNL
      _ ≤ M*R^2 := mul_le_mul_of_nonneg_left (by nlinarith only [hR] : R ≤ R^2) hM.le
  have hInv : 1/M ≤ R^2/(L^2*N^2) :=
    (div_le_div_iff₀ hM (by positivity)).mpr (by nlinarith only [hNLR])
  have hcost : D*R^2/(L^2*N^2)+1/M ≤ (D+1)*R^2/(L^2*N^2) := by
    calc
      _ ≤ D*R^2/(L^2*N^2)+R^2/(L^2*N^2) := add_le_add le_rfl hInv
      _ = _ := by ring
  have hsquare : S^2 ≤ E^2*T^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hS.le hST 2
  have hupper : 4*M^4*b*g ≤ C*((D+1)*R^2/(L^2*N^2))*(E^2*T^2) :=
    hu.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hcost hC) hsquare (sq_nonneg S) (by positivity))
  have hh := (mul_le_mul_of_nonneg_left hlow
    (by positivity : 0 ≤ 4*M^4*b)).trans hupper
  have heleft : 4*M^4*b*(κ*L/(8*R^2))=κ*b*L*M^4/(2*R^2) := by ring
  have heright : C*((D+1)*R^2/(L^2*N^2))*(E^2*T^2)=
      C*(D+1)*R^2*E^2*T^2/(L^2*N^2) := by ring
  rw [heleft,heright] at hh
  have hcross := (div_le_div_iff₀ (by positivity : 0 < 2*R^2)
    (by positivity : 0 < L^2*N^2)).mp hh
  have hmul := mul_le_mul_of_nonneg_right hcross (sq_nonneg N)
  have hsq : T^2*N^2*R^4=M^6 := by
    have he := congrArg (fun z : ℝ => z^2) hscale
    nlinarith only [he]
  have hright : (C*(D+1)*R^2*E^2*T^2*(2*R^2))*N^2=
      2*C*(D+1)*E^2*M^6 := by
    calc
      _ = 2*C*(D+1)*E^2*(T^2*N^2*R^4) := by ring
      _ = _ := by rw [hsq]
  rw [hright] at hmul
  apply (mul_le_mul_iff_right₀ (pow_pos hM 4)).mp
  convert hmul using 1 <;> ring

                                                                
                                                                 
                                                                                              
private theorem positive_difference_quartic_upper_long_block_constraint
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a Csrc : ℝ, 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb b Tsrc E : ℝ)
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ)
    {F : Fin 2 → ℝ → ℝ} (A : Fin 2 → ℤ) {W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ},
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 < d) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, r i ≠ 0) →
    (∀ i, v i*r i-e i*s i=1) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d) →
    (StrictMono x) →
    (T*N*R^2=M^3) →
    (e 1=e 0+b*r 0 ∧ v 1=v 0+b*s 0 ∧ r 1=r 0 ∧ s 1=s 0) →
    0 < η → η ≤ 1/8 → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let D := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let H := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/D y i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, |n y i|^2 ≤ M*R) →
    (∀ j : Fin 7, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
    (∀ j : Fin 8, |α*x j+β-g (x j)+H (x j)| ≤ K*R^2/|r 0*G (x j)|) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let Src := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    (∀ i, f i=fun z => Src (yp i) ((A i:ℝ)+z)) →
    (∀ z∈({x 0,x 7} : Finset ℝ), ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ z i)/2)):ℝ × ℝ)-center‖ < a) →
    κ*|b| *L^3*N^4 ≤ 2*Csrc*(C+1)*E^2*M^2 := by
  obtain ⟨a,Csrc,ha,_hac,hCsrc,hcompression⟩ :=
    positive_difference_physical_upper_endpoint_compression hσsrc hcsrc hUsrc
  pm_119 a Csrc ha hCsrc
  intro Fsrc η xcenter ycenter ya yb b Tsrc E σ δ T M N R L d K α β x F A W x₀ e r v s x₁
    hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    f n μ ν D g H G hbase hpoint hsquare hgap hres κ Γ C yp Src Hsrc center hsource hlocalEnds
  pm_1740
  have hcurvOrder u w (hu : u∈Icc (x 0) (x 7)) (hv : w∈Icc (x 0) (x 7))
      (huv : u ≤ w) i :
      iteratedDeriv 2 (f i) (x₁ w i)/2 ≤ iteratedDeriv 2 (f i) (x₁ u i)/2 := by
    apply sub_nonneg.mp
    have hdu : 0 < D u i := hd.trans_le (hden u hu i)
    have hdv : 0 < D w i := hd.trans_le (hden w hv i)
    rw [hpoint u hu i,hpoint w hv i,div_sub_div _ _ hdu.ne' hdv.ne']
    have hnum : (e i*u+v i)*D w i-D u i*(e i*w+v i)=w-u := by
      dsimp only [D]
      linear_combination (w-u)*hdet i
    rw [hnum]
    exact div_nonneg (sub_nonneg.mpr huv) (mul_pos hdu hdv).le
  have hlocal z (hz : z∈Icc (x 0) (x 7)) i :
      ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ z i)/2)):ℝ × ℝ)-center‖ < a := by
    pm_8531 hl
    pm_8532 hu
    have hlo := mul_le_mul_of_nonneg_left (hcurvOrder z (x 7) hz hxright hz.2 i)
      (by positivity : 0 ≤ 2*M^2/Tsrc)
    have hhi := mul_le_mul_of_nonneg_left (hcurvOrder (x 0) z hxleft hz hz.1 i)
      (by positivity : 0 ≤ 2*M^2/Tsrc)
    change max |yp i-center.1|
      |(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ (x 7) i)/2)-center.2| < a at hl
    change max |yp i-center.1|
      |(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ (x 0) i)/2)-center.2| < a at hu
    change max |yp i-center.1|
      |(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ z i)/2)-center.2| < a
    pm_1738
  pm_1774
  pm_1776
  pm_1775
  pm_6344 z₁ z₀
  pm_1779
  pb_17
  have hC : 0 ≤ C := by
    have hh : 0 ≤ C*(R^2/(L^2*N^2)) := by simpa only [Δ,mul_div_assoc] using hΔ
    have hp : 0 < R^2/(L^2*N^2) := by positivity
    nlinarith only [hh,hp]
  have hDsame t : D t 1=D t 0 := by
    dsimp only [D]
    rw [htransport.2.2.1,htransport.2.2.2]
  have hmap t (ht : t∈Icc (x 0) (x 7)) :
      iteratedDeriv 2 (f 1) (x₁ t 1)/2=profile t+b := by
    change _=iteratedDeriv 2 (f 0) (x₁ t 0)/2+b
    rw [hpoint t ht 1,hpoint t ht 0,hDsame]
    rw [htransport.1,htransport.2.1]
    have hd0 : r 0*t+s 0 ≠ 0 := (hdpos t ht 0).ne'
    dsimp only [D]
    field_simp [hd0]
    ring
  have hthird' p : |μnew (z p) 1/μnew (z p) 0-1| ≤ Δ := by
    pm_1739
    rw [hDsame] at hh
    rwa [mul_div_mul_right _ _ (pow_ne_zero 3 (hdpos _ (hz p) 0).ne')] at hh
  pm_1736
  pm_1741
  pm_1737
  have hub p : iteratedDeriv 2 (Src yb) (xb p)/2=profile (z p)+b := by
    pm_1742
  have hstrict : profile z₁ < profile z₀ := by
    have hp : 0 < κ*L/(8*R^2) := by positivity
    linarith only [hlo,hp]
  have hh := hcompression Fsrc η xcenter ycenter ya yb b Δ Tsrc M xa xb
    hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hΔ hphysical
    (by
      change iteratedDeriv 2 (Src ya) (xa 0)/2 < iteratedDeriv 2 (Src ya) (xa 1)/2
      rw [hua,hua]
      exact hstrict)
    (by
      intro p
      change iteratedDeriv 2 (Src yb) (xb p)/2=iteratedDeriv 2 (Src ya) (xa p)/2+b
      rw [hua,hub])
    (by
      intro p
      have hh := hthird' p
      change |(iteratedDeriv 3 (f 1) (round (x₁ (z p) 1))/6)/
        (iteratedDeriv 3 (f 0) (round (x₁ (z p) 0))/6)-1| ≤ Δ at hh
      rw [hrounded,hrounded] at hh
      exact hh)
    (by
      intro p
      change ‖((ya,(2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa p)/2)):ℝ × ℝ)-center‖ < a ∧
        ‖((yb,(2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa p)/2)+2*M^2*b/Tsrc):ℝ × ℝ)-center‖ < a
      pm_7164
      · have he : (2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa p)/2)+
            2*M^2*b/Tsrc=(2*M^2/Tsrc)*(iteratedDeriv 2 (f 1) (x₁ (z p) 1)/2) := by
          rw [hua,hmap _ (hz p)]
          ring
        rw [he]
        exact hlocal _ (hz p) 1)
  change 4*M^4*|b| *(iteratedDeriv 2 (Src ya) (xa 1)/2-iteratedDeriv 2 (Src ya) (xa 0)/2) ≤
    Csrc*(Δ+1/M)*Tsrc^2 at hh
  rw [hua,hua] at hh
  exact huxley_upper_endpoint_source_scale hL hR hM hN hTsrc hCsrc.le hC
    (abs_nonneg b) hNL hscale hsourceScale hlo hh

                                                                
                                                                        
                                                                     
theorem positive_difference_normalized_quartic_upper_long_block_constraint
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a Csrc : ℝ, 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb b Tsrc E : ℝ)
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ)
    (A : Fin 2 → ℤ) {W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ},
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*(![ya,yb] : Fin 2 → ℝ) i))/(σsrc*η)
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 < d) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, r i ≠ 0) →
    (∀ i, v i*r i-e i*s i=1) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d) →
    (StrictMono x) →
    (T*N*R^2=M^3) →
    (e 1=e 0+b*r 0 ∧ v 1=v 0+b*s 0 ∧ r 1=r 0 ∧ s 1=s 0) →
    0 < η → η ≤ 1/8 → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let D := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let H := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/D y i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, |n y i|^2 ≤ M*R) →
    (∀ j : Fin 7, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
    (∀ j : Fin 8, |α*x j+β-g (x j)+H (x j)| ≤ K*R^2/|r 0*G (x j)|) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    (∀ z∈({x 0,x 7} : Finset ℝ), ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ z i)/2)):ℝ × ℝ)-center‖ < a) →
    κ*|b| *L^3*N^4 ≤ 2*Csrc*(C+1)*E^2*M^2 := by
  pm_8471 hcore positive_difference_quartic_upper_long_block_constraint
  pm_119 a Csrc ha hCsrc
  intro Fsrc η xcenter ycenter ya yb b Tsrc E σ δ T M N R L d K α β x A W x₀ e r v s x₁
    F hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    f n μ ν D g H G hbase hpoint hsquare hgap hres κ Γ C yp Hsrc center hlocalEnds
  pm_1743
  pm_1744
  exact hcore Fsrc η xcenter ycenter ya yb b Tsrc E x (F:=F) A
    hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    hbase hpoint hsquare hgap hres hsource hlocalEnds

private theorem positive_difference_actual_reciprocal_endpoint_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ a ≤ 1/2 ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b l r δ : ℝ) (xa xb : Fin 2 → ℝ),
    0 < η → η ≤ η₀ → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let G := fun z : ℝ × ℝ =>
      (iteratedDeriv 3 F z.2-iteratedDeriv 3 F (z.2+η*z.1))/(σ*η)
    let t : Fin 2 → ℝ := ![l,r]
    let z₀ := (y₀,(H (y₀,x₀))⁻¹)
    l < r →
    (∀ i, xa i∈Icc (1:ℝ) 2 ∧ xb i∈Icc (1:ℝ) 2 ∧
      H (ya,xa i)=(t i)⁻¹ ∧ H (yb,xb i)=(t i+b)⁻¹) →
    (∀ i, ‖((ya,t i):ℝ × ℝ)-z₀‖ < a ∧ ‖((yb,t i+b):ℝ × ℝ)-z₀‖ < a) →
    (∀ i, |G (yb,xb i)*((H (yb,xb i))⁻¹)^3-
      G (ya,xa i)*((H (ya,xa i))⁻¹)^3| ≤ δ) →
    ‖((yb-ya,b):ℝ × ℝ)‖*(r-l) ≤ C*δ := by
  obtain ⟨η₀,a₀,C,hη₀,hηcap,ha₀,hC,hcompression⟩ :=
    positive_difference_constructed_reciprocal_endpoint_compression hσ hc hU
  pm_7741
  refine ⟨η₀,a,C,hη₀,hηcap,lt_min ha₀ (by norm_num),min_le_right _ _,hC,?_⟩
  pm_1488 hηsmall
  pm_4902 hηmax hηsmall.trans
  pm_1731
  let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
  pm_1730
  have hcanonical i : |k (yb,t i+b)-k (ya,t i)| ≤ δ := by
    have ha : ρ (ya,(t i)⁻¹)=xa i := positive_difference_curvature_inverse_eq F
      hσ hc hU hη hηmax (hxext _ (hroots i).1) (hyext _ hya)
      hf hbound htests (hroots i).2.2.1
    have hb : ρ (yb,(t i+b)⁻¹)=xb i := positive_difference_curvature_inverse_eq F
      hσ hc hU hη hηmax (hxext _ (hroots i).2.1) (hyext _ hyb)
      hf hbound htests (hroots i).2.2.2
    dsimp only [k,g]
    pm_1006
    have hh := hnear i
    rw [(hroots i).2.2.1,(hroots i).2.2.2,inv_inv,inv_inv] at hh
    simpa only [mul_comm] using hh
  pm_1729
  exact hcompression F η x₀ y₀ ya yb b l r δ hη hηsmall hx₀ hy₀ hya hyb
    hf hbound htests hlr hlen hpts (hcanonical 0) (hcanonical 1)



private theorem reciprocal_endpoint_curvature_bound
    {a b T M R C D γ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hT : 0 < T) (hM : 0 < M)
    (horder : a⁻¹ ≤ b⁻¹)
    (hA : |a| ≤ T*R/(2*M^2)) (hB : |b| ≤ T*R/(2*M^2))
    (hraw : T^2*|γ| *(b⁻¹-a⁻¹) ≤ 4*C*D*M^4) :
    |γ| *|b-a| ≤ C*D*R^2 := by
  have hi : 0 ≤ b⁻¹-a⁻¹ := sub_nonneg.mpr horder
  have hbox : 0 ≤ T*R/(2*M^2) := (abs_nonneg a).trans hA
  have hab : |a| *|b| ≤ (T*R/(2*M^2))^2 := by
    simpa only [pow_two] using mul_le_mul hA hB (abs_nonneg b) hbox
  have hid : |b-a|=|a| *|b| *(b⁻¹-a⁻¹) := by
    have he : b-a=a*b*(a⁻¹-b⁻¹) := by field_simp
    rw [he,abs_mul,abs_mul,abs_sub_comm,abs_of_nonneg hi]
  have hmain : T^2*|γ| *(b⁻¹-a⁻¹)/(4*M^4) ≤ C*D :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hraw])
  calc
    |γ| *|b-a| = |γ| *(|a| *|b| *(b⁻¹-a⁻¹)) := by rw [hid]
    _ ≤ |γ| *((T*R/(2*M^2))^2*(b⁻¹-a⁻¹)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hab hi) (abs_nonneg _)
    _ = (T^2*|γ| *(b⁻¹-a⁻¹)/(4*M^4))*R^2 := by field_simp; ring
    _ ≤ C*D*R^2 := mul_le_mul_of_nonneg_right hmain (sq_nonneg R)



                                                                
                                                           
public  theorem positive_difference_physical_lower_endpoint_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ a ≤ 1/2 ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb γ Δ T M : ℝ) (xa xb : Fin 2 → ℝ),
    0 < η → η ≤ η₀ → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    0 < T → 2 ≤ M → 0 ≤ Δ →
    (∀ i, xa i∈Icc M (2*M) ∧ xb i∈Icc M (2*M)) →
    let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
    let h := fun y z => iteratedDeriv 2 (f y) z/2
    let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
    let u := fun i => (h ya (xa i))⁻¹
    let t := fun i => (T/(2*M^2))*u i
    let bnorm := T*γ/(2*M^2)
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let z₀ := (y₀,(H (y₀,x₀))⁻¹)
    u 0 < u 1 →
    (∀ i, h yb (xb i)=h ya (xa i)/(γ*h ya (xa i)+1)) →
    (∀ i, |μ yb (xb i)/μ ya (xa i)*(γ*h ya (xa i)+1)^3-1| ≤ Δ) →
    (∀ i, ‖((ya,t i):ℝ × ℝ)-z₀‖ < a ∧
      ‖((yb,t i+bnorm):ℝ × ℝ)-z₀‖ < a) →
    |γ| *|h ya (xa 1)-h ya (xa 0)| ≤ C*(Δ+1/M) := by
  obtain ⟨η₀,a,C,hη₀,hηcap,ha,hac,hC,hcompression⟩ :=
    positive_difference_actual_reciprocal_endpoint_compression hσ hc hU
  pm_2570
  pm_2546 hR R zero_lt_one.trans_le le_max_left
  refine ⟨η₀,a,C*R^12,hη₀,hηcap,ha,hac,by positivity,?_⟩
  intro F η x₀ y₀ ya yb γ Δ T M xa xb hη hηsmall hx₀ hy₀ hya hyb
    hf hbound htests hT hM hΔ hpoints f h μ u t bnorm H z₀ hu hmap hthird hends
  pm_4902 hηmax hηsmall.trans
  pm_2580
  pm_2557 G
  let P := fun v => G v*((H v)⁻¹)^3
  let L := T/(2*M^2)
  have hL : L ≠ 0 := by dsimp only [L]; positivity
  have hnorm x (hx : x ∈ Icc M (2*M)) : x/M ∈ Icc (1:ℝ) 2 := by
    constructor
    · exact (le_div_iff₀ hMpos).mpr (by simpa using hx.1)
    · exact (div_le_iff₀ hMpos).mpr hx.2
  have hpos x (hx : x ∈ Icc M (2*M)) : 0 < x := hMpos.trans_le hx.1
  have hroundpos x (hx : x ∈ Icc M (2*M)) : (0:ℝ) < round x := by
    have hh := abs_le.mp (abs_sub_round x)
    linarith only [hh.2,hx.1,hM]
  have hd n x y (hx : 0 < x) (hy : y ∈ Icc (1:ℝ) 2) :
      iteratedDeriv n (f y) x=
        T/M^n*((iteratedDeriv n F (x/M)-iteratedDeriv n F (x/M+η*y))/(σ*η)) :=
    positive_difference_physical_iteratedDeriv F hMpos hx
      (mul_nonneg hη.le (by linarith only [hy.1])) hf n
  have hHne x y (hx : x ∈ Icc M (2*M)) (hy : y ∈ Icc (1:ℝ) 2) :
      H (y,x/M) ≠ 0 := by
    have hx' := hnorm x hx
    have hxwide : x/M ∈ Icc (3/4:ℝ) (9/4) :=
      ⟨by linarith only [hx'.1],by linarith only [hx'.2]⟩
    have hywide : y ∈ Icc (1/2:ℝ) 3 :=
      ⟨by linarith only [hy.1],by linarith only [hy.2]⟩
    pm_1745
    pm_4996 hlo F hσ hc hηmax hxwide hywide hf
    exact abs_pos.mp (lt_of_lt_of_le (by positivity) hlo)
  have hHbound x y (hx : x∈Icc M (2*M)) (hy : y∈Icc (1:ℝ) 2) :
      |H (y,x/M)| ≤ R := by
    have hx' := hnorm x hx
    have hxwide : x/M∈Icc (3/4:ℝ) (9/4) :=
      ⟨by linarith only [hx'.1],by linarith only [hx'.2]⟩
    pm_1821
    pm_1745
    pm_5131 hxwide hywide
    exact hup.trans ((le_max_left _ _).trans (le_max_right _ _))
  have hscale x y (hx : x ∈ Icc M (2*M)) (hy : y ∈ Icc (1:ℝ) 2) :
      h y x=L*H (y,x/M) := by
    dsimp only [h]
    rw [hd 2 x y (hpos x hx) hy]
    dsimp only [L,H]
    ring
  have hroots k :
      xa k/M ∈ Icc (1:ℝ) 2 ∧ xb k/M ∈ Icc (1:ℝ) 2 ∧
      (H (yb,xb k/M))⁻¹=(H (ya,xa k/M))⁻¹+T*γ/(2*M^2) := by
    refine ⟨hnorm _ (hpoints k).1,hnorm _ (hpoints k).2,?_⟩
    have hh := hmap k
    rw [hscale _ _ (hpoints k).2 hyb,hscale _ _ (hpoints k).1 hya] at hh
    have hHa := hHne _ _ (hpoints k).1 hya
    calc
      _ = L*(L*H (yb,xb k/M))⁻¹ := by simp [mul_inv_rev,hL,mul_comm]
      _ = L*((γ*(L*H (ya,xa k/M))+1)/(L*H (ya,xa k/M))) := by rw [hh,inv_div]
      _ = _ := by dsimp only [L]; field_simp; ring
  have hratio k :
      H (ya,xa k/M)/H (yb,xb k/M)=γ*h ya (xa k)+1 := by
    have hHa : h ya (xa k) ≠ 0 := by
      pm_5587 k
    calc
      _ = h ya (xa k)/h yb (xb k) := by
        rw [hscale _ _ (hpoints k).1 hya,hscale _ _ (hpoints k).2 hyb,
          mul_div_mul_left _ _ hL]
      _ = h ya (xa k)/(h ya (xa k)/(γ*h ya (xa k)+1)) := by rw [hmap k]
      _ = _ := by field_simp
  have hrounded k :
      |G (yb,(round (M*(xb k/M)):ℝ)/M)/
        G (ya,(round (M*(xa k/M)):ℝ)/M)*(H (ya,xa k/M)/H (yb,xb k/M))^3-1| ≤ Δ := by
    pm_5727 x hMpos.ne'
    pm_1735 k
    rw [←hratio k] at hh
    pm_1734
  have hnear k : |P (yb,xb k/M)-P (ya,xa k/M)| ≤ R^10*(Δ+1/M) :=
    positive_difference_rounded_reciprocal_profile_bound F hσ hc hU hη hηmax hM
      (hroots k).1 (hroots k).2.1 hya hyb hf hbound htests hΔ (hrounded k)
  have htA k : (H (ya,xa k/M))⁻¹=t k := by
    change _=(T/(2*M^2))*(h ya (xa k))⁻¹
    rw [hscale _ _ (hpoints k).1 hya]
    change _=L*(L*H (ya,xa k/M))⁻¹
    simp [mul_inv_rev,hL,mul_comm]
  have hrootA k : H (ya,xa k/M)=(t k)⁻¹ := by
    rw [←htA,inv_inv]
  have hrootB k : H (yb,xb k/M)=(t k+bnorm)⁻¹ := by
    have hh := (hroots k).2.2
    rw [htA] at hh
    change (H (yb,xb k/M))⁻¹=t k+bnorm at hh
    rw [←hh,inv_inv]
  pm_1733
  have hh := hcompression F η x₀ y₀ ya yb bnorm (t 0) (t 1) (R^10*(Δ+1/M))
    (fun i => xa i/M) (fun i => xb i/M) hη hηsmall hx₀ hy₀ hya hyb hf hbound htests ht
    (by intro i; rw [htvec]; exact ⟨hnorm _ (hpoints i).1,hnorm _ (hpoints i).2,hrootA i,hrootB i⟩)
    (by intro i; rw [htvec]; exact hends i)
    hnear
  have hn : T*|γ|/(2*M^2) ≤ ‖((yb-ya,bnorm):ℝ × ℝ)‖ := by
    pm_1732
  have hm := (mul_le_mul_of_nonneg_right hn (sub_nonneg.mpr ht.le)).trans hh
  have hm' := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ 4*M^4)
  have he : (T*|γ|/(2*M^2)*(t 1-t 0))*(4*M^4)=T^2*|γ| *(u 1-u 0) := by
    dsimp only [t]
    field_simp
    ring
  rw [he] at hm'
  have hraw : T^2*|γ| *(u 1-u 0) ≤ 4*(C*R^10)*(Δ+1/M)*M^4 :=
    hm'.trans_eq (by ring)
  have hne i : h ya (xa i) ≠ 0 := by
    pm_5587 i
  have hheight i : |h ya (xa i)| ≤ T*R/(2*M^2) := by
    rw [hscale _ _ (hpoints i).1 hya,abs_mul,abs_of_pos (by dsimp only [L]; positivity : 0 < L)]
    calc
      L*|H (ya,xa i/M)| ≤ L*R :=
        mul_le_mul_of_nonneg_left (hHbound _ _ (hpoints i).1 hya) (by dsimp only [L]; positivity)
      _ = _ := by dsimp only [L]; ring
  have hfinal := reciprocal_endpoint_curvature_bound (hne 0) (hne 1) hT hMpos
    hu.le (hheight 0) (hheight 1) hraw
  exact hfinal.trans_eq (by ring)



private theorem huxley_lower_endpoint_source_scale
    {κ γ L N R M C K Δg : ℝ}
    (hL : 0 < L) (hN : 0 < N) (hR : 1 ≤ R) (hM : 0 < M)
    (hC : 0 ≤ C) (hNL : (L*N)^2 ≤ M*R)
    (hlo : κ*L/(8*R^2) ≤ Δg)
    (hhi : |γ| *Δg ≤ C*(K*R^2/(L^2*N^2)+1/M)) :
    κ*|γ| *L^3*N^2 ≤ 8*C*(K+1)*R^4 := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hround : 1/M ≤ R^2/(L^2*N^2) := by
    apply (div_le_div_iff₀ hM (by positivity)).mpr
    nlinarith only [hNL,mul_nonneg hM.le (show 0 ≤ R^2-R by nlinarith only [hR])]
  have hbound := (mul_le_mul_of_nonneg_left hlo (abs_nonneg γ)).trans hhi
  have hh := hbound.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hround) hC)
  have hm := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ 8*R^2*L^2*N^2)
  have he : |γ| *(κ*L/(8*R^2))*(8*R^2*L^2*N^2)=κ*|γ| *L^3*N^2 := by
    field_simp
  have he' : C*(K*R^2/(L^2*N^2)+R^2/(L^2*N^2))*(8*R^2*L^2*N^2)=8*C*(K+1)*R^4 := by
    field_simp
  rwa [he,he'] at hm

public  theorem reciprocal_fraction_strictMonoOn
    {e r v s l u : ℝ} (hdet : v*r-e*s=1)
    (hne : ∀ z∈Icc l u, e*z+v ≠ 0) :
    StrictMonoOn (fun z => (r*z+s)/(e*z+v)) (Icc l u) := by
  have hd z (hz : z∈Icc l u) :
      HasDerivAt (fun z => (r*z+s)/(e*z+v)) (1/(e*z+v)^2) z := by
    have hh := (((hasDerivAt_id z).const_mul r).add_const s).div
      (((hasDerivAt_id z).const_mul e).add_const v) (hne z hz)
    convert hh using 1
    · rfl
    · have he : r*(e*z+v)-(r*z+s)*e=1 := by linear_combination hdet
      simp only [id_eq,mul_one,he]
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc l u)
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (interior_subset hz)).hasDerivWithinAt)
  intro z hz
  exact div_pos zero_lt_one (sq_pos_of_ne_zero (hne z (interior_subset hz)))



                                                                         
                                                                 
                                                                                              
section
variable {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
include σsrc csrc Usrc hσsrc hcsrc hUsrc
private theorem positive_difference_quartic_lower_long_block_constraint :
    ∃ η₀ a Csrc : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb γ Tsrc : ℝ)
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ)
    {F : Fin 2 → ℝ → ℝ} (A : Fin 2 → ℤ) {W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ},
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 < d) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, r i ≠ 0) →
    (∀ i, v i*r i-e i*s i=1) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d) →
    (StrictMono x) →
    (T*N*R^2=M^3) →
    (e 1=e 0 ∧ v 1=v 0 ∧ r 1=r 0+γ*e 0 ∧ s 1=s 0+γ*v 0) →
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let D := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let H := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/D y i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, |n y i|^2 ≤ M*R) →
    (∀ j : Fin 7, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
    (∀ j : Fin 8, |α*x j+β-g (x j)+H (x j)| ≤ K*R^2/|r 0*G (x j)|) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let Src := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ i, f i=fun z => Src (yp i) ((A i:ℝ)+z)) →
    (∀ z∈({x 0,x 7} : Finset ℝ), ∀ i,
      ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ z i)/2)⁻¹):ℝ × ℝ)-center‖ < a) →
    κ*|γ| *L^3*N^2 ≤ 8*Csrc*(C+1)*R^4 := by
  obtain ⟨η₀,a,Csrc,hη₀,hηcap,ha,_hac,hCsrc,hcompression⟩ :=
    positive_difference_physical_lower_endpoint_compression hσsrc hcsrc hUsrc
  pm_1747
  intro Fsrc η xcenter ycenter ya yb γ Tsrc σ δ T M N R L d K α β x F A W x₀ e r v s x₁
    hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo
    f n μ ν D g H G hbase hpoint hsquare hgap hres κ Γ C yp Src Hsrc center hsource hlocalEnds
  pm_1740
  pm_4902 hηmax' hηmax.trans
  pm_1736
  pm_1741
  pm_1746
  have hcurvNe t (ht : t∈Icc (x 0) (x 7)) i :
      iteratedDeriv 2 (f i) (x₁ t i)/2 ≠ 0 := by
    let q := (A i:ℝ)+x₁ t i
    have hq : q∈Icc M (2*M) :=
      ⟨by dsimp only [q]; linarith only [hA i,(hx₁ _ ht i).1],
       by dsimp only [q]; linarith only [hW i,(hx₁ _ ht i).2]⟩
    have hqnorm : q/M∈Icc (3/4:ℝ) (9/4) := by
      constructor
      · apply (le_div_iff₀ hM).mpr
        linarith only [hq.1,hM]
      · apply (div_le_iff₀ hM).mpr
        linarith only [hq.2,hM]
    have hywide : yp i∈Icc (1/2:ℝ) 3 :=
      ⟨by linarith only [(hyp i).1],by linarith only [(hyp i).2]⟩
    have he := (positive_jets_difference_curvature_entry Fsrc hσsrc hcsrc hUsrc hη hηmax'
      hqnorm hywide hreg hjets htests 3 (by norm_num) (by norm_num)).1
    change iteratedDeriv 2 (fun u => (Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)) (q/M)=
      Hsrc (yp i,q/M) at he
    pm_4996 hloH Fsrc hσsrc hcsrc hηmax' hqnorm hywide hreg
    have hneH : Hsrc (yp i,q/M) ≠ 0 :=
      abs_pos.mp (lt_of_lt_of_le (by positivity) hloH)
    have hd : iteratedDeriv 2 (Src (yp i)) q=Tsrc/M^2*Hsrc (yp i,q/M) :=
      positive_difference_physical_iteratedDeriv Fsrc hM (hM.trans_le hq.1)
        (mul_nonneg hη.le (by linarith only [(hyp i).1])) hreg 2
    rw [hjet]
    change iteratedDeriv 2 (Src (yp i)) q/2 ≠ 0
    rw [hd]
    exact div_ne_zero (mul_ne_zero (div_ne_zero hTsrc.ne' (pow_ne_zero 2 hM.ne')) hneH)
      (by norm_num)
  have hnumNe t (ht : t∈Icc (x 0) (x 7)) i : e i*t+v i ≠ 0 := by
    intro he
    have hh := hcurvNe t ht i
    rw [hpoint t ht i,he,zero_div] at hh
    exact hh rfl
  have hinvEq t (ht : t∈Icc (x 0) (x 7)) i :
      (iteratedDeriv 2 (f i) (x₁ t i)/2)⁻¹=(r i*t+s i)/(e i*t+v i) := by
    rw [hpoint t ht i,inv_div]
  have hinvMono i : StrictMonoOn
      (fun t => (iteratedDeriv 2 (f i) (x₁ t i)/2)⁻¹) (Icc (x 0) (x 7)) := by
    intro u hu w hw huw
    change (iteratedDeriv 2 (f i) (x₁ u i)/2)⁻¹ < (iteratedDeriv 2 (f i) (x₁ w i)/2)⁻¹
    rw [hinvEq u hu i,hinvEq w hw i]
    exact reciprocal_fraction_strictMonoOn (hdet i) (fun t ht => hnumNe t ht i) hu hw huw
  have hlocal z (hz : z∈Icc (x 0) (x 7)) i :
      ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ z i)/2)⁻¹):ℝ × ℝ)-center‖ < a := by
    pm_8532 hl
    pm_8531 hu
    have hlo := mul_le_mul_of_nonneg_left ((hinvMono i).monotoneOn hxleft hz hz.1)
      (by positivity : 0 ≤ Tsrc/(2*M^2))
    have hhi := mul_le_mul_of_nonneg_left ((hinvMono i).monotoneOn hz hxright hz.2)
      (by positivity : 0 ≤ Tsrc/(2*M^2))
    change max |yp i-center.1|
      |(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ (x 0) i)/2)⁻¹-center.2| < a at hl
    change max |yp i-center.1|
      |(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ (x 7) i)/2)⁻¹-center.2| < a at hu
    change max |yp i-center.1|
      |(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ z i)/2)⁻¹-center.2| < a
    pm_1738
  pm_1774
  pm_1776
  pm_1775
  pm_6344 z₀ z₁
  let profile : ℝ → ℝ := fun t => iteratedDeriv 2 (f 0) (x₁ t 0)/2
  have hz p : z p∈Icc (x 0) (x 7) := by
    fin_cases p
    · exact hz₀'
    · exact hz₁'
  pb_17
  have hDmap t : D t 1=D t 0+γ*(e 0*t+v 0) := by
    dsimp only [D]
    rw [htransport.2.2.1,htransport.2.2.2]
    ring_nf
  have hratio t (ht : t∈Icc (x 0) (x 7)) : γ*profile t+1=D t 1/D t 0 := by
    change γ*(iteratedDeriv 2 (f 0) (x₁ t 0)/2)+1=_
    rw [hpoint t ht 0,hDmap]
    field_simp [(hdpos t ht 0).ne']
    ring_nf
  have hmap t (ht : t∈Icc (x 0) (x 7)) :
      iteratedDeriv 2 (f 1) (x₁ t 1)/2=profile t/(γ*profile t+1) := by
    rw [hratio t ht]
    change _=(iteratedDeriv 2 (f 0) (x₁ t 0)/2)/(D t 1/D t 0)
    rw [hpoint t ht 1,hpoint t ht 0,htransport.1,htransport.2.1]
    field_simp [(hdpos t ht 0).ne',(hdpos t ht 1).ne']
  have hinvMap t (ht : t∈Icc (x 0) (x 7)) :
      (iteratedDeriv 2 (f 1) (x₁ t 1)/2)⁻¹=(profile t)⁻¹+γ := by
    rw [hmap t ht,inv_div]
    have hp : profile t ≠ 0 := hcurvNe t ht 0
    rw [add_div,mul_div_cancel_right₀ γ hp,one_div,add_comm]
  have hthird' p :
      |μnew (z p) 1/μnew (z p) 0*(γ*profile (z p)+1)^3-1| ≤ Δ := by
    pm_1739
    have he : μnew (z p) 1/μnew (z p) 0*(D (z p) 1/D (z p) 0)^3=
        μnew (z p) 1*(D (z p) 1)^3/(μnew (z p) 0*(D (z p) 0)^3) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring_nf
    rw [hratio _ (hz p),he]
    exact hh
  pm_1737
  have hub p : iteratedDeriv 2 (Src yb) (xb p)/2=profile (z p)/(γ*profile (z p)+1) := by
    pm_1742
  have hzstrict : z₀ < z₁ := hz₀.2.trans_le
    ((hmono.monotone (by decide : (3:Fin 8) ≤ 4)).trans hz₁.1.le)
  have hh := hcompression Fsrc η xcenter ycenter ya yb γ Δ Tsrc M xa xb
    hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hΔ hphysical
    (by
      change (iteratedDeriv 2 (Src ya) (xa 0)/2)⁻¹ <
        (iteratedDeriv 2 (Src ya) (xa 1)/2)⁻¹
      rw [hua,hua]
      exact hinvMono 0 hz₀' hz₁' hzstrict)
    (by
      intro p
      pm_1748 p
      rw [hua,hub])
    (by
      intro p
      have hh := hthird' p
      change |(iteratedDeriv 3 (f 1) (round (x₁ (z p) 1))/6)/
        (iteratedDeriv 3 (f 0) (round (x₁ (z p) 0))/6)*(γ*profile (z p)+1)^3-1| ≤ Δ at hh
      rw [hrounded,hrounded] at hh
      change |(iteratedDeriv 3 (Src yb) (round (xb p))/6)/
        (iteratedDeriv 3 (Src ya) (round (xa p))/6)*
        (γ*(iteratedDeriv 2 (Src ya) (xa p)/2)+1)^3-1| ≤ Δ
      rw [hua]
      exact hh)
    (by
      intro p
      change ‖((ya,(Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa p)/2)⁻¹):ℝ × ℝ)-center‖ < a ∧
        ‖((yb,(Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa p)/2)⁻¹+Tsrc*γ/(2*M^2)):ℝ × ℝ)-center‖ < a
      pm_7164
      · have he : (Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa p)/2)⁻¹+
            Tsrc*γ/(2*M^2)=(Tsrc/(2*M^2))*(iteratedDeriv 2 (f 1) (x₁ (z p) 1)/2)⁻¹ := by
          rw [hua,hinvMap _ (hz p)]
          ring_nf
        rw [he]
        exact hlocal _ (hz p) 1)
  change |γ| *|iteratedDeriv 2 (Src ya) (xa 1)/2-iteratedDeriv 2 (Src ya) (xa 0)/2| ≤
    Csrc*(Δ+1/M) at hh
  rw [hua,hua] at hh
  change |γ| *|profile z₁-profile z₀| ≤ Csrc*(Δ+1/M) at hh
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr horder)] at hh
  exact huxley_lower_endpoint_source_scale hL hN hR hM hCsrc.le hNL hlo hh


                                                                
                                                                        
                                                                     
theorem positive_difference_normalized_quartic_lower_long_block_constraint :
    ∃ η₀ a Csrc : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb γ Tsrc : ℝ)
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ)
    (A : Fin 2 → ℤ) {W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ},
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*(![ya,yb] : Fin 2 → ℝ) i))/(σsrc*η)
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 < d) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, r i ≠ 0) →
    (∀ i, v i*r i-e i*s i=1) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d) →
    (StrictMono x) →
    (T*N*R^2=M^3) →
    (e 1=e 0 ∧ v 1=v 0 ∧ r 1=r 0+γ*e 0 ∧ s 1=s 0+γ*v 0) →
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let D := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let H := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/D y i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, |n y i|^2 ≤ M*R) →
    (∀ j : Fin 7, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
    (∀ j : Fin 8, |α*x j+β-g (x j)+H (x j)| ≤ K*R^2/|r 0*G (x j)|) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ z∈({x 0,x 7} : Finset ℝ), ∀ i,
      ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ z i)/2)⁻¹):ℝ × ℝ)-center‖ < a) →
    κ*|γ| *L^3*N^2 ≤ 8*Csrc*(C+1)*R^4 := by
  obtain ⟨η₀,a,Csrc,hη₀,hηcap,ha,hCsrc,hcore⟩ :=
    positive_difference_quartic_lower_long_block_constraint hσsrc hcsrc hUsrc
  pm_1747
  intro Fsrc η xcenter ycenter ya yb γ Tsrc σ δ T M N R L d K α β x A W x₀ e r v s x₁
    F hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo
    f n μ ν D g H G hbase hpoint hsquare hgap hres κ Γ C yp Hsrc center hlocalEnds
  pm_1743
  pm_1744
  exact hcore Fsrc η xcenter ycenter ya yb γ Tsrc x (F:=F) A
    hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo
    hbase hpoint hsquare hgap hres hsource hlocalEnds
end


                                                                   
                                                                      
                                                                        
                                                                  
theorem positive_difference_actual_fourier_charted_triangular_constraints
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb Tsrc E : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) {Bselect gapLo gapHi : ℝ}
    (S : Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    let centerInv := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ j∈S, ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(rat j i:ℝ)):ℝ × ℝ)-center‖ < a ∧
      ‖((yp i,(Tsrc/(2*M^2))*(rat j i:ℝ)⁻¹):ℝ × ℝ)-centerInv‖ < a) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ j∈S, ∀ i, lambda ≤ |(rat j i:ℝ)| ∧ |(rat j i:ℝ)| ≤ Uband) →
    (∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1) →
    (v*r-e*s=1) →
    (((0:ℝ) < r ∧ (e:ℝ)/r=gapLo) ∨
      ((r:ℝ) < 0 ∧ (e:ℝ)/r=gapHi)) →
    (0 < Bcut) →
    (s ≠ 0) →
    ((e:ℝ)/r∈Refs) →
    ((v:ℝ)/s∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ j∈S, ∀ i, x j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (R^2 ≤ (r:ℝ)^2*(Uref:ℝ)) →
    (gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := ⌊Real.logb (5/4) ((gapHi-gapLo)/(12*ε))⌋₊+1
    let sourceColor := fun j i => (⌊((rat j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ j∈S, sourceColor j 0=sourceColor j 1) →
    6+Ccharts*(105+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1))) ≤ S.card →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 →
    61*Ccurv*Cphys ≤ Bcut →
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Cthird := ((σ*(σ+1)+1)/κ)*(32*Kres+9*quarticReciprocalConstant σ δ)
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 6+Ccharts*(105+17*S₀.card) ∧
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    0 < L ∧
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) →
      κ*|(Mat 1:ℝ)| *L^3*N^4 ≤ 2*Cupper*(Cthird+1)*E^2*M^2) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) →
      κ*|(Mat 2:ℝ)| *L^3*N^2 ≤ 8*Clower*(Cthird+1)*R^4) ∧
    ∀ Bmajor Cmajor n : ℕ, Blabels ≤ Bmajor → Ccharts ≤ Cmajor → 0 < n →
      (6+Cmajor*(105+544*Bmajor))*n ≤ S.card →
      let Lblock := (2*κ/Cphys)*(n:ℝ)
      ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) →
        κ*|(Mat 1:ℝ)| *Lblock^3*N^4 ≤ 2*Cupper*(Cthird+1)*E^2*M^2) ∧
      ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) →
        κ*|(Mat 2:ℝ)| *Lblock^3*N^2 ≤ 8*Clower*(Cthird+1)*R^4) := by
  pm_1750 positive_difference_normalized_quartic_upper_long_block_constraint positive_difference_normalized_quartic_lower_long_block_constraint
  pm_1749
  intro Fsrc η xcenter ycenter ya yb Tsrc E Uref Refs Bselect gapLo gapHi S Q K₀ inst
    rat vinv parity anchor Mat e r v s σ δ T M N R base Bcut lambda Uband θ A W x
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    yp F Hsrc center centerInv hlocal
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor hS
    f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize Blabels Cthird
  pm_4902 hηmax hηsmall.trans
  have hselected := physicalModelPhase_actual_fourier_charted_reference_gap_quartic_witnesses
    Uref Refs (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) S
    Q K₀ rat vinv parity anchor Mat e r v s
    (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
    (lambda:=lambda) (Uband:=Uband) (θ:=θ) (F:=F) (A:=fun i => (A i:ℝ)) (W:=W) (x:=x)
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap
    hsourceColor hS hlevel hcolor hnear hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hanchor hcut hcount
  obtain ⟨_Schart,_hSchart,_hSchartMass,_G,_hG,_hGMass,_jref,_hjref,xref,hxr,hrest⟩ := hselected
  obtain ⟨d,l,w,hd,S₀,hS₀,hSmass,_hinside,j,z,curve,alpha,beta,
    hpairs,hmono,hLpos,hspan,hK,hcurve,hgap,hres⟩ := hrest hsize hD hΔ hBsize
  let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
  pm_8432 rp r e
  pm_1758
  pm_8432 sp s v
  pm_5023 Ep ep Rp rp
  pm_5023 Vp vp Sp sp
  have hrp i : Rp i ≠ 0 := by
    have hh := (hxr i).1
    change 0 < rp i*r at hh
    intro hz
    change (rp i:ℝ)=0 at hz
    have hz' : rp i=0 := by exact_mod_cast hz
    rw [hz',zero_mul] at hh
    exact (lt_irrefl 0) hh
  have hdet i : Vp i*Rp i-Ep i*Sp i=1 := by
    pm_2663 hd₀ v r e s hchart
    pm_5743 hd₁ hMatdet
    fin_cases i
    · exact hd₀
    · change ((Mat 0*v+Mat 1*s:ℤ):ℝ)*((Mat 2*e+Mat 3*r:ℤ):ℝ)-
        ((Mat 0*e+Mat 1*r:ℤ):ℝ)*((Mat 2*v+Mat 3*s:ℤ):ℝ)=1
      push_cast
      linear_combination ((v:ℝ)*r-e*s)*hd₁+hd₀
  pm_696
  have hbase i : iteratedDeriv 2 (f i) (xref i)/2=Ep i/Rp i := (hxr i).2.2.1
  have hxcurve t (ht : t∈Icc (z 0) (z 7)) i :
      curve t i∈Ioo (1/2:ℝ) (W i-1/2) := ((hcurve t ht).2 i).1
  have hdenL t (ht : t∈Icc (z 0) (z 7)) i : d ≤ Rp i*t+Sp i :=
    ((hcurve t ht).2 i).2.1
  have hdenU t (ht : t∈Icc (z 0) (z 7)) i : Rp i*t+Sp i ≤ 2*d :=
    ((hcurve t ht).2 i).2.2.1
  have hpoint t (ht : t∈Icc (z 0) (z 7)) i :
      iteratedDeriv 2 (f i) (curve t i)/2=(Ep i*t+Vp i)/(Rp i*t+Sp i) :=
    ((hcurve t ht).2 i).2.2.2.1
  have hsquare t (ht : t∈Icc (z 0) (z 7)) i :
      |(round (curve t i):ℝ)-(round (xref i):ℝ)|^2 ≤ M*R :=
    ((hcurve t ht).2 i).2.2.2.2
  have hendlevel k i : iteratedDeriv 2 (f i) (curve (z k) i)/2=(rat (j k) i:ℝ) := by
    have hzk : z k∈Icc (z 0) (z 7) := ⟨hmono.monotone (by omega),hmono.monotone (by omega)⟩
    exact (hpoint _ hzk i).trans ((hpairs k).2 i).symm
  let Lsource := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
  have hupperBound : (Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) →
      κ*|(Mat 1:ℝ)| *Lsource^3*N^4 ≤ 2*CU*(Cthird+1)*E^2*M^2 := by
    intro htri
    have htransport : Ep 1=Ep 0+(Mat 1:ℝ)*Rp 0 ∧
        Vp 1=Vp 0+(Mat 1:ℝ)*Sp 0 ∧ Rp 1=Rp 0 ∧ Sp 1=Sp 0 := by
      simp [Ep,Rp,Vp,Sp,ep,rp,vp,sp,htri.1,htri.2.1,htri.2.2]
    apply hupper Fsrc η xcenter ycenter ya yb (Mat 1) Tsrc E z A
      hσ hδ hF hT hM hN hR hLpos hspan hd hK hA hW hxref hxcurve hrp hdet
      hdenL hdenU hmono hscale htransport hη hηmax hcenterx hcentery hya hyb
      hreg hjets htests hTsrc hMtwo hsourceScale hbase hpoint hsquare hgap hres
    pm_8043
    · subst t
      change ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve (z 0) i)/2)):ℝ × ℝ)-center‖ < aU
      rw [hendlevel]
      exact ((hlocal _ (hS₀ (hpairs 0).1) i).1).trans_le (min_le_left _ _)
    · have he' : t=z 7 := Finset.mem_singleton.mp he
      subst t
      change ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve (z 7) i)/2)):ℝ × ℝ)-center‖ < aU
      rw [hendlevel]
      exact ((hlocal _ (hS₀ (hpairs 7).1) i).1).trans_le (min_le_left _ _)
  have hlowerBound : (Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) →
      κ*|(Mat 2:ℝ)| *Lsource^3*N^2 ≤ 8*CL*(Cthird+1)*R^4 := by
    intro htri
    have htransport : Ep 1=Ep 0 ∧ Vp 1=Vp 0 ∧
        Rp 1=Rp 0+(Mat 2:ℝ)*Ep 0 ∧ Sp 1=Sp 0+(Mat 2:ℝ)*Vp 0 := by
      simp [Ep,Rp,Vp,Sp,ep,rp,vp,sp,htri.1,htri.2.1,htri.2.2,add_comm]
    apply hlower Fsrc η xcenter ycenter ya yb (Mat 2) Tsrc z A
      hσ hδ hF hT hM hN hR hLpos hspan hd hK hA hW hxref hxcurve hrp hdet
      hdenL hdenU hmono hscale htransport hη hηsmall hcenterx hcentery hya hyb
      hreg hjets htests hTsrc hMtwo hbase hpoint hsquare hgap hres
    pm_8043
    · subst t
      change ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve (z 0) i)/2)⁻¹):ℝ × ℝ)-centerInv‖ < aL
      rw [hendlevel]
      exact ((hlocal _ (hS₀ (hpairs 0).1) i).2).trans_le (min_le_right _ _)
    · have he' : t=z 7 := Finset.mem_singleton.mp he
      subst t
      change ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve (z 7) i)/2)⁻¹):ℝ × ℝ)-centerInv‖ < aL
      rw [hendlevel]
      exact ((hlocal _ (hS₀ (hpairs 7).1) i).2).trans_le (min_le_right _ _)
  pm_211 S₀ hS₀ hSmass hLpos hupperBound hlowerBound
  intro Bmajor Cmajor n hBmajor hCmajor hn hblocks Lblock
  pm_1689
  have hlength : Lblock ≤ Lsource :=
    charted_selected_source_length (by dsimp only [Blabels]; omega)
      (by dsimp only [Ccharts]; omega) hBmajor hCmajor hn hκ hCphys hSmass hblocks
  pm_82 hLblock Lblock
  have hpower := pow_le_pow_left₀ hLblock hlength 3
  constructor
  · intro htri
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpower (mul_nonneg hκ.le (abs_nonneg _)))
      (by positivity : 0 ≤ N^4)).trans (hupperBound htri)
  · intro htri
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpower (mul_nonneg hκ.le (abs_nonneg _)))
      (sq_nonneg N)).trans (hlowerBound htri)

                                                                
                                                           

-- Exact proof abbreviations: every original parameter and premise is retained.
abbrev nativeHuxleyReference_physical_source_quartic_constants_nonneg := @physical_source_quartic_constants_nonneg
abbrev nativeHuxleyReference_finite_reference_closed_bracket := @finite_reference_closed_bracket
abbrev nativeHuxleyReference_reference_gap_count_of_closed_profile_width := @reference_gap_count_of_closed_profile_width
abbrev nativeHuxleyReference_reference_chart_fraction_antitone := @reference_chart_fraction_antitone
abbrev nativeHuxleyReference_finite_occupied_cubic_tail_sum := @finite_occupied_cubic_tail_sum
abbrev nativeHuxleyReference_quotient_block_mass := @quotient_block_mass
abbrev nativeHuxleyReference_charted_selected_source_length := @charted_selected_source_length
abbrev nativeHuxleyReference_huxley_completed_narrowed_source_sieve := @huxley_completed_narrowed_source_sieve
abbrev nativeHuxleyReference_huxley_actual_dual_source_box := @huxley_actual_dual_source_box
abbrev nativeHuxleyReference_eventually_reference_chart_majorants := @eventually_reference_chart_majorants
abbrev nativeHuxleyReference_physical_reference_chart_ratio := @physical_reference_chart_ratio
abbrev nativeHuxleyReference_eventually_physical_reference_chart_budgets := @eventually_physical_reference_chart_budgets
abbrev nativeHuxleyReference_positive_difference_physical_upper_endpoint_compression := @positive_difference_physical_upper_endpoint_compression
abbrev nativeHuxleyReference_positive_difference_physical_lower_endpoint_compression := @positive_difference_physical_lower_endpoint_compression
abbrev nativeHuxleyReference_reciprocal_fraction_strictMonoOn := @reciprocal_fraction_strictMonoOn

end TaoTrudgianYang2025.HuxleyRationalPhase

-- Generated closures: source context is replayed in the next part.
end
end
