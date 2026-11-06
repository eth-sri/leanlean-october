module
public import OAI.NumberTheory.DirichletL.Descent.FirstChildWindowsActual
public import OAI.NumberTheory.DirichletL.Inversion.SecondSourceBlocks

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstChildWindows
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels
open InverseSecondSourceBlocks (dyadIndex dyadScale dyadScale_pos dyadIndex_bounds)
open ConcreteTraceCRT (eisEmbedding)

abbrev SourceIndex := Fin 6→ℕ

def sourceNorms {κ : Type*} (A₁ A₂ C R : κ→ℝ) (d h : κ→O) (x : κ) : Fin 6→ℝ :=
  ![A₁ x,A₂ x,C x,‖eisEmbedding (d x)‖^2,R x,‖eisEmbedding (h x)‖^2]

def sourceIndex {κ : Type*} (q : κ→Fin 6→ℝ) (x : κ) : SourceIndex := fun i=>dyadIndex (q x i)
def sourceCell {κ : Type*} [DecidableEq κ] (q : κ→Fin 6→ℝ) (S : Finset κ) (k : SourceIndex) :=
  S.filter (fun x=>sourceIndex q x=k)

def commonSelector {ι : Type*} [DecidableEq ι] (p : ι→O) (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι) : ℂ :=
  if dyadIndex (primeProductNorm p D)=l then selector D else 0

def rawScales (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) : Fin 9→ℝ :=
  ![dyadScale (k 0),dyadScale (k 1),dyadScale (k 2),dyadScale (k 3),dyadScale (k 4),
    dyadScale l,dyadScale (k 5),T₁,T₂]

lemma rawScales_pos (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) (h₁ : 0<T₁) (h₂ : 0<T₂) :
    ∀i,0<rawScales k l T₁ T₂ i := by
  intro i
  fin_cases i <;> first | exact dyadScale_pos _ | exact h₁ | exact h₂

lemma sourceNorms_ge_one {κ : Type*} (A₁ A₂ C R : κ→ℝ) (d h : κ→O) (x : κ)
    (hA₁ : 1≤A₁ x) (hA₂ : 1≤A₂ x) (hC : 1≤C x) (hR : 1≤R x)
    (hd : d x≠0) (hh : h x≠0) : ∀i,1≤sourceNorms A₁ A₂ C R d h x i := by
  intro i
  fin_cases i
  · exact hA₁
  · exact hA₂
  · exact hC
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hd
  · exact hR
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hh

lemma sourceCell_ratios {κ : Type*} [DecidableEq κ] (q : κ→Fin 6→ℝ) (S : Finset κ)
    (hq : ∀x∈S,∀i,1≤q x i) (k : SourceIndex) (x : κ) (hx : x∈sourceCell q S k) (i : Fin 6) :
    q x i/dyadScale (k i)∈Set.Icc 1 2 := by
  obtain ⟨hxs,hindex⟩ := Finset.mem_filter.mp hx
  have hh := dyadIndex_bounds (q x i) (hq x hxs i)
  have he : dyadIndex (q x i)=k i := congrFun hindex i
  rw [he] at hh
  exact ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hh.1),
    (div_le_iff₀ (dyadScale_pos _)).mpr hh.2.le⟩

theorem actual_original_cell_ratios {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (S : Finset κ) (selector C₁ C₂ : κ→Finset ι→ℂ)
    (A₁ A₂ C R : κ→ℝ) (d h : κ→O)
    (hq : ∀x∈S,∀i,1≤sourceNorms A₁ A₂ C R d h x i)
    (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) (x : κ)
    (hx : x∈sourceCell (sourceNorms A₁ A₂ C R d h) S k) (j : FirstCommonIndex ι)
    (hn : commonSelector p (selector x) l j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0) :
    ∀i,actualOuterRatios p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j (rawScales k l T₁ T₂) i∈Set.Icc 1 2 := by
  have hl : dyadIndex (primeProductNorm p j.2.1)=l := by
    by_contra he
    exact hn (by simp [commonSelector,he])
  have hh := dyadIndex_bounds _ (SecondPassArithmetic.primeProductNorm_ge_one p hp j.2.1)
  rw [hl] at hh
  have hD : primeProductNorm p j.2.1/dyadScale l∈Set.Icc 1 2 :=
    ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hh.1),
      (div_le_iff₀ (dyadScale_pos _)).mpr hh.2.le⟩
  intro i
  fin_cases i
  · exact sourceCell_ratios _ S hq k x hx 0
  · exact sourceCell_ratios _ S hq k x hx 1
  · exact sourceCell_ratios _ S hq k x hx 2
  · exact sourceCell_ratios _ S hq k x hx 3
  · exact sourceCell_ratios _ S hq k x hx 4
  · exact hD
  · exact sourceCell_ratios _ S hq k x hx 5
