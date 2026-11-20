/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/PathFractions.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Adapted to the Lean module system and simplified for this proof.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.PathWords

@[expose] public section

namespace OAI.EuclideanRamsey

noncomputable section

structure NormalBound (G : Type*) [Group G] where
  Holds : ℝ → G → Prop
  one : Holds 0 1
  weaken : ∀ {a b x}, Holds a x → a ≤ b → Holds b x
  mul : ∀ {a b x y}, Holds a x → Holds b y → Holds (a+b) (x*y)
  inv : ∀ {a x}, Holds a x → Holds a x⁻¹
  conj : ∀ {a x}, Holds a x → ∀ g, Holds a (g*x*g⁻¹)

variable {ι : Type*} {a : ι → Hilbert}

/-- A fraction whose numerator and denominator must agree with the endpoint on `s`. -/
def PartialBound (a : ι → Hilbert) (s : Finset ι) (z : ι → LetterGroup) (c : ℝ) : Prop :=
  ∃ u v m n, Path a u m ∧ Path a v n ∧ (∀ i ∈ s, z i = u i * (v i)⁻¹) ∧ m+n ≤ c

def FractionOn (a : ι → Hilbert) (s : Finset ι) (z : ι → LetterGroup) : Prop := ∃ c, PartialBound a s z c

namespace PartialBound
variable {s : Finset ι} {z t : ι → LetterGroup} {b c : ℝ}

lemma mono (h : PartialBound a s z b) (hc : b ≤ c) : PartialBound a s z c := by
  obtain ⟨u,v,m,n,hu,hv,hz,ha⟩ := h
  exact ⟨u,v,m,n,hu,hv,hz,ha.trans hc⟩

lemma one : PartialBound a s 1 0 := ⟨1,1,0,0,Path.diag 1,Path.diag 1,by simp,by simp⟩

lemma inv (h : PartialBound a s z c) : PartialBound a s z⁻¹ c := by
  obtain ⟨u,v,m,n,hu,hv,hz,hc⟩ := h
  exact ⟨v,u,n,m,hv,hu,fun i hi => by simp [hz i hi], by linarith⟩

lemma conj (h : PartialBound a s z c) (g : LetterGroup) :
    PartialBound a s (fun i => g*z i*g⁻¹) c := by
  obtain ⟨u,v,m,n,hu,hv,hz,hc⟩ := h
  refine ⟨_,_,m,n,hu.diag_mul g,hv.diag_mul g,fun i hi => ?_,hc⟩
  simp only [hz i hi]
  group

private lemma mul_aux {e : ℝ} (hz : PartialBound a s z b) (ht : PartialBound a s t c)
    (h : ∀ v n, Path a v n → n ≤ b → ∃ w r, Path a w r ∧ r ≤ e ∧ ∀ i ∈ s, Commute (v i*w i) (t i)) :
    PartialBound a s (z*t) (b+c+2*e) := by
  obtain ⟨u,v,m,n,hu,hv,hz,hm⟩ := hz
  obtain ⟨p,q,k,l,hp,hq,ht,hk⟩ := ht
  obtain ⟨w,r,hw,hr,he⟩ := h v n hv (by linarith [hu.nonneg])
  refine ⟨u*w*p,v*w*q,m+r+k,n+r+l,(hu.mul hw).mul hp,(hv.mul hw).mul hq,fun i hi => ?_,by linarith⟩
  simp only [Pi.mul_apply,hz i hi]
  calc
    _ = (u i*w i)*(v i*w i)⁻¹*t i := by group
    _ = _ := by rw [mul_assoc,(he i hi).inv_left.eq,ht i hi]; group

lemma mul_single [DecidableEq ι] {i : ι} {g : LetterGroup}
    (hz : PartialBound a s z b) (ht : PartialBound a s (Pi.mulSingle i g) c) :
    PartialBound a s (z*Pi.mulSingle i g) (b+c) := by
  simpa using hz.mul_aux (e:=0) ht fun v _ _ _ => ⟨_,0,Path.diag (v i)⁻¹,le_rfl,fun j _ => by
    by_cases h : j=i <;> simp [h]⟩

end PartialBound

lemma FractionOn.congr {s : Finset ι} {z t : ι → LetterGroup} (h : FractionOn a s z)
    (he : ∀ i ∈ s, t i = z i) : FractionOn a s t := by
  obtain ⟨c,u,v,m,n,hu,hv,hz,hc⟩ := h
  exact ⟨c,u,v,m,n,hu,hv,fun i hi => (he i hi).trans (hz i hi),hc⟩

lemma FractionOn.inv {s : Finset ι} {z : ι → LetterGroup} (h : FractionOn a s z) : FractionOn a s z⁻¹ :=
  h.imp fun _ => PartialBound.inv

lemma FractionOn.of_word {s : Finset ι} {z u : ι → LetterGroup} {r : ℝ} (hu : Path a u r)
    (h : ∀ i ∈ s, z i = u i) : FractionOn a s z :=
  ⟨r,u,1,r,0,hu,Path.diag 1,by simpa using h,by simp⟩

lemma FractionOn.mul_pair {s : Finset ι} {z t : ι → LetterGroup} (hz : FractionOn a s z) (ht : FractionOn a s t) {j k : ι}
    (h : ∀ i ∈ s, i≠j → i≠k → t i=1) : FractionOn a s (z*t) := by
  obtain ⟨b,hb⟩ := hz
  obtain ⟨c,hc⟩ := ht
  refine ⟨_,hb.mul_aux (e:=b) hc fun v n hv hn => ?_⟩
  obtain ⟨u,hu,hj,hk⟩ := hv.pair_inverse j k
  refine ⟨u,n,hu,hn,fun i hi => ?_⟩
  by_cases h₁ : i=j
  · subst i; simp [hj]
  by_cases h₂ : i=k
  · subst i; simp [hk]
  aesop

variable [DecidableEq ι]

lemma conj_mulSingle (i : ι) (g h : LetterGroup) :
    (fun j => g*(Pi.mulSingle i h : ι → LetterGroup) j*g⁻¹) = Pi.mulSingle i (g*h*g⁻¹) := by
  ext j
  by_cases hj : j=i <;> simp [hj]

def normalBound (a : ι → Hilbert) (s : Finset ι) (i : ι) : NormalBound LetterGroup where
  Holds B g := PartialBound a s (Pi.mulSingle i g) B
  one := by simpa using PartialBound.one (a:=a) (s:=s)
  weaken := PartialBound.mono
  inv h := by simpa only [Pi.mulSingle_inv] using h.inv
  conj h k := by simpa only [conj_mulSingle] using h.conj k
  mul h h' := by rw [Pi.mulSingle_mul]; exact h.mul_single h'

def NormalBound.covered {G : Type*} [Group G] (c : NormalBound G) : Subgroup G where
  carrier := {g | ∃ B, c.Holds B g}
  one_mem' := ⟨0,c.one⟩
  inv_mem' := fun ⟨_,h⟩ => ⟨_,c.inv h⟩
  mul_mem' := fun ⟨_,h⟩ ⟨_,h'⟩ => ⟨_,c.mul h h'⟩

instance {G : Type*} [Group G] (c : NormalBound G) : c.covered.Normal :=
  ⟨fun _ ⟨_,h⟩ k => ⟨_,c.conj h k⟩⟩

abbrev Correctable (a : ι → Hilbert) (s : Finset ι) (i : ι) : Subgroup LetterGroup :=
  (normalBound a s i).covered

end
end OAI.EuclideanRamsey
