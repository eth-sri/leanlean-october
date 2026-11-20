module
public import LaterPairs.Native.HuxleyProfileGeometry.Part02

@[expose] public section

namespace TaoTrudgianYang2025.HuxleyRationalPhase
open scoped Classical BigOperators
open Set

/-- At fixed parameter and curvature, all the centers coincide. The block geometry
then leaves at most three integer indices, with two labels for each. -/
theorem physical_grid_level_card (S : Finset ((ℝ × ℤ) × Fin 2))
    (z : ℝ → ℤ → ℝ) (A : ℝ → ℤ → ℕ) (Z : ℝ → ℤ) {N : ℕ} (hN : 0<N)
    {M q : ℝ} (curvature : ℝ → ℝ → ℝ)
    (hpoints : ∀ ip∈S, z ip.1.1 ip.1.2∈Icc M (2*M))
    (hgrid : ∀ ip∈S, N≤A ip.1.1 ip.1.2 ∧ A ip.1.1 ip.1.2≤3*N ∧
      round (z ip.1.1 ip.1.2)+(A ip.1.1 ip.1.2:ℤ)=Z ip.1.1+(N:ℤ)*ip.1.2+2*(N:ℤ))
    (hlevel : ∀ ip∈S, curvature ip.1.1 (z ip.1.1 ip.1.2)=q)
    (hinj : ∀ y∈S.image (fun ip => ip.1.1), InjOn (curvature y) (Icc M (2*M))) :
    (S.card:ℝ) ≤ 6*((S.image (fun ip => ip.1.1)).card:ℝ) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  suffices hcard : S.card ≤ 6*(S.image (fun ip => ip.1.1)).card by exact_mod_cast hcard
  apply Finset.card_le_mul_card_image S 6
  intro y hy
  obtain ⟨j,hj,hjy⟩ := Finset.mem_image.mp hy
  let m : ℝ := round (z j.1.1 j.1.2)
  obtain ⟨I,hI,_,hIhigh⟩ := physical_grid_interval_card (Z:=(Z y:ℝ))
    (x:=m-(N:ℝ)) (z:=m+(N:ℝ)) hNp (by linarith only [hNp])
  have hIcard : I.card≤3 := by
    have h : (I.card:ℝ)≤3 := hIhigh.trans_eq (by field_simp; ring)
    exact_mod_cast h
  let E := S.filter (fun ip => ip.1.1=y)
  have hfiber : E.card≤(I ×ˢ (Finset.univ : Finset (Fin 2))).card := by
    apply Finset.card_le_card_of_injOn (fun ip => (ip.1.2,ip.2))
    · intro ip hip
      refine Finset.mem_product.mpr ⟨(hI _).mpr ?_,Finset.mem_univ _⟩
      obtain ⟨hS,hiy⟩ := Finset.mem_filter.mp hip
      have hs : z ip.1.1 ip.1.2=z j.1.1 j.1.2 := by
        have hi : curvature y (z ip.1.1 ip.1.2)=q := by rw [←hiy,hlevel ip hS]
        have hj' : curvature y (z j.1.1 j.1.2)=q := by rw [←hjy,hlevel j hj]
        exact hinj y hy (hpoints ip hS) (hpoints j hj) (hi.trans hj'.symm)
      have hg := hgrid ip hS
      have hlo : (N:ℝ) ≤ A ip.1.1 ip.1.2 := by exact_mod_cast hg.1
      have hhi : (A ip.1.1 ip.1.2:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hg.2.1
      have he : (round (z ip.1.1 ip.1.2):ℝ)+(A ip.1.1 ip.1.2:ℝ)=
          (Z ip.1.1:ℝ)+(N:ℝ)*ip.1.2+2*(N:ℝ) := by exact_mod_cast hg.2.2
      rw [hs,hiy] at he
      rw [hiy] at hlo hhi
      change m+_=_ at he
      constructor <;> nlinarith only [he,hlo,hhi]
    · intro ip hip jp hjp he
      exact Prod.ext (Prod.ext ((Finset.mem_filter.mp hip).2.trans (Finset.mem_filter.mp hjp).2.symm)
        (congrArg (fun p : ℤ × Fin 2 => p.1) he)) (congrArg (fun p : ℤ × Fin 2 => p.2) he)
  simp only [Finset.card_product,Finset.card_univ,Fintype.card_fin] at hfiber
  change E.card ≤ 6
  omega

/-- Sum the fiber counts for pairs with a fixed matrix and first point. -/
theorem matrix_pair_card_of_fixed_left {α : Type*} [DecidableEq α] (P : Finset (α×α))
    (mat : α×α → Fin 4 → ℤ) (h μ : α → ℝ) {Δ B : ℝ}
    (hmap : ∀ ij∈P, ((mat ij 0:ℝ)*h ij.1+mat ij 1)/((mat ij 2:ℝ)*h ij.1+mat ij 3)=h ij.2)
    (hthird : ∀ ij∈P, |μ ij.2/μ ij.1*((mat ij 2:ℝ)*h ij.1+mat ij 3)^3-1|≤Δ)
    (hcount : ∀ ij∈P, ∀ S : Finset α, let t := (mat ij 2:ℝ)*h ij.1+mat ij 3
      (∀ k∈S,(ij.1,k)∈P) →
      (∀ k∈S,h k=((mat ij 0:ℝ)*h ij.1+mat ij 1)/t) →
      (∀ k∈S,|μ k/μ ij.1*t^3-1|≤Δ) → (S.card:ℝ)≤B) :
    (P.card:ℝ)≤B*((P.image (fun ij => (mat ij,ij.1))).card:ℝ) := by
  let key := fun ij => (mat ij,ij.1)
  have hfiber k (hk : k∈P.image key) : ((P.filter (fun ij => key ij=k)).card:ℝ)≤B := by
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hk
    let E := P.filter (fun a => key a=key ij)
    let S := E.image Prod.snd
    have hmem a (ha : a∈E) : a∈P ∧ mat a=mat ij ∧ a.1=ij.1 := by
      obtain ⟨hP,he⟩ := Finset.mem_filter.mp ha
      exact ⟨hP,congrArg Prod.fst he,congrArg Prod.snd he⟩
    have h1 k (hk : k∈S) : (ij.1,k)∈P := by
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hk
      rw [←(hmem a ha).2.2,Prod.eta]
      exact (hmem a ha).1
    have hB := hcount ij hij S h1 (by
      intro k hk
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hk
      simpa only [(hmem a ha).2.1,(hmem a ha).2.2] using (hmap a (hmem a ha).1).symm) (by
      intro k hk
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hk
      simpa only [(hmem a ha).2.1,(hmem a ha).2.2] using hthird a (hmem a ha).1)
    rwa [Finset.card_image_of_injOn (fun a ha b hb h =>
      Prod.ext ((hmem a ha).2.2.trans (hmem b hb).2.2.symm) h)] at hB
  have he : (P.card:ℝ)=∑ k∈P.image key,((P.filter (fun ij => key ij=k)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image key P
  rw [he]
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using Finset.sum_le_sum hfiber

end TaoTrudgianYang2025.HuxleyRationalPhase
