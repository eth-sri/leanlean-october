/- The actual nine-dimensional compact complex sector and its projection.
No spanning or equality conclusion is assumed in a structure field. -/
module
public import Glennie.Native.CoordinateSimp
public import Glennie.Sector
public import Glennie.Hilbert
public import Glennie.Obligations
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section
namespace Glennie
noncomputable section

abbrev ComplexCoordinates := (ℝ × ℝ × ℝ) × (ℂ × ℂ × ℂ)

def complexAlbertLinear : ComplexCoordinates →ₗ[ℝ] Albert where
  toFun q := complexAlbert q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2.1 q.2.2.2
  map_add' x y := by
    ext <;> simp [complexAlbert, complexOct]
  map_smul' r x := by
    ext <;> simp [complexAlbert, complexOct, smul_eq_mul]

def complexCoordinatesLinear : Albert →ₗ[ℝ] ComplexCoordinates where
  toFun x := ((x.d0,x.d1,x.d2),
    (complexPart x.o01,complexPart x.o02,complexPart x.o12))
  map_add' x y := by
    ext <;> simp [complexPart]
    all_goals apply Complex.ext <;> simp
  map_smul' r x := by
    ext <;> simp [complexPart, smul_eq_mul]
    all_goals apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem complexCoordinates_albert (q : ComplexCoordinates) :
    complexCoordinatesLinear (complexAlbertLinear q) = q := rfl

theorem complexAlbert_coordinates (x : Albert) :
    complexAlbertLinear (complexCoordinatesLinear x) = complexProjection x := rfl

                                                                                    
             
                                                
                                                 

def complexSector : Submodule ℝ Albert := LinearMap.range complexAlbertLinear

                                                                        
                                                                   
                                                                                               
                                                         

theorem complexProjection_mem (x : Albert) : complexProjection x ∈ complexSector :=
  ⟨complexCoordinatesLinear x, complexAlbert_coordinates x⟩

theorem complexProjection_eq_self (x : Albert) (hx : InComplexSector x) :
    complexProjection x = x := by
  rcases hx with ⟨⟨h01j,h01k,h01s⟩,⟨h02j,h02k,h02s⟩,⟨h12j,h12k,h12s⟩⟩
  ext <;> simp [complexProjection, complexPart, complexOct,
    h01j,h01k,h01s,h02j,h02k,h02s,h12j,h12k,h12s]

theorem complexSector_mem_iff (x : Albert) : x ∈ complexSector ↔ InComplexSector x := by
  constructor
  · rintro ⟨q, rfl⟩
    simp [complexAlbertLinear, complexAlbert, complexOct, InComplexSector, OctInComplex]
  · intro hx
    rw [← complexProjection_eq_self x hx]
    exact complexProjection_mem x

theorem complexSector_jordan (x y : Albert) (hx : InComplexSector x)
    (hy : InComplexSector y) : InComplexSector (jordan x y) := by
  rw [← complexProjection_eq_self x hx, ← complexProjection_eq_self y hy]
  simp [albert_coords, InComplexSector, OctInComplex, complexProjection, complexPart, complexOct]

                                                                        
                                                                    
                                                        
                                        
                               
                     
                                              
                                                       
            



                                                                        
                                                                               
                                                                 
                           
                                 
                                                 
                                                     
                                                                   
                               
                     
              
                                      
            
           
                                                   

end
end Glennie
