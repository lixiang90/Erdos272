module

public import Erdos272.Arithmetic.N291012.RowGeometryCertificates291012G0
public import Erdos272.Arithmetic.N291012.RowGeometryCertificates291012G1
public import Erdos272.Arithmetic.N291012.RowGeometryCertificates291012G2
public import Erdos272.Arithmetic.N291012.RowGeometryCertificates291012G3
public import Erdos272.Arithmetic.N291012.RowGeometryCertificates291012G4
public import Erdos272.Arithmetic.N291012.RowGeometryCertificates291012G5
public import Erdos272.Arithmetic.N291012.RowGeometryCertificates291012G6

@[expose] public section

namespace JSP233.RowGeometry291012
open StarCompletion CleanupRows291012 UnitRecipeStatic208 RowStatic291012
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem parameters {k : ℕ} (hk : k < 91) : Static (CleanupRows291012.data k) := by
  interval_cases k
  · exact RowGeometryCertificates291012G0.static00
  · exact RowGeometryCertificates291012G0.static01
  · exact RowGeometryCertificates291012G0.static02
  · exact RowGeometryCertificates291012G0.static03
  · exact RowGeometryCertificates291012G0.static04
  · exact RowGeometryCertificates291012G0.static05
  · exact RowGeometryCertificates291012G0.static06
  · exact RowGeometryCertificates291012G0.static07
  · exact RowGeometryCertificates291012G0.static08
  · exact RowGeometryCertificates291012G0.static09
  · exact RowGeometryCertificates291012G0.static10
  · exact RowGeometryCertificates291012G0.static11
  · exact RowGeometryCertificates291012G0.static12
  · exact RowGeometryCertificates291012G1.static13
  · exact RowGeometryCertificates291012G1.static14
  · exact RowGeometryCertificates291012G1.static15
  · exact RowGeometryCertificates291012G1.static16
  · exact RowGeometryCertificates291012G1.static17
  · exact RowGeometryCertificates291012G1.static18
  · exact RowGeometryCertificates291012G1.static19
  · exact RowGeometryCertificates291012G1.static20
  · exact RowGeometryCertificates291012G1.static21
  · exact RowGeometryCertificates291012G1.static22
  · exact RowGeometryCertificates291012G1.static23
  · exact RowGeometryCertificates291012G1.static24
  · exact RowGeometryCertificates291012G1.static25
  · exact RowGeometryCertificates291012G2.static26
  · exact RowGeometryCertificates291012G2.static27
  · exact RowGeometryCertificates291012G2.static28
  · exact RowGeometryCertificates291012G2.static29
  · exact RowGeometryCertificates291012G2.static30
  · exact RowGeometryCertificates291012G2.static31
  · exact RowGeometryCertificates291012G2.static32
  · exact RowGeometryCertificates291012G2.static33
  · exact RowGeometryCertificates291012G2.static34
  · exact RowGeometryCertificates291012G2.static35
  · exact RowGeometryCertificates291012G2.static36
  · exact RowGeometryCertificates291012G2.static37
  · exact RowGeometryCertificates291012G2.static38
  · exact RowGeometryCertificates291012G3.static39
  · exact RowGeometryCertificates291012G3.static40
  · exact RowGeometryCertificates291012G3.static41
  · exact RowGeometryCertificates291012G3.static42
  · exact RowGeometryCertificates291012G3.static43
  · exact RowGeometryCertificates291012G3.static44
  · exact RowGeometryCertificates291012G3.static45
  · exact RowGeometryCertificates291012G3.static46
  · exact RowGeometryCertificates291012G3.static47
  · exact RowGeometryCertificates291012G3.static48
  · exact RowGeometryCertificates291012G3.static49
  · exact RowGeometryCertificates291012G3.static50
  · exact RowGeometryCertificates291012G3.static51
  · exact RowGeometryCertificates291012G4.static52
  · exact RowGeometryCertificates291012G4.static53
  · exact RowGeometryCertificates291012G4.static54
  · exact RowGeometryCertificates291012G4.static55
  · exact RowGeometryCertificates291012G4.static56
  · exact RowGeometryCertificates291012G4.static57
  · exact RowGeometryCertificates291012G4.static58
  · exact RowGeometryCertificates291012G4.static59
  · exact RowGeometryCertificates291012G4.static60
  · exact RowGeometryCertificates291012G4.static61
  · exact RowGeometryCertificates291012G4.static62
  · exact RowGeometryCertificates291012G4.static63
  · exact RowGeometryCertificates291012G4.static64
  · exact RowGeometryCertificates291012G5.static65
  · exact RowGeometryCertificates291012G5.static66
  · exact RowGeometryCertificates291012G5.static67
  · exact RowGeometryCertificates291012G5.static68
  · exact RowGeometryCertificates291012G5.static69
  · exact RowGeometryCertificates291012G5.static70
  · exact RowGeometryCertificates291012G5.static71
  · exact RowGeometryCertificates291012G5.static72
  · exact RowGeometryCertificates291012G5.static73
  · exact RowGeometryCertificates291012G5.static74
  · exact RowGeometryCertificates291012G5.static75
  · exact RowGeometryCertificates291012G5.static76
  · exact RowGeometryCertificates291012G5.static77
  · exact RowGeometryCertificates291012G6.static78
  · exact RowGeometryCertificates291012G6.static79
  · exact RowGeometryCertificates291012G6.static80
  · exact RowGeometryCertificates291012G6.static81
  · exact RowGeometryCertificates291012G6.static82
  · exact RowGeometryCertificates291012G6.static83
  · exact RowGeometryCertificates291012G6.static84
  · exact RowGeometryCertificates291012G6.static85
  · exact RowGeometryCertificates291012G6.static86
  · exact RowGeometryCertificates291012G6.static87
  · exact RowGeometryCertificates291012G6.static88
  · exact RowGeometryCertificates291012G6.static89
  · exact RowGeometryCertificates291012G6.static90

theorem cover {v : Data} (h : Static v) {N n : ℕ}
    (hN : N ≤ v.row.high) (hm : v.memberFloor ≤ n) (hs : 12*n ≤ N) :
    ∃ b : Fin 7, (evalData v.row b).T ≤ n ∧ n < (evalData v.row b).U := by
  have hfirst := h.first
  have hlast := h.last
  have h01 := h.joins 0
  have h12 := h.joins 1
  have h23 := h.joins 2
  have h34 := h.joins 3
  have h45 := h.joins 4
  have h56 := h.joins 5
  change (evalData v.row 0).U = (evalData v.row 1).T at h01
  change (evalData v.row 1).U = (evalData v.row 2).T at h12
  change (evalData v.row 2).U = (evalData v.row 3).T at h23
  change (evalData v.row 3).U = (evalData v.row 4).T at h34
  change (evalData v.row 4).U = (evalData v.row 5).T at h45
  change (evalData v.row 5).U = (evalData v.row 6).T at h56
  have htop : n < (evalData v.row 6).U := by omega
  by_cases h0 : n < (evalData v.row 0).U
  · exact ⟨0, by omega, h0⟩
  by_cases h1 : n < (evalData v.row 1).U
  · exact ⟨1, by omega, h1⟩
  by_cases h2 : n < (evalData v.row 2).U
  · exact ⟨2, by omega, h2⟩
  by_cases h3 : n < (evalData v.row 3).U
  · exact ⟨3, by omega, h3⟩
  by_cases h4 : n < (evalData v.row 4).U
  · exact ⟨4, by omega, h4⟩
  by_cases h5 : n < (evalData v.row 5).U
  · exact ⟨5, by omega, h5⟩
  exact ⟨6, by omega, htop⟩

#print axioms parameters
#print axioms cover
end
end JSP233.RowGeometry291012
