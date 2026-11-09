module

public import Erdos272.Resources.Unit240Family218
public import Erdos272.Arithmetic.Unit240RowsChecked218

@[expose] public section

namespace JSP233.Unit240Aggregate218
open StarCompletion APGeometry
open SevenFamily208 UnitNearAggregate208 Unit240Rows218 Unit240Family218
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def Fee : ℝ := 21831250792

theorem facts (k : ℕ) (hk : k<7) : Facts k := by
  interval_cases k
  · exact Unit240RowsChecked218.facts0
  · exact Unit240RowsChecked218.facts1
  · exact Unit240RowsChecked218.facts2
  · exact Unit240RowsChecked218.facts3
  · exact Unit240RowsChecked218.facts4
  · exact Unit240RowsChecked218.facts5
  · exact Unit240RowsChecked218.facts6

theorem psi0 : Psi 0=0 := psi_zero
theorem psi1 : Psi 1=38010 := by
  change (SourceCertified208.floorAt row242 23 : ℝ)=38010
  norm_num [show SourceCertified208.floorAt row242 23=38010 from by decide +kernel]
theorem psi2 : Psi 2=138256 := by
  change (SourceCertified208.floorAt row242 46 : ℝ)=138256
  norm_num [show SourceCertified208.floorAt row242 46=138256 from by decide +kernel]
theorem psi3 : Psi 3=285674 := by
  change (SourceCertified208.floorAt row242 69 : ℝ)=285674
  norm_num [show SourceCertified208.floorAt row242 69=285674 from by decide +kernel]
theorem psi4 : Psi 4=466724 := by
  change (SourceCertified208.floorAt row242 92 : ℝ)=466724
  norm_num [show SourceCertified208.floorAt row242 92=466724 from by decide +kernel]
theorem psi5 : Psi 5=671172 := by
  change (SourceCertified208.floorAt row242 115 : ℝ)=671172
  norm_num [show SourceCertified208.floorAt row242 115=671172 from by decide +kernel]
theorem psi6 : Psi 6=889318 := by
  change (SourceCertified208.floorAt row242 138 : ℝ)=889318
  norm_num [show SourceCertified208.floorAt row242 138=889318 from by decide +kernel]
theorem psi7 : Psi 7=1027396 := by
  change (SourceCertified208.floorAt row242 150 : ℝ)=1027396
  norm_num [show SourceCertified208.floorAt row242 150=1027396 from by decide +kernel]

theorem weighted_upper : 6*G*(∑k∈Finset.range 7,(Psi (k+1)-Psi k)*Upper k)≤Fee := by
  norm_num [Finset.sum_range_succ,psi0,psi1,psi2,psi3,psi4,psi5,psi6,psi7,
    G,Upper,Fee,row,row0,row1,row2,row3,row4,row5,row6,
    expected,expected0,expected1,expected2,expected3,expected4,expected5,expected6,
    units,units0,units1,units2,units3,units4,units5,units6,
    light,light0,light1,light2,light3,light4,light5,light6]

theorem actual_paid_pad {A : Finset (Finset ℤ)}
    (hlegal : Legal (Ground 659912) A) (hbad : ∀S∈A,¬IsAP S)
    (hsize : ∀S∈A,240≤S.card) (hsparse : ∀S∈A,11*S.card≤659912) :
    UnitNearObligation 659912 A G 0 0 Fee := by
  refine ⟨Psi,7,psi_mono,psi_zero,reciprocal,?_⟩
  have hs := Finset.sum_le_sum (s := Finset.range 7) (fun k hk=>
    mul_le_mul_of_nonneg_left
      (actual_upper k (Finset.mem_range.mp hk) hlegal hbad hsize hsparse
        (facts k (Finset.mem_range.mp hk)))
      (sub_nonneg.mpr (psi_mono (Nat.le_succ k))))
  have hb := (mul_le_mul_of_nonneg_left hs (show (0 : ℝ)≤6*G by norm_num [G])).trans weighted_upper
  simpa only [zero_mul,zero_add] using hb

#print axioms facts
#print axioms psi0
#print axioms psi1
#print axioms psi2
#print axioms psi3
#print axioms psi4
#print axioms psi5
#print axioms psi6
#print axioms psi7
#print axioms weighted_upper
#print axioms actual_paid_pad
end
end JSP233.Unit240Aggregate218
