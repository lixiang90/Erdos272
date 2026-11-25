module

public import Erdos272.Arithmetic.N82427.RowLightData82427
public import Erdos272.Arithmetic.N82427.ClassChecks82427G00
public import Erdos272.Arithmetic.N82427.ClassChecks82427G02
public import Erdos272.Arithmetic.N82427.ClassChecks82427G03
public import Erdos272.Arithmetic.N82427.ClassChecks82427G05
public import Erdos272.Arithmetic.N82427.ClassChecks82427G08
public import Erdos272.Arithmetic.N82427.ClassChecks82427G10
public import Erdos272.Arithmetic.N82427.ClassChecks82427G11
public import Erdos272.Arithmetic.N82427.ClassChecks82427G12
public import Erdos272.Arithmetic.N82427.ClassChecks82427G13

@[expose] public section

namespace JSP233.RowLightCertificates82427G00
open RowLightSlope82427 PhaseSlope82427 PhaseRampSlope82427 ActualCleanupEval208 ClassCount158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxErrors 1

attribute [local irreducible] ClassFastNumeric82427.check

theorem classes00 (b : CrossBandCredit208.Band) (t : Term) (ht : t ∈ terms 0 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p ((row 0).low/(t.q*(t.q+1))) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,85,5⟩, ⟨2,169,1⟩, ⟨3,85,1⟩, ⟨11,85,1⟩} : Finset Term) at ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G00.checked0009⟩
    · exact ⟨by decide, ClassChecks82427G00.checked0000⟩
    · exact ⟨by decide, ClassChecks82427G03.checked0202⟩
    · exact ⟨by decide, ClassChecks82427G11.checked0719⟩
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
#print axioms classes00

theorem ramps00 (b : CrossBandCredit208.Band) (t : RampTerm) (ht : t ∈ ramps 0 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p (RampLength (row 0).low (At (row 0) (length (k:=0) (by decide)) b) t.p) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,272⟩, ⟨3,91⟩, ⟨5,36⟩, ⟨7,20⟩, ⟨11,123⟩} : Finset RampTerm) at ht
    change t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧
      ClassFastNumeric82427.check t.p (RampLength 82427 (⟨87,2,119,84,85,85,85,85⟩ : CleanupEval208.Band) t.p) t.count=true
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G02.checked0105⟩
    · exact ⟨by decide, ClassChecks82427G05.checked0296⟩
    · exact ⟨by decide, ClassChecks82427G08.checked0469⟩
    · exact ⟨by decide, ClassChecks82427G10.checked0626⟩
    · exact ⟨by decide, ClassChecks82427G13.checked0807⟩
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
#print axioms ramps00

theorem classes01 (b : CrossBandCredit208.Band) (t : Term) (ht : t ∈ terms 1 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p ((row 1).low/(t.q*(t.q+1))) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,84,5⟩, ⟨2,166,1⟩, ⟨3,84,1⟩, ⟨11,84,1⟩} : Finset Term) at ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G00.checked0009⟩
    · exact ⟨by decide, ClassChecks82427G00.checked0000⟩
    · exact ⟨by decide, ClassChecks82427G03.checked0202⟩
    · exact ⟨by decide, ClassChecks82427G11.checked0719⟩
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
#print axioms classes01

theorem ramps01 (b : CrossBandCredit208.Band) (t : RampTerm) (ht : t ∈ ramps 1 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p (RampLength (row 1).low (At (row 1) (length (k:=1) (by decide)) b) t.p) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,299⟩, ⟨3,100⟩, ⟨5,40⟩, ⟨7,21⟩, ⟨11,136⟩} : Finset RampTerm) at ht
    change t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧
      ClassFastNumeric82427.check t.p (RampLength 82427 (⟨87,3,145,82,83,84,84,84⟩ : CleanupEval208.Band) t.p) t.count=true
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G02.checked0112⟩
    · exact ⟨by decide, ClassChecks82427G05.checked0303⟩
    · exact ⟨by decide, ClassChecks82427G08.checked0477⟩
    · exact ⟨by decide, ClassChecks82427G10.checked0633⟩
    · exact ⟨by decide, ClassChecks82427G13.checked0816⟩
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
#print axioms ramps01

theorem classes02 (b : CrossBandCredit208.Band) (t : Term) (ht : t ∈ terms 2 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p ((row 2).low/(t.q*(t.q+1))) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,83,5⟩, ⟨2,163,1⟩, ⟨3,83,1⟩, ⟨11,83,1⟩} : Finset Term) at ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G00.checked0009⟩
    · exact ⟨by decide, ClassChecks82427G00.checked0001⟩
    · exact ⟨by decide, ClassChecks82427G03.checked0202⟩
    · exact ⟨by decide, ClassChecks82427G11.checked0719⟩
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
#print axioms classes02

theorem ramps02 (b : CrossBandCredit208.Band) (t : RampTerm) (ht : t ∈ ramps 2 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p (RampLength (row 2).low (At (row 2) (length (k:=2) (by decide)) b) t.p) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,316⟩, ⟨3,106⟩, ⟨5,42⟩, ⟨7,24⟩, ⟨11,143⟩} : Finset RampTerm) at ht
    change t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧
      ClassFastNumeric82427.check t.p (RampLength 82427 (⟨87,4,163,80,82,83,83,83⟩ : CleanupEval208.Band) t.p) t.count=true
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G02.checked0115⟩
    · exact ⟨by decide, ClassChecks82427G05.checked0306⟩
    · exact ⟨by decide, ClassChecks82427G08.checked0480⟩
    · exact ⟨by decide, ClassChecks82427G10.checked0636⟩
    · exact ⟨by decide, ClassChecks82427G13.checked0819⟩
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
#print axioms ramps02

theorem classes03 (b : CrossBandCredit208.Band) (t : Term) (ht : t ∈ terms 3 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p ((row 3).low/(t.q*(t.q+1))) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,82,6⟩, ⟨2,160,1⟩, ⟨3,82,2⟩, ⟨11,82,1⟩} : Finset Term) at ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G00.checked0010⟩
    · exact ⟨by decide, ClassChecks82427G00.checked0001⟩
    · exact ⟨by decide, ClassChecks82427G03.checked0203⟩
    · exact ⟨by decide, ClassChecks82427G12.checked0720⟩
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset Term) at ht
    exact (Finset.notMem_empty t ht).elim
#print axioms classes03

theorem ramps03 (b : CrossBandCredit208.Band) (t : RampTerm) (ht : t ∈ ramps 3 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p (RampLength (row 3).low (At (row 3) (length (k:=3) (by decide)) b) t.p) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,333⟩, ⟨3,111⟩, ⟨5,44⟩, ⟨7,24⟩, ⟨11,150⟩} : Finset RampTerm) at ht
    change t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧
      ClassFastNumeric82427.check t.p (RampLength 82427 (⟨87,5,181,78,80,81,82,82⟩ : CleanupEval208.Band) t.p) t.count=true
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G02.checked0117⟩
    · exact ⟨by decide, ClassChecks82427G05.checked0308⟩
    · exact ⟨by decide, ClassChecks82427G08.checked0482⟩
    · exact ⟨by decide, ClassChecks82427G10.checked0638⟩
    · exact ⟨by decide, ClassChecks82427G13.checked0821⟩
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
  · change t ∈ (∅ : Finset RampTerm) at ht
    exact (Finset.notMem_empty t ht).elim
#print axioms ramps03

end
end JSP233.RowLightCertificates82427G00
