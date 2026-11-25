module

public import Erdos272.Arithmetic.N82427.RowLightData82427
public import Erdos272.Arithmetic.N82427.ClassChecks82427G00
public import Erdos272.Arithmetic.N82427.ClassChecks82427G01
public import Erdos272.Arithmetic.N82427.ClassChecks82427G02
public import Erdos272.Arithmetic.N82427.ClassChecks82427G03
public import Erdos272.Arithmetic.N82427.ClassChecks82427G04
public import Erdos272.Arithmetic.N82427.ClassChecks82427G05
public import Erdos272.Arithmetic.N82427.ClassChecks82427G08
public import Erdos272.Arithmetic.N82427.ClassChecks82427G10
public import Erdos272.Arithmetic.N82427.ClassChecks82427G11
public import Erdos272.Arithmetic.N82427.ClassChecks82427G12
public import Erdos272.Arithmetic.N82427.ClassChecks82427G13

@[expose] public section

namespace JSP233.RowLightCertificates82427G02
open RowLightSlope82427 PhaseSlope82427 PhaseRampSlope82427 ActualCleanupEval208 ClassCount158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxErrors 1

attribute [local irreducible] ClassFastNumeric82427.check

theorem classes08 (b : CrossBandCredit208.Band) (t : Term) (ht : t ∈ terms 8 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p ((row 8).low/(t.q*(t.q+1))) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,72,7⟩, ⟨2,130,2⟩, ⟨2,188,1⟩, ⟨3,72,2⟩, ⟨11,72,1⟩} : Finset Term) at ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G00.checked0013⟩
    · exact ⟨by decide, ClassChecks82427G00.checked0002⟩
    · exact ⟨by decide, ClassChecks82427G00.checked0000⟩
    · exact ⟨by decide, ClassChecks82427G03.checked0206⟩
    · exact ⟨by decide, ClassChecks82427G12.checked0723⟩
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
#print axioms classes08

theorem ramps08 (b : CrossBandCredit208.Band) (t : RampTerm) (ht : t ∈ ramps 8 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p (RampLength (row 8).low (At (row 8) (length (k:=8) (by decide)) b) t.p) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,434⟩, ⟨3,145⟩, ⟨5,58⟩, ⟨7,32⟩, ⟨11,197⟩} : Finset RampTerm) at ht
    change t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧
      ClassFastNumeric82427.check t.p (RampLength 82427 (⟨87,15,276,58,65,69,70,71⟩ : CleanupEval208.Band) t.p) t.count=true
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G02.checked0130⟩
    · exact ⟨by decide, ClassChecks82427G05.checked0321⟩
    · exact ⟨by decide, ClassChecks82427G08.checked0495⟩
    · exact ⟨by decide, ClassChecks82427G10.checked0651⟩
    · exact ⟨by decide, ClassChecks82427G13.checked0834⟩
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
#print axioms ramps08

theorem classes09 (b : CrossBandCredit208.Band) (t : Term) (ht : t ∈ terms 9 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p ((row 9).low/(t.q*(t.q+1))) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,70,8⟩, ⟨2,124,2⟩, ⟨2,178,1⟩, ⟨3,70,2⟩, ⟨11,70,1⟩} : Finset Term) at ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G00.checked0014⟩
    · exact ⟨by decide, ClassChecks82427G00.checked0003⟩
    · exact ⟨by decide, ClassChecks82427G00.checked0000⟩
    · exact ⟨by decide, ClassChecks82427G03.checked0207⟩
    · exact ⟨by decide, ClassChecks82427G12.checked0724⟩
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
#print axioms classes09

theorem ramps09 (b : CrossBandCredit208.Band) (t : RampTerm) (ht : t ∈ ramps 9 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p (RampLength (row 9).low (At (row 9) (length (k:=9) (by decide)) b) t.p) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,451⟩, ⟨3,151⟩, ⟨5,60⟩, ⟨7,34⟩, ⟨11,205⟩} : Finset RampTerm) at ht
    change t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧
      ClassFastNumeric82427.check t.p (RampLength 82427 (⟨87,17,284,54,62,66,68,69⟩ : CleanupEval208.Band) t.p) t.count=true
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G02.checked0133⟩
    · exact ⟨by decide, ClassChecks82427G05.checked0323⟩
    · exact ⟨by decide, ClassChecks82427G08.checked0497⟩
    · exact ⟨by decide, ClassChecks82427G10.checked0653⟩
    · exact ⟨by decide, ClassChecks82427G13.checked0836⟩
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
#print axioms ramps09

theorem classes10 (b : CrossBandCredit208.Band) (t : Term) (ht : t ∈ terms 10 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p ((row 10).low/(t.q*(t.q+1))) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,68,8⟩, ⟨2,118,2⟩, ⟨2,168,1⟩, ⟨3,68,2⟩, ⟨11,68,1⟩} : Finset Term) at ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G00.checked0015⟩
    · exact ⟨by decide, ClassChecks82427G00.checked0003⟩
    · exact ⟨by decide, ClassChecks82427G00.checked0000⟩
    · exact ⟨by decide, ClassChecks82427G04.checked0208⟩
    · exact ⟨by decide, ClassChecks82427G12.checked0725⟩
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
#print axioms classes10

theorem ramps10 (b : CrossBandCredit208.Band) (t : RampTerm) (ht : t ∈ ramps 10 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p (RampLength (row 10).low (At (row 10) (length (k:=10) (by decide)) b) t.p) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,468⟩, ⟨3,157⟩, ⟨5,62⟩, ⟨7,34⟩, ⟨11,214⟩} : Finset RampTerm) at ht
    change t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧
      ClassFastNumeric82427.check t.p (RampLength 82427 (⟨87,19,292,50,59,64,65,67⟩ : CleanupEval208.Band) t.p) t.count=true
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G02.checked0137⟩
    · exact ⟨by decide, ClassChecks82427G05.checked0327⟩
    · exact ⟨by decide, ClassChecks82427G08.checked0500⟩
    · exact ⟨by decide, ClassChecks82427G11.checked0656⟩
    · exact ⟨by decide, ClassChecks82427G13.checked0839⟩
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
#print axioms ramps10

theorem classes11 (b : CrossBandCredit208.Band) (t : Term) (ht : t ∈ terms 11 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p ((row 11).low/(t.q*(t.q+1))) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,66,9⟩, ⟨2,112,3⟩, ⟨2,158,1⟩, ⟨3,66,3⟩, ⟨11,66,1⟩} : Finset Term) at ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G01.checked0016⟩
    · exact ⟨by decide, ClassChecks82427G00.checked0004⟩
    · exact ⟨by decide, ClassChecks82427G00.checked0001⟩
    · exact ⟨by decide, ClassChecks82427G04.checked0209⟩
    · exact ⟨by decide, ClassChecks82427G12.checked0726⟩
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
#print axioms classes11

theorem ramps11 (b : CrossBandCredit208.Band) (t : RampTerm) (ht : t ∈ ramps 11 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p (RampLength (row 11).low (At (row 11) (length (k:=11) (by decide)) b) t.p) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,486⟩, ⟨3,163⟩, ⟨5,65⟩, ⟨7,36⟩, ⟨11,222⟩} : Finset RampTerm) at ht
    change t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧
      ClassFastNumeric82427.check t.p (RampLength 82427 (⟨87,21,298,46,56,61,63,64⟩ : CleanupEval208.Band) t.p) t.count=true
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G02.checked0143⟩
    · exact ⟨by decide, ClassChecks82427G05.checked0330⟩
    · exact ⟨by decide, ClassChecks82427G08.checked0503⟩
    · exact ⟨by decide, ClassChecks82427G11.checked0658⟩
    · exact ⟨by decide, ClassChecks82427G13.checked0841⟩
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
#print axioms ramps11

end
end JSP233.RowLightCertificates82427G02
