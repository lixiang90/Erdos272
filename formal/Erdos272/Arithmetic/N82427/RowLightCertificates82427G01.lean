module

public import Erdos272.Arithmetic.N82427.RowLightData82427
public import Erdos272.Arithmetic.N82427.ClassChecks82427G00
public import Erdos272.Arithmetic.N82427.ClassChecks82427G02
public import Erdos272.Arithmetic.N82427.ClassChecks82427G03
public import Erdos272.Arithmetic.N82427.ClassChecks82427G05
public import Erdos272.Arithmetic.N82427.ClassChecks82427G08
public import Erdos272.Arithmetic.N82427.ClassChecks82427G10
public import Erdos272.Arithmetic.N82427.ClassChecks82427G12
public import Erdos272.Arithmetic.N82427.ClassChecks82427G13

@[expose] public section

namespace JSP233.RowLightCertificates82427G01
open RowLightSlope82427 PhaseSlope82427 PhaseRampSlope82427 ActualCleanupEval208 ClassCount158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxErrors 1

attribute [local irreducible] ClassFastNumeric82427.check

theorem classes04 (b : CrossBandCredit208.Band) (t : Term) (ht : t ∈ terms 4 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p ((row 4).low/(t.q*(t.q+1))) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,80,6⟩, ⟨2,154,1⟩, ⟨3,80,2⟩, ⟨11,80,1⟩} : Finset Term) at ht
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
#print axioms classes04

theorem ramps04 (b : CrossBandCredit208.Band) (t : RampTerm) (ht : t ∈ ramps 4 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p (RampLength (row 4).low (At (row 4) (length (k:=4) (by decide)) b) t.p) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,358⟩, ⟨3,120⟩, ⟨5,48⟩, ⟨7,26⟩, ⟨11,163⟩} : Finset RampTerm) at ht
    change t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧
      ClassFastNumeric82427.check t.p (RampLength 82427 (⟨87,7,210,74,77,79,79,80⟩ : CleanupEval208.Band) t.p) t.count=true
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G02.checked0120⟩
    · exact ⟨by decide, ClassChecks82427G05.checked0311⟩
    · exact ⟨by decide, ClassChecks82427G08.checked0485⟩
    · exact ⟨by decide, ClassChecks82427G10.checked0641⟩
    · exact ⟨by decide, ClassChecks82427G13.checked0824⟩
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
#print axioms ramps04

theorem classes05 (b : CrossBandCredit208.Band) (t : Term) (ht : t ∈ terms 5 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p ((row 5).low/(t.q*(t.q+1))) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,78,6⟩, ⟨2,148,1⟩, ⟨3,78,2⟩, ⟨11,78,1⟩} : Finset Term) at ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G00.checked0011⟩
    · exact ⟨by decide, ClassChecks82427G00.checked0001⟩
    · exact ⟨by decide, ClassChecks82427G03.checked0204⟩
    · exact ⟨by decide, ClassChecks82427G12.checked0721⟩
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
#print axioms classes05

theorem ramps05 (b : CrossBandCredit208.Band) (t : RampTerm) (ht : t ∈ ramps 5 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p (RampLength (row 5).low (At (row 5) (length (k:=5) (by decide)) b) t.p) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,380⟩, ⟨3,127⟩, ⟨5,50⟩, ⟨7,28⟩, ⟨11,172⟩} : Finset RampTerm) at ht
    change t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧
      ClassFastNumeric82427.check t.p (RampLength 82427 (⟨87,9,232,70,74,76,77,78⟩ : CleanupEval208.Band) t.p) t.count=true
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G02.checked0123⟩
    · exact ⟨by decide, ClassChecks82427G05.checked0314⟩
    · exact ⟨by decide, ClassChecks82427G08.checked0488⟩
    · exact ⟨by decide, ClassChecks82427G10.checked0644⟩
    · exact ⟨by decide, ClassChecks82427G13.checked0827⟩
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
#print axioms ramps05

theorem classes06 (b : CrossBandCredit208.Band) (t : Term) (ht : t ∈ terms 6 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p ((row 6).low/(t.q*(t.q+1))) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,76,7⟩, ⟨2,142,2⟩, ⟨3,76,2⟩, ⟨11,76,1⟩} : Finset Term) at ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G00.checked0012⟩
    · exact ⟨by decide, ClassChecks82427G00.checked0002⟩
    · exact ⟨by decide, ClassChecks82427G03.checked0205⟩
    · exact ⟨by decide, ClassChecks82427G12.checked0722⟩
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
#print axioms classes06

theorem ramps06 (b : CrossBandCredit208.Band) (t : RampTerm) (ht : t ∈ ramps 6 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p (RampLength (row 6).low (At (row 6) (length (k:=6) (by decide)) b) t.p) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,398⟩, ⟨3,133⟩, ⟨5,53⟩, ⟨7,29⟩, ⟨11,181⟩} : Finset RampTerm) at ht
    change t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧
      ClassFastNumeric82427.check t.p (RampLength 82427 (⟨87,11,248,66,71,74,75,75⟩ : CleanupEval208.Band) t.p) t.count=true
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G02.checked0125⟩
    · exact ⟨by decide, ClassChecks82427G05.checked0316⟩
    · exact ⟨by decide, ClassChecks82427G08.checked0490⟩
    · exact ⟨by decide, ClassChecks82427G10.checked0646⟩
    · exact ⟨by decide, ClassChecks82427G13.checked0829⟩
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
#print axioms ramps06

theorem classes07 (b : CrossBandCredit208.Band) (t : Term) (ht : t ∈ terms 7 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p ((row 7).low/(t.q*(t.q+1))) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,74,7⟩, ⟨2,136,2⟩, ⟨2,198,1⟩, ⟨3,74,2⟩, ⟨11,74,1⟩} : Finset Term) at ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G00.checked0012⟩
    · exact ⟨by decide, ClassChecks82427G00.checked0002⟩
    · exact ⟨by decide, ClassChecks82427G00.checked0000⟩
    · exact ⟨by decide, ClassChecks82427G03.checked0205⟩
    · exact ⟨by decide, ClassChecks82427G12.checked0722⟩
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
#print axioms classes07

theorem ramps07 (b : CrossBandCredit208.Band) (t : RampTerm) (ht : t ∈ ramps 7 b) :
    t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p (RampLength (row 7).low (At (row 7) (length (k:=7) (by decide)) b) t.p) t.count=true := by
  revert ht
  rcases b with ⟨b,hb⟩
  interval_cases b <;> intro ht
  · change t ∈ ({⟨2,416⟩, ⟨3,139⟩, ⟨5,56⟩, ⟨7,32⟩, ⟨11,189⟩} : Finset RampTerm) at ht
    change t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧
      ClassFastNumeric82427.check t.p (RampLength 82427 (⟨87,13,263,62,68,71,72,73⟩ : CleanupEval208.Band) t.p) t.count=true
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, ClassChecks82427G02.checked0128⟩
    · exact ⟨by decide, ClassChecks82427G05.checked0319⟩
    · exact ⟨by decide, ClassChecks82427G08.checked0493⟩
    · exact ⟨by decide, ClassChecks82427G10.checked0649⟩
    · exact ⟨by decide, ClassChecks82427G13.checked0832⟩
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
#print axioms ramps07

end
end JSP233.RowLightCertificates82427G01
