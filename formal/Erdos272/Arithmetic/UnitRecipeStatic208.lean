module

public import Erdos272.Arithmetic.CleanupRecipes208
public import Erdos272.Arithmetic.CleanupMachineSound208
public import Erdos272.Resources.SourceCertified208
public import Mathlib.Data.List.GetD

@[expose] public section

namespace JSP233.UnitRecipeStatic208
open SourcePrefixSpecs208 SourceCertified208
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 200000

def base242 : Fin 14 := ⟨0,by decide⟩
def base243 : Fin 14 := ⟨1,by decide⟩
def source242 (b : Fin 7) : Fin 14 := ⟨2*b.val,by omega⟩
def source243 (b : Fin 7) : Fin 14 := ⟨2*b.val+1,by omega⟩
def lower242 (b : Fin 7) : ℕ := [242,338,484,726,1210,2420,7744].getD b.val 0
def upper242 (b : Fin 7) : ℕ := [338,484,726,1210,2420,7744,247808].getD b.val 0
def lower243 (b : Fin 7) : ℕ := [243,340,486,729,1215,2430,7776].getD b.val 0
def upper243 (b : Fin 7) : ℕ := [340,486,729,1215,2430,7776,248832].getD b.val 0
def emptyBand : CleanupMachine208.Band := ⟨0,0,0,0,0,0,0,0⟩
def data (r : CleanupMachine208.Row) (b : Fin 7) : CleanupMachine208.Band :=
  r.bands.getD b.val emptyBand
def evalData (r : CleanupMachine208.Row) (b : Fin 7) : CleanupEval208.Band :=
  CleanupMachineSound208.toBand (data r b)

def Static (M : ℕ) (base : Fin 14) (source : Fin 7→Fin 14)
    (lower upper : Fin 7→ℕ) (r : CleanupMachine208.Row) : Prop :=
  r.bands.length=7 ∧ 1≤r.i ∧ r.i≤184 ∧ r.i<M ∧
    ∀b : Fin 7,(data r b).T=lower b ∧ (data r b).U=upper b ∧
      rowStart (source b)=(data r b).T ∧ M≤(data r b).T ∧
      1≤(data r b).E ∧ (data r b).E≤r.i ∧ (data r b).T<(data r b).U ∧
      floorAt base r.i≤floorAt (source b) (data r b).E
instance (M : ℕ) (base : Fin 14) (source : Fin 7→Fin 14)
    (lower upper : Fin 7→ℕ) (r : CleanupMachine208.Row) :
    Decidable (Static M base source lower upper r) := by unfold Static;infer_instance

theorem cover242 {N n : ℕ} (hN : N≤705097) (hlow : 242≤n) (hsparse : 11*n≤N) :
    ∃b : Fin 7,lower242 b≤n ∧ n<upper242 b := by
  by_cases h0 : n<338
  · exact ⟨0,by norm_num [lower242,upper242];exact ⟨hlow,h0⟩⟩
  by_cases h1 : n<484
  · exact ⟨1,by norm_num [lower242,upper242];omega⟩
  by_cases h2 : n<726
  · exact ⟨2,by norm_num [lower242,upper242];omega⟩
  by_cases h3 : n<1210
  · exact ⟨3,by norm_num [lower242,upper242];omega⟩
  by_cases h4 : n<2420
  · exact ⟨4,by norm_num [lower242,upper242];omega⟩
  by_cases h5 : n<7744
  · exact ⟨5,by norm_num [lower242,upper242];omega⟩
  exact ⟨6,by norm_num [lower242,upper242];omega⟩

theorem cover243 {N n : ℕ} (hN : N≤705097) (hlow : 243≤n) (hsparse : 11*n≤N) :
    ∃b : Fin 7,lower243 b≤n ∧ n<upper243 b := by
  by_cases h0 : n<340
  · exact ⟨0,by norm_num [lower243,upper243];exact ⟨hlow,h0⟩⟩
  by_cases h1 : n<486
  · exact ⟨1,by norm_num [lower243,upper243];omega⟩
  by_cases h2 : n<729
  · exact ⟨2,by norm_num [lower243,upper243];omega⟩
  by_cases h3 : n<1215
  · exact ⟨3,by norm_num [lower243,upper243];omega⟩
  by_cases h4 : n<2430
  · exact ⟨4,by norm_num [lower243,upper243];omega⟩
  by_cases h5 : n<7776
  · exact ⟨5,by norm_num [lower243,upper243];omega⟩
  exact ⟨6,by norm_num [lower243,upper243];omega⟩

#print axioms cover242
#print axioms cover243
end JSP233.UnitRecipeStatic208
