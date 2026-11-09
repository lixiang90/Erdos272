module

public import Erdos272.Resources.ActualUnitSystem208
public import Erdos272.Arithmetic.UnitRecipeStatic208
public import Erdos272.Resources.CleanupRowBounds208
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.ActualUnitRecipe208
open StarCompletion ActualUnitSystem208 UnitRecipeStatic208
open CrossBandCredit208 CleanupMachineSound208 SourcePrefixSpecs208 SourceCertified208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 200000

theorem data_mem {r : CleanupMachine208.Row} (h : r.bands.length=7) (b : Fin 7) :
    data r b∈r.bands := by
  have hb : b.val<r.bands.length := by rw [h];exact b.isLt
  rw [data,List.getD_eq_getElem _ _ hb]
  exact List.getElem_mem hb

theorem evalData_mem {r : CleanupMachine208.Row} (h : r.bands.length=7) (b : Fin 7) :
    evalData r b∈(toRow r).bands := by
  exact List.mem_map.mpr ⟨data r b,data_mem h b,rfl⟩

def recipe {N M : ℕ} {base : Fin 14} {source : Fin 7→Fin 14} {lower upper : Fin 7→ℕ}
    {r : CleanupMachine208.Row} (h : Static M base source lower upper r)
    (hcover : ∀n : ℕ,M≤n→11*n≤N→∃b,lower b≤n ∧ n<upper b)
    (hgood : ∀d∈Finset.Icc 1 (N/(M-r.i)),(CleanupEval208.step (toRow r) d).good=true) :
    Recipe N M r.i (r.i-1) (potential base) where
  data:=evalData r
  source:=source
  source_start:=fun b=>by exact (h.2.2.2.2 b).2.2.1
  source_height:=by
    intro b
    have hi : r.i-1+1=r.i := by have hh:=h.2.1;omega
    simp only [hi,potential,evalData,toBand]
    exact_mod_cast (h.2.2.2.2 b).2.2.2.2.2.2.2
  M_le:=fun b=>(h.2.2.2.2 b).2.2.2.1
  E_one:=fun b=>(h.2.2.2.2 b).2.2.2.2.1
  E_le:=fun b=>(h.2.2.2.2 b).2.2.2.2.2.1
  TU:=fun b=>(h.2.2.2.2 b).2.2.2.2.2.2.1
  cover:=by
    intro n hn hs
    obtain ⟨b,hb⟩ := hcover n hn hs
    refine ⟨b,?_⟩
    simpa only [evalData,toBand,(h.2.2.2.2 b).1,(h.2.2.2.2 b).2.1] using hb
  physical:=by
    intro d hd b
    have hb := (CleanupEval208.step_good (hgood d hd)).1 (evalData r b) (evalData_mem h.1 b)
    rcases hb with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    exact ⟨h5,h6,h8⟩

#print axioms data_mem
#print axioms evalData_mem
#print axioms recipe
end
end JSP233.ActualUnitRecipe208
