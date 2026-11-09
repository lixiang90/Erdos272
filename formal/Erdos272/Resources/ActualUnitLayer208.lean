module

public import Erdos272.Resources.ActualUnitRecipe208
public import Erdos272.Resources.ActualCleanupEval208
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.ActualUnitLayer208
open StarCompletion APGeometry NearAP36 SourceBridge208 SourceCertified208 SourcePrefixSpecs208
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208
open SevenFamily208 ActualUnitSystem208 ActualUnitRecipe208 UnitRecipeStatic208 CleanupMachineSound208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 200000

theorem evalData_at {r : CleanupMachine208.Row} (hlen : r.bands.length=7) (b : Band) :
    evalData r b=ActualCleanupEval208.At (toRow r) (by simpa only [toRow,List.length_map] using hlen) b := by
  have hb : b.val<r.bands.length := by rw [hlen];exact b.isLt
  simp only [evalData,data,ActualCleanupEval208.At,toRow,List.getElem_map,List.getD_eq_getElem _ _ hb]

/-- The first layer is empty by the actual source certificate and crookedness;
it requires no numerical cleanup row certificate. -/
theorem actual_first_empty {N M : ℕ} {base : Fin 14} {source : Fin 7→Fin 14}
    {lower upper : Fin 7→ℕ} {r : CleanupMachine208.Row} {A : Finset (Finset ℤ)}
    (h : Static M base source lower upper r) (hi : r.i≤1) (hM : 2≤M) (hN : N<2^50)
    (hcover : ∀n : ℕ,M≤n→11*n≤N→∃b,lower b≤n ∧ n<upper b)
    (hlegal : Legal (Ground N) A) (hbad : ∀S∈A,¬IsAP S)
    (hsize : ∀S∈A,M≤S.card) (hsparse : ∀S∈A,11*S.card≤N) :
    PoolNear A (potential base) (r.i-1)=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  have hSA := (Finset.mem_filter.mp hS).1
  obtain ⟨b,hlo,hhi⟩ := hcover S.card (hsize S hSA) (hsparse S hSA)
  have hn : r.i-1+1=r.i := by have hh:=h.2.1;omega
  have hs := h.2.2.2.2 b
  have hcard : S.card<2^50 := (Finset.card_le_card (hlegal.1 S hSA)).trans_lt (by simpa only [ground_card] using hN)
  have hsource : potential base (r.i-1+1)≤(floorAt (source b) (data r b).E : ℝ) := by
    simp only [hn,potential]
    exact_mod_cast hs.2.2.2.2.2.2.2
  have hlow : rowStart (source b)≤S.card := by rw [hs.2.2.1,hs.1];exact hlo
  have he := DeficiencyCuts208.actual_unit_cut (source b) hS hlow hcard hsource
  have hp := CoreCoordinates208.defect_positive (hM.trans (hsize S hSA)) (hlegal.1 S hSA) (hbad S hSA)
  have hei := hs.2.2.2.2.2.1
  omega

/-- A genuine actual source-deficiency layer is paid by the certified finite
cleanup row.  Only its row ChunkFacts, rather than any near-family bound,
are consumed. -/
theorem actual_layer {N M : ℕ} {base : Fin 14} {source : Fin 7→Fin 14}
    {lower upper : Fin 7→ℕ} {r : CleanupMachine208.Row} {out : CleanupEval208.Totals}
    {A : Finset (Finset ℤ)} (h : Static M base source lower upper r)
    (hi : 2≤r.i) (hM : 2≤M) (hN : N<2^50)
    (hcover : ∀n : ℕ,M≤n→11*n≤N→∃b,lower b≤n ∧ n<upper b)
    (hlegal : Legal (Ground N) A) (hbad : ∀S∈A,¬IsAP S)
    (hsize : ∀S∈A,M≤S.card) (hsparse : ∀S∈A,11*S.card≤N)
    (hf : CleanupEval208.ChunkFacts (toRow r) 1 (r.high/(M-r.i)) out)
    (hgrid : 0<r.grid) (hlow : 0<r.low) (hlN : r.low≤N) (hNh : N≤r.high) :
    ((PoolNear A (potential base) (r.i-1)).card : ℝ)≤
      (N : ℝ)^2*ResidualAggregate208.Price r.i (ResidualTwoCensus208.H M)+
        (253/35 : ℝ)*N+out.light+(N : ℝ)*((out.net : ℝ)/r.grid) := by
  have hDn : N/(M-r.i)≤r.high/(M-r.i) := Nat.div_le_div_right (c := M-r.i) hNh
  have hgood : ∀d∈Finset.Icc 1 (N/(M-r.i)),(CleanupEval208.step (toRow r) d).good=true := by
    intro d hd
    apply CleanupRowBounds208.good_Icc hf
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans hDn⟩
  let p:=recipe h hcover hgood
  obtain ⟨s,hsN,hsD,hsM,hse,hsF,hmap,hv⟩ :=
    actual_system p hM hi h.2.2.2.1 hN hlegal hbad hsize hsparse
  let hlen : (toRow r).bands.length=7 := by simpa only [toRow,List.length_map] using h.1
  have hmatch : ∀d∈Finset.Icc 1 s.D,∀b : Band,
      (ActualCleanupEval208.At (toRow r) hlen b).T=s.T d b ∧
      (ActualCleanupEval208.At (toRow r) hlen b).E=s.E d b ∧
      (ActualCleanupEval208.At (toRow r) hlen b).U=s.U d b ∧
      CleanupEval208.block (ActualCleanupEval208.At (toRow r) hlen b) d=s.B d b := by
    intro d hd b
    rw [←evalData_at h.1 b]
    exact ⟨(hmap d b).1.symm,(hmap d b).2.1.symm,(hmap d b).2.2.1.symm,(hmap d b).2.2.2.symm⟩
  have hc := ActualCleanupEval208.actual_family_bound hv (toRow r) hlen hf
    (by simpa only [hsD] using hDn) hmatch hgrid hlow (by simpa only [hsN,toRow] using hlN)
    (by simpa only [hsN,toRow] using hNh) (by change s.e≤r.i;exact hse.le)
  simpa only [hsN,hsM,hse,hsF,toRow] using hc

#print axioms evalData_at
#print axioms actual_first_empty
#print axioms actual_layer
end
end JSP233.ActualUnitLayer208
