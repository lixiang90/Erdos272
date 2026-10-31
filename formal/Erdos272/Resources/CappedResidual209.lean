import Erdos272.Arithmetic.CappedWeights209
import Erdos272.Counting.CoarseCensus209
import Erdos272.Resources.ResidualGlobal208

namespace JSP233.CappedResidual209
open StarCompletion APGeometry NearAP36 ResidualStratum208 ResidualGlobal208 ResidualPrice208
open ResidualAggregate208 ResidualWeights208 CappedWeights209 CoarseCensus209
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem actual_cumulative_bound {N M D b : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hb : b≤M)
    (core : Finset ℤ→Finset ℤ) (step : Finset ℤ→ℕ) (point : ℕ→ℤ)
    (hstep : ∀ S∈F,step S∈Finset.Icc 1 D)
    (hsub : ∀ S∈F,core S⊆S)
    (hAt : ∀ S∈F,APAt (step S : ℤ) (point (step S)) (core S))
    (ht : ∀ S∈F,point (step S)∈core S) (hsize : ∀ S∈F,M≤S.card)
    (hmax : ∀ S∈F,∀R : Finset ℤ,IsAP R → R⊆S → R.card≤(core S).card)
    (x : ℤ) :
    Cumulative F (fun S=>S\core S) x b≤∑d∈Finset.Icc 1 D,Occupancy N M d b := by
  have hpoint : ∀d∈Finset.Icc 1 D,
      Cumulative (F.filter (fun S=>step S=d)) (fun S=>S\core S) x b≤Occupancy N M d b := by
    intro d hd
    let G := F.filter (fun S=>step S=d)
    have hGF : G⊆F := Finset.filter_subset _ _
    have hG : Legal (Ground N) G := ⟨fun S hS=>hF.1 S (hGF hS),
      fun S hS T hT hST=>hF.2 S (hGF hS) T (hGF hT) hST⟩
    have hGAt : ∀S∈G,APAt (d : ℤ) (point d) (core S) := by
      intro S hS
      simpa only [(Finset.mem_filter.mp hS).2] using hAt S (hGF hS)
    have hGt : ∀S∈G,point d∈core S := by
      intro S hS
      simpa only [(Finset.mem_filter.mp hS).2] using ht S (hGF hS)
    exact actual_defect_stratum hG hb core (fun S hS=>hsub S (hGF hS)) hGAt hGt
      (fun S hS=>hsize S (hGF hS)) (fun S hS=>hmax S (hGF hS)) x
  have hs := Finset.sum_le_sum hpoint
  rw [←cumulative_step_partition F (fun S=>S\core S) step D hstep x b] at hs
  exact hs

theorem actual_global_residual {N M D e c : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hc : 1≤c) (hce : c<e) (heM : e<M) (hshort : 3*c<2*M)
    (core : Finset ℤ→Finset ℤ) (step : Finset ℤ→ℕ) (point : ℕ→ℤ)
    (hstep : ∀S∈F,step S∈Finset.Icc 1 D) (hsub : ∀S∈F,core S⊆S)
    (hAt : ∀S∈F,APAt (step S : ℤ) (point (step S)) (core S))
    (ht : ∀S∈F,point (step S)∈core S) (hsize : ∀S∈F,M≤S.card)
    (hbad : ∀S∈F,¬IsAP S) (hsmall : ∀S∈F,(S\core S).card<e)
    (hmax : ∀S∈F,∀R : Finset ℤ,IsAP R → R⊆S → R.card≤(core S).card) :
    (F.card : ℝ)≤(N : ℝ)^2*
      ((∑b∈Finset.Icc 2 c,(1/((M-b : ℕ) : ℝ)+1/((2*M-3*b : ℕ) : ℝ))/((b : ℝ)*(b-1)))+
        (2/((M-e : ℕ) : ℝ))/(c : ℝ)) := by
  let piece := fun S=>S\core S
  have hpos : ∀S∈F,0<(piece S).card := by
    intro S hS
    by_contra hn
    have hz : (S\core S).card=0 := by dsimp only [piece] at hn; omega
    have hcS := Finset.card_sdiff_add_card_eq_card (hsub S hS)
    have heq : core S=S := Finset.eq_of_subset_of_card_le (hsub S hS) (by omega)
    apply hbad S hS
    rw [←heq]
    exact (isAP_iff_exists_APAt _).mpr ⟨step S,point (step S),hAt S hS,ht S hS⟩
  have hs : ∀x∈Ground N,∀b,2≤b → b≤c →
      (Cumulative F piece x b : ℝ)≤((Ground N).card : ℝ)*
        (1/((M-b : ℕ) : ℝ)+1/((2*M-3*b : ℕ) : ℝ)) := by
    intro x hx b hb hbc
    simp only [ground_card]
    have hcum := actual_cumulative_bound hF (by omega : b≤M) core step point hstep hsub hAt ht hsize hmax x
    have hR : (Cumulative F piece x b : ℝ)≤((∑d∈Finset.Icc 1 D,Occupancy N M d b : ℕ) : ℝ) := by exact_mod_cast hcum
    exact hR.trans (occupancy_short (by omega : b<M) (by omega : 3*b<2*M))
  have ht' : ∀x∈Ground N,∀b,c<b → b≤e →
      (Cumulative F piece x b : ℝ)≤((Ground N).card : ℝ)*(2/((M-e : ℕ) : ℝ)) := by
    intro x hx b hcb hbe
    simp only [ground_card]
    have hcum := actual_cumulative_bound hF (by omega : b≤M) core step point hstep hsub hAt ht hsize hmax x
    have hR : (Cumulative F piece x b : ℝ)≤((∑d∈Finset.Icc 1 D,Occupancy N M d b : ℕ) : ℝ) := by exact_mod_cast hcum
    have hp := hR.trans (occupancy_tail hbe heM)
    calc
      _≤2*(N : ℝ)/((M-e : ℕ) : ℝ) := hp
      _=_ := by ring
  have hh := actual_capped_payment F (Ground N) piece
    (fun b=>1/((M-b : ℕ) : ℝ)+1/((2*M-3*b : ℕ) : ℝ)) (2/((M-e : ℕ) : ℝ)) hc hce
    (fun S hS=>Finset.sdiff_subset.trans (hF.1 S hS)) hpos hsmall hs ht'
  simpa only [ground_card] using hh

#print axioms actual_cumulative_bound
#print axioms actual_global_residual
end
end JSP233.CappedResidual209
