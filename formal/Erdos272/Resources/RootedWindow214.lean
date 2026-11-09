module

public import Erdos272.Resources.RetainedIntervals214
public import Erdos272.Resources.InitialPreparation213

@[expose] public section
namespace JSP233.RootedWindow214
open StarCompletion APGeometry DenseDeletion40
set_option autoImplicit false
set_option maxHeartbeats 0
theorem actual_original_upper_of_root11 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 653292≤N) (hhigh : N≤656184) (hF : Legal (Ground N) F)
    (hcommon : ∃c∈Ground N,∀S∈Retained N 11 F,¬IsAP S→c∈S) : F.card≤B N := by
  by_cases hcard : B N≤F.card
  · rcases InitialPreparation213.actual_initial_preparation (by omega : 646000≤N)
      (by omega : N≤705097) hF hcard hcommon with hb | ⟨H,c,L,R,P,T,_hHF,hcardH,g⟩
    · exact hb
    · have hb := RetainedIntervals214.actual_recovered_original g hN hhigh
      omega
  · omega
#print axioms actual_original_upper_of_root11
end JSP233.RootedWindow214
