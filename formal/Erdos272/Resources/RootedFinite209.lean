module

public import Erdos272.Resources.RootedWindow209
public import Erdos272.Resources.RegionalRecoveryActual209
public import Erdos272.Resources.GlobalRecoveryActual209

@[expose] public section

namespace JSP233.RootedFinite209
open StarCompletion APGeometry DenseDeletion40
noncomputable section
set_option maxHeartbeats 0

theorem actual_original_upper_of_root11 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912 ≤ N) (hhigh : N ≤ 62443451) (hF : Legal (Ground N) F)
    (hcommon : ∃ c ∈ Ground N, ∀ S ∈ Retained N 11 F, ¬IsAP S → c ∈ S) :
    F.card ≤ B N := by
  by_cases hsmall : N ≤ 705097
  · exact RootedWindow209.actual_original_upper_of_root11 hN hsmall hF hcommon
  · by_cases hmiddle : N ≤ 2000000
    · exact RegionalRecoveryActual209.actual_original_upper_of_root11
        (by omega) hmiddle hF hcommon
    · exact GlobalRecoveryActual209.actual_original_upper_of_root11
        (by omega) hhigh hF hcommon

#print axioms actual_original_upper_of_root11
end
end JSP233.RootedFinite209
