import Erdos272.Global.InitialPreparation218
import Erdos272.Resources.RecoveryBounds218
import Erdos272.Resources.OriginalTerminal218

/-! Complete rooted recovery on the original family.  All geometry, omitted
families, density upgrades and terminal plans are constructed internally. -/
namespace JSP233.Rooted642498218
open StarCompletion APGeometry DenseDeletion40
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem actual_rooted_upper {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 642498≤N) (hhigh : N≤653292) (hF : Legal (Ground N) F)
    (hcommon : ∃c∈Ground N,∀S∈Retained N 11 F,¬IsAP S→c∈S) :
    F.card≤B N := by
  by_cases hb : F.card≤B N
  · exact hb
  · have hcard : B N≤F.card := by omega
    rcases InitialPreparation218.actual_initial_preparation hN (by omega : N≤705097)
      hF hcard hcommon with hb | ⟨H,c,L,R,P,T,_hchoice,hcardH,g⟩
    · exact hb
    · have hs := RecoveryBounds218.actual_final_bounds hN hhigh g
      have hn : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
      have hl : (L : ℝ)<(5/97 : ℝ)*N := by nlinarith only [hs.1,hn]
      have hH := OriginalTerminal218.actual_recovered_original g hN hhigh hl hs.2
      omega

#print axioms actual_rooted_upper
end
end JSP233.Rooted642498218
