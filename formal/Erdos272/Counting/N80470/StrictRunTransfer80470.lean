module

public import Erdos272.Resources.N86412.StrictRunSource86412
public import Erdos272.Resources.N86412.SourceContract86412

@[expose] public section

namespace JSP233.StrictRunTransfer80470
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208
open SourceContract86412 StrictRunSource86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_run_plan_source {N : ℕ} {S : Finset ℤ} (q : Plan)
    (hq : Conditions q) (high : CertifiedContract)
    (hlower : high.contract.lower ≤ q.upper)
    (hdefect : high.contract.defect ≤ q.defect)
    (htarget : q.target ≤ high.contract.target)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : q.lower ≤ S.card) (he : q.defect ≤ Defect S) :
    q.target ≤ (Pool S).card := by
  rcases hq with ⟨he₂,helower,hl,hu,hlen,hpoints⟩
  by_cases hupper : q.upper ≤ S.card
  · exact htarget.trans (high.actual hN hground hS (hlower.trans hupper) (hdefect.trans he))
  · have hi : S.card-q.lower ∈ Finset.range q.heads.length :=
      Finset.mem_range.mpr (by omega)
    have hs : q.lower+(S.card-q.lower)=S.card := by omega
    have hc := hpoints (S.card-q.lower) hi
    rw [hs] at hc
    rcases hc with hshort | ⟨hh,hha,hp⟩
    · have hmax := maxAPSize_le_card S
      have htwo := two_le_maxAPSize hS
      unfold Defect at he
      omega
    · exact hp.trans (StrictRunSource86412.actual_point_source hS (by omega) he₂ he hh hha)

#print axioms actual_run_plan_source
end
end JSP233.StrictRunTransfer80470
