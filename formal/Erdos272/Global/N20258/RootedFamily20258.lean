module

public import Erdos272.Global.N20258.InitialPreparation20258
public import Erdos272.Retention.N20258.OneSidedRecovery20258

@[expose] public section
namespace JSP233.RootedFamily20258
open StarCompletion DenseDeletion40
set_option autoImplicit false

/-- The common root may be destroyed by the deleted members. Recovery
still bounds the cardinality of the entire original family. -/
theorem actual_upper_from_19227 {N : ℕ} {F : Finset (Finset ℤ)} (lo : 19227 ≤ N) (hi : N < 2^16)
    (legal : Legal (Ground N) F)
    (common : ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S) : F.card ≤ B N := by
  by_cases near : B N ≤ F.card
  · rcases InitialPreparation20258.actual_initial_preparation lo hi legal near common with paid|start
    · exact paid
    · obtain ⟨H,c,L,R,P,T,_,card,g⟩ := start
      exact card ▸ OneSidedRecovery20258.actual_upper lo hi g
  · omega

theorem actual_upper {N : ℕ} {F : Finset (Finset ℤ)} (lo : 20000 ≤ N) (hi : N < 2^16)
    (legal : Legal (Ground N) F)
    (common : ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S) : F.card ≤ B N :=
  actual_upper_from_19227 (by omega) hi legal common

#print axioms actual_upper
end JSP233.RootedFamily20258
