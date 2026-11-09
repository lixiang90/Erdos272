module

public import Erdos272.Certificates.TotientLookup208

@[expose] public section

/-! Complete kernel certificate for the proposed totient lookup, using a
proved bounded prime test. The data generator is outside the trust base.
-/
namespace JSP233.SourceLookupFast208
open SourceLookupData208
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem sieve_check : PrimeCover208.check phi factor Limit = true := by
  change (decide (phi 0 = 0 ∧ phi 1 = 1) &&
    (List.range (Limit - 1)).all (fun j =>
      TotientSieveFast208.checkStepWith PrimeCover208.primeCheck phi factor (j + 2))) = true
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by decide +kernel, List.all_eq_true.mpr ?_⟩
  intro j hj
  have hjlt : j < 32752 := by
    simpa only [Limit, Nat.reduceSub] using List.mem_range.mp hj
  let b : Fin 128 := ⟨j / 256, by omega⟩
  have hr : j % 256 < min 256 (Limit - 1 - b.val * 256) := by
    dsimp [b]
    norm_num only [Limit, Nat.reduceSub]
    omega
  have checked := block_step (blocks_checked b) hr
  have he : b.val * 256 + 2 + j % 256 = j + 2 := by
    dsimp [b]
    omega
  simpa only [he] using checked

theorem phi_correct (n : ℕ) (hn : n ≤ Limit) : phi n = Nat.totient n :=
  PrimeCover208.check_sound sieve_check n hn

#print axioms sieve_check
#print axioms phi_correct
end JSP233.SourceLookupFast208
