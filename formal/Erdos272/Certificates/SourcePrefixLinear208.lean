module

public import Erdos272.Certificates.SourcePrefixBlocks208

@[expose] public section

/-! Use the proved linear row checker when the physical size exceeds twice
the target-list length. The certificate statements retain the original checker. -/
namespace JSP233.BatchSource208
set_option maxHeartbeats 0
set_option Elab.async false

def linearRowBlockCheck (a : ℕ → ℕ) (lo count : ℕ) (targets : List ℕ) : Bool :=
  (List.range count).all (fun r => BatchSourceLinear208.checkRowFrom a (lo + r) 0 0 targets)

theorem rowBlockCheck_eq_linear {a : ℕ → ℕ} {lo count : ℕ} {targets : List ℕ}
    (h : 2 * targets.length < lo) :
    rowBlockCheck a lo count targets = linearRowBlockCheck a lo count targets := by
  unfold rowBlockCheck linearRowBlockCheck
  apply congrArg (List.all (List.range count))
  funext r
  exact (BatchSourceLinear208.checkRowFrom_eq targets (by omega)).symm

#print axioms rowBlockCheck_eq_linear
end JSP233.BatchSource208
