import Erdos272.Arithmetic.SourceLookupFast208
import Erdos272.Arithmetic.SourceTargetOrder208

/-! Shared, already certified data for the disjoint finite-prefix chunks. -/
namespace JSP233.SourcePrefixSpecs208
open SourceTargets208 SourceTargetOrder208

def rowTargets (i : Fin 14) : List ℕ := (targetAt i).2

def rowStart (i : Fin 14) : ℕ := (targetAt i).1

theorem phi_correct {n : ℕ} (hn : n ≤ 32753) :
    SourceLookupData208.phi n = Nat.totient n :=
  SourceLookupFast208.phi_correct n hn

theorem rowTargets_length (i : Fin 14) : (rowTargets i).length = 185 := targetAt_length i

#print axioms phi_correct
end JSP233.SourcePrefixSpecs208
