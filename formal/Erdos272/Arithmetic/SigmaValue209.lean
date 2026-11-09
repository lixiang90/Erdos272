module

public import Erdos272.Arithmetic.ComputedSigma209
public import Erdos272.Arithmetic.SigmaBaseData209
public import Erdos272.Arithmetic.FastFullLookup209
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section
namespace JSP233.SigmaValue209
set_option maxHeartbeats 0

def value (n : Nat) : Nat :=
  ComputedSigma209.fastValue SigmaBaseData209.value FastFullLookup209.factor 6 n

theorem correct
    (hbase : ∀ n,n≤32753 → SigmaBaseData209.value n=SigmaSieve209.sigmaOne n)
    (hfactor : ∀ n,32753<n → n≤1670000 →
      (FactorFullData209.factor n=0 → n.Prime) ∧
      (FactorFullData209.factor n≠0 → (FactorFullData209.factor n).Prime ∧ FactorFullData209.factor n∣n))
    (n : Nat) (hn : n≤1670000) : value n=SigmaSieve209.sigmaOne n := by
  unfold value
  rw [ComputedSigma209.fastValue_eq]
  have hfac : ∀ m,32753<m → m≤1670000 →
      (FastFullLookup209.factor m=0 → m.Prime) ∧
      (FastFullLookup209.factor m≠0 → (FastFullLookup209.factor m).Prime ∧ FastFullLookup209.factor m∣m) := by
    intro m hm hmH
    simpa only [FastFullLookup209.factor_eq] using hfactor m hm hmH
  exact ComputedSigma209.correct hbase hfac 6 n hn (by norm_num;omega)

#print axioms correct
end JSP233.SigmaValue209

