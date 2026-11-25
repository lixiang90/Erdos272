module

public import Erdos272.Arithmetic.FactorFullData209

@[expose] public section
namespace JSP233.FastFullLookup209
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def codePack (i : Nat) : Nat := packNode_0 i
theorem codePack_eq (i : Nat) : codePack i = FactorFullData209.codePack i := by rfl
def code (n : Nat) : Nat := (codePack (n / 128) / FactorFullData209.denominator ((n % 128) / 2)) % 256
theorem code_eq (n : Nat) : code n = FactorFullData209.code n := by
  simp only [code, FactorFullData209.code, codePack_eq]
def tailFactor (n : Nat) : Nat :=
  match code n with
  | 0 => 0
  | i + 1 => FactorFullData209.primeAt (i + 1)
theorem tailFactor_eq (n : Nat) : tailFactor n = FactorFullData209.tailFactor n := by
  simp only [tailFactor, FactorFullData209.tailFactor, code_eq]
  rfl
def factor (n : Nat) : Nat :=
  if n % 2 = 0 then 2 else
  if n % 3 = 0 then 3 else
  if n % 5 = 0 then 5 else
  if n % 7 = 0 then 7 else
  if n % 11 = 0 then 11 else
  if n % 13 = 0 then 13 else tailFactor n
theorem factor_eq (n : Nat) : factor n = FactorFullData209.factor n := by
  simp only [factor, FactorFullData209.factor, tailFactor_eq]
def marked (n : Nat) : Bool := decide (factor n ≠ 0)
theorem marked_eq (n : Nat) : marked n = FactorFullData209.marked n := by
  simp only [marked, FactorFullData209.marked, factor_eq]
#print axioms codePack_eq
#print axioms factor_eq
end JSP233.FastFullLookup209
