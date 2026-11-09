module

public import Erdos272.Arithmetic.N291012.PrefixLookup291012
public import Mathlib.Data.List.Basic

@[expose] public section

/-! Pure arithmetic checks shared by the data certificates and their
source-bound interpretation. -/
namespace JSP233.PrefixLookup291012
def Value (p q : ℕ → ℕ) (s e : ℕ) : ℕ :=
  s * (p s - p (s-e)) - (q s - q (s-e))

end JSP233.PrefixLookup291012

namespace JSP233.PrefixTableSound291012
def Check (p q : ℕ → ℕ) (lo len : ℕ) : Bool :=
  (List.range len).all fun j =>
    let n := lo+j
    decide (p (n+1) = p n + PrefixLookup291012.phi n ∧
      q (n+1) = q n + n * PrefixLookup291012.phi n)

def FloorCheck (p q : ℕ → ℕ) (lo hi e b : ℕ) : Bool :=
  (List.range (hi+1-lo)).all fun j => decide (b ≤ PrefixLookup291012.Value p q (lo+j) e)

end JSP233.PrefixTableSound291012
