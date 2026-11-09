module

public import Erdos272.Arithmetic.TotientWords208

@[expose] public section

/-! Arithmetic lookup data for the prefix certificates. The lookup uses
the shared canonical words in TotientWords208. The theory module proves
identity with the established totient lookup. -/
namespace JSP233.PrefixLookup291012
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def phi (n : ℕ) : ℕ :=
  (SourceLookupData208.phiPack (n / 64) / 2 ^ (16 * (n % 64))) % 65536

end JSP233.PrefixLookup291012
