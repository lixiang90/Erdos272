module

public meta import Erdos272.Certificates.TotientPrefixTable
public import Erdos272.Arithmetic.N291012.PrefixChecks291012

@[expose] public section

namespace JSP233.PrefixData291012
set_option maxRecDepth 10000

def Limit : ℕ := 29435

noncomputable def pPack (i : ℕ) : ℕ :=
  totientPrefix32 i

noncomputable def p (n : ℕ) : ℕ :=
  (pPack (n / 32) >>> (32 * (n % 32))) % 4294967296

noncomputable def qPack (i : ℕ) : ℕ :=
  totientMoment48 i

noncomputable def q (n : ℕ) : ℕ :=
  (qPack (n / 32) >>> (48 * (n % 32))) % 281474976710656

end JSP233.PrefixData291012
