module

public import Mathlib.Tactic.IntervalCases
public import Erdos272.Geometry.N82427.PhaseHighChecks82427G00
public import Erdos272.Geometry.N82427.PhaseHighChecks82427G01
public import Erdos272.Geometry.N82427.PhaseHighChecks82427G02
public import Erdos272.Geometry.N82427.PhaseHighChecks82427G03
public import Erdos272.Geometry.N82427.PhaseHighChecks82427G04
public import Erdos272.Geometry.N82427.PhaseHighChecks82427G05
public import Erdos272.Geometry.N82427.PhaseHighChecks82427G06

@[expose] public section

namespace JSP233.PhaseHighFacts82427
open PhaseNumeric82427
set_option autoImplicit false

theorem bound {k : ℕ} (hk : k < 88) : value (data k) ≤ (data k).cap := by
  interval_cases k
  · exact PhaseHighChecks82427G00.checked00
  · exact PhaseHighChecks82427G00.checked01
  · exact PhaseHighChecks82427G00.checked02
  · exact PhaseHighChecks82427G00.checked03
  · exact PhaseHighChecks82427G01.checked04
  · exact PhaseHighChecks82427G01.checked05
  · exact PhaseHighChecks82427G01.checked06
  · exact PhaseHighChecks82427G01.checked07
  · exact PhaseHighChecks82427G01.checked08
  · exact PhaseHighChecks82427G01.checked09
  · exact PhaseHighChecks82427G01.checked10
  · exact PhaseHighChecks82427G01.checked11
  · exact PhaseHighChecks82427G01.checked12
  · exact PhaseHighChecks82427G01.checked13
  · exact PhaseHighChecks82427G01.checked14
  · exact PhaseHighChecks82427G01.checked15
  · exact PhaseHighChecks82427G01.checked16
  · exact PhaseHighChecks82427G01.checked17
  · exact PhaseHighChecks82427G01.checked18
  · exact PhaseHighChecks82427G01.checked19
  · exact PhaseHighChecks82427G02.checked20
  · exact PhaseHighChecks82427G02.checked21
  · exact PhaseHighChecks82427G02.checked22
  · exact PhaseHighChecks82427G02.checked23
  · exact PhaseHighChecks82427G02.checked24
  · exact PhaseHighChecks82427G02.checked25
  · exact PhaseHighChecks82427G02.checked26
  · exact PhaseHighChecks82427G02.checked27
  · exact PhaseHighChecks82427G02.checked28
  · exact PhaseHighChecks82427G02.checked29
  · exact PhaseHighChecks82427G02.checked30
  · exact PhaseHighChecks82427G02.checked31
  · exact PhaseHighChecks82427G02.checked32
  · exact PhaseHighChecks82427G02.checked33
  · exact PhaseHighChecks82427G02.checked34
  · exact PhaseHighChecks82427G02.checked35
  · exact PhaseHighChecks82427G03.checked36
  · exact PhaseHighChecks82427G03.checked37
  · exact PhaseHighChecks82427G03.checked38
  · exact PhaseHighChecks82427G03.checked39
  · exact PhaseHighChecks82427G03.checked40
  · exact PhaseHighChecks82427G03.checked41
  · exact PhaseHighChecks82427G03.checked42
  · exact PhaseHighChecks82427G03.checked43
  · exact PhaseHighChecks82427G03.checked44
  · exact PhaseHighChecks82427G03.checked45
  · exact PhaseHighChecks82427G03.checked46
  · exact PhaseHighChecks82427G03.checked47
  · exact PhaseHighChecks82427G03.checked48
  · exact PhaseHighChecks82427G03.checked49
  · exact PhaseHighChecks82427G03.checked50
  · exact PhaseHighChecks82427G03.checked51
  · exact PhaseHighChecks82427G04.checked52
  · exact PhaseHighChecks82427G04.checked53
  · exact PhaseHighChecks82427G04.checked54
  · exact PhaseHighChecks82427G04.checked55
  · exact PhaseHighChecks82427G04.checked56
  · exact PhaseHighChecks82427G04.checked57
  · exact PhaseHighChecks82427G04.checked58
  · exact PhaseHighChecks82427G04.checked59
  · exact PhaseHighChecks82427G04.checked60
  · exact PhaseHighChecks82427G04.checked61
  · exact PhaseHighChecks82427G04.checked62
  · exact PhaseHighChecks82427G04.checked63
  · exact PhaseHighChecks82427G04.checked64
  · exact PhaseHighChecks82427G04.checked65
  · exact PhaseHighChecks82427G04.checked66
  · exact PhaseHighChecks82427G04.checked67
  · exact PhaseHighChecks82427G05.checked68
  · exact PhaseHighChecks82427G05.checked69
  · exact PhaseHighChecks82427G05.checked70
  · exact PhaseHighChecks82427G05.checked71
  · exact PhaseHighChecks82427G05.checked72
  · exact PhaseHighChecks82427G05.checked73
  · exact PhaseHighChecks82427G05.checked74
  · exact PhaseHighChecks82427G05.checked75
  · exact PhaseHighChecks82427G05.checked76
  · exact PhaseHighChecks82427G05.checked77
  · exact PhaseHighChecks82427G05.checked78
  · exact PhaseHighChecks82427G05.checked79
  · exact PhaseHighChecks82427G05.checked80
  · exact PhaseHighChecks82427G05.checked81
  · exact PhaseHighChecks82427G05.checked82
  · exact PhaseHighChecks82427G05.checked83
  · exact PhaseHighChecks82427G06.checked84
  · exact PhaseHighChecks82427G06.checked85
  · exact PhaseHighChecks82427G06.checked86
  · exact PhaseHighChecks82427G06.checked87

#print axioms bound
end JSP233.PhaseHighFacts82427
