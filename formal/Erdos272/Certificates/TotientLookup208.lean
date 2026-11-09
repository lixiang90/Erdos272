module

public import Erdos272.Arithmetic.SourceLookupData208
public import Erdos272.Arithmetic.PrimeCover208
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Small kernel certificates for every original totient recurrence check. -/
namespace JSP233.SourceLookupFast208
open SourceLookupData208
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def blockCheck (lo count : ℕ) : Bool :=
  (List.range count).all (fun r => TotientSieveFast208.checkStepWith
    PrimeCover208.primeCheck phi factor (lo + r))

theorem block_step {lo count r : ℕ} (hc : blockCheck lo count = true)
    (hr : r < count) :
    TotientSieveFast208.checkStepWith PrimeCover208.primeCheck phi factor (lo + r) = true :=
  (List.all_eq_true.mp hc) r (List.mem_range.mpr hr)

private theorem checkedBlock000 : blockCheck 2 256 = true := by decide +kernel

private theorem checkedBlock001 : blockCheck 258 256 = true := by decide +kernel

private theorem checkedBlock002 : blockCheck 514 256 = true := by decide +kernel

private theorem checkedBlock003 : blockCheck 770 256 = true := by decide +kernel

private theorem checkedBlock004 : blockCheck 1026 256 = true := by decide +kernel

private theorem checkedBlock005 : blockCheck 1282 256 = true := by decide +kernel

private theorem checkedBlock006 : blockCheck 1538 256 = true := by decide +kernel

private theorem checkedBlock007 : blockCheck 1794 256 = true := by decide +kernel

private theorem checkedBlock008 : blockCheck 2050 256 = true := by decide +kernel

private theorem checkedBlock009 : blockCheck 2306 256 = true := by decide +kernel

private theorem checkedBlock010 : blockCheck 2562 256 = true := by decide +kernel

private theorem checkedBlock011 : blockCheck 2818 256 = true := by decide +kernel

private theorem checkedBlock012 : blockCheck 3074 256 = true := by decide +kernel

private theorem checkedBlock013 : blockCheck 3330 256 = true := by decide +kernel

private theorem checkedBlock014 : blockCheck 3586 256 = true := by decide +kernel

private theorem checkedBlock015 : blockCheck 3842 256 = true := by decide +kernel

private theorem checkedBlock016 : blockCheck 4098 256 = true := by decide +kernel

private theorem checkedBlock017 : blockCheck 4354 256 = true := by decide +kernel

private theorem checkedBlock018 : blockCheck 4610 256 = true := by decide +kernel

private theorem checkedBlock019 : blockCheck 4866 256 = true := by decide +kernel

private theorem checkedBlock020 : blockCheck 5122 256 = true := by decide +kernel

private theorem checkedBlock021 : blockCheck 5378 256 = true := by decide +kernel

private theorem checkedBlock022 : blockCheck 5634 256 = true := by decide +kernel

private theorem checkedBlock023 : blockCheck 5890 256 = true := by decide +kernel

private theorem checkedBlock024 : blockCheck 6146 256 = true := by decide +kernel

private theorem checkedBlock025 : blockCheck 6402 256 = true := by decide +kernel

private theorem checkedBlock026 : blockCheck 6658 256 = true := by decide +kernel

private theorem checkedBlock027 : blockCheck 6914 256 = true := by decide +kernel

private theorem checkedBlock028 : blockCheck 7170 256 = true := by decide +kernel

private theorem checkedBlock029 : blockCheck 7426 256 = true := by decide +kernel

private theorem checkedBlock030 : blockCheck 7682 256 = true := by decide +kernel

private theorem checkedBlock031 : blockCheck 7938 256 = true := by decide +kernel

private theorem checkedBlock032 : blockCheck 8194 256 = true := by decide +kernel

private theorem checkedBlock033 : blockCheck 8450 256 = true := by decide +kernel

private theorem checkedBlock034 : blockCheck 8706 256 = true := by decide +kernel

private theorem checkedBlock035 : blockCheck 8962 256 = true := by decide +kernel

private theorem checkedBlock036 : blockCheck 9218 256 = true := by decide +kernel

private theorem checkedBlock037 : blockCheck 9474 256 = true := by decide +kernel

private theorem checkedBlock038 : blockCheck 9730 256 = true := by decide +kernel

private theorem checkedBlock039 : blockCheck 9986 256 = true := by decide +kernel

private theorem checkedBlock040 : blockCheck 10242 256 = true := by decide +kernel

private theorem checkedBlock041 : blockCheck 10498 256 = true := by decide +kernel

private theorem checkedBlock042 : blockCheck 10754 256 = true := by decide +kernel

private theorem checkedBlock043 : blockCheck 11010 256 = true := by decide +kernel

private theorem checkedBlock044 : blockCheck 11266 256 = true := by decide +kernel

private theorem checkedBlock045 : blockCheck 11522 256 = true := by decide +kernel

private theorem checkedBlock046 : blockCheck 11778 256 = true := by decide +kernel

private theorem checkedBlock047 : blockCheck 12034 256 = true := by decide +kernel

private theorem checkedBlock048 : blockCheck 12290 256 = true := by decide +kernel

private theorem checkedBlock049 : blockCheck 12546 256 = true := by decide +kernel

private theorem checkedBlock050 : blockCheck 12802 256 = true := by decide +kernel

private theorem checkedBlock051 : blockCheck 13058 256 = true := by decide +kernel

private theorem checkedBlock052 : blockCheck 13314 256 = true := by decide +kernel

private theorem checkedBlock053 : blockCheck 13570 256 = true := by decide +kernel

private theorem checkedBlock054 : blockCheck 13826 256 = true := by decide +kernel

private theorem checkedBlock055 : blockCheck 14082 256 = true := by decide +kernel

private theorem checkedBlock056 : blockCheck 14338 256 = true := by decide +kernel

private theorem checkedBlock057 : blockCheck 14594 256 = true := by decide +kernel

private theorem checkedBlock058 : blockCheck 14850 256 = true := by decide +kernel

private theorem checkedBlock059 : blockCheck 15106 256 = true := by decide +kernel

private theorem checkedBlock060 : blockCheck 15362 256 = true := by decide +kernel

private theorem checkedBlock061 : blockCheck 15618 256 = true := by decide +kernel

private theorem checkedBlock062 : blockCheck 15874 256 = true := by decide +kernel

private theorem checkedBlock063 : blockCheck 16130 256 = true := by decide +kernel

private theorem checkedBlock064 : blockCheck 16386 256 = true := by decide +kernel

private theorem checkedBlock065 : blockCheck 16642 256 = true := by decide +kernel

private theorem checkedBlock066 : blockCheck 16898 256 = true := by decide +kernel

private theorem checkedBlock067 : blockCheck 17154 256 = true := by decide +kernel

private theorem checkedBlock068 : blockCheck 17410 256 = true := by decide +kernel

private theorem checkedBlock069 : blockCheck 17666 256 = true := by decide +kernel

private theorem checkedBlock070 : blockCheck 17922 256 = true := by decide +kernel

private theorem checkedBlock071 : blockCheck 18178 256 = true := by decide +kernel

private theorem checkedBlock072 : blockCheck 18434 256 = true := by decide +kernel

private theorem checkedBlock073 : blockCheck 18690 256 = true := by decide +kernel

private theorem checkedBlock074 : blockCheck 18946 256 = true := by decide +kernel

private theorem checkedBlock075 : blockCheck 19202 256 = true := by decide +kernel

private theorem checkedBlock076 : blockCheck 19458 256 = true := by decide +kernel

private theorem checkedBlock077 : blockCheck 19714 256 = true := by decide +kernel

private theorem checkedBlock078 : blockCheck 19970 256 = true := by decide +kernel

private theorem checkedBlock079 : blockCheck 20226 256 = true := by decide +kernel

private theorem checkedBlock080 : blockCheck 20482 256 = true := by decide +kernel

private theorem checkedBlock081 : blockCheck 20738 256 = true := by decide +kernel

private theorem checkedBlock082 : blockCheck 20994 256 = true := by decide +kernel

private theorem checkedBlock083 : blockCheck 21250 256 = true := by decide +kernel

private theorem checkedBlock084 : blockCheck 21506 256 = true := by decide +kernel

private theorem checkedBlock085 : blockCheck 21762 256 = true := by decide +kernel

private theorem checkedBlock086 : blockCheck 22018 256 = true := by decide +kernel

private theorem checkedBlock087 : blockCheck 22274 256 = true := by decide +kernel

private theorem checkedBlock088 : blockCheck 22530 256 = true := by decide +kernel

private theorem checkedBlock089 : blockCheck 22786 256 = true := by decide +kernel

private theorem checkedBlock090 : blockCheck 23042 256 = true := by decide +kernel

private theorem checkedBlock091 : blockCheck 23298 256 = true := by decide +kernel

private theorem checkedBlock092 : blockCheck 23554 256 = true := by decide +kernel

private theorem checkedBlock093 : blockCheck 23810 256 = true := by decide +kernel

private theorem checkedBlock094 : blockCheck 24066 256 = true := by decide +kernel

private theorem checkedBlock095 : blockCheck 24322 256 = true := by decide +kernel

private theorem checkedBlock096 : blockCheck 24578 256 = true := by decide +kernel

private theorem checkedBlock097 : blockCheck 24834 256 = true := by decide +kernel

private theorem checkedBlock098 : blockCheck 25090 256 = true := by decide +kernel

private theorem checkedBlock099 : blockCheck 25346 256 = true := by decide +kernel

private theorem checkedBlock100 : blockCheck 25602 256 = true := by decide +kernel

private theorem checkedBlock101 : blockCheck 25858 256 = true := by decide +kernel

private theorem checkedBlock102 : blockCheck 26114 256 = true := by decide +kernel

private theorem checkedBlock103 : blockCheck 26370 256 = true := by decide +kernel

private theorem checkedBlock104 : blockCheck 26626 256 = true := by decide +kernel

private theorem checkedBlock105 : blockCheck 26882 256 = true := by decide +kernel

private theorem checkedBlock106 : blockCheck 27138 256 = true := by decide +kernel

private theorem checkedBlock107 : blockCheck 27394 256 = true := by decide +kernel

private theorem checkedBlock108 : blockCheck 27650 256 = true := by decide +kernel

private theorem checkedBlock109 : blockCheck 27906 256 = true := by decide +kernel

private theorem checkedBlock110 : blockCheck 28162 256 = true := by decide +kernel

private theorem checkedBlock111 : blockCheck 28418 256 = true := by decide +kernel

private theorem checkedBlock112 : blockCheck 28674 256 = true := by decide +kernel

private theorem checkedBlock113 : blockCheck 28930 256 = true := by decide +kernel

private theorem checkedBlock114 : blockCheck 29186 256 = true := by decide +kernel

private theorem checkedBlock115 : blockCheck 29442 256 = true := by decide +kernel

private theorem checkedBlock116 : blockCheck 29698 256 = true := by decide +kernel

private theorem checkedBlock117 : blockCheck 29954 256 = true := by decide +kernel

private theorem checkedBlock118 : blockCheck 30210 256 = true := by decide +kernel

private theorem checkedBlock119 : blockCheck 30466 256 = true := by decide +kernel

private theorem checkedBlock120 : blockCheck 30722 256 = true := by decide +kernel

private theorem checkedBlock121 : blockCheck 30978 256 = true := by decide +kernel

private theorem checkedBlock122 : blockCheck 31234 256 = true := by decide +kernel

private theorem checkedBlock123 : blockCheck 31490 256 = true := by decide +kernel

private theorem checkedBlock124 : blockCheck 31746 256 = true := by decide +kernel

private theorem checkedBlock125 : blockCheck 32002 256 = true := by decide +kernel

private theorem checkedBlock126 : blockCheck 32258 256 = true := by decide +kernel

private theorem checkedBlock127 : blockCheck 32514 240 = true := by decide +kernel

theorem blocks_checked (b : Fin 128) :
    blockCheck (b.val * 256 + 2) (min 256 (Limit - 1 - b.val * 256)) = true := by
  fin_cases b
  · exact checkedBlock000
  · exact checkedBlock001
  · exact checkedBlock002
  · exact checkedBlock003
  · exact checkedBlock004
  · exact checkedBlock005
  · exact checkedBlock006
  · exact checkedBlock007
  · exact checkedBlock008
  · exact checkedBlock009
  · exact checkedBlock010
  · exact checkedBlock011
  · exact checkedBlock012
  · exact checkedBlock013
  · exact checkedBlock014
  · exact checkedBlock015
  · exact checkedBlock016
  · exact checkedBlock017
  · exact checkedBlock018
  · exact checkedBlock019
  · exact checkedBlock020
  · exact checkedBlock021
  · exact checkedBlock022
  · exact checkedBlock023
  · exact checkedBlock024
  · exact checkedBlock025
  · exact checkedBlock026
  · exact checkedBlock027
  · exact checkedBlock028
  · exact checkedBlock029
  · exact checkedBlock030
  · exact checkedBlock031
  · exact checkedBlock032
  · exact checkedBlock033
  · exact checkedBlock034
  · exact checkedBlock035
  · exact checkedBlock036
  · exact checkedBlock037
  · exact checkedBlock038
  · exact checkedBlock039
  · exact checkedBlock040
  · exact checkedBlock041
  · exact checkedBlock042
  · exact checkedBlock043
  · exact checkedBlock044
  · exact checkedBlock045
  · exact checkedBlock046
  · exact checkedBlock047
  · exact checkedBlock048
  · exact checkedBlock049
  · exact checkedBlock050
  · exact checkedBlock051
  · exact checkedBlock052
  · exact checkedBlock053
  · exact checkedBlock054
  · exact checkedBlock055
  · exact checkedBlock056
  · exact checkedBlock057
  · exact checkedBlock058
  · exact checkedBlock059
  · exact checkedBlock060
  · exact checkedBlock061
  · exact checkedBlock062
  · exact checkedBlock063
  · exact checkedBlock064
  · exact checkedBlock065
  · exact checkedBlock066
  · exact checkedBlock067
  · exact checkedBlock068
  · exact checkedBlock069
  · exact checkedBlock070
  · exact checkedBlock071
  · exact checkedBlock072
  · exact checkedBlock073
  · exact checkedBlock074
  · exact checkedBlock075
  · exact checkedBlock076
  · exact checkedBlock077
  · exact checkedBlock078
  · exact checkedBlock079
  · exact checkedBlock080
  · exact checkedBlock081
  · exact checkedBlock082
  · exact checkedBlock083
  · exact checkedBlock084
  · exact checkedBlock085
  · exact checkedBlock086
  · exact checkedBlock087
  · exact checkedBlock088
  · exact checkedBlock089
  · exact checkedBlock090
  · exact checkedBlock091
  · exact checkedBlock092
  · exact checkedBlock093
  · exact checkedBlock094
  · exact checkedBlock095
  · exact checkedBlock096
  · exact checkedBlock097
  · exact checkedBlock098
  · exact checkedBlock099
  · exact checkedBlock100
  · exact checkedBlock101
  · exact checkedBlock102
  · exact checkedBlock103
  · exact checkedBlock104
  · exact checkedBlock105
  · exact checkedBlock106
  · exact checkedBlock107
  · exact checkedBlock108
  · exact checkedBlock109
  · exact checkedBlock110
  · exact checkedBlock111
  · exact checkedBlock112
  · exact checkedBlock113
  · exact checkedBlock114
  · exact checkedBlock115
  · exact checkedBlock116
  · exact checkedBlock117
  · exact checkedBlock118
  · exact checkedBlock119
  · exact checkedBlock120
  · exact checkedBlock121
  · exact checkedBlock122
  · exact checkedBlock123
  · exact checkedBlock124
  · exact checkedBlock125
  · exact checkedBlock126
  · exact checkedBlock127

#print axioms block_step
#print axioms blocks_checked
end JSP233.SourceLookupFast208
