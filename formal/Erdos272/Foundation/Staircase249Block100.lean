import Erdos272.Foundation.Staircase249Data
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

namespace JSP233.Staircase249Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem checkedRow100 : Block 100 1 := by
  constructor <;> decide +kernel

private theorem checkedRow101 : Block 101 1 := by
  constructor <;> decide +kernel

private theorem checkedRow102 : Block 102 1 := by
  constructor <;> decide +kernel

private theorem checkedRow103 : Block 103 1 := by
  constructor <;> decide +kernel

private theorem checkedRow104 : Block 104 1 := by
  constructor <;> decide +kernel

private theorem checkedRow105 : Block 105 1 := by
  constructor <;> decide +kernel

private theorem checkedRow106 : Block 106 1 := by
  constructor <;> decide +kernel

private theorem checkedRow107 : Block 107 1 := by
  constructor <;> decide +kernel

private theorem checkedRow108 : Block 108 1 := by
  constructor <;> decide +kernel

private theorem checkedRow109 : Block 109 1 := by
  constructor <;> decide +kernel

private theorem checkedRow110 : Block 110 1 := by
  constructor <;> decide +kernel

private theorem checkedRow111 : Block 111 1 := by
  constructor <;> decide +kernel

private theorem checkedRow112 : Block 112 1 := by
  constructor <;> decide +kernel

private theorem checkedRow113 : Block 113 1 := by
  constructor <;> decide +kernel

private theorem checkedRow114 : Block 114 1 := by
  constructor <;> decide +kernel

private theorem checkedRow115 : Block 115 1 := by
  constructor <;> decide +kernel

private theorem checkedRow116 : Block 116 1 := by
  constructor <;> decide +kernel

private theorem checkedRow117 : Block 117 1 := by
  constructor <;> decide +kernel

private theorem checkedRow118 : Block 118 1 := by
  constructor <;> decide +kernel

private theorem checkedRow119 : Block 119 1 := by
  constructor <;> decide +kernel

private theorem checkedRow120 : Block 120 1 := by
  constructor <;> decide +kernel

private theorem checkedRow121 : Block 121 1 := by
  constructor <;> decide +kernel

private theorem checkedRow122 : Block 122 1 := by
  constructor <;> decide +kernel

private theorem checkedRow123 : Block 123 1 := by
  constructor <;> decide +kernel

private theorem checkedRow124 : Block 124 1 := by
  constructor <;> decide +kernel

theorem block100 : Block 100 25 := by
  apply Block.ofRows
  intro r
  fin_cases r
  · exact checkedRow100
  · exact checkedRow101
  · exact checkedRow102
  · exact checkedRow103
  · exact checkedRow104
  · exact checkedRow105
  · exact checkedRow106
  · exact checkedRow107
  · exact checkedRow108
  · exact checkedRow109
  · exact checkedRow110
  · exact checkedRow111
  · exact checkedRow112
  · exact checkedRow113
  · exact checkedRow114
  · exact checkedRow115
  · exact checkedRow116
  · exact checkedRow117
  · exact checkedRow118
  · exact checkedRow119
  · exact checkedRow120
  · exact checkedRow121
  · exact checkedRow122
  · exact checkedRow123
  · exact checkedRow124

#print axioms block100
end JSP233.Staircase249Data
