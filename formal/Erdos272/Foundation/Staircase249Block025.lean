import Erdos272.Foundation.Staircase249Data
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

namespace JSP233.Staircase249Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem checkedRow025 : Block 25 1 := by
  constructor <;> decide +kernel

private theorem checkedRow026 : Block 26 1 := by
  constructor <;> decide +kernel

private theorem checkedRow027 : Block 27 1 := by
  constructor <;> decide +kernel

private theorem checkedRow028 : Block 28 1 := by
  constructor <;> decide +kernel

private theorem checkedRow029 : Block 29 1 := by
  constructor <;> decide +kernel

private theorem checkedRow030 : Block 30 1 := by
  constructor <;> decide +kernel

private theorem checkedRow031 : Block 31 1 := by
  constructor <;> decide +kernel

private theorem checkedRow032 : Block 32 1 := by
  constructor <;> decide +kernel

private theorem checkedRow033 : Block 33 1 := by
  constructor <;> decide +kernel

private theorem checkedRow034 : Block 34 1 := by
  constructor <;> decide +kernel

private theorem checkedRow035 : Block 35 1 := by
  constructor <;> decide +kernel

private theorem checkedRow036 : Block 36 1 := by
  constructor <;> decide +kernel

private theorem checkedRow037 : Block 37 1 := by
  constructor <;> decide +kernel

private theorem checkedRow038 : Block 38 1 := by
  constructor <;> decide +kernel

private theorem checkedRow039 : Block 39 1 := by
  constructor <;> decide +kernel

private theorem checkedRow040 : Block 40 1 := by
  constructor <;> decide +kernel

private theorem checkedRow041 : Block 41 1 := by
  constructor <;> decide +kernel

private theorem checkedRow042 : Block 42 1 := by
  constructor <;> decide +kernel

private theorem checkedRow043 : Block 43 1 := by
  constructor <;> decide +kernel

private theorem checkedRow044 : Block 44 1 := by
  constructor <;> decide +kernel

private theorem checkedRow045 : Block 45 1 := by
  constructor <;> decide +kernel

private theorem checkedRow046 : Block 46 1 := by
  constructor <;> decide +kernel

private theorem checkedRow047 : Block 47 1 := by
  constructor <;> decide +kernel

private theorem checkedRow048 : Block 48 1 := by
  constructor <;> decide +kernel

private theorem checkedRow049 : Block 49 1 := by
  constructor <;> decide +kernel

theorem block025 : Block 25 25 := by
  apply Block.ofRows
  intro r
  fin_cases r
  · exact checkedRow025
  · exact checkedRow026
  · exact checkedRow027
  · exact checkedRow028
  · exact checkedRow029
  · exact checkedRow030
  · exact checkedRow031
  · exact checkedRow032
  · exact checkedRow033
  · exact checkedRow034
  · exact checkedRow035
  · exact checkedRow036
  · exact checkedRow037
  · exact checkedRow038
  · exact checkedRow039
  · exact checkedRow040
  · exact checkedRow041
  · exact checkedRow042
  · exact checkedRow043
  · exact checkedRow044
  · exact checkedRow045
  · exact checkedRow046
  · exact checkedRow047
  · exact checkedRow048
  · exact checkedRow049

#print axioms block025
end JSP233.Staircase249Data
