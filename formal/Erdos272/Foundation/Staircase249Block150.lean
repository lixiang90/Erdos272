import Erdos272.Foundation.Staircase249Data
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

namespace JSP233.Staircase249Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem checkedRow150 : Block 150 1 := by
  constructor <;> decide +kernel

private theorem checkedRow151 : Block 151 1 := by
  constructor <;> decide +kernel

private theorem checkedRow152 : Block 152 1 := by
  constructor <;> decide +kernel

private theorem checkedRow153 : Block 153 1 := by
  constructor <;> decide +kernel

private theorem checkedRow154 : Block 154 1 := by
  constructor <;> decide +kernel

private theorem checkedRow155 : Block 155 1 := by
  constructor <;> decide +kernel

private theorem checkedRow156 : Block 156 1 := by
  constructor <;> decide +kernel

private theorem checkedRow157 : Block 157 1 := by
  constructor <;> decide +kernel

private theorem checkedRow158 : Block 158 1 := by
  constructor <;> decide +kernel

private theorem checkedRow159 : Block 159 1 := by
  constructor <;> decide +kernel

private theorem checkedRow160 : Block 160 1 := by
  constructor <;> decide +kernel

private theorem checkedRow161 : Block 161 1 := by
  constructor <;> decide +kernel

private theorem checkedRow162 : Block 162 1 := by
  constructor <;> decide +kernel

private theorem checkedRow163 : Block 163 1 := by
  constructor <;> decide +kernel

private theorem checkedRow164 : Block 164 1 := by
  constructor <;> decide +kernel

private theorem checkedRow165 : Block 165 1 := by
  constructor <;> decide +kernel

private theorem checkedRow166 : Block 166 1 := by
  constructor <;> decide +kernel

private theorem checkedRow167 : Block 167 1 := by
  constructor <;> decide +kernel

private theorem checkedRow168 : Block 168 1 := by
  constructor <;> decide +kernel

private theorem checkedRow169 : Block 169 1 := by
  constructor <;> decide +kernel

private theorem checkedRow170 : Block 170 1 := by
  constructor <;> decide +kernel

private theorem checkedRow171 : Block 171 1 := by
  constructor <;> decide +kernel

private theorem checkedRow172 : Block 172 1 := by
  constructor <;> decide +kernel

private theorem checkedRow173 : Block 173 1 := by
  constructor <;> decide +kernel

private theorem checkedRow174 : Block 174 1 := by
  constructor <;> decide +kernel

theorem block150 : Block 150 25 := by
  apply Block.ofRows
  intro r
  fin_cases r
  · exact checkedRow150
  · exact checkedRow151
  · exact checkedRow152
  · exact checkedRow153
  · exact checkedRow154
  · exact checkedRow155
  · exact checkedRow156
  · exact checkedRow157
  · exact checkedRow158
  · exact checkedRow159
  · exact checkedRow160
  · exact checkedRow161
  · exact checkedRow162
  · exact checkedRow163
  · exact checkedRow164
  · exact checkedRow165
  · exact checkedRow166
  · exact checkedRow167
  · exact checkedRow168
  · exact checkedRow169
  · exact checkedRow170
  · exact checkedRow171
  · exact checkedRow172
  · exact checkedRow173
  · exact checkedRow174

#print axioms block150
end JSP233.Staircase249Data
