module

public import Erdos272.Foundation.Staircase249Data
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace JSP233.Staircase249Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem checkedRow200 : Block 200 1 := by
  constructor <;> decide +kernel

private theorem checkedRow201 : Block 201 1 := by
  constructor <;> decide +kernel

private theorem checkedRow202 : Block 202 1 := by
  constructor <;> decide +kernel

private theorem checkedRow203 : Block 203 1 := by
  constructor <;> decide +kernel

private theorem checkedRow204 : Block 204 1 := by
  constructor <;> decide +kernel

private theorem checkedRow205 : Block 205 1 := by
  constructor <;> decide +kernel

private theorem checkedRow206 : Block 206 1 := by
  constructor <;> decide +kernel

private theorem checkedRow207 : Block 207 1 := by
  constructor <;> decide +kernel

private theorem checkedRow208 : Block 208 1 := by
  constructor <;> decide +kernel

private theorem checkedRow209 : Block 209 1 := by
  constructor <;> decide +kernel

private theorem checkedRow210 : Block 210 1 := by
  constructor <;> decide +kernel

private theorem checkedRow211 : Block 211 1 := by
  constructor <;> decide +kernel

private theorem checkedRow212 : Block 212 1 := by
  constructor <;> decide +kernel

private theorem checkedRow213 : Block 213 1 := by
  constructor <;> decide +kernel

private theorem checkedRow214 : Block 214 1 := by
  constructor <;> decide +kernel

private theorem checkedRow215 : Block 215 1 := by
  constructor <;> decide +kernel

private theorem checkedRow216 : Block 216 1 := by
  constructor <;> decide +kernel

private theorem checkedRow217 : Block 217 1 := by
  constructor <;> decide +kernel

private theorem checkedRow218 : Block 218 1 := by
  constructor <;> decide +kernel

private theorem checkedRow219 : Block 219 1 := by
  constructor <;> decide +kernel

private theorem checkedRow220 : Block 220 1 := by
  constructor <;> decide +kernel

private theorem checkedRow221 : Block 221 1 := by
  constructor <;> decide +kernel

private theorem checkedRow222 : Block 222 1 := by
  constructor <;> decide +kernel

private theorem checkedRow223 : Block 223 1 := by
  constructor <;> decide +kernel

private theorem checkedRow224 : Block 224 1 := by
  constructor <;> decide +kernel

theorem block200 : Block 200 25 := by
  apply Block.ofRows
  intro r
  fin_cases r
  · exact checkedRow200
  · exact checkedRow201
  · exact checkedRow202
  · exact checkedRow203
  · exact checkedRow204
  · exact checkedRow205
  · exact checkedRow206
  · exact checkedRow207
  · exact checkedRow208
  · exact checkedRow209
  · exact checkedRow210
  · exact checkedRow211
  · exact checkedRow212
  · exact checkedRow213
  · exact checkedRow214
  · exact checkedRow215
  · exact checkedRow216
  · exact checkedRow217
  · exact checkedRow218
  · exact checkedRow219
  · exact checkedRow220
  · exact checkedRow221
  · exact checkedRow222
  · exact checkedRow223
  · exact checkedRow224

#print axioms block200
end JSP233.Staircase249Data
