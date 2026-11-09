module

public import Erdos272.Foundation.Staircase249Data
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace JSP233.Staircase249Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem checkedRow000 : Block 0 1 := by
  constructor <;> decide +kernel

private theorem checkedRow001 : Block 1 1 := by
  constructor <;> decide +kernel

private theorem checkedRow002 : Block 2 1 := by
  constructor <;> decide +kernel

private theorem checkedRow003 : Block 3 1 := by
  constructor <;> decide +kernel

private theorem checkedRow004 : Block 4 1 := by
  constructor <;> decide +kernel

private theorem checkedRow005 : Block 5 1 := by
  constructor <;> decide +kernel

private theorem checkedRow006 : Block 6 1 := by
  constructor <;> decide +kernel

private theorem checkedRow007 : Block 7 1 := by
  constructor <;> decide +kernel

private theorem checkedRow008 : Block 8 1 := by
  constructor <;> decide +kernel

private theorem checkedRow009 : Block 9 1 := by
  constructor <;> decide +kernel

private theorem checkedRow010 : Block 10 1 := by
  constructor <;> decide +kernel

private theorem checkedRow011 : Block 11 1 := by
  constructor <;> decide +kernel

private theorem checkedRow012 : Block 12 1 := by
  constructor <;> decide +kernel

private theorem checkedRow013 : Block 13 1 := by
  constructor <;> decide +kernel

private theorem checkedRow014 : Block 14 1 := by
  constructor <;> decide +kernel

private theorem checkedRow015 : Block 15 1 := by
  constructor <;> decide +kernel

private theorem checkedRow016 : Block 16 1 := by
  constructor <;> decide +kernel

private theorem checkedRow017 : Block 17 1 := by
  constructor <;> decide +kernel

private theorem checkedRow018 : Block 18 1 := by
  constructor <;> decide +kernel

private theorem checkedRow019 : Block 19 1 := by
  constructor <;> decide +kernel

private theorem checkedRow020 : Block 20 1 := by
  constructor <;> decide +kernel

private theorem checkedRow021 : Block 21 1 := by
  constructor <;> decide +kernel

private theorem checkedRow022 : Block 22 1 := by
  constructor <;> decide +kernel

private theorem checkedRow023 : Block 23 1 := by
  constructor <;> decide +kernel

private theorem checkedRow024 : Block 24 1 := by
  constructor <;> decide +kernel

theorem block000 : Block 0 25 := by
  apply Block.ofRows
  intro r
  fin_cases r
  · exact checkedRow000
  · exact checkedRow001
  · exact checkedRow002
  · exact checkedRow003
  · exact checkedRow004
  · exact checkedRow005
  · exact checkedRow006
  · exact checkedRow007
  · exact checkedRow008
  · exact checkedRow009
  · exact checkedRow010
  · exact checkedRow011
  · exact checkedRow012
  · exact checkedRow013
  · exact checkedRow014
  · exact checkedRow015
  · exact checkedRow016
  · exact checkedRow017
  · exact checkedRow018
  · exact checkedRow019
  · exact checkedRow020
  · exact checkedRow021
  · exact checkedRow022
  · exact checkedRow023
  · exact checkedRow024

#print axioms block000
end JSP233.Staircase249Data
