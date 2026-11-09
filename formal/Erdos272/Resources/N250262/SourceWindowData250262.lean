module

public import Erdos272.Arithmetic.N250262.RowGeometry250262
public import Erdos272.Arithmetic.N291012.ShadowResponse291012

@[expose] public section

namespace JSP233.SourceWindowData250262
open CleanupRows250262
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

structure Info where
  low : ℕ
  high : ℕ
  memberFloor : ℕ
  lastPotential : ℕ
  fee : ℕ

def info00 : Info := ⟨251008, 261008, 150, 237924, 5172917334⟩

def info01 : Info := ⟨261009, 271009, 153, 248404, 5411644326⟩

def info02 : Info := ⟨271010, 281010, 156, 258232, 5641932865⟩

def info03 : Info := ⟨281011, 291011, 158, 263600, 5900724730⟩

def info (w : ℕ) : Info := match w with
  | 0 => info00
  | 1 => info01
  | 2 => info02
  | 3 => info03
  | _ => info00

def potential (w n : ℕ) : ℕ :=
  if n=0 then 0 else (data (7*w+min (n-1) 6)).potential

def Psi (w n : ℕ) : ℝ := potential w n

def G (w : ℕ) : ℝ := 1/(6*((info w).lastPotential : ℝ))

theorem links {w i : ℕ} (hw : w < 4) (hi : i < 7) :
    7*w+i < 28 ∧ (data (7*w+i)).row.low = (info w).low ∧
    (data (7*w+i)).row.high = (info w).high ∧
    (data (7*w+i)).memberFloor = (info w).memberFloor ∧
    potential w (i+1) = (data (7*w+i)).potential := by
  interval_cases w <;> interval_cases i <;> decide +kernel

theorem psi_mono {w : ℕ} (hw : w < 4) : Monotone (Psi w) := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n < 7
  · have hh : potential w n ≤ potential w (n+1) := by
      interval_cases w <;> interval_cases n <;> decide +kernel
    dsimp only [Psi]
    exact_mod_cast hh
  · have h0 : n ≠ 0 := by omega
    have h1 : n+1 ≠ 0 := by omega
    have hm0 : min (n-1) 6 = 6 := by omega
    have hm1 : min (n+1-1) 6 = 6 := by omega
    simp only [Psi, potential, if_neg h0, if_neg h1, hm0, hm1, le_refl]

theorem psi_zero (w : ℕ) : Psi w 0 = 0 := by simp [Psi, potential]

theorem reciprocal {w : ℕ} (hw : w < 4) : 6*G w*Psi w 7 = 1 := by
  interval_cases w <;> norm_num [G, Psi, potential, info,info00, info01, info02, info03, data,data06, data13, data20, data27]


theorem g_positive {w : ℕ} (hw : w < 4) : 0 < G w := by
  interval_cases w <;> norm_num [G, info, info00, info01, info02, info03]

theorem intervals {w : ℕ} (hw : w < 4) :
    (info w).low ≤ (info w).high ∧ (info w).high ≤ 291011 := by
  interval_cases w <;> decide

#print axioms links
#print axioms psi_mono
#print axioms psi_zero
#print axioms reciprocal
#print axioms g_positive
#print axioms intervals
end
end JSP233.SourceWindowData250262
