module

public import Erdos272.Arithmetic.N200000.ExactResponse200000

@[expose] public section

namespace JSP233.WindowData158375
noncomputable section
set_option autoImplicit false

structure Info where
  low : ℕ
  high : ℕ
  memberFloor : ℕ

def info (w : ℕ) : Info :=
  if w=0 then ⟨158375,166000,120⟩ else if w=1 then ⟨166001,170999,122⟩ else ⟨171000,179999,124⟩

def G (w : ℕ) : ℝ :=
  if w=0 then (1/805584 : ℝ) else if w=1 then (1/859464 : ℝ) else (1/873324 : ℝ)

def CoeffA (w : ℕ) : ℝ :=
  if w=0 then (1723105322067509/134264000000000000 : ℝ) else if w=1 then (151076813043281/11937000000000000 : ℝ) else (301555525204083/24259000000000000 : ℝ)

def CoeffB (w : ℕ) : ℝ :=
  if w=0 then (1358875015711759627561/187969600000000000 : ℝ) else if w=1 then (815947845770838976999/100270800000000000 : ℝ) else (169980162752241702639/21226625000000000 : ℝ)

def CoeffC (w : ℕ) : ℝ :=
  if w=0 then (66609080166197/134264 : ℝ) else if w=1 then (69114079702187/143244 : ℝ) else (13806377402367/24259 : ℝ)

def HCommon : ℝ := 5107/400
def Fee (w N : ℕ) : ℝ := CoeffA w*(N:ℝ)^2+CoeffB w*N+CoeffC w
def SmallCount (w : ℕ) : ℕ := ((info w).memberFloor-2)^2+((info w).memberFloor-1)

theorem cover {N : ℕ} (hlo : 158375 ≤ N) (hhi : N ≤ 179999) :
    ∃ w : ℕ, w < 3 ∧ (info w).low ≤ N ∧ N ≤ (info w).high := by
  by_cases h0 : N ≤ 166000
  · exact ⟨0, by decide, by simpa [info] using hlo, by simpa [info] using h0⟩
  by_cases h1 : N ≤ 170999
  · exact ⟨1, by decide, by simp [info]; omega, by simpa [info] using h1⟩
  · exact ⟨2, by decide, by simp [info]; omega, by simpa [info] using hhi⟩
#print axioms cover

end
end JSP233.WindowData158375
