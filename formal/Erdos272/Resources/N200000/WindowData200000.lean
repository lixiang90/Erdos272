module

public import Erdos272.Resources.N200000.SourceData200000W0
public import Erdos272.Resources.N200000.SourceData200000W1
public import Erdos272.Resources.N200000.SourceData200000W2
public import Erdos272.Arithmetic.N200000.ExactResponse200000

@[expose] public section

namespace JSP233.WindowData200000
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
structure Info where
  low : ℕ
  high : ℕ
  memberFloor : ℕ
def info (w : ℕ) : Info :=
  if w=0 then ⟨200000,210000,134⟩ else if w=1 then ⟨210001,220000,137⟩ else ⟨220001,233810,140⟩
def HCommon : ℝ := 5271/400
def G (w : ℕ) : ℝ := if w=0 then SourceData200000W0.G else if w=1 then SourceData200000W1.G else SourceData200000W2.G
def Fee (w : ℕ) : ℝ := if w=0 then SourceData200000W0.SourceUpper 210000 else if w=1 then SourceData200000W1.SourceUpper 220000 else SourceData200000W2.SourceUpper 233810
def Loss : ℝ := 594+289/2+HCommon
def SmallCount (w : ℕ) : ℕ := ((info w).memberFloor-2)^2+((info w).memberFloor-1)
def PayMargin (w : ℕ) (n : ℝ) : ℝ := ExactResponse200000.Margin (271/800) (G w) Loss (Fee w+1/(432*(G w)^2)+1295) n
structure Gates (w : ℕ) : Prop where
  low_bound : 200000 ≤ (info w).low
  low_high : (info w).low ≤ (info w).high
  high_bound : (info w).high ≤ 233810
  member_three : 3 ≤ (info w).memberFloor
  g_positive : 0 < G w
  chord : (271/800 : ℝ) ≤ G w*(2*(info w).low+(info w).high-3)
  low_gap : 0 < PayMargin w (info w).low
  high_gap : 0 < PayMargin w (info w).high
  small_gap : 0 < (71/800 : ℝ)*(info w).low-((SmallCount w : ℝ)+289/2+HCommon)-1296/(info w).low

theorem gate0 : Gates 0 := by constructor <;> norm_num [info, HCommon, G, Fee, Loss, SmallCount, PayMargin, ExactResponse200000.Margin, SourceData200000W0.G, SourceData200000W0.SourceUpper, SourceData200000W0.CoeffA, SourceData200000W0.CoeffB, SourceData200000W0.CoeffC, SourceData200000W1.G, SourceData200000W1.SourceUpper, SourceData200000W1.CoeffA, SourceData200000W1.CoeffB, SourceData200000W1.CoeffC, SourceData200000W2.G, SourceData200000W2.SourceUpper, SourceData200000W2.CoeffA, SourceData200000W2.CoeffB, SourceData200000W2.CoeffC]
#print axioms gate0

theorem gate1 : Gates 1 := by constructor <;> norm_num [info, HCommon, G, Fee, Loss, SmallCount, PayMargin, ExactResponse200000.Margin, SourceData200000W0.G, SourceData200000W0.SourceUpper, SourceData200000W0.CoeffA, SourceData200000W0.CoeffB, SourceData200000W0.CoeffC, SourceData200000W1.G, SourceData200000W1.SourceUpper, SourceData200000W1.CoeffA, SourceData200000W1.CoeffB, SourceData200000W1.CoeffC, SourceData200000W2.G, SourceData200000W2.SourceUpper, SourceData200000W2.CoeffA, SourceData200000W2.CoeffB, SourceData200000W2.CoeffC]
#print axioms gate1

theorem gate2 : Gates 2 := by constructor <;> norm_num [info, HCommon, G, Fee, Loss, SmallCount, PayMargin, ExactResponse200000.Margin, SourceData200000W0.G, SourceData200000W0.SourceUpper, SourceData200000W0.CoeffA, SourceData200000W0.CoeffB, SourceData200000W0.CoeffC, SourceData200000W1.G, SourceData200000W1.SourceUpper, SourceData200000W1.CoeffA, SourceData200000W1.CoeffB, SourceData200000W1.CoeffC, SourceData200000W2.G, SourceData200000W2.SourceUpper, SourceData200000W2.CoeffA, SourceData200000W2.CoeffB, SourceData200000W2.CoeffC]
#print axioms gate2

theorem gates {w : ℕ} (hw : w < 3) : Gates w := by
  interval_cases w
  · exact gate0
  · exact gate1
  · exact gate2
theorem cover {N : ℕ} (hlo : 200000 ≤ N) (hhi : N ≤ 233810) :
    ∃ w : ℕ, w < 3 ∧ (info w).low ≤ N ∧ N ≤ (info w).high := by
  by_cases h0 : N ≤ 210000
  · exact ⟨0, by decide, by simpa [info] using hlo, by simpa [info] using h0⟩
  by_cases h1 : N ≤ 220000
  · exact ⟨1, by decide, by simp [info]; omega, by simpa [info] using h1⟩
  · exact ⟨2, by decide, by simp [info]; omega, by simpa [info] using hhi⟩
#print axioms gates
#print axioms cover
end
end JSP233.WindowData200000
