module

public import Erdos272.Counting.N158375.LightSlope158375
public import Erdos272.Arithmetic.N118533.ClassCertificates118533
public import Erdos272.Arithmetic.N118533.CleanupRows118533
public import Erdos272.Arithmetic.CleanupMachineSound208

@[expose] public section

namespace JSP233.RowLightSlope118533
open CleanupRows118533 CleanupEval208 CleanupMachineSound208 ActualCleanupEval208
open LightFamily158375 LightSlope158375 ClassCertificates118533
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

local instance (b : CleanupEval208.Band) : Decidable (Shape b) :=
  inferInstanceAs (Decidable (b.E ≤ b.T ∧ b.T < b.U ∧ 2 ≤ b.b2 ∧ 2 ≤ b.b3 ∧
    2 ≤ b.b5 ∧ 2 ≤ b.b7 ∧ 2 ≤ b.b11))

local instance (high D : ℕ) (b : CleanupEval208.Band) (t : Term) :
    Decidable (TermFacts high D b t) :=
  inferInstanceAs (Decidable (0 < t.q ∧ high/t.q ≤ D ∧
    t.q = b.T-b.E+((t.q-(b.T-b.E))/OwnerBlock b t.p)*OwnerBlock b t.p))

local instance (high D : ℕ) (b : CleanupEval208.Band) (ts : Finset Term) :
    Decidable (BandFacts high D b ts) :=
  inferInstanceAs (Decidable (Shape b ∧ (b.E ≤ 1 → ts=∅) ∧
    (∀ t ∈ ts, ∀ u ∈ ts, t.p=u.p → t.q=u.q → t=u) ∧
    ∀ t ∈ ts, TermFacts high D b t))

def row (k : ℕ) : Row := toRow (data k).row

theorem length {k : ℕ} (hk : k < 21) : (row k).bands.length=7 := by
  interval_cases k <;> rfl

def terms (k : ℕ) (b : CrossBandCredit208.Band) : Finset Term :=
  match k, b.val with
  | 0, 0 => {⟨2, 100, 5⟩, ⟨2, 197, 1⟩, ⟨3, 100, 1⟩, ⟨11, 100, 1⟩}
  | 1, 0 => {⟨2, 94, 6⟩, ⟨2, 179, 1⟩, ⟨3, 94, 2⟩, ⟨11, 94, 1⟩}
  | 1, 1 => {⟨2, 206, 1⟩}
  | 2, 0 => {⟨2, 86, 7⟩, ⟨2, 155, 2⟩, ⟨2, 224, 1⟩, ⟨3, 86, 2⟩, ⟨11, 86, 1⟩}
  | 2, 1 => {⟨2, 204, 1⟩}
  | 3, 0 => {⟨2, 76, 10⟩, ⟨2, 125, 3⟩, ⟨2, 174, 1⟩, ⟨2, 223, 1⟩, ⟨3, 76, 3⟩, ⟨3, 139, 1⟩, ⟨5, 76, 1⟩, ⟨11, 76, 2⟩}
  | 3, 1 => {⟨2, 204, 1⟩}
  | 4, 0 => {⟨2, 61, 15⟩, ⟨2, 92, 6⟩, ⟨2, 123, 3⟩, ⟨2, 154, 2⟩, ⟨2, 185, 1⟩, ⟨2, 216, 1⟩, ⟨3, 61, 5⟩, ⟨3, 102, 1⟩, ⟨5, 61, 2⟩, ⟨11, 61, 4⟩}
  | 4, 1 => {⟨2, 176, 1⟩}
  | 5, 0 => {⟨2, 57, 17⟩, ⟨2, 86, 7⟩, ⟨2, 115, 4⟩, ⟨2, 144, 2⟩, ⟨2, 173, 1⟩, ⟨2, 202, 1⟩, ⟨2, 231, 1⟩, ⟨3, 57, 5⟩, ⟨3, 95, 2⟩, ⟨3, 133, 1⟩, ⟨5, 57, 2⟩, ⟨11, 57, 4⟩}
  | 5, 1 => {⟨2, 175, 1⟩}
  | 6, 0 => {⟨2, 53, 20⟩, ⟨2, 80, 9⟩, ⟨2, 107, 5⟩, ⟨2, 134, 3⟩, ⟨2, 161, 2⟩, ⟨2, 188, 1⟩, ⟨2, 215, 1⟩, ⟨2, 242, 1⟩, ⟨3, 53, 6⟩, ⟨3, 89, 2⟩, ⟨3, 125, 1⟩, ⟨5, 53, 2⟩, ⟨11, 53, 6⟩, ⟨11, 102, 1⟩}
  | 6, 1 => {⟨2, 174, 1⟩}
  | 7, 0 => {⟨2, 49, 24⟩, ⟨2, 74, 10⟩, ⟨2, 99, 5⟩, ⟨2, 124, 3⟩, ⟨2, 149, 2⟩, ⟨2, 174, 1⟩, ⟨2, 199, 1⟩, ⟨2, 224, 1⟩, ⟨3, 49, 8⟩, ⟨3, 82, 2⟩, ⟨3, 115, 1⟩, ⟨5, 49, 2⟩, ⟨7, 49, 1⟩, ⟨11, 49, 8⟩, ⟨11, 94, 1⟩}
  | 7, 1 => {⟨2, 173, 1⟩}
  | 8, 0 => {⟨2, 45, 28⟩, ⟨2, 68, 12⟩, ⟨2, 91, 7⟩, ⟨2, 114, 4⟩, ⟨2, 137, 3⟩, ⟨2, 160, 2⟩, ⟨2, 183, 1⟩, ⟨2, 206, 1⟩, ⟨2, 229, 1⟩, ⟨3, 45, 9⟩, ⟨3, 75, 3⟩, ⟨3, 105, 1⟩, ⟨3, 135, 1⟩, ⟨5, 45, 3⟩, ⟨7, 45, 1⟩, ⟨11, 45, 9⟩, ⟨11, 86, 1⟩}
  | 8, 1 => {⟨2, 172, 1⟩}
  | 9, 0 => {⟨2, 41, 34⟩, ⟨2, 62, 15⟩, ⟨2, 83, 8⟩, ⟨2, 104, 5⟩, ⟨2, 125, 3⟩, ⟨2, 146, 2⟩, ⟨2, 167, 2⟩, ⟨2, 188, 1⟩, ⟨2, 209, 1⟩, ⟨2, 230, 1⟩, ⟨3, 41, 11⟩, ⟨3, 69, 4⟩, ⟨3, 97, 2⟩, ⟨3, 125, 1⟩, ⟨5, 41, 4⟩, ⟨5, 74, 1⟩, ⟨7, 41, 1⟩, ⟨11, 41, 12⟩, ⟨11, 79, 1⟩}
  | 9, 1 => {⟨2, 139, 3⟩, ⟨3, 139, 1⟩}
  | 10, 0 => {⟨2, 38, 39⟩, ⟨2, 57, 17⟩, ⟨2, 76, 10⟩, ⟨2, 95, 6⟩, ⟨2, 114, 4⟩, ⟨2, 133, 3⟩, ⟨2, 152, 2⟩, ⟨2, 171, 2⟩, ⟨2, 190, 1⟩, ⟨2, 209, 1⟩, ⟨2, 228, 1⟩, ⟨3, 38, 13⟩, ⟨3, 64, 4⟩, ⟨3, 90, 2⟩, ⟨3, 116, 1⟩, ⟨5, 38, 4⟩, ⟨5, 69, 1⟩, ⟨7, 38, 2⟩, ⟨11, 38, 15⟩, ⟨11, 73, 2⟩, ⟨11, 108, 1⟩}
  | 10, 1 => {⟨2, 137, 3⟩, ⟨3, 137, 1⟩}
  | 11, 0 => {⟨2, 35, 47⟩, ⟨2, 53, 20⟩, ⟨2, 71, 11⟩, ⟨2, 89, 7⟩, ⟨2, 107, 5⟩, ⟨2, 125, 3⟩, ⟨2, 143, 2⟩, ⟨2, 161, 2⟩, ⟨2, 179, 1⟩, ⟨2, 197, 1⟩, ⟨2, 215, 1⟩, ⟨2, 233, 1⟩, ⟨3, 35, 15⟩, ⟨3, 59, 5⟩, ⟨3, 83, 2⟩, ⟨3, 107, 1⟩, ⟨3, 131, 1⟩, ⟨5, 35, 6⟩, ⟨5, 63, 1⟩, ⟨7, 35, 2⟩, ⟨11, 35, 19⟩, ⟨11, 67, 2⟩, ⟨11, 99, 1⟩}
  | 11, 1 => {⟨2, 136, 3⟩, ⟨3, 136, 1⟩}
  | 12, 0 => {⟨2, 93, 7⟩, ⟨2, 173, 2⟩, ⟨3, 93, 2⟩, ⟨11, 93, 1⟩}
  | 12, 1 => {⟨2, 211, 1⟩}
  | 13, 0 => {⟨2, 79, 9⟩, ⟨2, 131, 3⟩, ⟨2, 183, 1⟩, ⟨2, 235, 1⟩, ⟨3, 79, 3⟩, ⟨11, 79, 1⟩}
  | 13, 1 => {⟨2, 210, 1⟩}
  | 14, 0 => {⟨2, 57, 18⟩, ⟨2, 86, 8⟩, ⟨2, 115, 4⟩, ⟨2, 144, 3⟩, ⟨2, 173, 2⟩, ⟨2, 202, 1⟩, ⟨2, 231, 1⟩, ⟨3, 57, 6⟩, ⟨3, 95, 2⟩, ⟨3, 133, 1⟩, ⟨5, 57, 2⟩, ⟨11, 57, 5⟩, ⟨11, 110, 1⟩}
  | 14, 1 => {⟨2, 179, 1⟩}
  | 15, 0 => {⟨2, 51, 23⟩, ⟨2, 77, 10⟩, ⟨2, 103, 5⟩, ⟨2, 129, 3⟩, ⟨2, 155, 2⟩, ⟨2, 181, 1⟩, ⟨2, 207, 1⟩, ⟨2, 233, 1⟩, ⟨3, 51, 7⟩, ⟨3, 85, 2⟩, ⟨3, 119, 1⟩, ⟨5, 51, 2⟩, ⟨7, 51, 1⟩, ⟨11, 51, 7⟩, ⟨11, 98, 1⟩}
  | 15, 1 => {⟨2, 177, 1⟩}
  | 16, 0 => {⟨2, 43, 33⟩, ⟨2, 65, 14⟩, ⟨2, 87, 8⟩, ⟨2, 109, 5⟩, ⟨2, 131, 3⟩, ⟨2, 153, 2⟩, ⟨2, 175, 2⟩, ⟨2, 197, 1⟩, ⟨2, 219, 1⟩, ⟨2, 241, 1⟩, ⟨3, 43, 11⟩, ⟨3, 72, 3⟩, ⟨3, 101, 2⟩, ⟨3, 130, 1⟩, ⟨5, 43, 4⟩, ⟨5, 78, 1⟩, ⟨7, 43, 1⟩, ⟨11, 43, 12⟩, ⟨11, 83, 1⟩}
  | 16, 1 => {⟨2, 142, 3⟩, ⟨3, 142, 1⟩}
  | 17, 0 => {⟨2, 38, 42⟩, ⟨2, 57, 18⟩, ⟨2, 76, 10⟩, ⟨2, 95, 6⟩, ⟨2, 114, 4⟩, ⟨2, 133, 3⟩, ⟨2, 152, 2⟩, ⟨2, 171, 2⟩, ⟨2, 190, 1⟩, ⟨2, 209, 1⟩, ⟨2, 228, 1⟩, ⟨2, 247, 1⟩, ⟨3, 38, 14⟩, ⟨3, 64, 5⟩, ⟨3, 90, 2⟩, ⟨3, 116, 1⟩, ⟨3, 142, 1⟩, ⟨5, 38, 5⟩, ⟨5, 69, 1⟩, ⟨7, 38, 2⟩, ⟨11, 38, 17⟩, ⟨11, 73, 2⟩, ⟨11, 108, 1⟩}
  | 17, 1 => {⟨2, 140, 3⟩, ⟨3, 140, 1⟩}
  | 18, 0 => {⟨2, 116, 4⟩, ⟨2, 219, 1⟩, ⟨3, 116, 1⟩}
  | 19, 0 => {⟨2, 98, 6⟩, ⟨2, 165, 2⟩, ⟨2, 232, 1⟩, ⟨3, 98, 2⟩, ⟨11, 98, 1⟩}
  | 20, 0 => {⟨2, 69, 12⟩, ⟨2, 104, 5⟩, ⟨2, 139, 3⟩, ⟨2, 174, 1⟩, ⟨2, 209, 1⟩, ⟨3, 69, 4⟩, ⟨3, 115, 1⟩, ⟨5, 69, 1⟩, ⟨11, 69, 2⟩}
  | 20, 1 => {⟨2, 218, 1⟩}
  | _, _ => ∅

def slope : ℕ → ℕ
  | 0 => 832
  | 1 => 1248
  | 2 => 1560
  | 3 => 2496
  | 4 => 4342
  | 5 => 5070
  | 6 => 6422
  | 7 => 7462
  | 8 => 9230
  | 9 => 11960
  | 10 => 14248
  | 11 => 16848
  | 12 => 1498
  | 13 => 2140
  | 14 => 5965
  | 15 => 7356
  | 16 => 11982
  | 17 => 15834
  | 18 => 780
  | 19 => 1560
  | 20 => 4127
  | _ => 0

def FiniteFacts (k : ℕ) (hk : k < 21) : Prop :=
  (∀ b : CrossBandCredit208.Band,
    BandFacts (row k).high (data k).steps (At (row k) (length hk) b) (terms k b) ∧
      ∀ t ∈ terms k b, (t.p,(row k).low/(t.q*(t.q+1)),t.count) ∈ Required) ∧
    RowSlope (row k) (length hk) (terms k) = slope k

local instance (k : ℕ) (hk : k < 21) : Decidable (FiniteFacts k hk) :=
  inferInstanceAs (Decidable ((∀ b : CrossBandCredit208.Band,
    BandFacts (row k).high (data k).steps (At (row k) (length hk) b) (terms k b) ∧
      ∀ t ∈ terms k b, (t.p,(row k).low/(t.q*(t.q+1)),t.count) ∈ Required) ∧
    RowSlope (row k) (length hk) (terms k) = slope k))

theorem facts00 : FiniteFacts 0 (by decide) := by decide +kernel
#print axioms facts00

theorem facts01 : FiniteFacts 1 (by decide) := by decide +kernel
#print axioms facts01

theorem facts02 : FiniteFacts 2 (by decide) := by decide +kernel
#print axioms facts02

theorem facts03 : FiniteFacts 3 (by decide) := by decide +kernel
#print axioms facts03

theorem facts04 : FiniteFacts 4 (by decide) := by decide +kernel
#print axioms facts04

theorem facts05 : FiniteFacts 5 (by decide) := by decide +kernel
#print axioms facts05

theorem facts06 : FiniteFacts 6 (by decide) := by decide +kernel
#print axioms facts06

theorem facts07 : FiniteFacts 7 (by decide) := by decide +kernel
#print axioms facts07

theorem facts08 : FiniteFacts 8 (by decide) := by decide +kernel
#print axioms facts08

theorem facts09 : FiniteFacts 9 (by decide) := by decide +kernel
#print axioms facts09

theorem facts10 : FiniteFacts 10 (by decide) := by decide +kernel
#print axioms facts10

theorem facts11 : FiniteFacts 11 (by decide) := by decide +kernel
#print axioms facts11

theorem facts12 : FiniteFacts 12 (by decide) := by decide +kernel
#print axioms facts12

theorem facts13 : FiniteFacts 13 (by decide) := by decide +kernel
#print axioms facts13

theorem facts14 : FiniteFacts 14 (by decide) := by decide +kernel
#print axioms facts14

theorem facts15 : FiniteFacts 15 (by decide) := by decide +kernel
#print axioms facts15

theorem facts16 : FiniteFacts 16 (by decide) := by decide +kernel
#print axioms facts16

theorem facts17 : FiniteFacts 17 (by decide) := by decide +kernel
#print axioms facts17

theorem facts18 : FiniteFacts 18 (by decide) := by decide +kernel
#print axioms facts18

theorem facts19 : FiniteFacts 19 (by decide) := by decide +kernel
#print axioms facts19

theorem facts20 : FiniteFacts 20 (by decide) := by decide +kernel
#print axioms facts20

theorem facts {k : ℕ} (hk : k < 21) : FiniteFacts k hk := by
  interval_cases k
  · exact facts00
  · exact facts01
  · exact facts02
  · exact facts03
  · exact facts04
  · exact facts05
  · exact facts06
  · exact facts07
  · exact facts08
  · exact facts09
  · exact facts10
  · exact facts11
  · exact facts12
  · exact facts13
  · exact facts14
  · exact facts15
  · exact facts16
  · exact facts17
  · exact facts18
  · exact facts19
  · exact facts20

theorem slope_bound {k N : ℕ} (hk : k < 21)
    (hlo : (data k).row.low ≤ N) (hhi : N ≤ (data k).row.high)
    (hchecked : ChunkFacts (row k) 1 (data k).steps (toTotals (data k).total)) :
    RowLight (row k) (length hk) (data k).steps N+
      slope k*((data k).row.high-N) ≤ (data k).total.light := by
  have hf : ∀ b, BandFacts (row k).high (data k).steps
      (At (row k) (length hk) b) (terms k b) := fun b => ((facts hk).1 b).1
  have hc : ∀ b, ∀ t ∈ terms k b,
      ClassCount158375.Certificate t.p ((row k).low/(t.q*(t.q+1))) t.count := by
    intro b t ht
    exact selected_certificate (((facts hk).1 b).2 t ht)
  have h := LightSlope158375.row_light_bound hlo hhi hf hc hchecked
  rw [(facts hk).2] at h
  exact h

#print axioms length
#print axioms facts
#print axioms slope_bound
end
end JSP233.RowLightSlope118533
