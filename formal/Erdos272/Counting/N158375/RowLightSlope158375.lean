module

public import Erdos272.Counting.N158375.LightSlope158375
public import Erdos272.Arithmetic.N158375.ClassCertificates158375
public import Erdos272.Arithmetic.N158375.CleanupRows158375
public import Erdos272.Arithmetic.CleanupMachineSound208

@[expose] public section

namespace JSP233.RowLightSlope158375
open CleanupRows158375 CleanupEval208 CleanupMachineSound208 ActualCleanupEval208
open LightFamily158375 LightSlope158375 ClassCertificates158375
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

theorem length {k : ℕ} (hk : k < 20) : (row k).bands.length=7 := by
  interval_cases k <;> rfl

def terms (k : ℕ) (b : CrossBandCredit208.Band) : Finset Term :=
  match k, b.val with
  | 0, 0 => {⟨2, 116, 5⟩, ⟨2, 229, 1⟩, ⟨3, 116, 1⟩, ⟨11, 116, 1⟩}
  | 0, 1 => {⟨2, 166, 2⟩}
  | 1, 0 => {⟨2, 109, 6⟩, ⟨2, 208, 1⟩, ⟨3, 109, 2⟩, ⟨11, 109, 1⟩}
  | 1, 1 => {⟨2, 163, 2⟩}
  | 1, 2 => {⟨2, 237, 1⟩}
  | 2, 0 => {⟨2, 99, 7⟩, ⟨2, 178, 2⟩, ⟨2, 257, 1⟩, ⟨3, 99, 2⟩, ⟨11, 99, 1⟩}
  | 2, 1 => {⟨2, 160, 3⟩, ⟨3, 160, 1⟩}
  | 2, 2 => {⟨2, 236, 1⟩}
  | 3, 0 => {⟨2, 88, 10⟩, ⟨2, 145, 3⟩, ⟨2, 202, 1⟩, ⟨2, 259, 1⟩, ⟨3, 88, 3⟩, ⟨3, 161, 1⟩, ⟨5, 88, 1⟩, ⟨11, 88, 2⟩}
  | 3, 1 => {⟨2, 158, 3⟩, ⟨3, 158, 1⟩}
  | 3, 2 => {⟨2, 235, 1⟩}
  | 4, 0 => {⟨2, 61, 20⟩, ⟨2, 92, 9⟩, ⟨2, 123, 5⟩, ⟨2, 154, 3⟩, ⟨2, 185, 2⟩, ⟨2, 216, 1⟩, ⟨2, 247, 1⟩, ⟨2, 278, 1⟩, ⟨3, 61, 6⟩, ⟨3, 102, 2⟩, ⟨3, 143, 1⟩, ⟨5, 61, 2⟩, ⟨11, 61, 6⟩, ⟨11, 117, 1⟩}
  | 4, 1 => {⟨2, 154, 3⟩, ⟨3, 154, 1⟩}
  | 4, 2 => {⟨2, 234, 1⟩}
  | 5, 0 => {⟨2, 55, 25⟩, ⟨2, 83, 11⟩, ⟨2, 111, 6⟩, ⟨2, 139, 4⟩, ⟨2, 167, 2⟩, ⟨2, 195, 2⟩, ⟨2, 223, 1⟩, ⟨2, 251, 1⟩, ⟨2, 279, 1⟩, ⟨3, 55, 8⟩, ⟨3, 92, 3⟩, ⟨3, 129, 1⟩, ⟨5, 55, 3⟩, ⟨7, 55, 1⟩, ⟨11, 55, 8⟩, ⟨11, 105, 1⟩}
  | 5, 1 => {⟨2, 152, 3⟩, ⟨3, 152, 1⟩}
  | 5, 2 => {⟨2, 233, 1⟩}
  | 6, 0 => {⟨2, 51, 29⟩, ⟨2, 77, 13⟩, ⟨2, 103, 7⟩, ⟨2, 129, 4⟩, ⟨2, 155, 3⟩, ⟨2, 181, 2⟩, ⟨2, 207, 1⟩, ⟨2, 233, 1⟩, ⟨2, 259, 1⟩, ⟨3, 51, 9⟩, ⟨3, 85, 3⟩, ⟨3, 119, 1⟩, ⟨3, 153, 1⟩, ⟨5, 51, 3⟩, ⟨7, 51, 1⟩, ⟨11, 51, 9⟩, ⟨11, 98, 1⟩}
  | 6, 1 => {⟨2, 150, 3⟩, ⟨3, 150, 1⟩}
  | 6, 2 => {⟨2, 232, 1⟩}
  | 7, 0 => {⟨2, 47, 35⟩, ⟨2, 71, 15⟩, ⟨2, 95, 8⟩, ⟨2, 119, 5⟩, ⟨2, 143, 3⟩, ⟨2, 167, 2⟩, ⟨2, 191, 2⟩, ⟨2, 215, 1⟩, ⟨2, 239, 1⟩, ⟨2, 263, 1⟩, ⟨3, 47, 11⟩, ⟨3, 79, 4⟩, ⟨3, 111, 2⟩, ⟨3, 143, 1⟩, ⟨5, 47, 4⟩, ⟨5, 85, 1⟩, ⟨7, 47, 2⟩, ⟨11, 47, 14⟩, ⟨11, 90, 1⟩}
  | 7, 1 => {⟨2, 147, 3⟩, ⟨2, 274, 1⟩, ⟨3, 147, 1⟩}
  | 7, 2 => {⟨2, 231, 1⟩}
  | 8, 0 => {⟨2, 43, 41⟩, ⟨2, 65, 18⟩, ⟨2, 87, 10⟩, ⟨2, 109, 6⟩, ⟨2, 131, 4⟩, ⟨2, 153, 3⟩, ⟨2, 175, 2⟩, ⟨2, 197, 2⟩, ⟨2, 219, 1⟩, ⟨2, 241, 1⟩, ⟨2, 263, 1⟩, ⟨3, 43, 13⟩, ⟨3, 72, 5⟩, ⟨3, 101, 2⟩, ⟨3, 130, 1⟩, ⟨3, 159, 1⟩, ⟨5, 43, 5⟩, ⟨5, 78, 1⟩, ⟨7, 43, 2⟩, ⟨11, 43, 15⟩, ⟨11, 83, 2⟩, ⟨11, 123, 1⟩}
  | 8, 1 => {⟨2, 144, 3⟩, ⟨2, 265, 1⟩, ⟨3, 144, 1⟩}
  | 8, 2 => {⟨2, 231, 1⟩}
  | 9, 0 => {⟨2, 111, 6⟩, ⟨2, 212, 1⟩, ⟨3, 111, 2⟩, ⟨11, 111, 1⟩}
  | 9, 1 => {⟨2, 165, 3⟩, ⟨3, 165, 1⟩}
  | 9, 2 => {⟨2, 241, 1⟩}
  | 10, 0 => {⟨2, 90, 10⟩, ⟨2, 149, 3⟩, ⟨2, 208, 1⟩, ⟨2, 267, 1⟩, ⟨3, 90, 3⟩, ⟨3, 165, 1⟩, ⟨5, 90, 1⟩, ⟨11, 90, 2⟩}
  | 10, 1 => {⟨2, 160, 3⟩, ⟨3, 160, 1⟩}
  | 10, 2 => {⟨2, 239, 1⟩}
  | 11, 0 => {⟨2, 61, 21⟩, ⟨2, 92, 9⟩, ⟨2, 123, 5⟩, ⟨2, 154, 3⟩, ⟨2, 185, 2⟩, ⟨2, 216, 1⟩, ⟨2, 247, 1⟩, ⟨2, 278, 1⟩, ⟨3, 61, 7⟩, ⟨3, 102, 2⟩, ⟨3, 143, 1⟩, ⟨5, 61, 2⟩, ⟨7, 61, 1⟩, ⟨11, 61, 7⟩, ⟨11, 117, 1⟩}
  | 11, 1 => {⟨2, 156, 3⟩, ⟨3, 156, 1⟩}
  | 11, 2 => {⟨2, 238, 1⟩}
  | 12, 0 => {⟨2, 53, 29⟩, ⟨2, 80, 12⟩, ⟨2, 107, 7⟩, ⟨2, 134, 4⟩, ⟨2, 161, 3⟩, ⟨2, 188, 2⟩, ⟨2, 215, 1⟩, ⟨2, 242, 1⟩, ⟨2, 269, 1⟩, ⟨3, 53, 9⟩, ⟨3, 89, 3⟩, ⟨3, 125, 1⟩, ⟨3, 161, 1⟩, ⟨5, 53, 3⟩, ⟨7, 53, 1⟩, ⟨11, 53, 9⟩, ⟨11, 102, 1⟩}
  | 12, 1 => {⟨2, 152, 3⟩, ⟨2, 287, 1⟩, ⟨3, 152, 1⟩}
  | 12, 2 => {⟨2, 236, 1⟩}
  | 13, 0 => {⟨2, 47, 36⟩, ⟨2, 71, 16⟩, ⟨2, 95, 9⟩, ⟨2, 119, 5⟩, ⟨2, 143, 4⟩, ⟨2, 167, 2⟩, ⟨2, 191, 2⟩, ⟨2, 215, 1⟩, ⟨2, 239, 1⟩, ⟨2, 263, 1⟩, ⟨2, 287, 1⟩, ⟨3, 47, 12⟩, ⟨3, 79, 4⟩, ⟨3, 111, 2⟩, ⟨3, 143, 1⟩, ⟨5, 47, 4⟩, ⟨5, 85, 1⟩, ⟨7, 47, 2⟩, ⟨11, 47, 13⟩, ⟨11, 90, 2⟩}
  | 13, 1 => {⟨2, 148, 3⟩, ⟨2, 275, 1⟩, ⟨3, 148, 1⟩}
  | 13, 2 => {⟨2, 235, 1⟩}
  | 14, 0 => {⟨2, 43, 43⟩, ⟨2, 65, 19⟩, ⟨2, 87, 10⟩, ⟨2, 109, 6⟩, ⟨2, 131, 4⟩, ⟨2, 153, 3⟩, ⟨2, 175, 2⟩, ⟨2, 197, 2⟩, ⟨2, 219, 1⟩, ⟨2, 241, 1⟩, ⟨2, 263, 1⟩, ⟨2, 285, 1⟩, ⟨3, 43, 14⟩, ⟨3, 72, 5⟩, ⟨3, 101, 2⟩, ⟨3, 130, 1⟩, ⟨3, 159, 1⟩, ⟨5, 43, 5⟩, ⟨5, 78, 1⟩, ⟨7, 43, 2⟩, ⟨11, 43, 16⟩, ⟨11, 83, 2⟩, ⟨11, 123, 1⟩}
  | 14, 1 => {⟨2, 145, 3⟩, ⟨2, 266, 1⟩, ⟨3, 145, 1⟩}
  | 14, 2 => {⟨2, 234, 1⟩}
  | 15, 0 => {⟨2, 113, 6⟩, ⟨2, 216, 1⟩, ⟨3, 113, 2⟩, ⟨11, 113, 1⟩}
  | 15, 1 => {⟨2, 168, 3⟩, ⟨3, 168, 1⟩}
  | 15, 2 => {⟨2, 245, 1⟩}
  | 16, 0 => {⟨2, 91, 10⟩, ⟨2, 150, 3⟩, ⟨2, 209, 1⟩, ⟨2, 268, 1⟩, ⟨3, 91, 3⟩, ⟨3, 166, 1⟩, ⟨5, 91, 1⟩, ⟨11, 91, 2⟩}
  | 16, 1 => {⟨2, 162, 3⟩, ⟨3, 162, 1⟩}
  | 16, 2 => {⟨2, 243, 1⟩}
  | 17, 0 => {⟨2, 59, 24⟩, ⟨2, 89, 10⟩, ⟨2, 119, 5⟩, ⟨2, 149, 3⟩, ⟨2, 179, 2⟩, ⟨2, 209, 1⟩, ⟨2, 239, 1⟩, ⟨2, 269, 1⟩, ⟨3, 59, 8⟩, ⟨3, 99, 2⟩, ⟨3, 139, 1⟩, ⟨5, 59, 2⟩, ⟨7, 59, 1⟩, ⟨11, 59, 8⟩, ⟨11, 113, 1⟩}
  | 17, 1 => {⟨2, 157, 3⟩, ⟨3, 157, 1⟩}
  | 17, 2 => {⟨2, 241, 1⟩}
  | 18, 0 => {⟨2, 51, 32⟩, ⟨2, 77, 14⟩, ⟨2, 103, 7⟩, ⟨2, 129, 5⟩, ⟨2, 155, 3⟩, ⟨2, 181, 2⟩, ⟨2, 207, 1⟩, ⟨2, 233, 1⟩, ⟨2, 259, 1⟩, ⟨2, 285, 1⟩, ⟨3, 51, 10⟩, ⟨3, 85, 3⟩, ⟨3, 119, 1⟩, ⟨3, 153, 1⟩, ⟨5, 51, 4⟩, ⟨7, 51, 1⟩, ⟨11, 51, 11⟩, ⟨11, 98, 1⟩}
  | 18, 1 => {⟨2, 153, 3⟩, ⟨2, 287, 1⟩, ⟨3, 153, 1⟩}
  | 18, 2 => {⟨2, 240, 1⟩}
  | 19, 0 => {⟨2, 45, 41⟩, ⟨2, 68, 18⟩, ⟨2, 91, 10⟩, ⟨2, 114, 6⟩, ⟨2, 137, 4⟩, ⟨2, 160, 3⟩, ⟨2, 183, 2⟩, ⟨2, 206, 2⟩, ⟨2, 229, 1⟩, ⟨2, 252, 1⟩, ⟨2, 275, 1⟩, ⟨3, 45, 13⟩, ⟨3, 75, 5⟩, ⟨3, 105, 2⟩, ⟨3, 135, 1⟩, ⟨3, 165, 1⟩, ⟨5, 45, 5⟩, ⟨5, 81, 1⟩, ⟨7, 45, 2⟩, ⟨11, 45, 15⟩, ⟨11, 86, 2⟩, ⟨11, 127, 1⟩}
  | 19, 1 => {⟨2, 149, 3⟩, ⟨2, 275, 1⟩, ⟨3, 149, 1⟩}
  | 19, 2 => {⟨2, 238, 1⟩}
  | _, _ => ∅

def slope : ℕ → ℕ
  | 0 => 1296
  | 1 => 1776
  | 2 => 2472
  | 3 => 3552
  | 4 => 8112
  | 5 => 10272
  | 6 => 11592
  | 7 => 14640
  | 8 => 17520
  | 9 => 2144
  | 10 => 3608
  | 11 => 8732
  | 12 => 11830
  | 13 => 15612
  | 14 => 18540
  | 15 => 2180
  | 16 => 3668
  | 17 => 9620
  | 18 => 13389
  | 19 => 18101
  | _ => 0

def FiniteFacts (k : ℕ) (hk : k < 20) : Prop :=
  (∀ b : CrossBandCredit208.Band,
    BandFacts (row k).high (data k).steps (At (row k) (length hk) b) (terms k b) ∧
      ∀ t ∈ terms k b, (t.p,(row k).low/(t.q*(t.q+1)),t.count) ∈ Required) ∧
    RowSlope (row k) (length hk) (terms k) = slope k

local instance (k : ℕ) (hk : k < 20) : Decidable (FiniteFacts k hk) :=
  inferInstanceAs (Decidable ((∀ b : CrossBandCredit208.Band,
    BandFacts (row k).high (data k).steps (At (row k) (length hk) b) (terms k b) ∧
      ∀ t ∈ terms k b, (t.p,(row k).low/(t.q*(t.q+1)),t.count) ∈ Required) ∧
    RowSlope (row k) (length hk) (terms k) = slope k))

theorem facts00 : FiniteFacts 0 (by decide) := by
  decide +kernel
#print axioms facts00

theorem facts01 : FiniteFacts 1 (by decide) := by
  decide +kernel
#print axioms facts01

theorem facts02 : FiniteFacts 2 (by decide) := by
  decide +kernel
#print axioms facts02

theorem facts03 : FiniteFacts 3 (by decide) := by
  decide +kernel
#print axioms facts03

theorem facts04 : FiniteFacts 4 (by decide) := by
  decide +kernel
#print axioms facts04

theorem facts05 : FiniteFacts 5 (by decide) := by
  decide +kernel
#print axioms facts05

theorem facts06 : FiniteFacts 6 (by decide) := by
  decide +kernel
#print axioms facts06

theorem facts07 : FiniteFacts 7 (by decide) := by
  decide +kernel
#print axioms facts07

theorem facts08 : FiniteFacts 8 (by decide) := by
  decide +kernel
#print axioms facts08

theorem facts09 : FiniteFacts 9 (by decide) := by
  decide +kernel
#print axioms facts09

theorem facts10 : FiniteFacts 10 (by decide) := by
  decide +kernel
#print axioms facts10

theorem facts11 : FiniteFacts 11 (by decide) := by
  decide +kernel
#print axioms facts11

theorem facts12 : FiniteFacts 12 (by decide) := by
  decide +kernel
#print axioms facts12

theorem facts13 : FiniteFacts 13 (by decide) := by
  decide +kernel
#print axioms facts13

theorem facts14 : FiniteFacts 14 (by decide) := by
  decide +kernel
#print axioms facts14

theorem facts15 : FiniteFacts 15 (by decide) := by
  decide +kernel
#print axioms facts15

theorem facts16 : FiniteFacts 16 (by decide) := by
  decide +kernel
#print axioms facts16

theorem facts17 : FiniteFacts 17 (by decide) := by
  decide +kernel
#print axioms facts17

theorem facts18 : FiniteFacts 18 (by decide) := by
  decide +kernel
#print axioms facts18

theorem facts19 : FiniteFacts 19 (by decide) := by
  decide +kernel
#print axioms facts19

theorem facts {k : ℕ} (hk : k < 20) : FiniteFacts k hk := by
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

theorem slope_bound {k N : ℕ} (hk : k < 20)
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
end JSP233.RowLightSlope158375
