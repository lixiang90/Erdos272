module

public import Erdos272.Counting.N158375.LightSlope158375
public import Erdos272.Arithmetic.N151879.ClassCertificates151879
public import Erdos272.Arithmetic.N151879.CleanupRows151879
public import Erdos272.Arithmetic.CleanupMachineSound208

@[expose] public section

namespace JSP233.RowLightSlope151879
open CleanupRows151879 CleanupEval208 CleanupMachineSound208 ActualCleanupEval208
open LightFamily158375 LightSlope158375 ClassCertificates151879
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

theorem length {k : ℕ} (hk : k < 11) : (row k).bands.length=7 := by
  interval_cases k <;> rfl

def terms (k : ℕ) (b : CrossBandCredit208.Band) : Finset Term :=
  match k, b.val with
  | 0, 0 => {⟨2, 113, 5⟩, ⟨2, 223, 1⟩, ⟨3, 113, 1⟩, ⟨11, 113, 1⟩}
  | 0, 1 => {⟨2, 161, 2⟩}
  | 1, 0 => {⟨2, 106, 6⟩, ⟨2, 202, 1⟩, ⟨3, 106, 2⟩, ⟨11, 106, 1⟩}
  | 1, 1 => {⟨2, 158, 3⟩, ⟨3, 158, 1⟩}
  | 1, 2 => {⟨2, 231, 1⟩}
  | 2, 0 => {⟨2, 96, 8⟩, ⟨2, 172, 2⟩, ⟨2, 248, 1⟩, ⟨3, 96, 2⟩, ⟨11, 96, 1⟩}
  | 2, 1 => {⟨2, 155, 3⟩, ⟨3, 155, 1⟩}
  | 2, 2 => {⟨2, 230, 1⟩}
  | 3, 0 => {⟨2, 85, 10⟩, ⟨2, 139, 3⟩, ⟨2, 193, 2⟩, ⟨2, 247, 1⟩, ⟨3, 85, 3⟩, ⟨3, 155, 1⟩, ⟨5, 85, 1⟩, ⟨11, 85, 2⟩}
  | 3, 1 => {⟨2, 153, 3⟩, ⟨3, 153, 1⟩}
  | 3, 2 => {⟨2, 229, 1⟩}
  | 4, 0 => {⟨2, 63, 18⟩, ⟨2, 95, 8⟩, ⟨2, 127, 4⟩, ⟨2, 159, 2⟩, ⟨2, 191, 2⟩, ⟨2, 223, 1⟩, ⟨2, 255, 1⟩, ⟨3, 63, 6⟩, ⟨3, 105, 2⟩, ⟨3, 147, 1⟩, ⟨5, 63, 2⟩, ⟨11, 63, 5⟩, ⟨11, 121, 1⟩}
  | 4, 1 => {⟨2, 151, 3⟩, ⟨3, 151, 1⟩}
  | 4, 2 => {⟨2, 229, 1⟩}
  | 5, 0 => {⟨2, 59, 21⟩, ⟨2, 89, 9⟩, ⟨2, 119, 5⟩, ⟨2, 149, 3⟩, ⟨2, 179, 2⟩, ⟨2, 209, 1⟩, ⟨2, 239, 1⟩, ⟨2, 269, 1⟩, ⟨3, 59, 7⟩, ⟨3, 99, 2⟩, ⟨3, 139, 1⟩, ⟨5, 59, 2⟩, ⟨7, 59, 1⟩, ⟨11, 59, 7⟩, ⟨11, 113, 1⟩}
  | 5, 1 => {⟨2, 149, 3⟩, ⟨3, 149, 1⟩}
  | 5, 2 => {⟨2, 228, 1⟩}
  | 6, 0 => {⟨2, 53, 26⟩, ⟨2, 80, 11⟩, ⟨2, 107, 6⟩, ⟨2, 134, 4⟩, ⟨2, 161, 2⟩, ⟨2, 188, 2⟩, ⟨2, 215, 1⟩, ⟨2, 242, 1⟩, ⟨2, 269, 1⟩, ⟨3, 53, 8⟩, ⟨3, 89, 3⟩, ⟨3, 125, 1⟩, ⟨5, 53, 3⟩, ⟨7, 53, 1⟩, ⟨11, 53, 8⟩, ⟨11, 102, 1⟩}
  | 6, 1 => {⟨2, 147, 3⟩, ⟨3, 147, 1⟩}
  | 6, 2 => {⟨2, 227, 1⟩}
  | 7, 0 => {⟨2, 49, 30⟩, ⟨2, 74, 13⟩, ⟨2, 99, 7⟩, ⟨2, 124, 4⟩, ⟨2, 149, 3⟩, ⟨2, 174, 2⟩, ⟨2, 199, 1⟩, ⟨2, 224, 1⟩, ⟨2, 249, 1⟩, ⟨2, 274, 1⟩, ⟨3, 49, 10⟩, ⟨3, 82, 3⟩, ⟨3, 115, 1⟩, ⟨3, 148, 1⟩, ⟨5, 49, 4⟩, ⟨7, 49, 1⟩, ⟨11, 49, 11⟩, ⟨11, 94, 1⟩}
  | 7, 1 => {⟨2, 144, 3⟩, ⟨2, 270, 1⟩, ⟨3, 144, 1⟩}
  | 7, 2 => {⟨2, 226, 1⟩}
  | 8, 0 => {⟨2, 46, 35⟩, ⟨2, 69, 15⟩, ⟨2, 92, 8⟩, ⟨2, 115, 5⟩, ⟨2, 138, 3⟩, ⟨2, 161, 2⟩, ⟨2, 184, 2⟩, ⟨2, 207, 1⟩, ⟨2, 230, 1⟩, ⟨2, 253, 1⟩, ⟨3, 46, 11⟩, ⟨3, 77, 4⟩, ⟨3, 108, 2⟩, ⟨3, 139, 1⟩, ⟨5, 46, 4⟩, ⟨5, 83, 1⟩, ⟨7, 46, 2⟩, ⟨11, 46, 14⟩, ⟨11, 88, 1⟩}
  | 8, 1 => {⟨2, 142, 3⟩, ⟨2, 264, 1⟩, ⟨3, 142, 1⟩}
  | 8, 2 => {⟨2, 226, 1⟩}
  | 9, 0 => {⟨2, 43, 40⟩, ⟨2, 65, 17⟩, ⟨2, 87, 9⟩, ⟨2, 109, 6⟩, ⟨2, 131, 4⟩, ⟨2, 153, 3⟩, ⟨2, 175, 2⟩, ⟨2, 197, 1⟩, ⟨2, 219, 1⟩, ⟨2, 241, 1⟩, ⟨2, 263, 1⟩, ⟨3, 43, 13⟩, ⟨3, 72, 4⟩, ⟨3, 101, 2⟩, ⟨3, 130, 1⟩, ⟨5, 43, 5⟩, ⟨5, 78, 1⟩, ⟨7, 43, 2⟩, ⟨11, 43, 15⟩, ⟨11, 83, 2⟩}
  | 9, 1 => {⟨2, 140, 3⟩, ⟨2, 258, 1⟩, ⟨3, 140, 1⟩}
  | 9, 2 => {⟨2, 225, 1⟩}
  | 10, 0 => {⟨2, 41, 44⟩, ⟨2, 62, 19⟩, ⟨2, 83, 10⟩, ⟨2, 104, 6⟩, ⟨2, 125, 4⟩, ⟨2, 146, 3⟩, ⟨2, 167, 2⟩, ⟨2, 188, 2⟩, ⟨2, 209, 1⟩, ⟨2, 230, 1⟩, ⟨2, 251, 1⟩, ⟨2, 272, 1⟩, ⟨3, 41, 14⟩, ⟨3, 69, 5⟩, ⟨3, 97, 2⟩, ⟨3, 125, 1⟩, ⟨3, 153, 1⟩, ⟨5, 41, 5⟩, ⟨5, 74, 1⟩, ⟨7, 41, 2⟩, ⟨11, 41, 17⟩, ⟨11, 79, 2⟩, ⟨11, 117, 1⟩}
  | 10, 1 => {⟨2, 138, 3⟩, ⟨2, 252, 1⟩, ⟨3, 138, 1⟩}
  | 10, 2 => {⟨2, 225, 1⟩}
  | _, _ => ∅

def slope : ℕ → ℕ
  | 0 => 1262
  | 1 => 2056
  | 2 => 2524
  | 3 => 3577
  | 4 => 7087
  | 5 => 8374
  | 6 => 10129
  | 7 => 12164
  | 8 => 14270
  | 9 => 16259
  | 10 => 18014
  | _ => 0

def FiniteFacts (k : ℕ) (hk : k < 11) : Prop :=
  (∀ b : CrossBandCredit208.Band,
    BandFacts (row k).high (data k).steps (At (row k) (length hk) b) (terms k b) ∧
      ∀ t ∈ terms k b, (t.p,(row k).low/(t.q*(t.q+1)),t.count) ∈ Required) ∧
    RowSlope (row k) (length hk) (terms k) = slope k

local instance (k : ℕ) (hk : k < 11) : Decidable (FiniteFacts k hk) :=
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

theorem facts {k : ℕ} (hk : k < 11) : FiniteFacts k hk := by
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

theorem slope_bound {k N : ℕ} (hk : k < 11)
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
end JSP233.RowLightSlope151879
