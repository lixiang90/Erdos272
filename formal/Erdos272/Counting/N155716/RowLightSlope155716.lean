module

public import Erdos272.Counting.N158375.LightSlope158375
public import Erdos272.Arithmetic.N155716.ClassCertificates155716
public import Erdos272.Arithmetic.N155716.CleanupRows155716
public import Erdos272.Arithmetic.CleanupMachineSound208

@[expose] public section

namespace JSP233.RowLightSlope155716
open CleanupRows155716 CleanupEval208 CleanupMachineSound208 ActualCleanupEval208
open LightFamily158375 LightSlope158375 ClassCertificates155716
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

theorem length {k : ℕ} (hk : k < 9) : (row k).bands.length=7 := by
  interval_cases k <;> rfl

def terms (k : ℕ) (b : CrossBandCredit208.Band) : Finset Term :=
  match k, b.val with
  | 0, 0 => {⟨2, 115, 5⟩, ⟨2, 227, 1⟩, ⟨3, 115, 1⟩, ⟨11, 115, 1⟩}
  | 0, 1 => {⟨2, 164, 2⟩}
  | 1, 0 => {⟨2, 108, 6⟩, ⟨2, 206, 1⟩, ⟨3, 108, 2⟩, ⟨11, 108, 1⟩}
  | 1, 1 => {⟨2, 161, 2⟩}
  | 1, 2 => {⟨2, 235, 1⟩}
  | 2, 0 => {⟨2, 98, 8⟩, ⟨2, 176, 2⟩, ⟨2, 254, 1⟩, ⟨3, 98, 2⟩, ⟨11, 98, 1⟩}
  | 2, 1 => {⟨2, 158, 3⟩, ⟨3, 158, 1⟩}
  | 2, 2 => {⟨2, 234, 1⟩}
  | 3, 0 => {⟨2, 87, 10⟩, ⟨2, 143, 3⟩, ⟨2, 199, 1⟩, ⟨2, 255, 1⟩, ⟨3, 87, 3⟩, ⟨3, 159, 1⟩, ⟨5, 87, 1⟩, ⟨11, 87, 2⟩}
  | 3, 1 => {⟨2, 156, 3⟩, ⟨3, 156, 1⟩}
  | 3, 2 => {⟨2, 233, 1⟩}
  | 4, 0 => {⟨2, 61, 20⟩, ⟨2, 92, 9⟩, ⟨2, 123, 5⟩, ⟨2, 154, 3⟩, ⟨2, 185, 2⟩, ⟨2, 216, 1⟩, ⟨2, 247, 1⟩, ⟨2, 278, 1⟩, ⟨3, 61, 6⟩, ⟨3, 102, 2⟩, ⟨3, 143, 1⟩, ⟨5, 61, 2⟩, ⟨11, 61, 6⟩, ⟨11, 117, 1⟩}
  | 4, 1 => {⟨2, 153, 3⟩, ⟨3, 153, 1⟩}
  | 4, 2 => {⟨2, 232, 1⟩}
  | 5, 0 => {⟨2, 55, 25⟩, ⟨2, 83, 11⟩, ⟨2, 111, 6⟩, ⟨2, 139, 4⟩, ⟨2, 167, 2⟩, ⟨2, 195, 2⟩, ⟨2, 223, 1⟩, ⟨2, 251, 1⟩, ⟨3, 55, 8⟩, ⟨3, 92, 3⟩, ⟨3, 129, 1⟩, ⟨5, 55, 3⟩, ⟨7, 55, 1⟩, ⟨11, 55, 8⟩, ⟨11, 105, 1⟩}
  | 5, 1 => {⟨2, 150, 3⟩, ⟨3, 150, 1⟩}
  | 5, 2 => {⟨2, 231, 1⟩}
  | 6, 0 => {⟨2, 51, 29⟩, ⟨2, 77, 12⟩, ⟨2, 103, 7⟩, ⟨2, 129, 4⟩, ⟨2, 155, 3⟩, ⟨2, 181, 2⟩, ⟨2, 207, 1⟩, ⟨2, 233, 1⟩, ⟨2, 259, 1⟩, ⟨3, 51, 9⟩, ⟨3, 85, 3⟩, ⟨3, 119, 1⟩, ⟨3, 153, 1⟩, ⟨5, 51, 3⟩, ⟨7, 51, 1⟩, ⟨11, 51, 9⟩, ⟨11, 98, 1⟩}
  | 6, 1 => {⟨2, 148, 3⟩, ⟨3, 148, 1⟩}
  | 6, 2 => {⟨2, 230, 1⟩}
  | 7, 0 => {⟨2, 47, 34⟩, ⟨2, 71, 15⟩, ⟨2, 95, 8⟩, ⟨2, 119, 5⟩, ⟨2, 143, 3⟩, ⟨2, 167, 2⟩, ⟨2, 191, 2⟩, ⟨2, 215, 1⟩, ⟨2, 239, 1⟩, ⟨2, 263, 1⟩, ⟨3, 47, 11⟩, ⟨3, 79, 4⟩, ⟨3, 111, 2⟩, ⟨3, 143, 1⟩, ⟨5, 47, 4⟩, ⟨5, 85, 1⟩, ⟨7, 47, 1⟩, ⟨11, 47, 12⟩, ⟨11, 90, 1⟩}
  | 7, 1 => {⟨2, 145, 3⟩, ⟨2, 270, 1⟩, ⟨3, 145, 1⟩}
  | 7, 2 => {⟨2, 230, 1⟩}
  | 8, 0 => {⟨2, 43, 41⟩, ⟨2, 65, 18⟩, ⟨2, 87, 10⟩, ⟨2, 109, 6⟩, ⟨2, 131, 4⟩, ⟨2, 153, 3⟩, ⟨2, 175, 2⟩, ⟨2, 197, 1⟩, ⟨2, 219, 1⟩, ⟨2, 241, 1⟩, ⟨2, 263, 1⟩, ⟨3, 43, 13⟩, ⟨3, 72, 4⟩, ⟨3, 101, 2⟩, ⟨3, 130, 1⟩, ⟨3, 159, 1⟩, ⟨5, 43, 5⟩, ⟨5, 78, 1⟩, ⟨7, 43, 2⟩, ⟨11, 43, 15⟩, ⟨11, 83, 2⟩, ⟨11, 123, 1⟩}
  | 8, 1 => {⟨2, 142, 3⟩, ⟨2, 261, 1⟩, ⟨3, 142, 1⟩}
  | 8, 2 => {⟨2, 229, 1⟩}
  | _, _ => ∅

def slope : ℕ → ℕ
  | 0 => 1284
  | 1 => 1760
  | 2 => 2568
  | 3 => 3520
  | 4 => 8042
  | 5 => 10065
  | 6 => 11374
  | 7 => 14039
  | 8 => 17133
  | _ => 0

def FiniteFacts (k : ℕ) (hk : k < 9) : Prop :=
  (∀ b : CrossBandCredit208.Band,
    BandFacts (row k).high (data k).steps (At (row k) (length hk) b) (terms k b) ∧
      ∀ t ∈ terms k b, (t.p,(row k).low/(t.q*(t.q+1)),t.count) ∈ Required) ∧
    RowSlope (row k) (length hk) (terms k) = slope k

local instance (k : ℕ) (hk : k < 9) : Decidable (FiniteFacts k hk) :=
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

theorem facts {k : ℕ} (hk : k < 9) : FiniteFacts k hk := by
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

theorem slope_bound {k N : ℕ} (hk : k < 9)
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
end JSP233.RowLightSlope155716
