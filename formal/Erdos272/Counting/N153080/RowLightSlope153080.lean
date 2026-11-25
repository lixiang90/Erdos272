module

public import Erdos272.Counting.N158375.LightSlope158375
public import Erdos272.Arithmetic.N153080.ClassCertificates153080
public import Erdos272.Arithmetic.N153080.CleanupRows153080
public import Erdos272.Arithmetic.CleanupMachineSound208

@[expose] public section

namespace JSP233.RowLightSlope153080
open CleanupRows153080 CleanupEval208 CleanupMachineSound208 ActualCleanupEval208
open LightFamily158375 LightSlope158375 ClassCertificates153080
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
  | 0, 0 => {⟨2, 114, 5⟩, ⟨2, 225, 1⟩, ⟨3, 114, 1⟩, ⟨11, 114, 1⟩}
  | 0, 1 => {⟨2, 163, 2⟩}
  | 1, 0 => {⟨2, 107, 6⟩, ⟨2, 204, 1⟩, ⟨3, 107, 2⟩, ⟨11, 107, 1⟩}
  | 1, 1 => {⟨2, 160, 2⟩}
  | 1, 2 => {⟨2, 233, 1⟩}
  | 2, 0 => {⟨2, 97, 8⟩, ⟨2, 174, 2⟩, ⟨2, 251, 1⟩, ⟨3, 97, 2⟩, ⟨11, 97, 1⟩}
  | 2, 1 => {⟨2, 157, 3⟩, ⟨3, 157, 1⟩}
  | 2, 2 => {⟨2, 232, 1⟩}
  | 3, 0 => {⟨2, 87, 9⟩, ⟨2, 144, 3⟩, ⟨2, 201, 1⟩, ⟨2, 258, 1⟩, ⟨3, 87, 3⟩, ⟨3, 159, 1⟩, ⟨11, 87, 1⟩}
  | 3, 1 => {⟨2, 155, 3⟩, ⟨3, 155, 1⟩}
  | 3, 2 => {⟨2, 231, 1⟩}
  | 4, 0 => {⟨2, 61, 20⟩, ⟨2, 92, 8⟩, ⟨2, 123, 5⟩, ⟨2, 154, 3⟩, ⟨2, 185, 2⟩, ⟨2, 216, 1⟩, ⟨2, 247, 1⟩, ⟨3, 61, 6⟩, ⟨3, 102, 2⟩, ⟨3, 143, 1⟩, ⟨5, 61, 2⟩, ⟨11, 61, 6⟩, ⟨11, 117, 1⟩}
  | 4, 1 => {⟨2, 152, 3⟩, ⟨3, 152, 1⟩}
  | 4, 2 => {⟨2, 230, 1⟩}
  | 5, 0 => {⟨2, 55, 24⟩, ⟨2, 83, 10⟩, ⟨2, 111, 6⟩, ⟨2, 139, 3⟩, ⟨2, 167, 2⟩, ⟨2, 195, 2⟩, ⟨2, 223, 1⟩, ⟨2, 251, 1⟩, ⟨3, 55, 8⟩, ⟨3, 92, 2⟩, ⟨3, 129, 1⟩, ⟨5, 55, 2⟩, ⟨7, 55, 1⟩, ⟨11, 55, 8⟩, ⟨11, 105, 1⟩}
  | 5, 1 => {⟨2, 149, 3⟩, ⟨3, 149, 1⟩}
  | 5, 2 => {⟨2, 229, 1⟩}
  | 6, 0 => {⟨2, 49, 31⟩, ⟨2, 74, 13⟩, ⟨2, 99, 7⟩, ⟨2, 124, 4⟩, ⟨2, 149, 3⟩, ⟨2, 174, 2⟩, ⟨2, 199, 1⟩, ⟨2, 224, 1⟩, ⟨2, 249, 1⟩, ⟨2, 274, 1⟩, ⟨3, 49, 10⟩, ⟨3, 82, 3⟩, ⟨3, 115, 1⟩, ⟨3, 148, 1⟩, ⟨5, 49, 4⟩, ⟨7, 49, 1⟩, ⟨11, 49, 10⟩, ⟨11, 94, 1⟩}
  | 6, 1 => {⟨2, 146, 3⟩, ⟨2, 274, 1⟩, ⟨3, 146, 1⟩}
  | 6, 2 => {⟨2, 228, 1⟩}
  | 7, 0 => {⟨2, 45, 36⟩, ⟨2, 68, 16⟩, ⟨2, 91, 9⟩, ⟨2, 114, 5⟩, ⟨2, 137, 4⟩, ⟨2, 160, 2⟩, ⟨2, 183, 2⟩, ⟨2, 206, 1⟩, ⟨2, 229, 1⟩, ⟨2, 252, 1⟩, ⟨2, 275, 1⟩, ⟨3, 45, 12⟩, ⟨3, 75, 4⟩, ⟨3, 105, 2⟩, ⟨3, 135, 1⟩, ⟨5, 45, 4⟩, ⟨5, 81, 1⟩, ⟨7, 45, 2⟩, ⟨11, 45, 13⟩, ⟨11, 86, 2⟩}
  | 7, 1 => {⟨2, 144, 3⟩, ⟨2, 268, 1⟩, ⟨3, 144, 1⟩}
  | 7, 2 => {⟨2, 227, 1⟩}
  | 8, 0 => {⟨2, 41, 44⟩, ⟨2, 62, 19⟩, ⟨2, 83, 10⟩, ⟨2, 104, 7⟩, ⟨2, 125, 4⟩, ⟨2, 146, 3⟩, ⟨2, 167, 2⟩, ⟨2, 188, 2⟩, ⟨2, 209, 1⟩, ⟨2, 230, 1⟩, ⟨2, 251, 1⟩, ⟨2, 272, 1⟩, ⟨3, 41, 14⟩, ⟨3, 69, 5⟩, ⟨3, 97, 2⟩, ⟨3, 125, 1⟩, ⟨3, 153, 1⟩, ⟨5, 41, 5⟩, ⟨5, 74, 1⟩, ⟨7, 41, 2⟩, ⟨11, 41, 17⟩, ⟨11, 79, 2⟩, ⟨11, 117, 1⟩}
  | 8, 1 => {⟨2, 140, 3⟩, ⟨2, 256, 1⟩, ⟨3, 140, 1⟩}
  | 8, 2 => {⟨2, 226, 1⟩}
  | _, _ => ∅

def slope : ℕ → ℕ
  | 0 => 1274
  | 1 => 1746
  | 2 => 2548
  | 3 => 3138
  | 4 => 7740
  | 5 => 9392
  | 6 => 12271
  | 7 => 15103
  | 8 => 18289
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
end JSP233.RowLightSlope153080
