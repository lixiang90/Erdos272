module

public import Erdos272.Counting.N158375.LightSlope158375
public import Erdos272.Arithmetic.N142758.ClassCertificates142758
public import Erdos272.Arithmetic.N142758.CleanupRows142758
public import Erdos272.Arithmetic.CleanupMachineSound208

@[expose] public section

namespace JSP233.RowLightSlope142758
open CleanupRows142758 CleanupEval208 CleanupMachineSound208 ActualCleanupEval208
open LightFamily158375 LightSlope158375 ClassCertificates142758
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

theorem length {k : ℕ} (hk : k < 38) : (row k).bands.length=7 := by
  interval_cases k <;> rfl

def terms (k : ℕ) (b : CrossBandCredit208.Band) : Finset Term :=
  match k, b.val with
  | 0, 0 => {⟨2, 112, 5⟩, ⟨2, 223, 1⟩, ⟨3, 112, 1⟩, ⟨11, 112, 1⟩}
  | 1, 0 => {⟨2, 110, 5⟩, ⟨2, 217, 1⟩, ⟨3, 110, 1⟩, ⟨11, 110, 1⟩}
  | 1, 1 => {⟨2, 157, 2⟩}
  | 2, 0 => {⟨2, 103, 6⟩, ⟨2, 196, 1⟩, ⟨3, 103, 2⟩, ⟨11, 103, 1⟩}
  | 2, 1 => {⟨2, 154, 2⟩}
  | 2, 2 => {⟨2, 225, 1⟩}
  | 3, 0 => {⟨2, 96, 7⟩, ⟨2, 175, 2⟩, ⟨2, 254, 1⟩, ⟨3, 96, 2⟩, ⟨11, 96, 1⟩}
  | 3, 1 => {⟨2, 152, 3⟩, ⟨3, 152, 1⟩}
  | 3, 2 => {⟨2, 224, 1⟩}
  | 4, 0 => {⟨2, 90, 8⟩, ⟨2, 157, 2⟩, ⟨2, 224, 1⟩, ⟨3, 90, 2⟩, ⟨11, 90, 1⟩}
  | 4, 1 => {⟨2, 150, 3⟩, ⟨3, 150, 1⟩}
  | 4, 2 => {⟨2, 224, 1⟩}
  | 5, 0 => {⟨2, 83, 10⟩, ⟨2, 136, 3⟩, ⟨2, 189, 1⟩, ⟨2, 242, 1⟩, ⟨3, 83, 3⟩, ⟨3, 151, 1⟩, ⟨5, 83, 1⟩, ⟨11, 83, 2⟩}
  | 5, 1 => {⟨2, 149, 3⟩, ⟨3, 149, 1⟩}
  | 5, 2 => {⟨2, 223, 1⟩}
  | 6, 0 => {⟨2, 61, 18⟩, ⟨2, 92, 8⟩, ⟨2, 123, 4⟩, ⟨2, 154, 2⟩, ⟨2, 185, 2⟩, ⟨2, 216, 1⟩, ⟨2, 247, 1⟩, ⟨3, 61, 6⟩, ⟨3, 102, 2⟩, ⟨3, 143, 1⟩, ⟨5, 61, 2⟩, ⟨11, 61, 5⟩, ⟨11, 117, 1⟩}
  | 6, 1 => {⟨2, 147, 3⟩, ⟨3, 147, 1⟩}
  | 6, 2 => {⟨2, 223, 1⟩}
  | 7, 0 => {⟨2, 57, 21⟩, ⟨2, 86, 9⟩, ⟨2, 115, 5⟩, ⟨2, 144, 3⟩, ⟨2, 173, 2⟩, ⟨2, 202, 1⟩, ⟨2, 231, 1⟩, ⟨2, 260, 1⟩, ⟨3, 57, 7⟩, ⟨3, 95, 2⟩, ⟨3, 133, 1⟩, ⟨5, 57, 2⟩, ⟨7, 57, 1⟩, ⟨11, 57, 7⟩, ⟨11, 109, 1⟩}
  | 7, 1 => {⟨2, 146, 3⟩, ⟨3, 146, 1⟩}
  | 7, 2 => {⟨2, 222, 1⟩}
  | 8, 0 => {⟨2, 53, 24⟩, ⟨2, 80, 11⟩, ⟨2, 107, 6⟩, ⟨2, 134, 3⟩, ⟨2, 161, 2⟩, ⟨2, 188, 2⟩, ⟨2, 215, 1⟩, ⟨2, 242, 1⟩, ⟨3, 53, 8⟩, ⟨3, 89, 2⟩, ⟨3, 125, 1⟩, ⟨5, 53, 2⟩, ⟨7, 53, 1⟩, ⟨11, 53, 8⟩, ⟨11, 102, 1⟩}
  | 8, 1 => {⟨2, 144, 3⟩, ⟨3, 144, 1⟩}
  | 8, 2 => {⟨2, 221, 1⟩}
  | 9, 0 => {⟨2, 51, 26⟩, ⟨2, 77, 11⟩, ⟨2, 103, 6⟩, ⟨2, 129, 4⟩, ⟨2, 155, 2⟩, ⟨2, 181, 2⟩, ⟨2, 207, 1⟩, ⟨2, 233, 1⟩, ⟨2, 259, 1⟩, ⟨3, 51, 8⟩, ⟨3, 85, 3⟩, ⟨3, 119, 1⟩, ⟨3, 153, 1⟩, ⟨5, 51, 3⟩, ⟨7, 51, 1⟩, ⟨11, 51, 8⟩, ⟨11, 98, 1⟩}
  | 9, 1 => {⟨2, 143, 3⟩, ⟨3, 143, 1⟩}
  | 9, 2 => {⟨2, 221, 1⟩}
  | 10, 0 => {⟨2, 49, 29⟩, ⟨2, 74, 12⟩, ⟨2, 99, 7⟩, ⟨2, 124, 4⟩, ⟨2, 149, 3⟩, ⟨2, 174, 2⟩, ⟨2, 199, 1⟩, ⟨2, 224, 1⟩, ⟨2, 249, 1⟩, ⟨3, 49, 9⟩, ⟨3, 82, 3⟩, ⟨3, 115, 1⟩, ⟨3, 148, 1⟩, ⟨5, 49, 3⟩, ⟨7, 49, 1⟩, ⟨11, 49, 9⟩, ⟨11, 94, 1⟩}
  | 10, 1 => {⟨2, 142, 3⟩, ⟨3, 142, 1⟩}
  | 10, 2 => {⟨2, 221, 1⟩}
  | 11, 0 => {⟨2, 47, 31⟩, ⟨2, 71, 13⟩, ⟨2, 95, 7⟩, ⟨2, 119, 4⟩, ⟨2, 143, 3⟩, ⟨2, 167, 2⟩, ⟨2, 191, 1⟩, ⟨2, 215, 1⟩, ⟨2, 239, 1⟩, ⟨2, 263, 1⟩, ⟨3, 47, 10⟩, ⟨3, 79, 3⟩, ⟨3, 111, 1⟩, ⟨3, 143, 1⟩, ⟨5, 47, 4⟩, ⟨7, 47, 1⟩, ⟨11, 47, 10⟩, ⟨11, 90, 1⟩}
  | 11, 1 => {⟨2, 140, 3⟩, ⟨2, 262, 1⟩, ⟨3, 140, 1⟩}
  | 11, 2 => {⟨2, 220, 1⟩}
  | 12, 0 => {⟨2, 45, 34⟩, ⟨2, 68, 15⟩, ⟨2, 91, 8⟩, ⟨2, 114, 5⟩, ⟨2, 137, 3⟩, ⟨2, 160, 2⟩, ⟨2, 183, 2⟩, ⟨2, 206, 1⟩, ⟨2, 229, 1⟩, ⟨2, 252, 1⟩, ⟨3, 45, 11⟩, ⟨3, 75, 4⟩, ⟨3, 105, 2⟩, ⟨3, 135, 1⟩, ⟨5, 45, 4⟩, ⟨5, 81, 1⟩, ⟨7, 45, 1⟩, ⟨11, 45, 12⟩, ⟨11, 86, 1⟩}
  | 12, 1 => {⟨2, 139, 3⟩, ⟨2, 259, 1⟩, ⟨3, 139, 1⟩}
  | 12, 2 => {⟨2, 220, 1⟩}
  | 13, 0 => {⟨2, 43, 37⟩, ⟨2, 65, 16⟩, ⟨2, 87, 9⟩, ⟨2, 109, 5⟩, ⟨2, 131, 4⟩, ⟨2, 153, 3⟩, ⟨2, 175, 2⟩, ⟨2, 197, 1⟩, ⟨2, 219, 1⟩, ⟨2, 241, 1⟩, ⟨2, 263, 1⟩, ⟨3, 43, 12⟩, ⟨3, 72, 4⟩, ⟨3, 101, 2⟩, ⟨3, 130, 1⟩, ⟨5, 43, 4⟩, ⟨5, 78, 1⟩, ⟨7, 43, 2⟩, ⟨11, 43, 13⟩, ⟨11, 83, 2⟩}
  | 13, 1 => {⟨2, 138, 3⟩, ⟨2, 256, 1⟩, ⟨3, 138, 1⟩}
  | 13, 2 => {⟨2, 219, 1⟩}
  | 14, 0 => {⟨2, 41, 41⟩, ⟨2, 62, 18⟩, ⟨2, 83, 10⟩, ⟨2, 104, 6⟩, ⟨2, 125, 4⟩, ⟨2, 146, 3⟩, ⟨2, 167, 2⟩, ⟨2, 188, 2⟩, ⟨2, 209, 1⟩, ⟨2, 230, 1⟩, ⟨2, 251, 1⟩, ⟨3, 41, 13⟩, ⟨3, 69, 4⟩, ⟨3, 97, 2⟩, ⟨3, 125, 1⟩, ⟨3, 153, 1⟩, ⟨5, 41, 5⟩, ⟨5, 74, 1⟩, ⟨7, 41, 2⟩, ⟨11, 41, 15⟩, ⟨11, 79, 2⟩, ⟨11, 117, 1⟩}
  | 14, 1 => {⟨2, 136, 3⟩, ⟨2, 250, 1⟩, ⟨3, 136, 1⟩}
  | 14, 2 => {⟨2, 219, 1⟩}
  | 15, 0 => {⟨2, 39, 45⟩, ⟨2, 59, 20⟩, ⟨2, 79, 11⟩, ⟨2, 99, 7⟩, ⟨2, 119, 4⟩, ⟨2, 139, 3⟩, ⟨2, 159, 2⟩, ⟨2, 179, 2⟩, ⟨2, 199, 1⟩, ⟨2, 219, 1⟩, ⟨2, 239, 1⟩, ⟨2, 259, 1⟩, ⟨3, 39, 15⟩, ⟨3, 65, 5⟩, ⟨3, 91, 2⟩, ⟨3, 117, 1⟩, ⟨3, 143, 1⟩, ⟨5, 39, 6⟩, ⟨5, 71, 1⟩, ⟨7, 39, 2⟩, ⟨11, 39, 19⟩, ⟨11, 75, 2⟩, ⟨11, 111, 1⟩}
  | 15, 1 => {⟨2, 135, 3⟩, ⟨2, 247, 1⟩, ⟨3, 135, 1⟩}
  | 15, 2 => {⟨2, 219, 1⟩}
  | 16, 0 => {⟨2, 113, 5⟩, ⟨2, 225, 1⟩, ⟨3, 113, 1⟩, ⟨11, 113, 1⟩}
  | 17, 0 => {⟨2, 111, 5⟩, ⟨2, 219, 1⟩, ⟨3, 111, 1⟩, ⟨11, 111, 1⟩}
  | 17, 1 => {⟨2, 159, 2⟩}
  | 18, 0 => {⟨2, 104, 6⟩, ⟨2, 198, 1⟩, ⟨3, 104, 2⟩, ⟨11, 104, 1⟩}
  | 18, 1 => {⟨2, 156, 2⟩}
  | 18, 2 => {⟨2, 227, 1⟩}
  | 19, 0 => {⟨2, 97, 7⟩, ⟨2, 177, 2⟩, ⟨2, 257, 1⟩, ⟨3, 97, 2⟩, ⟨11, 97, 1⟩}
  | 19, 1 => {⟨2, 154, 3⟩, ⟨3, 154, 1⟩}
  | 19, 2 => {⟨2, 226, 1⟩}
  | 20, 0 => {⟨2, 90, 8⟩, ⟨2, 156, 2⟩, ⟨2, 222, 1⟩, ⟨3, 90, 2⟩, ⟨11, 90, 1⟩}
  | 20, 1 => {⟨2, 152, 3⟩, ⟨3, 152, 1⟩}
  | 20, 2 => {⟨2, 226, 1⟩}
  | 21, 0 => {⟨2, 83, 10⟩, ⟨2, 135, 3⟩, ⟨2, 187, 2⟩, ⟨2, 239, 1⟩, ⟨3, 83, 3⟩, ⟨3, 151, 1⟩, ⟨5, 83, 1⟩, ⟨11, 83, 2⟩}
  | 21, 1 => {⟨2, 151, 3⟩, ⟨3, 151, 1⟩}
  | 21, 2 => {⟨2, 225, 1⟩}
  | 22, 0 => {⟨2, 65, 16⟩, ⟨2, 98, 7⟩, ⟨2, 131, 4⟩, ⟨2, 164, 2⟩, ⟨2, 197, 1⟩, ⟨2, 230, 1⟩, ⟨2, 263, 1⟩, ⟨3, 65, 5⟩, ⟨3, 109, 2⟩, ⟨3, 153, 1⟩, ⟨5, 65, 2⟩, ⟨11, 65, 3⟩}
  | 22, 1 => {⟨2, 150, 3⟩, ⟨3, 150, 1⟩}
  | 22, 2 => {⟨2, 225, 1⟩}
  | 23, 0 => {⟨2, 61, 19⟩, ⟨2, 92, 8⟩, ⟨2, 123, 4⟩, ⟨2, 154, 3⟩, ⟨2, 185, 2⟩, ⟨2, 216, 1⟩, ⟨2, 247, 1⟩, ⟨3, 61, 6⟩, ⟨3, 102, 2⟩, ⟨3, 143, 1⟩, ⟨5, 61, 2⟩, ⟨11, 61, 5⟩, ⟨11, 117, 1⟩}
  | 23, 1 => {⟨2, 149, 3⟩, ⟨3, 149, 1⟩}
  | 23, 2 => {⟨2, 225, 1⟩}
  | 24, 0 => {⟨2, 58, 21⟩, ⟨2, 87, 9⟩, ⟨2, 116, 5⟩, ⟨2, 145, 3⟩, ⟨2, 174, 2⟩, ⟨2, 203, 1⟩, ⟨2, 232, 1⟩, ⟨2, 261, 1⟩, ⟨3, 58, 7⟩, ⟨3, 97, 2⟩, ⟨3, 136, 1⟩, ⟨5, 58, 2⟩, ⟨7, 58, 1⟩, ⟨11, 58, 7⟩, ⟨11, 111, 1⟩}
  | 24, 1 => {⟨2, 148, 3⟩, ⟨3, 148, 1⟩}
  | 24, 2 => {⟨2, 224, 1⟩}
  | 25, 0 => {⟨2, 55, 23⟩, ⟨2, 83, 10⟩, ⟨2, 111, 5⟩, ⟨2, 139, 3⟩, ⟨2, 167, 2⟩, ⟨2, 195, 1⟩, ⟨2, 223, 1⟩, ⟨2, 251, 1⟩, ⟨3, 55, 7⟩, ⟨3, 92, 2⟩, ⟨3, 129, 1⟩, ⟨5, 55, 2⟩, ⟨7, 55, 1⟩, ⟨11, 55, 7⟩, ⟨11, 105, 1⟩}
  | 25, 1 => {⟨2, 146, 3⟩, ⟨3, 146, 1⟩}
  | 25, 2 => {⟨2, 224, 1⟩}
  | 26, 0 => {⟨2, 53, 25⟩, ⟨2, 80, 11⟩, ⟨2, 107, 6⟩, ⟨2, 134, 4⟩, ⟨2, 161, 2⟩, ⟨2, 188, 2⟩, ⟨2, 215, 1⟩, ⟨2, 242, 1⟩, ⟨2, 269, 1⟩, ⟨3, 53, 8⟩, ⟨3, 89, 3⟩, ⟨3, 125, 1⟩, ⟨5, 53, 3⟩, ⟨7, 53, 1⟩, ⟨11, 53, 8⟩, ⟨11, 102, 1⟩}
  | 26, 1 => {⟨2, 146, 3⟩, ⟨3, 146, 1⟩}
  | 26, 2 => {⟨2, 223, 1⟩}
  | 27, 0 => {⟨2, 51, 27⟩, ⟨2, 77, 12⟩, ⟨2, 103, 6⟩, ⟨2, 129, 4⟩, ⟨2, 155, 3⟩, ⟨2, 181, 2⟩, ⟨2, 207, 1⟩, ⟨2, 233, 1⟩, ⟨2, 259, 1⟩, ⟨3, 51, 9⟩, ⟨3, 85, 3⟩, ⟨3, 119, 1⟩, ⟨3, 153, 1⟩, ⟨5, 51, 3⟩, ⟨7, 51, 1⟩, ⟨11, 51, 9⟩, ⟨11, 98, 1⟩}
  | 27, 1 => {⟨2, 144, 3⟩, ⟨3, 144, 1⟩}
  | 27, 2 => {⟨2, 223, 1⟩}
  | 28, 0 => {⟨2, 49, 29⟩, ⟨2, 74, 13⟩, ⟨2, 99, 7⟩, ⟨2, 124, 4⟩, ⟨2, 149, 3⟩, ⟨2, 174, 2⟩, ⟨2, 199, 1⟩, ⟨2, 224, 1⟩, ⟨2, 249, 1⟩, ⟨3, 49, 9⟩, ⟨3, 82, 3⟩, ⟨3, 115, 1⟩, ⟨3, 148, 1⟩, ⟨5, 49, 3⟩, ⟨7, 49, 1⟩, ⟨11, 49, 9⟩, ⟨11, 94, 1⟩}
  | 28, 1 => {⟨2, 143, 3⟩, ⟨2, 269, 1⟩, ⟨3, 143, 1⟩}
  | 28, 2 => {⟨2, 223, 1⟩}
  | 29, 0 => {⟨2, 47, 32⟩, ⟨2, 71, 14⟩, ⟨2, 95, 7⟩, ⟨2, 119, 5⟩, ⟨2, 143, 3⟩, ⟨2, 167, 2⟩, ⟨2, 191, 1⟩, ⟨2, 215, 1⟩, ⟨2, 239, 1⟩, ⟨2, 263, 1⟩, ⟨3, 47, 10⟩, ⟨3, 79, 3⟩, ⟨3, 111, 1⟩, ⟨3, 143, 1⟩, ⟨5, 47, 4⟩, ⟨7, 47, 1⟩, ⟨11, 47, 11⟩, ⟨11, 90, 1⟩}
  | 29, 1 => {⟨2, 142, 3⟩, ⟨2, 266, 1⟩, ⟨3, 142, 1⟩}
  | 29, 2 => {⟨2, 222, 1⟩}
  | 30, 0 => {⟨2, 45, 35⟩, ⟨2, 68, 15⟩, ⟨2, 91, 8⟩, ⟨2, 114, 5⟩, ⟨2, 137, 3⟩, ⟨2, 160, 2⟩, ⟨2, 183, 2⟩, ⟨2, 206, 1⟩, ⟨2, 229, 1⟩, ⟨2, 252, 1⟩, ⟨3, 45, 11⟩, ⟨3, 75, 4⟩, ⟨3, 105, 2⟩, ⟨3, 135, 1⟩, ⟨5, 45, 4⟩, ⟨5, 81, 1⟩, ⟨7, 45, 2⟩, ⟨11, 45, 14⟩, ⟨11, 86, 1⟩}
  | 30, 1 => {⟨2, 141, 3⟩, ⟨2, 263, 1⟩, ⟨3, 141, 1⟩}
  | 30, 2 => {⟨2, 222, 1⟩}
  | 31, 0 => {⟨2, 43, 38⟩, ⟨2, 65, 16⟩, ⟨2, 87, 9⟩, ⟨2, 109, 6⟩, ⟨2, 131, 4⟩, ⟨2, 153, 3⟩, ⟨2, 175, 2⟩, ⟨2, 197, 1⟩, ⟨2, 219, 1⟩, ⟨2, 241, 1⟩, ⟨2, 263, 1⟩, ⟨3, 43, 12⟩, ⟨3, 72, 4⟩, ⟨3, 101, 2⟩, ⟨3, 130, 1⟩, ⟨5, 43, 4⟩, ⟨5, 78, 1⟩, ⟨7, 43, 2⟩, ⟨11, 43, 14⟩, ⟨11, 83, 2⟩}
  | 31, 1 => {⟨2, 139, 3⟩, ⟨2, 257, 1⟩, ⟨3, 139, 1⟩}
  | 31, 2 => {⟨2, 221, 1⟩}
  | 32, 0 => {⟨2, 41, 42⟩, ⟨2, 62, 18⟩, ⟨2, 83, 10⟩, ⟨2, 104, 6⟩, ⟨2, 125, 4⟩, ⟨2, 146, 3⟩, ⟨2, 167, 2⟩, ⟨2, 188, 2⟩, ⟨2, 209, 1⟩, ⟨2, 230, 1⟩, ⟨2, 251, 1⟩, ⟨3, 41, 14⟩, ⟨3, 69, 5⟩, ⟨3, 97, 2⟩, ⟨3, 125, 1⟩, ⟨3, 153, 1⟩, ⟨5, 41, 5⟩, ⟨5, 74, 1⟩, ⟨7, 41, 2⟩, ⟨11, 41, 17⟩, ⟨11, 79, 2⟩, ⟨11, 117, 1⟩}
  | 32, 1 => {⟨2, 138, 3⟩, ⟨2, 254, 1⟩, ⟨3, 138, 1⟩}
  | 32, 2 => {⟨2, 221, 1⟩}
  | 33, 0 => {⟨2, 39, 46⟩, ⟨2, 59, 20⟩, ⟨2, 79, 11⟩, ⟨2, 99, 7⟩, ⟨2, 119, 5⟩, ⟨2, 139, 3⟩, ⟨2, 159, 2⟩, ⟨2, 179, 2⟩, ⟨2, 199, 1⟩, ⟨2, 219, 1⟩, ⟨2, 239, 1⟩, ⟨2, 259, 1⟩, ⟨3, 39, 15⟩, ⟨3, 65, 5⟩, ⟨3, 91, 2⟩, ⟨3, 117, 1⟩, ⟨3, 143, 1⟩, ⟨5, 39, 6⟩, ⟨5, 71, 1⟩, ⟨7, 39, 2⟩, ⟨11, 39, 18⟩, ⟨11, 75, 2⟩, ⟨11, 111, 1⟩}
  | 33, 1 => {⟨2, 136, 3⟩, ⟨2, 248, 1⟩, ⟨3, 136, 1⟩}
  | 33, 2 => {⟨2, 220, 1⟩}
  | 34, 0 => {⟨2, 120, 4⟩, ⟨2, 231, 1⟩, ⟨3, 120, 1⟩}
  | 34, 1 => {⟨2, 177, 2⟩}
  | 34, 2 => {⟨2, 257, 1⟩}
  | 35, 0 => {⟨2, 100, 7⟩, ⟨2, 171, 2⟩, ⟨2, 242, 1⟩, ⟨3, 100, 2⟩, ⟨11, 100, 1⟩}
  | 35, 1 => {⟨2, 172, 2⟩}
  | 35, 2 => {⟨2, 255, 1⟩}
  | 36, 0 => {⟨2, 67, 15⟩, ⟨2, 101, 6⟩, ⟨2, 135, 3⟩, ⟨2, 169, 2⟩, ⟨2, 203, 1⟩, ⟨2, 237, 1⟩, ⟨3, 67, 5⟩, ⟨3, 112, 1⟩, ⟨5, 67, 2⟩, ⟨11, 67, 4⟩}
  | 36, 1 => {⟨2, 168, 2⟩}
  | 36, 2 => {⟨2, 253, 1⟩}
  | 37, 0 => {⟨2, 59, 20⟩, ⟨2, 89, 8⟩, ⟨2, 119, 4⟩, ⟨2, 149, 3⟩, ⟨2, 179, 2⟩, ⟨2, 209, 1⟩, ⟨2, 239, 1⟩, ⟨3, 59, 6⟩, ⟨3, 99, 2⟩, ⟨3, 139, 1⟩, ⟨5, 59, 2⟩, ⟨11, 59, 6⟩, ⟨11, 113, 1⟩}
  | 37, 1 => {⟨2, 164, 2⟩}
  | 37, 2 => {⟨2, 252, 1⟩}
  | _, _ => ∅

def slope : ℕ → ℕ
  | 0 => 912
  | 1 => 1230
  | 2 => 1686
  | 3 => 2346
  | 4 => 2460
  | 5 => 3372
  | 6 => 6906
  | 7 => 8160
  | 8 => 9186
  | 9 => 9984
  | 10 => 10896
  | 11 => 11853
  | 12 => 13449
  | 13 => 14817
  | 14 => 16527
  | 15 => 18465
  | 16 => 920
  | 17 => 1242
  | 18 => 1702
  | 19 => 2369
  | 20 => 2484
  | 21 => 3519
  | 22 => 6049
  | 23 => 7199
  | 24 => 8234
  | 25 => 8579
  | 26 => 9844
  | 27 => 10649
  | 28 => 11270
  | 29 => 12420
  | 30 => 14030
  | 31 => 15295
  | 32 => 17250
  | 33 => 18745
  | 34 => 1404
  | 35 => 2314
  | 36 => 5824
  | 37 => 8034
  | _ => 0

def FiniteFacts (k : ℕ) (hk : k < 38) : Prop :=
  (∀ b : CrossBandCredit208.Band,
    BandFacts (row k).high (data k).steps (At (row k) (length hk) b) (terms k b) ∧
      ∀ t ∈ terms k b, (t.p,(row k).low/(t.q*(t.q+1)),t.count) ∈ Required) ∧
    RowSlope (row k) (length hk) (terms k) = slope k

local instance (k : ℕ) (hk : k < 38) : Decidable (FiniteFacts k hk) :=
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

theorem facts21 : FiniteFacts 21 (by decide) := by decide +kernel
#print axioms facts21

theorem facts22 : FiniteFacts 22 (by decide) := by decide +kernel
#print axioms facts22

theorem facts23 : FiniteFacts 23 (by decide) := by decide +kernel
#print axioms facts23

theorem facts24 : FiniteFacts 24 (by decide) := by decide +kernel
#print axioms facts24

theorem facts25 : FiniteFacts 25 (by decide) := by decide +kernel
#print axioms facts25

theorem facts26 : FiniteFacts 26 (by decide) := by decide +kernel
#print axioms facts26

theorem facts27 : FiniteFacts 27 (by decide) := by decide +kernel
#print axioms facts27

theorem facts28 : FiniteFacts 28 (by decide) := by decide +kernel
#print axioms facts28

theorem facts29 : FiniteFacts 29 (by decide) := by decide +kernel
#print axioms facts29

theorem facts30 : FiniteFacts 30 (by decide) := by decide +kernel
#print axioms facts30

theorem facts31 : FiniteFacts 31 (by decide) := by decide +kernel
#print axioms facts31

theorem facts32 : FiniteFacts 32 (by decide) := by decide +kernel
#print axioms facts32

theorem facts33 : FiniteFacts 33 (by decide) := by decide +kernel
#print axioms facts33

theorem facts34 : FiniteFacts 34 (by decide) := by decide +kernel
#print axioms facts34

theorem facts35 : FiniteFacts 35 (by decide) := by decide +kernel
#print axioms facts35

theorem facts36 : FiniteFacts 36 (by decide) := by decide +kernel
#print axioms facts36

theorem facts37 : FiniteFacts 37 (by decide) := by decide +kernel
#print axioms facts37

theorem facts {k : ℕ} (hk : k < 38) : FiniteFacts k hk := by
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
  · exact facts21
  · exact facts22
  · exact facts23
  · exact facts24
  · exact facts25
  · exact facts26
  · exact facts27
  · exact facts28
  · exact facts29
  · exact facts30
  · exact facts31
  · exact facts32
  · exact facts33
  · exact facts34
  · exact facts35
  · exact facts36
  · exact facts37

theorem slope_bound {k N : ℕ} (hk : k < 38)
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
end JSP233.RowLightSlope142758
