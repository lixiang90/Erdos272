module

public import Erdos272.Counting.N158375.LightSlope158375
public import Erdos272.Arithmetic.N130000.ClassCertificates130000
public import Erdos272.Arithmetic.N130000.CleanupRows130000
public import Erdos272.Arithmetic.CleanupMachineSound208

@[expose] public section

namespace JSP233.RowLightSlope130000
open CleanupRows130000 CleanupEval208 CleanupMachineSound208 ActualCleanupEval208
open LightFamily158375 LightSlope158375 ClassCertificates130000
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

theorem length {k : ℕ} (hk : k < 48) : (row k).bands.length=7 := by
  interval_cases k <;> rfl

def terms (k : ℕ) (b : CrossBandCredit208.Band) : Finset Term :=
  match k, b.val with
  | 0, 0 => {⟨2, 104, 5⟩, ⟨2, 205, 1⟩, ⟨3, 104, 1⟩, ⟨11, 104, 1⟩}
  | 1, 0 => {⟨2, 100, 6⟩, ⟨2, 193, 1⟩, ⟨3, 100, 2⟩, ⟨11, 100, 1⟩}
  | 1, 1 => {⟨2, 214, 1⟩}
  | 2, 0 => {⟨2, 96, 6⟩, ⟨2, 181, 1⟩, ⟨3, 96, 2⟩, ⟨11, 96, 1⟩}
  | 2, 1 => {⟨2, 213, 1⟩}
  | 3, 0 => {⟨2, 92, 7⟩, ⟨2, 169, 2⟩, ⟨2, 246, 1⟩, ⟨3, 92, 2⟩, ⟨11, 92, 1⟩}
  | 3, 1 => {⟨2, 213, 1⟩}
  | 4, 0 => {⟨2, 88, 8⟩, ⟨2, 157, 2⟩, ⟨2, 226, 1⟩, ⟨3, 88, 2⟩, ⟨11, 88, 1⟩}
  | 4, 1 => {⟨2, 212, 1⟩}
  | 5, 0 => {⟨2, 83, 9⟩, ⟨2, 142, 3⟩, ⟨2, 201, 1⟩, ⟨3, 83, 3⟩, ⟨11, 83, 1⟩}
  | 5, 1 => {⟨2, 212, 1⟩}
  | 6, 0 => {⟨2, 78, 10⟩, ⟨2, 127, 3⟩, ⟨2, 176, 2⟩, ⟨2, 225, 1⟩, ⟨3, 78, 3⟩, ⟨3, 142, 1⟩, ⟨5, 78, 1⟩, ⟨11, 78, 2⟩}
  | 6, 1 => {⟨2, 212, 1⟩}
  | 7, 0 => {⟨2, 61, 17⟩, ⟨2, 92, 7⟩, ⟨2, 123, 4⟩, ⟨2, 154, 2⟩, ⟨2, 185, 1⟩, ⟨2, 216, 1⟩, ⟨2, 247, 1⟩, ⟨3, 61, 5⟩, ⟨3, 102, 2⟩, ⟨3, 143, 1⟩, ⟨5, 61, 2⟩, ⟨11, 61, 4⟩}
  | 7, 1 => {⟨2, 183, 1⟩}
  | 8, 0 => {⟨2, 59, 18⟩, ⟨2, 89, 8⟩, ⟨2, 119, 4⟩, ⟨2, 149, 2⟩, ⟨2, 179, 2⟩, ⟨2, 209, 1⟩, ⟨2, 239, 1⟩, ⟨3, 59, 6⟩, ⟨3, 99, 2⟩, ⟨3, 139, 1⟩, ⟨5, 59, 2⟩, ⟨11, 59, 5⟩}
  | 8, 1 => {⟨2, 183, 1⟩}
  | 9, 0 => {⟨2, 57, 19⟩, ⟨2, 86, 8⟩, ⟨2, 115, 4⟩, ⟨2, 144, 3⟩, ⟨2, 173, 2⟩, ⟨2, 202, 1⟩, ⟨2, 231, 1⟩, ⟨3, 57, 6⟩, ⟨3, 95, 2⟩, ⟨3, 133, 1⟩, ⟨5, 57, 2⟩, ⟨11, 57, 5⟩, ⟨11, 109, 1⟩}
  | 9, 1 => {⟨2, 182, 1⟩}
  | 10, 0 => {⟨2, 55, 21⟩, ⟨2, 83, 9⟩, ⟨2, 111, 5⟩, ⟨2, 139, 3⟩, ⟨2, 167, 2⟩, ⟨2, 195, 1⟩, ⟨2, 223, 1⟩, ⟨2, 251, 1⟩, ⟨3, 55, 7⟩, ⟨3, 92, 2⟩, ⟨3, 129, 1⟩, ⟨5, 55, 2⟩, ⟨7, 55, 1⟩, ⟨11, 55, 7⟩, ⟨11, 105, 1⟩}
  | 10, 1 => {⟨2, 182, 1⟩}
  | 11, 0 => {⟨2, 53, 22⟩, ⟨2, 80, 10⟩, ⟨2, 107, 5⟩, ⟨2, 134, 3⟩, ⟨2, 161, 2⟩, ⟨2, 188, 1⟩, ⟨2, 215, 1⟩, ⟨2, 242, 1⟩, ⟨3, 53, 7⟩, ⟨3, 89, 2⟩, ⟨3, 125, 1⟩, ⟨5, 53, 2⟩, ⟨7, 53, 1⟩, ⟨11, 53, 6⟩, ⟨11, 102, 1⟩}
  | 11, 1 => {⟨2, 181, 1⟩}
  | 12, 0 => {⟨2, 51, 24⟩, ⟨2, 77, 10⟩, ⟨2, 103, 6⟩, ⟨2, 129, 3⟩, ⟨2, 155, 2⟩, ⟨2, 181, 1⟩, ⟨2, 207, 1⟩, ⟨2, 233, 1⟩, ⟨3, 51, 8⟩, ⟨3, 85, 2⟩, ⟨3, 119, 1⟩, ⟨5, 51, 2⟩, ⟨7, 51, 1⟩, ⟨11, 51, 8⟩, ⟨11, 98, 1⟩}
  | 12, 1 => {⟨2, 181, 1⟩}
  | 13, 0 => {⟨2, 49, 26⟩, ⟨2, 74, 11⟩, ⟨2, 99, 6⟩, ⟨2, 124, 4⟩, ⟨2, 149, 2⟩, ⟨2, 174, 2⟩, ⟨2, 199, 1⟩, ⟨2, 224, 1⟩, ⟨2, 249, 1⟩, ⟨3, 49, 8⟩, ⟨3, 82, 3⟩, ⟨3, 115, 1⟩, ⟨5, 49, 3⟩, ⟨7, 49, 1⟩, ⟨11, 49, 8⟩, ⟨11, 94, 1⟩}
  | 13, 1 => {⟨2, 180, 1⟩}
  | 14, 0 => {⟨2, 47, 28⟩, ⟨2, 71, 12⟩, ⟨2, 95, 7⟩, ⟨2, 119, 4⟩, ⟨2, 143, 3⟩, ⟨2, 167, 2⟩, ⟨2, 191, 1⟩, ⟨2, 215, 1⟩, ⟨2, 239, 1⟩, ⟨3, 47, 9⟩, ⟨3, 79, 3⟩, ⟨3, 111, 1⟩, ⟨3, 143, 1⟩, ⟨5, 47, 3⟩, ⟨7, 47, 1⟩, ⟨11, 47, 9⟩, ⟨11, 90, 1⟩}
  | 14, 1 => {⟨2, 180, 1⟩}
  | 15, 0 => {⟨2, 45, 31⟩, ⟨2, 68, 13⟩, ⟨2, 91, 7⟩, ⟨2, 114, 4⟩, ⟨2, 137, 3⟩, ⟨2, 160, 2⟩, ⟨2, 183, 1⟩, ⟨2, 206, 1⟩, ⟨2, 229, 1⟩, ⟨2, 252, 1⟩, ⟨3, 45, 10⟩, ⟨3, 75, 3⟩, ⟨3, 105, 1⟩, ⟨3, 135, 1⟩, ⟨5, 45, 4⟩, ⟨7, 45, 1⟩, ⟨11, 45, 10⟩, ⟨11, 86, 1⟩}
  | 15, 1 => {⟨2, 179, 2⟩}
  | 16, 0 => {⟨2, 43, 34⟩, ⟨2, 65, 15⟩, ⟨2, 87, 8⟩, ⟨2, 109, 5⟩, ⟨2, 131, 3⟩, ⟨2, 153, 2⟩, ⟨2, 175, 2⟩, ⟨2, 197, 1⟩, ⟨2, 219, 1⟩, ⟨2, 241, 1⟩, ⟨3, 43, 11⟩, ⟨3, 72, 4⟩, ⟨3, 101, 2⟩, ⟨3, 130, 1⟩, ⟨5, 43, 4⟩, ⟨5, 78, 1⟩, ⟨7, 43, 1⟩, ⟨11, 43, 12⟩, ⟨11, 83, 1⟩}
  | 16, 1 => {⟨2, 179, 2⟩}
  | 17, 0 => {⟨2, 41, 37⟩, ⟨2, 62, 16⟩, ⟨2, 83, 9⟩, ⟨2, 104, 5⟩, ⟨2, 125, 4⟩, ⟨2, 146, 3⟩, ⟨2, 167, 2⟩, ⟨2, 188, 1⟩, ⟨2, 209, 1⟩, ⟨2, 230, 1⟩, ⟨2, 251, 1⟩, ⟨3, 41, 12⟩, ⟨3, 69, 4⟩, ⟨3, 97, 2⟩, ⟨3, 125, 1⟩, ⟨5, 41, 4⟩, ⟨5, 74, 1⟩, ⟨7, 41, 2⟩, ⟨11, 41, 13⟩, ⟨11, 79, 2⟩}
  | 17, 1 => {⟨2, 146, 3⟩, ⟨3, 146, 1⟩}
  | 18, 0 => {⟨2, 40, 39⟩, ⟨2, 60, 17⟩, ⟨2, 80, 10⟩, ⟨2, 100, 6⟩, ⟨2, 120, 4⟩, ⟨2, 140, 3⟩, ⟨2, 160, 2⟩, ⟨2, 180, 1⟩, ⟨2, 200, 1⟩, ⟨2, 220, 1⟩, ⟨2, 240, 1⟩, ⟨3, 40, 13⟩, ⟨3, 67, 4⟩, ⟨3, 94, 2⟩, ⟨3, 121, 1⟩, ⟨5, 40, 4⟩, ⟨5, 72, 1⟩, ⟨7, 40, 2⟩, ⟨11, 40, 15⟩, ⟨11, 77, 2⟩}
  | 18, 1 => {⟨2, 146, 3⟩, ⟨3, 146, 1⟩}
  | 19, 0 => {⟨2, 39, 41⟩, ⟨2, 59, 18⟩, ⟨2, 79, 10⟩, ⟨2, 99, 6⟩, ⟨2, 119, 4⟩, ⟨2, 139, 3⟩, ⟨2, 159, 2⟩, ⟨2, 179, 2⟩, ⟨2, 199, 1⟩, ⟨2, 219, 1⟩, ⟨2, 239, 1⟩, ⟨3, 39, 13⟩, ⟨3, 65, 5⟩, ⟨3, 91, 2⟩, ⟨3, 117, 1⟩, ⟨3, 143, 1⟩, ⟨5, 39, 5⟩, ⟨5, 71, 1⟩, ⟨7, 39, 2⟩, ⟨11, 39, 15⟩, ⟨11, 75, 2⟩, ⟨11, 111, 1⟩}
  | 19, 1 => {⟨2, 145, 3⟩, ⟨3, 145, 1⟩}
  | 20, 0 => {⟨2, 38, 43⟩, ⟨2, 57, 19⟩, ⟨2, 76, 11⟩, ⟨2, 95, 7⟩, ⟨2, 114, 4⟩, ⟨2, 133, 3⟩, ⟨2, 152, 2⟩, ⟨2, 171, 2⟩, ⟨2, 190, 1⟩, ⟨2, 209, 1⟩, ⟨2, 228, 1⟩, ⟨2, 247, 1⟩, ⟨3, 38, 14⟩, ⟨3, 64, 5⟩, ⟨3, 90, 2⟩, ⟨3, 116, 1⟩, ⟨3, 142, 1⟩, ⟨5, 38, 5⟩, ⟨5, 69, 1⟩, ⟨7, 38, 2⟩, ⟨11, 38, 16⟩, ⟨11, 73, 2⟩, ⟨11, 108, 1⟩}
  | 20, 1 => {⟨2, 145, 3⟩, ⟨3, 145, 1⟩}
  | 21, 0 => {⟨2, 37, 46⟩, ⟨2, 56, 20⟩, ⟨2, 75, 11⟩, ⟨2, 94, 7⟩, ⟨2, 113, 5⟩, ⟨2, 132, 3⟩, ⟨2, 151, 2⟩, ⟨2, 170, 2⟩, ⟨2, 189, 1⟩, ⟨2, 208, 1⟩, ⟨2, 227, 1⟩, ⟨2, 246, 1⟩, ⟨3, 37, 15⟩, ⟨3, 62, 5⟩, ⟨3, 87, 2⟩, ⟨3, 112, 1⟩, ⟨3, 137, 1⟩, ⟨5, 37, 6⟩, ⟨5, 67, 1⟩, ⟨7, 37, 2⟩, ⟨11, 37, 18⟩, ⟨11, 71, 2⟩, ⟨11, 105, 1⟩}
  | 21, 1 => {⟨2, 144, 3⟩, ⟨3, 144, 1⟩}
  | 22, 0 => {⟨2, 35, 51⟩, ⟨2, 53, 22⟩, ⟨2, 71, 12⟩, ⟨2, 89, 8⟩, ⟨2, 107, 5⟩, ⟨2, 125, 4⟩, ⟨2, 143, 3⟩, ⟨2, 161, 2⟩, ⟨2, 179, 2⟩, ⟨2, 197, 1⟩, ⟨2, 215, 1⟩, ⟨2, 233, 1⟩, ⟨2, 251, 1⟩, ⟨3, 35, 17⟩, ⟨3, 59, 6⟩, ⟨3, 83, 3⟩, ⟨3, 107, 1⟩, ⟨3, 131, 1⟩, ⟨5, 35, 6⟩, ⟨5, 63, 2⟩, ⟨7, 35, 2⟩, ⟨11, 35, 20⟩, ⟨11, 67, 3⟩, ⟨11, 99, 1⟩}
  | 22, 1 => {⟨2, 143, 3⟩, ⟨3, 143, 1⟩}
  | 23, 0 => {⟨2, 34, 54⟩, ⟨2, 51, 24⟩, ⟨2, 68, 13⟩, ⟨2, 85, 8⟩, ⟨2, 102, 6⟩, ⟨2, 119, 4⟩, ⟨2, 136, 3⟩, ⟨2, 153, 2⟩, ⟨2, 170, 2⟩, ⟨2, 187, 1⟩, ⟨2, 204, 1⟩, ⟨2, 221, 1⟩, ⟨2, 238, 1⟩, ⟨3, 34, 18⟩, ⟨3, 57, 6⟩, ⟨3, 80, 3⟩, ⟨3, 103, 2⟩, ⟨3, 126, 1⟩, ⟨5, 34, 6⟩, ⟨5, 62, 2⟩, ⟨7, 34, 2⟩, ⟨11, 34, 22⟩, ⟨11, 65, 4⟩, ⟨11, 96, 1⟩}
  | 23, 1 => {⟨2, 142, 3⟩, ⟨3, 142, 1⟩}
  | 24, 0 => {⟨2, 106, 5⟩, ⟨2, 209, 1⟩, ⟨3, 106, 1⟩, ⟨11, 106, 1⟩}
  | 25, 0 => {⟨2, 99, 6⟩, ⟨2, 188, 1⟩, ⟨3, 99, 2⟩, ⟨11, 99, 1⟩}
  | 25, 1 => {⟨2, 217, 1⟩}
  | 26, 0 => {⟨2, 90, 8⟩, ⟨2, 161, 2⟩, ⟨2, 232, 1⟩, ⟨3, 90, 2⟩, ⟨11, 90, 1⟩}
  | 26, 1 => {⟨2, 216, 1⟩}
  | 27, 0 => {⟨2, 80, 10⟩, ⟨2, 131, 3⟩, ⟨2, 182, 1⟩, ⟨2, 233, 1⟩, ⟨3, 80, 3⟩, ⟨3, 146, 1⟩, ⟨5, 80, 1⟩, ⟨11, 80, 2⟩}
  | 27, 1 => {⟨2, 216, 1⟩}
  | 28, 0 => {⟨2, 59, 18⟩, ⟨2, 89, 8⟩, ⟨2, 119, 4⟩, ⟨2, 149, 2⟩, ⟨2, 179, 2⟩, ⟨2, 209, 1⟩, ⟨2, 239, 1⟩, ⟨3, 59, 6⟩, ⟨3, 99, 2⟩, ⟨3, 139, 1⟩, ⟨5, 59, 2⟩, ⟨11, 59, 5⟩, ⟨11, 113, 1⟩}
  | 28, 1 => {⟨2, 185, 1⟩}
  | 29, 0 => {⟨2, 55, 21⟩, ⟨2, 83, 9⟩, ⟨2, 111, 5⟩, ⟨2, 139, 3⟩, ⟨2, 167, 2⟩, ⟨2, 195, 1⟩, ⟨2, 223, 1⟩, ⟨2, 251, 1⟩, ⟨3, 55, 7⟩, ⟨3, 92, 2⟩, ⟨3, 129, 1⟩, ⟨5, 55, 2⟩, ⟨7, 55, 1⟩, ⟨11, 55, 7⟩, ⟨11, 105, 1⟩}
  | 29, 1 => {⟨2, 184, 1⟩}
  | 30, 0 => {⟨2, 51, 25⟩, ⟨2, 77, 11⟩, ⟨2, 103, 6⟩, ⟨2, 129, 3⟩, ⟨2, 155, 2⟩, ⟨2, 181, 2⟩, ⟨2, 207, 1⟩, ⟨2, 233, 1⟩, ⟨3, 51, 8⟩, ⟨3, 85, 3⟩, ⟨3, 119, 1⟩, ⟨5, 51, 3⟩, ⟨7, 51, 1⟩, ⟨11, 51, 8⟩, ⟨11, 98, 1⟩}
  | 30, 1 => {⟨2, 184, 1⟩}
  | 31, 0 => {⟨2, 47, 29⟩, ⟨2, 71, 12⟩, ⟨2, 95, 7⟩, ⟨2, 119, 4⟩, ⟨2, 143, 3⟩, ⟨2, 167, 2⟩, ⟨2, 191, 1⟩, ⟨2, 215, 1⟩, ⟨2, 239, 1⟩, ⟨3, 47, 9⟩, ⟨3, 79, 3⟩, ⟨3, 111, 1⟩, ⟨3, 143, 1⟩, ⟨5, 47, 3⟩, ⟨7, 47, 1⟩, ⟨11, 47, 9⟩, ⟨11, 90, 1⟩}
  | 31, 1 => {⟨2, 182, 1⟩}
  | 32, 0 => {⟨2, 43, 35⟩, ⟨2, 65, 15⟩, ⟨2, 87, 8⟩, ⟨2, 109, 5⟩, ⟨2, 131, 3⟩, ⟨2, 153, 2⟩, ⟨2, 175, 2⟩, ⟨2, 197, 1⟩, ⟨2, 219, 1⟩, ⟨2, 241, 1⟩, ⟨3, 43, 11⟩, ⟨3, 72, 4⟩, ⟨3, 101, 2⟩, ⟨3, 130, 1⟩, ⟨5, 43, 4⟩, ⟨5, 78, 1⟩, ⟨7, 43, 2⟩, ⟨11, 43, 14⟩, ⟨11, 83, 1⟩}
  | 32, 1 => {⟨2, 149, 2⟩}
  | 33, 0 => {⟨2, 41, 38⟩, ⟨2, 62, 16⟩, ⟨2, 83, 9⟩, ⟨2, 104, 6⟩, ⟨2, 125, 4⟩, ⟨2, 146, 3⟩, ⟨2, 167, 2⟩, ⟨2, 188, 1⟩, ⟨2, 209, 1⟩, ⟨2, 230, 1⟩, ⟨2, 251, 1⟩, ⟨3, 41, 12⟩, ⟨3, 69, 4⟩, ⟨3, 97, 2⟩, ⟨3, 125, 1⟩, ⟨5, 41, 4⟩, ⟨5, 74, 1⟩, ⟨7, 41, 2⟩, ⟨11, 41, 14⟩, ⟨11, 79, 2⟩}
  | 33, 1 => {⟨2, 148, 3⟩, ⟨3, 148, 1⟩}
  | 34, 0 => {⟨2, 39, 42⟩, ⟨2, 59, 18⟩, ⟨2, 79, 10⟩, ⟨2, 99, 6⟩, ⟨2, 119, 4⟩, ⟨2, 139, 3⟩, ⟨2, 159, 2⟩, ⟨2, 179, 2⟩, ⟨2, 199, 1⟩, ⟨2, 219, 1⟩, ⟨2, 239, 1⟩, ⟨3, 39, 14⟩, ⟨3, 65, 5⟩, ⟨3, 91, 2⟩, ⟨3, 117, 1⟩, ⟨3, 143, 1⟩, ⟨5, 39, 5⟩, ⟨5, 71, 1⟩, ⟨7, 39, 2⟩, ⟨11, 39, 17⟩, ⟨11, 75, 2⟩, ⟨11, 111, 1⟩}
  | 34, 1 => {⟨2, 147, 3⟩, ⟨3, 147, 1⟩}
  | 35, 0 => {⟨2, 37, 47⟩, ⟨2, 56, 20⟩, ⟨2, 75, 11⟩, ⟨2, 94, 7⟩, ⟨2, 113, 5⟩, ⟨2, 132, 3⟩, ⟨2, 151, 2⟩, ⟨2, 170, 2⟩, ⟨2, 189, 1⟩, ⟨2, 208, 1⟩, ⟨2, 227, 1⟩, ⟨2, 246, 1⟩, ⟨3, 37, 15⟩, ⟨3, 62, 5⟩, ⟨3, 87, 2⟩, ⟨3, 112, 1⟩, ⟨3, 137, 1⟩, ⟨5, 37, 6⟩, ⟨5, 67, 1⟩, ⟨7, 37, 2⟩, ⟨11, 37, 19⟩, ⟨11, 71, 2⟩, ⟨11, 105, 1⟩}
  | 35, 1 => {⟨2, 146, 3⟩, ⟨3, 146, 1⟩}
  | 36, 0 => {⟨2, 108, 5⟩, ⟨2, 213, 1⟩, ⟨3, 108, 1⟩, ⟨11, 108, 1⟩}
  | 37, 0 => {⟨2, 96, 7⟩, ⟨2, 177, 2⟩, ⟨2, 258, 1⟩, ⟨3, 96, 2⟩, ⟨11, 96, 1⟩}
  | 37, 1 => {⟨2, 221, 1⟩}
  | 38, 0 => {⟨2, 82, 10⟩, ⟨2, 135, 3⟩, ⟨2, 188, 1⟩, ⟨2, 241, 1⟩, ⟨3, 82, 3⟩, ⟨3, 150, 1⟩, ⟨5, 82, 1⟩, ⟨11, 82, 2⟩}
  | 38, 1 => {⟨2, 220, 1⟩}
  | 39, 0 => {⟨2, 57, 20⟩, ⟨2, 86, 9⟩, ⟨2, 115, 5⟩, ⟨2, 144, 3⟩, ⟨2, 173, 2⟩, ⟨2, 202, 1⟩, ⟨2, 231, 1⟩, ⟨2, 260, 1⟩, ⟨3, 57, 6⟩, ⟨3, 95, 2⟩, ⟨3, 133, 1⟩, ⟨5, 57, 2⟩, ⟨11, 57, 6⟩, ⟨11, 109, 1⟩}
  | 39, 1 => {⟨2, 189, 1⟩}
  | 40, 0 => {⟨2, 49, 28⟩, ⟨2, 74, 12⟩, ⟨2, 99, 6⟩, ⟨2, 124, 4⟩, ⟨2, 149, 3⟩, ⟨2, 174, 2⟩, ⟨2, 199, 1⟩, ⟨2, 224, 1⟩, ⟨2, 249, 1⟩, ⟨3, 49, 9⟩, ⟨3, 82, 3⟩, ⟨3, 115, 1⟩, ⟨3, 148, 1⟩, ⟨5, 49, 3⟩, ⟨7, 49, 1⟩, ⟨11, 49, 9⟩, ⟨11, 94, 1⟩}
  | 40, 1 => {⟨2, 187, 1⟩}
  | 41, 0 => {⟨2, 45, 33⟩, ⟨2, 68, 14⟩, ⟨2, 91, 8⟩, ⟨2, 114, 5⟩, ⟨2, 137, 3⟩, ⟨2, 160, 2⟩, ⟨2, 183, 2⟩, ⟨2, 206, 1⟩, ⟨2, 229, 1⟩, ⟨2, 252, 1⟩, ⟨3, 45, 11⟩, ⟨3, 75, 4⟩, ⟨3, 105, 2⟩, ⟨3, 135, 1⟩, ⟨5, 45, 4⟩, ⟨5, 81, 1⟩, ⟨7, 45, 1⟩, ⟨11, 45, 12⟩, ⟨11, 86, 1⟩}
  | 41, 1 => {⟨2, 153, 2⟩}
  | 42, 0 => {⟨2, 41, 39⟩, ⟨2, 62, 17⟩, ⟨2, 83, 9⟩, ⟨2, 104, 6⟩, ⟨2, 125, 4⟩, ⟨2, 146, 3⟩, ⟨2, 167, 2⟩, ⟨2, 188, 1⟩, ⟨2, 209, 1⟩, ⟨2, 230, 1⟩, ⟨2, 251, 1⟩, ⟨3, 41, 13⟩, ⟨3, 69, 4⟩, ⟨3, 97, 2⟩, ⟨3, 125, 1⟩, ⟨5, 41, 4⟩, ⟨5, 74, 1⟩, ⟨7, 41, 2⟩, ⟨11, 41, 15⟩, ⟨11, 79, 2⟩}
  | 42, 1 => {⟨2, 151, 3⟩, ⟨3, 151, 1⟩}
  | 43, 0 => {⟨2, 37, 48⟩, ⟨2, 56, 21⟩, ⟨2, 75, 12⟩, ⟨2, 94, 7⟩, ⟨2, 113, 5⟩, ⟨2, 132, 3⟩, ⟨2, 151, 3⟩, ⟨2, 170, 2⟩, ⟨2, 189, 1⟩, ⟨2, 208, 1⟩, ⟨2, 227, 1⟩, ⟨2, 246, 1⟩, ⟨3, 37, 16⟩, ⟨3, 62, 5⟩, ⟨3, 87, 2⟩, ⟨3, 112, 1⟩, ⟨3, 137, 1⟩, ⟨5, 37, 6⟩, ⟨5, 67, 2⟩, ⟨7, 37, 2⟩, ⟨11, 37, 20⟩, ⟨11, 71, 2⟩, ⟨11, 105, 1⟩}
  | 43, 1 => {⟨2, 149, 3⟩, ⟨3, 149, 1⟩}
  | 44, 0 => {⟨2, 120, 4⟩, ⟨2, 231, 1⟩, ⟨3, 120, 1⟩}
  | 44, 1 => {⟨2, 191, 1⟩}
  | 45, 0 => {⟨2, 101, 6⟩, ⟨2, 174, 2⟩, ⟨2, 247, 1⟩, ⟨3, 101, 2⟩, ⟨11, 101, 1⟩}
  | 45, 1 => {⟨2, 186, 1⟩}
  | 46, 0 => {⟨2, 69, 13⟩, ⟨2, 104, 5⟩, ⟨2, 139, 3⟩, ⟨2, 174, 2⟩, ⟨2, 209, 1⟩, ⟨2, 244, 1⟩, ⟨3, 69, 4⟩, ⟨3, 115, 1⟩, ⟨5, 69, 1⟩, ⟨11, 69, 2⟩}
  | 46, 1 => {⟨2, 184, 1⟩}
  | 47, 0 => {⟨2, 61, 17⟩, ⟨2, 92, 7⟩, ⟨2, 123, 4⟩, ⟨2, 154, 2⟩, ⟨2, 185, 1⟩, ⟨2, 216, 1⟩, ⟨2, 247, 1⟩, ⟨3, 61, 5⟩, ⟨3, 102, 2⟩, ⟨3, 143, 1⟩, ⟨5, 61, 2⟩, ⟨11, 61, 4⟩}
  | 47, 1 => {⟨2, 181, 1⟩}
  | _, _ => ∅

def slope : ℕ → ℕ
  | 0 => 864
  | 1 => 1296
  | 2 => 1296
  | 3 => 1620
  | 4 => 1728
  | 5 => 2052
  | 6 => 2700
  | 7 => 5265
  | 8 => 5805
  | 9 => 6129
  | 10 => 7101
  | 11 => 7209
  | 12 => 7857
  | 13 => 8721
  | 14 => 9585
  | 15 => 10638
  | 16 => 12150
  | 17 => 13716
  | 18 => 14580
  | 19 => 15444
  | 20 => 16308
  | 21 => 17280
  | 22 => 19548
  | 23 => 20844
  | 24 => 880
  | 25 => 1320
  | 26 => 1760
  | 27 => 2640
  | 28 => 6022
  | 29 => 7232
  | 30 => 8552
  | 31 => 9872
  | 32 => 12760
  | 33 => 14300
  | 34 => 16170
  | 35 => 17820
  | 36 => 896
  | 37 => 1680
  | 38 => 2688
  | 39 => 6916
  | 40 => 9828
  | 41 => 12320
  | 42 => 15008
  | 43 => 18928
  | 44 => 975
  | 45 => 1755
  | 46 => 4485
  | 47 => 6305
  | _ => 0

def FiniteFacts (k : ℕ) (hk : k < 48) : Prop :=
  (∀ b : CrossBandCredit208.Band,
    BandFacts (row k).high (data k).steps (At (row k) (length hk) b) (terms k b) ∧
      ∀ t ∈ terms k b, (t.p,(row k).low/(t.q*(t.q+1)),t.count) ∈ Required) ∧
    RowSlope (row k) (length hk) (terms k) = slope k

local instance (k : ℕ) (hk : k < 48) : Decidable (FiniteFacts k hk) :=
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

theorem facts38 : FiniteFacts 38 (by decide) := by decide +kernel
#print axioms facts38

theorem facts39 : FiniteFacts 39 (by decide) := by decide +kernel
#print axioms facts39

theorem facts40 : FiniteFacts 40 (by decide) := by decide +kernel
#print axioms facts40

theorem facts41 : FiniteFacts 41 (by decide) := by decide +kernel
#print axioms facts41

theorem facts42 : FiniteFacts 42 (by decide) := by decide +kernel
#print axioms facts42

theorem facts43 : FiniteFacts 43 (by decide) := by decide +kernel
#print axioms facts43

theorem facts44 : FiniteFacts 44 (by decide) := by decide +kernel
#print axioms facts44

theorem facts45 : FiniteFacts 45 (by decide) := by decide +kernel
#print axioms facts45

theorem facts46 : FiniteFacts 46 (by decide) := by decide +kernel
#print axioms facts46

theorem facts47 : FiniteFacts 47 (by decide) := by decide +kernel
#print axioms facts47

theorem facts {k : ℕ} (hk : k < 48) : FiniteFacts k hk := by
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
  · exact facts38
  · exact facts39
  · exact facts40
  · exact facts41
  · exact facts42
  · exact facts43
  · exact facts44
  · exact facts45
  · exact facts46
  · exact facts47

theorem slope_bound {k N : ℕ} (hk : k < 48)
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
end JSP233.RowLightSlope130000
