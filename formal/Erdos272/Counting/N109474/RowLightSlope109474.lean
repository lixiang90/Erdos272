module

public import Erdos272.Counting.N158375.LightSlope158375
public import Erdos272.Arithmetic.N109474.ClassCertificates109474
public import Erdos272.Arithmetic.N109474.CleanupRows109474
public import Erdos272.Arithmetic.CleanupMachineSound208

@[expose] public section

namespace JSP233.RowLightSlope109474
open CleanupRows109474 CleanupEval208 CleanupMachineSound208 ActualCleanupEval208
open LightFamily158375 LightSlope158375 ClassCertificates109474
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

theorem length {k : ℕ} (hk : k < 59) : (row k).bands.length=7 := by
  interval_cases k <;> rfl

def terms (k : ℕ) (b : CrossBandCredit208.Band) : Finset Term :=
  match k, b.val with
  | 0, 0 => {⟨2, 96, 5⟩, ⟨2, 189, 1⟩, ⟨3, 96, 1⟩, ⟨11, 96, 1⟩}
  | 1, 0 => {⟨2, 93, 6⟩, ⟨2, 180, 1⟩, ⟨3, 93, 2⟩, ⟨11, 93, 1⟩}
  | 1, 1 => {⟨2, 198, 1⟩}
  | 2, 0 => {⟨2, 90, 6⟩, ⟨2, 171, 1⟩, ⟨3, 90, 2⟩, ⟨11, 90, 1⟩}
  | 2, 1 => {⟨2, 198, 1⟩}
  | 3, 0 => {⟨2, 86, 7⟩, ⟨2, 159, 2⟩, ⟨2, 232, 1⟩, ⟨3, 86, 2⟩, ⟨11, 86, 1⟩}
  | 3, 1 => {⟨2, 197, 1⟩}
  | 4, 0 => {⟨2, 82, 8⟩, ⟨2, 147, 2⟩, ⟨2, 212, 1⟩, ⟨3, 82, 2⟩, ⟨11, 82, 1⟩}
  | 4, 1 => {⟨2, 197, 1⟩}
  | 5, 0 => {⟨2, 78, 8⟩, ⟨2, 135, 2⟩, ⟨2, 192, 1⟩, ⟨3, 78, 2⟩, ⟨11, 78, 1⟩}
  | 5, 1 => {⟨2, 196, 1⟩}
  | 6, 0 => {⟨2, 74, 9⟩, ⟨2, 123, 3⟩, ⟨2, 172, 1⟩, ⟨2, 221, 1⟩, ⟨3, 74, 3⟩, ⟨11, 74, 1⟩}
  | 6, 1 => {⟨2, 196, 1⟩}
  | 7, 0 => {⟨2, 69, 11⟩, ⟨2, 108, 4⟩, ⟨2, 147, 2⟩, ⟨2, 186, 1⟩, ⟨2, 225, 1⟩, ⟨3, 69, 3⟩, ⟨3, 123, 1⟩, ⟨5, 69, 1⟩, ⟨11, 69, 2⟩}
  | 7, 1 => {⟨2, 196, 1⟩}
  | 8, 0 => {⟨2, 59, 15⟩, ⟨2, 89, 6⟩, ⟨2, 119, 3⟩, ⟨2, 149, 2⟩, ⟨2, 179, 1⟩, ⟨2, 209, 1⟩, ⟨3, 59, 5⟩, ⟨3, 99, 1⟩, ⟨5, 59, 2⟩, ⟨11, 59, 4⟩}
  | 8, 1 => {⟨2, 169, 1⟩}
  | 9, 0 => {⟨2, 57, 16⟩, ⟨2, 86, 7⟩, ⟨2, 115, 4⟩, ⟨2, 144, 2⟩, ⟨2, 173, 1⟩, ⟨2, 202, 1⟩, ⟨2, 231, 1⟩, ⟨3, 57, 5⟩, ⟨3, 95, 2⟩, ⟨3, 133, 1⟩, ⟨5, 57, 2⟩, ⟨11, 57, 3⟩}
  | 9, 1 => {⟨2, 168, 1⟩}
  | 10, 0 => {⟨2, 55, 17⟩, ⟨2, 83, 7⟩, ⟨2, 111, 4⟩, ⟨2, 139, 2⟩, ⟨2, 167, 1⟩, ⟨2, 195, 1⟩, ⟨2, 223, 1⟩, ⟨3, 55, 5⟩, ⟨3, 92, 2⟩, ⟨3, 129, 1⟩, ⟨5, 55, 2⟩, ⟨11, 55, 4⟩}
  | 10, 1 => {⟨2, 168, 1⟩}
  | 11, 0 => {⟨2, 53, 19⟩, ⟨2, 80, 8⟩, ⟨2, 107, 4⟩, ⟨2, 134, 3⟩, ⟨2, 161, 2⟩, ⟨2, 188, 1⟩, ⟨2, 215, 1⟩, ⟨3, 53, 6⟩, ⟨3, 89, 2⟩, ⟨3, 125, 1⟩, ⟨5, 53, 2⟩, ⟨11, 53, 5⟩, ⟨11, 102, 1⟩}
  | 11, 1 => {⟨2, 167, 1⟩}
  | 12, 0 => {⟨2, 51, 20⟩, ⟨2, 77, 9⟩, ⟨2, 103, 5⟩, ⟨2, 129, 3⟩, ⟨2, 155, 2⟩, ⟨2, 181, 1⟩, ⟨2, 207, 1⟩, ⟨2, 233, 1⟩, ⟨3, 51, 6⟩, ⟨3, 85, 2⟩, ⟨3, 119, 1⟩, ⟨5, 51, 2⟩, ⟨11, 51, 6⟩, ⟨11, 98, 1⟩}
  | 12, 1 => {⟨2, 167, 1⟩}
  | 13, 0 => {⟨2, 49, 22⟩, ⟨2, 74, 9⟩, ⟨2, 99, 5⟩, ⟨2, 124, 3⟩, ⟨2, 149, 2⟩, ⟨2, 174, 1⟩, ⟨2, 199, 1⟩, ⟨2, 224, 1⟩, ⟨3, 49, 7⟩, ⟨3, 82, 2⟩, ⟨3, 115, 1⟩, ⟨5, 49, 2⟩, ⟨7, 49, 1⟩, ⟨11, 49, 6⟩, ⟨11, 94, 1⟩}
  | 13, 1 => {⟨2, 166, 1⟩}
  | 14, 0 => {⟨2, 47, 24⟩, ⟨2, 71, 10⟩, ⟨2, 95, 6⟩, ⟨2, 119, 3⟩, ⟨2, 143, 2⟩, ⟨2, 167, 1⟩, ⟨2, 191, 1⟩, ⟨2, 215, 1⟩, ⟨3, 47, 8⟩, ⟨3, 79, 2⟩, ⟨3, 111, 1⟩, ⟨5, 47, 2⟩, ⟨7, 47, 1⟩, ⟨11, 47, 8⟩, ⟨11, 90, 1⟩}
  | 14, 1 => {⟨2, 166, 1⟩}
  | 15, 0 => {⟨2, 46, 25⟩, ⟨2, 69, 11⟩, ⟨2, 92, 6⟩, ⟨2, 115, 4⟩, ⟨2, 138, 2⟩, ⟨2, 161, 2⟩, ⟨2, 184, 1⟩, ⟨2, 207, 1⟩, ⟨2, 230, 1⟩, ⟨3, 46, 8⟩, ⟨3, 77, 3⟩, ⟨3, 108, 1⟩, ⟨5, 46, 3⟩, ⟨7, 46, 1⟩, ⟨11, 46, 8⟩, ⟨11, 88, 1⟩}
  | 15, 1 => {⟨2, 166, 1⟩}
  | 16, 0 => {⟨2, 45, 26⟩, ⟨2, 68, 11⟩, ⟨2, 91, 6⟩, ⟨2, 114, 4⟩, ⟨2, 137, 2⟩, ⟨2, 160, 2⟩, ⟨2, 183, 1⟩, ⟨2, 206, 1⟩, ⟨2, 229, 1⟩, ⟨3, 45, 8⟩, ⟨3, 75, 3⟩, ⟨3, 105, 1⟩, ⟨5, 45, 3⟩, ⟨7, 45, 1⟩, ⟨11, 45, 8⟩, ⟨11, 86, 1⟩}
  | 16, 1 => {⟨2, 136, 2⟩}
  | 17, 0 => {⟨2, 43, 28⟩, ⟨2, 65, 12⟩, ⟨2, 87, 7⟩, ⟨2, 109, 4⟩, ⟨2, 131, 3⟩, ⟨2, 153, 2⟩, ⟨2, 175, 1⟩, ⟨2, 197, 1⟩, ⟨2, 219, 1⟩, ⟨3, 43, 9⟩, ⟨3, 72, 3⟩, ⟨3, 101, 1⟩, ⟨3, 130, 1⟩, ⟨5, 43, 3⟩, ⟨7, 43, 1⟩, ⟨11, 43, 9⟩, ⟨11, 83, 1⟩}
  | 17, 1 => {⟨2, 165, 1⟩}
  | 18, 0 => {⟨2, 41, 31⟩, ⟨2, 62, 14⟩, ⟨2, 83, 7⟩, ⟨2, 104, 5⟩, ⟨2, 125, 3⟩, ⟨2, 146, 2⟩, ⟨2, 167, 1⟩, ⟨2, 188, 1⟩, ⟨2, 209, 1⟩, ⟨2, 230, 1⟩, ⟨3, 41, 10⟩, ⟨3, 69, 3⟩, ⟨3, 97, 1⟩, ⟨3, 125, 1⟩, ⟨5, 41, 4⟩, ⟨7, 41, 1⟩, ⟨11, 41, 10⟩, ⟨11, 79, 1⟩}
  | 18, 1 => {⟨2, 134, 3⟩, ⟨3, 134, 1⟩}
  | 19, 0 => {⟨2, 39, 35⟩, ⟨2, 59, 15⟩, ⟨2, 79, 8⟩, ⟨2, 99, 5⟩, ⟨2, 119, 3⟩, ⟨2, 139, 2⟩, ⟨2, 159, 2⟩, ⟨2, 179, 1⟩, ⟨2, 199, 1⟩, ⟨2, 219, 1⟩, ⟨3, 39, 11⟩, ⟨3, 65, 4⟩, ⟨3, 91, 2⟩, ⟨3, 117, 1⟩, ⟨5, 39, 4⟩, ⟨5, 71, 1⟩, ⟨7, 39, 2⟩, ⟨11, 39, 14⟩, ⟨11, 75, 1⟩}
  | 19, 1 => {⟨2, 133, 3⟩, ⟨3, 133, 1⟩}
  | 20, 0 => {⟨2, 37, 38⟩, ⟨2, 56, 17⟩, ⟨2, 75, 9⟩, ⟨2, 94, 6⟩, ⟨2, 113, 4⟩, ⟨2, 132, 3⟩, ⟨2, 151, 2⟩, ⟨2, 170, 1⟩, ⟨2, 189, 1⟩, ⟨2, 208, 1⟩, ⟨2, 227, 1⟩, ⟨3, 37, 12⟩, ⟨3, 62, 4⟩, ⟨3, 87, 2⟩, ⟨3, 112, 1⟩, ⟨5, 37, 4⟩, ⟨5, 67, 1⟩, ⟨7, 37, 2⟩, ⟨11, 37, 14⟩, ⟨11, 71, 2⟩}
  | 20, 1 => {⟨2, 132, 3⟩, ⟨3, 132, 1⟩}
  | 21, 0 => {⟨2, 36, 41⟩, ⟨2, 54, 18⟩, ⟨2, 72, 10⟩, ⟨2, 90, 6⟩, ⟨2, 108, 4⟩, ⟨2, 126, 3⟩, ⟨2, 144, 2⟩, ⟨2, 162, 2⟩, ⟨2, 180, 1⟩, ⟨2, 198, 1⟩, ⟨2, 216, 1⟩, ⟨3, 36, 13⟩, ⟨3, 60, 4⟩, ⟨3, 84, 2⟩, ⟨3, 108, 1⟩, ⟨3, 132, 1⟩, ⟨5, 36, 5⟩, ⟨5, 65, 1⟩, ⟨7, 36, 2⟩, ⟨11, 36, 15⟩, ⟨11, 69, 2⟩, ⟨11, 102, 1⟩}
  | 21, 1 => {⟨2, 131, 3⟩, ⟨3, 131, 1⟩}
  | 22, 0 => {⟨2, 35, 43⟩, ⟨2, 53, 19⟩, ⟨2, 71, 10⟩, ⟨2, 89, 6⟩, ⟨2, 107, 4⟩, ⟨2, 125, 3⟩, ⟨2, 143, 2⟩, ⟨2, 161, 2⟩, ⟨2, 179, 1⟩, ⟨2, 197, 1⟩, ⟨2, 215, 1⟩, ⟨2, 233, 1⟩, ⟨3, 35, 14⟩, ⟨3, 59, 5⟩, ⟨3, 83, 2⟩, ⟨3, 107, 1⟩, ⟨3, 131, 1⟩, ⟨5, 35, 5⟩, ⟨5, 63, 1⟩, ⟨7, 35, 2⟩, ⟨11, 35, 16⟩, ⟨11, 67, 2⟩, ⟨11, 99, 1⟩}
  | 22, 1 => {⟨2, 131, 3⟩, ⟨3, 131, 1⟩}
  | 23, 0 => {⟨2, 34, 45⟩, ⟨2, 51, 20⟩, ⟨2, 68, 11⟩, ⟨2, 85, 7⟩, ⟨2, 102, 5⟩, ⟨2, 119, 3⟩, ⟨2, 136, 2⟩, ⟨2, 153, 2⟩, ⟨2, 170, 1⟩, ⟨2, 187, 1⟩, ⟨2, 204, 1⟩, ⟨2, 221, 1⟩, ⟨3, 34, 15⟩, ⟨3, 57, 5⟩, ⟨3, 80, 2⟩, ⟨3, 103, 1⟩, ⟨3, 126, 1⟩, ⟨5, 34, 6⟩, ⟨5, 62, 1⟩, ⟨7, 34, 2⟩, ⟨11, 34, 19⟩, ⟨11, 65, 2⟩, ⟨11, 96, 1⟩}
  | 23, 1 => {⟨2, 130, 3⟩, ⟨3, 130, 1⟩}
  | 24, 0 => {⟨2, 97, 5⟩, ⟨2, 191, 1⟩, ⟨3, 97, 1⟩, ⟨11, 97, 1⟩}
  | 25, 0 => {⟨2, 91, 6⟩, ⟨2, 173, 1⟩, ⟨3, 91, 2⟩, ⟨11, 91, 1⟩}
  | 25, 1 => {⟨2, 200, 1⟩}
  | 26, 0 => {⟨2, 85, 7⟩, ⟨2, 155, 2⟩, ⟨2, 225, 1⟩, ⟨3, 85, 2⟩, ⟨11, 85, 1⟩}
  | 26, 1 => {⟨2, 199, 1⟩}
  | 27, 0 => {⟨2, 79, 8⟩, ⟨2, 137, 2⟩, ⟨2, 195, 1⟩, ⟨3, 79, 2⟩, ⟨11, 79, 1⟩}
  | 27, 1 => {⟨2, 198, 1⟩}
  | 28, 0 => {⟨2, 71, 10⟩, ⟨2, 113, 4⟩, ⟨2, 155, 2⟩, ⟨2, 197, 1⟩, ⟨3, 71, 3⟩, ⟨3, 128, 1⟩, ⟨5, 71, 1⟩, ⟨11, 71, 2⟩}
  | 28, 1 => {⟨2, 198, 1⟩}
  | 29, 0 => {⟨2, 59, 15⟩, ⟨2, 89, 6⟩, ⟨2, 119, 3⟩, ⟨2, 149, 2⟩, ⟨2, 179, 1⟩, ⟨2, 209, 1⟩, ⟨3, 59, 5⟩, ⟨3, 99, 1⟩, ⟨5, 59, 2⟩, ⟨11, 59, 4⟩}
  | 29, 1 => {⟨2, 170, 1⟩}
  | 30, 0 => {⟨2, 55, 18⟩, ⟨2, 83, 8⟩, ⟨2, 111, 4⟩, ⟨2, 139, 2⟩, ⟨2, 167, 1⟩, ⟨2, 195, 1⟩, ⟨2, 223, 1⟩, ⟨3, 55, 6⟩, ⟨3, 92, 2⟩, ⟨3, 129, 1⟩, ⟨5, 55, 2⟩, ⟨11, 55, 5⟩}
  | 30, 1 => {⟨2, 168, 1⟩}
  | 31, 0 => {⟨2, 52, 20⟩, ⟨2, 78, 9⟩, ⟨2, 104, 5⟩, ⟨2, 130, 3⟩, ⟨2, 156, 2⟩, ⟨2, 182, 1⟩, ⟨2, 208, 1⟩, ⟨2, 234, 1⟩, ⟨3, 52, 6⟩, ⟨3, 87, 2⟩, ⟨3, 122, 1⟩, ⟨5, 52, 2⟩, ⟨11, 52, 6⟩, ⟨11, 100, 1⟩}
  | 31, 1 => {⟨2, 168, 1⟩}
  | 32, 0 => {⟨2, 49, 22⟩, ⟨2, 74, 10⟩, ⟨2, 99, 5⟩, ⟨2, 124, 3⟩, ⟨2, 149, 2⟩, ⟨2, 174, 1⟩, ⟨2, 199, 1⟩, ⟨2, 224, 1⟩, ⟨3, 49, 7⟩, ⟨3, 82, 2⟩, ⟨3, 115, 1⟩, ⟨5, 49, 2⟩, ⟨7, 49, 1⟩, ⟨11, 49, 6⟩, ⟨11, 94, 1⟩}
  | 32, 1 => {⟨2, 167, 1⟩}
  | 33, 0 => {⟨2, 47, 24⟩, ⟨2, 71, 10⟩, ⟨2, 95, 6⟩, ⟨2, 119, 3⟩, ⟨2, 143, 2⟩, ⟨2, 167, 1⟩, ⟨2, 191, 1⟩, ⟨2, 215, 1⟩, ⟨3, 47, 8⟩, ⟨3, 79, 2⟩, ⟨3, 111, 1⟩, ⟨5, 47, 2⟩, ⟨7, 47, 1⟩, ⟨11, 47, 8⟩, ⟨11, 90, 1⟩}
  | 33, 1 => {⟨2, 167, 1⟩}
  | 34, 0 => {⟨2, 45, 26⟩, ⟨2, 68, 11⟩, ⟨2, 91, 6⟩, ⟨2, 114, 4⟩, ⟨2, 137, 2⟩, ⟨2, 160, 2⟩, ⟨2, 183, 1⟩, ⟨2, 206, 1⟩, ⟨2, 229, 1⟩, ⟨3, 45, 8⟩, ⟨3, 75, 3⟩, ⟨3, 105, 1⟩, ⟨3, 135, 1⟩, ⟨5, 45, 3⟩, ⟨7, 45, 1⟩, ⟨11, 45, 8⟩, ⟨11, 86, 1⟩}
  | 34, 1 => {⟨2, 166, 2⟩}
  | 35, 0 => {⟨2, 43, 29⟩, ⟨2, 65, 13⟩, ⟨2, 87, 7⟩, ⟨2, 109, 4⟩, ⟨2, 131, 3⟩, ⟨2, 153, 2⟩, ⟨2, 175, 1⟩, ⟨2, 197, 1⟩, ⟨2, 219, 1⟩, ⟨3, 43, 9⟩, ⟨3, 72, 3⟩, ⟨3, 101, 1⟩, ⟨3, 130, 1⟩, ⟨5, 43, 3⟩, ⟨7, 43, 1⟩, ⟨11, 43, 9⟩, ⟨11, 83, 1⟩}
  | 35, 1 => {⟨2, 135, 3⟩, ⟨3, 135, 1⟩}
  | 36, 0 => {⟨2, 41, 32⟩, ⟨2, 62, 14⟩, ⟨2, 83, 8⟩, ⟨2, 104, 5⟩, ⟨2, 125, 3⟩, ⟨2, 146, 2⟩, ⟨2, 167, 1⟩, ⟨2, 188, 1⟩, ⟨2, 209, 1⟩, ⟨2, 230, 1⟩, ⟨3, 41, 10⟩, ⟨3, 69, 3⟩, ⟨3, 97, 1⟩, ⟨3, 125, 1⟩, ⟨5, 41, 4⟩, ⟨5, 74, 1⟩, ⟨7, 41, 1⟩, ⟨11, 41, 11⟩, ⟨11, 79, 1⟩}
  | 36, 1 => {⟨2, 134, 3⟩, ⟨3, 134, 1⟩}
  | 37, 0 => {⟨2, 39, 35⟩, ⟨2, 59, 15⟩, ⟨2, 79, 8⟩, ⟨2, 99, 5⟩, ⟨2, 119, 3⟩, ⟨2, 139, 2⟩, ⟨2, 159, 2⟩, ⟨2, 179, 1⟩, ⟨2, 199, 1⟩, ⟨2, 219, 1⟩, ⟨3, 39, 11⟩, ⟨3, 65, 4⟩, ⟨3, 91, 2⟩, ⟨3, 117, 1⟩, ⟨5, 39, 4⟩, ⟨5, 71, 1⟩, ⟨7, 39, 2⟩, ⟨11, 39, 14⟩, ⟨11, 75, 1⟩}
  | 37, 1 => {⟨2, 133, 3⟩, ⟨3, 133, 1⟩}
  | 38, 0 => {⟨2, 37, 39⟩, ⟨2, 56, 17⟩, ⟨2, 75, 9⟩, ⟨2, 94, 6⟩, ⟨2, 113, 4⟩, ⟨2, 132, 3⟩, ⟨2, 151, 2⟩, ⟨2, 170, 1⟩, ⟨2, 189, 1⟩, ⟨2, 208, 1⟩, ⟨2, 227, 1⟩, ⟨3, 37, 13⟩, ⟨3, 62, 4⟩, ⟨3, 87, 2⟩, ⟨3, 112, 1⟩, ⟨5, 37, 4⟩, ⟨5, 67, 1⟩, ⟨7, 37, 2⟩, ⟨11, 37, 15⟩, ⟨11, 71, 2⟩, ⟨11, 105, 1⟩}
  | 38, 1 => {⟨2, 132, 3⟩, ⟨3, 132, 1⟩}
  | 39, 0 => {⟨2, 35, 44⟩, ⟨2, 53, 19⟩, ⟨2, 71, 10⟩, ⟨2, 89, 6⟩, ⟨2, 107, 4⟩, ⟨2, 125, 3⟩, ⟨2, 143, 2⟩, ⟨2, 161, 2⟩, ⟨2, 179, 1⟩, ⟨2, 197, 1⟩, ⟨2, 215, 1⟩, ⟨2, 233, 1⟩, ⟨3, 35, 14⟩, ⟨3, 59, 5⟩, ⟨3, 83, 2⟩, ⟨3, 107, 1⟩, ⟨3, 131, 1⟩, ⟨5, 35, 5⟩, ⟨5, 63, 1⟩, ⟨7, 35, 2⟩, ⟨11, 35, 17⟩, ⟨11, 67, 2⟩, ⟨11, 99, 1⟩}
  | 39, 1 => {⟨2, 131, 3⟩, ⟨3, 131, 1⟩}
  | 40, 0 => {⟨2, 98, 5⟩, ⟨2, 193, 1⟩, ⟨3, 98, 1⟩, ⟨11, 98, 1⟩}
  | 41, 0 => {⟨2, 92, 6⟩, ⟨2, 175, 1⟩, ⟨3, 92, 2⟩, ⟨11, 92, 1⟩}
  | 41, 1 => {⟨2, 202, 1⟩}
  | 42, 0 => {⟨2, 86, 7⟩, ⟨2, 157, 2⟩, ⟨2, 228, 1⟩, ⟨3, 86, 2⟩, ⟨11, 86, 1⟩}
  | 42, 1 => {⟨2, 201, 1⟩}
  | 43, 0 => {⟨2, 79, 9⟩, ⟨2, 136, 3⟩, ⟨2, 193, 1⟩, ⟨3, 79, 3⟩, ⟨11, 79, 1⟩}
  | 43, 1 => {⟨2, 200, 1⟩}
  | 44, 0 => {⟨2, 72, 10⟩, ⟨2, 115, 4⟩, ⟨2, 158, 2⟩, ⟨2, 201, 1⟩, ⟨3, 72, 3⟩, ⟨3, 130, 1⟩, ⟨5, 72, 1⟩, ⟨11, 72, 2⟩}
  | 44, 1 => {⟨2, 200, 1⟩}
  | 45, 0 => {⟨2, 61, 15⟩, ⟨2, 92, 6⟩, ⟨2, 123, 3⟩, ⟨2, 154, 2⟩, ⟨2, 185, 1⟩, ⟨2, 216, 1⟩, ⟨3, 61, 5⟩, ⟨3, 102, 1⟩, ⟨5, 61, 2⟩, ⟨11, 61, 4⟩}
  | 45, 1 => {⟨2, 172, 1⟩}
  | 46, 0 => {⟨2, 57, 17⟩, ⟨2, 86, 7⟩, ⟨2, 115, 4⟩, ⟨2, 144, 2⟩, ⟨2, 173, 1⟩, ⟨2, 202, 1⟩, ⟨2, 231, 1⟩, ⟨3, 57, 5⟩, ⟨3, 95, 2⟩, ⟨3, 133, 1⟩, ⟨5, 57, 2⟩, ⟨11, 57, 4⟩}
  | 46, 1 => {⟨2, 171, 1⟩}
  | 47, 0 => {⟨2, 53, 19⟩, ⟨2, 80, 8⟩, ⟨2, 107, 4⟩, ⟨2, 134, 3⟩, ⟨2, 161, 2⟩, ⟨2, 188, 1⟩, ⟨2, 215, 1⟩, ⟨3, 53, 6⟩, ⟨3, 89, 2⟩, ⟨3, 125, 1⟩, ⟨5, 53, 2⟩, ⟨11, 53, 5⟩, ⟨11, 102, 1⟩}
  | 47, 1 => {⟨2, 170, 1⟩}
  | 48, 0 => {⟨2, 49, 23⟩, ⟨2, 74, 10⟩, ⟨2, 99, 5⟩, ⟨2, 124, 3⟩, ⟨2, 149, 2⟩, ⟨2, 174, 1⟩, ⟨2, 199, 1⟩, ⟨2, 224, 1⟩, ⟨3, 49, 7⟩, ⟨3, 82, 2⟩, ⟨3, 115, 1⟩, ⟨5, 49, 2⟩, ⟨7, 49, 1⟩, ⟨11, 49, 7⟩, ⟨11, 94, 1⟩}
  | 48, 1 => {⟨2, 169, 1⟩}
  | 49, 0 => {⟨2, 47, 25⟩, ⟨2, 71, 11⟩, ⟨2, 95, 6⟩, ⟨2, 119, 3⟩, ⟨2, 143, 2⟩, ⟨2, 167, 2⟩, ⟨2, 191, 1⟩, ⟨2, 215, 1⟩, ⟨3, 47, 8⟩, ⟨3, 79, 3⟩, ⟨3, 111, 1⟩, ⟨5, 47, 3⟩, ⟨7, 47, 1⟩, ⟨11, 47, 8⟩, ⟨11, 90, 1⟩}
  | 49, 1 => {⟨2, 168, 2⟩}
  | 50, 0 => {⟨2, 45, 27⟩, ⟨2, 68, 12⟩, ⟨2, 91, 6⟩, ⟨2, 114, 4⟩, ⟨2, 137, 3⟩, ⟨2, 160, 2⟩, ⟨2, 183, 1⟩, ⟨2, 206, 1⟩, ⟨2, 229, 1⟩, ⟨3, 45, 9⟩, ⟨3, 75, 3⟩, ⟨3, 105, 1⟩, ⟨3, 135, 1⟩, ⟨5, 45, 3⟩, ⟨7, 45, 1⟩, ⟨11, 45, 9⟩, ⟨11, 86, 1⟩}
  | 50, 1 => {⟨2, 168, 2⟩}
  | 51, 0 => {⟨2, 43, 30⟩, ⟨2, 65, 13⟩, ⟨2, 87, 7⟩, ⟨2, 109, 4⟩, ⟨2, 131, 3⟩, ⟨2, 153, 2⟩, ⟨2, 175, 1⟩, ⟨2, 197, 1⟩, ⟨2, 219, 1⟩, ⟨3, 43, 10⟩, ⟨3, 72, 3⟩, ⟨3, 101, 1⟩, ⟨3, 130, 1⟩, ⟨5, 43, 4⟩, ⟨7, 43, 1⟩, ⟨11, 43, 11⟩, ⟨11, 83, 1⟩}
  | 51, 1 => {⟨2, 137, 3⟩, ⟨3, 137, 1⟩}
  | 52, 0 => {⟨2, 41, 33⟩, ⟨2, 62, 14⟩, ⟨2, 83, 8⟩, ⟨2, 104, 5⟩, ⟨2, 125, 3⟩, ⟨2, 146, 2⟩, ⟨2, 167, 2⟩, ⟨2, 188, 1⟩, ⟨2, 209, 1⟩, ⟨2, 230, 1⟩, ⟨3, 41, 11⟩, ⟨3, 69, 3⟩, ⟨3, 97, 1⟩, ⟨3, 125, 1⟩, ⟨5, 41, 4⟩, ⟨5, 74, 1⟩, ⟨7, 41, 1⟩, ⟨11, 41, 12⟩, ⟨11, 79, 1⟩}
  | 52, 1 => {⟨2, 136, 3⟩, ⟨3, 136, 1⟩}
  | 53, 0 => {⟨2, 39, 36⟩, ⟨2, 59, 16⟩, ⟨2, 79, 9⟩, ⟨2, 99, 5⟩, ⟨2, 119, 3⟩, ⟨2, 139, 2⟩, ⟨2, 159, 2⟩, ⟨2, 179, 1⟩, ⟨2, 199, 1⟩, ⟨2, 219, 1⟩, ⟨3, 39, 12⟩, ⟨3, 65, 4⟩, ⟨3, 91, 2⟩, ⟨3, 117, 1⟩, ⟨5, 39, 4⟩, ⟨5, 71, 1⟩, ⟨7, 39, 2⟩, ⟨11, 39, 13⟩, ⟨11, 75, 1⟩}
  | 53, 1 => {⟨2, 135, 3⟩, ⟨3, 135, 1⟩}
  | 54, 0 => {⟨2, 37, 40⟩, ⟨2, 56, 17⟩, ⟨2, 75, 9⟩, ⟨2, 94, 6⟩, ⟨2, 113, 4⟩, ⟨2, 132, 3⟩, ⟨2, 151, 2⟩, ⟨2, 170, 1⟩, ⟨2, 189, 1⟩, ⟨2, 208, 1⟩, ⟨2, 227, 1⟩, ⟨3, 37, 13⟩, ⟨3, 62, 4⟩, ⟨3, 87, 2⟩, ⟨3, 112, 1⟩, ⟨3, 137, 1⟩, ⟨5, 37, 5⟩, ⟨5, 67, 1⟩, ⟨7, 37, 2⟩, ⟨11, 37, 15⟩, ⟨11, 71, 2⟩, ⟨11, 105, 1⟩}
  | 54, 1 => {⟨2, 134, 3⟩, ⟨3, 134, 1⟩}
  | 55, 0 => {⟨2, 35, 45⟩, ⟨2, 53, 19⟩, ⟨2, 71, 11⟩, ⟨2, 89, 7⟩, ⟨2, 107, 4⟩, ⟨2, 125, 3⟩, ⟨2, 143, 2⟩, ⟨2, 161, 2⟩, ⟨2, 179, 1⟩, ⟨2, 197, 1⟩, ⟨2, 215, 1⟩, ⟨2, 233, 1⟩, ⟨3, 35, 15⟩, ⟨3, 59, 5⟩, ⟨3, 83, 2⟩, ⟨3, 107, 1⟩, ⟨3, 131, 1⟩, ⟨5, 35, 6⟩, ⟨5, 63, 1⟩, ⟨7, 35, 2⟩, ⟨11, 35, 19⟩, ⟨11, 67, 2⟩, ⟨11, 99, 1⟩}
  | 55, 1 => {⟨2, 133, 3⟩, ⟨3, 133, 1⟩}
  | 56, 0 => {⟨2, 114, 4⟩, ⟨2, 213, 1⟩, ⟨3, 114, 1⟩}
  | 57, 0 => {⟨2, 97, 5⟩, ⟨2, 162, 2⟩, ⟨2, 227, 1⟩, ⟨3, 97, 1⟩, ⟨11, 97, 1⟩}
  | 58, 0 => {⟨2, 75, 9⟩, ⟨2, 113, 4⟩, ⟨2, 151, 2⟩, ⟨2, 189, 1⟩, ⟨2, 227, 1⟩, ⟨3, 75, 3⟩, ⟨3, 125, 1⟩, ⟨11, 75, 1⟩}
  | 58, 1 => {⟨2, 219, 1⟩}
  | _, _ => ∅

def slope : ℕ → ℕ
  | 0 => 800
  | 1 => 1200
  | 2 => 1200
  | 3 => 1500
  | 4 => 1600
  | 5 => 1600
  | 6 => 2000
  | 7 => 2800
  | 8 => 4175
  | 9 => 4675
  | 10 => 4875
  | 11 => 5675
  | 12 => 6175
  | 13 => 6575
  | 14 => 7275
  | 15 => 7975
  | 16 => 8200
  | 17 => 8875
  | 18 => 10300
  | 19 => 11900
  | 20 => 13100
  | 21 => 14200
  | 22 => 14900
  | 23 => 16000
  | 24 => 808
  | 25 => 1212
  | 26 => 1515
  | 27 => 1616
  | 28 => 2626
  | 29 => 4216
  | 30 => 5327
  | 31 => 6236
  | 32 => 6741
  | 33 => 7347
  | 34 => 8432
  | 35 => 9593
  | 36 => 10805
  | 37 => 12017
  | 38 => 13633
  | 39 => 15249
  | 40 => 816
  | 41 => 1224
  | 42 => 1530
  | 43 => 1938
  | 44 => 2652
  | 45 => 4258
  | 46 => 4972
  | 47 => 5788
  | 48 => 7012
  | 49 => 8108
  | 50 => 9026
  | 51 => 10200
  | 52 => 11322
  | 53 => 12444
  | 54 => 14076
  | 55 => 16116
  | 56 => 780
  | 57 => 1300
  | 58 => 3087
  | _ => 0

def FiniteFacts (k : ℕ) (hk : k < 59) : Prop :=
  (∀ b : CrossBandCredit208.Band,
    BandFacts (row k).high (data k).steps (At (row k) (length hk) b) (terms k b) ∧
      ∀ t ∈ terms k b, (t.p,(row k).low/(t.q*(t.q+1)),t.count) ∈ Required) ∧
    RowSlope (row k) (length hk) (terms k) = slope k

local instance (k : ℕ) (hk : k < 59) : Decidable (FiniteFacts k hk) :=
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

theorem facts48 : FiniteFacts 48 (by decide) := by decide +kernel
#print axioms facts48

theorem facts49 : FiniteFacts 49 (by decide) := by decide +kernel
#print axioms facts49

theorem facts50 : FiniteFacts 50 (by decide) := by decide +kernel
#print axioms facts50

theorem facts51 : FiniteFacts 51 (by decide) := by decide +kernel
#print axioms facts51

theorem facts52 : FiniteFacts 52 (by decide) := by decide +kernel
#print axioms facts52

theorem facts53 : FiniteFacts 53 (by decide) := by decide +kernel
#print axioms facts53

theorem facts54 : FiniteFacts 54 (by decide) := by decide +kernel
#print axioms facts54

theorem facts55 : FiniteFacts 55 (by decide) := by decide +kernel
#print axioms facts55

theorem facts56 : FiniteFacts 56 (by decide) := by decide +kernel
#print axioms facts56

theorem facts57 : FiniteFacts 57 (by decide) := by decide +kernel
#print axioms facts57

theorem facts58 : FiniteFacts 58 (by decide) := by decide +kernel
#print axioms facts58

theorem facts {k : ℕ} (hk : k < 59) : FiniteFacts k hk := by
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
  · exact facts48
  · exact facts49
  · exact facts50
  · exact facts51
  · exact facts52
  · exact facts53
  · exact facts54
  · exact facts55
  · exact facts56
  · exact facts57
  · exact facts58

theorem slope_bound {k N : ℕ} (hk : k < 59)
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
end JSP233.RowLightSlope109474
