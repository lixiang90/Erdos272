module

public import Erdos272.Counting.N158375.LightSlope158375
public import Erdos272.Arithmetic.N88404.ClassCertificates88404
public import Erdos272.Arithmetic.N88404.CleanupRows88404
public import Erdos272.Arithmetic.CleanupMachineSound208

@[expose] public section

namespace JSP233.RowLightSlope88404
open CleanupRows88404 CleanupEval208 CleanupMachineSound208 ActualCleanupEval208
open LightFamily158375 LightSlope158375 ClassCertificates88404
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

theorem length {k : ℕ} (hk : k < 81) : (row k).bands.length=7 := by
  interval_cases k <;> rfl

def terms (k : ℕ) (b : CrossBandCredit208.Band) : Finset Term :=
  match k, b.val with
  | 0, 0 => {⟨2, 88, 5⟩, ⟨2, 175, 1⟩, ⟨3, 88, 1⟩, ⟨11, 88, 1⟩}
  | 1, 0 => {⟨2, 87, 5⟩, ⟨2, 172, 1⟩, ⟨3, 87, 1⟩, ⟨11, 87, 1⟩}
  | 2, 0 => {⟨2, 86, 5⟩, ⟨2, 169, 1⟩, ⟨3, 86, 1⟩, ⟨11, 86, 1⟩}
  | 3, 0 => {⟨2, 85, 6⟩, ⟨2, 166, 1⟩, ⟨3, 85, 2⟩, ⟨11, 85, 1⟩}
  | 3, 1 => {⟨2, 178, 1⟩}
  | 4, 0 => {⟨2, 84, 6⟩, ⟨2, 163, 1⟩, ⟨3, 84, 2⟩, ⟨11, 84, 1⟩}
  | 4, 1 => {⟨2, 178, 1⟩}
  | 5, 0 => {⟨2, 83, 6⟩, ⟨2, 160, 1⟩, ⟨3, 83, 2⟩, ⟨11, 83, 1⟩}
  | 5, 1 => {⟨2, 178, 1⟩}
  | 6, 0 => {⟨2, 82, 6⟩, ⟨2, 157, 1⟩, ⟨3, 82, 2⟩, ⟨11, 82, 1⟩}
  | 6, 1 => {⟨2, 178, 1⟩}
  | 7, 0 => {⟨2, 81, 6⟩, ⟨2, 154, 1⟩, ⟨3, 81, 2⟩, ⟨11, 81, 1⟩}
  | 7, 1 => {⟨2, 178, 1⟩}
  | 8, 0 => {⟨2, 80, 6⟩, ⟨2, 151, 1⟩, ⟨3, 80, 2⟩, ⟨11, 80, 1⟩}
  | 8, 1 => {⟨2, 178, 1⟩}
  | 9, 0 => {⟨2, 79, 6⟩, ⟨2, 148, 2⟩, ⟨3, 79, 2⟩, ⟨11, 79, 1⟩}
  | 9, 1 => {⟨2, 177, 1⟩}
  | 10, 0 => {⟨2, 78, 7⟩, ⟨2, 145, 2⟩, ⟨3, 78, 2⟩, ⟨11, 78, 1⟩}
  | 10, 1 => {⟨2, 177, 1⟩}
  | 11, 0 => {⟨2, 77, 7⟩, ⟨2, 142, 2⟩, ⟨2, 207, 1⟩, ⟨3, 77, 2⟩, ⟨11, 77, 1⟩}
  | 11, 1 => {⟨2, 177, 1⟩}
  | 12, 0 => {⟨2, 76, 7⟩, ⟨2, 139, 2⟩, ⟨2, 202, 1⟩, ⟨3, 76, 2⟩, ⟨11, 76, 1⟩}
  | 12, 1 => {⟨2, 177, 1⟩}
  | 13, 0 => {⟨2, 75, 7⟩, ⟨2, 136, 2⟩, ⟨2, 197, 1⟩, ⟨3, 75, 2⟩, ⟨11, 75, 1⟩}
  | 13, 1 => {⟨2, 177, 1⟩}
  | 14, 0 => {⟨2, 74, 7⟩, ⟨2, 133, 2⟩, ⟨2, 192, 1⟩, ⟨3, 74, 2⟩, ⟨11, 74, 1⟩}
  | 14, 1 => {⟨2, 177, 1⟩}
  | 15, 0 => {⟨2, 73, 8⟩, ⟨2, 130, 2⟩, ⟨2, 187, 1⟩, ⟨3, 73, 2⟩, ⟨11, 73, 1⟩}
  | 15, 1 => {⟨2, 177, 1⟩}
  | 16, 0 => {⟨2, 72, 8⟩, ⟨2, 127, 2⟩, ⟨2, 182, 1⟩, ⟨3, 72, 2⟩, ⟨11, 72, 1⟩}
  | 16, 1 => {⟨2, 177, 1⟩}
  | 17, 0 => {⟨2, 71, 8⟩, ⟨2, 124, 2⟩, ⟨2, 177, 1⟩, ⟨3, 71, 2⟩, ⟨11, 71, 1⟩}
  | 17, 1 => {⟨2, 177, 1⟩}
  | 18, 0 => {⟨2, 70, 8⟩, ⟨2, 121, 2⟩, ⟨2, 172, 1⟩, ⟨3, 70, 2⟩, ⟨11, 70, 1⟩}
  | 18, 1 => {⟨2, 177, 1⟩}
  | 19, 0 => {⟨2, 69, 9⟩, ⟨2, 118, 3⟩, ⟨2, 167, 1⟩, ⟨3, 69, 3⟩, ⟨11, 69, 1⟩}
  | 19, 1 => {⟨2, 176, 1⟩}
  | 20, 0 => {⟨2, 68, 9⟩, ⟨2, 115, 3⟩, ⟨2, 162, 1⟩, ⟨2, 209, 1⟩, ⟨3, 68, 3⟩, ⟨11, 68, 1⟩}
  | 20, 1 => {⟨2, 176, 1⟩}
  | 21, 0 => {⟨2, 67, 9⟩, ⟨2, 112, 3⟩, ⟨2, 157, 1⟩, ⟨2, 202, 1⟩, ⟨3, 67, 3⟩, ⟨11, 67, 1⟩}
  | 21, 1 => {⟨2, 176, 1⟩}
  | 22, 0 => {⟨2, 66, 9⟩, ⟨2, 109, 3⟩, ⟨2, 152, 1⟩, ⟨2, 195, 1⟩, ⟨3, 66, 3⟩, ⟨11, 66, 1⟩}
  | 22, 1 => {⟨2, 176, 1⟩}
  | 23, 0 => {⟨2, 65, 10⟩, ⟨2, 106, 3⟩, ⟨2, 147, 2⟩, ⟨2, 188, 1⟩, ⟨3, 65, 3⟩, ⟨3, 118, 1⟩, ⟨5, 65, 1⟩, ⟨11, 65, 2⟩}
  | 23, 1 => {⟨2, 176, 1⟩}
  | 24, 0 => {⟨2, 64, 10⟩, ⟨2, 103, 4⟩, ⟨2, 142, 2⟩, ⟨2, 181, 1⟩, ⟨3, 64, 3⟩, ⟨3, 116, 1⟩, ⟨5, 64, 1⟩, ⟨11, 64, 2⟩}
  | 24, 1 => {⟨2, 176, 1⟩}
  | 25, 0 => {⟨2, 63, 10⟩, ⟨2, 100, 4⟩, ⟨2, 137, 2⟩, ⟨2, 174, 1⟩, ⟨3, 63, 3⟩, ⟨3, 113, 1⟩, ⟨5, 63, 1⟩, ⟨11, 63, 2⟩}
  | 25, 1 => {⟨2, 176, 1⟩}
  | 26, 0 => {⟨2, 62, 11⟩, ⟨2, 97, 4⟩, ⟨2, 132, 2⟩, ⟨2, 167, 1⟩, ⟨2, 202, 1⟩, ⟨3, 62, 3⟩, ⟨3, 111, 1⟩, ⟨5, 62, 1⟩, ⟨11, 62, 2⟩}
  | 26, 1 => {⟨2, 176, 1⟩}
  | 27, 0 => {⟨2, 61, 11⟩, ⟨2, 94, 4⟩, ⟨2, 127, 2⟩, ⟨2, 160, 1⟩, ⟨2, 193, 1⟩, ⟨3, 61, 3⟩, ⟨3, 108, 1⟩, ⟨5, 61, 1⟩, ⟨11, 61, 2⟩}
  | 27, 1 => {⟨2, 176, 1⟩}
  | 28, 0 => {⟨2, 56, 13⟩, ⟨2, 84, 6⟩, ⟨2, 112, 3⟩, ⟨2, 140, 2⟩, ⟨2, 168, 1⟩, ⟨2, 196, 1⟩, ⟨3, 56, 4⟩, ⟨3, 96, 1⟩, ⟨5, 56, 1⟩, ⟨11, 56, 2⟩}
  | 28, 1 => {⟨2, 152, 1⟩}
  | 29, 0 => {⟨2, 55, 14⟩, ⟨2, 83, 6⟩, ⟨2, 111, 3⟩, ⟨2, 139, 2⟩, ⟨2, 167, 1⟩, ⟨2, 195, 1⟩, ⟨3, 55, 4⟩, ⟨3, 93, 1⟩, ⟨5, 55, 1⟩, ⟨11, 55, 3⟩}
  | 29, 1 => {⟨2, 152, 1⟩}
  | 30, 0 => {⟨2, 54, 14⟩, ⟨2, 81, 6⟩, ⟨2, 108, 3⟩, ⟨2, 135, 2⟩, ⟨2, 162, 1⟩, ⟨2, 189, 1⟩, ⟨3, 54, 4⟩, ⟨3, 91, 1⟩, ⟨5, 54, 1⟩, ⟨11, 54, 3⟩}
  | 30, 1 => {⟨2, 151, 1⟩}
  | 31, 0 => {⟨2, 53, 15⟩, ⟨2, 80, 6⟩, ⟨2, 107, 3⟩, ⟨2, 134, 2⟩, ⟨2, 161, 1⟩, ⟨2, 188, 1⟩, ⟨3, 53, 5⟩, ⟨3, 89, 1⟩, ⟨5, 53, 2⟩, ⟨11, 53, 4⟩}
  | 31, 1 => {⟨2, 151, 1⟩}
  | 32, 0 => {⟨2, 52, 16⟩, ⟨2, 78, 7⟩, ⟨2, 104, 4⟩, ⟨2, 130, 2⟩, ⟨2, 156, 1⟩, ⟨2, 182, 1⟩, ⟨2, 208, 1⟩, ⟨3, 52, 5⟩, ⟨3, 87, 1⟩, ⟨5, 52, 2⟩, ⟨11, 52, 3⟩}
  | 32, 1 => {⟨2, 151, 1⟩}
  | 33, 0 => {⟨2, 51, 16⟩, ⟨2, 77, 7⟩, ⟨2, 103, 4⟩, ⟨2, 129, 2⟩, ⟨2, 155, 1⟩, ⟨2, 181, 1⟩, ⟨2, 207, 1⟩, ⟨3, 51, 5⟩, ⟨3, 85, 2⟩, ⟨3, 119, 1⟩, ⟨5, 51, 2⟩, ⟨11, 51, 3⟩}
  | 33, 1 => {⟨2, 151, 1⟩}
  | 34, 0 => {⟨2, 50, 17⟩, ⟨2, 75, 7⟩, ⟨2, 100, 4⟩, ⟨2, 125, 2⟩, ⟨2, 150, 1⟩, ⟨2, 175, 1⟩, ⟨2, 200, 1⟩, ⟨3, 50, 5⟩, ⟨3, 84, 2⟩, ⟨3, 118, 1⟩, ⟨5, 50, 2⟩, ⟨11, 50, 4⟩}
  | 34, 1 => {⟨2, 150, 1⟩}
  | 35, 0 => {⟨2, 49, 18⟩, ⟨2, 74, 7⟩, ⟨2, 99, 4⟩, ⟨2, 124, 2⟩, ⟨2, 149, 1⟩, ⟨2, 174, 1⟩, ⟨2, 199, 1⟩, ⟨3, 49, 6⟩, ⟨3, 82, 2⟩, ⟨3, 115, 1⟩, ⟨5, 49, 2⟩, ⟨11, 49, 5⟩}
  | 35, 1 => {⟨2, 150, 1⟩}
  | 36, 0 => {⟨2, 48, 18⟩, ⟨2, 72, 8⟩, ⟨2, 96, 4⟩, ⟨2, 120, 3⟩, ⟨2, 144, 2⟩, ⟨2, 168, 1⟩, ⟨2, 192, 1⟩, ⟨3, 48, 6⟩, ⟨3, 80, 2⟩, ⟨3, 112, 1⟩, ⟨5, 48, 2⟩, ⟨11, 48, 5⟩, ⟨11, 92, 1⟩}
  | 36, 1 => {⟨2, 150, 1⟩}
  | 37, 0 => {⟨2, 47, 19⟩, ⟨2, 71, 8⟩, ⟨2, 95, 4⟩, ⟨2, 119, 3⟩, ⟨2, 143, 2⟩, ⟨2, 167, 1⟩, ⟨2, 191, 1⟩, ⟨3, 47, 6⟩, ⟨3, 79, 2⟩, ⟨3, 111, 1⟩, ⟨5, 47, 2⟩, ⟨11, 47, 5⟩, ⟨11, 90, 1⟩}
  | 37, 1 => {⟨2, 150, 1⟩}
  | 38, 0 => {⟨2, 46, 20⟩, ⟨2, 69, 9⟩, ⟨2, 92, 5⟩, ⟨2, 115, 3⟩, ⟨2, 138, 2⟩, ⟨2, 161, 1⟩, ⟨2, 184, 1⟩, ⟨2, 207, 1⟩, ⟨3, 46, 6⟩, ⟨3, 77, 2⟩, ⟨3, 108, 1⟩, ⟨5, 46, 2⟩, ⟨11, 46, 6⟩, ⟨11, 88, 1⟩}
  | 38, 1 => {⟨2, 149, 1⟩}
  | 39, 0 => {⟨2, 45, 21⟩, ⟨2, 68, 9⟩, ⟨2, 91, 5⟩, ⟨2, 114, 3⟩, ⟨2, 137, 2⟩, ⟨2, 160, 1⟩, ⟨2, 183, 1⟩, ⟨2, 206, 1⟩, ⟨3, 45, 7⟩, ⟨3, 75, 2⟩, ⟨3, 105, 1⟩, ⟨5, 45, 2⟩, ⟨7, 45, 1⟩, ⟨11, 45, 7⟩, ⟨11, 86, 1⟩}
  | 39, 1 => {⟨2, 149, 1⟩}
  | 40, 0 => {⟨2, 44, 22⟩, ⟨2, 66, 9⟩, ⟨2, 88, 5⟩, ⟨2, 110, 3⟩, ⟨2, 132, 2⟩, ⟨2, 154, 1⟩, ⟨2, 176, 1⟩, ⟨2, 198, 1⟩, ⟨3, 44, 7⟩, ⟨3, 74, 2⟩, ⟨3, 104, 1⟩, ⟨5, 44, 2⟩, ⟨7, 44, 1⟩, ⟨11, 44, 6⟩, ⟨11, 84, 1⟩}
  | 40, 1 => {⟨2, 149, 1⟩}
  | 41, 0 => {⟨2, 43, 23⟩, ⟨2, 65, 10⟩, ⟨2, 87, 5⟩, ⟨2, 109, 3⟩, ⟨2, 131, 2⟩, ⟨2, 153, 1⟩, ⟨2, 175, 1⟩, ⟨2, 197, 1⟩, ⟨3, 43, 7⟩, ⟨3, 72, 2⟩, ⟨3, 101, 1⟩, ⟨5, 43, 2⟩, ⟨7, 43, 1⟩, ⟨11, 43, 7⟩, ⟨11, 83, 1⟩}
  | 41, 1 => {⟨2, 149, 1⟩}
  | 42, 0 => {⟨2, 42, 24⟩, ⟨2, 63, 10⟩, ⟨2, 84, 6⟩, ⟨2, 105, 3⟩, ⟨2, 126, 2⟩, ⟨2, 147, 2⟩, ⟨2, 168, 1⟩, ⟨2, 189, 1⟩, ⟨3, 42, 8⟩, ⟨3, 70, 2⟩, ⟨3, 98, 1⟩, ⟨5, 42, 2⟩, ⟨7, 42, 1⟩, ⟨11, 42, 8⟩, ⟨11, 81, 1⟩}
  | 42, 1 => {⟨2, 149, 1⟩}
  | 43, 0 => {⟨2, 41, 25⟩, ⟨2, 62, 11⟩, ⟨2, 83, 6⟩, ⟨2, 104, 4⟩, ⟨2, 125, 2⟩, ⟨2, 146, 2⟩, ⟨2, 167, 1⟩, ⟨2, 188, 1⟩, ⟨2, 209, 1⟩, ⟨3, 41, 8⟩, ⟨3, 69, 3⟩, ⟨3, 97, 1⟩, ⟨5, 41, 3⟩, ⟨7, 41, 1⟩, ⟨11, 41, 8⟩, ⟨11, 79, 1⟩}
  | 43, 1 => {⟨2, 148, 2⟩}
  | 44, 0 => {⟨2, 40, 26⟩, ⟨2, 60, 12⟩, ⟨2, 80, 6⟩, ⟨2, 100, 4⟩, ⟨2, 120, 3⟩, ⟨2, 140, 2⟩, ⟨2, 160, 1⟩, ⟨2, 180, 1⟩, ⟨2, 200, 1⟩, ⟨3, 40, 8⟩, ⟨3, 67, 3⟩, ⟨3, 94, 1⟩, ⟨5, 40, 3⟩, ⟨7, 40, 1⟩, ⟨11, 40, 8⟩, ⟨11, 77, 1⟩}
  | 44, 1 => {⟨2, 148, 2⟩}
  | 45, 0 => {⟨2, 39, 28⟩, ⟨2, 59, 12⟩, ⟨2, 79, 6⟩, ⟨2, 99, 4⟩, ⟨2, 119, 3⟩, ⟨2, 139, 2⟩, ⟨2, 159, 1⟩, ⟨2, 179, 1⟩, ⟨2, 199, 1⟩, ⟨3, 39, 9⟩, ⟨3, 65, 3⟩, ⟨3, 91, 1⟩, ⟨3, 117, 1⟩, ⟨5, 39, 3⟩, ⟨7, 39, 1⟩, ⟨11, 39, 9⟩, ⟨11, 75, 1⟩}
  | 45, 1 => {⟨2, 148, 2⟩}
  | 46, 0 => {⟨2, 38, 29⟩, ⟨2, 57, 13⟩, ⟨2, 76, 7⟩, ⟨2, 95, 4⟩, ⟨2, 114, 3⟩, ⟨2, 133, 2⟩, ⟨2, 152, 1⟩, ⟨2, 171, 1⟩, ⟨2, 190, 1⟩, ⟨2, 209, 1⟩, ⟨3, 38, 9⟩, ⟨3, 64, 3⟩, ⟨3, 90, 1⟩, ⟨3, 116, 1⟩, ⟨5, 38, 3⟩, ⟨7, 38, 1⟩, ⟨11, 38, 9⟩, ⟨11, 73, 1⟩}
  | 46, 1 => {⟨2, 147, 2⟩}
  | 47, 0 => {⟨2, 37, 31⟩, ⟨2, 56, 13⟩, ⟨2, 75, 7⟩, ⟨2, 94, 4⟩, ⟨2, 113, 3⟩, ⟨2, 132, 2⟩, ⟨2, 151, 1⟩, ⟨2, 170, 1⟩, ⟨2, 189, 1⟩, ⟨2, 208, 1⟩, ⟨3, 37, 10⟩, ⟨3, 62, 3⟩, ⟨3, 87, 1⟩, ⟨3, 112, 1⟩, ⟨5, 37, 4⟩, ⟨7, 37, 1⟩, ⟨11, 37, 10⟩, ⟨11, 71, 1⟩}
  | 47, 1 => {⟨2, 147, 2⟩}
  | 48, 0 => {⟨2, 36, 33⟩, ⟨2, 54, 14⟩, ⟨2, 72, 8⟩, ⟨2, 90, 5⟩, ⟨2, 108, 3⟩, ⟨2, 126, 2⟩, ⟨2, 144, 2⟩, ⟨2, 162, 1⟩, ⟨2, 180, 1⟩, ⟨2, 198, 1⟩, ⟨3, 36, 11⟩, ⟨3, 60, 4⟩, ⟨3, 84, 2⟩, ⟨3, 108, 1⟩, ⟨5, 36, 4⟩, ⟨5, 65, 1⟩, ⟨7, 36, 1⟩, ⟨11, 36, 12⟩, ⟨11, 69, 1⟩}
  | 48, 1 => {⟨2, 120, 3⟩, ⟨3, 120, 1⟩}
  | 49, 0 => {⟨2, 35, 35⟩, ⟨2, 53, 15⟩, ⟨2, 71, 8⟩, ⟨2, 89, 5⟩, ⟨2, 107, 3⟩, ⟨2, 125, 2⟩, ⟨2, 143, 2⟩, ⟨2, 161, 1⟩, ⟨2, 179, 1⟩, ⟨2, 197, 1⟩, ⟨3, 35, 11⟩, ⟨3, 59, 4⟩, ⟨3, 83, 2⟩, ⟨3, 107, 1⟩, ⟨5, 35, 4⟩, ⟨5, 63, 1⟩, ⟨7, 35, 2⟩, ⟨11, 35, 14⟩, ⟨11, 67, 1⟩}
  | 49, 1 => {⟨2, 120, 3⟩, ⟨3, 120, 1⟩}
  | 50, 0 => {⟨2, 34, 37⟩, ⟨2, 51, 16⟩, ⟨2, 68, 9⟩, ⟨2, 85, 6⟩, ⟨2, 102, 4⟩, ⟨2, 119, 3⟩, ⟨2, 136, 2⟩, ⟨2, 153, 1⟩, ⟨2, 170, 1⟩, ⟨2, 187, 1⟩, ⟨2, 204, 1⟩, ⟨3, 34, 12⟩, ⟨3, 57, 4⟩, ⟨3, 80, 2⟩, ⟨3, 103, 1⟩, ⟨5, 34, 4⟩, ⟨5, 62, 1⟩, ⟨7, 34, 2⟩, ⟨11, 34, 13⟩, ⟨11, 65, 2⟩}
  | 50, 1 => {⟨2, 119, 3⟩, ⟨3, 119, 1⟩}
  | 51, 0 => {⟨2, 33, 39⟩, ⟨2, 50, 17⟩, ⟨2, 67, 9⟩, ⟨2, 84, 6⟩, ⟨2, 101, 4⟩, ⟨2, 118, 3⟩, ⟨2, 135, 2⟩, ⟨2, 152, 1⟩, ⟨2, 169, 1⟩, ⟨2, 186, 1⟩, ⟨2, 203, 1⟩, ⟨3, 33, 13⟩, ⟨3, 55, 4⟩, ⟨3, 77, 2⟩, ⟨3, 99, 1⟩, ⟨5, 33, 4⟩, ⟨5, 60, 1⟩, ⟨7, 33, 2⟩, ⟨11, 33, 15⟩, ⟨11, 63, 2⟩, ⟨11, 93, 1⟩}
  | 51, 1 => {⟨2, 119, 3⟩, ⟨3, 119, 1⟩}
  | 52, 0 => {⟨2, 87, 5⟩, ⟨2, 171, 1⟩, ⟨3, 87, 1⟩, ⟨11, 87, 1⟩}
  | 53, 0 => {⟨2, 82, 6⟩, ⟨2, 156, 1⟩, ⟨3, 82, 2⟩, ⟨11, 82, 1⟩}
  | 53, 1 => {⟨2, 180, 1⟩}
  | 54, 0 => {⟨2, 77, 7⟩, ⟨2, 141, 2⟩, ⟨2, 205, 1⟩, ⟨3, 77, 2⟩, ⟨11, 77, 1⟩}
  | 54, 1 => {⟨2, 179, 1⟩}
  | 55, 0 => {⟨2, 72, 8⟩, ⟨2, 126, 2⟩, ⟨2, 180, 1⟩, ⟨3, 72, 2⟩, ⟨11, 72, 1⟩}
  | 55, 1 => {⟨2, 179, 1⟩}
  | 56, 0 => {⟨2, 64, 10⟩, ⟨2, 102, 4⟩, ⟨2, 140, 2⟩, ⟨2, 178, 1⟩, ⟨3, 64, 3⟩, ⟨3, 115, 1⟩, ⟨5, 64, 1⟩, ⟨11, 64, 2⟩}
  | 56, 1 => {⟨2, 178, 1⟩}
  | 57, 0 => {⟨2, 55, 14⟩, ⟨2, 83, 6⟩, ⟨2, 111, 3⟩, ⟨2, 139, 2⟩, ⟨2, 167, 1⟩, ⟨2, 195, 1⟩, ⟨3, 55, 4⟩, ⟨3, 93, 1⟩, ⟨5, 55, 1⟩, ⟨11, 55, 3⟩}
  | 57, 1 => {⟨2, 154, 1⟩}
  | 58, 0 => {⟨2, 53, 15⟩, ⟨2, 80, 6⟩, ⟨2, 107, 3⟩, ⟨2, 134, 2⟩, ⟨2, 161, 1⟩, ⟨2, 188, 1⟩, ⟨3, 53, 5⟩, ⟨3, 89, 1⟩, ⟨5, 53, 2⟩, ⟨11, 53, 4⟩}
  | 58, 1 => {⟨2, 153, 1⟩}
  | 59, 0 => {⟨2, 51, 17⟩, ⟨2, 77, 7⟩, ⟨2, 103, 4⟩, ⟨2, 129, 2⟩, ⟨2, 155, 1⟩, ⟨2, 181, 1⟩, ⟨2, 207, 1⟩, ⟨3, 51, 5⟩, ⟨3, 85, 2⟩, ⟨3, 119, 1⟩, ⟨5, 51, 2⟩, ⟨11, 51, 4⟩}
  | 59, 1 => {⟨2, 152, 1⟩}
  | 60, 0 => {⟨2, 49, 18⟩, ⟨2, 74, 8⟩, ⟨2, 99, 4⟩, ⟨2, 124, 2⟩, ⟨2, 149, 2⟩, ⟨2, 174, 1⟩, ⟨2, 199, 1⟩, ⟨3, 49, 6⟩, ⟨3, 82, 2⟩, ⟨3, 115, 1⟩, ⟨5, 49, 2⟩, ⟨11, 49, 5⟩, ⟨11, 94, 1⟩}
  | 60, 1 => {⟨2, 152, 1⟩}
  | 61, 0 => {⟨2, 47, 20⟩, ⟨2, 71, 8⟩, ⟨2, 95, 4⟩, ⟨2, 119, 3⟩, ⟨2, 143, 2⟩, ⟨2, 167, 1⟩, ⟨2, 191, 1⟩, ⟨3, 47, 6⟩, ⟨3, 79, 2⟩, ⟨3, 111, 1⟩, ⟨5, 47, 2⟩, ⟨11, 47, 6⟩, ⟨11, 90, 1⟩}
  | 61, 1 => {⟨2, 151, 1⟩}
  | 62, 0 => {⟨2, 44, 22⟩, ⟨2, 66, 10⟩, ⟨2, 88, 5⟩, ⟨2, 110, 3⟩, ⟨2, 132, 2⟩, ⟨2, 154, 1⟩, ⟨2, 176, 1⟩, ⟨2, 198, 1⟩, ⟨3, 44, 7⟩, ⟨3, 74, 2⟩, ⟨3, 104, 1⟩, ⟨5, 44, 2⟩, ⟨7, 44, 1⟩, ⟨11, 44, 6⟩, ⟨11, 84, 1⟩}
  | 62, 1 => {⟨2, 151, 1⟩}
  | 63, 0 => {⟨2, 41, 26⟩, ⟨2, 62, 11⟩, ⟨2, 83, 6⟩, ⟨2, 104, 4⟩, ⟨2, 125, 2⟩, ⟨2, 146, 2⟩, ⟨2, 167, 1⟩, ⟨2, 188, 1⟩, ⟨2, 209, 1⟩, ⟨3, 41, 8⟩, ⟨3, 69, 3⟩, ⟨3, 97, 1⟩, ⟨5, 41, 3⟩, ⟨7, 41, 1⟩, ⟨11, 41, 8⟩, ⟨11, 79, 1⟩}
  | 63, 1 => {⟨2, 150, 1⟩}
  | 64, 0 => {⟨2, 39, 28⟩, ⟨2, 59, 12⟩, ⟨2, 79, 7⟩, ⟨2, 99, 4⟩, ⟨2, 119, 3⟩, ⟨2, 139, 2⟩, ⟨2, 159, 1⟩, ⟨2, 179, 1⟩, ⟨2, 199, 1⟩, ⟨3, 39, 9⟩, ⟨3, 65, 3⟩, ⟨3, 91, 1⟩, ⟨3, 117, 1⟩, ⟨5, 39, 3⟩, ⟨7, 39, 1⟩, ⟨11, 39, 9⟩, ⟨11, 75, 1⟩}
  | 64, 1 => {⟨2, 150, 1⟩}
  | 65, 0 => {⟨2, 37, 32⟩, ⟨2, 56, 14⟩, ⟨2, 75, 7⟩, ⟨2, 94, 5⟩, ⟨2, 113, 3⟩, ⟨2, 132, 2⟩, ⟨2, 151, 1⟩, ⟨2, 170, 1⟩, ⟨2, 189, 1⟩, ⟨2, 208, 1⟩, ⟨3, 37, 10⟩, ⟨3, 62, 3⟩, ⟨3, 87, 1⟩, ⟨3, 112, 1⟩, ⟨5, 37, 4⟩, ⟨7, 37, 1⟩, ⟨11, 37, 11⟩, ⟨11, 71, 1⟩}
  | 65, 1 => {⟨2, 121, 3⟩, ⟨3, 121, 1⟩}
  | 66, 0 => {⟨2, 35, 35⟩, ⟨2, 53, 15⟩, ⟨2, 71, 8⟩, ⟨2, 89, 5⟩, ⟨2, 107, 3⟩, ⟨2, 125, 2⟩, ⟨2, 143, 2⟩, ⟨2, 161, 1⟩, ⟨2, 179, 1⟩, ⟨2, 197, 1⟩, ⟨3, 35, 11⟩, ⟨3, 59, 4⟩, ⟨3, 83, 2⟩, ⟨3, 107, 1⟩, ⟨5, 35, 4⟩, ⟨5, 63, 1⟩, ⟨7, 35, 2⟩, ⟨11, 35, 14⟩, ⟨11, 67, 1⟩}
  | 66, 1 => {⟨2, 120, 3⟩, ⟨3, 120, 1⟩}
  | 67, 0 => {⟨2, 34, 37⟩, ⟨2, 51, 17⟩, ⟨2, 68, 9⟩, ⟨2, 85, 6⟩, ⟨2, 102, 4⟩, ⟨2, 119, 3⟩, ⟨2, 136, 2⟩, ⟨2, 153, 1⟩, ⟨2, 170, 1⟩, ⟨2, 187, 1⟩, ⟨2, 204, 1⟩, ⟨3, 34, 12⟩, ⟨3, 57, 4⟩, ⟨3, 80, 2⟩, ⟨3, 103, 1⟩, ⟨5, 34, 4⟩, ⟨5, 62, 1⟩, ⟨7, 34, 2⟩, ⟨11, 34, 13⟩, ⟨11, 65, 2⟩}
  | 67, 1 => {⟨2, 120, 3⟩, ⟨3, 120, 1⟩}
  | 68, 0 => {⟨2, 88, 5⟩, ⟨2, 173, 1⟩, ⟨3, 88, 1⟩, ⟨11, 88, 1⟩}
  | 69, 0 => {⟨2, 81, 6⟩, ⟨2, 152, 1⟩, ⟨3, 81, 2⟩, ⟨11, 81, 1⟩}
  | 69, 1 => {⟨2, 181, 1⟩}
  | 70, 0 => {⟨2, 73, 8⟩, ⟨2, 128, 2⟩, ⟨2, 183, 1⟩, ⟨3, 73, 2⟩, ⟨11, 73, 1⟩}
  | 70, 1 => {⟨2, 181, 1⟩}
  | 71, 0 => {⟨2, 64, 11⟩, ⟨2, 101, 4⟩, ⟨2, 138, 2⟩, ⟨2, 175, 1⟩, ⟨2, 212, 1⟩, ⟨3, 64, 3⟩, ⟨3, 115, 1⟩, ⟨5, 64, 1⟩, ⟨11, 64, 2⟩}
  | 71, 1 => {⟨2, 180, 1⟩}
  | 72, 0 => {⟨2, 53, 16⟩, ⟨2, 80, 7⟩, ⟨2, 107, 3⟩, ⟨2, 134, 2⟩, ⟨2, 161, 1⟩, ⟨2, 188, 1⟩, ⟨3, 53, 5⟩, ⟨3, 89, 1⟩, ⟨5, 53, 2⟩, ⟨11, 53, 3⟩}
  | 72, 1 => {⟨2, 155, 1⟩}
  | 73, 0 => {⟨2, 49, 18⟩, ⟨2, 74, 8⟩, ⟨2, 99, 4⟩, ⟨2, 124, 2⟩, ⟨2, 149, 2⟩, ⟨2, 174, 1⟩, ⟨2, 199, 1⟩, ⟨3, 49, 6⟩, ⟨3, 82, 2⟩, ⟨3, 115, 1⟩, ⟨5, 49, 2⟩, ⟨11, 49, 5⟩, ⟨11, 94, 1⟩}
  | 73, 1 => {⟨2, 154, 1⟩}
  | 74, 0 => {⟨2, 45, 22⟩, ⟨2, 68, 9⟩, ⟨2, 91, 5⟩, ⟨2, 114, 3⟩, ⟨2, 137, 2⟩, ⟨2, 160, 1⟩, ⟨2, 183, 1⟩, ⟨2, 206, 1⟩, ⟨3, 45, 7⟩, ⟨3, 75, 2⟩, ⟨3, 105, 1⟩, ⟨5, 45, 2⟩, ⟨7, 45, 1⟩, ⟨11, 45, 6⟩, ⟨11, 86, 1⟩}
  | 74, 1 => {⟨2, 153, 1⟩}
  | 75, 0 => {⟨2, 41, 26⟩, ⟨2, 62, 11⟩, ⟨2, 83, 6⟩, ⟨2, 104, 4⟩, ⟨2, 125, 2⟩, ⟨2, 146, 2⟩, ⟨2, 167, 1⟩, ⟨2, 188, 1⟩, ⟨2, 209, 1⟩, ⟨3, 41, 8⟩, ⟨3, 69, 3⟩, ⟨3, 97, 1⟩, ⟨5, 41, 3⟩, ⟨7, 41, 1⟩, ⟨11, 41, 8⟩, ⟨11, 79, 1⟩}
  | 75, 1 => {⟨2, 152, 1⟩}
  | 76, 0 => {⟨2, 39, 29⟩, ⟨2, 59, 13⟩, ⟨2, 79, 7⟩, ⟨2, 99, 4⟩, ⟨2, 119, 3⟩, ⟨2, 139, 2⟩, ⟨2, 159, 1⟩, ⟨2, 179, 1⟩, ⟨2, 199, 1⟩, ⟨3, 39, 9⟩, ⟨3, 65, 3⟩, ⟨3, 91, 1⟩, ⟨3, 117, 1⟩, ⟨5, 39, 3⟩, ⟨7, 39, 1⟩, ⟨11, 39, 9⟩, ⟨11, 75, 1⟩}
  | 76, 1 => {⟨2, 151, 2⟩}
  | 77, 0 => {⟨2, 35, 36⟩, ⟨2, 53, 16⟩, ⟨2, 71, 9⟩, ⟨2, 89, 5⟩, ⟨2, 107, 3⟩, ⟨2, 125, 2⟩, ⟨2, 143, 2⟩, ⟨2, 161, 1⟩, ⟨2, 179, 1⟩, ⟨2, 197, 1⟩, ⟨3, 35, 12⟩, ⟨3, 59, 4⟩, ⟨3, 83, 2⟩, ⟨3, 107, 1⟩, ⟨5, 35, 4⟩, ⟨5, 63, 1⟩, ⟨7, 35, 2⟩, ⟨11, 35, 13⟩, ⟨11, 67, 2⟩}
  | 77, 1 => {⟨2, 122, 3⟩, ⟨3, 122, 1⟩}
  | 78, 0 => {⟨2, 126, 2⟩}
  | 79, 0 => {⟨2, 111, 3⟩, ⟨2, 204, 1⟩, ⟨3, 111, 1⟩}
  | 80, 0 => {⟨2, 94, 4⟩, ⟨2, 153, 1⟩, ⟨3, 94, 1⟩}
  | _, _ => ∅

def slope : ℕ → ℕ
  | 0 => 720
  | 1 => 720
  | 2 => 720
  | 3 => 1080
  | 4 => 1080
  | 5 => 1080
  | 6 => 1080
  | 7 => 1080
  | 8 => 1080
  | 9 => 1170
  | 10 => 1260
  | 11 => 1350
  | 12 => 1350
  | 13 => 1350
  | 14 => 1350
  | 15 => 1440
  | 16 => 1440
  | 17 => 1440
  | 18 => 1440
  | 19 => 1710
  | 20 => 1800
  | 21 => 1800
  | 22 => 1800
  | 23 => 2250
  | 24 => 2340
  | 25 => 2340
  | 26 => 2520
  | 27 => 2520
  | 28 => 3217
  | 29 => 3397
  | 30 => 3397
  | 31 => 3757
  | 32 => 4027
  | 33 => 4207
  | 34 => 4387
  | 35 => 4657
  | 36 => 5017
  | 37 => 5107
  | 38 => 5557
  | 39 => 5917
  | 40 => 5917
  | 41 => 6187
  | 42 => 6637
  | 43 => 7334
  | 44 => 7604
  | 45 => 8054
  | 46 => 8414
  | 47 => 8864
  | 48 => 10170
  | 49 => 10710
  | 50 => 11520
  | 51 => 12150
  | 52 => 728
  | 53 => 1092
  | 54 => 1365
  | 55 => 1456
  | 56 => 2366
  | 57 => 3435
  | 58 => 3799
  | 59 => 4436
  | 60 => 4982
  | 61 => 5346
  | 62 => 6074
  | 63 => 7348
  | 64 => 8076
  | 65 => 9553
  | 66 => 10827
  | 67 => 11737
  | 68 => 736
  | 69 => 1104
  | 70 => 1472
  | 71 => 2576
  | 72 => 3933
  | 73 => 5037
  | 74 => 6049
  | 75 => 7429
  | 76 => 8510
  | 77 => 11316
  | 78 => 260
  | 79 => 650
  | 80 => 780
  | _ => 0

def FiniteFacts (k : ℕ) (hk : k < 81) : Prop :=
  (∀ b : CrossBandCredit208.Band,
    BandFacts (row k).high (data k).steps (At (row k) (length hk) b) (terms k b) ∧
      ∀ t ∈ terms k b, (t.p,(row k).low/(t.q*(t.q+1)),t.count) ∈ Required) ∧
    RowSlope (row k) (length hk) (terms k) = slope k

local instance (k : ℕ) (hk : k < 81) : Decidable (FiniteFacts k hk) :=
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

theorem facts59 : FiniteFacts 59 (by decide) := by decide +kernel
#print axioms facts59

theorem facts60 : FiniteFacts 60 (by decide) := by decide +kernel
#print axioms facts60

theorem facts61 : FiniteFacts 61 (by decide) := by decide +kernel
#print axioms facts61

theorem facts62 : FiniteFacts 62 (by decide) := by decide +kernel
#print axioms facts62

theorem facts63 : FiniteFacts 63 (by decide) := by decide +kernel
#print axioms facts63

theorem facts64 : FiniteFacts 64 (by decide) := by decide +kernel
#print axioms facts64

theorem facts65 : FiniteFacts 65 (by decide) := by decide +kernel
#print axioms facts65

theorem facts66 : FiniteFacts 66 (by decide) := by decide +kernel
#print axioms facts66

theorem facts67 : FiniteFacts 67 (by decide) := by decide +kernel
#print axioms facts67

theorem facts68 : FiniteFacts 68 (by decide) := by decide +kernel
#print axioms facts68

theorem facts69 : FiniteFacts 69 (by decide) := by decide +kernel
#print axioms facts69

theorem facts70 : FiniteFacts 70 (by decide) := by decide +kernel
#print axioms facts70

theorem facts71 : FiniteFacts 71 (by decide) := by decide +kernel
#print axioms facts71

theorem facts72 : FiniteFacts 72 (by decide) := by decide +kernel
#print axioms facts72

theorem facts73 : FiniteFacts 73 (by decide) := by decide +kernel
#print axioms facts73

theorem facts74 : FiniteFacts 74 (by decide) := by decide +kernel
#print axioms facts74

theorem facts75 : FiniteFacts 75 (by decide) := by decide +kernel
#print axioms facts75

theorem facts76 : FiniteFacts 76 (by decide) := by decide +kernel
#print axioms facts76

theorem facts77 : FiniteFacts 77 (by decide) := by decide +kernel
#print axioms facts77

theorem facts78 : FiniteFacts 78 (by decide) := by decide +kernel
#print axioms facts78

theorem facts79 : FiniteFacts 79 (by decide) := by decide +kernel
#print axioms facts79

theorem facts80 : FiniteFacts 80 (by decide) := by decide +kernel
#print axioms facts80

theorem facts {k : ℕ} (hk : k < 81) : FiniteFacts k hk := by
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
  · exact facts59
  · exact facts60
  · exact facts61
  · exact facts62
  · exact facts63
  · exact facts64
  · exact facts65
  · exact facts66
  · exact facts67
  · exact facts68
  · exact facts69
  · exact facts70
  · exact facts71
  · exact facts72
  · exact facts73
  · exact facts74
  · exact facts75
  · exact facts76
  · exact facts77
  · exact facts78
  · exact facts79
  · exact facts80

theorem slope_bound {k N : ℕ} (hk : k < 81)
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
end JSP233.RowLightSlope88404
