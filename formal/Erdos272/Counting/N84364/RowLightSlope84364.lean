module

public import Erdos272.Counting.N158375.LightSlope158375
public import Erdos272.Arithmetic.N84364.ClassCertificates84364
public import Erdos272.Arithmetic.N84364.CleanupRows84364
public import Erdos272.Arithmetic.CleanupMachineSound208

@[expose] public section

namespace JSP233.RowLightSlope84364
open CleanupRows84364 CleanupEval208 CleanupMachineSound208 ActualCleanupEval208
open LightFamily158375 LightSlope158375 ClassCertificates84364
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

theorem length {k : ℕ} (hk : k < 43) : (row k).bands.length=7 := by
  interval_cases k <;> rfl

def terms (k : ℕ) (b : CrossBandCredit208.Band) : Finset Term :=
  match k, b.val with
  | 0, 0 => {⟨2, 86, 5⟩, ⟨2, 171, 1⟩, ⟨3, 86, 1⟩, ⟨11, 86, 1⟩}
  | 1, 0 => {⟨2, 84, 5⟩, ⟨2, 165, 1⟩, ⟨3, 84, 1⟩, ⟨11, 84, 1⟩}
  | 2, 0 => {⟨2, 82, 6⟩, ⟨2, 159, 1⟩, ⟨3, 82, 2⟩, ⟨11, 82, 1⟩}
  | 3, 0 => {⟨2, 80, 6⟩, ⟨2, 153, 1⟩, ⟨3, 80, 2⟩, ⟨11, 80, 1⟩}
  | 4, 0 => {⟨2, 78, 6⟩, ⟨2, 147, 1⟩, ⟨3, 78, 2⟩, ⟨11, 78, 1⟩}
  | 5, 0 => {⟨2, 74, 7⟩, ⟨2, 135, 2⟩, ⟨2, 196, 1⟩, ⟨3, 74, 2⟩, ⟨11, 74, 1⟩}
  | 6, 0 => {⟨2, 72, 8⟩, ⟨2, 129, 2⟩, ⟨2, 186, 1⟩, ⟨3, 72, 2⟩, ⟨11, 72, 1⟩}
  | 7, 0 => {⟨2, 69, 8⟩, ⟨2, 120, 2⟩, ⟨2, 171, 1⟩, ⟨3, 69, 2⟩, ⟨11, 69, 1⟩}
  | 8, 0 => {⟨2, 66, 9⟩, ⟨2, 111, 3⟩, ⟨2, 156, 1⟩, ⟨2, 201, 1⟩, ⟨3, 66, 3⟩, ⟨11, 66, 1⟩}
  | 9, 0 => {⟨2, 63, 10⟩, ⟨2, 102, 4⟩, ⟨2, 141, 2⟩, ⟨2, 180, 1⟩, ⟨3, 63, 3⟩, ⟨3, 114, 1⟩, ⟨5, 63, 1⟩, ⟨11, 63, 2⟩}
  | 10, 0 => {⟨2, 53, 14⟩, ⟨2, 80, 6⟩, ⟨2, 107, 3⟩, ⟨2, 134, 2⟩, ⟨2, 161, 1⟩, ⟨2, 188, 1⟩, ⟨3, 53, 4⟩, ⟨3, 89, 1⟩, ⟨5, 53, 1⟩, ⟨11, 53, 3⟩}
  | 10, 1 => {⟨2, 149, 1⟩}
  | 11, 0 => {⟨2, 51, 15⟩, ⟨2, 77, 7⟩, ⟨2, 103, 3⟩, ⟨2, 129, 2⟩, ⟨2, 155, 1⟩, ⟨2, 181, 1⟩, ⟨3, 51, 5⟩, ⟨3, 85, 1⟩, ⟨5, 51, 2⟩, ⟨11, 51, 4⟩}
  | 11, 1 => {⟨2, 124, 2⟩}
  | 12, 0 => {⟨2, 49, 17⟩, ⟨2, 74, 7⟩, ⟨2, 99, 4⟩, ⟨2, 124, 2⟩, ⟨2, 149, 1⟩, ⟨2, 174, 1⟩, ⟨2, 199, 1⟩, ⟨3, 49, 5⟩, ⟨3, 82, 2⟩, ⟨3, 115, 1⟩, ⟨5, 49, 2⟩, ⟨11, 49, 4⟩}
  | 12, 1 => {⟨2, 148, 1⟩}
  | 13, 0 => {⟨2, 47, 18⟩, ⟨2, 71, 8⟩, ⟨2, 95, 4⟩, ⟨2, 119, 2⟩, ⟨2, 143, 2⟩, ⟨2, 167, 1⟩, ⟨2, 191, 1⟩, ⟨3, 47, 6⟩, ⟨3, 79, 2⟩, ⟨3, 111, 1⟩, ⟨5, 47, 2⟩, ⟨11, 47, 5⟩, ⟨11, 90, 1⟩}
  | 13, 1 => {⟨2, 123, 2⟩}
  | 14, 0 => {⟨2, 45, 20⟩, ⟨2, 68, 8⟩, ⟨2, 91, 5⟩, ⟨2, 114, 3⟩, ⟨2, 137, 2⟩, ⟨2, 160, 1⟩, ⟨2, 183, 1⟩, ⟨3, 45, 6⟩, ⟨3, 75, 2⟩, ⟨3, 105, 1⟩, ⟨5, 45, 2⟩, ⟨11, 45, 6⟩, ⟨11, 86, 1⟩}
  | 14, 1 => {⟨2, 122, 2⟩}
  | 15, 0 => {⟨2, 43, 22⟩, ⟨2, 65, 9⟩, ⟨2, 87, 5⟩, ⟨2, 109, 3⟩, ⟨2, 131, 2⟩, ⟨2, 153, 1⟩, ⟨2, 175, 1⟩, ⟨2, 197, 1⟩, ⟨3, 43, 7⟩, ⟨3, 72, 2⟩, ⟨3, 101, 1⟩, ⟨5, 43, 2⟩, ⟨7, 43, 1⟩, ⟨11, 43, 6⟩, ⟨11, 83, 1⟩}
  | 15, 1 => {⟨2, 121, 2⟩}
  | 16, 0 => {⟨2, 42, 23⟩, ⟨2, 63, 10⟩, ⟨2, 84, 5⟩, ⟨2, 105, 3⟩, ⟨2, 126, 2⟩, ⟨2, 147, 1⟩, ⟨2, 168, 1⟩, ⟨2, 189, 1⟩, ⟨3, 42, 7⟩, ⟨3, 70, 2⟩, ⟨3, 98, 1⟩, ⟨5, 42, 2⟩, ⟨7, 42, 1⟩, ⟨11, 42, 7⟩, ⟨11, 81, 1⟩}
  | 16, 1 => {⟨2, 121, 2⟩}
  | 17, 0 => {⟨2, 40, 25⟩, ⟨2, 60, 11⟩, ⟨2, 80, 6⟩, ⟨2, 100, 4⟩, ⟨2, 120, 2⟩, ⟨2, 140, 2⟩, ⟨2, 160, 1⟩, ⟨2, 180, 1⟩, ⟨2, 200, 1⟩, ⟨3, 40, 8⟩, ⟨3, 67, 3⟩, ⟨3, 94, 1⟩, ⟨5, 40, 3⟩, ⟨7, 40, 1⟩, ⟨11, 40, 8⟩, ⟨11, 77, 1⟩}
  | 17, 1 => {⟨2, 120, 2⟩}
  | 18, 0 => {⟨2, 39, 27⟩, ⟨2, 59, 11⟩, ⟨2, 79, 6⟩, ⟨2, 99, 4⟩, ⟨2, 119, 2⟩, ⟨2, 139, 2⟩, ⟨2, 159, 1⟩, ⟨2, 179, 1⟩, ⟨2, 199, 1⟩, ⟨3, 39, 9⟩, ⟨3, 65, 3⟩, ⟨3, 91, 1⟩, ⟨3, 117, 1⟩, ⟨5, 39, 3⟩, ⟨7, 39, 1⟩, ⟨11, 39, 9⟩, ⟨11, 75, 1⟩}
  | 18, 1 => {⟨2, 120, 2⟩}
  | 19, 0 => {⟨2, 37, 30⟩, ⟨2, 56, 13⟩, ⟨2, 75, 7⟩, ⟨2, 94, 4⟩, ⟨2, 113, 3⟩, ⟨2, 132, 2⟩, ⟨2, 151, 1⟩, ⟨2, 170, 1⟩, ⟨2, 189, 1⟩, ⟨3, 37, 10⟩, ⟨3, 62, 3⟩, ⟨3, 87, 1⟩, ⟨3, 112, 1⟩, ⟨5, 37, 4⟩, ⟨7, 37, 1⟩, ⟨11, 37, 11⟩, ⟨11, 71, 1⟩}
  | 19, 1 => {⟨2, 119, 2⟩}
  | 20, 0 => {⟨2, 35, 33⟩, ⟨2, 53, 14⟩, ⟨2, 71, 8⟩, ⟨2, 89, 5⟩, ⟨2, 107, 3⟩, ⟨2, 125, 2⟩, ⟨2, 143, 2⟩, ⟨2, 161, 1⟩, ⟨2, 179, 1⟩, ⟨2, 197, 1⟩, ⟨3, 35, 11⟩, ⟨3, 59, 3⟩, ⟨3, 83, 2⟩, ⟨3, 107, 1⟩, ⟨5, 35, 4⟩, ⟨5, 63, 1⟩, ⟨7, 35, 1⟩, ⟨11, 35, 12⟩, ⟨11, 67, 1⟩}
  | 20, 1 => {⟨2, 118, 3⟩, ⟨3, 118, 1⟩}
  | 21, 0 => {⟨2, 34, 35⟩, ⟨2, 51, 15⟩, ⟨2, 68, 8⟩, ⟨2, 85, 5⟩, ⟨2, 102, 4⟩, ⟨2, 119, 2⟩, ⟨2, 136, 2⟩, ⟨2, 153, 1⟩, ⟨2, 170, 1⟩, ⟨2, 187, 1⟩, ⟨2, 204, 1⟩, ⟨3, 34, 11⟩, ⟨3, 57, 4⟩, ⟨3, 80, 2⟩, ⟨3, 103, 1⟩, ⟨5, 34, 4⟩, ⟨5, 62, 1⟩, ⟨7, 34, 2⟩, ⟨11, 34, 14⟩, ⟨11, 65, 1⟩}
  | 21, 1 => {⟨2, 118, 3⟩, ⟨3, 118, 1⟩}
  | 22, 0 => {⟨2, 33, 37⟩, ⟨2, 50, 16⟩, ⟨2, 67, 9⟩, ⟨2, 84, 5⟩, ⟨2, 101, 4⟩, ⟨2, 118, 3⟩, ⟨2, 135, 2⟩, ⟨2, 152, 1⟩, ⟨2, 169, 1⟩, ⟨2, 186, 1⟩, ⟨2, 203, 1⟩, ⟨3, 33, 12⟩, ⟨3, 55, 4⟩, ⟨3, 77, 2⟩, ⟨3, 99, 1⟩, ⟨5, 33, 4⟩, ⟨5, 60, 1⟩, ⟨7, 33, 2⟩, ⟨11, 33, 13⟩, ⟨11, 63, 2⟩}
  | 22, 1 => {⟨2, 117, 3⟩, ⟨3, 117, 1⟩}
  | 23, 0 => {⟨2, 32, 39⟩, ⟨2, 48, 17⟩, ⟨2, 64, 10⟩, ⟨2, 80, 6⟩, ⟨2, 96, 4⟩, ⟨2, 112, 3⟩, ⟨2, 128, 2⟩, ⟨2, 144, 2⟩, ⟨2, 160, 1⟩, ⟨2, 176, 1⟩, ⟨2, 192, 1⟩, ⟨3, 32, 13⟩, ⟨3, 54, 4⟩, ⟨3, 76, 2⟩, ⟨3, 98, 1⟩, ⟨5, 32, 4⟩, ⟨5, 58, 1⟩, ⟨7, 32, 2⟩, ⟨11, 32, 15⟩, ⟨11, 62, 2⟩}
  | 23, 1 => {⟨2, 117, 3⟩, ⟨3, 117, 1⟩}
  | 24, 0 => {⟨2, 84, 5⟩, ⟨2, 164, 1⟩, ⟨3, 84, 1⟩, ⟨11, 84, 1⟩}
  | 25, 0 => {⟨2, 81, 6⟩, ⟨2, 155, 1⟩, ⟨3, 81, 2⟩, ⟨11, 81, 1⟩}
  | 26, 0 => {⟨2, 78, 6⟩, ⟨2, 146, 1⟩, ⟨3, 78, 2⟩, ⟨11, 78, 1⟩}
  | 27, 0 => {⟨2, 74, 7⟩, ⟨2, 134, 2⟩, ⟨2, 194, 1⟩, ⟨3, 74, 2⟩, ⟨11, 74, 1⟩}
  | 28, 0 => {⟨2, 70, 8⟩, ⟨2, 122, 2⟩, ⟨2, 174, 1⟩, ⟨3, 70, 2⟩, ⟨11, 70, 1⟩}
  | 29, 0 => {⟨2, 63, 10⟩, ⟨2, 101, 4⟩, ⟨2, 139, 2⟩, ⟨2, 177, 1⟩, ⟨3, 63, 3⟩, ⟨3, 114, 1⟩, ⟨5, 63, 1⟩, ⟨11, 63, 2⟩}
  | 30, 0 => {⟨2, 53, 14⟩, ⟨2, 80, 6⟩, ⟨2, 107, 3⟩, ⟨2, 134, 2⟩, ⟨2, 161, 1⟩, ⟨2, 188, 1⟩, ⟨3, 53, 4⟩, ⟨3, 89, 1⟩, ⟨5, 53, 1⟩, ⟨11, 53, 3⟩}
  | 30, 1 => {⟨2, 150, 1⟩}
  | 31, 0 => {⟨2, 51, 15⟩, ⟨2, 77, 7⟩, ⟨2, 103, 3⟩, ⟨2, 129, 2⟩, ⟨2, 155, 1⟩, ⟨2, 181, 1⟩, ⟨3, 51, 5⟩, ⟨3, 85, 1⟩, ⟨5, 51, 2⟩, ⟨11, 51, 4⟩}
  | 31, 1 => {⟨2, 125, 2⟩}
  | 32, 0 => {⟨2, 49, 17⟩, ⟨2, 74, 7⟩, ⟨2, 99, 4⟩, ⟨2, 124, 2⟩, ⟨2, 149, 1⟩, ⟨2, 174, 1⟩, ⟨2, 199, 1⟩, ⟨3, 49, 5⟩, ⟨3, 82, 2⟩, ⟨3, 115, 1⟩, ⟨5, 49, 2⟩, ⟨11, 49, 4⟩}
  | 32, 1 => {⟨2, 124, 2⟩}
  | 33, 0 => {⟨2, 47, 18⟩, ⟨2, 71, 8⟩, ⟨2, 95, 4⟩, ⟨2, 119, 2⟩, ⟨2, 143, 2⟩, ⟨2, 167, 1⟩, ⟨2, 191, 1⟩, ⟨3, 47, 6⟩, ⟨3, 79, 2⟩, ⟨3, 111, 1⟩, ⟨5, 47, 2⟩, ⟨11, 47, 5⟩, ⟨11, 90, 1⟩}
  | 33, 1 => {⟨2, 148, 1⟩}
  | 34, 0 => {⟨2, 45, 20⟩, ⟨2, 68, 8⟩, ⟨2, 91, 5⟩, ⟨2, 114, 3⟩, ⟨2, 137, 2⟩, ⟨2, 160, 1⟩, ⟨2, 183, 1⟩, ⟨3, 45, 6⟩, ⟨3, 75, 2⟩, ⟨3, 105, 1⟩, ⟨5, 45, 2⟩, ⟨11, 45, 6⟩, ⟨11, 86, 1⟩}
  | 34, 1 => {⟨2, 123, 2⟩}
  | 35, 0 => {⟨2, 43, 22⟩, ⟨2, 65, 9⟩, ⟨2, 87, 5⟩, ⟨2, 109, 3⟩, ⟨2, 131, 2⟩, ⟨2, 153, 1⟩, ⟨2, 175, 1⟩, ⟨2, 197, 1⟩, ⟨3, 43, 7⟩, ⟨3, 72, 2⟩, ⟨3, 101, 1⟩, ⟨5, 43, 2⟩, ⟨7, 43, 1⟩, ⟨11, 43, 6⟩, ⟨11, 83, 1⟩}
  | 35, 1 => {⟨2, 122, 2⟩}
  | 36, 0 => {⟨2, 40, 25⟩, ⟨2, 60, 11⟩, ⟨2, 80, 6⟩, ⟨2, 100, 4⟩, ⟨2, 120, 2⟩, ⟨2, 140, 2⟩, ⟨2, 160, 1⟩, ⟨2, 180, 1⟩, ⟨2, 200, 1⟩, ⟨3, 40, 8⟩, ⟨3, 67, 3⟩, ⟨3, 94, 1⟩, ⟨5, 40, 3⟩, ⟨7, 40, 1⟩, ⟨11, 40, 8⟩, ⟨11, 77, 1⟩}
  | 36, 1 => {⟨2, 120, 2⟩}
  | 37, 0 => {⟨2, 38, 28⟩, ⟨2, 57, 12⟩, ⟨2, 76, 7⟩, ⟨2, 95, 4⟩, ⟨2, 114, 3⟩, ⟨2, 133, 2⟩, ⟨2, 152, 1⟩, ⟨2, 171, 1⟩, ⟨2, 190, 1⟩, ⟨3, 38, 9⟩, ⟨3, 64, 3⟩, ⟨3, 90, 1⟩, ⟨3, 116, 1⟩, ⟨5, 38, 3⟩, ⟨7, 38, 1⟩, ⟨11, 38, 9⟩, ⟨11, 73, 1⟩}
  | 37, 1 => {⟨2, 120, 2⟩}
  | 38, 0 => {⟨2, 35, 33⟩, ⟨2, 53, 14⟩, ⟨2, 71, 8⟩, ⟨2, 89, 5⟩, ⟨2, 107, 3⟩, ⟨2, 125, 2⟩, ⟨2, 143, 2⟩, ⟨2, 161, 1⟩, ⟨2, 179, 1⟩, ⟨2, 197, 1⟩, ⟨3, 35, 11⟩, ⟨3, 59, 3⟩, ⟨3, 83, 2⟩, ⟨3, 107, 1⟩, ⟨5, 35, 4⟩, ⟨5, 63, 1⟩, ⟨7, 35, 1⟩, ⟨11, 35, 12⟩, ⟨11, 67, 1⟩}
  | 38, 1 => {⟨2, 119, 2⟩}
  | 39, 0 => {⟨2, 33, 37⟩, ⟨2, 50, 16⟩, ⟨2, 67, 9⟩, ⟨2, 84, 5⟩, ⟨2, 101, 4⟩, ⟨2, 118, 3⟩, ⟨2, 135, 2⟩, ⟨2, 152, 1⟩, ⟨2, 169, 1⟩, ⟨2, 186, 1⟩, ⟨2, 203, 1⟩, ⟨3, 33, 12⟩, ⟨3, 55, 4⟩, ⟨3, 77, 2⟩, ⟨3, 99, 1⟩, ⟨5, 33, 4⟩, ⟨5, 60, 1⟩, ⟨7, 33, 2⟩, ⟨11, 33, 13⟩, ⟨11, 63, 2⟩}
  | 39, 1 => {⟨2, 118, 3⟩, ⟨3, 118, 1⟩}
  | 40, 0 => {⟨2, 126, 2⟩}
  | 41, 0 => {⟨2, 111, 3⟩, ⟨2, 204, 1⟩, ⟨3, 111, 1⟩}
  | 42, 0 => {⟨2, 96, 4⟩, ⟨2, 159, 1⟩, ⟨3, 96, 1⟩}
  | _, _ => ∅

def slope : ℕ → ℕ
  | 0 => 704
  | 1 => 704
  | 2 => 880
  | 3 => 880
  | 4 => 880
  | 5 => 1144
  | 6 => 1232
  | 7 => 1232
  | 8 => 1584
  | 9 => 2112
  | 10 => 3322
  | 11 => 3872
  | 12 => 4290
  | 13 => 4928
  | 14 => 5368
  | 15 => 5896
  | 16 => 6160
  | 17 => 7128
  | 18 => 7568
  | 19 => 8536
  | 20 => 9856
  | 21 => 10648
  | 22 => 11176
  | 23 => 11968
  | 24 => 712
  | 25 => 890
  | 26 => 890
  | 27 => 1157
  | 28 => 1246
  | 29 => 2136
  | 30 => 3359
  | 31 => 3915
  | 32 => 4449
  | 33 => 4872
  | 34 => 5428
  | 35 => 5962
  | 36 => 7208
  | 37 => 8009
  | 38 => 9700
  | 39 => 11301
  | 40 => 260
  | 41 => 650
  | 42 => 780
  | _ => 0

def FiniteFacts (k : ℕ) (hk : k < 43) : Prop :=
  (∀ b : CrossBandCredit208.Band,
    BandFacts (row k).high (data k).steps (At (row k) (length hk) b) (terms k b) ∧
      ∀ t ∈ terms k b, (t.p,(row k).low/(t.q*(t.q+1)),t.count) ∈ Required) ∧
    RowSlope (row k) (length hk) (terms k) = slope k

local instance (k : ℕ) (hk : k < 43) : Decidable (FiniteFacts k hk) :=
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

theorem facts {k : ℕ} (hk : k < 43) : FiniteFacts k hk := by
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

theorem slope_bound {k N : ℕ} (hk : k < 43)
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
end JSP233.RowLightSlope84364
