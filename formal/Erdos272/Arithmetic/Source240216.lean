import Erdos272.Resources.SourceCertified208
import Erdos272.Resources.UnitNearAggregate208
import Erdos272.Arithmetic.SourceLookupFast208

namespace JSP233.Source240216
open SourceCertified208 UnitNearAggregate208 FastSource208 PureSource208
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def Heights240 : List ℕ := [0, 1, 2, 3, 4, 5, 7, 7, 8, 9, 11, 11, 12, 13, 14, 15, 17, 17, 18, 19, 21, 22, 23, 23, 25, 25, 27, 28, 29, 29, 31, 31, 32, 34, 35, 36, 37, 38, 39, 40, 41, 41, 43, 43, 44, 46, 47, 47, 49, 49, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 61, 62, 64, 65, 66, 67, 68, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 89, 89, 90, 91, 92, 93, 94, 95, 97, 97, 98, 99, 101, 101, 103, 103, 104, 105, 107, 107, 109, 109, 111, 111, 113, 113, 114, 115, 117, 117, 119, 119, 121, 121, 123, 123, 125, 125, 127, 127, 129, 129, 131, 131, 133, 133, 134, 135, 137, 137, 138, 139, 140, 141, 143, 143, 145, 145, 147, 147, 149, 149, 151, 151]

def Heights241 : List ℕ := [0, 2, 2, 3, 4, 5, 6, 8, 8, 9, 10, 12, 12, 13, 14, 15, 16, 18, 18, 19, 20, 22, 22, 24, 24, 26, 26, 28, 28, 30, 30, 32, 32, 34, 35, 36, 36, 38, 38, 40, 41, 42, 42, 44, 44, 45, 47, 48, 48, 50, 50, 52, 53, 54, 54, 56, 56, 58, 59, 60, 60, 62, 62, 63, 65, 66, 67, 68, 68, 69, 71, 72, 72, 74, 74, 76, 77, 78, 78, 80, 80, 82, 83, 84, 84, 86, 87, 88, 89, 90, 90, 92, 92, 94, 95, 96, 97, 98, 98, 100, 101, 102, 102, 104, 104, 106, 107, 108, 109, 110, 110, 112, 113, 114, 114, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 128, 130, 131, 132, 132, 134, 134, 136, 137, 138, 138, 140, 140, 142, 143, 144, 144, 146, 147, 148, 149, 150, 151]

def eAt (s i : ℕ) : ℕ :=
  ((if s=240 then Heights240 else Heights241)[i]?).getD 0
def Check (s : ℕ) : Bool := (List.range 151).all fun i =>
  decide (floorAt row242 i ≤ fastPhysicalK SourceLookupData208.phi s (eAt s i))

private theorem all151_of_blocks (p : ℕ → Bool)
    (h0 : (List.range' 0 16).all p = true)
    (h1 : (List.range' 16 16).all p = true)
    (h2 : (List.range' 32 16).all p = true)
    (h3 : (List.range' 48 16).all p = true)
    (h4 : (List.range' 64 16).all p = true)
    (h5 : (List.range' 80 16).all p = true)
    (h6 : (List.range' 96 16).all p = true)
    (h7 : (List.range' 112 16).all p = true)
    (h8 : (List.range' 128 16).all p = true)
    (h9 : (List.range' 144 7).all p = true)
    : (List.range 151).all p = true := by
  have hs : List.range 151 = (List.range' 0 16) ++ (List.range' 16 16) ++ (List.range' 32 16) ++ (List.range' 48 16) ++ (List.range' 64 16) ++ (List.range' 80 16) ++ (List.range' 96 16) ++ (List.range' 112 16) ++ (List.range' 128 16) ++ (List.range' 144 7) := by decide +kernel
  rw [hs]
  simpa only [List.all_append, Bool.and_eq_true_iff, and_assoc] using (And.intro h0 (And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 (And.intro h5 (And.intro h6 (And.intro h7 (And.intro h8 h9)))))))))

private theorem check240_00 :
    (List.range' 0 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 240 (eAt 240 i))) = true := by
  decide +kernel

private theorem check240_01 :
    (List.range' 16 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 240 (eAt 240 i))) = true := by
  decide +kernel

private theorem check240_02 :
    (List.range' 32 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 240 (eAt 240 i))) = true := by
  decide +kernel

private theorem check240_03 :
    (List.range' 48 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 240 (eAt 240 i))) = true := by
  decide +kernel

private theorem check240_04 :
    (List.range' 64 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 240 (eAt 240 i))) = true := by
  decide +kernel

private theorem check240_05 :
    (List.range' 80 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 240 (eAt 240 i))) = true := by
  decide +kernel

private theorem check240_06 :
    (List.range' 96 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 240 (eAt 240 i))) = true := by
  decide +kernel

private theorem check240_07 :
    (List.range' 112 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 240 (eAt 240 i))) = true := by
  decide +kernel

private theorem check240_08 :
    (List.range' 128 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 240 (eAt 240 i))) = true := by
  decide +kernel

private theorem check240_09 :
    (List.range' 144 7).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 240 (eAt 240 i))) = true := by
  decide +kernel

private theorem check241_00 :
    (List.range' 0 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 241 (eAt 241 i))) = true := by
  decide +kernel

private theorem check241_01 :
    (List.range' 16 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 241 (eAt 241 i))) = true := by
  decide +kernel

private theorem check241_02 :
    (List.range' 32 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 241 (eAt 241 i))) = true := by
  decide +kernel

private theorem check241_03 :
    (List.range' 48 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 241 (eAt 241 i))) = true := by
  decide +kernel

private theorem check241_04 :
    (List.range' 64 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 241 (eAt 241 i))) = true := by
  decide +kernel

private theorem check241_05 :
    (List.range' 80 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 241 (eAt 241 i))) = true := by
  decide +kernel

private theorem check241_06 :
    (List.range' 96 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 241 (eAt 241 i))) = true := by
  decide +kernel

private theorem check241_07 :
    (List.range' 112 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 241 (eAt 241 i))) = true := by
  decide +kernel

private theorem check241_08 :
    (List.range' 128 16).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 241 (eAt 241 i))) = true := by
  decide +kernel

private theorem check241_09 :
    (List.range' 144 7).all (fun i => decide (floorAt row242 i ≤
      fastPhysicalK SourceLookupData208.phi 241 (eAt 241 i))) = true := by
  decide +kernel

theorem check240 : Check 240 = true :=
  all151_of_blocks _ check240_00 check240_01 check240_02 check240_03 check240_04 check240_05 check240_06 check240_07 check240_08 check240_09
theorem check241 : Check 241 = true :=
  all151_of_blocks _ check241_00 check241_01 check241_02 check241_03 check241_04 check241_05 check241_06 check241_07 check241_08 check241_09

theorem physical_bound (s : ℕ) (hs : s=240 ∨ s=241) (i : ℕ) (hi : i≤150) :
    floorAt row242 i ≤ physicalK s (eAt s i) := by
  have hc : Check s=true := by rcases hs with rfl | rfl; exact check240; exact check241
  have hh := List.all_eq_true.mp hc i (List.mem_range.mpr (by omega : i<151))
  have hb : floorAt row242 i ≤ fastPhysicalK SourceLookupData208.phi s (eAt s i) :=
    of_decide_eq_true hh
  have he := fastPhysicalK_eq (H := SourceLookupData208.Limit)
    SourceLookupFast208.phi_correct (show s≤SourceLookupData208.Limit by rcases hs with rfl | rfl <;> decide) (eAt s i)
  rwa [he] at hb

#print axioms check240
#print axioms check241
#print axioms physical_bound
end JSP233.Source240216
