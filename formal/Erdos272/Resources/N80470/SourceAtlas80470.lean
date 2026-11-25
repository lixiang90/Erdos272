module

public import Erdos272.Resources.N80470.SourceEntries80470G0
public import Erdos272.Resources.N80470.SourceEntries80470G1

@[expose] public section

namespace JSP233.SourceAtlas80470
open StarCompletion SourceBridge208 IntrinsicTriples208 SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def demand (i : ℕ) : Contract := (([⟨86,1,2186⟩, ⟨86,18,24246⟩, ⟨284,1,24246⟩, ⟨86,41,38220⟩, ⟨150,7,38220⟩, ⟨356,1,38220⟩, ⟨86,49,48000⟩, ⟨150,9,48000⟩, ⟨399,1,48000⟩, ⟨86,55,55942⟩, ⟨150,10,55942⟩, ⟨431,1,55942⟩, ⟨86,54,54522⟩, ⟨150,10,54522⟩, ⟨425,1,54522⟩, ⟨87,1,2240⟩, ⟨87,4,7988⟩, ⟨163,1,7988⟩, ⟨87,8,14360⟩, ⟨219,1,14360⟩, ⟨87,13,20878⟩, ⟨263,1,20878⟩, ⟨87,19,25593⟩, ⟨292,1,25593⟩, ⟨87,24,27612⟩, ⟨303,1,27612⟩, ⟨87,38,34966⟩, ⟨174,5,34966⟩, ⟨341,1,34966⟩, ⟨87,42,40290⟩, ⟨152,7,40290⟩, ⟨366,1,40290⟩, ⟨87,45,44128⟩, ⟨152,8,44128⟩, ⟨383,1,44128⟩, ⟨87,48,47882⟩, ⟨152,8,47882⟩, ⟨398,1,47882⟩, ⟨87,50,50284⟩, ⟨152,9,50284⟩, ⟨409,1,50284⟩, ⟨87,52,52528⟩, ⟨152,9,52528⟩, ⟨417,1,52528⟩, ⟨87,54,55262⟩, ⟨152,10,55262⟩, ⟨428,1,55262⟩] : List Contract)[i]?).getD ⟨0,0,0⟩

def sourceReference (i : ℕ) : CertifiedContract := (([
  SourceEntries80470G0.entry000,
  SourceEntries80470G0.entry001,
  SourceEntries80470G0.entry002,
  SourceEntries80470G0.entry003,
  SourceEntries80470G0.entry004,
  SourceEntries80470G0.entry005,
  SourceEntries80470G0.entry006,
  SourceEntries80470G0.entry007,
  SourceEntries80470G0.entry008,
  SourceEntries80470G0.entry009,
  SourceEntries80470G0.entry010,
  SourceEntries80470G0.entry011,
  SourceEntries80470G0.entry012,
  SourceEntries80470G0.entry013,
  SourceEntries80470G0.entry014,
  SourceEntries80470G0.entry015,
  SourceEntries80470G0.entry016,
  SourceEntries80470G0.entry017,
  SourceEntries80470G0.entry018,
  SourceEntries80470G0.entry019,
  SourceEntries80470G0.entry020,
  SourceEntries80470G0.entry021,
  SourceEntries80470G0.entry022,
  SourceEntries80470G0.entry023,
  SourceEntries80470G0.entry024,
  SourceEntries80470G0.entry025,
  SourceEntries80470G0.entry026,
  SourceEntries80470G0.entry027,
  SourceEntries80470G0.entry028,
  SourceEntries80470G0.entry029,
  SourceEntries80470G0.entry030,
  SourceEntries80470G0.entry031,
  SourceEntries80470G1.entry032,
  SourceEntries80470G1.entry033,
  SourceEntries80470G1.entry034,
  SourceEntries80470G1.entry035,
  SourceEntries80470G1.entry036,
  SourceEntries80470G1.entry037,
  SourceEntries80470G1.entry038,
  SourceEntries80470G1.entry039,
  SourceEntries80470G1.entry040,
  SourceEntries80470G1.entry041,
  SourceEntries80470G1.entry042,
  SourceEntries80470G1.entry043,
  SourceEntries80470G1.entry044,
  SourceEntries80470G1.entry045,
  SourceEntries80470G1.entry046
] : List CertifiedContract)[i]?).getD (SourceNodes80470G0.node000)

theorem reference_piece0 {i : ℕ} (hlo : 0 ≤ i) (hhi : i < 16) :
    (sourceReference i).contract=demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece0

theorem reference_piece1 {i : ℕ} (hlo : 16 ≤ i) (hhi : i < 32) :
    (sourceReference i).contract=demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece1

theorem reference_piece2 {i : ℕ} (hlo : 32 ≤ i) (hhi : i < 47) :
    (sourceReference i).contract=demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece2

theorem reference_eq {i : ℕ} (hi : i < 47) : (sourceReference i).contract=demand i := by
  by_cases h0 : i < 16
  · exact reference_piece0 (by omega) h0
  by_cases h1 : i < 32
  · exact reference_piece1 (by omega) h1
  exact reference_piece2 (by omega) hi
#print axioms reference_eq

theorem actual_source {N i : ℕ} {S : Finset ℤ} (hi : i < 47)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (demand i).lower ≤ S.card) (hdefect : (demand i).defect ≤ Defect S) :
    (demand i).target ≤ (Pool S).card := by
  have hp : Paid (demand i) := by
    rw [← reference_eq hi]
    exact (sourceReference i).actual
  exact hp hN hground hS hsize hdefect
#print axioms actual_source
end
end JSP233.SourceAtlas80470
