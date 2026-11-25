module

public import Erdos272.Resources.N86412.SourceEntries86412G0
public import Erdos272.Resources.N86412.SourceEntries86412G1
public import Erdos272.Resources.N86412.SourceEntries86412G2
public import Erdos272.Resources.N86412.SourceEntries86412G3
public import Erdos272.Resources.N86412.SourceEntries86412G4

@[expose] public section

namespace JSP233.SourceAtlas86412
open StarCompletion SourceBridge208 IntrinsicTriples208 SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def demand (i : ℕ) : Contract := (([⟨89,1,2366⟩, ⟨89,2,4392⟩, ⟨122,1,4392⟩, ⟨89,3,6465⟩, ⟨148,1,6465⟩, ⟨89,4,8368⟩, ⟨167,1,8368⟩, ⟨89,5,10450⟩, ⟨178,2,10450⟩, ⟨187,1,10450⟩, ⟨89,7,13657⟩, ⟨178,2,13657⟩, ⟨214,1,13657⟩, ⟨89,9,16857⟩, ⟨178,2,16857⟩, ⟨237,1,16857⟩, ⟨89,11,19591⟩, ⟨178,3,19591⟩, ⟨256,1,19591⟩, ⟨89,13,21762⟩, ⟨178,3,21762⟩, ⟨269,1,21762⟩, ⟨89,15,24045⟩, ⟨178,3,24045⟩, ⟨283,1,24045⟩, ⟨89,17,25823⟩, ⟨178,3,25823⟩, ⟨293,1,25823⟩, ⟨89,19,27113⟩, ⟨178,4,27113⟩, ⟨301,1,27113⟩, ⟨89,21,28094⟩, ⟨178,4,28094⟩, ⟨306,1,28094⟩, ⟨89,23,29112⟩, ⟨178,4,29112⟩, ⟨311,1,29112⟩, ⟨89,26,29652⟩, ⟨178,4,29652⟩, ⟨314,1,29652⟩, ⟨89,35,31074⟩, ⟨155,5,31074⟩, ⟨321,1,31074⟩, ⟨89,36,32658⟩, ⟨155,5,32658⟩, ⟨329,1,32658⟩, ⟨89,37,33842⟩, ⟨133,8,33842⟩, ⟨335,1,33842⟩, ⟨89,38,35822⟩, ⟨133,8,35822⟩, ⟨345,1,35822⟩, ⟨89,39,37130⟩, ⟨155,6,37130⟩, ⟨351,1,37130⟩, ⟨89,40,39050⟩, ⟨155,7,39050⟩, ⟨360,1,39050⟩, ⟨89,41,40362⟩, ⟨155,7,40362⟩, ⟨366,1,40362⟩, ⟨89,42,41660⟩, ⟨155,7,41660⟩, ⟨372,1,41660⟩, ⟨89,43,43164⟩, ⟨155,7,43164⟩, ⟨379,1,43164⟩, ⟨89,44,44088⟩, ⟨155,7,44088⟩, ⟨383,1,44088⟩, ⟨89,45,45100⟩, ⟨155,8,45100⟩, ⟨387,1,45100⟩, ⟨89,46,47172⟩, ⟨155,8,47172⟩, ⟨395,1,47172⟩, ⟨89,47,48308⟩, ⟨155,8,48308⟩, ⟨401,1,48308⟩, ⟨89,48,49320⟩, ⟨155,8,49320⟩, ⟨404,1,49320⟩, ⟨89,49,51138⟩, ⟨155,9,51138⟩, ⟨412,1,51138⟩, ⟨89,50,51908⟩, ⟨155,9,51908⟩, ⟨415,1,51908⟩, ⟨89,51,53672⟩, ⟨155,9,53672⟩, ⟨422,1,53672⟩, ⟨89,52,54464⟩, ⟨155,9,54464⟩, ⟨425,1,54464⟩, ⟨89,53,56094⟩, ⟨155,9,56094⟩, ⟨431,1,56094⟩, ⟨89,54,57574⟩, ⟨155,10,57574⟩, ⟨437,1,57574⟩, ⟨89,55,58758⟩, ⟨155,10,58758⟩, ⟨441,1,58758⟩, ⟨89,56,60564⟩, ⟨133,15,60564⟩, ⟨356,2,60564⟩, ⟨448,1,60564⟩, ⟨90,1,2390⟩, ⟨90,4,8620⟩, ⟨170,1,8620⟩, ⟨90,10,18730⟩, ⟨180,3,18730⟩, ⟨250,1,18730⟩, ⟨90,16,25648⟩, ⟨180,3,25648⟩, ⟨292,1,25648⟩, ⟨90,24,30325⟩, ⟨180,4,30325⟩, ⟨317,1,30325⟩, ⟨90,37,34606⟩, ⟨157,6,34606⟩, ⟨339,1,34606⟩, ⟨90,41,41164⟩, ⟨157,7,41164⟩, ⟨370,1,41164⟩, ⟨90,44,44770⟩, ⟨157,7,44770⟩, ⟨388,1,44770⟩, ⟨90,47,49168⟩, ⟨157,8,49168⟩, ⟨405,1,49168⟩, ⟨90,49,51738⟩, ⟨157,9,51738⟩, ⟨415,1,51738⟩, ⟨90,51,54238⟩, ⟨157,9,54238⟩, ⟨425,1,54238⟩, ⟨90,53,57032⟩, ⟨157,9,57032⟩, ⟨436,1,57032⟩, ⟨90,55,60062⟩, ⟨157,10,60062⟩, ⟨447,1,60062⟩, ⟨130,1,5024⟩, ⟨130,4,18736⟩, ⟨250,1,18736⟩, ⟨130,19,68381⟩, ⟨260,4,68381⟩, ⟨476,1,68381⟩, ⟨130,34,91188⟩, ⟨260,6,91188⟩, ⟨549,1,91188⟩] : List Contract)[i]?).getD ⟨0,0,0⟩

def sourceReference (i : ℕ) : CertifiedContract := (([
  SourceEntries86412G0.entry000,
  SourceEntries86412G0.entry001,
  SourceEntries86412G0.entry002,
  SourceEntries86412G0.entry003,
  SourceEntries86412G0.entry004,
  SourceEntries86412G0.entry005,
  SourceEntries86412G0.entry006,
  SourceEntries86412G0.entry007,
  SourceEntries86412G0.entry008,
  SourceEntries86412G0.entry009,
  SourceEntries86412G0.entry010,
  SourceEntries86412G0.entry011,
  SourceEntries86412G0.entry012,
  SourceEntries86412G0.entry013,
  SourceEntries86412G0.entry014,
  SourceEntries86412G0.entry015,
  SourceEntries86412G0.entry016,
  SourceEntries86412G0.entry017,
  SourceEntries86412G0.entry018,
  SourceEntries86412G0.entry019,
  SourceEntries86412G0.entry020,
  SourceEntries86412G0.entry021,
  SourceEntries86412G0.entry022,
  SourceEntries86412G0.entry023,
  SourceEntries86412G0.entry024,
  SourceEntries86412G0.entry025,
  SourceEntries86412G0.entry026,
  SourceEntries86412G0.entry027,
  SourceEntries86412G0.entry028,
  SourceEntries86412G0.entry029,
  SourceEntries86412G0.entry030,
  SourceEntries86412G0.entry031,
  SourceEntries86412G1.entry032,
  SourceEntries86412G1.entry033,
  SourceEntries86412G1.entry034,
  SourceEntries86412G1.entry035,
  SourceEntries86412G1.entry036,
  SourceEntries86412G1.entry037,
  SourceEntries86412G1.entry038,
  SourceEntries86412G1.entry039,
  SourceEntries86412G1.entry040,
  SourceEntries86412G1.entry041,
  SourceEntries86412G1.entry042,
  SourceEntries86412G1.entry043,
  SourceEntries86412G1.entry044,
  SourceEntries86412G1.entry045,
  SourceEntries86412G1.entry046,
  SourceEntries86412G1.entry047,
  SourceEntries86412G1.entry048,
  SourceEntries86412G1.entry049,
  SourceEntries86412G1.entry050,
  SourceEntries86412G1.entry051,
  SourceEntries86412G1.entry052,
  SourceEntries86412G1.entry053,
  SourceEntries86412G1.entry054,
  SourceEntries86412G1.entry055,
  SourceEntries86412G1.entry056,
  SourceEntries86412G1.entry057,
  SourceEntries86412G1.entry058,
  SourceEntries86412G1.entry059,
  SourceEntries86412G1.entry060,
  SourceEntries86412G1.entry061,
  SourceEntries86412G1.entry062,
  SourceEntries86412G1.entry063,
  SourceEntries86412G2.entry064,
  SourceEntries86412G2.entry065,
  SourceEntries86412G2.entry066,
  SourceEntries86412G2.entry067,
  SourceEntries86412G2.entry068,
  SourceEntries86412G2.entry069,
  SourceEntries86412G2.entry070,
  SourceEntries86412G2.entry071,
  SourceEntries86412G2.entry072,
  SourceEntries86412G2.entry073,
  SourceEntries86412G2.entry074,
  SourceEntries86412G2.entry075,
  SourceEntries86412G2.entry076,
  SourceEntries86412G2.entry077,
  SourceEntries86412G2.entry078,
  SourceEntries86412G2.entry079,
  SourceEntries86412G2.entry080,
  SourceEntries86412G2.entry081,
  SourceEntries86412G2.entry082,
  SourceEntries86412G2.entry083,
  SourceEntries86412G2.entry084,
  SourceEntries86412G2.entry085,
  SourceEntries86412G2.entry086,
  SourceEntries86412G2.entry087,
  SourceEntries86412G2.entry088,
  SourceEntries86412G2.entry089,
  SourceEntries86412G2.entry090,
  SourceEntries86412G2.entry091,
  SourceEntries86412G2.entry092,
  SourceEntries86412G2.entry093,
  SourceEntries86412G2.entry094,
  SourceEntries86412G2.entry095,
  SourceEntries86412G3.entry096,
  SourceEntries86412G3.entry097,
  SourceEntries86412G3.entry098,
  SourceEntries86412G3.entry099,
  SourceEntries86412G3.entry100,
  SourceEntries86412G3.entry101,
  SourceEntries86412G3.entry102,
  SourceEntries86412G3.entry103,
  SourceEntries86412G3.entry104,
  SourceEntries86412G3.entry105,
  SourceEntries86412G3.entry106,
  SourceEntries86412G3.entry107,
  SourceEntries86412G3.entry108,
  SourceEntries86412G3.entry109,
  SourceEntries86412G3.entry110,
  SourceEntries86412G3.entry111,
  SourceEntries86412G3.entry112,
  SourceEntries86412G3.entry113,
  SourceEntries86412G3.entry114,
  SourceEntries86412G3.entry115,
  SourceEntries86412G3.entry116,
  SourceEntries86412G3.entry117,
  SourceEntries86412G3.entry118,
  SourceEntries86412G3.entry119,
  SourceEntries86412G3.entry120,
  SourceEntries86412G3.entry121,
  SourceEntries86412G3.entry122,
  SourceEntries86412G3.entry123,
  SourceEntries86412G3.entry124,
  SourceEntries86412G3.entry125,
  SourceEntries86412G3.entry126,
  SourceEntries86412G3.entry127,
  SourceEntries86412G4.entry128,
  SourceEntries86412G4.entry129,
  SourceEntries86412G4.entry130,
  SourceEntries86412G4.entry131,
  SourceEntries86412G4.entry132,
  SourceEntries86412G4.entry133,
  SourceEntries86412G4.entry134,
  SourceEntries86412G4.entry135,
  SourceEntries86412G4.entry136,
  SourceEntries86412G4.entry137,
  SourceEntries86412G4.entry138,
  SourceEntries86412G4.entry139,
  SourceEntries86412G4.entry140,
  SourceEntries86412G4.entry141,
  SourceEntries86412G4.entry142,
  SourceEntries86412G4.entry143,
  SourceEntries86412G4.entry144,
  SourceEntries86412G4.entry145,
  SourceEntries86412G4.entry146,
  SourceEntries86412G4.entry147,
  SourceEntries86412G4.entry148,
  SourceEntries86412G4.entry149,
  SourceEntries86412G4.entry150,
  SourceEntries86412G4.entry151
] : List CertifiedContract)[i]?).getD (SourceOld86412.old 0)

theorem reference_piece0 {i : ℕ} (hlo : 0 ≤ i) (hhi : i < 16) :
    (sourceReference i).contract = demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece0

theorem reference_piece1 {i : ℕ} (hlo : 16 ≤ i) (hhi : i < 32) :
    (sourceReference i).contract = demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece1

theorem reference_piece2 {i : ℕ} (hlo : 32 ≤ i) (hhi : i < 48) :
    (sourceReference i).contract = demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece2

theorem reference_piece3 {i : ℕ} (hlo : 48 ≤ i) (hhi : i < 64) :
    (sourceReference i).contract = demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece3

theorem reference_piece4 {i : ℕ} (hlo : 64 ≤ i) (hhi : i < 80) :
    (sourceReference i).contract = demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece4

theorem reference_piece5 {i : ℕ} (hlo : 80 ≤ i) (hhi : i < 96) :
    (sourceReference i).contract = demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece5

theorem reference_piece6 {i : ℕ} (hlo : 96 ≤ i) (hhi : i < 112) :
    (sourceReference i).contract = demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece6

theorem reference_piece7 {i : ℕ} (hlo : 112 ≤ i) (hhi : i < 128) :
    (sourceReference i).contract = demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece7

theorem reference_piece8 {i : ℕ} (hlo : 128 ≤ i) (hhi : i < 144) :
    (sourceReference i).contract = demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece8

theorem reference_piece9 {i : ℕ} (hlo : 144 ≤ i) (hhi : i < 152) :
    (sourceReference i).contract = demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece9

theorem reference_eq {i : ℕ} (hi : i < 152) :
    (sourceReference i).contract = demand i := by
  by_cases h0 : i < 16
  · exact reference_piece0 (by omega) h0
  by_cases h1 : i < 32
  · exact reference_piece1 (by omega) h1
  by_cases h2 : i < 48
  · exact reference_piece2 (by omega) h2
  by_cases h3 : i < 64
  · exact reference_piece3 (by omega) h3
  by_cases h4 : i < 80
  · exact reference_piece4 (by omega) h4
  by_cases h5 : i < 96
  · exact reference_piece5 (by omega) h5
  by_cases h6 : i < 112
  · exact reference_piece6 (by omega) h6
  by_cases h7 : i < 128
  · exact reference_piece7 (by omega) h7
  by_cases h8 : i < 144
  · exact reference_piece8 (by omega) h8
  exact reference_piece9 (by omega) hi

theorem actual_source {N i : ℕ} {S : Finset ℤ} (hi : i < 152)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (demand i).lower ≤ S.card) (hdefect : (demand i).defect ≤ Defect S) :
    (demand i).target ≤ (Pool S).card := by
  have hp : Paid (demand i) := by
    rw [← reference_eq hi]
    exact (sourceReference i).actual
  exact hp hN hground hS hsize hdefect

#print axioms reference_eq
#print axioms actual_source
end
end JSP233.SourceAtlas86412
