module

public import Erdos272.Resources.N82427.SourceEntries82427G0
public import Erdos272.Resources.N82427.SourceEntries82427G1
public import Erdos272.Resources.N82427.SourceEntries82427G2
public import Erdos272.Resources.N82427.SourceEntries82427G3
public import Erdos272.Resources.N82427.SourceEntries82427G4

@[expose] public section

namespace JSP233.SourceAtlas82427
open StarCompletion SourceBridge208 IntrinsicTriples208 SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def demand (i : ℕ) : Contract := (([⟨87,1,2240⟩, ⟨87,2,4198⟩, ⟨119,1,4198⟩, ⟨87,3,6291⟩, ⟨145,1,6291⟩, ⟨87,4,7988⟩, ⟨163,1,7988⟩, ⟨87,5,9790⟩, ⟨181,1,9790⟩, ⟨87,7,13160⟩, ⟨210,1,13160⟩, ⟨87,9,16092⟩, ⟨232,1,16092⟩, ⟨87,11,18491⟩, ⟨248,1,18491⟩, ⟨87,13,20878⟩, ⟨263,1,20878⟩, ⟨87,15,22830⟩, ⟨276,1,22830⟩, ⟨87,17,24310⟩, ⟨284,1,24310⟩, ⟨87,19,25593⟩, ⟨292,1,25593⟩, ⟨87,21,26752⟩, ⟨298,1,26752⟩, ⟨87,24,27612⟩, ⟨303,1,27612⟩, ⟨87,27,27744⟩, ⟨304,1,27744⟩, ⟨87,34,28906⟩, ⟨152,5,28906⟩, ⟨310,1,28906⟩, ⟨87,35,30026⟩, ⟨152,5,30026⟩, ⟨316,1,30026⟩, ⟨87,36,31910⟩, ⟨152,6,31910⟩, ⟨326,1,31910⟩, ⟨87,37,33142⟩, ⟨152,6,33142⟩, ⟨332,1,33142⟩, ⟨87,38,34966⟩, ⟨130,8,34966⟩, ⟨341,1,34966⟩, ⟨87,39,36214⟩, ⟨152,6,36214⟩, ⟨347,1,36214⟩, ⟨87,40,37654⟩, ⟨152,6,37654⟩, ⟨353,1,37654⟩, ⟨87,41,38764⟩, ⟨130,10,38764⟩, ⟨359,1,38764⟩, ⟨87,42,40290⟩, ⟨130,10,40290⟩, ⟨366,1,40290⟩, ⟨87,43,41174⟩, ⟨130,10,41174⟩, ⟨370,1,41174⟩, ⟨87,44,42210⟩, ⟨130,10,42210⟩, ⟨374,1,42210⟩, ⟨87,45,44128⟩, ⟨130,11,44128⟩, ⟨383,1,44128⟩, ⟨87,46,45310⟩, ⟨130,11,45310⟩, ⟨388,1,45310⟩, ⟨87,47,46176⟩, ⟨130,12,46176⟩, ⟨391,1,46176⟩, ⟨87,48,47882⟩, ⟨130,12,47882⟩, ⟨398,1,47882⟩, ⟨87,49,48484⟩, ⟨130,12,48484⟩, ⟨401,1,48484⟩, ⟨87,50,50284⟩, ⟨130,13,50284⟩, ⟨409,1,50284⟩, ⟨87,51,51164⟩, ⟨130,13,51164⟩, ⟨412,1,51164⟩, ⟨87,52,52528⟩, ⟨130,14,52528⟩, ⟨417,1,52528⟩, ⟨87,53,54108⟩, ⟨130,14,54108⟩, ⟨423,1,54108⟩, ⟨87,54,55262⟩, ⟨130,14,55262⟩, ⟨428,1,55262⟩, ⟨87,55,56624⟩, ⟨130,15,56624⟩, ⟨433,1,56624⟩, ⟨87,6,11424⟩, ⟨196,1,11424⟩, ⟨87,56,58282⟩, ⟨130,16,58282⟩, ⟨439,1,58282⟩, ⟨88,1,2280⟩, ⟨88,4,8388⟩, ⟨167,1,8388⟩, ⟨88,8,15040⟩, ⟨224,1,15040⟩, ⟨88,13,21385⟩, ⟨267,1,21385⟩, ⟨88,18,25740⟩, ⟨293,1,25740⟩, ⟨88,24,28416⟩, ⟨307,1,28416⟩, ⟨88,37,33842⟩, ⟨132,8,33842⟩, ⟨335,1,33842⟩, ⟨88,39,36984⟩, ⟨154,6,36984⟩, ⟨351,1,36984⟩, ⟨88,41,39616⟩, ⟨132,9,39616⟩, ⟨363,1,39616⟩, ⟨88,43,42260⟩, ⟨132,10,42260⟩, ⟨374,1,42260⟩, ⟨88,46,46400⟩, ⟨132,11,46400⟩, ⟨392,1,46400⟩, ⟨88,49,50088⟩, ⟨132,12,50088⟩, ⟨407,1,50088⟩, ⟨88,51,52556⟩, ⟨132,13,52556⟩, ⟨418,1,52556⟩, ⟨88,53,54720⟩, ⟨132,14,54720⟩, ⟨426,1,54720⟩, ⟨88,55,57994⟩, ⟨132,15,57994⟩, ⟨439,1,57994⟩] : List Contract)[i]?).getD ⟨0,0,0⟩

def sourceReference (i : ℕ) : CertifiedContract := (([
  SourceEntries82427G0.entry000,
  SourceEntries82427G0.entry001,
  SourceEntries82427G0.entry002,
  SourceEntries82427G0.entry003,
  SourceEntries82427G0.entry004,
  SourceEntries82427G0.entry005,
  SourceEntries82427G0.entry006,
  SourceEntries82427G0.entry007,
  SourceEntries82427G0.entry008,
  SourceEntries82427G0.entry009,
  SourceEntries82427G0.entry010,
  SourceEntries82427G0.entry011,
  SourceEntries82427G0.entry012,
  SourceEntries82427G0.entry013,
  SourceEntries82427G0.entry014,
  SourceEntries82427G0.entry015,
  SourceEntries82427G0.entry016,
  SourceEntries82427G0.entry017,
  SourceEntries82427G0.entry018,
  SourceEntries82427G0.entry019,
  SourceEntries82427G0.entry020,
  SourceEntries82427G0.entry021,
  SourceEntries82427G0.entry022,
  SourceEntries82427G0.entry023,
  SourceEntries82427G0.entry024,
  SourceEntries82427G0.entry025,
  SourceEntries82427G0.entry026,
  SourceEntries82427G0.entry027,
  SourceEntries82427G0.entry028,
  SourceEntries82427G0.entry029,
  SourceEntries82427G0.entry030,
  SourceEntries82427G0.entry031,
  SourceEntries82427G1.entry032,
  SourceEntries82427G1.entry033,
  SourceEntries82427G1.entry034,
  SourceEntries82427G1.entry035,
  SourceEntries82427G1.entry036,
  SourceEntries82427G1.entry037,
  SourceEntries82427G1.entry038,
  SourceEntries82427G1.entry039,
  SourceEntries82427G1.entry040,
  SourceEntries82427G1.entry041,
  SourceEntries82427G1.entry042,
  SourceEntries82427G1.entry043,
  SourceEntries82427G1.entry044,
  SourceEntries82427G1.entry045,
  SourceEntries82427G1.entry046,
  SourceEntries82427G1.entry047,
  SourceEntries82427G1.entry048,
  SourceEntries82427G1.entry049,
  SourceEntries82427G1.entry050,
  SourceEntries82427G1.entry051,
  SourceEntries82427G1.entry052,
  SourceEntries82427G1.entry053,
  SourceEntries82427G1.entry054,
  SourceEntries82427G1.entry055,
  SourceEntries82427G1.entry056,
  SourceEntries82427G1.entry057,
  SourceEntries82427G1.entry058,
  SourceEntries82427G1.entry059,
  SourceEntries82427G1.entry060,
  SourceEntries82427G1.entry061,
  SourceEntries82427G1.entry062,
  SourceEntries82427G1.entry063,
  SourceEntries82427G2.entry064,
  SourceEntries82427G2.entry065,
  SourceEntries82427G2.entry066,
  SourceEntries82427G2.entry067,
  SourceEntries82427G2.entry068,
  SourceEntries82427G2.entry069,
  SourceEntries82427G2.entry070,
  SourceEntries82427G2.entry071,
  SourceEntries82427G2.entry072,
  SourceEntries82427G2.entry073,
  SourceEntries82427G2.entry074,
  SourceEntries82427G2.entry075,
  SourceEntries82427G2.entry076,
  SourceEntries82427G2.entry077,
  SourceEntries82427G2.entry078,
  SourceEntries82427G2.entry079,
  SourceEntries82427G2.entry080,
  SourceEntries82427G2.entry081,
  SourceEntries82427G2.entry082,
  SourceEntries82427G2.entry083,
  SourceEntries82427G2.entry084,
  SourceEntries82427G2.entry085,
  SourceEntries82427G2.entry086,
  SourceEntries82427G2.entry087,
  SourceEntries82427G2.entry088,
  SourceEntries82427G2.entry089,
  SourceEntries82427G2.entry090,
  SourceEntries82427G2.entry091,
  SourceEntries82427G2.entry092,
  SourceEntries82427G2.entry093,
  SourceEntries82427G2.entry094,
  SourceEntries82427G2.entry095,
  SourceEntries82427G3.entry096,
  SourceEntries82427G3.entry097,
  SourceEntries82427G3.entry098,
  SourceEntries82427G3.entry099,
  SourceEntries82427G3.entry100,
  SourceEntries82427G3.entry101,
  SourceEntries82427G3.entry102,
  SourceEntries82427G3.entry103,
  SourceEntries82427G3.entry104,
  SourceEntries82427G3.entry105,
  SourceEntries82427G3.entry106,
  SourceEntries82427G3.entry107,
  SourceEntries82427G3.entry108,
  SourceEntries82427G3.entry109,
  SourceEntries82427G3.entry110,
  SourceEntries82427G3.entry111,
  SourceEntries82427G3.entry112,
  SourceEntries82427G3.entry113,
  SourceEntries82427G3.entry114,
  SourceEntries82427G3.entry115,
  SourceEntries82427G3.entry116,
  SourceEntries82427G3.entry117,
  SourceEntries82427G3.entry118,
  SourceEntries82427G3.entry119,
  SourceEntries82427G3.entry120,
  SourceEntries82427G3.entry121,
  SourceEntries82427G3.entry122,
  SourceEntries82427G3.entry123,
  SourceEntries82427G3.entry124,
  SourceEntries82427G3.entry125,
  SourceEntries82427G3.entry126,
  SourceEntries82427G3.entry127,
  SourceEntries82427G4.entry128,
  SourceEntries82427G4.entry129,
  SourceEntries82427G4.entry130,
  SourceEntries82427G4.entry131,
  SourceEntries82427G4.entry132,
  SourceEntries82427G4.entry133,
  SourceEntries82427G4.entry134,
  SourceEntries82427G4.entry135,
  SourceEntries82427G4.entry136,
  SourceEntries82427G4.entry137
] : List CertifiedContract)[i]?).getD (SourceNodes82427G0.node000)

theorem reference_piece0 {i : ℕ} (hlo : 0 ≤ i) (hhi : i < 16) :
    (sourceReference i).contract=demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece0

theorem reference_piece1 {i : ℕ} (hlo : 16 ≤ i) (hhi : i < 32) :
    (sourceReference i).contract=demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece1

theorem reference_piece2 {i : ℕ} (hlo : 32 ≤ i) (hhi : i < 48) :
    (sourceReference i).contract=demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece2

theorem reference_piece3 {i : ℕ} (hlo : 48 ≤ i) (hhi : i < 64) :
    (sourceReference i).contract=demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece3

theorem reference_piece4 {i : ℕ} (hlo : 64 ≤ i) (hhi : i < 80) :
    (sourceReference i).contract=demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece4

theorem reference_piece5 {i : ℕ} (hlo : 80 ≤ i) (hhi : i < 96) :
    (sourceReference i).contract=demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece5

theorem reference_piece6 {i : ℕ} (hlo : 96 ≤ i) (hhi : i < 112) :
    (sourceReference i).contract=demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece6

theorem reference_piece7 {i : ℕ} (hlo : 112 ≤ i) (hhi : i < 128) :
    (sourceReference i).contract=demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece7

theorem reference_piece8 {i : ℕ} (hlo : 128 ≤ i) (hhi : i < 138) :
    (sourceReference i).contract=demand i := by
  interval_cases i <;> rfl
#print axioms reference_piece8

theorem reference_eq {i : ℕ} (hi : i < 138) : (sourceReference i).contract=demand i := by
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
  exact reference_piece8 (by omega) hi
#print axioms reference_eq

theorem actual_source {N i : ℕ} {S : Finset ℤ} (hi : i < 138)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (demand i).lower ≤ S.card) (hdefect : (demand i).defect ≤ Defect S) :
    (demand i).target ≤ (Pool S).card := by
  have hp : Paid (demand i) := by
    rw [← reference_eq hi]
    exact (sourceReference i).actual
  exact hp hN hground hS hsize hdefect
#print axioms actual_source
end
end JSP233.SourceAtlas82427
