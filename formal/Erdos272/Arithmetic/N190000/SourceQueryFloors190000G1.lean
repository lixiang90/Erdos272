module

public import Erdos272.Arithmetic.N190000.SourceQueryData190000
public import Erdos272.Arithmetic.N190000.SourceFloors190000

@[expose] public section

namespace JSP233.SourceQueryFloors190000G1
open SourceQueryData190000 SourceFloorSound291012
set_option maxHeartbeats 0

theorem floors {i : ℕ} (hlo : 50 ≤ i) (hhi : i < 100) :
    Floor (query i).lower (query i).cutoff (query i).target := by
  interval_cases i
  · exact weaken (by decide) (by decide) SourceFloors190000.floor008
  · exact weaken (by decide) (by decide) SourceFloors190000.floor055
  · exact weaken (by decide) (by decide) SourceFloors190000.floor043
  · exact weaken (by decide) (by decide) SourceFloors190000.floor033
  · exact weaken (by decide) (by decide) SourceFloors190000.floor023
  · exact weaken (by decide) (by decide) SourceFloors190000.floor017
  · exact weaken (by decide) (by decide) SourceFloors190000.floor004
  · exact weaken (by decide) (by decide) SourceFloors190000.floor001
  · exact weaken (by decide) (by decide) SourceFloors190000.floor075
  · exact weaken (by decide) (by decide) SourceFloors190000.floor063
  · exact weaken (by decide) (by decide) SourceFloors190000.floor053
  · exact weaken (by decide) (by decide) SourceFloors190000.floor039
  · exact weaken (by decide) (by decide) SourceFloors190000.floor027
  · exact weaken (by decide) (by decide) SourceFloors190000.floor019
  · exact weaken (by decide) (by decide) SourceFloors190000.floor003
  · exact weaken (by decide) (by decide) SourceFloors190000.floor085
  · exact weaken (by decide) (by decide) SourceFloors190000.floor074
  · exact weaken (by decide) (by decide) SourceFloors190000.floor062
  · exact weaken (by decide) (by decide) SourceFloors190000.floor050
  · exact weaken (by decide) (by decide) SourceFloors190000.floor037
  · exact weaken (by decide) (by decide) SourceFloors190000.floor021
  · exact weaken (by decide) (by decide) SourceFloors190000.floor006
  · exact weaken (by decide) (by decide) SourceFloors190000.floor091
  · exact weaken (by decide) (by decide) SourceFloors190000.floor081
  · exact weaken (by decide) (by decide) SourceFloors190000.floor069
  · exact weaken (by decide) (by decide) SourceFloors190000.floor057
  · exact weaken (by decide) (by decide) SourceFloors190000.floor042
  · exact weaken (by decide) (by decide) SourceFloors190000.floor026
  · exact weaken (by decide) (by decide) SourceFloors190000.floor011
  · exact weaken (by decide) (by decide) SourceFloors190000.floor093
  · exact weaken (by decide) (by decide) SourceFloors190000.floor083
  · exact weaken (by decide) (by decide) SourceFloors190000.floor071
  · exact weaken (by decide) (by decide) SourceFloors190000.floor059
  · exact weaken (by decide) (by decide) SourceFloors190000.floor045
  · exact weaken (by decide) (by decide) SourceFloors190000.floor029
  · exact weaken (by decide) (by decide) SourceFloors190000.floor013
  · exact weaken (by decide) (by decide) SourceFloors190000.floor095
  · exact weaken (by decide) (by decide) SourceFloors190000.floor087
  · exact weaken (by decide) (by decide) SourceFloors190000.floor077
  · exact weaken (by decide) (by decide) SourceFloors190000.floor065
  · exact weaken (by decide) (by decide) SourceFloors190000.floor047
  · exact weaken (by decide) (by decide) SourceFloors190000.floor031
  · exact weaken (by decide) (by decide) SourceFloors190000.floor013
  · exact weaken (by decide) (by decide) SourceFloors190000.floor097
  · exact weaken (by decide) (by decide) SourceFloors190000.floor089
  · exact weaken (by decide) (by decide) SourceFloors190000.floor079
  · exact weaken (by decide) (by decide) SourceFloors190000.floor067
  · exact weaken (by decide) (by decide) SourceFloors190000.floor052
  · exact weaken (by decide) (by decide) SourceFloors190000.floor035
  · exact weaken (by decide) (by decide) SourceFloors190000.floor015

#print axioms floors
end JSP233.SourceQueryFloors190000G1
