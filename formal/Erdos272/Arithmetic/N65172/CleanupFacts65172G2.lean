module

public import Erdos272.Arithmetic.N65172.CleanupChecks65172G05
public import Erdos272.Arithmetic.N65172.CleanupChecks65172G06
public import Erdos272.Arithmetic.N65172.CleanupChecks65172G07
public import Erdos272.Arithmetic.CleanupFastSound208
public import Erdos272.Arithmetic.CleanupSegments208

@[expose] public section

namespace JSP233.CleanupFacts65172G2
open CleanupRows65172
open CleanupEval208 (ChunkFacts)
open CleanupMachineSound208 (toRow toTotals)
open CleanupSegments208 (append_exact)
open CleanupFastSound208 (check_sound)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem fact32 : ChunkFacts (toRow data32.row) 1 data32.steps (toTotals data32.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G05.checked0114)
    (check_sound CleanupChecks65172G05.checked0115)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65172G05.checked0116)
    (check_sound CleanupChecks65172G05.checked0117)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact32

theorem fact33 : ChunkFacts (toRow data33.row) 1 data33.steps (toTotals data33.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G05.checked0118)
    (check_sound CleanupChecks65172G05.checked0119)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65172G06.checked0120)
    (check_sound CleanupChecks65172G06.checked0121)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact33

theorem fact34 : ChunkFacts (toRow data34.row) 1 data34.steps (toTotals data34.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65172G06.checked0122)
      (check_sound CleanupChecks65172G06.checked0123)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65172G06.checked0124)
      (check_sound CleanupChecks65172G06.checked0125)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G06.checked0126)
  rfl rfl rfl)
#print axioms fact34

theorem fact35 : ChunkFacts (toRow data35.row) 1 data35.steps (toTotals data35.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65172G06.checked0127)
      (check_sound CleanupChecks65172G06.checked0128)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65172G06.checked0129)
      (check_sound CleanupChecks65172G06.checked0130)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G06.checked0131)
  rfl rfl rfl)
#print axioms fact35

theorem fact36 : ChunkFacts (toRow data36.row) 1 data36.steps (toTotals data36.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65172G06.checked0132)
      (check_sound CleanupChecks65172G06.checked0133)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65172G06.checked0134)
      (check_sound CleanupChecks65172G06.checked0135)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G06.checked0136)
  rfl rfl rfl)
#print axioms fact36

theorem fact37 : ChunkFacts (toRow data37.row) 1 data37.steps (toTotals data37.total) :=
  (append_exact
  (check_sound CleanupChecks65172G06.checked0137)
  (check_sound CleanupChecks65172G06.checked0138)
  rfl rfl rfl)
#print axioms fact37

theorem fact38 : ChunkFacts (toRow data38.row) 1 data38.steps (toTotals data38.total) :=
  (append_exact
  (check_sound CleanupChecks65172G06.checked0139)
  (check_sound CleanupChecks65172G07.checked0140)
  rfl rfl rfl)
#print axioms fact38

theorem fact39 : ChunkFacts (toRow data39.row) 1 data39.steps (toTotals data39.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G07.checked0141)
    (check_sound CleanupChecks65172G07.checked0142)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G07.checked0143)
  rfl rfl rfl)
#print axioms fact39

theorem fact40 : ChunkFacts (toRow data40.row) 1 data40.steps (toTotals data40.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G07.checked0144)
    (check_sound CleanupChecks65172G07.checked0145)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G07.checked0146)
  rfl rfl rfl)
#print axioms fact40

theorem fact41 : ChunkFacts (toRow data41.row) 1 data41.steps (toTotals data41.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G07.checked0147)
    (check_sound CleanupChecks65172G07.checked0148)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65172G07.checked0149)
    (check_sound CleanupChecks65172G07.checked0150)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact41

theorem fact42 : ChunkFacts (toRow data42.row) 1 data42.steps (toTotals data42.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G07.checked0151)
    (check_sound CleanupChecks65172G07.checked0152)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65172G07.checked0153)
    (check_sound CleanupChecks65172G07.checked0154)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact42

end
end JSP233.CleanupFacts65172G2
