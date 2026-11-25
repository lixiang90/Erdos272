module

public import Erdos272.Arithmetic.N65172.CleanupChecks65172G02
public import Erdos272.Arithmetic.N65172.CleanupChecks65172G03
public import Erdos272.Arithmetic.N65172.CleanupChecks65172G04
public import Erdos272.Arithmetic.N65172.CleanupChecks65172G05
public import Erdos272.Arithmetic.CleanupFastSound208
public import Erdos272.Arithmetic.CleanupSegments208

@[expose] public section

namespace JSP233.CleanupFacts65172G1
open CleanupRows65172
open CleanupEval208 (ChunkFacts)
open CleanupMachineSound208 (toRow toTotals)
open CleanupSegments208 (append_exact)
open CleanupFastSound208 (check_sound)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem fact16 : ChunkFacts (toRow data16.row) 1 data16.steps (toTotals data16.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G02.checked0050)
    (check_sound CleanupChecks65172G02.checked0051)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65172G02.checked0052)
    (check_sound CleanupChecks65172G02.checked0053)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact16

theorem fact17 : ChunkFacts (toRow data17.row) 1 data17.steps (toTotals data17.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65172G02.checked0054)
      (check_sound CleanupChecks65172G02.checked0055)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65172G02.checked0056)
      (check_sound CleanupChecks65172G02.checked0057)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G02.checked0058)
  rfl rfl rfl)
#print axioms fact17

theorem fact18 : ChunkFacts (toRow data18.row) 1 data18.steps (toTotals data18.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65172G02.checked0059)
      (check_sound CleanupChecks65172G03.checked0060)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65172G03.checked0061)
      (check_sound CleanupChecks65172G03.checked0062)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G03.checked0063)
  rfl rfl rfl)
#print axioms fact18

theorem fact19 : ChunkFacts (toRow data19.row) 1 data19.steps (toTotals data19.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65172G03.checked0064)
      (check_sound CleanupChecks65172G03.checked0065)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65172G03.checked0066)
      (check_sound CleanupChecks65172G03.checked0067)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G03.checked0068)
  rfl rfl rfl)
#print axioms fact19

theorem fact20 : ChunkFacts (toRow data20.row) 1 data20.steps (toTotals data20.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65172G03.checked0069)
      (check_sound CleanupChecks65172G03.checked0070)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65172G03.checked0071)
      (check_sound CleanupChecks65172G03.checked0072)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G03.checked0073)
  rfl rfl rfl)
#print axioms fact20

theorem fact21 : ChunkFacts (toRow data21.row) 1 data21.steps (toTotals data21.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65172G03.checked0074)
      (check_sound CleanupChecks65172G03.checked0075)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65172G03.checked0076)
      (check_sound CleanupChecks65172G03.checked0077)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G03.checked0078)
  rfl rfl rfl)
#print axioms fact21

theorem fact22 : ChunkFacts (toRow data22.row) 1 data22.steps (toTotals data22.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65172G03.checked0079)
      (check_sound CleanupChecks65172G04.checked0080)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65172G04.checked0081)
      (check_sound CleanupChecks65172G04.checked0082)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G04.checked0083)
  rfl rfl rfl)
#print axioms fact22

theorem fact23 : ChunkFacts (toRow data23.row) 1 data23.steps (toTotals data23.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65172G04.checked0084)
      (check_sound CleanupChecks65172G04.checked0085)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65172G04.checked0086)
      (check_sound CleanupChecks65172G04.checked0087)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65172G04.checked0088)
    (check_sound CleanupChecks65172G04.checked0089)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact23

theorem fact24 : ChunkFacts (toRow data24.row) 1 data24.steps (toTotals data24.total) :=
  (append_exact
  (check_sound CleanupChecks65172G04.checked0090)
  (check_sound CleanupChecks65172G04.checked0091)
  rfl rfl rfl)
#print axioms fact24

theorem fact25 : ChunkFacts (toRow data25.row) 1 data25.steps (toTotals data25.total) :=
  (append_exact
  (check_sound CleanupChecks65172G04.checked0092)
  (check_sound CleanupChecks65172G04.checked0093)
  rfl rfl rfl)
#print axioms fact25

theorem fact26 : ChunkFacts (toRow data26.row) 1 data26.steps (toTotals data26.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G04.checked0094)
    (check_sound CleanupChecks65172G04.checked0095)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G04.checked0096)
  rfl rfl rfl)
#print axioms fact26

theorem fact27 : ChunkFacts (toRow data27.row) 1 data27.steps (toTotals data27.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G04.checked0097)
    (check_sound CleanupChecks65172G04.checked0098)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G04.checked0099)
  rfl rfl rfl)
#print axioms fact27

theorem fact28 : ChunkFacts (toRow data28.row) 1 data28.steps (toTotals data28.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G05.checked0100)
    (check_sound CleanupChecks65172G05.checked0101)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G05.checked0102)
  rfl rfl rfl)
#print axioms fact28

theorem fact29 : ChunkFacts (toRow data29.row) 1 data29.steps (toTotals data29.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G05.checked0103)
    (check_sound CleanupChecks65172G05.checked0104)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G05.checked0105)
  rfl rfl rfl)
#print axioms fact29

theorem fact30 : ChunkFacts (toRow data30.row) 1 data30.steps (toTotals data30.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G05.checked0106)
    (check_sound CleanupChecks65172G05.checked0107)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65172G05.checked0108)
    (check_sound CleanupChecks65172G05.checked0109)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact30

theorem fact31 : ChunkFacts (toRow data31.row) 1 data31.steps (toTotals data31.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G05.checked0110)
    (check_sound CleanupChecks65172G05.checked0111)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65172G05.checked0112)
    (check_sound CleanupChecks65172G05.checked0113)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact31

end
end JSP233.CleanupFacts65172G1
