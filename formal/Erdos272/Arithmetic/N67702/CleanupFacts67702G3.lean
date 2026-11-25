module

public import Erdos272.Arithmetic.N67702.CleanupChecks67702G33
public import Erdos272.Arithmetic.N67702.CleanupChecks67702G34
public import Erdos272.Arithmetic.CleanupFastSound208
public import Erdos272.Arithmetic.CleanupSegments208

@[expose] public section

namespace JSP233.CleanupFacts67702
open CleanupRows67702
open CleanupEval208 (ChunkFacts)
open CleanupMachineSound208 (toRow toTotals)
open CleanupSegments208 (append_exact)
open CleanupFastSound208 (check_sound)
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem fact144 : ChunkFacts (toRow data144.row) 1 data144.steps (toTotals data144.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks67702G33.checked0541)
    (check_sound CleanupChecks67702G33.checked0542)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks67702G33.checked0543)
    (check_sound CleanupChecks67702G34.checked0544)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact144

theorem fact145 : ChunkFacts (toRow data145.row) 1 data145.steps (toTotals data145.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks67702G34.checked0545)
      (check_sound CleanupChecks67702G34.checked0546)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks67702G34.checked0547)
      (check_sound CleanupChecks67702G34.checked0548)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks67702G34.checked0549)
  rfl rfl rfl)
#print axioms fact145

theorem fact146 : ChunkFacts (toRow data146.row) 1 data146.steps (toTotals data146.total) :=
  (append_exact
  (check_sound CleanupChecks67702G34.checked0550)
  (check_sound CleanupChecks67702G34.checked0551)
  rfl rfl rfl)
#print axioms fact146

theorem fact147 : ChunkFacts (toRow data147.row) 1 data147.steps (toTotals data147.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks67702G34.checked0552)
    (check_sound CleanupChecks67702G34.checked0553)
    rfl rfl rfl)
  (check_sound CleanupChecks67702G34.checked0554)
  rfl rfl rfl)
#print axioms fact147

end JSP233.CleanupFacts67702
