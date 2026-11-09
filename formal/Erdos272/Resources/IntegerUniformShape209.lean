module

public import Erdos272.Resources.IntegerUniformProfiles209

@[expose] public section

namespace JSP233.IntegerUniformShape209
open IntegerUniformProfiles209 IntegerUniformRows209
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

def Facts (w : Fin 11) : Prop := ∀i : Fin (count w),∀b : Fin 7,
    (band (row w i.val) b).b3=(band (row w i.val) b).b2 ∧
    (band (row w i.val) b).b5=(band (row w i.val) b).b2 ∧
    (band (row w i.val) b).b7=(band (row w i.val) b).b2 ∧
    (band (row w i.val) b).b11=(band (row w i.val) b).b2
instance (w : Fin 11) : Decidable (Facts w) := by unfold Facts;infer_instance
theorem facts (w : Fin 11) : Facts w := by fin_cases w <;> decide +kernel

theorem block_constant (w : Fin 11) (i : Fin (count w)) (b : Fin 7) (d : ℕ) :
    CleanupEval208.block (band (row w i.val) b) d=(band (row w i.val) b).b2 := by
  have h := facts w i b
  unfold CleanupEval208.block
  split <;> simp only [h.1,h.2.1,h.2.2.1,h.2.2.2]

theorem physical_domain (w : Fin 11) (i : Fin (count w)) (b : Fin 7) :
    (band (row w i.val) b).E<(band (row w i.val) b).T ∧
    0<(band (row w i.val) b).T-(band (row w i.val) b).E ∧
    0<(band (row w i.val) b).b2 ∧
    (band (row w i.val) b).T≤(band (row w i.val) b).U+(band (row w i.val) b).b2 := by
  have hw := IntegerUniformRows209.facts (W_mem w) (row_mem w i)
  have hb := hw.2.2.2.2.2.2.1 b
  have heM := hw.2.2.1
  have h2 := hb.2.2.2.2 2 (by simp)
  have hB : 2≤(band (row w i.val) b).b2 := by simpa only [blockPrime] using h2.1
  have hMT := hb.1
  have hEi := hb.2.2.1
  have hTU := hb.2.2.2.1
  omega

#print axioms facts
#print axioms block_constant
#print axioms physical_domain
end
end JSP233.IntegerUniformShape209

