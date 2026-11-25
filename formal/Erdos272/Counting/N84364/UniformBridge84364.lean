module

public import Erdos272.Counting.N84364.UniformPhi84364G0
public import Erdos272.Counting.N84364.UniformPhi84364G1
public import Erdos272.Counting.N84364.UniformPhi84364G2
public import Erdos272.Counting.N84364.UniformPhi84364G3
public import Erdos272.Counting.N84364.UniformPhi84364G4
public import Erdos272.Counting.N86412.UniformSound86412

@[expose] public section

namespace JSP233.UniformBridge84364
open scoped BigOperators
set_option autoImplicit false

theorem phi_eq {n : ℕ} (hn : n < 549) :
    UniformNumeric84364.phi n = FastDecode208.phi n := by
  by_cases h0 : n < 128
  · exact UniformPhi84364G0.correct (by omega) h0
  by_cases h1 : n < 256
  · exact UniformPhi84364G1.correct (by omega) h1
  by_cases h2 : n < 384
  · exact UniformPhi84364G2.correct (by omega) h2
  by_cases h3 : n < 512
  · exact UniformPhi84364G3.correct (by omega) h3
  exact UniformPhi84364G4.correct (by omega) hn
#print axioms phi_eq

theorem value_eq {s : ℕ} (hs : s ≤ 549) :
    UniformNumeric84364.value s = UniformEval86412.value s := by
  unfold UniformNumeric84364.value UniformEval86412.value
  apply Finset.sum_congr rfl
  intro q hq
  have hq549 : q < 549 := (Finset.mem_Ico.mp hq).2.trans_le hs
  rw [phi_eq hq549]
#print axioms value_eq

theorem uniform_paid {lower target : ℕ}
    (hlower : 4 ≤ lower) (hcap : lower ≤ 549)
    (hvalue : target ≤ UniformNumeric84364.value lower)
    (hpool : ∀ S : Finset ℤ, 4 ≤ S.card → ¬StarCompletion.IsAP S →
      TotientStrict86412.U S.card ≤ (IntrinsicTriples208.Pool S).card) :
    SourceContract86412.Paid ⟨lower,1,target⟩ := by
  have hv : target ≤ UniformEval86412.value lower := by
    simpa only [value_eq hcap] using hvalue
  intro N S hN hground hS hsize hdefect
  exact UniformSound86412.uniform_paid (lower:=lower) (target:=target) hlower
    (hcap.trans (by decide : 549 ≤ 32753)) hv hpool
    hN hground hS hsize hdefect
#print axioms uniform_paid
end JSP233.UniformBridge84364
