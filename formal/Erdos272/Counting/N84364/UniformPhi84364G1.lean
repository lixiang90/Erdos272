module

public import Erdos272.Arithmetic.N84364.UniformNumeric84364
public import Erdos272.Arithmetic.FastDecode208

@[expose] public section

namespace JSP233.UniformPhi84364G1
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem checked : (List.range 128).all (fun j => decide (UniformNumeric84364.phi (128+j) = FastDecode208.phi (128+j))) = true := by
  decide +kernel
#print axioms checked

theorem correct {n : ℕ} (hlo : 128 ≤ n) (hhi : n < 256) :
    UniformNumeric84364.phi n = FastDecode208.phi n := by
  have hm : n-128 ∈ List.range 128 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked (n-128) hm)
  have he : 128+(n-128) = n := by omega
  simpa only [he] using hc
#print axioms correct
end JSP233.UniformPhi84364G1
