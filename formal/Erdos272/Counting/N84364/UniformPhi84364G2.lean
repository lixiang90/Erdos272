module

public import Erdos272.Arithmetic.N84364.UniformNumeric84364
public import Erdos272.Arithmetic.FastDecode208

@[expose] public section

namespace JSP233.UniformPhi84364G2
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem checked : (List.range 128).all (fun j => decide (UniformNumeric84364.phi (256+j) = FastDecode208.phi (256+j))) = true := by
  decide +kernel
#print axioms checked

theorem correct {n : ℕ} (hlo : 256 ≤ n) (hhi : n < 384) :
    UniformNumeric84364.phi n = FastDecode208.phi n := by
  have hm : n-256 ∈ List.range 128 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked (n-256) hm)
  have he : 256+(n-256) = n := by omega
  simpa only [he] using hc
#print axioms correct
end JSP233.UniformPhi84364G2
