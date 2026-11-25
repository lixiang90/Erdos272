module

public import Erdos272.Arithmetic.N19227.Cut42
public import Erdos272.Arithmetic.N19227.Cut43
public import Erdos272.Arithmetic.N19227.Cut44
public import Erdos272.Arithmetic.N19227.Cut45
public import Erdos272.Arithmetic.N19227.Cut46
public import Erdos272.Arithmetic.N19227.Cut47
public import Erdos272.Arithmetic.N19227.Cut48
public import Erdos272.Arithmetic.N19227.Cut49
public import Erdos272.Arithmetic.N19227.Cut50
public import Erdos272.Arithmetic.N19227.Cut51
public import Erdos272.Arithmetic.N19227.Cut52
public import Erdos272.Arithmetic.N19227.Cut53
public import Erdos272.Arithmetic.N19227.Cut54
public import Erdos272.Arithmetic.N19227.Cut55
public import Erdos272.Arithmetic.N19227.Cut56
public import Erdos272.Arithmetic.N19227.Cut57
public import Erdos272.Arithmetic.N19227.Cut58
public import Erdos272.Arithmetic.N19227.Cut59
public import Erdos272.Arithmetic.N19227.Cut60
public import Erdos272.Arithmetic.N19227.Cut61
public import Erdos272.Arithmetic.N19227.Cut62
public import Erdos272.Arithmetic.N19227.Cut63
public import Erdos272.Arithmetic.N19227.Cut64
public import Erdos272.Arithmetic.N19227.Cut65
public import Erdos272.Arithmetic.N19227.Large
public import Erdos272.Global.N19227.CutBridge19227

@[expose] public section
namespace JSP233.Credit19227
open StarCompletion DenseDeletion40 FirstSparseCut20258 PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem middle (m : ℕ) (lo : 42≤m) (hi : m≤65) : Win m 19227 19682 := by
  interval_cases m
  · exact cut42
  · exact cut43
  · exact cut44
  · exact cut45
  · exact cut46
  · exact cut47
  · exact cut48
  · exact cut49
  · exact cut50
  · exact cut51
  · exact cut52
  · exact cut53
  · exact cut54
  · exact cut55
  · exact cut56
  · exact cut57
  · exact cut58
  · exact cut59
  · exact cut60
  · exact cut61
  · exact cut62
  · exact cut63
  · exact cut64
  · exact cut65

theorem of_cut {N m : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (lo : 19227≤N) (hi : N≤19682) (legal : Legal (Ground N) F) (cut : Cut N F m c T) : F.card≤B N := by
  have sparse := cut.sparse
  by_cases small : m≤41
  · have sq := Nat.mul_le_mul (Nat.sub_le_sub_right small 1) small
    apply FortyFourFamily20258.of_member (by omega) (by omega) legal (Density41.actual_sparse_membership.mp cut.omitter).1 cut.crooked
    rw [cut.size]
    omega
  by_cases mid : m≤65
  · exact middle m (by omega) mid lo hi legal cut
  by_cases firstBand : m≤76
  · exact band66 m (by omega) firstBand lo hi legal cut
  by_cases nextBand : m≤237
  · exact band77 m (by omega) nextBand lo hi legal cut
  exact band238 m (by omega) (by omega) lo hi legal cut

/-- In the verified slice, any counterexample would have a common
ground point in every retained nonprogression member. -/
theorem unrooted_upper {N : ℕ} {F : Finset (Finset ℤ)} (lo : 19227≤N) (hi : N≤20257)
    (legal : Legal (Ground N) F) (unrooted : ¬∃ c∈Ground N,∀ S∈Retained N 12 F,¬IsAP S → c∈S) :
    F.card≤B N := by
  by_contra! counter
  obtain ⟨m,c,T,cut⟩ := FiniteCuts19227.first (by omega) legal counter unrooted
  by_cases slice : N≤19682
  · exact (not_lt_of_ge (of_cut lo slice legal cut)) counter
  · exact (not_lt_of_ge (of_cut_bridge (by omega) hi legal cut)) counter

#print axioms of_cut
#print axioms unrooted_upper

end JSP233.Credit19227
