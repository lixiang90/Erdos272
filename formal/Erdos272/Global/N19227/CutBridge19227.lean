module

public import Erdos272.Arithmetic.N19227.Bridge.Cut43
public import Erdos272.Arithmetic.N19227.Bridge.Cut44
public import Erdos272.Arithmetic.N19227.Bridge.Cut45
public import Erdos272.Arithmetic.N19227.Bridge.Cut46
public import Erdos272.Arithmetic.N19227.Bridge.Cut47
public import Erdos272.Arithmetic.N19227.Bridge.Cut48
public import Erdos272.Arithmetic.N19227.Bridge.Cut49
public import Erdos272.Arithmetic.N19227.Bridge.Cut50
public import Erdos272.Arithmetic.N19227.Bridge.Cut51
public import Erdos272.Arithmetic.N19227.Bridge.Cut52
public import Erdos272.Arithmetic.N19227.Bridge.Cut53
public import Erdos272.Arithmetic.N19227.Bridge.Cut54
public import Erdos272.Arithmetic.N19227.Bridge.Cut55
public import Erdos272.Arithmetic.N19227.Bridge.Cut56
public import Erdos272.Arithmetic.N19227.Bridge.Cut57
public import Erdos272.Arithmetic.N19227.Bridge.Cut58
public import Erdos272.Arithmetic.N19227.Bridge.Cut59
public import Erdos272.Arithmetic.N19227.Bridge.Cut60
public import Erdos272.Arithmetic.N19227.Bridge.Cut61
public import Erdos272.Arithmetic.N19227.Bridge.Cut62
public import Erdos272.Arithmetic.N19227.Bridge.Cut63
public import Erdos272.Arithmetic.N19227.Bridge.Cut64
public import Erdos272.Arithmetic.N19227.Bridge.Cut65
public import Erdos272.Arithmetic.N19227.Bridge.Cut66
public import Erdos272.Arithmetic.N19227.Bridge.Large

@[expose] public section
namespace JSP233.Credit19227
open StarCompletion FirstSparseCut20258 PopulationRanges20258
set_option autoImplicit false

private theorem bridge_middle (m : ℕ) (lo : 43≤m) (hi : m≤66) : Win m 19683 20257 := by
  interval_cases m
  · exact bridge43
  · exact bridge44
  · exact bridge45
  · exact bridge46
  · exact bridge47
  · exact bridge48
  · exact bridge49
  · exact bridge50
  · exact bridge51
  · exact bridge52
  · exact bridge53
  · exact bridge54
  · exact bridge55
  · exact bridge56
  · exact bridge57
  · exact bridge58
  · exact bridge59
  · exact bridge60
  · exact bridge61
  · exact bridge62
  · exact bridge63
  · exact bridge64
  · exact bridge65
  · exact bridge66

/-- Above the first slice, the same first-cut argument uses the repriced
ground windows through the start of the existing 20258 theorem. -/
theorem of_cut_bridge {N m : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (lo : 19683≤N) (hi : N≤20257) (legal : Legal (Ground N) F) (cut : Cut N F m c T) :
    F.card≤B N := by
  have sparse := cut.sparse
  by_cases small : m≤42
  · have prod := Nat.mul_le_mul (Nat.sub_le_sub_right small 1) small
    exact short (by decide : 2≤19683) (by omega : 5000*((m-1)*m+17)≤443*19683)
      lo hi legal cut
  by_cases mid : m≤66
  · exact bridge_middle m (by omega) mid lo hi legal cut
  by_cases firstBand : m≤76
  · exact bridgeBand67 m (by omega) firstBand lo hi legal cut
  by_cases nextBand : m≤237
  · exact bridgeBand77 m (by omega) nextBand lo hi legal cut
  exact bridgeBand238 m (by omega) (by omega) lo hi legal cut

end JSP233.Credit19227
