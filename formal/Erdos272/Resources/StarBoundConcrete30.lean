import Erdos272.Foundation.JSP233
import Erdos272.Resources.StarBound30

/-! The new complete common-point theorem discharges the previously explicit
StarBound parameter of the existing actual-[N] omitter threshold. -/
namespace JSP233.StarBoundConcrete30
open StarCompletion

theorem ground_eq_Icc (N : ℕ) : Ground N=Finset.Icc (1:ℤ) (N:ℤ) := by
  ext x
  exact (mem_ground N x).trans Finset.mem_Icc.symm

theorem actual_starBound (N : ℕ) : StarBound (Ground N) (B N) := by
  rw [ground_eq_Icc]
  exact StarBound30.physical_starBound N

theorem best_omitter_threshold_unconditional
    (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (hcrooked : ∀ S∈Avoiders F c, ¬IsAP S)
    (hcount : (Avoiders F c).card≤max ((2*N+2)/3) (5*N/6)) : F.card≤B N := by
  exact best_certified_omitter_threshold N F c hc hlegal (actual_starBound N)
    hcrooked hcount

#print axioms ground_eq_Icc
#print axioms actual_starBound
#print axioms best_omitter_threshold_unconditional
end JSP233.StarBoundConcrete30
