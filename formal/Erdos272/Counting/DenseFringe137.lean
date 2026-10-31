import Erdos272.Arithmetic.AlignedLinear137
import Erdos272.Counting.ActualOffBlock119

/-! Actual dense long traces.  The original full sources keep their dense
rank and crookedness while the p13 private-key and periodic-hole counts are
combined.  No source is changed into a legal family on the trace interval. -/
namespace JSP233.DenseFringe137
open StarCompletion APGeometry ThinFringe33 KKRetention32 Restore33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_long_trace_fringe_bound {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hM : 1801800≤R-L+1) (hlarge : 90<L+N-R)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<11*S.card)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hm : ∀S∈E,(R-L+1)/13+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    E.card+63≤30*(L+N-R) := by
  obtain ⟨H,hHF,hHAP,hKH⟩ := hcore
  let M := R-L+1
  have hpair : ∀S∈E,IsAP (S∩H) := by
    intro S hS
    exact hlegal.2 S (hEF hS) H hHF (by intro hh;exact hbad S hS (hh ▸ hHAP))
  have hcover : ∀S∈E,∃k∈Relative13Fringe116.Keys,
      Relative13Fringe116.HasAnchor M (L:ℤ) (R:ℤ) k S := by
    intro S hS
    exact Relative13Fringe116.actual_trace_anchor hL hLR (by omega)
      (hpair S hS) hKH (hm S hS)
  let K : Finset ℤ→Relative13Fringe116.Key :=
    fun S=>if h:S∈E then Classical.choose (hcover S h) else ⟨1,1,1⟩
  have hK : ∀S∈E,K S∈Relative13Fringe116.Keys ∧
      Relative13Fringe116.HasAnchor M (L:ℤ) (R:ℤ) (K S) S := by
    intro S hS
    simpa only [K,dif_pos hS] using Classical.choose_spec (hcover S hS)
  have hELegal : Legal (Ground N) E := ⟨fun S hS=>hlegal.1 S (hEF hS),
    fun S hS T hT hn=>hlegal.2 S (hEF hS) T (hEF hT) hn⟩
  let d : Finset ℤ→ℤ := fun S=>(K S).1
  let a : Finset ℤ→ℤ := fun S=>Relative13Fringe116.Origin M (L:ℤ) (K S)
  have hsteps : ∀S∈E,d S≤12 := by
    intro S hS
    have hh := Finset.mem_Icc.mp (Finset.mem_sigma.mp (hK S hS).1).1
    dsimp only [d]
    exact_mod_cast hh.2
  have ho := ActualOffBlock119.actual_off_residue_count11 d a hLR hM hELegal
    (fun S hS=>(hK S hS).2.1) hsteps hm
  have ha := AlignedLinear137.actual_aligned_count19 K hL hLR hRN hlarge hELegal hbad hdense
    (fun S hS=>(hK S hS).1) (fun S hS=>(hK S hS).2)
  have he : E.filter (fun S=>¬Relative13Fringe116.Aligned K M (L:ℤ) S)=
      OffResidue44.OffMembers E d a := by
    ext S
    simp [Relative13Fringe116.Aligned,OffResidue44.OffMembers,d,a]
  have hc := Finset.card_filter_add_card_filter_not (s:=E) (Relative13Fringe116.Aligned K M (L:ℤ))
  rw [he] at hc
  have hext := ground_interval_exterior_card N (by exact_mod_cast hL : (1:ℤ)≤L)
    (by exact_mod_cast hLR : (L:ℤ)≤R) (by exact_mod_cast hRN : (R:ℤ)≤N)
  have hOc : (Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card+1=L+N-R := by omega
  nlinarith only [ha,ho,hc,hOc]


#print axioms actual_long_trace_fringe_bound
end
end JSP233.DenseFringe137
