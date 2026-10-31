import Erdos272.Retention.Dense10Aligned117
import Erdos272.Counting.ActualOffBlock119

/-! Actual dense long traces.  The original full sources keep their dense
rank and crookedness while the p13 private-key and periodic-hole counts are
combined.  No source is changed into a legal family on the trace interval. -/
namespace JSP233.DenseFringe120
open StarCompletion APGeometry ThinFringe33 KKRetention32 Restore33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_long_trace_fringe_bound {N L R r : ℕ} {F E : Finset (Finset ℤ)}
    (hL : 1≤L) (hLR : L≤R) (_hRN : R≤N) (hM : 1801800≤R-L+1)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<r*S.card)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hm : ∀S∈E,(R-L+1)/13+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    E.card≤((DenseAligned117.DenseShortKeys r).card+11)*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
  obtain ⟨H,hHF,hHAP,hKH⟩ := hcore
  let M := R-L+1
  have hI : 13^3≤(Finset.Icc (L:ℤ) (R:ℤ)).card := by
    rw [Relative13Fringe116.interval_card hLR]
    norm_num at *
    omega
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
  have hlong : ∀S∈E,(Finset.Icc (L:ℤ) (R:ℤ)).card<
      13*(S∩Finset.Icc (L:ℤ) (R:ℤ)).card := by
    intro S hS
    have hh := Nat.lt_mul_div_succ M (by decide : 0<13)
    have hhm := hm S hS
    rw [Relative13Fringe116.interval_card hLR]
    change M<13*(S∩Finset.Icc (L:ℤ) (R:ℤ)).card
    omega
  have hsteps : ∀S∈E,d S≤12 := by
    intro S hS
    have hh := Finset.mem_Icc.mp (Finset.mem_sigma.mp (hK S hS).1).1
    dsimp only [d]
    exact_mod_cast hh.2
  have ho := ActualOffBlock119.actual_off_residue_count11 d a hLR hM hELegal
    (fun S hS=>(hK S hS).2.1) hsteps hm
  have ha := DenseAligned117.actual_aligned_count K hELegal hbad hdense
    (fun S hS=>(hK S hS).1) (fun S hS=>(hK S hS).2)
  have he : E.filter (fun S=>¬Relative13Fringe116.Aligned K M (L:ℤ) S)=
      OffResidue44.OffMembers E d a := by
    ext S
    simp [Relative13Fringe116.Aligned,OffResidue44.OffMembers,d,a]
  have hc := Finset.card_filter_add_card_filter_not (s:=E) (Relative13Fringe116.Aligned K M (L:ℤ))
  rw [he] at hc
  nlinarith only [ha,ho,hc]


theorem actual_long_trace_fringe_bound44 {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hM : 1801800≤R-L+1)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S)
    (hdense : ∀S∈E,N<11*S.card)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hm : ∀S∈E,(R-L+1)/13+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    E.card≤44*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
  have h := actual_long_trace_fringe_bound hL hLR hRN hM hlegal hEF hbad hdense hcore hm
  simpa only [DenseAligned117.dense_short_keys_card11,Nat.reduceAdd] using h

theorem actual_long_trace_fringe_bound43 {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hM : 1801800≤R-L+1)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S)
    (hdense : ∀S∈E,N<10*S.card)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hm : ∀S∈E,(R-L+1)/13+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    E.card≤43*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
  have h := actual_long_trace_fringe_bound hL hLR hRN hM hlegal hEF hbad hdense hcore hm
  simpa only [Dense10Aligned117.dense_short_keys_card10,Nat.reduceAdd] using h

theorem actual_long_trace_fringe_bound42 {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hM : 1801800≤R-L+1)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S)
    (hdense : ∀S∈E,N<9*S.card)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hm : ∀S∈E,(R-L+1)/13+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    E.card≤42*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
  have h := actual_long_trace_fringe_bound hL hLR hRN hM hlegal hEF hbad hdense hcore hm
  simpa only [DenseAligned117.dense_short_keys_card9,Nat.reduceAdd] using h


#print axioms actual_long_trace_fringe_bound
#print axioms actual_long_trace_fringe_bound44
#print axioms actual_long_trace_fringe_bound43
#print axioms actual_long_trace_fringe_bound42
end
end JSP233.DenseFringe120
