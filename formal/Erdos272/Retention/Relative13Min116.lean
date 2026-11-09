module

public import Erdos272.Retention.Relative13Fringe116
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Relative off-point capacity retains the actual minimum full-source size.
No source is reinterpreted as a legal family on the trace interval. -/
namespace JSP233.Relative13Min116
open StarCompletion APGeometry ThinFringe33 KKRetention32 Restore33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_off_point_capacity12 {N L R m : ℕ} {E : Finset (Finset ℤ)}
    (d a : Finset ℤ→ℤ) (y : ℤ) (hLR : L≤R)
    (hlegal : Legal (Ground N) E)
    (htrace : ∀S∈E,APAt (d S) (a S) (S∩Finset.Icc (L:ℤ) (R:ℤ)))
    (hminimum : ∀S∈E,m≤S.card)
    (hgeometry : N+12*(L+N-R)+66<13*m)
    (hL : 1≤L) (hRN : R≤N) :
    (OffResidue44.OffPoint E d a y).card≤12 := by
  by_contra hn
  obtain ⟨C,hCE,hCc⟩ := Finset.exists_subset_card_eq (show 13≤(OffResidue44.OffPoint E d a y).card by omega)
  let T := fun S:Finset ℤ=>S∩Finset.Icc (L:ℤ) (R:ℤ)
  have hpair : ∀S∈C,∀U∈C,S≠U→((T S)∩(T U)).card≤1 := by
    intro S hS U hU hne
    obtain ⟨hSE,hyS,hoff⟩ := Finset.mem_filter.mp (hCE hS)
    obtain ⟨hUE,hyU,_hoffU⟩ := Finset.mem_filter.mp (hCE hU)
    exact OffResidue44.off_point_trace_inter_card (htrace S hSE)
      (hlegal.2 S hSE U hUE hne) hyS hyU hoff
  have hs := TracePacking43.trace_sum_bound C T hpair
  have hsub : C.biUnion T⊆Finset.Icc (L:ℤ) (R:ℤ) := by
    intro x hx
    obtain ⟨S,_hS,hx⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hx).2
  have hu := Finset.card_le_card hsub
  have hext := ground_interval_exterior_card N (by exact_mod_cast hL : (1:ℤ)≤L)
    (by exact_mod_cast hLR : (L:ℤ)≤R) (by exact_mod_cast hRN : (R:ℤ)≤N)
  have hext' : (Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card+1=L+N-R := by omega
  have hlow : ∑S∈C,m≤∑S∈C,((T S).card+(L+N-R)-1) := by
    apply Finset.sum_le_sum
    intro S hS
    have hSE := (Finset.mem_filter.mp (hCE hS)).1
    have hmin := hminimum S hSE
    have hb := card_le_trace_add_exterior (K:=Finset.Icc (L:ℤ) (R:ℤ)) (hlegal.1 S hSE)
    dsimp only [T]
    omega
  have hw : 1≤L+N-R := by omega
  have hlow' : ∑S∈C,m≤∑S∈C,((T S).card+((L+N-R)-1)) := by
    simpa only [Nat.add_sub_assoc hw] using hlow
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.sum_add_distrib,hCc] at hlow'
  rw [hCc] at hs
  norm_num [Nat.choose] at hs
  rw [Relative13Fringe116.interval_card hLR] at hu
  omega

theorem actual_off_residue_count12 {N L R m : ℕ} {E : Finset (Finset ℤ)}
    (d a : Finset ℤ→ℤ) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hlegal : Legal (Ground N) E)
    (htrace : ∀S∈E,APAt (d S) (a S) (S∩Finset.Icc (L:ℤ) (R:ℤ)))
    (hminimum : ∀S∈E,m≤S.card) (hgeometry : N+12*(L+N-R)+66<13*m) :
    (OffResidue44.OffMembers E d a).card≤12*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
  have hcover : OffResidue44.OffMembers E d a⊆
      (Ground N\Finset.Icc (L:ℤ) (R:ℤ)).biUnion (OffResidue44.OffPoint E d a) := by
    intro S hS
    obtain ⟨hSE,y,hyS,hoff⟩ := Finset.mem_filter.mp hS
    have hyI : y∉Finset.Icc (L:ℤ) (R:ℤ) := by
      intro hyI
      exact hoff (OffResidue44.origin_dvd (htrace S hSE) (Finset.mem_inter.mpr ⟨hyS,hyI⟩))
    exact Finset.mem_biUnion.mpr ⟨y,Finset.mem_sdiff.mpr ⟨hlegal.1 S hSE hyS,hyI⟩,
      Finset.mem_filter.mpr ⟨hSE,hyS,hoff⟩⟩
  calc
    _≤((Ground N\Finset.Icc (L:ℤ) (R:ℤ)).biUnion (OffResidue44.OffPoint E d a)).card := Finset.card_le_card hcover
    _≤∑y∈Ground N\Finset.Icc (L:ℤ) (R:ℤ),(OffResidue44.OffPoint E d a y).card := Finset.card_biUnion_le
    _≤∑_y∈Ground N\Finset.Icc (L:ℤ) (R:ℤ),12 := Finset.sum_le_sum (by
      intro y hy
      exact actual_off_point_capacity12 d a y hLR hlegal htrace hminimum hgeometry hL hRN)
    _=12*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by simp [Nat.mul_comm]

theorem actual_minimum_trace_long {N L R m : ℕ} {S : Finset ℤ}
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hS : S⊆Ground N)
    (hmin : m≤S.card) (hgeometry : N+12*(L+N-R)+66<13*m) :
    (R-L+1)/13+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card := by
  have hext := ground_interval_exterior_card N (by exact_mod_cast hL : (1:ℤ)≤L)
    (by exact_mod_cast hLR : (L:ℤ)≤R) (by exact_mod_cast hRN : (R:ℤ)≤N)
  have hs := card_le_trace_add_exterior (K:=Finset.Icc (L:ℤ) (R:ℤ)) hS
  have hd := Nat.mul_div_le (R-L+1) 13
  omega

theorem actual_minimum_fringe_bound47 {N L R m : ℕ} {F E : Finset (Finset ℤ)}
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hM : 169≤R-L+1)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S)
    (hminimum : ∀S∈E,m≤S.card)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hgeometry : N+12*(L+N-R)+66<13*m) :
    E.card≤47*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
  obtain ⟨H,hHF,hHAP,hKH⟩ := hcore
  let M := R-L+1
  have hpair : ∀S∈E,IsAP (S∩H) := by
    intro S hS
    exact hlegal.2 S (hEF hS) H hHF (by intro hh;exact hbad S hS (hh ▸ hHAP))
  have hm : ∀S∈E,M/13+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card := by
    intro S hS
    exact actual_minimum_trace_long hL hLR hRN (hlegal.1 S (hEF hS)) (hminimum S hS) hgeometry
  have hcover : ∀S∈E,∃k∈Relative13Fringe116.Keys,
      Relative13Fringe116.HasAnchor M (L:ℤ) (R:ℤ) k S := by
    intro S hS
    exact Relative13Fringe116.actual_trace_anchor hL hLR hM (hpair S hS) hKH (hm S hS)
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
  have ho := actual_off_residue_count12 d a hL hLR hRN hELegal
    (fun S hS=>(hK S hS).2.1) hminimum hgeometry
  have ha := Relative13Fringe116.actual_aligned_count K hELegal hbad
    (fun S hS=>(hK S hS).1) (fun S hS=>(hK S hS).2)
  have he : E.filter (fun S=>¬Relative13Fringe116.Aligned K M (L:ℤ) S)=
      OffResidue44.OffMembers E d a := by
    ext S
    simp [Relative13Fringe116.Aligned,OffResidue44.OffMembers,d,a]
  have hc := Finset.card_filter_add_card_filter_not (s:=E) (Relative13Fringe116.Aligned K M (L:ℤ))
  rw [he] at hc
  nlinarith only [ha,ho,hc]

#print axioms actual_off_point_capacity12
#print axioms actual_off_residue_count12
#print axioms actual_minimum_trace_long
#print axioms actual_minimum_fringe_bound47
end
end JSP233.Relative13Min116
