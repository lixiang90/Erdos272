module

public import Erdos272.Retention.BadFringe115
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! The long-trace fringe and the exceptional short-trace family are counted
on the same actual exterior.  The minimum source size is retained throughout. -/
namespace JSP233.BalancedFringe115
open StarCompletion APGeometry ThinFringe33 KKRetention32 Restore33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_short_trace_missing {N L R m : ℕ} {S : Finset ℤ}
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hS : S⊆Ground N)
    (hm : m≤S.card)
    (hshort : (S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤(R-L+1)/14+1) :
    ((Ground N\Finset.Icc (L:ℤ) (R:ℤ))\S).card≤
      (L+N-R)+(R-L+1)/14-m := by
  let I := Finset.Icc (L:ℤ) (R:ℤ)
  let O := Ground N\I
  have hs := Finset.card_sdiff_add_card_inter S I
  have ho := Finset.card_sdiff_add_card_inter O S
  have he : S\I=O∩S := by
    ext x
    change x∈S\I ↔ x∈(Ground N\I)∩S
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    constructor
    · intro h;exact ⟨⟨hS h.1,h.2⟩,h.1⟩
    · intro h;exact ⟨h.2,h.1.2⟩
  rw [he] at hs
  have hext := ground_interval_exterior_card N (by exact_mod_cast hL : (1:ℤ)≤L)
    (by exact_mod_cast hLR : (L:ℤ)≤R) (by exact_mod_cast hRN : (R:ℤ)≤N)
  change (O\S).card≤(L+N-R)+(R-L+1)/14-m
  change (S∩I).card≤(R-L+1)/14+1 at hshort
  have hext' : O.card+1=L+N-R := by dsimp only [O,I];omega
  omega

theorem actual_missing_shape {N L R m : ℕ}
    (_hL : 1≤L) (hLR : L≤R) (_hRN : R≤N)
    (hm : N<11*m) (hthin : 83*(L+N-R)≤2*N) (hlarge : 90<L+N-R) :
    8*((L+N-R)+(R-L+1)/14-m)+4≤L+N-R := by
  let w := L+N-R
  let M := R-L+1
  have hMw : M+w=N+1 := by dsimp only [M,w];omega
  have hdiv := Nat.mul_div_le M 14
  by_cases hs : w+M/14<m
  · have hb : w+M/14-m=0 := by omega
    change 8*(w+M/14-m)+4≤w
    omega
  · have hsub := Nat.sub_add_cancel (show m≤w+M/14 by omega)
    have hd : 154*(w+M/14-m)+3*N+3≤143*w := by
      nlinarith only [hsub,hdiv,hMw,hm]
    change 83*w≤2*N at hthin
    change 90<w at hlarge
    change 8*(w+M/14-m)+4≤w
    omega

theorem actual_long_trace_fringe_bound51 {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hL : 1≤L) (hLR : L≤R) (_hRN : R≤N) (hM : 14^3≤R-L+1)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hm : ∀S∈E,(R-L+1)/14+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    E.card≤51*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
  obtain ⟨H,hHF,hHAP,hKH⟩ := hcore
  let M := R-L+1
  have hI : 14^3≤(Finset.Icc (L:ℤ) (R:ℤ)).card := by
    rwa [RelativeFringe114.interval_card hLR]
  have hpair : ∀S∈E,IsAP (S∩H) := by
    intro S hS
    exact hlegal.2 S (hEF hS) H hHF (by intro hh;exact hbad S hS (hh ▸ hHAP))
  have hcover : ∀S∈E,∃k∈RelativeFringe114.Keys,
      RelativeFringe114.HasAnchor M (L:ℤ) (R:ℤ) k S := by
    intro S hS
    exact RelativeFringe114.actual_trace_anchor hL hLR (by norm_num at hM;omega)
      (hpair S hS) hKH (hm S hS)
  let K : Finset ℤ→RelativeFringe114.Key :=
    fun S=>if h:S∈E then Classical.choose (hcover S h) else ⟨1,1,1⟩
  have hK : ∀S∈E,K S∈RelativeFringe114.Keys ∧
      RelativeFringe114.HasAnchor M (L:ℤ) (R:ℤ) (K S) S := by
    intro S hS
    simpa only [K,dif_pos hS] using Classical.choose_spec (hcover S hS)
  have hELegal : Legal (Ground N) E := ⟨fun S hS=>hlegal.1 S (hEF hS),
    fun S hS T hT hn=>hlegal.2 S (hEF hS) T (hEF hT) hn⟩
  let d : Finset ℤ→ℤ := fun S=>(K S).1
  let a : Finset ℤ→ℤ := fun S=>RelativeFringe114.Origin M (L:ℤ) (K S)
  have hlong : ∀S∈E,(Finset.Icc (L:ℤ) (R:ℤ)).card<
      14*(S∩Finset.Icc (L:ℤ) (R:ℤ)).card := by
    intro S hS
    have hh := Nat.lt_mul_div_succ M (by decide : 0<14)
    have hhm := hm S hS
    rw [RelativeFringe114.interval_card hLR]
    change M<14*(S∩Finset.Icc (L:ℤ) (R:ℤ)).card
    omega
  have ho := RelativeFringe114.actual_off_residue_count14 d a hI hELegal
    (fun S hS=>(hK S hS).2.1) hlong
  have ha := RelativeFringe114.actual_aligned_count K hELegal hbad
    (fun S hS=>(hK S hS).1) (fun S hS=>(hK S hS).2)
  have he : E.filter (fun S=>¬RelativeFringe114.Aligned K M (L:ℤ) S)=
      OffResidue44.OffMembers E d a := by
    ext S
    simp [RelativeFringe114.Aligned,OffResidue44.OffMembers,d,a]
  have hc := Finset.card_filter_add_card_filter_not (s:=E) (RelativeFringe114.Aligned K M (L:ℤ))
  rw [he] at hc
  nlinarith only [ha,ho,hc]

theorem actual_fringe_bound51_or_unbalanced {N L R m : ℕ} {F E : Finset (Finset ℤ)}
    (hsize : 26000≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hmin : ∀S∈E,m≤S.card) (hm : N<11*m)
    (hthin : 83*(L+N-R)≤2*N) (hlarge : 90<L+N-R) :
    E.card≤51*(L+N-R) ∨ 4*L≤L+N-R ∨ 4*(N-R)≤L+N-R := by
  let w := L+N-R
  let M := R-L+1
  let b := w+M/14-m
  have hMw : M+w=N+1 := by dsimp only [M,w];omega
  have hshape : 8*b+4≤w := actual_missing_shape hL hLR hRN hm hthin hlarge
  by_cases hl : 2*b+1≤L-1
  · by_cases hr : 2*b+1≤N-R
    · left
      let D := E.filter (fun S=>(S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤M/14+1)
      let G := E.filter (fun S=>¬(S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤M/14+1)
      have hM : 14^3≤M := by norm_num;omega
      have hshort : ∀S∈D,(S∩Finset.Icc (L:ℤ) (R:ℤ)).card<
          (Finset.Icc (L:ℤ) (R:ℤ)).card := by
        intro S hS
        have hs := (Finset.mem_filter.mp hS).2
        rw [RelativeFringe114.interval_card hLR]
        change (S∩Finset.Icc (L:ℤ) (R:ℤ)).card<M
        omega
      have hd : D.card≤1 := BadFringe115.actual_short_trace_family_card_le_one hL hLR hRN
        hlegal ((Finset.filter_subset _ _).trans hEF)
        (fun S hS=>actual_short_trace_missing hL hLR hRN
          (hlegal.1 S (hEF (Finset.mem_filter.mp hS).1))
          (hmin S (Finset.mem_filter.mp hS).1) (Finset.mem_filter.mp hS).2)
        hshort hl hr (by omega)
      have hg : G.card≤51*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card :=
        actual_long_trace_fringe_bound51 hL hLR hRN hM hlegal
          ((Finset.filter_subset _ _).trans hEF)
          (fun S hS=>hbad S (Finset.mem_filter.mp hS).1) hcore
          (fun S hS=>by have hh := (Finset.mem_filter.mp hS).2;omega)
      have hc := Finset.card_filter_add_card_filter_not (s:=E)
        (fun S=>(S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤M/14+1)
      have hext := ground_interval_exterior_card N (by exact_mod_cast hL : (1:ℤ)≤L)
        (by exact_mod_cast hLR : (L:ℤ)≤R) (by exact_mod_cast hRN : (R:ℤ)≤N)
      change D.card+G.card=E.card at hc
      have hext' : (Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card+1=w := by
        dsimp only [w]
        omega
      change E.card≤51*w
      omega
    · right;right;dsimp only [w] at hshape ⊢;omega
  · right;left;dsimp only [w] at hshape ⊢;omega

#print axioms actual_short_trace_missing
#print axioms actual_missing_shape
#print axioms actual_long_trace_fringe_bound51
#print axioms actual_fringe_bound51_or_unbalanced
end
end JSP233.BalancedFringe115
