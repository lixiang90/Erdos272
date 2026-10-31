import Erdos272.Counting.AlignedResidue137
namespace JSP233.AlignedLinear137
open StarCompletion APGeometry Relative13Fringe116 AlignedResidue137 ResidueInterval137
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_aligned_count11_real {N M L R:ℕ} {E:Finset (Finset ℤ)}
    (K:Finset ℤ→Key) (hL:1≤L) (hLR:L≤R) (hRN:R≤N)
    (hlegal:Legal (Ground N) E) (hbad:∀S∈E,¬IsAP S) (hdense:∀S∈E,N<11*S.card)
    (hkeys:∀S∈E,K S∈Keys)
    (hanchor:∀S∈E,Relative13Fringe116.HasAnchor M (L:ℤ) (R:ℤ) (K S) S) :
    ((E.filter (Aligned K M (L:ℤ))).card:ℝ)≤
      (9221/504:ℝ)*((L:ℝ)+(N:ℝ)-(R:ℝ))+1867/168 := by
  obtain ⟨phase,hcount⟩:=actual_aligned_count_residue K hlegal hbad hdense hkeys hanchor
  let C:ℕ→Finset ℤ:=fun d=>ResidueOutside N (L:ℤ) (R:ℤ) d (phase d)
  change (E.filter (Aligned K M (L:ℤ))).card≤∑d∈Finset.Icc 1 10,(12/d)*(C d).card at hcount
  have hcountR:((E.filter (Aligned K M (L:ℤ))).card:ℝ)≤
      ∑d∈Finset.Icc 1 10,((12/d:ℕ):ℝ)*((C d).card:ℝ):=by exact_mod_cast hcount
  have hrow (d:ℕ) (hd:d∈Finset.Icc 1 10):
      (d:ℝ)*((C d).card:ℝ)≤(L:ℝ)-1+(N:ℝ)-(R:ℝ)+2*((d:ℝ)-1):=by
    have hd1:1≤d:=(Finset.mem_Icc.mp hd).1
    have hd0:0<d:=by omega
    have hh:=residue_outside_mass hL hLR hRN hd0 (phase d)
    have hr:(d:ℝ)*((C d).card:ℝ)≤
        ((L-1:ℕ):ℝ)+((N-R:ℕ):ℝ)+2*((d-1:ℕ):ℝ):=by exact_mod_cast hh
    rw [Nat.cast_sub hL,Nat.cast_sub hRN,Nat.cast_sub hd1,Nat.cast_one] at hr
    linarith only [hr]
  have h1:=hrow 1 (by decide)
  have h2:=hrow 2 (by decide)
  have h3:=hrow 3 (by decide)
  have h4:=hrow 4 (by decide)
  have h5:=hrow 5 (by decide)
  have h6:=hrow 6 (by decide)
  have h7:=hrow 7 (by decide)
  have h8:=hrow 8 (by decide)
  have h9:=hrow 9 (by decide)
  have h10:=hrow 10 (by decide)
  norm_num [Finset.sum_Icc_succ_top] at hcountR
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  linarith only [hcountR,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]

theorem actual_aligned_count19 {N M L R:ℕ} {E:Finset (Finset ℤ)}
    (K:Finset ℤ→Key) (hL:1≤L) (hLR:L≤R) (hRN:R≤N) (hlarge:90<L+N-R)
    (hlegal:Legal (Ground N) E) (hbad:∀S∈E,¬IsAP S) (hdense:∀S∈E,N<11*S.card)
    (hkeys:∀S∈E,K S∈Keys)
    (hanchor:∀S∈E,Relative13Fringe116.HasAnchor M (L:ℤ) (R:ℤ) (K S) S) :
    (E.filter (Aligned K M (L:ℤ))).card+52≤19*(L+N-R) := by
  have hh:=actual_aligned_count11_real K hL hLR hRN hlegal hbad hdense hkeys hanchor
  have he:((L+N-R:ℕ):ℝ)=(L:ℝ)+(N:ℝ)-(R:ℝ):=by
    rw [Nat.cast_sub (by omega:R≤L+N),Nat.cast_add]
  have hw:(91:ℝ)≤((L+N-R:ℕ):ℝ):=by exact_mod_cast (show 91≤L+N-R by omega)
  have hc:((E.filter (Aligned K M (L:ℤ))).card:ℝ)+52≤19*((L+N-R:ℕ):ℝ):=by
    rw [←he] at hh
    linarith only [hh,hw]
  exact_mod_cast hc

#print axioms actual_aligned_count11_real
#print axioms actual_aligned_count19
end
end JSP233.AlignedLinear137
