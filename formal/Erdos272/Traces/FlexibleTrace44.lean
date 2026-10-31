import Erdos272.Core.TracePacking43

/-! Actual dense traces with a grid parameter p independent of the dense
rank r. Actual anchors are constructed from the same legal original family. -/
namespace JSP233.FlexibleTrace44
open StarCompletion APGeometry ThinFringe33 ThinFringe42 KKRetention32 Restore33
open scoped Classical BigOperators
noncomputable section

theorem trace_count_lower (r p N m o : ℕ) (hr : 0<r) (hp : r<p)
    (hdense : N<r*(m+o)) (hthin : r*p*(o+1)≤(p-r)*N) : N/p+1<m := by
  have hpr : p-r+r=p := Nat.sub_add_cancel hp.le
  have hq := Nat.mul_div_le N p
  by_contra hn
  have hm : m≤N/p+1 := by omega
  have hmN : p*m≤N+p := by
    have hh := Nat.mul_le_mul_left p hm
    nlinarith only [hh,hq]
  have h1 := Nat.mul_lt_mul_of_pos_left hdense (by omega : 0<p)
  have h2 := Nat.mul_le_mul_left r hmN
  nlinarith only [h1,h2,hthin,hpr]

theorem dense_trace_geometry (r p N : ℕ) (hr : 0<r) (hp : r<p)
    {S H : Finset ℤ} {L R : ℤ}
    (hS : S⊆Ground N) (hpair : IsAP (S∩H)) (hKH : Finset.Icc L R⊆H)
    (hL : 1≤L) (_hLR : L≤R) (hR : R≤(N:ℤ)) (hdense : N<r*S.card)
    (hthin : r*p*((Ground N\Finset.Icc L R).card+1)≤(p-r)*N) :
    ∃ d a,APAt d a (S∩Finset.Icc L R) ∧ d≤(p-1:ℕ) ∧
      N/p+1<(S∩Finset.Icc L R).card := by
  let m := (S∩Finset.Icc L R).card
  let o := (Ground N\Finset.Icc L R).card
  have hc := card_le_trace_add_exterior (K:=Finset.Icc L R) hS
  have hD : N<r*(m+o) := hdense.trans_le (Nat.mul_le_mul_left r hc)
  have hm := trace_count_lower r p N m o hr hp hD hthin
  have hm2 : 2≤m := by
    have hz := Nat.zero_le (N/p)
    omega
  obtain ⟨d,a,hAP⟩ := apAt_interval_trace hpair hKH
  refine ⟨d,a,hAP,?_,hm⟩
  have hne : (S∩Finset.Icc L R).Nonempty := Finset.card_pos.mp (by change 0<m;omega)
  have hspan := apAt_span_eq hAP hne
  have ha := Finset.mem_Icc.mp (Finset.mem_inter.mp (Finset.min'_mem (S∩Finset.Icc L R) hne)).2
  have hb := Finset.mem_Icc.mp (Finset.mem_inter.mp (Finset.max'_mem (S∩Finset.Icc L R) hne)).2
  have hbound : d*((m:ℤ)-1)≤(N:ℤ)-1 := by dsimp [m];omega
  have hNq : N<p*(N/p+1) := Nat.lt_mul_div_succ N (by omega)
  have hNqZ : (N:ℤ)<(p:ℤ)*((N/p:ℕ)+1:ℕ) := by exact_mod_cast hNq
  have hmm : (N/p:ℕ)+1≤m-1 := by omega
  have hmmZ : ((N/p:ℕ)+1:ℕ)≤((m:ℤ)-1) := by omega
  have hp1 : p-1+1=p := by omega
  have hpsub : ((p-1:ℕ):ℤ)=(p:ℤ)-1 := by omega
  by_contra hn
  have hdp : (p:ℤ)≤d := by omega
  have hpos : (0:ℤ)≤(m:ℤ)-1 := by omega
  have hmul := mul_le_mul_of_nonneg_right hdp hpos
  have hmul2 := mul_le_mul_of_nonneg_left hmmZ (show (0:ℤ)≤p by positivity)
  nlinarith only [hbound,hNqZ,hmul,hmul2]

theorem actual_trace_anchor (r p N : ℕ) (hr : 0<r) (hp : r<p) (hp3 : 3≤p)
    (hN : p^2≤N) {S H : Finset ℤ} {L R : ℤ}
    (hS : S⊆Ground N) (hpair : IsAP (S∩H)) (hKH : Finset.Icc L R⊆H)
    (hL : 1≤L) (hLR : L≤R) (hR : R≤(N:ℤ)) (hdense : N<r*S.card)
    (hthin : r*p*((Ground N\Finset.Icc L R).card+1)≤(p-r)*N) :
    ∃ k∈ThinFringe42.AnchorKeys (p-1),ThinFringe42.HasAnchor (p-1) N L R k S := by
  obtain ⟨d,a0,hAP,hdr,hm⟩ := dense_trace_geometry r p N hr hp hS hpair hKH hL hLR hR hdense hthin
  have hd := hAP.1
  have hcard : 2≤(S∩Finset.Icc L R).card := by
    have hz := Nat.zero_le (N/p)
    omega
  have hne : (S∩Finset.Icc L R).Nonempty := Finset.card_pos.mp (by omega)
  let a := (S∩Finset.Icc L R).min' hne
  let b := (S∩Finset.Icc L R).max' hne
  have haS : a∈S∩Finset.Icc L R := Finset.min'_mem _ hne
  have hbS : b∈S∩Finset.Icc L R := Finset.max'_mem _ hne
  have haK := Finset.mem_Icc.mp (Finset.mem_inter.mp haS).2
  have hbK := Finset.mem_Icc.mp (Finset.mem_inter.mp hbS).2
  have ha : 1≤a := by omega
  have hab : a≤b := Finset.min'_le _ b hbS
  have haCast : (a.toNat:ℤ)=a := Int.toNat_of_nonneg (by omega)
  have hbCast : (b.toNat:ℤ)=b := Int.toNat_of_nonneg (by omega)
  have hdCast : (d.toNat:ℤ)=d := Int.toNat_of_nonneg hd.le
  have hspan := apAt_span_eq hAP hne
  have hsub : (((S∩Finset.Icc L R).card-1:ℕ):ℤ)=((S∩Finset.Icc L R).card:ℤ)-1 := by omega
  have hspanN : b.toNat=a.toNat+d.toNat*((S∩Finset.Icc L R).card-1) := by
    have hh : (b.toNat:ℤ)=(a.toNat:ℤ)+(d.toNat:ℤ)*(((S∩Finset.Icc L R).card-1:ℕ):ℤ) := by
      rw [haCast,hbCast,hdCast,hsub]
      dsimp [a,b]
      linarith
    exact_mod_cast hh
  have hp1 : p-1+1=p := by omega
  obtain ⟨k,hk,hkd,hau,hub,hdiv⟩ := grid_anchor_cover (p-1) N a.toNat b.toNat d.toNat
    (S∩Finset.Icc L R).card (by omega) (by simpa only [hp1] using hN)
    (by omega) (by omega) (by omega) (by omega) hspanN (by simpa only [hp1] using hm)
  have hu0 : 0≤ThinFringe42.AnchorPoint (p-1) N k := by unfold ThinFringe42.AnchorPoint;positivity
  have huCast : ((ThinFringe42.AnchorPoint (p-1) N k).toNat:ℤ)=ThinFringe42.AnchorPoint (p-1) N k := Int.toNat_of_nonneg hu0
  have hkdZ : (k.1:ℤ)=d := by rw [hkd,hdCast]
  have hauZ : a≤ThinFringe42.AnchorPoint (p-1) N k := by omega
  have hubZ : ThinFringe42.AnchorPoint (p-1) N k+d≤b := by omega
  have hdivZ : d∣ThinFringe42.AnchorPoint (p-1) N k-a := by
    have hh : (d.toNat:ℤ)∣(((ThinFringe42.AnchorPoint (p-1) N k).toNat-a.toNat:ℕ):ℤ) := by exact_mod_cast hdiv
    rw [Nat.cast_sub hau,huCast,haCast,hdCast] at hh
    exact hh
  have huS : ThinFringe42.AnchorPoint (p-1) N k∈S∩Finset.Icc L R := apAt_fill hAP haS hbS hauZ (by omega) hdivZ
  have hvS : ThinFringe42.AnchorPoint (p-1) N k+d∈S∩Finset.Icc L R :=
    apAt_fill hAP haS hbS (by omega) hubZ (by
      have hh := Int.dvd_add hdivZ (dvd_refl d)
      convert hh using 1
      ring)
  refine ⟨k,hk,?_,huS,?_⟩
  · rw [hkdZ]
    exact apAt_rebase hAP huS
  · simpa only [hkdZ] using hvS

theorem actual_dense_anchor_cover (r p N : ℕ) (hr : 0<r) (hp : r<p) (hp3 : 3≤p)
    (hN : p^2≤N) (F E : Finset (Finset ℤ)) (L R : ℤ)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀ S∈E,¬IsAP S)
    (hdense : ∀ S∈E,N<r*S.card) (hL : 1≤L) (hLR : L≤R) (hR : R≤(N:ℤ))
    (hcore : ∃ H∈F,IsAP H ∧ Finset.Icc L R⊆H)
    (hthin : r*p*((Ground N\Finset.Icc L R).card+1)≤(p-r)*N) :
    ∀ S∈E,∃ k∈ThinFringe42.AnchorKeys (p-1),ThinFringe42.HasAnchor (p-1) N L R k S := by
  obtain ⟨H,hHF,hHAP,hKH⟩ := hcore
  intro S hS
  have hne : S≠H := by intro he;exact hbad S hS (he ▸ hHAP)
  exact actual_trace_anchor r p N hr hp hp3 hN (hlegal.1 S (hEF hS))
    (hlegal.2 S (hEF hS) H hHF hne) hKH hL hLR hR (hdense S hS) hthin

theorem geometry39_41_of_quarter800 (N t : ℕ) (h : 800*t≤N) :
    39*41*t≤(41-39)*N := by nlinarith

#print axioms trace_count_lower
#print axioms dense_trace_geometry
#print axioms actual_trace_anchor
#print axioms actual_dense_anchor_cover
#print axioms geometry39_41_of_quarter800
end
end JSP233.FlexibleTrace44
