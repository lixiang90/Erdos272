import Erdos272.Retention.Terminal36
import Erdos272.Retention.JointFringe44
import Erdos272.Arithmetic.PrimorialRatio39

/-! Actual external avoiders force a small-AP deficit.  The adaptive original
family restoration below retains the established logarithmic physical terminal
condition.  The separate uniform-seven arithmetic theorem does not silently
replace that condition in the imported terminal. -/
namespace JSP233.TerminalDeficit51
open StarCompletion PrivatePairExistence StarResources30 LongTerminal35
open APGeometry KKRetention32 Restore33 DenseDeletion40 JointFringe44 ThinFringe33
open scoped Classical BigOperators
noncomputable section

theorem actual_uniform_totient_seven {N m : ℕ} (hN : N<2^50) (hm : m≤N) :
    m≤7*Nat.totient m := by
  have hu := (PrimorialRatio39.uniform_q49 N hN).2.1 m hm
  have hc : (131710070791/19110297600:ℝ)≤7 := by norm_num
  have hp : (0:ℝ)≤Nat.totient m := by positivity
  have hh : (m:ℝ)≤7*(Nat.totient m:ℝ) :=
    hu.trans (mul_le_mul_of_nonneg_right hc hp)
  exact_mod_cast hh

theorem actual_long_core_totient_supply_seven (N c L R d u : ℕ)
    (hN : N<2^50) (hcL : c<L) (_hLR : L≤R) (hRN : R≤N)
    (hd : 0<d) (hdt : d≤L+N-R) (hthin : 28*(L+N-R)≤N)
    (hu : (R-c)/d<u) (huN : u≤N/d) :
    ((L-c)/d+1)+(c-1)/d+1≤Nat.totient u := by
  let t := L+N-R
  have hLt : L≤t := by dsimp [t];omega
  have hsum : N+L=t+R := by dsimp [t];omega
  have hLc : L-c+c=L := Nat.sub_add_cancel hcL.le
  have hRc : R-c+c=R := Nat.sub_add_cancel (by omega)
  have hratio := actual_uniform_totient_seven hN (huN.trans (Nat.div_le_self N d))
  have hlow : R-c<u*d := (Nat.div_lt_iff_lt_mul hd).mp hu
  by_contra hfail
  have hphi : Nat.totient u≤(L-c)/d+c/d+1 := by
    have hh : (c-1)/d≤c/d := Nat.div_le_div_right (Nat.sub_le c 1)
    omega
  have hdphi : d*Nat.totient u≤2*t := by
    have h1 := Nat.mul_div_le (L-c) d
    have h2 := Nat.mul_div_le c d
    have hh := Nat.mul_le_mul_left d hphi
    change d≤t at hdt
    nlinarith only [h1,h2,hh,hdt,hLt,hLc]
  have hupper : d*u≤14*t := by
    have hh := Nat.mul_le_mul_left d hratio
    nlinarith only [hh,hdphi]
  change 28*t≤N at hthin
  nlinarith only [hupper,hlow,hsum,hRc,hLc,hthin]

theorem actual_normalized_cutoff_seven (N c L R d : ℕ)
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d)
    (hdt : d≤L+N-R) (hthin : 28*(L+N-R)≤N) : 2≤(R-c)/d := by
  apply (Nat.le_div_iff_mul_le hd).mpr
  omega

theorem actual_coprime_prefix_core_seven {N c L R d h m : ℕ}
    (hN : N<2^50) (hcL : c<L) (_hLR : L≤R) (hRN : R≤N)
    (hd : 0<d) (hdL : d≤L) (hthin : 42*(L+N-R)≤N)
    (hmR : R<c+m*d) (hmN : c+m*d≤N) (hhalf : R+c<2*(c+h*d)) :
    ∃ j,L≤c+j*d ∧ j≤h ∧ Nat.Coprime j m := by
  let t := L+N-R
  let a := (L-c)/d+1
  let q := 2*a+(m-2*h)
  have hLt : L≤t := by dsimp [t];omega
  have hsum : N+L=t+R := by dsimp [t];omega
  have hLc : L-c+c=L := Nat.sub_add_cancel hcL.le
  have hmN' : m≤N := by
    have hh := Nat.le_mul_of_pos_right m hd
    omega
  have ha : d*a≤L-c+d := by
    have hh := Nat.mul_div_le (L-c) d
    dsimp [a]
    nlinarith only [hh]
  have hmid : d*(m-2*h)≤N-R := by
    by_cases hh : 2*h≤m
    · have he := congrArg (fun z=>d*z) (Nat.sub_add_cancel hh)
      have hNR := Nat.sub_add_cancel hRN
      nlinarith only [he,hNR,hmN,hhalf]
    · have he : m-2*h=0 := by omega
      simp only [he,mul_zero,Nat.zero_le]
  have hq : d*q≤4*t := by
    calc
      d*q=2*(d*a)+d*(m-2*h) := by dsimp [q];ring
      _≤2*(L-c+d)+(N-R) := by omega
      _≤4*t := by omega
  have hratio := actual_uniform_totient_seven hN hmN'
  have hlarge : q*7<m := by
    by_contra hh
    have hbound : d*m≤28*t := by
      have hh := Nat.mul_le_mul_left d (show m≤q*7 by omega)
      nlinarith only [hq,hh]
    change 42*t≤N at hthin
    nlinarith only [hbound,hmR,hsum,hLc,hthin]
  obtain ⟨j,haj,hjh,hcop⟩ := CoprimeMiddle36.exists_coprime_middle_of_supply hratio hlarge
  have hj : (L-c)/d<j := by change (L-c)/d+1≤j at haj;omega
  have hjd : L-c<j*d := (Nat.div_lt_iff_lt_mul hd).mp hj
  exact ⟨j,by omega,hjh,hcop⟩

theorem actual_APSmall_external_avoider (N : ℕ) (c : ℤ)
    (F H : Finset (Finset ℤ)) (P : Finset ℤ)
    (hlegal : Legal (Ground N) F) (hHF : H⊆F) (hroot : Rooted H c)
    (hPF : P∈F) (hcP : c∉P) : (APSmall H).card≤P.card := by
  have hH : Legal (Ground N) H :=
    ⟨fun S hS=>hlegal.1 S (hHF hS),fun S hS T hT he=>hlegal.2 S (hHF hS) T (hHF hT) he⟩
  have hs : APSmall H⊆PairStar P c := by
    intro S hS
    obtain ⟨x,_hx,hSx⟩ := Finset.mem_image.mp (apSmall_subset_pairStar c (Ground N) H hH hroot hS)
    have hSH := (Finset.mem_filter.mp hS).1
    have hne : S≠P := by intro he;exact hcP (he ▸ hroot S hSH)
    obtain ⟨y,hy⟩ := isAP_nonempty (hlegal.2 S (hHF hSH) P hPF hne)
    obtain ⟨hyS,hyP⟩ := Finset.mem_inter.mp hy
    rw [←hSx] at hyS
    simp only [Finset.mem_insert,Finset.mem_singleton] at hyS
    have hxP : x∈P := by
      rcases hyS with rfl|rfl
      · exact False.elim (hcP hyP)
      · exact hyP
    exact Finset.mem_image.mpr ⟨x,hxP,hSx⟩
  exact (Finset.card_le_card hs).trans_eq (pairStar_card P c)

theorem actual_boundary_fringe_count (N c L R : ℕ) (I : Finset (ℕ×ℕ))
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N) (hv : ValidIntervals N c L R I) :
    (Boundary c N I).card≤L+N-R-c := by
  let K := Finset.Icc c (L-1) ∪ Finset.Icc (R+1) N
  have hmaps : ∀ p∈Boundary c N I,BoundaryCode c N p∈K := by
    intro p hp
    obtain ⟨hpI,hpB⟩ := Finset.mem_filter.mp hp
    obtain ⟨hcp,hpL,hRp,hpN⟩ := hv p hpI
    simp only [K,Finset.mem_union,Finset.mem_Icc]
    unfold BoundaryCode
    split_ifs <;> omega
  have hinj := boundary_code_injective N c L R I hLR hv (by
    intro p hp q hq
    obtain ⟨_,hpL,hRp,_⟩ := hv p hp
    obtain ⟨_,hqL,hRq,_⟩ := hv q hq
    exact ⟨(L:ℤ),Finset.mem_Icc.mpr ⟨by omega,by omega⟩,
      Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩)
  have hcard : (Boundary c N I).card≤K.card :=
    (Finset.card_image_of_injOn hinj).symm.trans_le (Finset.card_le_card (by
      intro x hx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      exact hmaps p hp))
  have hK : K.card≤L+N-R-c := by
    have hh := Finset.card_union_le (Finset.Icc c (L-1)) (Finset.Icc (R+1) N)
    simp only [Nat.card_Icc] at hh
    dsimp [K]
    omega
  exact hcard.trans hK

theorem actual_native_terminal_deficit (N c L R : ℕ)
    (F G : Finset (Finset ℤ)) (P : Finset ℤ)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hlegal : Legal (Ground N) F) (hGF : G⊆F) (hPF : P∈F) (hcP : (c:ℤ)∉P)
    (hi : ∀ S∈Avoiders G (c:ℤ),∃ a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) :
    G.card+N≤N.choose 2+P.card+(L+N-R) := by
  obtain ⟨I,hv,_hIA,hG⟩ := actual_avoider_interval_encoding N c L R G hi
  let H := RootPart G (c:ℤ)
  have hroot : Rooted H (c:ℤ) := fun S hS=>(Finset.mem_filter.mp hS).2
  have hHF : H⊆F := (Finset.filter_subset _ _).trans hGF
  have hlegalG : Legal (Ground N) G :=
    ⟨fun S hS=>hlegal.1 S (hGF hS),fun S hS T hT he=>hlegal.2 S (hGF hS) T (hGF hT) he⟩
  have hlegal' : Legal (Ground N) (H∪Intervals I) := hG ▸ hlegalG
  have hr := Terminal36.actual_root_large_with_reservation N c L R H I hc hcL hLR hRN hthin hv hlegal' hroot
  have hs := actual_APSmall_external_avoider N (c:ℤ) F H P hlegal hHF hroot hPF hcP
  have hb := actual_boundary_fringe_count N c L R I hcL hLR hRN hv
  have hp := reserved_card_partition N c L R I hLR hv
  have hd : Disjoint H (Intervals I) := by
    apply Finset.disjoint_left.mpr
    intro S hS hI
    obtain ⟨p,hpI,rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨hcp,_,_,_⟩ := hv p hpI
    have hh := hroot (Interval p) hS
    simp only [Interval,Finset.mem_Icc] at hh
    omega
  have hf : G.card=H.card+I.card := by
    calc
      G.card=(H∪Intervals I).card := congrArg Finset.card hG
      _=H.card+I.card := by rw [Finset.card_union_of_disjoint hd,intervals_card N c L R I hLR hv]
  have hU : (PairUniverse (c:ℤ) (Ground N)).card=(N-1).choose 2 := by
    unfold PairUniverse
    rw [Finset.card_powersetCard,Finset.card_erase_of_mem ((mem_ground _ _).mpr ⟨by omega,by omega⟩),ground_card]
  have hchoose : N.choose 2=(N-1)+(N-1).choose 2 := by
    calc
      N.choose 2=((N-1)+1).choose (1+1) := by congr 1;omega
      _=(N-1).choose 1+(N-1).choose 2 := Nat.choose_succ_succ _ _
      _=(N-1)+(N-1).choose 2 := by simp
  rw [hU] at hr
  have hdiv : (c-1)/2≤c-1 := Nat.div_le_self _ _
  omega

theorem actual_interval_fringe_count (r p N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hr : 0<r) (hp : r<p) (hp3 : 3≤p) (hN : p^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hgeometry : r*p*(L+N-R)≤(p-r)*N)
    (hGF : G⊆F) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈E,¬IsAP S) (hdense : ∀ S∈E,N<r*S.card)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈Avoiders G (c:ℤ),∃ a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) :
    E.card≤JointCount p*((L+N-R)-1) := by
  obtain ⟨H,hHG,hHAP,hKH⟩ := RestoreTerminal35.actual_interval_core_member N c L R G hLR hne hi
  have ho := ground_interval_exterior_card N (by omega : (1:ℤ)≤L)
    (by exact_mod_cast hLR : (L:ℤ)≤R) (by exact_mod_cast hRN : (R:ℤ)≤N)
  have he : (Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card+1=L+N-R := by omega
  have hb := actual_dense_fringe_bound r p N hr hp hp3 hN F E (L:ℤ) (R:ℤ)
    hlegal hEF hbad hdense (by omega) (by exact_mod_cast hLR) (by exact_mod_cast hRN)
    ⟨H,hGF hHG,hHAP,hKH⟩ (by rw [he];exact hgeometry)
  have he' : (Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card=(L+N-R)-1 := by omega
  simpa only [he'] using hb

theorem actual_adaptive_restore (r p N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hr : 0<r) (hp : r<p) (hp3 : 3≤p) (hN : p^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hgeometry : r*p*(L+N-R)≤(p-r)*N)
    (hhalf : 2*(JointCount p+1)*(L+N-R)≤N) (hquarter : 28*(L+N-R)≤N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈E,¬IsAP S) (hdense : ∀ S∈E,N<r*S.card)
    (havoid : ∀ S∈E,(c:ℤ)∉S)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈Avoiders G (c:ℤ),∃ a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  have hGF : G⊆F := by rw [hG];exact Finset.sdiff_subset
  have hGlegal := RestoreTerminal35.retained_legal hG hlegal
  have ht := Terminal36.actual_native_interval_terminal N c L R G hc hcL hLR hRN hthin hGlegal hne hi
  have hcard := deletion_card_exact F E hEF
  rw [←hG] at hcard
  by_cases he : E.Nonempty
  · obtain ⟨P,hPE,hmin⟩ := Finset.exists_min_image E Finset.card he
    by_cases hm : 2*P.card≤N
    · have hd := actual_native_terminal_deficit N c L R F G P hc hcL hLR hRN hthin
        hlegal hGF (hEF hPE) (havoid P hPE) hi
      have hb := actual_interval_fringe_count r p N c L R F G E hr hp hp3 hN hc hcL hLR hRN
        hgeometry hGF hEF hlegal hbad hdense hne hi
      have ht1 : 1≤L+N-R := by omega
      have hmul : JointCount p*((L+N-R)-1)≤JointCount p*(L+N-R) :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have hf : F.card≤N.choose 2 := by nlinarith only [hd,hb,hm,hhalf,hcard,hmul]
      unfold B
      omega
    · have h3 : 3^3≤N := (Nat.pow_le_pow_left hp3 3).trans hN
      have hgeo : 2*3*(L+N-R)≤(3-2)*N := by omega
      have hd2 : ∀ S∈E,N<2*S.card := by
        intro S hS
        have hs := hmin S hS
        omega
      have hb := actual_interval_fringe_count 2 3 N c L R F G E (by decide) (by decide)
        (by decide) h3 hc hcL hLR hRN hgeo hGF hEF hlegal hbad hd2 hne hi
      have hj : JointCount 3=7 := by norm_num [JointCount,ShortCount,Finset.sum_Icc_succ_top]
      rw [hj] at hb
      have hpay := quarter_payment 7 N (L+N-R) (by omega) (by simpa using hquarter)
      unfold B
      omega
  · have hE : E=∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [hE,Finset.card_empty,add_zero] at hcard
    unfold B
    omega

def OmittedAvoiders (N r : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) : Finset (Finset ℤ) :=
  (Deleted N r F).filter (fun S=>c∉S)

theorem actual_avoider_readdition (N r : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) :
    Avoiders (F\OmittedAvoiders N r F c) c=Avoiders (Retained N r F) c := by
  ext S
  simp only [Avoiders,OmittedAvoiders,Retained,Finset.mem_filter,Finset.mem_sdiff]
  tauto

theorem actual_deleted_avoider_restore (r p N c L R : ℕ) (F : Finset (Finset ℤ))
    (hr : 0<r) (hp : r<p) (hp3 : 3≤p) (hN : p^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hgeometry : r*p*(L+N-R)≤(p-r)*N)
    (hhalf : 2*(JointCount p+1)*(L+N-R)≤N) (hquarter : 28*(L+N-R)≤N)
    (hlegal : Legal (Ground N) F) (hne : (Avoiders (Retained N r F) (c:ℤ)).Nonempty)
    (hi : ∀ S∈Avoiders (Retained N r F) (c:ℤ),∃ a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  let E := OmittedAvoiders N r F (c:ℤ)
  have hEF : E⊆F := (Finset.filter_subset _ _).trans (actual_deleted_subset N r F)
  have ha := actual_avoider_readdition N r F (c:ℤ)
  apply actual_adaptive_restore r p N c L R F (F\E) E hr hp hp3 hN hc hcL hLR hRN hthin
    hgeometry hhalf hquarter rfl hEF hlegal
  · intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  · intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.2
  · intro S hS
    exact (Finset.mem_filter.mp hS).2
  · simpa only [E,ha] using hne
  · simpa only [E,ha] using hi

#print axioms actual_uniform_totient_seven
#print axioms actual_long_core_totient_supply_seven
#print axioms actual_normalized_cutoff_seven
#print axioms actual_coprime_prefix_core_seven
#print axioms actual_APSmall_external_avoider
#print axioms actual_boundary_fringe_count
#print axioms actual_native_terminal_deficit
#print axioms actual_interval_fringe_count
#print axioms actual_adaptive_restore
#print axioms actual_avoider_readdition
#print axioms actual_deleted_avoider_restore
end
end JSP233.TerminalDeficit51
