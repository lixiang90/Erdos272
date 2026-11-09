module

public import Erdos272.Retention.LongTerminal35
public import Erdos272.Traces.CoprimeMiddle36

@[expose] public section

/-! Direct completion geometry for every exterior-corner crooked member.
The first-positive-neighbor gcd determines the actual AP prefix. Interior
hitting makes that prefix reach the core; its tail is forced onto the same
lattice. A certified middle coprime index then fills the complete set, which
contradicts crookedness. The public endpoints construct an intrinsic witness
outside the actual reservation, with no witness premise.
The geometric argument follows the fixed KK source and the round-35 direct
CompletionAt rewrite, adapted to the project's actual finite integer sets. -/
namespace JSP233.ExteriorWitness36
open StarCompletion PrivatePairExistence StepHall33 LongTerminal35
open scoped Classical BigOperators
noncomputable section

def NonExteriorClosed (S : Finset ℤ) (c L R : ℤ) : Prop :=
  ∀ u∈S, ∀ v∈S, ¬ExteriorPair c L R {u,v} →
    ∀ x, CompletionAt c u v x → x∈S

theorem exterior_mem_gt {c L R x : ℤ} {Q : Finset ℤ}
    (hLR : L≤R) (hQ : ExteriorPair c L R Q) (hx : x∈Q) : c<x := by
  obtain ⟨u,v,rfl,hcu,huL,hRv⟩ := hQ
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> omega

theorem pair_not_exterior_upper {c L R a b : ℤ}
    (ha : a≤R) (hb : b≤R) : ¬ExteriorPair c L R {a,b} := by
  rintro ⟨u,v,he,hcu,huL,hRv⟩
  have hv : v=a ∨ v=b := by
    simpa only [Finset.mem_insert,Finset.mem_singleton] using
      (show v∈({a,b}:Finset ℤ) by rw [he]; simp)
  rcases hv with rfl | rfl <;> omega

theorem pair_not_exterior_lower {c L R a b : ℤ}
    (ha : L≤a) (hb : L≤b) : ¬ExteriorPair c L R {a,b} := by
  rintro ⟨u,v,he,hcu,huL,hRv⟩
  have hu : u=a ∨ u=b := by
    simpa only [Finset.mem_insert,Finset.mem_singleton] using
      (show u∈({a,b}:Finset ℤ) by rw [he]; simp)
  rcases hu with rfl | rfl <;> omega

theorem all_intrinsic_exterior_closed {S : Finset ℤ} {c L R : ℤ}
    (hc : c∈S) (hcorner : ∀ Q, IntrinsicPair c S Q → ExteriorPair c L R Q) :
    NonExteriorClosed S c L R := by
  intro u hu v hv hnot x hx
  by_contra hxn
  have hbad3 : ¬IsAP ({c,u,v}:Finset ℤ) := by
    intro hAP
    have hm := completionAt_least hAP (by simp) (by simp) (by simp) hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl <;> contradiction
  have huc : u≠c := by
    intro he; subst u
    exact hbad3 (by simpa using pair_isAP c v)
  have hvc : v≠c := by
    intro he; subst v
    exact hbad3 (by simpa [Finset.pair_comm] using pair_isAP c u)
  have huv : u≠v := by
    intro he; subst v
    exact hbad3 (by simpa [Finset.pair_comm] using pair_isAP c u)
  exact hnot (hcorner {u,v} (intrinsic_pair_of_completion_gap hu hv huc hvc huv hx hxn))

theorem all_intrinsic_exterior_minimum {S : Finset ℤ} {c L R : ℤ}
    (hc : c∈S) (hbad : ¬IsAP S) (hLR : L≤R)
    (hcorner : ∀ Q, IntrinsicPair c S Q → ExteriorPair c L R Q) :
    ∀ x∈S, c≤x := by
  intro x hx
  by_contra hcx
  obtain ⟨a,ha,v,hv,hac,hvc,hav,y,hy,hyn⟩ :=
    crooked_left_neighbor_missing_completion hc hbad ⟨x,hx,by omega⟩
  have hh := hcorner {a,v} (intrinsic_pair_of_completion_gap ha hv (by omega) hvc hav hy hyn)
  have hca := exterior_mem_gt hLR hh (show a∈({a,v}:Finset ℤ) by simp)
  omega

theorem right_neighbor_gcd {S : Finset ℤ} {c a w : ℤ}
    (_ha : a∈S) (hca : c<a) (hnear : ∀ y∈S, c<y → a≤y)
    (hcl : ∀ x, CompletionAt c a w x → x∈S) :
    Int.gcd (a-c) (w-c)=(a-c).natAbs := by
  have had : ((a-c).natAbs:ℤ)=a-c := Int.natAbs_of_nonneg (by omega)
  have hgpos : 0<Int.gcd (a-c) (w-c) := Int.gcd_pos_of_ne_zero_left _ (by omega)
  have hgle : Int.gcd (a-c) (w-c)≤(a-c).natAbs := Int.gcd_le_natAbs_left _ (by omega)
  have hgleZ : (Int.gcd (a-c) (w-c):ℤ)≤(a-c).natAbs := by exact_mod_cast hgle
  have hcomp : CompletionAt c a w (c+(Int.gcd (a-c) (w-c):ℤ)) := by
    unfold CompletionAt Completion
    refine ⟨by omega,by omega,?_⟩
    simp
  have hmem := hcl _ hcomp
  have hh := hnear _ hmem (by omega)
  omega

theorem right_neighbor_fill {S : Finset ℤ} {c a w : ℤ}
    (ha : a∈S) (hca : c<a) (hnear : ∀ y∈S, c<y → a≤y)
    (hcl : ∀ x, CompletionAt c a w x → x∈S) :
    ((a-c).natAbs:ℤ)∣w-c ∧
      ∀ x, c≤x → x≤w → ((a-c).natAbs:ℤ)∣x-c → x∈S := by
  have hg := right_neighbor_gcd ha hca hnear hcl
  refine ⟨by simpa only [hg] using Int.gcd_dvd_right (a-c) (w-c),?_⟩
  intro x hcx hxw hdx
  apply hcl x
  unfold CompletionAt Completion
  exact ⟨by omega,by omega,by simpa only [hg] using hdx⟩

theorem closed_at_right_neighbor_isAP {S : Finset ℤ} {c a : ℤ}
    (hc : c∈S) (ha : a∈S) (hca : c<a)
    (hnear : ∀ y∈S, c<y → a≤y)
    (hcl : ∀ w∈S, ∀ x, CompletionAt c a w x → x∈S) : IsAP S := by
  let d := (a-c).natAbs
  have hd : (0:ℤ)<d := by
    have hh := Int.natAbs_of_nonneg (by omega : 0≤a-c)
    dsimp [d]
    omega
  have hg : ∀ w∈S, Int.gcd (a-c) (w-c)=d := fun w hw =>
    right_neighbor_gcd ha hca hnear (hcl w hw)
  have hne : S.Nonempty := ⟨c,hc⟩
  let lo := S.min' hne
  let hi := S.max' hne
  have hlo : lo∈S := Finset.min'_mem S hne
  have hhi : hi∈S := Finset.max'_mem S hne
  have hlo0 : lo≤c := Finset.min'_le S c hc
  have hhi0 : c≤hi := Finset.le_max' S c hc
  have hhia : a≤hi := Finset.le_max' S a ha
  have hhlo := hg lo hlo
  have hhhi := hg hi hhi
  refine ⟨d,c,hd,lo,hi,?_,hc⟩
  intro x
  constructor
  · intro hx
    exact ⟨Finset.min'_le S x hx,Finset.le_max' S x hx,by
      simpa only [hg x hx] using Int.gcd_dvd_right (a-c) (x-c)⟩
  · rintro ⟨hlx,hxh,hdx⟩
    by_cases hxc : x≤c
    · apply hcl lo hlo x
      unfold CompletionAt Completion
      exact ⟨by omega,by omega,by simpa only [hhlo] using hdx⟩
    · apply hcl hi hhi x
      unfold CompletionAt Completion
      exact ⟨by omega,by omega,by simpa only [hhhi] using hdx⟩

theorem actual_right_neighbor {S : Finset ℤ} {c : ℤ} (hc : c∈S) (hbad : ¬IsAP S)
    (hmin : ∀ x∈S, c≤x) :
    ∃ a∈S, c<a ∧ ∀ x∈S, c<x → a≤x := by
  have hnon : ∃ x∈S, c<x := by
    by_contra hh
    have he : S={c} := by
      ext x
      simp only [Finset.mem_singleton]
      constructor
      · intro hx
        have hm := hmin x hx
        by_contra he
        exact hh ⟨x,hx,by omega⟩
      · rintro rfl; exact hc
    exact hbad (he ▸ singleton_isAP c)
  let B := S.filter (fun x => c<x)
  have hB : B.Nonempty := by
    obtain ⟨x,hx,hcx⟩ := hnon
    exact ⟨x,Finset.mem_filter.mpr ⟨hx,hcx⟩⟩
  let a := B.min' hB
  obtain ⟨ha,hca⟩ := Finset.mem_filter.mp (Finset.min'_mem B hB)
  exact ⟨a,ha,hca,fun x hx hcx => Finset.min'_le B x (Finset.mem_filter.mpr ⟨hx,hcx⟩)⟩

theorem right_neighbor_below_core {S : Finset ℤ} {c L R a : ℤ}
    (hc : c∈S) (hbad : ¬IsAP S) (ha : a∈S) (hca : c<a)
    (hnear : ∀ y∈S, c<y → a≤y) (hmin : ∀ x∈S, c≤x) (hLR : L≤R)
    (hclosed : NonExteriorClosed S c L R) : a<L := by
  by_contra haL
  apply hbad (closed_at_right_neighbor_isAP hc ha hca hnear ?_)
  intro w hw x hx
  apply hclosed a ha w hw _ x hx
  by_cases hwc : w=c
  · subst w
    intro hE
    have hh := exterior_mem_gt hLR hE (by simp : c∈({a,c}:Finset ℤ))
    omega
  · have hcw : c<w := by have := hmin w hw; omega
    exact pair_not_exterior_lower (by omega) (le_trans (by omega) (hnear w hw hcw))

structure PrefixGrid (S : Finset ℤ) (c R : ℤ) (d : ℕ) (z : ℤ) : Prop where
  step_pos : 0<d
  top_gt : c<z
  top_le : z≤R
  top_mem : z∈S
  prefix_dvd : ∀ x∈S, x≤R → (d:ℤ)∣x-c
  prefix_le : ∀ x∈S, x≤R → x≤z
  fill : ∀ x, c≤x → x≤z → (d:ℤ)∣x-c → x∈S

theorem exterior_actual_prefix {S : Finset ℤ} {c L R : ℤ}
    (hc : c∈S) (hbad : ¬IsAP S) (hLR : L≤R)
    (hcorner : ∀ Q, IntrinsicPair c S Q → ExteriorPair c L R Q) :
    ∃ d : ℕ, ∃ z : ℤ, (d:ℤ)<L-c ∧ PrefixGrid S c R d z ∧ ∃ v∈S, R<v := by
  have hmin := all_intrinsic_exterior_minimum hc hbad hLR hcorner
  have hclosed := all_intrinsic_exterior_closed hc hcorner
  obtain ⟨a,ha,hca,hnear⟩ := actual_right_neighbor hc hbad hmin
  have haL := right_neighbor_below_core hc hbad ha hca hnear hmin hLR hclosed
  let d := (a-c).natAbs
  have had : (d:ℤ)=a-c := Int.natAbs_of_nonneg (by omega)
  have hdZ : (0:ℤ)<d := by omega
  have hd : 0<d := by exact_mod_cast hdZ
  let P := S.filter (fun x => x≤R)
  have haP : a∈P := Finset.mem_filter.mpr ⟨ha,by omega⟩
  have hP : P.Nonempty := ⟨a,haP⟩
  let z := P.max' hP
  obtain ⟨hzS,hzR⟩ := Finset.mem_filter.mp (Finset.max'_mem P hP)
  have haz : a≤z := Finset.le_max' P a haP
  have hwfill : ∀ w∈S, w≤R → (d:ℤ)∣w-c ∧
      ∀ x, c≤x → x≤w → (d:ℤ)∣x-c → x∈S := by
    intro w hw hwR
    exact right_neighbor_fill ha hca hnear
      (hclosed a ha w hw (pair_not_exterior_upper (by omega) hwR))
  have hprefix : PrefixGrid S c R d z :=
    ⟨hd,by omega,hzR,hzS,fun w hw hwR => (hwfill w hw hwR).1,
      fun w hw hwR => Finset.le_max' P w (Finset.mem_filter.mpr ⟨hw,hwR⟩),
      (hwfill z hzS hzR).2⟩
  refine ⟨d,z,by omega,hprefix,?_⟩
  by_contra hnone
  have hall : ∀ x∈S, x≤R := by
    intro x hx
    by_contra hh
    exact hnone ⟨x,hx,by omega⟩
  apply hbad
  refine ⟨d,c,hdZ,c,z,?_,hc⟩
  intro x
  constructor
  · intro hx
    exact ⟨hmin x hx,hprefix.prefix_le x hx (hall x hx),hprefix.prefix_dvd x hx (hall x hx)⟩
  · rintro ⟨hcx,hxz,hdx⟩
    exact hprefix.fill x hcx hxz hdx

theorem distant_consecutive_intrinsic {S : Finset ℤ} {c z v : ℤ}
    (_hc : c∈S) (hz : z∈S) (hv : v∈S) (hcz : c<z) (hzv : z<v)
    (hcon : ∀ x∈S, ¬(z<x ∧ x<v)) (hgap : 2*z<c+v) : IntrinsicPair c S {z,v} := by
  let g := Int.gcd (z-c) (v-c)
  have hgpos : (0:ℤ)<g := by
    have hh := Int.gcd_pos_of_ne_zero_left (v-c) (by omega : z-c≠0)
    exact_mod_cast hh
  have hgle : (g:ℤ)≤z-c := by
    have hh := Int.gcd_le_natAbs_left (v-c) (by omega : z-c≠0)
    have hzabs : ((z-c).natAbs:ℤ)=z-c := Int.natAbs_of_nonneg (by omega)
    have hcast : (g:ℤ)≤((z-c).natAbs:ℤ) := by exact_mod_cast hh
    omega
  have hgp : (g:ℤ)∣z-c := Int.gcd_dvd_left (z-c) (v-c)
  have hmiss : z+(g:ℤ)∉S := by
    intro hh
    exact hcon _ hh ⟨by omega,by omega⟩
  apply intrinsic_pair_of_completion_gap hz hv (by omega) (by omega) (by omega) _ hmiss
  unfold CompletionAt Completion
  refine ⟨by omega,by omega,?_⟩
  change (g:ℤ)∣z+(g:ℤ)-c
  rw [show z+(g:ℤ)-c=(z-c)+(g:ℤ) by omega]
  exact dvd_add hgp (dvd_refl _)

theorem actual_prefix_reaches_core {S : Finset ℤ} {c L R z : ℤ} {d : ℕ}
    (hc : c∈S) (hp : PrefixGrid S c R d z) (htail : ∃ v∈S, R<v)
    (hwide : 2*L≤R+c)
    (hbetween : ∀ u v : ℤ, u<v → IntrinsicPair c S {u,v} → ∃ x∈S, u<x ∧ x<v) :
    L≤z := by
  by_contra hzL
  let B := S.filter (fun v => R<v)
  have hB : B.Nonempty := by
    obtain ⟨v,hv,hRv⟩ := htail
    exact ⟨v,Finset.mem_filter.mpr ⟨hv,hRv⟩⟩
  let v := B.min' hB
  obtain ⟨hvS,hRv⟩ := Finset.mem_filter.mp (Finset.min'_mem B hB)
  have hzv : z<v := by have := hp.top_le; omega
  have hcon : ∀ x∈S, ¬(z<x ∧ x<v) := by
    intro x hx hbetween
    by_cases hxR : x≤R
    · have hh := hp.prefix_le x hx hxR
      omega
    · have hh := Finset.min'_le B x (Finset.mem_filter.mpr ⟨hx,by omega⟩)
      omega
  have hgap : 2*z<c+v := by omega
  have hI := distant_consecutive_intrinsic hc hp.top_mem hvS hp.top_gt hzv hcon hgap
  obtain ⟨x,hx,hzx,hxv⟩ := hbetween z v hzv hI
  exact hcon x hx ⟨hzx,hxv⟩

theorem actual_prefix_tail_grid {S : Finset ℤ} {c L R z v : ℤ} {d : ℕ}
    (hp : PrefixGrid S c R d z) (_hmin : ∀ x∈S, c≤x)
    (hzL : L≤z) (hvS : v∈S) (hRv : R<v)
    (hclosed : NonExteriorClosed S c L R) :
    (d:ℤ)∣v-c ∧ R+c<2*z := by
  have hcz := hp.top_gt
  have hzR := hp.top_le
  have hzv : z<v := lt_of_le_of_lt hp.top_le hRv
  have hcl : ∀ x, CompletionAt c z v x → x∈S :=
    hclosed z hp.top_mem v hvS (pair_not_exterior_lower hzL (by omega))
  let g := Int.gcd (z-c) (v-c)
  have hgpos : (0:ℤ)<g := by
    have hh := Int.gcd_pos_of_ne_zero_left (v-c) (by have := hp.top_gt; omega : z-c≠0)
    exact_mod_cast hh
  have hgle : (g:ℤ)≤z-c := by
    have hh := Int.gcd_le_natAbs_left (v-c) (by have := hp.top_gt; omega : z-c≠0)
    have hzabs : ((z-c).natAbs:ℤ)=z-c := Int.natAbs_of_nonneg (by have := hp.top_gt; omega)
    have hcast : (g:ℤ)≤((z-c).natAbs:ℤ) := by exact_mod_cast hh
    omega
  have hgS : c+(g:ℤ)∈S := by
    apply hcl
    unfold CompletionAt Completion
    refine ⟨by have := hp.top_gt; omega,by omega,?_⟩
    change (g:ℤ)∣c+(g:ℤ)-c
    simp
  have hdg : (d:ℤ)∣(g:ℤ) := by
    simpa only [add_sub_cancel_left] using hp.prefix_dvd _ hgS (by have := hp.top_le; omega)
  have hgv : (g:ℤ)∣v-c := Int.gcd_dvd_right (z-c) (v-c)
  have hgz : (g:ℤ)∣z-c := Int.gcd_dvd_left (z-c) (v-c)
  have hnext : z+(g:ℤ)≤v := by
    have hgapdiv : (g:ℤ)∣v-z := by
      rw [show v-z=(v-c)-(z-c) by omega]
      exact dvd_sub hgv hgz
    have hh := Int.le_of_dvd (by omega : 0<v-z) hgapdiv
    omega
  have hnS : z+(g:ℤ)∈S := by
    apply hcl
    unfold CompletionAt Completion
    refine ⟨by have := hp.top_gt; omega,by omega,?_⟩
    change (g:ℤ)∣z+(g:ℤ)-c
    rw [show z+(g:ℤ)-c=(z-c)+(g:ℤ) by omega]
    exact dvd_add hgz (dvd_refl _)
  have hRnext : R<z+(g:ℤ) := by
    by_contra hh
    have hbound := hp.prefix_le _ hnS (by omega)
    omega
  exact ⟨hdg.trans hgv,by omega⟩

theorem nat_grid_index {c x : ℤ} {d : ℕ} (hd : 0<d) (hcx : c≤x) (hdiv : (d:ℤ)∣x-c) :
    ∃ k : ℕ, x=c+(k:ℤ)*d := by
  obtain ⟨k,hk⟩ := hdiv
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  have hk0 : 0≤k := by nlinarith
  refine ⟨k.toNat,?_⟩
  rw [Int.toNat_of_nonneg hk0]
  nlinarith

theorem coprime_grid_gcd (c : ℤ) (d j m : ℕ) (hcop : Nat.Coprime j m) :
    Int.gcd ((c+(j:ℤ)*d)-c) ((c+(m:ℤ)*d)-c)=d := by
  simp only [add_sub_cancel_left,Int.gcd_mul_right,Int.gcd_natCast_natCast,
    hcop.gcd_eq_one,Int.natAbs_natCast,one_mul]

theorem completed_maximum_grid_isAP {S : Finset ℤ} {c u v : ℤ} {d : ℕ}
    (hc : c∈S) (hd : 0<d) (hcu : c≤u) (huv : u≤v)
    (hmin : ∀ x∈S, c≤x) (hmax : ∀ x∈S, x≤v)
    (hgrid : ∀ x∈S, (d:ℤ)∣x-c) (hgcd : Int.gcd (u-c) (v-c)=d)
    (hcl : ∀ x, CompletionAt c u v x → x∈S) : IsAP S := by
  refine ⟨d,c,by exact_mod_cast hd,c,v,?_,hc⟩
  intro x
  constructor
  · intro hx; exact ⟨hmin x hx,hmax x hx,hgrid x hx⟩
  · rintro ⟨hcx,hxv,hdx⟩
    apply hcl x
    unfold CompletionAt Completion
    exact ⟨by omega,by omega,by simpa only [hgcd] using hdx⟩

theorem exterior_intrinsic_contradiction {N c L R : ℕ} {S : Finset ℤ}
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hsub : S⊆Ground N) (hc : (c:ℤ)∈S) (hbad : ¬IsAP S)
    (hcorner : ∀ Q, IntrinsicPair (c:ℤ) S Q → ExteriorPair (c:ℤ) (L:ℤ) (R:ℤ) Q)
    (hbetween : ∀ u v : ℤ, u<v → IntrinsicPair (c:ℤ) S {u,v} →
      ∃ x∈S, u<x ∧ x<v) : False := by
  have hLRZ : (L:ℤ)≤R := by exact_mod_cast hLR
  have hmin := all_intrinsic_exterior_minimum hc hbad hLRZ hcorner
  have hclosed := all_intrinsic_exterior_closed hc hcorner
  obtain ⟨d,z,hdL,hp,htail⟩ := exterior_actual_prefix hc hbad hLRZ hcorner
  have hwide : 2*(L:ℤ)≤(R:ℤ)+c := by
    exact_mod_cast CoprimeMiddle36.thin_core_wide N c L R hcL hLR hRN hthin
  have hzL := actual_prefix_reaches_core hc hp htail hwide hbetween
  have hgrid : ∀ x∈S, (d:ℤ)∣x-c := by
    intro x hx
    by_cases hxR : x≤(R:ℤ)
    · exact hp.prefix_dvd x hx hxR
    · exact (actual_prefix_tail_grid hp hmin hzL hx (by omega) hclosed).1
  have hne : S.Nonempty := ⟨c,hc⟩
  let v := S.max' hne
  have hvS : v∈S := Finset.max'_mem S hne
  have hmax : ∀ x∈S, x≤v := fun x hx => Finset.le_max' S x hx
  have hRv : (R:ℤ)<v := by
    obtain ⟨w,hw,hRw⟩ := htail
    have hh := hmax w hw
    omega
  have hvN : v≤N := ((mem_ground N v).mp (hsub hvS)).2
  obtain ⟨h,hzeq⟩ := nat_grid_index hp.step_pos hp.top_gt.le (hp.prefix_dvd z hp.top_mem hp.top_le)
  obtain ⟨m,hveq⟩ := nat_grid_index hp.step_pos (hmin v hvS) (hgrid v hvS)
  have hdNatL : d≤L := by exact_mod_cast (show (d:ℤ)≤L by omega)
  have hmR : R<c+m*d := by
    exact_mod_cast (show (R:ℤ)<(c:ℤ)+(m:ℤ)*d by omega)
  have hmN : c+m*d≤N := by
    exact_mod_cast (show (c:ℤ)+(m:ℤ)*d≤N by omega)
  have hhalf : R+c<2*(c+h*d) := by
    have hh := (actual_prefix_tail_grid hp hmin hzL hvS hRv hclosed).2
    exact_mod_cast (show (R:ℤ)+c<2*((c:ℤ)+(h:ℤ)*d) by omega)
  obtain ⟨j,hjL,hjh,hcop⟩ := CoprimeMiddle36.exists_coprime_in_prefix_core
    hcL hLR hRN hp.step_pos hdNatL hthin hmR hmN hhalf
  let u : ℤ := c+(j:ℤ)*d
  have huL : (L:ℤ)≤u := by dsimp [u]; exact_mod_cast hjL
  have hcu : (c:ℤ)≤u := by dsimp [u]; exact le_add_of_nonneg_right (by positivity)
  have huz : u≤z := by
    have hm := Nat.mul_le_mul_right d hjh
    have hmZ : (j:ℤ)*d≤(h:ℤ)*d := by exact_mod_cast hm
    dsimp [u]
    omega
  have huS : u∈S := hp.fill u hcu huz ⟨(j:ℤ),by dsimp [u]; ring⟩
  have huv : u≤v := hmax u huS
  have hgcd : Int.gcd (u-c) (v-c)=d := by
    rw [hveq]
    exact coprime_grid_gcd (c:ℤ) d j m hcop
  have hcl : ∀ x, CompletionAt (c:ℤ) u v x → x∈S :=
    hclosed u huS v hvS (pair_not_exterior_lower huL (by omega))
  exact hbad (completed_maximum_grid_isAP hc hp.step_pos hcu huv hmin hmax hgrid hgcd hcl)

theorem exists_intrinsic_outside_exterior {N c L R : ℕ} {S : Finset ℤ}
    {W : Finset (Finset ℤ)} (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hsub : S⊆Ground N) (hc : (c:ℤ)∈S) (hbad : ¬IsAP S)
    (hW : ∀ Q∈W, ExteriorPair (c:ℤ) (L:ℤ) (R:ℤ) Q)
    (hbetween : ∀ u v : ℤ, u<v → ({u,v}:Finset ℤ)∈W → ∃ x∈S, u<x ∧ x<v) :
    ∃ Q, IntrinsicPair (c:ℤ) S Q ∧ Q∉W := by
  by_contra hnone
  have hin : ∀ Q, IntrinsicPair (c:ℤ) S Q → Q∈W := by
    intro Q hQ
    by_contra hh
    exact hnone ⟨Q,hQ,hh⟩
  exact exterior_intrinsic_contradiction hcL hLR hRN hthin hsub hc hbad
    (fun Q hQ => hW Q (hin Q hQ))
    (fun u v huv hQ => hbetween u v huv (hin {u,v} hQ))

theorem actual_reserved_avoiding_intrinsic (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hv : ValidIntervals N c L R I) (hlegal : Legal (Ground N) (H∪Intervals I))
    (hroot : Rooted H (c:ℤ)) {S : Finset ℤ} (hS : S∈H) (hbad : ¬IsAP S) :
    ∃ Q, IntrinsicPair (c:ℤ) S Q ∧ Q∉Reserved c N I := by
  exact exists_intrinsic_outside_exterior hcL hLR hRN hthin
    (hlegal.1 S (Finset.mem_union_left _ hS)) (hroot S hS) hbad
    (fun Q hQ => (reserved_geometry N c L R I hc hLR hv hQ).2)
    (fun u v huv hQ => legal_root_interval_between N c L R H I hLR hv hlegal hroot hS huv hQ)

theorem actual_crooked_reserved_avoiding_witnesses (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hv : ValidIntervals N c L R I) (hlegal : Legal (Ground N) (H∪Intervals I))
    (hroot : Rooted H (c:ℤ)) : CrookedWitnesses (c:ℤ) H (Reserved c N I) := by
  intro S hS hbad
  exact actual_reserved_avoiding_intrinsic N c L R H I hc hcL hLR hRN hthin hv hlegal hroot hS hbad

#print axioms exterior_mem_gt
#print axioms pair_not_exterior_upper
#print axioms pair_not_exterior_lower
#print axioms all_intrinsic_exterior_closed
#print axioms all_intrinsic_exterior_minimum
#print axioms right_neighbor_gcd
#print axioms right_neighbor_fill
#print axioms closed_at_right_neighbor_isAP
#print axioms actual_right_neighbor
#print axioms right_neighbor_below_core
#print axioms exterior_actual_prefix
#print axioms distant_consecutive_intrinsic
#print axioms actual_prefix_reaches_core
#print axioms actual_prefix_tail_grid
#print axioms nat_grid_index
#print axioms coprime_grid_gcd
#print axioms completed_maximum_grid_isAP
#print axioms exterior_intrinsic_contradiction
#print axioms exists_intrinsic_outside_exterior
#print axioms actual_reserved_avoiding_intrinsic
#print axioms actual_crooked_reserved_avoiding_witnesses
end
end JSP233.ExteriorWitness36
