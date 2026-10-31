import Erdos272.Capacity.AnchorCapacity33
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact gcd-cell counts in actual anchored integer intervals. -/
namespace JSP233.DivisorCells34
open AnchorCapacity33
open scoped Classical BigOperators
noncomputable section

def CoprimeSegment (q M : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (q*M)).filter (fun k => q.Coprime k)

def PositiveNatCell (g M d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (g*M)).filter (fun k => Nat.gcd k g=d)

def NatCell (g M d : ℕ) : Finset ℕ :=
  (Finset.Icc 0 (g*M)).filter (fun k => Nat.gcd k g=d)

def Cell (u : ℤ) (g M d : ℕ) : Finset ℤ :=
  (Finset.Icc u (u+((g*M:ℕ):ℤ))).filter (fun x => Int.gcd (x-u) (g:ℤ)=d)

theorem coprime_periods_card (q M : ℕ) :
    ((Finset.Ico 1 (1+q*M)).filter (fun k => q.Coprime k)).card=M*Nat.totient q := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hI := Finset.Ico_union_Ico_eq_Ico (show 1≤1+q*M by omega)
      (show 1+q*M≤1+q*M+q by omega)
    have hdis : Disjoint
        ((Finset.Ico 1 (1+q*M)).filter (fun k => q.Coprime k))
        ((Finset.Ico (1+q*M) (1+q*M+q)).filter (fun k => q.Coprime k)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      have hx' := Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1
      have hy' := Finset.mem_Ico.mp (Finset.mem_filter.mp hy).1
      omega
    rw [Nat.mul_succ,show 1+(q*M+q)=1+q*M+q by omega,←hI,
      Finset.filter_union,Finset.card_union_of_disjoint hdis,ih,
      Nat.filter_coprime_Ico_eq_totient]
    ring

theorem coprimeSegment_card (q M : ℕ) :
    (CoprimeSegment q M).card=M*Nat.totient q := by
  have he : Finset.Icc 1 (q*M)=Finset.Ico 1 (1+q*M) := by
    ext x
    simp only [Finset.mem_Icc,Finset.mem_Ico]
    omega
  simpa only [CoprimeSegment,he] using coprime_periods_card q M

theorem gcd_scaled_eq_iff (d q k : ℕ) (hd : 0<d) :
    Nat.gcd (d*k) (d*q)=d ↔ q.Coprime k := by
  rw [Nat.gcd_mul_left]
  constructor
  · intro he
    have hcop : Nat.gcd k q=1 := by nlinarith
    exact Nat.coprime_comm.mpr hcop
  · intro hc
    rw [Nat.coprime_comm.mp hc]
    omega

theorem positiveNatCell_eq_scaled (g M d : ℕ) (_hg : 0<g) (hd : 0<d) (hdg : d∣g) :
    PositiveNatCell g M d=(CoprimeSegment (g/d) M).image (fun k => d*k) := by
  have hgq : d*(g/d)=g := Nat.mul_div_cancel' hdg
  ext x
  simp only [PositiveNatCell,CoprimeSegment,Finset.mem_filter,Finset.mem_Icc,Finset.mem_image]
  constructor
  · rintro ⟨⟨hx1,hxM⟩,hxg⟩
    have hdx : d∣x := by rw [←hxg]; exact Nat.gcd_dvd_left x g
    have hxe : d*(x/d)=x := Nat.mul_div_cancel' hdx
    have hq : Nat.Coprime (g/d) (x/d) := by
      apply (gcd_scaled_eq_iff d (g/d) (x/d) hd).mp
      rwa [hxe,hgq]
    refine ⟨x/d,⟨⟨?_,?_⟩,hq⟩,hxe⟩
    · have hh := Nat.le_of_dvd hx1 hdx
      exact Nat.div_pos hh hd
    · have hh : d*(x/d)≤d*((g/d)*M) := by
        simpa only [hxe,←Nat.mul_assoc,hgq] using hxM
      exact Nat.le_of_mul_le_mul_left hh hd
  · rintro ⟨k,⟨⟨hk1,hkM⟩,hcop⟩,rfl⟩
    refine ⟨⟨by nlinarith,?_⟩,?_⟩
    · have hh := Nat.mul_le_mul_left d hkM
      simpa only [←Nat.mul_assoc,hgq] using hh
    · rw [←hgq]
      exact (gcd_scaled_eq_iff d (g/d) k hd).mpr hcop

theorem positiveNatCell_card (g M d : ℕ) (hg : 0<g) (hd : 0<d) (hdg : d∣g) :
    (PositiveNatCell g M d).card=M*Nat.totient (g/d) := by
  rw [positiveNatCell_eq_scaled g M d hg hd hdg,Finset.card_image_of_injective]
  · exact coprimeSegment_card (g/d) M
  · intro a b he
    exact Nat.eq_of_mul_eq_mul_left hd he

theorem natCell_eq_positive (g M d : ℕ) :
    NatCell g M d=if d=g then insert 0 (PositiveNatCell g M d) else PositiveNatCell g M d := by
  ext x
  split_ifs with he
  · simp only [NatCell,PositiveNatCell,Finset.mem_filter,Finset.mem_Icc,Finset.mem_insert]
    by_cases hx : x=0
    · subst x; simp [he]
    · constructor
      · rintro ⟨⟨_,hxM⟩,hxg⟩
        exact Or.inr ⟨⟨by omega,hxM⟩,hxg⟩
      · rintro (hzero | ⟨⟨h1,hM⟩,hgd⟩)
        · exact False.elim (hx hzero)
        · exact ⟨⟨by omega,hM⟩,hgd⟩
  · simp only [NatCell,PositiveNatCell,Finset.mem_filter,Finset.mem_Icc]
    constructor
    · rintro ⟨⟨_,hxM⟩,hxg⟩
      have hx : x≠0 := by intro hz; subst x; simp only [Nat.gcd_zero_left] at hxg; exact he hxg.symm
      exact ⟨⟨by omega,hxM⟩,hxg⟩
    · rintro ⟨⟨_,hxM⟩,hxg⟩
      exact ⟨⟨by omega,hxM⟩,hxg⟩

theorem natCell_card (g M d : ℕ) (hg : 0<g) (hd : 0<d) (hdg : d∣g) :
    (NatCell g M d).card=M*Nat.totient (g/d)+(if d=g then 1 else 0) := by
  rw [natCell_eq_positive]
  split_ifs with he
  · rw [Finset.card_insert_of_notMem (by simp [PositiveNatCell]),positiveNatCell_card g M d hg hd hdg]
  · rw [positiveNatCell_card g M d hg hd hdg]
    omega

theorem natCell_proper_card (g M d : ℕ) (hg : 0<g) (hd : 0<d) (hdg : d∣g) (hne : d≠g) :
    (NatCell g M d).card=M*Nat.totient (g/d) := by
  simpa only [if_neg hne,add_zero] using natCell_card g M d hg hd hdg

theorem natCell_anchor_card (g M : ℕ) (hg : 0<g) :
    (NatCell g M g).card=M+1 := by
  simpa [Nat.div_self hg] using natCell_card g M g hg hg (dvd_refl g)

theorem mem_natCell (g M d k : ℕ) :
    k∈NatCell g M d ↔ k≤g*M ∧ Nat.gcd k g=d := by
  simp [NatCell]

theorem mem_cell (u x : ℤ) (g M d : ℕ) :
    x∈Cell u g M d ↔ u≤x ∧ x≤u+((g*M:ℕ):ℤ) ∧ Int.gcd (x-u) (g:ℤ)=d := by
  simp [Cell,and_assoc]

theorem cell_eq_nat_image (u : ℤ) (g M d : ℕ) :
    Cell u g M d=(NatCell g M d).image (fun k : ℕ => u+(k:ℤ)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hux,hxv,hgcd⟩ := (mem_cell u x g M d).mp hx
    let k := (x-u).toNat
    have hk : (k:ℤ)=x-u := Int.toNat_of_nonneg (by omega)
    have hkM : k≤g*M := by exact_mod_cast (show (k:ℤ)≤((g*M:ℕ):ℤ) by omega)
    have hkgcd : Nat.gcd k g=d := by
      rw [←Int.gcd_natCast_natCast,hk]
      exact hgcd
    exact Finset.mem_image.mpr ⟨k,(mem_natCell g M d k).mpr ⟨hkM,hkgcd⟩,by omega⟩
  · intro hx
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hkM,hkgcd⟩ := (mem_natCell g M d k).mp hk
    have hkMZ : (k:ℤ)≤((g*M:ℕ):ℤ) := by exact_mod_cast hkM
    exact (mem_cell u _ g M d).mpr ⟨by omega,by omega,by
      simpa only [add_sub_cancel_left,Int.gcd_natCast_natCast] using hkgcd⟩

theorem cell_card (u : ℤ) (g M d : ℕ) (hg : 0<g) (hd : 0<d) (hdg : d∣g) :
    (Cell u g M d).card=M*Nat.totient (g/d)+(if d=g then 1 else 0) := by
  rw [cell_eq_nat_image,Finset.card_image_of_injective]
  · exact natCell_card g M d hg hd hdg
  · intro a b he
    dsimp at he
    omega

theorem cell_proper_card (u : ℤ) (g M d : ℕ) (hg : 0<g) (hd : 0<d)
    (hdg : d∣g) (hne : d≠g) : (Cell u g M d).card=M*Nat.totient (g/d) := by
  simpa only [if_neg hne,add_zero] using cell_card u g M d hg hd hdg

theorem cell_anchor_card (u : ℤ) (g M : ℕ) (hg : 0<g) :
    (Cell u g M g).card=M+1 := by
  simpa [Nat.div_self hg] using cell_card u g M g hg hg (dvd_refl g)

theorem integer_step_cell_card (u g : ℤ) (M d : ℕ) (hg : 0<g)
    (hd : 0<d) (hdg : d∣g.toNat) :
    ((Finset.Icc u (u+g*(M:ℤ))).filter (fun x => Int.gcd (x-u) g=d)).card=
      M*Nat.totient (g.toNat/d)+(if d=g.toNat then 1 else 0) := by
  have hcast : (g.toNat:ℤ)=g := Int.toNat_of_nonneg hg.le
  have hpos : 0<g.toNat := by omega
  simpa only [Cell,Nat.cast_mul,hcast] using cell_card u g.toNat M d hpos hd hdg

theorem integer_step_proper_cell_card (u g : ℤ) (M d : ℕ) (hg : 0<g)
    (hd : 0<d) (hdg : d∣g.toNat) (hne : d≠g.toNat) :
    ((Finset.Icc u (u+g*(M:ℤ))).filter (fun x => Int.gcd (x-u) g=d)).card=
      M*Nat.totient (g.toNat/d) := by
  simpa only [if_neg hne,add_zero] using integer_step_cell_card u g M d hg hd hdg

theorem cell_anchor_eq_trace (u : ℤ) (g M : ℕ) :
    Cell u g M g=AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ) := by
  ext x
  have hh : Int.gcd (x-u) (g:ℤ)=g ↔ (g:ℤ)∣x-u := by
    simpa using (Int.gcd_eq_natAbs_right_iff_dvd (a:=x-u) (b:=(g:ℤ)))
  simp only [mem_cell,mem_anchorTrace,hh]

theorem anchor_trace_card (u : ℤ) (g M : ℕ) (hg : 0<g) :
    (AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ)).card=M+1 := by
  rw [←cell_anchor_eq_trace]
  exact cell_anchor_card u g M hg

theorem cells_disjoint (u : ℤ) (g M d e : ℕ) (hne : d≠e) :
    Disjoint (Cell u g M d) (Cell u g M e) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hd := ((mem_cell u x g M d).mp hx).2.2
  have he := ((mem_cell u x g M e).mp hy).2.2
  exact hne (hd.symm.trans he)

theorem cell_label_dvd {u x : ℤ} {g M d : ℕ} (hx : x∈Cell u g M d) : d∣g := by
  have he := ((mem_cell u x g M d).mp hx).2.2
  have hh := Int.gcd_dvd_natAbs_right (x-u) (g:ℤ)
  simpa only [he,Int.natAbs_natCast] using hh

theorem cells_partition (u : ℤ) (g M : ℕ) (hg : 0<g) :
    g.divisors.biUnion (Cell u g M)=Finset.Icc u (u+((g*M:ℕ):ℤ)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hxd).1
  · intro hx
    let d := Int.gcd (x-u) (g:ℤ)
    have hxc : x∈Cell u g M d := Finset.mem_filter.mpr ⟨hx,rfl⟩
    exact Finset.mem_biUnion.mpr ⟨d,Nat.mem_divisors.mpr ⟨cell_label_dvd hxc,hg.ne'⟩,hxc⟩

theorem selected_cells_card (u : ℤ) (g M : ℕ) (A : Finset ℕ) (hg : 0<g)
    (hA : A⊆g.divisors) :
    (A.biUnion (Cell u g M)).card=
      M*(∑ d∈A, Nat.totient (g/d))+(if g∈A then 1 else 0) := by
  rw [Finset.card_biUnion (by
    intro d hd e he hne
    exact cells_disjoint u g M d e hne)]
  calc
    (∑ d∈A, (Cell u g M d).card)=
        ∑ d∈A, (M*Nat.totient (g/d)+(if d=g then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact cell_card u g M d hg (Nat.pos_of_mem_divisors (hA hd)) (Nat.dvd_of_mem_divisors (hA hd))
    _=M*(∑ d∈A, Nat.totient (g/d))+(if g∈A then 1 else 0) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum]
      simp

theorem selected_proper_cells_card (u : ℤ) (g M : ℕ) (A : Finset ℕ) (hg : 0<g)
    (hA : A⊆g.divisors) (hgap : g∉A) :
    (A.biUnion (Cell u g M)).card=M*(∑ d∈A, Nat.totient (g/d)) := by
  simpa only [if_neg hgap,add_zero] using selected_cells_card u g M A hg hA

theorem proper_cells_partition (u : ℤ) (g M : ℕ) (hg : 0<g) :
    (g.divisors.erase g).biUnion (Cell u g M)=
      Finset.Icc u (u+((g*M:ℕ):ℤ))\AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ) := by
  rw [←cells_partition u g M hg,←cell_anchor_eq_trace]
  ext x
  constructor
  · intro hx
    obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨d,(Finset.mem_erase.mp hd).2,hxd⟩,
      fun hxg => Finset.disjoint_left.mp (cells_disjoint u g M d g (Finset.mem_erase.mp hd).1) hxd hxg⟩
  · intro hx
    obtain ⟨hxU,hxg⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hxU
    have hne : d≠g := by intro he; subst d; exact hxg hxd
    exact Finset.mem_biUnion.mpr ⟨d,Finset.mem_erase.mpr ⟨hne,hd⟩,hxd⟩

theorem outside_anchor_card (u : ℤ) (g M : ℕ) (hg : 0<g) :
    (Finset.Icc u (u+((g*M:ℕ):ℤ))\AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ)).card=
      M*(∑ d∈g.divisors.erase g, Nat.totient (g/d)) := by
  rw [←proper_cells_partition u g M hg]
  exact selected_proper_cells_card u g M _ hg (Finset.erase_subset _ _) (Finset.notMem_erase _ _)

theorem cell_nonempty (u : ℤ) (g M d : ℕ) (hg : 0<g) (hM : 0<M)
    (hd : d∈g.divisors) : (Cell u g M d).Nonempty := by
  have hdpos := Nat.pos_of_mem_divisors hd
  have hqpos := Nat.div_pos (Nat.le_of_dvd hg (Nat.dvd_of_mem_divisors hd)) hdpos
  have hp := Nat.mul_pos hM (Nat.totient_pos.mpr hqpos)
  apply Finset.card_pos.mp
  rw [cell_card u g M d hg hdpos (Nat.dvd_of_mem_divisors hd)]
  omega

theorem selected_cells_subset_iff (u : ℤ) (g M : ℕ) (A B : Finset ℕ)
    (hg : 0<g) (hM : 0<M) (hA : A⊆g.divisors) :
    A.biUnion (Cell u g M)⊆B.biUnion (Cell u g M) ↔ A⊆B := by
  constructor
  · intro hsub d hd
    obtain ⟨x,hx⟩ := cell_nonempty u g M d hg hM (hA hd)
    obtain ⟨e,he,hxe⟩ := Finset.mem_biUnion.mp (hsub (Finset.mem_biUnion.mpr ⟨d,hd,hx⟩))
    have hdlabel := ((mem_cell u x g M d).mp hx).2.2
    have helabel := ((mem_cell u x g M e).mp hxe).2.2
    have hde : d=e := hdlabel.symm.trans helabel
    exact hde.symm ▸ he
  · intro hsub x hx
    obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨d,hsub hd,hxd⟩

theorem selected_cells_eq_iff (u : ℤ) (g M : ℕ) (A B : Finset ℕ)
    (hg : 0<g) (hM : 0<M) (hA : A⊆g.divisors) (hB : B⊆g.divisors) :
    A.biUnion (Cell u g M)=B.biUnion (Cell u g M) ↔ A=B := by
  constructor
  · intro he
    exact Finset.Subset.antisymm
      ((selected_cells_subset_iff u g M A B hg hM hA).mp (fun x hx => he ▸ hx))
      ((selected_cells_subset_iff u g M B A hg hM hB).mp (fun x hx => he.symm ▸ hx))
  · rintro rfl; rfl

theorem trace_mem_iff_label_dvd {u x : ℤ} {g M d q : ℕ}
    (hx : x∈Cell u g M d) (hqg : q∣g) :
    x∈AnchorTrace u (u+((g*M:ℕ):ℤ)) (q:ℤ) ↔ q∣d := by
  obtain ⟨hux,hxv,hlabel⟩ := (mem_cell u x g M d).mp hx
  have hqZ : (q:ℤ)∣(g:ℤ) := by exact_mod_cast hqg
  have he : q∣d ↔ (q:ℤ)∣x-u := by
    rw [←hlabel,Int.dvd_gcd_iff]
    exact and_iff_left hqZ
  simpa only [mem_anchorTrace,hux,hxv,true_and] using he.symm

theorem anchor_trace_eq_cells (u : ℤ) (g M q : ℕ) (hg : 0<g) (hqg : q∣g) :
    AnchorTrace u (u+((g*M:ℕ):ℤ)) (q:ℤ)=
      (g.divisors.filter (fun d => q∣d)).biUnion (Cell u g M) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hux,hxv,hqx⟩ := (mem_anchorTrace u _ (q:ℤ) x).mp hx
    let d := Int.gcd (x-u) (g:ℤ)
    have hxc : x∈Cell u g M d := (mem_cell u x g M d).mpr ⟨hux,hxv,rfl⟩
    have hd := Nat.mem_divisors.mpr ⟨cell_label_dvd hxc,hg.ne'⟩
    exact Finset.mem_biUnion.mpr ⟨d,Finset.mem_filter.mpr
      ⟨hd,(trace_mem_iff_label_dvd hxc hqg).mp hx⟩,hxc⟩
  · intro hx
    obtain ⟨d,hd,hxc⟩ := Finset.mem_biUnion.mp hx
    exact (trace_mem_iff_label_dvd hxc hqg).mpr (Finset.mem_filter.mp hd).2

#print axioms coprime_periods_card
#print axioms coprimeSegment_card
#print axioms gcd_scaled_eq_iff
#print axioms positiveNatCell_eq_scaled
#print axioms positiveNatCell_card
#print axioms natCell_eq_positive
#print axioms natCell_card
#print axioms natCell_proper_card
#print axioms natCell_anchor_card
#print axioms mem_natCell
#print axioms mem_cell
#print axioms cell_eq_nat_image
#print axioms cell_card
#print axioms cell_proper_card
#print axioms cell_anchor_card
#print axioms integer_step_cell_card
#print axioms integer_step_proper_cell_card
#print axioms cell_anchor_eq_trace
#print axioms anchor_trace_card
#print axioms cells_disjoint
#print axioms cell_label_dvd
#print axioms cells_partition
#print axioms selected_cells_card
#print axioms selected_proper_cells_card
#print axioms proper_cells_partition
#print axioms outside_anchor_card
#print axioms cell_nonempty
#print axioms selected_cells_subset_iff
#print axioms selected_cells_eq_iff
#print axioms trace_mem_iff_label_dvd
#print axioms anchor_trace_eq_cells
end
end JSP233.DivisorCells34
