module

public import Erdos272.Global.PreparedClasses50

@[expose] public section

/-! Actual primitive witnesses and centered integer models in the middle region. -/
namespace JSP233.MiddleCoordinates51
open StarCompletion APGeometry APCount41 APPrepare49 PreparedWitness48 PreparedClasses50
open LongTerminal35 WitnessInterval43
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

def CenteredGrid (c d a b : ℕ) : Finset ℤ :=
  (Finset.Icc (-(a:ℤ)) (b:ℤ)).image (fun z=>(c:ℤ)+(d:ℤ)*z)

def CenterModel (S : Finset ℤ) (c d a b : ℕ) : Prop := S=CenteredGrid c d a b

theorem mem_centered_grid {c d a b : ℕ} {x : ℤ} :
    x∈CenteredGrid c d a b ↔ ∃z:ℤ,-(a:ℤ)≤z ∧ z≤(b:ℤ) ∧ (c:ℤ)+(d:ℤ)*z=x := by
  simp only [CenteredGrid,Finset.mem_image,Finset.mem_Icc]
  aesop

theorem centered_grid_root_mem (c d a b : ℕ) : (c:ℤ)∈CenteredGrid c d a b := by
  apply mem_centered_grid.mpr
  exact ⟨0,by omega,by omega,by ring⟩

theorem centered_grid_positive_mem {c d a b k : ℕ} (hk : k≤b) :
    (c:ℤ)+(k:ℤ)*d∈CenteredGrid c d a b := by
  exact mem_centered_grid.mpr ⟨k,by omega,by exact_mod_cast hk,by ring⟩

theorem centered_grid_negative_mem {c d a b k : ℕ} (hk : k≤a) :
    (c:ℤ)-(k:ℤ)*d∈CenteredGrid c d a b := by
  exact mem_centered_grid.mpr ⟨-(k:ℤ),by omega,by omega,by ring⟩

theorem centered_grid_isAP {c d a b : ℕ} (hd : 0<d) : IsAP (CenteredGrid c d a b) := by
  apply (isAP_iff_exists_APAt _).mpr
  refine ⟨d,c,?_,centered_grid_root_mem c d a b⟩
  refine ⟨by exact_mod_cast hd,(c:ℤ)-(d:ℤ)*a,(c:ℤ)+(d:ℤ)*b,?_⟩
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  intro x
  change x∈CenteredGrid c d a b ↔ _
  rw [mem_centered_grid]
  constructor
  · rintro ⟨z,hlo,hhi,hx⟩
    refine ⟨?_,?_,?_⟩
    · nlinarith
    · nlinarith
    · exact ⟨z,by nlinarith only [hx]⟩
  · rintro ⟨hlo,hhi,z,hz⟩
    exact ⟨z,by nlinarith,by nlinarith,by nlinarith only [hz]⟩

theorem centered_grid_low_high {c d a b : ℕ} (hd : 0<d) :
    Low (CenteredGrid c d a b)=(c:ℤ)-(a:ℤ)*d ∧
      High (CenteredGrid c d a b)=(c:ℤ)+(b:ℤ)*d := by
  have hne : (CenteredGrid c d a b).Nonempty := ⟨c,centered_grid_root_mem c d a b⟩
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  have hl := low_spec hne
  have hh := high_spec hne
  obtain ⟨z,hz,hz',he⟩ := mem_centered_grid.mp hl.1
  obtain ⟨w,hw,hw',hf⟩ := mem_centered_grid.mp hh.1
  have hlo := hl.2 _ (centered_grid_negative_mem (c:=c) (d:=d) (a:=a) (b:=b) (k:=a) le_rfl)
  have hhi := hh.2 _ (centered_grid_positive_mem (c:=c) (d:=d) (a:=a) (b:=b) (k:=b) le_rfl)
  exact ⟨by nlinarith,by nlinarith⟩

theorem centered_grid_parameters_unique {c d a b a' b' : ℕ} (hd : 0<d)
    (he : CenteredGrid c d a b=CenteredGrid c d a' b') : a=a' ∧ b=b' := by
  have h1 := centered_grid_low_high (c:=c) (a:=a) (b:=b) hd
  have h2 := centered_grid_low_high (c:=c) (a:=a') (b:=b') hd
  rw [he] at h1
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  constructor <;> nlinarith

theorem actual_AP_centered_model {S : Finset ℤ} {c : ℕ}
    (hAP : IsAP S) (hc : (c:ℤ)∈S) :
    ∃a b:ℕ,S=CenteredGrid c (Step S) a b ∧
      Low S=(c:ℤ)-(a:ℤ)*(Step S:ℤ) ∧ High S=(c:ℤ)+(b:ℤ)*(Step S:ℤ) := by
  obtain ⟨hd,p,hp⟩ := actual_step hAP
  have hdZ : (0:ℤ)<Step S := by exact_mod_cast hd
  have hne : S.Nonempty := ⟨c,hc⟩
  let a := Index (Low S) c (Step S)
  let b := Index c (High S) (Step S)
  have hl := index_equation ((low_spec hne).2 c hc) (apAt_dvd_sub hp (low_spec hne).1 hc)
  have hh := index_equation ((high_spec hne).2 c hc) (apAt_dvd_sub hp hc (high_spec hne).1)
  change Low S+(a:ℤ)*(Step S:ℤ)=(c:ℤ) at hl
  change (c:ℤ)+(b:ℤ)*(Step S:ℤ)=High S at hh
  refine ⟨a,b,?_,by nlinarith only [hl],hh.symm⟩
  ext x
  rw [mem_centered_grid]
  constructor
  · intro hx
    obtain ⟨z,hz⟩ := apAt_dvd_sub hp hc hx
    have hxlo := (low_spec hne).2 x hx
    have hxhi := (high_spec hne).2 x hx
    exact ⟨z,by nlinarith,by nlinarith,by nlinarith only [hz]⟩
  · rintro ⟨z,hza,hzb,hzx⟩
    apply apAt_fill hp (low_spec hne).1 (high_spec hne).1
    · nlinarith
    · nlinarith
    · exact ⟨z+(a:ℤ),by nlinarith only [hl,hzx]⟩

theorem primitive_scale_of_pos {u v : ℕ} (hu : 0<u) (hv : 0<v) :
    ∃d a b:ℕ,0<d ∧ d≤v ∧ 1≤a ∧ 1≤b ∧ a.Coprime b ∧ u=a*d ∧ v=b*d := by
  let d := u.gcd v
  have hd : 0<d := Nat.gcd_pos_of_pos_left v hu
  have hdu : d≤u := Nat.gcd_le_left v hu
  have hdv : d≤v := Nat.gcd_le_right u hv
  exact ⟨d,u/d,v/d,hd,hdv,Nat.div_pos hdu hd,Nat.div_pos hdv hd,
    Nat.coprime_div_gcd_div_gcd hd,(Nat.div_mul_cancel (Nat.gcd_dvd_left u v)).symm,
    (Nat.div_mul_cancel (Nat.gcd_dvd_right u v)).symm⟩

theorem actual_middle_AP_model {N c L R : ℕ} {S : Finset ℤ}
    (hsub : S⊆Ground N) (hAP : IsAP S) (hcard : 2≤S.card) (hc : (c:ℤ)∈S)
    (hcL : c≤L) (hlow : Low S<(c:ℤ)) (hhigh : (L:ℤ)<High S) (hR : High S≤(R:ℤ)) :
    ∃a b:ℕ,0<Step S ∧ Step S≤N ∧ S=CenteredGrid c (Step S) a b ∧
      1≤a ∧ a≤c/Step S ∧ (L-c)/Step S<b ∧ b≤(R-c)/Step S := by
  obtain ⟨a,b,he,hl,hh⟩ := actual_AP_centered_model hAP hc
  have hd := (actual_step hAP).1
  have hlo := (mem_ground N (Low S)).mp (hsub (low_spec (isAP_nonempty hAP)).1)
  have ha : 1≤a := by
    by_contra hn
    have az : a=0 := by omega
    simp only [az,Nat.cast_zero,zero_mul,sub_zero] at hl
    omega
  have hac : a*Step S≤c := by
    have hZ : ((a*Step S:ℕ):ℤ)≤(c:ℤ) := by push_cast;nlinarith only [hl,hlo.1]
    exact_mod_cast hZ
  have hlb : L-c<b*Step S := by
    have hZ : (L:ℤ)-(c:ℤ)<((b*Step S:ℕ):ℤ) := by push_cast;nlinarith only [hh,hhigh]
    omega
  have hbR : b*Step S≤R-c := by
    have hZ : ((b*Step S:ℕ):ℤ)≤(R:ℤ)-(c:ℤ) := by push_cast;nlinarith only [hh,hR]
    omega
  exact ⟨a,b,hd,actual_step_bound hsub hAP hcard,he,ha,
    (Nat.le_div_iff_mul_le hd).mpr hac,(Nat.div_lt_iff_lt_mul hd).mpr hlb,
    (Nat.le_div_iff_mul_le hd).mpr hbR⟩

theorem actual_EM_centered_model {N c L R : ℕ} {F : Finset (Finset ℤ)} {P S : Finset ℤ}
    (hF : Legal (Ground N) F) (hcL : c≤L) (hP : P∈F) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hS : S∈EM (PreparedAP F c L) c R) :
    ∃a b:ℕ,0<Step S ∧ Step S≤N ∧ S=CenteredGrid c (Step S) a b ∧
      1≤a ∧ a≤c/Step S ∧ (L-c)/Step S<b ∧ b≤(R-c)/Step S := by
  obtain ⟨hSE,hcS,hhigh⟩ := Finset.mem_filter.mp hS
  obtain ⟨hSF,hAP,hsize,_⟩ := actual_prepared_AP_member hSE
  have hs := actual_prepared_root_support hF hP hLP hSE hcS
  exact actual_middle_AP_model (hF.1 S hSF) hAP (by omega) hcS hcL hs.1 hs.2 hhigh

theorem actual_negative_witness_coordinates {N c L R : ℕ} {S : Finset ℤ} {x p : ℤ}
    (hsub : S⊆Ground N) (hcL : c≤L) (hRN : R≤N)
    (hcx : x<(c:ℤ)) (hLp : (L:ℤ)<p) (hpR : p≤(R:ℤ)) (hW : IntrinsicPair c S {x,p}) :
    ∃d a b:ℕ,0<d ∧ d≤N ∧ 1≤a ∧ a≤c/d ∧ (L-c)/d<b ∧ b≤(R-c)/d ∧
      a.Coprime b ∧ x=(c:ℤ)-(a:ℤ)*d ∧ p=(c:ℤ)+(b:ℤ)*d ∧
      IntrinsicPair c S {(c:ℤ)-(a:ℤ)*d,(c:ℤ)+(b:ℤ)*d} := by
  have hxS : x∈S := hW.2.2.1 (by simp)
  have hxN := (mem_ground N x).mp (hsub hxS)
  let u := ((c:ℤ)-x).toNat
  let v := (p-(c:ℤ)).toNat
  have hu : 0<u := by dsimp [u];omega
  have hv : 0<v := by dsimp [v];omega
  have huZ : (u:ℤ)=(c:ℤ)-x := Int.toNat_of_nonneg (by omega)
  have hvZ : (v:ℤ)=p-(c:ℤ) := Int.toNat_of_nonneg (by omega)
  obtain ⟨d,a,b,hd,hdv,ha,_hb,hcop,hua,hvb⟩ := primitive_scale_of_pos hu hv
  have huc : u≤c := by omega
  have hvR : v≤R-c := by omega
  have hLv : L-c<v := by omega
  have hx : x=(c:ℤ)-(a:ℤ)*d := by rw [hua] at huZ;push_cast at huZ;nlinarith only [huZ]
  have hp : p=(c:ℤ)+(b:ℤ)*d := by rw [hvb] at hvZ;push_cast at hvZ;nlinarith only [hvZ]
  refine ⟨d,a,b,hd,by omega,ha,(Nat.le_div_iff_mul_le hd).mpr (by omega),
    (Nat.div_lt_iff_lt_mul hd).mpr (by omega),(Nat.le_div_iff_mul_le hd).mpr (by omega),
    hcop,hx,hp,?_⟩
  simpa only [←hx,←hp] using hW

theorem actual_positive_witness_coordinates {N c L R : ℕ} {S : Finset ℤ} {x p : ℤ}
    (hcL : c≤L) (hRN : R≤N) (hcx : (c:ℤ)<x) (hxp : x<p)
    (hLp : (L:ℤ)<p) (hpR : p≤(R:ℤ)) (hW : IntrinsicPair c S {x,p}) :
    ∃d a b:ℕ,0<d ∧ d≤N ∧ 1≤a ∧ a<b ∧ (L-c)/d<b ∧ b≤(R-c)/d ∧
      a.Coprime b ∧ x=(c:ℤ)+(a:ℤ)*d ∧ p=(c:ℤ)+(b:ℤ)*d ∧
      IntrinsicPair c S {(c:ℤ)+(a:ℤ)*d,(c:ℤ)+(b:ℤ)*d} := by
  let u := (x-(c:ℤ)).toNat
  let v := (p-(c:ℤ)).toNat
  have hu : 0<u := by dsimp [u];omega
  have hv : 0<v := by dsimp [v];omega
  have huZ : (u:ℤ)=x-(c:ℤ) := Int.toNat_of_nonneg (by omega)
  have hvZ : (v:ℤ)=p-(c:ℤ) := Int.toNat_of_nonneg (by omega)
  obtain ⟨d,a,b,hd,hdv,ha,_hb,hcop,hua,hvb⟩ := primitive_scale_of_pos hu hv
  have huv : u<v := by omega
  have hvR : v≤R-c := by omega
  have hLv : L-c<v := by omega
  have hab : a<b := by
    by_contra hn
    have hm := Nat.mul_le_mul_right d (show b≤a by omega)
    omega
  have hx : x=(c:ℤ)+(a:ℤ)*d := by rw [hua] at huZ;push_cast at huZ;nlinarith only [huZ]
  have hp : p=(c:ℤ)+(b:ℤ)*d := by rw [hvb] at hvZ;push_cast at hvZ;nlinarith only [hvZ]
  refine ⟨d,a,b,hd,by omega,ha,hab,(Nat.div_lt_iff_lt_mul hd).mpr (by omega),
    (Nat.le_div_iff_mul_le hd).mpr (by omega),hcop,hx,hp,?_⟩
  simpa only [←hx,←hp] using hW

def NegativeCM (C : Finset (Finset ℤ)) (x p : Finset ℤ→ℤ) (c R : ℕ) :=
  (CM C p R).filter (fun S=>x S<(c:ℤ))

def PositiveCM (C : Finset (Finset ℤ)) (x p : Finset ℤ→ℤ) (c R : ℕ) :=
  (CM C p R).filter (fun S=>(c:ℤ)<x S)

theorem actual_CM_sign_partition {C : Finset (Finset ℤ)} {c R : ℕ}
    (x p : Finset ℤ→ℤ) (hW : ∀S∈C,IntrinsicPair c S {x S,p S}) :
    CM C p R=NegativeCM C x p c R∪PositiveCM C x p c R ∧
      Disjoint (NegativeCM C x p c R) (PositiveCM C x p c R) ∧
      (CM C p R).card=(NegativeCM C x p c R).card+(PositiveCM C x p c R).card := by
  have he : CM C p R=NegativeCM C x p c R∪PositiveCM C x p c R := by
    ext S
    constructor
    · intro hS
      have hw := hW S (Finset.mem_filter.mp hS).1
      have hxc : x S≠(c:ℤ) := by intro hh;apply hw.2.1;simp [←hh]
      by_cases hx : x S<(c:ℤ)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS,hx⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hS,by omega⟩)
    · intro hS
      rcases Finset.mem_union.mp hS with hS|hS <;>exact (Finset.mem_filter.mp hS).1
  have hd : Disjoint (NegativeCM C x p c R) (PositiveCM C x p c R) := by
    apply Finset.disjoint_left.mpr
    intro S hS hT
    have hs := (Finset.mem_filter.mp hS).2
    have ht := (Finset.mem_filter.mp hT).2
    omega
  exact ⟨he,hd,by rw [he,Finset.card_union_of_disjoint hd]⟩

theorem actual_negative_CM_coordinates {N c L R : ℕ} {F : Finset (Finset ℤ)}
    {S : Finset ℤ} (x p : Finset ℤ→ℤ)
    (hF : Legal (Ground N) F) (hcL : c≤L) (hRN : R≤N)
    (hW : ∀S∈PreparedCrooked F c L,IntrinsicPair c S {x S,p S} ∧ (L:ℤ)<p S)
    (hS : S∈NegativeCM (PreparedCrooked F c L) x p c R) :
    ∃d a b:ℕ,0<d ∧ d≤N ∧ 1≤a ∧ a≤c/d ∧ (L-c)/d<b ∧ b≤(R-c)/d ∧
      a.Coprime b ∧ x S=(c:ℤ)-(a:ℤ)*d ∧ p S=(c:ℤ)+(b:ℤ)*d ∧
      IntrinsicPair c S {(c:ℤ)-(a:ℤ)*d,(c:ℤ)+(b:ℤ)*d} := by
  obtain ⟨hSC,hxc⟩ := Finset.mem_filter.mp hS
  obtain ⟨hC,hpR⟩ := Finset.mem_filter.mp hSC
  have hSF : S∈F := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).1).1
  exact actual_negative_witness_coordinates (hF.1 S hSF) hcL hRN hxc (hW S hC).2 hpR (hW S hC).1

theorem actual_positive_CM_coordinates {N c L R : ℕ} {F : Finset (Finset ℤ)}
    {S : Finset ℤ} (x p : Finset ℤ→ℤ)
    (hcL : c≤L) (hRN : R≤N)
    (hW : ∀S∈PreparedCrooked F c L,IntrinsicPair c S {x S,p S} ∧ x S<p S ∧ (L:ℤ)<p S)
    (hS : S∈PositiveCM (PreparedCrooked F c L) x p c R) :
    ∃d a b:ℕ,0<d ∧ d≤N ∧ 1≤a ∧ a<b ∧ (L-c)/d<b ∧ b≤(R-c)/d ∧
      a.Coprime b ∧ x S=(c:ℤ)+(a:ℤ)*d ∧ p S=(c:ℤ)+(b:ℤ)*d ∧
      IntrinsicPair c S {(c:ℤ)+(a:ℤ)*d,(c:ℤ)+(b:ℤ)*d} := by
  obtain ⟨hSC,hcx⟩ := Finset.mem_filter.mp hS
  obtain ⟨hC,hpR⟩ := Finset.mem_filter.mp hSC
  exact actual_positive_witness_coordinates hcL hRN hcx (hW S hC).2.1 (hW S hC).2.2 hpR (hW S hC).1

#print axioms mem_centered_grid
#print axioms centered_grid_root_mem
#print axioms centered_grid_positive_mem
#print axioms centered_grid_negative_mem
#print axioms centered_grid_isAP
#print axioms centered_grid_low_high
#print axioms centered_grid_parameters_unique
#print axioms actual_AP_centered_model
#print axioms primitive_scale_of_pos
#print axioms actual_middle_AP_model
#print axioms actual_EM_centered_model
#print axioms actual_negative_witness_coordinates
#print axioms actual_positive_witness_coordinates
#print axioms actual_CM_sign_partition
#print axioms actual_negative_CM_coordinates
#print axioms actual_positive_CM_coordinates

end
end JSP233.MiddleCoordinates51
