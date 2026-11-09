module

public import Erdos272.Counting.NearFloorActual64
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-!
Actual core-first Near bounds and the half-open size decomposition used in
round 110.  No Far cardinality or resource price is assumed or proved here.
The definitions keep the whole actual family, including all Large members.
-/
namespace JSP233.NearWhole112
open StarCompletion APGeometry NearAP36 NearFloor63 NearFloorAnalytic64
open NearFloorDyadic64 HarmonicAbel29 BandAggregation34
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Scale (K j : ℕ) : ℕ := 2^j*K

def Level (K n : ℕ) : ℕ := Nat.log 2 (n/(3*K))

def Band (F : Finset (Finset ℤ)) (K j : ℕ) : Finset (Finset ℤ) :=
  F.filter (fun S => 3*Scale K j≤S.card ∧ S.card<6*Scale K j)

def Tail (F : Finset (Finset ℤ)) (K : ℕ) : Finset (Finset ℤ) :=
  F.filter (fun S => 3*K≤S.card)

def Near (F : Finset (Finset ℤ)) (K : ℕ) : Finset (Finset ℤ) :=
  (Tail F K).filter (fun S => HasNearAPCore (Scale K (Level K S.card)) S)

def Far (F : Finset (Finset ℤ)) (K : ℕ) : Finset (Finset ℤ) :=
  (Tail F K).filter (fun S => ¬HasNearAPCore (Scale K (Level K S.card)) S)

theorem actual_core_first_floor_budget {N K b : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K)
    (hbad : ∀S∈F,¬IsAP S) (hhigh : ∀S∈F,S.card≤b*K)
    (hnear : ∀S∈F,HasNearAPCore K S) :
    F.card≤(b+1)*((N/(2*K))*N+
      K*(∑d∈Finset.Icc 1 (N/(2*K)),d*(N/(K*d)+1-2))) := by
  obtain ⟨start,step,length,hcoords⟩ :=
    NearHelly54.actual_nearAP_coordinate_selection hlegal.1 hhigh hnear
  exact actual_near_floor_step_budget hlegal hK (by decide : 2≤2)
    start step length hbad hhigh
    (fun S hS => (hcoords S hS).1)
    (fun S hS => (hcoords S hS).2.1)
    (fun S hS => (hcoords S hS).2.2.1)
    (fun S hS => (hcoords S hS).2.2.2.2.1)
    (fun S hS => (hcoords S hS).2.2.2.2.2)

theorem actual_core_first_quadratic {N K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K)
    (hbad : ∀S∈F,¬IsAP S) (hhigh : ∀S∈F,S.card≤6*K)
    (hnear : ∀S∈F,HasNearAPCore K S) :
    (F.card:ℝ)≤(2303/400:ℝ)*(N:ℝ)^2/K+(7/2:ℝ)*N*Harmonic N := by
  have hf := actual_core_first_floor_budget hlegal hK hbad hhigh hnear
  have hfR : (F.card:ℝ)≤7*
      (((N/(2*K):ℕ):ℝ)*N+(K:ℝ)*
        ((∑d∈Finset.Icc 1 (N/(2*K)),d*(N/(K*d)+1-2):ℕ):ℝ)) := by
    exact_mod_cast hf
  have hq := actual_floor_quadratic_budget (N:=N) hK
  calc
    _≤7*(((N/(2*K):ℕ):ℝ)*N+(K:ℝ)*
        ((∑d∈Finset.Icc 1 (N/(2*K)),d*(N/(K*d)+1-2):ℕ):ℝ)) := hfR
    _≤7*((329/400:ℝ)*(N:ℝ)^2/K+(1/2:ℝ)*N*Harmonic N) :=
      mul_le_mul_of_nonneg_left hq (by norm_num)
    _=_ := by ring

theorem actual_level_band {K n : ℕ} (hK : 0<K) (hn : 3*K≤n) :
    3*Scale K (Level K n)≤n ∧ n<6*Scale K (Level K n) := by
  let q := n/(3*K)
  have hq : 0<q := Nat.div_pos hn (by positivity)
  have hl := Nat.pow_log_le_self 2 (by omega : q≠0)
  have hu := Nat.lt_pow_succ_log_self (by decide : 1<2) q
  have hlo := (Nat.le_div_iff_mul_le (by positivity : 0<3*K)).mp hl
  have hhi := (Nat.div_lt_iff_lt_mul (by positivity : 0<3*K)).mp hu
  change 2^(Level K n)*(3*K)≤n at hlo
  change n<2^(Level K n+1)*(3*K) at hhi
  dsimp only [Scale]
  rw [pow_succ] at hhi
  constructor <;> nlinarith only [hlo,hhi]

theorem actual_band_unique {K n i j : ℕ}
    (hi : 3*Scale K i≤n ∧ n<6*Scale K i)
    (hj : 3*Scale K j≤n ∧ n<6*Scale K j) : i=j := by
  have hnot : ∀a b:ℕ,a<b→n<6*Scale K a→3*Scale K b≤n→False := by
    intro a b hab hna hbn
    have hp := Nat.pow_le_pow_right (by decide : 1≤2) (show a+1≤b by omega)
    have hm := Nat.mul_le_mul_right K hp
    rw [pow_succ] at hm
    dsimp only [Scale] at *
    nlinarith only [hm,hna,hbn]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij|hji
  · exact hnot i j hij hi.2 hj.1
  · exact hnot j i hji hj.2 hi.1

theorem actual_unique_band {K n : ℕ} (hK : 0<K) (hn : 3*K≤n) :
    ∃!j:ℕ,3*Scale K j≤n ∧ n<6*Scale K j :=
  ⟨Level K n,actual_level_band hK hn,
    fun _ hi => actual_band_unique hi (actual_level_band hK hn)⟩

theorem actual_first_boundary (K : ℕ) (hK : 0<K) :
    Level K (3*K)=0 ∧ Level K (6*K)=1 := by
  constructor
  · apply actual_band_unique (actual_level_band hK (by omega))
    simp only [Scale,pow_zero,one_mul]
    omega
  · apply actual_band_unique (actual_level_band hK (by omega))
    norm_num [Scale]
    omega

theorem actual_near_scale_inclusion {a b : ℕ} {S : Finset ℤ}
    (hab : a≤b) (hsize : 3*b≤S.card) (hnear : HasNearAPCore a S) :
    HasNearAPCore b S := by
  obtain ⟨P,hmax,hcore,hrem⟩ := hnear
  have hpart := Finset.card_sdiff_add_card_eq_card hmax.1
  exact ⟨P,hmax,by omega,hrem.trans_le hab⟩

theorem actual_near_scale_level {K h j : ℕ} {S : Finset ℤ}
    (hhj : h≤j) (hsize : 3*Scale K j≤S.card)
    (hnear : HasNearAPCore (Scale K h) S) : HasNearAPCore (Scale K j) S := by
  apply actual_near_scale_inclusion (b:=Scale K j) _ hsize hnear
  exact Nat.mul_le_mul_right K (Nat.pow_le_pow_right (by decide : 1≤2) hhj)

theorem actual_level_lt {N K J : ℕ} {F : Finset (Finset ℤ)}
    (level : Finset ℤ→ℕ) (hlegal : Legal (Ground N) F) (hK : 0<K) (hN : N<2^J)
    (hlow : ∀S∈F,3*Scale K (level S)≤S.card) {S : Finset ℤ} (hS : S∈F) :
    level S<J := by
  by_contra hn
  have hp := Nat.pow_le_pow_right (by decide : 1≤2) (show J≤level S by omega)
  have hm := Nat.mul_le_mul_left (2^(level S)) (show 1≤K by omega)
  have hc : S.card≤N := by
    simpa only [ground_card] using Finset.card_le_card (hlegal.1 S hS)
  have hlo := hlow S hS
  dsimp only [Scale] at hlo
  nlinarith only [hp,hm,hc,hlo,hN]

theorem actual_dyadic_core_first_quadratic {N K J : ℕ} {F : Finset (Finset ℤ)}
    (level : Finset ℤ→ℕ) (hlegal : Legal (Ground N) F) (hK : 0<K) (hN : N<2^J)
    (hbad : ∀S∈F,¬IsAP S)
    (hlow : ∀S∈F,3*Scale K (level S)≤S.card)
    (hhigh : ∀S∈F,S.card≤6*Scale K (level S))
    (hnear : ∀S∈F,HasNearAPCore (Scale K (level S)) S) :
    (F.card:ℝ)≤(2303/200:ℝ)*(N:ℝ)^2/K+(7/2:ℝ)*J^2*N := by
  let family : ℕ→Finset (Finset ℤ) := fun j=>F.filter (fun S=>level S=j)
  have hfamily : ∀j,family j⊆F := fun j=>Finset.filter_subset _ _
  have hmaps : ∀S∈F,level S∈Finset.range J := by
    intro S hS
    exact Finset.mem_range.mpr (actual_level_lt level hlegal hK hN hlow hS)
  have hpart : F.card=∑j∈Finset.range J,(family j).card := Finset.card_eq_sum_card_fiberwise hmaps
  have hpartR : (F.card:ℝ)=∑j∈Finset.range J,((family j).card:ℝ) := by exact_mod_cast hpart
  have hrow : ∀j∈Finset.range J,((family j).card:ℝ)≤
      (2303/400:ℝ)*(N:ℝ)^2/K*(1/2:ℝ)^j+(7/2:ℝ)*N*Harmonic N := by
    intro j _hj
    have hLj : Legal (Ground N) (family j) :=
      ⟨fun S hS=>hlegal.1 S (hfamily j hS),fun S hS T hT he=>
        hlegal.2 S (hfamily j hS) T (hfamily j hT) he⟩
    have hh := actual_core_first_quadratic hLj (by positivity : 0<2^j*K)
      (fun S hS=>hbad S (hfamily j hS)) (by
        intro S hS
        simpa only [(Finset.mem_filter.mp hS).2,Scale] using hhigh S (hfamily j hS)) (by
        intro S hS
        simpa only [(Finset.mem_filter.mp hS).2,Scale] using hnear S (hfamily j hS))
    push_cast at hh
    have he : (2303/400:ℝ)*(N:ℝ)^2/((2:ℝ)^j*K)=
        (2303/400:ℝ)*(N:ℝ)^2/K*(1/2:ℝ)^j := by
      rw [one_div,inv_pow]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rwa [he] at hh
  have hs := Finset.sum_le_sum hrow
  rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  rw [←hpartR] at hs
  have hgeom := mul_le_mul_of_nonneg_left (dyadic_sum_le_two J)
    (by positivity : (0:ℝ)≤(2303/400:ℝ)*(N:ℝ)^2/K)
  have hharm := mul_le_mul_of_nonneg_left (actual_harmonic_le_exponent hN)
    (by positivity : (0:ℝ)≤(J:ℝ)*((7/2:ℝ)*N))
  calc
    _≤(2303/400:ℝ)*(N:ℝ)^2/K*(∑j∈Finset.range J,(1/2:ℝ)^j)+
      (J:ℝ)*((7/2:ℝ)*N*Harmonic N) := hs
    _≤(2303/400:ℝ)*(N:ℝ)^2/K*2+(J:ℝ)*((7/2:ℝ)*N*J) := by
      apply add_le_add hgeom
      convert hharm using 1 <;> ring
    _=_ := by ring

theorem actual_near_whole_quadratic {N K J : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hN : N<2^J)
    (hbad : ∀S∈F,¬IsAP S) :
    ((Near F K).card:ℝ)≤(2303/200:ℝ)*(N:ℝ)^2/K+(7/2:ℝ)*J^2*N := by
  have hNF : Near F K⊆F := fun S hS =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hNL : Legal (Ground N) (Near F K) :=
    ⟨fun S hS=>hlegal.1 S (hNF hS),fun S hS T hT he=>hlegal.2 S (hNF hS) T (hNF hT) he⟩
  apply actual_dyadic_core_first_quadratic (fun S => Level K S.card) hNL hK hN
    (fun S hS=>hbad S (hNF hS))
  · intro S hS
    exact (actual_level_band hK (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2).1
  · intro S hS
    exact (actual_level_band hK (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2).2.le
  · intro S hS
    exact (Finset.mem_filter.mp hS).2

theorem actual_near_whole_normalized {N K J : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hN : N<2^J) (hpos : 0<N)
    (hbad : ∀S∈F,¬IsAP S) :
    ((Near F K).card:ℝ)/(N:ℝ)^2≤(2303/200:ℝ)/K+(7/2:ℝ)*J^2/N := by
  have hh := actual_near_whole_quadratic hlegal hK hN hbad
  have hp : (0:ℝ)<N := Nat.cast_pos.mpr hpos
  have hk : (0:ℝ)<K := Nat.cast_pos.mpr hK
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  have he : ((2303/200:ℝ)/K+(7/2:ℝ)*J^2/N)*(N:ℝ)^2=
      (2303/200:ℝ)*(N:ℝ)^2/K+(7/2:ℝ)*J^2*N := by
    field_simp [hp.ne',hk.ne']
  rwa [he]

theorem actual_tail_partition (F : Finset (Finset ℤ)) (K : ℕ) :
    (Near F K).card+(Far F K).card=(Tail F K).card := by
  exact Finset.card_filter_add_card_filter_not (s:=Tail F K) _

theorem actual_far_subset_fixed {F : Finset (Finset ℤ)} {K : ℕ} (hK : 0<K) :
    Far F K⊆F.filter (fun S => 3*K≤S.card ∧ ¬HasNearAPCore K S) := by
  intro S hS
  obtain ⟨hST,hfar⟩ := Finset.mem_filter.mp hS
  obtain ⟨hSF,hsize⟩ := Finset.mem_filter.mp hST
  refine Finset.mem_filter.mpr ⟨hSF,hsize,?_⟩
  intro hn
  have hm : K≤Scale K (Level K S.card) := by
    exact Nat.le_mul_of_pos_left K (by positivity)
  exact hfar (actual_near_scale_inclusion hm (actual_level_band hK hsize).1 hn)

theorem actual_scale_shift (K h j : ℕ) : Scale K (h+j)=Scale (Scale K h) j := by
  simp only [Scale,pow_add]
  ring

theorem actual_level_shift {K h n : ℕ} (hK : 0<K) (hn : 3*Scale K h≤n) :
    Level K n=h+Level (Scale K h) n := by
  have hk : 0<Scale K h := by unfold Scale;positivity
  have hm : K≤Scale K h := Nat.le_mul_of_pos_left K (by positivity)
  have hb := actual_level_band hk hn
  have hb' : 3*Scale K (h+Level (Scale K h) n)≤n ∧
      n<6*Scale K (h+Level (Scale K h) n) := by
    simpa only [actual_scale_shift] using hb
  exact actual_band_unique (actual_level_band hK (by omega)) hb'

def NearUnionTail (F : Finset (Finset ℤ)) (K h : ℕ) : Finset (Finset ℤ) :=
  F.filter (fun S => ∃j:ℕ,h≤j ∧ S∈Band F K j ∧ HasNearAPCore (Scale K j) S)

def FarUnionTail (F : Finset (Finset ℤ)) (K h : ℕ) : Finset (Finset ℤ) :=
  F.filter (fun S => ∃j:ℕ,h≤j ∧ S∈Band F K j ∧ ¬HasNearAPCore (Scale K j) S)

theorem actual_near_union_tail_eq {F : Finset (Finset ℤ)} {K h : ℕ} (hK : 0<K) :
    NearUnionTail F K h=Near F (Scale K h) := by
  ext S
  constructor
  · intro hs
    obtain ⟨hSF,j,hhj,hband,hn⟩ := Finset.mem_filter.mp hs
    have hb := (Finset.mem_filter.mp hband).2
    have hm := Nat.mul_le_mul_right K
      (Nat.pow_le_pow_right (by decide : 1≤2) hhj)
    change Scale K h≤Scale K j at hm
    have hsize : 3*Scale K h≤S.card := by nlinarith only [hm,hb.1]
    have he := actual_band_unique (actual_level_band hK (by
      have hk : K≤Scale K h := Nat.le_mul_of_pos_left K (by positivity)
      omega)) hb
    have hsft := actual_level_shift hK hsize
    have hscale : Scale (Scale K h) (Level (Scale K h) S.card)=Scale K j := by
      rw [←actual_scale_shift,←hsft,he]
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hSF,hsize⟩,hscale.symm ▸ hn⟩
  · intro hs
    obtain ⟨hst,hn⟩ := Finset.mem_filter.mp hs
    obtain ⟨hsf,hsize⟩ := Finset.mem_filter.mp hst
    let j := h+Level (Scale K h) S.card
    have hb := actual_level_band (by unfold Scale;positivity : 0<Scale K h) hsize
    have hscale : Scale K j=Scale (Scale K h) (Level (Scale K h) S.card) :=
      actual_scale_shift _ _ _
    exact Finset.mem_filter.mpr ⟨hsf,j,by omega,
      Finset.mem_filter.mpr ⟨hsf,by rw [hscale];exact hb.1,
        by rw [hscale];exact hb.2⟩,hscale ▸ hn⟩

theorem actual_far_union_tail_eq {F : Finset (Finset ℤ)} {K h : ℕ} (hK : 0<K) :
    FarUnionTail F K h=Far F (Scale K h) := by
  ext S
  constructor
  · intro hs
    obtain ⟨hSF,j,hhj,hband,hn⟩ := Finset.mem_filter.mp hs
    have hb := (Finset.mem_filter.mp hband).2
    have hm := Nat.mul_le_mul_right K
      (Nat.pow_le_pow_right (by decide : 1≤2) hhj)
    change Scale K h≤Scale K j at hm
    have hsize : 3*Scale K h≤S.card := by nlinarith only [hm,hb.1]
    have he := actual_band_unique (actual_level_band hK (by
      have hk : K≤Scale K h := Nat.le_mul_of_pos_left K (by positivity)
      omega)) hb
    have hsft := actual_level_shift hK hsize
    have hscale : Scale (Scale K h) (Level (Scale K h) S.card)=Scale K j := by
      rw [←actual_scale_shift,←hsft,he]
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hSF,hsize⟩,hscale.symm ▸ hn⟩
  · intro hs
    obtain ⟨hst,hn⟩ := Finset.mem_filter.mp hs
    obtain ⟨hsf,hsize⟩ := Finset.mem_filter.mp hst
    let j := h+Level (Scale K h) S.card
    have hb := actual_level_band (by unfold Scale;positivity : 0<Scale K h) hsize
    have hscale : Scale K j=Scale (Scale K h) (Level (Scale K h) S.card) :=
      actual_scale_shift _ _ _
    exact Finset.mem_filter.mpr ⟨hsf,j,by omega,
      Finset.mem_filter.mpr ⟨hsf,by rw [hscale];exact hb.1,
        by rw [hscale];exact hb.2⟩,hscale ▸ hn⟩

theorem actual_far_union_tail_subset_fixed {F : Finset (Finset ℤ)} {K h : ℕ}
    (hK : 0<K) :
    FarUnionTail F K h⊆F.filter
      (fun S => 3*Scale K h≤S.card ∧ ¬HasNearAPCore (Scale K h) S) := by
  rw [actual_far_union_tail_eq hK]
  exact actual_far_subset_fixed (by unfold Scale;positivity)

theorem actual_near_union_tail_normalized {N K J h : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hN : N<2^J) (hpos : 0<N)
    (hbad : ∀S∈F,¬IsAP S) :
    ((NearUnionTail F K h).card:ℝ)/(N:ℝ)^2≤
      ((2303/200:ℝ)/K)/(2:ℝ)^h+(7/2:ℝ)*J^2/N := by
  rw [actual_near_union_tail_eq hK]
  have hh := actual_near_whole_normalized hlegal
    (by unfold Scale;positivity : 0<Scale K h) hN hpos hbad
  have he : (2303/200:ℝ)/(Scale K h:ℝ)=((2303/200:ℝ)/K)/(2:ℝ)^h := by
    simp only [Scale,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
  rwa [he] at hh

theorem actual_fixed_near_tail_subset {F : Finset (Finset ℤ)} {K : ℕ} (hK : 0<K) :
    F.filter (fun S => 3*K≤S.card ∧ HasNearAPCore K S)⊆Near F K := by
  intro S hS
  obtain ⟨hsf,hsize,hn⟩ := Finset.mem_filter.mp hS
  have hm : K≤Scale K (Level K S.card) := Nat.le_mul_of_pos_left K (by positivity)
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hsf,hsize⟩,
    actual_near_scale_inclusion hm (actual_level_band hK hsize).1 hn⟩

/-- The unpaid term is the cardinality of the actual fixed-scale Far subset.
No putative numerical Far fee is a hypothesis. -/
theorem actual_tail_card_budget {N K J : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hN : N<2^J)
    (hbad : ∀S∈F,¬IsAP S) :
    ((Tail F K).card:ℝ)≤(2303/200:ℝ)*(N:ℝ)^2/K+(7/2:ℝ)*J^2*N+
      ((F.filter (fun S => 3*K≤S.card ∧ ¬HasNearAPCore K S)).card:ℝ) := by
  have hpart := actual_tail_partition F K
  have hpartR : ((Near F K).card:ℝ)+((Far F K).card:ℝ)=(Tail F K).card := by
    exact_mod_cast hpart
  have hnear := actual_near_whole_quadratic hlegal hK hN hbad
  have hfar : ((Far F K).card:ℝ)≤
      ((F.filter (fun S => 3*K≤S.card ∧ ¬HasNearAPCore K S)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (actual_far_subset_fixed (F:=F) hK)
  linarith only [hpartR,hnear,hfar]

theorem actual_whole_card_budget {N K J : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hN : N<2^J)
    (hbad : ∀S∈F,¬IsAP S) (hlow : ∀S∈F,3*K≤S.card) :
    (F.card:ℝ)≤(2303/200:ℝ)*(N:ℝ)^2/K+(7/2:ℝ)*J^2*N+
      ((F.filter (fun S => ¬HasNearAPCore K S)).card:ℝ) := by
  have ht : Tail F K=F := Finset.filter_eq_self.mpr hlow
  have hf : F.filter (fun S => 3*K≤S.card ∧ ¬HasNearAPCore K S)=
      F.filter (fun S => ¬HasNearAPCore K S) := by
    ext S
    simp only [Finset.mem_filter]
    exact ⟨fun hs => ⟨hs.1,hs.2.2⟩,fun hs => ⟨hs.1,hlow S hs.1,hs.2⟩⟩
  simpa only [ht,hf] using actual_tail_card_budget hlegal hK hN hbad

theorem actual_whole_normalized {N K J : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hN : N<2^J) (hpos : 0<N)
    (hbad : ∀S∈F,¬IsAP S) (hlow : ∀S∈F,3*K≤S.card) :
    (F.card:ℝ)/(N:ℝ)^2≤(2303/200:ℝ)/K+(7/2:ℝ)*J^2/N+
      ((F.filter (fun S => ¬HasNearAPCore K S)).card:ℝ)/(N:ℝ)^2 := by
  have hh := actual_whole_card_budget hlegal hK hN hbad hlow
  have hp : (0:ℝ)<N := Nat.cast_pos.mpr hpos
  have hk : (0:ℝ)<K := Nat.cast_pos.mpr hK
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  have he : ((2303/200:ℝ)/K+(7/2:ℝ)*J^2/N+
      ((F.filter (fun S => ¬HasNearAPCore K S)).card:ℝ)/(N:ℝ)^2)*(N:ℝ)^2=
      (2303/200:ℝ)*(N:ℝ)^2/K+(7/2:ℝ)*J^2*N+
      ((F.filter (fun S => ¬HasNearAPCore K S)).card:ℝ) := by
    field_simp [hp.ne',hk.ne']
  rwa [he]

#print axioms actual_core_first_floor_budget
#print axioms actual_core_first_quadratic
#print axioms actual_level_band
#print axioms actual_band_unique
#print axioms actual_unique_band
#print axioms actual_first_boundary
#print axioms actual_near_scale_inclusion
#print axioms actual_near_scale_level
#print axioms actual_level_lt
#print axioms actual_dyadic_core_first_quadratic
#print axioms actual_near_whole_quadratic
#print axioms actual_near_whole_normalized
#print axioms actual_tail_partition
#print axioms actual_far_subset_fixed
#print axioms actual_scale_shift
#print axioms actual_level_shift
#print axioms actual_near_union_tail_eq
#print axioms actual_far_union_tail_eq
#print axioms actual_far_union_tail_subset_fixed
#print axioms actual_near_union_tail_normalized
#print axioms actual_fixed_near_tail_subset
#print axioms actual_tail_card_budget
#print axioms actual_whole_card_budget
#print axioms actual_whole_normalized
end
end JSP233.NearWhole112
