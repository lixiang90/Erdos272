module

public import Erdos272.Resources.IntegerShared209
public import Erdos272.Arithmetic.IntegerHighPrices209

@[expose] public section

namespace JSP233.IntegerLowPrices209
open StarCompletion APGeometry DenseDeletion40 Density41 HarmonicAbel29
open IntegerHighPrices209 SharedUniform209
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def G (w : Fin 11) : ℝ := [(239/2262871800 : ℝ),(239/2372488524 : ℝ),(239/2532387312 : ℝ),(1195/14045470236 : ℝ),(1195/16406804442 : ℝ),(1195/20671825104 : ℝ),(239/5882474304 : ℝ),(239/9958095252 : ℝ),(239/21950055036 : ℝ),(1195/359374077216 : ℝ),(1195/2129326267488 : ℝ)].getD w.val 0
def U (w : Fin 11) : ℝ := [(317/5000 : ℝ),(641/10000 : ℝ),(621/10000 : ℝ),(301/5000 : ℝ),(609/10000 : ℝ),(7/125 : ℝ),(249/5000 : ℝ),(417/10000 : ℝ),(161/5000 : ℝ),(27/1250 : ℝ),(3/250 : ℝ)].getD w.val 0
def Eta (w : Fin 11) : ℕ := [748,752,751,754,773,776,782,783,802,875,933].getD w.val 0
def C (w : Fin 11) : ℝ := Eta w+142+4*M w

theorem numeric (w : Fin 11) : 0<G w ∧ 0≤U w ∧ 0≤C w ∧
    TripleShare*G w*(Upper w : ℝ)≤StrongAPResponse209.T ∧
    SharedUniformStrong209.CoupledShare*G w*(Upper w : ℝ)+U w+C w/(Lower w : ℝ)<(71/800 : ℝ) := by
  fin_cases w <;> norm_num [G,U,Eta,C,M,Lower,Upper,TripleShare,StrongAPResponse209.T,
    SharedUniformStrong209.CoupledShare]

theorem actual_price {N : ℕ} (w : Fin 11) (hlo : Lower w≤N) (hhi : N≤Upper w) :
    TripleShare*G w*(N : ℝ)≤StrongAPResponse209.T ∧
    SharedUniformStrong209.CoupledShare*G w*(N : ℝ)+U w+(Eta w+142)/(N : ℝ)+
      (4*(M w : ℝ)*N)/(N : ℝ)^2<(71/800 : ℝ) := by
  have hd := data_range w
  have hh := numeric w
  have hg : 0<G w := hh.1
  have hlR : (Lower w : ℝ)≤N := by exact_mod_cast hlo
  have huR : (N : ℝ)≤Upper w := by exact_mod_cast hhi
  have hlpos : (0 : ℝ)<Lower w := by
    have h : (705098 : ℝ)≤Lower w := by exact_mod_cast hd.2.1
    linarith only [h]
  have hn : (0 : ℝ)<N := hlpos.trans_le hlR
  constructor
  · exact (mul_le_mul_of_nonneg_left huR (by dsimp only [TripleShare]; positivity)).trans hh.2.2.2.1
  · have hm := mul_le_mul_of_nonneg_left huR
      (show 0≤SharedUniformStrong209.CoupledShare*G w by
        dsimp only [SharedUniformStrong209.CoupledShare];positivity)
    have hc := div_le_div_of_nonneg_left hh.2.2.1 hlpos hlR
    have he : SharedUniformStrong209.CoupledShare*G w*(N : ℝ)+U w+(Eta w+142)/(N : ℝ)+
        (4*(M w : ℝ)*N)/(N : ℝ)^2=
        SharedUniformStrong209.CoupledShare*G w*(N : ℝ)+U w+C w/(N : ℝ) := by
      dsimp only [C]
      field_simp
      <;> ring
    rw [he]
    linarith only [hm,hc,hh.2.2.2.2]

theorem actual_contradiction {N : ℕ} {A F : Finset (Finset ℤ)}
    (w : Fin 11) (hlo : Lower w≤N) (hhi : N≤Upper w)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hAG : A⊆SparseCrooked N 11 F)
    (hcover : ((SparseCrooked N 11 F).card : ℝ)≤A.card+4*(M w : ℝ)*N)
    (hfee : IntegerShared209.NearObligation N A (M w) (G w) (U w) (Eta w))
    (hH : Harmonic N≤19) : False := by
  have hd := data_range w
  have hN : 10902≤N := by omega
  have hm : (0 : ℝ)<M w := by
    have hh : (250 : ℝ)≤M w := by exact_mod_cast hd.1
    linarith only [hh]
  exact IntegerShared209.actual_shared_contradiction hN hm hF hcard (numeric w).1.le
    hAG hcover hfee (actual_price w hlo hhi).1 hH (actual_price w hlo hhi).2

#print axioms numeric
#print axioms actual_price
#print axioms actual_contradiction
end
end JSP233.IntegerLowPrices209
