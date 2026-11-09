module

public import Erdos272.Arithmetic.IntegerLowPrices209
public import Erdos272.Arithmetic.IntegerHighPrices209

@[expose] public section

namespace JSP233.IntegerRobustPrices209
open StarCompletion APGeometry DenseDeletion40 Density41 HarmonicAbel29
open IntegerHighPrices209 SharedUniform209
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def G (w : Fin 11) : ℝ := IntegerLowPrices209.G w
def U (w : Fin 11) : ℝ := IntegerLowPrices209.U w
def Eta (w : Fin 11) : ℕ := if w.val<4 then 1100 else 2000
def C (w : Fin 11) : ℝ := Eta w+142+4*M w

theorem numeric (w : Fin 11) : 0<G w ∧ 0≤U w ∧ 0≤C w ∧
    TripleShare*G w*(Upper w : ℝ)≤StrongAPResponse209.T ∧
    SharedUniformStrong209.CoupledShare*G w*(Upper w : ℝ)+U w+C w/(Lower w : ℝ)<(71/800 : ℝ) := by
  fin_cases w <;> norm_num [G,U,IntegerLowPrices209.G,IntegerLowPrices209.U,Eta,C,M,Lower,Upper,TripleShare,StrongAPResponse209.T,
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
end JSP233.IntegerRobustPrices209
