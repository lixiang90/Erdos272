import Erdos272.Resources.PairRecovery131
import Erdos272.Arithmetic.WindowFirst131
import Erdos272.Arithmetic.WindowGateA131
import Erdos272.Arithmetic.WindowGateB131
import Erdos272.Arithmetic.WindowGateC131
import Erdos272.Arithmetic.WindowGateD131
import Erdos272.Arithmetic.WindowGateE131
import Erdos272.Arithmetic.WindowGateF131
import Erdos272.Arithmetic.WindowGateG131
import Erdos272.Arithmetic.WindowGateH131
/-! Complete39-window original-family assembly; the frozen130 theorem pays
all N>=107277000. These development sources do not alter the public entry. -/
namespace JSP233.Global97p94m131
open StarCompletion PairRecovery131
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000
theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 97940000≤N) (hF : Legal (Ground N) F) : F.card≤B N := by
  refine actual_original_upper_of_window (lo:=97940000) (by norm_num) ?_ hN hF
  intro n hn hnhi
  by_cases h0 : n≤97971250
  · exact ⟨_,WindowFirst131.certificate_0 hn h0⟩
  · by_cases h1 : n≤98096250
    · exact ⟨_,WindowGateA131.certificate_1 (by omega) h1⟩
    · by_cases h2 : n≤98346250
      · exact ⟨_,WindowGateA131.certificate_2 (by omega) h2⟩
      · by_cases h3 : n≤98596250
        · exact ⟨_,WindowGateA131.certificate_3 (by omega) h3⟩
        · by_cases h4 : n≤98846250
          · exact ⟨_,WindowGateA131.certificate_4 (by omega) h4⟩
          · by_cases h5 : n≤99096250
            · exact ⟨_,WindowGateA131.certificate_5 (by omega) h5⟩
            · by_cases h6 : n≤99346250
              · exact ⟨_,WindowGateB131.certificate_6 (by omega) h6⟩
              · by_cases h7 : n≤99596250
                · exact ⟨_,WindowGateB131.certificate_7 (by omega) h7⟩
                · by_cases h8 : n≤99846250
                  · exact ⟨_,WindowGateB131.certificate_8 (by omega) h8⟩
                  · by_cases h9 : n≤100096250
                    · exact ⟨_,WindowGateB131.certificate_9 (by omega) h9⟩
                    · by_cases h10 : n≤100346250
                      · exact ⟨_,WindowGateB131.certificate_10 (by omega) h10⟩
                      · by_cases h11 : n≤100596250
                        · exact ⟨_,WindowGateC131.certificate_11 (by omega) h11⟩
                        · by_cases h12 : n≤100846250
                          · exact ⟨_,WindowGateC131.certificate_12 (by omega) h12⟩
                          · by_cases h13 : n≤101096250
                            · exact ⟨_,WindowGateC131.certificate_13 (by omega) h13⟩
                            · by_cases h14 : n≤101346250
                              · exact ⟨_,WindowGateC131.certificate_14 (by omega) h14⟩
                              · by_cases h15 : n≤101596250
                                · exact ⟨_,WindowGateC131.certificate_15 (by omega) h15⟩
                                · by_cases h16 : n≤101846250
                                  · exact ⟨_,WindowGateD131.certificate_16 (by omega) h16⟩
                                  · by_cases h17 : n≤102096250
                                    · exact ⟨_,WindowGateD131.certificate_17 (by omega) h17⟩
                                    · by_cases h18 : n≤102346250
                                      · exact ⟨_,WindowGateD131.certificate_18 (by omega) h18⟩
                                      · by_cases h19 : n≤102596250
                                        · exact ⟨_,WindowGateD131.certificate_19 (by omega) h19⟩
                                        · by_cases h20 : n≤102846250
                                          · exact ⟨_,WindowGateD131.certificate_20 (by omega) h20⟩
                                          · by_cases h21 : n≤103096250
                                            · exact ⟨_,WindowGateE131.certificate_21 (by omega) h21⟩
                                            · by_cases h22 : n≤103346250
                                              · exact ⟨_,WindowGateE131.certificate_22 (by omega) h22⟩
                                              · by_cases h23 : n≤103596250
                                                · exact ⟨_,WindowGateE131.certificate_23 (by omega) h23⟩
                                                · by_cases h24 : n≤103846250
                                                  · exact ⟨_,WindowGateE131.certificate_24 (by omega) h24⟩
                                                  · by_cases h25 : n≤104096250
                                                    · exact ⟨_,WindowGateE131.certificate_25 (by omega) h25⟩
                                                    · by_cases h26 : n≤104346250
                                                      · exact ⟨_,WindowGateF131.certificate_26 (by omega) h26⟩
                                                      · by_cases h27 : n≤104596250
                                                        · exact ⟨_,WindowGateF131.certificate_27 (by omega) h27⟩
                                                        · by_cases h28 : n≤104846250
                                                          · exact ⟨_,WindowGateF131.certificate_28 (by omega) h28⟩
                                                          · by_cases h29 : n≤105096250
                                                            · exact ⟨_,WindowGateF131.certificate_29 (by omega) h29⟩
                                                            · by_cases h30 : n≤105346250
                                                              · exact ⟨_,WindowGateF131.certificate_30 (by omega) h30⟩
                                                              · by_cases h31 : n≤105596250
                                                                · exact ⟨_,WindowGateG131.certificate_31 (by omega) h31⟩
                                                                · by_cases h32 : n≤105846250
                                                                  · exact ⟨_,WindowGateG131.certificate_32 (by omega) h32⟩
                                                                  · by_cases h33 : n≤106096250
                                                                    · exact ⟨_,WindowGateG131.certificate_33 (by omega) h33⟩
                                                                    · by_cases h34 : n≤106346250
                                                                      · exact ⟨_,WindowGateG131.certificate_34 (by omega) h34⟩
                                                                      · by_cases h35 : n≤106596250
                                                                        · exact ⟨_,WindowGateG131.certificate_35 (by omega) h35⟩
                                                                        · by_cases h36 : n≤106846250
                                                                          · exact ⟨_,WindowGateH131.certificate_36 (by omega) h36⟩
                                                                          · by_cases h37 : n≤107096250
                                                                            · exact ⟨_,WindowGateH131.certificate_37 (by omega) h37⟩
                                                                            · exact ⟨_,WindowGateH131.certificate_38 (by omega) (by omega)⟩

theorem actual_value_eq_B (N : ℕ) (hN : 97940000≤N) :
    ExtremalValue45.Value N=B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 97940000≤N) :
    ∃F:Finset (Finset ℤ),Legal (Ground N) F ∧ F.card=B N ∧
      ∀G:Finset (Finset ℤ),Legal (Ground N) G→G.card≤F.card := by
  obtain ⟨F,hF,hcard⟩ := Construction45.szabo_lower_construction N (by omega)
  exact ⟨F,hF,hcard,fun G hG=>by simpa only [hcard] using actual_original_upper_bound hN hG⟩

#check @actual_original_upper_bound
#check @actual_value_eq_B
#check @actual_optimal_family
#print axioms actual_original_upper_bound
#print axioms actual_value_eq_B
#print axioms actual_optimal_family
end
end JSP233.Global97p94m131
