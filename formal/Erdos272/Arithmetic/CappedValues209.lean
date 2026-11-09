module

public import Erdos272.Arithmetic.CappedCeil209

@[expose] public section
namespace JSP233.CappedValues209
set_option maxHeartbeats 0
set_option maxRecDepth 10000
noncomputable section
def data : List (ℕ×ℕ×ℕ×ℕ) := [
  (250,36,35,6216613031),
  (250,51,50,6214811832),
  (250,63,62,6217955785),
  (250,72,71,6221696603),
  (250,79,78,6225203713),
  (250,90,83,6233431734),
  (250,100,83,6243471894),
  (250,108,83,6252522180),
  (250,117,83,6264005155),
  (250,123,83,6272564643),
  (250,129,83,6281973006),
  (250,133,83,6288781337),
  (250,138,83,6297975623),
  (250,142,83,6305944005),
  (250,146,83,6314525339),
  (250,150,83,6323793179),
  (250,154,83,6333833340),
  (250,158,83,6344746558),
  (250,162,83,6356651887),
  (250,167,83,6373147222),
  (250,169,83,6380315565),
  (250,171,83,6387846862),
  (250,173,83,6395769396),
  (250,175,83,6404114464),
  (250,177,83,6412916797),
  (250,179,83,6422215036),
  (250,181,83,6432052303),
  (250,183,83,6442476869),
  (250,185,83,6453542948),
  (250,187,83,6465311634),
  (250,189,83,6477852038),
  (250,190,83,6484435750),
  (254,52,51,6114052177),
  (254,73,72,6120632992),
  (254,93,84,6133607299),
  (254,110,84,6151065974),
  (254,123,84,6167474149),
  (254,135,84,6185802090),
  (254,144,84,6202172275),
  (254,152,84,6219148762),
  (254,159,84,6236348625),
  (254,165,84,6253244798),
  (254,171,84,6272583791),
  (254,178,84,6299005266),
  (254,182,84,6316409889),
  (254,186,84,6335862114),
  (254,190,84,6357745868),
  (254,193,84,6376042121),
  (260,53,52,5968811408),
  (260,75,74,5975241425),
  (260,95,86,5987343126),
  (260,112,86,6003532677),
  (260,125,86,6018664088),
  (260,138,86,6037020225),
  (260,147,86,6052202463),
  (260,156,86,6070012395),
  (260,162,86,6083703023),
  (260,168,86,6099179386),
  (260,175,86,6119996611),
  (260,181,86,6140776191),
  (260,186,86,6160666556),
  (260,190,86,6178624713),
  (260,194,86,6198759617),
  (260,197,86,6215538703),
  (269,55,54,5763472039),
  (269,77,76,5769244745),
  (269,99,89,5781326268),
  (269,116,89,5796013791),
  (269,130,89,5810806979),
  (269,143,89,5827487054),
  (269,152,89,5841206169),
  (269,161,89,5857211803),
  (269,168,89,5871632721),
  (269,174,89,5885684983),
  (269,181,89,5904501176),
  (269,188,89,5926569550),
  (269,192,89,5940981550),
  (269,197,89,5961248424),
  (269,201,89,5979607828),
  (269,204,89,5994860255),
  (283,82,81,5476165329),
  (283,123,94,5500689530),
  (283,151,94,5528897138),
  (283,170,94,5555999265),
  (283,186,94,5587057155),
  (283,198,94,5618023698),
  (283,207,94,5647666014),
  (283,215,94,5680601921),
  (306,88,87,5053594723),
  (306,132,102,5073989595),
  (306,163,102,5098418626),
  (306,183,102,5120714201),
  (306,201,102,5148042205),
  (306,213,102,5172137865),
  (306,224,102,5200420880),
  (306,232,102,5226271695),
  (344,99,98,4482157203),
  (344,149,114,4498728503),
  (344,183,114,4517728064),
  (344,206,114,4535889410),
  (344,226,114,4557436769),
  (344,240,114,4577450950),
  (344,252,114,4599454119),
  (344,261,114,4620131795),
  (410,118,117,3745997705),
  (410,177,136,3757500709),
  (410,218,136,3770978472),
  (410,245,136,3783511894),
  (410,269,136,3798682372),
  (410,286,136,3812981160),
  (410,300,136,3828075174),
  (410,311,136,3842929600),
  (533,153,152,2867583356),
  (533,231,177,2874518675),
  (533,284,177,2882482584),
  (533,319,177,2889904425),
  (533,350,177,2898848874),
  (533,372,177,2907286153),
  (533,390,177,2916120355),
  (533,405,177,2925380163),
  (792,227,226,1919177160),
  (792,342,264,1922263057),
  (792,421,264,1925847872),
  (792,473,264,1929176497),
  (792,519,264,1933178068),
  (792,552,264,1936993697),
  (792,579,264,1940994977),
  (792,601,264,1945091693),
  (1432,411,410,1055708977),
  (1432,619,477,1056658037),
  (1432,762,477,1057758771),
  (1432,857,477,1058792704),
  (1432,940,477,1060022851),
  (1432,999,477,1061184060),
  (1432,1047,477,1062391330),
  (1432,1088,477,1063689335)]
theorem checks : data.all (fun r=>CappedCeil209.Check r.1 r.2.1 r.2.2.1 r.2.2.2)=true := by decide +kernel
theorem bound {M e c u : ℕ} (h : (M,e,c,u)∈data) :
    NearCapped209.Price M e c≤(u : ℝ)/(ResidualCeil208.Grid : ℝ) :=
  CappedCeil209.check_sound ((List.all_eq_true.mp checks) _ h)
theorem bound_250_36 : NearCapped209.Price 250 36 35≤((6216613031 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_51 : NearCapped209.Price 250 51 50≤((6214811832 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_63 : NearCapped209.Price 250 63 62≤((6217955785 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_72 : NearCapped209.Price 250 72 71≤((6221696603 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_79 : NearCapped209.Price 250 79 78≤((6225203713 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_90 : NearCapped209.Price 250 90 83≤((6233431734 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_100 : NearCapped209.Price 250 100 83≤((6243471894 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_108 : NearCapped209.Price 250 108 83≤((6252522180 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_117 : NearCapped209.Price 250 117 83≤((6264005155 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_123 : NearCapped209.Price 250 123 83≤((6272564643 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_129 : NearCapped209.Price 250 129 83≤((6281973006 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_133 : NearCapped209.Price 250 133 83≤((6288781337 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_138 : NearCapped209.Price 250 138 83≤((6297975623 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_142 : NearCapped209.Price 250 142 83≤((6305944005 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_146 : NearCapped209.Price 250 146 83≤((6314525339 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_150 : NearCapped209.Price 250 150 83≤((6323793179 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_154 : NearCapped209.Price 250 154 83≤((6333833340 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_158 : NearCapped209.Price 250 158 83≤((6344746558 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_162 : NearCapped209.Price 250 162 83≤((6356651887 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_167 : NearCapped209.Price 250 167 83≤((6373147222 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_169 : NearCapped209.Price 250 169 83≤((6380315565 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_171 : NearCapped209.Price 250 171 83≤((6387846862 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_173 : NearCapped209.Price 250 173 83≤((6395769396 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_175 : NearCapped209.Price 250 175 83≤((6404114464 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_177 : NearCapped209.Price 250 177 83≤((6412916797 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_179 : NearCapped209.Price 250 179 83≤((6422215036 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_181 : NearCapped209.Price 250 181 83≤((6432052303 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_183 : NearCapped209.Price 250 183 83≤((6442476869 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_185 : NearCapped209.Price 250 185 83≤((6453542948 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_187 : NearCapped209.Price 250 187 83≤((6465311634 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_189 : NearCapped209.Price 250 189 83≤((6477852038 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_250_190 : NearCapped209.Price 250 190 83≤((6484435750 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_254_52 : NearCapped209.Price 254 52 51≤((6114052177 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_254_73 : NearCapped209.Price 254 73 72≤((6120632992 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_254_93 : NearCapped209.Price 254 93 84≤((6133607299 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_254_110 : NearCapped209.Price 254 110 84≤((6151065974 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_254_123 : NearCapped209.Price 254 123 84≤((6167474149 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_254_135 : NearCapped209.Price 254 135 84≤((6185802090 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_254_144 : NearCapped209.Price 254 144 84≤((6202172275 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_254_152 : NearCapped209.Price 254 152 84≤((6219148762 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_254_159 : NearCapped209.Price 254 159 84≤((6236348625 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_254_165 : NearCapped209.Price 254 165 84≤((6253244798 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_254_171 : NearCapped209.Price 254 171 84≤((6272583791 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_254_178 : NearCapped209.Price 254 178 84≤((6299005266 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_254_182 : NearCapped209.Price 254 182 84≤((6316409889 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_254_186 : NearCapped209.Price 254 186 84≤((6335862114 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_254_190 : NearCapped209.Price 254 190 84≤((6357745868 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_254_193 : NearCapped209.Price 254 193 84≤((6376042121 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_260_53 : NearCapped209.Price 260 53 52≤((5968811408 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_260_75 : NearCapped209.Price 260 75 74≤((5975241425 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_260_95 : NearCapped209.Price 260 95 86≤((5987343126 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_260_112 : NearCapped209.Price 260 112 86≤((6003532677 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_260_125 : NearCapped209.Price 260 125 86≤((6018664088 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_260_138 : NearCapped209.Price 260 138 86≤((6037020225 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_260_147 : NearCapped209.Price 260 147 86≤((6052202463 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_260_156 : NearCapped209.Price 260 156 86≤((6070012395 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_260_162 : NearCapped209.Price 260 162 86≤((6083703023 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_260_168 : NearCapped209.Price 260 168 86≤((6099179386 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_260_175 : NearCapped209.Price 260 175 86≤((6119996611 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_260_181 : NearCapped209.Price 260 181 86≤((6140776191 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_260_186 : NearCapped209.Price 260 186 86≤((6160666556 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_260_190 : NearCapped209.Price 260 190 86≤((6178624713 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_260_194 : NearCapped209.Price 260 194 86≤((6198759617 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_260_197 : NearCapped209.Price 260 197 86≤((6215538703 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_269_55 : NearCapped209.Price 269 55 54≤((5763472039 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_269_77 : NearCapped209.Price 269 77 76≤((5769244745 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_269_99 : NearCapped209.Price 269 99 89≤((5781326268 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_269_116 : NearCapped209.Price 269 116 89≤((5796013791 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_269_130 : NearCapped209.Price 269 130 89≤((5810806979 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_269_143 : NearCapped209.Price 269 143 89≤((5827487054 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_269_152 : NearCapped209.Price 269 152 89≤((5841206169 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_269_161 : NearCapped209.Price 269 161 89≤((5857211803 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_269_168 : NearCapped209.Price 269 168 89≤((5871632721 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_269_174 : NearCapped209.Price 269 174 89≤((5885684983 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_269_181 : NearCapped209.Price 269 181 89≤((5904501176 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_269_188 : NearCapped209.Price 269 188 89≤((5926569550 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_269_192 : NearCapped209.Price 269 192 89≤((5940981550 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_269_197 : NearCapped209.Price 269 197 89≤((5961248424 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_269_201 : NearCapped209.Price 269 201 89≤((5979607828 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_269_204 : NearCapped209.Price 269 204 89≤((5994860255 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_283_82 : NearCapped209.Price 283 82 81≤((5476165329 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_283_123 : NearCapped209.Price 283 123 94≤((5500689530 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_283_151 : NearCapped209.Price 283 151 94≤((5528897138 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_283_170 : NearCapped209.Price 283 170 94≤((5555999265 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_283_186 : NearCapped209.Price 283 186 94≤((5587057155 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_283_198 : NearCapped209.Price 283 198 94≤((5618023698 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_283_207 : NearCapped209.Price 283 207 94≤((5647666014 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_283_215 : NearCapped209.Price 283 215 94≤((5680601921 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_306_88 : NearCapped209.Price 306 88 87≤((5053594723 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_306_132 : NearCapped209.Price 306 132 102≤((5073989595 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_306_163 : NearCapped209.Price 306 163 102≤((5098418626 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_306_183 : NearCapped209.Price 306 183 102≤((5120714201 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_306_201 : NearCapped209.Price 306 201 102≤((5148042205 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_306_213 : NearCapped209.Price 306 213 102≤((5172137865 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_306_224 : NearCapped209.Price 306 224 102≤((5200420880 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_306_232 : NearCapped209.Price 306 232 102≤((5226271695 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_344_99 : NearCapped209.Price 344 99 98≤((4482157203 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_344_149 : NearCapped209.Price 344 149 114≤((4498728503 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_344_183 : NearCapped209.Price 344 183 114≤((4517728064 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_344_206 : NearCapped209.Price 344 206 114≤((4535889410 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_344_226 : NearCapped209.Price 344 226 114≤((4557436769 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_344_240 : NearCapped209.Price 344 240 114≤((4577450950 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_344_252 : NearCapped209.Price 344 252 114≤((4599454119 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_344_261 : NearCapped209.Price 344 261 114≤((4620131795 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_410_118 : NearCapped209.Price 410 118 117≤((3745997705 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_410_177 : NearCapped209.Price 410 177 136≤((3757500709 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_410_218 : NearCapped209.Price 410 218 136≤((3770978472 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_410_245 : NearCapped209.Price 410 245 136≤((3783511894 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_410_269 : NearCapped209.Price 410 269 136≤((3798682372 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_410_286 : NearCapped209.Price 410 286 136≤((3812981160 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_410_300 : NearCapped209.Price 410 300 136≤((3828075174 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_410_311 : NearCapped209.Price 410 311 136≤((3842929600 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_533_153 : NearCapped209.Price 533 153 152≤((2867583356 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_533_231 : NearCapped209.Price 533 231 177≤((2874518675 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_533_284 : NearCapped209.Price 533 284 177≤((2882482584 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_533_319 : NearCapped209.Price 533 319 177≤((2889904425 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_533_350 : NearCapped209.Price 533 350 177≤((2898848874 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_533_372 : NearCapped209.Price 533 372 177≤((2907286153 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_533_390 : NearCapped209.Price 533 390 177≤((2916120355 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_533_405 : NearCapped209.Price 533 405 177≤((2925380163 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_792_227 : NearCapped209.Price 792 227 226≤((1919177160 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_792_342 : NearCapped209.Price 792 342 264≤((1922263057 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_792_421 : NearCapped209.Price 792 421 264≤((1925847872 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_792_473 : NearCapped209.Price 792 473 264≤((1929176497 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_792_519 : NearCapped209.Price 792 519 264≤((1933178068 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_792_552 : NearCapped209.Price 792 552 264≤((1936993697 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_792_579 : NearCapped209.Price 792 579 264≤((1940994977 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_792_601 : NearCapped209.Price 792 601 264≤((1945091693 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_1432_411 : NearCapped209.Price 1432 411 410≤((1055708977 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_1432_619 : NearCapped209.Price 1432 619 477≤((1056658037 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_1432_762 : NearCapped209.Price 1432 762 477≤((1057758771 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_1432_857 : NearCapped209.Price 1432 857 477≤((1058792704 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_1432_940 : NearCapped209.Price 1432 940 477≤((1060022851 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_1432_999 : NearCapped209.Price 1432 999 477≤((1061184060 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_1432_1047 : NearCapped209.Price 1432 1047 477≤((1062391330 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
theorem bound_1432_1088 : NearCapped209.Price 1432 1088 477≤((1063689335 : ℕ) : ℝ)/(ResidualCeil208.Grid : ℝ) := bound (by decide +kernel)
#print axioms checks
#print axioms bound
end
end JSP233.CappedValues209
