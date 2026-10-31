import Erdos272.Certificates.ForcedDual209
import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_008
namespace JSP233.FullPrefix209_009
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_294912 : DualFrontier209.checkFrom FactorFullCertificate209.phi 294912 1024 179285133607726030 26436688727 179907641221151929 26620592551 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_295936 : DualFrontier209.checkFrom FactorFullCertificate209.phi 295936 1024 179907641221151929 26620592551 180530285998113395 26805174547 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_296960 : DualFrontier209.checkFrom FactorFullCertificate209.phi 296960 1024 180530285998113395 26805174547 181152712450079998 26990329201 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_297984 : DualFrontier209.checkFrom FactorFullCertificate209.phi 297984 1024 181152712450079998 26990329201 181775192246586684 27176137083 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_299008 : DualFrontier209.checkFrom FactorFullCertificate209.phi 299008 1024 181775192246586684 27176137083 182397978682012868 27362674345 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_300032 : DualFrontier209.checkFrom FactorFullCertificate209.phi 300032 1024 182397978682012868 27362674345 183020144683832010 27549662829 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_301056 : DualFrontier209.checkFrom FactorFullCertificate209.phi 301056 1024 183020144683832010 27549662829 183642753009908069 27737421665 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_302080 : DualFrontier209.checkFrom FactorFullCertificate209.phi 302080 1024 183642753009908069 27737421665 184265596419093890 27925889413 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_294912 : DualFrontier209.checkFrom FactorFullCertificate209.phi 294912 8192 179285133607726030 26436688727 184265596419093890 27925889413 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 294912 179285133607726030 26436688727 179907641221151929 26620592551 7168 184265596419093890 27925889413 checked_small_294912 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 295936 179907641221151929 26620592551 180530285998113395 26805174547 6144 184265596419093890 27925889413 checked_small_295936 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 296960 180530285998113395 26805174547 181152712450079998 26990329201 5120 184265596419093890 27925889413 checked_small_296960 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 297984 181152712450079998 26990329201 181775192246586684 27176137083 4096 184265596419093890 27925889413 checked_small_297984 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 299008 181775192246586684 27176137083 182397978682012868 27362674345 3072 184265596419093890 27925889413 checked_small_299008 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 300032 182397978682012868 27362674345 183020144683832010 27549662829 2048 184265596419093890 27925889413 checked_small_300032 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 301056 183020144683832010 27549662829 183642753009908069 27737421665 1024 184265596419093890 27925889413 checked_small_301056 checked_small_302080)))))))
#print axioms checked_part_294912
private theorem checked_small_303104 : DualFrontier209.checkFrom FactorFullCertificate209.phi 303104 1024 184265596419093890 27925889413 184887925253352161 28114838781 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_304128 : DualFrontier209.checkFrom FactorFullCertificate209.phi 304128 1024 184887925253352161 28114838781 185510322016569319 28304445949 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_305152 : DualFrontier209.checkFrom FactorFullCertificate209.phi 305152 1024 185510322016569319 28304445949 186132895663682571 28494744481 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_306176 : DualFrontier209.checkFrom FactorFullCertificate209.phi 306176 1024 186132895663682571 28494744481 186755376464648501 28685652067 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_307200 : DualFrontier209.checkFrom FactorFullCertificate209.phi 307200 1024 186755376464648501 28685652067 187377969358664696 28877231579 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_308224 : DualFrontier209.checkFrom FactorFullCertificate209.phi 308224 1024 187377969358664696 28877231579 188000534164420636 29069440029 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_309248 : DualFrontier209.checkFrom FactorFullCertificate209.phi 309248 1024 188000534164420636 29069440029 188622873884221282 29262216191 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_310272 : DualFrontier209.checkFrom FactorFullCertificate209.phi 310272 1024 188622873884221282 29262216191 189245424232505055 29455695015 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_303104 : DualFrontier209.checkFrom FactorFullCertificate209.phi 303104 8192 184265596419093890 27925889413 189245424232505055 29455695015 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 303104 184265596419093890 27925889413 184887925253352161 28114838781 7168 189245424232505055 29455695015 checked_small_303104 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 304128 184887925253352161 28114838781 185510322016569319 28304445949 6144 189245424232505055 29455695015 checked_small_304128 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 305152 185510322016569319 28304445949 186132895663682571 28494744481 5120 189245424232505055 29455695015 checked_small_305152 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 306176 186132895663682571 28494744481 186755376464648501 28685652067 4096 189245424232505055 29455695015 checked_small_306176 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 307200 186755376464648501 28685652067 187377969358664696 28877231579 3072 189245424232505055 29455695015 checked_small_307200 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 308224 187377969358664696 28877231579 188000534164420636 29069440029 2048 189245424232505055 29455695015 checked_small_308224 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 309248 188000534164420636 29069440029 188622873884221282 29262216191 1024 189245424232505055 29455695015 checked_small_309248 checked_small_310272)))))))
#print axioms checked_part_303104
private theorem checked_small_311296 : DualFrontier209.checkFrom FactorFullCertificate209.phi 311296 1024 189245424232505055 29455695015 189868062577161367 29649838853 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_312320 : DualFrontier209.checkFrom FactorFullCertificate209.phi 312320 1024 189868062577161367 29649838853 190490597585217612 29844588013 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_313344 : DualFrontier209.checkFrom FactorFullCertificate209.phi 313344 1024 190490597585217612 29844588013 191113025331583765 30039940947 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_314368 : DualFrontier209.checkFrom FactorFullCertificate209.phi 314368 1024 191113025331583765 30039940947 191735675070456107 30236001169 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_315392 : DualFrontier209.checkFrom FactorFullCertificate209.phi 315392 1024 191735675070456107 30236001169 192357950515903403 30432580687 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_316416 : DualFrontier209.checkFrom FactorFullCertificate209.phi 316416 1024 192357950515903403 30432580687 192980520579302021 30629890693 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_317440 : DualFrontier209.checkFrom FactorFullCertificate209.phi 317440 1024 192980520579302021 30629890693 193603190001578868 30827869905 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_318464 : DualFrontier209.checkFrom FactorFullCertificate209.phi 318464 1024 193603190001578868 30827869905 194225545295028490 31026386525 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_311296 : DualFrontier209.checkFrom FactorFullCertificate209.phi 311296 8192 189245424232505055 29455695015 194225545295028490 31026386525 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 311296 189245424232505055 29455695015 189868062577161367 29649838853 7168 194225545295028490 31026386525 checked_small_311296 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 312320 189868062577161367 29649838853 190490597585217612 29844588013 6144 194225545295028490 31026386525 checked_small_312320 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 313344 190490597585217612 29844588013 191113025331583765 30039940947 5120 194225545295028490 31026386525 checked_small_313344 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 314368 191113025331583765 30039940947 191735675070456107 30236001169 4096 194225545295028490 31026386525 checked_small_314368 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 315392 191735675070456107 30236001169 192357950515903403 30432580687 3072 194225545295028490 31026386525 checked_small_315392 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 316416 192357950515903403 30432580687 192980520579302021 30629890693 2048 194225545295028490 31026386525 checked_small_316416 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 317440 192980520579302021 30629890693 193603190001578868 30827869905 1024 194225545295028490 31026386525 checked_small_317440 checked_small_318464)))))))
#print axioms checked_part_311296
private theorem checked_small_319488 : DualFrontier209.checkFrom FactorFullCertificate209.phi 319488 1024 194225545295028490 31026386525 194848036233746395 31225583739 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_320512 : DualFrontier209.checkFrom FactorFullCertificate209.phi 320512 1024 194848036233746395 31225583739 195470725332852871 31425482079 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_321536 : DualFrontier209.checkFrom FactorFullCertificate209.phi 321536 1024 195470725332852871 31425482079 196093032800353825 31625895127 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_322560 : DualFrontier209.checkFrom FactorFullCertificate209.phi 322560 1024 196093032800353825 31625895127 196715745953233811 31827076479 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_323584 : DualFrontier209.checkFrom FactorFullCertificate209.phi 323584 1024 196715745953233811 31827076479 197338319110564022 32028850249 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_324608 : DualFrontier209.checkFrom FactorFullCertificate209.phi 324608 1024 197338319110564022 32028850249 197960782852248559 32231225961 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_325632 : DualFrontier209.checkFrom FactorFullCertificate209.phi 325632 1024 197960782852248559 32231225961 198583078783712175 32434184201 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_326656 : DualFrontier209.checkFrom FactorFullCertificate209.phi 326656 1024 198583078783712175 32434184201 199205802047310123 32637919475 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_319488 : DualFrontier209.checkFrom FactorFullCertificate209.phi 319488 8192 194225545295028490 31026386525 199205802047310123 32637919475 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 319488 194225545295028490 31026386525 194848036233746395 31225583739 7168 199205802047310123 32637919475 checked_small_319488 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 320512 194848036233746395 31225583739 195470725332852871 31425482079 6144 199205802047310123 32637919475 checked_small_320512 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 321536 195470725332852871 31425482079 196093032800353825 31625895127 5120 199205802047310123 32637919475 checked_small_321536 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 322560 196093032800353825 31625895127 196715745953233811 31827076479 4096 199205802047310123 32637919475 checked_small_322560 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 323584 196715745953233811 31827076479 197338319110564022 32028850249 3072 199205802047310123 32637919475 checked_small_323584 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 324608 197338319110564022 32028850249 197960782852248559 32231225961 2048 199205802047310123 32637919475 checked_small_324608 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 325632 197960782852248559 32231225961 198583078783712175 32434184201 1024 199205802047310123 32637919475 checked_small_325632 checked_small_326656)))))))
#print axioms checked_part_319488
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 294912 32768 179285133607726030 26436688727 199205802047310123 32637919475 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 294912 179285133607726030 26436688727 184265596419093890 27925889413 24576 199205802047310123 32637919475 checked_part_294912 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 303104 184265596419093890 27925889413 189245424232505055 29455695015 16384 199205802047310123 32637919475 checked_part_303104 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 311296 189245424232505055 29455695015 194225545295028490 31026386525 8192 199205802047310123 32637919475 checked_part_311296 checked_part_319488)))
theorem block_sound :
    (199205802047310123 = FrontierCheck209.massFloor FactorFullCertificate209.phi 327680 ∧
     32637919475 = FrontierCheck209.triangle FactorFullCertificate209.phi 327680) ∧
    ∀ t, 294912 < t → t ≤ 327680 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 294912 179285133607726030 26436688727 199205802047310123 32637919475 FullPrefix209_008.endpoint.1 FullPrefix209_008.endpoint.2 checked
theorem endpoint :
    199205802047310123 = FrontierCheck209.massFloor FactorFullCertificate209.phi 327680 ∧
    32637919475 = FrontierCheck209.triangle FactorFullCertificate209.phi 327680 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 327680) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 294912
  · exact FullPrefix209_008.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_009
